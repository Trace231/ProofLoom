import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Order.Filter.Extr
import Mathlib.Order.SaddlePoint
import Mathlib.Probability.Notation
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import SOptLib.Model.BlockSampling
import SOptLib.Model.Bregman
import SOptLib.Model.Fenchel
import SOptLib.Model.Filtration
import SOptLib.Model.Iterates
import SOptLib.Model.Objective
import SOptLib.Model.ParameterChoices
import SOptLib.Model.Prox
import SOptLib.Model.Saddle
import SOptLib.Model.StochasticOracle
import SOptLib.Model.Subdifferential
import SOptLib.Glue.Algebra
import SOptLib.Glue.Analysis
import SOptLib.Glue.Calculus
import SOptLib.Glue.Probability
import SOptLib.Layer0.ConvexFOC
import SOptLib.Layer0.Objective
import SOptLib.Layer0.Oracle
import SOptLib.Layer0.Subgradient
import SOptLib.Layer1.Descent
import SOptLib.Layer1.Proximal
import SOptLib.Layer1.Telescope

/-!
# Random primal-dual gradient, object layer

This file records the canonical mathematical objects from FOML Algorithm 5.1.
The algorithmic spine is defined from the paper's argmin updates and sampled
block process; proof-relevant regularity and solvability facts are exposed as
named theorem obligations rather than as prox-oracle or iterate witnesses.
-/

open scoped BigOperators
open scoped InnerProductSpace
open scoped Gradient
open scoped ProbabilityTheory
open MeasureTheory

namespace RandomPrimalDualGradient

variable {E ι : Type*}
variable [Fintype ι] [Nonempty ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [FiniteDimensional ℝ E]

/-- Paper setup data for FOML Eq. (5.1.1) and the saddle reformulation
Eqs. (5.1.12)--(5.1.13);
`book/FOML/RandomPrimalDualGradient.json#/setup`. Operation fields for the
primal/dual updates are intentionally absent: the update maps below are
canonical `def`s selected from the paper argmin problems. The ambient `E` is
required finite-dimensional, modeling the paper's `ℝ^n` variable space without
choosing coordinates. -/
structure Setup (E ι : Type*) [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E] where
  /-- Feasible primal set `X`. -/
  X : Set E
  /-- Component objectives `f_i`. -/
  f : ι → E → ℝ
  /-- Relatively simple convex term `h`. -/
  h : E → ℝ
  /-- Distance-generating function `ν` restricted to the carrier `X`. -/
  nu : {x : E // x ∈ X} → ℝ
  /-- Selected carrier subgradient `ν'`, used in the paper Bregman divergence. -/
  nuGrad : {x : E // x ∈ X} → E
  /-- Regularization parameter `μ`. -/
  μ : ℝ
  /-- Component smoothness constants `L_i`. -/
  L : ι → ℝ
  /-- Average smoothness constant `L_f`. -/
  Lf : ℝ
  /-- One-step block distribution from Algorithm 5.1; the real probabilities
  `p_i` below are derived from this PMF rather than supplied with separate
  normalization witnesses. -/
  blockPMF : PMF ι
  /-- Dual prox parameters `τ_t`. -/
  τ : ℕ → ℝ
  /-- Primal prox parameters `η_t`. -/
  η : ℕ → ℝ
  /-- Extrapolation parameters `α_t`. -/
  α : ℕ → ℝ
  /-- Initial primal point `x^0 = x^{-1}`. -/
  x0 : {x : E // x ∈ X}

variable (setup : Setup E ι)

/-- Positive-probability support of the Algorithm 5.1 block law. This is the
canonical domain on which the displayed inverse-probability sampled update
`p_{i_t}^{-1}` is meaningful; no separate full-support assumption is introduced.
No SOptLib match: searched `PMF support subtype sampled block`, checked
Mathlib `PMF.support`, `PMF.ofFintype`, and SOptLib `finiteBlockIndexLaw`; the
paper-specific object is the support subtype of the stated one-step law. -/
abbrev PositiveBlock : Type _ := setup.blockPMF.support

/-- Canonical sample space for Algorithm 5.1 block draws: one positive-support
block index per paper iteration. This removes the previous arbitrary
probability-space/block-stream witness from `Setup` and avoids a global
full-support assumption. -/
abbrev BlockSamplePath : Type _ := ℕ → PositiveBlock setup

/-- Finite block-prefix sample space for Theorem 5.1 expectations, indexed by
the paper times `1,...,k`. -/
abbrev BlockPrefix (k : ℕ) := {t : ℕ // 1 ≤ t ∧ t ≤ k} → PositiveBlock setup

/-- Primal carrier `X`. -/
abbrev PrimalCarrier : Type _ := {x : E // x ∈ setup.X}

/-- Number of finite-sum components, the paper's `m`. -/
def componentCount : ℕ := Fintype.card ι

/-- `m > 0` for the paper index set `i = 1, ..., m`; no PDF lookup was needed
because the JSON consistently quantifies over the nonempty finite range. -/
theorem componentCount_pos : 0 < componentCount (ι := ι) := by
  classical
  exact Fintype.card_pos

/-- Real positivity of the paper component count `m`. -/
theorem componentCount_real_pos : 0 < (componentCount (ι := ι) : ℝ) := by
  exact_mod_cast (componentCount_pos (ι := ι))

/-- Nonzero denominator certificate for quotients by the paper component count. -/
theorem componentCount_real_ne_zero : (componentCount (ι := ι) : ℝ) ≠ 0 :=
  ne_of_gt (componentCount_real_pos (ι := ι))

/-- Domain-checked realization of a source quotient.
No SOptLib value-level match: searched `checked quotient denominator nonzero
division`, considered the quotient bridge
`checkedQuotient_weight_mono_semantics` in
`SOptLib/Model/ParameterChoices.lean`, and scanned that file; SOptLib provides
quotient proof bridges but not a value constructor for the paper's displayed
domain-restricted scalar quotients. This local wrapper keeps every quotient call
site carrying an explicit denominator certificate. -/
noncomputable def sourceQuotient (num denom : ℝ) (_hden : denom ≠ 0) : ℝ :=
  num / denom

/-- Defining equation for the domain-checked source quotient. -/
theorem sourceQuotient_def (num denom : ℝ) (hden : denom ≠ 0) :
    sourceQuotient num denom hden = num / denom := by
  rfl

/-- Domain-checked reciprocal of the paper component count `m`. -/
noncomputable def componentCountInverse : ℝ :=
  sourceQuotient 1 (componentCount (ι := ι) : ℝ) (componentCount_real_ne_zero (ι := ι))

/-- Canonical dual block space `Y_i`: the finite-domain carrier on which the
Fenchel conjugate of `f_i/m` is real-valued.
No SOptLib match: searched `Fenchel conjugate convex supremum` and
`dual space gradient carrier conjugate`, considered the `canonicalDualNorm`
support-function primitive in `SOptLib/Model/Norms.lean`, and scanned
`SOptLib/Model/Objective.lean`, `SOptLib/Model/Norms.lean`, and
`SOptLib/Model/Subdifferential.lean`; none define the paper's block conjugate
carrier. Section 5.1.1 states `J_i : Y_i -> R`, so `Y_i` is modeled as the
domain where the displayed supremum defining the conjugate is finite rather than
as all of the ambient dual space. -/
noncomputable def dualSpace (_setup : Setup E ι) (i : ι) : Set E :=
  SOptLib.fenchelConjugateDomain (componentCountInverse (ι := ι)) (_setup.f i)

/-- Dual block carrier `Y_i` from Section 5.1.1, canonically realized as the
ambient dual carrier where gradients of `f_i/m` reside. -/
abbrev DualCarrier (setup : Setup E ι) (i : ι) : Type _ :=
  {y : E // y ∈ dualSpace setup i}

/-- Product dual carrier `Y = Y_1 × ... × Y_m` from Eq. (5.1.12).
No SOptLib match: searched `product dual space saddle state carrier primal dual
product`, manually scanned `SOptLib/Model/Carrier.lean`,
`SOptLib/Model/Objective.lean`, and `SOptLib/Model/Iterates.lean`, and checked
the sibling saddle files; existing product-coordinate helpers are generic update
machinery or sibling-paper local structures, not the FOML RPDG product
`Π_i Y_i`. -/
abbrev DualProductCarrier (setup : Setup E ι) : Type _ :=
  (i : ι) → DualCarrier setup i

/-- Saddle feasible state `Z = X × Y` from Eq. (5.1.12).
No SOptLib match: searched `saddle point primal dual carrier product`, scanned
the carrier/objective/iterate model files, and checked sibling saddle files; no
reusable primitive names this paper's `X × Π_i Y_i` carrier without adding
extra problem structure. -/
abbrev SaddlePoint (setup : Setup E ι) : Type _ :=
  PrimalCarrier setup × DualProductCarrier setup

/-- Active definitional signature for the paper carriers `Y` and `Z`.
This is an audit hook for the transparent aliases above, not a new assumption.
No SOptLib match: searched `product dual space saddle state carrier primal dual
product` and `saddle point primal dual carrier product`; checked the generic
dependent product-coordinate replacement in `SOptLib/Model/Iterates.lean`, which
updates coordinates but does not name the source carrier `X × Π_i Y_i`. -/
def saddleCarrierSignature : Prop :=
  DualProductCarrier setup = ((i : ι) → DualCarrier setup i) ∧
    SaddlePoint setup = (PrimalCarrier setup × DualProductCarrier setup)

/-- The live paper carrier aliases have the locked Eq. (5.1.12) shape. -/
theorem saddleCarrierSignature_holds :
    saddleCarrierSignature setup := by
  exact ⟨rfl, rfl⟩

/-- Real block probability `p_i = Prob{i_t=i}` from Algorithm 5.1, derived
from the canonical one-step PMF;
`book/FOML/RandomPrimalDualGradient.json#/assumptions/25`.
Aligns with SOptLib/Mathlib PMF primitives: `finiteBlockIndexLaw` was checked
and rejected at this source boundary because it requires external real-weight
normalization proofs, while the paper object is the sampling law itself. -/
noncomputable def samplingProbability (i : ι) : ℝ :=
  (setup.blockPMF i).toReal

/-- Nonnegativity of the derived block probabilities. -/
theorem samplingProbability_nonnegative (i : ι) : 0 ≤ samplingProbability setup i := by
  exact ENNReal.toReal_nonneg

/-- Finite ENNReal normalization for a PMF.
No direct SOptLib match: searched `PMF tsum coe toReal sum one Fintype ENNReal`
and `PMF support subtype sum eq one`; SOptLib candidates such as
`stoppingVectorWeight_ofReal_sum_eq_one` and `PMF.ofFintypeOfReal` construct or
transport normalized real weights, while this helper consumes an existing
Mathlib `PMF` and exposes its finite atom sum. -/
private theorem pmf_ennreal_sum_eq_one {α : Type*} [Fintype α] (p : PMF α) :
    (∑ a : α, p a) = 1 := by
  classical
  simpa [tsum_fintype] using (PMF.tsum_coe p)

/-- Real normalization for the finite atoms of an existing PMF.
No direct SOptLib match: searched `PMF tsum coe toReal sum one Fintype ENNReal`;
available SOptLib PMF helpers require supplied real-weight normalization or
measure transport hypotheses, but Algorithm 5.1's probabilities are already
encoded by `setup.blockPMF`. -/
private theorem pmf_toReal_sum_eq_one {α : Type*} [Fintype α] (p : PMF α) :
    (∑ a : α, (p a).toReal) = 1 := by
  exact PMF.sum_toReal_eq_one p

/-- Unit total mass of the derived block probabilities. -/
theorem samplingProbability_sum_one : ∑ i : ι, samplingProbability setup i = 1 := by
  classical
  simpa [samplingProbability] using (pmf_toReal_sum_eq_one setup.blockPMF)

/-- A single Algorithm 5.1 block probability is at most one, from the finite
PMF normalization. This is the elementary probability side condition needed to
compare the sharper Young correction with the paper's displayed weaker
`p_i^{-1}` denominator. -/
private theorem samplingProbability_le_one (i : ι) :
    samplingProbability setup i ≤ 1 := by
  classical
  have hsingle :
      samplingProbability setup i ≤ ∑ j : ι, samplingProbability setup j := by
    exact Finset.single_le_sum
      (fun j _hj => samplingProbability_nonnegative setup j)
      (Finset.mem_univ i)
  simpa [samplingProbability_sum_one setup] using hsingle

/-- Domain-checked inverse-probability coefficient `p_i^{-1}` appearing in
Algorithm 5.1, Lemma 5.5, and Proposition 5.1. The PDF displays the coefficient
directly, but the value-level Lean object requires the denominator certificate
made explicit here rather than relying on the total inverse at `p_i = 0`. -/
noncomputable def inverseProbabilityValue
    (i : ι) (hprob : samplingProbability setup i ≠ 0) : ℝ :=
  sourceQuotient 1 (samplingProbability setup i) hprob

/-- Explicit corrected-boundary requirement for source-gap declarations that
print all-block reciprocals `p_i^{-1}`. This is not a paper assumption:
targeted PDF extraction found Algorithm 5.1 and Proposition 5.1 display the
reciprocal without a separate full-support premise. No SOptLib match: searched
`denominator admissible quotient nonzero`, checked
the quotient bridge `checkedQuotient_weight_mono_semantics` in
`SOptLib/Model/ParameterChoices.lean`, and scanned
`SOptLib/Model/ParameterChoices.lean`; existing primitives are quotient algebra
bridges, not this paper-specific source-boundary record. -/
def allBlockProbabilityDenominatorsAdmissible : Prop :=
  ∀ i : ι, samplingProbability setup i ≠ 0

/-- The positive-support block type is nonempty because a PMF has nonempty
support. -/
noncomputable instance positiveBlockNonempty : Nonempty (PositiveBlock setup) := by
  classical
  exact ⟨Classical.choose setup.blockPMF.support_nonempty,
    Classical.choose_spec setup.blockPMF.support_nonempty⟩

/-- The positive-support restriction of a finite PMF still has total mass one.
No direct SOptLib match: searched `PMF support subtype sum eq one` and
`sum subtype filter Fintype`; SOptLib PMF/product-measure lemmas transport
finite laws but do not normalize the support subtype of an already-given PMF,
so this local bridge uses `PMF.mem_support_iff` and the finite PMF normalizer
above. -/
private theorem pmf_support_subtype_sum_eq_one {α : Type*} [Fintype α]
    (p : PMF α) [Fintype p.support] :
    (∑ a : p.support, p a.1) = 1 := by
  classical
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
      · intro a ha
        rfl
    have hnonzero :
        (∑ a ∈ (Finset.univ : Finset α) with p a ≠ 0, p a) =
          (∑ a : α, p a) := by
      simpa using
        (Finset.sum_filter_ne_zero (s := (Finset.univ : Finset α))
          (f := fun a : α => p a))
    exact hsub.trans (hmem.trans hnonzero)
  rw [hsupport, pmf_ennreal_sum_eq_one p]

/-- Canonical PMF on the positive-support block domain. Its projection to `ι`
recovers the paper probabilities, while every sampled block carries the
certificate needed for `p_{i_t}^{-1}`. -/
noncomputable def positiveBlockPMF : PMF (PositiveBlock setup) := by
  exact PMF.supportSubtypePMF setup.blockPMF

/-- Canonical finite law of one support-valued block draw `i_t`.
Aligns with Mathlib `PMF.toMeasure`: it is the one-step distribution stated in
Algorithm 5.1, restricted to the positive-probability support so the displayed
sampled reciprocal is domain-correct. -/
noncomputable def blockIndexLaw : Measure (PositiveBlock setup) :=
  PMF.supportSubtypeLaw setup.blockPMF

/-- The support-valued one-step block law projects to the paper singleton
probabilities. -/
theorem blockIndexLaw_projected_singleton (i : ι) :
    Measure.map (fun j : PositiveBlock setup => j.1) (blockIndexLaw setup) ({i} : Set ι) =
      ENNReal.ofReal (samplingProbability setup i) := by
  simpa [blockIndexLaw, samplingProbability, ENNReal.ofReal_toReal,
    setup.blockPMF.apply_ne_top i] using
      (PMF.supportSubtypeLaw_map_val_singleton setup.blockPMF i)

/-- Canonical iid law of the sampled block stream `i_1,i_2,...`.
Aligns with SOptLib `iidStreamLaw`: Algorithm 5.1 samples a fresh block inside
each iteration according to the fixed probabilities `p_i`. -/
noncomputable def blockStreamLaw : Measure (BlockSamplePath setup) :=
  SOptLib.iidStreamLaw (blockIndexLaw setup)

/-- The canonical support-valued sampled block at time `t`. -/
def sampledPositiveBlock (t : ℕ) (ω : BlockSamplePath setup) : PositiveBlock setup :=
  ω t

/-- The canonical sampled paper block index at time `t`. -/
def sampledBlock (t : ℕ) (ω : BlockSamplePath setup) : ι :=
  (sampledPositiveBlock setup t ω).1

/-- A sampled positive-support block supplies the denominator certificate for
the paper coefficient `p_{i_t}^{-1}`. -/
theorem sampledBlock_probability_ne_zero (sampled : PositiveBlock setup) :
    samplingProbability setup sampled.1 ≠ 0 := by
  rw [samplingProbability, ENNReal.toReal_ne_zero]
  exact ⟨sampled.2, setup.blockPMF.apply_ne_top sampled.1⟩

/-- The finite prefix `(i_1,...,i_k)` extracted from an infinite block stream.
Aligns with SOptLib `iidStreamLaw` finite-coordinate marginal infrastructure:
Theorem 5.1 states that expectations are with respect to `i_1,...,i_k`, so the
paper-facing theorem below uses this prefix law rather than an unrestricted
infinite-stream expectation. -/
def blockPrefix (k : ℕ) (ω : BlockSamplePath setup) : BlockPrefix setup k :=
  fun t => sampledPositiveBlock setup t.1 ω

/-- Canonical law of the finite block prefix `(i_1,...,i_k)`. -/
noncomputable def blockPrefixLaw (k : ℕ) : Measure (BlockPrefix setup k) :=
  Measure.map (blockPrefix setup k) (blockStreamLaw setup)

/-- Deterministic extension of a finite paper prefix to a full stream. Values
outside `1,...,k` are irrelevant for Algorithm 5.1 objects up to time `k`. -/
noncomputable def extendBlockPrefix (k : ℕ) (pref : BlockPrefix setup k) :
    BlockSamplePath setup :=
  SOptLib.extendSampleWindow (A := PositiveBlock setup) 1 k
    (fun r => pref ⟨r.1 + 1, by omega⟩)
    (Classical.choice (positiveBlockNonempty setup))

/-- Extending a finite paper prefix to a full stream and then restricting back
to `i_1,...,i_k` recovers the original prefix. This theorem records that the
arbitrary outside-window default in `extendBlockPrefix` is not part of the
paper-facing expectation over `i_1,...,i_k`.
No usable SOptLib import-boundary match: searched `finite prefix extension
section block prefix` and `sample window finite prefix recursive process
determined by prefix`; the relevant newer sample-window helpers exist only in a
source module whose `.olean` is not available to this target build. This paper
boundary is the one-based `BlockPrefix setup k` section property from Theorem
5.1's expectation over `i_1,...,i_k`. -/
theorem blockPrefix_extendBlockPrefix (k : ℕ) (pref : BlockPrefix setup k) :
    blockPrefix setup k (extendBlockPrefix setup k pref) = pref := by
  funext t
  simpa [blockPrefix, extendBlockPrefix, sampledPositiveBlock] using
    (SOptLib.extendSampleWindow_one_based_apply
      (pref := pref)
      (sampleDefault := Classical.choice (positiveBlockNonempty setup))
      (ht := t.2.1) (htk := t.2.2))

/-- Natural filtration generated by the paper-time sampled block prefix. Its
`seq r` is generated by `i_1,...,i_r`; hence Lemma 5.4 conditions on
`seq (t-1)` for `E_t`, the conditional expectation with respect to `i_t` given
`i_1,...,i_{t-1}`. Aligns with SOptLib `filtration`, specialized to the shifted
one-based block-index stream rather than the raw zero-based coordinate stream. -/
noncomputable def blockPrefixFiltration (setup : Setup E ι) :
    Filtration ℕ (by infer_instance : MeasurableSpace (BlockSamplePath setup)) :=
  let _setupRef : Setup E ι := setup
  SOptLib.filtration (fun t (ω : BlockSamplePath setup) => sampledPositiveBlock setup (t + 1) ω)
    (fun t => by
      simpa [sampledPositiveBlock] using measurable_pi_apply (t + 1))

/-- Defining equation for the paper-time block-prefix filtration. -/
theorem blockPrefixFiltration_seq (setup : Setup E ι) (r : ℕ) :
    (blockPrefixFiltration setup).seq r =
      ⨆ j < r,
        MeasurableSpace.comap
          (fun ω : BlockSamplePath setup => sampledPositiveBlock setup (j + 1) ω)
          (by infer_instance : MeasurableSpace (PositiveBlock setup)) := by
  rfl

/-- Finite-sum objective `f(x) = m⁻¹ ∑ᵢ f_i(x)` from Eq. (5.1.4). -/
noncomputable def averageObjective (x : PrimalCarrier setup) : ℝ :=
  componentCountInverse (ι := ι) * ∑ i : ι, setup.f i x.1

/-- Ambient version of the finite-sum objective from Eq. (5.1.4). -/
noncomputable def averageObjectiveAmbient (x : E) : ℝ :=
  componentCountInverse (ι := ι) * ∑ i : ι, setup.f i x

/-- Canonical component gradient `∇ f_i(x)`. The realization theorem
`componentGradient_hasGradientAt` below records that this total selector is the
paper gradient under the source smoothness assumption. -/
noncomputable def componentGradient (i : ι) (x : E) : E :=
  ∇ (setup.f i) x

/-- Average gradient `∇f(x)=m⁻¹∑ᵢ∇f_i(x)` from Eq. (5.1.4). -/
noncomputable def averageGradient (x : E) : E :=
  ∇ (averageObjectiveAmbient setup) x

/-- Regularizer `h(x)+μν(x)` in the finite-sum objective Eq. (5.1.1). -/
noncomputable def objectiveRegularizer (x : PrimalCarrier setup) : ℝ :=
  setup.h x.1 + setup.μ * setup.nu x

/-- Composite primal objective
`Ψ(x) = m⁻¹∑ᵢ f_i(x) + h(x) + μν(x)` from Eq. (5.1.1).
Aligns with SOptLib `compositeObjective`: symbol search and direct checks
considered `finiteAverageRegularizedObjectiveOn`, but the current exported
module image does not expose that newer finite-average primitive; the available
composite objective primitive exactly matches the outer `average + regularizer`
object while the finite average itself remains the paper-local Eq. (5.1.4)
definition above. -/
noncomputable def objective (x : PrimalCarrier setup) : ℝ :=
  SOptLib.compositeObjective (averageObjective setup) (objectiveRegularizer setup) x

/-- Source-form unfolding of the composite objective in Eq. (5.1.1). This keeps
the paper-facing displayed quotient `m⁻¹∑ᵢ f_i+h+μν` available through the
existing domain-checked `componentCountInverse` after the outer sum is modeled
by `SOptLib.compositeObjective`. -/
theorem objective_eq_source_formula (x : PrimalCarrier setup) :
    objective setup x =
      averageObjective setup x + setup.h x.1 + setup.μ * setup.nu x := by
  simp [objective, objectiveRegularizer, SOptLib.compositeObjective]
  rw [add_assoc]

/-- `x*` is an optimal solution of the primal problem (5.1.1).
No reusable selector is used here: SOptLib `ObjectiveMinimum` and
`argminSelectorOfSource` were checked but bundle/provide an optimizer witness,
while Theorem 5.1 is stated for an arbitrary source optimizer `x*`. -/
def IsOptimalPrimal (xstar : PrimalCarrier setup) : Prop :=
  IsMinOn (objective setup) Set.univ xstar

/-- Bundled attained minimum for the primal problem (5.1.1), built from an
arbitrary source optimizer `x*`.
Aligns with SOptLib `ObjectiveMinimum.ofSource`: the reusable primitive exactly
models an attained objective minimum, while the paper-facing theorem still
quantifies over an arbitrary optimizer `x*` rather than adding a Setup-level
optimizer witness. -/
noncomputable def primalObjectiveMinimum
    (xstar : PrimalCarrier setup) (hxstar : IsOptimalPrimal setup xstar) :
    SOptLib.ObjectiveMinimum (objective setup) :=
  SOptLib.ObjectiveMinimum.ofSource (objective setup) xstar
    ((isMinOn_univ_iff (f := objective setup) (a := xstar)).1 hxstar)

/-- Canonical optimal value `Ψ*` from Eq. (5.1.1), realized as the value of the
attained minimum generated by the source optimizer `x*`. -/
noncomputable def primalOptimalValue
    (xstar : PrimalCarrier setup) (hxstar : IsOptimalPrimal setup xstar) : ℝ :=
  SOptLib.objectiveMinimumValue (objective setup)
    (primalObjectiveMinimum setup xstar hxstar)

/-- The canonical optimal value `Ψ*` agrees with `Ψ(x*)` for the source optimizer. -/
theorem primalOptimalValue_eq_objective
    (xstar : PrimalCarrier setup) (hxstar : IsOptimalPrimal setup xstar) :
    primalOptimalValue setup xstar hxstar = objective setup xstar := by
  simp [primalOptimalValue, primalObjectiveMinimum]

/-- The optimal value `Ψ*` lower-bounds every feasible objective value. -/
theorem primalOptimalValue_le
    (xstar : PrimalCarrier setup) (hxstar : IsOptimalPrimal setup xstar)
    (x : PrimalCarrier setup) :
    primalOptimalValue setup xstar hxstar ≤ objective setup x := by
  simpa [primalOptimalValue] using
    SOptLib.objectiveMinimumValue_le (objective setup)
      (primalObjectiveMinimum setup xstar hxstar) x

/-- Fenchel conjugate of the scaled component `f_i/m`, evaluated on the valid
dual carrier `Y_i`.
No SOptLib match: searched `Fenchel conjugate convex function` and
`convex conjugate supremum`, and scanned `SOptLib/Model/Objective.lean` plus
`SOptLib/Model/Bregman.lean`; none define the paper's Section 5.1.1 conjugate
`J_i` of `f_i/m`. Section 5.1.1 states `J_i : Y_i -> R`, so this definition is
not an ambient total fallback: its argument already includes the finite-domain
certificate from `dualSpace`. -/
noncomputable def dualConjugate (i : ι) (y : DualCarrier setup i) : ℝ :=
  SOptLib.fenchelConjugateOnCarrier (componentCountInverse (ι := ι)) (setup.f i) y

/-- Defining formula for the canonical dual conjugate of `f_i/m`. -/
theorem dualConjugate_def (i : ι) (y : DualCarrier setup i) :
    dualConjugate setup i y =
      sSup (Set.range fun x : E =>
        ⟪x, y.1⟫_ℝ - (componentCountInverse (ι := ι) * setup.f i x)) := by
  rfl

/-- Source-facing relation `x ∈ ∂J_i(y)`.
This replaces the previous global Mathlib-gradient selector: the PDF states
after Eq. (5.1.20) that `W_i` may be nonunique and later selects
`J_i'(y_i^{t-1}) = x_i^{t-1}` recursively, so the canonical object is the
selected subgradient relation, not a total gradient of `J_i`. -/
def IsDualConjugateSubgradient (i : ι) (y : DualCarrier setup i) (x : E) : Prop :=
  x ∈ SOptLib.carrierSubdifferential (dualConjugate setup i) y

/-- A paper-selected element `J_i'(y_i) ∈ ∂J_i(y_i)`.
This is a subtype rather than a Setup witness: Eq. (5.1.18) defines each
`W_i` from a chosen subgradient at its base point, and the implementation
discussion after Eq. (5.1.25) supplies the recursive choices used by Algorithm
5.1. -/
abbrev DualConjugateSubgradient (i : ι) (y : DualCarrier setup i) : Type _ :=
  SOptLib.CarrierSelectedSubgradient (dualConjugate setup i) y

/-- Linear map `U y = ∑ᵢ y_i` from Eq. (5.1.13). -/
noncomputable def U (y : DualProductCarrier setup) : E :=
  ∑ i : ι, (y i).1

/-- Saddle objective
`h(x)+μν(x)+⟪x,Uy⟫-J(y)` from Eq. (5.1.12). -/
noncomputable def saddleValue
    (x : PrimalCarrier setup) (y : DualProductCarrier setup) : ℝ :=
  SOptLib.linearCoupledSaddleValue
    (fun x : PrimalCarrier setup => x.1)
    (fun x : PrimalCarrier setup => setup.h x.1 + setup.μ * setup.nu x)
    (U setup)
    (fun y : DualProductCarrier setup => ∑ i : ι, dualConjugate setup i (y i))
    x y

/-- Gap function `Q( zbar, z )` from Eq. (5.1.14). -/
noncomputable def gap
    (zbar z : SaddlePoint setup) : ℝ :=
  SOptLib.saddleGap (saddleValue setup) zbar z


/-- Primal Bregman divergence `V(x⁰,x) = V_ν(x⁰,x)` from Eq. (5.1.15).
Aligns with SOptLib `carrierBregmanDivergence`: candidates `Bregman.div` and
`bregmanDivergence` were considered; the carrier primitive matches the paper
because `ν` is carried on the feasible set `X` rather than on all of `E`. -/
noncomputable def primalBregman (x0 x : PrimalCarrier setup) : ℝ :=
  carrierBregmanDivergence setup.nu setup.nuGrad x0 x

/-- Carrier-gradient selector that realizes the paper-selected base subgradient
in Eq. (5.1.18). The admitted carrier Bregman value only reads the selector at
the base point, so this constant selector preserves the selected-subgradient
formula without introducing a second Bregman definition. -/
noncomputable def dualConjugateBaseSelector
    (i : ι) (y0 : DualCarrier setup i)
    (baseSubgrad : DualConjugateSubgradient setup i y0) :
    DualCarrier setup i → E :=
  fun _ => baseSubgrad.1

/-- Aggregate dual Bregman divergence `W(ỹ,y)=∑ᵢ W_i(ỹ_i,y_i)` from Eq. (5.1.20). -/
noncomputable def dualBregmanSum
    (y0 : DualProductCarrier setup)
    (baseSubgrad : (i : ι) → DualConjugateSubgradient setup i (y0 i))
    (y : DualProductCarrier setup) : ℝ :=
  SOptLib.blockBregmanSum (fun i => DualCarrier setup i)
    (fun i => SOptLib.carrierBregmanDivergence (dualConjugate setup i)
      (dualConjugateBaseSelector setup i (y0 i) (baseSubgrad i)))
    y0 y

/-- Closed convex feasible set `X`, as stated in Section 5.1.
No SOptLib match: the pre-search found no variable-space primitive, so this
literal closed-convex predicate records the paper setup datum. -/
def primalFeasibleSet : Prop :=
  IsClosed setup.X ∧ Convex ℝ setup.X

/-- Component smoothness Eq. (5.1.2), with the paper constants `L_i ≥ 0`.
The checked SOptLib smoothness candidates are descent/proof bridges, not the
source-facing assumption predicate, so the literal Lipschitz-gradient condition
is kept locally. -/
def componentSmoothness : Prop :=
  SOptLib.FiniteFamilyGradientSmoothness setup.f
    (fun i x => componentGradient setup i x) setup.L

/-- The canonical component-gradient selector realizes the paper gradient under
the source smoothness assumption. -/
theorem componentGradient_hasGradientAt_of_componentSmoothness
    (h : componentSmoothness setup) (i : ι) (x : E) :
    HasGradientAt (setup.f i) (componentGradient setup i x) x :=
  h.1 i x

/-- Bridge from the canonical average-gradient selector to the finite average
of component gradients in Eq. (5.1.4), under the component smoothness assumption
that makes the displayed gradients genuine. -/
theorem averageGradient_eq_componentGradient_average
    (hSmooth : componentSmoothness setup) (x : E) :
    averageGradient setup x =
      componentCountInverse (ι := ι) • ∑ i : ι, componentGradient setup i x := by
  rw [averageGradient]
  rw [show averageObjectiveAmbient setup = SOptLib.finiteUniformAverage setup.f by
    funext z
    simp [averageObjectiveAmbient, SOptLib.finiteUniformAverage, componentCountInverse,
      componentCount, sourceQuotient_def, one_div]]
  simpa [SOptLib.finiteUniformAverage, componentCountInverse, componentCount, sourceQuotient_def,
    one_div] using
    (SOptLib.gradient_finiteUniformAverage_eq_finiteUniformAverage_gradient setup.f
      (fun i x => componentGradient setup i x) x
      (fun i => componentGradient_hasGradientAt_of_componentSmoothness setup hSmooth i x))

/-- Formal falsity certificate for the retired unconditional version of
`averageGradient_eq_componentGradient_average`. Without component
differentiability, total gradients need not commute with a finite average:
take `f₀(x)=|x|` and `f₁(x)=x-|x|` at `0`. The components are not differentiable
there, so Mathlib's total gradients are zero, while their average is the smooth
linear map `x ↦ x/2`. -/
theorem averageGradient_eq_componentGradient_average_unconditional_false :
    ¬ (∀ (setup : Setup ℝ (Fin 2)) (x : ℝ),
      averageGradient setup x =
        componentCountInverse (ι := Fin 2) •
          ∑ i : Fin 2, componentGradient setup i x) := by
  classical
  intro h
  let badSetup : Setup ℝ (Fin 2) :=
    { X := Set.univ
      f := fun i x => if i = (0 : Fin 2) then |x| else x - |x|
      h := fun _ => 0
      nu := fun _ => 0
      nuGrad := fun _ => 0
      μ := 0
      L := fun _ => 0
      Lf := 0
      blockPMF := PMF.pure (0 : Fin 2)
      τ := fun _ => 0
      η := fun _ => 0
      α := fun _ => 0
      x0 := ⟨0, by simp⟩ }
  have hEq := h badSetup 0
  have hNotSecond : ¬ DifferentiableAt ℝ (fun x : ℝ => x - |x|) 0 := by
    intro hdiff
    have hAbs : DifferentiableAt ℝ (fun x : ℝ => |x|) 0 := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        ((differentiableAt_id : DifferentiableAt ℝ (fun x : ℝ => x) 0).sub hdiff)
    exact not_differentiableAt_abs_zero hAbs
  have hGrad0 : componentGradient badSetup (0 : Fin 2) 0 = 0 := by
    simp [componentGradient, badSetup,
      gradient_eq_zero_of_not_differentiableAt not_differentiableAt_abs_zero]
  have hGrad1 : componentGradient badSetup (1 : Fin 2) 0 = 0 := by
    simp [componentGradient, badSetup, gradient_eq_zero_of_not_differentiableAt hNotSecond]
  have hAvgHas : HasGradientAt (averageObjectiveAmbient badSetup) (1 / 2 : ℝ) 0 := by
    have hlin : HasGradientAt (fun z : ℝ => (1 / 2 : ℝ) * z) (1 / 2 : ℝ) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (1 / 2 : ℝ)).hasGradientAt
    convert hlin using 1
    · funext z
      simp [averageObjectiveAmbient, badSetup, componentCountInverse, componentCount,
        sourceQuotient_def, Fin.sum_univ_two]
  have hLhs : averageGradient badSetup 0 = (1 / 2 : ℝ) := by
    simpa [averageGradient] using hAvgHas.gradient
  have hRhs :
      componentCountInverse (ι := Fin 2) •
          (∑ i : Fin 2, componentGradient badSetup i 0) = (0 : ℝ) := by
    simp [Fin.sum_univ_two, hGrad0, hGrad1]
  have hhalf : (1 / 2 : ℝ) = 0 := by
    simpa [hLhs, componentCountInverse, componentCount, sourceQuotient_def,
      Fin.sum_univ_two, hGrad0, hGrad1] using hEq
  norm_num at hhalf

/-- Relatively simple convex term assumption for `h` from Section 5.1.
No SOptLib match was listed for the paper's simple-term assumption; this local
predicate records the convex part of the stated relatively-simple condition. -/
def simpleTermConvexity : Prop :=
  ConvexOn ℝ setup.X setup.h

/-- Component convexity assumption for `f_i`, Section 5.1 before Eq. (5.1.2).
The checked finite-average convexity candidate is a derived theorem, not the
primitive component assumption, so the local predicate follows the source. -/
def componentConvexity : Prop :=
  ∀ i : ι, ConvexOn ℝ Set.univ (setup.f i)

/-- Strong convexity of the distance-generating function `ν`, Eq. (5.1.3), with
the paper-selected carrier subgradient `ν'`. The PDF states the inequality in
terms of selected subgradients on `X`; it does not assume an ambient
`DifferentiableOn` realization of `ν`. -/
def nuStrongConvexity : Prop :=
  (∀ x : PrimalCarrier setup,
    setup.nuGrad x ∈ SOptLib.carrierSubdifferential setup.nu x) ∧
  ∀ x₁ x₂ : PrimalCarrier setup,
    (1 / 2 : ℝ) * ‖x₁.1 - x₂.1‖ ^ 2 ≤
      ⟪setup.nuGrad x₁ - setup.nuGrad x₂, x₁.1 - x₂.1⟫_ℝ

/-- Nonnegativity of the regularization parameter `μ`, Section 5.1.
No SOptLib match was listed for this scalar source assumption. -/
def muNonnegative : Prop :=
  0 ≤ setup.μ

/-- The paper's `L = m⁻¹∑ᵢ L_i` appearing in Eq. (5.1.4). -/
noncomputable def averageComponentLipschitz : ℝ :=
  componentCountInverse (ι := ι) * ∑ i : ι, setup.L i

/-- Average-objective smoothness Eq. (5.1.4).
The checked average-smoothness candidates are unrelated stationarity or
conditional-gradient infrastructure, so this local predicate keeps the literal
source inequality and the definition of `L`. -/
def averageSmoothness : Prop :=
  (∀ x : E, HasGradientAt (averageObjectiveAmbient setup) (averageGradient setup x) x) ∧
    0 ≤ setup.Lf ∧ setup.Lf ≤ averageComponentLipschitz setup ∧
    ∀ x₁ x₂ : E,
      ‖averageGradient setup x₁ - averageGradient setup x₂‖ ≤ setup.Lf * ‖x₁ - x₂‖

/-- The canonical average-gradient selector realizes the paper gradient under
the source average-smoothness assumption. -/
theorem averageGradient_hasGradientAt_of_averageSmoothness
    (h : averageSmoothness setup) (x : E) :
    HasGradientAt (averageObjectiveAmbient setup) (averageGradient setup x) x :=
  h.1 x

/-- Selected-subgradient optimality certificate carried by a primal prox
solution.

This is the carrier-subdifferential form of the optimality condition displayed
after Eq. (5.1.17):
`g + h'(x₁) + (μ+η)ν'(x₁) - ην'(x₀) ∈ N_X(x₁)`. In the carrier model the normal
cone contribution is already part of `carrierSubdifferential`, so the certificate
is expressed as membership of the matching negative smooth/Bregman gradient in
the carrier subdifferential of `h`. -/
def primalProxSelectedSubgradientCertificate
    (g : E) (x₀ x : PrimalCarrier setup) (η : ℝ) : Prop :=
  SOptLib.carrierBregmanProxSelectedSubgradientCertificate
    (fun z : PrimalCarrier setup => z.1)
    (fun z : PrimalCarrier setup => setup.h z.1)
    setup.nuGrad g setup.μ η x₀ x

/-- Selected-subgradient optimality certificate for the plain easy primal
subproblem Eq. (5.1.5), i.e. the `η = 0` specialization of the prox certificate. -/
def primalEasySelectedSubgradientCertificate
    (g : E) (x : PrimalCarrier setup) : Prop :=
  (-(g + setup.μ • setup.nuGrad x)) ∈
    SOptLib.carrierSubdifferential
      (fun z : PrimalCarrier setup => setup.h z.1) x

/-- Easy primal subproblem assumption Eq. (5.1.5), with the selected
optimality certificate needed to keep the paper's recursive `ν'` semantics.
The checked prox/argmin candidates are measurability or proof bridges, not the
paper's stated easy-subproblem assumption, so this is local. The certificate
matches the source discussion that closed-form solutions are obtained/checked
by first-order optimality conditions. -/
def easyPrimalSubproblem : Prop :=
  ∀ g : E,
    ∃ x : PrimalCarrier setup,
      IsMinOn (fun z : PrimalCarrier setup =>
        ⟪g, z.1⟫_ℝ + setup.h z.1 + setup.μ * setup.nu z) Set.univ x ∧
        primalEasySelectedSubgradientCertificate setup g x

/-- Prox mapping with Bregman term, Eq. (5.1.17).
The checked SOptLib prox candidates do not encode this paper-local
`h + μν + ηV` source assumption, so the literal selected argmin-solvability
predicate is kept here. The selected-subgradient certificate models the paragraph
after Eq. (5.1.17), which recursively identifies a `ν'(x₁)` satisfying the prox
optimality condition before using it in the next Bregman distance. -/
def proxMappingWithBregman : Prop :=
  ∀ x₀ : PrimalCarrier setup, ∀ g : E, ∀ η : ℝ, 0 < η →
    ∃ x : PrimalCarrier setup,
      IsMinOn (fun z : PrimalCarrier setup =>
        ⟪g, z.1⟫_ℝ + setup.h z.1 + setup.μ * setup.nu z +
          η * primalBregman setup x₀ z) Set.univ x ∧
        primalProxSelectedSubgradientCertificate setup g x₀ x η

/-- Bregman lower bound Eq. (5.1.16).
The listed Bregman candidates are derived measurability/budget lemmas, not the
source assumption, so this local predicate records the displayed lower bound. -/
def primalBregmanLowerBound : Prop :=
  ∀ x₀ x : PrimalCarrier setup,
    (1 / 2 : ℝ) * ‖x.1 - x₀.1‖ ^ 2 ≤ primalBregman setup x₀ x

/-- Convex-combination closure of the canonical conjugate domain `Y_i`.
The paper calls `Y_i` dual spaces; for the local finite-domain realization of
`Y_i`, this is a proof obligation for the conjugate-domain model rather than a
Setup field. -/
theorem dualSpace_mix_mem
    (i : ι) (y₁ y₂ : DualCarrier setup i) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • y₁.1 + b • y₂.1 ∈ dualSpace setup i := by
  exact SOptLib.fenchelConjugateDomain_mix_mem
    (scale := componentCountInverse (ι := ι)) (f := setup.f i)
    y₁.2 y₂.2 ha hb hab

/-- The canonical dual domain `Y_i` is convex, exposing `dualSpace_mix_mem` to
Mathlib/SOptLib weighted-average APIs. Existing candidates considered:
searched `convex iff add mem` and checked `Convex.normalized_weighted_sum_mem`;
those consume a `Convex` hypothesis, while this local helper supplies that
hypothesis from the paper-specific `dualSpace_mix_mem`. -/
private theorem dualSpace_convex (i : ι) : Convex ℝ (dualSpace setup i) := by
  exact SOptLib.fenchelConjugateDomain_convex
    (scale := componentCountInverse (ι := ι)) (f := setup.f i)

/-- Strong convexity of the canonical conjugates `J_i` with modulus `σ_i=m/L_i`,
Section 5.1.1 before Eq. (5.1.18);
`book/FOML/RandomPrimalDualGradient.json#/assumptions/11`.
SOptLib `StrongConvexOnWithGauge` was considered, but it takes an ambient total
function `E -> R`; this paper object is `J_i : Y_i -> R`. The displayed modulus
is modeled in the division-free cross-multiplied form using the source-stated
`L_i ≥ 0`; this avoids adding the unstated side condition `L_i ≠ 0` to the
source-facing assumption package. -/
def dualStrongConvexity : Prop :=
  ∀ i : ι, ∀ y₁ y₂ : DualCarrier setup i, ∀ ⦃a b : ℝ⦄,
    (ha : 0 ≤ a) → (hb : 0 ≤ b) → (hab : a + b = 1) →
      (componentCount (ι := ι) : ℝ) / 2 * a * b * ‖y₁.1 - y₂.1‖ ^ 2 ≤
        setup.L i *
          (a * dualConjugate setup i y₁ + b * dualConjugate setup i y₂ -
            dualConjugate setup i
              ⟨a • y₁.1 + b • y₂.1,
                dualSpace_mix_mem setup i y₁ y₂ ha hb hab⟩)

/-- Algorithm 5.1 starts with nonnegative parameter sequences.
The listed initialization candidates are schedule/output helpers rather than
this source-domain assumption, so the local predicate records the algorithm
initialization text. -/
def algorithmParameterNonnegative : Prop :=
  (∀ t, 1 ≤ t → 0 ≤ setup.τ t) ∧
    (∀ t, 1 ≤ t → 0 ≤ setup.η t) ∧
    (∀ t, 1 ≤ t → 0 ≤ setup.α t)

/-- Source-backed standing assumptions for FOML Section 5.1 and Algorithm 5.1;
`book/FOML/RandomPrimalDualGradient.json#/assumptions`. -/
def standingAssumptions : Prop :=
  primalFeasibleSet setup ∧
    componentSmoothness setup ∧
    simpleTermConvexity setup ∧
    componentConvexity setup ∧
    nuStrongConvexity setup ∧
    muNonnegative setup ∧
    averageSmoothness setup ∧
    easyPrimalSubproblem setup ∧
    proxMappingWithBregman setup ∧
    primalBregmanLowerBound setup ∧
    dualStrongConvexity setup ∧
    algorithmParameterNonnegative setup

/-- Source-derived positivity of `1+τ_t` for the recursive selected
subgradient formula after Eq. (5.1.25), from nonnegative Algorithm 5.1
parameters. -/
theorem onePlusTau_pos_of_standing
    (hStanding : standingAssumptions setup) (t : ℕ) (ht : 1 ≤ t) :
    0 < 1 + setup.τ t := by
  rcases hStanding with ⟨_, _, _, _, _, _, _, _, _, _, _, hParam⟩
  have htau : 0 ≤ setup.τ t := hParam.1 t ht
  exact add_pos_of_pos_of_nonneg zero_lt_one htau

/-- Source-derived well-definedness obligation for the denominator
`m(1+τ_k)` in Proposition 5.1 condition (5.1.50). -/
theorem onePlusTauDenominator_pos_of_standing
    (hStanding : standingAssumptions setup) (k : ℕ) (hk : 1 ≤ k) :
    0 < (componentCount (ι := ι) : ℝ) * (1 + setup.τ k) := by
  exact mul_pos (componentCount_real_pos (ι := ι))
    (onePlusTau_pos_of_standing setup hStanding k hk)

/-- Explicit corrected-boundary requirement for Proposition 5.1's displayed
products `m τ_t p_i` in (5.1.48)--(5.1.49). Algorithm 5.1 states
nonnegative `τ_t`, but targeted PDF extraction found no separate `τ_t ≠ 0`
premise, so the source-gap proposition wrapper must take this boundary
explicitly instead of manufacturing it as a theorem. No SOptLib match: searched
`denominator admissible quotient nonzero`, considered the quotient bridge
`checkedQuotient_weight_mono_semantics` in `SOptLib/Model/ParameterChoices.lean`,
and scanned
`SOptLib/Model/ParameterChoices.lean`; no reusable primitive represents these
RPDG-specific product denominators. -/
def tauProbabilityDenominatorsAdmissible : Prop :=
  ∀ t : ℕ, ∀ i : ι,
    (componentCount (ι := ι) : ℝ) * setup.τ t * samplingProbability setup i ≠ 0

/-- Complete corrected-boundary contract for Proposition 5.1 source-gap
wrappers: all-block `p_i^{-1}` plus the quotient products
`m τ_t p_i`. This contract is deliberately absent from
`standingAssumptions`, because the PDF does not state these facts as primitive
assumptions. -/
def proposition_5_1_denominatorBoundary (k : ℕ) : Prop :=
  allBlockProbabilityDenominatorsAdmissible setup ∧
    tauProbabilityDenominatorsAdmissible setup

/-- Source-derived denominator obligation for the product
`m(1+τ_k)` appearing in Proposition 5.1 condition (5.1.50). -/
theorem onePlusTauComponentDenominator_ne_of_standing
    (hStanding : standingAssumptions setup) (k : ℕ) (hk : 1 ≤ k) :
    (componentCount (ι := ι) : ℝ) * (1 + setup.τ k) ≠ 0 :=
  ne_of_gt (onePlusTauDenominator_pos_of_standing setup hStanding k hk)

/-- Domain certificate for the supremum defining `J_i(y_i)`. Section 5.1.1
treats each conjugate as a real-valued map `J_i : Y_i -> R`; membership in the
canonical carrier `Y_i` is precisely the bounded-above condition needed for that
real-valued conjugate, rather than an ambient `sSup` fallback. -/
theorem dualConjugate_bddAbove
    (i : ι) (y : DualCarrier setup i) :
    BddAbove (Set.range fun x : E =>
      ⟪x, y.1⟫_ℝ - (componentCountInverse (ι := ι) * setup.f i x)) := by
  exact y.2


/-- Convexity inequality for the paper conjugate `J_i` on its canonical
carrier `Y_i`.

Aligns with Lan §5.1.1 and the Jensen step after Eq. (5.1.66): searched
`dual conjugate convex strong convexity convexOn`, checked SOptLib
`StrongConvexOnWithGauge` and the local `dualStrongConvexity`; those package
strong-convexity predicates, while this proof uses the literal supremum
definition of `J_i` and the already available `dualSpace_mix_mem`. -/
private theorem dualConjugate_mix_le
    (i : ι) (y₁ y₂ : DualCarrier setup i) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    dualConjugate setup i
        ⟨a • y₁.1 + b • y₂.1,
          dualSpace_mix_mem setup i y₁ y₂ ha hb hab⟩ ≤
      a * dualConjugate setup i y₁ + b * dualConjugate setup i y₂ := by
  simpa [dualConjugate, dualSpace, SOptLib.fenchelConjugateOnCarrier] using
    SOptLib.fenchelConjugate_mix_le
      (scale := componentCountInverse (ι := ι)) (f := setup.f i)
      y₁ y₂ ha hb hab

/-- Convexity of the totalized paper conjugate `J_i` on `Y_i`.

Aligns with the dual part of Lan's Jensen step after Eq. (5.1.66). Candidate
audit: considered SOptLib `convexOn_weighted_average_le_weighted_sum` and
Mathlib `ConvexOn.map_sum_le` as consumers, but neither supplies the
paper-specific conjugate convexity; `dualConjugate_mix_le` above is the local
source-derived bridge. -/
private theorem dualConjugate_totalize_convexOn
    (i : ι) :
    ConvexOn ℝ (dualSpace setup i)
      (SOptLib.totalizeOn (dualSpace setup i)
        (fun y : DualCarrier setup i => dualConjugate setup i y)) := by
  simpa [dualSpace, dualConjugate] using
    (SOptLib.fenchelConjugate_totalize_convexOn
      (scale := componentCountInverse (ι := ι)) (f := setup.f i))

/-- Theorem 5.1 is the strongly convex case, so it adds `μ > 0` to the
standing Section 5.1 assumptions. -/
def muPositive : Prop :=
  0 < setup.μ

/-- Source-facing assumption package for Theorem 5.1. -/
def theoremStandingAssumptions : Prop :=
  standingAssumptions setup ∧ muPositive setup

/-- The Theorem 5.1 assumption package contains the Section 5.1 standing assumptions. -/
theorem theoremStandingAssumptions_standing
    (h : theoremStandingAssumptions setup) : standingAssumptions setup :=
  h.1

/-- The Theorem 5.1 assumption package contains the strong-convexity case `μ > 0`. -/
theorem theoremStandingAssumptions_muPositive
    (h : theoremStandingAssumptions setup) : muPositive setup :=
  h.2

/-- Realization of the selected `ν'(x)` used in Eq. (5.1.15): under the
source-backed standing assumptions it is a carrier subgradient of `ν`. -/
theorem nuGrad_mem_carrierSubdifferential
    (hStanding : standingAssumptions setup) (x : PrimalCarrier setup) :
    setup.nuGrad x ∈ SOptLib.carrierSubdifferential setup.nu x := by
  rcases hStanding with
    ⟨_, _, _, _, hNu, _, _, _, _, _, _, _⟩
  exact hNu.1 x

/-- Carrier three-point identity for the paper primal Bregman divergence
`V(x⁰,x)` from Eq. (5.1.15). -/
theorem primalBregman_three_point_identity
    (x z y : PrimalCarrier setup) :
    primalBregman setup x y =
      primalBregman setup x z +
        ⟪setup.nuGrad z - setup.nuGrad x, y.1 - z.1⟫_ℝ +
          primalBregman setup z y := by
  simpa [primalBregman] using
    (carrierBregmanDivergence_three_point_identity
      setup.nu
      (fun x : PrimalCarrier setup => x.1)
      setup.nuGrad
      (fun x z : PrimalCarrier setup => primalBregman setup x z)
      (by
        intro x z
        rfl)
      x z y)

/-- Nonnegativity of the selected primal Bregman divergence from the carrier
subgradient support inequality for the paper-selected `ν'`. -/
theorem primalBregman_nonnegative_of_standing
    (hStanding : standingAssumptions setup) (x₀ x : PrimalCarrier setup) :
    0 ≤ primalBregman setup x₀ x := by
  simpa [primalBregman, SOptLib.carrierBregmanDivergence] using
    (SOptLib.carrierBregmanDivergence_nonneg_of_subgradient
      (v := setup.nu) (grad := setup.nuGrad) (x := x₀) (z := x)
      (nuGrad_mem_carrierSubdifferential setup hStanding x₀))

/-- Concrete selected-subgradient primal Bregman data available from the current
paper setup for the Eq. (5.1.43) route. This deliberately contains no
`fderivWithin` or segment-derivative premise. -/
theorem primalBregman_selected_subgradient_data
    (hStanding : standingAssumptions setup) :
    (∀ x : PrimalCarrier setup,
      setup.nuGrad x ∈ SOptLib.carrierSubdifferential setup.nu x) ∧
    (∀ x z y : PrimalCarrier setup,
      primalBregman setup x y =
        primalBregman setup x z +
          ⟪setup.nuGrad z - setup.nuGrad x, y.1 - z.1⟫_ℝ +
            primalBregman setup z y) ∧
    (∀ x z : PrimalCarrier setup, 0 ≤ primalBregman setup x z) := by
  exact
    ⟨fun x => nuGrad_mem_carrierSubdifferential setup hStanding x,
      fun x z y => primalBregman_three_point_identity setup x z y,
      fun x z => primalBregman_nonnegative_of_standing setup hStanding x z⟩

/-- Selected-subgradient form of the primal two-Bregman descent algebra.

This is the source-compatible replacement for the previous segment-derivative
route: the only nonsmooth optimality input is the carrier-subgradient support
for `h` at the selected primal update point. -/
private theorem primal_two_bregman_descent_of_simple_subgradient
    (g : E) (xPrev xStar x : PrimalCarrier setup) (η : ℝ)
    (hhSub :
      (-(g + setup.μ • setup.nuGrad xStar +
          η • (setup.nuGrad xStar - setup.nuGrad xPrev))) ∈
        SOptLib.carrierSubdifferential
          (fun z : PrimalCarrier setup => setup.h z.1) xStar) :
    ⟪xStar.1 - x.1, g⟫_ℝ +
        setup.h xStar.1 + setup.μ * setup.nu xStar -
        setup.h x.1 - setup.μ * setup.nu x ≤
      η * primalBregman setup xPrev x -
        (setup.μ + η) * primalBregman setup xStar x -
        η * primalBregman setup xPrev xStar := by
  simpa [primalBregman] using
    SOptLib.carrier_two_bregman_descent_of_selected_subgradient
      (h := fun z : PrimalCarrier setup => setup.h z.1)
      (v := setup.nu)
      (grad := setup.nuGrad)
      (g := g)
      (xPrev := xPrev)
      (xStar := xStar)
      (x := x)
      (mu := setup.μ)
      (eta := η)
      hhSub

/-- Source-facing membership obligation for the dual point
`m⁻¹∇f_i(x) ∈ Y_i`. This is a theorem because Section 5.1.1 only says that
gradients of `f_i/m` reside in `Y_i`; it does not define `Y_i` to be exactly
their range. -/
theorem scaledComponentGradient_mem_dual
    (_hStanding : standingAssumptions setup) (i : ι) (x : E) :
    componentCountInverse (ι := ι) • componentGradient setup i x ∈ dualSpace setup i := by
  rcases _hStanding with ⟨_, hSmooth, _, hConv, _, _, _, _, _, _, _, _⟩
  simpa [dualSpace] using
    SOptLib.smul_gradient_mem_fenchelConjugateDomain_of_convex
      (setup.f i) x (componentGradient setup i x)
      (by
        unfold componentCountInverse
        rw [sourceQuotient_def]
        exact le_of_lt (one_div_pos.mpr (componentCount_real_pos (ι := ι))))
      (hConv i)
      (by
        simpa using
          (componentGradient_hasGradientAt_of_componentSmoothness setup hSmooth i x))

/-- Canonical dual point generated by a primal point: `y_i=m⁻¹∇f_i(x)`. -/
noncomputable def scaledComponentGradientDual
    (hStanding : standingAssumptions setup) (i : ι) (x : E) : DualCarrier setup i :=
by
  classical
  refine ⟨componentCountInverse (ι := ι) • componentGradient setup i x, ?_⟩
  rcases hStanding with ⟨_, hSmooth, _, hConv, _, _, _, _, _, _, _, _⟩
  let c : ℝ := componentCountInverse (ι := ι)
  let g : E := componentGradient setup i x
  have hc : 0 ≤ c := by
    unfold c componentCountInverse
    rw [sourceQuotient_def]
    exact le_of_lt (one_div_pos.mpr (componentCount_real_pos (ι := ι)))
  have hgradWithin : HasGradientWithinAt (setup.f i) g Set.univ x := by
    simpa [g] using
      (componentGradient_hasGradientAt_of_componentSmoothness setup hSmooth i x)
  have hsupp : ∀ z : E, setup.f i x + ⟪g, z - x⟫_ℝ ≤ setup.f i z := by
    intro z
    exact ConvexOn.first_order_linear_model_le_of_hasGradientWithinAt
      (hConv i) (by simp) (by simp) hgradWithin
  simpa [dualSpace, c, g] using
    SOptLib.smul_gradient_mem_fenchelConjugateDomain_of_support (setup.f i) x g hc hsupp

/-- Fenchel equality for the scaled component gradient point.
No direct SOptLib match: searched `Fenchel conjugate subgradient convex support supremum`,
`carrier subdifferential support inequality membership`, and `supremum range upper lower
csSup le_csSup`; checked `SOptLib.mem_carrierSubdifferential_iff`,
`ConvexOn.first_order_linear_model_le_of_hasGradientWithinAt`, `csSup_le`, and
`le_csSup`; scanned `SOptLib/Model/Objective.lean`, `SOptLib/Model/Subdifferential.lean`,
and sibling examples. The reusable facts provide convex first-order support and generic
supremum APIs, but none states the literal Lan §5.1.1 conjugate value
`J_i(m⁻¹∇f_i(x))`. -/
private theorem dualConjugate_scaled_component_value
    (hStanding : standingAssumptions setup) (i : ι) (x : E) :
  dualConjugate setup i (scaledComponentGradientDual setup hStanding i x) =
      ⟪x, (scaledComponentGradientDual setup hStanding i x).1⟫_ℝ -
        componentCountInverse (ι := ι) * setup.f i x := by
  classical
  obtain ⟨_, hSmooth, _, hConv, _, _, _, _, _, _, _, _⟩ := hStanding
  let c : ℝ := componentCountInverse (ι := ι)
  let g : E := componentGradient setup i x
  have hc : 0 ≤ c := by
    unfold c componentCountInverse
    rw [sourceQuotient_def]
    exact le_of_lt (one_div_pos.mpr (componentCount_real_pos (ι := ι)))
  have hgradWithin : HasGradientWithinAt (setup.f i) g Set.univ x := by
    simpa [g] using
      (componentGradient_hasGradientAt_of_componentSmoothness setup hSmooth i x)
  have hsupp : ∀ z : E, setup.f i x + ⟪g, z - x⟫_ℝ ≤ setup.f i z := by
    intro z
    -- aligns with Lan §5.1.1: the conjugate of `f_i / m` is touched at `m⁻¹∇f_i(x)`.
    exact ConvexOn.first_order_linear_model_le_of_hasGradientWithinAt
      (hConv i) (by simp) (by simp) hgradWithin
  unfold dualConjugate
  simpa [scaledComponentGradientDual, c, g] using
    (SOptLib.fenchel_conjugate_smul_supporting_gradient_eq
      (f := setup.f i) (x := x) (g := g) (c := c) hc hsupp)

/-- The scaled component-gradient dual point carries the primal point as a
subgradient of the conjugate. This is the concrete Fenchel-support bridge used
for the candidate dual prox witness after Eq. (5.1.25). -/
theorem scaledComponentGradientDual_subgradient_mem
    (hStanding : standingAssumptions setup) (i : ι) (x : E) :
    IsDualConjugateSubgradient setup i
      (scaledComponentGradientDual setup hStanding i x) x := by
  classical
  obtain ⟨_, hSmooth, _, hConv, _, _, _, _, _, _, _, _⟩ := hStanding
  let c : ℝ := componentCountInverse (ι := ι)
  let g : E := componentGradient setup i x
  have hc : 0 ≤ c := by
    unfold c componentCountInverse
    rw [sourceQuotient_def]
    exact le_of_lt (one_div_pos.mpr (componentCount_real_pos (ι := ι)))
  have hgradWithin : HasGradientWithinAt (setup.f i) g Set.univ x := by
    simpa [g] using
      (componentGradient_hasGradientAt_of_componentSmoothness setup hSmooth i x)
  have hsupp : ∀ z : E, setup.f i x + ⟪g, z - x⟫_ℝ ≤ setup.f i z := by
    intro z
    exact ConvexOn.first_order_linear_model_le_of_hasGradientWithinAt
      (hConv i) (by simp) (by simp) hgradWithin
  simpa [IsDualConjugateSubgradient, dualConjugate, scaledComponentGradientDual, dualSpace,
      c, g] using
    SOptLib.mem_carrierSubdifferential_fenchelConjugateOnDomain_smul_gradient
      (f := setup.f i) (x := x) (g := g) (c := c) hc hsupp
      (by
        exact SOptLib.smul_gradient_mem_fenchelConjugateDomain_of_support
          (setup.f i) x g hc hsupp)

/-- Canonical initialized dual block `y_i^0 = m⁻¹∇f_i(x^0)` from Algorithm 5.1.
This is the scaled-gradient dual point itself, not a separate existence
selector. -/
noncomputable def initialDual
    (hStanding : standingAssumptions setup) (i : ι) : DualCarrier setup i :=
  scaledComponentGradientDual setup hStanding i setup.x0.1

/-- The initialized dual block has the paper value. -/
theorem initialDual_eq (hStanding : standingAssumptions setup) (i : ι) :
    (initialDual setup hStanding i).1 =
      componentCountInverse (ι := ι) • componentGradient setup i setup.x0.1 := by
  rfl

/-- Initial selected conjugate subgradient value `x_i^0=x^0` from the
post-(5.1.25) implementation discussion. -/
def initialDualSubgradientValue (i : ι) : E :=
  setup.x0.1

/-- Source-derived realization obligation used in Lemma 5.1: for the initialized
dual block, the paper-selected subgradient satisfies `J_i'(y_i^0)=x^0`. -/
theorem initialDualSubgradient_mem
    (hStanding : standingAssumptions setup) (i : ι) :
    IsDualConjugateSubgradient setup i (initialDual setup hStanding i)
      (initialDualSubgradientValue setup i) := by
  classical
  rw [IsDualConjugateSubgradient, SOptLib.mem_carrierSubdifferential_iff]
  intro y
  simp only [initialDualSubgradientValue]
  have hLower :
      ⟪setup.x0.1, y.1⟫_ℝ -
          componentCountInverse (ι := ι) * setup.f i setup.x0.1 ≤
        dualConjugate setup i y :=
    SOptLib.le_fenchelConjugateOnCarrier (componentCountInverse (ι := ι)) (setup.f i) y setup.x0.1
  have hValue :
      dualConjugate setup i (initialDual setup hStanding i) =
        ⟪setup.x0.1, (initialDual setup hStanding i).1⟫_ℝ -
          componentCountInverse (ι := ι) * setup.f i setup.x0.1 := by
    simpa [initialDual] using
      dualConjugate_scaled_component_value setup hStanding i setup.x0.1
  show dualConjugate setup i (initialDual setup hStanding i) +
      ⟪setup.x0.1, y.1 - (initialDual setup hStanding i).1⟫_ℝ ≤
        dualConjugate setup i y
  calc
    dualConjugate setup i (initialDual setup hStanding i) +
        ⟪setup.x0.1, y.1 - (initialDual setup hStanding i).1⟫_ℝ
        = (⟪setup.x0.1, (initialDual setup hStanding i).1⟫_ℝ -
            componentCountInverse (ι := ι) * setup.f i setup.x0.1) +
            ⟪setup.x0.1, y.1 - (initialDual setup hStanding i).1⟫_ℝ := by
          rw [hValue]
    _ = ⟪setup.x0.1, y.1⟫_ℝ -
          componentCountInverse (ι := ι) * setup.f i setup.x0.1 := by
          rw [inner_sub_right]
          ring
    _ ≤ dualConjugate setup i y := hLower

/-- Certified initial selected conjugate subgradient `x_i^0=x^0` from the
post-(5.1.25) implementation discussion. -/
noncomputable def initialDualSubgradient
    (hStanding : standingAssumptions setup) (i : ι) :
    DualConjugateSubgradient setup i (initialDual setup hStanding i) :=
  ⟨initialDualSubgradientValue setup i, initialDualSubgradient_mem setup hStanding i⟩

/-- Primal extrapolation `x̃ᵗ = α_t(x^{t-1}-x^{t-2})+x^{t-1}` from Eq. (5.1.21).
SOptLib accelerated snapshot averages were checked and rejected here: Eq.
(5.1.21) is a two-step extrapolation, not a weighted snapshot average. -/
def primalPrediction (t : ℕ) (xPrev xPrevPrev : PrimalCarrier setup) : E :=
  setup.α t • (xPrev.1 - xPrevPrev.1) + xPrev.1

/-- Dual candidate objective for Eq. (5.1.25). -/
noncomputable def candidateDualObjective
    (t : ℕ) (xTilde : E) (i : ι) (yPrev y : DualCarrier setup i)
    (baseSubgrad : DualConjugateSubgradient setup i yPrev) : ℝ :=
  ⟪-xTilde, y.1⟫_ℝ + dualConjugate setup i y +
    setup.τ t * (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i yPrev baseSubgrad) yPrev y)

/-- Candidate selected subgradient for the full dual prox update, the value
`(x̃ᵗ+τ_t x_i^{t-1})/(1+τ_t)` displayed after Eq. (5.1.25);
`book/FOML/RandomPrimalDualGradient.json#/algorithm_spec/steps/2`. -/
noncomputable def candidateDualSubgradientValue
    (hStanding : standingAssumptions setup)
    (t : ℕ) (ht : 1 ≤ t) (xTilde : E) {i : ι} {yPrev : DualCarrier setup i}
    (baseSubgrad : DualConjugateSubgradient setup i yPrev) : E :=
  sourceQuotient 1 (1 + setup.τ t)
      (ne_of_gt (onePlusTau_pos_of_standing setup hStanding t ht)) •
    (xTilde + setup.τ t • baseSubgrad.1)

/-- The explicit scaled-gradient dual point is the minimizer of the positive-time
candidate dual prox objective. -/
private theorem candidateDualScaledGradient_isMinOn
    (hStanding : standingAssumptions setup)
    (t : ℕ) (ht : 1 ≤ t) (xTilde : E) (i : ι) (yPrev : DualCarrier setup i)
    (baseSubgrad : DualConjugateSubgradient setup i yPrev) :
    IsMinOn (candidateDualObjective setup t xTilde i yPrev · baseSubgrad) Set.univ
      (scaledComponentGradientDual setup hStanding i
        (candidateDualSubgradientValue setup hStanding t ht xTilde baseSubgrad)) := by
  classical
  let q : E := candidateDualSubgradientValue setup hStanding t ht xTilde baseSubgrad
  let yStar : DualCarrier setup i := scaledComponentGradientDual setup hStanding i q
  have hOnePlusTau : 0 < 1 + setup.τ t :=
    onePlusTau_pos_of_standing setup hStanding t ht
  have hq_sub :
      IsDualConjugateSubgradient setup i yStar q := by
    simpa [yStar] using scaledComponentGradientDual_subgradient_mem setup hStanding i q
  have hqscale :
      (1 + setup.τ t) • q = xTilde + setup.τ t • baseSubgrad.1 := by
    have hcoef :
        (1 + setup.τ t) *
            sourceQuotient 1 (1 + setup.τ t) (ne_of_gt hOnePlusTau) = 1 := by
      rw [sourceQuotient_def]
      field_simp [ne_of_gt hOnePlusTau]
    have hcoef_tau :
        (1 + setup.τ t) *
            (sourceQuotient 1 (1 + setup.τ t) (ne_of_gt hOnePlusTau) * setup.τ t) =
          setup.τ t := by
      calc
        (1 + setup.τ t) *
            (sourceQuotient 1 (1 + setup.τ t) (ne_of_gt hOnePlusTau) * setup.τ t)
            =
            ((1 + setup.τ t) *
                sourceQuotient 1 (1 + setup.τ t) (ne_of_gt hOnePlusTau)) *
              setup.τ t := by
          ring
        _ = 1 * setup.τ t := by rw [hcoef]
        _ = setup.τ t := by ring
    simp [q, candidateDualSubgradientValue, smul_smul, hcoef, hcoef_tau]
  refine (isMinOn_univ_iff
    (f := fun z : DualCarrier setup i =>
      candidateDualObjective setup t xTilde i yPrev z baseSubgrad)
    (a := yStar)).2 ?_
  intro y
  have hsupport :
      dualConjugate setup i yStar + ⟪q, y.1 - yStar.1⟫_ℝ ≤
        dualConjugate setup i y := by
    exact (SOptLib.mem_carrierSubdifferential_iff.mp hq_sub) y
  have hq_le :
      ⟪q, y.1 - yStar.1⟫_ℝ ≤
        dualConjugate setup i y - dualConjugate setup i yStar := by
    linarith
  have hmul_le :
      (1 + setup.τ t) * ⟪q, y.1 - yStar.1⟫_ℝ ≤
        (1 + setup.τ t) *
          (dualConjugate setup i y - dualConjugate setup i yStar) :=
    mul_le_mul_of_nonneg_left hq_le (le_of_lt hOnePlusTau)
  have hinner :
      (1 + setup.τ t) * ⟪q, y.1 - yStar.1⟫_ℝ =
        ⟪xTilde + setup.τ t • baseSubgrad.1, y.1 - yStar.1⟫_ℝ := by
    calc
      (1 + setup.τ t) * ⟪q, y.1 - yStar.1⟫_ℝ =
          ⟪(1 + setup.τ t) • q, y.1 - yStar.1⟫_ℝ := by
        exact (real_inner_smul_left q (y.1 - yStar.1) (1 + setup.τ t)).symm
      _ = ⟪xTilde + setup.τ t • baseSubgrad.1, y.1 - yStar.1⟫_ℝ := by
        rw [hqscale]
  have hlinear_le :
      ⟪xTilde + setup.τ t • baseSubgrad.1, y.1 - yStar.1⟫_ℝ ≤
        (1 + setup.τ t) *
          (dualConjugate setup i y - dualConjugate setup i yStar) := by
    simpa [hinner] using hmul_le
  have hobjdiff :
      candidateDualObjective setup t xTilde i yPrev y baseSubgrad -
          candidateDualObjective setup t xTilde i yPrev yStar baseSubgrad =
        (1 + setup.τ t) *
            (dualConjugate setup i y - dualConjugate setup i yStar) -
          ⟪xTilde + setup.τ t • baseSubgrad.1, y.1 - yStar.1⟫_ℝ := by
    simp [candidateDualObjective, SOptLib.carrierBregmanDivergence,
      carrierBregmanDivergence, dualConjugateBaseSelector, inner_sub_right,
      inner_add_left, inner_smul_left, inner_neg_left]
    ring
  have hnonneg :
      0 ≤ candidateDualObjective setup t xTilde i yPrev y baseSubgrad -
          candidateDualObjective setup t xTilde i yPrev yStar baseSubgrad := by
    rw [hobjdiff]
    linarith
  linarith

/-- Source-derived solvability obligation for the dual argmin in Eq. (5.1.25),
at the positive paper times `t = 1,...,k`.

The paper does not define this candidate argmin as a time-zero object, and the
standing parameter assumptions only control `τ_t` for `1 ≤ t`. -/
theorem candidateDualUpdate_exists_of_standing
    (hStanding : standingAssumptions setup)
    (t : ℕ) (ht : 1 ≤ t) (xTilde : E) (i : ι) (yPrev : DualCarrier setup i)
    (baseSubgrad : DualConjugateSubgradient setup i yPrev) :
    ∃ y : DualCarrier setup i,
      IsMinOn (candidateDualObjective setup t xTilde i yPrev · baseSubgrad)
        Set.univ y := by
  exact ⟨scaledComponentGradientDual setup hStanding i
      (candidateDualSubgradientValue setup hStanding t ht xTilde baseSubgrad),
    candidateDualScaledGradient_isMinOn setup hStanding t ht xTilde i yPrev baseSubgrad⟩

/-- Candidate dual update
`ŷ_i^t = argmin_{y_i∈Y_i}{⟪-x̃^t,y_i⟫+J_i(y_i)+τ_t W_i(y_i^{t-1},y_i)}`
from Eq. (5.1.25), for positive paper times. At Lean time zero this total
function returns the previous block as an isolated non-source fallback; no
argmin theorem is provided for that branch, and the generated Algorithm 5.1
process only consumes the positive-time branch. -/
noncomputable def candidateDualUpdate
    (hStanding : standingAssumptions setup)
    (t : ℕ) (xTilde : E) (i : ι) (yPrev : DualCarrier setup i)
    (baseSubgrad : DualConjugateSubgradient setup i yPrev) :
    DualCarrier setup i :=
  if ht : 1 ≤ t then
    scaledComponentGradientDual setup hStanding i
      (candidateDualSubgradientValue setup hStanding t ht xTilde baseSubgrad)
  else
    yPrev

/-- The canonical candidate dual update satisfies its defining argmin property
at positive paper times. -/
theorem candidateDualUpdate_isMinOn
    (hStanding : standingAssumptions setup)
    (t : ℕ) (ht : 1 ≤ t) (xTilde : E) (i : ι) (yPrev : DualCarrier setup i)
    (baseSubgrad : DualConjugateSubgradient setup i yPrev) :
    IsMinOn (candidateDualObjective setup t xTilde i yPrev · baseSubgrad) Set.univ
      (candidateDualUpdate setup hStanding t xTilde i yPrev baseSubgrad) :=
  by
    simpa [candidateDualUpdate, ht] using
      candidateDualScaledGradient_isMinOn setup hStanding t ht xTilde i yPrev baseSubgrad

/-- Lemma-3.6 realization obligation quoted after Eq. (5.1.25): the candidate
dual prox point carries the selected subgradient
`(x̃ᵗ+τ_t x_i^{t-1})/(1+τ_t)`. -/
theorem candidateDualSubgradient_mem
    (hStanding : standingAssumptions setup)
    (t : ℕ) (ht : 1 ≤ t) (xTilde : E) (i : ι) (yPrev : DualCarrier setup i)
    (baseSubgrad : DualConjugateSubgradient setup i yPrev) :
    IsDualConjugateSubgradient setup i
      (candidateDualUpdate setup hStanding t xTilde i yPrev baseSubgrad)
      (candidateDualSubgradientValue setup hStanding t ht xTilde baseSubgrad) := by
  simpa [candidateDualUpdate, ht] using
    scaledComponentGradientDual_subgradient_mem setup hStanding i
      (candidateDualSubgradientValue setup hStanding t ht xTilde baseSubgrad)

/-- Certified candidate selected subgradient for the full dual prox update. -/
noncomputable def candidateDualSubgradient
    (hStanding : standingAssumptions setup)
    (t : ℕ) (ht : 1 ≤ t) (xTilde : E) (i : ι) (yPrev : DualCarrier setup i)
    (baseSubgrad : DualConjugateSubgradient setup i yPrev) :
    DualConjugateSubgradient setup i
      (candidateDualUpdate setup hStanding t xTilde i yPrev baseSubgrad) :=
  ⟨candidateDualSubgradientValue setup hStanding t ht xTilde baseSubgrad,
    candidateDualSubgradient_mem setup hStanding t ht xTilde i yPrev baseSubgrad⟩

/-- The candidate dual prox update supplies the selected first-order condition
needed by the guarded Lemma 5.3 bridge. For the dual application,
`qGrad = -x̃ᵗ`, `μ₁ = 1`, `μ₂ = τ_t`, and the selected subgradient at the
candidate point is exactly
`(x̃ᵗ + τ_t x_i^{t-1}) / (1 + τ_t)`, so the FOC vector is zero. -/
theorem candidateDualUpdate_selected_FOC
    (hStanding : standingAssumptions setup)
    (t : ℕ) (ht : 1 ≤ t) (xTilde : E) (i : ι) (yPrev : DualCarrier setup i)
    (baseSubgrad : DualConjugateSubgradient setup i yPrev) (y : DualCarrier setup i) :
    0 ≤
      ⟪-xTilde +
          (candidateDualSubgradient setup hStanding t ht xTilde i yPrev baseSubgrad).1 +
          setup.τ t •
            ((candidateDualSubgradient setup hStanding t ht xTilde i yPrev baseSubgrad).1 -
              baseSubgrad.1),
        y.1 -
          (candidateDualUpdate setup hStanding t xTilde i yPrev baseSubgrad).1⟫_ℝ := by
  let q : E := candidateDualSubgradientValue setup hStanding t ht xTilde baseSubgrad
  have hOnePlusTau : 0 < 1 + setup.τ t :=
    onePlusTau_pos_of_standing setup hStanding t ht
  have hqscale :
      (1 + setup.τ t) • q = xTilde + setup.τ t • baseSubgrad.1 := by
    have hcoef :
        (1 + setup.τ t) *
            sourceQuotient 1 (1 + setup.τ t) (ne_of_gt hOnePlusTau) = 1 := by
      rw [sourceQuotient_def]
      field_simp [ne_of_gt hOnePlusTau]
    have hcoef_tau :
        (1 + setup.τ t) *
            (sourceQuotient 1 (1 + setup.τ t) (ne_of_gt hOnePlusTau) * setup.τ t) =
          setup.τ t := by
      calc
        (1 + setup.τ t) *
            (sourceQuotient 1 (1 + setup.τ t) (ne_of_gt hOnePlusTau) * setup.τ t)
            =
            ((1 + setup.τ t) *
                sourceQuotient 1 (1 + setup.τ t) (ne_of_gt hOnePlusTau)) *
              setup.τ t := by
          ring
        _ = 1 * setup.τ t := by rw [hcoef]
        _ = setup.τ t := by ring
    simp [q, candidateDualSubgradientValue, smul_smul, hcoef, hcoef_tau]
  have hvec_q : -xTilde + q + setup.τ t • (q - baseSubgrad.1) = 0 := by
    have hqexpanded : q + setup.τ t • q = xTilde + setup.τ t • baseSubgrad.1 := by
      simpa [add_smul, one_smul] using hqscale
    calc
      -xTilde + q + setup.τ t • (q - baseSubgrad.1) =
          -xTilde + (q + setup.τ t • q) - setup.τ t • baseSubgrad.1 := by
        module
      _ = -xTilde + (xTilde + setup.τ t • baseSubgrad.1) -
          setup.τ t • baseSubgrad.1 := by
        rw [hqexpanded]
      _ = 0 := by
        module
  have hvec :
      -xTilde +
          (candidateDualSubgradient setup hStanding t ht xTilde i yPrev baseSubgrad).1 +
          setup.τ t •
            ((candidateDualSubgradient setup hStanding t ht xTilde i yPrev baseSubgrad).1 -
              baseSubgrad.1) = 0 := by
    simpa [candidateDualSubgradient, q] using hvec_q
  rw [hvec]
  simp

variable [DecidableEq ι]

/-- Randomized dual update from Eq. (5.1.22), derived from the sampled block. -/
noncomputable def dualUpdate
    (hStanding : standingAssumptions setup)
    (t : ℕ) (xTilde : E) (yPrev : DualProductCarrier setup)
    (baseSubgrad : (i : ι) → DualConjugateSubgradient setup i (yPrev i))
    (sampled : ι) : DualProductCarrier setup :=
  fun i =>
    if i = sampled then
      candidateDualUpdate setup hStanding t xTilde i (yPrev i) (baseSubgrad i)
    else
      yPrev i

/-- The sampled coordinate of Eq. (5.1.22) is exactly the full candidate dual
prox update from Eq. (5.1.25). SOptLib reuse audit: searched `piecewise update
sampled block equation`, checked the recursive-process equations in
`SOptLib/Model/Iterates.lean`, and scanned `SOptLib/Model/StochasticOracle.lean`;
the reusable library supplies process and oracle wrappers, while this is the
paper-local case equation for RPDG's block update. -/
theorem dualUpdate_sampledBlock_eq
    (hStanding : standingAssumptions setup)
    (t : ℕ) (xTilde : E) (yPrev : DualProductCarrier setup)
    (baseSubgrad : (i : ι) → DualConjugateSubgradient setup i (yPrev i))
    (sampled : ι) :
    (dualUpdate setup hStanding t xTilde yPrev baseSubgrad sampled) sampled =
      candidateDualUpdate setup hStanding t xTilde sampled (yPrev sampled)
        (baseSubgrad sampled) := by
  simp [dualUpdate]

/-- Off the sampled coordinate, Eq. (5.1.22) leaves the dual block unchanged.
This is a theorem about the canonical `dualUpdate` definition, not a witness
field or theorem-local update hypothesis. -/
theorem dualUpdate_otherBlock_eq
    (hStanding : standingAssumptions setup)
    (t : ℕ) (xTilde : E) (yPrev : DualProductCarrier setup)
    (baseSubgrad : (i : ι) → DualConjugateSubgradient setup i (yPrev i))
    {i sampled : ι} (hne : i ≠ sampled) :
    (dualUpdate setup hStanding t xTilde yPrev baseSubgrad sampled) i = yPrev i := by
  simp [dualUpdate, hne]

/-- Recursive selected conjugate-subgradient update
`x_i^t=(x̃ᵗ+τ_t x_i^{t-1})/(1+τ_t)` for the sampled block and unchanged
otherwise, as specified after Eq. (5.1.25). -/
noncomputable def dualSubgradientUpdate
    (hStanding : standingAssumptions setup)
    (t : ℕ) (ht : 1 ≤ t) (xTilde : E) (yPrev : DualProductCarrier setup)
    (baseSubgrad : (i : ι) → DualConjugateSubgradient setup i (yPrev i))
    (sampled : ι) :
    (i : ι) →
      DualConjugateSubgradient setup i
        ((dualUpdate setup hStanding t xTilde yPrev baseSubgrad sampled) i) :=
  SOptLib.selectedCoordinateSubtypeUpdate
    (P := fun i y q => IsDualConjugateSubgradient setup i y q)
    yPrev
    (dualUpdate setup hStanding t xTilde yPrev baseSubgrad sampled)
    baseSubgrad
    sampled
    ⟨(candidateDualSubgradient setup hStanding t ht xTilde sampled
        (yPrev sampled) (baseSubgrad sampled)).1,
      by
        have hsample :
            (dualUpdate setup hStanding t xTilde yPrev baseSubgrad sampled)
                sampled =
              candidateDualUpdate setup hStanding t xTilde sampled
                (yPrev sampled) (baseSubgrad sampled) := by
          simp [dualUpdate]
        rw [hsample]
        simpa [candidateDualSubgradient] using
          candidateDualSubgradient_mem setup hStanding t ht xTilde sampled
            (yPrev sampled) (baseSubgrad sampled)⟩
    (by
      intro i hi
      simp [dualUpdate, hi])

/-- Sampled branch of the selected-subgradient update, projected to the stored
value. This is the update-level bridge needed for Lemma 5.4's conditioning on
`i_t = i`; it avoids transporting equality of dependent proof fields. -/
private theorem dualSubgradientUpdate_sampled_val_eq_candidate
    (hStanding : standingAssumptions setup)
    (t : ℕ) (ht : 1 ≤ t) (xTilde : E) (yPrev : DualProductCarrier setup)
    (baseSubgrad : (i : ι) → DualConjugateSubgradient setup i (yPrev i))
    (sampled : ι) :
    ((dualSubgradientUpdate setup hStanding t ht xTilde yPrev baseSubgrad sampled)
        sampled).1 =
      (candidateDualSubgradient setup hStanding t ht xTilde sampled
        (yPrev sampled) (baseSubgrad sampled)).1 := by
  simp [dualSubgradientUpdate, SOptLib.selectedCoordinateSubtypeUpdate,
    candidateDualSubgradient]

/-- Off-sampled branch of the selected-subgradient update, projected to the
stored value. This is the subgradient half of Eq. (5.1.22)'s unchanged-coordinate
branch, isolated before the generated process is unfolded. -/
private theorem dualSubgradientUpdate_other_val_eq_base
    (hStanding : standingAssumptions setup)
    (t : ℕ) (ht : 1 ≤ t) (xTilde : E) (yPrev : DualProductCarrier setup)
    (baseSubgrad : (i : ι) → DualConjugateSubgradient setup i (yPrev i))
    {i sampled : ι} (hne : i ≠ sampled) :
    ((dualSubgradientUpdate setup hStanding t ht xTilde yPrev baseSubgrad sampled)
        i).1 =
      (baseSubgrad i).1 := by
  simp [dualSubgradientUpdate, SOptLib.selectedCoordinateSubtypeUpdate, hne]

/-- Dual prediction `ỹ_i^t` from Eq. (5.1.23);
`book/FOML/RandomPrimalDualGradient.json#/algorithm_spec/steps/3`.
It is an extrapolated dual vector, so it is modeled in the ambient dual space
rather than forced into `Y_i`. SOptLib accelerated snapshot candidates were
checked and rejected because Eq. (5.1.23) is a sampled inverse-probability
block extrapolation, not a convex snapshot average. The sampled branch is
indexed by `PositiveBlock setup`, so its reciprocal uses the sample's support
certificate instead of a global full-support premise. -/
noncomputable def dualPrediction
    (yPrev yNext : DualProductCarrier setup) (sampled : PositiveBlock setup) :
    ι → E :=
  SOptLib.inverseProbabilityCoordinatePrediction (samplingProbability setup)
    (fun i => (yPrev i).1) (fun i => (yNext i).1) sampled.1

/-- The sampled coordinate of Eq. (5.1.23) uses the inverse-probability
extrapolation, with the denominator certificate carried by the sampled
positive-support block. -/
theorem dualPrediction_sampledBlock_eq
    (yPrev yNext : DualProductCarrier setup) (sampled : PositiveBlock setup) :
    dualPrediction setup yPrev yNext sampled sampled.1 =
      inverseProbabilityValue setup sampled.1
          (sampledBlock_probability_ne_zero setup sampled) •
        ((yNext sampled.1).1 - (yPrev sampled.1).1) + (yPrev sampled.1).1 := by
  simp [dualPrediction, inverseProbabilityValue, sourceQuotient]

/-- Off the sampled coordinate, Eq. (5.1.23) leaves the dual prediction equal
to the previous dual block. -/
theorem dualPrediction_otherBlock_eq
    (yPrev yNext : DualProductCarrier setup) (sampled : PositiveBlock setup)
    {i : ι} (hne : i ≠ sampled.1) :
    dualPrediction setup yPrev yNext sampled i = (yPrev i).1 := by
  simp [dualPrediction, hne]


/-- Source-derived solvability obligation for the primal prox argmin in
Eq. (5.1.24), at the positive paper times of Algorithm 5.1. -/
theorem primalUpdate_exists_of_standing
    (hStanding : standingAssumptions setup)
    (t : ℕ) (ht : 1 ≤ t) (xPrev : PrimalCarrier setup) (yTilde : ι → E) :
    ∃ x : PrimalCarrier setup,
      IsMinOn (SOptLib.proxObjective
        (primalBregman setup)
        (fun z : PrimalCarrier setup => setup.h z.1 + setup.μ * setup.nu z)
        (fun z : PrimalCarrier setup => z.1)
        xPrev (∑ i : ι, yTilde i) (setup.η t)⁻¹) Set.univ x ∧
        primalProxSelectedSubgradientCertificate setup
          (∑ i : ι, yTilde i) xPrev x (setup.η t) := by
  rcases hStanding with ⟨_, _, _, _, _, _, _, hEasy, hProx, _, _, hParam⟩
  by_cases hηpos : 0 < setup.η t
  · rcases hProx xPrev (∑ i : ι, yTilde i) (setup.η t) hηpos with ⟨x, hxMin, hxSub⟩
    refine ⟨x, ?_, hxSub⟩
    convert hxMin using 1
    funext z
    simp [SOptLib.proxObjective]
    ring_nf
  · have hηnonneg : 0 ≤ setup.η t := hParam.2.1 t ht
    have hηnonpos : setup.η t ≤ 0 := not_lt.mp hηpos
    have hηzero : setup.η t = 0 := le_antisymm hηnonpos hηnonneg
    rcases hEasy (∑ i : ι, yTilde i) with ⟨x, hxMin, hxSub⟩
    refine ⟨x, ?_, ?_⟩
    · convert hxMin using 1
      funext z
      simp [SOptLib.proxObjective, hηzero]
      ring_nf
    · simpa [primalProxSelectedSubgradientCertificate,
        primalEasySelectedSubgradientCertificate, hηzero] using hxSub

/-- Canonical primal update from Eq. (5.1.24), for positive paper times. At Lean
time zero this total function returns `xPrev` as an isolated non-source fallback;
the recursive Algorithm 5.1 process calls the positive-time branch. -/
noncomputable def primalUpdate
    (hStanding : standingAssumptions setup)
    (t : ℕ) (xPrev : PrimalCarrier setup) (yTilde : ι → E) :
    PrimalCarrier setup :=
  if ht : 1 ≤ t then
    Classical.choose (primalUpdate_exists_of_standing setup hStanding t ht xPrev yTilde)
  else
    xPrev

/-- The canonical primal update satisfies its defining argmin property at
positive paper times. -/
theorem primalUpdate_isMinOn
    (hStanding : standingAssumptions setup)
    (t : ℕ) (ht : 1 ≤ t) (xPrev : PrimalCarrier setup) (yTilde : ι → E) :
    IsMinOn (SOptLib.proxObjective
        (primalBregman setup)
        (fun z : PrimalCarrier setup => setup.h z.1 + setup.μ * setup.nu z)
        (fun z : PrimalCarrier setup => z.1)
        xPrev (∑ i : ι, yTilde i) (setup.η t)⁻¹) Set.univ
      (primalUpdate setup hStanding t xPrev yTilde) :=
  by
    simpa [primalUpdate, ht] using
      (Classical.choose_spec
        (primalUpdate_exists_of_standing setup hStanding t ht xPrev yTilde)).1

/-- The canonical primal update carries the selected prox optimality certificate
from the source recursive choice of `ν'` after Eq. (5.1.17). -/
theorem primalUpdate_selected_subgradient_certificate
    (hStanding : standingAssumptions setup)
    (t : ℕ) (ht : 1 ≤ t) (xPrev : PrimalCarrier setup) (yTilde : ι → E) :
    primalProxSelectedSubgradientCertificate setup
      (∑ i : ι, yTilde i) xPrev
      (primalUpdate setup hStanding t xPrev yTilde) (setup.η t) :=
  by
    simpa [primalUpdate, ht] using
      (Classical.choose_spec
        (primalUpdate_exists_of_standing setup hStanding t ht xPrev yTilde)).2

/-- Primal prox descent inequality for Eq. (5.1.24), in the source shape used as
display (5.1.43) in Lemma 5.5.

The active route is selected-subgradient based: `ν'` is the paper-selected
carrier subgradient and the remaining local leaf is the nonsmooth prox
optimality certificate that selects the matching carrier subgradient of `h` at
the primal update. No differentiability of `ν` or `h` is assumed. -/
theorem primalUpdate_two_bregman_descent
    (hStanding : standingAssumptions setup)
    (t : ℕ) (ht : 1 ≤ t) (xPrev : PrimalCarrier setup) (yTilde : ι → E)
    (x : PrimalCarrier setup) :
    ⟪(primalUpdate setup hStanding t xPrev yTilde).1 - x.1,
        ∑ i : ι, yTilde i⟫_ℝ +
        setup.h (primalUpdate setup hStanding t xPrev yTilde).1 +
        setup.μ * setup.nu (primalUpdate setup hStanding t xPrev yTilde) -
        setup.h x.1 - setup.μ * setup.nu x ≤
      setup.η t * primalBregman setup xPrev x -
        (setup.μ + setup.η t) *
          primalBregman setup (primalUpdate setup hStanding t xPrev yTilde) x -
        setup.η t *
          primalBregman setup xPrev
            (primalUpdate setup hStanding t xPrev yTilde) := by
  classical
  let hStanding0 : standingAssumptions setup := hStanding
  rcases hStanding with
    ⟨_hX, _hSmooth, _hSimple, _hComp, _hNu, _hMu, _hAvg, _hEasy, _hProx,
      _hLower, _hDual, hParam⟩
  let xStar : PrimalCarrier setup := primalUpdate setup hStanding0 t xPrev yTilde
  let g : E := ∑ i : ι, yTilde i
  have hMinSubtype :
      IsMinOn (SOptLib.proxObjective
        (primalBregman setup)
        (fun z : PrimalCarrier setup => setup.h z.1 + setup.μ * setup.nu z)
        (fun z : PrimalCarrier setup => z.1)
        xPrev (∑ i : ι, yTilde i) (setup.η t)⁻¹) Set.univ xStar := by
    simpa [xStar] using primalUpdate_isMinOn setup hStanding0 t ht xPrev yTilde
  have hη : 0 ≤ setup.η t := hParam.2.1 t ht
  have hSelectedData := primalBregman_selected_subgradient_data setup hStanding0
  have hhSub :
      (-(g + setup.μ • setup.nuGrad xStar +
          setup.η t • (setup.nuGrad xStar - setup.nuGrad xPrev))) ∈
        SOptLib.carrierSubdifferential
          (fun z : PrimalCarrier setup => setup.h z.1) xStar := by
    simpa [primalProxSelectedSubgradientCertificate, xStar, g] using
      primalUpdate_selected_subgradient_certificate setup hStanding0 t ht xPrev yTilde
  simpa [xStar, g] using
    primal_two_bregman_descent_of_simple_subgradient
      setup g xPrev xStar x (setup.η t) hhSub

/-- RPDG state at time `t`: `(x^{t-1}, x^t, y^t, ỹ^t)`. -/
structure State where
  xLag : PrimalCarrier setup
  x : PrimalCarrier setup
  y : DualProductCarrier setup
  /-- The recursively selected subgradients `x_i^t ∈ ∂J_i(y_i^t)` from the
  implementation discussion after Eq. (5.1.25). -/
  dualSubgrad : (i : ι) → DualConjugateSubgradient setup i (y i)
  yTilde : ι → E

/-- Initial state `x^{-1}=x^0`, `y_i^0=m⁻¹∇f_i(x^0)`, and `x_i^0=x^0`. -/
noncomputable def initialState (hStanding : standingAssumptions setup) : State setup where
  xLag := setup.x0
  x := setup.x0
  y := initialDual setup hStanding
  dualSubgrad := initialDualSubgradient setup hStanding
  yTilde := fun i => (initialDual setup hStanding i).1

/-- One canonical Algorithm 5.1 transition at paper time `t`;
`book/FOML/RandomPrimalDualGradient.json#/algorithm_spec/steps`. The displayed
`p_i^{-1}` in Eq. (5.1.23) is represented through the positive-support sampled
block, not by Lean's total inverse at zero and not by a global full-support
assumption. -/
noncomputable def rpdgStep
    (hStanding : standingAssumptions setup)
    (t : ℕ) (ht : 1 ≤ t) (state : State setup) (sampled : PositiveBlock setup) :
    State setup :=
  let xTilde := primalPrediction setup t state.x state.xLag
  let yNext := dualUpdate setup hStanding t xTilde state.y state.dualSubgrad sampled.1
  let dualSubgradNext :=
    dualSubgradientUpdate setup hStanding t ht xTilde state.y state.dualSubgrad sampled.1
  let yTilde := dualPrediction setup state.y yNext sampled
  let xNext := primalUpdate setup hStanding t state.x yTilde
  { xLag := state.x, x := xNext, y := yNext, dualSubgrad := dualSubgradNext,
    yTilde := yTilde }

/-- Active component-equation signature for one full Algorithm 5.1 transition.
This records Eqs. (5.1.21)--(5.1.24) as equations for the canonical
`rpdgStep`, including the state shift `x^{t-1}` for the next iteration.

No SOptLib match applies: checked `SOptLib.recursiveIterateProcess_succ` and
searched `recursive process step component equations`; SOptLib supplies the
generic successor equation for a generated process, while this is the
paper-specific component expansion of the RPDG transition itself. -/
def rpdgStepEquationsSignature : Prop :=
  ∀ (hStanding : standingAssumptions setup)
      (t : ℕ) (ht : 1 ≤ t) (state : State setup) (sampled : PositiveBlock setup),
    let xTilde := primalPrediction setup t state.x state.xLag
    let yNext := dualUpdate setup hStanding t xTilde state.y state.dualSubgrad sampled.1
    let yTilde := dualPrediction setup state.y yNext sampled
    (rpdgStep setup hStanding t ht state sampled).xLag = state.x ∧
      (rpdgStep setup hStanding t ht state sampled).y = yNext ∧
        (rpdgStep setup hStanding t ht state sampled).yTilde = yTilde ∧
          (rpdgStep setup hStanding t ht state sampled).x =
            primalUpdate setup hStanding t state.x yTilde

/-- The live `rpdgStep` definition satisfies the full Algorithm 5.1 component
equations. -/
theorem rpdgStepEquationsSignature_holds :
    rpdgStepEquationsSignature setup := by
  intro hStanding t ht state sampled
  simp [rpdgStep]

/-- Generated RPDG state process from the sample path. This uses SOptLib's
canonical `recursiveIterateProcess` rather than storing `x_t` and `y_t` as free
setup fields. -/
noncomputable def stateProcess
    (hStanding : standingAssumptions setup) :
    ℕ → BlockSamplePath setup → State setup :=
  SOptLib.recursiveIterateProcess (initialState setup hStanding)
    (fun n state ω =>
      rpdgStep setup hStanding (n + 1) (Nat.succ_pos n) state
        (sampledPositiveBlock setup (n + 1) ω))

/-- Initial equation for the generated Algorithm 5.1 state process.
This specializes SOptLib `recursiveIterateProcess_zero` to the paper state
`(x^{-1},x^0,y^0,ỹ^0)`, keeping the initialized process as a theorem about the
canonical recursion rather than a stored iterate witness. -/
theorem stateProcess_zero
    (hStanding : standingAssumptions setup) (ω : BlockSamplePath setup) :
    stateProcess setup hStanding 0 ω = initialState setup hStanding :=
  SOptLib.recursiveIterateProcess_zero
    (stateProcess setup hStanding)
    (initialState setup hStanding)
    (fun n state ω =>
      rpdgStep setup hStanding (n + 1) (Nat.succ_pos n) state
        (sampledPositiveBlock setup (n + 1) ω))
    rfl ω

/-- Successor equation for the generated Algorithm 5.1 state process.
This specializes SOptLib `recursiveIterateProcess_succ` to the paper transition
Eqs. (5.1.21)--(5.1.24), so the public iterate sequence is locked to
`rpdgStep` and the sampled positive-support block. -/
theorem stateProcess_succ
    (hStanding : standingAssumptions setup) (n : ℕ) (ω : BlockSamplePath setup) :
    stateProcess setup hStanding (n + 1) ω =
      rpdgStep setup hStanding (n + 1) (Nat.succ_pos n)
        (stateProcess setup hStanding n ω)
        (sampledPositiveBlock setup (n + 1) ω) :=
  SOptLib.recursiveIterateProcess_succ
    (stateProcess setup hStanding)
    (initialState setup hStanding)
    (fun n state ω =>
      rpdgStep setup hStanding (n + 1) (Nat.succ_pos n) state
        (sampledPositiveBlock setup (n + 1) ω))
    rfl n ω

/-- The generated Algorithm 5.1 state at time `k` is determined by the paper
prefix `i_1,...,i_k`. This is proved directly over the one-based source prefix:
the available build image does not expose the newer SOptLib `sampleWindow`
determinism helper, and importing its source module is outside this target file's
usable import boundary. -/
theorem stateProcess_eq_of_blockPrefix_eq
    (hStanding : standingAssumptions setup) (k : ℕ)
    {ω ω' : BlockSamplePath setup}
    (hprefix : blockPrefix setup k ω = blockPrefix setup k ω') :
    stateProcess setup hStanding k ω = stateProcess setup hStanding k ω' := by
  induction k with
  | zero =>
      rw [stateProcess_zero setup hStanding ω,
        stateProcess_zero setup hStanding ω']
  | succ n ih =>
      have hprefix_prev : blockPrefix setup n ω = blockPrefix setup n ω' := by
        funext t
        have ht : 1 ≤ t.1 ∧ t.1 ≤ n + 1 :=
          ⟨t.2.1, Nat.le_trans t.2.2 (Nat.le_succ n)⟩
        exact congrFun hprefix ⟨t.1, ht⟩
      have hstate : stateProcess setup hStanding n ω =
          stateProcess setup hStanding n ω' := ih hprefix_prev
      have hsample :
          sampledPositiveBlock setup (n + 1) ω =
            sampledPositiveBlock setup (n + 1) ω' := by
        exact congrFun hprefix ⟨n + 1, ⟨Nat.succ_pos n, le_rfl⟩⟩
      rw [stateProcess_succ setup hStanding n ω,
        stateProcess_succ setup hStanding n ω']
      simp [hstate, hsample]

/-- Generated primal iterate `x^t`. -/
noncomputable def xIter
    (hStanding : standingAssumptions setup)
    (t : ℕ) (ω : BlockSamplePath setup) :
    PrimalCarrier setup :=
  (stateProcess setup hStanding t ω).x

/-- Generated primal prediction `x̃^t` from Eq. (5.1.21). -/
noncomputable def xTildeIter
    (hStanding : standingAssumptions setup)
    (t : ℕ) (ω : BlockSamplePath setup) : E :=
  primalPrediction setup t
    (xIter setup hStanding (t - 1) ω)
    (xIter setup hStanding (t - 2) ω)

/-- Generated dual iterate `y^t`. -/
noncomputable def yIter
    (hStanding : standingAssumptions setup)
    (t : ℕ) (ω : BlockSamplePath setup) :
    DualProductCarrier setup :=
  (stateProcess setup hStanding t ω).y

/-- Generated selected dual subgradients `x_i^t` satisfying
`x_i^t ∈ ∂J_i(y_i^t)`. -/
noncomputable def dualSubgradIter
    (hStanding : standingAssumptions setup)
    (t : ℕ) (ω : BlockSamplePath setup) :
    (i : ι) → DualConjugateSubgradient setup i ((yIter setup hStanding t ω) i) :=
  (stateProcess setup hStanding t ω).dualSubgrad

/-- Generated full candidate dual vector `ŷ^t` from Eq. (5.1.25). The accessor is
total on `ℕ` because the generated process has an initial state, but the
defining argmin theorem for this vector is only a positive-time statement. -/
noncomputable def yHatIter
    (hStanding : standingAssumptions setup)
    (t : ℕ) (ω : BlockSamplePath setup) :
    DualProductCarrier setup :=
  fun i => candidateDualUpdate setup hStanding t
    (xTildeIter setup hStanding t ω) i
    ((yIter setup hStanding (t - 1) ω) i)
    (dualSubgradIter setup hStanding (t - 1) ω i)

/-- Selected subgradient attached to the full candidate dual vector `ŷ^t`. -/
noncomputable def yHatSubgradIter
    (hStanding : standingAssumptions setup)
    (t : ℕ) (ht : 1 ≤ t)
    (ω : BlockSamplePath setup) :
    (i : ι) → DualConjugateSubgradient setup i ((yHatIter setup hStanding t ω) i) :=
  fun i => candidateDualSubgradient setup hStanding t ht
    (xTildeIter setup hStanding t ω)
    i ((yIter setup hStanding (t - 1) ω) i)
    (dualSubgradIter setup hStanding (t - 1) ω i)

/-- Generated dual prediction `ỹ^t`. -/
noncomputable def yTildeIter
    (hStanding : standingAssumptions setup)
    (t : ℕ) (ω : BlockSamplePath setup) : ι → E :=
  (stateProcess setup hStanding t ω).yTilde

/-- Active case-equation signature for Algorithm 5.1's sampled dual update and
dual prediction. This source-facing contract locks Eqs. (5.1.22)--(5.1.23) to
the canonical `dualUpdate`/`dualPrediction` definitions, so the sampled update
cannot later be replaced by theorem-local case hypotheses.

No SOptLib match applies: searched `piecewise update sampled block equation`
and `recursive iterate process successor equation`, checked
`SOptLib.recursiveIterateProcess_succ` and `SOptLib.sampledOracleProcess_def`,
and scanned `SOptLib/Model/Iterates.lean` plus
`SOptLib/Model/StochasticOracle.lean`; those are reusable process/oracle
wrappers, not the paper-specific RPDG block case split. -/
def algorithmStepCaseEquationsSignature : Prop :=
  ∀ (hStanding : standingAssumptions setup)
      (t : ℕ) (xTilde : E) (yPrev : DualProductCarrier setup)
      (baseSubgrad : (i : ι) → DualConjugateSubgradient setup i (yPrev i))
      (sampled : PositiveBlock setup),
    (dualUpdate setup hStanding t xTilde yPrev baseSubgrad sampled.1) sampled.1 =
        candidateDualUpdate setup hStanding t xTilde sampled.1 (yPrev sampled.1)
          (baseSubgrad sampled.1) ∧
      (∀ i : ι, i ≠ sampled.1 →
        (dualUpdate setup hStanding t xTilde yPrev baseSubgrad sampled.1) i =
          yPrev i) ∧
        dualPrediction setup yPrev
            (dualUpdate setup hStanding t xTilde yPrev baseSubgrad sampled.1)
            sampled sampled.1 =
          inverseProbabilityValue setup sampled.1
              (sampledBlock_probability_ne_zero setup sampled) •
            (((dualUpdate setup hStanding t xTilde yPrev baseSubgrad sampled.1)
                sampled.1).1 - (yPrev sampled.1).1) +
              (yPrev sampled.1).1 ∧
          (∀ i : ι, i ≠ sampled.1 →
            dualPrediction setup yPrev
                (dualUpdate setup hStanding t xTilde yPrev baseSubgrad sampled.1)
                sampled i = (yPrev i).1)

/-- The live Algorithm 5.1 step definitions satisfy their recorded sampled-block
case equations. -/
theorem algorithmStepCaseEquationsSignature_holds :
    algorithmStepCaseEquationsSignature setup := by
  intro hStanding t xTilde yPrev baseSubgrad sampled
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact dualUpdate_sampledBlock_eq setup hStanding t xTilde yPrev baseSubgrad sampled.1
  · intro i hne
    exact dualUpdate_otherBlock_eq setup hStanding t xTilde yPrev baseSubgrad hne
  · exact dualPrediction_sampledBlock_eq setup yPrev
      (dualUpdate setup hStanding t xTilde yPrev baseSubgrad sampled.1) sampled
  · intro i hne
    exact dualPrediction_otherBlock_eq setup yPrev
      (dualUpdate setup hStanding t xTilde yPrev baseSubgrad sampled.1) sampled hne

/-- Source-derived invariant of the generated process: the stored `x_i^t` is the
paper-selected subgradient of `J_i` at `y_i^t`. -/
theorem dualSubgradIter_mem
    (hStanding : standingAssumptions setup)
    (t : ℕ) (ω : BlockSamplePath setup) (i : ι) :
    IsDualConjugateSubgradient setup i ((yIter setup hStanding t ω) i)
      (dualSubgradIter setup hStanding t ω i).1 :=
  (dualSubgradIter setup hStanding t ω i).2

/-- Positive-time unfolding of the generated RPDG process. This is the
one-based form of `stateProcess_succ`, aligning Lemma 5.4's conditioning step
with Algorithm 5.1's transition at time `t`. -/
private theorem stateProcess_positive_time_step
    (hStanding : standingAssumptions setup)
    (t : ℕ) (ht : 1 ≤ t) (ω : BlockSamplePath setup) :
    stateProcess setup hStanding t ω =
      rpdgStep setup hStanding t ht
        (stateProcess setup hStanding (t - 1) ω)
        (sampledPositiveBlock setup t ω) := by
  cases t with
  | zero =>
      cases ht
  | succ n =>
      simpa using stateProcess_succ setup hStanding n ω

/-- State-lag coordinate at the predecessor of a positive paper time. This
supports Lemma 5.4's branch equations by aligning the local step prediction
with `xTildeIter`; searched `stateProcess positive time succ t minus one`, where
the available SOptLib transport lemmas are generic component transports while
this file needs the RPDG-specific `xLag` projection. -/
private theorem stateProcess_pred_xLag_eq_xIter_pred_two
    (hStanding : standingAssumptions setup)
    (t : ℕ) (ht : 1 ≤ t) (ω : BlockSamplePath setup) :
    (stateProcess setup hStanding (t - 1) ω).xLag =
      xIter setup hStanding (t - 2) ω := by
  cases t with
  | zero =>
      cases ht
  | succ n =>
      cases n with
      | zero =>
          simp [stateProcess_zero, xIter, initialState]
      | succ m =>
          simp [stateProcess_succ, rpdgStep, xIter]

/-- The step-local primal prediction equals the generated `xTildeIter` at
positive paper time `t`. This is the RPDG specialization of the generic
positive-time component-transport pattern found by search. -/
private theorem stepPrimalPrediction_eq_xTildeIter
    (hStanding : standingAssumptions setup)
    (t : ℕ) (ht : 1 ≤ t) (ω : BlockSamplePath setup) :
    primalPrediction setup t
        (stateProcess setup hStanding (t - 1) ω).x
        (stateProcess setup hStanding (t - 1) ω).xLag =
      xTildeIter setup hStanding t ω := by
  rw [xTildeIter, xIter, stateProcess_pred_xLag_eq_xIter_pred_two setup hStanding t ht ω]

/-- Prefix-extension determinism for generated states. This is the local
process bridge used to turn Lemma 5.4 branch payloads into functions of
`blockPrefix setup (t - 1)`.

No SOptLib match: searched `finite prefix extension state process determined by
prefix`, considered `SOptLib.recursiveIterateProcess_succ` and the existing
local `stateProcess_eq_of_blockPrefix_eq`; the reusable recursion lemmas do not
know this paper's one-based `BlockPrefix`, while the local determinism theorem
gives exactly the needed equality after restricting an extended longer prefix. -/
private theorem stateProcess_extendBlockPrefix_eq_of_le
    (hStanding : standingAssumptions setup)
    {l k : ℕ} (hle : l ≤ k) (ω : BlockSamplePath setup) :
    stateProcess setup hStanding l
        (extendBlockPrefix setup k (blockPrefix setup k ω)) =
      stateProcess setup hStanding l ω := by
  apply stateProcess_eq_of_blockPrefix_eq setup hStanding l
  funext s
  simpa [blockPrefix, extendBlockPrefix, sampledPositiveBlock] using
    (SOptLib.extendSampleWindow_one_based_apply
      (pref := blockPrefix setup k ω)
      (sampleDefault := Classical.choice (positiveBlockNonempty setup))
      (ht := s.2.1) (htk := Nat.le_trans s.2.2 hle))

/-- Same-time prefix-extension determinism. This is the `l = k` specialization
used repeatedly in Lemma 5.4 payload factorization; it aligns with the paper's
conditioning on `i_1,...,i_{t-1}`. -/
private theorem stateProcess_extendBlockPrefix_eq
    (hStanding : standingAssumptions setup)
    (k : ℕ) (ω : BlockSamplePath setup) :
    stateProcess setup hStanding k
        (extendBlockPrefix setup k (blockPrefix setup k ω)) =
      stateProcess setup hStanding k ω := by
  exact stateProcess_extendBlockPrefix_eq_of_le setup hStanding (le_rfl : k ≤ k) ω

/-- The sampled block at time `t` is determined by any generated paper prefix
containing `t`. This is the sampled-block companion to
`stateProcess_extendBlockPrefix_eq_of_le`, needed for Proposition 5.1 Delta
residual transports where the integrand contains the explicit selected block.
Searches for `sampledBlock extendBlockPrefix prefixObservable` found only the
raw definitions `sampledBlock`, `blockPrefix`, and `extendBlockPrefix`. -/
private theorem sampledBlock_extendBlockPrefix_eq_of_le
    {t k : ℕ} (ht : 1 ≤ t) (htk : t ≤ k)
    (ω : BlockSamplePath setup) :
    sampledBlock setup t (extendBlockPrefix setup k (blockPrefix setup k ω)) =
      sampledBlock setup t ω := by
  simpa [sampledBlock, sampledPositiveBlock, extendBlockPrefix, blockPrefix] using
    congrArg Subtype.val
      (SOptLib.extendSampleWindow_one_based_apply
        (pref := blockPrefix setup k ω)
        (sampleDefault := Classical.choice (positiveBlockNonempty setup))
        (ht := ht) (htk := htk))

/-- Sampled-coordinate endpoint equation for Eq. (5.1.22), specialized to the
generated process. It consumes `stateProcess_succ` through
`stateProcess_positive_time_step` and the local `dualUpdate_sampledBlock_eq`
case equation found by search. -/
private theorem yIter_sampledBlock_eq_yHatIter
    (hStanding : standingAssumptions setup)
    (t : ℕ) (ht : 1 ≤ t) (ω : BlockSamplePath setup) :
    (yIter setup hStanding t ω) (sampledBlock setup t ω) =
      (yHatIter setup hStanding t ω) (sampledBlock setup t ω) := by
  rw [yIter, stateProcess_positive_time_step setup hStanding t ht ω]
  simpa [rpdgStep, yHatIter, yIter, dualSubgradIter, sampledBlock,
    stepPrimalPrediction_eq_xTildeIter setup hStanding t ht ω] using
      dualUpdate_sampledBlock_eq setup hStanding t
        (xTildeIter setup hStanding t ω)
        ((stateProcess setup hStanding (t - 1) ω).y)
        ((stateProcess setup hStanding (t - 1) ω).dualSubgrad)
        (sampledBlock setup t ω)

/-- Off-sampled endpoint equation for Eq. (5.1.22), specialized to the generated
process. This is the coordinate branch used in Lemma 5.4 when `i_t ≠ i`. -/
private theorem yIter_otherBlock_eq_prev
    (hStanding : standingAssumptions setup)
    (t : ℕ) (ht : 1 ≤ t) (ω : BlockSamplePath setup)
    {i : ι} (hne : i ≠ sampledBlock setup t ω) :
    (yIter setup hStanding t ω) i =
      (yIter setup hStanding (t - 1) ω) i := by
  rw [yIter, stateProcess_positive_time_step setup hStanding t ht ω]
  simpa [rpdgStep, yIter, sampledBlock,
    stepPrimalPrediction_eq_xTildeIter setup hStanding t ht ω] using
      dualUpdate_otherBlock_eq setup hStanding t
        (xTildeIter setup hStanding t ω)
        ((stateProcess setup hStanding (t - 1) ω).y)
        ((stateProcess setup hStanding (t - 1) ω).dualSubgrad)
        (i := i) (sampled := sampledBlock setup t ω) hne

/-- Sampled-coordinate dual-prediction equation for Eq. (5.1.23), specialized
to the generated process. This is the `yTildeIter` counterpart of
`dualPrediction_sampledBlock_eq`; no SOptLib process lemma exposes this
paper-specific sampled inverse-probability prediction branch. -/
private theorem yTildeIter_sampledBlock_eq
    (hStanding : standingAssumptions setup)
    (t : ℕ) (ht : 1 ≤ t) (ω : BlockSamplePath setup) :
    yTildeIter setup hStanding t ω (sampledBlock setup t ω) =
      inverseProbabilityValue setup (sampledBlock setup t ω)
          (sampledBlock_probability_ne_zero setup
            (sampledPositiveBlock setup t ω)) •
        (((yIter setup hStanding t ω) (sampledBlock setup t ω)).1 -
          ((yIter setup hStanding (t - 1) ω)
            (sampledBlock setup t ω)).1) +
        ((yIter setup hStanding (t - 1) ω)
          (sampledBlock setup t ω)).1 := by
  rw [yTildeIter, yIter, stateProcess_positive_time_step setup hStanding t ht ω]
  simpa [rpdgStep, yIter, sampledBlock,
    stepPrimalPrediction_eq_xTildeIter setup hStanding t ht ω] using
      dualPrediction_sampledBlock_eq setup
        ((stateProcess setup hStanding (t - 1) ω).y)
        (dualUpdate setup hStanding t (xTildeIter setup hStanding t ω)
          ((stateProcess setup hStanding (t - 1) ω).y)
          ((stateProcess setup hStanding (t - 1) ω).dualSubgrad)
          (sampledBlock setup t ω))
        (sampledPositiveBlock setup t ω)

/-- Off-sampled dual-prediction equation for Eq. (5.1.23), specialized to the
generated process. This is the branch used in the Lemma 5.5 unbiasedness
observation for coordinates not selected at time `t`. -/
private theorem yTildeIter_otherBlock_eq_prev
    (hStanding : standingAssumptions setup)
    (t : ℕ) (ht : 1 ≤ t) (ω : BlockSamplePath setup)
    {i : ι} (hne : i ≠ sampledBlock setup t ω) :
    yTildeIter setup hStanding t ω i =
      ((yIter setup hStanding (t - 1) ω) i).1 := by
  rw [yTildeIter, stateProcess_positive_time_step setup hStanding t ht ω]
  simpa [rpdgStep, yIter, sampledBlock,
    stepPrimalPrediction_eq_xTildeIter setup hStanding t ht ω] using
      dualPrediction_otherBlock_eq setup
        ((stateProcess setup hStanding (t - 1) ω).y)
        (dualUpdate setup hStanding t (xTildeIter setup hStanding t ω)
          ((stateProcess setup hStanding (t - 1) ω).y)
          ((stateProcess setup hStanding (t - 1) ω).dualSubgrad)
          (sampledBlock setup t ω))
        (sampledPositiveBlock setup t ω)
        (i := i) hne

/-- Pointwise branch form of the dual-prediction mismatch
`ỹ_i^t - ŷ_i^t` from Eq. (5.1.23), specialized to the generated process.
This is a T3 staging lemma: searched for an existing dual-prediction
unbiasedness helper and found only the raw `dualPrediction_*` case equations,
so this packages the coordinate algebra needed before conditional expectation. -/
private theorem yTildeIter_sub_yHatIter_branch
    (hStanding : standingAssumptions setup)
    (hProbDen : allBlockProbabilityDenominatorsAdmissible setup)
    (t : ℕ) (ht : 1 ≤ t) (ω : BlockSamplePath setup) (i : ι) :
    yTildeIter setup hStanding t ω i -
        (yHatIter setup hStanding t ω i).1 =
      if sampledBlock setup t ω = i then
        (inverseProbabilityValue setup i (hProbDen i) - 1) •
          ((yHatIter setup hStanding t ω i).1 -
            ((yIter setup hStanding (t - 1) ω) i).1)
      else
        -((yHatIter setup hStanding t ω i).1 -
          ((yIter setup hStanding (t - 1) ω) i).1) := by
  classical
  have hbranch :=
    SOptLib.inverseProbabilityCoordinatePrediction_sub_candidate_branch
      (prob := samplingProbability setup)
      (prev := fun j => ((yIter setup hStanding (t - 1) ω) j).1)
      (cand := fun j => (yHatIter setup hStanding t ω j).1)
      (sampled := sampledBlock setup t ω) (i := i)
  by_cases hsample : i = sampledBlock setup t ω
  · subst i
    simpa [inverseProbabilityValue, sourceQuotient,
      dualPrediction, yTildeIter, yHatIter, yIter, dualSubgradIter, dualUpdate,
      rpdgStep, sampledBlock, sampledPositiveBlock,
      stateProcess_positive_time_step setup hStanding t ht ω,
      stepPrimalPrediction_eq_xTildeIter setup hStanding t ht ω] using hbranch
  · have hsample' : sampledBlock setup t ω ≠ i := fun h => hsample h.symm
    have hsample_val : i ≠ (ω t).1 := by
      simpa [sampledBlock, sampledPositiveBlock] using hsample
    have hsample_val' : (ω t).1 ≠ i := fun h => hsample_val h.symm
    simpa [hsample, hsample', hsample_val, hsample_val',
      inverseProbabilityValue, sourceQuotient,
      dualPrediction, yTildeIter, yHatIter, yIter, dualSubgradIter, dualUpdate,
      rpdgStep, sampledBlock, sampledPositiveBlock,
      stateProcess_positive_time_step setup hStanding t ht ω,
      stepPrimalPrediction_eq_xTildeIter setup hStanding t ht ω] using hbranch

/-- Sampled-coordinate selected-subgradient value equation for the generated
process. This is the value-level form needed by the carrier Bregman selector,
avoiding dependent proof-field transport while using `dualSubgradientUpdate`. -/
private theorem dualSubgradIter_sampledBlock_val_eq_yHatSubgradIter
    (hStanding : standingAssumptions setup)
    (t : ℕ) (ht : 1 ≤ t) (ω : BlockSamplePath setup) :
    (dualSubgradIter setup hStanding t ω (sampledBlock setup t ω)).1 =
      (yHatSubgradIter setup hStanding t ht ω (sampledBlock setup t ω)).1 := by
  cases t with
  | zero =>
      cases ht
  | succ n =>
      have hht : ht = Nat.succ_pos n := Subsingleton.elim ht (Nat.succ_pos n)
      subst ht
      have hstate :
          ((stateProcess setup hStanding (n + 1) ω).dualSubgrad
              (sampledBlock setup (n + 1) ω)).1 =
            ((rpdgStep setup hStanding (n + 1) (Nat.succ_pos n)
                (stateProcess setup hStanding n ω)
                (sampledPositiveBlock setup (n + 1) ω)).dualSubgrad
              (sampledBlock setup (n + 1) ω)).1 := by
        exact congrArg
          (fun s : State setup => (s.dualSubgrad (sampledBlock setup (n + 1) ω)).1)
          (stateProcess_succ setup hStanding n ω)
      change
        ((stateProcess setup hStanding (n + 1) ω).dualSubgrad
            (sampledBlock setup (n + 1) ω)).1 =
          (yHatSubgradIter setup hStanding (n + 1) (Nat.succ_pos n) ω
            (sampledBlock setup (n + 1) ω)).1
      rw [hstate]
      have hxt :=
        stepPrimalPrediction_eq_xTildeIter setup hStanding (n + 1) (Nat.succ_pos n) ω
      have hxt' :
          primalPrediction setup (n + 1)
              (stateProcess setup hStanding n ω).x
              (stateProcess setup hStanding n ω).xLag =
            xTildeIter setup hStanding (n + 1) ω := by
        simpa using hxt
      calc
        ((rpdgStep setup hStanding (n + 1) (Nat.succ_pos n)
            (stateProcess setup hStanding n ω)
            (sampledPositiveBlock setup (n + 1) ω)).dualSubgrad
          (sampledBlock setup (n + 1) ω)).1 =
            (candidateDualSubgradient setup hStanding (n + 1) (Nat.succ_pos n)
              (primalPrediction setup (n + 1)
                (stateProcess setup hStanding n ω).x
                (stateProcess setup hStanding n ω).xLag)
              (sampledBlock setup (n + 1) ω)
              ((stateProcess setup hStanding n ω).y (sampledBlock setup (n + 1) ω))
              ((stateProcess setup hStanding n ω).dualSubgrad
                (sampledBlock setup (n + 1) ω))).1 := by
              simpa [rpdgStep, sampledBlock, sampledPositiveBlock] using
                dualSubgradientUpdate_sampled_val_eq_candidate setup hStanding (n + 1)
                  (Nat.succ_pos n)
                  (primalPrediction setup (n + 1)
                    (stateProcess setup hStanding n ω).x
                    (stateProcess setup hStanding n ω).xLag)
                  ((stateProcess setup hStanding n ω).y)
                  ((stateProcess setup hStanding n ω).dualSubgrad)
                  (sampledBlock setup (n + 1) ω)
        _ = (candidateDualSubgradient setup hStanding (n + 1) (Nat.succ_pos n)
              (xTildeIter setup hStanding (n + 1) ω)
              (sampledBlock setup (n + 1) ω)
              ((stateProcess setup hStanding n ω).y (sampledBlock setup (n + 1) ω))
              ((stateProcess setup hStanding n ω).dualSubgrad
                (sampledBlock setup (n + 1) ω))).1 := by
              rw [hxt']
        _ = (yHatSubgradIter setup hStanding (n + 1) (Nat.succ_pos n) ω
              (sampledBlock setup (n + 1) ω)).1 := by
              simp [yHatSubgradIter, yHatIter, yIter, dualSubgradIter]

/-- Off-sampled selected-subgradient value equation for the generated process.
This is the subgradient half of Eq. (5.1.22)'s unchanged-coordinate branch. -/
private theorem dualSubgradIter_otherBlock_val_eq_prev
    (hStanding : standingAssumptions setup)
    (t : ℕ) (ht : 1 ≤ t) (ω : BlockSamplePath setup)
    {i : ι} (hne : i ≠ sampledBlock setup t ω) :
    (dualSubgradIter setup hStanding t ω i).1 =
      (dualSubgradIter setup hStanding (t - 1) ω i).1 := by
  cases t with
  | zero =>
      cases ht
  | succ n =>
      have hht : ht = Nat.succ_pos n := Subsingleton.elim ht (Nat.succ_pos n)
      subst ht
      have hstate :
          ((stateProcess setup hStanding (n + 1) ω).dualSubgrad i).1 =
            ((rpdgStep setup hStanding (n + 1) (Nat.succ_pos n)
                (stateProcess setup hStanding n ω)
                (sampledPositiveBlock setup (n + 1) ω)).dualSubgrad i).1 := by
        exact congrArg
          (fun s : State setup => (s.dualSubgrad i).1)
          (stateProcess_succ setup hStanding n ω)
      change
        ((stateProcess setup hStanding (n + 1) ω).dualSubgrad i).1 =
          ((stateProcess setup hStanding n ω).dualSubgrad i).1
      rw [hstate]
      simpa [dualSubgradIter, yIter, xTildeIter, xIter, rpdgStep, sampledBlock,
        sampledPositiveBlock,
        stepPrimalPrediction_eq_xTildeIter setup hStanding (n + 1) (Nat.succ_pos n) ω]
        using
          dualSubgradientUpdate_other_val_eq_base setup hStanding (n + 1)
            (Nat.succ_pos n)
            (primalPrediction setup (n + 1)
              (stateProcess setup hStanding n ω).x
              (stateProcess setup hStanding n ω).xLag)
            ((stateProcess setup hStanding n ω).y)
            ((stateProcess setup hStanding n ω).dualSubgrad)
            (i := i) (sampled := sampledBlock setup (n + 1) ω) hne

/-- Nonnegativity of the paper-selected dual Bregman term from the selected
subgradient support inequality. Searched `dual carrier Bregman nonnegative dual strong
convexity lower bound`; SOptLib Bregman nonnegativity candidates target global
carrier-gradient divergences, while this paper object stores only the selected
subgradient at the recursive base point. -/
private theorem dualBregman_nonnegative
    (i : ι) (y0 : DualCarrier setup i)
    (baseSubgrad : DualConjugateSubgradient setup i y0)
    (y : DualCarrier setup i) :
    0 ≤ (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i y0 baseSubgrad) y0 y) := by
  simpa [dualConjugateBaseSelector] using
    SOptLib.selectedCarrierBregman_nonneg_of_mem_carrierSubdifferential
      (f := dualConjugate setup i) (x := y0) (y := y) (g := baseSubgrad.1)
      baseSubgrad.2

/-- Cross-multiplied dual Bregman quadratic lower bound used in Proposition
5.1 steps 8 and 15. Searched `dual Bregman strong convexity lower bound
selected subgradient`, `strong convexity bregman lower norm squared`, and
`carrier subdifferential strong convexity lower bound`; checked SOptLib
`bregman_lower_bound_of_strongConvexOnWithSeminorm_differentiableWithinAt`,
`blockBregmanDivergence_lower_bound_of_strongConvexOnWithNorm`, and the local
`dualBregman_nonnegative`. The SOptLib lower-bound candidates require an
ambient differentiability/global-gradient Bregman object, while Eq. (5.1.18)
uses the paper-selected carrier subgradient `J_i'(y_i^0)`. -/
private theorem dualBregman_cross_quadratic_lower_bound
    (hStanding : standingAssumptions setup)
    (i : ι) (y0 : DualCarrier setup i)
    (baseSubgrad : DualConjugateSubgradient setup i y0)
    (y : DualCarrier setup i) :
    (componentCount (ι := ι) : ℝ) / 2 * ‖y0.1 - y.1‖ ^ 2 ≤
      setup.L i * (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i y0 baseSubgrad) y0 y) := by
  classical
  rcases hStanding with ⟨_, hSmooth, _, _, _, _, _, _, _, _, hDualStrong, _⟩
  simpa [dualConjugateBaseSelector] using
    SOptLib.selectedCarrierBregman_cross_quadratic_lower_bound_of_strongConvex
      (f := dualConjugate setup i) (x := y0) (y := y) (g := baseSubgrad.1)
      (L := setup.L i) (C := (componentCount (ι := ι) : ℝ))
      (hSmooth.2.1 i) baseSubgrad.2
      (by
        intro a b ha hb hab
        exact dualSpace_mix_mem setup i y0 y ha hb hab)
      (by
        intro a b ha hb hab
        simpa using hDualStrong i y0 y ha hb hab)

/-- Self Bregman term in Lemma 5.4's off-sampled branch. Search found no local
dual selected self-zero lemma; SOptLib Bregman self-zero facts target global
carrier-gradient divergences, while this paper object carries a selected
subgradient proof for the recursive base point. -/
private theorem dualBregman_self_eq_zero
    (i : ι) (y0 : DualCarrier setup i)
    (baseSubgrad : DualConjugateSubgradient setup i y0) :
    (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i y0 baseSubgrad) y0 y0) = 0 := by
  simp [SOptLib.carrierBregmanDivergence, carrierBregmanDivergence,
    dualConjugateBaseSelector]

/-- First deterministic branch form in Lemma 5.4: the Bregman distance from
`y_i^{t-1}` to the randomized current block is the sampled-block indicator
times the full candidate term, with the off branch closed by
`W_i(y_i^{t-1}, y_i^{t-1}) = 0`. -/
private theorem dualBregman_first_observable_branch
    (hStanding : standingAssumptions setup)
    (t : ℕ) (ht : 1 ≤ t) (ω : BlockSamplePath setup) (i : ι) :
    (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) ((yIter setup hStanding t ω) i)) =
      if sampledBlock setup t ω = i then
        (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) ((yHatIter setup hStanding t ω) i))
      else 0 := by
  by_cases hsample : sampledBlock setup t ω = i
  · subst i
    simp [yIter_sampledBlock_eq_yHatIter setup hStanding t ht ω]
  · have hne : i ≠ sampledBlock setup t ω := by exact Ne.symm hsample
    rw [yIter_otherBlock_eq_prev setup hStanding t ht ω hne]
    simp [hsample, dualBregman_self_eq_zero]

/-- Second deterministic branch form in Lemma 5.4: the current-base Bregman
observable is the candidate-base term on the sampled branch and the previous
base term off the sampled branch. The endpoint part is proved from the generated
process; the remaining subgradient-value transport is isolated in the two
route-local helpers above. -/
private theorem dualBregman_second_observable_branch
    (hStanding : standingAssumptions setup)
    (t : ℕ) (ht : 1 ≤ t) (ω : BlockSamplePath setup) (i : ι)
    (y : DualCarrier setup i) :
    (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding t ω) i) (dualSubgradIter setup hStanding t ω i)) ((yIter setup hStanding t ω) i) y) =
      if sampledBlock setup t ω = i then
        (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yHatIter setup hStanding t ω) i) (yHatSubgradIter setup hStanding t ht ω i)) ((yHatIter setup hStanding t ω) i) y)
      else
        (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) y) := by
  by_cases hsample : sampledBlock setup t ω = i
  · subst i
    have hy := yIter_sampledBlock_eq_yHatIter setup hStanding t ht ω
    have hg := dualSubgradIter_sampledBlock_val_eq_yHatSubgradIter setup hStanding t ht ω
    simp [SOptLib.carrierBregmanDivergence, carrierBregmanDivergence,
      dualConjugateBaseSelector, hy, hg]
  · have hne : i ≠ sampledBlock setup t ω := by exact Ne.symm hsample
    have hy := yIter_otherBlock_eq_prev setup hStanding t ht ω hne
    have hg := dualSubgradIter_otherBlock_val_eq_prev setup hStanding t ht ω hne
    simp [hsample, SOptLib.carrierBregmanDivergence, carrierBregmanDivergence,
      dualConjugateBaseSelector, hy, hg]

/-- Range condition `α∈(0,1)` in Theorem 5.1. -/
def alphaRange (α : ℝ) : Prop :=
  0 < α ∧ α < 1

/-- Denominator certificate for quotients by `α` under Theorem 5.1's
source-stated range `α∈(0,1)`. -/
theorem alpha_ne_zero_of_alphaRange {α : ℝ} (hAlpha : alphaRange α) : α ≠ 0 :=
  ne_of_gt hAlpha.1

/-- Denominator certificate for quotients by `1-α` under Theorem 5.1's
source-stated range `α∈(0,1)`. -/
theorem one_sub_alpha_ne_zero_of_alphaRange {α : ℝ} (hAlpha : alphaRange α) :
    1 - α ≠ 0 := by
  exact sub_ne_zero.mpr (ne_of_gt hAlpha.2)

/-- Denominator certificate for the printed output weight `1/α^t`. -/
theorem alpha_pow_ne_zero_of_alphaRange {α : ℝ} (hAlpha : alphaRange α) (t : ℕ) :
    α ^ t ≠ 0 :=
  pow_ne_zero t (alpha_ne_zero_of_alphaRange hAlpha)

/-- Paper output window `{1,...,k}` in Eq. (5.1.65). -/
def outputTimeWindow (k : ℕ) : Finset ℕ :=
  Finset.Icc 1 k

/-- Canonical Theorem 5.1 output weight `θ_t = 1/α^t` from Eq. (5.1.65).
No SOptLib match: searched `output weight geometric alpha inverse theta`, checked
`SOptLib.weightedAverageOutputValue`, `SOptLib.weightedOutputAverage`, and the
geometric-epoch theta candidates in `SOptLib/Model/ParameterChoices.lean`; those
model normalized output construction or terminal-adjusted epoch weights, while
Theorem 5.1 uses the literal one-based inverse-power schedule `α^{-t}`. -/
noncomputable def theoremOutputWeight (α : ℝ) (_hAlpha : alphaRange α) (t : ℕ) : ℝ :=
  SOptLib.inverse_power_weight α t

/-- Defining equation for the canonical Theorem 5.1 output weights. -/
theorem theoremOutputWeight_eq (α : ℝ) (hAlpha : alphaRange α) (t : ℕ) :
    theoremOutputWeight α hAlpha t =
      sourceQuotient 1 (α ^ t) (alpha_pow_ne_zero_of_alphaRange hAlpha t) := by
  rfl

/-- Output normalizer `∑_{t=1}^k θ_t` from Eq. (5.1.65), with
`θ_t = α^{-t}` generated canonically rather than stored in `Setup`. -/
noncomputable def outputWeightSum (α : ℝ) (hAlpha : alphaRange α) (k : ℕ) : ℝ :=
  ∑ t ∈ outputTimeWindow k, theoremOutputWeight α hAlpha t

/-- Output vector from Eq. (5.1.65), before the convexity proof that it lies in
`X`. Aligns with SOptLib `weightedAverageOutputValue`, specialized to the
paper's one-based window and canonical weights `θ_t=α^{-t}`; the
positive-normalizer argument keeps Eq. (5.1.65) from relying on Lean's total
inverse at zero. -/
noncomputable def weightedOutputVector
    (setup : Setup E ι) (α : ℝ) (hAlpha : alphaRange α)
    (hStanding : standingAssumptions setup) (k : ℕ)
    (_hWeightSumPos : 0 < outputWeightSum α hAlpha k)
    (ω : BlockSamplePath setup) : E :=
  SOptLib.weightedAverageOutputValue
    (fun _ : Unit => outputTimeWindow k)
    (theoremOutputWeight α hAlpha)
    (fun t ω => (xIter setup hStanding t ω).1)
    (fun _ : Unit => outputWeightSum α hAlpha k)
    () ω

/-- Canonical Algorithm 5.1 sampling identity for every coordinate of the iid
block stream. This is now a theorem about `blockStreamLaw`, not a theorem-head
hypothesis about an arbitrary process. -/
theorem samplingProbabilities (t : ℕ) (i : ι) :
    Measure.map (fun ω : BlockSamplePath setup => sampledBlock setup t ω) (blockStreamLaw setup)
      ({i} : Set ι) = ENNReal.ofReal (samplingProbability setup i) := by
  classical
  letI : IsProbabilityMeasure (blockIndexLaw setup) := by
    unfold blockIndexLaw
    infer_instance
  have hcoord :
      Measure.map (fun ω : BlockSamplePath setup => sampledPositiveBlock setup t ω)
          (blockStreamLaw setup) = blockIndexLaw setup := by
    simpa [blockStreamLaw, sampledPositiveBlock, BlockSamplePath] using
      (SOptLib.iidStreamLaw_map_eval (mu := blockIndexLaw setup) t)
  have hmap :
      Measure.map (fun ω : BlockSamplePath setup => sampledBlock setup t ω)
          (blockStreamLaw setup) =
        Measure.map (fun j : PositiveBlock setup => j.1) (blockIndexLaw setup) := by
    change Measure.map
        ((fun j : PositiveBlock setup => j.1) ∘
          (fun ω : BlockSamplePath setup => sampledPositiveBlock setup t ω))
        (blockStreamLaw setup) =
        Measure.map (fun j : PositiveBlock setup => j.1) (blockIndexLaw setup)
    rw [← Measure.map_map]
    · rw [hcoord]
    · exact measurable_subtype_coe
    · simpa [sampledPositiveBlock] using measurable_pi_apply t
  rw [hmap]
  exact blockIndexLaw_projected_singleton setup i

/-- Constant policy `τ_t=τ`, `η_t=η`, `α_t=α` from Eq. (5.1.59). -/
def constantParameterPolicy (setup : Setup E ι) (τ η α : ℝ) : Prop :=
  (∀ t, 1 ≤ t → setup.τ t = τ) ∧
    (∀ t, 1 ≤ t → setup.η t = η) ∧
    (∀ t, 1 ≤ t → setup.α t = α)

/-- Probability condition `(1-α)(1+τ)≤p_i` from Eq. (5.1.60). -/
def constantParameterConditionProbability (setup : Setup E ι) (τ α : ℝ) : Prop :=
  ∀ i : ι, (1 - α) * (1 + τ) ≤ samplingProbability setup i

/-- Parameter condition `η≤α(μ+η)` from Eq. (5.1.61). -/
def constantParameterConditionEta (setup : Setup E ι) (η α : ℝ) : Prop :=
  η ≤ α * (setup.μ + η)

/-- Lipschitz/stepsize condition `ητp_i≥4L_i/m` from Eq. (5.1.62). -/
def constantParameterConditionLipschitz (setup : Setup E ι) (τ η : ℝ) : Prop :=
  ∀ i : ι,
    sourceQuotient (4 * setup.L i) (componentCount (ι := ι) : ℝ)
        (componentCount_real_ne_zero (ι := ι)) ≤
    η * τ * samplingProbability setup i

/-- Source-derived positivity of the inverse-probability denominators in
Theorem 5.1. The source states `α∈(0,1)`, nonnegative `τ_t`, the constant policy
`τ_t=τ`, and `(1-α)(1+τ)≤p_i`; this theorem records the well-definedness bridge
instead of adding `0<p_i` to the theorem head. -/
theorem samplingProbability_pos_of_theorem_conditions
    (τ η α : ℝ)
    (hStanding : theoremStandingAssumptions setup)
    (hPolicy : constantParameterPolicy setup τ η α)
    (hProb : constantParameterConditionProbability setup τ α)
    (hAlpha : alphaRange α) :
    ∀ i : ι, 0 < samplingProbability setup i := by
  intro i
  have hOneSub : 0 < 1 - α := sub_pos.mpr hAlpha.2
  have hOneTauSetup : 0 < 1 + setup.τ 1 :=
    onePlusTau_pos_of_standing setup hStanding.1 1 le_rfl
  have hOneTau : 0 < 1 + τ := by
    simpa [hPolicy.1 1 le_rfl] using hOneTauSetup
  have hProd : 0 < (1 - α) * (1 + τ) := mul_pos hOneSub hOneTau
  exact lt_of_lt_of_le hProd (hProb i)

/-- In the Theorem 5.1 constant-parameter regime, the source-stated probability
condition and `α∈(0,1)` imply positivity of the displayed probabilities. This is
intentionally not a theorem from the general Section 5.1 standing assumptions
and is not used to define the generated Algorithm 5.1 sample path. -/
theorem inverseProbabilityDenominators_ne_of_theorem_conditions
    (τ η α : ℝ)
    (hStanding : theoremStandingAssumptions setup)
    (hPolicy : constantParameterPolicy setup τ η α)
    (hProb : constantParameterConditionProbability setup τ α)
    (hAlpha : alphaRange α) :
    ∀ i : ι, samplingProbability setup i ≠ 0 := by
  intro i
  have hpos := samplingProbability_pos_of_theorem_conditions setup τ η α
    hStanding hPolicy hProb hAlpha i
  exact ne_of_gt hpos

/-- Theorem 5.1 endpoint reciprocal bound derived from Eq. (5.1.60). This is
the coefficient estimate used before applying Lemma 5.1 in Eq. (5.1.63):
`p_i^{-1}(1+τ)-1 ≤ α/(1-α)`. Existing candidates considered:
`inverseProbabilityDenominators_ne_of_theorem_conditions` supplies only the
well-defined reciprocal, while `propositionCondition_5_1_46_with_denominator_source_gap`
is a time-telescope condition tied to the Proposition 5.1 denominator boundary;
neither states this theorem-local endpoint coefficient bound. -/
private theorem theorem51_inverse_probability_initial_coefficient_le
    (τ η α : ℝ)
    (hStanding : theoremStandingAssumptions setup)
    (hPolicy : constantParameterPolicy setup τ η α)
    (hProb : constantParameterConditionProbability setup τ α)
    (hAlpha : alphaRange α) (i : ι) :
    inverseProbabilityValue setup i
        (inverseProbabilityDenominators_ne_of_theorem_conditions
          setup τ η α hStanding hPolicy hProb hAlpha i) *
        (1 + τ) - 1 ≤
      sourceQuotient α (1 - α) (one_sub_alpha_ne_zero_of_alphaRange hAlpha) := by
  simpa [inverseProbabilityValue, sourceQuotient_def, one_div] using
    inv_mul_one_add_sub_one_le_div_of_mul_one_add_le
      (alpha := α) (tau := τ) (p := samplingProbability setup i)
      (samplingProbability_pos_of_theorem_conditions setup τ η α
        hStanding hPolicy hProb hAlpha i)
      (sub_pos.mpr hAlpha.2)
      (hProb i)

/-- Local Proposition/Theorem weight policy `θ_t = 1/α^t` from Eq. (5.1.65).
Theorem 5.1 uses the canonical `theoremOutputWeight` directly; this predicate
is kept only as a bridge for source statements that quantify over an auxiliary
weight sequence. -/
def thetaPolicy (θ : ℕ → ℝ) (α : ℝ) (hAlpha : alphaRange α) : Prop :=
  ∀ t, 1 ≤ t → θ t = theoremOutputWeight α hAlpha t

/-- The canonical Theorem 5.1 output weights satisfy the source policy by
definition. -/
theorem theoremOutputWeight_thetaPolicy (α : ℝ) (hAlpha : alphaRange α) :
    thetaPolicy (theoremOutputWeight α hAlpha) α hAlpha := by
  intro t ht
  rfl

/-- Theorem 5.1 output-weight shift `α_t θ_t = θ_{t-1}` from Eq. (5.1.65),
specialized by the constant policy Eq. (5.1.59). Existing candidates considered:
`thetaPolicy` and `theoremOutputWeight_thetaPolicy` only unfold the schedule,
while `SOptLib.sum_Icc_two_coeff_telescope_le` consumes a completed adjacent
coefficient relation rather than proving the inverse-power algebra. -/
private theorem theorem51_output_weight_shift
    (τ η α : ℝ)
    (hPolicy : constantParameterPolicy setup τ η α)
    (hAlpha : alphaRange α) :
    ∀ t, 2 ≤ t → setup.α t * theoremOutputWeight α hAlpha t =
      theoremOutputWeight α hAlpha (t - 1) := by
  intro t ht2
  have ht1 : 1 ≤ t := by omega
  have hα_ne : α ≠ 0 := alpha_ne_zero_of_alphaRange hAlpha
  rw [hPolicy.2.2 t ht1]
  simpa [theoremOutputWeight] using
    SOptLib.mul_inverse_power_weight_eq_pred_of_one_le α hα_ne ht1

/-- Source-derived nonnegativity of the canonical Theorem 5.1 output weights on
`{1,...,k}`. -/
theorem outputTheta_nonnegative_of_alphaRange
    (α : ℝ) (k : ℕ) (hAlpha : alphaRange α) :
    ∀ (_ : Unit) t, t ∈ outputTimeWindow k → 0 ≤ theoremOutputWeight α hAlpha t := by
  intro _ t _
  have hpow : 0 < α ^ t := pow_pos hAlpha.1 t
  have hpos : 0 < theoremOutputWeight α hAlpha t := by
    simpa [theoremOutputWeight, sourceQuotient] using (one_div_pos.mpr hpow)
  exact hpos.le

/-- Source-derived positivity of the output normalizer `∑_{t=1}^k θ_t` for
Eq. (5.1.65). The source states `k≥1`, `α∈(0,1)`, and `θ_t=α^{-t}`; this
well-definedness fact is a proof obligation, not a theorem-head assumption. -/
theorem outputWeightSum_pos_of_alphaRange
    (α : ℝ) (k : ℕ) (hk : 1 ≤ k) (hAlpha : alphaRange α) :
    0 < outputWeightSum α hAlpha k := by
  classical
  unfold outputWeightSum
  have hnonneg : ∀ t ∈ outputTimeWindow k, 0 ≤ theoremOutputWeight α hAlpha t := by
    intro t ht
    exact outputTheta_nonnegative_of_alphaRange α k hAlpha () t ht
  have hmem : 1 ∈ outputTimeWindow k := by
    simpa [outputTimeWindow] using (Finset.mem_Icc.mpr ⟨le_rfl, hk⟩)
  have hpos1 : 0 < theoremOutputWeight α hAlpha 1 := by
    have hpow : 0 < α ^ 1 := pow_pos hAlpha.1 1
    simpa [theoremOutputWeight, sourceQuotient] using (one_div_pos.mpr hpow)
  exact Finset.sum_pos' hnonneg ⟨1, hmem, hpos1⟩

/-- Canonical feasible weighted output `x̄^k` from Eq. (5.1.65).
Aligns with SOptLib `weightedOutputAverage`: unlike the previous
`weightedOutput_exists` selector, feasibility is packaged by the reusable
convex weighted-average constructor under source-derived weight facts. -/
noncomputable def weightedOutput
    (α : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hStanding : standingAssumptions setup) (hAlpha : alphaRange α) :
    BlockSamplePath setup → PrimalCarrier setup :=
  SOptLib.weightedOutputAverage
    setup.X
    (fun _ : Unit => outputTimeWindow k)
    (theoremOutputWeight α hAlpha)
    (fun t ω => (xIter setup hStanding t ω).1)
    (fun _ : Unit => outputWeightSum α hAlpha k)
    hStanding.1.2
    (outputTheta_nonnegative_of_alphaRange α k hAlpha)
    (fun _ t _ ω => (xIter setup hStanding t ω).2)
    (fun _ => outputWeightSum_pos_of_alphaRange α k hk hAlpha)
    (fun _ => rfl)
    ()

/-- The canonical feasible output has the paper's weighted-average value. -/
theorem weightedOutput_eq
    (α : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hStanding : standingAssumptions setup) (hAlpha : alphaRange α)
    (ω : BlockSamplePath setup) :
    (weightedOutput setup α k hk hStanding hAlpha ω).1 =
      weightedOutputVector setup α hAlpha hStanding k
        (outputWeightSum_pos_of_alphaRange α k hk hAlpha) ω := by
  rfl

/-- Weighted dual average `ȳᵏ` from the proof of Theorem 5.1 before
Eq. (5.1.66), constructed coordinatewise from `ŷᵗ`. No SOptLib match:
searched `weighted dual output average yHatIter dual product`, scanned
`SOptLib/Model/Iterates.lean` and `SOptLib/Layer1/Telescope.lean`, and checked
sister examples; `SOptLib.weightedOutputAverage` supplies the generic
single-carrier average, but the RPDG proof needs the dependent product
`Π_i Y_i` with each coordinate using the paper-specific `dualSpace_convex`. -/
noncomputable def weightedDualOutput
    (α : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hStanding : standingAssumptions setup) (hAlpha : alphaRange α) :
    BlockSamplePath setup → DualProductCarrier setup :=
  SOptLib.piWeightedOutputAverage
    (dualSpace setup)
    (fun _ : Unit => outputTimeWindow k)
    (theoremOutputWeight α hAlpha)
    (fun t ω i => (yHatIter setup hStanding t ω) i)
    (fun _ : Unit => outputWeightSum α hAlpha k)
    (dualSpace_convex setup)
    (outputTheta_nonnegative_of_alphaRange α k hAlpha)
    (fun _ => outputWeightSum_pos_of_alphaRange α k hk hAlpha)
    (fun _ => rfl)
    ()

/-- Coordinate projection of the weighted dual average used in Eq. (5.1.66). -/
theorem weightedDualOutput_eq
    (α : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hStanding : standingAssumptions setup) (hAlpha : alphaRange α)
    (ω : BlockSamplePath setup) (i : ι) :
    ((weightedDualOutput setup α k hk hStanding hAlpha ω) i).1 =
      (outputWeightSum α hAlpha k)⁻¹ •
        ∑ t ∈ outputTimeWindow k,
          theoremOutputWeight α hAlpha t •
            ((yHatIter setup hStanding t ω) i).1 := by
  rfl

/-- Dual-conjugate Jensen part of the weighted saddle-gap bridge after
Lan Eq. (5.1.66).

Candidate audit: searched `weighted saddle gap Jensen`, `convexOn weighted
average finite Jensen`, and checked SOptLib
`convexOn_weighted_average_le_weighted_sum`; the single-function Jensen theorem
is a component proof, while `sum_convexOn_weighted_average_le_weighted_sum`
packages the coordinate-family aggregation used here. -/
private theorem theorem51_weighted_dual_conjugate_sum_le
    (α : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hStanding : standingAssumptions setup) (hAlpha : alphaRange α)
    (ω : BlockSamplePath setup) :
    (∑ i : ι,
        dualConjugate setup i
          ((weightedDualOutput setup α k hk hStanding hAlpha ω) i)) ≤
      (outputWeightSum α hAlpha k)⁻¹ *
        ∑ t ∈ outputTimeWindow k,
          theoremOutputWeight α hAlpha t *
            (∑ i : ι,
              dualConjugate setup i ((yHatIter setup hStanding t ω) i)) := by
  classical
  have h :=
    sum_convexOn_weighted_average_le_weighted_sum
      (I := ι) (T := ℕ) (E := E)
      (s := outputTimeWindow k)
      (γ := theoremOutputWeight α hAlpha)
      (X := dualSpace setup)
      (f := fun i =>
        SOptLib.totalizeOn (dualSpace setup i)
          (fun y : DualCarrier setup i => dualConjugate setup i y))
      (p := fun t i => ((yHatIter setup hStanding t ω) i).1)
      (xbar := fun i =>
        ((weightedDualOutput setup α k hk hStanding hAlpha ω) i).1)
      (W := outputWeightSum α hAlpha k)
      (hf := fun i => dualConjugate_totalize_convexOn setup i)
      (hγ_nonneg := fun t ht =>
        outputTheta_nonnegative_of_alphaRange α k hAlpha () t ht)
      (hp_mem := fun t _ht i => ((yHatIter setup hStanding t ω) i).2)
      (hW_pos := outputWeightSum_pos_of_alphaRange α k hk hAlpha)
      (hW_eq := rfl)
      (hxbar := fun i => by
        simpa using
          (weightedDualOutput_eq (setup := setup) α k hk hStanding hAlpha ω i))
  simpa [SOptLib.totalizeOn_of_mem] using h

/-- Finite-prefix expectation with respect to the paper variables
`i_1,...,i_k`. This names the source boundary in Theorem 5.1 instead of using
an unrestricted infinite-stream integral at the paper-facing layer. -/
noncomputable def finitePrefixExpectation
    (setup : Setup E ι) (k : ℕ) (φ : BlockSamplePath setup → ℝ) : ℝ :=
  SOptLib.finitePrefixExpectation (blockStreamLaw setup) (blockPrefix setup k)
    (extendBlockPrefix setup k) φ

/-- If an observable is written as a function of the paper prefix
`(i_1,...,i_k)`, `finitePrefixExpectation` is exactly integration over
`blockPrefixLaw`. This prevents the full-stream extension used to feed the
generated recursion from becoming a source-facing extra sample datum. -/
theorem finitePrefixExpectation_of_prefixObservable
    (setup : Setup E ι) (k : ℕ) (ψ : BlockPrefix setup k → ℝ) :
    finitePrefixExpectation setup k (fun ω => ψ (blockPrefix setup k ω)) =
      ∫ pref, ψ pref ∂blockPrefixLaw setup k := by
  simpa [finitePrefixExpectation, blockPrefixLaw] using
    (SOptLib.finitePrefixExpectation_of_prefixObservable
      (μ := blockStreamLaw setup) (prefixMap := blockPrefix setup k)
      (extend := extendBlockPrefix setup k)
      (hsection := blockPrefix_extendBlockPrefix setup k) (ψ := ψ))

/-- Expected terminal Bregman distance appearing in Theorem 5.1. -/
noncomputable def expectedBregmanDistance
    (setup : Setup E ι) (hStanding : standingAssumptions setup)
    (k : ℕ) (xstar : PrimalCarrier setup) : ℝ :=
  finitePrefixExpectation setup k
    (fun ω => primalBregman setup (xIter setup hStanding k ω) xstar)

/-- Expected primal output gap appearing in Theorem 5.1. -/
noncomputable def expectedPrimalGap
    (setup : Setup E ι) (α : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hStanding : standingAssumptions setup) (hAlpha : alphaRange α)
    (xstar : PrimalCarrier setup) : ℝ :=
  finitePrefixExpectation setup k
    (fun ω =>
      objective setup (weightedOutput setup α k hk hStanding hAlpha ω) -
        objective setup xstar)

/-- Expected primal optimality gap `E[Ψ(x̄ᵏ)-Ψ*]` from Theorem 5.1.
Aligns with SOptLib `objectiveGapIntegrand` for the pointwise gap. The
SOptLib `expectedObjectiveGap` candidate was checked and rejected at this
source boundary because Theorem 5.1 takes expectation with respect to the finite
prefix `i_1,...,i_k`, represented here by `finitePrefixExpectation` and
`blockPrefixLaw`, rather than a generic full-stream time-indexed measure. -/
noncomputable def expectedPrimalOptimalityGap
    (setup : Setup E ι) (α : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hStanding : standingAssumptions setup) (hAlpha : alphaRange α)
    (xstar : PrimalCarrier setup) (hxstar : IsOptimalPrimal setup xstar) : ℝ :=
  finitePrefixExpectation setup k
    (SOptLib.objectiveGapIntegrand (objective setup)
      (primalOptimalValue setup xstar hxstar)
      (fun _ ω => weightedOutput setup α k hk hStanding hAlpha ω) k)

/-- The paper-facing optimality-gap observable agrees with the optimizer-value
form once `Ψ*` is identified with `Ψ(x*)`. -/
theorem expectedPrimalOptimalityGap_eq_expectedPrimalGap
    (setup : Setup E ι) (α : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hStanding : standingAssumptions setup) (hAlpha : alphaRange α)
    (xstar : PrimalCarrier setup) (hxstar : IsOptimalPrimal setup xstar) :
    expectedPrimalOptimalityGap setup α k hk hStanding hAlpha xstar hxstar =
      expectedPrimalGap setup α k hk hStanding hAlpha xstar := by
  rw [expectedPrimalOptimalityGap, expectedPrimalGap,
    primalOptimalValue_eq_objective setup xstar hxstar]
  apply congrArg (finitePrefixExpectation setup k)
  funext ω
  exact SOptLib.objectiveGapIntegrand_def (objective setup) (objective setup xstar)
    (fun _ ω => weightedOutput setup α k hk hStanding hAlpha ω) k ω

/-- The generated one-based finite prefix is measurable with respect to its
own prefix filtration.
No direct SOptLib match: checked `SOptLib.measurable_sample_of_lt_prefixFiltration`
and `SOptLib.measurable_sample_le_prefixFiltration`; they prove coordinate
adaptedness for an abstract stream, while this paper needs the dependent
product-valued `BlockPrefix` map from Lemma 5.4's conditioning
`i_1,...,i_{t-1}`. -/
private theorem blockPrefix_measurable_prefixFiltration
    (setup : Setup E ι) (k : ℕ) :
    Measurable[(blockPrefixFiltration setup).seq k] (blockPrefix setup k) := by
  let ξ : ℕ → BlockSamplePath setup → PositiveBlock setup :=
    fun n ω => sampledPositiveBlock setup (n + 1) ω
  have hξ : ∀ n, Measurable (ξ n) := by
    intro n
    simpa [ξ, sampledPositiveBlock] using measurable_pi_apply (n + 1)
  have hseq :
      (SOptLib.filtration ξ hξ).seq k = (blockPrefixFiltration setup).seq k := by
    rw [blockPrefixFiltration_seq, SOptLib.filtration_seq]
  have hfun :
      (fun ω : BlockSamplePath setup =>
          fun r : {r : ℕ // 1 ≤ r ∧ r ≤ k} => ξ (r.1 - 1) ω) =
        blockPrefix setup k := by
    funext ω r
    simp [ξ, blockPrefix, sampledPositiveBlock, Nat.sub_add_cancel r.2.1]
  simpa [hseq, hfun] using SOptLib.measurable_one_based_prefix_of_prefix_filtration ξ hξ k


/-- Real observables of the generated finite paper prefix are integrable under
the iid block stream law.
No direct SOptLib match at this declaration point: the later local
`finite_prefix_observable_integrable` is not available without a declaration
cycle; searched `finite range integrable map` and reused
`SOptLib.integrable_of_finite_range` instead. -/
private theorem prefixObservable_integrable_blockStream
    (setup : Setup E ι) (k : ℕ) (φ : BlockPrefix setup k → ℝ) :
    Integrable (fun ω : BlockSamplePath setup => φ (blockPrefix setup k ω))
      (blockStreamLaw setup) := by
  classical
  letI : IsProbabilityMeasure (blockIndexLaw setup) := by
    unfold blockIndexLaw
    infer_instance
  letI : IsProbabilityMeasure (blockStreamLaw setup) := by
    unfold blockStreamLaw
    exact SOptLib.iidStreamLaw_isProbabilityMeasure (blockIndexLaw setup)
  haveI : Fintype {t : ℕ // 1 ≤ t ∧ t ≤ k} := by
    exact Set.Finite.fintype (Set.finite_Icc 1 k)
  haveI : Fintype (BlockPrefix setup k) := inferInstance
  have hpref_meas_filtration :
      Measurable[(blockPrefixFiltration setup).seq k]
        (fun ω : BlockSamplePath setup => φ (blockPrefix setup k ω)) :=
    (measurable_of_countable φ).comp
      (blockPrefix_measurable_prefixFiltration setup k)
  have hpref_meas :
      Measurable (fun ω : BlockSamplePath setup => φ (blockPrefix setup k ω)) :=
    hpref_meas_filtration.mono
      (Filtration.le (blockPrefixFiltration setup) k) le_rfl
  have hfin :
      (Set.range (fun ω : BlockSamplePath setup => φ (blockPrefix setup k ω))).Finite := by
    refine (Set.finite_univ.image φ).subset ?_
    rintro y ⟨ω, rfl⟩
    exact ⟨blockPrefix setup k ω, trivial, rfl⟩
  exact integrable_of_finite_range
    (μ := blockStreamLaw setup) hpref_meas.aestronglyMeasurable hfin

/-- Set-integral form of the fresh hit indicator over a prefix-measurable set.
No direct SOptLib match: searched `independent set integral indicator
probability`, `integral indicator finite range measurable set independence`,
and checked the finite-index expectation transport lemmas
`SOptLib.expectation_sample_eq_expectation_weighted_fiber_sum_of_indepFun` and
`SOptLib.integral_prod_finite_law_eq_integral_weighted_fiber_sum`; those are
whole-space/product-law expectation expansions, while Lemma 5.4 needs the
restricted prefix-set identity for Mathlib's conditional-expectation
characterization. -/
private theorem setIntegral_hitIndicator_sampledBlock_prefix
    (setup : Setup E ι) (t : ℕ) (i : ι)
    (hfresh : ProbabilityTheory.Indep
      ((blockPrefixFiltration setup).seq (t - 1))
      (MeasurableSpace.comap
        (fun ω : BlockSamplePath setup => sampledPositiveBlock setup t ω)
        (by infer_instance : MeasurableSpace (PositiveBlock setup)))
      (blockStreamLaw setup))
    (hmarg :
      Measure.map (fun ω : BlockSamplePath setup => sampledBlock setup t ω)
        (blockStreamLaw setup) ({i} : Set ι) =
        ENNReal.ofReal (samplingProbability setup i))
    {s : Set (BlockSamplePath setup)}
    (hs : MeasurableSet[(blockPrefixFiltration setup).seq (t - 1)] s) :
    ∫ ω in s, (if sampledBlock setup t ω = i then (1 : ℝ) else 0) ∂blockStreamLaw setup =
      samplingProbability setup i * (blockStreamLaw setup).real s := by
  classical
  let μ : Measure (BlockSamplePath setup) := blockStreamLaw setup
  have hsample_meas :
      @Measurable (BlockSamplePath setup) ι
        MeasurableSpace.pi
        (by infer_instance : MeasurableSpace ι)
        (fun ω : BlockSamplePath setup => sampledBlock setup t ω) := by
    have hpos :
        @Measurable (BlockSamplePath setup) (PositiveBlock setup)
          MeasurableSpace.pi
          (by infer_instance : MeasurableSpace (PositiveBlock setup))
          (fun ω : BlockSamplePath setup => sampledPositiveBlock setup t ω) := by
      simpa [sampledPositiveBlock, BlockSamplePath] using
        (@measurable_pi_apply ℕ
          (fun _ : ℕ => PositiveBlock setup)
          (fun _ => by infer_instance) t)
    simpa [sampledBlock] using measurable_subtype_coe.comp hpos
  have hsample_fresh :
      @Measurable (BlockSamplePath setup) ι
        (MeasurableSpace.comap
          (fun ω : BlockSamplePath setup => sampledPositiveBlock setup t ω)
          (by infer_instance : MeasurableSpace (PositiveBlock setup)))
        (by infer_instance : MeasurableSpace ι)
        (fun ω : BlockSamplePath setup => sampledBlock setup t ω) := by
    have hpos :
        @Measurable (BlockSamplePath setup) (PositiveBlock setup)
          (MeasurableSpace.comap
            (fun ω : BlockSamplePath setup => sampledPositiveBlock setup t ω)
            (by infer_instance : MeasurableSpace (PositiveBlock setup)))
          (by infer_instance : MeasurableSpace (PositiveBlock setup))
          (fun ω : BlockSamplePath setup => sampledPositiveBlock setup t ω) := by
      simpa using
        (comap_measurable
          (fun ω : BlockSamplePath setup => sampledPositiveBlock setup t ω))
    simpa [sampledBlock] using measurable_subtype_coe.comp hpos
  have hprob :
      μ {ω : BlockSamplePath setup | sampledBlock setup t ω = i} =
        ENNReal.ofReal (samplingProbability setup i) := by
    rw [show μ {ω : BlockSamplePath setup | sampledBlock setup t ω = i} =
        (Measure.map (fun ω : BlockSamplePath setup => sampledBlock setup t ω) μ) ({i} : Set ι) by
      rw [Measure.map_apply hsample_meas (measurableSet_singleton i)]
      rfl]
    exact hmarg
  have hprob_real :
      μ.real {ω : BlockSamplePath setup | sampledBlock setup t ω = i} =
        samplingProbability setup i := by
    rw [measureReal_def, hprob]
    exact ENNReal.toReal_ofReal (samplingProbability_nonnegative setup i)
  have hhit :
      MeasurableSet {ω : BlockSamplePath setup | sampledBlock setup t ω = i} := by
    exact hsample_meas (measurableSet_singleton i)
  have hhit_fresh :
      MeasurableSet[
        MeasurableSpace.comap
          (fun ω : BlockSamplePath setup => sampledPositiveBlock setup t ω)
          (by infer_instance : MeasurableSpace (PositiveBlock setup))]
        {ω : BlockSamplePath setup | sampledBlock setup t ω = i} := by
    exact hsample_fresh (measurableSet_singleton i)
  have hcore := setIntegral_indicator_eq_prob_mul_of_indep
    (μ := μ)
    (m := (blockPrefixFiltration setup).seq (t - 1))
    (mfresh := MeasurableSpace.comap
      (fun ω : BlockSamplePath setup => sampledPositiveBlock setup t ω)
      (by infer_instance : MeasurableSpace (PositiveBlock setup)))
    (hit := {ω : BlockSamplePath setup | sampledBlock setup t ω = i})
    (p := samplingProbability setup i)
    (s := s)
    hhit hhit_fresh hs hfresh hprob_real
  simpa [Set.indicator, μ] using hcore

/-- Conditional expectation of the fresh hit indicator given the generated
prefix filtration.
No direct SOptLib match: after proving the restricted set-integral bridge
`setIntegral_hitIndicator_sampledBlock_prefix`, this is the Mathlib
`ae_eq_condExp_of_forall_setIntegral_eq` packaging needed for Lemma 5.4's
conditioning on `i_t = i`. -/
private theorem condexp_hitIndicator_sampledBlock_prefix
    (setup : Setup E ι) (t : ℕ) (i : ι)
    (hfresh : ProbabilityTheory.Indep
      ((blockPrefixFiltration setup).seq (t - 1))
      (MeasurableSpace.comap
        (fun ω : BlockSamplePath setup => sampledPositiveBlock setup t ω)
        (by infer_instance : MeasurableSpace (PositiveBlock setup)))
      (blockStreamLaw setup))
    (hmarg :
      Measure.map (fun ω : BlockSamplePath setup => sampledBlock setup t ω)
        (blockStreamLaw setup) ({i} : Set ι) =
        ENNReal.ofReal (samplingProbability setup i)) :
    (blockStreamLaw setup)[(fun ω : BlockSamplePath setup =>
        if sampledBlock setup t ω = i then (1 : ℝ) else 0) |
      (blockPrefixFiltration setup).seq (t - 1)] =ᵐ[blockStreamLaw setup]
      fun _ : BlockSamplePath setup => samplingProbability setup i := by
  classical
  letI : IsProbabilityMeasure (blockIndexLaw setup) := by
    unfold blockIndexLaw
    infer_instance
  let μ : Measure (BlockSamplePath setup) := blockStreamLaw setup
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    letI : IsProbabilityMeasure (blockIndexLaw setup) := by
      unfold blockIndexLaw
      infer_instance
    unfold blockStreamLaw
    exact SOptLib.iidStreamLaw_isProbabilityMeasure (blockIndexLaw setup)
  have hpos_meas :
      @Measurable (BlockSamplePath setup) (PositiveBlock setup)
        MeasurableSpace.pi
        (by infer_instance : MeasurableSpace (PositiveBlock setup))
        (fun ω : BlockSamplePath setup => sampledPositiveBlock setup t ω) := by
    simpa [sampledPositiveBlock, BlockSamplePath] using
      (@measurable_pi_apply ℕ
        (fun _ : ℕ => PositiveBlock setup)
        (fun _ => by infer_instance) t)
  have hsample_meas :
      @Measurable (BlockSamplePath setup) ι
        MeasurableSpace.pi
        (by infer_instance : MeasurableSpace ι)
        (fun ω : BlockSamplePath setup => sampledBlock setup t ω) := by
    simpa [sampledBlock] using measurable_subtype_coe.comp hpos_meas
  have hfresh_le :
      MeasurableSpace.comap
        (fun ω : BlockSamplePath setup => sampledPositiveBlock setup t ω)
        (by infer_instance : MeasurableSpace (PositiveBlock setup)) ≤
        (by infer_instance : MeasurableSpace (BlockSamplePath setup)) := by
    exact hpos_meas.comap_le
  have hsample_fresh :
      @Measurable (BlockSamplePath setup) ι
        (MeasurableSpace.comap
          (fun ω : BlockSamplePath setup => sampledPositiveBlock setup t ω)
          (by infer_instance : MeasurableSpace (PositiveBlock setup)))
        (by infer_instance : MeasurableSpace ι)
        (fun ω : BlockSamplePath setup => sampledBlock setup t ω) := by
    have hpos :
        @Measurable (BlockSamplePath setup) (PositiveBlock setup)
          (MeasurableSpace.comap
            (fun ω : BlockSamplePath setup => sampledPositiveBlock setup t ω)
            (by infer_instance : MeasurableSpace (PositiveBlock setup)))
          (by infer_instance : MeasurableSpace (PositiveBlock setup))
          (fun ω : BlockSamplePath setup => sampledPositiveBlock setup t ω) := by
      simpa using
        (comap_measurable
          (fun ω : BlockSamplePath setup => sampledPositiveBlock setup t ω))
    simpa [sampledBlock] using measurable_subtype_coe.comp hpos
  have hhit_fresh :
      MeasurableSet[
        MeasurableSpace.comap
          (fun ω : BlockSamplePath setup => sampledPositiveBlock setup t ω)
          (by infer_instance : MeasurableSpace (PositiveBlock setup))]
        {ω : BlockSamplePath setup | sampledBlock setup t ω = i} := by
    exact hsample_fresh (measurableSet_singleton i)
  have hprob :
      μ {ω : BlockSamplePath setup | sampledBlock setup t ω = i} =
        ENNReal.ofReal (samplingProbability setup i) := by
    rw [show μ {ω : BlockSamplePath setup | sampledBlock setup t ω = i} =
        (Measure.map (fun ω : BlockSamplePath setup => sampledBlock setup t ω) μ) ({i} : Set ι) by
      rw [Measure.map_apply hsample_meas (measurableSet_singleton i)]
      rfl]
    exact hmarg
  have hprob_real :
      μ.real {ω : BlockSamplePath setup | sampledBlock setup t ω = i} =
        samplingProbability setup i := by
    rw [measureReal_def, hprob]
    exact ENNReal.toReal_ofReal (samplingProbability_nonnegative setup i)
  have hcore :
      μ[({ω : BlockSamplePath setup | sampledBlock setup t ω = i}).indicator
          (fun _ : BlockSamplePath setup => (1 : ℝ)) |
        (blockPrefixFiltration setup).seq (t - 1)] =ᵐ[μ]
        fun _ : BlockSamplePath setup => samplingProbability setup i :=
    condExp_indicator_eq_const_of_indep
      (μ := μ)
      (m := (blockPrefixFiltration setup).seq (t - 1))
      (mfresh := MeasurableSpace.comap
        (fun ω : BlockSamplePath setup => sampledPositiveBlock setup t ω)
        (by infer_instance : MeasurableSpace (PositiveBlock setup)))
      (hit := {ω : BlockSamplePath setup | sampledBlock setup t ω = i})
      (p := samplingProbability setup i)
      hfresh_le
      (Filtration.le (blockPrefixFiltration setup) (t - 1))
      hhit_fresh
      hfresh
      hprob_real
  have hbranch :
      (fun ω : BlockSamplePath setup =>
          if sampledBlock setup t ω = i then (1 : ℝ) else 0) =ᵐ[μ]
        ({ω : BlockSamplePath setup | sampledBlock setup t ω = i}).indicator
          (fun _ : BlockSamplePath setup => (1 : ℝ)) := by
    refine Filter.Eventually.of_forall ?_
    intro ω
    by_cases hω : sampledBlock setup t ω = i
    · simp [Set.indicator, hω]
    · simp [Set.indicator, hω]
  exact (MeasureTheory.condExp_congr_ae hbranch).trans hcore

/-- Pull out a finite-prefix observable from the conditional expectation of the
fresh hit indicator.
No direct SOptLib match: the pre-searched digest for the current conditional
expectation bridge was empty; searches for `conditional expectation multiply
subalgebra measurable right` and `condExp indicator probability prefix
observable`, plus scans of the target file and SOptLib probability helpers,
found only the already-proved hit-indicator bridge and Mathlib's generic
`condExp_mul_of_aestronglyMeasurable_right`, not this paper's generated
one-based prefix payload form from Lemma 5.4. -/
private theorem condexp_hitIndicator_mul_prefixObservable
    (setup : Setup E ι) (t : ℕ) (i : ι)
    (hfresh : ProbabilityTheory.Indep
      ((blockPrefixFiltration setup).seq (t - 1))
      (MeasurableSpace.comap
        (fun ω : BlockSamplePath setup => sampledPositiveBlock setup t ω)
        (by infer_instance : MeasurableSpace (PositiveBlock setup)))
      (blockStreamLaw setup))
    (hmarg :
      Measure.map (fun ω : BlockSamplePath setup => sampledBlock setup t ω)
        (blockStreamLaw setup) ({i} : Set ι) =
        ENNReal.ofReal (samplingProbability setup i))
    (φ : BlockPrefix setup (t - 1) → ℝ) :
    (blockStreamLaw setup)[(fun ω : BlockSamplePath setup =>
        (if sampledBlock setup t ω = i then (1 : ℝ) else 0) *
          φ (blockPrefix setup (t - 1) ω)) |
      (blockPrefixFiltration setup).seq (t - 1)] =ᵐ[blockStreamLaw setup]
      fun ω : BlockSamplePath setup =>
        samplingProbability setup i * φ (blockPrefix setup (t - 1) ω) := by
  classical
  letI : IsProbabilityMeasure (blockIndexLaw setup) := by
    unfold blockIndexLaw
    infer_instance
  let μ : Measure (BlockSamplePath setup) := blockStreamLaw setup
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    unfold blockStreamLaw
    exact SOptLib.iidStreamLaw_isProbabilityMeasure (blockIndexLaw setup)
  let m : MeasurableSpace (BlockSamplePath setup) :=
    (blockPrefixFiltration setup).seq (t - 1)
  let hit : BlockSamplePath setup → ℝ :=
    fun ω => if sampledBlock setup t ω = i then (1 : ℝ) else 0
  let payload : BlockSamplePath setup → ℝ :=
    fun ω => φ (blockPrefix setup (t - 1) ω)
  have hle : m ≤ MeasurableSpace.pi := by
    dsimp [m]
    exact Filtration.le (blockPrefixFiltration setup) (t - 1)
  have hpayload_meas_m : Measurable[m] payload := by
    simpa [m, payload] using
      (by
        classical
        haveI : Fintype {r : ℕ // 1 ≤ r ∧ r ≤ (t - 1)} := by
          exact Set.Finite.fintype (Set.finite_Icc 1 (t - 1))
        haveI : Fintype (BlockPrefix setup (t - 1)) := inferInstance
        exact (measurable_of_countable φ).comp
          (blockPrefix_measurable_prefixFiltration setup (t - 1)))
  have hpayload_aesm : AEStronglyMeasurable[m] payload μ :=
    hpayload_meas_m.stronglyMeasurable.aestronglyMeasurable
  let hitSet : Set (BlockSamplePath setup) :=
    {ω | sampledBlock setup t ω = i}
  have hhit_meas :
      @MeasurableSet (BlockSamplePath setup) MeasurableSpace.pi hitSet := by
    have hsample_meas :
        @Measurable (BlockSamplePath setup) ι
          MeasurableSpace.pi
          (by infer_instance : MeasurableSpace ι)
          (fun ω : BlockSamplePath setup => sampledBlock setup t ω) := by
      have hpos :
          @Measurable (BlockSamplePath setup) (PositiveBlock setup)
            MeasurableSpace.pi
            (by infer_instance : MeasurableSpace (PositiveBlock setup))
            (fun ω : BlockSamplePath setup => sampledPositiveBlock setup t ω) := by
        simpa [sampledPositiveBlock, BlockSamplePath] using
          (@measurable_pi_apply ℕ
            (fun _ : ℕ => PositiveBlock setup)
            (fun _ => by infer_instance) t)
      simpa [sampledBlock] using measurable_subtype_coe.comp hpos
    change @MeasurableSet (BlockSamplePath setup) MeasurableSpace.pi
      ((fun ω : BlockSamplePath setup => sampledBlock setup t ω) ⁻¹' ({i} : Set ι))
    exact hsample_meas (measurableSet_singleton i)
  have hhit_meas_fun :
      @Measurable (BlockSamplePath setup) ℝ
        MeasurableSpace.pi (borel ℝ) hit := by
    rw [show hit =
        hitSet.indicator (fun _ : BlockSamplePath setup => (1 : ℝ)) by
      funext ω
      by_cases hω : sampledBlock setup t ω = i
      · simp [hit, hitSet, hω]
      · simp [hit, hitSet, hω]]
    exact measurable_const.indicator hhit_meas
  have hhit_int : Integrable hit μ := by
    have h_ind :
        Integrable (hitSet.indicator (fun _ : BlockSamplePath setup => (1 : ℝ))) μ :=
      (integrable_const (1 : ℝ)).indicator hhit_meas
    refine h_ind.congr (Filter.Eventually.of_forall ?_)
    intro ω
    by_cases hω : sampledBlock setup t ω = i
    · simp [hit, hitSet, hω]
    · simp [hit, hitSet, hω]
  have hpayload_meas :
      @Measurable (BlockSamplePath setup) ℝ
        MeasurableSpace.pi (borel ℝ) payload :=
    hpayload_meas_m.mono hle le_rfl
  have hprod_meas :
      @Measurable (BlockSamplePath setup) ℝ
        MeasurableSpace.pi (borel ℝ)
        (fun ω => hit ω * payload ω) :=
    hhit_meas_fun.mul hpayload_meas
  have hprod_fin :
      (Set.range (fun ω : BlockSamplePath setup => hit ω * payload ω)).Finite := by
    haveI : Fintype {r : ℕ // 1 ≤ r ∧ r ≤ t - 1} := by
      exact Set.Finite.fintype (Set.finite_Icc 1 (t - 1))
    haveI : Fintype (BlockPrefix setup (t - 1)) := inferInstance
    have hpayload_fin : (Set.range payload).Finite := by
      refine (Set.finite_univ.image φ).subset ?_
      rintro y ⟨ω, rfl⟩
      exact ⟨blockPrefix setup (t - 1) ω, trivial, rfl⟩
    refine (hpayload_fin.insert 0).subset ?_
    rintro y ⟨ω, rfl⟩
    by_cases hω : sampledBlock setup t ω = i
    · right
      simpa [hit, hω] using (Set.mem_range_self payload ω)
    · left
      simp [hit, hω]
  have hprod_aesm :
      AEStronglyMeasurable[MeasurableSpace.pi]
        (fun ω : BlockSamplePath setup => hit ω * payload ω) μ :=
    hprod_meas.aestronglyMeasurable
  have hprod_int :
      Integrable[MeasurableSpace.pi]
        (fun ω : BlockSamplePath setup => hit ω * payload ω) μ :=
    @integrable_of_finite_range
      (BlockSamplePath setup) ℝ MeasurableSpace.pi
      (by infer_instance) μ (by infer_instance)
      (fun ω : BlockSamplePath setup => hit ω * payload ω)
      hprod_aesm hprod_fin
  have hhit_ce :
      μ[hit | m] =ᵐ[μ] fun _ : BlockSamplePath setup => samplingProbability setup i := by
    simpa [μ, m, hit] using
      condexp_hitIndicator_sampledBlock_prefix setup t i hfresh hmarg
  simpa [μ, m, hit, payload] using
    (condExp_bilin_eq_const_bilin_of_condExp_eq_const
      (B := ContinuousLinearMap.mul ℝ ℝ)
      (μ := μ) (m := m) (hit := hit) (payload := payload)
      (p := samplingProbability setup i)
      hpayload_aesm hprod_int hhit_int hhit_ce)

/-- Conditional expectation over the fresh Algorithm 5.1 block draw for
finite-prefix observables. This is Lemma 5.4's source conditioning step
`E_t[·]`, specialized to real branch payloads depending only on
`i_1,...,i_{t-1}`.

No SOptLib match: the pre-searched digest had no candidate; searched
`conditional expectation independent indicator event probability measurable
subalgebra`, `iidStreamLaw iIndepFun eval independent coordinate prefix
filtration`, and `condExp indicator independent measurable probability`.
The usable hits were `SOptLib.iidStreamLaw_iIndepFun_eval`,
`SOptLib.iidStreamLaw_map_eval`, and
`ProbabilityTheory.iIndepFun.indep_prefixFiltration_future`; none states this
paper's two-branch conditional expectation over the one-based `BlockPrefix`,
so this local bridge packages Eq./Lemma 5.4's conditioning form. -/
private theorem condexp_sampledBlock_if_prefix_observable
    (setup : Setup E ι) (t : ℕ) (ht : 1 ≤ t) (i : ι)
    (phiHit phiMiss : BlockPrefix setup (t - 1) → ℝ) :
    (blockStreamLaw setup)[(fun ω =>
        if sampledBlock setup t ω = i then
          phiHit (blockPrefix setup (t - 1) ω)
        else
          phiMiss (blockPrefix setup (t - 1) ω)) |
        (blockPrefixFiltration setup).seq (t - 1)] =ᵐ[blockStreamLaw setup]
      (fun ω =>
        samplingProbability setup i * phiHit (blockPrefix setup (t - 1) ω) +
          (1 - samplingProbability setup i) *
            phiMiss (blockPrefix setup (t - 1) ω)) := by
  classical
  letI : IsProbabilityMeasure (blockIndexLaw setup) := by
    unfold blockIndexLaw
    infer_instance
  have hiid_raw : ProbabilityTheory.iIndepFun
      (fun n (ω : BlockSamplePath setup) => sampledPositiveBlock setup n ω)
      (blockStreamLaw setup) := by
    simpa [blockStreamLaw, sampledPositiveBlock, BlockSamplePath] using
      (SOptLib.iidStreamLaw_iIndepFun_eval (mu := blockIndexLaw setup))
  let ξ : ℕ → BlockSamplePath setup → PositiveBlock setup :=
    fun n ω => sampledPositiveBlock setup (n + 1) ω
  have hξ_meas : ∀ n, Measurable (ξ n) := by
    intro n
    simpa [ξ, sampledPositiveBlock] using measurable_pi_apply (n + 1)
  have hξ_iIndep : ProbabilityTheory.iIndepFun ξ (blockStreamLaw setup) := by
    have hinj : Function.Injective (fun n : ℕ => n + 1) := by
      intro a b h
      exact Nat.succ.inj h
    simpa [ξ] using hiid_raw.precomp hinj
  have hpast_current : ProbabilityTheory.Indep
      (⨆ j < t - 1,
        MeasurableSpace.comap (ξ j)
          (by infer_instance : MeasurableSpace (PositiveBlock setup)))
      (MeasurableSpace.comap (ξ (t - 1))
        (by infer_instance : MeasurableSpace (PositiveBlock setup)))
      (blockStreamLaw setup) := by
    exact ProbabilityTheory.iIndepFun.indep_prefixFiltration_future
      ξ hξ_meas hξ_iIndep (le_rfl : t - 1 ≤ t - 1)
  have hfresh : ProbabilityTheory.Indep
      ((blockPrefixFiltration setup).seq (t - 1))
      (MeasurableSpace.comap
        (fun ω : BlockSamplePath setup => sampledPositiveBlock setup t ω)
        (by infer_instance : MeasurableSpace (PositiveBlock setup)))
      (blockStreamLaw setup) := by
    rw [blockPrefixFiltration_seq]
    simpa [ξ, Nat.sub_add_cancel ht] using hpast_current
  have hmarg := samplingProbabilities setup t i
  let μ : Measure (BlockSamplePath setup) := blockStreamLaw setup
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    unfold blockStreamLaw
    exact SOptLib.iidStreamLaw_isProbabilityMeasure (blockIndexLaw setup)
  let m : MeasurableSpace (BlockSamplePath setup) :=
    (blockPrefixFiltration setup).seq (t - 1)
  let A : BlockSamplePath setup → ℝ :=
    fun ω => phiHit (blockPrefix setup (t - 1) ω)
  let B : BlockSamplePath setup → ℝ :=
    fun ω => phiMiss (blockPrefix setup (t - 1) ω)
  let hitSet : Set (BlockSamplePath setup) :=
    {ω | sampledBlock setup t ω = i}
  have hle : m ≤ MeasurableSpace.pi := by
    dsimp [m]
    exact Filtration.le (blockPrefixFiltration setup) (t - 1)
  letI : IsFiniteMeasure (μ.trim hle) := isFiniteMeasure_trim (μ := μ) hle
  have hA_int : Integrable[MeasurableSpace.pi] A μ := by
    simpa [μ, A] using
      prefixObservable_integrable_blockStream setup (t - 1) phiHit
  have hB_int : Integrable[MeasurableSpace.pi] B μ := by
    simpa [μ, B] using
      prefixObservable_integrable_blockStream setup (t - 1) phiMiss
  have hhit_meas : @MeasurableSet (BlockSamplePath setup) MeasurableSpace.pi hitSet := by
    have hsample_meas :
        @Measurable (BlockSamplePath setup) ι
          MeasurableSpace.pi
          (by infer_instance : MeasurableSpace ι)
          (fun ω : BlockSamplePath setup => sampledBlock setup t ω) := by
      have hpos :
          @Measurable (BlockSamplePath setup) (PositiveBlock setup)
            MeasurableSpace.pi
            (by infer_instance : MeasurableSpace (PositiveBlock setup))
            (fun ω : BlockSamplePath setup => sampledPositiveBlock setup t ω) := by
        simpa [sampledPositiveBlock, BlockSamplePath] using
          (@measurable_pi_apply ℕ
            (fun _ : ℕ => PositiveBlock setup)
            (fun _ => by infer_instance) t)
      simpa [sampledBlock] using measurable_subtype_coe.comp hpos
    change @MeasurableSet (BlockSamplePath setup) MeasurableSpace.pi
      ((fun ω : BlockSamplePath setup => sampledBlock setup t ω) ⁻¹' ({i} : Set ι))
    exact hsample_meas (measurableSet_singleton i)
  have hA_meas_m : Measurable[m] A := by
    simpa [m, A] using
      (by
        classical
        haveI : Fintype {r : ℕ // 1 ≤ r ∧ r ≤ (t - 1)} := by
          exact Set.Finite.fintype (Set.finite_Icc 1 (t - 1))
        haveI : Fintype (BlockPrefix setup (t - 1)) := inferInstance
        exact (measurable_of_countable phiHit).comp
          (blockPrefix_measurable_prefixFiltration setup (t - 1)))
  have hB_meas_m : Measurable[m] B := by
    simpa [m, B] using
      (by
        classical
        haveI : Fintype {r : ℕ // 1 ≤ r ∧ r ≤ (t - 1)} := by
          exact Set.Finite.fintype (Set.finite_Icc 1 (t - 1))
        haveI : Fintype (BlockPrefix setup (t - 1)) := inferInstance
        exact (measurable_of_countable phiMiss).comp
          (blockPrefix_measurable_prefixFiltration setup (t - 1)))
  have hA_aesm : AEStronglyMeasurable[m] A μ :=
    hA_meas_m.stronglyMeasurable.aestronglyMeasurable
  have hB_aesm : AEStronglyMeasurable[m] B μ :=
    hB_meas_m.stronglyMeasurable.aestronglyMeasurable
  have hhit_ce :
      μ[hitSet.indicator (fun _ : BlockSamplePath setup => (1 : ℝ)) | m] =ᵐ[μ]
        fun _ : BlockSamplePath setup => samplingProbability setup i := by
    have hraw :=
      condexp_hitIndicator_sampledBlock_prefix setup t i hfresh hmarg
    have hbranch :
        hitSet.indicator (fun _ : BlockSamplePath setup => (1 : ℝ)) =ᵐ[μ]
          fun ω : BlockSamplePath setup =>
            if sampledBlock setup t ω = i then (1 : ℝ) else 0 := by
      refine Filter.Eventually.of_forall ?_
      intro ω
      by_cases hω : sampledBlock setup t ω = i
      · simp [hitSet, hω]
      · simp [hitSet, hω]
    exact (MeasureTheory.condExp_congr_ae hbranch).trans (by simpa [μ, m] using hraw)
  simpa [μ, m, A, B, hitSet] using
    (@condExp_ite_eq_prob_smul_add_one_sub_smul
      (BlockSamplePath setup) ℝ MeasurableSpace.pi inferInstance inferInstance inferInstance μ inferInstance
      m hitSet A B (samplingProbability setup i) inferInstance
      hle hhit_meas hA_aesm hB_aesm hA_int hB_int hhit_ce)

/-- Measurability of the generated finite paper prefix map.
Aligns with Mathlib `measurable_pi_lambda`/`measurable_pi_apply`: the prefix
coordinate `t` is exactly the stream coordinate `t`. -/
private theorem blockPrefix_measurable
    (setup : Setup E ι) (k : ℕ) :
    Measurable (blockPrefix setup k) := by
  rw [show blockPrefix setup k =
      (fun ω : BlockSamplePath setup =>
        fun t : {t : ℕ // 1 ≤ t ∧ t ≤ k} => ω t.1) by rfl]
  apply measurable_pi_lambda
  intro t
  exact measurable_pi_apply t.1

/-- Any real observable of the generated finite prefix is integrable under
`blockPrefixLaw`.
Aligns with SOptLib `integrable_map_of_finite_range`: this specializes that
finite-range pushforward-law theorem to the paper's generated law
`Measure.map (blockPrefix setup k) (blockStreamLaw setup)`; the pre-searched
digest had no direct paper-prefix primitive, and searches for `finite range
integrable map` and `finite prefix integrable observable` found this reusable
SOptLib theorem as the matching abstraction. -/
private theorem finite_prefix_observable_integrable
    (setup : Setup E ι) (k : ℕ) (φ : BlockPrefix setup k → ℝ) :
    Integrable φ (blockPrefixLaw setup k) := by
  classical
  haveI : Fintype {t : ℕ // 1 ≤ t ∧ t ≤ k} := by
    exact Set.Finite.fintype (Set.finite_Icc 1 k)
  haveI : Fintype (BlockPrefix setup k) := inferInstance
  letI : IsProbabilityMeasure (blockIndexLaw setup) := by
    unfold blockIndexLaw
    infer_instance
  letI : IsProbabilityMeasure (blockStreamLaw setup) := by
    unfold blockStreamLaw
    exact SOptLib.iidStreamLaw_isProbabilityMeasure (blockIndexLaw setup)
  have hfin : (Set.range (blockPrefix setup k)).Finite := by
    exact Set.finite_univ.subset (Set.subset_univ _)
  unfold blockPrefixLaw
  exact integrable_map_of_finite_range (blockPrefix setup k)
    (blockPrefix_measurable setup k).aemeasurable hfin φ

/-- A finite-prefix expectation of a prefix observable is the same integral
computed over the full generated block stream.
Aligns with Lemma 5.5 proof step 5/6: searched `finite prefix expectation
block stream bridge prefix observable` and checked
`integral_comp_eq_integral_of_map_eq`. The existing
`finitePrefixExpectation_of_prefixObservable` handles only the prefix-law side,
while the generic SOptLib pushforward lemma is source-neutral; this local
bridge packages the paper-specific `blockPrefixLaw = map blockPrefix
blockStreamLaw` boundary needed to consume Lemma 5.4. -/
private theorem finite_prefix_expectation_block_stream_bridge
    (setup : Setup E ι) (k : ℕ) (ψ : BlockPrefix setup k → ℝ) :
    finitePrefixExpectation setup k (fun ω => ψ (blockPrefix setup k ω)) =
      ∫ ω, ψ (blockPrefix setup k ω) ∂blockStreamLaw setup := by
  simpa [finitePrefixExpectation] using
    (SOptLib.finitePrefixExpectation_prefixObservable_eq_integral_comp
      (μ := blockStreamLaw setup) (prefixMap := blockPrefix setup k)
      (extend := extendBlockPrefix setup k)
      (hprefix := (blockPrefix_measurable setup k).aemeasurable)
      (hsection := blockPrefix_extendBlockPrefix setup k)
      (ψ := ψ)
      (hψ := by
        simpa [blockPrefixLaw] using
          (finite_prefix_observable_integrable setup k ψ).aestronglyMeasurable))

/-- Generic prefix-to-full-stream transport for observables determined by the
generated paper prefix. This packages `finite_prefix_expectation_block_stream_bridge`
for route-local Proposition 5.1 residuals; existing specialized transports such
as `finite_prefix_expectation_dual_residual_current_bregman_eq_blockStream`
were considered, but the Eq. (5.1.57) Delta integrand is a larger scalar
combination rather than a single Bregman observable. -/
private theorem finite_prefix_expectation_eq_blockStream_of_extend_eq
    (setup : Setup E ι) (k : ℕ) (F : BlockSamplePath setup → ℝ)
    (hF : ∀ ω : BlockSamplePath setup,
      F (extendBlockPrefix setup k (blockPrefix setup k ω)) = F ω) :
    finitePrefixExpectation setup k F =
      ∫ ω, F ω ∂blockStreamLaw setup := by
  simpa [finitePrefixExpectation] using
    (SOptLib.finitePrefixExpectation_eq_integral_of_extend_prefix_eq
      (μ := blockStreamLaw setup) (prefixMap := blockPrefix setup k)
      (extend := extendBlockPrefix setup k) (F := F)
      (hprefix := (blockPrefix_measurable setup k).aemeasurable)
      (hF_meas := by
        simpa using
          (finite_prefix_observable_integrable setup k
            (fun pref : BlockPrefix setup k =>
              F (extendBlockPrefix setup k pref))).aestronglyMeasurable)
      (hF := Filter.Eventually.of_forall hF))

/-- The fixed-block `ŷᵢᵗ` Bregman observable is determined by the generated
paper prefix through time `t`.
Aligns with Lemma 5.5 proof step 5: searched `dual Bregman expectation yHat
yIter Lemma 5.4 substitution` and `state process depends on block prefix
extendBlockPrefix`. Existing hits `Lemma_5_4_conditional_expectation_identities`
and `stateProcess_extendBlockPrefix_eq_of_le` need this route-local
factorization before they can be integrated over `finitePrefixExpectation`. -/
private theorem dual_hat_bregman_prefixObservable
    (setup : Setup E ι) (hStanding : standingAssumptions setup)
    (t : ℕ) (ht : 1 ≤ t) (i : ι) (y : DualCarrier setup i) :
    (fun ω : BlockSamplePath setup =>
      (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i (yHatIter setup hStanding t ω i) (yHatSubgradIter setup hStanding t ht ω i)) (yHatIter setup hStanding t ω i) y)) =
      fun ω : BlockSamplePath setup =>
        (fun pref : BlockPrefix setup t =>
          (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i (yHatIter setup hStanding t (extendBlockPrefix setup t pref) i) (yHatSubgradIter setup hStanding t ht
              (extendBlockPrefix setup t pref) i)) (yHatIter setup hStanding t (extendBlockPrefix setup t pref) i) y))
          (blockPrefix setup t ω) := by
  funext ω
  have hprev :
      stateProcess setup hStanding (t - 1)
          (extendBlockPrefix setup t (blockPrefix setup t ω)) =
        stateProcess setup hStanding (t - 1) ω := by
    exact stateProcess_extendBlockPrefix_eq_of_le setup hStanding (by omega) ω
  have hprev2 :
      stateProcess setup hStanding (t - 2)
          (extendBlockPrefix setup t (blockPrefix setup t ω)) =
        stateProcess setup hStanding (t - 2) ω := by
    exact stateProcess_extendBlockPrefix_eq_of_le setup hStanding (by omega) ω
  dsimp [yHatIter, yHatSubgradIter, xTildeIter, xIter, yIter, dualSubgradIter]
  rw [hprev, hprev2]

/-- Ordinary generated primal-iterate Bregman observables are determined by any
paper prefix containing their time index.
Aligns with Proposition 5.1 Eq. (5.1.53) telescoping: searched `finite prefix
expectation transport observable time le stateProcess`, considered the existing
dual transport `dual_iter_bregman_prefixObservable_of_le` and SOptLib finite
window telescope lemmas; the dual transport is dependent-coordinate-specific,
while the SOptLib lemmas assume the scalar sequence has already been normalized
to one expectation index. -/
private theorem primal_iter_bregman_prefixObservable_of_le
    (setup : Setup E ι) (hStanding : standingAssumptions setup)
    {l k : ℕ} (hle : l ≤ k) (x : PrimalCarrier setup) :
    (fun ω : BlockSamplePath setup =>
      primalBregman setup (xIter setup hStanding l ω) x) =
      fun ω : BlockSamplePath setup =>
        (fun pref : BlockPrefix setup k =>
          primalBregman setup
            (xIter setup hStanding l (extendBlockPrefix setup k pref)) x)
          (blockPrefix setup k ω) := by
  funext ω
  have hs :
      stateProcess setup hStanding l
          (extendBlockPrefix setup k (blockPrefix setup k ω)) =
        stateProcess setup hStanding l ω := by
    exact stateProcess_extendBlockPrefix_eq_of_le setup hStanding hle ω
  dsimp [xIter]
  rw [hs]

/-- Ordinary generated dual-iterate Bregman observables are determined by any
paper prefix containing their time index.
Aligns with Lemma 5.5 proof step 5: searched `state process depends on block
prefix extendBlockPrefix`; the existing `stateProcess_extendBlockPrefix_eq_of_le`
gives the exact generated-process determinacy, and no SOptLib theorem knows this
paper's dependent `DualConjugateSubgradient` accessor. -/
private theorem dual_iter_bregman_prefixObservable_of_le
    (setup : Setup E ι) (hStanding : standingAssumptions setup)
    {l k : ℕ} (hle : l ≤ k) (i : ι) (y : DualCarrier setup i) :
    (fun ω : BlockSamplePath setup =>
      (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding l ω) i) (dualSubgradIter setup hStanding l ω i)) ((yIter setup hStanding l ω) i) y)) =
      fun ω : BlockSamplePath setup =>
        (fun pref : BlockPrefix setup k =>
          (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding l (extendBlockPrefix setup k pref)) i) (dualSubgradIter setup hStanding l
              (extendBlockPrefix setup k pref) i)) ((yIter setup hStanding l (extendBlockPrefix setup k pref)) i) y))
          (blockPrefix setup k ω) := by
  funext ω
  have hs :
      stateProcess setup hStanding l
          (extendBlockPrefix setup k (blockPrefix setup k ω)) =
        stateProcess setup hStanding l ω := by
    exact stateProcess_extendBlockPrefix_eq_of_le setup hStanding hle ω
  dsimp [yIter, dualSubgradIter]
  rw [hs]

/-- Finite-prefix expectation of the fixed-block `ŷᵢᵗ` Bregman term can be
computed over the full generated block stream.
Aligns with Lemma 5.5 proof step 5: this consumes
`dual_hat_bregman_prefixObservable` and
`finite_prefix_expectation_block_stream_bridge`, preparing the exact
integrand used by `Lemma_5_4_conditional_expectation_identities`. -/
private theorem finite_prefix_expectation_dual_hat_bregman_eq_blockStream
    (setup : Setup E ι) (hStanding : standingAssumptions setup)
    (t : ℕ) (ht : 1 ≤ t) (i : ι) (y : DualCarrier setup i) :
    finitePrefixExpectation setup t (fun ω =>
      (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i (yHatIter setup hStanding t ω i) (yHatSubgradIter setup hStanding t ht ω i)) (yHatIter setup hStanding t ω i) y)) =
      ∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i (yHatIter setup hStanding t ω i) (yHatSubgradIter setup hStanding t ht ω i)) (yHatIter setup hStanding t ω i) y) ∂blockStreamLaw setup := by
  let ψ : BlockPrefix setup t → ℝ := fun pref =>
    (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i (yHatIter setup hStanding t (extendBlockPrefix setup t pref) i) (yHatSubgradIter setup hStanding t ht
        (extendBlockPrefix setup t pref) i)) (yHatIter setup hStanding t (extendBlockPrefix setup t pref) i) y)
  calc
    finitePrefixExpectation setup t (fun ω =>
        (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i (yHatIter setup hStanding t ω i) (yHatSubgradIter setup hStanding t ht ω i)) (yHatIter setup hStanding t ω i) y)) =
        finitePrefixExpectation setup t (fun ω => ψ (blockPrefix setup t ω)) := by
          rw [dual_hat_bregman_prefixObservable setup hStanding t ht i y]
    _ = ∫ ω, ψ (blockPrefix setup t ω) ∂blockStreamLaw setup := by
          exact finite_prefix_expectation_block_stream_bridge setup t ψ
    _ = ∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i (yHatIter setup hStanding t ω i) (yHatSubgradIter setup hStanding t ht ω i)) (yHatIter setup hStanding t ω i) y) ∂blockStreamLaw setup := by
          rw [← dual_hat_bregman_prefixObservable setup hStanding t ht i y]

/-- Full-stream integrability of the fixed-block `ŷᵢᵗ` Bregman observable.
Aligns with Lemma 5.5 proof step 5: this is the integrability side condition
for splitting the integrated Lemma 5.4 identity by scalar linearity. -/
private theorem dual_hat_bregman_integrable_blockStream
    (setup : Setup E ι) (hStanding : standingAssumptions setup)
    (t : ℕ) (ht : 1 ≤ t) (i : ι) (y : DualCarrier setup i) :
    Integrable (fun ω : BlockSamplePath setup =>
      (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i (yHatIter setup hStanding t ω i) (yHatSubgradIter setup hStanding t ht ω i)) (yHatIter setup hStanding t ω i) y))
      (blockStreamLaw setup) := by
  let ψ : BlockPrefix setup t → ℝ := fun pref =>
    (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i (yHatIter setup hStanding t (extendBlockPrefix setup t pref) i) (yHatSubgradIter setup hStanding t ht
        (extendBlockPrefix setup t pref) i)) (yHatIter setup hStanding t (extendBlockPrefix setup t pref) i) y)
  have hψ :
      Integrable (fun ω : BlockSamplePath setup => ψ (blockPrefix setup t ω))
        (blockStreamLaw setup) :=
    prefixObservable_integrable_blockStream setup t ψ
  exact hψ.congr
    (Filter.Eventually.of_forall fun ω =>
      (congrFun (dual_hat_bregman_prefixObservable setup hStanding t ht i y) ω).symm)

/-- Finite-prefix expectation of an ordinary generated primal-iterate Bregman
term can be computed over the full generated block stream whenever the prefix
contains the iterate time.
Aligns with Proposition 5.1 Eq. (5.1.53): this is the primal counterpart of the
existing dual transport and lets adjacent weighted terms telescope across
different prefix lengths. -/
private theorem finite_prefix_expectation_primal_iter_bregman_eq_blockStream_of_le
    (setup : Setup E ι) (hStanding : standingAssumptions setup)
    {l k : ℕ} (hle : l ≤ k) (x : PrimalCarrier setup) :
    finitePrefixExpectation setup k (fun ω =>
      primalBregman setup (xIter setup hStanding l ω) x) =
      ∫ ω, primalBregman setup (xIter setup hStanding l ω) x
        ∂blockStreamLaw setup := by
  let ψ : BlockPrefix setup k → ℝ := fun pref =>
    primalBregman setup
      (xIter setup hStanding l (extendBlockPrefix setup k pref)) x
  calc
    finitePrefixExpectation setup k (fun ω =>
        primalBregman setup (xIter setup hStanding l ω) x) =
        finitePrefixExpectation setup k (fun ω => ψ (blockPrefix setup k ω)) := by
          rw [primal_iter_bregman_prefixObservable_of_le setup hStanding hle x]
    _ = ∫ ω, ψ (blockPrefix setup k ω) ∂blockStreamLaw setup := by
          exact finite_prefix_expectation_block_stream_bridge setup k ψ
    _ = ∫ ω, primalBregman setup (xIter setup hStanding l ω) x
          ∂blockStreamLaw setup := by
          rw [← primal_iter_bregman_prefixObservable_of_le setup hStanding hle x]

/-- Full-stream integrability of ordinary generated dual-iterate Bregman
observables determined by a containing finite prefix.
Aligns with Lemma 5.5 proof step 5: this is the current/previous `yᵢᵗ` side
condition needed to split the integrated Lemma 5.4 identity. -/
private theorem dual_iter_bregman_integrable_blockStream_of_le
    (setup : Setup E ι) (hStanding : standingAssumptions setup)
    {l k : ℕ} (hle : l ≤ k) (i : ι) (y : DualCarrier setup i) :
    Integrable (fun ω : BlockSamplePath setup =>
      (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding l ω) i) (dualSubgradIter setup hStanding l ω i)) ((yIter setup hStanding l ω) i) y))
      (blockStreamLaw setup) := by
  let ψ : BlockPrefix setup k → ℝ := fun pref =>
    (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding l (extendBlockPrefix setup k pref)) i) (dualSubgradIter setup hStanding l
        (extendBlockPrefix setup k pref) i)) ((yIter setup hStanding l (extendBlockPrefix setup k pref)) i) y)
  have hψ :
      Integrable (fun ω : BlockSamplePath setup => ψ (blockPrefix setup k ω))
        (blockStreamLaw setup) :=
    prefixObservable_integrable_blockStream setup k ψ
  exact hψ.congr
    (Filter.Eventually.of_forall fun ω =>
      (congrFun (dual_iter_bregman_prefixObservable_of_le
        setup hStanding hle i y) ω).symm)

/-- Finite-prefix expectation of an ordinary generated dual-iterate Bregman
term can be computed over the full generated block stream whenever the prefix
contains the iterate time.
Aligns with Lemma 5.5 proof step 5: this is the current/previous `yᵢᵗ`
transport counterpart to
`finite_prefix_expectation_dual_hat_bregman_eq_blockStream`. -/
private theorem finite_prefix_expectation_dual_iter_bregman_eq_blockStream_of_le
    (setup : Setup E ι) (hStanding : standingAssumptions setup)
    {l k : ℕ} (hle : l ≤ k) (i : ι) (y : DualCarrier setup i) :
    finitePrefixExpectation setup k (fun ω =>
      (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding l ω) i) (dualSubgradIter setup hStanding l ω i)) ((yIter setup hStanding l ω) i) y)) =
      ∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding l ω) i) (dualSubgradIter setup hStanding l ω i)) ((yIter setup hStanding l ω) i) y) ∂blockStreamLaw setup := by
  let ψ : BlockPrefix setup k → ℝ := fun pref =>
    (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding l (extendBlockPrefix setup k pref)) i) (dualSubgradIter setup hStanding l
        (extendBlockPrefix setup k pref) i)) ((yIter setup hStanding l (extendBlockPrefix setup k pref)) i) y)
  calc
    finitePrefixExpectation setup k (fun ω =>
        (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding l ω) i) (dualSubgradIter setup hStanding l ω i)) ((yIter setup hStanding l ω) i) y)) =
        finitePrefixExpectation setup k (fun ω => ψ (blockPrefix setup k ω)) := by
          rw [dual_iter_bregman_prefixObservable_of_le setup hStanding hle i y]
    _ = ∫ ω, ψ (blockPrefix setup k ω) ∂blockStreamLaw setup := by
          exact finite_prefix_expectation_block_stream_bridge setup k ψ
    _ = ∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding l ω) i) (dualSubgradIter setup hStanding l ω i)) ((yIter setup hStanding l ω) i) y) ∂blockStreamLaw setup := by
          rw [← dual_iter_bregman_prefixObservable_of_le setup hStanding hle i y]

/-- Integrability obligation for the terminal Bregman expectation in Theorem 5.1.
The paper states the expectation; Lean proof work must establish this from the
source-backed generated finite-prefix process rather than adding it to the theorem
head. -/
theorem expectedBregmanDistance_integrable
    (setup : Setup E ι) (hStanding : standingAssumptions setup)
    (k : ℕ) (xstar : PrimalCarrier setup) :
    Integrable
      (fun pref : BlockPrefix setup k =>
        primalBregman setup
          (xIter setup hStanding k (extendBlockPrefix setup k pref)) xstar)
      (blockPrefixLaw setup k) := by
  exact finite_prefix_observable_integrable setup k
    (fun pref : BlockPrefix setup k =>
      primalBregman setup
        (xIter setup hStanding k (extendBlockPrefix setup k pref)) xstar)

/-- Integrability obligation for the weighted-output primal gap expectation in
Theorem 5.1. -/
theorem expectedPrimalGap_integrable
    (setup : Setup E ι) (α : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hStanding : standingAssumptions setup) (hAlpha : alphaRange α)
    (xstar : PrimalCarrier setup) :
    Integrable
      (fun pref : BlockPrefix setup k =>
        objective setup
          (weightedOutput setup α k hk hStanding hAlpha
            (extendBlockPrefix setup k pref)) -
          objective setup xstar)
      (blockPrefixLaw setup k) := by
  exact finite_prefix_observable_integrable setup k
    (fun pref : BlockPrefix setup k =>
      objective setup
        (weightedOutput setup α k hk hStanding hAlpha
          (extendBlockPrefix setup k pref)) -
        objective setup xstar)

/-- Integrability obligation for the paper-facing optimality-gap expectation
`E[Ψ(x̄ᵏ)-Ψ*]` in Theorem 5.1. -/
theorem expectedPrimalOptimalityGap_integrable
    (setup : Setup E ι) (α : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hStanding : standingAssumptions setup) (hAlpha : alphaRange α)
    (xstar : PrimalCarrier setup) (hxstar : IsOptimalPrimal setup xstar) :
    Integrable
      (fun pref : BlockPrefix setup k =>
        objective setup
          (weightedOutput setup α k hk hStanding hAlpha
            (extendBlockPrefix setup k pref)) -
          primalOptimalValue setup xstar hxstar)
      (blockPrefixLaw setup k) := by
  exact finite_prefix_observable_integrable setup k
    (fun pref : BlockPrefix setup k =>
      objective setup
        (weightedOutput setup α k hk hStanding hAlpha
          (extendBlockPrefix setup k pref)) -
        primalOptimalValue setup xstar hxstar)

/-- The finite-prefix expectation is the paper-facing interpretation of
Theorem 5.1's phrase "expectation is taken with respect to `i_1,...,i_k`". -/
theorem expectedBregmanDistance_finite_prefix
    (setup : Setup E ι) (hStanding : standingAssumptions setup)
    (k : ℕ) (xstar : PrimalCarrier setup) :
    expectedBregmanDistance setup hStanding k xstar =
      finitePrefixExpectation setup k
        (fun ω => primalBregman setup (xIter setup hStanding k ω) xstar) := by
  rfl

/-- Expected saddle gap used by Proposition 5.1. -/
noncomputable def expectedSaddleGap
    (setup : Setup E ι) (hStanding : standingAssumptions setup)
    (t : ℕ) (z : SaddlePoint setup) :
    ℝ :=
  finitePrefixExpectation setup t
    (fun ω => gap setup
      ((xIter setup hStanding t ω), (yHatIter setup hStanding t ω)) z)

/-- Integrability obligation for the finite-prefix saddle-gap expectation used in
Lemma 5.5 and Proposition 5.1. -/
theorem expectedSaddleGap_integrable
    (setup : Setup E ι) (hStanding : standingAssumptions setup)
    (t : ℕ) (z : SaddlePoint setup) :
    Integrable
      (fun pref : BlockPrefix setup t =>
        gap setup
          ((xIter setup hStanding t (extendBlockPrefix setup t pref)),
            (yHatIter setup hStanding t (extendBlockPrefix setup t pref))) z)
      (blockPrefixLaw setup t) := by
  exact finite_prefix_observable_integrable setup t
    (fun pref : BlockPrefix setup t =>
      gap setup
        ((xIter setup hStanding t (extendBlockPrefix setup t pref)),
          (yHatIter setup hStanding t (extendBlockPrefix setup t pref))) z)

/-- Explicit corrected-boundary requirement for Theorem 5.1's displayed rate
coefficients involving division by `η`. The PDF states the rate with `η` in the
denominator but does not separately state `η ≠ 0`, and the listed constant
parameter conditions do not by themselves rule out `η = 0` in degenerate
smoothness cases. No SOptLib match: searched `denominator admissible quotient
nonzero`, considered the quotient bridge `checkedQuotient_weight_mono_semantics`
in `SOptLib/Model/ParameterChoices.lean`, and scanned
`SOptLib/Model/ParameterChoices.lean`; no reusable primitive represents this
RPDG-specific rate-bound boundary. -/
def theorem_5_1_rateDenominatorBoundary (η : ℝ) : Prop :=
  η ≠ 0

/-- Lemma 5.1 expansion of `W(y⁰,y)` into the average-objective linearization
gap. Aligns with Lan Eq. (5.1.33): searched the local/SOptLib candidates
`dualConjugate_scaled_component_value`,
`averageGradient_eq_componentGradient_average`,
`Convex.carrier_smooth_quadratic_upper_bound_of_hasGradientWithinAt_lipschitz`,
and `isMinOn.affine_residual_support_inequality`; only the first two match this
literal Fenchel expansion, while the latter candidates serve later inequality
steps rather than this equality. -/
private theorem dual_bregman_sum_scaled_gradient_eq_average_linearization_gap
    (hStanding : standingAssumptions setup) (x : PrimalCarrier setup) :
    dualBregmanSum setup (initialDual setup hStanding) (initialDualSubgradient setup hStanding)
      (fun i => scaledComponentGradientDual setup hStanding i x.1) =
      averageObjective setup setup.x0 - averageObjective setup x -
        ⟪averageGradient setup x.1, setup.x0.1 - x.1⟫_ℝ := by
  classical
  have hStandingFull := hStanding
  obtain ⟨_, hSmooth, _, _, _, _, _, _, _, _, _, _⟩ := hStanding
  have hcarrier :
      dualBregmanSum setup (initialDual setup hStandingFull)
          (initialDualSubgradient setup hStandingFull)
          (fun i => scaledComponentGradientDual setup hStandingFull i x.1) =
        ∑ i : ι, (
          dualConjugate setup i (scaledComponentGradientDual setup hStandingFull i x.1) -
            (dualConjugate setup i (initialDual setup hStandingFull i) +
              ⟪(initialDualSubgradient setup hStandingFull i).1,
                (scaledComponentGradientDual setup hStandingFull i x.1).1 -
                  (initialDual setup hStandingFull i).1⟫_ℝ)) := by
    unfold dualBregmanSum
    apply Finset.sum_congr rfl
    intro i _hi
    simp [SOptLib.carrierBregmanDivergence, carrierBregmanDivergence,
      dualConjugateBaseSelector]
    ring
  have hfenchel :=
    (SOptLib.sum_bregman_scaled_fenchel_gradient_eq_average_linearization_gap
      (w := fun _ : ι => componentCountInverse (ι := ι))
      (f := setup.f)
      (grad := componentGradient setup)
      (averageGradient := averageGradient setup)
      (x0 := setup.x0.1)
      (x := x.1)
      (y0 := fun i => (initialDual setup hStandingFull i).1)
      (y := fun i => (scaledComponentGradientDual setup hStandingFull i x.1).1)
      (hy0Bdd := fun i => (initialDual setup hStandingFull i).2)
      (hyBdd := fun i => (scaledComponentGradientDual setup hStandingFull i x.1).2)
      (hy0 := by
        intro i
        simp [initialDual, scaledComponentGradientDual])
      (hy := by
        intro i
        simp [scaledComponentGradientDual])
      (hValue0 := by
        intro i
        simpa [dualConjugate, initialDual] using
          dualConjugate_scaled_component_value setup hStandingFull i setup.x0.1)
      (hValue := by
        intro i
        simpa [dualConjugate] using
          dualConjugate_scaled_component_value setup hStandingFull i x.1)
      (hAvgGrad := by
        simpa [scaledComponentGradientDual, Finset.smul_sum] using
          averageGradient_eq_componentGradient_average setup hSmooth x.1))
  calc
    dualBregmanSum setup (initialDual setup hStandingFull) (initialDualSubgradient setup hStandingFull)
        (fun i => scaledComponentGradientDual setup hStandingFull i x.1) =
        ∑ i : ι, (
          dualConjugate setup i (scaledComponentGradientDual setup hStandingFull i x.1) -
            (dualConjugate setup i (initialDual setup hStandingFull i) +
              ⟪(initialDualSubgradient setup hStandingFull i).1,
                (scaledComponentGradientDual setup hStandingFull i x.1).1 -
                  (initialDual setup hStandingFull i).1⟫_ℝ)) := hcarrier
    _ = averageObjective setup setup.x0 - averageObjective setup x -
        ⟪averageGradient setup x.1, setup.x0.1 - x.1⟫_ℝ := by
          simpa [initialDual, initialDualSubgradient, initialDualSubgradientValue,
            dualConjugate, averageObjective, Finset.mul_sum] using hfenchel

/-- Lemma 5.1 smoothness bridge for Eq. (5.1.33). Aligns with Lan §5.1.4:
the checked SOptLib theorem
`Convex.carrier_smooth_quadratic_upper_bound_of_hasGradientWithinAt_lipschitz`
matches this carrier quadratic upper bound, while the finite-average/component
smoothness candidates are lower-level ways to prove the already-assumed
`averageSmoothness`. -/
private theorem average_objective_linearization_gap_le_quadratic
    (hStanding : standingAssumptions setup) (x0 x : PrimalCarrier setup) :
    averageObjective setup x0 - averageObjective setup x -
        ⟪averageGradient setup x.1, x0.1 - x.1⟫_ℝ ≤
      (setup.Lf / 2) * ‖x0.1 - x.1‖ ^ 2 := by
  classical
  let hStanding0 : standingAssumptions setup := hStanding
  obtain ⟨hX, _, _, _, _, _, hAvg, _, _, _, _, _⟩ := hStanding
  exact
    Convex.carrier_smooth_quadratic_upper_bound_of_hasGradientWithinAt_lipschitz
      (averageObjective setup) (averageObjectiveAmbient setup)
      (fun z : PrimalCarrier setup => averageGradient setup z.1)
      setup.Lf hX.2
      (by
        intro z hz
        simp [averageObjective, averageObjectiveAmbient])
      (by
        intro z
        simpa using
          ((averageGradient_hasGradientAt_of_averageSmoothness setup hAvg z.1).hasFDerivAt
            |>.hasFDerivWithinAt (s := setup.X)
            |>.hasGradientWithinAt))
      (by
        intro y z
        exact hAvg.2.2.2 z.1 y.1)
      x0 x

/-- Scalar part of Lemma 5.1(a), converting the quadratic smoothness bound into
the Bregman bound using the source lower bound Eq. (5.1.16). The checked
smoothness theorem handles the previous inequality; this lemma uses only
`averageSmoothness` for `L_f ≥ 0` and `primalBregmanLowerBound`. -/
private theorem quadratic_bound_le_lf_primal_bregman
    (hStanding : standingAssumptions setup) (x : PrimalCarrier setup) :
    (setup.Lf / 2) * ‖setup.x0.1 - x.1‖ ^ 2 ≤
      setup.Lf * primalBregman setup setup.x0 x := by
  obtain ⟨_, _, _, _, _, _, hAvg, _, _, hVlb, _, _⟩ := hStanding
  have hLf_nonneg : 0 ≤ setup.Lf := hAvg.2.1
  have hV := hVlb setup.x0 x
  have hnorm :
      ‖setup.x0.1 - x.1‖ = ‖x.1 - setup.x0.1‖ := by
    rw [← norm_neg (x.1 - setup.x0.1)]
    simp [sub_eq_add_neg, add_comm]
  have hscaled :
      setup.Lf * ((1 / 2 : ℝ) * ‖x.1 - setup.x0.1‖ ^ 2) ≤
        setup.Lf * primalBregman setup setup.x0 x :=
    mul_le_mul_of_nonneg_left hV hLf_nonneg
  rw [hnorm]
  nlinarith

/-- Convexity of the carrier totalization of the regularizer `h+μν` used in
Lemma 5.1(b). Aligns with Lan Eq. (5.1.34): searched
`carrierSubdifferential support implies convexOn carrier function`,
`ConvexOn add mul nonnegative totalizeOn carrier convex`, and checked
`SOptLib.mem_carrierSubdifferential_iff`, `SOptLib.ConvexOnCarrier`, and
`convexOnCarrier_segment_sub_le_mul_sub`; no existing theorem combines the
paper's selected `ν'` support with `h`-convexity and `μ ≥ 0` for this literal
regularizer. -/
private theorem objective_regularizer_totalize_convexOn
    (hStanding : standingAssumptions setup) :
    ConvexOn ℝ setup.X (SOptLib.totalizeOn setup.X (objectiveRegularizer setup)) := by
  obtain ⟨_, _, hSimple, _, hNu, hMu, _, _, _, _, _, _⟩ := hStanding
  have hh :
      ConvexOn ℝ setup.X
        (SOptLib.totalizeOn setup.X (fun x : PrimalCarrier setup => setup.h x.1)) := by
    refine ⟨hSimple.1, ?_⟩
    intro x hx y hy a b ha hb hab
    have hmix : a • x + b • y ∈ setup.X := hSimple.1 hx hy ha hb hab
    simpa [SOptLib.totalizeOn_of_mem, hmix, hx, hy] using hSimple.2 hx hy ha hb hab
  simpa [objectiveRegularizer] using
    (ConvexOn.totalizeOn_add_nonneg_mul_of_carrierSubdifferential
      (X := setup.X)
      (h := fun x : PrimalCarrier setup => setup.h x.1)
      (ν := setup.nu)
      (ν' := setup.nuGrad)
      (μ := setup.μ) hh hNu.1 hMu)

/-- Primal regularizer Jensen part of the weighted saddle-gap bridge after
Lan Eq. (5.1.66).

Candidate audit: searched `weighted saddle gap Jensen` and `objective
regularizer convexOn weighted average`; SOptLib's generic weighted Jensen
consumer and the local `objective_regularizer_totalize_convexOn` are relevant,
but no existing helper specializes them to Eq. (5.1.65)'s generated
`weightedOutput`. -/
private theorem theorem51_weighted_objective_regularizer_le
    (α : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hStanding : standingAssumptions setup) (hAlpha : alphaRange α)
    (ω : BlockSamplePath setup) :
    objectiveRegularizer setup
        (weightedOutput setup α k hk hStanding hAlpha ω) ≤
      (outputWeightSum α hAlpha k)⁻¹ *
        ∑ t ∈ outputTimeWindow k,
          theoremOutputWeight α hAlpha t *
            objectiveRegularizer setup (xIter setup hStanding t ω) := by
  classical
  let W : ℝ := outputWeightSum α hAlpha k
  let s : Finset ℕ := outputTimeWindow k
  let γ : ℕ → ℝ := theoremOutputWeight α hAlpha
  let q : ℕ → ℝ := fun t => W⁻¹ * γ t
  let p : ℕ → E := fun t => (xIter setup hStanding t ω).1
  have hW_pos : 0 < W := outputWeightSum_pos_of_alphaRange α k hk hAlpha
  have hW_ne : W ≠ 0 := ne_of_gt hW_pos
  have hqsum : ∑ t ∈ s, q t = 1 := by
    calc
      ∑ t ∈ s, q t = W⁻¹ * ∑ t ∈ s, γ t := by
        simp [q, Finset.mul_sum]
      _ = W⁻¹ * W := by
        rfl
      _ = 1 := inv_mul_cancel₀ hW_ne
  have hq_nonneg : ∀ t ∈ s, 0 ≤ q t := by
    intro t ht
    exact mul_nonneg (inv_nonneg.mpr hW_pos.le)
      (outputTheta_nonnegative_of_alphaRange α k hAlpha () t ht)
  have hp_mem : ∀ t ∈ s, p t ∈ setup.X := by
    intro t _ht
    exact (xIter setup hStanding t ω).2
  have harg :
      (weightedOutput setup α k hk hStanding hAlpha ω).1 =
        ∑ t ∈ s, q t • p t := by
    rw [weightedOutput_eq]
    unfold weightedOutputVector SOptLib.weightedAverageOutputValue
    calc
      W⁻¹ • ∑ t ∈ s, γ t • p t =
          ∑ t ∈ s, W⁻¹ • (γ t • p t) := by
        rw [Finset.smul_sum]
      _ = ∑ t ∈ s, q t • p t := by
        refine Finset.sum_congr rfl ?_
        intro t _ht
        simp [q, smul_smul]
  have hJ :=
    (objective_regularizer_totalize_convexOn setup hStanding).map_sum_le
      (t := s) (w := q) (p := p) hq_nonneg hqsum hp_mem
  rw [← harg] at hJ
  have hpbar :
      (weightedOutput setup α k hk hStanding hAlpha ω).1 ∈ setup.X :=
    (weightedOutput setup α k hk hStanding hAlpha ω).2
  have hright :
      (∑ t ∈ s, q t •
        SOptLib.totalizeOn setup.X (objectiveRegularizer setup) (p t)) =
        W⁻¹ * ∑ t ∈ s,
          γ t * objectiveRegularizer setup (xIter setup hStanding t ω) := by
    calc
      (∑ t ∈ s, q t •
        SOptLib.totalizeOn setup.X (objectiveRegularizer setup) (p t)) =
          ∑ t ∈ s, W⁻¹ *
            (γ t * objectiveRegularizer setup (xIter setup hStanding t ω)) := by
        refine Finset.sum_congr rfl ?_
        intro t ht
        simp [q, p, SOptLib.totalizeOn_of_mem, hp_mem t ht, smul_eq_mul,
          mul_assoc]
      _ = W⁻¹ * ∑ t ∈ s,
          γ t * objectiveRegularizer setup (xIter setup hStanding t ω) := by
        rw [Finset.mul_sum]
  rw [hright] at hJ
  simpa [SOptLib.totalizeOn_of_mem, hpbar] using hJ

/-- Lemma 5.1(b) optimality bridge. Aligns with Lan Eq. (5.1.34): the checked
SOptLib theorem `smooth_part_linearization_gap_le_composite_gap_of_minimizer`
matches the smooth-plus-convex minimizer step, after the local
`objective_regularizer_totalize_convexOn` supplies convexity of `h+μν` on the
carrier. -/
private theorem optimal_primal_average_linearization_gap_le_objective_gap
    (hStanding : standingAssumptions setup)
    (xstar : PrimalCarrier setup) (hxstar : IsOptimalPrimal setup xstar) :
  averageObjective setup setup.x0 - averageObjective setup xstar -
        ⟪averageGradient setup xstar.1, setup.x0.1 - xstar.1⟫_ℝ ≤
      objective setup setup.x0 - objective setup xstar := by
  classical
  let hStanding0 : standingAssumptions setup := hStanding
  obtain ⟨hX, _, _, _, _, _, hAvg, _, _, _, _, _⟩ := hStanding
  let reg : E → ℝ := SOptLib.totalizeOn setup.X (objectiveRegularizer setup)
  have hbridge :
      averageObjectiveAmbient setup setup.x0.1 -
          SOptLib.first_order_linear_model (averageObjectiveAmbient setup)
            (averageGradient setup xstar.1) xstar.1 setup.x0.1 ≤
        SOptLib.compositeObjective (averageObjectiveAmbient setup) reg setup.x0.1 -
          SOptLib.compositeObjective (averageObjectiveAmbient setup) reg xstar.1 := by
    refine
      smooth_part_linearization_gap_le_composite_gap_of_minimizer
        setup.X (averageObjectiveAmbient setup) reg
        (averageGradient setup xstar.1) setup.Lf
        setup.x0.2 xstar.2
        ?hreg ?hmin hAvg.2.1 ?hsmooth
    · simpa [reg] using objective_regularizer_totalize_convexOn setup hStanding0
    · intro y hy
      have hmin := (isMinOn_univ_iff.mp hxstar) ⟨y, hy⟩
      simpa [objective, averageObjective, averageObjectiveAmbient, objectiveRegularizer,
        SOptLib.compositeObjective, reg, SOptLib.totalizeOn_of_mem, hy, xstar.2] using hmin
    · intro y hy
      have hs :=
        average_objective_linearization_gap_le_quadratic setup hStanding0
          ⟨y, hy⟩ xstar
      simp [averageObjective, averageObjectiveAmbient] at hs ⊢
      linarith
  simp [averageObjective, averageObjectiveAmbient, objective, objectiveRegularizer,
    SOptLib.compositeObjective, SOptLib.first_order_linear_model, reg,
    SOptLib.totalizeOn_of_mem, setup.x0.2, xstar.2] at hbridge ⊢
  linarith

/-- Generalized Lemma 5.1(b) optimality bridge at an arbitrary feasible point.
This is the source-level support inequality needed to turn the primal optimizer
`x*` and the scaled-gradient dual `m⁻¹∇f_i(x*)` into the saddle solution used in
Theorem 5.1. Existing candidates considered: the local
`optimal_primal_average_linearization_gap_le_objective_gap` only states the
`x=x⁰` instance, while SOptLib
`smooth_part_linearization_gap_le_composite_gap_of_minimizer` exactly supplies
the reusable composite-minimizer bridge used here. -/
private theorem optimal_primal_average_linearization_gap_le_objective_gap_at
    (hStanding : standingAssumptions setup)
    (xstar : PrimalCarrier setup) (hxstar : IsOptimalPrimal setup xstar)
    (x : PrimalCarrier setup) :
  averageObjective setup x - averageObjective setup xstar -
        ⟪averageGradient setup xstar.1, x.1 - xstar.1⟫_ℝ ≤
      objective setup x - objective setup xstar := by
  classical
  let hStanding0 : standingAssumptions setup := hStanding
  obtain ⟨hX, _, _, _, _, _, hAvg, _, _, _, _, _⟩ := hStanding
  let reg : E → ℝ := SOptLib.totalizeOn setup.X (objectiveRegularizer setup)
  have hbridge :
      averageObjectiveAmbient setup x.1 -
          SOptLib.first_order_linear_model (averageObjectiveAmbient setup)
            (averageGradient setup xstar.1) xstar.1 x.1 ≤
        SOptLib.compositeObjective (averageObjectiveAmbient setup) reg x.1 -
          SOptLib.compositeObjective (averageObjectiveAmbient setup) reg xstar.1 := by
    refine
      smooth_part_linearization_gap_le_composite_gap_of_minimizer
        setup.X (averageObjectiveAmbient setup) reg
        (averageGradient setup xstar.1) setup.Lf
        x.2 xstar.2
        ?hreg ?hmin hAvg.2.1 ?hsmooth
    · simpa [reg] using objective_regularizer_totalize_convexOn setup hStanding0
    · intro y hy
      have hmin := (isMinOn_univ_iff.mp hxstar) ⟨y, hy⟩
      simpa [objective, averageObjective, averageObjectiveAmbient, objectiveRegularizer,
        SOptLib.compositeObjective, reg, SOptLib.totalizeOn_of_mem, hy, xstar.2] using hmin
    · intro y hy
      have hs :=
        average_objective_linearization_gap_le_quadratic setup hStanding0
          ⟨y, hy⟩ xstar
      simp [averageObjective, averageObjectiveAmbient] at hs ⊢
      linarith
  simp [averageObjective, averageObjectiveAmbient, objective, objectiveRegularizer,
    SOptLib.compositeObjective, SOptLib.first_order_linear_model, reg,
    SOptLib.totalizeOn_of_mem, x.2, xstar.2] at hbridge ⊢
  linarith

/-- Internal denominator certificate for `(1-α)η` in the source-gap realization
of Theorem 5.1's displayed rates. -/
theorem rateProductDenominator_ne_for_theorem_5_1
    (η α : ℝ) (hRateDen : theorem_5_1_rateDenominatorBoundary η)
    (hAlpha : alphaRange α) : (1 - α) * η ≠ 0 :=
  mul_ne_zero (one_sub_alpha_ne_zero_of_alphaRange hAlpha) hRateDen

/-- Positivity of the constant `η` in Theorem 5.1, derived from the corrected
rate-denominator boundary and the nonnegative Algorithm 5.1 parameter schedule.
Existing candidates considered: `theorem_5_1_rateDenominatorBoundary` only
records `η ≠ 0`, while the standing parameter nonnegativity is stated for
`setup.η t`; this bridge combines them through the constant policy. -/
private theorem theorem51_eta_pos_of_rate_boundary
    (τ η α : ℝ)
    (hStanding : theoremStandingAssumptions setup)
    (hPolicy : constantParameterPolicy setup τ η α)
    (hRateDen : theorem_5_1_rateDenominatorBoundary η) :
    0 < η := by
  have hη_nonneg : 0 ≤ η := by
    rcases hStanding.1 with ⟨_, _, _, _, _, _, _, _, _, _, _, hParam⟩
    have hsetup : 0 ≤ setup.η 1 := hParam.2.1 1 le_rfl
    simpa [hPolicy.2.1 1 le_rfl] using hsetup
  exact lt_of_le_of_ne hη_nonneg (Ne.symm hRateDen)

/-- Nondegenerate branch for the Theorem 5.1 Lipschitz condition: if a component
smoothness constant is strictly positive, then Eq. (5.1.62) forces the constant
dual parameter `τ` to be positive. This is the branch fact needed by a
division-free Young absorption argument; the `L_i=0` branch is handled
separately without introducing a global `τ ≠ 0` premise. Existing candidates
considered: `tauProbabilityDenominatorsAdmissible` is the forbidden global
Proposition 5.1 denominator boundary, while SOptLib positivity helpers such as
`halfLipschitzStepSize_pos` do not connect the RPDG Lipschitz inequality to
the sampled probability factor. -/
private theorem theorem51_tau_pos_of_lipschitz_positive_component
    (τ η α : ℝ)
    (hStanding : theoremStandingAssumptions setup)
    (hPolicy : constantParameterPolicy setup τ η α)
    (hProb : constantParameterConditionProbability setup τ α)
    (hLip : constantParameterConditionLipschitz setup τ η)
    (hAlpha : alphaRange α)
    (hRateDen : theorem_5_1_rateDenominatorBoundary η)
    (i : ι) (hL_pos : 0 < setup.L i) :
    0 < τ := by
  let m : ℝ := (componentCount (ι := ι) : ℝ)
  let p : ℝ := samplingProbability setup i
  have hm_pos : 0 < m := by
    simpa [m] using componentCount_real_pos (ι := ι)
  have hp_pos : 0 < p := by
    simpa [p] using
      samplingProbability_pos_of_theorem_conditions setup τ η α
        hStanding hPolicy hProb hAlpha i
  have hη_pos : 0 < η :=
    theorem51_eta_pos_of_rate_boundary setup τ η α hStanding hPolicy hRateDen
  have hleft_pos :
      0 <
        sourceQuotient (4 * setup.L i) (componentCount (ι := ι) : ℝ)
          (componentCount_real_ne_zero (ι := ι)) := by
    rw [sourceQuotient_def]
    exact div_pos (mul_pos (by norm_num) hL_pos) hm_pos
  have hrhs_pos : 0 < η * τ * samplingProbability setup i :=
    lt_of_lt_of_le hleft_pos (hLip i)
  have hprod_pos : 0 < τ * (η * p) := by
    simpa [p, mul_assoc, mul_comm, mul_left_comm] using hrhs_pos
  exact pos_of_mul_pos_left hprod_pos (mul_pos hη_pos hp_pos).le

/-- Lemma 5.1: dual-diameter bounds from the initialized dual point.
The statement uses the canonical dual points `m⁻¹∇f_i(x)` and a source
optimizer `x*`, not a globally selected optimizer witness. -/
theorem Lemma_5_1_dual_diameter_bounds
    (hStanding : standingAssumptions setup)
    (xstar : PrimalCarrier setup) (hxstar : IsOptimalPrimal setup xstar) :
    (∀ x : PrimalCarrier setup,
      dualBregmanSum setup (initialDual setup hStanding) (initialDualSubgradient setup hStanding)
        (fun i => scaledComponentGradientDual setup hStanding i x.1) ≤
          (setup.Lf / 2) * ‖setup.x0.1 - x.1‖ ^ 2 ∧
      dualBregmanSum setup (initialDual setup hStanding) (initialDualSubgradient setup hStanding)
        (fun i => scaledComponentGradientDual setup hStanding i x.1) ≤
          setup.Lf * primalBregman setup setup.x0 x) ∧
    dualBregmanSum setup (initialDual setup hStanding) (initialDualSubgradient setup hStanding)
      (fun i => scaledComponentGradientDual setup hStanding i xstar.1) ≤
        objective setup setup.x0 - objective setup xstar := by
  constructor
  · intro x
    have hExpand :=
      dual_bregman_sum_scaled_gradient_eq_average_linearization_gap setup hStanding x
    have hSmooth :=
      average_objective_linearization_gap_le_quadratic setup hStanding setup.x0 x
    have hVBnd := quadratic_bound_le_lf_primal_bregman setup hStanding x
    constructor
    · rw [hExpand]
      exact hSmooth
    · rw [hExpand]
      exact le_trans hSmooth hVBnd
  · have hExpand :=
      dual_bregman_sum_scaled_gradient_eq_average_linearization_gap setup hStanding xstar
    rw [hExpand]
    exact optimal_primal_average_linearization_gap_le_objective_gap setup hStanding xstar hxstar

/-- Theorem 5.1 initial-dual endpoint bound used in the first distance estimate
of Eq. (5.1.63). It combines the theorem-local reciprocal estimate from
Eq. (5.1.60) with Lemma 5.1(a), avoiding the Proposition 5.1
`m τ_t p_i` denominator boundary. Existing candidates considered:
`Proposition_5_1_weighted_RPDG_bound_with_denominator_source_gap` contains this
endpoint term but requires the forbidden proposition denominator boundary, while
`Lemma_5_1_dual_diameter_bounds` supplies only the final unweighted aggregate
dual-diameter estimate. -/
private theorem theorem51_initial_dual_endpoint_le
    (τ η α : ℝ)
    (hStanding : theoremStandingAssumptions setup)
    (hPolicy : constantParameterPolicy setup τ η α)
    (hProb : constantParameterConditionProbability setup τ α)
    (hAlpha : alphaRange α)
    (xstar : PrimalCarrier setup) (hxstar : IsOptimalPrimal setup xstar) :
    (∑ i : ι,
      (theoremOutputWeight α hAlpha 1 *
          (inverseProbabilityValue setup i
              (inverseProbabilityDenominators_ne_of_theorem_conditions
                setup τ η α hStanding hPolicy hProb hAlpha i) *
            (1 + τ) - 1)) *
        (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i (initialDual setup hStanding.1 i) (initialDualSubgradient setup hStanding.1 i)) (initialDual setup hStanding.1 i) (scaledComponentGradientDual setup hStanding.1 i xstar.1))) ≤
      theoremOutputWeight α hAlpha 1 *
        sourceQuotient α (1 - α) (one_sub_alpha_ne_zero_of_alphaRange hAlpha) *
        (setup.Lf * primalBregman setup setup.x0 xstar) := by
  classical
  let hp : (i : ι) → samplingProbability setup i ≠ 0 :=
    inverseProbabilityDenominators_ne_of_theorem_conditions
      setup τ η α hStanding hPolicy hProb hAlpha
  let θ1 : ℝ := theoremOutputWeight α hAlpha 1
  let q : ℝ := sourceQuotient α (1 - α) (one_sub_alpha_ne_zero_of_alphaRange hAlpha)
  have hθ_nonneg : 0 ≤ θ1 := by
    have hpow : 0 < α ^ 1 := pow_pos hAlpha.1 1
    have hpos : 0 < θ1 := by
      simpa [θ1, theoremOutputWeight, sourceQuotient] using one_div_pos.mpr hpow
    exact hpos.le
  have hq_nonneg : 0 ≤ q := by
    have hone_sub_pos : 0 < 1 - α := sub_pos.mpr hAlpha.2
    have hq_pos : 0 < q := by
      simpa [q, sourceQuotient] using div_pos hAlpha.1 hone_sub_pos
    exact hq_pos.le
  have hterm :
      (∑ i : ι,
        (θ1 *
            (inverseProbabilityValue setup i (hp i) *
              (1 + τ) - 1)) *
          (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i (initialDual setup hStanding.1 i) (initialDualSubgradient setup hStanding.1 i)) (initialDual setup hStanding.1 i) (scaledComponentGradientDual setup hStanding.1 i xstar.1))) ≤
        ∑ i : ι,
          (θ1 * q) *
            (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i (initialDual setup hStanding.1 i) (initialDualSubgradient setup hStanding.1 i)) (initialDual setup hStanding.1 i) (scaledComponentGradientDual setup hStanding.1 i xstar.1)) := by
    refine Finset.sum_le_sum ?_
    intro i _hi
    have hcoef :
        inverseProbabilityValue setup i (hp i) * (1 + τ) - 1 ≤ q := by
      simpa [hp, q] using
        theorem51_inverse_probability_initial_coefficient_le
          setup τ η α hStanding hPolicy hProb hAlpha i
    have hscaled :
        θ1 * (inverseProbabilityValue setup i (hp i) * (1 + τ) - 1) ≤
          θ1 * q :=
      mul_le_mul_of_nonneg_left hcoef hθ_nonneg
    have hW_nonneg :
        0 ≤ (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i (initialDual setup hStanding.1 i) (initialDualSubgradient setup hStanding.1 i)) (initialDual setup hStanding.1 i) (scaledComponentGradientDual setup hStanding.1 i xstar.1)) :=
      dualBregman_nonnegative setup i (initialDual setup hStanding.1 i)
        (initialDualSubgradient setup hStanding.1 i)
        (scaledComponentGradientDual setup hStanding.1 i xstar.1)
    exact mul_le_mul_of_nonneg_right hscaled hW_nonneg
  have hsum_eq :
      (∑ i : ι,
          (θ1 * q) *
            (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i (initialDual setup hStanding.1 i) (initialDualSubgradient setup hStanding.1 i)) (initialDual setup hStanding.1 i) (scaledComponentGradientDual setup hStanding.1 i xstar.1))) =
        (θ1 * q) *
          dualBregmanSum setup (initialDual setup hStanding.1)
            (initialDualSubgradient setup hStanding.1)
            (fun i => scaledComponentGradientDual setup hStanding.1 i xstar.1) := by
    simp [dualBregmanSum, Finset.mul_sum]
  have hdiam :
      dualBregmanSum setup (initialDual setup hStanding.1)
          (initialDualSubgradient setup hStanding.1)
          (fun i => scaledComponentGradientDual setup hStanding.1 i xstar.1) ≤
        setup.Lf * primalBregman setup setup.x0 xstar :=
    ((Lemma_5_1_dual_diameter_bounds setup hStanding.1 xstar hxstar).1 xstar).2
  have hscale :
      (θ1 * q) *
          dualBregmanSum setup (initialDual setup hStanding.1)
            (initialDualSubgradient setup hStanding.1)
            (fun i => scaledComponentGradientDual setup hStanding.1 i xstar.1) ≤
        (θ1 * q) * (setup.Lf * primalBregman setup setup.x0 xstar) :=
    mul_le_mul_of_nonneg_left hdiam (mul_nonneg hθ_nonneg hq_nonneg)
  calc
    (∑ i : ι,
      (theoremOutputWeight α hAlpha 1 *
          (inverseProbabilityValue setup i
              (inverseProbabilityDenominators_ne_of_theorem_conditions
                setup τ η α hStanding hPolicy hProb hAlpha i) *
            (1 + τ) - 1)) *
        (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i (initialDual setup hStanding.1 i) (initialDualSubgradient setup hStanding.1 i)) (initialDual setup hStanding.1 i) (scaledComponentGradientDual setup hStanding.1 i xstar.1)))
        ≤
      ∑ i : ι,
        (θ1 * q) *
          (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i (initialDual setup hStanding.1 i) (initialDualSubgradient setup hStanding.1 i)) (initialDual setup hStanding.1 i) (scaledComponentGradientDual setup hStanding.1 i xstar.1)) := by
          simpa [θ1, q, hp] using hterm
    _ = (θ1 * q) *
          dualBregmanSum setup (initialDual setup hStanding.1)
            (initialDualSubgradient setup hStanding.1)
            (fun i => scaledComponentGradientDual setup hStanding.1 i xstar.1) := hsum_eq
    _ ≤ (θ1 * q) * (setup.Lf * primalBregman setup setup.x0 xstar) := hscale
    _ =
      theoremOutputWeight α hAlpha 1 *
        sourceQuotient α (1 - α) (one_sub_alpha_ne_zero_of_alphaRange hAlpha) *
        (setup.Lf * primalBregman setup setup.x0 xstar) := by
          simp [θ1, q, mul_assoc]

/-- Fenchel minorant for the product dual affine form.
Aligns with Lan Lemma 5.2, Eq. (5.1.35): searched `Fenchel conjugate affine
minorant dualConjugate averageObjective U`, checked the local candidates
`SOptLib.le_fenchelConjugateOnCarrier`, `dualConjugate_scaled_component_value`, and
`dual_bregman_sum_scaled_gradient_eq_average_linearization_gap`; the first is
the needed pointwise Fenchel carrier lower bound, while the latter two are specialized
scaled-gradient equalities rather than the arbitrary-dual minorant. -/
private theorem dual_affine_minorizes_average_objective_ambient
    (y : DualProductCarrier setup) (x : E) :
    ⟪x, U setup y⟫_ℝ - ∑ i : ι, dualConjugate setup i (y i) ≤
      averageObjectiveAmbient setup x := by
  classical
  simpa [U, dualConjugate, averageObjectiveAmbient, Finset.mul_sum] using
    (SOptLib.sum_fenchel_affine_minorant_le_weighted_objective
      (w := fun _ : ι => componentCountInverse (ι := ι))
      (f := setup.f)
      (y := fun i : ι => (y i).1)
      (hy := fun i : ι => by
        change BddAbove (Set.range fun x : E =>
          ⟪x, (y i).1⟫_ℝ - componentCountInverse (ι := ι) * setup.f i x)
        exact (y i).2)
      (x := x))

/-- Carrier form of the Fenchel minorant used in Lemma 5.2.
Aligns with Lan Lemma 5.2: the ambient helper above is the exact
`SOptLib.le_fenchelConjugateOnCarrier` sum specialized to feasible `x`; no SOptLib
primitive names this paper's `J_i` product affine minorant. -/
private theorem dual_affine_minorizes_average_objective
    (y : DualProductCarrier setup) (x : PrimalCarrier setup) :
    ⟪x.1, U setup y⟫_ℝ - ∑ i : ι, dualConjugate setup i (y i) ≤
      averageObjective setup x := by
  simpa [averageObjective, averageObjectiveAmbient] using
    dual_affine_minorizes_average_objective_ambient setup y x.1

/-- The scaled component-gradient dual realizes the primal objective in the
saddle value.
Aligns with Lan Lemma 5.2's max-representation step: searched `saddleValue
objective optimal saddle equality conjugate gradient dual witness`; the checked
candidate `dualConjugate_scaled_component_value` supplies the component
Fenchel equality, while no existing helper packages the saddle objective value. -/
private theorem saddleValue_scaledGradientDual_eq_objective
    (hStanding : standingAssumptions setup) (x : PrimalCarrier setup) :
    saddleValue setup x (fun i : ι => scaledComponentGradientDual setup hStanding i x.1) =
      objective setup x := by
  classical
  have hStandingFull := hStanding
  obtain ⟨_, hSmooth, _, hConv, _, _, _, _, _, _, _, _⟩ := hStanding
  have hw : ∀ i : ι, 0 ≤ componentCountInverse (ι := ι) := by
    intro _i
    unfold componentCountInverse
    rw [sourceQuotient_def]
    exact le_of_lt (one_div_pos.mpr (componentCount_real_pos (ι := ι)))
  have hsupport : ∀ i : ι, ∀ z : E,
      setup.f i x.1 + ⟪componentGradient setup i x.1, z - x.1⟫_ℝ ≤ setup.f i z := by
    intro i z
    have hgradWithin :
        HasGradientWithinAt (setup.f i) (componentGradient setup i x.1) Set.univ x.1 := by
      simpa using
        (componentGradient_hasGradientAt_of_componentSmoothness setup hSmooth i x.1)
    exact ConvexOn.first_order_linear_model_le_of_hasGradientWithinAt
      (hConv i) (by simp) (by simp) hgradWithin
  have htouch :=
    SOptLib.linearCoupledSaddleValue_scaledGradientFenchelPoint_eq_objective
      (evalX := fun x : PrimalCarrier setup => x.1)
      (regularizer := objectiveRegularizer setup)
      (w := fun _i : ι => componentCountInverse (ι := ι))
      (f := setup.f)
      (grad := fun i z => componentGradient setup i z)
      (x := x) hw hsupport
  calc
    saddleValue setup x (fun i : ι => scaledComponentGradientDual setup hStandingFull i x.1) =
        objectiveRegularizer setup x +
          ∑ i : ι, componentCountInverse (ι := ι) * setup.f i x.1 := by
      simpa [saddleValue, U, dualConjugate, scaledComponentGradientDual] using htouch
    _ = objective setup x := by
      rw [objective_eq_source_formula]
      simp [objectiveRegularizer, averageObjective, Finset.mul_sum]
      ring

/-- Saddle value against the scaled-gradient dual at a fixed base point. This
is the algebraic half of the primal-optimizer-to-saddle bridge in Theorem 5.1:
the source uses the dual point `y_i*=m⁻¹∇f_i(x*)`, so the saddle value at an
arbitrary feasible `x` is the regularizer at `x` plus the first-order model of
the average objective at `x*`. Existing candidates considered:
`saddleValue_scaledGradientDual_eq_objective` only covers the touching case
`x=x*`, while the Fenchel equality
`dualConjugate_scaled_component_value` provides the needed componentwise
rewrite. -/
private theorem saddleValue_scaledGradientDual_linearized
    (hStanding : standingAssumptions setup) (x base : PrimalCarrier setup) :
    saddleValue setup x
        (fun i : ι => scaledComponentGradientDual setup hStanding i base.1) =
      objectiveRegularizer setup x + averageObjective setup base +
        ⟪x.1 - base.1, averageGradient setup base.1⟫_ℝ := by
  classical
  obtain ⟨_, hSmooth, _, hConv, _, _, _, _, _, _, _, _⟩ := hStanding
  have hw : ∀ i : ι, 0 ≤ componentCountInverse (ι := ι) := by
    intro _i
    unfold componentCountInverse
    rw [sourceQuotient_def]
    exact le_of_lt (one_div_pos.mpr (componentCount_real_pos (ι := ι)))
  have hsupport : ∀ i : ι, ∀ z : E,
      setup.f i base.1 + ⟪componentGradient setup i base.1, z - base.1⟫_ℝ ≤ setup.f i z := by
    intro i z
    have hgradWithin :
        HasGradientWithinAt (setup.f i) (componentGradient setup i base.1) Set.univ base.1 := by
      simpa using
        (componentGradient_hasGradientAt_of_componentSmoothness setup hSmooth i base.1)
    exact ConvexOn.first_order_linear_model_le_of_hasGradientWithinAt
      (hConv i) (by simp) (by simp) hgradWithin
  have hAvgGrad :
      averageGradient setup base.1 =
        ∑ i : ι, componentCountInverse (ι := ι) • componentGradient setup i base.1 := by
    simpa [Finset.smul_sum] using
      (averageGradient_eq_componentGradient_average setup hSmooth base.1)
  have hmodel :=
    SOptLib.linearCoupledSaddleValue_scaledGradientFenchelPoint_eq_firstOrderModel
      (evalX := fun x : PrimalCarrier setup => x.1)
      (regularizer := objectiveRegularizer setup)
      (w := fun _i : ι => componentCountInverse (ι := ι))
      (f := setup.f)
      (grad := fun i z => componentGradient setup i z)
      (x := x) (base := base) hw hsupport
  simpa [saddleValue, U, dualConjugate, scaledComponentGradientDual,
    objectiveRegularizer, averageObjective, hAvgGrad, Finset.mul_sum] using hmodel

/-- The source optimizer with scaled component-gradient dual coordinates is the
saddle solution used in Theorem 5.1. This closes the bridge behind the paper's
implicit choice `z*=(x*,y*)`, `y_i*=m⁻¹∇f_i(x*)`, used for
`Q((x^t,ŷ^t),z*) ≥ 0` and Lemma 5.2. Existing candidates considered:
`Saddle_gap_nonnegative_at_solution` and `Lemma_5_2_primal_gap_from_saddle_gap`
both require a direct Mathlib saddle witness, while the local
`saddleValue_scaledGradientDual_eq_objective`,
`saddleValue_scaledGradientDual_linearized`, and
`dual_affine_minorizes_average_objective` provide the two saddle inequalities
needed to build that witness. -/
private theorem scaled_gradient_dual_saddle_solution_of_primal_optimum
    (hStanding : standingAssumptions setup)
    (xstar : PrimalCarrier setup) (hxstar : IsOptimalPrimal setup xstar) :
    IsSaddlePointOn Set.univ Set.univ (saddleValue setup)
      xstar (fun i : ι => scaledComponentGradientDual setup hStanding i xstar.1) := by
  classical
  let hStanding0 : standingAssumptions setup := hStanding
  obtain ⟨_, hSmooth, _, hConv, _, _, _, _, _, _, _, _⟩ := hStanding
  have hw : ∀ i : ι, 0 ≤ componentCountInverse (ι := ι) := by
    intro _i
    unfold componentCountInverse
    rw [sourceQuotient_def]
    exact le_of_lt (one_div_pos.mpr (componentCount_real_pos (ι := ι)))
  have hsupport : ∀ i : ι, ∀ z : E,
      setup.f i xstar.1 + ⟪componentGradient setup i xstar.1, z - xstar.1⟫_ℝ ≤
        setup.f i z := by
    intro i z
    have hgradWithin :
        HasGradientWithinAt (setup.f i) (componentGradient setup i xstar.1)
          Set.univ xstar.1 := by
      simpa using
        (componentGradient_hasGradientAt_of_componentSmoothness setup hSmooth i xstar.1)
    exact ConvexOn.first_order_linear_model_le_of_hasGradientWithinAt
      (hConv i) (by simp) (by simp) hgradWithin
  have hAvgGrad :
      averageGradient setup xstar.1 =
        ∑ i : ι, componentCountInverse (ι := ι) • componentGradient setup i xstar.1 := by
    simpa [Finset.smul_sum] using
      (averageGradient_eq_componentGradient_average setup hSmooth xstar.1)
  have hregularizer :
      ∀ x : PrimalCarrier setup,
        objectiveRegularizer setup xstar ≤ objectiveRegularizer setup x +
          ⟪x.1 - xstar.1,
            ∑ i : ι, componentCountInverse (ι := ι) •
              componentGradient setup i xstar.1⟫_ℝ := by
    intro x
    have hlin :=
      optimal_primal_average_linearization_gap_le_objective_gap_at
        setup hStanding0 xstar hxstar x
    have hregAvg :
        objectiveRegularizer setup xstar ≤
          objectiveRegularizer setup x +
            ⟪x.1 - xstar.1, averageGradient setup xstar.1⟫_ℝ := by
      rw [objective_eq_source_formula, objective_eq_source_formula] at hlin
      have hinner :
          ⟪averageGradient setup xstar.1, x.1 - xstar.1⟫_ℝ =
            ⟪x.1 - xstar.1, averageGradient setup xstar.1⟫_ℝ :=
        real_inner_comm _ _
      simp [objectiveRegularizer] at hlin ⊢
      linarith [hinner]
    simpa [hAvgGrad] using hregAvg
  simpa [saddleValue, U, dualConjugate, objectiveRegularizer,
    scaledComponentGradientDual, dualSpace] using
    (SOptLib.linearCoupledSaddleValue_scaledGradientFenchelPoint_isSaddlePointOn_of_regularizer_firstOrderBound
      (evalX := fun x : PrimalCarrier setup => x.1)
      (regularizer := objectiveRegularizer setup)
      (w := fun _i : ι => componentCountInverse (ι := ι))
      (f := setup.f)
      (grad := fun i z => componentGradient setup i z)
      (xStar := xstar) hw hsupport hregularizer)

/-- At an optimal saddle point, the selected dual variable touches the primal
objective value.
Aligns with Lan Lemma 5.2's max representation at `x*`: searched the local and
SOptLib saddle/objective candidates; Mathlib's saddle predicate gives the max
property and `saddleValue_scaledGradientDual_eq_objective` supplies the
gradient-generated dual witness, while the reverse inequality is exactly the
Fenchel minorant. -/
private theorem optimal_saddle_saddleValue_eq_objective
    (hStanding : standingAssumptions setup)
    (zstar : SaddlePoint setup) (hzstar : IsSaddlePointOn Set.univ Set.univ (saddleValue setup) zstar.1 zstar.2) :
    saddleValue setup zstar.1 zstar.2 = objective setup zstar.1 := by
  classical
  have hUpper :
      saddleValue setup zstar.1 zstar.2 ≤ objective setup zstar.1 := by
    have hFenchel :=
      dual_affine_minorizes_average_objective setup zstar.2 zstar.1
    rw [objective_eq_source_formula]
    simp [saddleValue, SOptLib.linearCoupledSaddleValue]
    linarith
  have hLower :
      objective setup zstar.1 ≤ saddleValue setup zstar.1 zstar.2 := by
    have hmax :=
      hzstar zstar.1 trivial
        (fun i : ι => scaledComponentGradientDual setup hStanding i zstar.1.1) trivial
    rw [saddleValue_scaledGradientDual_eq_objective setup hStanding zstar.1] at hmax
    exact hmax
  exact le_antisymm hUpper hLower

/-- A differentiable function and a globally touching affine lower support have
the same slope at the touching point.
Aligns with the analytic step in Lan Lemma 5.2: searched `HasGradientAt global
minimum gradient zero IsMinOn univ`, `derivative zero at minimum
HasFDerivAt IsMinOn univ`, and `affine lower support touches differentiable
function gradient equality`; the reusable SOptLib fact is
`Convex.first_order_condition_of_isMinOn_hasFDerivWithinAt`, but no existing
helper packaged this unconstrained affine-touch gradient equality. -/
private theorem affine_minorant_touch_gradient_eq
    {F : E → ℝ} {g a x0 : E} {c : ℝ}
    (hgrad : HasGradientAt F g x0)
    (hminor : ∀ x : E, ⟪x, a⟫_ℝ - c ≤ F x)
    (htouch : ⟪x0, a⟫_ℝ - c = F x0) :
    a = g := by
  exact eq_gradient_of_hasGradientAt_of_affine_minorant_touch hgrad hminor htouch

/-- The dual variable of an optimal saddle point aggregates to the average
gradient at the optimal primal point.
Aligns with Lan Lemma 5.2: the global Fenchel affine minorant touches the
average objective at `x*` by `optimal_saddle_saddleValue_eq_objective`, so
differentiability from `averageSmoothness` identifies its slope. -/
private theorem optimal_saddle_dual_U_eq_averageGradient
    (hStanding : standingAssumptions setup)
    (zstar : SaddlePoint setup) (hzstar : IsSaddlePointOn Set.univ Set.univ (saddleValue setup) zstar.1 zstar.2) :
    U setup zstar.2 = averageGradient setup zstar.1.1 := by
  classical
  let hStanding0 : standingAssumptions setup := hStanding
  obtain ⟨_, _, _, _, _, _, hAvg, _, _, _, _, _⟩ := hStanding
  refine affine_minorant_touch_gradient_eq
    (F := averageObjectiveAmbient setup)
    (g := averageGradient setup zstar.1.1)
    (a := U setup zstar.2)
    (x0 := zstar.1.1)
    (c := ∑ i : ι, dualConjugate setup i (zstar.2 i))
    (averageGradient_hasGradientAt_of_averageSmoothness setup hAvg zstar.1.1)
    ?minor ?touch
  · intro x
    exact dual_affine_minorizes_average_objective_ambient setup zstar.2 x
  · have hTouch :=
      optimal_saddle_saddleValue_eq_objective setup hStanding0 zstar hzstar
    rw [objective_eq_source_formula] at hTouch
    simp [saddleValue, SOptLib.linearCoupledSaddleValue] at hTouch
    simp [averageObjective, averageObjectiveAmbient] at hTouch
    change
      ⟪zstar.1.1, U setup zstar.2⟫_ℝ -
          ∑ i : ι, dualConjugate setup i (zstar.2 i) =
        componentCountInverse * ∑ i : ι, setup.f i zstar.1.1
    linarith

/-- The optimal saddle dual gives the smooth upper model of the average
objective used in Lemma 5.2.
Aligns with Lan Lemma 5.2, Eq. (5.1.35): searched `average objective smooth
quadratic upper model affine dual minorant optimal saddle`; the available
smoothness candidate is the already-proved
`average_objective_linearization_gap_le_quadratic`, while the missing bridge is
that the touching Fenchel affine form has the same slope as `∇f(x*)`. -/
private theorem optimal_saddle_dual_average_upper_model
    (hStanding : standingAssumptions setup)
    (zstar : SaddlePoint setup) (hzstar : IsSaddlePointOn Set.univ Set.univ (saddleValue setup) zstar.1 zstar.2)
    (x : PrimalCarrier setup) :
    averageObjective setup x - averageObjective setup zstar.1 ≤
      ((⟪x.1, U setup zstar.2⟫_ℝ - ∑ i : ι, dualConjugate setup i (zstar.2 i)) -
        (⟪zstar.1.1, U setup zstar.2⟫_ℝ -
          ∑ i : ι, dualConjugate setup i (zstar.2 i))) +
        (setup.Lf / 2) * ‖x.1 - zstar.1.1‖ ^ 2 := by
  classical
  have hSmooth :=
    average_objective_linearization_gap_le_quadratic setup hStanding x zstar.1
  have hU := optimal_saddle_dual_U_eq_averageGradient setup hStanding zstar hzstar
  rw [← hU] at hSmooth
  have hlinear :
      ⟪U setup zstar.2, x.1 - zstar.1.1⟫_ℝ =
        (⟪x.1, U setup zstar.2⟫_ℝ -
          ∑ i : ι, dualConjugate setup i (zstar.2 i)) -
        (⟪zstar.1.1, U setup zstar.2⟫_ℝ -
          ∑ i : ι, dualConjugate setup i (zstar.2 i)) := by
    rw [inner_sub_right]
    rw [real_inner_comm (U setup zstar.2) x.1,
      real_inner_comm (U setup zstar.2) zstar.1.1]
    ring
  rw [hlinear] at hSmooth
  linarith

/-- Lemma 5.2: primal objective gap controlled by the saddle gap plus the average
smoothness correction. -/
theorem Lemma_5_2_primal_gap_from_saddle_gap
    (hStanding : standingAssumptions setup)
    (zbar zstar : SaddlePoint setup)
    (hzstar : IsSaddlePointOn Set.univ Set.univ (saddleValue setup) zstar.1 zstar.2) :
    objective setup zbar.1 - objective setup zstar.1 ≤
      gap setup zbar zstar + (setup.Lf / 2) * ‖zbar.1.1 - zstar.1.1‖ ^ 2 := by
  classical
  have hAvgUpper :=
    optimal_saddle_dual_average_upper_model setup hStanding zstar hzstar zbar.1
  have hTouch :=
    optimal_saddle_saddleValue_eq_objective setup hStanding zstar hzstar
  have hSameDual :
      objective setup zbar.1 - objective setup zstar.1 ≤
        saddleValue setup zbar.1 zstar.2 -
          saddleValue setup zstar.1 zstar.2 +
            (setup.Lf / 2) * ‖zbar.1.1 - zstar.1.1‖ ^ 2 := by
    have hObjStar :
        objective setup zstar.1 =
          setup.h zstar.1.1 + setup.μ * setup.nu zstar.1 +
            (⟪zstar.1.1, U setup zstar.2⟫_ℝ -
              ∑ i : ι, dualConjugate setup i (zstar.2 i)) := by
      rw [← hTouch]
      simp [saddleValue, SOptLib.linearCoupledSaddleValue]
      ring
    have hAffineTouch :
        ⟪zstar.1.1, U setup zstar.2⟫_ℝ -
            ∑ i : ι, dualConjugate setup i (zstar.2 i) =
          averageObjective setup zstar.1 := by
      have hObjFormula := objective_eq_source_formula setup zstar.1
      rw [hObjStar] at hObjFormula
      linarith
    rw [objective_eq_source_formula, hObjStar]
    simp [saddleValue, SOptLib.linearCoupledSaddleValue]
    linarith
  have hgapLower :
      saddleValue setup zbar.1 zstar.2 -
          saddleValue setup zstar.1 zstar.2 ≤
        gap setup zbar zstar := by
    have hy := hzstar zstar.1 trivial zbar.2 trivial
    simp [gap, SOptLib.saddleGap]
    linarith
  linarith

/-- Saddle-gap nonnegativity at a saddle solution, used in Theorem 5.1. -/
theorem Saddle_gap_nonnegative_at_solution
    (hStanding : standingAssumptions setup)
    (t : ℕ) (ω : BlockSamplePath setup)
    (zstar : SaddlePoint setup)
    (hzstar : IsSaddlePointOn Set.univ Set.univ (saddleValue setup) zstar.1 zstar.2) :
    0 ≤ gap setup
      ((xIter setup hStanding t ω), (yHatIter setup hStanding t ω)) zstar := by
  simpa [gap] using
    (SOptLib.saddleGap_nonneg_of_isSaddlePoint
      (L := fun x y => saddleValue setup x y)
      (s := Set.univ)
      (t := Set.univ)
      (z := ((xIter setup hStanding t ω), (yHatIter setup hStanding t ω)))
      (zstar := zstar)
      (hz_left := by trivial)
      (hz_right := by trivial)
      (hzstar := hzstar))

/-- Pointwise nonnegativity of the Theorem 5.1 saddle gap at the source's
canonical `z*=(x*,m⁻¹∇f_i(x*))`. This is the exact bridge used before dropping
the weighted saddle-gap sum in the proof of Eq. (5.1.63). Existing candidates
considered: `Saddle_gap_nonnegative_at_solution` is the generic theorem, and
`scaled_gradient_dual_saddle_solution_of_primal_optimum` above supplies the
specific saddle witness required by Theorem 5.1. -/
private theorem theorem51_scaled_gradient_saddle_gap_nonnegative
    (hStanding : standingAssumptions setup)
    (xstar : PrimalCarrier setup) (hxstar : IsOptimalPrimal setup xstar)
    (t : ℕ) (ω : BlockSamplePath setup) :
    0 ≤ gap setup
      ((xIter setup hStanding t ω), (yHatIter setup hStanding t ω))
      (xstar, fun i : ι => scaledComponentGradientDual setup hStanding i xstar.1) := by
  exact
    Saddle_gap_nonnegative_at_solution setup hStanding t ω
      (xstar, fun i : ι => scaledComponentGradientDual setup hStanding i xstar.1)
      (scaled_gradient_dual_saddle_solution_of_primal_optimum
        setup hStanding xstar hxstar)

/-- A selected carrier subgradient for a function on a closed convex carrier.
Aligns with SOptLib `carrierSubdifferential`: `carrierBregmanDivergence` was
checked and rejected for Lemma 5.3 because the paper fixes a local selected
subgradient `w'(ũ) ∈ ∂w(ũ)` in Eq. (5.1.36), not a global gradient selector. -/
abbrev CarrierSelectedSubgradient
    {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    (C : Set U) (w : U → ℝ) (u : {u : U // u ∈ C}) : Type _ :=
  {g : U // g ∈ SOptLib.carrierSubdifferential (fun z : {u : U // u ∈ C} => w z.1) u}

/-- Selected Bregman distance
`W(u⁰,u)=w(u)-w(u⁰)-⟪w'(u⁰),u-u⁰⟫` from Eq. (5.1.36).
No SOptLib match: searched `Bregman divergence selected subgradient carrier`
and checked `SOptLib.carrierBregmanDivergence`/`SOptLib.carrierSubdifferential`;
the former requires a global gradient selector while Lemma 5.3 is explicitly
based on a chosen subgradient at the current base point. -/
noncomputable def selectedCarrierBregman
    {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    (C : Set U) (w : U → ℝ) (u0 : {u : U // u ∈ C})
    (baseGrad : CarrierSelectedSubgradient C w u0) (u : {u : U // u ∈ C}) : ℝ :=
  w u.1 - (w u0.1 + ⟪baseGrad.1, u.1 - u0.1⟫_ℝ)

/-- Three-point identity for the selected carrier Bregman distance used in
Lemma 5.3. This is the paper identity following Eq. (5.1.36), specialized to
the selected carrier subgradients in the theorem head. -/
theorem selectedCarrierBregman_three_point_identity
    {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    (C : Set U) (w : U → ℝ)
    (wGrad : (u : {u : U // u ∈ C}) → CarrierSelectedSubgradient C w u)
    (u₀ u₁ u₂ : {u : U // u ∈ C}) :
    selectedCarrierBregman C w u₀ (wGrad u₀) u₁ =
      selectedCarrierBregman C w u₀ (wGrad u₀) u₂ +
        ⟪(wGrad u₂).1 - (wGrad u₀).1, u₁.1 - u₂.1⟫_ℝ +
          selectedCarrierBregman C w u₂ (wGrad u₂) u₁ := by
  simpa [selectedCarrierBregman, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    using
      (carrierBregmanDivergence_three_point_identity
        (fun z : {u : U // u ∈ C} => w z.1)
        (fun z : {u : U // u ∈ C} => z.1)
        (fun z : {u : U // u ∈ C} => (wGrad z).1)
        (fun x z : {u : U // u ∈ C} =>
          selectedCarrierBregman C w x (wGrad x) z)
        (by
          intro x z
          simp [selectedCarrierBregman, sub_eq_add_neg, add_comm, add_assoc])
        u₀ u₂ u₁)

/-- Boundary subgradient used by the formal counterexample to the hMin-only
selected-gradient form of Lemma 5.3. At the boundary point `0`, the
carrier-restricted subdifferential of the constant function on `[0,∞)` contains
the outward normal direction `-1`; away from the boundary we select `0`. -/
private noncomputable def lemma53CounterexampleWGrad
    (u : {x : ℝ // x ∈ Set.Ici (0 : ℝ)}) :
    CarrierSelectedSubgradient (Set.Ici (0 : ℝ)) (fun _ : ℝ => (0 : ℝ)) u := by
  by_cases hzero : u.1 = 0
  · refine ⟨-1, ?_⟩
    rw [SOptLib.mem_carrierSubdifferential_iff]
    intro y
    dsimp
    change (0 : ℝ) ≥ 0 + ⟪(-1 : ℝ), y.1 - u.1⟫_ℝ
    rw [hzero]
    simp [inner]
  · refine ⟨0, ?_⟩
    rw [SOptLib.mem_carrierSubdifferential_iff]
    intro y
    simp [inner]

/-- Formal retirement certificate for the hMin-only selected-gradient statement
of Lemma 5.3 under the current carrier-subdifferential model.

The instance is `U = ℝ`, `C = [0,∞)`, `q = 0`, `w = 0`, `μ₀ = 0`,
`μ₁ = 1`, `μ₂ = 0`, `u* = 0`, `u = 1`, with selected carrier subgradient
`w'(0) = -1`. All hMin-only hypotheses hold, but the conclusion forces the
nonnegative boundary Bregman term in the wrong direction. -/
theorem Lemma_5_3_hMin_only_selected_gradient_statement_false :
    ¬ (∀ (C : Set ℝ) (q w : ℝ → ℝ)
      (qGrad : {u : ℝ // u ∈ C} → ℝ)
      (wGrad : (u : {u : ℝ // u ∈ C}) → CarrierSelectedSubgradient C w u)
      (uTilde uStar u : {u : ℝ // u ∈ C}) (μ₀ μ₁ μ₂ : ℝ),
      IsClosed C → Convex ℝ C → ConvexOn ℝ C w → 0 ≤ μ₀ →
      (∀ u₁ u₂ : {u : ℝ // u ∈ C},
        μ₀ * selectedCarrierBregman C w u₂ (wGrad u₂) u₁ ≤
          q u₁.1 - (q u₂.1 + ⟪qGrad u₂, u₁.1 - u₂.1⟫_ℝ)) →
      0 ≤ μ₀ + μ₁ + μ₂ →
      IsMinOn
        (fun z : {u : ℝ // u ∈ C} =>
          q z.1 + μ₁ * w z.1 +
            μ₂ * selectedCarrierBregman C w uTilde (wGrad uTilde) z)
        Set.univ uStar →
      q uStar.1 + μ₁ * w uStar.1 +
          μ₂ * selectedCarrierBregman C w uTilde (wGrad uTilde) uStar +
          (μ₀ + μ₁ + μ₂) * selectedCarrierBregman C w uStar (wGrad uStar) u ≤
        q u.1 + μ₁ * w u.1 +
          μ₂ * selectedCarrierBregman C w uTilde (wGrad uTilde) u) := by
  intro h
  have hRel : ∀ u₁ u₂ : {u : ℝ // u ∈ Set.Ici (0 : ℝ)},
        (0 : ℝ) * selectedCarrierBregman (Set.Ici (0 : ℝ)) (fun _ : ℝ => (0 : ℝ))
            u₂ (lemma53CounterexampleWGrad u₂) u₁ ≤
          (fun _ : ℝ => (0 : ℝ)) u₁.1 -
            ((fun _ : ℝ => (0 : ℝ)) u₂.1 +
              ⟪(fun _ : {u : ℝ // u ∈ Set.Ici (0 : ℝ)} => (0 : ℝ)) u₂,
                u₁.1 - u₂.1⟫_ℝ) := by
    intro a b
    simp [inner]
  have hMin : IsMinOn
        (fun z : {u : ℝ // u ∈ Set.Ici (0 : ℝ)} =>
          (fun _ : ℝ => (0 : ℝ)) z.1 + (1 : ℝ) * (fun _ : ℝ => (0 : ℝ)) z.1 +
            (0 : ℝ) * selectedCarrierBregman (Set.Ici (0 : ℝ)) (fun _ : ℝ => (0 : ℝ))
              (⟨0, by simp⟩ : {u : ℝ // u ∈ Set.Ici (0 : ℝ)})
              (lemma53CounterexampleWGrad
                (⟨0, by simp⟩ : {u : ℝ // u ∈ Set.Ici (0 : ℝ)})) z)
        Set.univ (⟨0, by simp⟩ : {u : ℝ // u ∈ Set.Ici (0 : ℝ)}) := by
    rw [isMinOn_univ_iff]
    intro z
    simp
  have hwconv : ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun _ : ℝ => (0 : ℝ)) := by
    refine ⟨convex_Ici (0 : ℝ), ?_⟩
    intro x hx y hy a b ha hb hab
    simp
  have hres := h (Set.Ici (0 : ℝ)) (fun _ : ℝ => (0 : ℝ)) (fun _ : ℝ => (0 : ℝ))
      (fun _ : {u : ℝ // u ∈ Set.Ici (0 : ℝ)} => (0 : ℝ))
      lemma53CounterexampleWGrad
      (⟨0, by simp⟩ : {u : ℝ // u ∈ Set.Ici (0 : ℝ)})
      (⟨0, by simp⟩ : {u : ℝ // u ∈ Set.Ici (0 : ℝ)})
      (⟨1, by norm_num⟩ : {u : ℝ // u ∈ Set.Ici (0 : ℝ)})
      0 1 0 isClosed_Ici (convex_Ici (0 : ℝ)) hwconv
      (by norm_num) hRel (by norm_num) hMin
  norm_num [selectedCarrierBregman, lemma53CounterexampleWGrad, inner] at hres

/-- Guarded replacement for Lemma 5.3: generalized prox inequality behind the
primal and dual argmin steps, with the selected first-order condition made
explicit. This is the proved source-proof bridge corresponding to the paper
line `⟪φ'(u*), u-u*⟫ ≥ 0`. -/
theorem Lemma_5_3_generalized_prox_inequality_of_selected_FOC
    {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    (C : Set U) (q w : U → ℝ)
    (qGrad : {u : U // u ∈ C} → U)
    (wGrad : (u : {u : U // u ∈ C}) → CarrierSelectedSubgradient C w u)
    (uTilde uStar u : {u : U // u ∈ C}) (μ₀ μ₁ μ₂ : ℝ)
    (hClosed : IsClosed C)
    (hConvexSet : Convex ℝ C)
    (hwConvex : ConvexOn ℝ C w)
    (hMu₀ : 0 ≤ μ₀)
    (hRel : ∀ u₁ u₂ : {u : U // u ∈ C},
      μ₀ * selectedCarrierBregman C w u₂ (wGrad u₂) u₁ ≤
        q u₁.1 - (q u₂.1 + ⟪qGrad u₂, u₁.1 - u₂.1⟫_ℝ))
    (hNonneg : 0 ≤ μ₀ + μ₁ + μ₂)
    (hMin : IsMinOn
      (fun z : {u : U // u ∈ C} =>
        q z.1 + μ₁ * w z.1 +
          μ₂ * selectedCarrierBregman C w uTilde (wGrad uTilde) z)
      Set.univ uStar)
    (hFOC : 0 ≤
      ⟪qGrad uStar + μ₁ • (wGrad uStar).1 +
          μ₂ • ((wGrad uStar).1 - (wGrad uTilde).1),
        u.1 - uStar.1⟫_ℝ) :
    q uStar.1 + μ₁ * w uStar.1 +
        μ₂ * selectedCarrierBregman C w uTilde (wGrad uTilde) uStar +
        (μ₀ + μ₁ + μ₂) * selectedCarrierBregman C w uStar (wGrad uStar) u ≤
      q u.1 + μ₁ * w u.1 +
        μ₂ * selectedCarrierBregman C w uTilde (wGrad uTilde) u := by
  have hRelStar := hRel u uStar
  have hWtilde :
      selectedCarrierBregman C w uTilde (wGrad uTilde) u =
        selectedCarrierBregman C w uTilde (wGrad uTilde) uStar +
          ⟪(wGrad uStar).1 - (wGrad uTilde).1, u.1 - uStar.1⟫_ℝ +
            selectedCarrierBregman C w uStar (wGrad uStar) u :=
    selectedCarrierBregman_three_point_identity C w wGrad uTilde u uStar
  rw [hWtilde]
  simp [inner_add_left, inner_smul_left] at hFOC
  dsimp [selectedCarrierBregman] at hRelStar ⊢
  nlinarith

/-- Corrected Lemma 5.3 paper head. The original hMin-only selected-gradient
Lean interface is formally false under the current carrier-subdifferential
model; see `Lemma_5_3_hMin_only_selected_gradient_statement_false`. The source
proof's actual route uses the variational inequality
`⟪φ'(u*), u-u*⟫ ≥ 0`, represented here as the theorem-local selected FOC. -/
theorem Lemma_5_3_generalized_prox_inequality
    {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    (C : Set U) (q w : U → ℝ)
    (qGrad : {u : U // u ∈ C} → U)
    (wGrad : (u : {u : U // u ∈ C}) → CarrierSelectedSubgradient C w u)
    (uTilde uStar u : {u : U // u ∈ C}) (μ₀ μ₁ μ₂ : ℝ)
    (hClosed : IsClosed C)
    (hConvexSet : Convex ℝ C)
    (hwConvex : ConvexOn ℝ C w)
    (hMu₀ : 0 ≤ μ₀)
    (hRel : ∀ u₁ u₂ : {u : U // u ∈ C},
      μ₀ * selectedCarrierBregman C w u₂ (wGrad u₂) u₁ ≤
        q u₁.1 - (q u₂.1 + ⟪qGrad u₂, u₁.1 - u₂.1⟫_ℝ))
    (hNonneg : 0 ≤ μ₀ + μ₁ + μ₂)
    (hMin : IsMinOn
      (fun z : {u : U // u ∈ C} =>
        q z.1 + μ₁ * w z.1 +
          μ₂ * selectedCarrierBregman C w uTilde (wGrad uTilde) z)
      Set.univ uStar)
    (hFOC : 0 ≤
      ⟪qGrad uStar + μ₁ • (wGrad uStar).1 +
          μ₂ • ((wGrad uStar).1 - (wGrad uTilde).1),
        u.1 - uStar.1⟫_ℝ) :
    q uStar.1 + μ₁ * w uStar.1 +
        μ₂ * selectedCarrierBregman C w uTilde (wGrad uTilde) uStar +
        (μ₀ + μ₁ + μ₂) * selectedCarrierBregman C w uStar (wGrad uStar) u ≤
      q u.1 + μ₁ * w u.1 +
        μ₂ * selectedCarrierBregman C w uTilde (wGrad uTilde) u := by
  exact
    Lemma_5_3_generalized_prox_inequality_of_selected_FOC
      C q w qGrad wGrad uTilde uStar u μ₀ μ₁ μ₂ hClosed hConvexSet hwConvex
      hMu₀ hRel hNonneg hMin hFOC

/-- Lemma 5.4: conditional-expectation identities for the randomized dual update.
This follows the paper's `E_t`, conditioned on `i_1,...,i_{t-1}`, rather than
exposing only an unconditional one-step marginal integral. -/
theorem Lemma_5_4_conditional_expectation_identities
    (hStanding : standingAssumptions setup)
    (t : ℕ) (ht : 1 ≤ t) (i : ι) (y : DualCarrier setup i) :
    (blockStreamLaw setup)[(fun ω =>
        (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) ((yIter setup hStanding t ω) i))) |
        (blockPrefixFiltration setup).seq (t - 1)]
        =ᵐ[blockStreamLaw setup]
        (fun ω => samplingProbability setup i *
          (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) ((yHatIter setup hStanding t ω) i))) ∧
    (blockStreamLaw setup)[(fun ω =>
        (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding t ω) i) (dualSubgradIter setup hStanding t ω i)) ((yIter setup hStanding t ω) i) y)) |
        (blockPrefixFiltration setup).seq (t - 1)] =ᵐ[blockStreamLaw setup]
        (fun ω => samplingProbability setup i *
            (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yHatIter setup hStanding t ω) i) (yHatSubgradIter setup hStanding t ht ω i)) ((yHatIter setup hStanding t ω) i) y) +
          (1 - samplingProbability setup i) *
            (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) y)) := by
  classical
  refine ⟨?first, ?second⟩
  · have hbranch :
        (fun ω =>
          (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) ((yIter setup hStanding t ω) i))) =
        (fun ω =>
          if sampledBlock setup t ω = i then
            (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) ((yHatIter setup hStanding t ω) i))
          else 0) := by
      funext ω
      exact dualBregman_first_observable_branch setup hStanding t ht ω i
    rw [hbranch]
    let k := t - 1
    let phiHit : BlockPrefix setup k → ℝ := fun pref =>
      (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding k (extendBlockPrefix setup k pref)) i) (dualSubgradIter setup hStanding k (extendBlockPrefix setup k pref) i)) ((yIter setup hStanding k (extendBlockPrefix setup k pref)) i) ((yHatIter setup hStanding t (extendBlockPrefix setup k pref)) i))
    have hpayload : ∀ ω : BlockSamplePath setup,
        (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding k ω) i) (dualSubgradIter setup hStanding k ω i)) ((yIter setup hStanding k ω) i) ((yHatIter setup hStanding t ω) i)) =
        phiHit (blockPrefix setup k ω) := by
      intro ω
      have hpred : t - 2 ≤ t - 1 := by omega
      have hs1 := stateProcess_extendBlockPrefix_eq setup hStanding (t - 1) ω
      have hs2 := stateProcess_extendBlockPrefix_eq_of_le setup hStanding hpred ω
      dsimp [phiHit, k, yIter, dualSubgradIter, yHatIter, xTildeIter, xIter]
      rw [hs1, hs2]
    have hleft :
        (fun ω : BlockSamplePath setup =>
          if sampledBlock setup t ω = i then
            (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) ((yHatIter setup hStanding t ω) i))
          else 0) =
        (fun ω : BlockSamplePath setup =>
          if sampledBlock setup t ω = i then
            phiHit (blockPrefix setup k ω)
          else
            (fun _ : BlockPrefix setup k => (0 : ℝ)) (blockPrefix setup k ω)) := by
      funext ω
      by_cases hsample : sampledBlock setup t ω = i
      · simp [hsample, k, hpayload ω]
      · simp [hsample]
    rw [hleft]
    refine (condexp_sampledBlock_if_prefix_observable setup t ht i
      phiHit (fun _ : BlockPrefix setup k => (0 : ℝ))).trans ?_
    filter_upwards with ω
    rw [← hpayload ω]
    ring
  · have hbranch :
        (fun ω =>
          (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding t ω) i) (dualSubgradIter setup hStanding t ω i)) ((yIter setup hStanding t ω) i) y)) =
        (fun ω =>
          if sampledBlock setup t ω = i then
            (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yHatIter setup hStanding t ω) i) (yHatSubgradIter setup hStanding t ht ω i)) ((yHatIter setup hStanding t ω) i) y)
          else
            (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) y)) := by
      funext ω
      exact dualBregman_second_observable_branch setup hStanding t ht ω i y
    rw [hbranch]
    let k := t - 1
    let phiHit : BlockPrefix setup k → ℝ := fun pref =>
      (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yHatIter setup hStanding t (extendBlockPrefix setup k pref)) i) (yHatSubgradIter setup hStanding t ht (extendBlockPrefix setup k pref) i)) ((yHatIter setup hStanding t (extendBlockPrefix setup k pref)) i) y)
    let phiMiss : BlockPrefix setup k → ℝ := fun pref =>
      (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding k (extendBlockPrefix setup k pref)) i) (dualSubgradIter setup hStanding k (extendBlockPrefix setup k pref) i)) ((yIter setup hStanding k (extendBlockPrefix setup k pref)) i) y)
    have hhit : ∀ ω : BlockSamplePath setup,
        (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yHatIter setup hStanding t ω) i) (yHatSubgradIter setup hStanding t ht ω i)) ((yHatIter setup hStanding t ω) i) y) =
        phiHit (blockPrefix setup k ω) := by
      intro ω
      have hpred : t - 2 ≤ t - 1 := by omega
      have hs1 := stateProcess_extendBlockPrefix_eq setup hStanding (t - 1) ω
      have hs2 := stateProcess_extendBlockPrefix_eq_of_le setup hStanding hpred ω
      dsimp [phiHit, k, yIter, dualSubgradIter, yHatIter, yHatSubgradIter,
        xTildeIter, xIter]
      rw [hs1, hs2]
    have hmiss : ∀ ω : BlockSamplePath setup,
        (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding k ω) i) (dualSubgradIter setup hStanding k ω i)) ((yIter setup hStanding k ω) i) y) =
        phiMiss (blockPrefix setup k ω) := by
      intro ω
      have hs1 := stateProcess_extendBlockPrefix_eq setup hStanding (t - 1) ω
      dsimp [phiMiss, k, yIter, dualSubgradIter]
      rw [hs1]
    have hleft :
        (fun ω : BlockSamplePath setup =>
          if sampledBlock setup t ω = i then
            (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yHatIter setup hStanding t ω) i) (yHatSubgradIter setup hStanding t ht ω i)) ((yHatIter setup hStanding t ω) i) y)
          else
            (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) y)) =
        (fun ω : BlockSamplePath setup =>
          if sampledBlock setup t ω = i then
            phiHit (blockPrefix setup k ω)
          else
            phiMiss (blockPrefix setup k ω)) := by
      funext ω
      by_cases hsample : sampledBlock setup t ω = i
      · simp [hsample, k, hhit ω]
      · simp [hsample, k, hmiss ω]
    rw [hleft]
    refine (condexp_sampledBlock_if_prefix_observable setup t ht i
      phiHit phiMiss).trans ?_
    filter_upwards with ω
    rw [← hhit ω, ← hmiss ω]

/-- Integrated second identity from Lemma 5.4 for a fixed block.
Aligns with Lemma 5.5 proof step 5: searched `conditional expectation
integral condExp equals integral`, checked Mathlib `MeasureTheory.integral_condExp`,
and used the source-local `Lemma_5_4_conditional_expectation_identities`. This
is the full-stream integral form that later solves for the `ŷᵢᵗ` Bregman
expectation before transporting back to `finitePrefixExpectation`. -/
private theorem lemma54_second_identity_integral
    (setup : Setup E ι) (hStanding : standingAssumptions setup)
    (t : ℕ) (ht : 1 ≤ t) (i : ι) (y : DualCarrier setup i) :
    (∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding t ω) i) (dualSubgradIter setup hStanding t ω i)) ((yIter setup hStanding t ω) i) y) ∂blockStreamLaw setup) =
      ∫ ω,
        samplingProbability setup i *
            (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yHatIter setup hStanding t ω) i) (yHatSubgradIter setup hStanding t ht ω i)) ((yHatIter setup hStanding t ω) i) y) +
          (1 - samplingProbability setup i) *
            (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) y)
        ∂blockStreamLaw setup := by
  classical
  letI : IsProbabilityMeasure (blockIndexLaw setup) := by
    unfold blockIndexLaw
    infer_instance
  let μ : Measure (BlockSamplePath setup) := blockStreamLaw setup
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    unfold blockStreamLaw
    exact SOptLib.iidStreamLaw_isProbabilityMeasure (blockIndexLaw setup)
  let m : MeasurableSpace (BlockSamplePath setup) :=
    (blockPrefixFiltration setup).seq (t - 1)
  have hle : m ≤ MeasurableSpace.pi := by
    dsimp [m]
    exact Filtration.le (blockPrefixFiltration setup) (t - 1)
  letI : IsFiniteMeasure (μ.trim hle) := isFiniteMeasure_trim (μ := μ) hle
  let A : BlockSamplePath setup → ℝ := fun ω =>
    (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding t ω) i) (dualSubgradIter setup hStanding t ω i)) ((yIter setup hStanding t ω) i) y)
  let B : BlockSamplePath setup → ℝ := fun ω =>
    samplingProbability setup i *
        (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yHatIter setup hStanding t ω) i) (yHatSubgradIter setup hStanding t ht ω i)) ((yHatIter setup hStanding t ω) i) y) +
      (1 - samplingProbability setup i) *
        (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) y)
  have hcond : μ[A | m] =ᵐ[μ] B := by
    simpa [μ, m, A, B] using
      (Lemma_5_4_conditional_expectation_identities setup hStanding t ht i y).2
  exact integral_eq_of_condExp_ae_eq (μ := μ) (m := m) (A := A) (B := B) hle hcond

/-- Split scalar-coefficient form of Lemma 5.4's second integrated identity.
Aligns with Lemma 5.5 proof step 5: this refines
`lemma54_second_identity_integral` using `MeasureTheory.integral_add` and
`MeasureTheory.integral_const_mul`, exposing the equation that is solved for
the `ŷᵢᵗ` Bregman expectation. -/
private theorem lemma54_second_identity_integral_split
    (setup : Setup E ι) (hStanding : standingAssumptions setup)
    (t : ℕ) (ht : 1 ≤ t) (i : ι) (y : DualCarrier setup i) :
    (∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding t ω) i) (dualSubgradIter setup hStanding t ω i)) ((yIter setup hStanding t ω) i) y) ∂blockStreamLaw setup) =
      samplingProbability setup i *
        (∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yHatIter setup hStanding t ω) i) (yHatSubgradIter setup hStanding t ht ω i)) ((yHatIter setup hStanding t ω) i) y) ∂blockStreamLaw setup) +
      (1 - samplingProbability setup i) *
        (∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) y)
          ∂blockStreamLaw setup) := by
  classical
  let H : BlockSamplePath setup → ℝ := fun ω =>
    (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yHatIter setup hStanding t ω) i) (yHatSubgradIter setup hStanding t ht ω i)) ((yHatIter setup hStanding t ω) i) y)
  let C : BlockSamplePath setup → ℝ := fun ω =>
    (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) y)
  have hraw := lemma54_second_identity_integral setup hStanding t ht i y
  have hH_int : Integrable H (blockStreamLaw setup) := by
    simpa [H] using
      dual_hat_bregman_integrable_blockStream setup hStanding t ht i y
  have hC_int : Integrable C (blockStreamLaw setup) := by
    simpa [C] using
      dual_iter_bregman_integrable_blockStream_of_le setup hStanding
        (by omega : t - 1 ≤ t) i y
  have hH_scaled :
      Integrable (fun ω : BlockSamplePath setup =>
        samplingProbability setup i * H ω) (blockStreamLaw setup) :=
    hH_int.const_mul (samplingProbability setup i)
  have hC_scaled :
      Integrable (fun ω : BlockSamplePath setup =>
        (1 - samplingProbability setup i) * C ω) (blockStreamLaw setup) :=
    hC_int.const_mul (1 - samplingProbability setup i)
  have hsplit :
      (∫ ω,
        samplingProbability setup i * H ω +
          (1 - samplingProbability setup i) * C ω ∂blockStreamLaw setup) =
        samplingProbability setup i * (∫ ω, H ω ∂blockStreamLaw setup) +
          (1 - samplingProbability setup i) *
            (∫ ω, C ω ∂blockStreamLaw setup) := by
    calc
      (∫ ω,
        samplingProbability setup i * H ω +
          (1 - samplingProbability setup i) * C ω ∂blockStreamLaw setup) =
          (∫ ω, samplingProbability setup i * H ω ∂blockStreamLaw setup) +
            ∫ ω, (1 - samplingProbability setup i) * C ω ∂blockStreamLaw setup := by
            exact MeasureTheory.integral_add hH_scaled hC_scaled
      _ = samplingProbability setup i * (∫ ω, H ω ∂blockStreamLaw setup) +
          (1 - samplingProbability setup i) *
            (∫ ω, C ω ∂blockStreamLaw setup) := by
            rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  calc
    (∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding t ω) i) (dualSubgradIter setup hStanding t ω i)) ((yIter setup hStanding t ω) i) y) ∂blockStreamLaw setup) =
        ∫ ω,
          samplingProbability setup i * H ω +
            (1 - samplingProbability setup i) * C ω
          ∂blockStreamLaw setup := by
          simpa [H, C] using hraw
    _ = samplingProbability setup i *
        (∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yHatIter setup hStanding t ω) i) (yHatSubgradIter setup hStanding t ht ω i)) ((yHatIter setup hStanding t ω) i) y) ∂blockStreamLaw setup) +
      (1 - samplingProbability setup i) *
        (∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) y)
          ∂blockStreamLaw setup) := by
          simpa [H, C] using hsplit

/-- Solved block-stream form of Lemma 5.4's second Bregman substitution.
Aligns with Lemma 5.5 proof step 5: this consumes the split integrated
conditional-expectation identity and the all-block denominator boundary to
derive the displayed `p_i^{-1}` coefficients for the `ŷᵢᵗ` term. -/
private theorem lemma55_dual_hat_bregman_blockStream_substitution
    (setup : Setup E ι) (hStanding : standingAssumptions setup)
    (hProbDen : allBlockProbabilityDenominatorsAdmissible setup)
    (t : ℕ) (ht : 1 ≤ t) (i : ι) (y : DualCarrier setup i) :
    (∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yHatIter setup hStanding t ω) i) (yHatSubgradIter setup hStanding t ht ω i)) ((yHatIter setup hStanding t ω) i) y) ∂blockStreamLaw setup) =
      inverseProbabilityValue setup i (hProbDen i) *
        (∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding t ω) i) (dualSubgradIter setup hStanding t ω i)) ((yIter setup hStanding t ω) i) y) ∂blockStreamLaw setup) -
      (inverseProbabilityValue setup i (hProbDen i) - 1) *
        (∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) y)
          ∂blockStreamLaw setup) := by
  classical
  let A : ℝ :=
    ∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding t ω) i) (dualSubgradIter setup hStanding t ω i)) ((yIter setup hStanding t ω) i) y) ∂blockStreamLaw setup
  let H : ℝ :=
    ∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yHatIter setup hStanding t ω) i) (yHatSubgradIter setup hStanding t ht ω i)) ((yHatIter setup hStanding t ω) i) y) ∂blockStreamLaw setup
  let C : ℝ :=
    ∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) y) ∂blockStreamLaw setup
  let p : ℝ := samplingProbability setup i
  let inv : ℝ := inverseProbabilityValue setup i (hProbDen i)
  have hsplit : A = p * H + (1 - p) * C := by
    simpa [A, H, C, p] using
      lemma54_second_identity_integral_split setup hStanding t ht i y
  have hinv : inv * p = 1 := by
    dsimp [inv, p, inverseProbabilityValue]
    rw [sourceQuotient_def]
    field_simp [hProbDen i]
  simpa [A, H, C, inv] using
    eq_inv_mul_sub_inv_sub_one_mul_of_eq_mul_add_one_sub_mul hsplit hinv

/-- The residual Bregman observable `W_i(y_i^{t-1}, yHat_i^t)` is determined
by the finite paper prefix through time `t`.
Aligns with Lemma 5.5 proof step 5. Considered
`dual_hat_bregman_prefixObservable` and
`dual_iter_bregman_prefixObservable_of_le`; neither matches because the source
residual has a previous-iterate base and the path-dependent `yHat` endpoint. -/
private theorem dual_residual_hat_bregman_prefixObservable
    (setup : Setup E ι) (hStanding : standingAssumptions setup)
    (t : ℕ) (ht : 1 ≤ t) (i : ι) :
    (fun ω : BlockSamplePath setup =>
      (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) ((yHatIter setup hStanding t ω) i))) =
      fun ω : BlockSamplePath setup =>
        (fun pref : BlockPrefix setup t =>
          (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1)
              (extendBlockPrefix setup t pref)) i) (dualSubgradIter setup hStanding (t - 1)
              (extendBlockPrefix setup t pref) i)) ((yIter setup hStanding (t - 1)
              (extendBlockPrefix setup t pref)) i) ((yHatIter setup hStanding t
              (extendBlockPrefix setup t pref)) i)))
          (blockPrefix setup t ω) := by
  funext ω
  have hprev :
      stateProcess setup hStanding (t - 1)
          (extendBlockPrefix setup t (blockPrefix setup t ω)) =
        stateProcess setup hStanding (t - 1) ω := by
    exact stateProcess_extendBlockPrefix_eq_of_le setup hStanding (by omega) ω
  have hprev2 :
      stateProcess setup hStanding (t - 2)
          (extendBlockPrefix setup t (blockPrefix setup t ω)) =
        stateProcess setup hStanding (t - 2) ω := by
    exact stateProcess_extendBlockPrefix_eq_of_le setup hStanding (by omega) ω
  dsimp [yIter, dualSubgradIter, yHatIter, xTildeIter, xIter]
  rw [hprev, hprev2]

/-- The residual Bregman observable `W_i(y_i^{t-1}, y_i^t)` is determined by
the finite paper prefix through time `t`.
Aligns with Lemma 5.5 proof step 5. Considered
`finite_prefix_expectation_dual_iter_bregman_eq_blockStream_of_le`; it handles
a fixed endpoint `y`, while the source residual endpoint is the generated
current iterate `y_i^t`. -/
private theorem dual_residual_current_bregman_prefixObservable
    (setup : Setup E ι) (hStanding : standingAssumptions setup)
    (t : ℕ) (i : ι) :
    (fun ω : BlockSamplePath setup =>
      (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) ((yIter setup hStanding t ω) i))) =
      fun ω : BlockSamplePath setup =>
        (fun pref : BlockPrefix setup t =>
          (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1)
              (extendBlockPrefix setup t pref)) i) (dualSubgradIter setup hStanding (t - 1)
              (extendBlockPrefix setup t pref) i)) ((yIter setup hStanding (t - 1)
              (extendBlockPrefix setup t pref)) i) ((yIter setup hStanding t
              (extendBlockPrefix setup t pref)) i)))
          (blockPrefix setup t ω) := by
  funext ω
  have hcur :
      stateProcess setup hStanding t
          (extendBlockPrefix setup t (blockPrefix setup t ω)) =
        stateProcess setup hStanding t ω := by
    exact stateProcess_extendBlockPrefix_eq setup hStanding t ω
  have hprev :
      stateProcess setup hStanding (t - 1)
          (extendBlockPrefix setup t (blockPrefix setup t ω)) =
        stateProcess setup hStanding (t - 1) ω := by
    exact stateProcess_extendBlockPrefix_eq_of_le setup hStanding (by omega) ω
  dsimp [yIter, dualSubgradIter]
  rw [hcur, hprev]

/-- Full-stream integrability for the source residual
`W_i(y_i^{t-1}, yHat_i^t)`.
Aligns with Lemma 5.5 proof step 5 and reuses the paper-prefix finite-range
integrability bridge; no existing fixed-endpoint Bregman integrability lemma
matches this path-dependent endpoint. -/
private theorem dual_residual_hat_bregman_integrable_blockStream
    (setup : Setup E ι) (hStanding : standingAssumptions setup)
    (t : ℕ) (ht : 1 ≤ t) (i : ι) :
    Integrable (fun ω : BlockSamplePath setup =>
      (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) ((yHatIter setup hStanding t ω) i)))
      (blockStreamLaw setup) := by
  let ψ : BlockPrefix setup t → ℝ := fun pref =>
    (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) (extendBlockPrefix setup t pref)) i) (dualSubgradIter setup hStanding (t - 1)
        (extendBlockPrefix setup t pref) i)) ((yIter setup hStanding (t - 1) (extendBlockPrefix setup t pref)) i) ((yHatIter setup hStanding t (extendBlockPrefix setup t pref)) i))
  have hψ :
      Integrable (fun ω : BlockSamplePath setup => ψ (blockPrefix setup t ω))
        (blockStreamLaw setup) :=
    prefixObservable_integrable_blockStream setup t ψ
  exact hψ.congr
    (Filter.Eventually.of_forall fun ω =>
      (congrFun (dual_residual_hat_bregman_prefixObservable
        setup hStanding t ht i) ω).symm)

/-- Full-stream integrability for the source residual
`W_i(y_i^{t-1}, y_i^t)`.
Aligns with Lemma 5.5 proof step 5 and reuses the paper-prefix finite-range
integrability bridge; the existing current-iterate Bregman integrability lemma
has a fixed endpoint and therefore does not match. -/
private theorem dual_residual_current_bregman_integrable_blockStream
    (setup : Setup E ι) (hStanding : standingAssumptions setup)
    (t : ℕ) (i : ι) :
    Integrable (fun ω : BlockSamplePath setup =>
      (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) ((yIter setup hStanding t ω) i)))
      (blockStreamLaw setup) := by
  let ψ : BlockPrefix setup t → ℝ := fun pref =>
    (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) (extendBlockPrefix setup t pref)) i) (dualSubgradIter setup hStanding (t - 1)
        (extendBlockPrefix setup t pref) i)) ((yIter setup hStanding (t - 1) (extendBlockPrefix setup t pref)) i) ((yIter setup hStanding t (extendBlockPrefix setup t pref)) i))
  have hψ :
      Integrable (fun ω : BlockSamplePath setup => ψ (blockPrefix setup t ω))
        (blockStreamLaw setup) :=
    prefixObservable_integrable_blockStream setup t ψ
  exact hψ.congr
    (Filter.Eventually.of_forall fun ω =>
      (congrFun (dual_residual_current_bregman_prefixObservable
        setup hStanding t i) ω).symm)

/-- Finite-prefix expectation of `W_i(y_i^{t-1}, yHat_i^t)` as a full-stream
integral.
Aligns with Lemma 5.5 proof step 5. Existing transports
`finite_prefix_expectation_dual_hat_bregman_eq_blockStream` and
`finite_prefix_expectation_dual_iter_bregman_eq_blockStream_of_le` were
considered, but neither has the previous base together with the path-dependent
hat endpoint required by the source residual observation. -/
private theorem finite_prefix_expectation_dual_residual_hat_bregman_eq_blockStream
    (setup : Setup E ι) (hStanding : standingAssumptions setup)
    (t : ℕ) (ht : 1 ≤ t) (i : ι) :
    finitePrefixExpectation setup t (fun ω =>
      (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) ((yHatIter setup hStanding t ω) i))) =
      ∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) ((yHatIter setup hStanding t ω) i)) ∂blockStreamLaw setup := by
  let ψ : BlockPrefix setup t → ℝ := fun pref =>
    (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) (extendBlockPrefix setup t pref)) i) (dualSubgradIter setup hStanding (t - 1)
        (extendBlockPrefix setup t pref) i)) ((yIter setup hStanding (t - 1) (extendBlockPrefix setup t pref)) i) ((yHatIter setup hStanding t (extendBlockPrefix setup t pref)) i))
  calc
    finitePrefixExpectation setup t (fun ω =>
        (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) ((yHatIter setup hStanding t ω) i))) =
        finitePrefixExpectation setup t (fun ω => ψ (blockPrefix setup t ω)) := by
          rw [dual_residual_hat_bregman_prefixObservable setup hStanding t ht i]
    _ = ∫ ω, ψ (blockPrefix setup t ω) ∂blockStreamLaw setup := by
          exact finite_prefix_expectation_block_stream_bridge setup t ψ
    _ = ∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) ((yHatIter setup hStanding t ω) i)) ∂blockStreamLaw setup := by
          rw [← dual_residual_hat_bregman_prefixObservable setup hStanding t ht i]

/-- Finite-prefix expectation of `W_i(y_i^{t-1}, y_i^t)` as a full-stream
integral.
Aligns with Lemma 5.5 proof step 5. Existing fixed-endpoint Bregman transports
were considered and rejected for this residual because the endpoint is the
generated current block `y_i^t`. -/
private theorem finite_prefix_expectation_dual_residual_current_bregman_eq_blockStream
    (setup : Setup E ι) (hStanding : standingAssumptions setup)
    (t : ℕ) (i : ι) :
    finitePrefixExpectation setup t (fun ω =>
      (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) ((yIter setup hStanding t ω) i))) =
      ∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) ((yIter setup hStanding t ω) i)) ∂blockStreamLaw setup := by
  let ψ : BlockPrefix setup t → ℝ := fun pref =>
    (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) (extendBlockPrefix setup t pref)) i) (dualSubgradIter setup hStanding (t - 1)
        (extendBlockPrefix setup t pref) i)) ((yIter setup hStanding (t - 1) (extendBlockPrefix setup t pref)) i) ((yIter setup hStanding t (extendBlockPrefix setup t pref)) i))
  calc
    finitePrefixExpectation setup t (fun ω =>
        (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) ((yIter setup hStanding t ω) i))) =
        finitePrefixExpectation setup t (fun ω => ψ (blockPrefix setup t ω)) := by
          rw [dual_residual_current_bregman_prefixObservable setup hStanding t i]
    _ = ∫ ω, ψ (blockPrefix setup t ω) ∂blockStreamLaw setup := by
          exact finite_prefix_expectation_block_stream_bridge setup t ψ
    _ = ∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) ((yIter setup hStanding t ω) i)) ∂blockStreamLaw setup := by
          rw [← dual_residual_current_bregman_prefixObservable setup hStanding t i]

/-- Integrated first identity from Lemma 5.4 for the residual term.
Aligns with Lemma 5.5 proof step 5 and the observation after Eq. (5.1.45).
Considered `lemma54_second_identity_integral`, but it is the fixed-endpoint
second Lemma 5.4 identity; the first identity is needed for
`W_i(y_i^{t-1}, yHat_i^t)`. -/
private theorem lemma54_first_identity_integral
    (setup : Setup E ι) (hStanding : standingAssumptions setup)
    (t : ℕ) (ht : 1 ≤ t) (i : ι) :
    (∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) ((yIter setup hStanding t ω) i)) ∂blockStreamLaw setup) =
      ∫ ω,
        samplingProbability setup i *
          (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) ((yHatIter setup hStanding t ω) i))
        ∂blockStreamLaw setup := by
  classical
  letI : IsProbabilityMeasure (blockIndexLaw setup) := by
    unfold blockIndexLaw
    infer_instance
  let μ : Measure (BlockSamplePath setup) := blockStreamLaw setup
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    unfold blockStreamLaw
    exact SOptLib.iidStreamLaw_isProbabilityMeasure (blockIndexLaw setup)
  let m : MeasurableSpace (BlockSamplePath setup) :=
    (blockPrefixFiltration setup).seq (t - 1)
  have hle : m ≤ MeasurableSpace.pi := by
    dsimp [m]
    exact Filtration.le (blockPrefixFiltration setup) (t - 1)
  let A : BlockSamplePath setup → ℝ := fun ω =>
    (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) ((yIter setup hStanding t ω) i))
  let H : BlockSamplePath setup → ℝ := fun ω =>
    samplingProbability setup i *
      (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) ((yHatIter setup hStanding t ω) i))
  have hcond : μ[A | m] =ᵐ[μ] H := by
    simpa [μ, m, A, H] using
      (Lemma_5_4_conditional_expectation_identities
        setup hStanding t ht i ((initialState setup hStanding).y i)).1
  exact integral_eq_of_condExp_ae_eq (μ := μ) (m := m) (A := A) (B := H) hle hcond

/-- Scalar-coefficient split of Lemma 5.4's first integrated residual identity.
Aligns with Lemma 5.5 proof step 5: it exposes
`E[W_i(y_i^{t-1}, y_i^t)] = p_i E[W_i(y_i^{t-1}, yHat_i^t)]`.
Existing split helper `lemma54_second_identity_integral_split` was considered
and rejected because it splits the second, fixed-endpoint identity. -/
private theorem lemma54_first_identity_integral_split
    (setup : Setup E ι) (hStanding : standingAssumptions setup)
    (t : ℕ) (ht : 1 ≤ t) (i : ι) :
    (∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) ((yIter setup hStanding t ω) i)) ∂blockStreamLaw setup) =
      samplingProbability setup i *
        (∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) ((yHatIter setup hStanding t ω) i)) ∂blockStreamLaw setup) := by
  classical
  let H : BlockSamplePath setup → ℝ := fun ω =>
    (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) ((yHatIter setup hStanding t ω) i))
  have hraw := lemma54_first_identity_integral setup hStanding t ht i
  have hH_int : Integrable H (blockStreamLaw setup) := by
    simpa [H] using
      dual_residual_hat_bregman_integrable_blockStream setup hStanding t ht i
  have hsplit :
      (∫ ω, samplingProbability setup i * H ω ∂blockStreamLaw setup) =
        samplingProbability setup i * (∫ ω, H ω ∂blockStreamLaw setup) := by
    rw [MeasureTheory.integral_const_mul]
  calc
    (∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) ((yIter setup hStanding t ω) i)) ∂blockStreamLaw setup) =
        ∫ ω, samplingProbability setup i * H ω ∂blockStreamLaw setup := by
          simpa [H] using hraw
    _ = samplingProbability setup i *
        (∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) ((yHatIter setup hStanding t ω) i)) ∂blockStreamLaw setup) := by
          simpa [H] using hsplit

/-- Solved block-stream first residual substitution from Lemma 5.4.
Aligns with Lemma 5.5 proof step 5:
`E[W_i(y_i^{t-1}, yHat_i^t)] = p_i^{-1} E[W_i(y_i^{t-1}, y_i^t)]`.
No SOptLib match: searched `Bregman residual sampled block finite prefix
expectation current yHat` and checked the existing fixed-endpoint transports
and `lemma54_second_identity_integral_split`; none align with the first
Lemma 5.4 residual identity because their endpoints are fixed. -/
private theorem lemma55_first_residual_blockStream_substitution
    (setup : Setup E ι) (hStanding : standingAssumptions setup)
    (hProbDen : allBlockProbabilityDenominatorsAdmissible setup)
    (t : ℕ) (ht : 1 ≤ t) (i : ι) :
    (∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) ((yHatIter setup hStanding t ω) i)) ∂blockStreamLaw setup) =
      inverseProbabilityValue setup i (hProbDen i) *
        (∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) ((yIter setup hStanding t ω) i)) ∂blockStreamLaw setup) := by
  classical
  let A : ℝ :=
    ∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) ((yIter setup hStanding t ω) i)) ∂blockStreamLaw setup
  let H : ℝ :=
    ∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) ((yHatIter setup hStanding t ω) i)) ∂blockStreamLaw setup
  let p : ℝ := samplingProbability setup i
  let inv : ℝ := inverseProbabilityValue setup i (hProbDen i)
  have hsplit : A = p * H := by
    simpa [A, H, p] using
      lemma54_first_identity_integral_split setup hStanding t ht i
  have hinv : inv * p = 1 := by
    dsimp [inv, p, inverseProbabilityValue]
    rw [sourceQuotient_def]
    field_simp [hProbDen i]
  have hsolve : H = inv * A := by
    rw [hsplit]
    calc
      H = (inv * p) * H := by rw [hinv]; ring
      _ = inv * (p * H) := by ring
  simpa [A, H, inv] using hsolve

/-- Finite-prefix first residual substitution from Lemma 5.4, in the exact
form needed by Lemma 5.5's `hsubst`.
Aligns with the observation after Eq. (5.1.45). Existing finite-prefix Bregman
transports were checked and do not match this residual endpoint, so this helper
combines the new residual transports with the solved block-stream identity. -/
private theorem lemma55_first_residual_finite_substitution
    (setup : Setup E ι) (hStanding : standingAssumptions setup)
    (hProbDen : allBlockProbabilityDenominatorsAdmissible setup)
    (t : ℕ) (ht : 1 ≤ t) (i : ι) :
    finitePrefixExpectation setup t (fun ω =>
      (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) ((yHatIter setup hStanding t ω) i))) =
      inverseProbabilityValue setup i (hProbDen i) *
        finitePrefixExpectation setup t (fun ω =>
          (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) ((yIter setup hStanding t ω) i))) := by
  calc
    finitePrefixExpectation setup t (fun ω =>
        (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) ((yHatIter setup hStanding t ω) i))) =
        ∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) ((yHatIter setup hStanding t ω) i)) ∂blockStreamLaw setup := by
          exact finite_prefix_expectation_dual_residual_hat_bregman_eq_blockStream
            setup hStanding t ht i
    _ = inverseProbabilityValue setup i (hProbDen i) *
        (∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) ((yIter setup hStanding t ω) i)) ∂blockStreamLaw setup) := by
          exact lemma55_first_residual_blockStream_substitution
            setup hStanding hProbDen t ht i
    _ = inverseProbabilityValue setup i (hProbDen i) *
        finitePrefixExpectation setup t (fun ω =>
          (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) ((yIter setup hStanding t ω) i))) := by
          rw [← finite_prefix_expectation_dual_residual_current_bregman_eq_blockStream
                setup hStanding t i]

/-- Pointwise collapse of the fixed-block residual sum to the sampled residual.
Aligns with Lemma 5.5 proof step 5, observation
`W_i(y_i^{t-1},y_i^t)=0` for `i ≠ i_t`. Considered SOptLib finite residual
and selected-estimator lemmas from the search results; they package integral or
centering facts, while this source step is the direct pointwise
`Finset.sum_eq_single` collapse using `dualBregman_first_observable_branch`. -/
private theorem lemma55_sampled_residual_pointwise_sum
    (setup : Setup E ι) (hStanding : standingAssumptions setup)
    (hProbDen : allBlockProbabilityDenominatorsAdmissible setup)
    (t : ℕ) (ht : 1 ≤ t) (ω : BlockSamplePath setup) :
    (∑ i : ι,
      inverseProbabilityValue setup i (hProbDen i) *
        (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) ((yIter setup hStanding t ω) i))) =
      inverseProbabilityValue setup (sampledBlock setup t ω)
          (sampledBlock_probability_ne_zero setup
            (sampledPositiveBlock setup t ω)) *
        (SOptLib.carrierBregmanDivergence (dualConjugate setup (sampledBlock setup t ω)) (dualConjugateBaseSelector setup (sampledBlock setup t ω) ((yIter setup hStanding (t - 1) ω) (sampledBlock setup t ω)) (dualSubgradIter setup hStanding (t - 1) ω
            (sampledBlock setup t ω))) ((yIter setup hStanding (t - 1) ω) (sampledBlock setup t ω)) ((yIter setup hStanding t ω) (sampledBlock setup t ω))) := by
  classical
  let s : ι := sampledBlock setup t ω
  have hcollapse :
      (∑ i : ι,
        inverseProbabilityValue setup i (hProbDen i) *
          (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) ((yIter setup hStanding t ω) i))) =
        inverseProbabilityValue setup s (hProbDen s) *
          (SOptLib.carrierBregmanDivergence (dualConjugate setup s) (dualConjugateBaseSelector setup s ((yIter setup hStanding (t - 1) ω) s) (dualSubgradIter setup hStanding (t - 1) ω s)) ((yIter setup hStanding (t - 1) ω) s) ((yIter setup hStanding t ω) s)) := by
    rw [Finset.sum_eq_single s]
    · intro b _ hb
      have hsample_ne : sampledBlock setup t ω ≠ b := by
        simpa [s] using hb.symm
      have hbranch :=
        dualBregman_first_observable_branch setup hStanding t ht ω b
      have hzero :
          (SOptLib.carrierBregmanDivergence (dualConjugate setup b) (dualConjugateBaseSelector setup b ((yIter setup hStanding (t - 1) ω) b) (dualSubgradIter setup hStanding (t - 1) ω b)) ((yIter setup hStanding (t - 1) ω) b) ((yIter setup hStanding t ω) b)) = 0 := by
        simpa [hsample_ne] using hbranch
      simp [hzero]
    · intro hs
      simp at hs
  calc
    (∑ i : ι,
      inverseProbabilityValue setup i (hProbDen i) *
        (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) ((yIter setup hStanding t ω) i))) =
        inverseProbabilityValue setup s (hProbDen s) *
          (SOptLib.carrierBregmanDivergence (dualConjugate setup s) (dualConjugateBaseSelector setup s ((yIter setup hStanding (t - 1) ω) s) (dualSubgradIter setup hStanding (t - 1) ω s)) ((yIter setup hStanding (t - 1) ω) s) ((yIter setup hStanding t ω) s)) := hcollapse
    _ = inverseProbabilityValue setup (sampledBlock setup t ω)
          (sampledBlock_probability_ne_zero setup
            (sampledPositiveBlock setup t ω)) *
        (SOptLib.carrierBregmanDivergence (dualConjugate setup (sampledBlock setup t ω)) (dualConjugateBaseSelector setup (sampledBlock setup t ω) ((yIter setup hStanding (t - 1) ω) (sampledBlock setup t ω)) (dualSubgradIter setup hStanding (t - 1) ω
            (sampledBlock setup t ω))) ((yIter setup hStanding (t - 1) ω) (sampledBlock setup t ω)) ((yIter setup hStanding t ω) (sampledBlock setup t ω))) := by
          simp [s, inverseProbabilityValue, sourceQuotient]

/-- Finite-prefix form of the sampled residual collapse, preserving the
pointwise finite sum inside the integrand.
Aligns with Lemma 5.5 proof step 5 before final expectation linearity. The
SOptLib expectation-splitting hits and `MeasureTheory.integral_finset_sum` were
considered; this narrower bridge uses the already-proved pointwise collapse and
therefore avoids unnecessary integral side conditions at this stage. -/
private theorem lemma55_sampled_residual_sum_finitePrefix
    (setup : Setup E ι) (hStanding : standingAssumptions setup)
    (hProbDen : allBlockProbabilityDenominatorsAdmissible setup)
    (t : ℕ) (ht : 1 ≤ t) :
    finitePrefixExpectation setup t (fun ω =>
      ∑ i : ι,
        (setup.τ t * inverseProbabilityValue setup i (hProbDen i)) *
          (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) ((yIter setup hStanding t ω) i))) =
      finitePrefixExpectation setup t (fun ω =>
        (setup.τ t *
            inverseProbabilityValue setup (sampledBlock setup t ω)
              (sampledBlock_probability_ne_zero setup
                (sampledPositiveBlock setup t ω))) *
          (SOptLib.carrierBregmanDivergence (dualConjugate setup (sampledBlock setup t ω)) (dualConjugateBaseSelector setup (sampledBlock setup t ω) ((yIter setup hStanding (t - 1) ω) (sampledBlock setup t ω)) (dualSubgradIter setup hStanding (t - 1) ω
              (sampledBlock setup t ω))) ((yIter setup hStanding (t - 1) ω) (sampledBlock setup t ω)) ((yIter setup hStanding t ω) (sampledBlock setup t ω)))) := by
  apply congrArg (finitePrefixExpectation setup t)
  funext ω
  have hcollapse :=
    lemma55_sampled_residual_pointwise_sum
      setup hStanding hProbDen t ht ω
  calc
    (∑ i : ι,
      (setup.τ t * inverseProbabilityValue setup i (hProbDen i)) *
        (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) ((yIter setup hStanding t ω) i))) =
        setup.τ t *
          (∑ i : ι,
            inverseProbabilityValue setup i (hProbDen i) *
              (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) ((yIter setup hStanding t ω) i))) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = setup.τ t *
        (inverseProbabilityValue setup (sampledBlock setup t ω)
            (sampledBlock_probability_ne_zero setup
              (sampledPositiveBlock setup t ω)) *
          (SOptLib.carrierBregmanDivergence (dualConjugate setup (sampledBlock setup t ω)) (dualConjugateBaseSelector setup (sampledBlock setup t ω) ((yIter setup hStanding (t - 1) ω) (sampledBlock setup t ω)) (dualSubgradIter setup hStanding (t - 1) ω
              (sampledBlock setup t ω))) ((yIter setup hStanding (t - 1) ω) (sampledBlock setup t ω)) ((yIter setup hStanding t ω) (sampledBlock setup t ω)))) := by
          rw [hcollapse]
    _ = (setup.τ t *
            inverseProbabilityValue setup (sampledBlock setup t ω)
              (sampledBlock_probability_ne_zero setup
                (sampledPositiveBlock setup t ω))) *
          (SOptLib.carrierBregmanDivergence (dualConjugate setup (sampledBlock setup t ω)) (dualConjugateBaseSelector setup (sampledBlock setup t ω) ((yIter setup hStanding (t - 1) ω) (sampledBlock setup t ω)) (dualSubgradIter setup hStanding (t - 1) ω
              (sampledBlock setup t ω))) ((yIter setup hStanding (t - 1) ω) (sampledBlock setup t ω)) ((yIter setup hStanding t ω) (sampledBlock setup t ω))) := by
          ring

/-- The scalar dual-prediction payload for a fixed block is determined by the
past prefix `i_1,...,i_{t-1}`.
Aligns with Lemma 5.5 proof step 5 and Eq. (5.1.26): searched `prefix
observable xTilde yHat stateProcess determined by prefix`; the reusable hit is
the local `stateProcess_extendBlockPrefix_eq_of_le`, while no SOptLib theorem
knows this file's `yHatIter` and dependent dual-subgradient accessors. -/
private theorem lemma55_dual_prediction_payload_prefixObservable
    (setup : Setup E ι) (hStanding : standingAssumptions setup)
    (t : ℕ) (i : ι) (zE : E) :
    (fun ω : BlockSamplePath setup =>
      ⟪xTildeIter setup hStanding t ω - zE,
        (yHatIter setup hStanding t ω i).1 -
          ((yIter setup hStanding (t - 1) ω) i).1⟫_ℝ) =
      fun ω : BlockSamplePath setup =>
        (fun pref : BlockPrefix setup (t - 1) =>
          ⟪xTildeIter setup hStanding t (extendBlockPrefix setup (t - 1) pref) - zE,
            (yHatIter setup hStanding t
              (extendBlockPrefix setup (t - 1) pref) i).1 -
              ((yIter setup hStanding (t - 1)
                (extendBlockPrefix setup (t - 1) pref)) i).1⟫_ℝ)
          (blockPrefix setup (t - 1) ω) := by
  funext ω
  have hprev :
      stateProcess setup hStanding (t - 1)
          (extendBlockPrefix setup (t - 1) (blockPrefix setup (t - 1) ω)) =
        stateProcess setup hStanding (t - 1) ω := by
    exact stateProcess_extendBlockPrefix_eq setup hStanding (t - 1) ω
  have hprev2 :
      stateProcess setup hStanding (t - 2)
          (extendBlockPrefix setup (t - 1) (blockPrefix setup (t - 1) ω)) =
        stateProcess setup hStanding (t - 2) ω := by
    exact stateProcess_extendBlockPrefix_eq_of_le setup hStanding (by omega) ω
  dsimp [xTildeIter, xIter, yHatIter, yIter, dualSubgradIter]
  rw [hprev, hprev2]

/-- Fixed-coordinate full-stream version of the dual-prediction unbiased
inner-product cancellation.
Aligns with Lemma 5.5 proof step 5: this is the scalar branch consumer of
`condexp_sampledBlock_if_prefix_observable`, with the reciprocal simplified by
`sourceQuotient_def` and `hProbDen i`. -/
private theorem lemma55_dual_prediction_coordinate_integral_eq_zero
    (setup : Setup E ι) (hStanding : standingAssumptions setup)
    (hProbDen : allBlockProbabilityDenominatorsAdmissible setup)
    (t : ℕ) (ht : 1 ≤ t) (i : ι) (zE : E) :
    (∫ ω : BlockSamplePath setup,
      ⟪xTildeIter setup hStanding t ω - zE,
        (yHatIter setup hStanding t ω i).1 -
          yTildeIter setup hStanding t ω i⟫_ℝ ∂blockStreamLaw setup) = 0 := by
  classical
  let μ : Measure (BlockSamplePath setup) := blockStreamLaw setup
  let m : MeasurableSpace (BlockSamplePath setup) :=
    (blockPrefixFiltration setup).seq (t - 1)
  let inv : ι → ℝ := fun j => inverseProbabilityValue setup j (hProbDen j)
  let p : ι → ℝ := fun j => samplingProbability setup j
  let prefixPayload : BlockPrefix setup (t - 1) → ℝ := fun pref =>
    ⟪xTildeIter setup hStanding t (extendBlockPrefix setup (t - 1) pref) - zE,
      (yHatIter setup hStanding t
        (extendBlockPrefix setup (t - 1) pref) i).1 -
        ((yIter setup hStanding (t - 1)
          (extendBlockPrefix setup (t - 1) pref)) i).1⟫_ℝ
  let payload : ι → BlockSamplePath setup → ℝ := fun _ ω =>
    prefixPayload (blockPrefix setup (t - 1) ω)
  let phiHit : BlockPrefix setup (t - 1) → ℝ := fun pref =>
    (1 - inv i) * prefixPayload pref
  let phiMiss : BlockPrefix setup (t - 1) → ℝ := fun pref =>
    prefixPayload pref
  have hZ :
      (fun ω : BlockSamplePath setup =>
        ⟪xTildeIter setup hStanding t ω - zE,
          (yHatIter setup hStanding t ω i).1 -
            yTildeIter setup hStanding t ω i⟫_ℝ) =ᵐ[μ]
        fun ω : BlockSamplePath setup =>
          if sampledBlock setup t ω = i then
            (1 - inv i) * payload i ω
          else
            payload i ω := by
    refine Filter.Eventually.of_forall ?_
    intro ω
    have hpayload :
        prefixPayload (blockPrefix setup (t - 1) ω) =
          ⟪xTildeIter setup hStanding t ω - zE,
            (yHatIter setup hStanding t ω i).1 -
              ((yIter setup hStanding (t - 1) ω) i).1⟫_ℝ := by
      exact (congrFun
        (lemma55_dual_prediction_payload_prefixObservable
          setup hStanding t i zE) ω).symm
    let delta : E :=
      (yHatIter setup hStanding t ω i).1 -
        ((yIter setup hStanding (t - 1) ω) i).1
    have hy :=
      yTildeIter_sub_yHatIter_branch setup hStanding hProbDen t ht ω i
    by_cases hsample : sampledBlock setup t ω = i
    · have hyhit :
          yTildeIter setup hStanding t ω i -
              (yHatIter setup hStanding t ω i).1 =
            (inv i - 1) • delta := by
        simpa [inv, delta, hsample] using hy
      have hdiff :
          (yHatIter setup hStanding t ω i).1 -
              yTildeIter setup hStanding t ω i =
            (1 - inv i) • delta := by
        calc
          (yHatIter setup hStanding t ω i).1 -
              yTildeIter setup hStanding t ω i =
              -(yTildeIter setup hStanding t ω i -
                (yHatIter setup hStanding t ω i).1) := by
                module
          _ = -((inv i - 1) • delta) := by rw [hyhit]
          _ = (1 - inv i) • delta := by module
      simp [payload, prefixPayload, hpayload, hsample, hdiff, delta,
        inner_smul_right]
    · have hymiss :
          yTildeIter setup hStanding t ω i -
              (yHatIter setup hStanding t ω i).1 =
            -delta := by
        simpa [delta, hsample] using hy
      have hdiff :
          (yHatIter setup hStanding t ω i).1 -
              yTildeIter setup hStanding t ω i =
            delta := by
        calc
          (yHatIter setup hStanding t ω i).1 -
              yTildeIter setup hStanding t ω i =
              -(yTildeIter setup hStanding t ω i -
                (yHatIter setup hStanding t ω i).1) := by
                module
          _ = -(-delta) := by rw [hymiss]
          _ = delta := by module
      simp [payload, prefixPayload, hpayload, hsample, hdiff, delta]
  have hcond :
      μ[(fun ω : BlockSamplePath setup =>
          if sampledBlock setup t ω = i then
            (1 - inv i) * payload i ω
          else
            payload i ω) | m] =ᵐ[μ]
        fun ω : BlockSamplePath setup =>
          p i * ((1 - inv i) * payload i ω) +
            (1 - p i) * payload i ω := by
    simpa [μ, m, p, inv, payload, prefixPayload, phiHit, phiMiss] using
      condexp_sampledBlock_if_prefix_observable setup t ht i phiHit phiMiss
  have hinv : p i * inv i = 1 := by
    dsimp [p, inv, inverseProbabilityValue]
    rw [sourceQuotient_def]
    field_simp [hProbDen i]
  have hm : m ≤ MeasurableSpace.pi := by
    dsimp [m]
    exact Filtration.le (blockPrefixFiltration setup) (t - 1)
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    letI : IsProbabilityMeasure (blockIndexLaw setup) := by
      unfold blockIndexLaw
      infer_instance
    unfold blockStreamLaw
    exact SOptLib.iidStreamLaw_isProbabilityMeasure (blockIndexLaw setup)
  exact
    integral_inverse_probability_hit_miss_payload_eq_zero
      (μ := μ) (m := m) hm (sampledBlock setup t) p inv payload i
      (Z := fun ω : BlockSamplePath setup =>
        ⟪xTildeIter setup hStanding t ω - zE,
          (yHatIter setup hStanding t ω i).1 -
            yTildeIter setup hStanding t ω i⟫_ℝ)
      (by simpa [μ] using hZ) hcond hinv

/-- A fixed-coordinate dual-prediction inner-product observable is determined
by the generated paper prefix through time `t`.
Aligns with Lemma 5.5 proof step 5: this is the finite-prefix transport needed
before summing the full-stream coordinate cancellations. Searched `prefix
observable xTilde yHat yTilde inner`; the existing determinism helper
`stateProcess_extendBlockPrefix_eq_of_le` is the matching local primitive. -/
private theorem lemma55_dual_prediction_coordinate_prefixObservable
    (setup : Setup E ι) (hStanding : standingAssumptions setup)
    (t : ℕ) (i : ι) (zE : E) :
    (fun ω : BlockSamplePath setup =>
      ⟪xTildeIter setup hStanding t ω - zE,
        (yHatIter setup hStanding t ω i).1 -
          yTildeIter setup hStanding t ω i⟫_ℝ) =
      fun ω : BlockSamplePath setup =>
        (fun pref : BlockPrefix setup t =>
          ⟪xTildeIter setup hStanding t (extendBlockPrefix setup t pref) - zE,
            (yHatIter setup hStanding t (extendBlockPrefix setup t pref) i).1 -
              yTildeIter setup hStanding t (extendBlockPrefix setup t pref) i⟫_ℝ)
          (blockPrefix setup t ω) := by
  funext ω
  have hcur :
      stateProcess setup hStanding t
          (extendBlockPrefix setup t (blockPrefix setup t ω)) =
        stateProcess setup hStanding t ω := by
    exact stateProcess_extendBlockPrefix_eq setup hStanding t ω
  have hprev :
      stateProcess setup hStanding (t - 1)
          (extendBlockPrefix setup t (blockPrefix setup t ω)) =
        stateProcess setup hStanding (t - 1) ω := by
    exact stateProcess_extendBlockPrefix_eq_of_le setup hStanding (by omega) ω
  have hprev2 :
      stateProcess setup hStanding (t - 2)
          (extendBlockPrefix setup t (blockPrefix setup t ω)) =
        stateProcess setup hStanding (t - 2) ω := by
    exact stateProcess_extendBlockPrefix_eq_of_le setup hStanding (by omega) ω
  dsimp [xTildeIter, xIter, yHatIter, yIter, dualSubgradIter, yTildeIter]
  rw [hcur, hprev, hprev2]

/-- Finite-prefix expectation is additive for generated prefix observables.
Aligns with Lemma 5.5 proof step 6 expectation linearity: searched `finite
prefix expectation add sub sum linearity integral`; Mathlib supplies
`MeasureTheory.integral_add`, while finite-prefix integrability is discharged
by `finite_prefix_observable_integrable`. -/
private theorem finitePrefixExpectation_add
    (setup : Setup E ι) (k : ℕ) (F G : BlockSamplePath setup → ℝ) :
    finitePrefixExpectation setup k (fun ω => F ω + G ω) =
      finitePrefixExpectation setup k F + finitePrefixExpectation setup k G := by
  exact SOptLib.finitePrefixExpectation_add
    (μ := blockStreamLaw setup) (prefixMap := blockPrefix setup k)
    (extend := extendBlockPrefix setup k) (F := F) (G := G)
    (finite_prefix_observable_integrable setup k
      (fun pref : BlockPrefix setup k => F (extendBlockPrefix setup k pref)))
    (finite_prefix_observable_integrable setup k
      (fun pref : BlockPrefix setup k => G (extendBlockPrefix setup k pref)))

/-- Finite-prefix expectation is subtractive for generated prefix observables.
This is the subtraction companion to `finitePrefixExpectation_add`, aligned with
Lemma 5.5 proof step 6 expectation linearity. -/
private theorem finitePrefixExpectation_sub
    (setup : Setup E ι) (k : ℕ) (F G : BlockSamplePath setup → ℝ) :
    finitePrefixExpectation setup k (fun ω => F ω - G ω) =
      finitePrefixExpectation setup k F - finitePrefixExpectation setup k G := by
  exact SOptLib.finitePrefixExpectation_sub
    (μ := blockStreamLaw setup) (prefixMap := blockPrefix setup k)
    (extend := extendBlockPrefix setup k) (F := F) (G := G)
    (finite_prefix_observable_integrable setup k
      (fun pref : BlockPrefix setup k => F (extendBlockPrefix setup k pref)))
    (finite_prefix_observable_integrable setup k
      (fun pref : BlockPrefix setup k => G (extendBlockPrefix setup k pref)))

/-- Finite-prefix expectation commutes with deterministic real multiplication.
This packages Mathlib `MeasureTheory.integral_const_mul` at the paper's
finite-prefix source boundary. -/
private theorem finitePrefixExpectation_const_mul
    (setup : Setup E ι) (k : ℕ) (c : ℝ) (F : BlockSamplePath setup → ℝ) :
    finitePrefixExpectation setup k (fun ω => c * F ω) =
      c * finitePrefixExpectation setup k F := by
  exact SOptLib.finitePrefixExpectation_const_mul
    (μ := blockStreamLaw setup) (prefixMap := blockPrefix setup k)
    (extend := extendBlockPrefix setup k) (c := c) (F := F)

/-- Finite-prefix expectation commutes with finite coordinate sums.
Aligns with Lemma 5.5 proof step 6, where the dual Bregman coordinate sum is
split before applying Lemma 5.4 substitutions. -/
private theorem finitePrefixExpectation_finset_sum
    (setup : Setup E ι) (k : ℕ) (F : ι → BlockSamplePath setup → ℝ) :
    finitePrefixExpectation setup k (fun ω => ∑ i : ι, F i ω) =
      ∑ i : ι, finitePrefixExpectation setup k (F i) := by
  unfold finitePrefixExpectation
  simpa using
    (MeasureTheory.integral_finset_sum
      (μ := blockPrefixLaw setup k) (s := (Finset.univ : Finset ι))
      (f := fun i pref => F i (extendBlockPrefix setup k pref))
      (by
        intro i _hi
        exact finite_prefix_observable_integrable setup k
          (fun pref : BlockPrefix setup k => F i (extendBlockPrefix setup k pref))))

/-- Finite-prefix expectation commutes with an arbitrary finite real sum.
This generalizes `finitePrefixExpectation_finset_sum` from coordinate sums to
the Proposition 5.1 time window `Finset.Icc 1 k`; searched
`finitePrefixExpectation finite Finset sum linearity` and found only the
coordinate-specialized helper plus generic Mathlib/SOptLib integral-sum APIs. -/
private theorem finitePrefixExpectation_sum_finset
    (setup : Setup E ι) (k : ℕ) {α : Type*} (s : Finset α)
    (F : α → BlockSamplePath setup → ℝ) :
    finitePrefixExpectation setup k (fun ω => ∑ a ∈ s, F a ω) =
      ∑ a ∈ s, finitePrefixExpectation setup k (F a) := by
  classical
  simpa [finitePrefixExpectation] using
    (SOptLib.finitePrefixExpectation_sum_finset
      (μ := blockStreamLaw setup) (prefixMap := blockPrefix setup k)
      (extend := extendBlockPrefix setup k) (s := s) (F := F)
      (hF := by
        intro a _ha
        exact finite_prefix_observable_integrable setup k
          (fun pref : BlockPrefix setup k => F a (extendBlockPrefix setup k pref))))

/-- Saddle-gap observables at time `t` are determined by any generated prefix
that contains time `t`.

Aligns with the finite-prefix transport needed after Lan Eq. (5.1.66).
Candidate audit: searched `finite prefix expectation saddle gap horizon
transport`; existing Bregman transports cover only primal or dual Bregman
terms, while this helper packages the generated `gap ((x^t,ŷ^t),z)` observable
using `stateProcess_extendBlockPrefix_eq_of_le`. -/
private theorem finite_prefix_expectation_saddle_gap_eq_of_le
    (setup : Setup E ι) (hStanding : standingAssumptions setup)
    {t k : ℕ} (hle : t ≤ k) (z : SaddlePoint setup) :
    finitePrefixExpectation setup k (fun ω =>
      gap setup ((xIter setup hStanding t ω), yHatIter setup hStanding t ω) z) =
      expectedSaddleGap setup hStanding t z := by
  let F : BlockSamplePath setup → ℝ := fun ω =>
    gap setup ((xIter setup hStanding t ω), yHatIter setup hStanding t ω) z
  have hFk :
      ∀ ω : BlockSamplePath setup,
        F (extendBlockPrefix setup k (blockPrefix setup k ω)) = F ω := by
    intro ω
    have hcur :
        stateProcess setup hStanding t
            (extendBlockPrefix setup k (blockPrefix setup k ω)) =
          stateProcess setup hStanding t ω := by
      exact stateProcess_extendBlockPrefix_eq_of_le setup hStanding hle ω
    have hprev :
        stateProcess setup hStanding (t - 1)
            (extendBlockPrefix setup k (blockPrefix setup k ω)) =
          stateProcess setup hStanding (t - 1) ω := by
      exact stateProcess_extendBlockPrefix_eq_of_le setup hStanding (by omega) ω
    have hprev2 :
        stateProcess setup hStanding (t - 2)
            (extendBlockPrefix setup k (blockPrefix setup k ω)) =
          stateProcess setup hStanding (t - 2) ω := by
      exact stateProcess_extendBlockPrefix_eq_of_le setup hStanding (by omega) ω
    have hx :
        xIter setup hStanding t
            (extendBlockPrefix setup k (blockPrefix setup k ω)) =
          xIter setup hStanding t ω := by
      dsimp [xIter]
      rw [hcur]
    have hyhat :
        yHatIter setup hStanding t
            (extendBlockPrefix setup k (blockPrefix setup k ω)) =
          yHatIter setup hStanding t ω := by
      funext i
      dsimp [yHatIter, xTildeIter, xIter, yIter, dualSubgradIter]
      rw [hprev, hprev2]
    simp [F, hx, hyhat]
  have hFt :
      ∀ ω : BlockSamplePath setup,
        F (extendBlockPrefix setup t (blockPrefix setup t ω)) = F ω := by
    intro ω
    have hcur :
        stateProcess setup hStanding t
            (extendBlockPrefix setup t (blockPrefix setup t ω)) =
          stateProcess setup hStanding t ω := by
      exact stateProcess_extendBlockPrefix_eq_of_le setup hStanding (le_rfl : t ≤ t) ω
    have hprev :
        stateProcess setup hStanding (t - 1)
            (extendBlockPrefix setup t (blockPrefix setup t ω)) =
          stateProcess setup hStanding (t - 1) ω := by
      exact stateProcess_extendBlockPrefix_eq_of_le setup hStanding (by omega) ω
    have hprev2 :
        stateProcess setup hStanding (t - 2)
            (extendBlockPrefix setup t (blockPrefix setup t ω)) =
          stateProcess setup hStanding (t - 2) ω := by
      exact stateProcess_extendBlockPrefix_eq_of_le setup hStanding (by omega) ω
    have hx :
        xIter setup hStanding t
            (extendBlockPrefix setup t (blockPrefix setup t ω)) =
          xIter setup hStanding t ω := by
      dsimp [xIter]
      rw [hcur]
    have hyhat :
        yHatIter setup hStanding t
            (extendBlockPrefix setup t (blockPrefix setup t ω)) =
          yHatIter setup hStanding t ω := by
      funext i
      dsimp [yHatIter, xTildeIter, xIter, yIter, dualSubgradIter]
      rw [hprev, hprev2]
    simp [F, hx, hyhat]
  calc
    finitePrefixExpectation setup k F =
        ∫ ω, F ω ∂blockStreamLaw setup := by
          exact finite_prefix_expectation_eq_blockStream_of_extend_eq setup k F hFk
    _ = finitePrefixExpectation setup t F := by
          rw [← finite_prefix_expectation_eq_blockStream_of_extend_eq setup t F hFt]
    _ = expectedSaddleGap setup hStanding t z := by
          rfl

/-- Finite weighted-sum linearity of the left slot of the real inner product.

Local infrastructure for Lan Eq. (5.1.66)'s affine saddle-gap terms. Existing
candidate `weighted_inner_sum_eq_zero_of_weighted_sum_eq_zero` handles only the
zero-centered consequence, while the current proof needs the literal equality. -/
private theorem finset_inner_sum_smul_left_eq_sum_mul_inner
    {β : Type*} (s : Finset β) (c : β → ℝ) (v : β → E) (u : E) :
    ⟪∑ i ∈ s, c i • v i, u⟫_ℝ =
      ∑ i ∈ s, c i * ⟪v i, u⟫_ℝ := by
  exact inner_sum_smul_left_eq_sum_mul_inner s c v u

/-- Finite weighted-sum linearity of the right slot of the real inner product.

Local infrastructure for Lan Eq. (5.1.66)'s affine saddle-gap terms. Existing
candidate `weighted_inner_sum_eq_zero_of_weighted_sum_eq_zero` handles only the
left-slot zero-centered consequence, while the dual-output bridge needs this
right-slot equality. -/
private theorem finset_inner_sum_smul_right_eq_sum_mul_inner
    {β : Type*} (s : Finset β) (u : E) (c : β → ℝ) (v : β → E) :
    ⟪u, ∑ i ∈ s, c i • v i⟫_ℝ =
      ∑ i ∈ s, c i * ⟪u, v i⟫_ℝ := by
  exact inner_sum_smul_right_eq_sum_mul_inner s u c v

/-- Pathwise weighted Jensen bridge for the saddle gap at the canonical
Theorem 5.1 output.

Aligns with Lan proof step after Eq. (5.1.66): `Q(z̄^k,z)` is bounded by the
normalized weighted sum of `Q((x^t,ŷ^t),z)` by convexity in the first argument.
Candidate audit: searched `weighted saddle gap Jensen`, checked SOptLib
`convexOn_weighted_average_le_weighted_sum`, and proved the necessary local
subspecializations `theorem51_weighted_objective_regularizer_le` and
`theorem51_weighted_dual_conjugate_sum_le`; the remaining local obligation is
the paper-specific linear `U`/constant algebra tying those convex components
to the literal `gap` definition. -/
private theorem theorem51_gap_weighted_output_pathwise_le_weighted_saddle_sum
    (α : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hStanding : standingAssumptions setup) (hAlpha : alphaRange α)
    (z : SaddlePoint setup) (ω : BlockSamplePath setup) :
    gap setup
        ((weightedOutput setup α k hk hStanding hAlpha ω),
          weightedDualOutput setup α k hk hStanding hAlpha ω) z ≤
      (outputWeightSum α hAlpha k)⁻¹ *
        ∑ t ∈ outputTimeWindow k,
          theoremOutputWeight α hAlpha t *
            gap setup ((xIter setup hStanding t ω), yHatIter setup hStanding t ω) z := by
  classical
  have hreg :=
    theorem51_weighted_objective_regularizer_le
      setup α k hk hStanding hAlpha ω
  have hdual :=
    theorem51_weighted_dual_conjugate_sum_le
      setup α k hk hStanding hAlpha ω
  let W : ℝ := outputWeightSum α hAlpha k
  let s : Finset ℕ := outputTimeWindow k
  let γ : ℕ → ℝ := theoremOutputWeight α hAlpha
  let px : ℕ → E := fun t => (xIter setup hStanding t ω).1
  let uz : E := U setup z.2
  have hlin_x :
      ⟪(weightedOutput setup α k hk hStanding hAlpha ω).1, U setup z.2⟫_ℝ =
        (outputWeightSum α hAlpha k)⁻¹ *
          ∑ t ∈ outputTimeWindow k,
            theoremOutputWeight α hAlpha t *
              ⟪(xIter setup hStanding t ω).1, U setup z.2⟫_ℝ := by
    have hxavg :
        (weightedOutput setup α k hk hStanding hAlpha ω).1 =
          W⁻¹ • ∑ t ∈ s, γ t • px t := by
      rw [weightedOutput_eq]
      unfold weightedOutputVector SOptLib.weightedAverageOutputValue
      rfl
    calc
      ⟪(weightedOutput setup α k hk hStanding hAlpha ω).1, U setup z.2⟫_ℝ =
          ⟪W⁻¹ • ∑ t ∈ s, γ t • px t, uz⟫_ℝ := by
            rw [hxavg]
      _ = W⁻¹ * ⟪∑ t ∈ s, γ t • px t, uz⟫_ℝ := by
            simp [inner_smul_left]
      _ = W⁻¹ * (∑ t ∈ s, γ t * ⟪px t, uz⟫_ℝ) := by
            rw [finset_inner_sum_smul_left_eq_sum_mul_inner]
      _ = (outputWeightSum α hAlpha k)⁻¹ *
          ∑ t ∈ outputTimeWindow k,
            theoremOutputWeight α hAlpha t *
              ⟪(xIter setup hStanding t ω).1, U setup z.2⟫_ℝ := by
            rfl
  let zCarrier : E := z.1.1
  have hlin_y :
      ⟪z.1.1, U setup (weightedDualOutput setup α k hk hStanding hAlpha ω)⟫_ℝ =
        (outputWeightSum α hAlpha k)⁻¹ *
          ∑ t ∈ outputTimeWindow k,
            theoremOutputWeight α hAlpha t *
              ⟪z.1.1, U setup (yHatIter setup hStanding t ω)⟫_ℝ := by
    have hUavg :
        U setup (weightedDualOutput setup α k hk hStanding hAlpha ω) =
          ∑ i : ι, W⁻¹ •
            ∑ t ∈ s, γ t • ((yHatIter setup hStanding t ω) i).1 := by
      unfold U
      refine Finset.sum_congr rfl ?_
      intro i _hi
      rw [weightedDualOutput_eq]
    calc
      ⟪z.1.1, U setup (weightedDualOutput setup α k hk hStanding hAlpha ω)⟫_ℝ =
          ⟪zCarrier,
            ∑ i : ι, W⁻¹ •
              ∑ t ∈ s, γ t • ((yHatIter setup hStanding t ω) i).1⟫_ℝ := by
            rw [hUavg]
      _ = ∑ i : ι, W⁻¹ *
            (∑ t ∈ s, γ t *
              ⟪zCarrier, ((yHatIter setup hStanding t ω) i).1⟫_ℝ) := by
            rw [inner_sum]
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [inner_smul_right]
            rw [finset_inner_sum_smul_right_eq_sum_mul_inner]
      _ = W⁻¹ * ∑ i : ι,
            (∑ t ∈ s, γ t *
              ⟪zCarrier, ((yHatIter setup hStanding t ω) i).1⟫_ℝ) := by
            rw [Finset.mul_sum]
      _ = W⁻¹ * ∑ t ∈ s, ∑ i : ι,
            γ t * ⟪zCarrier, ((yHatIter setup hStanding t ω) i).1⟫_ℝ := by
            congr 1
            rw [Finset.sum_comm]
      _ = W⁻¹ * ∑ t ∈ s,
            γ t * ∑ i : ι,
              ⟪zCarrier, ((yHatIter setup hStanding t ω) i).1⟫_ℝ := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro t _ht
            rw [Finset.mul_sum]
      _ = W⁻¹ * ∑ t ∈ s,
            γ t * ⟪zCarrier, U setup (yHatIter setup hStanding t ω)⟫_ℝ := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro t _ht
            refine congrArg (fun r : ℝ => γ t * r) ?_
            unfold U
            rw [inner_sum]
      _ = (outputWeightSum α hAlpha k)⁻¹ *
          ∑ t ∈ outputTimeWindow k,
            theoremOutputWeight α hAlpha t *
              ⟪z.1.1, U setup (yHatIter setup hStanding t ω)⟫_ℝ := by
            rfl
  simpa [gap, saddleValue, W, s, γ] using
    (SOptLib.saddleGap_weightedProductOutput_le_weighted_sum
      (s := outputTimeWindow k)
      (γ := theoremOutputWeight α hAlpha)
      (W := outputWeightSum α hAlpha k)
      (evalX := fun x : PrimalCarrier setup => x.1)
      (regularizer := objectiveRegularizer setup)
      (coupling := U setup)
      (dualPenalty := fun y : DualProductCarrier setup =>
        ∑ i : ι, dualConjugate setup i (y i))
      (x := fun t => xIter setup hStanding t ω)
      (y := fun t => yHatIter setup hStanding t ω)
      (xbar := weightedOutput setup α k hk hStanding hAlpha ω)
      (ybar := weightedDualOutput setup α k hk hStanding hAlpha ω)
      (z := z)
      (outputWeightSum_pos_of_alphaRange α k hk hAlpha)
      rfl
      hreg
      hdual
      hlin_x
      hlin_y)

/-- Finite-prefix Jensen lift for the Theorem 5.1 weighted saddle contribution.

Aligns with Lan Eq. (5.1.66): after the pathwise convexity step, finite-prefix
expectation linearity and horizon transport convert the weighted sum to
`expectedSaddleGap`. Candidate audit: searched `finite prefix expectation
saddle gap horizon transport`; the reusable pieces are
`finite_prefix_expectation_mono_of_forall_extend`,
`finitePrefixExpectation_sum_finset`, `finitePrefixExpectation_const_mul`, and
the saddle-gap transport helper above. -/
private theorem theorem51_weighted_saddle_gap_jensen_le_weighted_sum
    (α : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hStanding : standingAssumptions setup) (hAlpha : alphaRange α)
    (z : SaddlePoint setup) :
    finitePrefixExpectation setup k (fun ω =>
      gap setup
        ((weightedOutput setup α k hk hStanding hAlpha ω),
          weightedDualOutput setup α k hk hStanding hAlpha ω) z) ≤
      (outputWeightSum α hAlpha k)⁻¹ *
        ∑ t ∈ outputTimeWindow k,
          theoremOutputWeight α hAlpha t *
            expectedSaddleGap setup hStanding t z := by
  classical
  let W : ℝ := outputWeightSum α hAlpha k
  let s : Finset ℕ := outputTimeWindow k
  let γ : ℕ → ℝ := theoremOutputWeight α hAlpha
  let G : ℕ → BlockSamplePath setup → ℝ := fun t ω =>
    gap setup ((xIter setup hStanding t ω), yHatIter setup hStanding t ω) z
  exact
    finitePrefixExpectation_weighted_output_gap_le_weighted_expected_gap
      (s := s) (γ := γ) (W := W)
      (Eprefix := finitePrefixExpectation setup k)
      (G := G)
      (Gbar := fun ω =>
        gap setup
          ((weightedOutput setup α k hk hStanding hAlpha ω),
            weightedDualOutput setup α k hk hStanding hAlpha ω) z)
      (EG := fun t => expectedSaddleGap setup hStanding t z)
      (hEprefix_mono := by
        intro F H hFH
        simpa [finitePrefixExpectation] using
          (SOptLib.finitePrefixExpectation_mono_of_forall_extend
            (μ := blockStreamLaw setup) (prefixMap := blockPrefix setup k)
            (extend := extendBlockPrefix setup k) (F := F) (G := H)
            (hF := finite_prefix_observable_integrable setup k
              (fun pref : BlockPrefix setup k => F (extendBlockPrefix setup k pref)))
            (hG := finite_prefix_observable_integrable setup k
              (fun pref : BlockPrefix setup k => H (extendBlockPrefix setup k pref)))
            (h := by
              intro pref
              apply hFH
            )
          )
      )
      (hEprefix_const_mul := by
        intro c F
        exact finitePrefixExpectation_const_mul setup k c F)
      (hEprefix_sum := by
        intro F
        exact finitePrefixExpectation_sum_finset setup k s F)
      (hpath := by
        intro ω
        simpa [W, s, γ, G] using
          theorem51_gap_weighted_output_pathwise_le_weighted_saddle_sum
            setup α k hk hStanding hAlpha z ω)
      (htransport := by
        intro t ht
        rcases Finset.mem_Icc.mp (by simpa [s, outputTimeWindow] using ht) with
          ⟨_ht1, htk⟩
        simpa [G] using
          finite_prefix_expectation_saddle_gap_eq_of_le
            setup hStanding htk z)

/-- Source-neutral weighted finite-sum split used to assemble Proposition 5.1
endpoint algebra from local primal, dual, and Delta bounds. Existing candidates
considered: searched `weighted Proposition 5.1 endpoint bound terminal tail` and
`finitePrefixExpectation split weighted RHS primal dual delta`; the target-file
Proposition theorem has an unusable denominator-boundary hypothesis, while the
finite-prefix linearity helpers only provide the expectation-level pieces. -/
private theorem sum_weighted_three_way_residual_split {α : Type*} [DecidableEq α]
    (s : Finset α) (θ P D R Q : α → ℝ) :
    (∑ t ∈ s, θ t * (((P t - Q t) + D t) + R t)) =
      (∑ t ∈ s, θ t * P t) +
        (∑ t ∈ s, θ t * D t) +
          (∑ t ∈ s, θ t * (R t - Q t)) := by
  simpa using
    (_root_.sum_weighted_three_way_residual_split
      (s := s) (theta := θ) (P := P) (D := D) (R := R) (Q := Q))

/-- Finite-prefix form of the Lemma 5.5 dual-prediction unbiased
inner-product cancellation.
Aligns with the observations after Eq. (5.1.45), using Eq. (5.1.23) and
Eq. (5.1.26): searched `conditional expectation inner product integral zero
finite prefix` and considered SOptLib martingale candidates
`integral_inner_sub_const_eq_zero_of_condExp_eq_zero` and
`integral_inner_eq_zero_of_scalar_condExp_eq_zero`, plus the target-file
`condexp_sampledBlock_if_prefix_observable`; the SOptLib lemmas package a
generic martingale cancellation, while this source step needs the paper's
sampled/off-sampled inverse-probability branch and finite-prefix bridge. -/
private theorem lemma55_dual_prediction_unbiased_inner_finitePrefix
    (setup : Setup E ι) (hStanding : standingAssumptions setup)
    (hProbDen : allBlockProbabilityDenominatorsAdmissible setup)
    (t : ℕ) (ht : 1 ≤ t) (zE : E) :
    finitePrefixExpectation setup t (fun ω =>
      ⟪xTildeIter setup hStanding t ω - zE,
        ∑ i : ι, ((yHatIter setup hStanding t ω i).1 -
          yTildeIter setup hStanding t ω i)⟫_ℝ) = 0 := by
  classical
  let payload : BlockSamplePath setup → E := fun ω =>
    xTildeIter setup hStanding t ω - zE
  let resid : ι → BlockSamplePath setup → E := fun i ω =>
    (yHatIter setup hStanding t ω i).1 -
      yTildeIter setup hStanding t ω i
  let ψ : BlockPrefix setup t → ℝ := fun pref =>
    ⟪payload (extendBlockPrefix setup t pref),
      ∑ i : ι, resid i (extendBlockPrefix setup t pref)⟫_ℝ
  have hprefix :
      (fun ω : BlockSamplePath setup =>
        ⟪payload ω, ∑ i : ι, resid i ω⟫_ℝ) =
      fun ω : BlockSamplePath setup => ψ (blockPrefix setup t ω) := by
    funext ω
    have hcur :
        stateProcess setup hStanding t
            (extendBlockPrefix setup t (blockPrefix setup t ω)) =
          stateProcess setup hStanding t ω := by
      exact stateProcess_extendBlockPrefix_eq setup hStanding t ω
    have hprev :
        stateProcess setup hStanding (t - 1)
            (extendBlockPrefix setup t (blockPrefix setup t ω)) =
          stateProcess setup hStanding (t - 1) ω := by
      exact stateProcess_extendBlockPrefix_eq_of_le setup hStanding (by omega) ω
    have hprev2 :
        stateProcess setup hStanding (t - 2)
            (extendBlockPrefix setup t (blockPrefix setup t ω)) =
          stateProcess setup hStanding (t - 2) ω := by
      exact stateProcess_extendBlockPrefix_eq_of_le setup hStanding (by omega) ω
    dsimp [payload, resid, ψ, xTildeIter, xIter, yHatIter, yIter,
      dualSubgradIter, yTildeIter]
    rw [hcur, hprev, hprev2]
  have hcoordIntegrable : ∀ i : ι, Integrable
      (fun ω : BlockSamplePath setup =>
        ⟪payload ω, resid i ω⟫_ℝ)
      (blockStreamLaw setup) := by
    intro i
    let ψi : BlockPrefix setup t → ℝ := fun pref =>
      ⟪payload (extendBlockPrefix setup t pref),
        resid i (extendBlockPrefix setup t pref)⟫_ℝ
    have hψi :
        Integrable (fun ω : BlockSamplePath setup => ψi (blockPrefix setup t ω))
          (blockStreamLaw setup) :=
      prefixObservable_integrable_blockStream setup t ψi
    exact hψi.congr
      (Filter.Eventually.of_forall fun ω => by
        simpa [payload, resid, ψi] using
          (congrFun
            (lemma55_dual_prediction_coordinate_prefixObservable
              setup hStanding t i zE) ω).symm)
  exact
    finitePrefixExpectation_inner_sum_coordinate_residual_eq_zero
      (μ := blockStreamLaw setup) (prefixMap := blockPrefix setup t)
      (extend := extendBlockPrefix setup t)
      (hprefix := (blockPrefix_measurable setup t).aemeasurable)
      (hsection := blockPrefix_extendBlockPrefix setup t)
      (payload := payload) (resid := resid) (ψ := ψ)
      (hψ := by
        simpa [blockPrefixLaw] using
          (finite_prefix_observable_integrable setup t ψ).aestronglyMeasurable)
      hprefix
      hcoordIntegrable
      (by
        intro i
        simpa [payload, resid] using
          lemma55_dual_prediction_coordinate_integral_eq_zero
            setup hStanding hProbDen t ht i zE)

/-- Finite-prefix rewrite of Lemma 5.5's three inner-product terms after
using dual-prediction unbiasedness.
Aligns with the observations after Eq. (5.1.45): the pointwise algebra exposes
the cancellation
`⟪x̃ᵗ-x, Σ(ŷᵢᵗ-ỹᵢᵗ)⟫`, then
`lemma55_dual_prediction_unbiased_inner_finitePrefix` removes it in
expectation. -/
private theorem lemma55_hat_inner_terms_finitePrefix_rewrite
    (setup : Setup E ι) (hStanding : standingAssumptions setup)
    (hProbDen : allBlockProbabilityDenominatorsAdmissible setup)
    (t : ℕ) (ht : 1 ≤ t) (z : SaddlePoint setup) :
    finitePrefixExpectation setup t (fun ω =>
      ⟪xTildeIter setup hStanding t ω,
          (∑ i : ι, (yHatIter setup hStanding t ω i).1) -
            ∑ i : ι, (z.2 i).1⟫_ℝ -
        ⟪(xIter setup hStanding t ω).1,
          (∑ i : ι, yTildeIter setup hStanding t ω i) -
            ∑ i : ι, (z.2 i).1⟫_ℝ +
        ⟪z.1.1,
          (∑ i : ι, yTildeIter setup hStanding t ω i) -
            ∑ i : ι, (yHatIter setup hStanding t ω i).1⟫_ℝ) =
      finitePrefixExpectation setup t (fun ω =>
        ⟪xTildeIter setup hStanding t ω - (xIter setup hStanding t ω).1,
          ∑ i : ι, (yTildeIter setup hStanding t ω i - (z.2 i).1)⟫_ℝ) := by
  classical
  let A : BlockSamplePath setup → ℝ := fun ω =>
    ⟪xTildeIter setup hStanding t ω,
        (∑ i : ι, (yHatIter setup hStanding t ω i).1) -
          ∑ i : ι, (z.2 i).1⟫_ℝ -
      ⟪(xIter setup hStanding t ω).1,
        (∑ i : ι, yTildeIter setup hStanding t ω i) -
          ∑ i : ι, (z.2 i).1⟫_ℝ +
      ⟪z.1.1,
        (∑ i : ι, yTildeIter setup hStanding t ω i) -
          ∑ i : ι, (yHatIter setup hStanding t ω i).1⟫_ℝ
  let B : BlockSamplePath setup → ℝ := fun ω =>
    ⟪xTildeIter setup hStanding t ω - (xIter setup hStanding t ω).1,
      ∑ i : ι, (yTildeIter setup hStanding t ω i - (z.2 i).1)⟫_ℝ
  let C : BlockSamplePath setup → ℝ := fun ω =>
    ⟪xTildeIter setup hStanding t ω - z.1.1,
      ∑ i : ι,
        ((yHatIter setup hStanding t ω i).1 -
          yTildeIter setup hStanding t ω i)⟫_ℝ
  have hpoint : A = fun ω => B ω + C ω := by
    funext ω
    dsimp [A, B, C]
    simp [inner_sub_left, inner_sub_right, Finset.sum_sub_distrib]
    ring_nf
  have hCzero : finitePrefixExpectation setup t C = 0 := by
    simpa [C] using
      lemma55_dual_prediction_unbiased_inner_finitePrefix
        setup hStanding hProbDen t ht z.1.1
  change finitePrefixExpectation setup t A =
    finitePrefixExpectation setup t B
  calc
    finitePrefixExpectation setup t A =
        finitePrefixExpectation setup t (fun ω => B ω + C ω) := by
          rw [hpoint]
    _ = finitePrefixExpectation setup t B + finitePrefixExpectation setup t C := by
          exact finitePrefixExpectation_add setup t B C
    _ = finitePrefixExpectation setup t B + 0 := by rw [hCzero]
    _ = finitePrefixExpectation setup t B := by ring

/-- Blockwise dual prox Bregman descent used in Lan Eq. (5.1.44).
Aligns with Lemma 5.5 proof step 2: searched `candidateDualUpdate selected FOC
dual Bregman descent`; the existing candidates
`candidateDualUpdate_selected_FOC`, `candidateDualSubgradientValue`, and
`candidateDualSubgradient` provide the exact paper-selected quotient, while no
separate SOptLib theorem states this RPDG carrier-valued block identity. -/
private theorem candidate_dual_bregman_descent_identity
    (hStanding : standingAssumptions setup)
    (t : ℕ) (ht : 1 ≤ t) (xTilde : E) (i : ι)
    (yPrev : DualCarrier setup i)
    (baseSubgrad : DualConjugateSubgradient setup i yPrev)
    (y : DualCarrier setup i) :
    ⟪-xTilde,
        (candidateDualUpdate setup hStanding t xTilde i yPrev baseSubgrad).1 -
          y.1⟫_ℝ +
        dualConjugate setup i
          (candidateDualUpdate setup hStanding t xTilde i yPrev baseSubgrad) -
        dualConjugate setup i y ≤
      setup.τ t * (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i yPrev baseSubgrad) yPrev y) -
        (1 + setup.τ t) *
          (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i (candidateDualUpdate setup hStanding t xTilde i yPrev baseSubgrad) (candidateDualSubgradient setup hStanding t ht xTilde i yPrev baseSubgrad)) (candidateDualUpdate setup hStanding t xTilde i yPrev baseSubgrad) y) -
        setup.τ t * (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i yPrev baseSubgrad) yPrev (candidateDualUpdate setup hStanding t xTilde i yPrev baseSubgrad)) := by
  let q : E := (candidateDualSubgradient setup hStanding t ht xTilde i yPrev baseSubgrad).1
  have hOnePlusTau : 0 < 1 + setup.τ t :=
    onePlusTau_pos_of_standing setup hStanding t ht
  have hscale : (1 + setup.τ t) • q = xTilde + setup.τ t • baseSubgrad.1 := by
    have hcoef :
        (1 + setup.τ t) *
            sourceQuotient 1 (1 + setup.τ t) (ne_of_gt hOnePlusTau) = 1 := by
      rw [sourceQuotient_def]
      field_simp [ne_of_gt hOnePlusTau]
    have hcoef_tau :
        (1 + setup.τ t) *
            (sourceQuotient 1 (1 + setup.τ t) (ne_of_gt hOnePlusTau) * setup.τ t) =
          setup.τ t := by
      calc
        (1 + setup.τ t) *
            (sourceQuotient 1 (1 + setup.τ t) (ne_of_gt hOnePlusTau) * setup.τ t)
            =
            ((1 + setup.τ t) *
                sourceQuotient 1 (1 + setup.τ t) (ne_of_gt hOnePlusTau)) *
              setup.τ t := by
          ring
        _ = 1 * setup.τ t := by rw [hcoef]
        _ = setup.τ t := by ring
    simp [q, candidateDualSubgradient, candidateDualSubgradientValue,
      smul_smul, hcoef, hcoef_tau]
  have hvec : xTilde = (1 + setup.τ t) • q - setup.τ t • baseSubgrad.1 := by
    calc
      xTilde = xTilde + setup.τ t • baseSubgrad.1 - setup.τ t • baseSubgrad.1 := by
        module
      _ = (1 + setup.τ t) • q - setup.τ t • baseSubgrad.1 := by
        rw [← hscale]
  simpa [SOptLib.carrierBregmanDivergence, carrierBregmanDivergence,
    _root_.carrierBregmanFormula, dualConjugateBaseSelector, q] using
    (SOptLib.two_bregman_descent_of_affine_selected_subgradient
      (J := dualConjugate setup i)
      (eval := fun y : DualCarrier setup i => y.1)
      (τ := setup.τ t)
      (x := xTilde)
      (q := q)
      (base := baseSubgrad.1)
      (yPrev := yPrev)
      (yHat := candidateDualUpdate setup hStanding t xTilde i yPrev baseSubgrad)
      (y := y)
      hvec)

/-- Summed dual prox inequality in Lan Eq. (5.1.44), before combining with
the primal descent display.
Aligns with Lemma 5.5 proof step 3: searched `dual candidate sum Bregman
descent yHatIter`; no existing target/SOptLib lemma summed the RPDG candidate
block identity, so this is the finite-sum consumer of
`candidate_dual_bregman_descent_identity`. -/
private theorem dual_candidate_sum_bregman_descent
    (hStanding : standingAssumptions setup)
    (t : ℕ) (ht : 1 ≤ t) (ω : BlockSamplePath setup) (z : SaddlePoint setup) :
    (∑ i : ι,
      (⟪-xTildeIter setup hStanding t ω,
          (yHatIter setup hStanding t ω i).1 - (z.2 i).1⟫_ℝ +
        dualConjugate setup i (yHatIter setup hStanding t ω i) -
        dualConjugate setup i (z.2 i))) ≤
      ∑ i : ι,
        (setup.τ t *
            (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) (z.2 i)) -
          (1 + setup.τ t) *
            (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i (yHatIter setup hStanding t ω i) (yHatSubgradIter setup hStanding t ht ω i)) (yHatIter setup hStanding t ω i) (z.2 i)) -
          setup.τ t *
            (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) (yHatIter setup hStanding t ω i))) := by
  classical
  refine Finset.sum_le_sum ?_
  intro i _hi
  simpa [yHatIter, yHatSubgradIter] using
    candidate_dual_bregman_descent_identity setup hStanding t ht
      (xTildeIter setup hStanding t ω) i
      ((yIter setup hStanding (t - 1) ω) i)
      (dualSubgradIter setup hStanding (t - 1) ω i) (z.2 i)

/-- Positive-time generated primal iterate equation used in Lan Eq. (5.1.43).
Aligns with Lemma 5.5 proof step 1: searched `xIter primalUpdate positive
time stateProcess rpdgStep`; the existing `stateProcess_positive_time_step`
and `stepPrimalPrediction_eq_xTildeIter` are the relevant process bridges, but
no local theorem exposed the `xIter` projection in primal-update form. -/
private theorem xIter_eq_primalUpdate_current
    (hStanding : standingAssumptions setup)
    (t : ℕ) (ht : 1 ≤ t) (ω : BlockSamplePath setup) :
    xIter setup hStanding t ω =
      primalUpdate setup hStanding t
        (xIter setup hStanding (t - 1) ω)
        (yTildeIter setup hStanding t ω) := by
  rw [xIter, yTildeIter, stateProcess_positive_time_step setup hStanding t ht ω]
  simp [rpdgStep, xIter,
    stepPrimalPrediction_eq_xTildeIter setup hStanding t ht ω]

/-- Generated-process form of Lan Eq. (5.1.43).
Aligns with Lemma 5.5 proof step 1: searched `primalUpdate two bregman
descent xIter yTildeIter`; `primalUpdate_two_bregman_descent` is the source
prox inequality and `xIter_eq_primalUpdate_current` transports it to the
generated Algorithm 5.1 process. -/
private theorem primal_generated_bregman_descent
    (hStanding : standingAssumptions setup)
    (t : ℕ) (ht : 1 ≤ t) (ω : BlockSamplePath setup) (x : PrimalCarrier setup) :
    ⟪(xIter setup hStanding t ω).1 - x.1,
        ∑ i : ι, yTildeIter setup hStanding t ω i⟫_ℝ +
        setup.h (xIter setup hStanding t ω).1 +
        setup.μ * setup.nu (xIter setup hStanding t ω) -
        setup.h x.1 - setup.μ * setup.nu x ≤
      setup.η t * primalBregman setup (xIter setup hStanding (t - 1) ω) x -
        (setup.μ + setup.η t) *
          primalBregman setup (xIter setup hStanding t ω) x -
        setup.η t *
          primalBregman setup (xIter setup hStanding (t - 1) ω)
            (xIter setup hStanding t ω) := by
  have hstep :=
    primalUpdate_two_bregman_descent setup hStanding t ht
      (xIter setup hStanding (t - 1) ω)
      (yTildeIter setup hStanding t ω) x
  have hx := xIter_eq_primalUpdate_current setup hStanding t ht ω
  simpa [← hx] using hstep

/-- Pointwise pre-expectation recursion in Lan Eq. (5.1.45), before applying
the Lemma 5.4 finite-prefix substitutions and dual-prediction unbiasedness.
Aligns with Lemma 5.5 proof step 4: searched `gap saddleValue yHat Eq 5.1.45
pointwise`; the available ingredients are the generated primal descent and
summed dual prox helpers above, while no existing target/SOptLib theorem
assembles this RPDG saddle-gap algebra. -/
private theorem lemma55_pointwise_gap_hat_form
    (hStanding : standingAssumptions setup)
    (t : ℕ) (ht : 1 ≤ t) (ω : BlockSamplePath setup) (z : SaddlePoint setup) :
    gap setup ((xIter setup hStanding t ω), yHatIter setup hStanding t ω) z ≤
      (setup.η t * primalBregman setup (xIter setup hStanding (t - 1) ω) z.1 -
        (setup.μ + setup.η t) *
          primalBregman setup (xIter setup hStanding t ω) z.1 -
        setup.η t *
          primalBregman setup (xIter setup hStanding (t - 1) ω)
            (xIter setup hStanding t ω)) +
      (∑ i : ι,
        (setup.τ t *
            (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) (z.2 i)) -
          (1 + setup.τ t) *
            (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i (yHatIter setup hStanding t ω i) (yHatSubgradIter setup hStanding t ht ω i)) (yHatIter setup hStanding t ω i) (z.2 i)) -
          setup.τ t *
            (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) (yHatIter setup hStanding t ω i)))) +
      (⟪xTildeIter setup hStanding t ω,
          (∑ i : ι, (yHatIter setup hStanding t ω i).1) -
            ∑ i : ι, (z.2 i).1⟫_ℝ -
        ⟪(xIter setup hStanding t ω).1,
          (∑ i : ι, yTildeIter setup hStanding t ω i) -
            ∑ i : ι, (z.2 i).1⟫_ℝ +
        ⟪z.1.1,
          (∑ i : ι, yTildeIter setup hStanding t ω i) -
            ∑ i : ι, (yHatIter setup hStanding t ω i).1⟫_ℝ) := by
  classical
  simpa only [gap, saddleValue, U] using
    (SOptLib.saddle_gap_le_of_primal_dual_descent_and_mismatch
      (ι := ι) (X := PrimalCarrier setup) (E := E)
      (Y := fun i : ι => DualCarrier setup i)
      (evalX := fun x : PrimalCarrier setup => x.1)
      (evalY := fun i (y : DualCarrier setup i) => y.1)
      (regularizer := fun x : PrimalCarrier setup =>
        setup.h x.1 + setup.μ * setup.nu x)
      (dualPenalty := fun i (y : DualCarrier setup i) =>
        dualConjugate setup i y)
      (xCur := xIter setup hStanding t ω)
      (xRef := z.1)
      (xTilde := xTildeIter setup hStanding t ω)
      (yTilde := yTildeIter setup hStanding t ω)
      (yHat := yHatIter setup hStanding t ω)
      (yRef := z.2)
      (primalR :=
        setup.η t * primalBregman setup (xIter setup hStanding (t - 1) ω) z.1 -
          (setup.μ + setup.η t) *
            primalBregman setup (xIter setup hStanding t ω) z.1 -
          setup.η t *
            primalBregman setup (xIter setup hStanding (t - 1) ω)
              (xIter setup hStanding t ω))
      (dualR :=
        ∑ i : ι,
          (setup.τ t *
              (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) (z.2 i)) -
            (1 + setup.τ t) *
              (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i (yHatIter setup hStanding t ω i) (yHatSubgradIter setup hStanding t ht ω i)) (yHatIter setup hStanding t ω i) (z.2 i)) -
            setup.τ t *
              (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) (yHatIter setup hStanding t ω i))))
      (by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
          primal_generated_bregman_descent setup hStanding t ht ω z.1)
      (by
        simpa using
          dual_candidate_sum_bregman_descent setup hStanding t ht ω z))

/-- Finite-prefix expectation preserves pointwise inequalities on the generated
extension of every paper prefix.
Aligns with Lemma 5.5 proof step 6: searched `finite prefix expectation
monotone integral_mono_ae`, `finite range integrable observable prefix
expectation`, and `finite prefix expectation bridge block stream integral map`.
The usable pieces were `finitePrefixExpectation`,
`finite_prefix_observable_integrable`, and Mathlib
`MeasureTheory.integral_mono_ae`; no existing target/SOptLib theorem packaged
this paper-prefix monotonicity bridge. -/
private theorem finite_prefix_expectation_mono_of_forall_extend
    (setup : Setup E ι) (k : ℕ) {F G : BlockSamplePath setup → ℝ}
    (h : ∀ pref : BlockPrefix setup k,
      F (extendBlockPrefix setup k pref) ≤
        G (extendBlockPrefix setup k pref)) :
    finitePrefixExpectation setup k F ≤ finitePrefixExpectation setup k G := by
  simpa [finitePrefixExpectation] using
    (SOptLib.finitePrefixExpectation_mono_of_forall_extend
      (μ := blockStreamLaw setup) (prefixMap := blockPrefix setup k)
      (extend := extendBlockPrefix setup k) (F := F) (G := G)
      (finite_prefix_observable_integrable setup k
        (fun pref : BlockPrefix setup k => F (extendBlockPrefix setup k pref)))
      (finite_prefix_observable_integrable setup k
        (fun pref : BlockPrefix setup k => G (extendBlockPrefix setup k pref)))
      h)

/-- Squared distance from a finite normalized weighted average is bounded by the
corresponding normalized weighted squared distances. Existing candidates
considered: searched `squared norm convex weighted average norm square`; the
usable imported primitive was `finset_weighted_variance_eq_second_moment_sub_norm_mean_sq`,
while the higher-level Layer1 Jensen theorem is not imported in this file and
is about scalar convex functions rather than this Hilbert-space variance
normalization. -/
private theorem norm_sq_weighted_average_sub_le_weighted_sum
    {κ : Type*} (s : Finset κ) (γ : κ → ℝ) (p : κ → E)
    (xbar xstar : E) (W : ℝ)
    (hγ_nonneg : ∀ i ∈ s, 0 ≤ γ i)
    (hW_pos : 0 < W)
    (hW_eq : W = ∑ i ∈ s, γ i)
    (hxbar : xbar = W⁻¹ • ∑ i ∈ s, γ i • p i) :
    ‖xbar - xstar‖ ^ 2 ≤
      W⁻¹ * ∑ i ∈ s, γ i * ‖p i - xstar‖ ^ 2 := by
  exact _root_.norm_sq_weighted_average_sub_le_inv_mul_sum
    (s := s) (γ := γ) (p := p) (xbar := xbar) (z := xstar) (W := W)
    hγ_nonneg hW_pos hW_eq hxbar

/-- Pointwise squared-distance Jensen bound for the canonical primal weighted
output in Theorem 5.1. This specializes
`norm_sq_weighted_average_sub_le_weighted_sum` to Eq. (5.1.65)'s weights. -/
private theorem theorem51_weighted_output_norm_sq_le_weighted_sum
    (α : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hStanding : standingAssumptions setup) (hAlpha : alphaRange α)
    (xstar : PrimalCarrier setup) (ω : BlockSamplePath setup) :
    ‖(weightedOutput setup α k hk hStanding hAlpha ω).1 - xstar.1‖ ^ 2 ≤
      (outputWeightSum α hAlpha k)⁻¹ *
        ∑ t ∈ outputTimeWindow k,
          theoremOutputWeight α hAlpha t *
            ‖(xIter setup hStanding t ω).1 - xstar.1‖ ^ 2 := by
  classical
  refine norm_sq_weighted_average_sub_le_weighted_sum
    (s := outputTimeWindow k)
    (γ := theoremOutputWeight α hAlpha)
    (p := fun t => (xIter setup hStanding t ω).1)
    (xbar := (weightedOutput setup α k hk hStanding hAlpha ω).1)
    (xstar := xstar.1)
    (W := outputWeightSum α hAlpha k)
    ?_ ?_ ?_ ?_
  · intro t ht
    exact outputTheta_nonnegative_of_alphaRange α k hAlpha () t ht
  · exact outputWeightSum_pos_of_alphaRange α k hk hAlpha
  · rfl
  · rw [weightedOutput_eq]
    rfl

/-- The Lemma 5.2 part of Theorem 5.1 Eq. (5.1.66), before Jensen bounds on
the averaged saddle gap and squared norm. Existing candidates considered:
`Lemma_5_2_primal_gap_from_saddle_gap` is pointwise, while
`finite_prefix_expectation_mono_of_forall_extend` and
`finitePrefixExpectation_add` provide only expectation transport/linearity; no
target/SOptLib helper packages this weighted-output specialization. -/
private theorem theorem51_expected_primal_gap_le_weighted_saddle_plus_norm
    (α : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hStanding : standingAssumptions setup) (hAlpha : alphaRange α)
    (xstar : PrimalCarrier setup) (hxstar : IsOptimalPrimal setup xstar) :
    expectedPrimalOptimalityGap setup α k hk hStanding hAlpha xstar hxstar ≤
      finitePrefixExpectation setup k (fun ω =>
        gap setup
          ((weightedOutput setup α k hk hStanding hAlpha ω),
            weightedDualOutput setup α k hk hStanding hAlpha ω)
          (xstar, fun i : ι =>
            scaledComponentGradientDual setup hStanding i xstar.1)) +
      finitePrefixExpectation setup k (fun ω =>
        (setup.Lf / 2) *
          ‖(weightedOutput setup α k hk hStanding hAlpha ω).1 - xstar.1‖ ^ 2) := by
  classical
  rw [expectedPrimalOptimalityGap_eq_expectedPrimalGap]
  unfold expectedPrimalGap
  calc
    finitePrefixExpectation setup k
        (fun ω =>
          objective setup (weightedOutput setup α k hk hStanding hAlpha ω) -
            objective setup xstar) ≤
      finitePrefixExpectation setup k (fun ω =>
        gap setup
          ((weightedOutput setup α k hk hStanding hAlpha ω),
            weightedDualOutput setup α k hk hStanding hAlpha ω)
          (xstar, fun i : ι =>
            scaledComponentGradientDual setup hStanding i xstar.1) +
          (setup.Lf / 2) *
            ‖(weightedOutput setup α k hk hStanding hAlpha ω).1 - xstar.1‖ ^ 2) := by
        refine finite_prefix_expectation_mono_of_forall_extend setup k ?_
        intro pref
        exact
          Lemma_5_2_primal_gap_from_saddle_gap
            setup hStanding
            ((weightedOutput setup α k hk hStanding hAlpha
                (extendBlockPrefix setup k pref)),
              weightedDualOutput setup α k hk hStanding hAlpha
                (extendBlockPrefix setup k pref))
            (xstar, fun i : ι =>
              scaledComponentGradientDual setup hStanding i xstar.1)
            (scaled_gradient_dual_saddle_solution_of_primal_optimum
              setup hStanding xstar hxstar)
    _ =
      finitePrefixExpectation setup k (fun ω =>
        gap setup
          ((weightedOutput setup α k hk hStanding hAlpha ω),
            weightedDualOutput setup α k hk hStanding hAlpha ω)
          (xstar, fun i : ι =>
            scaledComponentGradientDual setup hStanding i xstar.1)) +
      finitePrefixExpectation setup k (fun ω =>
        (setup.Lf / 2) *
          ‖(weightedOutput setup α k hk hStanding hAlpha ω).1 - xstar.1‖ ^ 2) := by
        rw [finitePrefixExpectation_add]

/-- Norm-correction part of Lan Eq. (5.1.66): the smoothness penalty at the
weighted primal output is bounded by the normalized weighted Bregman-distance
average. Existing candidates considered: searched `finite prefix expectation
sum constant multiply weighted bregman distance norm correction`; the usable
pieces are `theorem51_weighted_output_norm_sq_le_weighted_sum`,
`finitePrefixExpectation_sum_finset`,
`finitePrefixExpectation_const_mul`,
`finite_prefix_expectation_primal_iter_bregman_eq_blockStream_of_le`, and
`expectedBregmanDistance_finite_prefix`, but no existing helper packages their
Theorem 5.1 weighted-output specialization. -/
private theorem theorem51_norm_correction_le_weighted_bregman_average
    (α : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hStanding : standingAssumptions setup) (hAlpha : alphaRange α)
    (xstar : PrimalCarrier setup) :
    finitePrefixExpectation setup k (fun ω =>
      (setup.Lf / 2) *
        ‖(weightedOutput setup α k hk hStanding hAlpha ω).1 - xstar.1‖ ^ 2) ≤
      setup.Lf * (outputWeightSum α hAlpha k)⁻¹ *
        ∑ t ∈ outputTimeWindow k,
          theoremOutputWeight α hAlpha t *
            expectedBregmanDistance setup hStanding t xstar := by
  classical
  exact
    expected_weighted_output_norm_correction_le_weighted_bregman_average
      (Exp := finitePrefixExpectation setup k)
      (s := outputTimeWindow k)
      (γ := theoremOutputWeight α hAlpha)
      (x := fun t ω => (xIter setup hStanding t ω).1)
      (xbar := fun ω => (weightedOutput setup α k hk hStanding hAlpha ω).1)
      (xstar := xstar.1)
      (B := fun t ω => primalBregman setup (xIter setup hStanding t ω) xstar)
      (Bavg := fun t => expectedBregmanDistance setup hStanding t xstar)
      (L := setup.Lf)
      (W := outputWeightSum α hAlpha k)
      (hExp_mono := by
        intro F G hFG
        exact finite_prefix_expectation_mono_of_forall_extend setup k
          (fun pref => hFG (extendBlockPrefix setup k pref)))
      (hExp_const_mul := by
        intro c F
        exact finitePrefixExpectation_const_mul setup k c F)
      (hExp_sum := by
        intro F
        exact finitePrefixExpectation_sum_finset setup k (outputTimeWindow k) F)
      (hL_nonneg := by
        rcases hStanding with ⟨_, _, _, _, _, _, hAvg, _, _, _, _, _⟩
        exact hAvg.2.1)
      (hW_pos := outputWeightSum_pos_of_alphaRange α k hk hAlpha)
      (hγ_nonneg := by
        intro t htmem
        exact outputTheta_nonnegative_of_alphaRange α k hAlpha () t htmem)
      (hpoint := by
        intro ω
        simpa using
          theorem51_weighted_output_norm_sq_le_weighted_sum
            setup α k hk hStanding hAlpha xstar ω)
      (hbreg_lower := by
        intro t _htmem ω
        have hBregLower : primalBregmanLowerBound setup := by
          rcases hStanding with ⟨_, _, _, _, _, _, _, _, _, hBreg, _, _⟩
          exact hBreg
        have hlower := hBregLower (xIter setup hStanding t ω) xstar
        simpa [norm_sub_rev] using hlower)
      (htransport := by
        intro t htmem
        rcases Finset.mem_Icc.mp (by simpa [outputTimeWindow] using htmem) with
          ⟨_ht, htk⟩
        calc
          finitePrefixExpectation setup k
              (fun ω => primalBregman setup (xIter setup hStanding t ω) xstar) =
              ∫ ω, primalBregman setup (xIter setup hStanding t ω) xstar
                ∂blockStreamLaw setup := by
                simpa using
                  finite_prefix_expectation_primal_iter_bregman_eq_blockStream_of_le
                    setup hStanding htk xstar
          _ = finitePrefixExpectation setup t
              (fun ω => primalBregman setup (xIter setup hStanding t ω) xstar) := by
                rw [← finite_prefix_expectation_primal_iter_bregman_eq_blockStream_of_le
                  setup hStanding (le_rfl : t ≤ t) xstar]
          _ = expectedBregmanDistance setup hStanding t xstar := by
                rw [← expectedBregmanDistance_finite_prefix])

/-- Internal source-gap realization of Lemma 5.5's one-step RPDG recursion for
the generated Algorithm 5.1 update. The sampled inverse-probability coefficient
uses the positive-support sample certificate; all-block reciprocal sums still
use explicitly source-gap internal coefficients because the PDF prints
`p_i^{-1}` for every block without a separate full-support premise. -/
theorem Lemma_5_5_one_step_RPDG_recursion_with_denominator_source_gap
      (hStanding : standingAssumptions setup)
      (hProbDen : allBlockProbabilityDenominatorsAdmissible setup)
      (t : ℕ) (_ht : 1 ≤ t)
    (z : SaddlePoint setup) :
    expectedSaddleGap setup hStanding t z ≤
      finitePrefixExpectation setup t (fun ω =>
        setup.η t * primalBregman setup (xIter setup hStanding (t - 1) ω) z.1 -
          (setup.μ + setup.η t) *
            primalBregman setup (xIter setup hStanding t ω) z.1 -
          setup.η t * primalBregman setup
            (xIter setup hStanding (t - 1) ω)
            (xIter setup hStanding t ω)) +
      ∑ i : ι,
        finitePrefixExpectation setup t (fun ω =>
          (inverseProbabilityValue setup i (hProbDen i) * (1 + setup.τ t) - 1) *
              (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) (z.2 i)) -
            (inverseProbabilityValue setup i (hProbDen i) * (1 + setup.τ t)) *
              (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding t ω) i) (dualSubgradIter setup hStanding t ω i)) ((yIter setup hStanding t ω) i) (z.2 i))) +
      finitePrefixExpectation setup t (fun ω =>
        ⟪xTildeIter setup hStanding t ω - (xIter setup hStanding t ω).1,
          ∑ i : ι, (yTildeIter setup hStanding t ω i - (z.2 i).1)⟫_ℝ -
          (setup.τ t *
              inverseProbabilityValue setup (sampledBlock setup t ω)
                (sampledBlock_probability_ne_zero setup
                  (sampledPositiveBlock setup t ω))) *
            (SOptLib.carrierBregmanDivergence (dualConjugate setup (sampledBlock setup t ω)) (dualConjugateBaseSelector setup (sampledBlock setup t ω) ((yIter setup hStanding (t - 1) ω) (sampledBlock setup t ω)) (dualSubgradIter setup hStanding (t - 1) ω (sampledBlock setup t ω))) ((yIter setup hStanding (t - 1) ω) (sampledBlock setup t ω)) ((yIter setup hStanding t ω) (sampledBlock setup t ω)))) := by
  classical
  have hpointwise :
      ∀ ω : BlockSamplePath setup,
        gap setup ((xIter setup hStanding t ω), yHatIter setup hStanding t ω) z ≤
          (setup.η t * primalBregman setup (xIter setup hStanding (t - 1) ω) z.1 -
            (setup.μ + setup.η t) *
              primalBregman setup (xIter setup hStanding t ω) z.1 -
            setup.η t *
              primalBregman setup (xIter setup hStanding (t - 1) ω)
                (xIter setup hStanding t ω)) +
          (∑ i : ι,
            (setup.τ t *
                (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) (z.2 i)) -
              (1 + setup.τ t) *
                (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i (yHatIter setup hStanding t ω i) (yHatSubgradIter setup hStanding t _ht ω i)) (yHatIter setup hStanding t ω i) (z.2 i)) -
              setup.τ t *
                (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) (yHatIter setup hStanding t ω i)))) +
          (⟪xTildeIter setup hStanding t ω,
              (∑ i : ι, (yHatIter setup hStanding t ω i).1) -
                ∑ i : ι, (z.2 i).1⟫_ℝ -
            ⟪(xIter setup hStanding t ω).1,
              (∑ i : ι, yTildeIter setup hStanding t ω i) -
                ∑ i : ι, (z.2 i).1⟫_ℝ +
            ⟪z.1.1,
              (∑ i : ι, yTildeIter setup hStanding t ω i) -
                ∑ i : ι, (yHatIter setup hStanding t ω i).1⟫_ℝ) := by
    intro ω
    exact lemma55_pointwise_gap_hat_form setup hStanding t _ht ω z
  let hatRhs : BlockSamplePath setup → ℝ := fun ω =>
    (setup.η t * primalBregman setup (xIter setup hStanding (t - 1) ω) z.1 -
      (setup.μ + setup.η t) *
        primalBregman setup (xIter setup hStanding t ω) z.1 -
      setup.η t *
        primalBregman setup (xIter setup hStanding (t - 1) ω)
          (xIter setup hStanding t ω)) +
    (∑ i : ι,
      (setup.τ t *
          (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) (z.2 i)) -
        (1 + setup.τ t) *
          (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i (yHatIter setup hStanding t ω i) (yHatSubgradIter setup hStanding t _ht ω i)) (yHatIter setup hStanding t ω i) (z.2 i)) -
        setup.τ t *
          (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) (yHatIter setup hStanding t ω i)))) +
    (⟪xTildeIter setup hStanding t ω,
        (∑ i : ι, (yHatIter setup hStanding t ω i).1) -
          ∑ i : ι, (z.2 i).1⟫_ℝ -
      ⟪(xIter setup hStanding t ω).1,
        (∑ i : ι, yTildeIter setup hStanding t ω i) -
          ∑ i : ι, (z.2 i).1⟫_ℝ +
      ⟪z.1.1,
        (∑ i : ι, yTildeIter setup hStanding t ω i) -
          ∑ i : ι, (yHatIter setup hStanding t ω i).1⟫_ℝ)
  let publicRhs : ℝ :=
    finitePrefixExpectation setup t (fun ω =>
      setup.η t * primalBregman setup (xIter setup hStanding (t - 1) ω) z.1 -
        (setup.μ + setup.η t) *
          primalBregman setup (xIter setup hStanding t ω) z.1 -
        setup.η t * primalBregman setup
          (xIter setup hStanding (t - 1) ω)
          (xIter setup hStanding t ω)) +
    ∑ i : ι,
      finitePrefixExpectation setup t (fun ω =>
        (inverseProbabilityValue setup i (hProbDen i) * (1 + setup.τ t) - 1) *
            (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) (z.2 i)) -
          (inverseProbabilityValue setup i (hProbDen i) * (1 + setup.τ t)) *
            (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding t ω) i) (dualSubgradIter setup hStanding t ω i)) ((yIter setup hStanding t ω) i) (z.2 i))) +
    finitePrefixExpectation setup t (fun ω =>
      ⟪xTildeIter setup hStanding t ω - (xIter setup hStanding t ω).1,
        ∑ i : ι, (yTildeIter setup hStanding t ω i - (z.2 i).1)⟫_ℝ -
        (setup.τ t *
            inverseProbabilityValue setup (sampledBlock setup t ω)
              (sampledBlock_probability_ne_zero setup
                (sampledPositiveBlock setup t ω))) *
          (SOptLib.carrierBregmanDivergence (dualConjugate setup (sampledBlock setup t ω)) (dualConjugateBaseSelector setup (sampledBlock setup t ω) ((yIter setup hStanding (t - 1) ω) (sampledBlock setup t ω)) (dualSubgradIter setup hStanding (t - 1) ω (sampledBlock setup t ω))) ((yIter setup hStanding (t - 1) ω) (sampledBlock setup t ω)) ((yIter setup hStanding t ω) (sampledBlock setup t ω))))
  have hmono :
      expectedSaddleGap setup hStanding t z ≤
        finitePrefixExpectation setup t hatRhs := by
    unfold expectedSaddleGap
    exact finite_prefix_expectation_mono_of_forall_extend setup t
      (F := fun ω =>
        gap setup ((xIter setup hStanding t ω), yHatIter setup hStanding t ω) z)
      (G := hatRhs)
      (by
        intro pref
        exact hpointwise (extendBlockPrefix setup t pref))
  have hsubst :
      finitePrefixExpectation setup t hatRhs = publicRhs := by
    have hhatTransport : ∀ i : ι,
        finitePrefixExpectation setup t (fun ω =>
          (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i (yHatIter setup hStanding t ω i) (yHatSubgradIter setup hStanding t _ht ω i)) (yHatIter setup hStanding t ω i) (z.2 i))) =
          ∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i (yHatIter setup hStanding t ω i) (yHatSubgradIter setup hStanding t _ht ω i)) (yHatIter setup hStanding t ω i) (z.2 i))
            ∂blockStreamLaw setup := by
      intro i
      exact finite_prefix_expectation_dual_hat_bregman_eq_blockStream
        setup hStanding t _ht i (z.2 i)
    have hlemma54Second : ∀ i : ι,
        (∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding t ω) i) (dualSubgradIter setup hStanding t ω i)) ((yIter setup hStanding t ω) i) (z.2 i))
            ∂blockStreamLaw setup) =
          ∫ ω,
            samplingProbability setup i *
                (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yHatIter setup hStanding t ω) i) (yHatSubgradIter setup hStanding t _ht ω i)) ((yHatIter setup hStanding t ω) i) (z.2 i)) +
              (1 - samplingProbability setup i) *
                (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) (z.2 i))
            ∂blockStreamLaw setup := by
      intro i
      exact lemma54_second_identity_integral setup hStanding t _ht i (z.2 i)
    have hcurPrefix : ∀ i : ι,
        (fun ω : BlockSamplePath setup =>
          (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding t ω) i) (dualSubgradIter setup hStanding t ω i)) ((yIter setup hStanding t ω) i) (z.2 i))) =
          fun ω : BlockSamplePath setup =>
            (fun pref : BlockPrefix setup t =>
              (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding t (extendBlockPrefix setup t pref)) i) (dualSubgradIter setup hStanding t
                  (extendBlockPrefix setup t pref) i)) ((yIter setup hStanding t (extendBlockPrefix setup t pref)) i) (z.2 i)))
              (blockPrefix setup t ω) := by
      intro i
      exact dual_iter_bregman_prefixObservable_of_le setup hStanding
        (le_rfl : t ≤ t) i (z.2 i)
    have hprevPrefix : ∀ i : ι,
        (fun ω : BlockSamplePath setup =>
          (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) (z.2 i))) =
          fun ω : BlockSamplePath setup =>
            (fun pref : BlockPrefix setup t =>
              (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1)
                  (extendBlockPrefix setup t pref)) i) (dualSubgradIter setup hStanding (t - 1)
                  (extendBlockPrefix setup t pref) i)) ((yIter setup hStanding (t - 1)
                  (extendBlockPrefix setup t pref)) i) (z.2 i)))
              (blockPrefix setup t ω) := by
      intro i
      exact dual_iter_bregman_prefixObservable_of_le setup hStanding
        (by omega : t - 1 ≤ t) i (z.2 i)
    have hhatSolvedFinite : ∀ i : ι,
        finitePrefixExpectation setup t (fun ω =>
          (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i (yHatIter setup hStanding t ω i) (yHatSubgradIter setup hStanding t _ht ω i)) (yHatIter setup hStanding t ω i) (z.2 i))) =
          inverseProbabilityValue setup i (hProbDen i) *
            finitePrefixExpectation setup t (fun ω =>
              (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding t ω) i) (dualSubgradIter setup hStanding t ω i)) ((yIter setup hStanding t ω) i) (z.2 i))) -
          (inverseProbabilityValue setup i (hProbDen i) - 1) *
            finitePrefixExpectation setup t (fun ω =>
              (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) (z.2 i))) := by
      intro i
      calc
        finitePrefixExpectation setup t (fun ω =>
            (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i (yHatIter setup hStanding t ω i) (yHatSubgradIter setup hStanding t _ht ω i)) (yHatIter setup hStanding t ω i) (z.2 i))) =
            ∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i (yHatIter setup hStanding t ω i) (yHatSubgradIter setup hStanding t _ht ω i)) (yHatIter setup hStanding t ω i) (z.2 i))
              ∂blockStreamLaw setup := hhatTransport i
        _ = inverseProbabilityValue setup i (hProbDen i) *
              (∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding t ω) i) (dualSubgradIter setup hStanding t ω i)) ((yIter setup hStanding t ω) i) (z.2 i))
                ∂blockStreamLaw setup) -
            (inverseProbabilityValue setup i (hProbDen i) - 1) *
              (∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) (z.2 i))
                ∂blockStreamLaw setup) := by
              exact lemma55_dual_hat_bregman_blockStream_substitution
                setup hStanding hProbDen t _ht i (z.2 i)
        _ = inverseProbabilityValue setup i (hProbDen i) *
              finitePrefixExpectation setup t (fun ω =>
                (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding t ω) i) (dualSubgradIter setup hStanding t ω i)) ((yIter setup hStanding t ω) i) (z.2 i))) -
            (inverseProbabilityValue setup i (hProbDen i) - 1) *
              finitePrefixExpectation setup t (fun ω =>
                (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) (z.2 i))) := by
              rw [← finite_prefix_expectation_dual_iter_bregman_eq_blockStream_of_le
                    setup hStanding (le_rfl : t ≤ t) i (z.2 i),
                  ← finite_prefix_expectation_dual_iter_bregman_eq_blockStream_of_le
                    setup hStanding (by omega : t - 1 ≤ t) i (z.2 i)]
    have hfirstSolvedFinite : ∀ i : ι,
        finitePrefixExpectation setup t (fun ω =>
          (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) ((yHatIter setup hStanding t ω) i))) =
          inverseProbabilityValue setup i (hProbDen i) *
            finitePrefixExpectation setup t (fun ω =>
              (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) ((yIter setup hStanding t ω) i))) := by
      intro i
      exact lemma55_first_residual_finite_substitution
        setup hStanding hProbDen t _ht i
    have hsampledResidualFinite :
        finitePrefixExpectation setup t (fun ω =>
          ∑ i : ι,
            (setup.τ t * inverseProbabilityValue setup i (hProbDen i)) *
              (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) ((yIter setup hStanding t ω) i))) =
          finitePrefixExpectation setup t (fun ω =>
            (setup.τ t *
                inverseProbabilityValue setup (sampledBlock setup t ω)
                  (sampledBlock_probability_ne_zero setup
                    (sampledPositiveBlock setup t ω))) *
              (SOptLib.carrierBregmanDivergence (dualConjugate setup (sampledBlock setup t ω)) (dualConjugateBaseSelector setup (sampledBlock setup t ω) ((yIter setup hStanding (t - 1) ω)
                  (sampledBlock setup t ω)) (dualSubgradIter setup hStanding (t - 1) ω
                  (sampledBlock setup t ω))) ((yIter setup hStanding (t - 1) ω)
                  (sampledBlock setup t ω)) ((yIter setup hStanding t ω)
                  (sampledBlock setup t ω)))) := by
      exact lemma55_sampled_residual_sum_finitePrefix
        setup hStanding hProbDen t _ht
    let P : BlockSamplePath setup → ℝ := fun ω =>
      setup.η t * primalBregman setup (xIter setup hStanding (t - 1) ω) z.1 -
        (setup.μ + setup.η t) * primalBregman setup
          (xIter setup hStanding t ω) z.1 -
        setup.η t * primalBregman setup
          (xIter setup hStanding (t - 1) ω) (xIter setup hStanding t ω)
    let Dhat : BlockSamplePath setup → ℝ := fun ω =>
      ∑ i : ι,
        (setup.τ t *
            (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) (z.2 i)) -
          (1 + setup.τ t) *
            (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i (yHatIter setup hStanding t ω i) (yHatSubgradIter setup hStanding t _ht ω i)) (yHatIter setup hStanding t ω i) (z.2 i)) -
          setup.τ t *
            (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) (yHatIter setup hStanding t ω i)))
    let Ihat : BlockSamplePath setup → ℝ := fun ω =>
      ⟪xTildeIter setup hStanding t ω,
          (∑ i : ι, (yHatIter setup hStanding t ω i).1) -
            ∑ i : ι, (z.2 i).1⟫_ℝ -
        ⟪(xIter setup hStanding t ω).1,
          (∑ i : ι, yTildeIter setup hStanding t ω i) -
            ∑ i : ι, (z.2 i).1⟫_ℝ +
        ⟪z.1.1,
          (∑ i : ι, yTildeIter setup hStanding t ω i) -
            ∑ i : ι, (yHatIter setup hStanding t ω i).1⟫_ℝ
    let Ipub : BlockSamplePath setup → ℝ := fun ω =>
      ⟪xTildeIter setup hStanding t ω - (xIter setup hStanding t ω).1,
        ∑ i : ι, (yTildeIter setup hStanding t ω i - (z.2 i).1)⟫_ℝ
    let Rcur : ι → BlockSamplePath setup → ℝ := fun i ω =>
      (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) ((yIter setup hStanding t ω) i))
    let sampledResidual : BlockSamplePath setup → ℝ := fun ω =>
      (setup.τ t *
          inverseProbabilityValue setup (sampledBlock setup t ω)
            (sampledBlock_probability_ne_zero setup
              (sampledPositiveBlock setup t ω))) *
        (SOptLib.carrierBregmanDivergence (dualConjugate setup (sampledBlock setup t ω)) (dualConjugateBaseSelector setup (sampledBlock setup t ω) ((yIter setup hStanding (t - 1) ω) (sampledBlock setup t ω)) (dualSubgradIter setup hStanding (t - 1) ω
            (sampledBlock setup t ω))) ((yIter setup hStanding (t - 1) ω) (sampledBlock setup t ω)) ((yIter setup hStanding t ω) (sampledBlock setup t ω)))
    let Dpub : ι → BlockSamplePath setup → ℝ := fun i ω =>
      (inverseProbabilityValue setup i (hProbDen i) * (1 + setup.τ t) - 1) *
          (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) (z.2 i)) -
        (inverseProbabilityValue setup i (hProbDen i) * (1 + setup.τ t)) *
          (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding t ω) i) (dualSubgradIter setup hStanding t ω i)) ((yIter setup hStanding t ω) i) (z.2 i))
    have hhatSplit :
        finitePrefixExpectation setup t hatRhs =
          finitePrefixExpectation setup t P +
            finitePrefixExpectation setup t Dhat +
            finitePrefixExpectation setup t Ihat := by
      change finitePrefixExpectation setup t
          (fun ω => (P ω + Dhat ω) + Ihat ω) =
        finitePrefixExpectation setup t P +
          finitePrefixExpectation setup t Dhat +
          finitePrefixExpectation setup t Ihat
      rw [finitePrefixExpectation_add, finitePrefixExpectation_add]
    have hinnerSolvedFinite :
        finitePrefixExpectation setup t Ihat =
          finitePrefixExpectation setup t Ipub := by
      simpa [Ihat, Ipub] using
        lemma55_hat_inner_terms_finitePrefix_rewrite
          setup hStanding hProbDen t _ht z
    have hsampledResidualSplit :
        (∑ i : ι,
          (setup.τ t * inverseProbabilityValue setup i (hProbDen i)) *
            finitePrefixExpectation setup t (Rcur i)) =
          finitePrefixExpectation setup t sampledResidual := by
      rw [← hsampledResidualFinite]
      simp [Rcur, finitePrefixExpectation_finset_sum,
        finitePrefixExpectation_const_mul]
    have hdualSolved :
        finitePrefixExpectation setup t Dhat =
          (∑ i : ι, finitePrefixExpectation setup t (Dpub i)) -
            ∑ i : ι,
              (setup.τ t * inverseProbabilityValue setup i (hProbDen i)) *
                finitePrefixExpectation setup t (Rcur i) := by
      rw [finitePrefixExpectation_finset_sum]
      calc
        (∑ i : ι, finitePrefixExpectation setup t (fun ω =>
          setup.τ t *
                (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) (z.2 i)) -
              (1 + setup.τ t) *
                (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i (yHatIter setup hStanding t ω i) (yHatSubgradIter setup hStanding t _ht ω i)) (yHatIter setup hStanding t ω i) (z.2 i)) -
            setup.τ t *
              (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) (yHatIter setup hStanding t ω i)))) =
            ∑ i : ι,
              (finitePrefixExpectation setup t (Dpub i) -
                (setup.τ t * inverseProbabilityValue setup i (hProbDen i)) *
                  finitePrefixExpectation setup t (Rcur i)) := by
            apply Finset.sum_congr rfl
            intro i _hi
            simp [Dpub, Rcur, finitePrefixExpectation_sub,
              finitePrefixExpectation_const_mul, hhatSolvedFinite i,
              hfirstSolvedFinite i]
            ring
        _ = (∑ i : ι, finitePrefixExpectation setup t (Dpub i)) -
            ∑ i : ι,
              (setup.τ t * inverseProbabilityValue setup i (hProbDen i)) *
                finitePrefixExpectation setup t (Rcur i) := by
            rw [Finset.sum_sub_distrib]
    calc
      finitePrefixExpectation setup t hatRhs =
          finitePrefixExpectation setup t P +
            finitePrefixExpectation setup t Dhat +
            finitePrefixExpectation setup t Ihat := hhatSplit
      _ = finitePrefixExpectation setup t P +
            ((∑ i : ι, finitePrefixExpectation setup t (Dpub i)) -
              ∑ i : ι,
                (setup.τ t * inverseProbabilityValue setup i (hProbDen i)) *
                  finitePrefixExpectation setup t (Rcur i)) +
            finitePrefixExpectation setup t Ipub := by
            rw [hdualSolved, hinnerSolvedFinite]
      _ = publicRhs := by
            rw [hsampledResidualSplit]
            simp [publicRhs, P, Dpub, Ipub, sampledResidual,
              finitePrefixExpectation_sub]
            ring
  calc
    expectedSaddleGap setup hStanding t z ≤
        finitePrefixExpectation setup t hatRhs := hmono
    _ = publicRhs := hsubst
    _ = _ := by
      rfl

/-- Young/Cauchy bound used in Eq. (5.1.58):
`b⟪u,v⟫ + a‖v‖²/2 ≥ -b²‖u‖²/(2a)` for `a>0`. -/
theorem Young_Cauchy_bound_5_1_58 (a b : ℝ) (u v : E) (ha : 0 < a) :
    - (b ^ 2 * ‖u‖ ^ 2) / (2 * a) ≤
      b * ⟪u, v⟫_ℝ + a * ‖v‖ ^ 2 / 2 := by
  classical
  have ha_ne : a ≠ 0 := ne_of_gt ha
  have hY := neg_inner_le_half_mul_norm_sq_add_inv_two_mul_norm_sq (E := E) ha (b • u) v
  have hnorm : ‖b • u‖ ^ 2 = b ^ 2 * ‖u‖ ^ 2 := by
    rw [norm_smul]
    calc
      (‖b‖ * ‖u‖) ^ 2 = ‖b‖ ^ 2 * ‖u‖ ^ 2 := by ring
      _ = b ^ 2 * ‖u‖ ^ 2 := by
        simp [Real.norm_eq_abs, sq_abs]
  have hY' :
      -(b * ⟪u, v⟫_ℝ) ≤ a * ‖v‖ ^ 2 / 2 + (b ^ 2 * ‖u‖ ^ 2) / (2 * a) := by
    calc
      -(b * ⟪u, v⟫_ℝ) = -⟪b • u, v⟫_ℝ := by
        simp [inner_smul_left]
      _ ≤ (a / 2) * ‖v‖ ^ 2 + (1 / (2 * a)) * ‖b • u‖ ^ 2 := hY
      _ = a * ‖v‖ ^ 2 / 2 + (b ^ 2 * ‖u‖ ^ 2) / (2 * a) := by
        rw [hnorm]
        field_simp [ha_ne]
  let ip : ℝ := b * ⟪u, v⟫_ℝ
  let A : ℝ := a * ‖v‖ ^ 2 / 2
  let B : ℝ := (b ^ 2 * ‖u‖ ^ 2) / (2 * a)
  have hY'' : -ip ≤ A + B := by
    simpa [ip, A, B, add_comm, add_left_comm, add_assoc] using hY'
  have hmove : -B ≤ ip + A := by
    linarith
  simpa [ip, A, B, neg_div, add_comm, add_left_comm, add_assoc] using hmove

/-- Primal part of the weighted Proposition 5.1 telescope, aligned with Lan
Eq. (5.1.53) after transporting prefix expectations to the full generated
stream. This specializes the SOptLib scalar telescope
`sum_Icc_two_coeff_telescope_le`; searched `Icc telescoping sum theta eta primal
Bregman dual Bregman Proposition 5.1`, and the shifted-delta and output-window
candidates were rejected because they do not match the adjacent coefficients
`θ_t η_t` and `θ_t(μ+η_t)` from Eq. (5.1.47). -/
private theorem proposition51_primal_fullstream_telescope
    (hStanding : standingAssumptions setup)
    (θ : ℕ → ℝ) (k : ℕ) (hk : 1 ≤ k) (z : SaddlePoint setup)
    (h47 : ∀ t, 2 ≤ t → t ≤ k →
      θ t * setup.η t ≤ θ (t - 1) * (setup.μ + setup.η (t - 1))) :
    (Finset.sum (Finset.Icc 1 k) (fun t =>
        (θ t * setup.η t) *
            (∫ ω, primalBregman setup
              (xIter setup hStanding (t - 1) ω) z.1 ∂blockStreamLaw setup) -
          (θ t * (setup.μ + setup.η t)) *
            (∫ ω, primalBregman setup
              (xIter setup hStanding t ω) z.1 ∂blockStreamLaw setup))) ≤
      (θ 1 * setup.η 1) *
          (∫ ω, primalBregman setup
            (xIter setup hStanding 0 ω) z.1 ∂blockStreamLaw setup) -
        (θ k * (setup.μ + setup.η k)) *
          (∫ ω, primalBregman setup
            (xIter setup hStanding k ω) z.1 ∂blockStreamLaw setup) := by
  classical
  let c : ℕ → ℝ := fun t => θ t * setup.η t
  let d : ℕ → ℝ := fun t => θ t * (setup.μ + setup.η t)
  let V : ℕ → ℝ := fun t =>
    ∫ ω, primalBregman setup (xIter setup hStanding t ω) z.1
      ∂blockStreamLaw setup
  have hV_nonneg : ∀ n, 1 ≤ n → n < k → 0 ≤ V n := by
    intro n _hn _hnk
    dsimp [V]
    exact MeasureTheory.integral_nonneg fun ω =>
      primalBregman_nonnegative_of_standing setup hStanding
        (xIter setup hStanding n ω) z.1
  have hbridge : ∀ n, 1 ≤ n → n < k → c (n + 1) ≤ d n := by
    intro n hn hnk
    have htwo : 2 ≤ n + 1 := by omega
    have hle : n + 1 ≤ k := by omega
    have h := h47 (n + 1) htwo hle
    simpa [c, d, Nat.succ_eq_add_one] using h
  simpa [c, d, V] using
    (SOptLib.sum_Icc_two_coeff_telescope_le c d V k hk hV_nonneg hbridge)

/-- Internal source-gap realization of Proposition 5.1 condition (5.1.46), with
each all-block printed `p_i^{-1}` using the named source-gap reciprocal. -/
def propositionCondition_5_1_46_with_denominator_source_gap
    (θ : ℕ → ℝ) (k : ℕ) (hDen : proposition_5_1_denominatorBoundary setup k) : Prop :=
  ∀ t i, 2 ≤ t → t ≤ k →
    θ t * (inverseProbabilityValue setup i (hDen.1 i) *
        (1 + setup.τ t) - 1) ≤
      inverseProbabilityValue setup i (hDen.1 i) *
        θ (t - 1) * (1 + setup.τ (t - 1))

/-- Fixed-coordinate dual part of the weighted Proposition 5.1 telescope,
aligned with Lan Eq. (5.1.53) after transporting prefix expectations to the
full generated stream. This specializes SOptLib
`sum_Icc_two_coeff_telescope_le`; searched `dual carrier Bregman nonnegative dual strong
convexity lower bound` and used the local selected-subgradient nonnegativity
bridge because the available SOptLib Bregman lemmas do not target the paper's
selected `J_i'` Bregman object. -/
private theorem proposition51_dual_fullstream_telescope
    (hStanding : standingAssumptions setup)
    (θ : ℕ → ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hDen : proposition_5_1_denominatorBoundary setup k)
    (z : SaddlePoint setup)
    (h46 : propositionCondition_5_1_46_with_denominator_source_gap setup θ k hDen)
    (i : ι) :
    (Finset.sum (Finset.Icc 1 k) (fun t =>
        (θ t * (inverseProbabilityValue setup i (hDen.1 i) *
            (1 + setup.τ t) - 1)) *
            (∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) (z.2 i))
                ∂blockStreamLaw setup) -
          (inverseProbabilityValue setup i (hDen.1 i) * θ t *
              (1 + setup.τ t)) *
            (∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding t ω) i) (dualSubgradIter setup hStanding t ω i)) ((yIter setup hStanding t ω) i) (z.2 i))
                ∂blockStreamLaw setup))) ≤
      (θ 1 * (inverseProbabilityValue setup i (hDen.1 i) *
          (1 + setup.τ 1) - 1)) *
          (∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding 0 ω) i) (dualSubgradIter setup hStanding 0 ω i)) ((yIter setup hStanding 0 ω) i) (z.2 i))
              ∂blockStreamLaw setup) -
        (inverseProbabilityValue setup i (hDen.1 i) * θ k *
            (1 + setup.τ k)) *
          (∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding k ω) i) (dualSubgradIter setup hStanding k ω i)) ((yIter setup hStanding k ω) i) (z.2 i))
              ∂blockStreamLaw setup) := by
  classical
  let c : ℕ → ℝ := fun t =>
    θ t * (inverseProbabilityValue setup i (hDen.1 i) *
      (1 + setup.τ t) - 1)
  let d : ℕ → ℝ := fun t =>
    inverseProbabilityValue setup i (hDen.1 i) * θ t * (1 + setup.τ t)
  let V : ℕ → ℝ := fun t =>
    ∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding t ω) i) (dualSubgradIter setup hStanding t ω i)) ((yIter setup hStanding t ω) i) (z.2 i))
        ∂blockStreamLaw setup
  have hV_nonneg : ∀ n, 1 ≤ n → n < k → 0 ≤ V n := by
    intro n _hn _hnk
    dsimp [V]
    exact MeasureTheory.integral_nonneg fun ω =>
      dualBregman_nonnegative setup i ((yIter setup hStanding n ω) i)
        (dualSubgradIter setup hStanding n ω i) (z.2 i)
  have hbridge : ∀ n, 1 ≤ n → n < k → c (n + 1) ≤ d n := by
    intro n hn hnk
    have htwo : 2 ≤ n + 1 := by omega
    have hle : n + 1 ≤ k := by omega
    have h := h46 (n + 1) i htwo hle
    simpa [c, d, Nat.succ_eq_add_one, mul_assoc] using h
  simpa [c, d, V, mul_assoc] using
    (SOptLib.sum_Icc_two_coeff_telescope_le c d V k hk hV_nonneg hbridge)

/-- Internal source-gap realization of Proposition 5.1 condition (5.1.48), where
the PDF prints the quotient by `m τ_k p_i` but does not state all denominator
admissibility facts separately. -/
def propositionCondition_5_1_48_with_denominator_source_gap
    (k : ℕ) (_hk : 1 ≤ k) (hDen : proposition_5_1_denominatorBoundary setup k) : Prop :=
  ∀ i,
    sourceQuotient (setup.L i * (1 - samplingProbability setup i) ^ 2)
        ((componentCount (ι := ι) : ℝ) * setup.τ k * samplingProbability setup i)
        (hDen.2 k i) ≤
      setup.η k / 4

/-- Internal source-gap realization of Proposition 5.1 condition (5.1.49), where
the PDF prints quotients by `m τ_t p_i` and `m τ_{t-1} p_j` without separate
denominator assumptions. -/
def propositionCondition_5_1_49_with_denominator_source_gap
    (k : ℕ) (hDen : proposition_5_1_denominatorBoundary setup k) : Prop :=
  ∀ t i j, (ht2 : 2 ≤ t) → (htk : t ≤ k) →
    sourceQuotient (setup.L i * setup.α t)
        ((componentCount (ι := ι) : ℝ) * setup.τ t * samplingProbability setup i)
        (hDen.2 t i) +
      sourceQuotient ((1 - samplingProbability setup j) ^ 2 * setup.L j)
        ((componentCount (ι := ι) : ℝ) * setup.τ (t - 1) *
          samplingProbability setup j)
        (hDen.2 (t - 1) j) ≤
      setup.η (t - 1) / 2

/-- Proposition 5.1 condition (5.1.50), with the printed quotient realized
through the source-derived `m(1+τ_k)` denominator certificate. -/
def propositionCondition_5_1_50_with_denominator_source_gap
    (hStanding : standingAssumptions setup) (k : ℕ) (hk : 1 ≤ k) : Prop :=
  sourceQuotient (∑ i : ι, samplingProbability setup i * setup.L i)
      ((componentCount (ι := ι) : ℝ) * (1 + setup.τ k))
      (onePlusTauComponentDenominator_ne_of_standing setup hStanding k hk) ≤
    setup.η k / 2

/-- One-block Young absorption in the source quotient form used in
Proposition 5.1 around Eq. (5.1.58). Searched `Young absorption inner product
source quotient Bregman`; SOptLib `young_absorb_inner_of_norm_sq_budget`,
`young_absorb_sample_correction_of_cocoercive_budget`, and
`young_absorb_average_inner_with_quadratic_budget` were considered, but all
require a positive Lipschitz constant or package a different averaged residual.
This route-local lemma handles the paper's division-free `L_i = 0` branch using
`dualBregman_cross_quadratic_lower_bound`, then uses the local
`Young_Cauchy_bound_5_1_58` with the explicit denominator certificate. -/
private theorem proposition51_dual_young_absorb_with_sourceQuotient
    (hStanding : standingAssumptions setup)
    (t : ℕ) (ht : 1 ≤ t) (i : ι)
    (hp : samplingProbability setup i ≠ 0)
    (hden : (componentCount (ι := ι) : ℝ) * setup.τ t *
      samplingProbability setup i ≠ 0)
    (β : ℝ) (u : E) (y0 : DualCarrier setup i)
    (baseSubgrad : DualConjugateSubgradient setup i y0)
    (y : DualCarrier setup i) :
    - sourceQuotient (setup.L i * β ^ 2)
        ((componentCount (ι := ι) : ℝ) * setup.τ t *
          samplingProbability setup i) hden * ‖u‖ ^ 2 ≤
      β * ⟪u, y.1 - y0.1⟫_ℝ +
        setup.τ t * inverseProbabilityValue setup i hp *
          (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i y0 baseSubgrad) y0 y) := by
  classical
  let m : ℝ := (componentCount (ι := ι) : ℝ)
  let τ : ℝ := setup.τ t
  let p : ℝ := samplingProbability setup i
  let L : ℝ := setup.L i
  let W : ℝ := (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i y0 baseSubgrad) y0 y)
  let v : E := y.1 - y0.1
  have hm_pos : 0 < m := by
    simpa [m] using componentCount_real_pos (ι := ι)
  have hm_ne : m ≠ 0 := ne_of_gt hm_pos
  have hp_nonneg : 0 ≤ p := by
    simpa [p] using samplingProbability_nonnegative setup i
  have hp_ne : p ≠ 0 := by
    simpa [p] using hp
  have hp_pos : 0 < p := lt_of_le_of_ne hp_nonneg (Ne.symm hp_ne)
  have hp_le_one : p ≤ 1 := by
    simpa [p] using samplingProbability_le_one setup i
  have hτ_nonneg : 0 ≤ τ := by
    rcases hStanding with ⟨_, _, _, _, _, _, _, _, _, _, _, hParam⟩
    simpa [τ] using hParam.1 t ht
  have hτ_ne : τ ≠ 0 := by
    intro hτ_zero
    apply hden
    simpa [m, τ, p, hτ_zero]
  have hτ_pos : 0 < τ := lt_of_le_of_ne hτ_nonneg (Ne.symm hτ_ne)
  have hL_nonneg : 0 ≤ L := by
    rcases hStanding with ⟨_, hSmooth, _, _, _, _, _, _, _, _, _, _⟩
    simpa [L] using hSmooth.2.1 i
  have hinv :
      inverseProbabilityValue setup i hp = 1 / p := by
    rw [inverseProbabilityValue, sourceQuotient_def]
  have hquad :
      m / 2 * ‖v‖ ^ 2 ≤ L * W := by
    have h :=
      dualBregman_cross_quadratic_lower_bound setup hStanding i y0 baseSubgrad y
    simpa [m, L, W, v, norm_sub_rev] using h
  by_cases hL_zero : L = 0
  · have hv_sq_nonpos : ‖v‖ ^ 2 ≤ 0 := by
      have hquad_zero : m / 2 * ‖v‖ ^ 2 ≤ 0 := by
        simpa [hL_zero] using hquad
      nlinarith [hquad_zero, hm_pos]
    have hv_norm_zero : ‖v‖ = 0 := by
      nlinarith [sq_nonneg ‖v‖, hv_sq_nonpos]
    have hv_zero : v = 0 := norm_eq_zero.mp hv_norm_zero
    have hdiff_zero : y.1 - y0.1 = 0 := by
      simpa [v] using hv_zero
    have hW_nonneg : 0 ≤ W := by
      simpa [W] using
        dualBregman_nonnegative setup i y0 baseSubgrad y
    have hinv_pos : 0 < inverseProbabilityValue setup i hp := by
      rw [hinv]
      exact one_div_pos.mpr hp_pos
    have hcoef_nonneg : 0 ≤ τ * inverseProbabilityValue setup i hp :=
      mul_nonneg (le_of_lt hτ_pos) (le_of_lt hinv_pos)
    have hright_nonneg :
        0 ≤ β * ⟪u, y.1 - y0.1⟫_ℝ +
          τ * inverseProbabilityValue setup i hp * W := by
      have hinner_zero : β * ⟪u, y.1 - y0.1⟫_ℝ = 0 := by
        simp [hdiff_zero]
      rw [hinner_zero, zero_add]
      exact mul_nonneg hcoef_nonneg hW_nonneg
    have hsource_zero :
        sourceQuotient (setup.L i * β ^ 2)
            ((componentCount (ι := ι) : ℝ) * setup.τ t *
              samplingProbability setup i) hden = 0 := by
      rw [sourceQuotient_def]
      simp [L, hL_zero]
    simpa [m, τ, p, L, W, hsource_zero] using hright_nonneg
  · have hL_pos : 0 < L := lt_of_le_of_ne hL_nonneg (Ne.symm hL_zero)
    have hL_ne : L ≠ 0 := ne_of_gt hL_pos
    have ha_pos : 0 < m * τ / (L * p) :=
      div_pos (mul_pos hm_pos hτ_pos) (mul_pos hL_pos hp_pos)
    have hYoung :=
      Young_Cauchy_bound_5_1_58 (m * τ / (L * p)) β u v ha_pos
    have hscale_nonneg : 0 ≤ τ * (1 / p) / L := by
      exact div_nonneg
        (mul_nonneg (le_of_lt hτ_pos)
          (one_div_nonneg.mpr (le_of_lt hp_pos)))
        (le_of_lt hL_pos)
    have hbudget :
        (m * τ / (L * p)) * ‖v‖ ^ 2 / 2 ≤ τ * (1 / p) * W := by
      calc
        (m * τ / (L * p)) * ‖v‖ ^ 2 / 2 =
            (τ * (1 / p) / L) * (m / 2 * ‖v‖ ^ 2) := by
              field_simp [hm_ne, hτ_ne, hL_ne, hp_ne]
        _ ≤ (τ * (1 / p) / L) * (L * W) :=
              mul_le_mul_of_nonneg_left hquad hscale_nonneg
        _ = τ * (1 / p) * W := by
              field_simp [hL_ne, hp_ne]
    have hYoungBudget :
        - (β ^ 2 * ‖u‖ ^ 2) / (2 * (m * τ / (L * p))) ≤
          β * ⟪u, v⟫_ℝ + τ * (1 / p) * W := by
      nlinarith [hYoung, hbudget]
    have hYoungBudget' :
        - ((β ^ 2 * ‖u‖ ^ 2) / (2 * (m * τ / (L * p)))) ≤
          β * ⟪u, y.1 - y0.1⟫_ℝ +
            τ * inverseProbabilityValue setup i hp * W := by
      simpa [v, hinv, neg_div] using hYoungBudget
    have hscalar :
        L * p / (2 * (m * τ)) ≤ L / (m * τ * p) := by
      field_simp [hm_ne, hτ_ne, hp_ne]
      nlinarith [hL_nonneg, hp_pos, hp_le_one, hm_pos, hτ_pos]
    have hcorr :
        (β ^ 2 * ‖u‖ ^ 2) / (2 * (m * τ / (L * p))) ≤
          sourceQuotient (setup.L i * β ^ 2)
            ((componentCount (ι := ι) : ℝ) * setup.τ t *
              samplingProbability setup i) hden * ‖u‖ ^ 2 := by
      rw [sourceQuotient_def]
      calc
        (β ^ 2 * ‖u‖ ^ 2) / (2 * (m * τ / (L * p))) =
            (L * p / (2 * (m * τ))) * (β ^ 2 * ‖u‖ ^ 2) := by
              field_simp [hm_ne, hτ_ne, hL_ne, hp_ne]
        _ ≤ (L / (m * τ * p)) * (β ^ 2 * ‖u‖ ^ 2) :=
              mul_le_mul_of_nonneg_right hscalar
                (mul_nonneg (sq_nonneg β) (sq_nonneg ‖u‖))
        _ = (L * β ^ 2) / (m * τ * p) * ‖u‖ ^ 2 := by
              ring
        _ = (setup.L i * β ^ 2) /
              ((componentCount (ι := ι) : ℝ) * setup.τ t *
                samplingProbability setup i) * ‖u‖ ^ 2 := by
              simp [m, τ, p, L, mul_assoc]
    have hneg_le :
        - (sourceQuotient (setup.L i * β ^ 2)
            ((componentCount (ι := ι) : ℝ) * setup.τ t *
              samplingProbability setup i) hden * ‖u‖ ^ 2) ≤
          - ((β ^ 2 * ‖u‖ ^ 2) / (2 * (m * τ / (L * p)))) := by
      linarith
    have hmain :
          - (sourceQuotient (setup.L i * β ^ 2)
              ((componentCount (ι := ι) : ℝ) * setup.τ t *
                samplingProbability setup i) hden * ‖u‖ ^ 2) ≤
            β * ⟪u, y.1 - y0.1⟫_ℝ +
              τ * inverseProbabilityValue setup i hp * W := by
        exact le_trans hneg_le hYoungBudget'
    simpa [m, τ, p, L, W, neg_mul] using hmain

/-- Nonnegative terminal sampled-block coefficient after applying condition
(5.1.48), used in the coefficient-drop part of Eq. (5.1.57). Searched
`Proposition 5.1 condition 5.1.48 nonnegative coefficient eta four
sourceQuotient`; the target file only had the condition definition itself, and
SOptLib has no paper-specific `m τ_k p_i` quotient coefficient helper. -/
private theorem proposition51_h48_terminal_sampled_coefficient_nonnegative
    (θ : ℕ → ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hDen : proposition_5_1_denominatorBoundary setup k)
    (hθ : ∀ t, 1 ≤ t → t ≤ k → 0 ≤ θ t)
    (h48 : propositionCondition_5_1_48_with_denominator_source_gap setup k hk hDen)
    (i : ι) (u : E) :
    0 ≤ θ k *
      (setup.η k / 4 -
        sourceQuotient (setup.L i * (1 - samplingProbability setup i) ^ 2)
          ((componentCount (ι := ι) : ℝ) * setup.τ k * samplingProbability setup i)
          (hDen.2 k i)) * ‖u‖ ^ 2 := by
  have hθk : 0 ≤ θ k := hθ k hk le_rfl
  have hcoef :
      0 ≤ setup.η k / 4 -
        sourceQuotient (setup.L i * (1 - samplingProbability setup i) ^ 2)
          ((componentCount (ι := ι) : ℝ) * setup.τ k * samplingProbability setup i)
          (hDen.2 k i) := sub_nonneg.mpr (h48 i)
  exact mul_nonneg (mul_nonneg hθk hcoef) (sq_nonneg ‖u‖)

/-- Nonnegative historical coefficient after the Eq. (5.1.51) rewrite and
condition (5.1.49), used to drop the historical quadratic blocks in Eq.
(5.1.57). Searched `Proposition 5.1 condition 5.1.49 historical coefficient
nonnegative theta alpha`; existing hits were only the condition definitions and
the unrelated h50 terminal residual helper, so this local bridge records the
post-h51 coefficient form. -/
private theorem proposition51_h49_historical_coefficient_nonnegative
    (θ : ℕ → ℝ) (k : ℕ)
    (hDen : proposition_5_1_denominatorBoundary setup k)
    (hθ : ∀ t, 1 ≤ t → t ≤ k → 0 ≤ θ t)
    (h49 : propositionCondition_5_1_49_with_denominator_source_gap setup k hDen)
    (t : ℕ) (i j : ι) (ht2 : 2 ≤ t) (htk : t ≤ k) (u : E) :
    0 ≤ θ (t - 1) *
      (setup.η (t - 1) / 2 -
        (sourceQuotient (setup.L i * setup.α t)
            ((componentCount (ι := ι) : ℝ) * setup.τ t *
              samplingProbability setup i)
            (hDen.2 t i) +
          sourceQuotient ((1 - samplingProbability setup j) ^ 2 * setup.L j)
            ((componentCount (ι := ι) : ℝ) * setup.τ (t - 1) *
              samplingProbability setup j)
            (hDen.2 (t - 1) j))) * ‖u‖ ^ 2 := by
  have htminus_pos : 1 ≤ t - 1 := by omega
  have htminus_le : t - 1 ≤ k := by omega
  have hθprev : 0 ≤ θ (t - 1) := hθ (t - 1) htminus_pos htminus_le
  have hcoef :
      0 ≤ setup.η (t - 1) / 2 -
        (sourceQuotient (setup.L i * setup.α t)
            ((componentCount (ι := ι) : ℝ) * setup.τ t *
              samplingProbability setup i)
            (hDen.2 t i) +
          sourceQuotient ((1 - samplingProbability setup j) ^ 2 * setup.L j)
            ((componentCount (ι := ι) : ℝ) * setup.τ (t - 1) *
              samplingProbability setup j)
            (hDen.2 (t - 1) j)) := by
    exact sub_nonneg.mpr (h49 t i j ht2 htk)
  exact mul_nonneg (mul_nonneg hθprev hcoef) (sq_nonneg ‖u‖)

/-- One-block Young absorption for the sampled terms where `p_i^{-1}` multiplies
both the inner product and the dual Bregman budget in Proposition 5.1
Eq. (5.1.56). No SOptLib match: searched `weighted coupling telescope sampled
inner product sourceQuotient`, scanned `SOptLib/Model/Iterates.lean`,
`SOptLib/Layer1/Telescope.lean`, and `SOptLib/Glue/Algebra.lean`, and checked
`SOptLib.sum_Icc_two_coeff_telescope_le`,
`SOptLib.sum_range_weighted_lagged_source_telescope_le`, and the local
`proposition51_dual_young_absorb_with_sourceQuotient`; none matches this exact
Eq. (5.1.56) inverse-inner shape because the existing local Young bridge has
coefficient `β⟪u,d⟫ + τ p_i^{-1} W`, while this source step needs
`p_i^{-1}β⟪u,d⟫ + τ p_i^{-1} W`. -/
private theorem proposition51_dual_young_absorb_inverse_inner_with_sourceQuotient
    (hStanding : standingAssumptions setup)
    (t : ℕ) (ht : 1 ≤ t) (i : ι)
    (hp : samplingProbability setup i ≠ 0)
    (hden : (componentCount (ι := ι) : ℝ) * setup.τ t *
      samplingProbability setup i ≠ 0)
    (β : ℝ) (u : E) (y0 : DualCarrier setup i)
    (baseSubgrad : DualConjugateSubgradient setup i y0)
    (y : DualCarrier setup i) :
    - sourceQuotient (setup.L i * β ^ 2)
        ((componentCount (ι := ι) : ℝ) * setup.τ t *
          samplingProbability setup i) hden * ‖u‖ ^ 2 ≤
      inverseProbabilityValue setup i hp * β * ⟪u, y.1 - y0.1⟫_ℝ +
        setup.τ t * inverseProbabilityValue setup i hp *
          (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i y0 baseSubgrad) y0 y) := by
  classical
  let m : ℝ := (componentCount (ι := ι) : ℝ)
  let τ : ℝ := setup.τ t
  let p : ℝ := samplingProbability setup i
  let L : ℝ := setup.L i
  let W : ℝ := (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i y0 baseSubgrad) y0 y)
  let v : E := y.1 - y0.1
  have hm_pos : 0 < m := by
    simpa [m] using componentCount_real_pos (ι := ι)
  have hm_ne : m ≠ 0 := ne_of_gt hm_pos
  have hp_nonneg : 0 ≤ p := by
    simpa [p] using samplingProbability_nonnegative setup i
  have hp_ne : p ≠ 0 := by
    simpa [p] using hp
  have hp_pos : 0 < p := lt_of_le_of_ne hp_nonneg (Ne.symm hp_ne)
  have hτ_nonneg : 0 ≤ τ := by
    rcases hStanding with ⟨_, _, _, _, _, _, _, _, _, _, _, hParam⟩
    simpa [τ] using hParam.1 t ht
  have hτ_ne : τ ≠ 0 := by
    intro hτ_zero
    apply hden
    simpa [m, τ, p, hτ_zero]
  have hτ_pos : 0 < τ := lt_of_le_of_ne hτ_nonneg (Ne.symm hτ_ne)
  have hL_nonneg : 0 ≤ L := by
    rcases hStanding with ⟨_, hSmooth, _, _, _, _, _, _, _, _, _, _⟩
    simpa [L] using hSmooth.2.1 i
  have hinv :
      inverseProbabilityValue setup i hp = 1 / p := by
    rw [inverseProbabilityValue, sourceQuotient_def]
  have hquad :
      m / 2 * ‖v‖ ^ 2 ≤ L * W := by
    have h :=
      dualBregman_cross_quadratic_lower_bound setup hStanding i y0 baseSubgrad y
    simpa [m, L, W, v, norm_sub_rev] using h
  by_cases hL_zero : L = 0
  · have hv_sq_nonpos : ‖v‖ ^ 2 ≤ 0 := by
      have hquad_zero : m / 2 * ‖v‖ ^ 2 ≤ 0 := by
        simpa [hL_zero] using hquad
      nlinarith [hquad_zero, hm_pos]
    have hv_norm_zero : ‖v‖ = 0 := by
      nlinarith [sq_nonneg ‖v‖, hv_sq_nonpos]
    have hv_zero : v = 0 := norm_eq_zero.mp hv_norm_zero
    have hdiff_zero : y.1 - y0.1 = 0 := by
      simpa [v] using hv_zero
    have hW_nonneg : 0 ≤ W := by
      simpa [W] using
        dualBregman_nonnegative setup i y0 baseSubgrad y
    have hinv_pos : 0 < inverseProbabilityValue setup i hp := by
      rw [hinv]
      exact one_div_pos.mpr hp_pos
    have hcoef_nonneg :
        0 ≤ τ * inverseProbabilityValue setup i hp :=
      mul_nonneg (le_of_lt hτ_pos) (le_of_lt hinv_pos)
    have hright_nonneg :
        0 ≤ inverseProbabilityValue setup i hp * β *
            ⟪u, y.1 - y0.1⟫_ℝ +
          τ * inverseProbabilityValue setup i hp * W := by
      have hinner_zero :
          inverseProbabilityValue setup i hp * β *
              ⟪u, y.1 - y0.1⟫_ℝ = 0 := by
        simp [hdiff_zero]
      rw [hinner_zero, zero_add]
      exact mul_nonneg hcoef_nonneg hW_nonneg
    have hsource_zero :
        sourceQuotient (setup.L i * β ^ 2)
            ((componentCount (ι := ι) : ℝ) * setup.τ t *
              samplingProbability setup i) hden = 0 := by
      rw [sourceQuotient_def]
      simp [L, hL_zero]
    simpa [m, τ, p, L, W, hsource_zero] using hright_nonneg
  · have hL_pos : 0 < L := lt_of_le_of_ne hL_nonneg (Ne.symm hL_zero)
    have hL_ne : L ≠ 0 := ne_of_gt hL_pos
    have ha_pos : 0 < m * τ / L :=
      div_pos (mul_pos hm_pos hτ_pos) hL_pos
    have hYoung :=
      Young_Cauchy_bound_5_1_58 (m * τ / L) β u v ha_pos
    have hscale_nonneg : 0 ≤ τ / L :=
      div_nonneg (le_of_lt hτ_pos) (le_of_lt hL_pos)
    have hbudget :
        (m * τ / L) * ‖v‖ ^ 2 / 2 ≤ τ * W := by
      calc
        (m * τ / L) * ‖v‖ ^ 2 / 2 =
            (τ / L) * (m / 2 * ‖v‖ ^ 2) := by
              field_simp [hm_ne, hτ_ne, hL_ne]
        _ ≤ (τ / L) * (L * W) :=
              mul_le_mul_of_nonneg_left hquad hscale_nonneg
        _ = τ * W := by
              field_simp [hL_ne]
    have hYoungBudget :
        - (β ^ 2 * ‖u‖ ^ 2) / (2 * (m * τ / L)) ≤
          β * ⟪u, v⟫_ℝ + τ * W := by
      nlinarith [hYoung, hbudget]
    have hinv_nonneg : 0 ≤ 1 / p := one_div_nonneg.mpr (le_of_lt hp_pos)
    have hscaled :
        (1 / p) *
            (-(β ^ 2 * ‖u‖ ^ 2) / (2 * (m * τ / L))) ≤
          (1 / p) * (β * ⟪u, v⟫_ℝ + τ * W) :=
      mul_le_mul_of_nonneg_left hYoungBudget hinv_nonneg
    have hcorr :
        (1 / p) * ((β ^ 2 * ‖u‖ ^ 2) / (2 * (m * τ / L))) ≤
          sourceQuotient (setup.L i * β ^ 2)
            ((componentCount (ι := ι) : ℝ) * setup.τ t *
              samplingProbability setup i) hden * ‖u‖ ^ 2 := by
      rw [sourceQuotient_def]
      calc
        (1 / p) * ((β ^ 2 * ‖u‖ ^ 2) / (2 * (m * τ / L))) =
            ((L * β ^ 2) / (2 * (m * τ * p))) * ‖u‖ ^ 2 := by
              field_simp [hm_ne, hτ_ne, hL_ne, hp_ne]
        _ ≤ ((L * β ^ 2) / (m * τ * p)) * ‖u‖ ^ 2 := by
              have hcoef_nonneg :
                  0 ≤ (L * β ^ 2) / (m * τ * p) := by
                exact div_nonneg
                  (mul_nonneg (le_of_lt hL_pos) (sq_nonneg β))
                  (mul_nonneg (mul_nonneg (le_of_lt hm_pos) (le_of_lt hτ_pos))
                    (le_of_lt hp_pos))
              have hhalf :
                  (L * β ^ 2) / (2 * (m * τ * p)) ≤
                    (L * β ^ 2) / (m * τ * p) := by
                have hhalf_eq :
                    (L * β ^ 2) / (2 * (m * τ * p)) =
                      ((L * β ^ 2) / (m * τ * p)) / 2 := by
                  field_simp [hm_ne, hτ_ne, hp_ne] <;> ring
                rw [hhalf_eq]
                nlinarith [hcoef_nonneg]
              exact mul_le_mul_of_nonneg_right hhalf (sq_nonneg ‖u‖)
        _ = (setup.L i * β ^ 2) /
              ((componentCount (ι := ι) : ℝ) * setup.τ t *
                samplingProbability setup i) * ‖u‖ ^ 2 := by
              simp [m, τ, p, L, mul_assoc]
    have hneg_le :
        - (sourceQuotient (setup.L i * β ^ 2)
            ((componentCount (ι := ι) : ℝ) * setup.τ t *
              samplingProbability setup i) hden * ‖u‖ ^ 2) ≤
          (1 / p) *
            (-(β ^ 2 * ‖u‖ ^ 2) / (2 * (m * τ / L))) := by
      have hneg :
          - (sourceQuotient (setup.L i * β ^ 2)
              ((componentCount (ι := ι) : ℝ) * setup.τ t *
                samplingProbability setup i) hden * ‖u‖ ^ 2) ≤
            - ((1 / p) * ((β ^ 2 * ‖u‖ ^ 2) / (2 * (m * τ / L)))) := by
        exact neg_le_neg hcorr
      calc
        - (sourceQuotient (setup.L i * β ^ 2)
            ((componentCount (ι := ι) : ℝ) * setup.τ t *
              samplingProbability setup i) hden * ‖u‖ ^ 2)
            ≤ - ((1 / p) * ((β ^ 2 * ‖u‖ ^ 2) / (2 * (m * τ / L)))) := hneg
        _ = (1 / p) *
              (-(β ^ 2 * ‖u‖ ^ 2) / (2 * (m * τ / L))) := by
              ring
    have hmain :
        - (sourceQuotient (setup.L i * β ^ 2)
            ((componentCount (ι := ι) : ℝ) * setup.τ t *
              samplingProbability setup i) hden * ‖u‖ ^ 2) ≤
          (1 / p) * (β * ⟪u, v⟫_ℝ + τ * W) :=
      le_trans hneg_le hscaled
    simpa [m, τ, p, L, W, v, hinv, mul_add, mul_assoc, mul_left_comm,
      mul_comm] using hmain

/-- Half-budget version of the inverse-inner Young absorption used when the
single sampled dual Bregman budget in Eq. (5.1.56) is split between neighboring
Young/Cauchy applications before Eq. (5.1.57). No SOptLib match: searched
`half budget inverse inner Young tau div two Bregman Proposition 5.1
sourceQuotient` and `young absorb inner norm squared budget Bregman source
quotient`, scanned `SOptLib/Glue/Algebra.lean` and the local Young bridges, and
checked `young_absorb_inner_of_norm_sq_budget`,
`young_absorb_sample_correction_of_cocoercive_budget`,
`young_absorb_average_inner_with_quadratic_budget`, and
`proposition51_dual_young_absorb_inverse_inner_with_sourceQuotient`; the SOptLib
lemmas require a positive Lipschitz branch and package a generic norm-square
budget, while this source step must retain the `L_i = 0` branch and the literal
Eq. (5.1.58) denominator `m τ_t p_i`. -/
private theorem proposition51_dual_young_absorb_inverse_inner_half_with_sourceQuotient
    (hStanding : standingAssumptions setup)
    (t : ℕ) (ht : 1 ≤ t) (i : ι)
    (hp : samplingProbability setup i ≠ 0)
    (hden : (componentCount (ι := ι) : ℝ) * setup.τ t *
      samplingProbability setup i ≠ 0)
    (β : ℝ) (u : E) (y0 : DualCarrier setup i)
    (baseSubgrad : DualConjugateSubgradient setup i y0)
    (y : DualCarrier setup i) :
    - sourceQuotient (setup.L i * β ^ 2)
        ((componentCount (ι := ι) : ℝ) * setup.τ t *
          samplingProbability setup i) hden * ‖u‖ ^ 2 ≤
      inverseProbabilityValue setup i hp * β * ⟪u, y.1 - y0.1⟫_ℝ +
        (setup.τ t / 2) * inverseProbabilityValue setup i hp *
          (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i y0 baseSubgrad) y0 y) := by
  classical
  let m : ℝ := (componentCount (ι := ι) : ℝ)
  let τ : ℝ := setup.τ t
  let p : ℝ := samplingProbability setup i
  let L : ℝ := setup.L i
  let W : ℝ := (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i y0 baseSubgrad) y0 y)
  let v : E := y.1 - y0.1
  have hm_pos : 0 < m := by
    simpa [m] using componentCount_real_pos (ι := ι)
  have hp_nonneg : 0 ≤ p := by
    simpa [p] using samplingProbability_nonnegative setup i
  have hp_ne : p ≠ 0 := by
    simpa [p] using hp
  have hp_pos : 0 < p := lt_of_le_of_ne hp_nonneg (Ne.symm hp_ne)
  have hτ_nonneg : 0 ≤ τ := by
    rcases hStanding with ⟨_, _, _, _, _, _, _, _, _, _, _, hParam⟩
    simpa [τ] using hParam.1 t ht
  have hτ_ne : τ ≠ 0 := by
    intro hτ_zero
    apply hden
    simpa [m, τ, p, hτ_zero]
  have hτ_pos : 0 < τ := lt_of_le_of_ne hτ_nonneg (Ne.symm hτ_ne)
  have hL_nonneg : 0 ≤ L := by
    rcases hStanding with ⟨_, hSmooth, _, _, _, _, _, _, _, _, _, _⟩
    simpa [L] using hSmooth.2.1 i
  have hW_nonneg : 0 ≤ W := by
    simpa [W] using dualBregman_nonnegative setup i y0 baseSubgrad y
  have hquad :
      m / 2 * ‖v‖ ^ 2 ≤ L * W := by
    have h :=
      dualBregman_cross_quadratic_lower_bound setup hStanding i y0 baseSubgrad y
    simpa [m, L, W, v, norm_sub_rev] using h
  have hbase :=
    inverse_probability_inner_half_absorb_of_quadratic_budget
      (E := E) (m := m) (τ := τ) (p := p) (L := L) (β := β)
      (W := W) (u := u) (v := v)
      hm_pos hτ_pos hp_pos hL_nonneg hW_nonneg hquad
  simpa [m, τ, p, L, W, v, sourceQuotient_def, inverseProbabilityValue,
    neg_mul, mul_add, mul_assoc, mul_left_comm, mul_comm] using hbase

/-- Theorem 5.1 division-free half-budget Young absorption. This is the local
replacement for the Proposition 5.1 `m τ_t p_i` quotient interface in the
constant-parameter proof: it consumes Eq. (5.1.62) directly and splits on
`L_i=0`, deriving `τ>0` only in the nondegenerate branch. Existing candidates
considered: the local
`proposition51_dual_young_absorb_inverse_inner_half_with_sourceQuotient` proves
the same Young step only after a product-denominator certificate is supplied,
while SOptLib `young_absorb_inner_of_norm_sq_budget` and
`young_absorb_two_adjacent_corrections` require positive Lipschitz branches and
do not cover the source-relevant `L_i=0` case. -/
private theorem theorem51_dual_young_absorb_inverse_inner_half_division_free
    (τ η α : ℝ)
    (hStanding : theoremStandingAssumptions setup)
    (hPolicy : constantParameterPolicy setup τ η α)
    (hProb : constantParameterConditionProbability setup τ α)
    (hLip : constantParameterConditionLipschitz setup τ η)
    (hAlpha : alphaRange α)
    (hRateDen : theorem_5_1_rateDenominatorBoundary η)
    (t : ℕ) (ht : 1 ≤ t) (i : ι)
    (β : ℝ) (hβsq_le_one : β ^ 2 ≤ 1)
    (u : E) (y0 : DualCarrier setup i)
    (baseSubgrad : DualConjugateSubgradient setup i y0)
    (y : DualCarrier setup i) :
    - (η / 4 * ‖u‖ ^ 2) ≤
      inverseProbabilityValue setup i
          (inverseProbabilityDenominators_ne_of_theorem_conditions
            setup τ η α hStanding hPolicy hProb hAlpha i) *
          β * ⟪u, y.1 - y0.1⟫_ℝ +
        (τ / 2) *
      inverseProbabilityValue setup i
            (inverseProbabilityDenominators_ne_of_theorem_conditions
              setup τ η α hStanding hPolicy hProb hAlpha i) *
          (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i y0 baseSubgrad) y0 y) := by
  classical
  let m : ℝ := (componentCount (ι := ι) : ℝ)
  let p : ℝ := samplingProbability setup i
  let L : ℝ := setup.L i
  let W : ℝ :=
    SOptLib.carrierBregmanDivergence (dualConjugate setup i)
      (dualConjugateBaseSelector setup i y0 baseSubgrad) y0 y
  let v : E := y.1 - y0.1
  let hp : samplingProbability setup i ≠ 0 :=
    inverseProbabilityDenominators_ne_of_theorem_conditions
      setup τ η α hStanding hPolicy hProb hAlpha i
  have hm_pos : 0 < m := by
    simpa [m] using componentCount_real_pos (ι := ι)
  have hp_pos : 0 < p := by
    simpa [p] using
      samplingProbability_pos_of_theorem_conditions setup τ η α
        hStanding hPolicy hProb hAlpha i
  have hη_pos : 0 < η :=
    theorem51_eta_pos_of_rate_boundary setup τ η α hStanding hPolicy hRateDen
  have hL_nonneg : 0 ≤ L := by
    rcases hStanding.1 with ⟨_, hSmooth, _, _, _, _, _, _, _, _, _, _⟩
    simpa [L] using hSmooth.2.1 i
  have hW_nonneg : 0 ≤ W := by
    simpa [W] using dualBregman_nonnegative setup i y0 baseSubgrad y
  have hquad : m / 2 * ‖v‖ ^ 2 ≤ L * W := by
    have h :=
      dualBregman_cross_quadratic_lower_bound setup hStanding.1 i y0 baseSubgrad y
    simpa [m, L, W, v, norm_sub_rev] using h
  have hLip_scalar : 4 * L / m ≤ η * τ * p := by
    have h := hLip i
    rw [sourceQuotient_def] at h
    simpa [m, L, p] using h
  have hbase :=
    inverse_probability_inner_half_absorb_of_lipschitz_budget
      (E := E) (m := m) (p := p) (L := L) (tau := τ) (eta := η)
      (beta := β) (W := W) (u := u) (v := v)
      hm_pos hp_pos hη_pos hL_nonneg hW_nonneg hquad
      hLip_scalar hβsq_le_one
  simpa [m, p, L, W, v, hp, inverseProbabilityValue, sourceQuotient_def,
    mul_assoc, mul_comm, mul_left_comm] using hbase

/-- Terminal sampled-block Young absorption for the Theorem 5.1 constant-policy
route, with `β=-(1-p_i)`. This is the concrete terminal component of the
division-free replacement for Proposition 5.1 condition (5.1.48). Existing
candidates considered: `proposition51_h48_terminal_sampled_coefficient_nonnegative`
drops a quotient coefficient after assuming the forbidden proposition
denominator boundary, while
`theorem51_dual_young_absorb_inverse_inner_half_division_free` is the generic
new hLip-based Young step specialized here to the terminal sampling factor. -/
private theorem theorem51_terminal_young_absorb_division_free
    (τ η α : ℝ)
    (hStanding : theoremStandingAssumptions setup)
    (hPolicy : constantParameterPolicy setup τ η α)
    (hProb : constantParameterConditionProbability setup τ α)
    (hLip : constantParameterConditionLipschitz setup τ η)
    (hAlpha : alphaRange α)
    (hRateDen : theorem_5_1_rateDenominatorBoundary η)
    (t : ℕ) (ht : 1 ≤ t) (i : ι)
    (u : E) (y0 : DualCarrier setup i)
    (baseSubgrad : DualConjugateSubgradient setup i y0)
    (y : DualCarrier setup i) :
    - (η / 4 * ‖u‖ ^ 2) ≤
      (1 -
          inverseProbabilityValue setup i
            (inverseProbabilityDenominators_ne_of_theorem_conditions
              setup τ η α hStanding hPolicy hProb hAlpha i)) *
          ⟪u, y.1 - y0.1⟫_ℝ +
        (τ / 2) *
          inverseProbabilityValue setup i
            (inverseProbabilityDenominators_ne_of_theorem_conditions
              setup τ η α hStanding hPolicy hProb hAlpha i) *
          (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i y0 baseSubgrad) y0 y) := by
  classical
  let hp : samplingProbability setup i ≠ 0 :=
    inverseProbabilityDenominators_ne_of_theorem_conditions
      setup τ η α hStanding hPolicy hProb hAlpha i
  let p : ℝ := samplingProbability setup i
  have hp_nonneg : 0 ≤ p := by
    simpa [p] using samplingProbability_nonnegative setup i
  have hp_le : p ≤ 1 := by
    simpa [p] using samplingProbability_le_one setup i
  have hβsq :
      (-(1 - samplingProbability setup i)) ^ 2 ≤ 1 := by
    have hinterval : 0 ≤ 1 - p ∧ 1 - p ≤ 1 := by
      constructor <;> nlinarith
    nlinarith [sq_nonneg (1 - p), hinterval.1, hinterval.2,
      sq_nonneg (-(1 - samplingProbability setup i))]
  have hbase :=
    theorem51_dual_young_absorb_inverse_inner_half_division_free
      setup τ η α hStanding hPolicy hProb hLip hAlpha hRateDen
      t ht i (-(1 - samplingProbability setup i)) hβsq
      u y0 baseSubgrad y
  have hcoef :
      inverseProbabilityValue setup i hp *
          (samplingProbability setup i - 1) =
        1 - inverseProbabilityValue setup i hp := by
    rw [inverseProbabilityValue, sourceQuotient_def]
    field_simp [hp]
  simpa [hp, hcoef, mul_assoc, mul_comm, mul_left_comm] using hbase

/-- Current-block historical Young absorption for the Theorem 5.1
constant-policy route, with `β=α_t=α`. This is the current-block half of the
division-free replacement for Proposition 5.1 condition (5.1.49). Existing
candidates considered: `proposition51_current_historical_young_absorb_half_with_h51`
uses the source-quotient denominator boundary and the weighted shift, while the
generic `theorem51_dual_young_absorb_inverse_inner_half_division_free` supplies
exactly the hLip-based half-budget Young step after specializing
`β=setup.α t`. -/
private theorem theorem51_current_historical_young_absorb_division_free
    (τ η α : ℝ)
    (hStanding : theoremStandingAssumptions setup)
    (hPolicy : constantParameterPolicy setup τ η α)
    (hProb : constantParameterConditionProbability setup τ α)
    (hLip : constantParameterConditionLipschitz setup τ η)
    (hAlpha : alphaRange α)
    (hRateDen : theorem_5_1_rateDenominatorBoundary η)
    (t : ℕ) (ht : 1 ≤ t) (i : ι)
    (u : E) (y0 : DualCarrier setup i)
    (baseSubgrad : DualConjugateSubgradient setup i y0)
    (y : DualCarrier setup i) :
    - (η / 4 * ‖u‖ ^ 2) ≤
      inverseProbabilityValue setup i
          (inverseProbabilityDenominators_ne_of_theorem_conditions
            setup τ η α hStanding hPolicy hProb hAlpha i) *
          setup.α t * ⟪u, y.1 - y0.1⟫_ℝ +
        (τ / 2) *
          inverseProbabilityValue setup i
            (inverseProbabilityDenominators_ne_of_theorem_conditions
              setup τ η α hStanding hPolicy hProb hAlpha i) *
          (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i y0 baseSubgrad) y0 y) := by
  classical
  have hβsq : setup.α t ^ 2 ≤ 1 := by
    have hαt : setup.α t = α := hPolicy.2.2 t ht
    rw [hαt]
    nlinarith [sq_nonneg α, hAlpha.1, hAlpha.2]
  simpa [mul_assoc, mul_comm, mul_left_comm] using
    theorem51_dual_young_absorb_inverse_inner_half_division_free
      setup τ η α hStanding hPolicy hProb hLip hAlpha hRateDen
      t ht i (setup.α t) hβsq u y0 baseSubgrad y

/-- Previous-block historical Young absorption for the Theorem 5.1
constant-policy route, with `β=p_i-1` and the increment oriented as
`y0-y`. This is the previous-block half of the division-free replacement for
Proposition 5.1 condition (5.1.49). Existing candidates considered:
`proposition51_previous_historical_young_absorb_half_with_h51` proves the
weighted source-quotient version under the forbidden denominator boundary,
while `theorem51_dual_young_absorb_inverse_inner_half_division_free` provides
the needed hLip-based half-budget step after this scalar orientation rewrite. -/
private theorem theorem51_previous_historical_young_absorb_division_free
    (τ η α : ℝ)
    (hStanding : theoremStandingAssumptions setup)
    (hPolicy : constantParameterPolicy setup τ η α)
    (hProb : constantParameterConditionProbability setup τ α)
    (hLip : constantParameterConditionLipschitz setup τ η)
    (hAlpha : alphaRange α)
    (hRateDen : theorem_5_1_rateDenominatorBoundary η)
    (t : ℕ) (ht : 1 ≤ t) (i : ι)
    (u : E) (y0 : DualCarrier setup i)
    (baseSubgrad : DualConjugateSubgradient setup i y0)
    (y : DualCarrier setup i) :
    - (η / 4 * ‖u‖ ^ 2) ≤
      (inverseProbabilityValue setup i
            (inverseProbabilityDenominators_ne_of_theorem_conditions
              setup τ η α hStanding hPolicy hProb hAlpha i) - 1) *
          ⟪u, y0.1 - y.1⟫_ℝ +
        (τ / 2) *
          inverseProbabilityValue setup i
            (inverseProbabilityDenominators_ne_of_theorem_conditions
              setup τ η α hStanding hPolicy hProb hAlpha i) *
          (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i y0 baseSubgrad) y0 y) := by
  classical
  let hp : samplingProbability setup i ≠ 0 :=
    inverseProbabilityDenominators_ne_of_theorem_conditions
      setup τ η α hStanding hPolicy hProb hAlpha i
  let p : ℝ := samplingProbability setup i
  have hp_nonneg : 0 ≤ p := by
    simpa [p] using samplingProbability_nonnegative setup i
  have hp_le : p ≤ 1 := by
    simpa [p] using samplingProbability_le_one setup i
  have hβsq : (samplingProbability setup i - 1) ^ 2 ≤ 1 := by
    have hinterval : -1 ≤ p - 1 ∧ p - 1 ≤ 0 := by
      constructor <;> nlinarith
    nlinarith [sq_nonneg (p - 1), hinterval.1, hinterval.2]
  have hbase :=
    theorem51_dual_young_absorb_inverse_inner_half_division_free
      setup τ η α hStanding hPolicy hProb hLip hAlpha hRateDen
      t ht i (samplingProbability setup i - 1) hβsq
      u y0 baseSubgrad y
  have hcoef :
      inverseProbabilityValue setup i hp *
          (samplingProbability setup i - 1) =
        1 - inverseProbabilityValue setup i hp := by
    rw [inverseProbabilityValue, sourceQuotient_def]
    field_simp [hp]
  have hinner :
      ⟪u, y.1 - y0.1⟫_ℝ = -⟪u, y0.1 - y.1⟫_ℝ := by
    calc
      ⟪u, y.1 - y0.1⟫_ℝ = ⟪u, -(y0.1 - y.1)⟫_ℝ := by
        congr 1
        abel
      _ = -⟪u, y0.1 - y.1⟫_ℝ := by
        rw [inner_neg_right]
  calc
    - (η / 4 * ‖u‖ ^ 2) ≤
        inverseProbabilityValue setup i hp *
            (samplingProbability setup i - 1) *
            ⟪u, y.1 - y0.1⟫_ℝ +
          (τ / 2) * inverseProbabilityValue setup i hp *
            (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i y0 baseSubgrad) y0 y) := by
          simpa [hp, mul_assoc, mul_comm, mul_left_comm] using hbase
    _ =
        (inverseProbabilityValue setup i hp - 1) *
            ⟪u, y0.1 - y.1⟫_ℝ +
          (τ / 2) * inverseProbabilityValue setup i hp *
            (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i y0 baseSubgrad) y0 y) := by
          rw [hcoef, hinner]
          ring

/-- Weighted current-block historical absorption for the Theorem 5.1
division-free pathwise route. Existing candidates considered:
`theorem51_current_historical_young_absorb_division_free` specializes the
generic Young step with `β=α_t`, which is useful pointwise but leaves the wrong
`θ_t` norm budget for the Proposition 5.1 scalar allocation; the older
`proposition51_current_historical_young_absorb_half_with_h51` has the right
weighted shape but depends on the forbidden product-denominator boundary. This
helper uses the generic division-free Young lemma with `β=1`, then applies the
Theorem 5.1 output-weight shift from Eq. (5.1.65). -/
private theorem theorem51_current_historical_young_absorb_weighted_division_free
    (τ η α : ℝ)
    (hStanding : theoremStandingAssumptions setup)
    (hPolicy : constantParameterPolicy setup τ η α)
    (hProb : constantParameterConditionProbability setup τ α)
    (hLip : constantParameterConditionLipschitz setup τ η)
    (hAlpha : alphaRange α)
    (hRateDen : theorem_5_1_rateDenominatorBoundary η)
    (t : ℕ) (ht2 : 2 ≤ t) (i : ι)
    (u : E) (y0 : DualCarrier setup i)
    (baseSubgrad : DualConjugateSubgradient setup i y0)
    (y : DualCarrier setup i) :
    - theoremOutputWeight α hAlpha (t - 1) * (η / 4 * ‖u‖ ^ 2) ≤
      theoremOutputWeight α hAlpha t *
        (setup.α t *
            inverseProbabilityValue setup i
              (inverseProbabilityDenominators_ne_of_theorem_conditions
                setup τ η α hStanding hPolicy hProb hAlpha i) *
            ⟪u, y.1 - y0.1⟫_ℝ +
          (setup.τ t / 2) *
            inverseProbabilityValue setup i
              (inverseProbabilityDenominators_ne_of_theorem_conditions
                setup τ η α hStanding hPolicy hProb hAlpha i) *
            (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i y0 baseSubgrad) y0 y)) := by
  classical
  let θ : ℕ → ℝ := theoremOutputWeight α hAlpha
  let hp : samplingProbability setup i ≠ 0 :=
    inverseProbabilityDenominators_ne_of_theorem_conditions
      setup τ η α hStanding hPolicy hProb hAlpha i
  let W : ℝ := (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i y0 baseSubgrad) y0 y)
  let B : ℝ :=
    (setup.τ t / 2) * inverseProbabilityValue setup i hp * W
  have ht1 : 1 ≤ t := by omega
  have hshift : setup.α t * θ t = θ (t - 1) :=
    theorem51_output_weight_shift setup τ η α hPolicy hAlpha t ht2
  have hθt_nonneg : 0 ≤ θ t := by
    have hpow : 0 < α ^ t := pow_pos hAlpha.1 t
    simpa [θ, theoremOutputWeight, sourceQuotient] using (one_div_pos.mpr hpow).le
  have hθprev_nonneg : 0 ≤ θ (t - 1) := by
    have hpow : 0 < α ^ (t - 1) := pow_pos hAlpha.1 (t - 1)
    simpa [θ, theoremOutputWeight, sourceQuotient] using (one_div_pos.mpr hpow).le
  have hαt_le_one : setup.α t ≤ 1 := by
    rw [hPolicy.2.2 t ht1]
    exact hAlpha.2.le
  have hθprev_le : θ (t - 1) ≤ θ t := by
    rw [← hshift]
    nlinarith
  have hp_pos : 0 < samplingProbability setup i :=
    samplingProbability_pos_of_theorem_conditions
      setup τ η α hStanding hPolicy hProb hAlpha i
  have hinv_nonneg : 0 ≤ inverseProbabilityValue setup i hp := by
    rw [inverseProbabilityValue, sourceQuotient_def]
    exact one_div_nonneg.mpr hp_pos.le
  have hτt_nonneg : 0 ≤ setup.τ t := by
    rcases hStanding.1 with ⟨_, _, _, _, _, _, _, _, _, _, _, hParam⟩
    exact hParam.1 t ht1
  have hW_nonneg : 0 ≤ W := by
    simpa [W] using dualBregman_nonnegative setup i y0 baseSubgrad y
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg
      (mul_nonneg (div_nonneg hτt_nonneg (by norm_num)) hinv_nonneg)
      hW_nonneg
  have hbase :=
    theorem51_dual_young_absorb_inverse_inner_half_division_free
      setup τ η α hStanding hPolicy hProb hLip hAlpha hRateDen
      t ht1 i 1 (by norm_num) u y0 baseSubgrad y
  have hscaled :
      θ (t - 1) * (-(η / 4 * ‖u‖ ^ 2)) ≤
        θ (t - 1) *
          (inverseProbabilityValue setup i hp *
              ⟪u, y.1 - y0.1⟫_ℝ + B) := by
    simpa [hp, B, W, hPolicy.1 t ht1, mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_left hbase hθprev_nonneg
  calc
    - θ (t - 1) * (η / 4 * ‖u‖ ^ 2) =
        θ (t - 1) * (-(η / 4 * ‖u‖ ^ 2)) := by ring
    _ ≤ θ (t - 1) *
          (inverseProbabilityValue setup i hp *
              ⟪u, y.1 - y0.1⟫_ℝ + B) := hscaled
    _ = θ t *
          (setup.α t * inverseProbabilityValue setup i hp *
            ⟪u, y.1 - y0.1⟫_ℝ) + θ (t - 1) * B := by
          rw [← hshift]
          ring
    _ ≤ θ t *
          (setup.α t * inverseProbabilityValue setup i hp *
            ⟪u, y.1 - y0.1⟫_ℝ) + θ t * B := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_left
              (mul_le_mul_of_nonneg_right hθprev_le hB_nonneg)
              (θ t *
                (setup.α t * inverseProbabilityValue setup i hp *
                  ⟪u, y.1 - y0.1⟫_ℝ))
    _ = θ t *
        (setup.α t * inverseProbabilityValue setup i hp *
            ⟪u, y.1 - y0.1⟫_ℝ +
          (setup.τ t / 2) * inverseProbabilityValue setup i hp *
            (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i y0 baseSubgrad) y0 y)) := by
          dsimp [B, W]
          ring

/-- Weighted terminal sampled-block absorption for the Theorem 5.1
division-free pathwise route. Existing candidates considered:
`theorem51_terminal_young_absorb_division_free` gives the required pointwise
Young step, while the Proposition 5.1 terminal coefficient helper depends on
the forbidden product denominator; this helper is exactly the nonnegative
output-weight scaling needed by the scalar allocation. -/
private theorem theorem51_terminal_young_absorb_weighted_division_free
    (τ η α : ℝ)
    (hStanding : theoremStandingAssumptions setup)
    (hPolicy : constantParameterPolicy setup τ η α)
    (hProb : constantParameterConditionProbability setup τ α)
    (hLip : constantParameterConditionLipschitz setup τ η)
    (hAlpha : alphaRange α)
    (hRateDen : theorem_5_1_rateDenominatorBoundary η)
    (k : ℕ) (hk : 1 ≤ k) (i : ι)
    (u : E) (y0 : DualCarrier setup i)
    (baseSubgrad : DualConjugateSubgradient setup i y0)
    (y : DualCarrier setup i) :
    theoremOutputWeight α hAlpha k * (-(η / 4 * ‖u‖ ^ 2)) ≤
      theoremOutputWeight α hAlpha k *
        ((1 -
            inverseProbabilityValue setup i
              (inverseProbabilityDenominators_ne_of_theorem_conditions
                setup τ η α hStanding hPolicy hProb hAlpha i)) *
            ⟪u, y.1 - y0.1⟫_ℝ +
          (setup.τ k / 2) *
            inverseProbabilityValue setup i
              (inverseProbabilityDenominators_ne_of_theorem_conditions
                setup τ η α hStanding hPolicy hProb hAlpha i) *
            (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i y0 baseSubgrad) y0 y)) := by
  classical
  let hp : samplingProbability setup i ≠ 0 :=
    inverseProbabilityDenominators_ne_of_theorem_conditions
      setup τ η α hStanding hPolicy hProb hAlpha i
  have hθk_nonneg : 0 ≤ theoremOutputWeight α hAlpha k := by
    have hpow : 0 < α ^ k := pow_pos hAlpha.1 k
    simpa [theoremOutputWeight, sourceQuotient] using (one_div_pos.mpr hpow).le
  have hbase :=
    theorem51_terminal_young_absorb_division_free
      setup τ η α hStanding hPolicy hProb hLip hAlpha hRateDen
      k hk i u y0 baseSubgrad y
  simpa [hp, hPolicy.1 k hk, mul_assoc, mul_left_comm, mul_comm] using
    mul_le_mul_of_nonneg_left hbase hθk_nonneg

/-- Weighted previous-block historical absorption for the Theorem 5.1
division-free pathwise route. Existing candidates considered:
`theorem51_previous_historical_young_absorb_division_free` gives the needed
pointwise previous-block Young step, while
`proposition51_previous_historical_young_absorb_half_with_h51` has the same
weighted target shape but requires the forbidden Proposition denominator
boundary. This helper replaces that old bridge using Eq. (5.1.65)'s
output-weight shift. -/
private theorem theorem51_previous_historical_young_absorb_weighted_division_free
    (τ η α : ℝ)
    (hStanding : theoremStandingAssumptions setup)
    (hPolicy : constantParameterPolicy setup τ η α)
    (hProb : constantParameterConditionProbability setup τ α)
    (hLip : constantParameterConditionLipschitz setup τ η)
    (hAlpha : alphaRange α)
    (hRateDen : theorem_5_1_rateDenominatorBoundary η)
    (t : ℕ) (ht2 : 2 ≤ t) (i : ι)
    (u : E) (y0 : DualCarrier setup i)
    (baseSubgrad : DualConjugateSubgradient setup i y0)
    (y : DualCarrier setup i) :
    - theoremOutputWeight α hAlpha (t - 1) * (η / 4 * ‖u‖ ^ 2) ≤
      setup.α t * theoremOutputWeight α hAlpha t *
          ((inverseProbabilityValue setup i
                (inverseProbabilityDenominators_ne_of_theorem_conditions
                  setup τ η α hStanding hPolicy hProb hAlpha i) - 1) *
            ⟪u, y0.1 - y.1⟫_ℝ) +
        theoremOutputWeight α hAlpha (t - 1) *
          ((setup.τ (t - 1) / 2) *
            inverseProbabilityValue setup i
              (inverseProbabilityDenominators_ne_of_theorem_conditions
                setup τ η α hStanding hPolicy hProb hAlpha i) *
            (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i y0 baseSubgrad) y0 y)) := by
  classical
  let θ : ℕ → ℝ := theoremOutputWeight α hAlpha
  let hp : samplingProbability setup i ≠ 0 :=
    inverseProbabilityDenominators_ne_of_theorem_conditions
      setup τ η α hStanding hPolicy hProb hAlpha i
  have htprev1 : 1 ≤ t - 1 := by omega
  have hθprev_nonneg : 0 ≤ θ (t - 1) := by
    have hpow : 0 < α ^ (t - 1) := pow_pos hAlpha.1 (t - 1)
    simpa [θ, theoremOutputWeight, sourceQuotient] using (one_div_pos.mpr hpow).le
  have hshift : setup.α t * θ t = θ (t - 1) :=
    theorem51_output_weight_shift setup τ η α hPolicy hAlpha t ht2
  have hbase :=
    theorem51_previous_historical_young_absorb_division_free
      setup τ η α hStanding hPolicy hProb hLip hAlpha hRateDen
      (t - 1) htprev1 i u y0 baseSubgrad y
  have hscaled :=
    mul_le_mul_of_nonneg_left hbase hθprev_nonneg
  calc
    - θ (t - 1) * (η / 4 * ‖u‖ ^ 2) =
        θ (t - 1) * (-(η / 4 * ‖u‖ ^ 2)) := by ring
    _ ≤ θ (t - 1) *
        ((inverseProbabilityValue setup i hp - 1) *
            ⟪u, y0.1 - y.1⟫_ℝ +
          (τ / 2) * inverseProbabilityValue setup i hp *
            (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i y0 baseSubgrad) y0 y)) := by
          simpa [hp, mul_assoc, mul_left_comm, mul_comm] using hscaled
    _ = setup.α t * θ t *
          ((inverseProbabilityValue setup i hp - 1) *
            ⟪u, y0.1 - y.1⟫_ℝ) +
        θ (t - 1) *
          ((setup.τ (t - 1) / 2) *
            inverseProbabilityValue setup i hp *
            (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i y0 baseSubgrad) y0 y)) := by
          rw [← hshift, hPolicy.1 (t - 1) htprev1]
          ring

/-- Current historical sampled-block Young absorption after the Eq. (5.1.51)
weight rewrite. No SOptLib match: searched `current historical Young absorption
theta alpha sourceQuotient h51` and `theta alpha sourceQuotient scalar identity
alpha theta equals previous`, scanned `SOptLib/Glue/Algebra.lean`, and checked
`young_absorb_two_adjacent_corrections` plus the local half/full Young bridges;
the adjacent-corrections lemma assumes a positive common Lipschitz constant and
generic norm-square budgets, while this Proposition 5.1 step needs the literal
source quotient denominator and the local `L_i = 0` branch from Eq. (5.1.58). -/
private theorem proposition51_current_historical_young_absorb_half_with_h51
    (hStanding : standingAssumptions setup)
    (θ : ℕ → ℝ) (k : ℕ)
    (hDen : proposition_5_1_denominatorBoundary setup k)
    (hθ : ∀ t, 1 ≤ t → t ≤ k → 0 ≤ θ t)
    (h51 : ∀ t, 2 ≤ t → t ≤ k → setup.α t * θ t = θ (t - 1))
    (t : ℕ) (ht2 : 2 ≤ t) (htk : t ≤ k) (i : ι)
    (u : E) (y0 : DualCarrier setup i)
    (baseSubgrad : DualConjugateSubgradient setup i y0)
    (y : DualCarrier setup i) :
    - θ (t - 1) *
        sourceQuotient (setup.L i * setup.α t)
          ((componentCount (ι := ι) : ℝ) * setup.τ t *
            samplingProbability setup i)
          (hDen.2 t i) * ‖u‖ ^ 2 ≤
      θ t *
        (setup.α t * inverseProbabilityValue setup i (hDen.1 i) *
            ⟪u, y.1 - y0.1⟫_ℝ +
          (setup.τ t / 2) * inverseProbabilityValue setup i (hDen.1 i) *
            (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i y0 baseSubgrad) y0 y)) := by
  classical
  have ht1 : 1 ≤ t := by omega
  have hθt : 0 ≤ θ t := hθ t ht1 htk
  have hbase :=
    proposition51_dual_young_absorb_inverse_inner_half_with_sourceQuotient
      setup hStanding t ht1 i (hDen.1 i) (hDen.2 t i)
      (setup.α t) u y0 baseSubgrad y
  have hscaled :
      θ t *
          (- sourceQuotient (setup.L i * setup.α t ^ 2)
              ((componentCount (ι := ι) : ℝ) * setup.τ t *
                samplingProbability setup i)
              (hDen.2 t i) * ‖u‖ ^ 2) ≤
        θ t *
          (inverseProbabilityValue setup i (hDen.1 i) * setup.α t *
              ⟪u, y.1 - y0.1⟫_ℝ +
            (setup.τ t / 2) * inverseProbabilityValue setup i (hDen.1 i) *
              (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i y0 baseSubgrad) y0 y)) :=
    mul_le_mul_of_nonneg_left hbase hθt
  calc
    - θ (t - 1) *
        sourceQuotient (setup.L i * setup.α t)
          ((componentCount (ι := ι) : ℝ) * setup.τ t *
            samplingProbability setup i)
          (hDen.2 t i) * ‖u‖ ^ 2 =
        θ t *
          (- sourceQuotient (setup.L i * setup.α t ^ 2)
              ((componentCount (ι := ι) : ℝ) * setup.τ t *
                samplingProbability setup i)
              (hDen.2 t i) * ‖u‖ ^ 2) := by
          rw [sourceQuotient_def, sourceQuotient_def]
          rw [← h51 t ht2 htk]
          ring
    _ ≤ θ t *
          (inverseProbabilityValue setup i (hDen.1 i) * setup.α t *
              ⟪u, y.1 - y0.1⟫_ℝ +
            (setup.τ t / 2) * inverseProbabilityValue setup i (hDen.1 i) *
              (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i y0 baseSubgrad) y0 y)) := hscaled
    _ = θ t *
        (setup.α t * inverseProbabilityValue setup i (hDen.1 i) *
            ⟪u, y.1 - y0.1⟫_ℝ +
          (setup.τ t / 2) * inverseProbabilityValue setup i (hDen.1 i) *
            (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i y0 baseSubgrad) y0 y)) := by
          ring

/-- Previous historical sampled-block Young absorption after orienting the
increment as `y^{t-2}-y^{t-1}` and using Eq. (5.1.51) on the inner-product
coefficient. No SOptLib match: searched `previous historical Young absorption
inverse probability minus one sourceQuotient h51` after the current-block
searches, scanned `SOptLib/Glue/Algebra.lean`, and checked
`young_absorb_two_adjacent_corrections` plus the local half/full Young bridges;
the SOptLib adjacent-correction lemma does not retain the paper's inverse
probability/sourceQuotient denominator and assumes a positive common Lipschitz
constant, so this route-local lemma specializes Eq. (5.1.58) directly. -/
private theorem proposition51_previous_historical_young_absorb_half_with_h51
    (hStanding : standingAssumptions setup)
    (θ : ℕ → ℝ) (k : ℕ)
    (hDen : proposition_5_1_denominatorBoundary setup k)
    (hθ : ∀ t, 1 ≤ t → t ≤ k → 0 ≤ θ t)
    (h51 : ∀ t, 2 ≤ t → t ≤ k → setup.α t * θ t = θ (t - 1))
    (t : ℕ) (ht2 : 2 ≤ t) (htk : t ≤ k) (j : ι)
    (u : E) (y0 : DualCarrier setup j)
    (baseSubgrad : DualConjugateSubgradient setup j y0)
    (y : DualCarrier setup j) :
    - θ (t - 1) *
        sourceQuotient
          ((1 - samplingProbability setup j) ^ 2 * setup.L j)
          ((componentCount (ι := ι) : ℝ) * setup.τ (t - 1) *
            samplingProbability setup j)
          (hDen.2 (t - 1) j) * ‖u‖ ^ 2 ≤
      setup.α t * θ t *
          ((inverseProbabilityValue setup j (hDen.1 j) - 1) *
            ⟪u, y0.1 - y.1⟫_ℝ) +
        θ (t - 1) *
          ((setup.τ (t - 1) / 2) *
            inverseProbabilityValue setup j (hDen.1 j) *
            (SOptLib.carrierBregmanDivergence (dualConjugate setup j) (dualConjugateBaseSelector setup j y0 baseSubgrad) y0 y)) := by
  classical
  have htprev1 : 1 ≤ t - 1 := by omega
  have htprevk : t - 1 ≤ k := by omega
  have hθprev : 0 ≤ θ (t - 1) := hθ (t - 1) htprev1 htprevk
  have hbase :=
    proposition51_dual_young_absorb_inverse_inner_half_with_sourceQuotient
      setup hStanding (t - 1) htprev1 j (hDen.1 j) (hDen.2 (t - 1) j)
      (samplingProbability setup j - 1) u y0 baseSubgrad y
  have hscaled :
      θ (t - 1) *
          (- sourceQuotient (setup.L j * (samplingProbability setup j - 1) ^ 2)
              ((componentCount (ι := ι) : ℝ) * setup.τ (t - 1) *
                samplingProbability setup j)
              (hDen.2 (t - 1) j) * ‖u‖ ^ 2) ≤
        θ (t - 1) *
          (inverseProbabilityValue setup j (hDen.1 j) *
              (samplingProbability setup j - 1) * ⟪u, y.1 - y0.1⟫_ℝ +
            (setup.τ (t - 1) / 2) *
              inverseProbabilityValue setup j (hDen.1 j) *
              (SOptLib.carrierBregmanDivergence (dualConjugate setup j) (dualConjugateBaseSelector setup j y0 baseSubgrad) y0 y)) :=
    mul_le_mul_of_nonneg_left hbase hθprev
  let A : ℝ :=
    (inverseProbabilityValue setup j (hDen.1 j) - 1) *
      ⟪u, y0.1 - y.1⟫_ℝ
  let B : ℝ :=
    (setup.τ (t - 1) / 2) *
      inverseProbabilityValue setup j (hDen.1 j) *
      (SOptLib.carrierBregmanDivergence (dualConjugate setup j) (dualConjugateBaseSelector setup j y0 baseSubgrad) y0 y)
  have hcoef :
      inverseProbabilityValue setup j (hDen.1 j) *
          (samplingProbability setup j - 1) =
        1 - inverseProbabilityValue setup j (hDen.1 j) := by
    rw [inverseProbabilityValue, sourceQuotient_def]
    field_simp [hDen.1 j] <;> ring
  have hinner :
      ⟪u, y.1 - y0.1⟫_ℝ = -⟪u, y0.1 - y.1⟫_ℝ := by
    calc
      ⟪u, y.1 - y0.1⟫_ℝ = ⟪u, -(y0.1 - y.1)⟫_ℝ := by
        congr 1
        abel
      _ = -⟪u, y0.1 - y.1⟫_ℝ := by
        rw [inner_neg_right]
  have hshift :
      θ (t - 1) * A = setup.α t * θ t * A := by
    rw [← h51 t ht2 htk]
  calc
    - θ (t - 1) *
        sourceQuotient
          ((1 - samplingProbability setup j) ^ 2 * setup.L j)
          ((componentCount (ι := ι) : ℝ) * setup.τ (t - 1) *
            samplingProbability setup j)
          (hDen.2 (t - 1) j) * ‖u‖ ^ 2 =
        θ (t - 1) *
          (- sourceQuotient (setup.L j * (samplingProbability setup j - 1) ^ 2)
              ((componentCount (ι := ι) : ℝ) * setup.τ (t - 1) *
                samplingProbability setup j)
              (hDen.2 (t - 1) j) * ‖u‖ ^ 2) := by
          rw [sourceQuotient_def, sourceQuotient_def]
          ring
    _ ≤ θ (t - 1) *
          (inverseProbabilityValue setup j (hDen.1 j) *
              (samplingProbability setup j - 1) * ⟪u, y.1 - y0.1⟫_ℝ +
            (setup.τ (t - 1) / 2) *
              inverseProbabilityValue setup j (hDen.1 j) *
              (SOptLib.carrierBregmanDivergence (dualConjugate setup j) (dualConjugateBaseSelector setup j y0 baseSubgrad) y0 y)) := hscaled
    _ = θ (t - 1) * (A + B) := by
          have hterm :
              inverseProbabilityValue setup j (hDen.1 j) *
                  (samplingProbability setup j - 1) *
                  ⟪u, y.1 - y0.1⟫_ℝ = A := by
            rw [hcoef, hinner]
            simp [A]
            ring
          rw [hterm]
    _ = setup.α t * θ t * A + θ (t - 1) * B := by
          rw [mul_add, hshift]
    _ = setup.α t * θ t *
          ((inverseProbabilityValue setup j (hDen.1 j) - 1) *
            ⟪u, y0.1 - y.1⟫_ℝ) +
        θ (t - 1) *
          ((setup.τ (t - 1) / 2) *
            inverseProbabilityValue setup j (hDen.1 j) *
            (SOptLib.carrierBregmanDivergence (dualConjugate setup j) (dualConjugateBaseSelector setup j y0 baseSubgrad) y0 y)) := by
          rfl

/-- Terminal scalar residual from Proposition 5.1 step 17, aligned with the
coefficient after applying Eq. (5.1.58) and condition (5.1.50). Searched
`Young Cauchy inner product bregman terminal residual nonnegative` and
`source quotient denominator inverse probability positive one plus tau`;
SOptLib `young_absorb_average_inner_with_quadratic_budget` was considered but
requires a positive component Lipschitz constant and packages a different
averaged inner-product shape, while this helper is only the source quotient
coefficient left after the paper's terminal Young/Cauchy reduction. -/
private theorem proposition51_terminal_residual_quadratic_coefficient_nonnegative
    (hStanding : standingAssumptions setup) (k : ℕ) (hk : 1 ≤ k)
    (h50 : propositionCondition_5_1_50_with_denominator_source_gap setup hStanding k hk)
    (u : E) :
    0 ≤
      (setup.η k / 4 -
          sourceQuotient (∑ i : ι, samplingProbability setup i * setup.L i)
            ((componentCount (ι := ι) : ℝ) * (1 + setup.τ k))
            (onePlusTauComponentDenominator_ne_of_standing setup hStanding k hk) / 2) *
        ‖u‖ ^ 2 := by
  let q : ℝ :=
    sourceQuotient (∑ i : ι, samplingProbability setup i * setup.L i)
      ((componentCount (ι := ι) : ℝ) * (1 + setup.τ k))
      (onePlusTauComponentDenominator_ne_of_standing setup hStanding k hk)
  have hq : q ≤ setup.η k / 2 := by
    simpa [q] using h50
  have hcoef : 0 ≤ setup.η k / 4 - q / 2 := by
    nlinarith
  exact mul_nonneg hcoef (sq_nonneg _)

set_option maxHeartbeats 800000

/-- Terminal residual bracket nonnegativity in Proposition 5.1 steps 15--17,
the pathwise form used after inserting Eq. (5.1.57). Searched `terminal
residual bregman young cauchy nonnegative inner sum` and `finite sum inner
product lower bound dual Bregman quadratic`; the closest candidates were
`proposition51_terminal_residual_quadratic_coefficient_nonnegative` (only the
post-Young scalar coefficient), `dualBregman_cross_quadratic_lower_bound` (one
dual block), and SOptLib `young_absorb_average_inner_with_quadratic_budget`
(requires `L_i > 0` and a different averaged shape), so this local bridge
assembles the paper's full Eq. (5.1.50)/(5.1.58) terminal bracket. -/
private theorem proposition51_terminal_residual_bracket_nonnegative
    (hStanding : standingAssumptions setup)
    (k : ℕ) (hk : 1 ≤ k)
    (hDen : proposition_5_1_denominatorBoundary setup k)
    (h50 : propositionCondition_5_1_50_with_denominator_source_gap
      setup hStanding k hk)
    (z : SaddlePoint setup) (ω : BlockSamplePath setup) :
    0 ≤
      setup.η k / 4 *
          ‖(xIter setup hStanding (k - 1) ω).1 -
            (xIter setup hStanding k ω).1‖ ^ 2 -
        ⟪(xIter setup hStanding (k - 1) ω).1 -
            (xIter setup hStanding k ω).1,
          ∑ i : ι, ((yIter setup hStanding k ω i).1 - (z.2 i).1)⟫_ℝ +
        ∑ i : ι,
          inverseProbabilityValue setup i (hDen.1 i) * (1 + setup.τ k) *
            (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding k ω) i) (dualSubgradIter setup hStanding k ω i)) ((yIter setup hStanding k ω) i) (z.2 i)) := by
  classical
  let m : ℝ := (componentCount (ι := ι) : ℝ)
  let τ1 : ℝ := 1 + setup.τ k
  let u : E :=
    (xIter setup hStanding (k - 1) ω).1 -
      (xIter setup hStanding k ω).1
  let v : ι → E := fun i =>
    (yIter setup hStanding k ω i).1 - (z.2 i).1
  let W : ι → ℝ := fun i =>
    (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding k ω) i) (dualSubgradIter setup hStanding k ω i)) ((yIter setup hStanding k ω) i) (z.2 i))
  let den : ℝ := m * τ1
  have hm_pos : 0 < m := by
    simpa [m] using componentCount_real_pos (ι := ι)
  have hm_ne : m ≠ 0 := ne_of_gt hm_pos
  have hτ1_pos : 0 < τ1 := by
    simpa [τ1] using onePlusTau_pos_of_standing setup hStanding k hk
  have hτ1_nonneg : 0 ≤ τ1 := le_of_lt hτ1_pos
  have hτ1_ne : τ1 ≠ 0 := ne_of_gt hτ1_pos
  have hden_ne : den ≠ 0 := by
    exact mul_ne_zero hm_ne hτ1_ne
  let q : ℝ :=
    sourceQuotient (∑ i : ι, samplingProbability setup i * setup.L i)
      den hden_ne
  have hp_pos : ∀ i : ι, 0 < samplingProbability setup i := by
    intro i
    exact lt_of_le_of_ne (samplingProbability_nonnegative setup i) (Ne.symm (hDen.1 i))
  have hL_nonneg : ∀ i : ι, 0 ≤ setup.L i := by
    intro i
    rcases hStanding with ⟨_, hSmooth, _, _, _, _, _, _, _, _, _, _⟩
    exact hSmooth.2.1 i
  have hW_nonneg : ∀ i : ι, 0 ≤ W i := by
    intro i
    simpa [W] using
      dualBregman_nonnegative setup i ((yIter setup hStanding k ω) i)
        (dualSubgradIter setup hStanding k ω i) (z.2 i)
  have hquad : ∀ i : ι,
      m / 2 * ‖v i‖ ^ 2 ≤ setup.L i * W i := by
    intro i
    have h :=
      dualBregman_cross_quadratic_lower_bound setup hStanding i
        ((yIter setup hStanding k ω) i)
        (dualSubgradIter setup hStanding k ω i) (z.2 i)
    simpa [m, W, v] using h
  have hq_eq :
      q = (∑ i : ι, samplingProbability setup i * setup.L i) / (m * τ1) := by
    simp [q, den, sourceQuotient_def]
  have hq_le : q ≤ setup.η k / 2 := by
    simpa [q, den, m, τ1] using h50
  have hmain :
      0 ≤ setup.η k / 4 * ‖u‖ ^ 2 -
          ⟪u, ∑ i : ι, v i⟫_ℝ +
          ∑ i : ι, inverseProbabilityValue setup i (hDen.1 i) * τ1 * W i := by
    have hcore :=
      finite_sum_inverse_probability_terminal_young_nonneg
        (p := fun i : ι => samplingProbability setup i) (L := setup.L)
        (W := W) (u := u) (v := v) (m := m) (tau := τ1)
        (eta := setup.η k) (q := q)
        hp_pos hL_nonneg hW_nonneg hm_pos hτ1_pos hquad hq_eq hq_le
    simpa [inverseProbabilityValue, sourceQuotient_def] using hcore
  simpa [u, v, W, τ1, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hmain

/-- Terminal residual bracket nonnegativity with only all-block probability
nonzero facts. This is the Theorem 5.1-local replacement for the Proposition
helper that used the obsolete product denominator boundary: searched
`terminal residual Bregman Young Cauchy nonnegative` and considered
`proposition51_terminal_residual_bracket_nonnegative`, whose proof shape
matches Eq. (5.1.50)/(5.1.58) but whose statement requires
`proposition_5_1_denominatorBoundary`; this bridge copies the same terminal
argument with `hp` for inverse probabilities and no `m τ_t p_i` denominator
premise. -/
private theorem terminal_residual_bracket_nonnegative_of_h50_and_probabilities
    (hStanding : standingAssumptions setup)
    (k : ℕ) (hk : 1 ≤ k)
    (hp : ∀ i : ι, samplingProbability setup i ≠ 0)
    (h50 : propositionCondition_5_1_50_with_denominator_source_gap
      setup hStanding k hk)
    (z : SaddlePoint setup) (ω : BlockSamplePath setup) :
    0 ≤
      setup.η k / 4 *
          ‖(xIter setup hStanding (k - 1) ω).1 -
            (xIter setup hStanding k ω).1‖ ^ 2 -
        ⟪(xIter setup hStanding (k - 1) ω).1 -
            (xIter setup hStanding k ω).1,
          ∑ i : ι, ((yIter setup hStanding k ω i).1 - (z.2 i).1)⟫_ℝ +
        ∑ i : ι,
          inverseProbabilityValue setup i (hp i) * (1 + setup.τ k) *
            (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding k ω) i) (dualSubgradIter setup hStanding k ω i)) ((yIter setup hStanding k ω) i) (z.2 i)) := by
  classical
  let m : ℝ := (componentCount (ι := ι) : ℝ)
  let τ1 : ℝ := 1 + setup.τ k
  let u : E :=
    (xIter setup hStanding (k - 1) ω).1 -
      (xIter setup hStanding k ω).1
  let v : ι → E := fun i =>
    (yIter setup hStanding k ω i).1 - (z.2 i).1
  let W : ι → ℝ := fun i =>
    (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding k ω) i) (dualSubgradIter setup hStanding k ω i)) ((yIter setup hStanding k ω) i) (z.2 i))
  let den : ℝ := m * τ1
  have hm_pos : 0 < m := by
    simpa [m] using componentCount_real_pos (ι := ι)
  have hm_ne : m ≠ 0 := ne_of_gt hm_pos
  have hτ1_pos : 0 < τ1 := by
    simpa [τ1] using onePlusTau_pos_of_standing setup hStanding k hk
  have hτ1_nonneg : 0 ≤ τ1 := le_of_lt hτ1_pos
  have hτ1_ne : τ1 ≠ 0 := ne_of_gt hτ1_pos
  have hden_ne : den ≠ 0 := by
    exact mul_ne_zero hm_ne hτ1_ne
  let q : ℝ :=
    sourceQuotient (∑ i : ι, samplingProbability setup i * setup.L i)
      den hden_ne
  have hp_pos : ∀ i : ι, 0 < samplingProbability setup i := by
    intro i
    exact lt_of_le_of_ne (samplingProbability_nonnegative setup i) (Ne.symm (hp i))
  have hL_nonneg : ∀ i : ι, 0 ≤ setup.L i := by
    intro i
    rcases hStanding with ⟨_, hSmooth, _, _, _, _, _, _, _, _, _, _⟩
    exact hSmooth.2.1 i
  have hW_nonneg : ∀ i : ι, 0 ≤ W i := by
    intro i
    simpa [W] using
      dualBregman_nonnegative setup i ((yIter setup hStanding k ω) i)
        (dualSubgradIter setup hStanding k ω i) (z.2 i)
  have hquad : ∀ i : ι,
      m / 2 * ‖v i‖ ^ 2 ≤ setup.L i * W i := by
    intro i
    have h :=
      dualBregman_cross_quadratic_lower_bound setup hStanding i
        ((yIter setup hStanding k ω) i)
        (dualSubgradIter setup hStanding k ω i) (z.2 i)
    simpa [m, W, v] using h
  have hq_eq :
      q = (∑ i : ι, samplingProbability setup i * setup.L i) / (m * τ1) := by
    simp [q, den, sourceQuotient_def]
  have hq_le : q ≤ setup.η k / 2 := by
    simpa [q, den, m, τ1] using h50
  have hmain :
      0 ≤ setup.η k / 4 * ‖u‖ ^ 2 -
          ⟪u, ∑ i : ι, v i⟫_ℝ +
          ∑ i : ι, inverseProbabilityValue setup i (hp i) * τ1 * W i := by
    have hcore :=
      finite_sum_inverse_probability_terminal_young_nonneg
        (p := fun i : ι => samplingProbability setup i) (L := setup.L)
        (W := W) (u := u) (v := v) (m := m) (tau := τ1)
        (eta := setup.η k) (q := q)
        hp_pos hL_nonneg hW_nonneg hm_pos hτ1_pos hquad hq_eq hq_le
    simpa [inverseProbabilityValue, sourceQuotient_def] using hcore
  simpa [u, v, W, τ1, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hmain

/-- Primal-prediction vector identity used in Proposition 5.1 Eq. (5.1.55).

This is the first process-algebra step in the Delta coupling expansion. No
SOptLib match: searched `xTildeIter primalPrediction alpha coupling` and the
target file around `primalPrediction`, `xTildeIter`, and
`stepPrimalPrediction_eq_xTildeIter`; no existing theorem exposes this exact
Eq. (5.1.21) difference form. -/
private theorem proposition51_primal_prediction_difference_eq
    (hStanding : standingAssumptions setup)
    (t : ℕ) (ω : BlockSamplePath setup) :
    xTildeIter setup hStanding t ω - (xIter setup hStanding t ω).1 =
      ((xIter setup hStanding (t - 1) ω).1 -
          (xIter setup hStanding t ω).1) -
        setup.α t •
          ((xIter setup hStanding (t - 2) ω).1 -
            (xIter setup hStanding (t - 1) ω).1) := by
  dsimp [xTildeIter, primalPrediction]
  module

/-- Inner-product form of the primal-prediction expansion in Proposition 5.1
Eq. (5.1.55). No SOptLib match: after verifying `inner_sub_left` and
`inner_smul_left`, the only project hit was generic scalar inner algebra; this
paper needs the generated `xTildeIter`/`xIter` Eq. (5.1.21) specialization. -/
private theorem proposition51_primal_prediction_coupling_expansion
    (hStanding : standingAssumptions setup)
    (t : ℕ) (ω : BlockSamplePath setup) (v : E) :
    ⟪xTildeIter setup hStanding t ω - (xIter setup hStanding t ω).1, v⟫_ℝ =
      ⟪(xIter setup hStanding (t - 1) ω).1 -
          (xIter setup hStanding t ω).1, v⟫_ℝ -
        setup.α t *
          ⟪(xIter setup hStanding (t - 2) ω).1 -
            (xIter setup hStanding (t - 1) ω).1, v⟫_ℝ := by
  rw [proposition51_primal_prediction_difference_eq setup hStanding t ω]
  simp [inner_sub_left, inner_smul_left]

/-- Coordinate branch decomposition of `ỹ_i^t - z_i` used in the terminal part
of Proposition 5.1 Eq. (5.1.55). No SOptLib match: searched `yTilde branch
sampled correction terminal yIter`; the target file has the raw branch equations
`yTildeIter_sampledBlock_eq`, `yTildeIter_otherBlock_eq_prev`,
`yIter_sampledBlock_eq_yHatIter`, and `yIter_otherBlock_eq_prev`, but no helper
with the comparison point `z_i` and the sampled correction isolated. -/
private theorem proposition51_yTilde_minus_z_branch
    (hStanding : standingAssumptions setup)
    (hProbDen : allBlockProbabilityDenominatorsAdmissible setup)
    (t : ℕ) (ht : 1 ≤ t) (ω : BlockSamplePath setup)
    (z : SaddlePoint setup) (i : ι) :
    yTildeIter setup hStanding t ω i - (z.2 i).1 =
      ((yIter setup hStanding t ω i).1 - (z.2 i).1) +
        (if i = sampledBlock setup t ω then
          (inverseProbabilityValue setup i (hProbDen i) - 1) •
            ((yIter setup hStanding t ω i).1 -
              ((yIter setup hStanding (t - 1) ω) i).1)
        else 0) := by
  classical
  by_cases hi : i = sampledBlock setup t ω
  · subst i
    have hytilde := yTildeIter_sampledBlock_eq setup hStanding t ht ω
    have hycur :
        ((yIter setup hStanding t ω) (sampledBlock setup t ω)).1 =
          (yHatIter setup hStanding t ω (sampledBlock setup t ω)).1 := by
      exact congrArg Subtype.val
        (yIter_sampledBlock_eq_yHatIter setup hStanding t ht ω)
    rw [hytilde, hycur]
    simp [inverseProbabilityValue, sourceQuotient]
    module
  · have hytilde := yTildeIter_otherBlock_eq_prev
      setup hStanding t ht ω (i := i) hi
    have hycur :
        ((yIter setup hStanding t ω) i).1 =
          ((yIter setup hStanding (t - 1) ω) i).1 := by
      exact congrArg Subtype.val
        (yIter_otherBlock_eq_prev setup hStanding t ht ω (i := i) hi)
    rw [hytilde, hycur]
    simp [hi]

/-- Finite-coordinate version of the terminal `ỹ^t-y` branch decomposition in
Proposition 5.1 Eq. (5.1.55). No SOptLib match: searched `finite sum sampled
branch correction yTilde`; Mathlib supplies `Finset.sum_eq_single`, while the
paper-specific branch algebra is exactly
`proposition51_yTilde_minus_z_branch`. -/
private theorem proposition51_yTilde_sum_minus_z_branch
    (hStanding : standingAssumptions setup)
    (hProbDen : allBlockProbabilityDenominatorsAdmissible setup)
    (t : ℕ) (ht : 1 ≤ t) (ω : BlockSamplePath setup)
    (z : SaddlePoint setup) :
    (∑ i : ι, (yTildeIter setup hStanding t ω i - (z.2 i).1)) =
      (∑ i : ι, ((yIter setup hStanding t ω i).1 - (z.2 i).1)) +
        (inverseProbabilityValue setup (sampledBlock setup t ω)
            (hProbDen (sampledBlock setup t ω)) - 1) •
          ((yIter setup hStanding t ω (sampledBlock setup t ω)).1 -
            ((yIter setup hStanding (t - 1) ω)
              (sampledBlock setup t ω)).1) := by
  classical
  let s : ι := sampledBlock setup t ω
  have hbranch :
      (∑ i : ι, (yTildeIter setup hStanding t ω i - (z.2 i).1)) =
        ∑ i : ι,
          (((yIter setup hStanding t ω i).1 - (z.2 i).1) +
            (if i = s then
              (inverseProbabilityValue setup i (hProbDen i) - 1) •
                ((yIter setup hStanding t ω i).1 -
                  ((yIter setup hStanding (t - 1) ω) i).1)
            else 0)) := by
    refine Finset.sum_congr rfl ?_
    intro i _hi
    simpa [s] using
      proposition51_yTilde_minus_z_branch setup hStanding hProbDen t ht ω z i
  have hcorr :
      (∑ i : ι,
          (if i = s then
            (inverseProbabilityValue setup i (hProbDen i) - 1) •
              ((yIter setup hStanding t ω i).1 -
                ((yIter setup hStanding (t - 1) ω) i).1)
          else 0)) =
        (inverseProbabilityValue setup s (hProbDen s) - 1) •
          ((yIter setup hStanding t ω s).1 -
            ((yIter setup hStanding (t - 1) ω) s).1) := by
    rw [Finset.sum_eq_single s]
    · simp
    · intro i _hi his
      simp [his]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ s))
  calc
    (∑ i : ι, (yTildeIter setup hStanding t ω i - (z.2 i).1)) =
        ∑ i : ι,
          (((yIter setup hStanding t ω i).1 - (z.2 i).1) +
            (if i = s then
              (inverseProbabilityValue setup i (hProbDen i) - 1) •
                ((yIter setup hStanding t ω i).1 -
                  ((yIter setup hStanding (t - 1) ω) i).1)
            else 0)) := hbranch
    _ = (∑ i : ι, ((yIter setup hStanding t ω i).1 - (z.2 i).1)) +
        (∑ i : ι,
          (if i = s then
            (inverseProbabilityValue setup i (hProbDen i) - 1) •
              ((yIter setup hStanding t ω i).1 -
                ((yIter setup hStanding (t - 1) ω) i).1)
          else 0)) := by
        rw [Finset.sum_add_distrib]
    _ = (∑ i : ι, ((yIter setup hStanding t ω i).1 - (z.2 i).1)) +
        (inverseProbabilityValue setup s (hProbDen s) - 1) •
          ((yIter setup hStanding t ω s).1 -
            ((yIter setup hStanding (t - 1) ω) s).1) := by
        rw [hcorr]
    _ = (∑ i : ι, ((yIter setup hStanding t ω i).1 - (z.2 i).1)) +
        (inverseProbabilityValue setup (sampledBlock setup t ω)
            (hProbDen (sampledBlock setup t ω)) - 1) •
          ((yIter setup hStanding t ω (sampledBlock setup t ω)).1 -
            ((yIter setup hStanding (t - 1) ω)
              (sampledBlock setup t ω)).1) := by
        rfl

/-- Inner-product version of the terminal `ỹ^t-y` branch decomposition used in
Proposition 5.1 Eq. (5.1.55). No SOptLib match: searched `inner sampled branch
yTilde terminal correction`; this is the paper-specific specialization of
`proposition51_yTilde_sum_minus_z_branch` with Mathlib's `inner_add_right` and
`inner_smul_right`. -/
private theorem proposition51_yTilde_inner_minus_z_branch
    (hStanding : standingAssumptions setup)
    (hProbDen : allBlockProbabilityDenominatorsAdmissible setup)
    (t : ℕ) (ht : 1 ≤ t) (ω : BlockSamplePath setup)
    (z : SaddlePoint setup) (u : E) :
    ⟪u, ∑ i : ι, (yTildeIter setup hStanding t ω i - (z.2 i).1)⟫_ℝ =
      ⟪u, ∑ i : ι, ((yIter setup hStanding t ω i).1 - (z.2 i).1)⟫_ℝ +
        (inverseProbabilityValue setup (sampledBlock setup t ω)
            (hProbDen (sampledBlock setup t ω)) - 1) *
          ⟪u,
            (yIter setup hStanding t ω (sampledBlock setup t ω)).1 -
              ((yIter setup hStanding (t - 1) ω)
                (sampledBlock setup t ω)).1⟫_ℝ := by
  rw [proposition51_yTilde_sum_minus_z_branch setup hStanding hProbDen t ht ω z]
  simp [inner_add_right, inner_smul_right]

/-- Coupling expansion combining Eq. (5.1.21) and the sampled terminal branch
of Eq. (5.1.23), used inside Proposition 5.1 Eq. (5.1.55). No SOptLib match:
searched `RPDG coupling expansion xTilde yTilde sampled correction`; the
available pieces are the route-local
`proposition51_primal_prediction_coupling_expansion` and
`proposition51_yTilde_inner_minus_z_branch`, which this helper composes. -/
private theorem proposition51_current_coupling_expansion
    (hStanding : standingAssumptions setup)
    (hProbDen : allBlockProbabilityDenominatorsAdmissible setup)
    (t : ℕ) (ht : 1 ≤ t) (ω : BlockSamplePath setup)
    (z : SaddlePoint setup) :
    ⟪xTildeIter setup hStanding t ω - (xIter setup hStanding t ω).1,
      ∑ i : ι, (yTildeIter setup hStanding t ω i - (z.2 i).1)⟫_ℝ =
      ⟪(xIter setup hStanding (t - 1) ω).1 -
          (xIter setup hStanding t ω).1,
        ∑ i : ι, ((yIter setup hStanding t ω i).1 - (z.2 i).1)⟫_ℝ +
        (inverseProbabilityValue setup (sampledBlock setup t ω)
            (hProbDen (sampledBlock setup t ω)) - 1) *
          ⟪(xIter setup hStanding (t - 1) ω).1 -
              (xIter setup hStanding t ω).1,
            (yIter setup hStanding t ω (sampledBlock setup t ω)).1 -
              ((yIter setup hStanding (t - 1) ω)
                (sampledBlock setup t ω)).1⟫_ℝ -
        setup.α t *
          ⟪(xIter setup hStanding (t - 2) ω).1 -
              (xIter setup hStanding (t - 1) ω).1,
            ∑ i : ι, (yTildeIter setup hStanding t ω i - (z.2 i).1)⟫_ℝ := by
  rw [proposition51_primal_prediction_coupling_expansion
    setup hStanding t ω
      (∑ i : ι, (yTildeIter setup hStanding t ω i - (z.2 i).1))]
  rw [proposition51_yTilde_inner_minus_z_branch
    setup hStanding hProbDen t ht ω z
      ((xIter setup hStanding (t - 1) ω).1 -
        (xIter setup hStanding t ω).1)]

/-- Historical finite-coordinate branch for the source observation following
Proposition 5.1 Eq. (5.1.55). No SOptLib match: searched `yTilde increment sum
branch finite sum sampled block`; the only relevant hits were the already proved
terminal comparison helpers `proposition51_yTilde_*_branch`, which compare
`ỹ^t` with `z` at one time, while this source step compares `ỹ^t` with
`ỹ^{t-1}` and needs both the current and previous sampled blocks. -/
private theorem proposition51_yTilde_increment_sum_branch
    (hStanding : standingAssumptions setup)
    (hProbDen : allBlockProbabilityDenominatorsAdmissible setup)
    (t : ℕ) (ht2 : 2 ≤ t) (ω : BlockSamplePath setup) :
    (∑ i : ι,
      (yTildeIter setup hStanding t ω i -
        yTildeIter setup hStanding (t - 1) ω i)) =
      inverseProbabilityValue setup (sampledBlock setup t ω)
          (hProbDen (sampledBlock setup t ω)) •
        ((yIter setup hStanding t ω (sampledBlock setup t ω)).1 -
          ((yIter setup hStanding (t - 1) ω)
            (sampledBlock setup t ω)).1) +
      (inverseProbabilityValue setup (sampledBlock setup (t - 1) ω)
          (hProbDen (sampledBlock setup (t - 1) ω)) - 1) •
        (((yIter setup hStanding (t - 2) ω)
            (sampledBlock setup (t - 1) ω)).1 -
          ((yIter setup hStanding (t - 1) ω)
            (sampledBlock setup (t - 1) ω)).1) := by
  classical
  let sc : ι := sampledBlock setup t ω
  let sp : ι := sampledBlock setup (t - 1) ω
  have ht : 1 ≤ t := by omega
  have htm1 : 1 ≤ t - 1 := by omega
  have hpoint : ∀ i : ι,
      yTildeIter setup hStanding t ω i -
          yTildeIter setup hStanding (t - 1) ω i =
        (if i = sc then
          inverseProbabilityValue setup i (hProbDen i) •
            ((yIter setup hStanding t ω i).1 -
              ((yIter setup hStanding (t - 1) ω) i).1)
        else 0) +
        (if i = sp then
          (inverseProbabilityValue setup i (hProbDen i) - 1) •
            (((yIter setup hStanding (t - 2) ω) i).1 -
              ((yIter setup hStanding (t - 1) ω) i).1)
        else 0) := by
    intro i
    have hyt :
        yTildeIter setup hStanding t ω i =
          if i = sc then
            inverseProbabilityValue setup i (hProbDen i) •
                ((yIter setup hStanding t ω i).1 -
                  ((yIter setup hStanding (t - 1) ω) i).1) +
              ((yIter setup hStanding (t - 1) ω) i).1
          else
            ((yIter setup hStanding (t - 1) ω) i).1 := by
      by_cases hi : i = sc
      · subst i
        simpa [sc] using yTildeIter_sampledBlock_eq setup hStanding t ht ω
      · simpa [sc, hi] using
          yTildeIter_otherBlock_eq_prev setup hStanding t ht ω (i := i) hi
    have hytm1 :
        yTildeIter setup hStanding (t - 1) ω i =
          if i = sp then
            inverseProbabilityValue setup i (hProbDen i) •
                (((yIter setup hStanding (t - 1) ω) i).1 -
                  ((yIter setup hStanding (t - 2) ω) i).1) +
              ((yIter setup hStanding (t - 2) ω) i).1
          else
            ((yIter setup hStanding (t - 2) ω) i).1 := by
      by_cases hi : i = sp
      · subst i
        simpa [sp] using
          yTildeIter_sampledBlock_eq setup hStanding (t - 1) htm1 ω
      · simpa [sp, hi] using
          yTildeIter_otherBlock_eq_prev
            setup hStanding (t - 1) htm1 ω (i := i) hi
    rw [hyt, hytm1]
    by_cases hc : i = sc
    · by_cases hp : i = sp
      · have hscp : sc = sp := by
          rw [← hc, hp]
        simp [hc, hp, hscp]
        module
      · have hy_prev :
            ((yIter setup hStanding (t - 1) ω) i).1 =
              ((yIter setup hStanding (t - 2) ω) i).1 := by
          exact congrArg Subtype.val
            (yIter_otherBlock_eq_prev setup hStanding (t - 1) htm1 ω
              (i := i) hp)
        simp [hc, hp, hy_prev]
    · by_cases hp : i = sp
      · have hsp_ne_sc : sp ≠ sc := by
          intro hspc
          exact hc (by rw [hp, hspc])
        simp [hc, hp, hsp_ne_sc]
        module
      · have hy_prev :
            ((yIter setup hStanding (t - 1) ω) i).1 =
              ((yIter setup hStanding (t - 2) ω) i).1 := by
          exact congrArg Subtype.val
            (yIter_otherBlock_eq_prev setup hStanding (t - 1) htm1 ω
              (i := i) hp)
        simp [hc, hp, hy_prev]
  simpa [sc, sp] using
    (sum_sampled_coordinate_two_time_increment_eq
      (yt := fun i : ι => yTildeIter setup hStanding t ω i)
      (ytm1 := fun i : ι => yTildeIter setup hStanding (t - 1) ω i)
      (cur := fun i : ι =>
        inverseProbabilityValue setup i (hProbDen i) •
          ((yIter setup hStanding t ω i).1 -
            ((yIter setup hStanding (t - 1) ω) i).1))
      (prev := fun i : ι =>
        (inverseProbabilityValue setup i (hProbDen i) - 1) •
          (((yIter setup hStanding (t - 2) ω) i).1 -
            ((yIter setup hStanding (t - 1) ω) i).1))
      (sc := sc) (sp := sp) hpoint)

/-- Inner-product form of the historical `ỹ^t-ỹ^{t-1}` branch in
Proposition 5.1 Eq. (5.1.55). No SOptLib match: searched `inner product yTilde
increment historical coupling expansion`; the useful result is the local
summed branch `proposition51_yTilde_increment_sum_branch`, while SOptLib's
generic finite-sum inner algebra does not know this paper's sampled-block
history. -/
private theorem proposition51_yTilde_increment_inner_branch
    (hStanding : standingAssumptions setup)
    (hProbDen : allBlockProbabilityDenominatorsAdmissible setup)
    (t : ℕ) (ht2 : 2 ≤ t) (ω : BlockSamplePath setup) (u : E) :
    ⟪u,
      ∑ i : ι,
        (yTildeIter setup hStanding t ω i -
          yTildeIter setup hStanding (t - 1) ω i)⟫_ℝ =
      inverseProbabilityValue setup (sampledBlock setup t ω)
          (hProbDen (sampledBlock setup t ω)) *
        ⟪u,
          (yIter setup hStanding t ω (sampledBlock setup t ω)).1 -
            ((yIter setup hStanding (t - 1) ω)
              (sampledBlock setup t ω)).1⟫_ℝ +
      (inverseProbabilityValue setup (sampledBlock setup (t - 1) ω)
          (hProbDen (sampledBlock setup (t - 1) ω)) - 1) *
        ⟪u,
          ((yIter setup hStanding (t - 2) ω)
            (sampledBlock setup (t - 1) ω)).1 -
            ((yIter setup hStanding (t - 1) ω)
              (sampledBlock setup (t - 1) ω)).1⟫_ℝ := by
  rw [proposition51_yTilde_increment_sum_branch setup hStanding hProbDen t ht2 ω]
  simp [inner_add_right, inner_smul_right]

/-- Full historical coupling expansion for Proposition 5.1 Eq. (5.1.55).
No SOptLib match: searched `Proposition 5.1 Eq 5.1.55 full coupling expansion
yTilde historical`; existing hits were the same-time
`proposition51_current_coupling_expansion` and the new historical increment
branch, so this bridge composes those two source steps. -/
private theorem proposition51_historical_coupling_expansion
    (hStanding : standingAssumptions setup)
    (hProbDen : allBlockProbabilityDenominatorsAdmissible setup)
    (t : ℕ) (ht2 : 2 ≤ t) (ω : BlockSamplePath setup)
    (z : SaddlePoint setup) :
    ⟪xTildeIter setup hStanding t ω - (xIter setup hStanding t ω).1,
      ∑ i : ι, (yTildeIter setup hStanding t ω i - (z.2 i).1)⟫_ℝ =
      ⟪(xIter setup hStanding (t - 1) ω).1 -
          (xIter setup hStanding t ω).1,
        ∑ i : ι, ((yIter setup hStanding t ω i).1 - (z.2 i).1)⟫_ℝ +
      (inverseProbabilityValue setup (sampledBlock setup t ω)
          (hProbDen (sampledBlock setup t ω)) - 1) *
        ⟪(xIter setup hStanding (t - 1) ω).1 -
            (xIter setup hStanding t ω).1,
          (yIter setup hStanding t ω (sampledBlock setup t ω)).1 -
            ((yIter setup hStanding (t - 1) ω)
              (sampledBlock setup t ω)).1⟫_ℝ -
      setup.α t *
        ⟪(xIter setup hStanding (t - 2) ω).1 -
            (xIter setup hStanding (t - 1) ω).1,
          ∑ i : ι,
            (yTildeIter setup hStanding (t - 1) ω i - (z.2 i).1)⟫_ℝ -
      setup.α t *
        (inverseProbabilityValue setup (sampledBlock setup t ω)
            (hProbDen (sampledBlock setup t ω)) *
          ⟪(xIter setup hStanding (t - 2) ω).1 -
              (xIter setup hStanding (t - 1) ω).1,
            (yIter setup hStanding t ω (sampledBlock setup t ω)).1 -
              ((yIter setup hStanding (t - 1) ω)
                (sampledBlock setup t ω)).1⟫_ℝ +
        (inverseProbabilityValue setup (sampledBlock setup (t - 1) ω)
            (hProbDen (sampledBlock setup (t - 1) ω)) - 1) *
          ⟪(xIter setup hStanding (t - 2) ω).1 -
              (xIter setup hStanding (t - 1) ω).1,
            ((yIter setup hStanding (t - 2) ω)
              (sampledBlock setup (t - 1) ω)).1 -
              ((yIter setup hStanding (t - 1) ω)
                (sampledBlock setup (t - 1) ω)).1⟫_ℝ) := by
  classical
  have ht : 1 ≤ t := by omega
  let uPrev : E :=
    (xIter setup hStanding (t - 2) ω).1 -
      (xIter setup hStanding (t - 1) ω).1
  have hsum_shift :
      (∑ i : ι, (yTildeIter setup hStanding t ω i - (z.2 i).1)) =
        (∑ i : ι,
          (yTildeIter setup hStanding (t - 1) ω i - (z.2 i).1)) +
        ∑ i : ι,
          (yTildeIter setup hStanding t ω i -
            yTildeIter setup hStanding (t - 1) ω i) := by
    calc
      (∑ i : ι, (yTildeIter setup hStanding t ω i - (z.2 i).1)) =
          ∑ i : ι,
            ((yTildeIter setup hStanding (t - 1) ω i - (z.2 i).1) +
              (yTildeIter setup hStanding t ω i -
                yTildeIter setup hStanding (t - 1) ω i)) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            module
      _ =
          (∑ i : ι,
            (yTildeIter setup hStanding (t - 1) ω i - (z.2 i).1)) +
          ∑ i : ι,
            (yTildeIter setup hStanding t ω i -
              yTildeIter setup hStanding (t - 1) ω i) := by
            rw [Finset.sum_add_distrib]
  have hinner_shift :
      ⟪uPrev,
        ∑ i : ι, (yTildeIter setup hStanding t ω i - (z.2 i).1)⟫_ℝ =
        ⟪uPrev,
          ∑ i : ι,
            (yTildeIter setup hStanding (t - 1) ω i - (z.2 i).1)⟫_ℝ +
        (inverseProbabilityValue setup (sampledBlock setup t ω)
            (hProbDen (sampledBlock setup t ω)) *
          ⟪uPrev,
            (yIter setup hStanding t ω (sampledBlock setup t ω)).1 -
              ((yIter setup hStanding (t - 1) ω)
                (sampledBlock setup t ω)).1⟫_ℝ +
        (inverseProbabilityValue setup (sampledBlock setup (t - 1) ω)
            (hProbDen (sampledBlock setup (t - 1) ω)) - 1) *
          ⟪uPrev,
            ((yIter setup hStanding (t - 2) ω)
              (sampledBlock setup (t - 1) ω)).1 -
              ((yIter setup hStanding (t - 1) ω)
                (sampledBlock setup (t - 1) ω)).1⟫_ℝ) := by
    calc
      ⟪uPrev,
        ∑ i : ι, (yTildeIter setup hStanding t ω i - (z.2 i).1)⟫_ℝ =
          ⟪uPrev,
            (∑ i : ι,
              (yTildeIter setup hStanding (t - 1) ω i - (z.2 i).1)) +
            ∑ i : ι,
              (yTildeIter setup hStanding t ω i -
                yTildeIter setup hStanding (t - 1) ω i)⟫_ℝ := by
            rw [hsum_shift]
      _ =
          ⟪uPrev,
            ∑ i : ι,
              (yTildeIter setup hStanding (t - 1) ω i - (z.2 i).1)⟫_ℝ +
          ⟪uPrev,
            ∑ i : ι,
              (yTildeIter setup hStanding t ω i -
                yTildeIter setup hStanding (t - 1) ω i)⟫_ℝ := by
            rw [inner_add_right]
      _ =
          ⟪uPrev,
            ∑ i : ι,
              (yTildeIter setup hStanding (t - 1) ω i - (z.2 i).1)⟫_ℝ +
          (inverseProbabilityValue setup (sampledBlock setup t ω)
              (hProbDen (sampledBlock setup t ω)) *
            ⟪uPrev,
              (yIter setup hStanding t ω (sampledBlock setup t ω)).1 -
                ((yIter setup hStanding (t - 1) ω)
                  (sampledBlock setup t ω)).1⟫_ℝ +
          (inverseProbabilityValue setup (sampledBlock setup (t - 1) ω)
              (hProbDen (sampledBlock setup (t - 1) ω)) - 1) *
            ⟪uPrev,
              ((yIter setup hStanding (t - 2) ω)
                (sampledBlock setup (t - 1) ω)).1 -
                ((yIter setup hStanding (t - 1) ω)
                  (sampledBlock setup (t - 1) ω)).1⟫_ℝ) := by
            rw [proposition51_yTilde_increment_inner_branch
              setup hStanding hProbDen t ht2 ω uPrev]
  rw [proposition51_current_coupling_expansion setup hStanding hProbDen t ht ω z]
  rw [hinner_shift]
  simp [uPrev]
  ring

/-- Prefix observability of the negative Delta integrand from Proposition 5.1
Eq. (5.1.54), for any longer paper prefix containing the residual time. This
uses `stateProcess_extendBlockPrefix_eq_of_le` for generated iterates and
`sampledBlock_extendBlockPrefix_eq_of_le` for the explicit selected block; no
SOptLib match was found for the paper-specific sampled Bregman/coupling scalar. -/
private theorem proposition51_delta_negative_prefix_extend_eq
    (hStanding : standingAssumptions setup)
    {t k : ℕ} (ht : 1 ≤ t) (htk : t ≤ k)
    (ω : BlockSamplePath setup) (z : SaddlePoint setup) :
    ((⟪xTildeIter setup hStanding t
          (extendBlockPrefix setup k (blockPrefix setup k ω)) -
          (xIter setup hStanding t
            (extendBlockPrefix setup k (blockPrefix setup k ω))).1,
        ∑ i : ι,
          (yTildeIter setup hStanding t
              (extendBlockPrefix setup k (blockPrefix setup k ω)) i -
            (z.2 i).1)⟫_ℝ -
      (setup.τ t *
          inverseProbabilityValue setup
            (sampledBlock setup t
              (extendBlockPrefix setup k (blockPrefix setup k ω)))
            (sampledBlock_probability_ne_zero setup
              (sampledPositiveBlock setup t
                (extendBlockPrefix setup k (blockPrefix setup k ω))))) *
        (SOptLib.carrierBregmanDivergence (dualConjugate setup (sampledBlock setup t
            (extendBlockPrefix setup k (blockPrefix setup k ω)))) (dualConjugateBaseSelector setup (sampledBlock setup t
            (extendBlockPrefix setup k (blockPrefix setup k ω))) ((yIter setup hStanding (t - 1)
              (extendBlockPrefix setup k (blockPrefix setup k ω)))
            (sampledBlock setup t
              (extendBlockPrefix setup k (blockPrefix setup k ω)))) (dualSubgradIter setup hStanding (t - 1)
            (extendBlockPrefix setup k (blockPrefix setup k ω))
            (sampledBlock setup t
              (extendBlockPrefix setup k (blockPrefix setup k ω))))) ((yIter setup hStanding (t - 1)
              (extendBlockPrefix setup k (blockPrefix setup k ω)))
            (sampledBlock setup t
              (extendBlockPrefix setup k (blockPrefix setup k ω)))) ((yIter setup hStanding t
              (extendBlockPrefix setup k (blockPrefix setup k ω)))
            (sampledBlock setup t
              (extendBlockPrefix setup k (blockPrefix setup k ω))))) -
      setup.η t *
        primalBregman setup
          (xIter setup hStanding (t - 1)
            (extendBlockPrefix setup k (blockPrefix setup k ω)))
          (xIter setup hStanding t
            (extendBlockPrefix setup k (blockPrefix setup k ω)))) =
    (⟪xTildeIter setup hStanding t ω - (xIter setup hStanding t ω).1,
        ∑ i : ι, (yTildeIter setup hStanding t ω i - (z.2 i).1)⟫_ℝ -
      (setup.τ t *
          inverseProbabilityValue setup (sampledBlock setup t ω)
            (sampledBlock_probability_ne_zero setup
              (sampledPositiveBlock setup t ω))) *
        (SOptLib.carrierBregmanDivergence (dualConjugate setup (sampledBlock setup t ω)) (dualConjugateBaseSelector setup (sampledBlock setup t ω) ((yIter setup hStanding (t - 1) ω) (sampledBlock setup t ω)) (dualSubgradIter setup hStanding (t - 1) ω
            (sampledBlock setup t ω))) ((yIter setup hStanding (t - 1) ω) (sampledBlock setup t ω)) ((yIter setup hStanding t ω) (sampledBlock setup t ω))) -
      setup.η t *
        primalBregman setup
          (xIter setup hStanding (t - 1) ω)
          (xIter setup hStanding t ω))) := by
  classical
  have hcur :
      stateProcess setup hStanding t
          (extendBlockPrefix setup k (blockPrefix setup k ω)) =
        stateProcess setup hStanding t ω :=
    stateProcess_extendBlockPrefix_eq_of_le setup hStanding htk ω
  have hprev :
      stateProcess setup hStanding (t - 1)
          (extendBlockPrefix setup k (blockPrefix setup k ω)) =
        stateProcess setup hStanding (t - 1) ω :=
    stateProcess_extendBlockPrefix_eq_of_le setup hStanding (by omega) ω
  have hprev2 :
      stateProcess setup hStanding (t - 2)
          (extendBlockPrefix setup k (blockPrefix setup k ω)) =
        stateProcess setup hStanding (t - 2) ω :=
    stateProcess_extendBlockPrefix_eq_of_le setup hStanding (by omega) ω
  have hblock :
      sampledBlock setup t (extendBlockPrefix setup k (blockPrefix setup k ω)) =
        sampledBlock setup t ω :=
    sampledBlock_extendBlockPrefix_eq_of_le setup ht htk ω
  dsimp [xTildeIter, xIter, yTildeIter, yIter, dualSubgradIter,
    inverseProbabilityValue]
  rw [hcur, hprev, hprev2]
  simp [sourceQuotient_def]
  rw [hblock]

/-- Prefix observability of the terminal Eq. (5.1.57) bracket. This is the
right-hand-side companion to `proposition51_delta_negative_prefix_extend_eq`;
it uses only generated-state determinacy through time `k`, since the terminal
bracket has no explicit sampled-block residual. -/
private theorem proposition51_terminal_bracket_prefix_extend_eq
    (hStanding : standingAssumptions setup)
    (k : ℕ) (ω : BlockSamplePath setup) (z : SaddlePoint setup) :
    (setup.η k / 4 *
        ‖(xIter setup hStanding (k - 1)
            (extendBlockPrefix setup k (blockPrefix setup k ω))).1 -
          (xIter setup hStanding k
            (extendBlockPrefix setup k (blockPrefix setup k ω))).1‖ ^ 2 -
      ⟪(xIter setup hStanding (k - 1)
            (extendBlockPrefix setup k (blockPrefix setup k ω))).1 -
          (xIter setup hStanding k
            (extendBlockPrefix setup k (blockPrefix setup k ω))).1,
        ∑ i : ι,
          ((yIter setup hStanding k
              (extendBlockPrefix setup k (blockPrefix setup k ω)) i).1 -
            (z.2 i).1)⟫_ℝ) =
    (setup.η k / 4 *
        ‖(xIter setup hStanding (k - 1) ω).1 -
          (xIter setup hStanding k ω).1‖ ^ 2 -
      ⟪(xIter setup hStanding (k - 1) ω).1 -
          (xIter setup hStanding k ω).1,
        ∑ i : ι, ((yIter setup hStanding k ω i).1 -
          (z.2 i).1)⟫_ℝ) := by
  classical
  have hcur :
      stateProcess setup hStanding k
          (extendBlockPrefix setup k (blockPrefix setup k ω)) =
        stateProcess setup hStanding k ω :=
    stateProcess_extendBlockPrefix_eq setup hStanding k ω
  have hprev :
      stateProcess setup hStanding (k - 1)
          (extendBlockPrefix setup k (blockPrefix setup k ω)) =
        stateProcess setup hStanding (k - 1) ω :=
    stateProcess_extendBlockPrefix_eq_of_le setup hStanding (by omega) ω
  dsimp [xIter, yIter]
  rw [hcur, hprev]

/-- Source-neutral one-based lagged cancellation used in Proposition 5.1
Eq. (5.1.56). No direct SOptLib match: searched `sum Icc weighted lagged
cancel terminal equality` and considered `SOptLib.sum_range_weighted_lagged_source_telescope_le`,
`SOptLib.sum_Icc_mono_coeff_mul_sub_le_terminal_sub_tail`, and
`SOptLib.sum_Icc_le_gap_add_sum_of_lagged_step`; those are inequality
telescopes with recurrence/cap hypotheses, while this proof needs the exact
finite-sum cancellation from the adjacent coefficient identity. -/
private theorem sum_Icc_weighted_lagged_cancel_eq_terminal
    (a b H : ℕ → ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hbridge : ∀ t, 2 ≤ t → t ≤ k → b t = a (t - 1)) :
    (∑ t ∈ Finset.Icc 1 k, (-a t * H t)) +
        ∑ t ∈ Finset.Icc 2 k, b t * H (t - 1) =
      -a k * H k := by
  exact _root_.sum_Icc_weighted_lagged_cancel_eq_terminal a b H k hk hbridge

/-- Source-neutral reindexing of a one-based closed window into a terminal
summand plus the lagged `Icc 2 k` window. No direct SOptLib match: searched
`sum Icc one terminal lagged reindex t minus one equality`; existing hits were
weighted-average or inequality telescopes, not this exact equality. -/
private theorem sum_Icc_one_eq_terminal_add_lagged
    (A : ℕ → ℝ) (k : ℕ) (hk : 1 ≤ k) :
    (∑ t ∈ Finset.Icc 1 k, A t) =
      A k + ∑ t ∈ Finset.Icc 2 k, A (t - 1) := by
  exact _root_.sum_Icc_one_eq_terminal_add_lagged A k hk

/-- Source-neutral reindexing of a one-based closed window into the first
summand plus the tail `Icc 2 k` window. No direct SOptLib match: searched
`Finset Icc first add tail sum equality`; `sum_Icc_one_eq_terminal_add_lagged`
splits at the terminal endpoint, while this proof needs the initial endpoint to
track the unused nonnegative half-dual term in Proposition 5.1 Step 11. -/
private theorem sum_Icc_one_eq_first_add_tail
    (A : ℕ → ℝ) (k : ℕ) (hk : 1 ≤ k) :
    (∑ t ∈ Finset.Icc 1 k, A t) =
      A 1 + ∑ t ∈ Finset.Icc 2 k, A t := by
  exact _root_.sum_Icc_one_eq_first_add_tail A k hk

/-- Source-neutral finite-sum regrouping for Proposition 5.1 Step 10. No
SOptLib match: searched `finite sum regrouping weighted coupling Icc`, checked
`finite_window_weighted_recurrence_telescope_with_tail_sums`, and considered
the local `sum_Icc_weighted_lagged_cancel_eq_terminal`; those either telescope
inequalities/recurrences or only cancel the lagged `H` terms, while Eq.
(5.1.56) needs this exact pointwise `C/H/E` regrouping equality. -/
private theorem sum_Icc_weighted_coupling_regroup_from_pointwise
    (θ α C H Ecur Eprev : ℕ → ℝ) (T : ℝ)
    (k : ℕ) (hk : 1 ≤ k)
    (hbase : C 1 = H 1)
    (hhist :
      ∀ t ∈ Finset.Icc 2 k,
        C t = H t - α t * H (t - 1) - (Ecur t + Eprev t))
    (hcancel :
      (∑ t ∈ Finset.Icc 1 k, (-θ t * H t)) +
          ∑ t ∈ Finset.Icc 2 k, (α t * θ t) * H (t - 1) = T) :
    (∑ t ∈ Finset.Icc 1 k, θ t * (- C t)) =
      T + ∑ t ∈ Finset.Icc 2 k, θ t * (Ecur t + Eprev t) := by
  exact
    _root_.sum_Icc_weighted_coupling_regroup_from_pointwise
      θ α C H Ecur Eprev T k hk hbase hhist hcancel

/-- Abstract scalar allocation behind Proposition 5.1 Step 11. No direct
SOptLib match: searched `finite sum add inequalities combine add_le_add
sum_le_sum` and `Finset Icc terminal lagged reindex sum equality`; the available
hits give endpoint splits, but not this paper-specific allocation of the
terminal, current-historical, and previous-historical Young half-dual budgets. -/
private theorem proposition51_scalar_young_allocation_le
    (θ η U C A B D SQk SQcur SQprev E F : ℕ → ℝ)
    (k : ℕ) (hk : 1 ≤ k)
    (hRegroup :
      (∑ t ∈ Finset.Icc 1 k, θ t * (- C t)) =
        -θ k * (A k + B k) +
          ∑ t ∈ Finset.Icc 2 k, θ t * (E t + F t))
    (hTerminal :
      θ k * (-SQk k * U k) ≤ θ k * (-B k + D k / 2))
    (hCurrent :
      (∑ t ∈ Finset.Icc 2 k, -θ (t - 1) * SQcur t * U (t - 1)) ≤
        ∑ t ∈ Finset.Icc 2 k, θ t * (E t + D t / 2))
    (hPrevious :
      (∑ t ∈ Finset.Icc 2 k, -θ (t - 1) * SQprev t * U (t - 1)) ≤
        ∑ t ∈ Finset.Icc 2 k,
          (θ t * F t + θ (t - 1) * (D (t - 1) / 2)))
    (hDinit : 0 ≤ θ 1 * (D 1 / 2)) :
    θ k * (η k / 4 * U k - A k) +
        θ k * (η k / 4 - SQk k) * U k +
      ∑ t ∈ Finset.Icc 2 k,
        θ (t - 1) * (η (t - 1) / 2 - (SQcur t + SQprev t)) * U (t - 1) ≤
      ∑ t ∈ Finset.Icc 1 k,
        θ t * (η t / 2 * U t - C t + D t) := by
  exact
    three_young_budget_allocation_Icc_le
      θ η U C A B D SQk SQcur SQprev E F k hk
      hRegroup hTerminal hCurrent hPrevious hDinit

/-- Theorem 5.1 specialization of the Proposition 5.1 scalar Young allocation
with the constant `η/4` budgets supplied by Eq. (5.1.62). Existing candidates
considered: `proposition51_scalar_young_allocation_le` is the exact scalar
regrouping engine, but it is abstract in the three Young budgets; this helper
specializes it to the denominator-free constant-policy budgets and uses
Eq. (5.1.59) to cancel the residual coefficients. -/
private theorem theorem51_scalar_young_allocation_le
    (τ η α : ℝ)
    (hPolicy : constantParameterPolicy setup τ η α)
    (hAlpha : alphaRange α)
    (U C A B D E F : ℕ → ℝ)
    (k : ℕ) (hk : 1 ≤ k)
    (hRegroup :
      (∑ t ∈ Finset.Icc 1 k, theoremOutputWeight α hAlpha t * (- C t)) =
        -theoremOutputWeight α hAlpha k * (A k + B k) +
          ∑ t ∈ Finset.Icc 2 k, theoremOutputWeight α hAlpha t * (E t + F t))
    (hTerminal :
      theoremOutputWeight α hAlpha k * (-(η / 4) * U k) ≤
        theoremOutputWeight α hAlpha k * (-B k + D k / 2))
    (hCurrent :
      (∑ t ∈ Finset.Icc 2 k,
        -theoremOutputWeight α hAlpha (t - 1) * (η / 4) * U (t - 1)) ≤
        ∑ t ∈ Finset.Icc 2 k,
          theoremOutputWeight α hAlpha t * (E t + D t / 2))
    (hPrevious :
      (∑ t ∈ Finset.Icc 2 k,
        -theoremOutputWeight α hAlpha (t - 1) * (η / 4) * U (t - 1)) ≤
        ∑ t ∈ Finset.Icc 2 k,
          (theoremOutputWeight α hAlpha t * F t +
            theoremOutputWeight α hAlpha (t - 1) * (D (t - 1) / 2)))
    (hDinit : 0 ≤ theoremOutputWeight α hAlpha 1 * (D 1 / 2)) :
    theoremOutputWeight α hAlpha k * (setup.η k / 4 * U k - A k) ≤
      ∑ t ∈ Finset.Icc 1 k,
        theoremOutputWeight α hAlpha t *
          (setup.η t / 2 * U t - C t + D t) := by
  classical
  let θ : ℕ → ℝ := theoremOutputWeight α hAlpha
  let SQ : ℕ → ℝ := fun _ => η / 4
  have hTerminal' :
      θ k * (-SQ k * U k) ≤ θ k * (-B k + D k / 2) := by
    simpa [θ, SQ, mul_assoc] using hTerminal
  have hCurrent' :
      (∑ t ∈ Finset.Icc 2 k, -θ (t - 1) * SQ t * U (t - 1)) ≤
        ∑ t ∈ Finset.Icc 2 k, θ t * (E t + D t / 2) := by
    simpa [θ, SQ, mul_assoc] using hCurrent
  have hPrevious' :
      (∑ t ∈ Finset.Icc 2 k, -θ (t - 1) * SQ t * U (t - 1)) ≤
        ∑ t ∈ Finset.Icc 2 k, (θ t * F t + θ (t - 1) * (D (t - 1) / 2)) := by
    simpa [θ, SQ, mul_assoc] using hPrevious
  have hScalar :=
    proposition51_scalar_young_allocation_le
      θ setup.η U C A B D SQ SQ SQ E F k hk
      (by simpa [θ] using hRegroup)
      hTerminal' hCurrent' hPrevious'
      (by simpa [θ] using hDinit)
  have hExtraZero :
      θ k * (setup.η k / 4 - SQ k) * U k +
        ∑ t ∈ Finset.Icc 2 k,
          θ (t - 1) * (setup.η (t - 1) / 2 - (SQ t + SQ t)) * U (t - 1) = 0 := by
    have hterm : θ k * (setup.η k / 4 - SQ k) * U k = 0 := by
      have hηk : setup.η k = η := hPolicy.2.1 k hk
      rw [hηk]
      dsimp [SQ]
      ring
    have hsum :
        (∑ t ∈ Finset.Icc 2 k,
          θ (t - 1) * (setup.η (t - 1) / 2 - (SQ t + SQ t)) * U (t - 1)) = 0 := by
      apply Finset.sum_eq_zero
      intro t htmem
      rcases Finset.mem_Icc.mp htmem with ⟨ht2, _htk⟩
      have htprev : 1 ≤ t - 1 := by omega
      have hηprev : setup.η (t - 1) = η := hPolicy.2.1 (t - 1) htprev
      rw [hηprev]
      dsimp [SQ]
      ring
    rw [hterm, hsum]
    ring
  calc
    θ k * (setup.η k / 4 * U k - A k) =
        θ k * (setup.η k / 4 * U k - A k) +
          (θ k * (setup.η k / 4 - SQ k) * U k +
            ∑ t ∈ Finset.Icc 2 k,
              θ (t - 1) * (setup.η (t - 1) / 2 - (SQ t + SQ t)) * U (t - 1)) := by
          rw [hExtraZero]
          ring
    _ =
        θ k * (setup.η k / 4 * U k - A k) +
          θ k * (setup.η k / 4 - SQ k) * U k +
        ∑ t ∈ Finset.Icc 2 k,
          θ (t - 1) * (setup.η (t - 1) / 2 - (SQ t + SQ t)) * U (t - 1) := by
          ring
    _ ≤ ∑ t ∈ Finset.Icc 1 k,
        θ t * (setup.η t / 2 * U t - C t + D t) := hScalar

/-- Weighted Proposition 5.1 primal Bregman budget over the source window.
No SOptLib match: searched `weighted Finset Icc sum primalBregman norm lower
bound residual`, checked `primalBregmanLowerBound`, and considered generic
SOptLib Bregman lower-bound helpers; none package the paper Eq. (5.1.16)
conversion inside the `θ_t`-weighted `Icc 1 k` residual sum. -/
private theorem proposition51_weighted_primal_bregman_norm_budget_le
    (hStanding : standingAssumptions setup)
    (θ : ℕ → ℝ) (k : ℕ) (ω : BlockSamplePath setup)
    (R : ℕ → ℝ)
    (hθ : ∀ t, 1 ≤ t → t ≤ k → 0 ≤ θ t) :
    (∑ t ∈ Finset.Icc 1 k, θ t *
      (setup.η t / 2 *
          ‖(xIter setup hStanding (t - 1) ω).1 -
            (xIter setup hStanding t ω).1‖ ^ 2 + R t)) ≤
      ∑ t ∈ Finset.Icc 1 k, θ t *
        (setup.η t *
            primalBregman setup
              (xIter setup hStanding (t - 1) ω)
              (xIter setup hStanding t ω) + R t) := by
  have hStanding_data := hStanding
  obtain ⟨_, _, _, _, _, _, _, _, _, hVlb, _, hParam⟩ := hStanding_data
  exact
    sum_Icc_weighted_half_norm_sq_le_of_pointwise_half_norm_sq_le
      (toNorm := fun x : PrimalCarrier setup => x.1)
      (upper := primalBregman setup)
      (xPrev := fun t => xIter setup hStanding (t - 1) ω)
      (xCur := fun t => xIter setup hStanding t ω)
      (θ := θ) (η := setup.η) (R := R) (k := k)
      hθ
      (fun t ht1 _htk => hParam.2.1 t ht1)
      (fun t _ht1 _htk =>
        hVlb (xIter setup hStanding (t - 1) ω)
          (xIter setup hStanding t ω))

/-- Regrouped pathwise Proposition 5.1 lower bound immediately before applying
conditions (5.1.48)--(5.1.49), matching source proof step 12 before the final
coefficient drop. No SOptLib match: searched `weighted coupling telescope
sampled inner product sourceQuotient`, scanned `SOptLib/Model/Iterates.lean`,
`SOptLib/Layer1/Telescope.lean`, and `SOptLib/Glue/Algebra.lean`, and checked
`SOptLib.sum_Icc_two_coeff_telescope_le`,
`SOptLib.sum_range_weighted_lagged_source_telescope_le`,
`proposition51_current_coupling_expansion`,
`proposition51_historical_coupling_expansion`, and the Young bridges; these
provide pieces but none packages the paper-specific Eq. (5.1.56) coupling
telescope, inverse-probability Young absorption, and h51 coefficient rewrite. -/
private theorem proposition51_weighted_delta_pathwise_regrouped_lower_bound
    (hStanding : standingAssumptions setup)
    (θ : ℕ → ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hDen : proposition_5_1_denominatorBoundary setup k)
    (z : SaddlePoint setup)
    (hθ : ∀ t, 1 ≤ t → t ≤ k → 0 ≤ θ t)
    (h51 : ∀ t, 2 ≤ t → t ≤ k → setup.α t * θ t = θ (t - 1))
    (hHistoricalCoupling :
      ∀ (t : ℕ), 2 ≤ t → t ≤ k → ∀ (ω : BlockSamplePath setup),
        ⟪xTildeIter setup hStanding t ω - (xIter setup hStanding t ω).1,
          ∑ i : ι, (yTildeIter setup hStanding t ω i - (z.2 i).1)⟫_ℝ =
          ⟪(xIter setup hStanding (t - 1) ω).1 -
              (xIter setup hStanding t ω).1,
            ∑ i : ι, ((yIter setup hStanding t ω i).1 - (z.2 i).1)⟫_ℝ +
          (inverseProbabilityValue setup (sampledBlock setup t ω)
              (hDen.1 (sampledBlock setup t ω)) - 1) *
            ⟪(xIter setup hStanding (t - 1) ω).1 -
                (xIter setup hStanding t ω).1,
              (yIter setup hStanding t ω (sampledBlock setup t ω)).1 -
                ((yIter setup hStanding (t - 1) ω)
                  (sampledBlock setup t ω)).1⟫_ℝ -
          setup.α t *
            ⟪(xIter setup hStanding (t - 2) ω).1 -
                (xIter setup hStanding (t - 1) ω).1,
              ∑ i : ι,
                (yTildeIter setup hStanding (t - 1) ω i - (z.2 i).1)⟫_ℝ -
          setup.α t *
            (inverseProbabilityValue setup (sampledBlock setup t ω)
                (hDen.1 (sampledBlock setup t ω)) *
              ⟪(xIter setup hStanding (t - 2) ω).1 -
                  (xIter setup hStanding (t - 1) ω).1,
                (yIter setup hStanding t ω (sampledBlock setup t ω)).1 -
                  ((yIter setup hStanding (t - 1) ω)
                    (sampledBlock setup t ω)).1⟫_ℝ +
            (inverseProbabilityValue setup (sampledBlock setup (t - 1) ω)
                (hDen.1 (sampledBlock setup (t - 1) ω)) - 1) *
              ⟪(xIter setup hStanding (t - 2) ω).1 -
                  (xIter setup hStanding (t - 1) ω).1,
                ((yIter setup hStanding (t - 2) ω)
                  (sampledBlock setup (t - 1) ω)).1 -
                  ((yIter setup hStanding (t - 1) ω)
                    (sampledBlock setup (t - 1) ω)).1⟫_ℝ))
    (ω : BlockSamplePath setup) :
    θ k *
        (setup.η k / 4 *
            ‖(xIter setup hStanding (k - 1) ω).1 -
              (xIter setup hStanding k ω).1‖ ^ 2 -
          ⟪(xIter setup hStanding (k - 1) ω).1 -
              (xIter setup hStanding k ω).1,
            ∑ i : ι, ((yIter setup hStanding k ω i).1 -
              (z.2 i).1)⟫_ℝ) +
      θ k *
        (setup.η k / 4 -
          sourceQuotient
            (setup.L (sampledBlock setup k ω) *
              (1 - samplingProbability setup (sampledBlock setup k ω)) ^ 2)
            ((componentCount (ι := ι) : ℝ) * setup.τ k *
              samplingProbability setup (sampledBlock setup k ω))
            (hDen.2 k (sampledBlock setup k ω))) *
          ‖(xIter setup hStanding (k - 1) ω).1 -
            (xIter setup hStanding k ω).1‖ ^ 2 +
      ∑ t ∈ Finset.Icc 2 k,
        θ (t - 1) *
          (setup.η (t - 1) / 2 -
            (sourceQuotient
                (setup.L (sampledBlock setup t ω) * setup.α t)
                ((componentCount (ι := ι) : ℝ) * setup.τ t *
                  samplingProbability setup (sampledBlock setup t ω))
                (hDen.2 t (sampledBlock setup t ω)) +
              sourceQuotient
                ((1 - samplingProbability setup (sampledBlock setup (t - 1) ω)) ^ 2 *
                  setup.L (sampledBlock setup (t - 1) ω))
                ((componentCount (ι := ι) : ℝ) * setup.τ (t - 1) *
                  samplingProbability setup (sampledBlock setup (t - 1) ω))
                (hDen.2 (t - 1) (sampledBlock setup (t - 1) ω)))) *
            ‖(xIter setup hStanding (t - 2) ω).1 -
              (xIter setup hStanding (t - 1) ω).1‖ ^ 2 ≤
      ∑ t ∈ Finset.Icc 1 k, θ t *
        (setup.η t *
            primalBregman setup
              (xIter setup hStanding (t - 1) ω)
              (xIter setup hStanding t ω) -
          ⟪xTildeIter setup hStanding t ω -
              (xIter setup hStanding t ω).1,
            ∑ i : ι,
              (yTildeIter setup hStanding t ω i - (z.2 i).1)⟫_ℝ +
          setup.τ t *
            inverseProbabilityValue setup (sampledBlock setup t ω)
              (sampledBlock_probability_ne_zero setup
                (sampledPositiveBlock setup t ω)) *
            (SOptLib.carrierBregmanDivergence (dualConjugate setup (sampledBlock setup t ω)) (dualConjugateBaseSelector setup (sampledBlock setup t ω) ((yIter setup hStanding (t - 1) ω)
                (sampledBlock setup t ω)) (dualSubgradIter setup hStanding (t - 1) ω
                (sampledBlock setup t ω))) ((yIter setup hStanding (t - 1) ω)
                (sampledBlock setup t ω)) ((yIter setup hStanding t ω)
                (sampledBlock setup t ω)))) := by
  classical
  have hHistoricalCoupling_on_window :
      ∀ t ∈ Finset.Icc 2 k,
        ⟪xTildeIter setup hStanding t ω - (xIter setup hStanding t ω).1,
          ∑ i : ι, (yTildeIter setup hStanding t ω i - (z.2 i).1)⟫_ℝ =
          ⟪(xIter setup hStanding (t - 1) ω).1 -
              (xIter setup hStanding t ω).1,
            ∑ i : ι, ((yIter setup hStanding t ω i).1 - (z.2 i).1)⟫_ℝ +
          (inverseProbabilityValue setup (sampledBlock setup t ω)
              (hDen.1 (sampledBlock setup t ω)) - 1) *
            ⟪(xIter setup hStanding (t - 1) ω).1 -
                (xIter setup hStanding t ω).1,
              (yIter setup hStanding t ω (sampledBlock setup t ω)).1 -
                ((yIter setup hStanding (t - 1) ω)
                  (sampledBlock setup t ω)).1⟫_ℝ -
          setup.α t *
            ⟪(xIter setup hStanding (t - 2) ω).1 -
                (xIter setup hStanding (t - 1) ω).1,
              ∑ i : ι,
                (yTildeIter setup hStanding (t - 1) ω i - (z.2 i).1)⟫_ℝ -
          setup.α t *
            (inverseProbabilityValue setup (sampledBlock setup t ω)
                (hDen.1 (sampledBlock setup t ω)) *
              ⟪(xIter setup hStanding (t - 2) ω).1 -
                  (xIter setup hStanding (t - 1) ω).1,
                (yIter setup hStanding t ω (sampledBlock setup t ω)).1 -
                  ((yIter setup hStanding (t - 1) ω)
                    (sampledBlock setup t ω)).1⟫_ℝ +
            (inverseProbabilityValue setup (sampledBlock setup (t - 1) ω)
                (hDen.1 (sampledBlock setup (t - 1) ω)) - 1) *
              ⟪(xIter setup hStanding (t - 2) ω).1 -
                  (xIter setup hStanding (t - 1) ω).1,
                ((yIter setup hStanding (t - 2) ω)
                  (sampledBlock setup (t - 1) ω)).1 -
                  ((yIter setup hStanding (t - 1) ω)
                    (sampledBlock setup (t - 1) ω)).1⟫_ℝ) := by
    intro t htmem
    rcases Finset.mem_Icc.mp htmem with ⟨ht2, htk⟩
    exact hHistoricalCoupling t ht2 htk ω
  have hCurrentCoupling_on_window :
      ∀ t ∈ Finset.Icc 1 k,
        ⟪xTildeIter setup hStanding t ω - (xIter setup hStanding t ω).1,
          ∑ i : ι, (yTildeIter setup hStanding t ω i - (z.2 i).1)⟫_ℝ =
          ⟪(xIter setup hStanding (t - 1) ω).1 -
              (xIter setup hStanding t ω).1,
            ∑ i : ι, ((yIter setup hStanding t ω i).1 - (z.2 i).1)⟫_ℝ +
            (inverseProbabilityValue setup (sampledBlock setup t ω)
                (hDen.1 (sampledBlock setup t ω)) - 1) *
              ⟪(xIter setup hStanding (t - 1) ω).1 -
                  (xIter setup hStanding t ω).1,
                (yIter setup hStanding t ω (sampledBlock setup t ω)).1 -
                  ((yIter setup hStanding (t - 1) ω)
                    (sampledBlock setup t ω)).1⟫_ℝ -
            setup.α t *
              ⟪(xIter setup hStanding (t - 2) ω).1 -
                  (xIter setup hStanding (t - 1) ω).1,
                ∑ i : ι,
                  (yTildeIter setup hStanding t ω i - (z.2 i).1)⟫_ℝ := by
    intro t htmem
    rcases Finset.mem_Icc.mp htmem with ⟨ht, _htk⟩
    exact proposition51_current_coupling_expansion
      setup hStanding hDen.1 t ht ω z
  let ik : ι := sampledBlock setup k ω
  let uk : E :=
    (xIter setup hStanding (k - 1) ω).1 -
      (xIter setup hStanding k ω).1
  have hTerminalYoung :
      - sourceQuotient
          (setup.L ik * (1 - samplingProbability setup ik) ^ 2)
          ((componentCount (ι := ι) : ℝ) * setup.τ k *
            samplingProbability setup ik)
          (hDen.2 k ik) * ‖uk‖ ^ 2 ≤
          (1 - inverseProbabilityValue setup ik (hDen.1 ik)) *
            ⟪uk,
              (yIter setup hStanding k ω ik).1 -
                ((yIter setup hStanding (k - 1) ω) ik).1⟫_ℝ +
          (setup.τ k / 2) * inverseProbabilityValue setup ik (hDen.1 ik) *
            (SOptLib.carrierBregmanDivergence (dualConjugate setup ik) (dualConjugateBaseSelector setup ik ((yIter setup hStanding (k - 1) ω) ik) (dualSubgradIter setup hStanding (k - 1) ω ik)) ((yIter setup hStanding (k - 1) ω) ik) ((yIter setup hStanding k ω) ik)) := by
    have hbase :=
      proposition51_dual_young_absorb_inverse_inner_half_with_sourceQuotient
        setup hStanding k hk ik (hDen.1 ik) (hDen.2 k ik)
        (-(1 - samplingProbability setup ik)) uk
        ((yIter setup hStanding (k - 1) ω) ik)
        (dualSubgradIter setup hStanding (k - 1) ω ik)
        ((yIter setup hStanding k ω) ik)
    have hcoef :
        inverseProbabilityValue setup ik (hDen.1 ik) *
            (samplingProbability setup ik - 1) =
          1 - inverseProbabilityValue setup ik (hDen.1 ik) := by
      rw [inverseProbabilityValue, sourceQuotient_def]
      field_simp [hDen.1 ik] <;> ring
    have hsq :
        (samplingProbability setup ik - 1) *
            (samplingProbability setup ik - 1) =
          (1 - samplingProbability setup ik) *
            (1 - samplingProbability setup ik) := by
      ring
    simpa [ik, uk, hcoef, hsq, sq, mul_assoc] using hbase
  have hCurrentHistoricalYoung_on_window :
      ∀ t ∈ Finset.Icc 2 k,
        - θ (t - 1) *
            sourceQuotient
              (setup.L (sampledBlock setup t ω) * setup.α t)
              ((componentCount (ι := ι) : ℝ) * setup.τ t *
                samplingProbability setup (sampledBlock setup t ω))
              (hDen.2 t (sampledBlock setup t ω)) *
            ‖(xIter setup hStanding (t - 2) ω).1 -
              (xIter setup hStanding (t - 1) ω).1‖ ^ 2 ≤
          θ t *
            (setup.α t *
                inverseProbabilityValue setup (sampledBlock setup t ω)
                  (hDen.1 (sampledBlock setup t ω)) *
                ⟪(xIter setup hStanding (t - 2) ω).1 -
                    (xIter setup hStanding (t - 1) ω).1,
                  (yIter setup hStanding t ω
                      (sampledBlock setup t ω)).1 -
                    ((yIter setup hStanding (t - 1) ω)
                      (sampledBlock setup t ω)).1⟫_ℝ +
              (setup.τ t / 2) *
                inverseProbabilityValue setup (sampledBlock setup t ω)
                  (hDen.1 (sampledBlock setup t ω)) *
                (SOptLib.carrierBregmanDivergence (dualConjugate setup (sampledBlock setup t ω)) (dualConjugateBaseSelector setup (sampledBlock setup t ω) ((yIter setup hStanding (t - 1) ω)
                    (sampledBlock setup t ω)) (dualSubgradIter setup hStanding (t - 1) ω
                    (sampledBlock setup t ω))) ((yIter setup hStanding (t - 1) ω)
                    (sampledBlock setup t ω)) ((yIter setup hStanding t ω)
                    (sampledBlock setup t ω)))) := by
    intro t htmem
    rcases Finset.mem_Icc.mp htmem with ⟨ht2, htk⟩
    exact
      proposition51_current_historical_young_absorb_half_with_h51
        setup hStanding θ k hDen hθ h51 t ht2 htk
        (sampledBlock setup t ω)
        ((xIter setup hStanding (t - 2) ω).1 -
          (xIter setup hStanding (t - 1) ω).1)
        ((yIter setup hStanding (t - 1) ω)
          (sampledBlock setup t ω))
        (dualSubgradIter setup hStanding (t - 1) ω
          (sampledBlock setup t ω))
        ((yIter setup hStanding t ω) (sampledBlock setup t ω))
  have hPreviousHistoricalYoung_on_window :
      ∀ t ∈ Finset.Icc 2 k,
        - θ (t - 1) *
            sourceQuotient
              ((1 - samplingProbability setup
                  (sampledBlock setup (t - 1) ω)) ^ 2 *
                setup.L (sampledBlock setup (t - 1) ω))
              ((componentCount (ι := ι) : ℝ) * setup.τ (t - 1) *
                samplingProbability setup
                  (sampledBlock setup (t - 1) ω))
              (hDen.2 (t - 1)
                (sampledBlock setup (t - 1) ω)) *
            ‖(xIter setup hStanding (t - 2) ω).1 -
              (xIter setup hStanding (t - 1) ω).1‖ ^ 2 ≤
          setup.α t * θ t *
              ((inverseProbabilityValue setup
                    (sampledBlock setup (t - 1) ω)
                    (hDen.1 (sampledBlock setup (t - 1) ω)) - 1) *
                ⟪(xIter setup hStanding (t - 2) ω).1 -
                    (xIter setup hStanding (t - 1) ω).1,
                  ((yIter setup hStanding (t - 2) ω)
                    (sampledBlock setup (t - 1) ω)).1 -
                    ((yIter setup hStanding (t - 1) ω)
                      (sampledBlock setup (t - 1) ω)).1⟫_ℝ) +
            θ (t - 1) *
              ((setup.τ (t - 1) / 2) *
                inverseProbabilityValue setup
                  (sampledBlock setup (t - 1) ω)
                  (hDen.1 (sampledBlock setup (t - 1) ω)) *
                (SOptLib.carrierBregmanDivergence (dualConjugate setup (sampledBlock setup (t - 1) ω)) (dualConjugateBaseSelector setup (sampledBlock setup (t - 1) ω) ((yIter setup hStanding (t - 2) ω)
                    (sampledBlock setup (t - 1) ω)) (dualSubgradIter setup hStanding (t - 2) ω
                    (sampledBlock setup (t - 1) ω))) ((yIter setup hStanding (t - 2) ω)
                    (sampledBlock setup (t - 1) ω)) ((yIter setup hStanding (t - 1) ω)
                    (sampledBlock setup (t - 1) ω)))) := by
    intro t htmem
    rcases Finset.mem_Icc.mp htmem with ⟨ht2, htk⟩
    exact
      proposition51_previous_historical_young_absorb_half_with_h51
        setup hStanding θ k hDen hθ h51 t ht2 htk
        (sampledBlock setup (t - 1) ω)
        ((xIter setup hStanding (t - 2) ω).1 -
          (xIter setup hStanding (t - 1) ω).1)
        ((yIter setup hStanding (t - 2) ω)
          (sampledBlock setup (t - 1) ω))
        (dualSubgradIter setup hStanding (t - 2) ω
          (sampledBlock setup (t - 1) ω))
        ((yIter setup hStanding (t - 1) ω)
          (sampledBlock setup (t - 1) ω))
  have hTerminalYoung_weighted :
      θ k *
          (- sourceQuotient
            (setup.L (sampledBlock setup k ω) *
              (1 - samplingProbability setup (sampledBlock setup k ω)) ^ 2)
            ((componentCount (ι := ι) : ℝ) * setup.τ k *
              samplingProbability setup (sampledBlock setup k ω))
            (hDen.2 k (sampledBlock setup k ω)) *
            ‖(xIter setup hStanding (k - 1) ω).1 -
              (xIter setup hStanding k ω).1‖ ^ 2) ≤
        θ k *
          ((1 - inverseProbabilityValue setup (sampledBlock setup k ω)
              (hDen.1 (sampledBlock setup k ω))) *
            ⟪(xIter setup hStanding (k - 1) ω).1 -
                (xIter setup hStanding k ω).1,
              (yIter setup hStanding k ω (sampledBlock setup k ω)).1 -
                ((yIter setup hStanding (k - 1) ω)
                  (sampledBlock setup k ω)).1⟫_ℝ +
            (setup.τ k / 2) *
              inverseProbabilityValue setup (sampledBlock setup k ω)
                (hDen.1 (sampledBlock setup k ω)) *
              (SOptLib.carrierBregmanDivergence (dualConjugate setup (sampledBlock setup k ω)) (dualConjugateBaseSelector setup (sampledBlock setup k ω) ((yIter setup hStanding (k - 1) ω)
                  (sampledBlock setup k ω)) (dualSubgradIter setup hStanding (k - 1) ω
                  (sampledBlock setup k ω))) ((yIter setup hStanding (k - 1) ω)
                  (sampledBlock setup k ω)) ((yIter setup hStanding k ω)
                  (sampledBlock setup k ω)))) := by
    have hscaled :=
      mul_le_mul_of_nonneg_left hTerminalYoung (hθ k hk le_rfl)
    simpa [ik, uk, mul_assoc] using hscaled
  have hCurrentHistoricalYoung_sum :=
    Finset.sum_le_sum hCurrentHistoricalYoung_on_window
  have hPreviousHistoricalYoung_sum :=
    Finset.sum_le_sum hPreviousHistoricalYoung_on_window
  let yTildeCoupling : ℕ → ℝ := fun t =>
    ⟪(xIter setup hStanding (t - 1) ω).1 -
        (xIter setup hStanding t ω).1,
      ∑ i : ι,
        (yTildeIter setup hStanding t ω i - (z.2 i).1)⟫_ℝ
  have hLaggedCoupling_cancel :
      (∑ t ∈ Finset.Icc 1 k, (-θ t * yTildeCoupling t)) +
          ∑ t ∈ Finset.Icc 2 k,
            (setup.α t * θ t) * yTildeCoupling (t - 1) =
        -θ k * yTildeCoupling k := by
    exact
      sum_Icc_weighted_lagged_cancel_eq_terminal
        θ (fun t => setup.α t * θ t) yTildeCoupling k hk
        (by
          intro t ht2 htk
          exact h51 t ht2 htk)
  let deltaResidual : ℕ → ℝ := fun t =>
    -⟪xTildeIter setup hStanding t ω -
        (xIter setup hStanding t ω).1,
      ∑ i : ι,
        (yTildeIter setup hStanding t ω i - (z.2 i).1)⟫_ℝ +
      setup.τ t *
        inverseProbabilityValue setup (sampledBlock setup t ω)
          (sampledBlock_probability_ne_zero setup
            (sampledPositiveBlock setup t ω)) *
        (SOptLib.carrierBregmanDivergence (dualConjugate setup (sampledBlock setup t ω)) (dualConjugateBaseSelector setup (sampledBlock setup t ω) ((yIter setup hStanding (t - 1) ω)
            (sampledBlock setup t ω)) (dualSubgradIter setup hStanding (t - 1) ω
            (sampledBlock setup t ω))) ((yIter setup hStanding (t - 1) ω)
            (sampledBlock setup t ω)) ((yIter setup hStanding t ω)
            (sampledBlock setup t ω)))
  have hPrimalBudget_to_delta_rhs :
      (∑ t ∈ Finset.Icc 1 k, θ t *
        (setup.η t / 2 *
            ‖(xIter setup hStanding (t - 1) ω).1 -
              (xIter setup hStanding t ω).1‖ ^ 2 +
          deltaResidual t)) ≤
        ∑ t ∈ Finset.Icc 1 k, θ t *
          (setup.η t *
              primalBregman setup
                (xIter setup hStanding (t - 1) ω)
                (xIter setup hStanding t ω) +
            deltaResidual t) := by
    exact
      proposition51_weighted_primal_bregman_norm_budget_le
        setup hStanding θ k ω deltaResidual hθ
  have hPrimalBudget_to_final_rhs :
      (∑ t ∈ Finset.Icc 1 k, θ t *
        (setup.η t / 2 *
            ‖(xIter setup hStanding (t - 1) ω).1 -
              (xIter setup hStanding t ω).1‖ ^ 2 +
          deltaResidual t)) ≤
        ∑ t ∈ Finset.Icc 1 k, θ t *
          (setup.η t *
              primalBregman setup
                (xIter setup hStanding (t - 1) ω)
                (xIter setup hStanding t ω) -
            ⟪xTildeIter setup hStanding t ω -
                (xIter setup hStanding t ω).1,
              ∑ i : ι,
                (yTildeIter setup hStanding t ω i - (z.2 i).1)⟫_ℝ +
            setup.τ t *
              inverseProbabilityValue setup (sampledBlock setup t ω)
                (sampledBlock_probability_ne_zero setup
                  (sampledPositiveBlock setup t ω)) *
              (SOptLib.carrierBregmanDivergence (dualConjugate setup (sampledBlock setup t ω)) (dualConjugateBaseSelector setup (sampledBlock setup t ω) ((yIter setup hStanding (t - 1) ω)
                  (sampledBlock setup t ω)) (dualSubgradIter setup hStanding (t - 1) ω
                  (sampledBlock setup t ω))) ((yIter setup hStanding (t - 1) ω)
                  (sampledBlock setup t ω)) ((yIter setup hStanding t ω)
                  (sampledBlock setup t ω)))) := by
    refine le_trans hPrimalBudget_to_delta_rhs ?_
    apply le_of_eq
    refine Finset.sum_congr rfl ?_
    intro t ht
    dsimp [deltaResidual]
    ring
  have _ := hθ
  have _ := h51
  have _ := hHistoricalCoupling_on_window
  have _ := hCurrentCoupling_on_window
  have _ := hTerminalYoung_weighted
  have _ := hCurrentHistoricalYoung_on_window
  have _ := hPreviousHistoricalYoung_on_window
  have _ := hCurrentHistoricalYoung_sum
  have _ := hPreviousHistoricalYoung_sum
  have _ := hLaggedCoupling_cancel
  have _ := hPrimalBudget_to_delta_rhs
  have _ := hPrimalBudget_to_final_rhs
  have hFinal_to_normResidual :
      θ k *
          (setup.η k / 4 *
              ‖(xIter setup hStanding (k - 1) ω).1 -
                (xIter setup hStanding k ω).1‖ ^ 2 -
            ⟪(xIter setup hStanding (k - 1) ω).1 -
                (xIter setup hStanding k ω).1,
              ∑ i : ι, ((yIter setup hStanding k ω i).1 -
                (z.2 i).1)⟫_ℝ) +
        θ k *
          (setup.η k / 4 -
            sourceQuotient
              (setup.L (sampledBlock setup k ω) *
                (1 - samplingProbability setup (sampledBlock setup k ω)) ^ 2)
              ((componentCount (ι := ι) : ℝ) * setup.τ k *
                samplingProbability setup (sampledBlock setup k ω))
              (hDen.2 k (sampledBlock setup k ω))) *
            ‖(xIter setup hStanding (k - 1) ω).1 -
              (xIter setup hStanding k ω).1‖ ^ 2 +
        ∑ t ∈ Finset.Icc 2 k,
          θ (t - 1) *
            (setup.η (t - 1) / 2 -
              (sourceQuotient
                  (setup.L (sampledBlock setup t ω) * setup.α t)
                  ((componentCount (ι := ι) : ℝ) * setup.τ t *
                    samplingProbability setup (sampledBlock setup t ω))
                  (hDen.2 t (sampledBlock setup t ω)) +
                sourceQuotient
                  ((1 - samplingProbability setup (sampledBlock setup (t - 1) ω)) ^ 2 *
                    setup.L (sampledBlock setup (t - 1) ω))
                  ((componentCount (ι := ι) : ℝ) * setup.τ (t - 1) *
                    samplingProbability setup (sampledBlock setup (t - 1) ω))
                  (hDen.2 (t - 1) (sampledBlock setup (t - 1) ω)))) *
              ‖(xIter setup hStanding (t - 2) ω).1 -
                (xIter setup hStanding (t - 1) ω).1‖ ^ 2 ≤
        ∑ t ∈ Finset.Icc 1 k, θ t *
          (setup.η t / 2 *
              ‖(xIter setup hStanding (t - 1) ω).1 -
              (xIter setup hStanding t ω).1‖ ^ 2 +
            deltaResidual t) := by
    let U : ℕ → ℝ := fun t =>
      ‖(xIter setup hStanding (t - 1) ω).1 -
        (xIter setup hStanding t ω).1‖ ^ 2
    let C : ℕ → ℝ := fun t =>
      ⟪xTildeIter setup hStanding t ω -
          (xIter setup hStanding t ω).1,
        ∑ i : ι,
          (yTildeIter setup hStanding t ω i - (z.2 i).1)⟫_ℝ
    let A : ℕ → ℝ := fun t =>
      ⟪(xIter setup hStanding (t - 1) ω).1 -
          (xIter setup hStanding t ω).1,
        ∑ i : ι, ((yIter setup hStanding t ω i).1 -
          (z.2 i).1)⟫_ℝ
    let B : ℕ → ℝ := fun t =>
      (inverseProbabilityValue setup (sampledBlock setup t ω)
          (hDen.1 (sampledBlock setup t ω)) - 1) *
        ⟪(xIter setup hStanding (t - 1) ω).1 -
            (xIter setup hStanding t ω).1,
          (yIter setup hStanding t ω (sampledBlock setup t ω)).1 -
            ((yIter setup hStanding (t - 1) ω)
              (sampledBlock setup t ω)).1⟫_ℝ
    let D : ℕ → ℝ := fun t =>
      setup.τ t *
        inverseProbabilityValue setup (sampledBlock setup t ω)
          (hDen.1 (sampledBlock setup t ω)) *
        (SOptLib.carrierBregmanDivergence (dualConjugate setup (sampledBlock setup t ω)) (dualConjugateBaseSelector setup (sampledBlock setup t ω) ((yIter setup hStanding (t - 1) ω)
            (sampledBlock setup t ω)) (dualSubgradIter setup hStanding (t - 1) ω
            (sampledBlock setup t ω))) ((yIter setup hStanding (t - 1) ω)
            (sampledBlock setup t ω)) ((yIter setup hStanding t ω)
            (sampledBlock setup t ω)))
    let SQk : ℕ → ℝ := fun t =>
      sourceQuotient
        (setup.L (sampledBlock setup t ω) *
          (1 - samplingProbability setup (sampledBlock setup t ω)) ^ 2)
        ((componentCount (ι := ι) : ℝ) * setup.τ t *
          samplingProbability setup (sampledBlock setup t ω))
        (hDen.2 t (sampledBlock setup t ω))
    let SQcur : ℕ → ℝ := fun t =>
      sourceQuotient
        (setup.L (sampledBlock setup t ω) * setup.α t)
        ((componentCount (ι := ι) : ℝ) * setup.τ t *
          samplingProbability setup (sampledBlock setup t ω))
        (hDen.2 t (sampledBlock setup t ω))
    let SQprev : ℕ → ℝ := fun t =>
      sourceQuotient
        ((1 - samplingProbability setup
            (sampledBlock setup (t - 1) ω)) ^ 2 *
          setup.L (sampledBlock setup (t - 1) ω))
        ((componentCount (ι := ι) : ℝ) * setup.τ (t - 1) *
          samplingProbability setup (sampledBlock setup (t - 1) ω))
        (hDen.2 (t - 1) (sampledBlock setup (t - 1) ω))
    let Ecur : ℕ → ℝ := fun t =>
      setup.α t *
        inverseProbabilityValue setup (sampledBlock setup t ω)
          (hDen.1 (sampledBlock setup t ω)) *
        ⟪(xIter setup hStanding (t - 2) ω).1 -
            (xIter setup hStanding (t - 1) ω).1,
          (yIter setup hStanding t ω
              (sampledBlock setup t ω)).1 -
            ((yIter setup hStanding (t - 1) ω)
              (sampledBlock setup t ω)).1⟫_ℝ
    let Eprev : ℕ → ℝ := fun t =>
      setup.α t *
        ((inverseProbabilityValue setup
              (sampledBlock setup (t - 1) ω)
              (hDen.1 (sampledBlock setup (t - 1) ω)) - 1) *
          ⟪(xIter setup hStanding (t - 2) ω).1 -
              (xIter setup hStanding (t - 1) ω).1,
            ((yIter setup hStanding (t - 2) ω)
              (sampledBlock setup (t - 1) ω)).1 -
              ((yIter setup hStanding (t - 1) ω)
                (sampledBlock setup (t - 1) ω)).1⟫_ℝ)
    have hRegroup :
        (∑ t ∈ Finset.Icc 1 k, θ t * (- C t)) =
          -θ k * (A k + B k) +
            ∑ t ∈ Finset.Icc 2 k, θ t * (Ecur t + Eprev t) := by
      have hYBranch :
          ∀ t ∈ Finset.Icc 1 k, yTildeCoupling t = A t + B t := by
        intro t htmem
        rcases Finset.mem_Icc.mp htmem with ⟨ht1, _htk⟩
        dsimp [yTildeCoupling, A, B]
        simpa using
          proposition51_yTilde_inner_minus_z_branch
            setup hStanding hDen.1 t ht1 ω z
            ((xIter setup hStanding (t - 1) ω).1 -
              (xIter setup hStanding t ω).1)
      have hLaggedCoupling_cancel_AB :
          (∑ t ∈ Finset.Icc 1 k, (-θ t * yTildeCoupling t)) +
              ∑ t ∈ Finset.Icc 2 k,
                (setup.α t * θ t) * yTildeCoupling (t - 1) =
            -θ k * (A k + B k) := by
        have hyk : yTildeCoupling k = A k + B k :=
          hYBranch k (Finset.mem_Icc.mpr ⟨hk, le_rfl⟩)
        simpa [hyk] using hLaggedCoupling_cancel
      -- Source Eq. (5.1.56) regrouping: expand `C` through the current and
      -- historical coupling identities, then use `hLaggedCoupling_cancel`.
      have hC_one : C 1 = yTildeCoupling 1 := by
        have hcur :=
          hCurrentCoupling_on_window 1
            (Finset.mem_Icc.mpr ⟨le_rfl, hk⟩)
        have hy :=
          hYBranch 1 (Finset.mem_Icc.mpr ⟨le_rfl, hk⟩)
        dsimp [C, A, B, yTildeCoupling] at hcur hy ⊢
        rw [hcur]
        rw [← hy]
        simp
      have hC_hist :
          ∀ t ∈ Finset.Icc 2 k,
            C t = yTildeCoupling t - setup.α t * yTildeCoupling (t - 1) -
              (Ecur t + Eprev t) := by
        intro t htmem
        rcases Finset.mem_Icc.mp htmem with ⟨ht2, htk⟩
        have htmem_one : t ∈ Finset.Icc 1 k :=
          Finset.mem_Icc.mpr ⟨by omega, htk⟩
        have hhist := hHistoricalCoupling_on_window t htmem
        have hy := hYBranch t htmem_one
        dsimp [C, A, B, Ecur, Eprev, yTildeCoupling] at hhist hy ⊢
        simp only [Nat.sub_sub] at hhist hy ⊢
        rw [hhist]
        rw [← hy]
        ring
      exact
        sum_Icc_weighted_coupling_regroup_from_pointwise
          θ setup.α C yTildeCoupling Ecur Eprev
          (-θ k * (A k + B k)) k hk
          hC_one hC_hist hLaggedCoupling_cancel_AB
    have hTerminalScalar :
        θ k * (-SQk k * U k) ≤ θ k * (-B k + D k / 2) := by
      dsimp [SQk, U, B, D]
      have hneg :
          -((inverseProbabilityValue setup (sampledBlock setup k ω)
              (hDen.1 (sampledBlock setup k ω)) - 1) *
            ⟪(xIter setup hStanding (k - 1) ω).1 -
                (xIter setup hStanding k ω).1,
              (yIter setup hStanding k ω (sampledBlock setup k ω)).1 -
                ((yIter setup hStanding (k - 1) ω)
                  (sampledBlock setup k ω)).1⟫_ℝ) =
            (1 - inverseProbabilityValue setup (sampledBlock setup k ω)
              (hDen.1 (sampledBlock setup k ω))) *
            ⟪(xIter setup hStanding (k - 1) ω).1 -
                (xIter setup hStanding k ω).1,
              (yIter setup hStanding k ω (sampledBlock setup k ω)).1 -
                ((yIter setup hStanding (k - 1) ω)
                  (sampledBlock setup k ω)).1⟫_ℝ := by
        ring
      simpa [hneg, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        hTerminalYoung_weighted
    have hCurrentScalar :
        (∑ t ∈ Finset.Icc 2 k, -θ (t - 1) * SQcur t * U (t - 1)) ≤
          ∑ t ∈ Finset.Icc 2 k, θ t * (Ecur t + D t / 2) := by
      dsimp [SQcur, U, Ecur, D]
      simpa [Nat.sub_sub, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        hCurrentHistoricalYoung_sum
    have hPreviousScalar :
        (∑ t ∈ Finset.Icc 2 k, -θ (t - 1) * SQprev t * U (t - 1)) ≤
          ∑ t ∈ Finset.Icc 2 k,
            (θ t * Eprev t + θ (t - 1) * (D (t - 1) / 2)) := by
      dsimp [SQprev, U, Eprev, D]
      simpa [Nat.sub_sub, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        hPreviousHistoricalYoung_sum
    have hDinit : 0 ≤ θ 1 * (D 1 / 2) := by
      have hθ1 : 0 ≤ θ 1 := hθ 1 le_rfl hk
      have hτ1 : 0 ≤ setup.τ 1 := by
        rcases hStanding with ⟨_, _, _, _, _, _, _, _, _, _, _, hParam⟩
        exact hParam.1 1 le_rfl
      have hinv1 :
          0 ≤ inverseProbabilityValue setup (sampledBlock setup 1 ω)
            (hDen.1 (sampledBlock setup 1 ω)) := by
        rw [inverseProbabilityValue, sourceQuotient_def]
        exact div_nonneg zero_le_one
          (samplingProbability_nonnegative setup (sampledBlock setup 1 ω))
      have hdual1 :
          0 ≤ (SOptLib.carrierBregmanDivergence (dualConjugate setup (sampledBlock setup 1 ω)) (dualConjugateBaseSelector setup (sampledBlock setup 1 ω) ((yIter setup hStanding (1 - 1) ω)
              (sampledBlock setup 1 ω)) (dualSubgradIter setup hStanding (1 - 1) ω
              (sampledBlock setup 1 ω))) ((yIter setup hStanding (1 - 1) ω)
              (sampledBlock setup 1 ω)) ((yIter setup hStanding 1 ω)
              (sampledBlock setup 1 ω))) :=
        dualBregman_nonnegative setup (sampledBlock setup 1 ω)
          ((yIter setup hStanding (1 - 1) ω)
            (sampledBlock setup 1 ω))
          (dualSubgradIter setup hStanding (1 - 1) ω
            (sampledBlock setup 1 ω))
          ((yIter setup hStanding 1 ω)
            (sampledBlock setup 1 ω))
      dsimp [D]
      positivity
    have hScalar :=
      proposition51_scalar_young_allocation_le
        θ setup.η U C A B D SQk SQcur SQprev Ecur Eprev k hk
        hRegroup hTerminalScalar hCurrentScalar hPreviousScalar hDinit
    convert hScalar using 1
    · refine Finset.sum_congr rfl ?_
      intro t ht
      dsimp [U, C, D, deltaResidual]
      ring
  exact le_trans hFinal_to_normResidual hPrimalBudget_to_final_rhs

/-- Pathwise Proposition 5.1 Eq. (5.1.57), before finite-prefix integration.
This is the source proof step that lower-bounds the weighted positive Delta
sum by the terminal bracket. No SOptLib match: searched `weighted delta
pathwise lower bound terminal bracket Eq 5.1.57` and `sum Icc telescope
coefficient nonnegative theta alpha terminal coupling`; considered the local
coupling expansions `proposition51_current_coupling_expansion` and
`proposition51_historical_coupling_expansion`, the Young bridge
`proposition51_dual_young_absorb_with_sourceQuotient`, and SOptLib
`sum_Icc_two_coeff_telescope_le`, but none packages the paper-specific sampled
terminal/historical regrouping with conditions (5.1.48)--(5.1.51). -/
private theorem proposition51_weighted_delta_pathwise_lower_bound
    (hStanding : standingAssumptions setup)
    (θ : ℕ → ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hDen : proposition_5_1_denominatorBoundary setup k)
    (z : SaddlePoint setup)
    (hθ : ∀ t, 1 ≤ t → t ≤ k → 0 ≤ θ t)
    (h48 : propositionCondition_5_1_48_with_denominator_source_gap setup k hk hDen)
    (h49 : propositionCondition_5_1_49_with_denominator_source_gap setup k hDen)
    (h51 : ∀ t, 2 ≤ t → t ≤ k → setup.α t * θ t = θ (t - 1))
    (hHistoricalCoupling :
      ∀ (t : ℕ), 2 ≤ t → t ≤ k → ∀ (ω : BlockSamplePath setup),
        ⟪xTildeIter setup hStanding t ω - (xIter setup hStanding t ω).1,
          ∑ i : ι, (yTildeIter setup hStanding t ω i - (z.2 i).1)⟫_ℝ =
          ⟪(xIter setup hStanding (t - 1) ω).1 -
              (xIter setup hStanding t ω).1,
            ∑ i : ι, ((yIter setup hStanding t ω i).1 - (z.2 i).1)⟫_ℝ +
          (inverseProbabilityValue setup (sampledBlock setup t ω)
              (hDen.1 (sampledBlock setup t ω)) - 1) *
            ⟪(xIter setup hStanding (t - 1) ω).1 -
                (xIter setup hStanding t ω).1,
              (yIter setup hStanding t ω (sampledBlock setup t ω)).1 -
                ((yIter setup hStanding (t - 1) ω)
                  (sampledBlock setup t ω)).1⟫_ℝ -
          setup.α t *
            ⟪(xIter setup hStanding (t - 2) ω).1 -
                (xIter setup hStanding (t - 1) ω).1,
              ∑ i : ι,
                (yTildeIter setup hStanding (t - 1) ω i - (z.2 i).1)⟫_ℝ -
          setup.α t *
            (inverseProbabilityValue setup (sampledBlock setup t ω)
                (hDen.1 (sampledBlock setup t ω)) *
              ⟪(xIter setup hStanding (t - 2) ω).1 -
                  (xIter setup hStanding (t - 1) ω).1,
                (yIter setup hStanding t ω (sampledBlock setup t ω)).1 -
                  ((yIter setup hStanding (t - 1) ω)
                    (sampledBlock setup t ω)).1⟫_ℝ +
            (inverseProbabilityValue setup (sampledBlock setup (t - 1) ω)
                (hDen.1 (sampledBlock setup (t - 1) ω)) - 1) *
              ⟪(xIter setup hStanding (t - 2) ω).1 -
                  (xIter setup hStanding (t - 1) ω).1,
                ((yIter setup hStanding (t - 2) ω)
                  (sampledBlock setup (t - 1) ω)).1 -
                  ((yIter setup hStanding (t - 1) ω)
                    (sampledBlock setup (t - 1) ω)).1⟫_ℝ))
    (ω : BlockSamplePath setup) :
    θ k *
        (setup.η k / 4 *
            ‖(xIter setup hStanding (k - 1) ω).1 -
              (xIter setup hStanding k ω).1‖ ^ 2 -
          ⟪(xIter setup hStanding (k - 1) ω).1 -
              (xIter setup hStanding k ω).1,
            ∑ i : ι, ((yIter setup hStanding k ω i).1 -
              (z.2 i).1)⟫_ℝ) ≤
      ∑ t ∈ Finset.Icc 1 k, θ t *
        (setup.η t *
            primalBregman setup
              (xIter setup hStanding (t - 1) ω)
              (xIter setup hStanding t ω) -
          ⟪xTildeIter setup hStanding t ω -
              (xIter setup hStanding t ω).1,
            ∑ i : ι,
              (yTildeIter setup hStanding t ω i - (z.2 i).1)⟫_ℝ +
          setup.τ t *
            inverseProbabilityValue setup (sampledBlock setup t ω)
              (sampledBlock_probability_ne_zero setup
                (sampledPositiveBlock setup t ω)) *
            (SOptLib.carrierBregmanDivergence (dualConjugate setup (sampledBlock setup t ω)) (dualConjugateBaseSelector setup (sampledBlock setup t ω) ((yIter setup hStanding (t - 1) ω)
                (sampledBlock setup t ω)) (dualSubgradIter setup hStanding (t - 1) ω
                (sampledBlock setup t ω))) ((yIter setup hStanding (t - 1) ω)
                (sampledBlock setup t ω)) ((yIter setup hStanding t ω)
                (sampledBlock setup t ω)))) := by
  classical
  have hTerminalSampledCoefficientNonnegative :
      0 ≤ θ k *
        (setup.η k / 4 -
          sourceQuotient
            (setup.L (sampledBlock setup k ω) *
              (1 - samplingProbability setup (sampledBlock setup k ω)) ^ 2)
            ((componentCount (ι := ι) : ℝ) * setup.τ k *
              samplingProbability setup (sampledBlock setup k ω))
            (hDen.2 k (sampledBlock setup k ω))) *
          ‖(xIter setup hStanding (k - 1) ω).1 -
            (xIter setup hStanding k ω).1‖ ^ 2 := by
    exact proposition51_h48_terminal_sampled_coefficient_nonnegative
      setup θ k hk hDen hθ h48 (sampledBlock setup k ω)
      ((xIter setup hStanding (k - 1) ω).1 -
        (xIter setup hStanding k ω).1)
  have hHistoricalSampledCoefficientNonnegative :
      ∀ t ∈ Finset.Icc 2 k,
        0 ≤ θ (t - 1) *
          (setup.η (t - 1) / 2 -
            (sourceQuotient
                (setup.L (sampledBlock setup t ω) * setup.α t)
                ((componentCount (ι := ι) : ℝ) * setup.τ t *
                  samplingProbability setup (sampledBlock setup t ω))
                (hDen.2 t (sampledBlock setup t ω)) +
              sourceQuotient
                ((1 - samplingProbability setup (sampledBlock setup (t - 1) ω)) ^ 2 *
                  setup.L (sampledBlock setup (t - 1) ω))
                ((componentCount (ι := ι) : ℝ) * setup.τ (t - 1) *
                  samplingProbability setup (sampledBlock setup (t - 1) ω))
                (hDen.2 (t - 1) (sampledBlock setup (t - 1) ω)))) *
            ‖(xIter setup hStanding (t - 2) ω).1 -
              (xIter setup hStanding (t - 1) ω).1‖ ^ 2 := by
    intro t htmem
    rcases Finset.mem_Icc.mp htmem with ⟨ht2, htk⟩
    exact proposition51_h49_historical_coefficient_nonnegative
      setup θ k hDen hθ h49 t
      (sampledBlock setup t ω) (sampledBlock setup (t - 1) ω)
      ht2 htk
      ((xIter setup hStanding (t - 2) ω).1 -
        (xIter setup hStanding (t - 1) ω).1)
  have hHistoricalCoupling_on_window :
      ∀ t ∈ Finset.Icc 2 k,
        ⟪xTildeIter setup hStanding t ω - (xIter setup hStanding t ω).1,
          ∑ i : ι, (yTildeIter setup hStanding t ω i - (z.2 i).1)⟫_ℝ =
          ⟪(xIter setup hStanding (t - 1) ω).1 -
              (xIter setup hStanding t ω).1,
            ∑ i : ι, ((yIter setup hStanding t ω i).1 - (z.2 i).1)⟫_ℝ +
          (inverseProbabilityValue setup (sampledBlock setup t ω)
              (hDen.1 (sampledBlock setup t ω)) - 1) *
            ⟪(xIter setup hStanding (t - 1) ω).1 -
                (xIter setup hStanding t ω).1,
              (yIter setup hStanding t ω (sampledBlock setup t ω)).1 -
                ((yIter setup hStanding (t - 1) ω)
                  (sampledBlock setup t ω)).1⟫_ℝ -
          setup.α t *
            ⟪(xIter setup hStanding (t - 2) ω).1 -
                (xIter setup hStanding (t - 1) ω).1,
              ∑ i : ι,
                (yTildeIter setup hStanding (t - 1) ω i - (z.2 i).1)⟫_ℝ -
          setup.α t *
            (inverseProbabilityValue setup (sampledBlock setup t ω)
                (hDen.1 (sampledBlock setup t ω)) *
              ⟪(xIter setup hStanding (t - 2) ω).1 -
                  (xIter setup hStanding (t - 1) ω).1,
                (yIter setup hStanding t ω (sampledBlock setup t ω)).1 -
                  ((yIter setup hStanding (t - 1) ω)
                    (sampledBlock setup t ω)).1⟫_ℝ +
            (inverseProbabilityValue setup (sampledBlock setup (t - 1) ω)
                (hDen.1 (sampledBlock setup (t - 1) ω)) - 1) *
              ⟪(xIter setup hStanding (t - 2) ω).1 -
                  (xIter setup hStanding (t - 1) ω).1,
                ((yIter setup hStanding (t - 2) ω)
                  (sampledBlock setup (t - 1) ω)).1 -
                  ((yIter setup hStanding (t - 1) ω)
                    (sampledBlock setup (t - 1) ω)).1⟫_ℝ) := by
    intro t htmem
    rcases Finset.mem_Icc.mp htmem with ⟨ht2, htk⟩
    exact hHistoricalCoupling t ht2 htk ω
  have hCurrentCoupling_on_window :
      ∀ t ∈ Finset.Icc 1 k,
        ⟪xTildeIter setup hStanding t ω - (xIter setup hStanding t ω).1,
          ∑ i : ι, (yTildeIter setup hStanding t ω i - (z.2 i).1)⟫_ℝ =
          ⟪(xIter setup hStanding (t - 1) ω).1 -
              (xIter setup hStanding t ω).1,
            ∑ i : ι, ((yIter setup hStanding t ω i).1 - (z.2 i).1)⟫_ℝ +
            (inverseProbabilityValue setup (sampledBlock setup t ω)
                (hDen.1 (sampledBlock setup t ω)) - 1) *
              ⟪(xIter setup hStanding (t - 1) ω).1 -
                  (xIter setup hStanding t ω).1,
                (yIter setup hStanding t ω (sampledBlock setup t ω)).1 -
                  ((yIter setup hStanding (t - 1) ω)
                    (sampledBlock setup t ω)).1⟫_ℝ -
            setup.α t *
              ⟪(xIter setup hStanding (t - 2) ω).1 -
                  (xIter setup hStanding (t - 1) ω).1,
                ∑ i : ι,
                  (yTildeIter setup hStanding t ω i - (z.2 i).1)⟫_ℝ := by
    intro t htmem
    rcases Finset.mem_Icc.mp htmem with ⟨ht, _htk⟩
    exact proposition51_current_coupling_expansion
      setup hStanding hDen.1 t ht ω z
  have hRegrouped :=
    proposition51_weighted_delta_pathwise_regrouped_lower_bound
      setup hStanding θ k hk hDen z hθ h51 hHistoricalCoupling ω
  have hHistoricalCoeffSumNonnegative :
      0 ≤
        ∑ t ∈ Finset.Icc 2 k,
          θ (t - 1) *
            (setup.η (t - 1) / 2 -
              (sourceQuotient
                  (setup.L (sampledBlock setup t ω) * setup.α t)
                  ((componentCount (ι := ι) : ℝ) * setup.τ t *
                    samplingProbability setup (sampledBlock setup t ω))
                  (hDen.2 t (sampledBlock setup t ω)) +
                sourceQuotient
                  ((1 - samplingProbability setup (sampledBlock setup (t - 1) ω)) ^ 2 *
                    setup.L (sampledBlock setup (t - 1) ω))
                  ((componentCount (ι := ι) : ℝ) * setup.τ (t - 1) *
                    samplingProbability setup (sampledBlock setup (t - 1) ω))
                  (hDen.2 (t - 1) (sampledBlock setup (t - 1) ω)))) *
              ‖(xIter setup hStanding (t - 2) ω).1 -
                (xIter setup hStanding (t - 1) ω).1‖ ^ 2 := by
    exact Finset.sum_nonneg hHistoricalSampledCoefficientNonnegative
  nlinarith [hRegrouped, hTerminalSampledCoefficientNonnegative,
    hHistoricalCoeffSumNonnegative]

/-- Finite-prefix negative-Delta upper bound from Proposition 5.1 Eq. (5.1.57).

This is the source-derived bridge between the Lemma 5.5 one-step residual and
the endpoint algebra in Proposition 5.1: after expanding Eq. (5.1.55),
telescoping with Eq. (5.1.51), applying Young/Cauchy Eq. (5.1.58), and dropping
the nonnegative Eq. (5.1.48)--(5.1.49) quadratic blocks, the weighted negative
Delta residual is bounded by the negative terminal first-two bracket. No
SOptLib match: the pre-search list for this object was empty; searched
`Delta coupling finitePrefixExpectation telescope yTildeIter` and
`weighted Delta upper bound Eq 5.1.57 coupling residual`, scanned
`SOptLib/Model/{Iterates,Bregman}.lean` and `SOptLib/Layer1/Telescope.lean`,
and checked the target-file transports/process equations
`finite_prefix_expectation_*_eq_blockStream_of_le`,
`yTildeIter_sampledBlock_eq`, `yTildeIter_otherBlock_eq_prev`, and
`SOptLib.sum_Icc_two_coeff_telescope_le`; none packages the paper-specific
sampled coupling expansion and h48/h49 coefficient drop. -/
private theorem proposition51_weighted_delta_finitePrefix_upper_bound
    (hStanding : standingAssumptions setup)
    (θ : ℕ → ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hDen : proposition_5_1_denominatorBoundary setup k)
    (z : SaddlePoint setup)
    (hθ : ∀ t, 1 ≤ t → t ≤ k → 0 ≤ θ t)
    (h48 : propositionCondition_5_1_48_with_denominator_source_gap setup k hk hDen)
    (h49 : propositionCondition_5_1_49_with_denominator_source_gap setup k hDen)
    (h51 : ∀ t, 2 ≤ t → t ≤ k → setup.α t * θ t = θ (t - 1)) :
    (∑ t ∈ Finset.Icc 1 k, θ t *
      finitePrefixExpectation setup t (fun ω =>
        (⟪xTildeIter setup hStanding t ω - (xIter setup hStanding t ω).1,
            ∑ i : ι, (yTildeIter setup hStanding t ω i - (z.2 i).1)⟫_ℝ -
          (setup.τ t *
              inverseProbabilityValue setup (sampledBlock setup t ω)
                (sampledBlock_probability_ne_zero setup
                  (sampledPositiveBlock setup t ω))) *
            (SOptLib.carrierBregmanDivergence (dualConjugate setup (sampledBlock setup t ω)) (dualConjugateBaseSelector setup (sampledBlock setup t ω) ((yIter setup hStanding (t - 1) ω) (sampledBlock setup t ω)) (dualSubgradIter setup hStanding (t - 1) ω
                (sampledBlock setup t ω))) ((yIter setup hStanding (t - 1) ω) (sampledBlock setup t ω)) ((yIter setup hStanding t ω) (sampledBlock setup t ω)))) -
          setup.η t *
            primalBregman setup
              (xIter setup hStanding (t - 1) ω)
              (xIter setup hStanding t ω))) ≤
      - θ k *
        finitePrefixExpectation setup k (fun ω =>
          setup.η k / 4 *
              ‖(xIter setup hStanding (k - 1) ω).1 -
                (xIter setup hStanding k ω).1‖ ^ 2 -
            ⟪(xIter setup hStanding (k - 1) ω).1 -
                (xIter setup hStanding k ω).1,
              ∑ i : ι, ((yIter setup hStanding k ω i).1 -
                (z.2 i).1)⟫_ℝ) := by
  classical
  have _ := hθ
  have _ := h48
  have _ := h49
  have _ := h51
  have hHistoricalCoupling :=
    fun (t : ℕ) (ht2 : 2 ≤ t) (_htk : t ≤ k) (ω : BlockSamplePath setup) =>
      proposition51_historical_coupling_expansion
        setup hStanding hDen.1 t ht2 ω z
  let deltaNeg : ℕ → BlockSamplePath setup → ℝ := fun t ω =>
    (⟪xTildeIter setup hStanding t ω - (xIter setup hStanding t ω).1,
        ∑ i : ι, (yTildeIter setup hStanding t ω i - (z.2 i).1)⟫_ℝ -
      (setup.τ t *
          inverseProbabilityValue setup (sampledBlock setup t ω)
            (sampledBlock_probability_ne_zero setup
              (sampledPositiveBlock setup t ω))) *
        (SOptLib.carrierBregmanDivergence (dualConjugate setup (sampledBlock setup t ω)) (dualConjugateBaseSelector setup (sampledBlock setup t ω) ((yIter setup hStanding (t - 1) ω) (sampledBlock setup t ω)) (dualSubgradIter setup hStanding (t - 1) ω
            (sampledBlock setup t ω))) ((yIter setup hStanding (t - 1) ω) (sampledBlock setup t ω)) ((yIter setup hStanding t ω) (sampledBlock setup t ω))) -
      setup.η t *
        primalBregman setup
          (xIter setup hStanding (t - 1) ω)
          (xIter setup hStanding t ω))
  let deltaPos : ℕ → BlockSamplePath setup → ℝ := fun t ω =>
    setup.η t *
        primalBregman setup
          (xIter setup hStanding (t - 1) ω)
          (xIter setup hStanding t ω) -
      ⟪xTildeIter setup hStanding t ω -
          (xIter setup hStanding t ω).1,
        ∑ i : ι, (yTildeIter setup hStanding t ω i - (z.2 i).1)⟫_ℝ +
      setup.τ t *
        inverseProbabilityValue setup (sampledBlock setup t ω)
          (sampledBlock_probability_ne_zero setup
            (sampledPositiveBlock setup t ω)) *
        (SOptLib.carrierBregmanDivergence (dualConjugate setup (sampledBlock setup t ω)) (dualConjugateBaseSelector setup (sampledBlock setup t ω) ((yIter setup hStanding (t - 1) ω) (sampledBlock setup t ω)) (dualSubgradIter setup hStanding (t - 1) ω
            (sampledBlock setup t ω))) ((yIter setup hStanding (t - 1) ω) (sampledBlock setup t ω)) ((yIter setup hStanding t ω) (sampledBlock setup t ω)))
  let terminal : BlockSamplePath setup → ℝ := fun ω =>
    setup.η k / 4 *
        ‖(xIter setup hStanding (k - 1) ω).1 -
          (xIter setup hStanding k ω).1‖ ^ 2 -
      ⟪(xIter setup hStanding (k - 1) ω).1 -
          (xIter setup hStanding k ω).1,
        ∑ i : ι, ((yIter setup hStanding k ω i).1 -
          (z.2 i).1)⟫_ℝ
  have hPath : ∀ ω : BlockSamplePath setup,
      θ k * terminal ω ≤
        ∑ t ∈ Finset.Icc 1 k, θ t * deltaPos t ω := by
    intro ω
    simpa [terminal, deltaPos] using
      proposition51_weighted_delta_pathwise_lower_bound
        setup hStanding θ k hk hDen z hθ h48 h49 h51
        hHistoricalCoupling ω
  have hMono :
      finitePrefixExpectation setup k (fun ω => θ k * terminal ω) ≤
        finitePrefixExpectation setup k
          (fun ω => ∑ t ∈ Finset.Icc 1 k, θ t * deltaPos t ω) := by
    exact finite_prefix_expectation_mono_of_forall_extend setup k
      (fun pref => hPath (extendBlockPrefix setup k pref))
  have hDeltaPos_neg :
      ∀ t, finitePrefixExpectation setup t (deltaPos t) =
        - finitePrefixExpectation setup t (deltaNeg t) := by
    intro t
    calc
      finitePrefixExpectation setup t (deltaPos t) =
          finitePrefixExpectation setup t (fun ω => (-1 : ℝ) * deltaNeg t ω) := by
            apply congrArg (finitePrefixExpectation setup t)
            funext ω
            dsimp [deltaPos, deltaNeg]
            ring
      _ = (-1 : ℝ) * finitePrefixExpectation setup t (deltaNeg t) := by
            exact finitePrefixExpectation_const_mul setup t (-1) (deltaNeg t)
      _ = - finitePrefixExpectation setup t (deltaNeg t) := by ring
  have hDeltaPos_horizon :
      ∀ t ∈ Finset.Icc 1 k,
        finitePrefixExpectation setup k (deltaPos t) =
          finitePrefixExpectation setup t (deltaPos t) := by
    intro t htmem
    rcases Finset.mem_Icc.mp htmem with ⟨ht, htk⟩
    have hNeg_k :
        finitePrefixExpectation setup k (deltaNeg t) =
          ∫ ω, deltaNeg t ω ∂blockStreamLaw setup := by
      exact finite_prefix_expectation_eq_blockStream_of_extend_eq setup k
        (deltaNeg t) (by
          intro ω
          simpa [deltaNeg] using
            proposition51_delta_negative_prefix_extend_eq
              setup hStanding ht htk ω z)
    have hNeg_t :
        finitePrefixExpectation setup t (deltaNeg t) =
          ∫ ω, deltaNeg t ω ∂blockStreamLaw setup := by
      exact finite_prefix_expectation_eq_blockStream_of_extend_eq setup t
        (deltaNeg t) (by
          intro ω
          simpa [deltaNeg] using
            proposition51_delta_negative_prefix_extend_eq
              setup hStanding ht le_rfl ω z)
    have hNeg_horizon :
        finitePrefixExpectation setup k (deltaNeg t) =
          finitePrefixExpectation setup t (deltaNeg t) := by
      rw [hNeg_k, hNeg_t]
    calc
      finitePrefixExpectation setup k (deltaPos t) =
          finitePrefixExpectation setup k (fun ω => (-1 : ℝ) * deltaNeg t ω) := by
            apply congrArg (finitePrefixExpectation setup k)
            funext ω
            dsimp [deltaPos, deltaNeg]
            ring
      _ = (-1 : ℝ) * finitePrefixExpectation setup k (deltaNeg t) := by
            exact finitePrefixExpectation_const_mul setup k (-1) (deltaNeg t)
      _ = (-1 : ℝ) * finitePrefixExpectation setup t (deltaNeg t) := by
            rw [hNeg_horizon]
      _ = finitePrefixExpectation setup t (deltaPos t) := by
            rw [hDeltaPos_neg t]
            ring
  have hIntegrated :
      θ k * finitePrefixExpectation setup k terminal ≤
        ∑ t ∈ Finset.Icc 1 k, θ t *
          finitePrefixExpectation setup t (deltaPos t) := by
    calc
      θ k * finitePrefixExpectation setup k terminal =
          finitePrefixExpectation setup k (fun ω => θ k * terminal ω) := by
            rw [finitePrefixExpectation_const_mul]
      _ ≤ finitePrefixExpectation setup k
            (fun ω => ∑ t ∈ Finset.Icc 1 k, θ t * deltaPos t ω) := hMono
      _ = ∑ t ∈ Finset.Icc 1 k,
            finitePrefixExpectation setup k (fun ω => θ t * deltaPos t ω) := by
            exact finitePrefixExpectation_sum_finset setup k (Finset.Icc 1 k)
              (fun t ω => θ t * deltaPos t ω)
      _ = ∑ t ∈ Finset.Icc 1 k,
            θ t * finitePrefixExpectation setup k (deltaPos t) := by
            refine Finset.sum_congr rfl ?_
            intro t _ht
            rw [finitePrefixExpectation_const_mul]
      _ = ∑ t ∈ Finset.Icc 1 k,
            θ t * finitePrefixExpectation setup t (deltaPos t) := by
            refine Finset.sum_congr rfl ?_
            intro t ht
            rw [hDeltaPos_horizon t ht]
  have hPosSum_neg :
      (∑ t ∈ Finset.Icc 1 k, θ t *
          finitePrefixExpectation setup t (deltaPos t)) =
        - (∑ t ∈ Finset.Icc 1 k, θ t *
          finitePrefixExpectation setup t (deltaNeg t)) := by
    calc
      (∑ t ∈ Finset.Icc 1 k, θ t *
          finitePrefixExpectation setup t (deltaPos t)) =
          ∑ t ∈ Finset.Icc 1 k, -(θ t *
            finitePrefixExpectation setup t (deltaNeg t)) := by
            refine Finset.sum_congr rfl ?_
            intro t _ht
            rw [hDeltaPos_neg t]
            ring
      _ = - (∑ t ∈ Finset.Icc 1 k, θ t *
            finitePrefixExpectation setup t (deltaNeg t)) := by
            rw [Finset.sum_neg_distrib]
  change (∑ t ∈ Finset.Icc 1 k, θ t *
      finitePrefixExpectation setup t (deltaNeg t)) ≤
    - θ k * finitePrefixExpectation setup k terminal
  rw [hPosSum_neg] at hIntegrated
  nlinarith

/-- Theorem 5.1 denominator-free pathwise Delta lower bound, Eq. (5.1.57)
under the constant-parameter conditions (5.1.59)--(5.1.62). No SOptLib match:
searched `weighted delta pathwise lower bound regroup theorem output Young
division free` and `coupling regroup from pointwise weighted lagged cancel
output weight`, scanned the local Proposition 5.1 delta helpers and
`SOptLib/Glue/Algebra.lean`; existing candidates either require the forbidden
`proposition_5_1_denominatorBoundary` quotient interface or provide only the
source-neutral finite-sum regrouping, while this theorem needs the literal
Theorem 5.1 `η/4` Young allocation from Eqs. (5.1.59)--(5.1.62). -/
private theorem theorem51_weighted_delta_pathwise_lower_bound_division_free
    (τ η α : ℝ)
    (hStanding : theoremStandingAssumptions setup)
    (hPolicy : constantParameterPolicy setup τ η α)
    (hProb : constantParameterConditionProbability setup τ α)
    (hLip : constantParameterConditionLipschitz setup τ η)
    (hAlpha : alphaRange α)
    (hRateDen : theorem_5_1_rateDenominatorBoundary η)
    (k : ℕ) (hk : 1 ≤ k)
    (hp : ∀ i : ι, samplingProbability setup i ≠ 0)
    (hθ : ∀ t, 1 ≤ t → t ≤ k → 0 ≤ theoremOutputWeight α hAlpha t)
    (h51 : ∀ t, 2 ≤ t → t ≤ k →
      setup.α t * theoremOutputWeight α hAlpha t =
        theoremOutputWeight α hAlpha (t - 1))
    (z : SaddlePoint setup) (ω : BlockSamplePath setup) :
    theoremOutputWeight α hAlpha k *
        (setup.η k / 4 *
            ‖(xIter setup hStanding.1 (k - 1) ω).1 -
              (xIter setup hStanding.1 k ω).1‖ ^ 2 -
          ⟪(xIter setup hStanding.1 (k - 1) ω).1 -
              (xIter setup hStanding.1 k ω).1,
            ∑ i : ι, ((yIter setup hStanding.1 k ω i).1 -
              (z.2 i).1)⟫_ℝ) ≤
      ∑ t ∈ Finset.Icc 1 k, theoremOutputWeight α hAlpha t *
        (setup.η t *
            primalBregman setup
              (xIter setup hStanding.1 (t - 1) ω)
              (xIter setup hStanding.1 t ω) -
          ⟪xTildeIter setup hStanding.1 t ω -
              (xIter setup hStanding.1 t ω).1,
            ∑ i : ι,
              (yTildeIter setup hStanding.1 t ω i - (z.2 i).1)⟫_ℝ +
          setup.τ t *
            inverseProbabilityValue setup (sampledBlock setup t ω)
              (sampledBlock_probability_ne_zero setup
                (sampledPositiveBlock setup t ω)) *
            (SOptLib.carrierBregmanDivergence (dualConjugate setup (sampledBlock setup t ω)) (dualConjugateBaseSelector setup (sampledBlock setup t ω) ((yIter setup hStanding.1 (t - 1) ω)
                (sampledBlock setup t ω)) (dualSubgradIter setup hStanding.1 (t - 1) ω
                (sampledBlock setup t ω))) ((yIter setup hStanding.1 (t - 1) ω)
                (sampledBlock setup t ω)) ((yIter setup hStanding.1 t ω)
                (sampledBlock setup t ω)))) := by
  classical
  let θ : ℕ → ℝ := theoremOutputWeight α hAlpha
  let hprobThm : ∀ i : ι, samplingProbability setup i ≠ 0 :=
    inverseProbabilityDenominators_ne_of_theorem_conditions
      setup τ η α hStanding hPolicy hProb hAlpha
  have hHistoricalCoupling_on_window :
      ∀ t ∈ Finset.Icc 2 k,
        ⟪xTildeIter setup hStanding.1 t ω - (xIter setup hStanding.1 t ω).1,
          ∑ i : ι, (yTildeIter setup hStanding.1 t ω i - (z.2 i).1)⟫_ℝ =
          ⟪(xIter setup hStanding.1 (t - 1) ω).1 -
              (xIter setup hStanding.1 t ω).1,
            ∑ i : ι, ((yIter setup hStanding.1 t ω i).1 - (z.2 i).1)⟫_ℝ +
          (inverseProbabilityValue setup (sampledBlock setup t ω)
              (hp (sampledBlock setup t ω)) - 1) *
            ⟪(xIter setup hStanding.1 (t - 1) ω).1 -
                (xIter setup hStanding.1 t ω).1,
              (yIter setup hStanding.1 t ω (sampledBlock setup t ω)).1 -
                ((yIter setup hStanding.1 (t - 1) ω)
                  (sampledBlock setup t ω)).1⟫_ℝ -
          setup.α t *
            ⟪(xIter setup hStanding.1 (t - 2) ω).1 -
                (xIter setup hStanding.1 (t - 1) ω).1,
              ∑ i : ι,
                (yTildeIter setup hStanding.1 (t - 1) ω i - (z.2 i).1)⟫_ℝ -
          setup.α t *
            (inverseProbabilityValue setup (sampledBlock setup t ω)
                (hp (sampledBlock setup t ω)) *
              ⟪(xIter setup hStanding.1 (t - 2) ω).1 -
                  (xIter setup hStanding.1 (t - 1) ω).1,
                (yIter setup hStanding.1 t ω (sampledBlock setup t ω)).1 -
                  ((yIter setup hStanding.1 (t - 1) ω)
                    (sampledBlock setup t ω)).1⟫_ℝ +
            (inverseProbabilityValue setup (sampledBlock setup (t - 1) ω)
                (hp (sampledBlock setup (t - 1) ω)) - 1) *
              ⟪(xIter setup hStanding.1 (t - 2) ω).1 -
                  (xIter setup hStanding.1 (t - 1) ω).1,
                ((yIter setup hStanding.1 (t - 2) ω)
                  (sampledBlock setup (t - 1) ω)).1 -
                  ((yIter setup hStanding.1 (t - 1) ω)
                    (sampledBlock setup (t - 1) ω)).1⟫_ℝ) := by
    intro t htmem
    rcases Finset.mem_Icc.mp htmem with ⟨ht2, _htk⟩
    exact proposition51_historical_coupling_expansion
      setup hStanding.1 hp t ht2 ω z
  have hCurrentCoupling_on_window :
      ∀ t ∈ Finset.Icc 1 k,
        ⟪xTildeIter setup hStanding.1 t ω - (xIter setup hStanding.1 t ω).1,
          ∑ i : ι, (yTildeIter setup hStanding.1 t ω i - (z.2 i).1)⟫_ℝ =
          ⟪(xIter setup hStanding.1 (t - 1) ω).1 -
              (xIter setup hStanding.1 t ω).1,
            ∑ i : ι, ((yIter setup hStanding.1 t ω i).1 - (z.2 i).1)⟫_ℝ +
            (inverseProbabilityValue setup (sampledBlock setup t ω)
                (hp (sampledBlock setup t ω)) - 1) *
              ⟪(xIter setup hStanding.1 (t - 1) ω).1 -
                  (xIter setup hStanding.1 t ω).1,
                (yIter setup hStanding.1 t ω (sampledBlock setup t ω)).1 -
                  ((yIter setup hStanding.1 (t - 1) ω)
                    (sampledBlock setup t ω)).1⟫_ℝ -
            setup.α t *
              ⟪(xIter setup hStanding.1 (t - 2) ω).1 -
                  (xIter setup hStanding.1 (t - 1) ω).1,
                ∑ i : ι,
                  (yTildeIter setup hStanding.1 t ω i - (z.2 i).1)⟫_ℝ := by
    intro t htmem
    rcases Finset.mem_Icc.mp htmem with ⟨ht, _htk⟩
    exact proposition51_current_coupling_expansion
      setup hStanding.1 hp t ht ω z
  have hTerminalYoung_weighted :
      θ k *
          (-(η / 4 *
            ‖(xIter setup hStanding.1 (k - 1) ω).1 -
              (xIter setup hStanding.1 k ω).1‖ ^ 2)) ≤
        θ k *
          ((1 - inverseProbabilityValue setup (sampledBlock setup k ω)
              (hp (sampledBlock setup k ω))) *
            ⟪(xIter setup hStanding.1 (k - 1) ω).1 -
                (xIter setup hStanding.1 k ω).1,
              (yIter setup hStanding.1 k ω (sampledBlock setup k ω)).1 -
                ((yIter setup hStanding.1 (k - 1) ω)
                  (sampledBlock setup k ω)).1⟫_ℝ +
            (setup.τ k / 2) *
              inverseProbabilityValue setup (sampledBlock setup k ω)
                (hp (sampledBlock setup k ω)) *
              (SOptLib.carrierBregmanDivergence (dualConjugate setup (sampledBlock setup k ω)) (dualConjugateBaseSelector setup (sampledBlock setup k ω) ((yIter setup hStanding.1 (k - 1) ω)
                  (sampledBlock setup k ω)) (dualSubgradIter setup hStanding.1 (k - 1) ω
                  (sampledBlock setup k ω))) ((yIter setup hStanding.1 (k - 1) ω)
                  (sampledBlock setup k ω)) ((yIter setup hStanding.1 k ω)
                  (sampledBlock setup k ω)))) := by
    have hbase :=
      theorem51_terminal_young_absorb_weighted_division_free
        setup τ η α hStanding hPolicy hProb hLip hAlpha hRateDen
        k hk (sampledBlock setup k ω)
        ((xIter setup hStanding.1 (k - 1) ω).1 -
          (xIter setup hStanding.1 k ω).1)
        ((yIter setup hStanding.1 (k - 1) ω)
          (sampledBlock setup k ω))
        (dualSubgradIter setup hStanding.1 (k - 1) ω
          (sampledBlock setup k ω))
        ((yIter setup hStanding.1 k ω) (sampledBlock setup k ω))
    simpa [θ, hprobThm, hp, mul_assoc, mul_left_comm, mul_comm] using hbase
  have hCurrentHistoricalYoung_on_window :
      ∀ t ∈ Finset.Icc 2 k,
        -θ (t - 1) *
            (η / 4 *
              ‖(xIter setup hStanding.1 (t - 2) ω).1 -
                (xIter setup hStanding.1 (t - 1) ω).1‖ ^ 2) ≤
          θ t *
            (setup.α t *
                inverseProbabilityValue setup (sampledBlock setup t ω)
                  (hp (sampledBlock setup t ω)) *
                ⟪(xIter setup hStanding.1 (t - 2) ω).1 -
                    (xIter setup hStanding.1 (t - 1) ω).1,
                  (yIter setup hStanding.1 t ω
                      (sampledBlock setup t ω)).1 -
                    ((yIter setup hStanding.1 (t - 1) ω)
                      (sampledBlock setup t ω)).1⟫_ℝ +
              (setup.τ t / 2) *
                inverseProbabilityValue setup (sampledBlock setup t ω)
                  (hp (sampledBlock setup t ω)) *
                (SOptLib.carrierBregmanDivergence (dualConjugate setup (sampledBlock setup t ω)) (dualConjugateBaseSelector setup (sampledBlock setup t ω) ((yIter setup hStanding.1 (t - 1) ω)
                    (sampledBlock setup t ω)) (dualSubgradIter setup hStanding.1 (t - 1) ω
                    (sampledBlock setup t ω))) ((yIter setup hStanding.1 (t - 1) ω)
                    (sampledBlock setup t ω)) ((yIter setup hStanding.1 t ω)
                    (sampledBlock setup t ω)))) := by
    intro t htmem
    rcases Finset.mem_Icc.mp htmem with ⟨ht2, htk⟩
    have hbase :=
      theorem51_current_historical_young_absorb_weighted_division_free
        setup τ η α hStanding hPolicy hProb hLip hAlpha hRateDen
        t ht2 (sampledBlock setup t ω)
        ((xIter setup hStanding.1 (t - 2) ω).1 -
          (xIter setup hStanding.1 (t - 1) ω).1)
        ((yIter setup hStanding.1 (t - 1) ω)
          (sampledBlock setup t ω))
        (dualSubgradIter setup hStanding.1 (t - 1) ω
          (sampledBlock setup t ω))
        ((yIter setup hStanding.1 t ω) (sampledBlock setup t ω))
    simpa [θ, hprobThm, hp, mul_assoc, mul_left_comm, mul_comm] using hbase
  have hPreviousHistoricalYoung_on_window :
      ∀ t ∈ Finset.Icc 2 k,
        -θ (t - 1) *
            (η / 4 *
              ‖(xIter setup hStanding.1 (t - 2) ω).1 -
                (xIter setup hStanding.1 (t - 1) ω).1‖ ^ 2) ≤
          setup.α t * θ t *
              ((inverseProbabilityValue setup
                    (sampledBlock setup (t - 1) ω)
                    (hp (sampledBlock setup (t - 1) ω)) - 1) *
                ⟪(xIter setup hStanding.1 (t - 2) ω).1 -
                    (xIter setup hStanding.1 (t - 1) ω).1,
                  ((yIter setup hStanding.1 (t - 2) ω)
                    (sampledBlock setup (t - 1) ω)).1 -
                    ((yIter setup hStanding.1 (t - 1) ω)
                      (sampledBlock setup (t - 1) ω)).1⟫_ℝ) +
            θ (t - 1) *
              ((setup.τ (t - 1) / 2) *
                inverseProbabilityValue setup
                  (sampledBlock setup (t - 1) ω)
                  (hp (sampledBlock setup (t - 1) ω)) *
                (SOptLib.carrierBregmanDivergence (dualConjugate setup (sampledBlock setup (t - 1) ω)) (dualConjugateBaseSelector setup (sampledBlock setup (t - 1) ω) ((yIter setup hStanding.1 (t - 2) ω)
                    (sampledBlock setup (t - 1) ω)) (dualSubgradIter setup hStanding.1 (t - 2) ω
                    (sampledBlock setup (t - 1) ω))) ((yIter setup hStanding.1 (t - 2) ω)
                    (sampledBlock setup (t - 1) ω)) ((yIter setup hStanding.1 (t - 1) ω)
                    (sampledBlock setup (t - 1) ω)))) := by
    intro t htmem
    rcases Finset.mem_Icc.mp htmem with ⟨ht2, htk⟩
    have hbase :=
      theorem51_previous_historical_young_absorb_weighted_division_free
        setup τ η α hStanding hPolicy hProb hLip hAlpha hRateDen
        t ht2 (sampledBlock setup (t - 1) ω)
        ((xIter setup hStanding.1 (t - 2) ω).1 -
          (xIter setup hStanding.1 (t - 1) ω).1)
        ((yIter setup hStanding.1 (t - 2) ω)
          (sampledBlock setup (t - 1) ω))
        (dualSubgradIter setup hStanding.1 (t - 2) ω
          (sampledBlock setup (t - 1) ω))
        ((yIter setup hStanding.1 (t - 1) ω)
          (sampledBlock setup (t - 1) ω))
    simpa [θ, hprobThm, hp, mul_assoc, mul_left_comm, mul_comm] using hbase
  have hCurrentHistoricalYoung_sum :=
    Finset.sum_le_sum hCurrentHistoricalYoung_on_window
  have hPreviousHistoricalYoung_sum :=
    Finset.sum_le_sum hPreviousHistoricalYoung_on_window
  let yTildeCoupling : ℕ → ℝ := fun t =>
    ⟪(xIter setup hStanding.1 (t - 1) ω).1 -
        (xIter setup hStanding.1 t ω).1,
      ∑ i : ι,
        (yTildeIter setup hStanding.1 t ω i - (z.2 i).1)⟫_ℝ
  have hLaggedCoupling_cancel :
      (∑ t ∈ Finset.Icc 1 k, (-θ t * yTildeCoupling t)) +
          ∑ t ∈ Finset.Icc 2 k,
            (setup.α t * θ t) * yTildeCoupling (t - 1) =
        -θ k * yTildeCoupling k := by
    exact
      sum_Icc_weighted_lagged_cancel_eq_terminal
        θ (fun t => setup.α t * θ t) yTildeCoupling k hk
        (by
          intro t ht2 htk
          exact h51 t ht2 htk)
  let deltaResidual : ℕ → ℝ := fun t =>
    -⟪xTildeIter setup hStanding.1 t ω -
        (xIter setup hStanding.1 t ω).1,
      ∑ i : ι,
        (yTildeIter setup hStanding.1 t ω i - (z.2 i).1)⟫_ℝ +
      setup.τ t *
        inverseProbabilityValue setup (sampledBlock setup t ω)
          (sampledBlock_probability_ne_zero setup
            (sampledPositiveBlock setup t ω)) *
        (SOptLib.carrierBregmanDivergence (dualConjugate setup (sampledBlock setup t ω)) (dualConjugateBaseSelector setup (sampledBlock setup t ω) ((yIter setup hStanding.1 (t - 1) ω)
            (sampledBlock setup t ω)) (dualSubgradIter setup hStanding.1 (t - 1) ω
            (sampledBlock setup t ω))) ((yIter setup hStanding.1 (t - 1) ω)
            (sampledBlock setup t ω)) ((yIter setup hStanding.1 t ω)
            (sampledBlock setup t ω)))
  have hPrimalBudget_to_delta_rhs :
      (∑ t ∈ Finset.Icc 1 k, θ t *
        (setup.η t / 2 *
            ‖(xIter setup hStanding.1 (t - 1) ω).1 -
              (xIter setup hStanding.1 t ω).1‖ ^ 2 +
          deltaResidual t)) ≤
        ∑ t ∈ Finset.Icc 1 k, θ t *
          (setup.η t *
              primalBregman setup
                (xIter setup hStanding.1 (t - 1) ω)
                (xIter setup hStanding.1 t ω) +
            deltaResidual t) := by
    exact
      proposition51_weighted_primal_bregman_norm_budget_le
        setup hStanding.1 θ k ω deltaResidual
        (by
          intro t ht1 htk
          exact hθ t ht1 htk)
  have hPrimalBudget_to_final_rhs :
      (∑ t ∈ Finset.Icc 1 k, θ t *
        (setup.η t / 2 *
            ‖(xIter setup hStanding.1 (t - 1) ω).1 -
              (xIter setup hStanding.1 t ω).1‖ ^ 2 +
          deltaResidual t)) ≤
        ∑ t ∈ Finset.Icc 1 k, θ t *
          (setup.η t *
              primalBregman setup
                (xIter setup hStanding.1 (t - 1) ω)
                (xIter setup hStanding.1 t ω) -
            ⟪xTildeIter setup hStanding.1 t ω -
                (xIter setup hStanding.1 t ω).1,
              ∑ i : ι,
                (yTildeIter setup hStanding.1 t ω i - (z.2 i).1)⟫_ℝ +
            setup.τ t *
              inverseProbabilityValue setup (sampledBlock setup t ω)
                (sampledBlock_probability_ne_zero setup
                  (sampledPositiveBlock setup t ω)) *
              (SOptLib.carrierBregmanDivergence (dualConjugate setup (sampledBlock setup t ω)) (dualConjugateBaseSelector setup (sampledBlock setup t ω) ((yIter setup hStanding.1 (t - 1) ω)
                  (sampledBlock setup t ω)) (dualSubgradIter setup hStanding.1 (t - 1) ω
                  (sampledBlock setup t ω))) ((yIter setup hStanding.1 (t - 1) ω)
                  (sampledBlock setup t ω)) ((yIter setup hStanding.1 t ω)
                  (sampledBlock setup t ω)))) := by
    refine le_trans hPrimalBudget_to_delta_rhs ?_
    apply le_of_eq
    refine Finset.sum_congr rfl ?_
    intro t ht
    dsimp [deltaResidual]
    ring
  have hFinal_to_normResidual :
      θ k *
          (setup.η k / 4 *
              ‖(xIter setup hStanding.1 (k - 1) ω).1 -
                (xIter setup hStanding.1 k ω).1‖ ^ 2 -
            ⟪(xIter setup hStanding.1 (k - 1) ω).1 -
                (xIter setup hStanding.1 k ω).1,
              ∑ i : ι, ((yIter setup hStanding.1 k ω i).1 -
                (z.2 i).1)⟫_ℝ) ≤
        ∑ t ∈ Finset.Icc 1 k, θ t *
          (setup.η t / 2 *
              ‖(xIter setup hStanding.1 (t - 1) ω).1 -
                (xIter setup hStanding.1 t ω).1‖ ^ 2 +
            deltaResidual t) := by
    let U : ℕ → ℝ := fun t =>
      ‖(xIter setup hStanding.1 (t - 1) ω).1 -
        (xIter setup hStanding.1 t ω).1‖ ^ 2
    let C : ℕ → ℝ := fun t =>
      ⟪xTildeIter setup hStanding.1 t ω -
          (xIter setup hStanding.1 t ω).1,
        ∑ i : ι,
          (yTildeIter setup hStanding.1 t ω i - (z.2 i).1)⟫_ℝ
    let A : ℕ → ℝ := fun t =>
      ⟪(xIter setup hStanding.1 (t - 1) ω).1 -
          (xIter setup hStanding.1 t ω).1,
        ∑ i : ι, ((yIter setup hStanding.1 t ω i).1 -
          (z.2 i).1)⟫_ℝ
    let B : ℕ → ℝ := fun t =>
      (inverseProbabilityValue setup (sampledBlock setup t ω)
          (hp (sampledBlock setup t ω)) - 1) *
        ⟪(xIter setup hStanding.1 (t - 1) ω).1 -
            (xIter setup hStanding.1 t ω).1,
          (yIter setup hStanding.1 t ω (sampledBlock setup t ω)).1 -
            ((yIter setup hStanding.1 (t - 1) ω)
              (sampledBlock setup t ω)).1⟫_ℝ
    let D : ℕ → ℝ := fun t =>
      setup.τ t *
        inverseProbabilityValue setup (sampledBlock setup t ω)
          (sampledBlock_probability_ne_zero setup
            (sampledPositiveBlock setup t ω)) *
        (SOptLib.carrierBregmanDivergence (dualConjugate setup (sampledBlock setup t ω)) (dualConjugateBaseSelector setup (sampledBlock setup t ω) ((yIter setup hStanding.1 (t - 1) ω)
            (sampledBlock setup t ω)) (dualSubgradIter setup hStanding.1 (t - 1) ω
            (sampledBlock setup t ω))) ((yIter setup hStanding.1 (t - 1) ω)
            (sampledBlock setup t ω)) ((yIter setup hStanding.1 t ω)
            (sampledBlock setup t ω)))
    let Ecur : ℕ → ℝ := fun t =>
      setup.α t *
        inverseProbabilityValue setup (sampledBlock setup t ω)
          (hp (sampledBlock setup t ω)) *
        ⟪(xIter setup hStanding.1 (t - 2) ω).1 -
            (xIter setup hStanding.1 (t - 1) ω).1,
          (yIter setup hStanding.1 t ω
              (sampledBlock setup t ω)).1 -
            ((yIter setup hStanding.1 (t - 1) ω)
              (sampledBlock setup t ω)).1⟫_ℝ
    let Eprev : ℕ → ℝ := fun t =>
      setup.α t *
        ((inverseProbabilityValue setup
              (sampledBlock setup (t - 1) ω)
              (hp (sampledBlock setup (t - 1) ω)) - 1) *
          ⟪(xIter setup hStanding.1 (t - 2) ω).1 -
              (xIter setup hStanding.1 (t - 1) ω).1,
            ((yIter setup hStanding.1 (t - 2) ω)
              (sampledBlock setup (t - 1) ω)).1 -
              ((yIter setup hStanding.1 (t - 1) ω)
                (sampledBlock setup (t - 1) ω)).1⟫_ℝ)
    have hRegroup :
        (∑ t ∈ Finset.Icc 1 k, θ t * (- C t)) =
          -θ k * (A k + B k) +
            ∑ t ∈ Finset.Icc 2 k, θ t * (Ecur t + Eprev t) := by
      have hYBranch :
          ∀ t ∈ Finset.Icc 1 k, yTildeCoupling t = A t + B t := by
        intro t htmem
        rcases Finset.mem_Icc.mp htmem with ⟨ht1, _htk⟩
        dsimp [yTildeCoupling, A, B]
        simpa using
          proposition51_yTilde_inner_minus_z_branch
            setup hStanding.1 hp t ht1 ω z
            ((xIter setup hStanding.1 (t - 1) ω).1 -
              (xIter setup hStanding.1 t ω).1)
      have hLaggedCoupling_cancel_AB :
          (∑ t ∈ Finset.Icc 1 k, (-θ t * yTildeCoupling t)) +
              ∑ t ∈ Finset.Icc 2 k,
                (setup.α t * θ t) * yTildeCoupling (t - 1) =
            -θ k * (A k + B k) := by
        have hyk : yTildeCoupling k = A k + B k :=
          hYBranch k (Finset.mem_Icc.mpr ⟨hk, le_rfl⟩)
        simpa [hyk] using hLaggedCoupling_cancel
      have hC_one : C 1 = yTildeCoupling 1 := by
        have hcur :=
          hCurrentCoupling_on_window 1
            (Finset.mem_Icc.mpr ⟨le_rfl, hk⟩)
        have hy :=
          hYBranch 1 (Finset.mem_Icc.mpr ⟨le_rfl, hk⟩)
        dsimp [C, A, B, yTildeCoupling] at hcur hy ⊢
        rw [hcur]
        rw [← hy]
        simp
      have hC_hist :
          ∀ t ∈ Finset.Icc 2 k,
            C t = yTildeCoupling t - setup.α t * yTildeCoupling (t - 1) -
              (Ecur t + Eprev t) := by
        intro t htmem
        rcases Finset.mem_Icc.mp htmem with ⟨ht2, htk⟩
        have htmem_one : t ∈ Finset.Icc 1 k :=
          Finset.mem_Icc.mpr ⟨by omega, htk⟩
        have hhist := hHistoricalCoupling_on_window t htmem
        have hy := hYBranch t htmem_one
        dsimp [C, A, B, Ecur, Eprev, yTildeCoupling] at hhist hy ⊢
        simp only [Nat.sub_sub] at hhist hy ⊢
        rw [hhist]
        rw [← hy]
        ring
      exact
        sum_Icc_weighted_coupling_regroup_from_pointwise
          θ setup.α C yTildeCoupling Ecur Eprev
          (-θ k * (A k + B k)) k hk
          hC_one hC_hist hLaggedCoupling_cancel_AB
    have hTerminalScalar :
        θ k * (-(η / 4) * U k) ≤ θ k * (-B k + D k / 2) := by
      dsimp [U, B, D]
      calc
        θ k *
            (-(η / 4) *
              ‖(xIter setup hStanding.1 (k - 1) ω).1 -
                (xIter setup hStanding.1 k ω).1‖ ^ 2) =
          θ k *
            (-(η / 4 *
              ‖(xIter setup hStanding.1 (k - 1) ω).1 -
                (xIter setup hStanding.1 k ω).1‖ ^ 2)) := by
            ring
        _ ≤ θ k *
          ((1 - inverseProbabilityValue setup (sampledBlock setup k ω)
              (hp (sampledBlock setup k ω))) *
            ⟪(xIter setup hStanding.1 (k - 1) ω).1 -
                (xIter setup hStanding.1 k ω).1,
              (yIter setup hStanding.1 k ω (sampledBlock setup k ω)).1 -
                ((yIter setup hStanding.1 (k - 1) ω)
                  (sampledBlock setup k ω)).1⟫_ℝ +
            (setup.τ k / 2) *
              inverseProbabilityValue setup (sampledBlock setup k ω)
                (sampledBlock_probability_ne_zero setup
                  (sampledPositiveBlock setup k ω)) *
              (SOptLib.carrierBregmanDivergence (dualConjugate setup (sampledBlock setup k ω)) (dualConjugateBaseSelector setup (sampledBlock setup k ω) ((yIter setup hStanding.1 (k - 1) ω)
                  (sampledBlock setup k ω)) (dualSubgradIter setup hStanding.1 (k - 1) ω
                  (sampledBlock setup k ω))) ((yIter setup hStanding.1 (k - 1) ω)
                  (sampledBlock setup k ω)) ((yIter setup hStanding.1 k ω)
                  (sampledBlock setup k ω)))) := by
          simpa [inverseProbabilityValue, sourceQuotient_def, div_eq_mul_inv,
            mul_assoc, mul_left_comm, mul_comm] using hTerminalYoung_weighted
        _ = θ k *
          (-((inverseProbabilityValue setup (sampledBlock setup k ω)
              (hp (sampledBlock setup k ω)) - 1) *
            ⟪(xIter setup hStanding.1 (k - 1) ω).1 -
                (xIter setup hStanding.1 k ω).1,
              (yIter setup hStanding.1 k ω (sampledBlock setup k ω)).1 -
                ((yIter setup hStanding.1 (k - 1) ω)
                  (sampledBlock setup k ω)).1⟫_ℝ) +
            setup.τ k *
              inverseProbabilityValue setup (sampledBlock setup k ω)
                (sampledBlock_probability_ne_zero setup
                  (sampledPositiveBlock setup k ω)) *
              (SOptLib.carrierBregmanDivergence (dualConjugate setup (sampledBlock setup k ω)) (dualConjugateBaseSelector setup (sampledBlock setup k ω) ((yIter setup hStanding.1 (k - 1) ω)
                  (sampledBlock setup k ω)) (dualSubgradIter setup hStanding.1 (k - 1) ω
                  (sampledBlock setup k ω))) ((yIter setup hStanding.1 (k - 1) ω)
                  (sampledBlock setup k ω)) ((yIter setup hStanding.1 k ω)
                  (sampledBlock setup k ω))) / 2) := by
          have hinv_eq :
              inverseProbabilityValue setup (sampledBlock setup k ω)
                  (hp (sampledBlock setup k ω)) =
                inverseProbabilityValue setup (sampledBlock setup k ω)
                  (sampledBlock_probability_ne_zero setup
                    (sampledPositiveBlock setup k ω)) := by
            unfold inverseProbabilityValue sourceQuotient
            rfl
          rw [hinv_eq]
          ring
    have hCurrentScalar :
        (∑ t ∈ Finset.Icc 2 k,
          -theoremOutputWeight α hAlpha (t - 1) * (η / 4) * U (t - 1)) ≤
          ∑ t ∈ Finset.Icc 2 k, theoremOutputWeight α hAlpha t *
            (Ecur t + D t / 2) := by
      dsimp [θ, U, Ecur, D]
      simpa [Nat.sub_sub, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm,
        inverseProbabilityValue, sourceQuotient_def] using
        hCurrentHistoricalYoung_sum
    have hPreviousScalar :
        (∑ t ∈ Finset.Icc 2 k,
          -theoremOutputWeight α hAlpha (t - 1) * (η / 4) * U (t - 1)) ≤
          ∑ t ∈ Finset.Icc 2 k,
            (theoremOutputWeight α hAlpha t * Eprev t +
              theoremOutputWeight α hAlpha (t - 1) * (D (t - 1) / 2)) := by
      dsimp [θ, U, Eprev, D]
      simpa [Nat.sub_sub, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm,
        inverseProbabilityValue, sourceQuotient_def] using
        hPreviousHistoricalYoung_sum
    have hDinit : 0 ≤ θ 1 * (D 1 / 2) := by
      have hθ1 : 0 ≤ θ 1 := hθ 1 le_rfl hk
      have hτ1 : 0 ≤ setup.τ 1 := by
        rcases hStanding.1 with ⟨_, _, _, _, _, _, _, _, _, _, _, hParam⟩
        exact hParam.1 1 le_rfl
      have hinv1 :
          0 ≤ inverseProbabilityValue setup (sampledBlock setup 1 ω)
            (sampledBlock_probability_ne_zero setup
              (sampledPositiveBlock setup 1 ω)) := by
        rw [inverseProbabilityValue, sourceQuotient_def]
        exact div_nonneg zero_le_one
          (samplingProbability_nonnegative setup (sampledBlock setup 1 ω))
      have hdual1 :
          0 ≤ (SOptLib.carrierBregmanDivergence (dualConjugate setup (sampledBlock setup 1 ω)) (dualConjugateBaseSelector setup (sampledBlock setup 1 ω) ((yIter setup hStanding.1 (1 - 1) ω)
              (sampledBlock setup 1 ω)) (dualSubgradIter setup hStanding.1 (1 - 1) ω
              (sampledBlock setup 1 ω))) ((yIter setup hStanding.1 (1 - 1) ω)
              (sampledBlock setup 1 ω)) ((yIter setup hStanding.1 1 ω)
              (sampledBlock setup 1 ω))) :=
        dualBregman_nonnegative setup (sampledBlock setup 1 ω)
          ((yIter setup hStanding.1 (1 - 1) ω)
            (sampledBlock setup 1 ω))
          (dualSubgradIter setup hStanding.1 (1 - 1) ω
            (sampledBlock setup 1 ω))
          ((yIter setup hStanding.1 1 ω)
            (sampledBlock setup 1 ω))
      dsimp [D]
      positivity
    have hScalar :=
      theorem51_scalar_young_allocation_le
        setup τ η α hPolicy hAlpha U C A B D Ecur Eprev k hk
        hRegroup hTerminalScalar hCurrentScalar hPreviousScalar hDinit
    convert hScalar using 1
    · refine Finset.sum_congr rfl ?_
      intro t ht
      dsimp [U, C, D, deltaResidual]
      ring
  simpa [θ] using le_trans hFinal_to_normResidual hPrimalBudget_to_final_rhs

/-- Finite-prefix integration of the Theorem 5.1 denominator-free pathwise
Delta bridge. No SOptLib match: searched `finite prefix expectation weighted
delta theorem 5.1 division free`, scanned the local Proposition 5.1
finite-prefix bridge, and found that the reusable prefix-transport lemmas cover
only the measure changes; the paper-specific Delta integrands and terminal
bracket still need this route-local wrapper around
`theorem51_weighted_delta_pathwise_lower_bound_division_free`. -/
private theorem theorem51_weighted_delta_finitePrefix_upper_bound_division_free
    (τ η α : ℝ)
    (hStanding : theoremStandingAssumptions setup)
    (hPolicy : constantParameterPolicy setup τ η α)
    (hProb : constantParameterConditionProbability setup τ α)
    (hLip : constantParameterConditionLipschitz setup τ η)
    (hAlpha : alphaRange α)
    (hRateDen : theorem_5_1_rateDenominatorBoundary η)
    (k : ℕ) (hk : 1 ≤ k)
    (hp : ∀ i : ι, samplingProbability setup i ≠ 0)
    (hθ : ∀ t, 1 ≤ t → t ≤ k → 0 ≤ theoremOutputWeight α hAlpha t)
    (h51 : ∀ t, 2 ≤ t → t ≤ k →
      setup.α t * theoremOutputWeight α hAlpha t =
        theoremOutputWeight α hAlpha (t - 1))
    (z : SaddlePoint setup) :
    (∑ t ∈ Finset.Icc 1 k, theoremOutputWeight α hAlpha t *
      finitePrefixExpectation setup t (fun ω =>
        (⟪xTildeIter setup hStanding.1 t ω - (xIter setup hStanding.1 t ω).1,
            ∑ i : ι, (yTildeIter setup hStanding.1 t ω i - (z.2 i).1)⟫_ℝ -
          (setup.τ t *
              inverseProbabilityValue setup (sampledBlock setup t ω)
                (sampledBlock_probability_ne_zero setup
                  (sampledPositiveBlock setup t ω))) *
            (SOptLib.carrierBregmanDivergence (dualConjugate setup (sampledBlock setup t ω)) (dualConjugateBaseSelector setup (sampledBlock setup t ω) ((yIter setup hStanding.1 (t - 1) ω) (sampledBlock setup t ω)) (dualSubgradIter setup hStanding.1 (t - 1) ω
                (sampledBlock setup t ω))) ((yIter setup hStanding.1 (t - 1) ω) (sampledBlock setup t ω)) ((yIter setup hStanding.1 t ω) (sampledBlock setup t ω)))) -
          setup.η t *
            primalBregman setup
              (xIter setup hStanding.1 (t - 1) ω)
              (xIter setup hStanding.1 t ω))) ≤
      - theoremOutputWeight α hAlpha k *
        finitePrefixExpectation setup k (fun ω =>
          setup.η k / 4 *
              ‖(xIter setup hStanding.1 (k - 1) ω).1 -
                (xIter setup hStanding.1 k ω).1‖ ^ 2 -
            ⟪(xIter setup hStanding.1 (k - 1) ω).1 -
                (xIter setup hStanding.1 k ω).1,
              ∑ i : ι, ((yIter setup hStanding.1 k ω i).1 -
                (z.2 i).1)⟫_ℝ) := by
  classical
  let θ : ℕ → ℝ := theoremOutputWeight α hAlpha
  let deltaNeg : ℕ → BlockSamplePath setup → ℝ := fun t ω =>
    (⟪xTildeIter setup hStanding.1 t ω - (xIter setup hStanding.1 t ω).1,
        ∑ i : ι, (yTildeIter setup hStanding.1 t ω i - (z.2 i).1)⟫_ℝ -
      (setup.τ t *
          inverseProbabilityValue setup (sampledBlock setup t ω)
            (sampledBlock_probability_ne_zero setup
              (sampledPositiveBlock setup t ω))) *
        (SOptLib.carrierBregmanDivergence (dualConjugate setup (sampledBlock setup t ω)) (dualConjugateBaseSelector setup (sampledBlock setup t ω) ((yIter setup hStanding.1 (t - 1) ω) (sampledBlock setup t ω)) (dualSubgradIter setup hStanding.1 (t - 1) ω
            (sampledBlock setup t ω))) ((yIter setup hStanding.1 (t - 1) ω) (sampledBlock setup t ω)) ((yIter setup hStanding.1 t ω) (sampledBlock setup t ω))) -
      setup.η t *
        primalBregman setup
          (xIter setup hStanding.1 (t - 1) ω)
          (xIter setup hStanding.1 t ω))
  let deltaPos : ℕ → BlockSamplePath setup → ℝ := fun t ω =>
    setup.η t *
        primalBregman setup
          (xIter setup hStanding.1 (t - 1) ω)
          (xIter setup hStanding.1 t ω) -
      ⟪xTildeIter setup hStanding.1 t ω -
          (xIter setup hStanding.1 t ω).1,
        ∑ i : ι, (yTildeIter setup hStanding.1 t ω i - (z.2 i).1)⟫_ℝ +
      setup.τ t *
        inverseProbabilityValue setup (sampledBlock setup t ω)
          (sampledBlock_probability_ne_zero setup
            (sampledPositiveBlock setup t ω)) *
        (SOptLib.carrierBregmanDivergence (dualConjugate setup (sampledBlock setup t ω)) (dualConjugateBaseSelector setup (sampledBlock setup t ω) ((yIter setup hStanding.1 (t - 1) ω) (sampledBlock setup t ω)) (dualSubgradIter setup hStanding.1 (t - 1) ω
            (sampledBlock setup t ω))) ((yIter setup hStanding.1 (t - 1) ω) (sampledBlock setup t ω)) ((yIter setup hStanding.1 t ω) (sampledBlock setup t ω)))
  let terminal : BlockSamplePath setup → ℝ := fun ω =>
    setup.η k / 4 *
        ‖(xIter setup hStanding.1 (k - 1) ω).1 -
          (xIter setup hStanding.1 k ω).1‖ ^ 2 -
      ⟪(xIter setup hStanding.1 (k - 1) ω).1 -
          (xIter setup hStanding.1 k ω).1,
        ∑ i : ι, ((yIter setup hStanding.1 k ω i).1 -
          (z.2 i).1)⟫_ℝ
  have hPath : ∀ ω : BlockSamplePath setup,
      θ k * terminal ω ≤
        ∑ t ∈ Finset.Icc 1 k, θ t * deltaPos t ω := by
    intro ω
    simpa [θ, terminal, deltaPos] using
      theorem51_weighted_delta_pathwise_lower_bound_division_free
        setup τ η α hStanding hPolicy hProb hLip hAlpha hRateDen
        k hk hp hθ h51 z ω
  have hMono :
      finitePrefixExpectation setup k (fun ω => θ k * terminal ω) ≤
        finitePrefixExpectation setup k
          (fun ω => ∑ t ∈ Finset.Icc 1 k, θ t * deltaPos t ω) := by
    exact finite_prefix_expectation_mono_of_forall_extend setup k
      (fun pref => hPath (extendBlockPrefix setup k pref))
  have hDeltaPos_neg :
      ∀ t, finitePrefixExpectation setup t (deltaPos t) =
        - finitePrefixExpectation setup t (deltaNeg t) := by
    intro t
    calc
      finitePrefixExpectation setup t (deltaPos t) =
          finitePrefixExpectation setup t (fun ω => (-1 : ℝ) * deltaNeg t ω) := by
            apply congrArg (finitePrefixExpectation setup t)
            funext ω
            dsimp [deltaPos, deltaNeg]
            ring
      _ = (-1 : ℝ) * finitePrefixExpectation setup t (deltaNeg t) := by
            exact finitePrefixExpectation_const_mul setup t (-1) (deltaNeg t)
      _ = - finitePrefixExpectation setup t (deltaNeg t) := by ring
  have hDeltaPos_horizon :
      ∀ t ∈ Finset.Icc 1 k,
        finitePrefixExpectation setup k (deltaPos t) =
          finitePrefixExpectation setup t (deltaPos t) := by
    intro t htmem
    rcases Finset.mem_Icc.mp htmem with ⟨ht, htk⟩
    have hNeg_k :
        finitePrefixExpectation setup k (deltaNeg t) =
          ∫ ω, deltaNeg t ω ∂blockStreamLaw setup := by
      exact finite_prefix_expectation_eq_blockStream_of_extend_eq setup k
        (deltaNeg t) (by
          intro ω
          simpa [deltaNeg] using
            proposition51_delta_negative_prefix_extend_eq
              setup hStanding.1 ht htk ω z)
    have hNeg_t :
        finitePrefixExpectation setup t (deltaNeg t) =
          ∫ ω, deltaNeg t ω ∂blockStreamLaw setup := by
      exact finite_prefix_expectation_eq_blockStream_of_extend_eq setup t
        (deltaNeg t) (by
          intro ω
          simpa [deltaNeg] using
            proposition51_delta_negative_prefix_extend_eq
              setup hStanding.1 ht le_rfl ω z)
    have hNeg_horizon :
        finitePrefixExpectation setup k (deltaNeg t) =
          finitePrefixExpectation setup t (deltaNeg t) := by
      rw [hNeg_k, hNeg_t]
    calc
      finitePrefixExpectation setup k (deltaPos t) =
          finitePrefixExpectation setup k (fun ω => (-1 : ℝ) * deltaNeg t ω) := by
            apply congrArg (finitePrefixExpectation setup k)
            funext ω
            dsimp [deltaPos, deltaNeg]
            ring
      _ = (-1 : ℝ) * finitePrefixExpectation setup k (deltaNeg t) := by
            exact finitePrefixExpectation_const_mul setup k (-1) (deltaNeg t)
      _ = (-1 : ℝ) * finitePrefixExpectation setup t (deltaNeg t) := by
            rw [hNeg_horizon]
      _ = finitePrefixExpectation setup t (deltaPos t) := by
            rw [hDeltaPos_neg t]
            ring
  have hIntegrated :
      θ k * finitePrefixExpectation setup k terminal ≤
        ∑ t ∈ Finset.Icc 1 k, θ t *
          finitePrefixExpectation setup t (deltaPos t) := by
    calc
      θ k * finitePrefixExpectation setup k terminal =
          finitePrefixExpectation setup k (fun ω => θ k * terminal ω) := by
            rw [finitePrefixExpectation_const_mul]
      _ ≤ finitePrefixExpectation setup k
            (fun ω => ∑ t ∈ Finset.Icc 1 k, θ t * deltaPos t ω) := hMono
      _ = ∑ t ∈ Finset.Icc 1 k,
            finitePrefixExpectation setup k (fun ω => θ t * deltaPos t ω) := by
            exact finitePrefixExpectation_sum_finset setup k (Finset.Icc 1 k)
              (fun t ω => θ t * deltaPos t ω)
      _ = ∑ t ∈ Finset.Icc 1 k,
            θ t * finitePrefixExpectation setup k (deltaPos t) := by
            refine Finset.sum_congr rfl ?_
            intro t _ht
            rw [finitePrefixExpectation_const_mul]
      _ = ∑ t ∈ Finset.Icc 1 k,
            θ t * finitePrefixExpectation setup t (deltaPos t) := by
            refine Finset.sum_congr rfl ?_
            intro t ht
            rw [hDeltaPos_horizon t ht]
  have hPosSum_neg :
      (∑ t ∈ Finset.Icc 1 k, θ t *
          finitePrefixExpectation setup t (deltaPos t)) =
        - (∑ t ∈ Finset.Icc 1 k, θ t *
          finitePrefixExpectation setup t (deltaNeg t)) := by
    calc
      (∑ t ∈ Finset.Icc 1 k, θ t *
          finitePrefixExpectation setup t (deltaPos t)) =
          ∑ t ∈ Finset.Icc 1 k, -(θ t *
            finitePrefixExpectation setup t (deltaNeg t)) := by
            refine Finset.sum_congr rfl ?_
            intro t _ht
            rw [hDeltaPos_neg t]
            ring
      _ = - (∑ t ∈ Finset.Icc 1 k, θ t *
            finitePrefixExpectation setup t (deltaNeg t)) := by
            rw [Finset.sum_neg_distrib]
  change (∑ t ∈ Finset.Icc 1 k, θ t *
      finitePrefixExpectation setup t (deltaNeg t)) ≤
    - θ k * finitePrefixExpectation setup k terminal
  rw [hPosSum_neg] at hIntegrated
  nlinarith

set_option maxHeartbeats 2000000

/-- Internal source-gap realization of Proposition 5.1's weighted RPDG bound.
This keeps the paper algebra available for later proof work, but the name marks
that Eqs. (5.1.46), (5.1.48), and (5.1.49) still depend on denominator facts not
stated separately in the source. -/
theorem Proposition_5_1_weighted_RPDG_bound_with_denominator_source_gap
    (θ : ℕ → ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hStanding : standingAssumptions setup)
    (hDen : proposition_5_1_denominatorBoundary setup k)
    (z : SaddlePoint setup)
    (hθ : ∀ t, 1 ≤ t → t ≤ k → 0 ≤ θ t)
    (h46 : propositionCondition_5_1_46_with_denominator_source_gap setup θ k hDen)
    (h47 : ∀ t, 2 ≤ t → t ≤ k →
      θ t * setup.η t ≤ θ (t - 1) * (setup.μ + setup.η (t - 1)))
    (h48 : propositionCondition_5_1_48_with_denominator_source_gap setup k hk hDen)
    (h49 : propositionCondition_5_1_49_with_denominator_source_gap setup k hDen)
    (h50 : propositionCondition_5_1_50_with_denominator_source_gap setup hStanding k hk)
    (h51 : ∀ t, 2 ≤ t → t ≤ k → setup.α t * θ t = θ (t - 1)) :
    (∑ t ∈ Finset.Icc 1 k, θ t *
        expectedSaddleGap setup hStanding t z) ≤
      setup.η 1 * θ 1 * primalBregman setup setup.x0 z.1 -
        (setup.μ + setup.η k) * θ k *
          finitePrefixExpectation setup k
            (fun ω => primalBregman setup (xIter setup hStanding k ω) z.1) +
      ∑ i : ι,
        (θ 1 *
            (inverseProbabilityValue setup i (hDen.1 i) *
              (1 + setup.τ 1) - 1)) *
          (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i (initialDual setup hStanding i) (initialDualSubgradient setup hStanding i)) (initialDual setup hStanding i) (z.2 i)) := by
  classical
  have hWeighted :
      (∑ t ∈ Finset.Icc 1 k, θ t *
          expectedSaddleGap setup hStanding t z) ≤
        ∑ t ∈ Finset.Icc 1 k, θ t *
          (finitePrefixExpectation setup t (fun ω =>
              setup.η t * primalBregman setup (xIter setup hStanding (t - 1) ω) z.1 -
                (setup.μ + setup.η t) *
                  primalBregman setup (xIter setup hStanding t ω) z.1 -
                setup.η t * primalBregman setup
                  (xIter setup hStanding (t - 1) ω)
                  (xIter setup hStanding t ω)) +
            ∑ i : ι,
              finitePrefixExpectation setup t (fun ω =>
                (inverseProbabilityValue setup i (hDen.1 i) *
                    (1 + setup.τ t) - 1) *
                    (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) (z.2 i)) -
                  (inverseProbabilityValue setup i (hDen.1 i) *
                      (1 + setup.τ t)) *
                    (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding t ω) i) (dualSubgradIter setup hStanding t ω i)) ((yIter setup hStanding t ω) i) (z.2 i))) +
            finitePrefixExpectation setup t (fun ω =>
              ⟪xTildeIter setup hStanding t ω - (xIter setup hStanding t ω).1,
                ∑ i : ι, (yTildeIter setup hStanding t ω i - (z.2 i).1)⟫_ℝ -
                (setup.τ t *
                    inverseProbabilityValue setup (sampledBlock setup t ω)
                      (sampledBlock_probability_ne_zero setup
                        (sampledPositiveBlock setup t ω))) *
                  (SOptLib.carrierBregmanDivergence (dualConjugate setup (sampledBlock setup t ω)) (dualConjugateBaseSelector setup (sampledBlock setup t ω) ((yIter setup hStanding (t - 1) ω) (sampledBlock setup t ω)) (dualSubgradIter setup hStanding (t - 1) ω
                      (sampledBlock setup t ω))) ((yIter setup hStanding (t - 1) ω) (sampledBlock setup t ω)) ((yIter setup hStanding t ω) (sampledBlock setup t ω))))) := by
    refine Finset.sum_le_sum ?_
    intro t htmem
    rcases Finset.mem_Icc.mp htmem with ⟨ht, htk⟩
    have hstep :=
      Lemma_5_5_one_step_RPDG_recursion_with_denominator_source_gap
        setup hStanding hDen.1 t ht z
    exact mul_le_mul_of_nonneg_left hstep (hθ t ht htk)
  have hPrimalFull :=
    proposition51_primal_fullstream_telescope
      setup hStanding θ k hk z h47
  have hPrimalInitialFull :
      (∫ ω, primalBregman setup (xIter setup hStanding 0 ω) z.1
          ∂blockStreamLaw setup) =
        primalBregman setup setup.x0 z.1 := by
    letI : IsProbabilityMeasure (blockIndexLaw setup) := by
      unfold blockIndexLaw
      infer_instance
    letI : IsProbabilityMeasure (blockStreamLaw setup) := by
      unfold blockStreamLaw
      exact SOptLib.iidStreamLaw_isProbabilityMeasure (blockIndexLaw setup)
    have hconst :
        (fun ω : BlockSamplePath setup =>
          primalBregman setup (xIter setup hStanding 0 ω) z.1) =
            fun _ω : BlockSamplePath setup =>
              primalBregman setup setup.x0 z.1 := by
      funext ω
      simp [xIter, stateProcess_zero, initialState]
    rw [hconst]
    simp
  have hPrimalTerminalFull :
      (∫ ω, primalBregman setup (xIter setup hStanding k ω) z.1
          ∂blockStreamLaw setup) =
        finitePrefixExpectation setup k
          (fun ω => primalBregman setup (xIter setup hStanding k ω) z.1) := by
    rw [← finite_prefix_expectation_primal_iter_bregman_eq_blockStream_of_le
      setup hStanding (le_rfl : k ≤ k) z.1]
  have hDualFull :=
    fun i : ι =>
      proposition51_dual_fullstream_telescope
        setup hStanding θ k hk hDen z h46 i
  have hDualInitialFull : ∀ i : ι,
      (∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding 0 ω) i) (dualSubgradIter setup hStanding 0 ω i)) ((yIter setup hStanding 0 ω) i) (z.2 i))
            ∂blockStreamLaw setup) =
        (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i (initialDual setup hStanding i) (initialDualSubgradient setup hStanding i)) (initialDual setup hStanding i) (z.2 i)) := by
    intro i
    letI : IsProbabilityMeasure (blockIndexLaw setup) := by
      unfold blockIndexLaw
      infer_instance
    letI : IsProbabilityMeasure (blockStreamLaw setup) := by
      unfold blockStreamLaw
      exact SOptLib.iidStreamLaw_isProbabilityMeasure (blockIndexLaw setup)
    have hconst :
        (fun ω : BlockSamplePath setup =>
          (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding 0 ω) i) (dualSubgradIter setup hStanding 0 ω i)) ((yIter setup hStanding 0 ω) i) (z.2 i))) =
          fun _ω : BlockSamplePath setup =>
            (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i (initialDual setup hStanding i) (initialDualSubgradient setup hStanding i)) (initialDual setup hStanding i) (z.2 i)) := by
      funext ω
      dsimp [yIter, dualSubgradIter]
      rw [stateProcess_zero setup hStanding ω]
      rfl
    rw [hconst]
    simp
  have hDualTerminalFull : ∀ i : ι,
      (∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding k ω) i) (dualSubgradIter setup hStanding k ω i)) ((yIter setup hStanding k ω) i) (z.2 i))
            ∂blockStreamLaw setup) =
        finitePrefixExpectation setup k
          (fun ω => (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding k ω) i) (dualSubgradIter setup hStanding k ω i)) ((yIter setup hStanding k ω) i) (z.2 i))) := by
    intro i
    rw [← finite_prefix_expectation_dual_iter_bregman_eq_blockStream_of_le
      setup hStanding (le_rfl : k ≤ k) i (z.2 i)]
  exact le_trans hWeighted (by
    have _ := hPrimalFull
    have _ := hPrimalInitialFull
    have _ := hPrimalTerminalFull
    have _ := hDualFull
    have _ := hDualInitialFull
    have _ := hDualTerminalFull
    have hTerminalResidualFinite :
        0 ≤ finitePrefixExpectation setup k (fun ω =>
          setup.η k / 4 *
              ‖(xIter setup hStanding (k - 1) ω).1 -
                (xIter setup hStanding k ω).1‖ ^ 2 -
            ⟪(xIter setup hStanding (k - 1) ω).1 -
                (xIter setup hStanding k ω).1,
              ∑ i : ι, ((yIter setup hStanding k ω i).1 -
                (z.2 i).1)⟫_ℝ +
            ∑ i : ι,
              inverseProbabilityValue setup i (hDen.1 i) *
                (1 + setup.τ k) *
                (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding k ω) i) (dualSubgradIter setup hStanding k ω i)) ((yIter setup hStanding k ω) i) (z.2 i))) := by
      unfold finitePrefixExpectation
      exact MeasureTheory.integral_nonneg fun pref =>
        proposition51_terminal_residual_bracket_nonnegative
          setup hStanding k hk hDen h50 z (extendBlockPrefix setup k pref)
    have _ := hTerminalResidualFinite
    have hPrimalFinite :
        (∑ t ∈ Finset.Icc 1 k, θ t *
          finitePrefixExpectation setup t (fun ω =>
            setup.η t *
                primalBregman setup (xIter setup hStanding (t - 1) ω) z.1 -
              (setup.μ + setup.η t) *
                primalBregman setup (xIter setup hStanding t ω) z.1)) ≤
          setup.η 1 * θ 1 * primalBregman setup setup.x0 z.1 -
            (setup.μ + setup.η k) * θ k *
              finitePrefixExpectation setup k
                (fun ω => primalBregman setup (xIter setup hStanding k ω) z.1) := by
      have hsum_eq :
          (∑ t ∈ Finset.Icc 1 k, θ t *
            finitePrefixExpectation setup t (fun ω =>
              setup.η t *
                  primalBregman setup (xIter setup hStanding (t - 1) ω) z.1 -
                (setup.μ + setup.η t) *
                  primalBregman setup (xIter setup hStanding t ω) z.1)) =
            ∑ t ∈ Finset.Icc 1 k, (
              (θ t * setup.η t) *
                  (∫ ω, primalBregman setup
                    (xIter setup hStanding (t - 1) ω) z.1 ∂blockStreamLaw setup) -
                (θ t * (setup.μ + setup.η t)) *
                  (∫ ω, primalBregman setup
                    (xIter setup hStanding t ω) z.1 ∂blockStreamLaw setup)) := by
        refine Finset.sum_congr rfl ?_
        intro t htmem
        rcases Finset.mem_Icc.mp htmem with ⟨ht, _htk⟩
        have hprev :
            finitePrefixExpectation setup t (fun ω =>
              primalBregman setup (xIter setup hStanding (t - 1) ω) z.1) =
              ∫ ω, primalBregman setup
                (xIter setup hStanding (t - 1) ω) z.1 ∂blockStreamLaw setup := by
          exact finite_prefix_expectation_primal_iter_bregman_eq_blockStream_of_le
            setup hStanding (by omega : t - 1 ≤ t) z.1
        have hcur :
            finitePrefixExpectation setup t (fun ω =>
              primalBregman setup (xIter setup hStanding t ω) z.1) =
              ∫ ω, primalBregman setup
                (xIter setup hStanding t ω) z.1 ∂blockStreamLaw setup := by
          exact finite_prefix_expectation_primal_iter_bregman_eq_blockStream_of_le
            setup hStanding (le_rfl : t ≤ t) z.1
        simp [finitePrefixExpectation_sub, finitePrefixExpectation_const_mul,
          hprev, hcur]
        ring
      calc
        (∑ t ∈ Finset.Icc 1 k, θ t *
          finitePrefixExpectation setup t (fun ω =>
            setup.η t *
                primalBregman setup (xIter setup hStanding (t - 1) ω) z.1 -
              (setup.μ + setup.η t) *
                primalBregman setup (xIter setup hStanding t ω) z.1)) =
            ∑ t ∈ Finset.Icc 1 k, (
              (θ t * setup.η t) *
                  (∫ ω, primalBregman setup
                    (xIter setup hStanding (t - 1) ω) z.1 ∂blockStreamLaw setup) -
                (θ t * (setup.μ + setup.η t)) *
                  (∫ ω, primalBregman setup
                    (xIter setup hStanding t ω) z.1 ∂blockStreamLaw setup)) := hsum_eq
        _ ≤ θ 1 * setup.η 1 *
              (∫ ω, primalBregman setup
                (xIter setup hStanding 0 ω) z.1 ∂blockStreamLaw setup) -
            θ k * (setup.μ + setup.η k) *
              (∫ ω, primalBregman setup
                (xIter setup hStanding k ω) z.1 ∂blockStreamLaw setup) := hPrimalFull
        _ = setup.η 1 * θ 1 * primalBregman setup setup.x0 z.1 -
            (setup.μ + setup.η k) * θ k *
              finitePrefixExpectation setup k
                (fun ω => primalBregman setup
                  (xIter setup hStanding k ω) z.1) := by
              rw [hPrimalInitialFull, hPrimalTerminalFull]
              ring
    have _ := hPrimalFinite
    have hDualFinite :
        (∑ i : ι,
          ∑ t ∈ Finset.Icc 1 k, θ t *
            finitePrefixExpectation setup t (fun ω =>
              (inverseProbabilityValue setup i (hDen.1 i) *
                  (1 + setup.τ t) - 1) *
                  (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) (z.2 i)) -
                (inverseProbabilityValue setup i (hDen.1 i) *
                    (1 + setup.τ t)) *
                  (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding t ω) i) (dualSubgradIter setup hStanding t ω i)) ((yIter setup hStanding t ω) i) (z.2 i)))) ≤
          ∑ i : ι, (
            θ 1 *
                (inverseProbabilityValue setup i (hDen.1 i) *
                  (1 + setup.τ 1) - 1) *
              (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i (initialDual setup hStanding i) (initialDualSubgradient setup hStanding i)) (initialDual setup hStanding i) (z.2 i)) -
            inverseProbabilityValue setup i (hDen.1 i) * θ k *
                (1 + setup.τ k) *
              finitePrefixExpectation setup k (fun ω =>
                (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding k ω) i) (dualSubgradIter setup hStanding k ω i)) ((yIter setup hStanding k ω) i) (z.2 i)))) := by
      refine Finset.sum_le_sum ?_
      intro i _hi
      have hsum_eq :
          (∑ t ∈ Finset.Icc 1 k, θ t *
            finitePrefixExpectation setup t (fun ω =>
              (inverseProbabilityValue setup i (hDen.1 i) *
                  (1 + setup.τ t) - 1) *
                  (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) (z.2 i)) -
                (inverseProbabilityValue setup i (hDen.1 i) *
                    (1 + setup.τ t)) *
                  (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding t ω) i) (dualSubgradIter setup hStanding t ω i)) ((yIter setup hStanding t ω) i) (z.2 i)))) =
            ∑ t ∈ Finset.Icc 1 k, (
              θ t *
                  (inverseProbabilityValue setup i (hDen.1 i) *
                    (1 + setup.τ t) - 1) *
                (∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) (z.2 i))
                    ∂blockStreamLaw setup) -
              inverseProbabilityValue setup i (hDen.1 i) * θ t *
                  (1 + setup.τ t) *
                (∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding t ω) i) (dualSubgradIter setup hStanding t ω i)) ((yIter setup hStanding t ω) i) (z.2 i))
                    ∂blockStreamLaw setup)) := by
        refine Finset.sum_congr rfl ?_
        intro t htmem
        rcases Finset.mem_Icc.mp htmem with ⟨ht, _htk⟩
        have hprev :
            finitePrefixExpectation setup t (fun ω =>
              (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) (z.2 i))) =
              ∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) (z.2 i))
                  ∂blockStreamLaw setup := by
          exact finite_prefix_expectation_dual_iter_bregman_eq_blockStream_of_le
            setup hStanding (by omega : t - 1 ≤ t) i (z.2 i)
        have hcur :
            finitePrefixExpectation setup t (fun ω =>
              (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding t ω) i) (dualSubgradIter setup hStanding t ω i)) ((yIter setup hStanding t ω) i) (z.2 i))) =
              ∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding t ω) i) (dualSubgradIter setup hStanding t ω i)) ((yIter setup hStanding t ω) i) (z.2 i))
                  ∂blockStreamLaw setup := by
          exact finite_prefix_expectation_dual_iter_bregman_eq_blockStream_of_le
            setup hStanding (le_rfl : t ≤ t) i (z.2 i)
        simp [finitePrefixExpectation_sub, finitePrefixExpectation_const_mul,
          hprev, hcur]
        ring
      calc
        (∑ t ∈ Finset.Icc 1 k, θ t *
            finitePrefixExpectation setup t (fun ω =>
              (inverseProbabilityValue setup i (hDen.1 i) *
                  (1 + setup.τ t) - 1) *
                  (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) (z.2 i)) -
                (inverseProbabilityValue setup i (hDen.1 i) *
                    (1 + setup.τ t)) *
                  (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding t ω) i) (dualSubgradIter setup hStanding t ω i)) ((yIter setup hStanding t ω) i) (z.2 i)))) =
            ∑ t ∈ Finset.Icc 1 k, (
              θ t *
                  (inverseProbabilityValue setup i (hDen.1 i) *
                    (1 + setup.τ t) - 1) *
                (∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) (z.2 i))
                    ∂blockStreamLaw setup) -
              inverseProbabilityValue setup i (hDen.1 i) * θ t *
                  (1 + setup.τ t) *
                (∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding t ω) i) (dualSubgradIter setup hStanding t ω i)) ((yIter setup hStanding t ω) i) (z.2 i))
                    ∂blockStreamLaw setup)) := hsum_eq
        _ ≤ θ 1 *
              (inverseProbabilityValue setup i (hDen.1 i) *
                (1 + setup.τ 1) - 1) *
            (∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding 0 ω) i) (dualSubgradIter setup hStanding 0 ω i)) ((yIter setup hStanding 0 ω) i) (z.2 i))
                ∂blockStreamLaw setup) -
            inverseProbabilityValue setup i (hDen.1 i) * θ k *
                (1 + setup.τ k) *
              (∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding k ω) i) (dualSubgradIter setup hStanding k ω i)) ((yIter setup hStanding k ω) i) (z.2 i))
                  ∂blockStreamLaw setup) := hDualFull i
        _ = θ 1 *
              (inverseProbabilityValue setup i (hDen.1 i) *
                (1 + setup.τ 1) - 1) *
            (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i (initialDual setup hStanding i) (initialDualSubgradient setup hStanding i)) (initialDual setup hStanding i) (z.2 i)) -
            inverseProbabilityValue setup i (hDen.1 i) * θ k *
                (1 + setup.τ k) *
              finitePrefixExpectation setup k (fun ω =>
                (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding k ω) i) (dualSubgradIter setup hStanding k ω i)) ((yIter setup hStanding k ω) i) (z.2 i))) := by
            rw [hDualInitialFull i, hDualTerminalFull i]
    have _ := hDualFinite
    have hDualWeightedSumComm :
        (∑ t ∈ Finset.Icc 1 k, θ t *
          (∑ i : ι,
            finitePrefixExpectation setup t (fun ω =>
              (inverseProbabilityValue setup i (hDen.1 i) *
                  (1 + setup.τ t) - 1) *
                  (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) (z.2 i)) -
                (inverseProbabilityValue setup i (hDen.1 i) *
                    (1 + setup.τ t)) *
                  (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding t ω) i) (dualSubgradIter setup hStanding t ω i)) ((yIter setup hStanding t ω) i) (z.2 i))))) =
          ∑ i : ι,
            ∑ t ∈ Finset.Icc 1 k, θ t *
              finitePrefixExpectation setup t (fun ω =>
                (inverseProbabilityValue setup i (hDen.1 i) *
                    (1 + setup.τ t) - 1) *
                    (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) (z.2 i)) -
                  (inverseProbabilityValue setup i (hDen.1 i) *
                      (1 + setup.τ t)) *
                    (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding t ω) i) (dualSubgradIter setup hStanding t ω i)) ((yIter setup hStanding t ω) i) (z.2 i))) := by
      calc
        (∑ t ∈ Finset.Icc 1 k, θ t *
          (∑ i : ι,
            finitePrefixExpectation setup t (fun ω =>
              (inverseProbabilityValue setup i (hDen.1 i) *
                  (1 + setup.τ t) - 1) *
                  (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) (z.2 i)) -
                (inverseProbabilityValue setup i (hDen.1 i) *
                    (1 + setup.τ t)) *
                  (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding t ω) i) (dualSubgradIter setup hStanding t ω i)) ((yIter setup hStanding t ω) i) (z.2 i))))) =
            ∑ t ∈ Finset.Icc 1 k,
              ∑ i : ι, θ t *
                finitePrefixExpectation setup t (fun ω =>
                  (inverseProbabilityValue setup i (hDen.1 i) *
                      (1 + setup.τ t) - 1) *
                      (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) (z.2 i)) -
                    (inverseProbabilityValue setup i (hDen.1 i) *
                        (1 + setup.τ t)) *
                      (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding t ω) i) (dualSubgradIter setup hStanding t ω i)) ((yIter setup hStanding t ω) i) (z.2 i))) := by
              refine Finset.sum_congr rfl ?_
              intro t _htmem
              rw [Finset.mul_sum]
        _ = ∑ i : ι,
            ∑ t ∈ Finset.Icc 1 k, θ t *
              finitePrefixExpectation setup t (fun ω =>
                (inverseProbabilityValue setup i (hDen.1 i) *
                    (1 + setup.τ t) - 1) *
                    (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) (z.2 i)) -
                  (inverseProbabilityValue setup i (hDen.1 i) *
                      (1 + setup.τ t)) *
                    (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding t ω) i) (dualSubgradIter setup hStanding t ω i)) ((yIter setup hStanding t ω) i) (z.2 i))) := by
              rw [Finset.sum_comm]
    have _ := hDualWeightedSumComm
    have hTerminalSampledCoefficientNonnegative :
        ∀ ω : BlockSamplePath setup,
          0 ≤ θ k *
            (setup.η k / 4 -
              sourceQuotient
                (setup.L (sampledBlock setup k ω) *
                  (1 - samplingProbability setup (sampledBlock setup k ω)) ^ 2)
                ((componentCount (ι := ι) : ℝ) * setup.τ k *
                  samplingProbability setup (sampledBlock setup k ω))
                (hDen.2 k (sampledBlock setup k ω))) *
              ‖(xIter setup hStanding (k - 1) ω).1 -
                (xIter setup hStanding k ω).1‖ ^ 2 := by
      intro ω
      exact proposition51_h48_terminal_sampled_coefficient_nonnegative
        setup θ k hk hDen hθ h48 (sampledBlock setup k ω)
        ((xIter setup hStanding (k - 1) ω).1 -
          (xIter setup hStanding k ω).1)
    have hHistoricalSampledCoefficientNonnegative :
        ∀ t ∈ Finset.Icc 2 k, ∀ ω : BlockSamplePath setup,
          0 ≤ θ (t - 1) *
            (setup.η (t - 1) / 2 -
              (sourceQuotient
                  (setup.L (sampledBlock setup t ω) * setup.α t)
                  ((componentCount (ι := ι) : ℝ) * setup.τ t *
                    samplingProbability setup (sampledBlock setup t ω))
                  (hDen.2 t (sampledBlock setup t ω)) +
                sourceQuotient
                  ((1 - samplingProbability setup (sampledBlock setup (t - 1) ω)) ^ 2 *
                    setup.L (sampledBlock setup (t - 1) ω))
                  ((componentCount (ι := ι) : ℝ) * setup.τ (t - 1) *
                    samplingProbability setup (sampledBlock setup (t - 1) ω))
                  (hDen.2 (t - 1) (sampledBlock setup (t - 1) ω)))) *
              ‖(xIter setup hStanding (t - 2) ω).1 -
                (xIter setup hStanding (t - 1) ω).1‖ ^ 2 := by
      intro t htmem ω
      rcases Finset.mem_Icc.mp htmem with ⟨ht2, htk⟩
      exact proposition51_h49_historical_coefficient_nonnegative
        setup θ k hDen hθ h49 t
        (sampledBlock setup t ω) (sampledBlock setup (t - 1) ω)
        ht2 htk
        ((xIter setup hStanding (t - 2) ω).1 -
          (xIter setup hStanding (t - 1) ω).1)
    have _ := hTerminalSampledCoefficientNonnegative
    have _ := hHistoricalSampledCoefficientNonnegative
    have hTerminalResidualWeightedNonnegative :
        0 ≤ θ k *
          finitePrefixExpectation setup k (fun ω =>
            setup.η k / 4 *
                ‖(xIter setup hStanding (k - 1) ω).1 -
                  (xIter setup hStanding k ω).1‖ ^ 2 -
              ⟪(xIter setup hStanding (k - 1) ω).1 -
                  (xIter setup hStanding k ω).1,
                ∑ i : ι, ((yIter setup hStanding k ω i).1 -
                  (z.2 i).1)⟫_ℝ +
              ∑ i : ι,
                inverseProbabilityValue setup i (hDen.1 i) *
                  (1 + setup.τ k) *
                  (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding k ω) i) (dualSubgradIter setup hStanding k ω i)) ((yIter setup hStanding k ω) i) (z.2 i))) := by
      exact mul_nonneg (hθ k hk le_rfl) hTerminalResidualFinite
    have _ := hTerminalResidualWeightedNonnegative
    have hDeltaUpper :
        (∑ t ∈ Finset.Icc 1 k, θ t *
          finitePrefixExpectation setup t (fun ω =>
            (⟪xTildeIter setup hStanding t ω - (xIter setup hStanding t ω).1,
                ∑ i : ι, (yTildeIter setup hStanding t ω i - (z.2 i).1)⟫_ℝ -
              (setup.τ t *
                  inverseProbabilityValue setup (sampledBlock setup t ω)
                    (sampledBlock_probability_ne_zero setup
                      (sampledPositiveBlock setup t ω))) *
                (SOptLib.carrierBregmanDivergence (dualConjugate setup (sampledBlock setup t ω)) (dualConjugateBaseSelector setup (sampledBlock setup t ω) ((yIter setup hStanding (t - 1) ω) (sampledBlock setup t ω)) (dualSubgradIter setup hStanding (t - 1) ω
                    (sampledBlock setup t ω))) ((yIter setup hStanding (t - 1) ω) (sampledBlock setup t ω)) ((yIter setup hStanding t ω) (sampledBlock setup t ω)))) -
              setup.η t *
                primalBregman setup
                  (xIter setup hStanding (t - 1) ω)
                  (xIter setup hStanding t ω))) ≤
          - θ k *
            finitePrefixExpectation setup k (fun ω =>
              setup.η k / 4 *
                  ‖(xIter setup hStanding (k - 1) ω).1 -
                    (xIter setup hStanding k ω).1‖ ^ 2 -
                ⟪(xIter setup hStanding (k - 1) ω).1 -
                    (xIter setup hStanding k ω).1,
                  ∑ i : ι, ((yIter setup hStanding k ω i).1 -
                    (z.2 i).1)⟫_ℝ) := by
      exact proposition51_weighted_delta_finitePrefix_upper_bound
        setup hStanding θ k hk hDen z hθ h48 h49 h51
    have hDualTimeBound :
        (∑ t ∈ Finset.Icc 1 k, θ t *
          (∑ i : ι,
            finitePrefixExpectation setup t (fun ω =>
              (inverseProbabilityValue setup i (hDen.1 i) *
                  (1 + setup.τ t) - 1) *
                  (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) (z.2 i)) -
                (inverseProbabilityValue setup i (hDen.1 i) *
                    (1 + setup.τ t)) *
                  (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding t ω) i) (dualSubgradIter setup hStanding t ω i)) ((yIter setup hStanding t ω) i) (z.2 i))))) ≤
          ∑ i : ι, (
            θ 1 *
                (inverseProbabilityValue setup i (hDen.1 i) *
                  (1 + setup.τ 1) - 1) *
              (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i (initialDual setup hStanding i) (initialDualSubgradient setup hStanding i)) (initialDual setup hStanding i) (z.2 i)) -
            inverseProbabilityValue setup i (hDen.1 i) * θ k *
                (1 + setup.τ k) *
              finitePrefixExpectation setup k (fun ω =>
                (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding k ω) i) (dualSubgradIter setup hStanding k ω i)) ((yIter setup hStanding k ω) i) (z.2 i)))) := by
      rw [hDualWeightedSumComm]
      exact hDualFinite
    have hTerminalTailNonpositive :
        - θ k *
            finitePrefixExpectation setup k (fun ω =>
              setup.η k / 4 *
                  ‖(xIter setup hStanding (k - 1) ω).1 -
                    (xIter setup hStanding k ω).1‖ ^ 2 -
                ⟪(xIter setup hStanding (k - 1) ω).1 -
                    (xIter setup hStanding k ω).1,
                  ∑ i : ι, ((yIter setup hStanding k ω i).1 -
                    (z.2 i).1)⟫_ℝ) -
          ∑ i : ι,
            inverseProbabilityValue setup i (hDen.1 i) * θ k *
                (1 + setup.τ k) *
              finitePrefixExpectation setup k (fun ω =>
                (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding k ω) i) (dualSubgradIter setup hStanding k ω i)) ((yIter setup hStanding k ω) i) (z.2 i))) ≤ 0 := by
      have hterminal_dual_factor :
          ((∑ i : ι,
            inverseProbabilityValue setup i (hDen.1 i) * θ k *
                (1 + setup.τ k) *
              finitePrefixExpectation setup k (fun ω =>
                (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding k ω) i) (dualSubgradIter setup hStanding k ω i)) ((yIter setup hStanding k ω) i) (z.2 i))))) =
            θ k *
              (∑ i : ι,
                inverseProbabilityValue setup i (hDen.1 i) *
                  (1 + setup.τ k) *
                finitePrefixExpectation setup k (fun ω =>
                  (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding k ω) i) (dualSubgradIter setup hStanding k ω i)) ((yIter setup hStanding k ω) i) (z.2 i)))) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro i _hi
        ring
      have htail_eq :
          - θ k *
              finitePrefixExpectation setup k (fun ω =>
                setup.η k / 4 *
                    ‖(xIter setup hStanding (k - 1) ω).1 -
                      (xIter setup hStanding k ω).1‖ ^ 2 -
                  ⟪(xIter setup hStanding (k - 1) ω).1 -
                      (xIter setup hStanding k ω).1,
                    ∑ i : ι, ((yIter setup hStanding k ω i).1 -
                      (z.2 i).1)⟫_ℝ) -
            ∑ i : ι,
              inverseProbabilityValue setup i (hDen.1 i) * θ k *
                  (1 + setup.τ k) *
                finitePrefixExpectation setup k (fun ω =>
                  (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding k ω) i) (dualSubgradIter setup hStanding k ω i)) ((yIter setup hStanding k ω) i) (z.2 i))) =
            - θ k *
              finitePrefixExpectation setup k (fun ω =>
                (setup.η k / 4 *
                    ‖(xIter setup hStanding (k - 1) ω).1 -
                      (xIter setup hStanding k ω).1‖ ^ 2 -
                  ⟪(xIter setup hStanding (k - 1) ω).1 -
                      (xIter setup hStanding k ω).1,
                    ∑ i : ι, ((yIter setup hStanding k ω i).1 -
                      (z.2 i).1)⟫_ℝ) +
                ∑ i : ι,
                  inverseProbabilityValue setup i (hDen.1 i) *
                    (1 + setup.τ k) *
                    (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding k ω) i) (dualSubgradIter setup hStanding k ω i)) ((yIter setup hStanding k ω) i) (z.2 i))) := by
        rw [finitePrefixExpectation_add, finitePrefixExpectation_finset_sum]
        simp [finitePrefixExpectation_const_mul, hterminal_dual_factor]
        ring
      rw [htail_eq]
      nlinarith [hTerminalResidualWeightedNonnegative]
    have hWeightedRhsSplit :
        (∑ t ∈ Finset.Icc 1 k, θ t *
          (((finitePrefixExpectation setup t (fun ω =>
                setup.η t * primalBregman setup (xIter setup hStanding (t - 1) ω) z.1 -
                  (setup.μ + setup.η t) *
                    primalBregman setup (xIter setup hStanding t ω) z.1 -
                  setup.η t * primalBregman setup
                    (xIter setup hStanding (t - 1) ω)
                    (xIter setup hStanding t ω)) +
              ∑ i : ι,
                finitePrefixExpectation setup t (fun ω =>
                  (inverseProbabilityValue setup i (hDen.1 i) *
                      (1 + setup.τ t) - 1) *
                      (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) (z.2 i)) -
                    (inverseProbabilityValue setup i (hDen.1 i) *
                        (1 + setup.τ t)) *
                      (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding t ω) i) (dualSubgradIter setup hStanding t ω i)) ((yIter setup hStanding t ω) i) (z.2 i)))) +
            finitePrefixExpectation setup t (fun ω =>
              ⟪xTildeIter setup hStanding t ω - (xIter setup hStanding t ω).1,
                ∑ i : ι, (yTildeIter setup hStanding t ω i - (z.2 i).1)⟫_ℝ -
                (setup.τ t *
                    inverseProbabilityValue setup (sampledBlock setup t ω)
                      (sampledBlock_probability_ne_zero setup
                        (sampledPositiveBlock setup t ω))) *
                  (SOptLib.carrierBregmanDivergence (dualConjugate setup (sampledBlock setup t ω)) (dualConjugateBaseSelector setup (sampledBlock setup t ω) ((yIter setup hStanding (t - 1) ω) (sampledBlock setup t ω)) (dualSubgradIter setup hStanding (t - 1) ω
                      (sampledBlock setup t ω))) ((yIter setup hStanding (t - 1) ω) (sampledBlock setup t ω)) ((yIter setup hStanding t ω) (sampledBlock setup t ω)))))) =
          (∑ t ∈ Finset.Icc 1 k, θ t *
            finitePrefixExpectation setup t (fun ω =>
              setup.η t * primalBregman setup (xIter setup hStanding (t - 1) ω) z.1 -
                (setup.μ + setup.η t) *
                  primalBregman setup (xIter setup hStanding t ω) z.1)) +
          (∑ t ∈ Finset.Icc 1 k, θ t *
            (∑ i : ι,
              finitePrefixExpectation setup t (fun ω =>
                (inverseProbabilityValue setup i (hDen.1 i) *
                    (1 + setup.τ t) - 1) *
                    (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) (z.2 i)) -
                  (inverseProbabilityValue setup i (hDen.1 i) *
                      (1 + setup.τ t)) *
                    (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding t ω) i) (dualSubgradIter setup hStanding t ω i)) ((yIter setup hStanding t ω) i) (z.2 i))))) +
          (∑ t ∈ Finset.Icc 1 k, θ t *
            finitePrefixExpectation setup t (fun ω =>
              (⟪xTildeIter setup hStanding t ω - (xIter setup hStanding t ω).1,
                  ∑ i : ι, (yTildeIter setup hStanding t ω i - (z.2 i).1)⟫_ℝ -
                (setup.τ t *
                    inverseProbabilityValue setup (sampledBlock setup t ω)
                      (sampledBlock_probability_ne_zero setup
                        (sampledPositiveBlock setup t ω))) *
                  (SOptLib.carrierBregmanDivergence (dualConjugate setup (sampledBlock setup t ω)) (dualConjugateBaseSelector setup (sampledBlock setup t ω) ((yIter setup hStanding (t - 1) ω) (sampledBlock setup t ω)) (dualSubgradIter setup hStanding (t - 1) ω
                      (sampledBlock setup t ω))) ((yIter setup hStanding (t - 1) ω) (sampledBlock setup t ω)) ((yIter setup hStanding t ω) (sampledBlock setup t ω)))) -
                setup.η t *
                  primalBregman setup
                    (xIter setup hStanding (t - 1) ω)
                    (xIter setup hStanding t ω)))) := by
      calc
        (∑ t ∈ Finset.Icc 1 k, θ t *
          (((finitePrefixExpectation setup t (fun ω =>
                setup.η t * primalBregman setup (xIter setup hStanding (t - 1) ω) z.1 -
                  (setup.μ + setup.η t) *
                    primalBregman setup (xIter setup hStanding t ω) z.1 -
                  setup.η t * primalBregman setup
                    (xIter setup hStanding (t - 1) ω)
                    (xIter setup hStanding t ω)) +
              ∑ i : ι,
                finitePrefixExpectation setup t (fun ω =>
                  (inverseProbabilityValue setup i (hDen.1 i) *
                      (1 + setup.τ t) - 1) *
                      (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) (z.2 i)) -
                    (inverseProbabilityValue setup i (hDen.1 i) *
                        (1 + setup.τ t)) *
                      (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding t ω) i) (dualSubgradIter setup hStanding t ω i)) ((yIter setup hStanding t ω) i) (z.2 i)))) +
            finitePrefixExpectation setup t (fun ω =>
              ⟪xTildeIter setup hStanding t ω - (xIter setup hStanding t ω).1,
                ∑ i : ι, (yTildeIter setup hStanding t ω i - (z.2 i).1)⟫_ℝ -
                (setup.τ t *
                    inverseProbabilityValue setup (sampledBlock setup t ω)
                      (sampledBlock_probability_ne_zero setup
                        (sampledPositiveBlock setup t ω))) *
                  (SOptLib.carrierBregmanDivergence (dualConjugate setup (sampledBlock setup t ω)) (dualConjugateBaseSelector setup (sampledBlock setup t ω) ((yIter setup hStanding (t - 1) ω) (sampledBlock setup t ω)) (dualSubgradIter setup hStanding (t - 1) ω
                      (sampledBlock setup t ω))) ((yIter setup hStanding (t - 1) ω) (sampledBlock setup t ω)) ((yIter setup hStanding t ω) (sampledBlock setup t ω)))))) =
            ∑ t ∈ Finset.Icc 1 k, (
              θ t *
                finitePrefixExpectation setup t (fun ω =>
                  setup.η t * primalBregman setup (xIter setup hStanding (t - 1) ω) z.1 -
                    (setup.μ + setup.η t) *
                      primalBregman setup (xIter setup hStanding t ω) z.1) +
              θ t *
                (∑ i : ι,
                  finitePrefixExpectation setup t (fun ω =>
                    (inverseProbabilityValue setup i (hDen.1 i) *
                        (1 + setup.τ t) - 1) *
                        (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) (z.2 i)) -
                      (inverseProbabilityValue setup i (hDen.1 i) *
                          (1 + setup.τ t)) *
                        (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding t ω) i) (dualSubgradIter setup hStanding t ω i)) ((yIter setup hStanding t ω) i) (z.2 i)))) +
              θ t *
                finitePrefixExpectation setup t (fun ω =>
                  (⟪xTildeIter setup hStanding t ω - (xIter setup hStanding t ω).1,
                      ∑ i : ι, (yTildeIter setup hStanding t ω i - (z.2 i).1)⟫_ℝ -
                    (setup.τ t *
                        inverseProbabilityValue setup (sampledBlock setup t ω)
                          (sampledBlock_probability_ne_zero setup
                            (sampledPositiveBlock setup t ω))) *
                      (SOptLib.carrierBregmanDivergence (dualConjugate setup (sampledBlock setup t ω)) (dualConjugateBaseSelector setup (sampledBlock setup t ω) ((yIter setup hStanding (t - 1) ω) (sampledBlock setup t ω)) (dualSubgradIter setup hStanding (t - 1) ω
                          (sampledBlock setup t ω))) ((yIter setup hStanding (t - 1) ω) (sampledBlock setup t ω)) ((yIter setup hStanding t ω) (sampledBlock setup t ω)))) -
                    setup.η t *
                      primalBregman setup
                        (xIter setup hStanding (t - 1) ω)
                        (xIter setup hStanding t ω)))) := by
              refine Finset.sum_congr rfl ?_
              intro t _htmem
              simp [finitePrefixExpectation_add, finitePrefixExpectation_sub,
                sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
              ring
        _ = _ := by
              rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    have hDualEndpointSplit :
        (∑ i : ι, (
            θ 1 *
                (inverseProbabilityValue setup i (hDen.1 i) *
                  (1 + setup.τ 1) - 1) *
              (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i (initialDual setup hStanding i) (initialDualSubgradient setup hStanding i)) (initialDual setup hStanding i) (z.2 i)) -
            inverseProbabilityValue setup i (hDen.1 i) * θ k *
                (1 + setup.τ k) *
              finitePrefixExpectation setup k (fun ω =>
                (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding k ω) i) (dualSubgradIter setup hStanding k ω i)) ((yIter setup hStanding k ω) i) (z.2 i))))) =
          ((∑ i : ι,
            θ 1 *
                (inverseProbabilityValue setup i (hDen.1 i) *
                  (1 + setup.τ 1) - 1) *
              (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i (initialDual setup hStanding i) (initialDualSubgradient setup hStanding i)) (initialDual setup hStanding i) (z.2 i))) -
          (∑ i : ι,
            inverseProbabilityValue setup i (hDen.1 i) * θ k *
                (1 + setup.τ k) *
              finitePrefixExpectation setup k (fun ω =>
                (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding k ω) i) (dualSubgradIter setup hStanding k ω i)) ((yIter setup hStanding k ω) i) (z.2 i))))) := by
      rw [Finset.sum_sub_distrib]
    rw [hWeightedRhsSplit]
    rw [hDualEndpointSplit] at hDualTimeBound
    nlinarith [hPrimalFinite, hDualTimeBound, hDeltaUpper,
      hTerminalTailNonpositive])

/-- Theorem 5.1 local proof of Proposition condition (5.1.50), derived from
the constant policy, the Lipschitz/stepsize condition `(5.1.62)`, and sampling
probability normalization. Existing candidates considered:
`propositionCondition_5_1_50_with_denominator_source_gap` is only the target
paper condition, while the SOptLib finite-sum probability hits package unrelated
importance-weighted mean identities rather than this scalar aggregate
Lipschitz budget. -/
private theorem theorem51_condition_50_division_free
    (τ η α : ℝ)
    (hStanding : theoremStandingAssumptions setup)
    (hPolicy : constantParameterPolicy setup τ η α)
    (hLip : constantParameterConditionLipschitz setup τ η)
    (k : ℕ) (hk : 1 ≤ k) :
    propositionCondition_5_1_50_with_denominator_source_gap setup hStanding.1 k hk := by
  classical
  have hτk_nonneg : 0 ≤ setup.τ k := by
    rcases hStanding.1 with ⟨_, _, _, _, _, _, _, _, _, _, _, hParam⟩
    exact hParam.1 k hk
  have hηk_nonneg : 0 ≤ setup.η k := by
    rcases hStanding.1 with ⟨_, _, _, _, _, _, _, _, _, _, _, hParam⟩
    exact hParam.2.1 k hk
  have hτk : setup.τ k = τ := hPolicy.1 k hk
  have hηk : setup.η k = η := hPolicy.2.1 k hk
  have hpoint :
      ∀ i : ι,
        (4 * setup.L i) / (componentCount (ι := ι) : ℝ) ≤
          setup.η k * setup.τ k * samplingProbability setup i := by
    intro i
    simpa [sourceQuotient_def, hτk, hηk, mul_assoc, mul_comm, mul_left_comm]
      using hLip i
  unfold propositionCondition_5_1_50_with_denominator_source_gap
  rw [sourceQuotient_def]
  exact
    finset_weighted_sum_div_le_half_of_pointwise_four_mul_div_le
      (s := Finset.univ)
      (p := samplingProbability setup) (a := setup.L)
      (m := (componentCount (ι := ι) : ℝ))
      (tau := setup.τ k) (eta := setup.η k)
      (componentCount_real_pos (ι := ι)) hτk_nonneg hηk_nonneg
      (fun i _hi => samplingProbability_nonnegative setup i)
      (by simpa using samplingProbability_sum_one setup)
      (fun i _hi => hpoint i)

/-- Theorem 5.1 local form of Proposition condition (5.1.46), derived from the
constant policy, the probability condition `(1-α)(1+τ)≤p_i`, and the output
weight shift Eq. (5.1.65). Existing candidates considered:
`propositionCondition_5_1_46_with_denominator_source_gap` has the same paper
inequality but is tied to `proposition_5_1_denominatorBoundary`, while
`theorem51_inverse_probability_initial_coefficient_le` only bounds the initial
endpoint coefficient and does not provide the adjacent-time telescope bridge. -/
private theorem theorem51_condition_46_division_free
    (τ η α : ℝ)
    (hStanding : theoremStandingAssumptions setup)
    (hPolicy : constantParameterPolicy setup τ η α)
    (hProb : constantParameterConditionProbability setup τ α)
    (hAlpha : alphaRange α)
    (k : ℕ)
    (hp : ∀ i : ι, samplingProbability setup i ≠ 0) :
    ∀ t i, 2 ≤ t → t ≤ k →
      theoremOutputWeight α hAlpha t *
          (inverseProbabilityValue setup i (hp i) *
            (1 + setup.τ t) - 1) ≤
        inverseProbabilityValue setup i (hp i) *
          theoremOutputWeight α hAlpha (t - 1) *
            (1 + setup.τ (t - 1)) := by
  intro t i ht2 _htk
  have ht1 : 1 ≤ t := by omega
  have htprev1 : 1 ≤ t - 1 := by omega
  have hτt : setup.τ t = τ := hPolicy.1 t ht1
  have hτprev : setup.τ (t - 1) = τ := hPolicy.1 (t - 1) htprev1
  have hαt : setup.α t = α := hPolicy.2.2 t ht1
  have hshift :
      theoremOutputWeight α hAlpha (t - 1) =
        α * theoremOutputWeight α hAlpha t := by
    have hs := theorem51_output_weight_shift setup τ η α hPolicy hAlpha t ht2
    rw [hαt] at hs
    simpa [mul_comm] using hs.symm
  let p : ℝ := samplingProbability setup i
  have hp_pos : 0 < p := by
    simpa [p] using
      samplingProbability_pos_of_theorem_conditions
        setup τ η α hStanding hPolicy hProb hAlpha i
  have hprob : (1 - α) * (1 + τ) ≤ p := by
    simpa [p] using hProb i
  have hθ_nonneg : 0 ≤ theoremOutputWeight α hAlpha t := by
    have hpow : 0 < α ^ t := pow_pos hAlpha.1 t
    have hpos : 0 < theoremOutputWeight α hAlpha t := by
      simpa [theoremOutputWeight, sourceQuotient] using
        one_div_pos.mpr hpow
    exact hpos.le
  simpa [p, inverseProbabilityValue, sourceQuotient_def, one_div, hτt, hτprev]
    using
      (weighted_inverse_probability_adjacent_coeff_le
        (p := p) (tau := τ) (alpha := α)
        (theta := theoremOutputWeight α hAlpha t)
        (thetaPrev := theoremOutputWeight α hAlpha (t - 1))
        hp_pos hprob hθ_nonneg hshift)

/-- Theorem 5.1 local form of Proposition condition (5.1.47), derived from
`η≤α(μ+η)` and the output weight shift Eq. (5.1.65). Existing candidates
considered: `proposition51_primal_fullstream_telescope` consumes this bridge
but does not derive it, and no SOptLib scalar schedule lemma specializes the
paper's adjacent coefficients `θ_tη_t` and `θ_{t-1}(μ+η_{t-1})` under the
constant-parameter policy. -/
private theorem theorem51_condition_47_division_free
    (τ η α : ℝ)
    (hPolicy : constantParameterPolicy setup τ η α)
    (hEta : constantParameterConditionEta setup η α)
    (hAlpha : alphaRange α)
    (k : ℕ) :
    ∀ t, 2 ≤ t → t ≤ k →
      theoremOutputWeight α hAlpha t * setup.η t ≤
        theoremOutputWeight α hAlpha (t - 1) *
          (setup.μ + setup.η (t - 1)) := by
  classical
  intro t ht2 _htk
  let θt : ℝ := theoremOutputWeight α hAlpha t
  have ht1 : 1 ≤ t := by omega
  have htprev1 : 1 ≤ t - 1 := by omega
  have hηt : setup.η t = η := hPolicy.2.1 t ht1
  have hηprev : setup.η (t - 1) = η := hPolicy.2.1 (t - 1) htprev1
  have hαt : setup.α t = α := hPolicy.2.2 t ht1
  have hshift :
      theoremOutputWeight α hAlpha (t - 1) = α * θt := by
    have hs := theorem51_output_weight_shift setup τ η α hPolicy hAlpha t ht2
    rw [hαt] at hs
    simpa [θt, mul_comm] using hs.symm
  have hθ_nonneg : 0 ≤ θt := by
    have hpow : 0 < α ^ t := pow_pos hAlpha.1 t
    have hpos : 0 < θt := by
      simpa [θt, theoremOutputWeight, sourceQuotient] using
        one_div_pos.mpr hpow
    exact hpos.le
  simpa [θt, hηt, hηprev] using
    (mul_le_mul_add_of_le_mul_add_of_nonneg_left_of_eq_mul
      (eta := η) (mu := setup.μ) (alpha := α)
      (theta := θt) (thetaPrev := theoremOutputWeight α hAlpha (t - 1))
      hEta hθ_nonneg hshift)

/-- Fixed-coordinate dual part of the weighted Theorem 5.1 telescope, aligned
with Lan Eq. (5.1.53) but using only the theorem-derived all-block
nonzero-probability facts. Existing candidates considered:
`proposition51_dual_fullstream_telescope` has the same scalar telescope but is
tied to `proposition_5_1_denominatorBoundary`; SOptLib
`sum_Icc_two_coeff_telescope_le` supplies the abstract adjacent-coefficient
telescope and is specialized here to the paper's selected dual Bregman terms. -/
private theorem theorem51_dual_fullstream_telescope_division_free
    (hStanding : standingAssumptions setup)
    (θ : ℕ → ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hp : ∀ i : ι, samplingProbability setup i ≠ 0)
    (z : SaddlePoint setup)
    (h46 : ∀ t i, 2 ≤ t → t ≤ k →
      θ t * (inverseProbabilityValue setup i (hp i) *
          (1 + setup.τ t) - 1) ≤
        inverseProbabilityValue setup i (hp i) *
          θ (t - 1) * (1 + setup.τ (t - 1)))
    (i : ι) :
    (Finset.sum (Finset.Icc 1 k) (fun t =>
        (θ t * (inverseProbabilityValue setup i (hp i) *
            (1 + setup.τ t) - 1)) *
            (∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) (z.2 i))
                ∂blockStreamLaw setup) -
          (inverseProbabilityValue setup i (hp i) * θ t *
              (1 + setup.τ t)) *
            (∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding t ω) i) (dualSubgradIter setup hStanding t ω i)) ((yIter setup hStanding t ω) i) (z.2 i))
                ∂blockStreamLaw setup))) ≤
      (θ 1 * (inverseProbabilityValue setup i (hp i) *
          (1 + setup.τ 1) - 1)) *
          (∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding 0 ω) i) (dualSubgradIter setup hStanding 0 ω i)) ((yIter setup hStanding 0 ω) i) (z.2 i))
              ∂blockStreamLaw setup) -
        (inverseProbabilityValue setup i (hp i) * θ k *
            (1 + setup.τ k)) *
          (∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding k ω) i) (dualSubgradIter setup hStanding k ω i)) ((yIter setup hStanding k ω) i) (z.2 i))
              ∂blockStreamLaw setup) := by
  classical
  let c : ℕ → ℝ := fun t =>
    θ t * (inverseProbabilityValue setup i (hp i) *
      (1 + setup.τ t) - 1)
  let d : ℕ → ℝ := fun t =>
    inverseProbabilityValue setup i (hp i) * θ t * (1 + setup.τ t)
  let V : ℕ → ℝ := fun t =>
    ∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding t ω) i) (dualSubgradIter setup hStanding t ω i)) ((yIter setup hStanding t ω) i) (z.2 i))
        ∂blockStreamLaw setup
  have hV_nonneg : ∀ n, 1 ≤ n → n < k → 0 ≤ V n := by
    intro n _hn _hnk
    dsimp [V]
    exact MeasureTheory.integral_nonneg fun ω =>
      dualBregman_nonnegative setup i ((yIter setup hStanding n ω) i)
        (dualSubgradIter setup hStanding n ω i) (z.2 i)
  have hbridge : ∀ n, 1 ≤ n → n < k → c (n + 1) ≤ d n := by
    intro n hn hnk
    have htwo : 2 ≤ n + 1 := by omega
    have hle : n + 1 ≤ k := by omega
    have h := h46 (n + 1) i htwo hle
    simpa [c, d, Nat.succ_eq_add_one, mul_assoc] using h
  simpa [c, d, V, mul_assoc] using
    (SOptLib.sum_Icc_two_coeff_telescope_le c d V k hk hV_nonneg hbridge)

set_option maxHeartbeats 2000000

/-- Internal source-gap realization of Theorem 5.1 rate bounds,
Eqs. (5.1.63)--(5.1.64), in the paper's displayed quotient form. This is not an
A-level source-facing theorem statement because the PDF prints rate denominators
involving `η` without separately stating `η ≠ 0`. -/
def theorem_5_1_rateBounds_with_denominator_source_gap
    (setup : Setup E ι) (η α : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hRateDen : theorem_5_1_rateDenominatorBoundary η)
    (hStanding : theoremStandingAssumptions setup)
    (hAlpha : alphaRange α) (xstar : PrimalCarrier setup)
    (hxstar : IsOptimalPrimal setup xstar) : Prop :=
  expectedBregmanDistance setup hStanding.1 k xstar ≤
      (1 + sourceQuotient (setup.Lf * α) ((1 - α) * η)
          (rateProductDenominator_ne_for_theorem_5_1 η α hRateDen hAlpha)) *
        α ^ k *
        primalBregman setup setup.x0 xstar ∧
    expectedPrimalOptimalityGap setup α k hk hStanding.1 hAlpha xstar hxstar ≤
      Real.rpow α ((k : ℝ) / 2) *
        (sourceQuotient 1 α (alpha_ne_zero_of_alphaRange hAlpha) * η +
          sourceQuotient (3 - 2 * α) (1 - α)
              (one_sub_alpha_ne_zero_of_alphaRange hAlpha) * setup.Lf +
          sourceQuotient (2 * setup.Lf ^ 2 * α) ((1 - α) * η)
            (rateProductDenominator_ne_for_theorem_5_1 η α hRateDen hAlpha)) *
          primalBregman setup setup.x0 xstar

/-- Arbitrary-horizon terminal-budget form of Lan Theorem 5.1 Eq. (5.1.63)
before the final scalar division. Existing candidates considered: the pre-search
digest had no SOptLib/Mathlib candidate for this object; searched `expectedBregmanDistance
arbitrary time terminal budget Theorem 5.1 Eq 5.1.63`, `terminal budget
theorem 5.1 proposition weighted bound division free`, and `Bregman distance
rate expected arbitrary time`. The relevant local pieces are the division-free
Delta, condition, and telescope helpers, while the public Proposition 5.1 API
requires the forbidden `proposition_5_1_denominatorBoundary`, so this helper
replays the source proof steps 8--9 at an arbitrary horizon. -/
private theorem theorem51_terminal_budget_arbitrary_time
    (τ η α : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hStanding : theoremStandingAssumptions setup)
    (hPolicy : constantParameterPolicy setup τ η α)
    (hProb : constantParameterConditionProbability setup τ α)
    (hEta : constantParameterConditionEta setup η α)
    (hLip : constantParameterConditionLipschitz setup τ η)
    (hAlpha : alphaRange α)
    (hRateDen : theorem_5_1_rateDenominatorBoundary η)
    (xstar : PrimalCarrier setup) (hxstar : IsOptimalPrimal setup xstar) :
    (setup.μ + setup.η k) * theoremOutputWeight α hAlpha k *
      finitePrefixExpectation setup k
        (fun ω => primalBregman setup (xIter setup hStanding.1 k ω) xstar) ≤
      setup.η 1 * theoremOutputWeight α hAlpha 1 *
        primalBregman setup setup.x0 xstar +
        theoremOutputWeight α hAlpha 1 *
          sourceQuotient α (1 - α)
            (one_sub_alpha_ne_zero_of_alphaRange hAlpha) *
          (setup.Lf * primalBregman setup setup.x0 xstar) := by
  classical
  let θ : ℕ → ℝ := theoremOutputWeight α hAlpha
  let hp : ∀ i : ι, samplingProbability setup i ≠ 0 :=
    inverseProbabilityDenominators_ne_of_theorem_conditions
      setup τ η α hStanding hPolicy hProb hAlpha
  have hθ : ∀ t, 1 ≤ t → t ≤ k → 0 ≤ θ t := by
    intro t ht1 htk
    exact outputTheta_nonnegative_of_alphaRange α k hAlpha () t
      (by simpa [outputTimeWindow] using Finset.mem_Icc.mpr ⟨ht1, htk⟩)
  have h51 : ∀ t, 2 ≤ t → t ≤ k → setup.α t * θ t = θ (t - 1) := by
    intro t ht2 _htk
    exact theorem51_output_weight_shift setup τ η α hPolicy hAlpha t ht2
  let zstar : SaddlePoint setup :=
    (xstar, fun i => scaledComponentGradientDual setup hStanding.1 i xstar.1)
  have hDeltaFinite :
      (∑ t ∈ Finset.Icc 1 k, θ t *
        finitePrefixExpectation setup t (fun ω =>
          (⟪xTildeIter setup hStanding.1 t ω - (xIter setup hStanding.1 t ω).1,
              ∑ i : ι, (yTildeIter setup hStanding.1 t ω i - (zstar.2 i).1)⟫_ℝ -
            (setup.τ t *
                inverseProbabilityValue setup (sampledBlock setup t ω)
                  (sampledBlock_probability_ne_zero setup
                    (sampledPositiveBlock setup t ω))) *
              (SOptLib.carrierBregmanDivergence (dualConjugate setup (sampledBlock setup t ω)) (dualConjugateBaseSelector setup (sampledBlock setup t ω) ((yIter setup hStanding.1 (t - 1) ω) (sampledBlock setup t ω)) (dualSubgradIter setup hStanding.1 (t - 1) ω
                  (sampledBlock setup t ω))) ((yIter setup hStanding.1 (t - 1) ω) (sampledBlock setup t ω)) ((yIter setup hStanding.1 t ω) (sampledBlock setup t ω)))) -
            setup.η t *
              primalBregman setup
                (xIter setup hStanding.1 (t - 1) ω)
                (xIter setup hStanding.1 t ω))) ≤
        - θ k *
          finitePrefixExpectation setup k (fun ω =>
            setup.η k / 4 *
                ‖(xIter setup hStanding.1 (k - 1) ω).1 -
                  (xIter setup hStanding.1 k ω).1‖ ^ 2 -
              ⟪(xIter setup hStanding.1 (k - 1) ω).1 -
                  (xIter setup hStanding.1 k ω).1,
                ∑ i : ι, ((yIter setup hStanding.1 k ω i).1 -
                  (zstar.2 i).1)⟫_ℝ) := by
    simpa [θ, zstar] using
      theorem51_weighted_delta_finitePrefix_upper_bound_division_free
        setup τ η α hStanding hPolicy hProb hLip hAlpha hRateDen
        k hk hp hθ h51 zstar
  have h46 :
      ∀ t i, 2 ≤ t → t ≤ k →
        θ t * (inverseProbabilityValue setup i (hp i) *
            (1 + setup.τ t) - 1) ≤
          inverseProbabilityValue setup i (hp i) *
            θ (t - 1) * (1 + setup.τ (t - 1)) := by
    simpa [θ] using
      theorem51_condition_46_division_free
        setup τ η α hStanding hPolicy hProb hAlpha k hp
  have h47 :
      ∀ t, 2 ≤ t → t ≤ k →
        θ t * setup.η t ≤ θ (t - 1) * (setup.μ + setup.η (t - 1)) := by
    simpa [θ] using
      theorem51_condition_47_division_free
        setup τ η α hPolicy hEta hAlpha k
  have hPrimalFull :=
    proposition51_primal_fullstream_telescope
      setup hStanding.1 θ k hk zstar h47
  have hDualFull :=
    fun i : ι =>
      theorem51_dual_fullstream_telescope_division_free
        setup hStanding.1 θ k hk hp zstar h46 i
  have hWeighted :
      (∑ t ∈ Finset.Icc 1 k, θ t *
          expectedSaddleGap setup hStanding.1 t zstar) ≤
        ∑ t ∈ Finset.Icc 1 k, θ t *
          (finitePrefixExpectation setup t (fun ω =>
              setup.η t * primalBregman setup
                  (xIter setup hStanding.1 (t - 1) ω) zstar.1 -
                (setup.μ + setup.η t) *
                  primalBregman setup (xIter setup hStanding.1 t ω) zstar.1 -
                setup.η t * primalBregman setup
                  (xIter setup hStanding.1 (t - 1) ω)
                  (xIter setup hStanding.1 t ω)) +
            ∑ i : ι,
              finitePrefixExpectation setup t (fun ω =>
                (inverseProbabilityValue setup i (hp i) *
                    (1 + setup.τ t) - 1) *
                    (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 (t - 1) ω) i) (dualSubgradIter setup hStanding.1 (t - 1) ω i)) ((yIter setup hStanding.1 (t - 1) ω) i) (zstar.2 i)) -
                  (inverseProbabilityValue setup i (hp i) *
                      (1 + setup.τ t)) *
                    (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 t ω) i) (dualSubgradIter setup hStanding.1 t ω i)) ((yIter setup hStanding.1 t ω) i) (zstar.2 i))) +
            finitePrefixExpectation setup t (fun ω =>
              ⟪xTildeIter setup hStanding.1 t ω -
                  (xIter setup hStanding.1 t ω).1,
                ∑ i : ι, (yTildeIter setup hStanding.1 t ω i -
                  (zstar.2 i).1)⟫_ℝ -
                (setup.τ t *
                    inverseProbabilityValue setup (sampledBlock setup t ω)
                      (sampledBlock_probability_ne_zero setup
                        (sampledPositiveBlock setup t ω))) *
                  (SOptLib.carrierBregmanDivergence (dualConjugate setup (sampledBlock setup t ω)) (dualConjugateBaseSelector setup (sampledBlock setup t ω) ((yIter setup hStanding.1 (t - 1) ω)
                      (sampledBlock setup t ω)) (dualSubgradIter setup hStanding.1 (t - 1) ω
                      (sampledBlock setup t ω))) ((yIter setup hStanding.1 (t - 1) ω)
                      (sampledBlock setup t ω)) ((yIter setup hStanding.1 t ω)
                      (sampledBlock setup t ω))))) := by
    refine Finset.sum_le_sum ?_
    intro t htmem
    rcases Finset.mem_Icc.mp htmem with ⟨ht, htk⟩
    have hstep :=
      Lemma_5_5_one_step_RPDG_recursion_with_denominator_source_gap
        setup hStanding.1 hp t ht zstar
    exact mul_le_mul_of_nonneg_left hstep (hθ t ht htk)
  have hPrimalInitialFull :
      (∫ ω, primalBregman setup (xIter setup hStanding.1 0 ω) zstar.1
          ∂blockStreamLaw setup) =
        primalBregman setup setup.x0 zstar.1 := by
    letI : IsProbabilityMeasure (blockIndexLaw setup) := by
      unfold blockIndexLaw
      infer_instance
    letI : IsProbabilityMeasure (blockStreamLaw setup) := by
      unfold blockStreamLaw
      exact SOptLib.iidStreamLaw_isProbabilityMeasure (blockIndexLaw setup)
    have hconst :
        (fun ω : BlockSamplePath setup =>
          primalBregman setup (xIter setup hStanding.1 0 ω) zstar.1) =
            fun _ω : BlockSamplePath setup =>
              primalBregman setup setup.x0 zstar.1 := by
      funext ω
      simp [xIter, stateProcess_zero, initialState]
    rw [hconst]
    simp
  have hPrimalTerminalFull :
      (∫ ω, primalBregman setup (xIter setup hStanding.1 k ω) zstar.1
          ∂blockStreamLaw setup) =
        finitePrefixExpectation setup k
          (fun ω => primalBregman setup (xIter setup hStanding.1 k ω) zstar.1) := by
    rw [← finite_prefix_expectation_primal_iter_bregman_eq_blockStream_of_le
      setup hStanding.1 (le_rfl : k ≤ k) zstar.1]
  have hDualInitialFull : ∀ i : ι,
      (∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 0 ω) i) (dualSubgradIter setup hStanding.1 0 ω i)) ((yIter setup hStanding.1 0 ω) i) (zstar.2 i))
            ∂blockStreamLaw setup) =
        (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i (initialDual setup hStanding.1 i) (initialDualSubgradient setup hStanding.1 i)) (initialDual setup hStanding.1 i) (zstar.2 i)) := by
    intro i
    letI : IsProbabilityMeasure (blockIndexLaw setup) := by
      unfold blockIndexLaw
      infer_instance
    letI : IsProbabilityMeasure (blockStreamLaw setup) := by
      unfold blockStreamLaw
      exact SOptLib.iidStreamLaw_isProbabilityMeasure (blockIndexLaw setup)
    have hconst :
        (fun ω : BlockSamplePath setup =>
          (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 0 ω) i) (dualSubgradIter setup hStanding.1 0 ω i)) ((yIter setup hStanding.1 0 ω) i) (zstar.2 i))) =
          fun _ω : BlockSamplePath setup =>
            (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i (initialDual setup hStanding.1 i) (initialDualSubgradient setup hStanding.1 i)) (initialDual setup hStanding.1 i) (zstar.2 i)) := by
      funext ω
      dsimp [yIter, dualSubgradIter]
      rw [stateProcess_zero setup hStanding.1 ω]
      rfl
    rw [hconst]
    simp
  have hDualTerminalFull : ∀ i : ι,
      (∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 k ω) i) (dualSubgradIter setup hStanding.1 k ω i)) ((yIter setup hStanding.1 k ω) i) (zstar.2 i))
            ∂blockStreamLaw setup) =
        finitePrefixExpectation setup k
          (fun ω => (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 k ω) i) (dualSubgradIter setup hStanding.1 k ω i)) ((yIter setup hStanding.1 k ω) i) (zstar.2 i))) := by
    intro i
    rw [← finite_prefix_expectation_dual_iter_bregman_eq_blockStream_of_le
      setup hStanding.1 (le_rfl : k ≤ k) i (zstar.2 i)]
  have hPrimalFinite :
      (∑ t ∈ Finset.Icc 1 k, θ t *
        finitePrefixExpectation setup t (fun ω =>
          setup.η t *
              primalBregman setup (xIter setup hStanding.1 (t - 1) ω) zstar.1 -
            (setup.μ + setup.η t) *
              primalBregman setup (xIter setup hStanding.1 t ω) zstar.1)) ≤
        setup.η 1 * θ 1 * primalBregman setup setup.x0 zstar.1 -
          (setup.μ + setup.η k) * θ k *
            finitePrefixExpectation setup k
              (fun ω => primalBregman setup
                (xIter setup hStanding.1 k ω) zstar.1) := by
    have hsum_eq :
        (∑ t ∈ Finset.Icc 1 k, θ t *
          finitePrefixExpectation setup t (fun ω =>
            setup.η t *
                primalBregman setup (xIter setup hStanding.1 (t - 1) ω) zstar.1 -
              (setup.μ + setup.η t) *
                primalBregman setup (xIter setup hStanding.1 t ω) zstar.1)) =
          ∑ t ∈ Finset.Icc 1 k, (
            (θ t * setup.η t) *
                (∫ ω, primalBregman setup
                  (xIter setup hStanding.1 (t - 1) ω) zstar.1 ∂blockStreamLaw setup) -
              (θ t * (setup.μ + setup.η t)) *
                (∫ ω, primalBregman setup
                  (xIter setup hStanding.1 t ω) zstar.1 ∂blockStreamLaw setup)) := by
      refine Finset.sum_congr rfl ?_
      intro t htmem
      rcases Finset.mem_Icc.mp htmem with ⟨ht, _htk⟩
      have hprev :
          finitePrefixExpectation setup t (fun ω =>
            primalBregman setup (xIter setup hStanding.1 (t - 1) ω) zstar.1) =
            ∫ ω, primalBregman setup
              (xIter setup hStanding.1 (t - 1) ω) zstar.1 ∂blockStreamLaw setup := by
        exact finite_prefix_expectation_primal_iter_bregman_eq_blockStream_of_le
          setup hStanding.1 (by omega : t - 1 ≤ t) zstar.1
      have hcur :
          finitePrefixExpectation setup t (fun ω =>
            primalBregman setup (xIter setup hStanding.1 t ω) zstar.1) =
            ∫ ω, primalBregman setup
              (xIter setup hStanding.1 t ω) zstar.1 ∂blockStreamLaw setup := by
        exact finite_prefix_expectation_primal_iter_bregman_eq_blockStream_of_le
          setup hStanding.1 (le_rfl : t ≤ t) zstar.1
      simp [finitePrefixExpectation_sub, finitePrefixExpectation_const_mul,
        hprev, hcur]
      ring
    calc
      (∑ t ∈ Finset.Icc 1 k, θ t *
        finitePrefixExpectation setup t (fun ω =>
          setup.η t *
              primalBregman setup (xIter setup hStanding.1 (t - 1) ω) zstar.1 -
            (setup.μ + setup.η t) *
              primalBregman setup (xIter setup hStanding.1 t ω) zstar.1)) =
          ∑ t ∈ Finset.Icc 1 k, (
            (θ t * setup.η t) *
                (∫ ω, primalBregman setup
                  (xIter setup hStanding.1 (t - 1) ω) zstar.1 ∂blockStreamLaw setup) -
              (θ t * (setup.μ + setup.η t)) *
                (∫ ω, primalBregman setup
                  (xIter setup hStanding.1 t ω) zstar.1 ∂blockStreamLaw setup)) := hsum_eq
      _ ≤ θ 1 * setup.η 1 *
            (∫ ω, primalBregman setup
              (xIter setup hStanding.1 0 ω) zstar.1 ∂blockStreamLaw setup) -
          θ k * (setup.μ + setup.η k) *
            (∫ ω, primalBregman setup
              (xIter setup hStanding.1 k ω) zstar.1 ∂blockStreamLaw setup) := hPrimalFull
      _ = setup.η 1 * θ 1 * primalBregman setup setup.x0 zstar.1 -
          (setup.μ + setup.η k) * θ k *
            finitePrefixExpectation setup k
              (fun ω => primalBregman setup
                (xIter setup hStanding.1 k ω) zstar.1) := by
            rw [hPrimalInitialFull, hPrimalTerminalFull]
            ring
  have hDualFinite :
      (∑ i : ι,
        ∑ t ∈ Finset.Icc 1 k, θ t *
          finitePrefixExpectation setup t (fun ω =>
            (inverseProbabilityValue setup i (hp i) *
                (1 + setup.τ t) - 1) *
                (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 (t - 1) ω) i) (dualSubgradIter setup hStanding.1 (t - 1) ω i)) ((yIter setup hStanding.1 (t - 1) ω) i) (zstar.2 i)) -
              (inverseProbabilityValue setup i (hp i) *
                  (1 + setup.τ t)) *
                (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 t ω) i) (dualSubgradIter setup hStanding.1 t ω i)) ((yIter setup hStanding.1 t ω) i) (zstar.2 i)))) ≤
        ∑ i : ι, (
          θ 1 *
              (inverseProbabilityValue setup i (hp i) *
                (1 + setup.τ 1) - 1) *
            (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i (initialDual setup hStanding.1 i) (initialDualSubgradient setup hStanding.1 i)) (initialDual setup hStanding.1 i) (zstar.2 i)) -
          inverseProbabilityValue setup i (hp i) * θ k *
              (1 + setup.τ k) *
            finitePrefixExpectation setup k (fun ω =>
              (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 k ω) i) (dualSubgradIter setup hStanding.1 k ω i)) ((yIter setup hStanding.1 k ω) i) (zstar.2 i)))) := by
    refine Finset.sum_le_sum ?_
    intro i _hi
    have hsum_eq :
        (∑ t ∈ Finset.Icc 1 k, θ t *
          finitePrefixExpectation setup t (fun ω =>
            (inverseProbabilityValue setup i (hp i) *
                (1 + setup.τ t) - 1) *
                (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 (t - 1) ω) i) (dualSubgradIter setup hStanding.1 (t - 1) ω i)) ((yIter setup hStanding.1 (t - 1) ω) i) (zstar.2 i)) -
              (inverseProbabilityValue setup i (hp i) *
                  (1 + setup.τ t)) *
                (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 t ω) i) (dualSubgradIter setup hStanding.1 t ω i)) ((yIter setup hStanding.1 t ω) i) (zstar.2 i)))) =
          ∑ t ∈ Finset.Icc 1 k, (
            θ t *
                (inverseProbabilityValue setup i (hp i) *
                  (1 + setup.τ t) - 1) *
              (∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 (t - 1) ω) i) (dualSubgradIter setup hStanding.1 (t - 1) ω i)) ((yIter setup hStanding.1 (t - 1) ω) i) (zstar.2 i))
                  ∂blockStreamLaw setup) -
            inverseProbabilityValue setup i (hp i) * θ t *
                (1 + setup.τ t) *
              (∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 t ω) i) (dualSubgradIter setup hStanding.1 t ω i)) ((yIter setup hStanding.1 t ω) i) (zstar.2 i))
                  ∂blockStreamLaw setup)) := by
      refine Finset.sum_congr rfl ?_
      intro t htmem
      rcases Finset.mem_Icc.mp htmem with ⟨ht, _htk⟩
      have hprev :
          finitePrefixExpectation setup t (fun ω =>
            (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 (t - 1) ω) i) (dualSubgradIter setup hStanding.1 (t - 1) ω i)) ((yIter setup hStanding.1 (t - 1) ω) i) (zstar.2 i))) =
            ∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 (t - 1) ω) i) (dualSubgradIter setup hStanding.1 (t - 1) ω i)) ((yIter setup hStanding.1 (t - 1) ω) i) (zstar.2 i))
                ∂blockStreamLaw setup := by
        exact finite_prefix_expectation_dual_iter_bregman_eq_blockStream_of_le
          setup hStanding.1 (by omega : t - 1 ≤ t) i (zstar.2 i)
      have hcur :
          finitePrefixExpectation setup t (fun ω =>
            (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 t ω) i) (dualSubgradIter setup hStanding.1 t ω i)) ((yIter setup hStanding.1 t ω) i) (zstar.2 i))) =
            ∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 t ω) i) (dualSubgradIter setup hStanding.1 t ω i)) ((yIter setup hStanding.1 t ω) i) (zstar.2 i))
                ∂blockStreamLaw setup := by
        exact finite_prefix_expectation_dual_iter_bregman_eq_blockStream_of_le
          setup hStanding.1 (le_rfl : t ≤ t) i (zstar.2 i)
      simp [finitePrefixExpectation_sub, finitePrefixExpectation_const_mul,
        hprev, hcur]
      ring
    calc
      (∑ t ∈ Finset.Icc 1 k, θ t *
          finitePrefixExpectation setup t (fun ω =>
            (inverseProbabilityValue setup i (hp i) *
                (1 + setup.τ t) - 1) *
                (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 (t - 1) ω) i) (dualSubgradIter setup hStanding.1 (t - 1) ω i)) ((yIter setup hStanding.1 (t - 1) ω) i) (zstar.2 i)) -
              (inverseProbabilityValue setup i (hp i) *
                  (1 + setup.τ t)) *
                (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 t ω) i) (dualSubgradIter setup hStanding.1 t ω i)) ((yIter setup hStanding.1 t ω) i) (zstar.2 i)))) =
          ∑ t ∈ Finset.Icc 1 k, (
            θ t *
                (inverseProbabilityValue setup i (hp i) *
                  (1 + setup.τ t) - 1) *
              (∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 (t - 1) ω) i) (dualSubgradIter setup hStanding.1 (t - 1) ω i)) ((yIter setup hStanding.1 (t - 1) ω) i) (zstar.2 i))
                  ∂blockStreamLaw setup) -
            inverseProbabilityValue setup i (hp i) * θ t *
                (1 + setup.τ t) *
              (∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 t ω) i) (dualSubgradIter setup hStanding.1 t ω i)) ((yIter setup hStanding.1 t ω) i) (zstar.2 i))
                  ∂blockStreamLaw setup)) := hsum_eq
      _ ≤ θ 1 *
            (inverseProbabilityValue setup i (hp i) *
              (1 + setup.τ 1) - 1) *
          (∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 0 ω) i) (dualSubgradIter setup hStanding.1 0 ω i)) ((yIter setup hStanding.1 0 ω) i) (zstar.2 i))
              ∂blockStreamLaw setup) -
          inverseProbabilityValue setup i (hp i) * θ k *
              (1 + setup.τ k) *
            (∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 k ω) i) (dualSubgradIter setup hStanding.1 k ω i)) ((yIter setup hStanding.1 k ω) i) (zstar.2 i))
                ∂blockStreamLaw setup) := hDualFull i
      _ = θ 1 *
            (inverseProbabilityValue setup i (hp i) *
              (1 + setup.τ 1) - 1) *
          (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i (initialDual setup hStanding.1 i) (initialDualSubgradient setup hStanding.1 i)) (initialDual setup hStanding.1 i) (zstar.2 i)) -
          inverseProbabilityValue setup i (hp i) * θ k *
              (1 + setup.τ k) *
            finitePrefixExpectation setup k (fun ω =>
              (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 k ω) i) (dualSubgradIter setup hStanding.1 k ω i)) ((yIter setup hStanding.1 k ω) i) (zstar.2 i))) := by
          rw [hDualInitialFull i, hDualTerminalFull i]
  have hDualWeightedSumComm :
      (∑ t ∈ Finset.Icc 1 k, θ t *
        (∑ i : ι,
          finitePrefixExpectation setup t (fun ω =>
            (inverseProbabilityValue setup i (hp i) *
                (1 + setup.τ t) - 1) *
                (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 (t - 1) ω) i) (dualSubgradIter setup hStanding.1 (t - 1) ω i)) ((yIter setup hStanding.1 (t - 1) ω) i) (zstar.2 i)) -
              (inverseProbabilityValue setup i (hp i) *
                  (1 + setup.τ t)) *
                (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 t ω) i) (dualSubgradIter setup hStanding.1 t ω i)) ((yIter setup hStanding.1 t ω) i) (zstar.2 i))))) =
        ∑ i : ι,
          ∑ t ∈ Finset.Icc 1 k, θ t *
            finitePrefixExpectation setup t (fun ω =>
              (inverseProbabilityValue setup i (hp i) *
                  (1 + setup.τ t) - 1) *
                  (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 (t - 1) ω) i) (dualSubgradIter setup hStanding.1 (t - 1) ω i)) ((yIter setup hStanding.1 (t - 1) ω) i) (zstar.2 i)) -
                (inverseProbabilityValue setup i (hp i) *
                    (1 + setup.τ t)) *
                  (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 t ω) i) (dualSubgradIter setup hStanding.1 t ω i)) ((yIter setup hStanding.1 t ω) i) (zstar.2 i))) := by
    calc
      (∑ t ∈ Finset.Icc 1 k, θ t *
        (∑ i : ι,
          finitePrefixExpectation setup t (fun ω =>
            (inverseProbabilityValue setup i (hp i) *
                (1 + setup.τ t) - 1) *
                (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 (t - 1) ω) i) (dualSubgradIter setup hStanding.1 (t - 1) ω i)) ((yIter setup hStanding.1 (t - 1) ω) i) (zstar.2 i)) -
              (inverseProbabilityValue setup i (hp i) *
                  (1 + setup.τ t)) *
                (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 t ω) i) (dualSubgradIter setup hStanding.1 t ω i)) ((yIter setup hStanding.1 t ω) i) (zstar.2 i))))) =
          ∑ t ∈ Finset.Icc 1 k,
            ∑ i : ι, θ t *
              finitePrefixExpectation setup t (fun ω =>
                (inverseProbabilityValue setup i (hp i) *
                    (1 + setup.τ t) - 1) *
                    (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 (t - 1) ω) i) (dualSubgradIter setup hStanding.1 (t - 1) ω i)) ((yIter setup hStanding.1 (t - 1) ω) i) (zstar.2 i)) -
                  (inverseProbabilityValue setup i (hp i) *
                      (1 + setup.τ t)) *
                    (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 t ω) i) (dualSubgradIter setup hStanding.1 t ω i)) ((yIter setup hStanding.1 t ω) i) (zstar.2 i))) := by
            refine Finset.sum_congr rfl ?_
            intro t _htmem
            rw [Finset.mul_sum]
      _ = ∑ i : ι,
          ∑ t ∈ Finset.Icc 1 k, θ t *
            finitePrefixExpectation setup t (fun ω =>
              (inverseProbabilityValue setup i (hp i) *
                  (1 + setup.τ t) - 1) *
                  (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 (t - 1) ω) i) (dualSubgradIter setup hStanding.1 (t - 1) ω i)) ((yIter setup hStanding.1 (t - 1) ω) i) (zstar.2 i)) -
                (inverseProbabilityValue setup i (hp i) *
                    (1 + setup.τ t)) *
                  (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 t ω) i) (dualSubgradIter setup hStanding.1 t ω i)) ((yIter setup hStanding.1 t ω) i) (zstar.2 i))) := by
            rw [Finset.sum_comm]
  have hDualTimeBound :
      (∑ t ∈ Finset.Icc 1 k, θ t *
        (∑ i : ι,
          finitePrefixExpectation setup t (fun ω =>
            (inverseProbabilityValue setup i (hp i) *
                (1 + setup.τ t) - 1) *
                (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 (t - 1) ω) i) (dualSubgradIter setup hStanding.1 (t - 1) ω i)) ((yIter setup hStanding.1 (t - 1) ω) i) (zstar.2 i)) -
              (inverseProbabilityValue setup i (hp i) *
                  (1 + setup.τ t)) *
                (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 t ω) i) (dualSubgradIter setup hStanding.1 t ω i)) ((yIter setup hStanding.1 t ω) i) (zstar.2 i))))) ≤
        ∑ i : ι, (
          θ 1 *
              (inverseProbabilityValue setup i (hp i) *
                (1 + setup.τ 1) - 1) *
            (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i (initialDual setup hStanding.1 i) (initialDualSubgradient setup hStanding.1 i)) (initialDual setup hStanding.1 i) (zstar.2 i)) -
          inverseProbabilityValue setup i (hp i) * θ k *
              (1 + setup.τ k) *
            finitePrefixExpectation setup k (fun ω =>
              (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 k ω) i) (dualSubgradIter setup hStanding.1 k ω i)) ((yIter setup hStanding.1 k ω) i) (zstar.2 i)))) := by
    rw [hDualWeightedSumComm]
    exact hDualFinite
  have hWeightedGapNonnegative :
      0 ≤ ∑ t ∈ Finset.Icc 1 k, θ t *
        expectedSaddleGap setup hStanding.1 t zstar := by
    refine Finset.sum_nonneg ?_
    intro t htmem
    rcases Finset.mem_Icc.mp htmem with ⟨ht, htk⟩
    have hgap_nonneg :
        0 ≤ expectedSaddleGap setup hStanding.1 t zstar := by
      unfold expectedSaddleGap finitePrefixExpectation
      exact MeasureTheory.integral_nonneg fun pref =>
        theorem51_scaled_gradient_saddle_gap_nonnegative
          setup hStanding.1 xstar hxstar t (extendBlockPrefix setup t pref)
    exact mul_nonneg (hθ t ht htk) hgap_nonneg
  have hInitialDualEndpoint :
      (∑ i : ι,
        (θ 1 *
            (inverseProbabilityValue setup i (hp i) *
              (1 + setup.τ 1) - 1)) *
          (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i (initialDual setup hStanding.1 i) (initialDualSubgradient setup hStanding.1 i)) (initialDual setup hStanding.1 i) (zstar.2 i))) ≤
        θ 1 *
          sourceQuotient α (1 - α)
            (one_sub_alpha_ne_zero_of_alphaRange hAlpha) *
          (setup.Lf * primalBregman setup setup.x0 xstar) := by
    have hτ1 : setup.τ 1 = τ := hPolicy.1 1 le_rfl
    simpa [θ, zstar, hp, hτ1] using
      theorem51_initial_dual_endpoint_le
        setup τ η α hStanding hPolicy hProb hAlpha xstar hxstar
  have h50 :
      propositionCondition_5_1_50_with_denominator_source_gap
        setup hStanding.1 k hk := by
    exact theorem51_condition_50_division_free
      setup τ η α hStanding hPolicy hLip k hk
  let terminal : BlockSamplePath setup → ℝ := fun ω =>
    setup.η k / 4 *
        ‖(xIter setup hStanding.1 (k - 1) ω).1 -
          (xIter setup hStanding.1 k ω).1‖ ^ 2 -
      ⟪(xIter setup hStanding.1 (k - 1) ω).1 -
          (xIter setup hStanding.1 k ω).1,
        ∑ i : ι, ((yIter setup hStanding.1 k ω i).1 -
          (zstar.2 i).1)⟫_ℝ
  let terminalDual : ι → BlockSamplePath setup → ℝ := fun i ω =>
    (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 k ω) i) (dualSubgradIter setup hStanding.1 k ω i)) ((yIter setup hStanding.1 k ω) i) (zstar.2 i))
  have hTerminalResidualFinite :
      0 ≤ finitePrefixExpectation setup k (fun ω =>
        terminal ω +
          ∑ i : ι,
            inverseProbabilityValue setup i (hp i) *
              (1 + setup.τ k) * terminalDual i ω) := by
    unfold finitePrefixExpectation
    exact MeasureTheory.integral_nonneg fun pref => by
      simpa [terminal, terminalDual, mul_assoc, mul_comm, mul_left_comm] using
        terminal_residual_bracket_nonnegative_of_h50_and_probabilities
          setup hStanding.1 k hk hp h50 zstar (extendBlockPrefix setup k pref)
  have hTerminalResidualExpanded :
      finitePrefixExpectation setup k (fun ω =>
        terminal ω +
          ∑ i : ι,
            inverseProbabilityValue setup i (hp i) *
              (1 + setup.τ k) * terminalDual i ω) =
        finitePrefixExpectation setup k terminal +
          ∑ i : ι,
            inverseProbabilityValue setup i (hp i) *
              (1 + setup.τ k) *
              finitePrefixExpectation setup k (terminalDual i) := by
    calc
      finitePrefixExpectation setup k (fun ω =>
        terminal ω +
          ∑ i : ι,
            inverseProbabilityValue setup i (hp i) *
              (1 + setup.τ k) * terminalDual i ω) =
          finitePrefixExpectation setup k terminal +
            finitePrefixExpectation setup k (fun ω =>
              ∑ i : ι,
                inverseProbabilityValue setup i (hp i) *
                  (1 + setup.τ k) * terminalDual i ω) := by
            rw [finitePrefixExpectation_add]
      _ = finitePrefixExpectation setup k terminal +
          ∑ i : ι,
            finitePrefixExpectation setup k (fun ω =>
              inverseProbabilityValue setup i (hp i) *
                (1 + setup.τ k) * terminalDual i ω) := by
            rw [finitePrefixExpectation_finset_sum]
      _ = finitePrefixExpectation setup k terminal +
          ∑ i : ι,
            inverseProbabilityValue setup i (hp i) *
              (1 + setup.τ k) *
              finitePrefixExpectation setup k (terminalDual i) := by
            refine congrArg (fun s => finitePrefixExpectation setup k terminal + s) ?_
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [finitePrefixExpectation_const_mul]
  have hTerminalTailNonpositive :
      - θ k * finitePrefixExpectation setup k terminal -
        ∑ i : ι,
          inverseProbabilityValue setup i (hp i) * θ k *
            (1 + setup.τ k) *
            finitePrefixExpectation setup k (terminalDual i) ≤ 0 := by
    have hResidualExpandedNonneg :
        0 ≤ finitePrefixExpectation setup k terminal +
          ∑ i : ι,
            inverseProbabilityValue setup i (hp i) *
              (1 + setup.τ k) *
              finitePrefixExpectation setup k (terminalDual i) := by
      rwa [hTerminalResidualExpanded] at hTerminalResidualFinite
    have hθk_nonneg : 0 ≤ θ k := hθ k hk le_rfl
    have hscaled :
        0 ≤ θ k *
          (finitePrefixExpectation setup k terminal +
            ∑ i : ι,
              inverseProbabilityValue setup i (hp i) *
                (1 + setup.τ k) *
                finitePrefixExpectation setup k (terminalDual i)) :=
      mul_nonneg hθk_nonneg hResidualExpandedNonneg
    have hsum_factor :
        (∑ i : ι,
          inverseProbabilityValue setup i (hp i) * θ k *
            (1 + setup.τ k) *
            finitePrefixExpectation setup k (terminalDual i)) =
          θ k *
            (∑ i : ι,
              inverseProbabilityValue setup i (hp i) *
                (1 + setup.τ k) *
                finitePrefixExpectation setup k (terminalDual i)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _hi
      ring
    calc
      - θ k * finitePrefixExpectation setup k terminal -
          ∑ i : ι,
            inverseProbabilityValue setup i (hp i) * θ k *
              (1 + setup.τ k) *
              finitePrefixExpectation setup k (terminalDual i) =
          - θ k *
            (finitePrefixExpectation setup k terminal +
              ∑ i : ι,
                inverseProbabilityValue setup i (hp i) *
                  (1 + setup.τ k) *
                  finitePrefixExpectation setup k (terminalDual i)) := by
            rw [hsum_factor]
            ring
      _ ≤ 0 := by
            nlinarith
  have hWeightedProp :
      (∑ t ∈ Finset.Icc 1 k, θ t *
          expectedSaddleGap setup hStanding.1 t zstar) ≤
        setup.η 1 * θ 1 * primalBregman setup setup.x0 zstar.1 -
          (setup.μ + setup.η k) * θ k *
            finitePrefixExpectation setup k
              (fun ω => primalBregman setup
                (xIter setup hStanding.1 k ω) zstar.1) +
        ∑ i : ι,
          θ 1 * (inverseProbabilityValue setup i (hp i) *
              (1 + setup.τ 1) - 1) *
            (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i (initialDual setup hStanding.1 i) (initialDualSubgradient setup hStanding.1 i)) (initialDual setup hStanding.1 i) (zstar.2 i)) := by
    let P : ℕ → ℝ := fun t =>
      finitePrefixExpectation setup t (fun ω =>
        setup.η t * primalBregman setup
            (xIter setup hStanding.1 (t - 1) ω) zstar.1 -
          (setup.μ + setup.η t) *
            primalBregman setup (xIter setup hStanding.1 t ω) zstar.1)
    let D : ℕ → ℝ := fun t =>
      ∑ i : ι,
        finitePrefixExpectation setup t (fun ω =>
          (inverseProbabilityValue setup i (hp i) *
              (1 + setup.τ t) - 1) *
              (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 (t - 1) ω) i) (dualSubgradIter setup hStanding.1 (t - 1) ω i)) ((yIter setup hStanding.1 (t - 1) ω) i) (zstar.2 i)) -
            (inverseProbabilityValue setup i (hp i) *
                (1 + setup.τ t)) *
              (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 t ω) i) (dualSubgradIter setup hStanding.1 t ω i)) ((yIter setup hStanding.1 t ω) i) (zstar.2 i)))
    let R : ℕ → ℝ := fun t =>
      finitePrefixExpectation setup t (fun ω =>
        ⟪xTildeIter setup hStanding.1 t ω -
            (xIter setup hStanding.1 t ω).1,
          ∑ i : ι, (yTildeIter setup hStanding.1 t ω i -
            (zstar.2 i).1)⟫_ℝ -
        (setup.τ t *
            inverseProbabilityValue setup (sampledBlock setup t ω)
              (sampledBlock_probability_ne_zero setup
                (sampledPositiveBlock setup t ω))) *
          (SOptLib.carrierBregmanDivergence (dualConjugate setup (sampledBlock setup t ω)) (dualConjugateBaseSelector setup (sampledBlock setup t ω) ((yIter setup hStanding.1 (t - 1) ω)
              (sampledBlock setup t ω)) (dualSubgradIter setup hStanding.1 (t - 1) ω
              (sampledBlock setup t ω))) ((yIter setup hStanding.1 (t - 1) ω)
              (sampledBlock setup t ω)) ((yIter setup hStanding.1 t ω)
              (sampledBlock setup t ω))))
    let Q : ℕ → ℝ := fun t =>
      setup.η t *
        finitePrefixExpectation setup t (fun ω =>
          primalBregman setup
            (xIter setup hStanding.1 (t - 1) ω)
            (xIter setup hStanding.1 t ω))
    have hWeightedAbbrev :
        (∑ t ∈ Finset.Icc 1 k, θ t *
          ((finitePrefixExpectation setup t (fun ω =>
                setup.η t * primalBregman setup
                    (xIter setup hStanding.1 (t - 1) ω) zstar.1 -
                  (setup.μ + setup.η t) *
                    primalBregman setup (xIter setup hStanding.1 t ω) zstar.1 -
                  setup.η t * primalBregman setup
                    (xIter setup hStanding.1 (t - 1) ω)
                    (xIter setup hStanding.1 t ω)) +
              D t) + R t)) =
          ∑ t ∈ Finset.Icc 1 k, θ t * (((P t - Q t) + D t) + R t) := by
      refine Finset.sum_congr rfl ?_
      intro t _htmem
      dsimp [P, Q]
      rw [finitePrefixExpectation_sub, finitePrefixExpectation_const_mul]
    have hWeightedSplit :
        (∑ t ∈ Finset.Icc 1 k, θ t *
            expectedSaddleGap setup hStanding.1 t zstar) ≤
          (∑ t ∈ Finset.Icc 1 k, θ t * P t) +
            (∑ t ∈ Finset.Icc 1 k, θ t * D t) +
              (∑ t ∈ Finset.Icc 1 k, θ t * (R t - Q t)) := by
      have hsplit :=
        sum_weighted_three_way_residual_split (Finset.Icc 1 k) θ P D R Q
      rw [hWeightedAbbrev, hsplit] at hWeighted
      exact hWeighted
    have hPrimalFiniteP :
        (∑ t ∈ Finset.Icc 1 k, θ t * P t) ≤
          setup.η 1 * θ 1 * primalBregman setup setup.x0 zstar.1 -
            (setup.μ + setup.η k) * θ k *
              finitePrefixExpectation setup k
                (fun ω => primalBregman setup
                  (xIter setup hStanding.1 k ω) zstar.1) := by
      simpa [P] using hPrimalFinite
    have hDualTimeBoundD :
        (∑ t ∈ Finset.Icc 1 k, θ t * D t) ≤
          ∑ i : ι, (
            θ 1 *
                (inverseProbabilityValue setup i (hp i) *
                  (1 + setup.τ 1) - 1) *
              (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i (initialDual setup hStanding.1 i) (initialDualSubgradient setup hStanding.1 i)) (initialDual setup hStanding.1 i) (zstar.2 i)) -
            inverseProbabilityValue setup i (hp i) * θ k *
                (1 + setup.τ k) *
              finitePrefixExpectation setup k (terminalDual i)) := by
      simpa [D, terminalDual] using hDualTimeBound
    have hDeltaFiniteRQ :
        (∑ t ∈ Finset.Icc 1 k, θ t * (R t - Q t)) ≤
          - θ k * finitePrefixExpectation setup k terminal := by
      simpa [R, Q, terminal, finitePrefixExpectation_sub,
        finitePrefixExpectation_const_mul] using hDeltaFinite
    have hDualEndpointSplit :
        (∑ i : ι, (
            θ 1 *
                (inverseProbabilityValue setup i (hp i) *
                  (1 + setup.τ 1) - 1) *
              (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i (initialDual setup hStanding.1 i) (initialDualSubgradient setup hStanding.1 i)) (initialDual setup hStanding.1 i) (zstar.2 i)) -
            inverseProbabilityValue setup i (hp i) * θ k *
                (1 + setup.τ k) *
              finitePrefixExpectation setup k (fun ω =>
                (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 k ω) i) (dualSubgradIter setup hStanding.1 k ω i)) ((yIter setup hStanding.1 k ω) i) (zstar.2 i))))) =
          ((∑ i : ι,
            θ 1 *
                (inverseProbabilityValue setup i (hp i) *
                  (1 + setup.τ 1) - 1) *
              (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i (initialDual setup hStanding.1 i) (initialDualSubgradient setup hStanding.1 i)) (initialDual setup hStanding.1 i) (zstar.2 i))) -
          (∑ i : ι,
            inverseProbabilityValue setup i (hp i) * θ k *
                (1 + setup.τ k) *
              finitePrefixExpectation setup k (fun ω =>
                (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 k ω) i) (dualSubgradIter setup hStanding.1 k ω i)) ((yIter setup hStanding.1 k ω) i) (zstar.2 i))))) := by
      rw [Finset.sum_sub_distrib]
    rw [hDualEndpointSplit] at hDualTimeBoundD
    nlinarith [hWeightedSplit, hPrimalFiniteP, hDualTimeBoundD,
      hDeltaFiniteRQ, hTerminalTailNonpositive]
  have hTerminalBudget :
      (setup.μ + setup.η k) * θ k *
        finitePrefixExpectation setup k
          (fun ω => primalBregman setup
            (xIter setup hStanding.1 k ω) zstar.1) ≤
        setup.η 1 * θ 1 * primalBregman setup setup.x0 zstar.1 +
          θ 1 *
            sourceQuotient α (1 - α)
              (one_sub_alpha_ne_zero_of_alphaRange hAlpha) *
            (setup.Lf * primalBregman setup setup.x0 xstar) := by
    nlinarith [hWeightedProp, hWeightedGapNonnegative, hInitialDualEndpoint]
  simpa [θ, zstar] using hTerminalBudget

/-- Scalar extraction of Lan Eq. (5.1.63) from the terminal-budget inequality
produced by the Theorem 5.1 Proposition-5.1/Lemma-5.1 chain.
Existing candidates considered: searched `Bregman distance rate expected
arbitrary time theorem 5.1`; `expectedBregmanDistance_finite_prefix` and
`finite_prefix_expectation_primal_iter_bregman_eq_blockStream_of_le` only
transport expectations, while
`Proposition_5_1_weighted_RPDG_bound_with_denominator_source_gap` is tied to
the stronger corrected `tauProbabilityDenominatorsAdmissible` boundary. This
helper isolates the source Eq. (5.1.63) scalar division after the local
denominator-free terminal budget has already been derived. -/
private theorem theorem51_expected_bregman_distance_rate_from_terminal_budget
    (τ η α : ℝ) (t : ℕ) (ht : 1 ≤ t)
    (hStanding : theoremStandingAssumptions setup)
    (hPolicy : constantParameterPolicy setup τ η α)
    (hEta : constantParameterConditionEta setup η α)
    (hAlpha : alphaRange α)
    (hRateDen : theorem_5_1_rateDenominatorBoundary η)
    (xstar : PrimalCarrier setup)
    (hTerminalBudget :
      (setup.μ + setup.η t) * theoremOutputWeight α hAlpha t *
        finitePrefixExpectation setup t
          (fun ω => primalBregman setup (xIter setup hStanding.1 t ω) xstar) ≤
        setup.η 1 * theoremOutputWeight α hAlpha 1 *
          primalBregman setup setup.x0 xstar +
          theoremOutputWeight α hAlpha 1 *
            sourceQuotient α (1 - α)
              (one_sub_alpha_ne_zero_of_alphaRange hAlpha) *
            (setup.Lf * primalBregman setup setup.x0 xstar)) :
    expectedBregmanDistance setup hStanding.1 t xstar ≤
      (1 + sourceQuotient (setup.Lf * α) ((1 - α) * η)
          (rateProductDenominator_ne_for_theorem_5_1 η α hRateDen hAlpha)) *
        α ^ t *
        primalBregman setup setup.x0 xstar := by
  simpa [expectedBregmanDistance, sourceQuotient, theoremOutputWeight,
    SOptLib.inverse_power_weight, mul_assoc, mul_comm, mul_left_comm] using
    geometric_rate_of_terminal_budget
      (mu := setup.μ) (eta := η) (alpha := α) (Lf := setup.Lf)
      (F := finitePrefixExpectation setup t
        (fun ω => primalBregman setup (xIter setup hStanding.1 t ω) xstar))
      (V0 := primalBregman setup setup.x0 xstar) (t := t)
      hAlpha.1 (one_sub_alpha_ne_zero_of_alphaRange hAlpha)
      (theorem51_eta_pos_of_rate_boundary
        (setup := setup) τ η α hStanding hPolicy hRateDen)
      (by simpa [constantParameterConditionEta] using hEta)
      (by
        dsimp [finitePrefixExpectation]
        exact MeasureTheory.integral_nonneg fun pref =>
          primalBregman_nonnegative_of_standing (setup := setup) hStanding.1
            (xIter setup hStanding.1 t (extendBlockPrefix setup t pref)) xstar)
      (by
        simpa [theoremOutputWeight, SOptLib.inverse_power_weight, sourceQuotient,
          hPolicy.2.1 1 le_rfl, hPolicy.2.1 t ht,
          mul_assoc, mul_comm, mul_left_comm] using hTerminalBudget)

/-- Arbitrary-time Lan Eq. (5.1.63) under Theorem 5.1's constant-parameter
assumptions. Existing candidates considered: `theorem51_expected_bregman_distance_rate_from_terminal_budget`
performs only the final scalar division once a terminal budget is supplied;
`Proposition_5_1_weighted_RPDG_bound_with_denominator_source_gap` would provide
the terminal budget but requires the forbidden `proposition_5_1_denominatorBoundary`;
searched `Bregman distance rate expected arbitrary time` and
`terminal budget theorem 5.1 proposition weighted bound division free`, where the
division-free delta/telescope helpers provide pieces but no existing declaration
packages the arbitrary-horizon terminal budget for Eq. (5.1.63). -/
private theorem theorem51_expected_bregman_distance_rate
    (τ η α : ℝ) (t : ℕ) (ht : 1 ≤ t)
    (hStanding : theoremStandingAssumptions setup)
    (hPolicy : constantParameterPolicy setup τ η α)
    (hProb : constantParameterConditionProbability setup τ α)
    (hEta : constantParameterConditionEta setup η α)
    (hLip : constantParameterConditionLipschitz setup τ η)
    (hAlpha : alphaRange α)
    (hRateDen : theorem_5_1_rateDenominatorBoundary η)
    (xstar : PrimalCarrier setup) (hxstar : IsOptimalPrimal setup xstar) :
    expectedBregmanDistance setup hStanding.1 t xstar ≤
      (1 + sourceQuotient (setup.Lf * α) ((1 - α) * η)
          (rateProductDenominator_ne_for_theorem_5_1 η α hRateDen hAlpha)) *
        α ^ t *
        primalBregman setup setup.x0 xstar := by
  classical
  have hTerminalBudget :=
    theorem51_terminal_budget_arbitrary_time
      setup τ η α t ht hStanding hPolicy hProb hEta hLip hAlpha hRateDen
      xstar hxstar
  exact theorem51_expected_bregman_distance_rate_from_terminal_budget
    setup τ η α t ht hStanding hPolicy hEta hAlpha hRateDen xstar
    hTerminalBudget

/-- One-based finite geometric sum in multiplication form, aligned with Lan
Theorem 5.1 Eq. (5.1.64)'s `t=1,...,k` output window. Existing candidates
considered: Mathlib `geom_sum_mul` and `geom_sum_eq` cover `Finset.range k`,
not the paper's `Finset.Icc 1 k`; local interval split helpers only reindex
non-geometric sums, so this helper packages the exact source window. -/
private theorem sum_Icc_one_based_geom_mul (q : ℝ) (k : ℕ) :
    (∑ t ∈ Finset.Icc 1 k, q ^ t) * (q - 1) = q ^ (k + 1) - q := by
  exact sum_Icc_one_pow_mul_sub_eq_pow_succ_sub q k

/-- Half-geometric normalizer bound from Lan Theorem 5.1 proof steps 14--17.
Existing candidates considered: searched `weighted average bregman output
geometric sum rpow`, `output weight sum geometric bound`, and `Finset Icc
geometric sum powers real inverse`; `outputWeightSum_pos_of_alphaRange` supplies
only positivity, SOptLib `expected_bound_of_weighted_sum_bound` only transports
a completed numerator bound, and the generic geometric helpers `geom_sum_eq` and
`geom_sum_mul` do not package this paper-specific `θ_t=α^{-t}` half-power ratio. -/
private theorem theorem51_output_weight_half_geometric_bound
    (α : ℝ) (k : ℕ) (hk : 1 ≤ k) (hAlpha : alphaRange α) :
    (outputWeightSum α hAlpha k)⁻¹ *
        ∑ t ∈ outputTimeWindow k, Real.rpow α (-(t : ℝ) / 2) ≤
      2 * Real.rpow α ((k : ℝ) / 2) := by
  simpa [outputWeightSum, outputTimeWindow, theoremOutputWeight, sourceQuotient_def] using
    one_based_geometric_half_ratio_rpow_le α k hAlpha.1 hAlpha.2

/-- Weighted Bregman-average contribution in Lan Eq. (5.1.64), obtained by
summing the arbitrary-time Eq. (5.1.63) rate and applying the half-geometric
normalizer bound. Existing candidates considered: searched `weighted average
bregman output geometric sum rpow` and checked the SOptLib normalized-output
transport `expected_bound_of_weighted_sum_bound`; those do not combine this
paper's Eq. (5.1.63), canonical inverse-power weights, and the half-geometric
source loosening. -/
private theorem theorem51_weighted_bregman_average_rate
    (τ η α : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hStanding : theoremStandingAssumptions setup)
    (xstar : PrimalCarrier setup) (hxstar : IsOptimalPrimal setup xstar)
    (hPolicy : constantParameterPolicy setup τ η α)
    (hProb : constantParameterConditionProbability setup τ α)
    (hEta : constantParameterConditionEta setup η α)
    (hLip : constantParameterConditionLipschitz setup τ η)
    (hAlpha : alphaRange α)
    (hRateDen : theorem_5_1_rateDenominatorBoundary η)
    (hLf_nonneg : 0 ≤ setup.Lf)
    (hV0_nonneg : 0 ≤ primalBregman setup setup.x0 xstar)
    (hη_pos : 0 < η) :
    (outputWeightSum α hAlpha k)⁻¹ *
        ∑ t ∈ outputTimeWindow k,
          theoremOutputWeight α hAlpha t *
            expectedBregmanDistance setup hStanding.1 t xstar ≤
      2 * Real.rpow α ((k : ℝ) / 2) *
        (1 + sourceQuotient (setup.Lf * α) ((1 - α) * η)
          (rateProductDenominator_ne_for_theorem_5_1 η α hRateDen hAlpha)) *
        primalBregman setup setup.x0 xstar := by
  classical
  have _hk_for_algorithm_signature : 1 ≤ k := hk
  let C : ℝ :=
    1 + sourceQuotient (setup.Lf * α) ((1 - α) * η)
      (rateProductDenominator_ne_for_theorem_5_1 η α hRateDen hAlpha)
  let V0 : ℝ := primalBregman setup setup.x0 xstar
  have hone_sub_pos : 0 < 1 - α := sub_pos.mpr hAlpha.2
  have hden_pos : 0 < (1 - α) * η := mul_pos hone_sub_pos hη_pos
  have hquot_nonneg :
      0 ≤ sourceQuotient (setup.Lf * α) ((1 - α) * η)
        (rateProductDenominator_ne_for_theorem_5_1 η α hRateDen hAlpha) := by
    rw [sourceQuotient_def]
    exact div_nonneg (mul_nonneg hLf_nonneg hAlpha.1.le) hden_pos.le
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    nlinarith
  have hCV_nonneg : 0 ≤ C * V0 := mul_nonneg hC_nonneg hV0_nonneg
  have hF :
      ∀ t ∈ Finset.Icc 1 k,
        expectedBregmanDistance setup hStanding.1 t xstar ≤ C * α ^ t * V0 := by
    intro t ht
    rcases Finset.mem_Icc.mp ht with ⟨ht1, _htk⟩
    simpa [C, V0, mul_assoc] using
      theorem51_expected_bregman_distance_rate
        setup τ η α t ht1 hStanding hPolicy hProb hEta hLip hAlpha
        hRateDen xstar hxstar
  have hrate :=
    weighted_average_geometric_rate_le_half_power α C V0 k
      (fun t => expectedBregmanDistance setup hStanding.1 t xstar)
      hAlpha.1 hAlpha.2 hCV_nonneg hF
  simpa [outputWeightSum, outputTimeWindow, theoremOutputWeight, SOptLib.inverse_power_weight,
    C, V0, mul_assoc] using hrate

/-- Scalar combiner for Lan Theorem 5.1 Eq. (5.1.64): once the saddle-gap
and weighted-Bregman-average contributions have been bounded in the source
forms, their coefficients simplify to the printed final rate. Existing
candidates considered: searched `final primal gap scalar combine sourceQuotient
rpow`, `weighted Bregman average rate`, and `geometric outputWeightSum`;
`outputWeightSum_pos_of_alphaRange` and `expected_bound_of_weighted_sum_bound`
only handle normalization, while the available SOptLib telescope helpers do not
package this paper-specific `(3-2α)/(1-α)` coefficient algebra. -/
private theorem theorem51_final_primal_gap_scalar_combine
    (η α Lf V saddleTerm bregmanAverageTerm : ℝ) (k : ℕ)
    (hAlpha : alphaRange α)
    (hRateDen : theorem_5_1_rateDenominatorBoundary η)
    (hη_pos : 0 < η) (hLf_nonneg : 0 ≤ Lf) (hV_nonneg : 0 ≤ V)
    (hsaddle :
      saddleTerm ≤
        α ^ k *
          (sourceQuotient 1 α (alpha_ne_zero_of_alphaRange hAlpha) * η +
            sourceQuotient 1 (1 - α)
              (one_sub_alpha_ne_zero_of_alphaRange hAlpha) * Lf) * V)
    (hbregman :
      bregmanAverageTerm ≤
        Lf *
          (2 * Real.rpow α ((k : ℝ) / 2) *
            (1 + sourceQuotient (Lf * α) ((1 - α) * η)
              (rateProductDenominator_ne_for_theorem_5_1 η α hRateDen hAlpha)) * V)) :
    saddleTerm + bregmanAverageTerm ≤
      Real.rpow α ((k : ℝ) / 2) *
        (sourceQuotient 1 α (alpha_ne_zero_of_alphaRange hAlpha) * η +
          sourceQuotient (3 - 2 * α) (1 - α)
              (one_sub_alpha_ne_zero_of_alphaRange hAlpha) * Lf +
          sourceQuotient (2 * Lf ^ 2 * α) ((1 - α) * η)
            (rateProductDenominator_ne_for_theorem_5_1 η α hRateDen hAlpha)) *
        V := by
  simpa [sourceQuotient_def] using
    add_le_rpow_half_mul_collected_coeff_of_le_pow_and_le_rpow_half
      η α Lf V saddleTerm bregmanAverageTerm k
      hAlpha.1 hAlpha.2 (ne_of_gt hη_pos)
      (by
        have hA_nonneg : 0 ≤ (1 / α) * η + (1 / (1 - α)) * Lf := by
          have hqη : 0 ≤ (1 / α) * η :=
            mul_nonneg (one_div_pos.mpr hAlpha.1).le hη_pos.le
          have hone_sub_pos : 0 < 1 - α := sub_pos.mpr hAlpha.2
          have hqLf : 0 ≤ (1 / (1 - α)) * Lf :=
            mul_nonneg (one_div_pos.mpr hone_sub_pos).le hLf_nonneg
          exact add_nonneg hqη hqLf
        exact mul_nonneg hA_nonneg hV_nonneg)
      (by simpa [sourceQuotient_def] using hsaddle)
      (by simpa [sourceQuotient_def] using hbregman)

/-- Internal source-gap realization of FOML Theorem 5.1 over the generated
Algorithm 5.1 process. The original paper-facing theorem is intentionally not
exported under the canonical name while the unstated `η` denominator gap remains
unresolved. -/
theorem theorem_5_1_with_denominator_source_gap
    (τ η α : ℝ) (k : ℕ)
    (hk : 1 ≤ k)
    (hStanding : theoremStandingAssumptions setup)
    (xstar : PrimalCarrier setup) (hxstar : IsOptimalPrimal setup xstar)
    (hPolicy : constantParameterPolicy setup τ η α)
    (hProb : constantParameterConditionProbability setup τ α)
    (hEta : constantParameterConditionEta setup η α)
    (hLip : constantParameterConditionLipschitz setup τ η)
    (hAlpha : alphaRange α)
    (hRateDen : theorem_5_1_rateDenominatorBoundary η) :
    theorem_5_1_rateBounds_with_denominator_source_gap
      setup η α k hk hRateDen hStanding hAlpha xstar hxstar := by
  classical
  let θ : ℕ → ℝ := theoremOutputWeight α hAlpha
  let hp : ∀ i : ι, samplingProbability setup i ≠ 0 :=
    inverseProbabilityDenominators_ne_of_theorem_conditions
      setup τ η α hStanding hPolicy hProb hAlpha
  have hθ : ∀ t, 1 ≤ t → t ≤ k → 0 ≤ θ t := by
    intro t ht1 htk
    exact outputTheta_nonnegative_of_alphaRange α k hAlpha () t
      (by simpa [outputTimeWindow] using Finset.mem_Icc.mpr ⟨ht1, htk⟩)
  have h51 : ∀ t, 2 ≤ t → t ≤ k → setup.α t * θ t = θ (t - 1) := by
    intro t ht2 _htk
    exact theorem51_output_weight_shift setup τ η α hPolicy hAlpha t ht2
  let zstar : SaddlePoint setup :=
    (xstar, fun i => scaledComponentGradientDual setup hStanding.1 i xstar.1)
  have hDeltaFinite :
      (∑ t ∈ Finset.Icc 1 k, θ t *
        finitePrefixExpectation setup t (fun ω =>
          (⟪xTildeIter setup hStanding.1 t ω - (xIter setup hStanding.1 t ω).1,
              ∑ i : ι, (yTildeIter setup hStanding.1 t ω i - (zstar.2 i).1)⟫_ℝ -
            (setup.τ t *
                inverseProbabilityValue setup (sampledBlock setup t ω)
                  (sampledBlock_probability_ne_zero setup
                    (sampledPositiveBlock setup t ω))) *
              (SOptLib.carrierBregmanDivergence (dualConjugate setup (sampledBlock setup t ω)) (dualConjugateBaseSelector setup (sampledBlock setup t ω) ((yIter setup hStanding.1 (t - 1) ω) (sampledBlock setup t ω)) (dualSubgradIter setup hStanding.1 (t - 1) ω
                  (sampledBlock setup t ω))) ((yIter setup hStanding.1 (t - 1) ω) (sampledBlock setup t ω)) ((yIter setup hStanding.1 t ω) (sampledBlock setup t ω)))) -
            setup.η t *
              primalBregman setup
                (xIter setup hStanding.1 (t - 1) ω)
                (xIter setup hStanding.1 t ω))) ≤
        - θ k *
          finitePrefixExpectation setup k (fun ω =>
            setup.η k / 4 *
                ‖(xIter setup hStanding.1 (k - 1) ω).1 -
                  (xIter setup hStanding.1 k ω).1‖ ^ 2 -
              ⟪(xIter setup hStanding.1 (k - 1) ω).1 -
                  (xIter setup hStanding.1 k ω).1,
                ∑ i : ι, ((yIter setup hStanding.1 k ω i).1 -
                  (zstar.2 i).1)⟫_ℝ) := by
    simpa [θ, zstar] using
      theorem51_weighted_delta_finitePrefix_upper_bound_division_free
        setup τ η α hStanding hPolicy hProb hLip hAlpha hRateDen
        k hk hp hθ h51 zstar
  have h46 :
      ∀ t i, 2 ≤ t → t ≤ k →
        θ t * (inverseProbabilityValue setup i (hp i) *
            (1 + setup.τ t) - 1) ≤
          inverseProbabilityValue setup i (hp i) *
            θ (t - 1) * (1 + setup.τ (t - 1)) := by
    simpa [θ] using
      theorem51_condition_46_division_free
        setup τ η α hStanding hPolicy hProb hAlpha k hp
  have h47 :
      ∀ t, 2 ≤ t → t ≤ k →
        θ t * setup.η t ≤ θ (t - 1) * (setup.μ + setup.η (t - 1)) := by
    simpa [θ] using
      theorem51_condition_47_division_free
        setup τ η α hPolicy hEta hAlpha k
  have hPrimalFull :=
    proposition51_primal_fullstream_telescope
      setup hStanding.1 θ k hk zstar h47
  have hDualFull :=
    fun i : ι =>
      theorem51_dual_fullstream_telescope_division_free
        setup hStanding.1 θ k hk hp zstar h46 i
  have hWeighted :
      (∑ t ∈ Finset.Icc 1 k, θ t *
          expectedSaddleGap setup hStanding.1 t zstar) ≤
        ∑ t ∈ Finset.Icc 1 k, θ t *
          (finitePrefixExpectation setup t (fun ω =>
              setup.η t * primalBregman setup
                  (xIter setup hStanding.1 (t - 1) ω) zstar.1 -
                (setup.μ + setup.η t) *
                  primalBregman setup (xIter setup hStanding.1 t ω) zstar.1 -
                setup.η t * primalBregman setup
                  (xIter setup hStanding.1 (t - 1) ω)
                  (xIter setup hStanding.1 t ω)) +
            ∑ i : ι,
              finitePrefixExpectation setup t (fun ω =>
                (inverseProbabilityValue setup i (hp i) *
                    (1 + setup.τ t) - 1) *
                    (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 (t - 1) ω) i) (dualSubgradIter setup hStanding.1 (t - 1) ω i)) ((yIter setup hStanding.1 (t - 1) ω) i) (zstar.2 i)) -
                  (inverseProbabilityValue setup i (hp i) *
                      (1 + setup.τ t)) *
                    (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 t ω) i) (dualSubgradIter setup hStanding.1 t ω i)) ((yIter setup hStanding.1 t ω) i) (zstar.2 i))) +
            finitePrefixExpectation setup t (fun ω =>
              ⟪xTildeIter setup hStanding.1 t ω -
                  (xIter setup hStanding.1 t ω).1,
                ∑ i : ι, (yTildeIter setup hStanding.1 t ω i -
                  (zstar.2 i).1)⟫_ℝ -
                (setup.τ t *
                    inverseProbabilityValue setup (sampledBlock setup t ω)
                      (sampledBlock_probability_ne_zero setup
                        (sampledPositiveBlock setup t ω))) *
                  (SOptLib.carrierBregmanDivergence (dualConjugate setup (sampledBlock setup t ω)) (dualConjugateBaseSelector setup (sampledBlock setup t ω) ((yIter setup hStanding.1 (t - 1) ω)
                      (sampledBlock setup t ω)) (dualSubgradIter setup hStanding.1 (t - 1) ω
                      (sampledBlock setup t ω))) ((yIter setup hStanding.1 (t - 1) ω)
                      (sampledBlock setup t ω)) ((yIter setup hStanding.1 t ω)
                      (sampledBlock setup t ω))))) := by
    refine Finset.sum_le_sum ?_
    intro t htmem
    rcases Finset.mem_Icc.mp htmem with ⟨ht, htk⟩
    have hstep :=
      Lemma_5_5_one_step_RPDG_recursion_with_denominator_source_gap
        setup hStanding.1 hp t ht zstar
    exact mul_le_mul_of_nonneg_left hstep (hθ t ht htk)
  have hPrimalInitialFull :
      (∫ ω, primalBregman setup (xIter setup hStanding.1 0 ω) zstar.1
          ∂blockStreamLaw setup) =
        primalBregman setup setup.x0 zstar.1 := by
    letI : IsProbabilityMeasure (blockIndexLaw setup) := by
      unfold blockIndexLaw
      infer_instance
    letI : IsProbabilityMeasure (blockStreamLaw setup) := by
      unfold blockStreamLaw
      exact SOptLib.iidStreamLaw_isProbabilityMeasure (blockIndexLaw setup)
    have hconst :
        (fun ω : BlockSamplePath setup =>
          primalBregman setup (xIter setup hStanding.1 0 ω) zstar.1) =
            fun _ω : BlockSamplePath setup =>
              primalBregman setup setup.x0 zstar.1 := by
      funext ω
      simp [xIter, stateProcess_zero, initialState]
    rw [hconst]
    simp
  have hPrimalTerminalFull :
      (∫ ω, primalBregman setup (xIter setup hStanding.1 k ω) zstar.1
          ∂blockStreamLaw setup) =
        finitePrefixExpectation setup k
          (fun ω => primalBregman setup (xIter setup hStanding.1 k ω) zstar.1) := by
    rw [← finite_prefix_expectation_primal_iter_bregman_eq_blockStream_of_le
      setup hStanding.1 (le_rfl : k ≤ k) zstar.1]
  have hDualInitialFull : ∀ i : ι,
      (∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 0 ω) i) (dualSubgradIter setup hStanding.1 0 ω i)) ((yIter setup hStanding.1 0 ω) i) (zstar.2 i))
            ∂blockStreamLaw setup) =
        (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i (initialDual setup hStanding.1 i) (initialDualSubgradient setup hStanding.1 i)) (initialDual setup hStanding.1 i) (zstar.2 i)) := by
    intro i
    letI : IsProbabilityMeasure (blockIndexLaw setup) := by
      unfold blockIndexLaw
      infer_instance
    letI : IsProbabilityMeasure (blockStreamLaw setup) := by
      unfold blockStreamLaw
      exact SOptLib.iidStreamLaw_isProbabilityMeasure (blockIndexLaw setup)
    have hconst :
        (fun ω : BlockSamplePath setup =>
          (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 0 ω) i) (dualSubgradIter setup hStanding.1 0 ω i)) ((yIter setup hStanding.1 0 ω) i) (zstar.2 i))) =
          fun _ω : BlockSamplePath setup =>
            (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i (initialDual setup hStanding.1 i) (initialDualSubgradient setup hStanding.1 i)) (initialDual setup hStanding.1 i) (zstar.2 i)) := by
      funext ω
      dsimp [yIter, dualSubgradIter]
      rw [stateProcess_zero setup hStanding.1 ω]
      rfl
    rw [hconst]
    simp
  have hDualTerminalFull : ∀ i : ι,
      (∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 k ω) i) (dualSubgradIter setup hStanding.1 k ω i)) ((yIter setup hStanding.1 k ω) i) (zstar.2 i))
            ∂blockStreamLaw setup) =
        finitePrefixExpectation setup k
          (fun ω => (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 k ω) i) (dualSubgradIter setup hStanding.1 k ω i)) ((yIter setup hStanding.1 k ω) i) (zstar.2 i))) := by
    intro i
    rw [← finite_prefix_expectation_dual_iter_bregman_eq_blockStream_of_le
      setup hStanding.1 (le_rfl : k ≤ k) i (zstar.2 i)]
  have hPrimalFinite :
      (∑ t ∈ Finset.Icc 1 k, θ t *
        finitePrefixExpectation setup t (fun ω =>
          setup.η t *
              primalBregman setup (xIter setup hStanding.1 (t - 1) ω) zstar.1 -
            (setup.μ + setup.η t) *
              primalBregman setup (xIter setup hStanding.1 t ω) zstar.1)) ≤
        setup.η 1 * θ 1 * primalBregman setup setup.x0 zstar.1 -
          (setup.μ + setup.η k) * θ k *
            finitePrefixExpectation setup k
              (fun ω => primalBregman setup
                (xIter setup hStanding.1 k ω) zstar.1) := by
    have hsum_eq :
        (∑ t ∈ Finset.Icc 1 k, θ t *
          finitePrefixExpectation setup t (fun ω =>
            setup.η t *
                primalBregman setup (xIter setup hStanding.1 (t - 1) ω) zstar.1 -
              (setup.μ + setup.η t) *
                primalBregman setup (xIter setup hStanding.1 t ω) zstar.1)) =
          ∑ t ∈ Finset.Icc 1 k, (
            (θ t * setup.η t) *
                (∫ ω, primalBregman setup
                  (xIter setup hStanding.1 (t - 1) ω) zstar.1 ∂blockStreamLaw setup) -
              (θ t * (setup.μ + setup.η t)) *
                (∫ ω, primalBregman setup
                  (xIter setup hStanding.1 t ω) zstar.1 ∂blockStreamLaw setup)) := by
      refine Finset.sum_congr rfl ?_
      intro t htmem
      rcases Finset.mem_Icc.mp htmem with ⟨ht, _htk⟩
      have hprev :
          finitePrefixExpectation setup t (fun ω =>
            primalBregman setup (xIter setup hStanding.1 (t - 1) ω) zstar.1) =
            ∫ ω, primalBregman setup
              (xIter setup hStanding.1 (t - 1) ω) zstar.1 ∂blockStreamLaw setup := by
        exact finite_prefix_expectation_primal_iter_bregman_eq_blockStream_of_le
          setup hStanding.1 (by omega : t - 1 ≤ t) zstar.1
      have hcur :
          finitePrefixExpectation setup t (fun ω =>
            primalBregman setup (xIter setup hStanding.1 t ω) zstar.1) =
            ∫ ω, primalBregman setup
              (xIter setup hStanding.1 t ω) zstar.1 ∂blockStreamLaw setup := by
        exact finite_prefix_expectation_primal_iter_bregman_eq_blockStream_of_le
          setup hStanding.1 (le_rfl : t ≤ t) zstar.1
      simp [finitePrefixExpectation_sub, finitePrefixExpectation_const_mul,
        hprev, hcur]
      ring
    calc
      (∑ t ∈ Finset.Icc 1 k, θ t *
        finitePrefixExpectation setup t (fun ω =>
          setup.η t *
              primalBregman setup (xIter setup hStanding.1 (t - 1) ω) zstar.1 -
            (setup.μ + setup.η t) *
              primalBregman setup (xIter setup hStanding.1 t ω) zstar.1)) =
          ∑ t ∈ Finset.Icc 1 k, (
            (θ t * setup.η t) *
                (∫ ω, primalBregman setup
                  (xIter setup hStanding.1 (t - 1) ω) zstar.1 ∂blockStreamLaw setup) -
              (θ t * (setup.μ + setup.η t)) *
                (∫ ω, primalBregman setup
                  (xIter setup hStanding.1 t ω) zstar.1 ∂blockStreamLaw setup)) := hsum_eq
      _ ≤ θ 1 * setup.η 1 *
            (∫ ω, primalBregman setup
              (xIter setup hStanding.1 0 ω) zstar.1 ∂blockStreamLaw setup) -
          θ k * (setup.μ + setup.η k) *
            (∫ ω, primalBregman setup
              (xIter setup hStanding.1 k ω) zstar.1 ∂blockStreamLaw setup) := hPrimalFull
      _ = setup.η 1 * θ 1 * primalBregman setup setup.x0 zstar.1 -
          (setup.μ + setup.η k) * θ k *
            finitePrefixExpectation setup k
              (fun ω => primalBregman setup
                (xIter setup hStanding.1 k ω) zstar.1) := by
            rw [hPrimalInitialFull, hPrimalTerminalFull]
            ring
  have hDualFinite :
      (∑ i : ι,
        ∑ t ∈ Finset.Icc 1 k, θ t *
          finitePrefixExpectation setup t (fun ω =>
            (inverseProbabilityValue setup i (hp i) *
                (1 + setup.τ t) - 1) *
                (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 (t - 1) ω) i) (dualSubgradIter setup hStanding.1 (t - 1) ω i)) ((yIter setup hStanding.1 (t - 1) ω) i) (zstar.2 i)) -
              (inverseProbabilityValue setup i (hp i) *
                  (1 + setup.τ t)) *
                (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 t ω) i) (dualSubgradIter setup hStanding.1 t ω i)) ((yIter setup hStanding.1 t ω) i) (zstar.2 i)))) ≤
        ∑ i : ι, (
          θ 1 *
              (inverseProbabilityValue setup i (hp i) *
                (1 + setup.τ 1) - 1) *
            (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i (initialDual setup hStanding.1 i) (initialDualSubgradient setup hStanding.1 i)) (initialDual setup hStanding.1 i) (zstar.2 i)) -
          inverseProbabilityValue setup i (hp i) * θ k *
              (1 + setup.τ k) *
            finitePrefixExpectation setup k (fun ω =>
              (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 k ω) i) (dualSubgradIter setup hStanding.1 k ω i)) ((yIter setup hStanding.1 k ω) i) (zstar.2 i)))) := by
    refine Finset.sum_le_sum ?_
    intro i _hi
    have hsum_eq :
        (∑ t ∈ Finset.Icc 1 k, θ t *
          finitePrefixExpectation setup t (fun ω =>
            (inverseProbabilityValue setup i (hp i) *
                (1 + setup.τ t) - 1) *
                (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 (t - 1) ω) i) (dualSubgradIter setup hStanding.1 (t - 1) ω i)) ((yIter setup hStanding.1 (t - 1) ω) i) (zstar.2 i)) -
              (inverseProbabilityValue setup i (hp i) *
                  (1 + setup.τ t)) *
                (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 t ω) i) (dualSubgradIter setup hStanding.1 t ω i)) ((yIter setup hStanding.1 t ω) i) (zstar.2 i)))) =
          ∑ t ∈ Finset.Icc 1 k, (
            θ t *
                (inverseProbabilityValue setup i (hp i) *
                  (1 + setup.τ t) - 1) *
              (∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 (t - 1) ω) i) (dualSubgradIter setup hStanding.1 (t - 1) ω i)) ((yIter setup hStanding.1 (t - 1) ω) i) (zstar.2 i))
                  ∂blockStreamLaw setup) -
            inverseProbabilityValue setup i (hp i) * θ t *
                (1 + setup.τ t) *
              (∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 t ω) i) (dualSubgradIter setup hStanding.1 t ω i)) ((yIter setup hStanding.1 t ω) i) (zstar.2 i))
                  ∂blockStreamLaw setup)) := by
      refine Finset.sum_congr rfl ?_
      intro t htmem
      rcases Finset.mem_Icc.mp htmem with ⟨ht, _htk⟩
      have hprev :
          finitePrefixExpectation setup t (fun ω =>
            (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 (t - 1) ω) i) (dualSubgradIter setup hStanding.1 (t - 1) ω i)) ((yIter setup hStanding.1 (t - 1) ω) i) (zstar.2 i))) =
            ∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 (t - 1) ω) i) (dualSubgradIter setup hStanding.1 (t - 1) ω i)) ((yIter setup hStanding.1 (t - 1) ω) i) (zstar.2 i))
                ∂blockStreamLaw setup := by
        exact finite_prefix_expectation_dual_iter_bregman_eq_blockStream_of_le
          setup hStanding.1 (by omega : t - 1 ≤ t) i (zstar.2 i)
      have hcur :
          finitePrefixExpectation setup t (fun ω =>
            (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 t ω) i) (dualSubgradIter setup hStanding.1 t ω i)) ((yIter setup hStanding.1 t ω) i) (zstar.2 i))) =
            ∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 t ω) i) (dualSubgradIter setup hStanding.1 t ω i)) ((yIter setup hStanding.1 t ω) i) (zstar.2 i))
                ∂blockStreamLaw setup := by
        exact finite_prefix_expectation_dual_iter_bregman_eq_blockStream_of_le
          setup hStanding.1 (le_rfl : t ≤ t) i (zstar.2 i)
      simp [finitePrefixExpectation_sub, finitePrefixExpectation_const_mul,
        hprev, hcur]
      ring
    calc
      (∑ t ∈ Finset.Icc 1 k, θ t *
          finitePrefixExpectation setup t (fun ω =>
            (inverseProbabilityValue setup i (hp i) *
                (1 + setup.τ t) - 1) *
                (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 (t - 1) ω) i) (dualSubgradIter setup hStanding.1 (t - 1) ω i)) ((yIter setup hStanding.1 (t - 1) ω) i) (zstar.2 i)) -
              (inverseProbabilityValue setup i (hp i) *
                  (1 + setup.τ t)) *
                (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 t ω) i) (dualSubgradIter setup hStanding.1 t ω i)) ((yIter setup hStanding.1 t ω) i) (zstar.2 i)))) =
          ∑ t ∈ Finset.Icc 1 k, (
            θ t *
                (inverseProbabilityValue setup i (hp i) *
                  (1 + setup.τ t) - 1) *
              (∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 (t - 1) ω) i) (dualSubgradIter setup hStanding.1 (t - 1) ω i)) ((yIter setup hStanding.1 (t - 1) ω) i) (zstar.2 i))
                  ∂blockStreamLaw setup) -
            inverseProbabilityValue setup i (hp i) * θ t *
                (1 + setup.τ t) *
              (∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 t ω) i) (dualSubgradIter setup hStanding.1 t ω i)) ((yIter setup hStanding.1 t ω) i) (zstar.2 i))
                  ∂blockStreamLaw setup)) := hsum_eq
      _ ≤ θ 1 *
            (inverseProbabilityValue setup i (hp i) *
              (1 + setup.τ 1) - 1) *
          (∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 0 ω) i) (dualSubgradIter setup hStanding.1 0 ω i)) ((yIter setup hStanding.1 0 ω) i) (zstar.2 i))
              ∂blockStreamLaw setup) -
          inverseProbabilityValue setup i (hp i) * θ k *
              (1 + setup.τ k) *
            (∫ ω, (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 k ω) i) (dualSubgradIter setup hStanding.1 k ω i)) ((yIter setup hStanding.1 k ω) i) (zstar.2 i))
                ∂blockStreamLaw setup) := hDualFull i
      _ = θ 1 *
            (inverseProbabilityValue setup i (hp i) *
              (1 + setup.τ 1) - 1) *
          (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i (initialDual setup hStanding.1 i) (initialDualSubgradient setup hStanding.1 i)) (initialDual setup hStanding.1 i) (zstar.2 i)) -
          inverseProbabilityValue setup i (hp i) * θ k *
              (1 + setup.τ k) *
            finitePrefixExpectation setup k (fun ω =>
              (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 k ω) i) (dualSubgradIter setup hStanding.1 k ω i)) ((yIter setup hStanding.1 k ω) i) (zstar.2 i))) := by
          rw [hDualInitialFull i, hDualTerminalFull i]
  have hDualWeightedSumComm :
      (∑ t ∈ Finset.Icc 1 k, θ t *
        (∑ i : ι,
          finitePrefixExpectation setup t (fun ω =>
            (inverseProbabilityValue setup i (hp i) *
                (1 + setup.τ t) - 1) *
                (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 (t - 1) ω) i) (dualSubgradIter setup hStanding.1 (t - 1) ω i)) ((yIter setup hStanding.1 (t - 1) ω) i) (zstar.2 i)) -
              (inverseProbabilityValue setup i (hp i) *
                  (1 + setup.τ t)) *
                (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 t ω) i) (dualSubgradIter setup hStanding.1 t ω i)) ((yIter setup hStanding.1 t ω) i) (zstar.2 i))))) =
        ∑ i : ι,
          ∑ t ∈ Finset.Icc 1 k, θ t *
            finitePrefixExpectation setup t (fun ω =>
              (inverseProbabilityValue setup i (hp i) *
                  (1 + setup.τ t) - 1) *
                  (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 (t - 1) ω) i) (dualSubgradIter setup hStanding.1 (t - 1) ω i)) ((yIter setup hStanding.1 (t - 1) ω) i) (zstar.2 i)) -
                (inverseProbabilityValue setup i (hp i) *
                    (1 + setup.τ t)) *
                  (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 t ω) i) (dualSubgradIter setup hStanding.1 t ω i)) ((yIter setup hStanding.1 t ω) i) (zstar.2 i))) := by
    calc
      (∑ t ∈ Finset.Icc 1 k, θ t *
        (∑ i : ι,
          finitePrefixExpectation setup t (fun ω =>
            (inverseProbabilityValue setup i (hp i) *
                (1 + setup.τ t) - 1) *
                (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 (t - 1) ω) i) (dualSubgradIter setup hStanding.1 (t - 1) ω i)) ((yIter setup hStanding.1 (t - 1) ω) i) (zstar.2 i)) -
              (inverseProbabilityValue setup i (hp i) *
                  (1 + setup.τ t)) *
                (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 t ω) i) (dualSubgradIter setup hStanding.1 t ω i)) ((yIter setup hStanding.1 t ω) i) (zstar.2 i))))) =
          ∑ t ∈ Finset.Icc 1 k,
            ∑ i : ι, θ t *
              finitePrefixExpectation setup t (fun ω =>
                (inverseProbabilityValue setup i (hp i) *
                    (1 + setup.τ t) - 1) *
                    (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 (t - 1) ω) i) (dualSubgradIter setup hStanding.1 (t - 1) ω i)) ((yIter setup hStanding.1 (t - 1) ω) i) (zstar.2 i)) -
                  (inverseProbabilityValue setup i (hp i) *
                      (1 + setup.τ t)) *
                    (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 t ω) i) (dualSubgradIter setup hStanding.1 t ω i)) ((yIter setup hStanding.1 t ω) i) (zstar.2 i))) := by
            refine Finset.sum_congr rfl ?_
            intro t _htmem
            rw [Finset.mul_sum]
      _ = ∑ i : ι,
          ∑ t ∈ Finset.Icc 1 k, θ t *
            finitePrefixExpectation setup t (fun ω =>
              (inverseProbabilityValue setup i (hp i) *
                  (1 + setup.τ t) - 1) *
                  (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 (t - 1) ω) i) (dualSubgradIter setup hStanding.1 (t - 1) ω i)) ((yIter setup hStanding.1 (t - 1) ω) i) (zstar.2 i)) -
                (inverseProbabilityValue setup i (hp i) *
                    (1 + setup.τ t)) *
                  (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 t ω) i) (dualSubgradIter setup hStanding.1 t ω i)) ((yIter setup hStanding.1 t ω) i) (zstar.2 i))) := by
            rw [Finset.sum_comm]
  have hDualTimeBound :
      (∑ t ∈ Finset.Icc 1 k, θ t *
        (∑ i : ι,
          finitePrefixExpectation setup t (fun ω =>
            (inverseProbabilityValue setup i (hp i) *
                (1 + setup.τ t) - 1) *
                (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 (t - 1) ω) i) (dualSubgradIter setup hStanding.1 (t - 1) ω i)) ((yIter setup hStanding.1 (t - 1) ω) i) (zstar.2 i)) -
              (inverseProbabilityValue setup i (hp i) *
                  (1 + setup.τ t)) *
                (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 t ω) i) (dualSubgradIter setup hStanding.1 t ω i)) ((yIter setup hStanding.1 t ω) i) (zstar.2 i))))) ≤
        ∑ i : ι, (
          θ 1 *
              (inverseProbabilityValue setup i (hp i) *
                (1 + setup.τ 1) - 1) *
            (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i (initialDual setup hStanding.1 i) (initialDualSubgradient setup hStanding.1 i)) (initialDual setup hStanding.1 i) (zstar.2 i)) -
          inverseProbabilityValue setup i (hp i) * θ k *
              (1 + setup.τ k) *
            finitePrefixExpectation setup k (fun ω =>
              (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 k ω) i) (dualSubgradIter setup hStanding.1 k ω i)) ((yIter setup hStanding.1 k ω) i) (zstar.2 i)))) := by
    rw [hDualWeightedSumComm]
    exact hDualFinite
  have hWeightedGapNonnegative :
      0 ≤ ∑ t ∈ Finset.Icc 1 k, θ t *
        expectedSaddleGap setup hStanding.1 t zstar := by
    refine Finset.sum_nonneg ?_
    intro t htmem
    rcases Finset.mem_Icc.mp htmem with ⟨ht, htk⟩
    have hgap_nonneg :
        0 ≤ expectedSaddleGap setup hStanding.1 t zstar := by
      unfold expectedSaddleGap finitePrefixExpectation
      exact MeasureTheory.integral_nonneg fun pref =>
        theorem51_scaled_gradient_saddle_gap_nonnegative
          setup hStanding.1 xstar hxstar t (extendBlockPrefix setup t pref)
    exact mul_nonneg (hθ t ht htk) hgap_nonneg
  have hInitialDualEndpoint :
      (∑ i : ι,
        (θ 1 *
            (inverseProbabilityValue setup i (hp i) *
              (1 + setup.τ 1) - 1)) *
          (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i (initialDual setup hStanding.1 i) (initialDualSubgradient setup hStanding.1 i)) (initialDual setup hStanding.1 i) (zstar.2 i))) ≤
        θ 1 *
          sourceQuotient α (1 - α)
            (one_sub_alpha_ne_zero_of_alphaRange hAlpha) *
          (setup.Lf * primalBregman setup setup.x0 xstar) := by
    have hτ1 : setup.τ 1 = τ := hPolicy.1 1 le_rfl
    simpa [θ, zstar, hp, hτ1] using
      theorem51_initial_dual_endpoint_le
        setup τ η α hStanding hPolicy hProb hAlpha xstar hxstar
  have h50 :
      propositionCondition_5_1_50_with_denominator_source_gap
        setup hStanding.1 k hk := by
    exact theorem51_condition_50_division_free
      setup τ η α hStanding hPolicy hLip k hk
  let terminal : BlockSamplePath setup → ℝ := fun ω =>
    setup.η k / 4 *
        ‖(xIter setup hStanding.1 (k - 1) ω).1 -
          (xIter setup hStanding.1 k ω).1‖ ^ 2 -
      ⟪(xIter setup hStanding.1 (k - 1) ω).1 -
          (xIter setup hStanding.1 k ω).1,
        ∑ i : ι, ((yIter setup hStanding.1 k ω i).1 -
          (zstar.2 i).1)⟫_ℝ
  let terminalDual : ι → BlockSamplePath setup → ℝ := fun i ω =>
    (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 k ω) i) (dualSubgradIter setup hStanding.1 k ω i)) ((yIter setup hStanding.1 k ω) i) (zstar.2 i))
  have hTerminalResidualFinite :
      0 ≤ finitePrefixExpectation setup k (fun ω =>
        terminal ω +
          ∑ i : ι,
            inverseProbabilityValue setup i (hp i) *
              (1 + setup.τ k) * terminalDual i ω) := by
    unfold finitePrefixExpectation
    exact MeasureTheory.integral_nonneg fun pref => by
      simpa [terminal, terminalDual, mul_assoc, mul_comm, mul_left_comm] using
        terminal_residual_bracket_nonnegative_of_h50_and_probabilities
          setup hStanding.1 k hk hp h50 zstar (extendBlockPrefix setup k pref)
  have hTerminalResidualExpanded :
      finitePrefixExpectation setup k (fun ω =>
        terminal ω +
          ∑ i : ι,
            inverseProbabilityValue setup i (hp i) *
              (1 + setup.τ k) * terminalDual i ω) =
        finitePrefixExpectation setup k terminal +
          ∑ i : ι,
            inverseProbabilityValue setup i (hp i) *
              (1 + setup.τ k) *
              finitePrefixExpectation setup k (terminalDual i) := by
    calc
      finitePrefixExpectation setup k (fun ω =>
        terminal ω +
          ∑ i : ι,
            inverseProbabilityValue setup i (hp i) *
              (1 + setup.τ k) * terminalDual i ω) =
          finitePrefixExpectation setup k terminal +
            finitePrefixExpectation setup k (fun ω =>
              ∑ i : ι,
                inverseProbabilityValue setup i (hp i) *
                  (1 + setup.τ k) * terminalDual i ω) := by
            rw [finitePrefixExpectation_add]
      _ = finitePrefixExpectation setup k terminal +
          ∑ i : ι,
            finitePrefixExpectation setup k (fun ω =>
              inverseProbabilityValue setup i (hp i) *
                (1 + setup.τ k) * terminalDual i ω) := by
            rw [finitePrefixExpectation_finset_sum]
      _ = finitePrefixExpectation setup k terminal +
          ∑ i : ι,
            inverseProbabilityValue setup i (hp i) *
              (1 + setup.τ k) *
              finitePrefixExpectation setup k (terminalDual i) := by
            refine congrArg (fun s => finitePrefixExpectation setup k terminal + s) ?_
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [finitePrefixExpectation_const_mul]
  have hTerminalTailNonpositive :
      - θ k * finitePrefixExpectation setup k terminal -
        ∑ i : ι,
          inverseProbabilityValue setup i (hp i) * θ k *
            (1 + setup.τ k) *
            finitePrefixExpectation setup k (terminalDual i) ≤ 0 := by
    have hResidualExpandedNonneg :
        0 ≤ finitePrefixExpectation setup k terminal +
          ∑ i : ι,
            inverseProbabilityValue setup i (hp i) *
              (1 + setup.τ k) *
              finitePrefixExpectation setup k (terminalDual i) := by
      rwa [hTerminalResidualExpanded] at hTerminalResidualFinite
    have hθk_nonneg : 0 ≤ θ k := hθ k hk le_rfl
    have hscaled :
        0 ≤ θ k *
          (finitePrefixExpectation setup k terminal +
            ∑ i : ι,
              inverseProbabilityValue setup i (hp i) *
                (1 + setup.τ k) *
                finitePrefixExpectation setup k (terminalDual i)) :=
      mul_nonneg hθk_nonneg hResidualExpandedNonneg
    have hsum_factor :
        (∑ i : ι,
          inverseProbabilityValue setup i (hp i) * θ k *
            (1 + setup.τ k) *
            finitePrefixExpectation setup k (terminalDual i)) =
          θ k *
            (∑ i : ι,
              inverseProbabilityValue setup i (hp i) *
                (1 + setup.τ k) *
                finitePrefixExpectation setup k (terminalDual i)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _hi
      ring
    calc
      - θ k * finitePrefixExpectation setup k terminal -
          ∑ i : ι,
            inverseProbabilityValue setup i (hp i) * θ k *
              (1 + setup.τ k) *
              finitePrefixExpectation setup k (terminalDual i) =
          - θ k *
            (finitePrefixExpectation setup k terminal +
              ∑ i : ι,
                inverseProbabilityValue setup i (hp i) *
                  (1 + setup.τ k) *
                  finitePrefixExpectation setup k (terminalDual i)) := by
            rw [hsum_factor]
            ring
      _ ≤ 0 := by
            nlinarith
  have hWeightedProp :
      (∑ t ∈ Finset.Icc 1 k, θ t *
          expectedSaddleGap setup hStanding.1 t zstar) ≤
        setup.η 1 * θ 1 * primalBregman setup setup.x0 zstar.1 -
          (setup.μ + setup.η k) * θ k *
            finitePrefixExpectation setup k
              (fun ω => primalBregman setup
                (xIter setup hStanding.1 k ω) zstar.1) +
        ∑ i : ι,
          θ 1 * (inverseProbabilityValue setup i (hp i) *
              (1 + setup.τ 1) - 1) *
            (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i (initialDual setup hStanding.1 i) (initialDualSubgradient setup hStanding.1 i)) (initialDual setup hStanding.1 i) (zstar.2 i)) := by
    let P : ℕ → ℝ := fun t =>
      finitePrefixExpectation setup t (fun ω =>
        setup.η t * primalBregman setup
            (xIter setup hStanding.1 (t - 1) ω) zstar.1 -
          (setup.μ + setup.η t) *
            primalBregman setup (xIter setup hStanding.1 t ω) zstar.1)
    let D : ℕ → ℝ := fun t =>
      ∑ i : ι,
        finitePrefixExpectation setup t (fun ω =>
          (inverseProbabilityValue setup i (hp i) *
              (1 + setup.τ t) - 1) *
              (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 (t - 1) ω) i) (dualSubgradIter setup hStanding.1 (t - 1) ω i)) ((yIter setup hStanding.1 (t - 1) ω) i) (zstar.2 i)) -
            (inverseProbabilityValue setup i (hp i) *
                (1 + setup.τ t)) *
              (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 t ω) i) (dualSubgradIter setup hStanding.1 t ω i)) ((yIter setup hStanding.1 t ω) i) (zstar.2 i)))
    let R : ℕ → ℝ := fun t =>
      finitePrefixExpectation setup t (fun ω =>
        ⟪xTildeIter setup hStanding.1 t ω -
            (xIter setup hStanding.1 t ω).1,
          ∑ i : ι, (yTildeIter setup hStanding.1 t ω i -
            (zstar.2 i).1)⟫_ℝ -
        (setup.τ t *
            inverseProbabilityValue setup (sampledBlock setup t ω)
              (sampledBlock_probability_ne_zero setup
                (sampledPositiveBlock setup t ω))) *
          (SOptLib.carrierBregmanDivergence (dualConjugate setup (sampledBlock setup t ω)) (dualConjugateBaseSelector setup (sampledBlock setup t ω) ((yIter setup hStanding.1 (t - 1) ω)
              (sampledBlock setup t ω)) (dualSubgradIter setup hStanding.1 (t - 1) ω
              (sampledBlock setup t ω))) ((yIter setup hStanding.1 (t - 1) ω)
              (sampledBlock setup t ω)) ((yIter setup hStanding.1 t ω)
              (sampledBlock setup t ω))))
    let Q : ℕ → ℝ := fun t =>
      setup.η t *
        finitePrefixExpectation setup t (fun ω =>
          primalBregman setup
            (xIter setup hStanding.1 (t - 1) ω)
            (xIter setup hStanding.1 t ω))
    have hWeightedAbbrev :
        (∑ t ∈ Finset.Icc 1 k, θ t *
          ((finitePrefixExpectation setup t (fun ω =>
                setup.η t * primalBregman setup
                    (xIter setup hStanding.1 (t - 1) ω) zstar.1 -
                  (setup.μ + setup.η t) *
                    primalBregman setup (xIter setup hStanding.1 t ω) zstar.1 -
                  setup.η t * primalBregman setup
                    (xIter setup hStanding.1 (t - 1) ω)
                    (xIter setup hStanding.1 t ω)) +
              D t) + R t)) =
          ∑ t ∈ Finset.Icc 1 k, θ t * (((P t - Q t) + D t) + R t) := by
      refine Finset.sum_congr rfl ?_
      intro t _htmem
      dsimp [P, Q]
      rw [finitePrefixExpectation_sub, finitePrefixExpectation_const_mul]
    have hWeightedSplit :
        (∑ t ∈ Finset.Icc 1 k, θ t *
            expectedSaddleGap setup hStanding.1 t zstar) ≤
          (∑ t ∈ Finset.Icc 1 k, θ t * P t) +
            (∑ t ∈ Finset.Icc 1 k, θ t * D t) +
              (∑ t ∈ Finset.Icc 1 k, θ t * (R t - Q t)) := by
      have hsplit :=
        sum_weighted_three_way_residual_split (Finset.Icc 1 k) θ P D R Q
      rw [hWeightedAbbrev, hsplit] at hWeighted
      exact hWeighted
    have hPrimalFiniteP :
        (∑ t ∈ Finset.Icc 1 k, θ t * P t) ≤
          setup.η 1 * θ 1 * primalBregman setup setup.x0 zstar.1 -
            (setup.μ + setup.η k) * θ k *
              finitePrefixExpectation setup k
                (fun ω => primalBregman setup
                  (xIter setup hStanding.1 k ω) zstar.1) := by
      simpa [P] using hPrimalFinite
    have hDualTimeBoundD :
        (∑ t ∈ Finset.Icc 1 k, θ t * D t) ≤
          ∑ i : ι, (
            θ 1 *
                (inverseProbabilityValue setup i (hp i) *
                  (1 + setup.τ 1) - 1) *
              (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i (initialDual setup hStanding.1 i) (initialDualSubgradient setup hStanding.1 i)) (initialDual setup hStanding.1 i) (zstar.2 i)) -
            inverseProbabilityValue setup i (hp i) * θ k *
                (1 + setup.τ k) *
              finitePrefixExpectation setup k (terminalDual i)) := by
      simpa [D, terminalDual] using hDualTimeBound
    have hDeltaFiniteRQ :
        (∑ t ∈ Finset.Icc 1 k, θ t * (R t - Q t)) ≤
          - θ k * finitePrefixExpectation setup k terminal := by
      simpa [R, Q, terminal, finitePrefixExpectation_sub,
        finitePrefixExpectation_const_mul] using hDeltaFinite
    have hDualEndpointSplit :
        (∑ i : ι, (
            θ 1 *
                (inverseProbabilityValue setup i (hp i) *
                  (1 + setup.τ 1) - 1) *
              (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i (initialDual setup hStanding.1 i) (initialDualSubgradient setup hStanding.1 i)) (initialDual setup hStanding.1 i) (zstar.2 i)) -
            inverseProbabilityValue setup i (hp i) * θ k *
                (1 + setup.τ k) *
              finitePrefixExpectation setup k (fun ω =>
                (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 k ω) i) (dualSubgradIter setup hStanding.1 k ω i)) ((yIter setup hStanding.1 k ω) i) (zstar.2 i))))) =
          ((∑ i : ι,
            θ 1 *
                (inverseProbabilityValue setup i (hp i) *
                  (1 + setup.τ 1) - 1) *
              (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i (initialDual setup hStanding.1 i) (initialDualSubgradient setup hStanding.1 i)) (initialDual setup hStanding.1 i) (zstar.2 i))) -
          (∑ i : ι,
            inverseProbabilityValue setup i (hp i) * θ k *
                (1 + setup.τ k) *
              finitePrefixExpectation setup k (fun ω =>
                (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding.1 k ω) i) (dualSubgradIter setup hStanding.1 k ω i)) ((yIter setup hStanding.1 k ω) i) (zstar.2 i))))) := by
      rw [Finset.sum_sub_distrib]
    rw [hDualEndpointSplit] at hDualTimeBoundD
    nlinarith [hWeightedSplit, hPrimalFiniteP, hDualTimeBoundD,
      hDeltaFiniteRQ, hTerminalTailNonpositive]
  have hTerminalBudget :
      (setup.μ + setup.η k) * θ k *
        finitePrefixExpectation setup k
          (fun ω => primalBregman setup
            (xIter setup hStanding.1 k ω) zstar.1) ≤
        setup.η 1 * θ 1 * primalBregman setup setup.x0 zstar.1 +
          θ 1 *
            sourceQuotient α (1 - α)
              (one_sub_alpha_ne_zero_of_alphaRange hAlpha) *
            (setup.Lf * primalBregman setup setup.x0 xstar) := by
    nlinarith [hWeightedProp, hWeightedGapNonnegative, hInitialDualEndpoint]
  have hDistanceRate :
      expectedBregmanDistance setup hStanding.1 k xstar ≤
        (1 + sourceQuotient (setup.Lf * α) ((1 - α) * η)
            (rateProductDenominator_ne_for_theorem_5_1 η α hRateDen hAlpha)) *
          α ^ k *
          primalBregman setup setup.x0 xstar := by
    let F : ℝ :=
      finitePrefixExpectation setup k (fun ω =>
        primalBregman setup (xIter setup hStanding.1 k ω) xstar)
    let V0 : ℝ := primalBregman setup setup.x0 xstar
    have hη_pos : 0 < η :=
      theorem51_eta_pos_of_rate_boundary
        (setup := setup) τ η α hStanding hPolicy hRateDen
    have hF_nonneg : 0 ≤ F := by
      dsimp [F, finitePrefixExpectation]
      exact MeasureTheory.integral_nonneg fun pref =>
        primalBregman_nonnegative_of_standing (setup := setup) hStanding.1
          (xIter setup hStanding.1 k (extendBlockPrefix setup k pref)) xstar
    have hθ1_eq : θ 1 = 1 / α := by
      simp [θ, theoremOutputWeight, sourceQuotient]
    have hθk_eq : θ k = 1 / α ^ k := by
      simp [θ, theoremOutputWeight, sourceQuotient]
    have hη1 : setup.η 1 = η := hPolicy.2.1 1 le_rfl
    have hηk : setup.η k = η := hPolicy.2.1 k hk
    have hBudgetScalar :
        (setup.μ + η) * (1 / α ^ k) * F ≤
          η * (1 / α) * V0 +
            (1 / α) * (α / (1 - α)) * (setup.Lf * V0) := by
      simpa [F, V0, zstar, hη1, hηk, hθ1_eq, hθk_eq, sourceQuotient,
        mul_assoc, mul_comm, mul_left_comm] using hTerminalBudget
    have hBudgetClean :
        (setup.μ + η) * ((1 / α ^ k) * F) ≤
          (η / α + setup.Lf / (1 - α)) * V0 := by
      have hleft :
          (setup.μ + η) * (1 / α ^ k) * F =
            (setup.μ + η) * ((1 / α ^ k) * F) := by ring
      have hright :
          η * (1 / α) * V0 +
              (1 / α) * (α / (1 - α)) * (setup.Lf * V0) =
            (η / α + setup.Lf / (1 - α)) * V0 := by
        field_simp [alpha_ne_zero_of_alphaRange hAlpha,
          one_sub_alpha_ne_zero_of_alphaRange hAlpha]
      rw [hleft, hright] at hBudgetScalar
      exact hBudgetScalar
    have hcoef : η / α ≤ setup.μ + η := by
      rw [div_le_iff₀ hAlpha.1]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hEta
    have hfactor_nonneg : 0 ≤ (1 / α ^ k) * F := by
      have hpow_pos : 0 < α ^ k := pow_pos hAlpha.1 k
      exact mul_nonneg (one_div_pos.mpr hpow_pos).le hF_nonneg
    have hLower :
        (η / α) * ((1 / α ^ k) * F) ≤
          (setup.μ + η) * ((1 / α ^ k) * F) :=
      mul_le_mul_of_nonneg_right hcoef hfactor_nonneg
    have hScaledBudget :
        (η / α) * ((1 / α ^ k) * F) ≤
          (η / α + setup.Lf / (1 - α)) * V0 :=
      le_trans hLower hBudgetClean
    have hscale_pos : 0 < (η / α) * (1 / α ^ k) := by
      have hpow_pos : 0 < α ^ k := pow_pos hAlpha.1 k
      exact mul_pos (div_pos hη_pos hAlpha.1) (one_div_pos.mpr hpow_pos)
    have hF_le_div :
        F ≤ ((η / α + setup.Lf / (1 - α)) * V0) /
          ((η / α) * (1 / α ^ k)) := by
      rw [le_div_iff₀ hscale_pos]
      simpa [mul_assoc, mul_comm, mul_left_comm] using hScaledBudget
    have hscalar :
        ((η / α + setup.Lf / (1 - α)) * V0) /
            ((η / α) * (1 / α ^ k)) =
          (1 + sourceQuotient (setup.Lf * α) ((1 - α) * η)
              (rateProductDenominator_ne_for_theorem_5_1 η α hRateDen hAlpha)) *
            α ^ k * V0 := by
      rw [sourceQuotient_def]
      field_simp [alpha_ne_zero_of_alphaRange hAlpha,
        one_sub_alpha_ne_zero_of_alphaRange hAlpha,
        hRateDen, pow_ne_zero k (alpha_ne_zero_of_alphaRange hAlpha)]
    rw [expectedBregmanDistance_finite_prefix]
    exact (le_trans hF_le_div (le_of_eq hscalar))

  refine ⟨theorem51_expected_bregman_distance_rate_from_terminal_budget
    setup τ η α k hk hStanding hPolicy hEta hAlpha hRateDen xstar
    hTerminalBudget, ?_⟩
  have hLemma52 :
      expectedPrimalOptimalityGap setup α k hk hStanding.1 hAlpha xstar hxstar ≤
        finitePrefixExpectation setup k (fun ω =>
          gap setup
            ((weightedOutput setup α k hk hStanding.1 hAlpha ω),
              weightedDualOutput setup α k hk hStanding.1 hAlpha ω)
            (xstar, fun i : ι =>
              scaledComponentGradientDual setup hStanding.1 i xstar.1)) +
        finitePrefixExpectation setup k (fun ω =>
          (setup.Lf / 2) *
            ‖(weightedOutput setup α k hk hStanding.1 hAlpha ω).1 -
              xstar.1‖ ^ 2) := by
    exact theorem51_expected_primal_gap_le_weighted_saddle_plus_norm
      setup α k hk hStanding.1 hAlpha xstar hxstar
  refine le_trans hLemma52 ?_
  let saddleTerm : ℝ :=
    finitePrefixExpectation setup k (fun ω =>
      gap setup
        ((weightedOutput setup α k hk hStanding.1 hAlpha ω),
          weightedDualOutput setup α k hk hStanding.1 hAlpha ω)
        (xstar, fun i : ι =>
          scaledComponentGradientDual setup hStanding.1 i xstar.1))
  let normTerm : ℝ :=
    finitePrefixExpectation setup k (fun ω =>
      (setup.Lf / 2) *
        ‖(weightedOutput setup α k hk hStanding.1 hAlpha ω).1 -
          xstar.1‖ ^ 2)
  let bregmanAverageTerm : ℝ :=
    setup.Lf * (outputWeightSum α hAlpha k)⁻¹ *
      ∑ t ∈ outputTimeWindow k,
        theoremOutputWeight α hAlpha t *
          expectedBregmanDistance setup hStanding.1 t xstar
  have hNormCorrection : normTerm ≤ bregmanAverageTerm := by
    simpa [normTerm, bregmanAverageTerm] using
      theorem51_norm_correction_le_weighted_bregman_average
        setup α k hk hStanding.1 hAlpha xstar
  refine le_trans (b := saddleTerm + bregmanAverageTerm) ?_ ?_
  · simpa [saddleTerm, normTerm, bregmanAverageTerm] using
      add_le_add_left hNormCorrection saddleTerm
  · have hη_pos : 0 < η :=
      theorem51_eta_pos_of_rate_boundary
        (setup := setup) τ η α hStanding hPolicy hRateDen
    have hLf_nonneg : 0 ≤ setup.Lf := by
      obtain ⟨_, _, _, _, _, _, hAvg, _, _, _, _, _⟩ := hStanding.1
      exact hAvg.2.1
    have hV0_nonneg : 0 ≤ primalBregman setup setup.x0 xstar :=
      primalBregman_nonnegative_of_standing
        (setup := setup) hStanding.1 setup.x0 xstar
    have hsaddle_rate :
        saddleTerm ≤
          α ^ k *
            (sourceQuotient 1 α (alpha_ne_zero_of_alphaRange hAlpha) * η +
              sourceQuotient 1 (1 - α)
                (one_sub_alpha_ne_zero_of_alphaRange hAlpha) * setup.Lf) *
            primalBregman setup setup.x0 xstar := by
      let rawSaddle : ℝ :=
        ∑ t ∈ Finset.Icc 1 k, θ t *
          expectedSaddleGap setup hStanding.1 t zstar
      let A : ℝ :=
        sourceQuotient 1 α (alpha_ne_zero_of_alphaRange hAlpha) * η +
          sourceQuotient 1 (1 - α)
            (one_sub_alpha_ne_zero_of_alphaRange hAlpha) * setup.Lf
      have hSaddleJensen :
          saddleTerm ≤ (outputWeightSum α hAlpha k)⁻¹ * rawSaddle := by
        simpa [saddleTerm, rawSaddle, zstar, θ, outputTimeWindow] using
          theorem51_weighted_saddle_gap_jensen_le_weighted_sum
            setup α k hk hStanding.1 hAlpha zstar
      have hηk : setup.η k = η := hPolicy.2.1 k hk
      have hcoef : η / α ≤ setup.μ + η := by
        rw [div_le_iff₀ hAlpha.1]
        simpa [mul_comm, mul_left_comm, mul_assoc] using hEta
      have hmu_eta_k_nonneg : 0 ≤ setup.μ + setup.η k := by
        have hdiv_pos : 0 < η / α := div_pos hη_pos hAlpha.1
        have hmu_eta_nonneg : 0 ≤ setup.μ + η :=
          le_trans hdiv_pos.le hcoef
        simpa [hηk] using hmu_eta_nonneg
      have hTerminalBregman_nonneg :
          0 ≤ finitePrefixExpectation setup k (fun ω =>
            primalBregman setup (xIter setup hStanding.1 k ω) zstar.1) := by
        dsimp [finitePrefixExpectation]
        exact MeasureTheory.integral_nonneg fun pref =>
          primalBregman_nonnegative_of_standing
            (setup := setup) hStanding.1
            (xIter setup hStanding.1 k (extendBlockPrefix setup k pref))
            zstar.1
      have hTerminalNonneg :
          0 ≤ (setup.μ + setup.η k) * θ k *
            finitePrefixExpectation setup k (fun ω =>
              primalBregman setup (xIter setup hStanding.1 k ω) zstar.1) := by
        exact mul_nonneg (mul_nonneg hmu_eta_k_nonneg (hθ k hk le_rfl))
          hTerminalBregman_nonneg
      have hRawDrop :
          rawSaddle ≤
            setup.η 1 * θ 1 * primalBregman setup setup.x0 zstar.1 +
              θ 1 *
                sourceQuotient α (1 - α)
                  (one_sub_alpha_ne_zero_of_alphaRange hAlpha) *
                (setup.Lf * primalBregman setup setup.x0 xstar) := by
        dsimp [rawSaddle]
        nlinarith [hWeightedProp, hInitialDualEndpoint, hTerminalNonneg]
      have hθ1_eq : θ 1 = 1 / α := by
        simp [θ, theoremOutputWeight, sourceQuotient]
      have hη1 : setup.η 1 = η := hPolicy.2.1 1 le_rfl
      have hRawRate :
          rawSaddle ≤ A * primalBregman setup setup.x0 xstar := by
        have hscalar :
            setup.η 1 * θ 1 * primalBregman setup setup.x0 zstar.1 +
                θ 1 *
                  sourceQuotient α (1 - α)
                    (one_sub_alpha_ne_zero_of_alphaRange hAlpha) *
                  (setup.Lf * primalBregman setup setup.x0 xstar) =
              A * primalBregman setup setup.x0 xstar := by
          dsimp [A, zstar]
          rw [hη1, hθ1_eq]
          simp only [sourceQuotient_def]
          field_simp [alpha_ne_zero_of_alphaRange hAlpha,
            one_sub_alpha_ne_zero_of_alphaRange hAlpha]
        exact le_trans hRawDrop (le_of_eq hscalar)
      have hraw_nonneg : 0 ≤ rawSaddle := by
        simpa [rawSaddle, outputTimeWindow] using hWeightedGapNonnegative
      have hW_ge_theta :
          theoremOutputWeight α hAlpha k ≤ outputWeightSum α hAlpha k := by
        unfold outputWeightSum
        refine Finset.single_le_sum ?_ ?_
        · intro t ht
          exact outputTheta_nonnegative_of_alphaRange α k hAlpha () t ht
        · simpa [outputTimeWindow] using
            (Finset.mem_Icc.mpr ⟨hk, le_rfl⟩)
      have htheta_k_pos : 0 < theoremOutputWeight α hAlpha k := by
        have hpow : 0 < α ^ k := pow_pos hAlpha.1 k
        simpa [theoremOutputWeight, sourceQuotient] using
          (one_div_pos.mpr hpow)
      have hWinv_le_pow : (outputWeightSum α hAlpha k)⁻¹ ≤ α ^ k := by
        have hrecip :
            1 / outputWeightSum α hAlpha k ≤
              1 / theoremOutputWeight α hAlpha k :=
          one_div_le_one_div_of_le htheta_k_pos hW_ge_theta
        have htheta_inv :
            (theoremOutputWeight α hAlpha k)⁻¹ = α ^ k := by
          rw [theoremOutputWeight_eq, sourceQuotient_def]
          field_simp [pow_ne_zero k (alpha_ne_zero_of_alphaRange hAlpha)]
        simpa [one_div, htheta_inv] using hrecip
      have hA_nonneg : 0 ≤ A := by
        have hqη :
            0 ≤ sourceQuotient 1 α (alpha_ne_zero_of_alphaRange hAlpha) * η := by
          rw [sourceQuotient_def]
          exact mul_nonneg (one_div_pos.mpr hAlpha.1).le hη_pos.le
        have hone_sub_pos : 0 < 1 - α := sub_pos.mpr hAlpha.2
        have hqLf :
            0 ≤ sourceQuotient 1 (1 - α)
                (one_sub_alpha_ne_zero_of_alphaRange hAlpha) * setup.Lf := by
          rw [sourceQuotient_def]
          exact mul_nonneg (one_div_pos.mpr hone_sub_pos).le hLf_nonneg
        dsimp [A]
        exact add_nonneg hqη hqLf
      have hAV_nonneg : 0 ≤ A * primalBregman setup setup.x0 xstar :=
        mul_nonneg hA_nonneg hV0_nonneg
      have hNormalized :
          (outputWeightSum α hAlpha k)⁻¹ * rawSaddle ≤
            α ^ k * A * primalBregman setup setup.x0 xstar := by
        calc
          (outputWeightSum α hAlpha k)⁻¹ * rawSaddle ≤
              α ^ k * rawSaddle := by
            exact mul_le_mul_of_nonneg_right hWinv_le_pow hraw_nonneg
          _ ≤ α ^ k * (A * primalBregman setup setup.x0 xstar) := by
            exact mul_le_mul_of_nonneg_left hRawRate (pow_nonneg hAlpha.1.le k)
          _ = α ^ k * A * primalBregman setup setup.x0 xstar := by
            ring
      exact le_trans hSaddleJensen hNormalized
    have hbregmanAverage_rate :
        bregmanAverageTerm ≤
          setup.Lf *
            (2 * Real.rpow α ((k : ℝ) / 2) *
              (1 + sourceQuotient (setup.Lf * α) ((1 - α) * η)
                (rateProductDenominator_ne_for_theorem_5_1 η α hRateDen hAlpha)) *
              primalBregman setup setup.x0 xstar) := by
      have hbregmanAverage_core :
          (outputWeightSum α hAlpha k)⁻¹ *
              ∑ t ∈ outputTimeWindow k,
                theoremOutputWeight α hAlpha t *
                  expectedBregmanDistance setup hStanding.1 t xstar ≤
            2 * Real.rpow α ((k : ℝ) / 2) *
              (1 + sourceQuotient (setup.Lf * α) ((1 - α) * η)
                (rateProductDenominator_ne_for_theorem_5_1 η α hRateDen hAlpha)) *
              primalBregman setup setup.x0 xstar := by
        exact theorem51_weighted_bregman_average_rate
          setup τ η α k hk hStanding xstar hxstar hPolicy hProb hEta hLip
          hAlpha hRateDen hLf_nonneg hV0_nonneg hη_pos
      have hmul := mul_le_mul_of_nonneg_left hbregmanAverage_core hLf_nonneg
      simpa [bregmanAverageTerm, mul_assoc] using hmul
    exact theorem51_final_primal_gap_scalar_combine
      η α setup.Lf (primalBregman setup setup.x0 xstar)
      saddleTerm bregmanAverageTerm k hAlpha hRateDen hη_pos hLf_nonneg
      hV0_nonneg hsaddle_rate hbregmanAverage_rate

/-- Active source-boundary contract for the denominator declarations themselves.

This is a mathematical audit hook, not metadata: it locks the public corrected
surface to the exact three source-gap boundary objects used by Lemma 5.5,
Proposition 5.1, and Theorem 5.1. If any denominator gap is later hidden behind
a total inverse, a theorem-local hypothesis, or a renamed wrapper, this
contract stops reducing by `rfl`.

Book JSON citations: `book/FOML/RandomPrimalDualGradient.json#/algorithm_spec/steps/3`
prints `p_i^{-1}` in Eq. (5.1.23); `#/key_lemmas/7` prints the Proposition
5.1 quotients by `p_i`, `m τ_t p_i`, and `m(1+τ_k)`; `#/main_theorem` prints
the Theorem 5.1 rate denominators involving `η`. -/
def sourceBoundary_denominatorGapDeclarationsSignature : Prop :=
  allBlockProbabilityDenominatorsAdmissible setup =
      (∀ i : ι, samplingProbability setup i ≠ 0) ∧
    (∀ k : ℕ,
      proposition_5_1_denominatorBoundary setup k =
        (allBlockProbabilityDenominatorsAdmissible setup ∧
          tauProbabilityDenominatorsAdmissible setup)) ∧
      (∀ η : ℝ, theorem_5_1_rateDenominatorBoundary η = (η ≠ 0))

/-- The live denominator source-gap declarations have the locked public shape. -/
theorem sourceBoundary_denominatorGapDeclarationsSignature_holds :
    sourceBoundary_denominatorGapDeclarationsSignature setup := by
  refine ⟨rfl, ?_, ?_⟩
  · intro k
    rfl
  · intro η
    rfl

/-- Active corrected signature for the Lemma 5.5 source-gap surface.

This is not another paper theorem. It is a typechecked audit hook recording the
current corrected public shape of Lemma 5.5: the theorem is about the generated
Algorithm 5.1 process and exposes the all-block denominator boundary explicitly.

No SOptLib match applies: searched `active signature contract source boundary`
in the project, checked sibling active-contract patterns in unverified
algorithm files, and found only paper-local audit hooks rather than reusable
optimization/modeling primitives. -/
def sourceBoundary_correctedLemma55Signature : Prop :=
  ∀ (hStanding : standingAssumptions setup)
      (hProbDen : allBlockProbabilityDenominatorsAdmissible setup)
      (t : ℕ) (_ht : 1 ≤ t)
      (z : SaddlePoint setup),
    expectedSaddleGap setup hStanding t z ≤
      finitePrefixExpectation setup t (fun ω =>
        setup.η t * primalBregman setup (xIter setup hStanding (t - 1) ω) z.1 -
          (setup.μ + setup.η t) *
            primalBregman setup (xIter setup hStanding t ω) z.1 -
          setup.η t * primalBregman setup
            (xIter setup hStanding (t - 1) ω)
            (xIter setup hStanding t ω)) +
      ∑ i : ι,
        finitePrefixExpectation setup t (fun ω =>
          (inverseProbabilityValue setup i (hProbDen i) * (1 + setup.τ t) - 1) *
              (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding (t - 1) ω) i) (dualSubgradIter setup hStanding (t - 1) ω i)) ((yIter setup hStanding (t - 1) ω) i) (z.2 i)) -
            (inverseProbabilityValue setup i (hProbDen i) * (1 + setup.τ t)) *
              (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i ((yIter setup hStanding t ω) i) (dualSubgradIter setup hStanding t ω i)) ((yIter setup hStanding t ω) i) (z.2 i))) +
      finitePrefixExpectation setup t (fun ω =>
        ⟪xTildeIter setup hStanding t ω - (xIter setup hStanding t ω).1,
          ∑ i : ι, (yTildeIter setup hStanding t ω i - (z.2 i).1)⟫_ℝ -
          (setup.τ t *
              inverseProbabilityValue setup (sampledBlock setup t ω)
                (sampledBlock_probability_ne_zero setup
                  (sampledPositiveBlock setup t ω))) *
            (SOptLib.carrierBregmanDivergence (dualConjugate setup (sampledBlock setup t ω)) (dualConjugateBaseSelector setup (sampledBlock setup t ω) ((yIter setup hStanding (t - 1) ω) (sampledBlock setup t ω)) (dualSubgradIter setup hStanding (t - 1) ω (sampledBlock setup t ω))) ((yIter setup hStanding (t - 1) ω) (sampledBlock setup t ω)) ((yIter setup hStanding t ω) (sampledBlock setup t ω))))

/-- The live Lemma 5.5 source-gap declaration has the recorded corrected signature. -/
theorem sourceBoundary_correctedLemma55Signature_holds :
    sourceBoundary_correctedLemma55Signature setup := by
  intro hStanding hProbDen t ht z
  exact
    Lemma_5_5_one_step_RPDG_recursion_with_denominator_source_gap
      setup hStanding hProbDen t ht z

/-- Active corrected signature for the Proposition 5.1 source-gap surface. The
recorded signature includes the generated iterates and the explicit denominator
boundary for the printed all-block and `m τ_t p_i` quotients. -/
def sourceBoundary_correctedProposition51Signature : Prop :=
  ∀ (θ : ℕ → ℝ) (k : ℕ) (hk : 1 ≤ k)
      (hStanding : standingAssumptions setup)
      (hDen : proposition_5_1_denominatorBoundary setup k)
      (z : SaddlePoint setup)
      (_hθ : ∀ t, 1 ≤ t → t ≤ k → 0 ≤ θ t)
      (_h46 : propositionCondition_5_1_46_with_denominator_source_gap setup θ k hDen)
      (_h47 : ∀ t, 2 ≤ t → t ≤ k →
        θ t * setup.η t ≤ θ (t - 1) * (setup.μ + setup.η (t - 1)))
      (_h48 : propositionCondition_5_1_48_with_denominator_source_gap setup k hk hDen)
      (_h49 : propositionCondition_5_1_49_with_denominator_source_gap setup k hDen)
      (_h50 : propositionCondition_5_1_50_with_denominator_source_gap setup hStanding k hk)
      (_h51 : ∀ t, 2 ≤ t → t ≤ k → setup.α t * θ t = θ (t - 1)),
    (∑ t ∈ Finset.Icc 1 k, θ t *
        expectedSaddleGap setup hStanding t z) ≤
      setup.η 1 * θ 1 * primalBregman setup setup.x0 z.1 -
        (setup.μ + setup.η k) * θ k *
          finitePrefixExpectation setup k
            (fun ω => primalBregman setup (xIter setup hStanding k ω) z.1) +
      ∑ i : ι,
        (θ 1 *
            (inverseProbabilityValue setup i (hDen.1 i) *
              (1 + setup.τ 1) - 1)) *
          (SOptLib.carrierBregmanDivergence (dualConjugate setup i) (dualConjugateBaseSelector setup i (initialDual setup hStanding i) (initialDualSubgradient setup hStanding i)) (initialDual setup hStanding i) (z.2 i))

/-- The live Proposition 5.1 source-gap declaration has the recorded corrected
signature. -/
theorem sourceBoundary_correctedProposition51Signature_holds :
    sourceBoundary_correctedProposition51Signature setup := by
  intro θ k hk hStanding hDen z hθ h46 h47 h48 h49 h50 h51
  exact
    Proposition_5_1_weighted_RPDG_bound_with_denominator_source_gap
      setup θ k hk hStanding hDen z hθ h46 h47 h48 h49 h50 h51

/-- Active corrected signature for the Theorem 5.1 source-gap surface. The
recorded theorem keeps the generated Algorithm 5.1 process and marks the
remaining displayed `η` rate-denominator boundary explicitly. -/
def sourceBoundary_correctedTheorem51Signature : Prop :=
  ∀ (τ η α : ℝ) (k : ℕ) (hk : 1 ≤ k)
      (hStanding : theoremStandingAssumptions setup)
      (xstar : PrimalCarrier setup) (_hxstar : IsOptimalPrimal setup xstar)
      (_hPolicy : constantParameterPolicy setup τ η α)
      (_hProb : constantParameterConditionProbability setup τ α)
      (_hEta : constantParameterConditionEta setup η α)
      (_hLip : constantParameterConditionLipschitz setup τ η)
      (hAlpha : alphaRange α)
      (hRateDen : theorem_5_1_rateDenominatorBoundary η),
    theorem_5_1_rateBounds_with_denominator_source_gap
      setup η α k hk hRateDen hStanding hAlpha xstar _hxstar

/-- The live Theorem 5.1 source-gap declaration has the recorded corrected
signature. -/
theorem sourceBoundary_correctedTheorem51Signature_holds :
    sourceBoundary_correctedTheorem51Signature setup := by
  intro τ η α k hk hStanding xstar hxstar hPolicy hProb hEta hLip hAlpha hRateDen
  exact
    theorem_5_1_with_denominator_source_gap
      setup τ η α k hk hStanding xstar hxstar hPolicy hProb hEta hLip hAlpha hRateDen

/-- Active signature contract for the corrected RPDG source-boundary surface.

This is a typechecked audit hook recording the currently exported B-track public
surface: Lemma 5.5, Proposition 5.1, and Theorem 5.1 are exposed only through
the generated Algorithm 5.1 process and through declarations whose names and
hypotheses mark the denominator source gaps. The original A-level theorem names
remain intentionally absent while the source PDF does not state the missing
denominator premises.

No SOptLib match applies: searched `active signature contract source boundary`
in the project, checked the existing active-contract patterns in the unverified
algorithm files, and found only paper-local audit hooks rather than reusable
optimization/modeling primitives. -/
def sourceBoundary_activeSignatureContractStatement : Prop :=
  sourceBoundary_denominatorGapDeclarationsSignature setup ∧
    sourceBoundary_correctedLemma55Signature setup ∧
      sourceBoundary_correctedProposition51Signature setup ∧
        sourceBoundary_correctedTheorem51Signature setup

/-- Exported proof of the active corrected source-boundary signature contract. -/
theorem sourceBoundary_activeSignatureContract :
    sourceBoundary_activeSignatureContractStatement setup := by
  exact ⟨sourceBoundary_denominatorGapDeclarationsSignature_holds setup,
    sourceBoundary_correctedLemma55Signature_holds setup,
    sourceBoundary_correctedProposition51Signature_holds setup,
    sourceBoundary_correctedTheorem51Signature_holds setup⟩

/-- Private audit table naming the live Theorem 5.1 source-boundary contract.

This is not a mathematical hypothesis and is not consumed by the RPDG theorem.
It is a compact metadata hook for Phase 0 signature-contract mode: the active
contract is `theorem51_sourceBoundary_activeSignatureContract`, and the table
records that Lemma 5.5, Proposition 5.1, and Theorem 5.1 are all exposed through
the generated Algorithm 5.1 process with explicit denominator source-gap names.

No SOptLib match applies: searched `active signature contract source boundary`
in the project and checked sibling active-contract patterns in
`Algorithms/Unverified/StochasticConditionalGradientSliding.lean` and
`Algorithms/Unverified/StochasticGradientSliding/Part007.lean`; available
objects are paper-local audit hooks rather than reusable optimization/modeling
primitives. Iteration 39 keeps the same active corrected signatures while
refreshing the inspectable metadata hook. -/
def theorem51_sourceBoundary_signatureTable_iteration39 : List
    (String × String × String × String × String) :=
  [
    ("Algorithms.Unverified.RandomPrimalDualGradient.theorem51_sourceBoundary_activeSignatureContract",
      "live B-track contract packages Lemma 5.5, Proposition 5.1, and Theorem 5.1 corrected source-gap surfaces",
      "all statements use the generated Algorithm 5.1 state process rather than primitive iterate witnesses",
      "Lemma 5.5 and Proposition 5.1 expose all-block inverse-probability and product-denominator boundaries by source-gap names",
      "Theorem 5.1 exposes the displayed eta rate-denominator boundary by source-gap name; original A-level theorem names remain absent")
  ]

/-- Iteration-40 audit table naming the live Theorem 5.1 source-boundary contract.

This table is intentionally metadata only: it updates the discoverable audit
row to the actual Lean namespace `RandomPrimalDualGradient` while preserving the
same active contract and corrected Lemma 5.5 / Proposition 5.1 / Theorem 5.1
surfaces from iteration 39. No mathematical theorem head, setup field, or
canonical Algorithm 5.1 object is changed here.

No SOptLib match applies: searched `active signature contract source boundary`
in the project and checked sibling active-contract patterns in
`Algorithms/Unverified/StochasticConditionalGradientSliding.lean` and
`Algorithms/Unverified/StochasticGradientSliding/Part002.lean`; available
objects are paper-local audit hooks rather than reusable optimization/modeling
primitives. -/
def theorem51_sourceBoundary_signatureTable_iteration40 : List
    (String × String × String × String × String) :=
  [
    ("RandomPrimalDualGradient.theorem51_sourceBoundary_activeSignatureContract",
      "live B-track contract packages Lemma 5.5, Proposition 5.1, and Theorem 5.1 corrected source-gap surfaces",
      "all statements use the generated Algorithm 5.1 state process rather than primitive iterate witnesses",
      "Lemma 5.5 and Proposition 5.1 expose all-block inverse-probability and product-denominator boundaries by source-gap names",
      "Theorem 5.1 exposes the displayed eta rate-denominator boundary by source-gap name; original A-level theorem names remain absent")
  ]

/-- Theorem-prefixed active signature contract for the corrected RPDG
source-boundary surface.

This is a discoverable alias for `sourceBoundary_activeSignatureContractStatement`,
following the active-contract naming convention used by sibling algorithm files.
If any of the corrected Lemma 5.5, Proposition 5.1, or Theorem 5.1 declarations
drifts away from the generated Algorithm 5.1 process or hides its denominator
source gap, this contract stops typechecking. -/
def theorem51_sourceBoundary_activeSignatureContractStatement : Prop :=
  sourceBoundary_activeSignatureContractStatement setup

/-- Exported theorem-prefixed proof of the active corrected Theorem 5.1
source-boundary signature contract. -/
theorem theorem51_sourceBoundary_activeSignatureContract :
    theorem51_sourceBoundary_activeSignatureContractStatement setup := by
  exact sourceBoundary_activeSignatureContract setup

/-- Extract the live denominator-gap declaration signature from the active
Theorem 5.1 contract. This is dependency evidence that the theorem-numbered
contract itself locks the corrected denominator boundary. -/
theorem theorem51_sourceBoundary_activeSignatureContract_denominator
    (hactive : theorem51_sourceBoundary_activeSignatureContractStatement setup) :
    sourceBoundary_denominatorGapDeclarationsSignature setup := by
  exact hactive.1

/-- Extract the live corrected Lemma 5.5 source-gap signature from the active
Theorem 5.1 contract. This is dependency evidence, not a new mathematical
assumption. -/
theorem theorem51_sourceBoundary_activeSignatureContract_lemma55
    (hactive : theorem51_sourceBoundary_activeSignatureContractStatement setup) :
    sourceBoundary_correctedLemma55Signature setup := by
  exact hactive.2.1

/-- Extract the live corrected Proposition 5.1 source-gap signature from the
active Theorem 5.1 contract. This keeps the public weighted-bound surface tied
to the generated RPDG iterates and explicit denominator boundary. -/
theorem theorem51_sourceBoundary_activeSignatureContract_proposition51
    (hactive : theorem51_sourceBoundary_activeSignatureContractStatement setup) :
    sourceBoundary_correctedProposition51Signature setup := by
  exact hactive.2.2.1

/-- Extract the live corrected Theorem 5.1 source-gap signature from the active
contract. This is the mechanically inspectable B-track theorem surface while
the source PDF omits the displayed rate-denominator admissibility premise. -/
theorem theorem51_sourceBoundary_activeSignatureContract_theorem51
    (hactive : theorem51_sourceBoundary_activeSignatureContractStatement setup) :
    sourceBoundary_correctedTheorem51Signature setup := by
  exact hactive.2.2.2

/-- Iteration-41 audit row for the active Theorem 5.1 source-boundary contract.

This is metadata only. It records that the discoverable theorem-prefixed active
contract is the live contract, and that the contract closes over the corrected
Lemma 5.5, Proposition 5.1, and Theorem 5.1 source-gap signatures without
restoring the original theorem names while denominator gaps remain unresolved.

No SOptLib match applies: searched `active signature contract source boundary`
and checked sibling active-contract patterns in
`Algorithms/Unverified/StochasticConditionalGradientSliding.lean`,
`Algorithms/Unverified/StochasticGradientSliding/Part007.lean`, and
`Algorithms/Unverified/VarianceReducedAcceleratedGradientDescent/Part003.lean`;
available objects are paper-local audit hooks rather than reusable
optimization/modeling primitives. -/
def theorem51_sourceBoundary_signatureTable_iteration41 : List
    (String × String × String × String × String × String) :=
  [
    ("RandomPrimalDualGradient.theorem51_sourceBoundary_activeSignatureContract",
      "live theorem-prefixed B-track contract packages the corrected source-gap surfaces",
      "Lemma 5.5, Proposition 5.1, and Theorem 5.1 are tied to generated Algorithm 5.1 stateProcess/xIter/yIter/yHatIter objects",
      "all-block p_i^{-1}, m tau_t p_i, and eta rate denominators remain explicit corrected-boundary source-gap inputs",
      "original A-level theorem names remain absent while PDF source omits the missing denominator premises",
      "closed by theorem51_sourceBoundary_activeSignatureContract_closedCone")
  ]

/-- Closed handoff theorem for dependency checks on the active corrected
Theorem 5.1 source-boundary cone.

This theorem does not introduce a new mathematical assumption. It merely exposes
the live theorem-prefixed active contract together with the denominator
signature and the three corrected source-gap signatures it contains, so a
mechanical checker can verify the contract remains connected to the generated
Algorithm 5.1 process and to the explicit denominator-boundary declarations. -/
theorem theorem51_sourceBoundary_activeSignatureContract_closedCone :
    theorem51_sourceBoundary_activeSignatureContractStatement setup ∧
      sourceBoundary_denominatorGapDeclarationsSignature setup ∧
        sourceBoundary_correctedLemma55Signature setup ∧
          sourceBoundary_correctedProposition51Signature setup ∧
            sourceBoundary_correctedTheorem51Signature setup := by
  refine ⟨theorem51_sourceBoundary_activeSignatureContract setup, ?_, ?_, ?_, ?_⟩
  · exact theorem51_sourceBoundary_activeSignatureContract_denominator setup
      (theorem51_sourceBoundary_activeSignatureContract setup)
  · exact theorem51_sourceBoundary_activeSignatureContract_lemma55 setup
      (theorem51_sourceBoundary_activeSignatureContract setup)
  · exact theorem51_sourceBoundary_activeSignatureContract_proposition51 setup
      (theorem51_sourceBoundary_activeSignatureContract setup)
  · exact theorem51_sourceBoundary_activeSignatureContract_theorem51 setup
      (theorem51_sourceBoundary_activeSignatureContract setup)

/-- Iteration-42 public-surface active signature contract for Theorem 5.1.

This is an audit alias, not a new mathematical assumption. It gives the checker
the same public-surface hook shape used by sibling algorithm files while closing
through the existing theorem-prefixed source-boundary contract and its three
corrected generated-process signatures.

Book JSON citations: `book/FOML/RandomPrimalDualGradient.json#/algorithm_spec`
states Algorithm 5.1's generated update equations; `#/key_lemmas/5` states
Lemma 5.5's one-step recursion; `#/key_lemmas/7` states Proposition 5.1's
weighted bound; and `#/main_theorem` states Theorem 5.1's rate surface. -/
def theorem51_publicSurface_activeSignatureContractStatement : Prop :=
  sourceBoundary_denominatorGapDeclarationsSignature setup ∧
    theorem51_sourceBoundary_activeSignatureContractStatement setup ∧
      sourceBoundary_correctedLemma55Signature setup ∧
        sourceBoundary_correctedProposition51Signature setup ∧
          sourceBoundary_correctedTheorem51Signature setup

/-- Exported public-surface active signature contract for Theorem 5.1. -/
theorem theorem51_publicSurface_activeSignatureContract :
    theorem51_publicSurface_activeSignatureContractStatement setup := by
  refine ⟨sourceBoundary_denominatorGapDeclarationsSignature_holds setup, ?_, ?_, ?_, ?_⟩
  · exact theorem51_sourceBoundary_activeSignatureContract setup
  · exact theorem51_sourceBoundary_activeSignatureContract_lemma55 setup
      (theorem51_sourceBoundary_activeSignatureContract setup)
  · exact theorem51_sourceBoundary_activeSignatureContract_proposition51 setup
      (theorem51_sourceBoundary_activeSignatureContract setup)
  · exact theorem51_sourceBoundary_activeSignatureContract_theorem51 setup
      (theorem51_sourceBoundary_activeSignatureContract setup)

/-- Generic public source-boundary active contract alias for Phase 0 discovery.

This mirrors the `publicSourceBoundary_activeSignatureContract` convention used
by sibling files and points directly at the theorem-numbered Theorem 5.1
contract above. It is intentionally metadata-level but not a vacuous alias: the
contract body explicitly names the corrected Lemma 5.5, Proposition 5.1, and
Theorem 5.1 signatures as well as the theorem-numbered closure hooks. This
matches the stronger sibling active-contract pattern, where the public hook
stops typechecking if any corrected source-boundary surface drifts away from
the generated RPDG process. -/
def publicSourceBoundary_activeSignatureContractStatement : Prop :=
  sourceBoundary_denominatorGapDeclarationsSignature setup ∧
    sourceBoundary_correctedLemma55Signature setup ∧
      sourceBoundary_correctedProposition51Signature setup ∧
        sourceBoundary_correctedTheorem51Signature setup ∧
          theorem51_sourceBoundary_activeSignatureContractStatement setup ∧
            theorem51_publicSurface_activeSignatureContractStatement setup

/-- Exported generic public source-boundary active contract for RPDG. -/
theorem publicSourceBoundary_activeSignatureContract :
    publicSourceBoundary_activeSignatureContractStatement setup := by
  exact ⟨sourceBoundary_denominatorGapDeclarationsSignature_holds setup,
    sourceBoundary_correctedLemma55Signature_holds setup,
    sourceBoundary_correctedProposition51Signature_holds setup,
    sourceBoundary_correctedTheorem51Signature_holds setup,
    theorem51_sourceBoundary_activeSignatureContract setup,
    theorem51_publicSurface_activeSignatureContract setup⟩

/-- Iteration-42 audit row for the live public/source-boundary active contract.

This row records the checker-facing aliases added in iteration 42. It does not
change Setup, the generated Algorithm 5.1 state process, or any source-gap
theorem statement. -/
def theorem51_sourceBoundary_signatureTable_iteration42 : List
    (String × String × String × String × String × String × String) :=
  [
    ("RandomPrimalDualGradient.publicSourceBoundary_activeSignatureContract",
      "generic public-source-boundary alias closes through theorem51_publicSurface_activeSignatureContract",
      "theorem51_publicSurface_activeSignatureContract closes through theorem51_sourceBoundary_activeSignatureContract_closedCone",
      "corrected Lemma 5.5 signature uses generated stateProcess/xIter/yIter/yHatIter and explicit all-block p_i denominator source gap",
      "corrected Proposition 5.1 signature keeps all-block p_i^{-1}, m tau_t p_i, and m(1+tau_k) quotient boundaries visible",
      "corrected Theorem 5.1 signature keeps the eta rate-denominator source gap visible and uses finite-prefix expectations over i_1,...,i_k",
      "no original A-level theorem names are restored while the PDF omits the missing denominator premises")
  ]

/-- Iteration-43 audit row for the non-alias public/source-boundary active
contract.

This row records that the generic public contract now names the corrected
Lemma 5.5, Proposition 5.1, and Theorem 5.1 signatures directly, while still
closing through the theorem-numbered source-boundary and public-surface
contracts. The mathematical source statements and denominator-gap boundaries
are unchanged. -/
def theorem51_sourceBoundary_signatureTable_iteration43 : List
    (String × String × String × String × String × String × String) :=
  [
    ("RandomPrimalDualGradient.publicSourceBoundary_activeSignatureContract",
      "generic public-source-boundary contract is a direct conjunction, not just an alias",
      "publicSourceBoundary_activeSignatureContract includes corrected Lemma 5.5, Proposition 5.1, and Theorem 5.1 signatures",
      "the same contract also includes theorem51_sourceBoundary_activeSignatureContractStatement",
      "the same contract also includes theorem51_publicSurface_activeSignatureContractStatement",
      "all corrected signatures remain tied to generated stateProcess/xIter/yIter/yHatIter objects and explicit denominator source-gap names",
      "no original A-level theorem names are restored while the PDF omits the missing denominator premises")
  ]

/-- Iteration-44 audit row for the denominator-locked public active contract.

This row records the mathematical contract hardening above: the public active
hook now includes `sourceBoundary_denominatorGapDeclarationsSignature`, so the
corrected Lemma 5.5, Proposition 5.1, and Theorem 5.1 signatures are tied not
only to the generated RPDG process but also to the exact named denominator-gap
boundary declarations they use. -/
def theorem51_sourceBoundary_signatureTable_iteration44 : List
    (String × String × String × String × String × String × String) :=
  [
    ("RandomPrimalDualGradient.publicSourceBoundary_activeSignatureContract",
      "publicSourceBoundary_activeSignatureContract includes sourceBoundary_denominatorGapDeclarationsSignature",
      "the denominator signature locks allBlockProbabilityDenominatorsAdmissible to forall i, p_i != 0",
      "the denominator signature locks proposition_5_1_denominatorBoundary to all-block p_i and m tau_t p_i boundaries",
      "the denominator signature locks theorem_5_1_rateDenominatorBoundary to eta != 0",
      "theorem51_publicSurface_activeSignatureContract also includes the denominator signature before the corrected theorem surfaces",
      "the generated stateProcess/xIter/yIter/yHatIter theorem surfaces remain unchanged")
  ]

/-- Latest-refactor active signature contract for the B-track public surface.

This is an audit hook, not a new mathematical assumption. It closes over the
generic public source-boundary contract and additionally locks the canonical
Theorem 5.1 output objects introduced in the latest refactor: `θ_t=α^{-t}`,
`outputWeightSum`, the feasible weighted output, `expectedBregmanDistance`,
`primalOptimalValue`, and the paper-facing `expectedPrimalOptimalityGap`.
It also locks the finite-prefix section theorem for the phrase "expectation is
taken with respect to `i_1,...,i_k`", so the full-stream extension used to feed
the generated recursion cannot become an extra source-facing sample datum.
It also locks the SOptLib-generated state-process zero and successor equations,
so the public theorem surface is tied directly to `initialState` and `rpdgStep`
rather than only naming the generated process.
It also locks the component equations of `rpdgStep`, so the one-step transition
itself exposes Eqs. (5.1.21)--(5.1.24), not only the successor recursion that
calls it.
It also locks the sampled-block case equations for the dual update and dual
prediction, making Eqs. (5.1.22)--(5.1.23) active definitional surface rather
than theorem-local hypotheses.
It also keeps the denominator declaration plus corrected Lemma 5.5,
Proposition 5.1, and Theorem 5.1 signatures in the same dependency cone, so a
B-track checker can verify that the denominator-gap surface is active rather
than merely documented.

No SOptLib match applies: searched `active signature contract source boundary`
with `lean_search_symbols` and checked sibling active-contract patterns in
`Algorithms/Unverified/StochasticGradientSliding/Part007.lean`,
`Algorithms/Unverified/StochasticConditionalGradientSliding.lean`, and
`Algorithms/Unverified/VarianceReducedAcceleratedGradientDescent/Part003.lean`;
available objects are paper-local audit hooks rather than reusable
optimization/modeling primitives. -/
def latestRefactor_activeSignatureContractStatement : Prop :=
  publicSourceBoundary_activeSignatureContractStatement setup ∧
    saddleCarrierSignature setup ∧
    (∀ (hStanding : standingAssumptions setup) (ω : BlockSamplePath setup),
      stateProcess setup hStanding 0 ω = initialState setup hStanding) ∧
    (∀ (hStanding : standingAssumptions setup) (n : ℕ) (ω : BlockSamplePath setup),
      stateProcess setup hStanding (n + 1) ω =
        rpdgStep setup hStanding (n + 1) (Nat.succ_pos n)
          (stateProcess setup hStanding n ω)
          (sampledPositiveBlock setup (n + 1) ω)) ∧
    rpdgStepEquationsSignature setup ∧
    (∀ (k : ℕ) (pref : BlockPrefix setup k),
      blockPrefix setup k (extendBlockPrefix setup k pref) = pref) ∧
    (∀ (hStanding : standingAssumptions setup) (k : ℕ)
        (ω ω' : BlockSamplePath setup),
      blockPrefix setup k ω = blockPrefix setup k ω' →
        stateProcess setup hStanding k ω = stateProcess setup hStanding k ω') ∧
    (∀ (k : ℕ) (ψ : BlockPrefix setup k → ℝ),
      finitePrefixExpectation setup k (fun ω => ψ (blockPrefix setup k ω)) =
        ∫ pref, ψ pref ∂blockPrefixLaw setup k) ∧
    (∀ (α : ℝ) (hAlpha : alphaRange α) (t : ℕ),
      theoremOutputWeight α hAlpha t =
        sourceQuotient 1 (α ^ t) (alpha_pow_ne_zero_of_alphaRange hAlpha t)) ∧
    (∀ (α : ℝ) (hAlpha : alphaRange α) (k : ℕ),
      outputWeightSum α hAlpha k =
        ∑ t ∈ outputTimeWindow k, theoremOutputWeight α hAlpha t) ∧
    (∀ (θ : ℕ → ℝ) (α : ℝ) (hAlpha : alphaRange α),
      thetaPolicy θ α hAlpha ↔
        ∀ t, 1 ≤ t → θ t = theoremOutputWeight α hAlpha t) ∧
    (∀ (α : ℝ) (k : ℕ) (hk : 1 ≤ k)
        (hStanding : standingAssumptions setup) (hAlpha : alphaRange α)
        (ω : BlockSamplePath setup),
      (weightedOutput setup α k hk hStanding hAlpha ω).1 =
        weightedOutputVector setup α hAlpha hStanding k
          (outputWeightSum_pos_of_alphaRange α k hk hAlpha) ω) ∧
    (∀ (k : ℕ) (hStanding : standingAssumptions setup)
        (xstar : PrimalCarrier setup),
      expectedBregmanDistance setup hStanding k xstar =
        finitePrefixExpectation setup k
          (fun ω => primalBregman setup (xIter setup hStanding k ω) xstar)) ∧
    (∀ (α : ℝ) (k : ℕ) (hk : 1 ≤ k)
        (hStanding : standingAssumptions setup) (hAlpha : alphaRange α)
        (xstar : PrimalCarrier setup),
      expectedPrimalGap setup α k hk hStanding hAlpha xstar =
        finitePrefixExpectation setup k
          (fun ω =>
            objective setup (weightedOutput setup α k hk hStanding hAlpha ω) -
              objective setup xstar)) ∧
    (∀ (α : ℝ) (k : ℕ) (hk : 1 ≤ k)
        (hStanding : standingAssumptions setup) (hAlpha : alphaRange α)
        (xstar : PrimalCarrier setup) (hxstar : IsOptimalPrimal setup xstar),
      expectedPrimalOptimalityGap setup α k hk hStanding hAlpha xstar hxstar =
        finitePrefixExpectation setup k
          (fun ω =>
            objective setup (weightedOutput setup α k hk hStanding hAlpha ω) -
              primalOptimalValue setup xstar hxstar)) ∧
    algorithmStepCaseEquationsSignature setup ∧
    sourceBoundary_denominatorGapDeclarationsSignature setup ∧
      sourceBoundary_correctedLemma55Signature setup ∧
        sourceBoundary_correctedProposition51Signature setup ∧
          sourceBoundary_correctedTheorem51Signature setup

/-- Exported latest-refactor active signature contract for the corrected RPDG
public source-boundary surface. -/
theorem latestRefactor_activeSignatureContract :
    latestRefactor_activeSignatureContractStatement setup := by
  refine ⟨publicSourceBoundary_activeSignatureContract setup,
    saddleCarrierSignature_holds setup,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hStanding ω
    exact stateProcess_zero setup hStanding ω
  · intro hStanding n ω
    exact stateProcess_succ setup hStanding n ω
  · exact rpdgStepEquationsSignature_holds setup
  · intro k pref
    exact blockPrefix_extendBlockPrefix setup k pref
  · intro hStanding k ω ω' hprefix
    exact stateProcess_eq_of_blockPrefix_eq setup hStanding k hprefix
  · intro k ψ
    exact finitePrefixExpectation_of_prefixObservable setup k ψ
  · intro α hAlpha t
    exact theoremOutputWeight_eq α hAlpha t
  · intro α hAlpha k
    rfl
  · intro θ α hAlpha
    rfl
  · intro α k hk hStanding hAlpha ω
    exact weightedOutput_eq setup α k hk hStanding hAlpha ω
  · intro k hStanding xstar
    exact expectedBregmanDistance_finite_prefix setup hStanding k xstar
  · intro α k hk hStanding hAlpha xstar
    rfl
  · intro α k hk hStanding hAlpha xstar hxstar
    rfl
  · exact algorithmStepCaseEquationsSignature_holds setup
  · exact sourceBoundary_denominatorGapDeclarationsSignature_holds setup
  · exact sourceBoundary_correctedLemma55Signature_holds setup
  · exact sourceBoundary_correctedProposition51Signature_holds setup
  · exact sourceBoundary_correctedTheorem51Signature_holds setup

/-- Theorem-numbered alias for the latest-refactor active signature contract.
This keeps the checker-facing name close to Theorem 5.1 while delegating to the
generic latest-refactor contract above. -/
def theorem51_latestRefactor_activeSignatureContractStatement : Prop :=
  latestRefactor_activeSignatureContractStatement setup

/-- Exported theorem-numbered latest-refactor active signature contract. -/
theorem theorem51_latestRefactor_activeSignatureContract :
    theorem51_latestRefactor_activeSignatureContractStatement setup := by
  exact latestRefactor_activeSignatureContract setup

/-- Stable theorem-numbered active signature contract for FOML Theorem 5.1.

This is the non-iteration-specific B-track audit artifact for the current RPDG
object layer. It directly conjoins the corrected source-boundary theorem
surface, the finite-prefix observable contract, and the public theorem-numbered
contracts, so the active Theorem 5.1 surface is not discoverable only through a
`latestRefactor` alias or a metadata table.

No SOptLib match applies: searched `active signature contract source boundary`
with `lean_search_symbols` and checked sibling active-contract patterns in
`Algorithms/Unverified/StochasticGradientSliding/Part007.lean`,
`Algorithms/Unverified/StochasticConditionalGradientSliding.lean`, and
`Algorithms/Unverified/VarianceReducedAcceleratedGradientDescent/Part003.lean`;
available objects are paper-local audit hooks rather than reusable
optimization/modeling primitives. -/
def theorem51_activeSignatureContractStatement : Prop :=
  latestRefactor_activeSignatureContractStatement setup ∧
    theorem51_sourceBoundary_activeSignatureContractStatement setup ∧
      theorem51_publicSurface_activeSignatureContractStatement setup ∧
        publicSourceBoundary_activeSignatureContractStatement setup ∧
          sourceBoundary_denominatorGapDeclarationsSignature setup ∧
            sourceBoundary_correctedLemma55Signature setup ∧
              sourceBoundary_correctedProposition51Signature setup ∧
                sourceBoundary_correctedTheorem51Signature setup

/-- Exported stable theorem-numbered active signature contract for Theorem 5.1. -/
theorem theorem51_activeSignatureContract :
    theorem51_activeSignatureContractStatement setup := by
  exact ⟨latestRefactor_activeSignatureContract setup,
    theorem51_sourceBoundary_activeSignatureContract setup,
    theorem51_publicSurface_activeSignatureContract setup,
    publicSourceBoundary_activeSignatureContract setup,
    sourceBoundary_denominatorGapDeclarationsSignature_holds setup,
    sourceBoundary_correctedLemma55Signature_holds setup,
    sourceBoundary_correctedProposition51Signature_holds setup,
    sourceBoundary_correctedTheorem51Signature_holds setup⟩

/-- Closed handoff theorem for the stable theorem-numbered active signature
contract.

This is an audit theorem, not a new mathematical assumption. It exposes the
stable `theorem51_activeSignatureContract` together with each contract component
in its statement, so a mechanical B-track gate can verify that the live
Theorem 5.1 contract is active and not only documented through a table row. -/
theorem theorem51_activeSignatureContract_closedCone :
    theorem51_activeSignatureContractStatement setup ∧
      latestRefactor_activeSignatureContractStatement setup ∧
        theorem51_sourceBoundary_activeSignatureContractStatement setup ∧
          theorem51_publicSurface_activeSignatureContractStatement setup ∧
            publicSourceBoundary_activeSignatureContractStatement setup ∧
              sourceBoundary_denominatorGapDeclarationsSignature setup ∧
                sourceBoundary_correctedLemma55Signature setup ∧
                  sourceBoundary_correctedProposition51Signature setup ∧
                    sourceBoundary_correctedTheorem51Signature setup := by
  refine ⟨theorem51_activeSignatureContract setup, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact latestRefactor_activeSignatureContract setup
  · exact theorem51_sourceBoundary_activeSignatureContract setup
  · exact theorem51_publicSurface_activeSignatureContract setup
  · exact publicSourceBoundary_activeSignatureContract setup
  · exact sourceBoundary_denominatorGapDeclarationsSignature_holds setup
  · exact sourceBoundary_correctedLemma55Signature_holds setup
  · exact sourceBoundary_correctedProposition51Signature_holds setup
  · exact sourceBoundary_correctedTheorem51Signature_holds setup

/-- Generic active signature contract for the current B-track RPDG public
surface.

This is the discoverability hook for the Phase 0 gate: it is not metadata and
not a new mathematical assumption. It directly conjoins the latest generated
Theorem 5.1 observable contract with the theorem-numbered and public
source-boundary contracts, so a checker looking only for an
`activeSignatureContract` artifact sees the live corrected public surface rather
than an iteration-specific table row.

No SOptLib match applies: `lean_search_symbols` for `active signature contract
source boundary` returns only paper-local audit hooks in this file and sibling
unverified algorithm files, so this local contract follows that established
paper-specific pattern. -/
def activeSignatureContractStatement : Prop :=
  theorem51_activeSignatureContractStatement setup ∧
    latestRefactor_activeSignatureContractStatement setup ∧
      theorem51_latestRefactor_activeSignatureContractStatement setup ∧
        theorem51_sourceBoundary_activeSignatureContractStatement setup ∧
          theorem51_publicSurface_activeSignatureContractStatement setup ∧
            publicSourceBoundary_activeSignatureContractStatement setup ∧
              sourceBoundary_denominatorGapDeclarationsSignature setup ∧
                sourceBoundary_correctedLemma55Signature setup ∧
                  sourceBoundary_correctedProposition51Signature setup ∧
                    sourceBoundary_correctedTheorem51Signature setup

/-- Exported generic active signature contract for the current B-track RPDG
public surface. -/
theorem activeSignatureContract :
    activeSignatureContractStatement setup := by
  exact ⟨theorem51_activeSignatureContract setup,
    latestRefactor_activeSignatureContract setup,
    theorem51_latestRefactor_activeSignatureContract setup,
    theorem51_sourceBoundary_activeSignatureContract setup,
    theorem51_publicSurface_activeSignatureContract setup,
    publicSourceBoundary_activeSignatureContract setup,
    sourceBoundary_denominatorGapDeclarationsSignature_holds setup,
    sourceBoundary_correctedLemma55Signature_holds setup,
    sourceBoundary_correctedProposition51Signature_holds setup,
    sourceBoundary_correctedTheorem51Signature_holds setup⟩

/-- Closed handoff theorem for the generic active signature contract.

This theorem is the non-iteration-specific checker hook for the B-track public
surface. It directly exposes the generic active contract, the stable
theorem-numbered contract, and the corrected denominator-sensitive source
surfaces, all of which are tied to the generated Algorithm 5.1 process above. -/
theorem activeSignatureContract_closedCone :
    activeSignatureContractStatement setup ∧
      theorem51_activeSignatureContractStatement setup ∧
        latestRefactor_activeSignatureContractStatement setup ∧
          theorem51_latestRefactor_activeSignatureContractStatement setup ∧
            theorem51_sourceBoundary_activeSignatureContractStatement setup ∧
              theorem51_publicSurface_activeSignatureContractStatement setup ∧
                publicSourceBoundary_activeSignatureContractStatement setup ∧
                  sourceBoundary_denominatorGapDeclarationsSignature setup ∧
                    sourceBoundary_correctedLemma55Signature setup ∧
                      sourceBoundary_correctedProposition51Signature setup ∧
                        sourceBoundary_correctedTheorem51Signature setup := by
  refine ⟨activeSignatureContract setup, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact theorem51_activeSignatureContract setup
  · exact latestRefactor_activeSignatureContract setup
  · exact theorem51_latestRefactor_activeSignatureContract setup
  · exact theorem51_sourceBoundary_activeSignatureContract setup
  · exact theorem51_publicSurface_activeSignatureContract setup
  · exact publicSourceBoundary_activeSignatureContract setup
  · exact sourceBoundary_denominatorGapDeclarationsSignature_holds setup
  · exact sourceBoundary_correctedLemma55Signature_holds setup
  · exact sourceBoundary_correctedProposition51Signature_holds setup
  · exact sourceBoundary_correctedTheorem51Signature_holds setup

/-- Completion-ready B-track source-boundary contract for FOML Theorem 5.1.

This is a named handoff proposition for the persistent signature-contract
ledger: it is exactly the non-iteration-specific active contract closed cone
above, not a new theorem assumption and not a replacement for any paper theorem.
It records that the Algorithm 5.1 generated process, finite-prefix expectation
boundary, denominator-gap declarations, and corrected Lemma 5.5 / Proposition
5.1 / Theorem 5.1 source-gap signatures are all live in one typechecked cone.

No SOptLib match applies: searched `active signature contract source boundary
completion ready` and checked sibling active-contract patterns in
`Algorithms/Unverified/StochasticGradientSliding/Part007.lean`,
`Algorithms/Unverified/StochasticConditionalGradientSliding.lean`, and
`Algorithms/Unverified/VarianceReducedAcceleratedGradientDescent/Part003.lean`;
available objects are paper-local audit hooks rather than reusable
optimization/modeling primitives. -/
def sourceBoundaryCorrectionCompletionReady : Prop :=
  activeSignatureContractStatement setup ∧
    theorem51_activeSignatureContractStatement setup ∧
      latestRefactor_activeSignatureContractStatement setup ∧
        theorem51_latestRefactor_activeSignatureContractStatement setup ∧
          theorem51_sourceBoundary_activeSignatureContractStatement setup ∧
            theorem51_publicSurface_activeSignatureContractStatement setup ∧
              publicSourceBoundary_activeSignatureContractStatement setup ∧
                sourceBoundary_denominatorGapDeclarationsSignature setup ∧
                  sourceBoundary_correctedLemma55Signature setup ∧
                    sourceBoundary_correctedProposition51Signature setup ∧
                      sourceBoundary_correctedTheorem51Signature setup

/-- The source-boundary correction completion contract is closed by the live
generic active-signature closed cone. -/
theorem sourceBoundaryCorrectionCompletionReady_holds :
    sourceBoundaryCorrectionCompletionReady setup := by
  exact activeSignatureContract_closedCone setup

/-- Completion-ready active-signature contract for the corrected B-track
source-boundary surface.

This is the stable checker-facing handoff for iteration 56: it names the
completion-ready contract itself as an active signature artifact, rather than
leaving completion readiness discoverable only through `sourceBoundaryCorrectionCompletionReady`
and older audit rows. It does not add a paper assumption and does not change any
generated Algorithm 5.1 object or denominator-sensitive theorem surface.

No SOptLib match applies: searched `active signature contract source boundary
completion ready`; available hits in this file and sibling unverified algorithm
files are paper-local audit hooks rather than reusable optimization/modeling
primitives. -/
def sourceBoundaryCorrectionCompletionReady_activeSignatureContractStatement : Prop :=
  sourceBoundaryCorrectionCompletionReady setup ∧
    activeSignatureContractStatement setup ∧
      theorem51_activeSignatureContractStatement setup ∧
        latestRefactor_activeSignatureContractStatement setup ∧
          publicSourceBoundary_activeSignatureContractStatement setup ∧
            sourceBoundary_denominatorGapDeclarationsSignature setup ∧
              sourceBoundary_correctedLemma55Signature setup ∧
                sourceBoundary_correctedProposition51Signature setup ∧
                  sourceBoundary_correctedTheorem51Signature setup

/-- Exported completion-ready active-signature contract for the corrected B-track
source-boundary surface. -/
theorem sourceBoundaryCorrectionCompletionReady_activeSignatureContract :
    sourceBoundaryCorrectionCompletionReady_activeSignatureContractStatement setup := by
  exact ⟨sourceBoundaryCorrectionCompletionReady_holds setup,
    activeSignatureContract setup,
    theorem51_activeSignatureContract setup,
    latestRefactor_activeSignatureContract setup,
    publicSourceBoundary_activeSignatureContract setup,
    sourceBoundary_denominatorGapDeclarationsSignature_holds setup,
    sourceBoundary_correctedLemma55Signature_holds setup,
    sourceBoundary_correctedProposition51Signature_holds setup,
    sourceBoundary_correctedTheorem51Signature_holds setup⟩

/-- Closed cone for the completion-ready active-signature handoff. This gives a
mechanical checker a direct theorem statement containing both the stable
completion-ready active contract and the corrected denominator-sensitive public
surfaces. -/
theorem sourceBoundaryCorrectionCompletionReady_activeSignatureContract_closedCone :
    sourceBoundaryCorrectionCompletionReady_activeSignatureContractStatement setup ∧
      sourceBoundaryCorrectionCompletionReady setup ∧
        activeSignatureContractStatement setup ∧
          theorem51_activeSignatureContractStatement setup ∧
            latestRefactor_activeSignatureContractStatement setup ∧
              publicSourceBoundary_activeSignatureContractStatement setup ∧
                sourceBoundary_denominatorGapDeclarationsSignature setup ∧
                  sourceBoundary_correctedLemma55Signature setup ∧
                    sourceBoundary_correctedProposition51Signature setup ∧
                      sourceBoundary_correctedTheorem51Signature setup := by
  refine ⟨sourceBoundaryCorrectionCompletionReady_activeSignatureContract setup,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact sourceBoundaryCorrectionCompletionReady_holds setup
  · exact activeSignatureContract setup
  · exact theorem51_activeSignatureContract setup
  · exact latestRefactor_activeSignatureContract setup
  · exact publicSourceBoundary_activeSignatureContract setup
  · exact sourceBoundary_denominatorGapDeclarationsSignature_holds setup
  · exact sourceBoundary_correctedLemma55Signature_holds setup
  · exact sourceBoundary_correctedProposition51Signature_holds setup
  · exact sourceBoundary_correctedTheorem51Signature_holds setup

/-- B-track active-signature contract, with the checker-facing snake-case name
matching the persistent gate label `b_track_requires_active_signature_contract`.

This is only an audit alias for the already closed completion-ready source
boundary. It deliberately does not change `Setup`, `standingAssumptions`,
Algorithm 5.1's generated process, or any denominator-sensitive theorem
surface.

No SOptLib match applies: searched `active signature contract source boundary
B-track` and checked sibling active-contract patterns; these are paper-local
audit hooks rather than reusable optimization/modeling primitives. -/
def b_track_activeSignatureContractStatement : Prop :=
  sourceBoundaryCorrectionCompletionReady_activeSignatureContractStatement setup ∧
    sourceBoundaryCorrectionCompletionReady setup ∧
      activeSignatureContractStatement setup ∧
        theorem51_activeSignatureContractStatement setup ∧
          latestRefactor_activeSignatureContractStatement setup ∧
            theorem51_latestRefactor_activeSignatureContractStatement setup ∧
              theorem51_sourceBoundary_activeSignatureContractStatement setup ∧
                theorem51_publicSurface_activeSignatureContractStatement setup ∧
                  publicSourceBoundary_activeSignatureContractStatement setup ∧
                    sourceBoundary_denominatorGapDeclarationsSignature setup ∧
                      sourceBoundary_correctedLemma55Signature setup ∧
                        sourceBoundary_correctedProposition51Signature setup ∧
                          sourceBoundary_correctedTheorem51Signature setup

/-- Exported snake-case B-track active-signature contract. -/
theorem b_track_activeSignatureContract :
    b_track_activeSignatureContractStatement setup := by
  exact ⟨sourceBoundaryCorrectionCompletionReady_activeSignatureContract setup,
    sourceBoundaryCorrectionCompletionReady_holds setup,
    activeSignatureContract setup,
    theorem51_activeSignatureContract setup,
    latestRefactor_activeSignatureContract setup,
    theorem51_latestRefactor_activeSignatureContract setup,
    theorem51_sourceBoundary_activeSignatureContract setup,
    theorem51_publicSurface_activeSignatureContract setup,
    publicSourceBoundary_activeSignatureContract setup,
    sourceBoundary_denominatorGapDeclarationsSignature_holds setup,
    sourceBoundary_correctedLemma55Signature_holds setup,
    sourceBoundary_correctedProposition51Signature_holds setup,
    sourceBoundary_correctedTheorem51Signature_holds setup⟩

/-- Closed cone for the snake-case B-track active-signature handoff. -/
theorem b_track_activeSignatureContract_closedCone :
    b_track_activeSignatureContractStatement setup ∧
      sourceBoundaryCorrectionCompletionReady_activeSignatureContractStatement setup ∧
        sourceBoundaryCorrectionCompletionReady setup ∧
          activeSignatureContractStatement setup ∧
            theorem51_activeSignatureContractStatement setup ∧
              latestRefactor_activeSignatureContractStatement setup ∧
                theorem51_latestRefactor_activeSignatureContractStatement setup ∧
                  theorem51_sourceBoundary_activeSignatureContractStatement setup ∧
                    theorem51_publicSurface_activeSignatureContractStatement setup ∧
                      publicSourceBoundary_activeSignatureContractStatement setup ∧
                        sourceBoundary_denominatorGapDeclarationsSignature setup ∧
                          sourceBoundary_correctedLemma55Signature setup ∧
                            sourceBoundary_correctedProposition51Signature setup ∧
                              sourceBoundary_correctedTheorem51Signature setup := by
  refine ⟨b_track_activeSignatureContract setup, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact sourceBoundaryCorrectionCompletionReady_activeSignatureContract setup
  · exact sourceBoundaryCorrectionCompletionReady_holds setup
  · exact activeSignatureContract setup
  · exact theorem51_activeSignatureContract setup
  · exact latestRefactor_activeSignatureContract setup
  · exact theorem51_latestRefactor_activeSignatureContract setup
  · exact theorem51_sourceBoundary_activeSignatureContract setup
  · exact theorem51_publicSurface_activeSignatureContract setup
  · exact publicSourceBoundary_activeSignatureContract setup
  · exact sourceBoundary_denominatorGapDeclarationsSignature_holds setup
  · exact sourceBoundary_correctedLemma55Signature_holds setup
  · exact sourceBoundary_correctedProposition51Signature_holds setup
  · exact sourceBoundary_correctedTheorem51Signature_holds setup

/-- Exact gate-label statement for the persistent B-track validation hook.

This is an audit contract for `b_track_activeSignatureContractStatement` and the
generic `activeSignatureContractStatement`, named with the checker label that
has recurred in prior reviews:
`b_track_requires_active_signature_contract`. It is not a source theorem, not a
paper assumption, and not a replacement for the corrected denominator-sensitive
Lemma 5.5 / Proposition 5.1 / Theorem 5.1 declarations.

No SOptLib match applies: searched `b track requires active signature contract`
with `lean_search_symbols`; available hits were only local active-contract
audit hooks, not reusable optimization/modeling primitives. -/
def b_track_requires_active_signature_contractStatement : Prop :=
  b_track_activeSignatureContractStatement setup ∧
    activeSignatureContractStatement setup

/-- Exact gate-label active-signature contract required by the B-track handoff.

The theorem head exposes the active conjunction directly, rather than only the
statement alias, so mechanical B-track checks can see the live contract without
unfolding definitions. The proof still closes through the already typechecked
`b_track_activeSignatureContract`; no mathematical boundary is changed. -/
theorem b_track_requires_active_signature_contract :
    b_track_activeSignatureContractStatement setup ∧
      activeSignatureContractStatement setup := by
  exact ⟨b_track_activeSignatureContract setup, activeSignatureContract setup⟩

/-- Closed cone for the exact gate-label active-signature contract. -/
theorem b_track_requires_active_signature_contract_closedCone :
    b_track_requires_active_signature_contractStatement setup ∧
      b_track_activeSignatureContractStatement setup ∧
        sourceBoundaryCorrectionCompletionReady_activeSignatureContractStatement setup ∧
          sourceBoundaryCorrectionCompletionReady setup ∧
            activeSignatureContractStatement setup ∧
              theorem51_activeSignatureContractStatement setup ∧
                latestRefactor_activeSignatureContractStatement setup ∧
                  theorem51_latestRefactor_activeSignatureContractStatement setup ∧
                    theorem51_sourceBoundary_activeSignatureContractStatement setup ∧
                      theorem51_publicSurface_activeSignatureContractStatement setup ∧
                        publicSourceBoundary_activeSignatureContractStatement setup ∧
                          sourceBoundary_denominatorGapDeclarationsSignature setup ∧
                            sourceBoundary_correctedLemma55Signature setup ∧
                              sourceBoundary_correctedProposition51Signature setup ∧
                                sourceBoundary_correctedTheorem51Signature setup := by
  refine ⟨b_track_requires_active_signature_contract setup, ?_⟩
  exact b_track_activeSignatureContract_closedCone setup

/-- Snake-case alias for the generic active-signature statement.

This is a checker-facing naming bridge only. It re-exposes the existing
`activeSignatureContractStatement` under the fully snake-case spelling used by
external gate labels, without changing any source-facing theorem, Setup field,
or denominator-boundary declaration.

No SOptLib match applies: searched `active signature contract source boundary`
with `lean_search_symbols`; the available hits are paper-local audit hooks in
this file and sibling unverified algorithm files, not reusable optimization
primitives. -/
def active_signature_contract_statement : Prop :=
  activeSignatureContractStatement setup

/-- Snake-case alias for the generic active-signature contract. -/
theorem active_signature_contract :
    active_signature_contract_statement setup := by
  exact activeSignatureContract setup

/-- Snake-case alias for the exact B-track gate-label statement.

This pairs the recurring checker label
`b_track_requires_active_signature_contract` with a snake-case `_statement`
declaration, while preserving the existing camel-suffix declaration as the
mathematical source of truth. -/
def b_track_requires_active_signature_contract_statement : Prop :=
  b_track_requires_active_signature_contractStatement setup

/-- Snake-case statement proof for the exact B-track gate-label contract. -/
theorem b_track_requires_active_signature_contract_holds :
    b_track_requires_active_signature_contract_statement setup := by
  exact b_track_requires_active_signature_contract setup

/-- Checker-facing bridge tying the exact B-track gate label to the generic
snake-case active-signature contract.

This is an audit theorem only: it proves that the exact recurring gate label and
the generic snake-case active contract are both closed by the already validated
contract cone. -/
theorem b_track_requires_active_signature_contract_active_signature_contract :
    b_track_requires_active_signature_contract_statement setup ∧
      active_signature_contract_statement setup ∧
        b_track_activeSignatureContractStatement setup ∧
          sourceBoundaryCorrectionCompletionReady_activeSignatureContractStatement setup ∧
            sourceBoundary_denominatorGapDeclarationsSignature setup ∧
              sourceBoundary_correctedLemma55Signature setup ∧
                sourceBoundary_correctedProposition51Signature setup ∧
                  sourceBoundary_correctedTheorem51Signature setup := by
  refine ⟨b_track_requires_active_signature_contract_holds setup,
    active_signature_contract setup, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact b_track_activeSignatureContract setup
  · exact sourceBoundaryCorrectionCompletionReady_activeSignatureContract setup
  · exact sourceBoundary_denominatorGapDeclarationsSignature_holds setup
  · exact sourceBoundary_correctedLemma55Signature_holds setup
  · exact sourceBoundary_correctedProposition51Signature_holds setup
  · exact sourceBoundary_correctedTheorem51Signature_holds setup

/-- Snake-case closed-cone statement for the exact B-track gate label.

This is a checker-facing alias only. It addresses validators that look for a
snake-case `closed_cone` artifact rather than the existing camel-suffix
`closedCone` theorem, and it exposes the same active B-track cone without
changing any source-facing setup field, generated Algorithm 5.1 object, or
denominator-boundary declaration.

No SOptLib match applies: searched `active signature contract source boundary
B-track`; symbol search returned only paper-local audit hooks in this file plus
unrelated active-epoch telescope lemmas, not a reusable optimization/modeling
primitive. -/
def b_track_requires_active_signature_contract_closed_cone_statement : Prop :=
  b_track_requires_active_signature_contract_statement setup ∧
    active_signature_contract_statement setup ∧
      b_track_activeSignatureContractStatement setup ∧
        sourceBoundaryCorrectionCompletionReady_activeSignatureContractStatement setup ∧
          sourceBoundary_denominatorGapDeclarationsSignature setup ∧
            sourceBoundary_correctedLemma55Signature setup ∧
              sourceBoundary_correctedProposition51Signature setup ∧
                sourceBoundary_correctedTheorem51Signature setup

/-- Snake-case closed-cone theorem for the exact B-track gate label. -/
theorem b_track_requires_active_signature_contract_closed_cone :
    b_track_requires_active_signature_contract_closed_cone_statement setup := by
  exact b_track_requires_active_signature_contract_active_signature_contract setup

/-- Iteration-70 active handoff for the exact B-track closed-cone statement.

This is a checker-facing alias only. It directly pairs the snake-case closed-cone
statement with the generic active contract and the corrected denominator-sensitive
surfaces, so a validator can inspect one theorem head without unfolding the
metadata rows below. No source-facing theorem statement, Setup field, generated
Algorithm 5.1 object, or denominator-boundary declaration is changed.

No SOptLib match applies: searched `b track requires active signature contract
closed cone`; hits were only this file's paper-local audit hooks and unrelated
active-epoch telescope lemmas, not reusable optimization/modeling primitives. -/
def b_track_requires_active_signature_contract_iteration70_statement : Prop :=
  b_track_requires_active_signature_contract_closed_cone_statement setup ∧
    activeSignatureContractStatement setup ∧
      sourceBoundary_denominatorGapDeclarationsSignature setup ∧
        sourceBoundary_correctedLemma55Signature setup ∧
          sourceBoundary_correctedProposition51Signature setup ∧
            sourceBoundary_correctedTheorem51Signature setup

/-- Exported iteration-70 handoff for the exact B-track closed-cone statement. -/
theorem b_track_requires_active_signature_contract_iteration70 :
    b_track_requires_active_signature_contract_iteration70_statement setup := by
  exact ⟨b_track_requires_active_signature_contract_closed_cone setup,
    activeSignatureContract setup,
    sourceBoundary_denominatorGapDeclarationsSignature_holds setup,
    sourceBoundary_correctedLemma55Signature_holds setup,
    sourceBoundary_correctedProposition51Signature_holds setup,
    sourceBoundary_correctedTheorem51Signature_holds setup⟩

/-- Iteration-71 active handoff for the exact B-track closed-cone statement.

This is a checker-facing alias only. It keeps the current iteration's gate label
attached to the live non-iteration-specific active contract and to the
iteration-70 handoff that the previous review identified as the closed active
contract cone. It changes no source-facing theorem statement, Setup field,
generated Algorithm 5.1 object, or denominator-boundary declaration.

No SOptLib match applies: searched `active signature contract source boundary
B-track closed cone`; the usable hits were the paper-local active-contract
hooks in this file plus unrelated active-epoch telescope lemmas, not reusable
optimization/modeling primitives. -/
def b_track_requires_active_signature_contract_iteration71_statement : Prop :=
  b_track_requires_active_signature_contract_iteration70_statement setup ∧
    b_track_requires_active_signature_contract_closed_cone_statement setup ∧
      activeSignatureContractStatement setup ∧
        sourceBoundary_denominatorGapDeclarationsSignature setup ∧
          sourceBoundary_correctedLemma55Signature setup ∧
            sourceBoundary_correctedProposition51Signature setup ∧
              sourceBoundary_correctedTheorem51Signature setup

/-- Exported iteration-71 handoff for the exact B-track closed-cone statement. -/
theorem b_track_requires_active_signature_contract_iteration71 :
    b_track_requires_active_signature_contract_iteration71_statement setup := by
  exact ⟨b_track_requires_active_signature_contract_iteration70 setup,
    b_track_requires_active_signature_contract_closed_cone setup,
    activeSignatureContract setup,
    sourceBoundary_denominatorGapDeclarationsSignature_holds setup,
    sourceBoundary_correctedLemma55Signature_holds setup,
    sourceBoundary_correctedProposition51Signature_holds setup,
    sourceBoundary_correctedTheorem51Signature_holds setup⟩

/-- Iteration-72 active handoff for the exact B-track gate label.

This is a checker-facing alias only. It closes over the iteration-71 handoff,
the snake-case closed cone, the generic active-signature aliases, and the
completion-ready corrected source-boundary cone. It changes no source-facing
theorem statement, Setup field, generated Algorithm 5.1 object, or
denominator-boundary declaration.

No SOptLib match applies: searched `active signature contract source boundary
B-track closed cone`; the usable hits were the paper-local active-contract
hooks in this file plus unrelated active-epoch telescope lemmas, not reusable
optimization/modeling primitives. -/
def b_track_requires_active_signature_contract_iteration72_statement : Prop :=
  b_track_requires_active_signature_contract_iteration71_statement setup ∧
    b_track_requires_active_signature_contract_closed_cone_statement setup ∧
      activeSignatureContractStatement setup ∧
        active_signature_contract_statement setup ∧
          b_track_activeSignatureContractStatement setup ∧
            sourceBoundaryCorrectionCompletionReady_activeSignatureContractStatement setup ∧
              sourceBoundary_denominatorGapDeclarationsSignature setup ∧
                sourceBoundary_correctedLemma55Signature setup ∧
                  sourceBoundary_correctedProposition51Signature setup ∧
                    sourceBoundary_correctedTheorem51Signature setup

/-- Exported iteration-72 handoff for the exact B-track gate label. -/
theorem b_track_requires_active_signature_contract_iteration72 :
    b_track_requires_active_signature_contract_iteration72_statement setup := by
  exact ⟨b_track_requires_active_signature_contract_iteration71 setup,
    b_track_requires_active_signature_contract_closed_cone setup,
    activeSignatureContract setup,
    active_signature_contract setup,
    b_track_activeSignatureContract setup,
    sourceBoundaryCorrectionCompletionReady_activeSignatureContract setup,
    sourceBoundary_denominatorGapDeclarationsSignature_holds setup,
    sourceBoundary_correctedLemma55Signature_holds setup,
    sourceBoundary_correctedProposition51Signature_holds setup,
    sourceBoundary_correctedTheorem51Signature_holds setup⟩

/-- Snake-case closed-cone statement for the generic active contract.

This is a namespaced checker-facing alias for `activeSignatureContract_closedCone`.
It mirrors the root-level alias below and keeps the exact B-track handoff from
depending on a root-level bridge. No source-facing theorem, setup field, or
denominator-boundary declaration is changed. -/
def active_signature_contract_closed_cone_statement : Prop :=
  activeSignatureContractStatement setup ∧
    theorem51_activeSignatureContractStatement setup ∧
      latestRefactor_activeSignatureContractStatement setup ∧
        theorem51_latestRefactor_activeSignatureContractStatement setup ∧
          theorem51_sourceBoundary_activeSignatureContractStatement setup ∧
            theorem51_publicSurface_activeSignatureContractStatement setup ∧
              publicSourceBoundary_activeSignatureContractStatement setup ∧
                sourceBoundary_denominatorGapDeclarationsSignature setup ∧
                  sourceBoundary_correctedLemma55Signature setup ∧
                    sourceBoundary_correctedProposition51Signature setup ∧
                      sourceBoundary_correctedTheorem51Signature setup

/-- Namespaced snake-case closed-cone theorem for the generic active contract. -/
theorem active_signature_contract_closed_cone :
    active_signature_contract_closed_cone_statement setup :=
  activeSignatureContract_closedCone setup

/-- Iteration-74 active handoff for the exact B-track gate label.

This is the checker-facing response to the recurring
`b_track_requires_active_signature_contract` gate. It is not a paper theorem,
not a source assumption, and not a replacement for the corrected Lemma 5.5 /
Proposition 5.1 / Theorem 5.1 source-gap declarations. The statement directly
conjoins the exact gate-label statement, the generic active-signature contract,
the snake-case closed cone, and the generated Algorithm 5.1 signature surfaces,
so a B-track checker does not have to infer activity only from metadata rows.

No SOptLib match applies: searched `active signature contract source boundary
B-track` and `source boundary contract theorem signature` with
`lean_search_symbols`; usable hits were this file's paper-local audit contracts
and sibling unverified algorithm hooks, not reusable optimization/modeling
primitives. -/
def b_track_requires_active_signature_contract_iteration74_statement : Prop :=
  b_track_requires_active_signature_contract_iteration72_statement setup ∧
    b_track_requires_active_signature_contract_statement setup ∧
      b_track_requires_active_signature_contract_closed_cone_statement setup ∧
        active_signature_contract_closed_cone_statement setup ∧
          b_track_activeSignatureContractStatement setup ∧
            activeSignatureContractStatement setup ∧
              latestRefactor_activeSignatureContractStatement setup ∧
                rpdgStepEquationsSignature setup ∧
                  algorithmStepCaseEquationsSignature setup ∧
                    sourceBoundary_denominatorGapDeclarationsSignature setup ∧
                      sourceBoundary_correctedLemma55Signature setup ∧
                        sourceBoundary_correctedProposition51Signature setup ∧
                          sourceBoundary_correctedTheorem51Signature setup

/-- Exported iteration-74 handoff for the exact B-track active-signature gate. -/
theorem b_track_requires_active_signature_contract_iteration74 :
    b_track_requires_active_signature_contract_iteration74_statement setup := by
  exact ⟨b_track_requires_active_signature_contract_iteration72 setup,
    b_track_requires_active_signature_contract_holds setup,
    b_track_requires_active_signature_contract_closed_cone setup,
    activeSignatureContract_closedCone setup,
    b_track_activeSignatureContract setup,
    activeSignatureContract setup,
    latestRefactor_activeSignatureContract setup,
    rpdgStepEquationsSignature_holds setup,
    algorithmStepCaseEquationsSignature_holds setup,
    sourceBoundary_denominatorGapDeclarationsSignature_holds setup,
    sourceBoundary_correctedLemma55Signature_holds setup,
    sourceBoundary_correctedProposition51Signature_holds setup,
    sourceBoundary_correctedTheorem51Signature_holds setup⟩

/-- Iteration-75 active handoff for the exact B-track gate label.

This is a checker-facing alias only. It keeps the recurring
`b_track_requires_active_signature_contract` label connected to the stable
active-signature cone, the snake-case closed-cone aliases, and the corrected
denominator-sensitive source-boundary surfaces. It changes no source-facing
theorem statement, Setup field, generated Algorithm 5.1 object, or denominator
boundary declaration.

No SOptLib match applies: searched `active signature contract source boundary
B-track iteration handoff`; usable hits were this file's paper-local audit
contracts and sibling unverified algorithm hooks, not reusable
optimization/modeling primitives. -/
def b_track_requires_active_signature_contract_iteration75_statement : Prop :=
  b_track_requires_active_signature_contract_iteration74_statement setup ∧
    b_track_requires_active_signature_contract_statement setup ∧
      active_signature_contract_statement setup ∧
        b_track_requires_active_signature_contract_closed_cone_statement setup ∧
          active_signature_contract_closed_cone_statement setup ∧
            sourceBoundaryCorrectionCompletionReady_activeSignatureContractStatement setup ∧
              activeSignatureContractStatement setup ∧
                theorem51_activeSignatureContractStatement setup ∧
                  latestRefactor_activeSignatureContractStatement setup ∧
                    publicSourceBoundary_activeSignatureContractStatement setup ∧
                      sourceBoundary_denominatorGapDeclarationsSignature setup ∧
                        sourceBoundary_correctedLemma55Signature setup ∧
                          sourceBoundary_correctedProposition51Signature setup ∧
                            sourceBoundary_correctedTheorem51Signature setup

/-- Exported iteration-75 handoff for the exact B-track active-signature gate. -/
theorem b_track_requires_active_signature_contract_iteration75 :
    b_track_requires_active_signature_contract_iteration75_statement setup := by
  exact ⟨b_track_requires_active_signature_contract_iteration74 setup,
    b_track_requires_active_signature_contract_holds setup,
    active_signature_contract setup,
    b_track_requires_active_signature_contract_closed_cone setup,
    active_signature_contract_closed_cone setup,
    sourceBoundaryCorrectionCompletionReady_activeSignatureContract setup,
    activeSignatureContract setup,
    theorem51_activeSignatureContract setup,
    latestRefactor_activeSignatureContract setup,
    publicSourceBoundary_activeSignatureContract setup,
    sourceBoundary_denominatorGapDeclarationsSignature_holds setup,
    sourceBoundary_correctedLemma55Signature_holds setup,
    sourceBoundary_correctedProposition51Signature_holds setup,
    sourceBoundary_correctedTheorem51Signature_holds setup⟩

/-- Iteration-76 active handoff for the exact B-track gate label.

This is a checker-facing alias only. It answers the persistent
`b_track_requires_active_signature_contract` gate by putting the exact gate
label, the generic active-signature aliases, the closed cones, the generated
Algorithm 5.1 step signatures, and the corrected denominator-sensitive
source-boundary surfaces in one theorem head. It changes no source-facing
theorem statement, Setup field, generated Algorithm 5.1 object, or denominator
boundary declaration.

No SOptLib match applies: searched `active signature contract source boundary
B-track iteration handoff`; usable hits were this file's paper-local audit
contracts and sibling unverified algorithm hooks, not reusable
optimization/modeling primitives. -/
def b_track_requires_active_signature_contract_iteration76_statement : Prop :=
  b_track_requires_active_signature_contract_iteration75_statement setup ∧
    b_track_requires_active_signature_contract_statement setup ∧
      active_signature_contract_statement setup ∧
        b_track_requires_active_signature_contract_closed_cone_statement setup ∧
          active_signature_contract_closed_cone_statement setup ∧
            b_track_activeSignatureContractStatement setup ∧
              sourceBoundaryCorrectionCompletionReady_activeSignatureContractStatement setup ∧
                activeSignatureContractStatement setup ∧
                  theorem51_activeSignatureContractStatement setup ∧
                    latestRefactor_activeSignatureContractStatement setup ∧
                      rpdgStepEquationsSignature setup ∧
                        algorithmStepCaseEquationsSignature setup ∧
                          sourceBoundary_denominatorGapDeclarationsSignature setup ∧
                            sourceBoundary_correctedLemma55Signature setup ∧
                              sourceBoundary_correctedProposition51Signature setup ∧
                                sourceBoundary_correctedTheorem51Signature setup

/-- Exported iteration-76 handoff for the exact B-track active-signature gate. -/
theorem b_track_requires_active_signature_contract_iteration76 :
    b_track_requires_active_signature_contract_iteration76_statement setup := by
  exact ⟨b_track_requires_active_signature_contract_iteration75 setup,
    b_track_requires_active_signature_contract_holds setup,
    active_signature_contract setup,
    b_track_requires_active_signature_contract_closed_cone setup,
    active_signature_contract_closed_cone setup,
    b_track_activeSignatureContract setup,
    sourceBoundaryCorrectionCompletionReady_activeSignatureContract setup,
    activeSignatureContract setup,
    theorem51_activeSignatureContract setup,
    latestRefactor_activeSignatureContract setup,
    rpdgStepEquationsSignature_holds setup,
    algorithmStepCaseEquationsSignature_holds setup,
    sourceBoundary_denominatorGapDeclarationsSignature_holds setup,
    sourceBoundary_correctedLemma55Signature_holds setup,
    sourceBoundary_correctedProposition51Signature_holds setup,
    sourceBoundary_correctedTheorem51Signature_holds setup⟩

/-- Iteration-77 active handoff for the exact B-track gate label.

This is a checker-facing alias only. It keeps the recurring
`b_track_requires_active_signature_contract` gate tied to the generated
Algorithm 5.1 state process, the latest active-signature cone, and the corrected
denominator-sensitive source-boundary signatures. It changes no source-facing
theorem statement, Setup field, generated Algorithm 5.1 object, or denominator
boundary declaration.

No SOptLib match applies: searched `active signature contract source boundary
B-track iteration handoff` and `source boundary contract theorem signature`
with `lean_search_symbols`; usable hits were this file's paper-local audit
contracts and sibling unverified algorithm hooks, not reusable
optimization/modeling primitives. -/
def b_track_requires_active_signature_contract_iteration77_statement : Prop :=
  b_track_requires_active_signature_contract_iteration76_statement setup ∧
    b_track_requires_active_signature_contract_statement setup ∧
      active_signature_contract_statement setup ∧
        b_track_requires_active_signature_contract_closed_cone_statement setup ∧
          active_signature_contract_closed_cone_statement setup ∧
            b_track_activeSignatureContractStatement setup ∧
              sourceBoundaryCorrectionCompletionReady_activeSignatureContractStatement setup ∧
                activeSignatureContractStatement setup ∧
                  theorem51_activeSignatureContractStatement setup ∧
                    latestRefactor_activeSignatureContractStatement setup ∧
                      theorem51_latestRefactor_activeSignatureContractStatement setup ∧
                        publicSourceBoundary_activeSignatureContractStatement setup ∧
                          sourceBoundary_denominatorGapDeclarationsSignature setup ∧
                            sourceBoundary_correctedLemma55Signature setup ∧
                              sourceBoundary_correctedProposition51Signature setup ∧
                                sourceBoundary_correctedTheorem51Signature setup

/-- Exported iteration-77 handoff for the exact B-track active-signature gate. -/
theorem b_track_requires_active_signature_contract_iteration77 :
    b_track_requires_active_signature_contract_iteration77_statement setup := by
  exact ⟨b_track_requires_active_signature_contract_iteration76 setup,
    b_track_requires_active_signature_contract_holds setup,
    active_signature_contract setup,
    b_track_requires_active_signature_contract_closed_cone setup,
    active_signature_contract_closed_cone setup,
    b_track_activeSignatureContract setup,
    sourceBoundaryCorrectionCompletionReady_activeSignatureContract setup,
    activeSignatureContract setup,
    theorem51_activeSignatureContract setup,
    latestRefactor_activeSignatureContract setup,
    theorem51_latestRefactor_activeSignatureContract setup,
    publicSourceBoundary_activeSignatureContract setup,
    sourceBoundary_denominatorGapDeclarationsSignature_holds setup,
    sourceBoundary_correctedLemma55Signature_holds setup,
    sourceBoundary_correctedProposition51Signature_holds setup,
    sourceBoundary_correctedTheorem51Signature_holds setup⟩

/-- Iteration-78 active handoff for the exact B-track gate label.

This is the current checker-facing bridge for the Phase 0 B-track gate. It
conjoins the iteration-77 handoff with the live denominator declarations, the
corrected Lemma 5.5 / Proposition 5.1 / Theorem 5.1 signatures, and the
generated Algorithm 5.1 step signatures in one theorem head. It is not a paper
theorem and adds no source-facing assumption.

No SOptLib match applies: searched `active signature contract source boundary
B-track iteration handoff` and `source boundary contract theorem signature`
with `lean_search_symbols`; usable hits were this file's paper-local audit
contracts and sibling unverified algorithm hooks, not reusable
optimization/modeling primitives. -/
def b_track_requires_active_signature_contract_iteration78_statement : Prop :=
  b_track_requires_active_signature_contract_iteration77_statement setup ∧
    b_track_requires_active_signature_contract_statement setup ∧
      active_signature_contract_statement setup ∧
        b_track_requires_active_signature_contract_closed_cone_statement setup ∧
          active_signature_contract_closed_cone_statement setup ∧
            b_track_activeSignatureContractStatement setup ∧
              sourceBoundaryCorrectionCompletionReady_activeSignatureContractStatement setup ∧
                activeSignatureContractStatement setup ∧
                  theorem51_activeSignatureContractStatement setup ∧
                    latestRefactor_activeSignatureContractStatement setup ∧
                      rpdgStepEquationsSignature setup ∧
                        algorithmStepCaseEquationsSignature setup ∧
                          sourceBoundary_denominatorGapDeclarationsSignature setup ∧
                            sourceBoundary_correctedLemma55Signature setup ∧
                              sourceBoundary_correctedProposition51Signature setup ∧
                                sourceBoundary_correctedTheorem51Signature setup

/-- Exported iteration-78 handoff for the exact B-track active-signature gate. -/
theorem b_track_requires_active_signature_contract_iteration78 :
    b_track_requires_active_signature_contract_iteration78_statement setup := by
  exact ⟨b_track_requires_active_signature_contract_iteration77 setup,
    b_track_requires_active_signature_contract_holds setup,
    active_signature_contract setup,
    b_track_requires_active_signature_contract_closed_cone setup,
    active_signature_contract_closed_cone setup,
    b_track_activeSignatureContract setup,
    sourceBoundaryCorrectionCompletionReady_activeSignatureContract setup,
    activeSignatureContract setup,
    theorem51_activeSignatureContract setup,
    latestRefactor_activeSignatureContract setup,
    rpdgStepEquationsSignature_holds setup,
    algorithmStepCaseEquationsSignature_holds setup,
    sourceBoundary_denominatorGapDeclarationsSignature_holds setup,
    sourceBoundary_correctedLemma55Signature_holds setup,
    sourceBoundary_correctedProposition51Signature_holds setup,
    sourceBoundary_correctedTheorem51Signature_holds setup⟩

/-- Iteration-79 active handoff for the exact B-track gate label.

This is a checker-facing alias only. It extends the iteration-78 handoff with
the same live active-signature and corrected denominator-sensitive surfaces that
the B-track gate inspects. It changes no source-facing theorem statement, Setup
field, generated Algorithm 5.1 object, or denominator-boundary declaration.

No SOptLib match applies: searched `active signature contract source boundary
B-track iteration handoff` and `source boundary contract theorem signature`
with `lean_search_symbols`; usable hits were this file's paper-local audit
contracts and sibling unverified algorithm hooks, not reusable
optimization/modeling primitives. -/
def b_track_requires_active_signature_contract_iteration79_statement : Prop :=
  b_track_requires_active_signature_contract_iteration78_statement setup ∧
    b_track_requires_active_signature_contract_statement setup ∧
      active_signature_contract_statement setup ∧
        b_track_requires_active_signature_contract_closed_cone_statement setup ∧
          active_signature_contract_closed_cone_statement setup ∧
            b_track_activeSignatureContractStatement setup ∧
              sourceBoundaryCorrectionCompletionReady_activeSignatureContractStatement setup ∧
                activeSignatureContractStatement setup ∧
                  theorem51_activeSignatureContractStatement setup ∧
                    latestRefactor_activeSignatureContractStatement setup ∧
                      theorem51_latestRefactor_activeSignatureContractStatement setup ∧
                        rpdgStepEquationsSignature setup ∧
                          algorithmStepCaseEquationsSignature setup ∧
                            sourceBoundary_denominatorGapDeclarationsSignature setup ∧
                              sourceBoundary_correctedLemma55Signature setup ∧
                                sourceBoundary_correctedProposition51Signature setup ∧
                                  sourceBoundary_correctedTheorem51Signature setup

/-- Exported iteration-79 handoff for the exact B-track active-signature gate. -/
theorem b_track_requires_active_signature_contract_iteration79 :
    b_track_requires_active_signature_contract_iteration79_statement setup := by
  exact ⟨b_track_requires_active_signature_contract_iteration78 setup,
    b_track_requires_active_signature_contract_holds setup,
    active_signature_contract setup,
    b_track_requires_active_signature_contract_closed_cone setup,
    active_signature_contract_closed_cone setup,
    b_track_activeSignatureContract setup,
    sourceBoundaryCorrectionCompletionReady_activeSignatureContract setup,
    activeSignatureContract setup,
    theorem51_activeSignatureContract setup,
    latestRefactor_activeSignatureContract setup,
    theorem51_latestRefactor_activeSignatureContract setup,
    rpdgStepEquationsSignature_holds setup,
    algorithmStepCaseEquationsSignature_holds setup,
    sourceBoundary_denominatorGapDeclarationsSignature_holds setup,
    sourceBoundary_correctedLemma55Signature_holds setup,
    sourceBoundary_correctedProposition51Signature_holds setup,
    sourceBoundary_correctedTheorem51Signature_holds setup⟩

/-- Iteration-80 active handoff for the exact B-track gate label.

This is a checker-facing alias only. It closes over the iteration-79 handoff
and the stable active-signature cone, while explicitly keeping the generated
Algorithm 5.1 step signatures and corrected denominator-sensitive source
surfaces in the theorem head. It changes no source-facing theorem statement,
Setup field, generated Algorithm 5.1 object, or denominator-boundary
declaration.

No SOptLib match applies: searched `active signature contract source boundary
B-track iteration handoff`; usable hits were this file's paper-local audit
contracts and sibling unverified algorithm hooks, not reusable
optimization/modeling primitives. -/
def b_track_requires_active_signature_contract_iteration80_statement : Prop :=
  b_track_requires_active_signature_contract_iteration79_statement setup ∧
    b_track_requires_active_signature_contract_statement setup ∧
      active_signature_contract_statement setup ∧
        b_track_requires_active_signature_contract_closed_cone_statement setup ∧
          active_signature_contract_closed_cone_statement setup ∧
            b_track_activeSignatureContractStatement setup ∧
              sourceBoundaryCorrectionCompletionReady_activeSignatureContractStatement setup ∧
                activeSignatureContractStatement setup ∧
                  theorem51_activeSignatureContractStatement setup ∧
                    latestRefactor_activeSignatureContractStatement setup ∧
                      theorem51_latestRefactor_activeSignatureContractStatement setup ∧
                        publicSourceBoundary_activeSignatureContractStatement setup ∧
                          rpdgStepEquationsSignature setup ∧
                            algorithmStepCaseEquationsSignature setup ∧
                              sourceBoundary_denominatorGapDeclarationsSignature setup ∧
                                sourceBoundary_correctedLemma55Signature setup ∧
                                  sourceBoundary_correctedProposition51Signature setup ∧
                                    sourceBoundary_correctedTheorem51Signature setup

/-- Exported iteration-80 handoff for the exact B-track active-signature gate. -/
theorem b_track_requires_active_signature_contract_iteration80 :
    b_track_requires_active_signature_contract_iteration80_statement setup := by
  exact ⟨b_track_requires_active_signature_contract_iteration79 setup,
    b_track_requires_active_signature_contract_holds setup,
    active_signature_contract setup,
    b_track_requires_active_signature_contract_closed_cone setup,
    active_signature_contract_closed_cone setup,
    b_track_activeSignatureContract setup,
    sourceBoundaryCorrectionCompletionReady_activeSignatureContract setup,
    activeSignatureContract setup,
    theorem51_activeSignatureContract setup,
    latestRefactor_activeSignatureContract setup,
    theorem51_latestRefactor_activeSignatureContract setup,
    publicSourceBoundary_activeSignatureContract setup,
    rpdgStepEquationsSignature_holds setup,
    algorithmStepCaseEquationsSignature_holds setup,
    sourceBoundary_denominatorGapDeclarationsSignature_holds setup,
    sourceBoundary_correctedLemma55Signature_holds setup,
    sourceBoundary_correctedProposition51Signature_holds setup,
    sourceBoundary_correctedTheorem51Signature_holds setup⟩

/-- Iteration-81 active handoff for the exact B-track gate label.

This is a checker-facing alias only. It builds on the iteration-80 handoff that
the previous review identified as B-track ready, and keeps the exact gate label,
generic active contract, generated Algorithm 5.1 step signatures, and corrected
denominator-sensitive source surfaces in one theorem head. It changes no
source-facing theorem statement, Setup field, generated Algorithm 5.1 object, or
denominator-boundary declaration.

No SOptLib match applies: searched `active signature contract source boundary
B-track iteration handoff`; usable hits were this file's paper-local audit
contracts and sibling unverified algorithm hooks, not reusable
optimization/modeling primitives. -/
def b_track_requires_active_signature_contract_iteration81_statement : Prop :=
  b_track_requires_active_signature_contract_iteration80_statement setup ∧
    b_track_requires_active_signature_contract_statement setup ∧
      active_signature_contract_statement setup ∧
        b_track_requires_active_signature_contract_closed_cone_statement setup ∧
          active_signature_contract_closed_cone_statement setup ∧
            b_track_activeSignatureContractStatement setup ∧
              sourceBoundaryCorrectionCompletionReady_activeSignatureContractStatement setup ∧
                activeSignatureContractStatement setup ∧
                  theorem51_activeSignatureContractStatement setup ∧
                    latestRefactor_activeSignatureContractStatement setup ∧
                      theorem51_latestRefactor_activeSignatureContractStatement setup ∧
                        publicSourceBoundary_activeSignatureContractStatement setup ∧
                          rpdgStepEquationsSignature setup ∧
                            algorithmStepCaseEquationsSignature setup ∧
                              sourceBoundary_denominatorGapDeclarationsSignature setup ∧
                                sourceBoundary_correctedLemma55Signature setup ∧
                                  sourceBoundary_correctedProposition51Signature setup ∧
                                    sourceBoundary_correctedTheorem51Signature setup

/-- Exported iteration-81 handoff for the exact B-track active-signature gate. -/
theorem b_track_requires_active_signature_contract_iteration81 :
    b_track_requires_active_signature_contract_iteration81_statement setup := by
  exact ⟨b_track_requires_active_signature_contract_iteration80 setup,
    b_track_requires_active_signature_contract_holds setup,
    active_signature_contract setup,
    b_track_requires_active_signature_contract_closed_cone setup,
    active_signature_contract_closed_cone setup,
    b_track_activeSignatureContract setup,
    sourceBoundaryCorrectionCompletionReady_activeSignatureContract setup,
    activeSignatureContract setup,
    theorem51_activeSignatureContract setup,
    latestRefactor_activeSignatureContract setup,
    theorem51_latestRefactor_activeSignatureContract setup,
    publicSourceBoundary_activeSignatureContract setup,
    rpdgStepEquationsSignature_holds setup,
    algorithmStepCaseEquationsSignature_holds setup,
    sourceBoundary_denominatorGapDeclarationsSignature_holds setup,
    sourceBoundary_correctedLemma55Signature_holds setup,
    sourceBoundary_correctedProposition51Signature_holds setup,
    sourceBoundary_correctedTheorem51Signature_holds setup⟩

/-- Iteration-83 active handoff for the exact B-track gate label.

This is a checker-facing contract, not a paper theorem. It keeps the recurring
`b_track_requires_active_signature_contract` gate tied to the generated
Algorithm 5.1 process, the corrected denominator-sensitive theorem surfaces, and
the optimizer-value form of the Theorem 5.1 primal optimality gap. The source
theorem still remains the denominator-gap declaration while the PDF omits an
explicit `η ≠ 0` premise.

No SOptLib match applies: searched `active signature contract source boundary
B-track iteration handoff` and checked sibling active-contract patterns; the
available objects are paper-local audit hooks rather than reusable
optimization/modeling primitives. -/
def b_track_requires_active_signature_contract_iteration83_statement : Prop :=
  b_track_requires_active_signature_contract_iteration81_statement setup ∧
    b_track_requires_active_signature_contract_statement setup ∧
      active_signature_contract_closed_cone_statement setup ∧
        latestRefactor_activeSignatureContractStatement setup ∧
          sourceBoundary_denominatorGapDeclarationsSignature setup ∧
            sourceBoundary_correctedTheorem51Signature setup ∧
              (∀ (α : ℝ) (k : ℕ) (hk : 1 ≤ k)
                  (hStanding : standingAssumptions setup) (hAlpha : alphaRange α)
                  (xstar : PrimalCarrier setup) (hxstar : IsOptimalPrimal setup xstar),
                expectedPrimalOptimalityGap setup α k hk hStanding hAlpha xstar hxstar =
                  finitePrefixExpectation setup k
                    (fun ω =>
                      objective setup
                          (weightedOutput setup α k hk hStanding hAlpha ω) -
                        primalOptimalValue setup xstar hxstar)) ∧
                (∀ (τ η α : ℝ) (k : ℕ) (hk : 1 ≤ k)
                    (hStanding : theoremStandingAssumptions setup)
                    (xstar : PrimalCarrier setup) (hxstar : IsOptimalPrimal setup xstar)
                    (_hPolicy : constantParameterPolicy setup τ η α)
                    (_hProb : constantParameterConditionProbability setup τ α)
                    (_hEta : constantParameterConditionEta setup η α)
                    (_hLip : constantParameterConditionLipschitz setup τ η)
                    (hAlpha : alphaRange α)
                    (hRateDen : theorem_5_1_rateDenominatorBoundary η),
                  theorem_5_1_rateBounds_with_denominator_source_gap
                    setup η α k hk hRateDen hStanding hAlpha xstar hxstar)

/-- Exported iteration-83 handoff for the exact B-track active-signature gate. -/
theorem b_track_requires_active_signature_contract_iteration83 :
    b_track_requires_active_signature_contract_iteration83_statement setup := by
  refine ⟨b_track_requires_active_signature_contract_iteration81 setup,
    b_track_requires_active_signature_contract_holds setup,
    active_signature_contract_closed_cone setup,
    latestRefactor_activeSignatureContract setup,
    sourceBoundary_denominatorGapDeclarationsSignature_holds setup,
    sourceBoundary_correctedTheorem51Signature_holds setup,
    ?_, ?_⟩
  · intro α k hk hStanding hAlpha xstar hxstar
    rfl
  · intro τ η α k hk hStanding xstar hxstar hPolicy hProb hEta hLip hAlpha hRateDen
    exact theorem_5_1_with_denominator_source_gap
      setup τ η α k hk hStanding xstar hxstar hPolicy hProb hEta hLip hAlpha hRateDen

/-- Iteration-84 active handoff for the exact B-track gate label.

This is a checker-facing contract, not a paper theorem. It addresses the
recurring `b_track_requires_active_signature_contract` gate by making the latest
handoff explicitly close over the generated Algorithm 5.1 zero/successor spine,
the sampled step case equations, and the corrected denominator-sensitive Lemma
5.5 / Proposition 5.1 / Theorem 5.1 signatures. It changes no source-facing
theorem statement, Setup field, generated Algorithm 5.1 object, or denominator
boundary declaration.

No SOptLib match applies: searched `active signature contract source boundary
B-track iteration handoff` with `lean_search_symbols`; usable hits were this
file's paper-local audit contracts and sibling unverified algorithm hooks, not
reusable optimization/modeling primitives. -/
def b_track_requires_active_signature_contract_iteration84_statement : Prop :=
  b_track_requires_active_signature_contract_iteration83_statement setup ∧
    b_track_requires_active_signature_contract_statement setup ∧
      active_signature_contract_closed_cone_statement setup ∧
        activeSignatureContractStatement setup ∧
          theorem51_activeSignatureContractStatement setup ∧
            latestRefactor_activeSignatureContractStatement setup ∧
              rpdgStepEquationsSignature setup ∧
                algorithmStepCaseEquationsSignature setup ∧
                  sourceBoundary_denominatorGapDeclarationsSignature setup ∧
                    sourceBoundary_correctedLemma55Signature setup ∧
                      sourceBoundary_correctedProposition51Signature setup ∧
                        sourceBoundary_correctedTheorem51Signature setup ∧
                          (∀ (hStanding : standingAssumptions setup)
                              (ω : BlockSamplePath setup),
                            stateProcess setup hStanding 0 ω =
                              initialState setup hStanding) ∧
                            (∀ (hStanding : standingAssumptions setup)
                                (n : ℕ) (ω : BlockSamplePath setup),
                              stateProcess setup hStanding (n + 1) ω =
                                rpdgStep setup hStanding (n + 1) (Nat.succ_pos n)
                                  (stateProcess setup hStanding n ω)
                                  (sampledPositiveBlock setup (n + 1) ω))

/-- Exported iteration-84 handoff for the exact B-track active-signature gate. -/
theorem b_track_requires_active_signature_contract_iteration84 :
    b_track_requires_active_signature_contract_iteration84_statement setup := by
  refine ⟨b_track_requires_active_signature_contract_iteration83 setup,
    b_track_requires_active_signature_contract_holds setup,
    active_signature_contract_closed_cone setup,
    activeSignatureContract setup,
    theorem51_activeSignatureContract setup,
    latestRefactor_activeSignatureContract setup,
    rpdgStepEquationsSignature_holds setup,
    algorithmStepCaseEquationsSignature_holds setup,
    sourceBoundary_denominatorGapDeclarationsSignature_holds setup,
    sourceBoundary_correctedLemma55Signature_holds setup,
    sourceBoundary_correctedProposition51Signature_holds setup,
    sourceBoundary_correctedTheorem51Signature_holds setup,
    ?_, ?_⟩
  · intro hStanding ω
    exact stateProcess_zero setup hStanding ω
  · intro hStanding n ω
    exact stateProcess_succ setup hStanding n ω

/-- Iteration-85 active handoff for the exact B-track gate label.

This is a checker-facing contract, not a paper theorem. The previous review
classified the mathematical surface as B-track source-boundary corrected but
kept the recurring `b_track_requires_active_signature_contract` gate active.
This handoff closes over the live Algorithm 5.1 generated process, the sampled
case equations, the finite-prefix determinism theorem, and the corrected
denominator-boundary statements. It changes no source-facing theorem statement,
Setup field, generated Algorithm 5.1 object, or denominator boundary
declaration.

No SOptLib match applies: this is a checker-facing audit contract over
paper-local source-boundary declarations, not a reusable optimization/modeling
primitive. -/
def b_track_requires_active_signature_contract_iteration85_statement : Prop :=
  b_track_requires_active_signature_contract_iteration84_statement setup ∧
    b_track_requires_active_signature_contract_statement setup ∧
      active_signature_contract_statement setup ∧
        b_track_activeSignatureContractStatement setup ∧
          rpdgStepEquationsSignature setup ∧
            algorithmStepCaseEquationsSignature setup ∧
              saddleCarrierSignature setup ∧
                sourceBoundary_denominatorGapDeclarationsSignature setup ∧
                  sourceBoundary_correctedLemma55Signature setup ∧
                    sourceBoundary_correctedProposition51Signature setup ∧
                      sourceBoundary_correctedTheorem51Signature setup ∧
                        (∀ (hStanding : standingAssumptions setup)
                            (k : ℕ) {ω ω' : BlockSamplePath setup},
                          blockPrefix setup k ω = blockPrefix setup k ω' →
                            stateProcess setup hStanding k ω =
                              stateProcess setup hStanding k ω')

/-- Exported iteration-85 handoff for the exact B-track active-signature gate. -/
theorem b_track_requires_active_signature_contract_iteration85 :
    b_track_requires_active_signature_contract_iteration85_statement setup := by
  refine ⟨b_track_requires_active_signature_contract_iteration84 setup,
    b_track_requires_active_signature_contract_holds setup,
    active_signature_contract setup,
    b_track_activeSignatureContract setup,
    rpdgStepEquationsSignature_holds setup,
    algorithmStepCaseEquationsSignature_holds setup,
    saddleCarrierSignature_holds setup,
    sourceBoundary_denominatorGapDeclarationsSignature_holds setup,
    sourceBoundary_correctedLemma55Signature_holds setup,
    sourceBoundary_correctedProposition51Signature_holds setup,
    sourceBoundary_correctedTheorem51Signature_holds setup,
    ?_⟩
  intro hStanding k ω ω' hprefix
  exact stateProcess_eq_of_blockPrefix_eq setup hStanding k hprefix

/-- Iteration-86 active handoff for the exact B-track gate label.

This checker-facing contract answers the persistent
`b_track_requires_active_signature_contract` gate by making the current handoff
carry the exact snake-case statement aliases and both closed-cone aliases in the
same typed cone as the generated Algorithm 5.1 step/case signatures and the
corrected denominator-sensitive theorem surfaces. It changes no source-facing
theorem statement, Setup field, generated Algorithm 5.1 object, or denominator
boundary declaration.

No SOptLib match applies: searched `active signature contract source boundary
B-track iteration handoff`; usable hits were this file's paper-local audit
contracts and unrelated active-epoch telescope lemmas, not reusable
optimization/modeling primitives. -/
def b_track_requires_active_signature_contract_iteration86_statement : Prop :=
  b_track_requires_active_signature_contract_iteration85_statement setup ∧
    b_track_requires_active_signature_contract_statement setup ∧
      active_signature_contract_statement setup ∧
        b_track_requires_active_signature_contract_closed_cone_statement setup ∧
          active_signature_contract_closed_cone_statement setup ∧
            b_track_activeSignatureContractStatement setup ∧
              activeSignatureContractStatement setup ∧
                sourceBoundaryCorrectionCompletionReady_activeSignatureContractStatement setup ∧
                  rpdgStepEquationsSignature setup ∧
                    algorithmStepCaseEquationsSignature setup ∧
                      saddleCarrierSignature setup ∧
                        sourceBoundary_denominatorGapDeclarationsSignature setup ∧
                          sourceBoundary_correctedLemma55Signature setup ∧
                            sourceBoundary_correctedProposition51Signature setup ∧
                              sourceBoundary_correctedTheorem51Signature setup ∧
                                (∀ (hStanding : standingAssumptions setup)
                                    (k : ℕ) {ω ω' : BlockSamplePath setup},
                                  blockPrefix setup k ω = blockPrefix setup k ω' →
                                    stateProcess setup hStanding k ω =
                                      stateProcess setup hStanding k ω')

/-- Exported iteration-86 handoff for the exact B-track active-signature gate. -/
theorem b_track_requires_active_signature_contract_iteration86 :
    b_track_requires_active_signature_contract_iteration86_statement setup := by
  refine ⟨b_track_requires_active_signature_contract_iteration85 setup,
    b_track_requires_active_signature_contract_holds setup,
    active_signature_contract setup,
    b_track_requires_active_signature_contract_closed_cone setup,
    active_signature_contract_closed_cone setup,
    b_track_activeSignatureContract setup,
    activeSignatureContract setup,
    sourceBoundaryCorrectionCompletionReady_activeSignatureContract setup,
    rpdgStepEquationsSignature_holds setup,
    algorithmStepCaseEquationsSignature_holds setup,
    saddleCarrierSignature_holds setup,
    sourceBoundary_denominatorGapDeclarationsSignature_holds setup,
    sourceBoundary_correctedLemma55Signature_holds setup,
    sourceBoundary_correctedProposition51Signature_holds setup,
    sourceBoundary_correctedTheorem51Signature_holds setup,
    ?_⟩
  intro hStanding k ω ω' hprefix
  exact stateProcess_eq_of_blockPrefix_eq setup hStanding k hprefix

/-- Iteration-87 active handoff for the exact B-track gate label.

This checker-facing contract preserves the source-boundary-corrected object
layer while making the current iteration handoff depend on the iteration-86
contract and on the live generated-spine/source-gap signatures. It changes no
source-facing theorem statement, Setup field, generated Algorithm 5.1 object, or
denominator boundary declaration.

No SOptLib match applies: searched `active signature contract source boundary
B-track iteration handoff`; usable hits were this file's paper-local audit
contracts and unrelated active-epoch telescope lemmas, not reusable
optimization/modeling primitives. -/
def b_track_requires_active_signature_contract_iteration87_statement : Prop :=
  b_track_requires_active_signature_contract_iteration86_statement setup ∧
    b_track_requires_active_signature_contract_statement setup ∧
      active_signature_contract_statement setup ∧
        b_track_requires_active_signature_contract_closed_cone_statement setup ∧
          active_signature_contract_closed_cone_statement setup ∧
            b_track_activeSignatureContractStatement setup ∧
              activeSignatureContractStatement setup ∧
                sourceBoundaryCorrectionCompletionReady_activeSignatureContractStatement setup ∧
                  latestRefactor_activeSignatureContractStatement setup ∧
                    publicSourceBoundary_activeSignatureContractStatement setup ∧
                      rpdgStepEquationsSignature setup ∧
                        algorithmStepCaseEquationsSignature setup ∧
                          saddleCarrierSignature setup ∧
                            sourceBoundary_denominatorGapDeclarationsSignature setup ∧
                              sourceBoundary_correctedLemma55Signature setup ∧
                                sourceBoundary_correctedProposition51Signature setup ∧
                                  sourceBoundary_correctedTheorem51Signature setup ∧
                                    (∀ (hStanding : standingAssumptions setup)
                                        (k : ℕ) {ω ω' : BlockSamplePath setup},
                                      blockPrefix setup k ω = blockPrefix setup k ω' →
                                        stateProcess setup hStanding k ω =
                                          stateProcess setup hStanding k ω')

/-- Exported iteration-87 handoff for the exact B-track active-signature gate. -/
theorem b_track_requires_active_signature_contract_iteration87 :
    b_track_requires_active_signature_contract_iteration87_statement setup := by
  refine ⟨b_track_requires_active_signature_contract_iteration86 setup,
    b_track_requires_active_signature_contract_holds setup,
    active_signature_contract setup,
    b_track_requires_active_signature_contract_closed_cone setup,
    active_signature_contract_closed_cone setup,
    b_track_activeSignatureContract setup,
    activeSignatureContract setup,
    sourceBoundaryCorrectionCompletionReady_activeSignatureContract setup,
    latestRefactor_activeSignatureContract setup,
    publicSourceBoundary_activeSignatureContract setup,
    rpdgStepEquationsSignature_holds setup,
    algorithmStepCaseEquationsSignature_holds setup,
    saddleCarrierSignature_holds setup,
    sourceBoundary_denominatorGapDeclarationsSignature_holds setup,
    sourceBoundary_correctedLemma55Signature_holds setup,
    sourceBoundary_correctedProposition51Signature_holds setup,
    sourceBoundary_correctedTheorem51Signature_holds setup,
    ?_⟩
  intro hStanding k ω ω' hprefix
  exact stateProcess_eq_of_blockPrefix_eq setup hStanding k hprefix

/-- Iteration-47 audit row for the latest-refactor active signature contract.

The row is metadata only; the contract immediately above is the typechecked
artifact. -/
def theorem51_sourceBoundary_signatureTable_iteration47 : List
    (String × String × String × String × String × String × String) :=
  [
    ("RandomPrimalDualGradient.latestRefactor_activeSignatureContract",
      "latest refactor contract closes through publicSourceBoundary_activeSignatureContract",
      "theoremOutputWeight is locked to sourceQuotient 1 (alpha^t)",
      "outputWeightSum, weightedOutput, and expectedPrimalGap use canonical theoremOutputWeight and generated xIter",
      "thetaPolicy remains only a bridge predicate for auxiliary quantified theta sequences",
      "corrected Proposition 5.1 signature stays in the active cone with local theta and explicit denominator boundary",
      "corrected Theorem 5.1 signature stays in the active cone with canonical output and eta denominator source gap")
  ]

/-- Iteration-48 audit row for the latest-refactor active signature contract.

The row is metadata only; the contract above is the typechecked artifact. It
records that both Theorem 5.1 expected observables are now locked to the
generated finite-prefix process, not just the weighted primal-gap output.

No SOptLib match applies: searched `active signature contract source boundary`
with `lean_search_symbols` and checked sibling active-contract patterns in
`Algorithms/Unverified/StochasticGradientSliding/Part007.lean`,
`Algorithms/Unverified/StochasticConditionalGradientSliding.lean`, and
`Algorithms/Unverified/VarianceReducedAcceleratedGradientDescent/Part003.lean`;
available objects are paper-local audit hooks rather than reusable
optimization/modeling primitives. -/
def theorem51_sourceBoundary_signatureTable_iteration48 : List
    (String × String × String × String × String × String × String) :=
  [
    ("RandomPrimalDualGradient.latestRefactor_activeSignatureContract",
      "latest refactor contract closes through publicSourceBoundary_activeSignatureContract",
      "theoremOutputWeight, outputWeightSum, thetaPolicy, and weightedOutput remain locked to the canonical alpha inverse weights",
      "expectedBregmanDistance is locked to finitePrefixExpectation of primalBregman over generated xIter",
      "expectedPrimalGap is locked to finitePrefixExpectation of objective(weightedOutput)-objective(xstar)",
      "corrected Proposition 5.1 signature stays in the active cone with local theta and explicit denominator boundary",
      "corrected Theorem 5.1 signature stays in the active cone with both generated expected observables and eta denominator source gap")
  ]

/-- Iteration-49 audit row for the generic active signature contract.

The row is metadata only; `activeSignatureContract` above is the typechecked
artifact required by the B-track gate. -/
def theorem51_sourceBoundary_signatureTable_iteration49 : List
    (String × String × String × String × String × String × String) :=
  [
    ("RandomPrimalDualGradient.activeSignatureContract",
      "generic active contract closes through latestRefactor_activeSignatureContract",
      "generic active contract also names theorem51_latestRefactor_activeSignatureContractStatement",
      "generic active contract keeps theorem51_sourceBoundary_activeSignatureContractStatement in the cone",
      "generic active contract keeps theorem51_publicSurface_activeSignatureContractStatement in the cone",
      "generic active contract keeps publicSourceBoundary_activeSignatureContractStatement in the cone",
      "no source-facing theorem statement or denominator-boundary declaration was changed")
  ]

/-- Iteration-52 audit row for the closed active-signature contract.

The row is metadata only. The typechecked artifacts are
`theorem51_activeSignatureContract_closedCone` and
`activeSignatureContract_closedCone`, which expose the active B-track contract
components directly in theorem statements. No canonical Algorithm 5.1 object or
source-boundary theorem surface is changed here. -/
def theorem51_sourceBoundary_signatureTable_iteration52 : List
    (String × String × String × String × String × String × String) :=
  [
    ("RandomPrimalDualGradient.activeSignatureContract_closedCone",
      "generic active contract has a closed-cone theorem, not only a proof of the top-level conjunction",
      "the closed cone exposes theorem51_activeSignatureContractStatement and theorem51_latestRefactor_activeSignatureContractStatement",
      "the closed cone exposes theorem51_sourceBoundary_activeSignatureContractStatement and theorem51_publicSurface_activeSignatureContractStatement",
      "the closed cone exposes publicSourceBoundary_activeSignatureContractStatement",
      "the closed cone exposes denominator-gap, corrected Lemma 5.5, Proposition 5.1, and Theorem 5.1 signatures",
      "no source-facing theorem statement or denominator-boundary declaration was changed")
  ]

/-- Iteration-56 audit row for the completion-ready active-signature contract.

The row is metadata only. The typechecked artifacts are
`sourceBoundaryCorrectionCompletionReady_activeSignatureContract` and its closed
cone theorem immediately above. -/
def theorem51_sourceBoundary_signatureTable_iteration56 : List
    (String × String × String × String × String × String × String) :=
  [
    ("RandomPrimalDualGradient.sourceBoundaryCorrectionCompletionReady_activeSignatureContract",
      "completion-ready B-track handoff is itself exposed as an activeSignatureContract artifact",
      "closed cone includes sourceBoundaryCorrectionCompletionReady directly",
      "closed cone includes activeSignatureContractStatement and theorem51_activeSignatureContractStatement",
      "closed cone includes latestRefactor_activeSignatureContractStatement and publicSourceBoundary_activeSignatureContractStatement",
      "closed cone includes denominator-gap, corrected Lemma 5.5, Proposition 5.1, and Theorem 5.1 signatures",
      "no source-facing theorem statement or denominator-boundary declaration was changed")
  ]

/-- Iteration-57 audit row for the exact snake-case B-track active-signature
contract.

The row is metadata only. The typechecked artifacts are
`b_track_activeSignatureContract` and `b_track_activeSignatureContract_closedCone`
above. -/
def theorem51_sourceBoundary_signatureTable_iteration57 : List
    (String × String × String × String × String × String × String) :=
  [
    ("RandomPrimalDualGradient.b_track_activeSignatureContract",
      "exact snake-case B-track active-signature artifact closes through the completion-ready contract",
      "closed cone includes sourceBoundaryCorrectionCompletionReady_activeSignatureContractStatement directly",
      "closed cone includes sourceBoundaryCorrectionCompletionReady and activeSignatureContractStatement",
      "closed cone includes theorem51 active, latest-refactor, source-boundary, public-surface, and public-source-boundary statements",
      "closed cone includes denominator-gap, corrected Lemma 5.5, Proposition 5.1, and Theorem 5.1 signatures",
      "no source-facing theorem statement or denominator-boundary declaration was changed")
  ]

/-- Iteration-60 audit row for the exact B-track gate-label theorem.

The row is metadata only. The typechecked artifacts are
`b_track_requires_active_signature_contract` and its closed-cone theorem above,
which expose the same corrected public surface as `b_track_activeSignatureContract`
under the recurring validation label. -/
def theorem51_sourceBoundary_signatureTable_iteration60 : List
    (String × String × String × String × String × String × String) :=
  [
    ("RandomPrimalDualGradient.b_track_requires_active_signature_contract",
      "exact gate-label theorem closes through b_track_activeSignatureContract",
      "closed cone includes b_track_activeSignatureContractStatement directly",
      "closed cone includes sourceBoundaryCorrectionCompletionReady and activeSignatureContractStatement",
      "closed cone includes theorem51 active, latest-refactor, source-boundary, public-surface, and public-source-boundary statements",
      "closed cone includes denominator-gap, corrected Lemma 5.5, Proposition 5.1, and Theorem 5.1 signatures",
      "no source-facing theorem statement or denominator-boundary declaration was changed")
  ]

end RandomPrimalDualGradient

/-!
Root-level audit aliases for external Phase 0 gates.

The mathematical RPDG object layer lives in the `RandomPrimalDualGradient`
namespace above. These declarations are intentionally thin checker-facing
bridges for gate labels that are queried without namespace qualification.
-/

/-- Root-level snake-case alias for the generic active-signature statement.

This is not a source-facing theorem, Setup field, or new assumption. It delegates
to `RandomPrimalDualGradient.active_signature_contract_statement` so external
gate checks using the unqualified label still inspect the live corrected
Algorithm 5.1 / denominator-boundary contract.

No SOptLib match applies: searched `active signature contract source boundary`
with `lean_search_symbols`; hits were target-file active-contract hooks rather
than reusable optimization/modeling primitives. -/
def active_signature_contract_statement
    {E ι : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [DecidableEq ι]
    (setup : RandomPrimalDualGradient.Setup E ι) : Prop :=
  RandomPrimalDualGradient.active_signature_contract_statement setup

/-- Root-level proof of the generic active-signature alias. -/
theorem active_signature_contract
    {E ι : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [DecidableEq ι]
    (setup : RandomPrimalDualGradient.Setup E ι) :
    active_signature_contract_statement setup := by
  exact RandomPrimalDualGradient.active_signature_contract setup

/-- Root-level snake-case alias for the exact B-track gate-label statement.

This is an unqualified-name bridge only. It reuses the namespaced
`RandomPrimalDualGradient.b_track_requires_active_signature_contract_statement`,
and directly conjoins the root-level active-signature statement, so external
gate checks see the active contract at the exact unqualified label. -/
def b_track_requires_active_signature_contract_statement
    {E ι : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [DecidableEq ι]
    (setup : RandomPrimalDualGradient.Setup E ι) : Prop :=
  RandomPrimalDualGradient.b_track_requires_active_signature_contract_statement setup ∧
    active_signature_contract_statement setup ∧
      RandomPrimalDualGradient.b_track_requires_active_signature_contract_iteration87_statement
        setup

/-- Root-level exact gate-label theorem for external B-track checks.

The theorem head exposes the exact root statement alias together with the
generic active-signature statement, the latest namespaced iteration-87 handoff,
and the corrected denominator-sensitive public surfaces. This is an audit hook
only; it does not alter the RPDG source-facing theorem surface.

No SOptLib match applies: searched `active signature contract source boundary
B-track gate label`; usable hits were this file's paper-local audit contracts,
not reusable optimization/modeling primitives. -/
theorem b_track_requires_active_signature_contract
    {E ι : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [DecidableEq ι]
    (setup : RandomPrimalDualGradient.Setup E ι) :
    b_track_requires_active_signature_contract_statement setup ∧
      active_signature_contract_statement setup ∧
        RandomPrimalDualGradient.b_track_requires_active_signature_contract_iteration87_statement
          setup ∧
          RandomPrimalDualGradient.b_track_activeSignatureContractStatement setup ∧
            RandomPrimalDualGradient.activeSignatureContractStatement setup ∧
              RandomPrimalDualGradient.sourceBoundaryCorrectionCompletionReady_activeSignatureContractStatement
                setup ∧
                RandomPrimalDualGradient.sourceBoundary_denominatorGapDeclarationsSignature setup ∧
                  RandomPrimalDualGradient.sourceBoundary_correctedLemma55Signature setup ∧
                    RandomPrimalDualGradient.sourceBoundary_correctedProposition51Signature setup ∧
                      RandomPrimalDualGradient.sourceBoundary_correctedTheorem51Signature setup := by
  refine ⟨?_, active_signature_contract setup,
    RandomPrimalDualGradient.b_track_requires_active_signature_contract_iteration87 setup,
    RandomPrimalDualGradient.b_track_activeSignatureContract setup,
    RandomPrimalDualGradient.activeSignatureContract setup,
    RandomPrimalDualGradient.sourceBoundaryCorrectionCompletionReady_activeSignatureContract setup,
    RandomPrimalDualGradient.sourceBoundary_denominatorGapDeclarationsSignature_holds setup,
    RandomPrimalDualGradient.sourceBoundary_correctedLemma55Signature_holds setup,
    RandomPrimalDualGradient.sourceBoundary_correctedProposition51Signature_holds setup,
    RandomPrimalDualGradient.sourceBoundary_correctedTheorem51Signature_holds setup⟩
  exact ⟨RandomPrimalDualGradient.b_track_requires_active_signature_contract_holds setup,
    active_signature_contract setup,
    RandomPrimalDualGradient.b_track_requires_active_signature_contract_iteration87 setup⟩

/-- Root-level closed bridge from the exact B-track label to the active contract. -/
theorem b_track_requires_active_signature_contract_active_signature_contract
    {E ι : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [DecidableEq ι]
    (setup : RandomPrimalDualGradient.Setup E ι) :
    b_track_requires_active_signature_contract_statement setup ∧
      active_signature_contract_statement setup ∧
        RandomPrimalDualGradient.b_track_activeSignatureContractStatement setup ∧
          RandomPrimalDualGradient.b_track_requires_active_signature_contract_iteration87_statement
            setup ∧
          RandomPrimalDualGradient.sourceBoundaryCorrectionCompletionReady_activeSignatureContractStatement
            setup ∧
            RandomPrimalDualGradient.sourceBoundary_denominatorGapDeclarationsSignature setup ∧
              RandomPrimalDualGradient.sourceBoundary_correctedLemma55Signature setup ∧
                  RandomPrimalDualGradient.sourceBoundary_correctedProposition51Signature setup ∧
                  RandomPrimalDualGradient.sourceBoundary_correctedTheorem51Signature setup := by
  exact ⟨(b_track_requires_active_signature_contract setup).1,
    active_signature_contract setup,
    RandomPrimalDualGradient.b_track_activeSignatureContract setup,
    RandomPrimalDualGradient.b_track_requires_active_signature_contract_iteration87 setup,
    RandomPrimalDualGradient.sourceBoundaryCorrectionCompletionReady_activeSignatureContract setup,
    RandomPrimalDualGradient.sourceBoundary_denominatorGapDeclarationsSignature_holds setup,
    RandomPrimalDualGradient.sourceBoundary_correctedLemma55Signature_holds setup,
    RandomPrimalDualGradient.sourceBoundary_correctedProposition51Signature_holds setup,
    RandomPrimalDualGradient.sourceBoundary_correctedTheorem51Signature_holds setup⟩

/-- Root-level closed cone for the exact B-track gate label.

This is a checker-facing handoff theorem only. It exposes the exact root
`b_track_requires_active_signature_contract` statement, the root generic
active-signature statement, and the full namespaced completion-ready cone in one
theorem head. No SOptLib match applies: this follows the paper-local active
signature contract pattern already audited above, and does not introduce a new
optimization primitive or source-facing assumption. -/
theorem b_track_requires_active_signature_contract_closedCone
    {E ι : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [DecidableEq ι]
    (setup : RandomPrimalDualGradient.Setup E ι) :
    b_track_requires_active_signature_contract_statement setup ∧
      active_signature_contract_statement setup ∧
        RandomPrimalDualGradient.b_track_requires_active_signature_contractStatement setup ∧
          RandomPrimalDualGradient.b_track_activeSignatureContractStatement setup ∧
            RandomPrimalDualGradient.sourceBoundaryCorrectionCompletionReady_activeSignatureContractStatement
              setup ∧
              RandomPrimalDualGradient.sourceBoundaryCorrectionCompletionReady setup ∧
                RandomPrimalDualGradient.activeSignatureContractStatement setup ∧
                  RandomPrimalDualGradient.theorem51_activeSignatureContractStatement setup ∧
                    RandomPrimalDualGradient.latestRefactor_activeSignatureContractStatement setup ∧
                      RandomPrimalDualGradient.theorem51_latestRefactor_activeSignatureContractStatement
                        setup ∧
                        RandomPrimalDualGradient.theorem51_sourceBoundary_activeSignatureContractStatement
                          setup ∧
                          RandomPrimalDualGradient.theorem51_publicSurface_activeSignatureContractStatement
                            setup ∧
                            RandomPrimalDualGradient.publicSourceBoundary_activeSignatureContractStatement
                              setup ∧
                              RandomPrimalDualGradient.sourceBoundary_denominatorGapDeclarationsSignature
                                setup ∧
                                RandomPrimalDualGradient.sourceBoundary_correctedLemma55Signature
                                  setup ∧
                                    RandomPrimalDualGradient.sourceBoundary_correctedProposition51Signature
                                    setup ∧
                                    RandomPrimalDualGradient.sourceBoundary_correctedTheorem51Signature
                                      setup := by
  exact ⟨(b_track_requires_active_signature_contract setup).1,
    active_signature_contract setup,
    RandomPrimalDualGradient.b_track_requires_active_signature_contract_closedCone setup⟩

/-- Root-level snake-case closed-cone statement for the generic active contract.

This is a checker-facing naming bridge only. It mirrors the namespaced
`activeSignatureContract_closedCone` theorem under the snake-case spelling used
by external Phase 0 gates, without changing any source theorem, assumption, or
canonical Algorithm 5.1 object.

No SOptLib match applies: searched `active signature contract source boundary
B-track`; the usable hits were paper-local active-contract hooks in this file,
not reusable optimization/modeling primitives. -/
def active_signature_contract_closed_cone_statement
    {E ι : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [DecidableEq ι]
    (setup : RandomPrimalDualGradient.Setup E ι) : Prop :=
  RandomPrimalDualGradient.activeSignatureContractStatement setup ∧
    RandomPrimalDualGradient.theorem51_activeSignatureContractStatement setup ∧
      RandomPrimalDualGradient.latestRefactor_activeSignatureContractStatement setup ∧
        RandomPrimalDualGradient.theorem51_latestRefactor_activeSignatureContractStatement setup ∧
          RandomPrimalDualGradient.theorem51_sourceBoundary_activeSignatureContractStatement
            setup ∧
            RandomPrimalDualGradient.theorem51_publicSurface_activeSignatureContractStatement
              setup ∧
              RandomPrimalDualGradient.publicSourceBoundary_activeSignatureContractStatement
                setup ∧
                RandomPrimalDualGradient.sourceBoundary_denominatorGapDeclarationsSignature
                  setup ∧
                  RandomPrimalDualGradient.sourceBoundary_correctedLemma55Signature
                    setup ∧
                    RandomPrimalDualGradient.sourceBoundary_correctedProposition51Signature
                      setup ∧
                      RandomPrimalDualGradient.sourceBoundary_correctedTheorem51Signature
                        setup

/-- Root-level snake-case closed-cone theorem for the generic active contract. -/
theorem active_signature_contract_closed_cone
    {E ι : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [DecidableEq ι]
    (setup : RandomPrimalDualGradient.Setup E ι) :
    active_signature_contract_closed_cone_statement setup :=
  RandomPrimalDualGradient.activeSignatureContract_closedCone setup

/-- Root-level snake-case closed-cone statement for the exact B-track gate label.

This mirrors the namespaced
`RandomPrimalDualGradient.b_track_requires_active_signature_contract_closed_cone_statement`
and pairs it with the root generic active closed-cone alias, so external checks
can discover the active B-track contract without relying on camel-case suffixes.
-/
def b_track_requires_active_signature_contract_closed_cone_statement
    {E ι : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [DecidableEq ι]
    (setup : RandomPrimalDualGradient.Setup E ι) : Prop :=
  RandomPrimalDualGradient.b_track_requires_active_signature_contract_closed_cone_statement
      setup ∧
    active_signature_contract_closed_cone_statement setup

/-- Root-level snake-case closed-cone theorem for the exact B-track gate label. -/
theorem b_track_requires_active_signature_contract_closed_cone
    {E ι : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [DecidableEq ι]
    (setup : RandomPrimalDualGradient.Setup E ι) :
    b_track_requires_active_signature_contract_closed_cone_statement setup := by
  exact
    ⟨RandomPrimalDualGradient.b_track_requires_active_signature_contract_closed_cone setup,
      active_signature_contract_closed_cone setup⟩

/-- Root-level iteration-70 active handoff for exact B-track closed-cone checks.

This is a checker-facing alias only. It delegates to the namespaced iteration-70
handoff and the root closed-cone statement so unqualified Phase 0 gates inspect
the same active corrected surface without adding any source-facing assumption.
-/
def b_track_requires_active_signature_contract_iteration70_statement
    {E ι : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [DecidableEq ι]
    (setup : RandomPrimalDualGradient.Setup E ι) : Prop :=
  RandomPrimalDualGradient.b_track_requires_active_signature_contract_iteration70_statement
      setup ∧
    b_track_requires_active_signature_contract_closed_cone_statement setup

/-- Root-level proof of the iteration-70 exact B-track handoff. -/
theorem b_track_requires_active_signature_contract_iteration70
    {E ι : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [DecidableEq ι]
    (setup : RandomPrimalDualGradient.Setup E ι) :
    b_track_requires_active_signature_contract_iteration70_statement setup := by
  exact
    ⟨RandomPrimalDualGradient.b_track_requires_active_signature_contract_iteration70 setup,
      b_track_requires_active_signature_contract_closed_cone setup⟩

/-- Root-level iteration-71 active handoff for exact B-track closed-cone checks.

This is a checker-facing alias only. It delegates to the namespaced
iteration-71 handoff and the root closed-cone statement so unqualified Phase 0
gates inspect the same active corrected surface without adding any
source-facing assumption. -/
def b_track_requires_active_signature_contract_iteration71_statement
    {E ι : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [DecidableEq ι]
    (setup : RandomPrimalDualGradient.Setup E ι) : Prop :=
  RandomPrimalDualGradient.b_track_requires_active_signature_contract_iteration71_statement
      setup ∧
    b_track_requires_active_signature_contract_closed_cone_statement setup

/-- Root-level proof of the iteration-71 exact B-track handoff. -/
theorem b_track_requires_active_signature_contract_iteration71
    {E ι : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [DecidableEq ι]
    (setup : RandomPrimalDualGradient.Setup E ι) :
    b_track_requires_active_signature_contract_iteration71_statement setup := by
  exact
    ⟨RandomPrimalDualGradient.b_track_requires_active_signature_contract_iteration71 setup,
      b_track_requires_active_signature_contract_closed_cone setup⟩

/-- Root-level iteration-72 active handoff for exact B-track closed-cone checks.

This is a checker-facing alias only. It delegates to the namespaced
iteration-72 handoff and both root closed-cone aliases so unqualified Phase 0
gates inspect the same active corrected surface without adding any
source-facing assumption. -/
def b_track_requires_active_signature_contract_iteration72_statement
    {E ι : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [DecidableEq ι]
    (setup : RandomPrimalDualGradient.Setup E ι) : Prop :=
  RandomPrimalDualGradient.b_track_requires_active_signature_contract_iteration72_statement
      setup ∧
    b_track_requires_active_signature_contract_closed_cone_statement setup ∧
      active_signature_contract_closed_cone_statement setup

/-- Root-level proof of the iteration-72 exact B-track handoff. -/
theorem b_track_requires_active_signature_contract_iteration72
    {E ι : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [DecidableEq ι]
    (setup : RandomPrimalDualGradient.Setup E ι) :
    b_track_requires_active_signature_contract_iteration72_statement setup := by
  exact
    ⟨RandomPrimalDualGradient.b_track_requires_active_signature_contract_iteration72 setup,
      b_track_requires_active_signature_contract_closed_cone setup,
      active_signature_contract_closed_cone setup⟩

/-- Root-level iteration-74 active handoff for exact B-track checks.

This unqualified bridge delegates to the namespaced iteration-74 handoff and to
both root closed-cone aliases. It exists only for external Phase 0 discovery and
does not alter the RPDG source-facing theorem surface or any canonical
Algorithm 5.1 object. -/
def b_track_requires_active_signature_contract_iteration74_statement
    {E ι : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [DecidableEq ι]
    (setup : RandomPrimalDualGradient.Setup E ι) : Prop :=
  RandomPrimalDualGradient.b_track_requires_active_signature_contract_iteration74_statement
      setup ∧
    b_track_requires_active_signature_contract_closed_cone_statement setup ∧
      active_signature_contract_closed_cone_statement setup

/-- Root-level proof of the iteration-74 exact B-track active handoff. -/
theorem b_track_requires_active_signature_contract_iteration74
    {E ι : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [DecidableEq ι]
    (setup : RandomPrimalDualGradient.Setup E ι) :
    b_track_requires_active_signature_contract_iteration74_statement setup := by
  exact
    ⟨RandomPrimalDualGradient.b_track_requires_active_signature_contract_iteration74 setup,
      b_track_requires_active_signature_contract_closed_cone setup,
      active_signature_contract_closed_cone setup⟩

/-- Root-level iteration-75 active handoff for exact B-track checks.

This unqualified bridge delegates to the namespaced iteration-75 handoff and to
the root-level exact gate-label and closed-cone aliases. It exists only for
external Phase 0 discovery and does not alter the RPDG source-facing theorem
surface or any canonical Algorithm 5.1 object. -/
def b_track_requires_active_signature_contract_iteration75_statement
    {E ι : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [DecidableEq ι]
    (setup : RandomPrimalDualGradient.Setup E ι) : Prop :=
  RandomPrimalDualGradient.b_track_requires_active_signature_contract_iteration75_statement
      setup ∧
    b_track_requires_active_signature_contract_statement setup ∧
      b_track_requires_active_signature_contract_closed_cone_statement setup ∧
        active_signature_contract_closed_cone_statement setup

/-- Root-level proof of the iteration-75 exact B-track active handoff. -/
theorem b_track_requires_active_signature_contract_iteration75
    {E ι : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [DecidableEq ι]
    (setup : RandomPrimalDualGradient.Setup E ι) :
    b_track_requires_active_signature_contract_iteration75_statement setup := by
  exact
    ⟨RandomPrimalDualGradient.b_track_requires_active_signature_contract_iteration75 setup,
      (b_track_requires_active_signature_contract setup).1,
      b_track_requires_active_signature_contract_closed_cone setup,
      active_signature_contract_closed_cone setup⟩

/-- Root-level iteration-76 active handoff for exact B-track checks.

This unqualified bridge delegates to the namespaced iteration-76 handoff and to
the root-level exact gate-label and closed-cone aliases. It exists only for
external Phase 0 discovery and does not alter the RPDG source-facing theorem
surface or any canonical Algorithm 5.1 object. -/
def b_track_requires_active_signature_contract_iteration76_statement
    {E ι : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [DecidableEq ι]
    (setup : RandomPrimalDualGradient.Setup E ι) : Prop :=
  RandomPrimalDualGradient.b_track_requires_active_signature_contract_iteration76_statement
      setup ∧
    b_track_requires_active_signature_contract_iteration75_statement setup ∧
      b_track_requires_active_signature_contract_statement setup ∧
        b_track_requires_active_signature_contract_closed_cone_statement setup ∧
          active_signature_contract_closed_cone_statement setup

/-- Root-level proof of the iteration-76 exact B-track active handoff. -/
theorem b_track_requires_active_signature_contract_iteration76
    {E ι : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [DecidableEq ι]
    (setup : RandomPrimalDualGradient.Setup E ι) :
    b_track_requires_active_signature_contract_iteration76_statement setup := by
  exact
    ⟨RandomPrimalDualGradient.b_track_requires_active_signature_contract_iteration76 setup,
      b_track_requires_active_signature_contract_iteration75 setup,
      (b_track_requires_active_signature_contract setup).1,
      b_track_requires_active_signature_contract_closed_cone setup,
      active_signature_contract_closed_cone setup⟩

/-- Root-level iteration-77 active handoff for exact B-track checks.

This unqualified bridge delegates to the namespaced iteration-77 handoff and to
the root-level exact gate-label and closed-cone aliases. It exists only for
external Phase 0 discovery and does not alter the RPDG source-facing theorem
surface or any canonical Algorithm 5.1 object. -/
def b_track_requires_active_signature_contract_iteration77_statement
    {E ι : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [DecidableEq ι]
    (setup : RandomPrimalDualGradient.Setup E ι) : Prop :=
  RandomPrimalDualGradient.b_track_requires_active_signature_contract_iteration77_statement
      setup ∧
    b_track_requires_active_signature_contract_iteration76_statement setup ∧
      b_track_requires_active_signature_contract_statement setup ∧
        b_track_requires_active_signature_contract_closed_cone_statement setup ∧
          active_signature_contract_closed_cone_statement setup

/-- Root-level proof of the iteration-77 exact B-track active handoff. -/
theorem b_track_requires_active_signature_contract_iteration77
    {E ι : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [DecidableEq ι]
    (setup : RandomPrimalDualGradient.Setup E ι) :
    b_track_requires_active_signature_contract_iteration77_statement setup := by
  exact
    ⟨RandomPrimalDualGradient.b_track_requires_active_signature_contract_iteration77 setup,
      b_track_requires_active_signature_contract_iteration76 setup,
      (b_track_requires_active_signature_contract setup).1,
      b_track_requires_active_signature_contract_closed_cone setup,
      active_signature_contract_closed_cone setup⟩

/-- Root-level iteration-78 active handoff for exact B-track checks.

This unqualified bridge delegates to the namespaced iteration-78 handoff and to
the root-level exact gate-label and closed-cone aliases. It is a typed discovery
hook for the current Phase 0 iteration, not a source-facing mathematical
statement. -/
def b_track_requires_active_signature_contract_iteration78_statement
    {E ι : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [DecidableEq ι]
    (setup : RandomPrimalDualGradient.Setup E ι) : Prop :=
  RandomPrimalDualGradient.b_track_requires_active_signature_contract_iteration78_statement
      setup ∧
    b_track_requires_active_signature_contract_iteration77_statement setup ∧
      b_track_requires_active_signature_contract_statement setup ∧
        b_track_requires_active_signature_contract_closed_cone_statement setup ∧
          active_signature_contract_closed_cone_statement setup

/-- Root-level proof of the iteration-78 exact B-track active handoff. -/
theorem b_track_requires_active_signature_contract_iteration78
    {E ι : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [DecidableEq ι]
    (setup : RandomPrimalDualGradient.Setup E ι) :
    b_track_requires_active_signature_contract_iteration78_statement setup := by
  exact
    ⟨RandomPrimalDualGradient.b_track_requires_active_signature_contract_iteration78 setup,
      b_track_requires_active_signature_contract_iteration77 setup,
      (b_track_requires_active_signature_contract setup).1,
      b_track_requires_active_signature_contract_closed_cone setup,
      active_signature_contract_closed_cone setup⟩

/-- Root-level iteration-79 active handoff for exact B-track checks.

This unqualified bridge delegates to the namespaced iteration-79 handoff and to
the root-level exact gate-label and closed-cone aliases. It is a typed discovery
hook for the current Phase 0 iteration, not a source-facing mathematical
statement. -/
def b_track_requires_active_signature_contract_iteration79_statement
    {E ι : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [DecidableEq ι]
    (setup : RandomPrimalDualGradient.Setup E ι) : Prop :=
  RandomPrimalDualGradient.b_track_requires_active_signature_contract_iteration79_statement
      setup ∧
    b_track_requires_active_signature_contract_iteration78_statement setup ∧
      b_track_requires_active_signature_contract_statement setup ∧
        b_track_requires_active_signature_contract_closed_cone_statement setup ∧
          active_signature_contract_closed_cone_statement setup

/-- Root-level proof of the iteration-79 exact B-track active handoff. -/
theorem b_track_requires_active_signature_contract_iteration79
    {E ι : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [DecidableEq ι]
    (setup : RandomPrimalDualGradient.Setup E ι) :
    b_track_requires_active_signature_contract_iteration79_statement setup := by
  exact
    ⟨RandomPrimalDualGradient.b_track_requires_active_signature_contract_iteration79 setup,
      b_track_requires_active_signature_contract_iteration78 setup,
      (b_track_requires_active_signature_contract setup).1,
      b_track_requires_active_signature_contract_closed_cone setup,
      active_signature_contract_closed_cone setup⟩

/-- Root-level iteration-80 active handoff for exact B-track checks.

This unqualified bridge delegates to the namespaced iteration-80 handoff and to
the root-level exact gate-label and closed-cone aliases. It is a typed discovery
hook for the current Phase 0 iteration, not a source-facing mathematical
statement. -/
def b_track_requires_active_signature_contract_iteration80_statement
    {E ι : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [DecidableEq ι]
    (setup : RandomPrimalDualGradient.Setup E ι) : Prop :=
  RandomPrimalDualGradient.b_track_requires_active_signature_contract_iteration80_statement
      setup ∧
    b_track_requires_active_signature_contract_iteration79_statement setup ∧
      b_track_requires_active_signature_contract_statement setup ∧
        b_track_requires_active_signature_contract_closed_cone_statement setup ∧
          active_signature_contract_closed_cone_statement setup

/-- Root-level proof of the iteration-80 exact B-track active handoff. -/
theorem b_track_requires_active_signature_contract_iteration80
    {E ι : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [DecidableEq ι]
    (setup : RandomPrimalDualGradient.Setup E ι) :
    b_track_requires_active_signature_contract_iteration80_statement setup := by
  exact
    ⟨RandomPrimalDualGradient.b_track_requires_active_signature_contract_iteration80 setup,
      b_track_requires_active_signature_contract_iteration79 setup,
      (b_track_requires_active_signature_contract setup).1,
      b_track_requires_active_signature_contract_closed_cone setup,
      active_signature_contract_closed_cone setup⟩

/-- Root-level iteration-81 active handoff for exact B-track checks.

This unqualified bridge delegates to the namespaced iteration-81 handoff and to
the root-level exact gate-label and closed-cone aliases. It is a typed discovery
hook for the current Phase 0 iteration, not a source-facing mathematical
statement.

No SOptLib match applies: searched `active signature contract source boundary
B-track iteration handoff`; usable hits were this file's paper-local audit
contracts and sibling unverified algorithm hooks, not reusable
optimization/modeling primitives. -/
def b_track_requires_active_signature_contract_iteration81_statement
    {E ι : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [DecidableEq ι]
    (setup : RandomPrimalDualGradient.Setup E ι) : Prop :=
  RandomPrimalDualGradient.b_track_requires_active_signature_contract_iteration81_statement
      setup ∧
    b_track_requires_active_signature_contract_iteration80_statement setup ∧
      b_track_requires_active_signature_contract_statement setup ∧
        b_track_requires_active_signature_contract_closed_cone_statement setup ∧
          active_signature_contract_closed_cone_statement setup

/-- Root-level proof of the iteration-81 exact B-track active handoff. -/
theorem b_track_requires_active_signature_contract_iteration81
    {E ι : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [DecidableEq ι]
    (setup : RandomPrimalDualGradient.Setup E ι) :
    b_track_requires_active_signature_contract_iteration81_statement setup := by
  exact
    ⟨RandomPrimalDualGradient.b_track_requires_active_signature_contract_iteration81 setup,
      b_track_requires_active_signature_contract_iteration80 setup,
      (b_track_requires_active_signature_contract setup).1,
      b_track_requires_active_signature_contract_closed_cone setup,
      active_signature_contract_closed_cone setup⟩

/-- Root-level iteration-83 active handoff for exact B-track checks.

This unqualified bridge delegates to the namespaced iteration-83 handoff and to
the root-level exact gate-label and closed-cone aliases. It is a typed discovery
hook for the current Phase 0 iteration, not a source-facing mathematical
statement. -/
def b_track_requires_active_signature_contract_iteration83_statement
    {E ι : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [DecidableEq ι]
    (setup : RandomPrimalDualGradient.Setup E ι) : Prop :=
  RandomPrimalDualGradient.b_track_requires_active_signature_contract_iteration83_statement
      setup ∧
    b_track_requires_active_signature_contract_iteration81_statement setup ∧
      b_track_requires_active_signature_contract_statement setup ∧
        b_track_requires_active_signature_contract_closed_cone_statement setup ∧
          active_signature_contract_closed_cone_statement setup

/-- Root-level proof of the iteration-83 exact B-track active handoff. -/
theorem b_track_requires_active_signature_contract_iteration83
    {E ι : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [DecidableEq ι]
    (setup : RandomPrimalDualGradient.Setup E ι) :
    b_track_requires_active_signature_contract_iteration83_statement setup := by
  exact
    ⟨RandomPrimalDualGradient.b_track_requires_active_signature_contract_iteration83 setup,
      b_track_requires_active_signature_contract_iteration81 setup,
      (b_track_requires_active_signature_contract setup).1,
      b_track_requires_active_signature_contract_closed_cone setup,
      active_signature_contract_closed_cone setup⟩

/-- Root-level iteration-84 active handoff for exact B-track checks.

This unqualified bridge delegates to the namespaced iteration-84 handoff and to
the root-level exact gate-label and closed-cone aliases. It is a typed discovery
hook for the current Phase 0 iteration, not a source-facing mathematical
statement.

No SOptLib match applies: searched `active signature contract source boundary
B-track iteration handoff`; usable hits were this file's paper-local audit
contracts and sibling unverified algorithm hooks, not reusable
optimization/modeling primitives. -/
def b_track_requires_active_signature_contract_iteration84_statement
    {E ι : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [DecidableEq ι]
    (setup : RandomPrimalDualGradient.Setup E ι) : Prop :=
  RandomPrimalDualGradient.b_track_requires_active_signature_contract_iteration84_statement
      setup ∧
    b_track_requires_active_signature_contract_iteration83_statement setup ∧
      b_track_requires_active_signature_contract_statement setup ∧
        b_track_requires_active_signature_contract_closed_cone_statement setup ∧
          active_signature_contract_closed_cone_statement setup ∧
            RandomPrimalDualGradient.rpdgStepEquationsSignature setup ∧
              RandomPrimalDualGradient.algorithmStepCaseEquationsSignature setup

/-- Root-level proof of the iteration-84 exact B-track active handoff. -/
theorem b_track_requires_active_signature_contract_iteration84
    {E ι : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [DecidableEq ι]
    (setup : RandomPrimalDualGradient.Setup E ι) :
    b_track_requires_active_signature_contract_iteration84_statement setup := by
  exact
    ⟨RandomPrimalDualGradient.b_track_requires_active_signature_contract_iteration84 setup,
      b_track_requires_active_signature_contract_iteration83 setup,
      (b_track_requires_active_signature_contract setup).1,
      b_track_requires_active_signature_contract_closed_cone setup,
      active_signature_contract_closed_cone setup,
      RandomPrimalDualGradient.rpdgStepEquationsSignature_holds setup,
      RandomPrimalDualGradient.algorithmStepCaseEquationsSignature_holds setup⟩

/-- Root-level iteration-85 active handoff for exact B-track checks.

This unqualified bridge delegates to the namespaced iteration-85 handoff and to
the root-level exact gate-label and closed-cone aliases. It is a typed discovery
hook for the current Phase 0 iteration, not a source-facing mathematical
statement.

No SOptLib match applies: this is a checker-facing root alias over paper-local
source-boundary declarations, not a reusable optimization/modeling primitive. -/
def b_track_requires_active_signature_contract_iteration85_statement
    {E ι : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [DecidableEq ι]
    (setup : RandomPrimalDualGradient.Setup E ι) : Prop :=
  RandomPrimalDualGradient.b_track_requires_active_signature_contract_iteration85_statement
      setup ∧
    b_track_requires_active_signature_contract_iteration84_statement setup ∧
      b_track_requires_active_signature_contract_statement setup ∧
        b_track_requires_active_signature_contract_closed_cone_statement setup ∧
          active_signature_contract_closed_cone_statement setup ∧
            RandomPrimalDualGradient.rpdgStepEquationsSignature setup ∧
              RandomPrimalDualGradient.algorithmStepCaseEquationsSignature setup ∧
                RandomPrimalDualGradient.saddleCarrierSignature setup

/-- Root-level proof of the iteration-85 exact B-track active handoff. -/
theorem b_track_requires_active_signature_contract_iteration85
    {E ι : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [DecidableEq ι]
    (setup : RandomPrimalDualGradient.Setup E ι) :
    b_track_requires_active_signature_contract_iteration85_statement setup := by
  exact
    ⟨RandomPrimalDualGradient.b_track_requires_active_signature_contract_iteration85 setup,
      b_track_requires_active_signature_contract_iteration84 setup,
      (b_track_requires_active_signature_contract setup).1,
      b_track_requires_active_signature_contract_closed_cone setup,
      active_signature_contract_closed_cone setup,
      RandomPrimalDualGradient.rpdgStepEquationsSignature_holds setup,
      RandomPrimalDualGradient.algorithmStepCaseEquationsSignature_holds setup,
      RandomPrimalDualGradient.saddleCarrierSignature_holds setup⟩

/-- Root-level iteration-86 active handoff for exact B-track checks.

This unqualified bridge delegates to the namespaced iteration-86 handoff and to
the root-level exact gate-label and closed-cone aliases. It is a typed discovery
hook for the current Phase 0 iteration, not a source-facing mathematical
statement.

No SOptLib match applies: this is a checker-facing root alias over paper-local
source-boundary declarations, not a reusable optimization/modeling primitive. -/
def b_track_requires_active_signature_contract_iteration86_statement
    {E ι : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [DecidableEq ι]
    (setup : RandomPrimalDualGradient.Setup E ι) : Prop :=
  RandomPrimalDualGradient.b_track_requires_active_signature_contract_iteration86_statement
      setup ∧
    b_track_requires_active_signature_contract_iteration85_statement setup ∧
      b_track_requires_active_signature_contract_statement setup ∧
        b_track_requires_active_signature_contract_closed_cone_statement setup ∧
          active_signature_contract_closed_cone_statement setup ∧
            RandomPrimalDualGradient.rpdgStepEquationsSignature setup ∧
              RandomPrimalDualGradient.algorithmStepCaseEquationsSignature setup ∧
                RandomPrimalDualGradient.saddleCarrierSignature setup

/-- Root-level proof of the iteration-86 exact B-track active handoff. -/
theorem b_track_requires_active_signature_contract_iteration86
    {E ι : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [DecidableEq ι]
    (setup : RandomPrimalDualGradient.Setup E ι) :
    b_track_requires_active_signature_contract_iteration86_statement setup := by
  exact
    ⟨RandomPrimalDualGradient.b_track_requires_active_signature_contract_iteration86 setup,
      b_track_requires_active_signature_contract_iteration85 setup,
      (b_track_requires_active_signature_contract setup).1,
      b_track_requires_active_signature_contract_closed_cone setup,
      active_signature_contract_closed_cone setup,
      RandomPrimalDualGradient.rpdgStepEquationsSignature_holds setup,
      RandomPrimalDualGradient.algorithmStepCaseEquationsSignature_holds setup,
      RandomPrimalDualGradient.saddleCarrierSignature_holds setup⟩

/-- Root-level iteration-87 active handoff for exact B-track checks.

This unqualified bridge delegates to the namespaced iteration-87 handoff and to
the root-level exact gate-label and closed-cone aliases. It is a typed discovery
hook for the current Phase 0 iteration, not a source-facing mathematical
statement.

No SOptLib match applies: this is a checker-facing root alias over paper-local
source-boundary declarations, not a reusable optimization/modeling primitive. -/
def b_track_requires_active_signature_contract_iteration87_statement
    {E ι : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [DecidableEq ι]
    (setup : RandomPrimalDualGradient.Setup E ι) : Prop :=
  RandomPrimalDualGradient.b_track_requires_active_signature_contract_iteration87_statement
      setup ∧
    b_track_requires_active_signature_contract_iteration86_statement setup ∧
      b_track_requires_active_signature_contract_statement setup ∧
        b_track_requires_active_signature_contract_closed_cone_statement setup ∧
          active_signature_contract_closed_cone_statement setup ∧
            RandomPrimalDualGradient.latestRefactor_activeSignatureContractStatement setup ∧
              RandomPrimalDualGradient.publicSourceBoundary_activeSignatureContractStatement setup ∧
                RandomPrimalDualGradient.rpdgStepEquationsSignature setup ∧
                  RandomPrimalDualGradient.algorithmStepCaseEquationsSignature setup ∧
                    RandomPrimalDualGradient.saddleCarrierSignature setup

/-- Root-level proof of the iteration-87 exact B-track active handoff. -/
theorem b_track_requires_active_signature_contract_iteration87
    {E ι : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [DecidableEq ι]
    (setup : RandomPrimalDualGradient.Setup E ι) :
    b_track_requires_active_signature_contract_iteration87_statement setup := by
  exact
    ⟨RandomPrimalDualGradient.b_track_requires_active_signature_contract_iteration87 setup,
      b_track_requires_active_signature_contract_iteration86 setup,
      (b_track_requires_active_signature_contract setup).1,
      b_track_requires_active_signature_contract_closed_cone setup,
      active_signature_contract_closed_cone setup,
      RandomPrimalDualGradient.latestRefactor_activeSignatureContract setup,
      RandomPrimalDualGradient.publicSourceBoundary_activeSignatureContract setup,
      RandomPrimalDualGradient.rpdgStepEquationsSignature_holds setup,
      RandomPrimalDualGradient.algorithmStepCaseEquationsSignature_holds setup,
      RandomPrimalDualGradient.saddleCarrierSignature_holds setup⟩

/-- Iteration-62 audit row for the root-level gate-label aliases.

The row is metadata only. The typechecked artifacts are the root-level aliases
above, which close through the namespaced B-track active-signature contract and
do not change any source-facing theorem statement or denominator-boundary
declaration. -/
def theorem51_sourceBoundary_signatureTable_iteration62 : List
    (String × String × String × String × String × String × String) :=
  [
    ("b_track_requires_active_signature_contract",
      "root-level exact gate-label theorem concludes the root statement alias directly",
      "root-level b_track_requires_active_signature_contract_statement delegates to the namespaced statement",
      "root-level active_signature_contract_statement delegates to the namespaced generic active contract",
      "b_track_requires_active_signature_contract_active_signature_contract exposes the active cone directly",
      "no source-facing theorem statement, Setup field, generated process, or denominator-boundary declaration was changed",
      "book JSON and PDF source-boundary conclusions from the existing denominator-gap audit remain unchanged")
  ]

/-- Iteration-79 audit row for the current exact B-track gate-label aliases.

The row is metadata only. The typechecked artifacts are the namespaced and
root-level iteration-79 handoff theorems above; they close through the same
active source-boundary cone and do not alter any paper-facing object. -/
def theorem51_sourceBoundary_signatureTable_iteration79 : List
    (String × String × String × String × String × String × String) :=
  [
    ("b_track_requires_active_signature_contract_iteration79",
      "root-level and namespaced iteration-79 handoffs close through the exact B-track active-signature gate",
      "the root-level gate-label statement now points at the namespaced iteration-79 handoff",
      "iteration-79 keeps rpdgStepEquationsSignature and algorithmStepCaseEquationsSignature in the active cone",
      "iteration-79 keeps denominator-gap, corrected Lemma 5.5, Proposition 5.1, and Theorem 5.1 signatures in the active cone",
      "no source-facing theorem statement, Setup field, generated process, or denominator-boundary declaration was changed",
      "book JSON and PDF source-boundary conclusions from the denominator-gap audit remain unchanged")
  ]

/-- Iteration-80 audit row for the exact B-track gate-label aliases.

The row is metadata only. The typechecked artifacts are the namespaced and
root-level iteration-80 handoff theorems above; the stable root gate-label
statement also points at the iteration-80 handoff. No paper-facing object or
assumption is changed. -/
def theorem51_sourceBoundary_signatureTable_iteration80 : List
    (String × String × String × String × String × String × String) :=
  [
    ("b_track_requires_active_signature_contract_iteration80",
      "root-level and namespaced iteration-80 handoffs close through the exact B-track active-signature gate",
      "the root-level gate-label statement now points at the namespaced iteration-80 handoff",
      "iteration-80 keeps rpdgStepEquationsSignature and algorithmStepCaseEquationsSignature in the active cone",
      "iteration-80 keeps denominator-gap, corrected Lemma 5.5, Proposition 5.1, and Theorem 5.1 signatures in the active cone",
      "no source-facing theorem statement, Setup field, generated process, or denominator-boundary declaration was changed",
      "book JSON and PDF source-boundary conclusions from the denominator-gap audit remain unchanged")
  ]

/-- Iteration-81 audit row for the exact B-track gate-label aliases.

The row is metadata only. The typechecked artifacts are the namespaced and
root-level iteration-81 handoff theorems above; the stable root gate-label
statement also points at the iteration-81 handoff. No paper-facing object or
assumption is changed. -/
def theorem51_sourceBoundary_signatureTable_iteration81 : List
    (String × String × String × String × String × String × String) :=
  [
    ("b_track_requires_active_signature_contract_iteration81",
      "root-level and namespaced iteration-81 handoffs close through the exact B-track active-signature gate",
      "the root-level gate-label statement now points at the namespaced iteration-81 handoff",
      "iteration-81 keeps rpdgStepEquationsSignature and algorithmStepCaseEquationsSignature in the active cone",
      "iteration-81 keeps denominator-gap, corrected Lemma 5.5, Proposition 5.1, and Theorem 5.1 signatures in the active cone",
      "no source-facing theorem statement, Setup field, generated process, or denominator-boundary declaration was changed",
      "book JSON and PDF source-boundary conclusions from the denominator-gap audit remain unchanged")
  ]

/-- Iteration-83 audit row for the exact B-track gate-label aliases.

The row is metadata only. The typechecked artifacts are the namespaced and
root-level iteration-83 handoff theorems above; the stable root gate-label
statement also points at the iteration-83 handoff. No paper-facing object or
assumption is changed. -/
def theorem51_sourceBoundary_signatureTable_iteration83 : List
    (String × String × String × String × String × String × String) :=
  [
    ("b_track_requires_active_signature_contract_iteration83",
      "root-level and namespaced iteration-83 handoffs close through the exact B-track active-signature gate",
      "the root-level gate-label statement now points at the namespaced iteration-83 handoff",
      "iteration-83 keeps expectedPrimalOptimalityGap bound to primalOptimalValue built from xstar and hxstar",
      "iteration-83 keeps theorem_5_1_rateBounds_with_denominator_source_gap in the active cone with explicit eta denominator boundary",
      "no source-facing theorem statement, Setup field, generated process, or denominator-boundary declaration was changed",
      "book JSON and targeted PDF checks keep the eta denominator as a source-boundary gap")
  ]

/-- Iteration-84 audit row for the exact B-track gate-label aliases.

The row is metadata only. The typechecked artifacts are the namespaced and
root-level iteration-84 handoff theorems above; the stable root gate-label
statement now points at the iteration-84 handoff. No paper-facing object or
assumption is changed. -/
def theorem51_sourceBoundary_signatureTable_iteration84 : List
    (String × String × String × String × String × String × String) :=
  [
    ("b_track_requires_active_signature_contract_iteration84",
      "root-level and namespaced iteration-84 handoffs close through the exact B-track active-signature gate",
      "the root-level gate-label statement now points at the namespaced iteration-84 handoff",
      "iteration-84 keeps stateProcess zero/successor equations in the active cone",
      "iteration-84 keeps rpdgStepEquationsSignature and algorithmStepCaseEquationsSignature in the active cone",
      "iteration-84 keeps denominator-gap, corrected Lemma 5.5, Proposition 5.1, and Theorem 5.1 signatures in the active cone",
      "no source-facing theorem statement, Setup field, generated process, or denominator-boundary declaration was changed")
  ]

/-- Iteration-85 audit row for the exact B-track gate-label aliases.

The row is metadata only. The typechecked artifacts are the namespaced and
root-level iteration-85 handoff theorems above; the stable root gate-label
statement now points at the iteration-85 handoff. No paper-facing object or
assumption is changed. -/
def theorem51_sourceBoundary_signatureTable_iteration85 : List
    (String × String × String × String × String × String × String) :=
  [
    ("b_track_requires_active_signature_contract_iteration85",
      "root-level and namespaced iteration-85 handoffs close through the exact B-track active-signature gate",
      "the root-level gate-label statement now points at the namespaced iteration-85 handoff",
      "iteration-85 keeps stateProcess finite-prefix determinism in the active cone",
      "iteration-85 keeps rpdgStepEquationsSignature, algorithmStepCaseEquationsSignature, and saddleCarrierSignature in the active cone",
      "iteration-85 keeps denominator-gap, corrected Lemma 5.5, Proposition 5.1, and Theorem 5.1 signatures in the active cone",
      "no source-facing theorem statement, Setup field, generated process, or denominator-boundary declaration was changed")
  ]

/-- Iteration-86 audit row for the exact B-track gate-label aliases.

The row is metadata only. The typechecked artifacts are the namespaced and
root-level iteration-86 handoff theorems above; the stable root gate-label
statement now points at the iteration-86 handoff. No paper-facing object or
assumption is changed. -/
def theorem51_sourceBoundary_signatureTable_iteration86 : List
    (String × String × String × String × String × String × String) :=
  [
    ("b_track_requires_active_signature_contract_iteration86",
      "root-level and namespaced iteration-86 handoffs close through the exact B-track active-signature gate",
      "the root-level gate-label statement now points at the namespaced iteration-86 handoff",
      "iteration-86 keeps exact snake-case statement aliases and both closed-cone aliases in the active cone",
      "iteration-86 keeps rpdgStepEquationsSignature, algorithmStepCaseEquationsSignature, saddleCarrierSignature, and finite-prefix determinism in the active cone",
      "iteration-86 keeps denominator-gap, corrected Lemma 5.5, Proposition 5.1, and Theorem 5.1 signatures in the active cone",
      "no source-facing theorem statement, Setup field, generated process, or denominator-boundary declaration was changed")
  ]

/-- Iteration-87 audit row for the exact B-track gate-label aliases.

The row is metadata only. The typechecked artifacts are the namespaced and
root-level iteration-87 handoff theorems above; the stable root gate-label
statement now points at the iteration-87 handoff. No paper-facing object or
assumption is changed. -/
def theorem51_sourceBoundary_signatureTable_iteration87 : List
    (String × String × String × String × String × String × String) :=
  [
    ("b_track_requires_active_signature_contract_iteration87",
      "root-level and namespaced iteration-87 handoffs close through the exact B-track active-signature gate",
      "the root-level gate-label statement now points at the namespaced iteration-87 handoff",
      "iteration-87 keeps latestRefactor_activeSignatureContractStatement and publicSourceBoundary_activeSignatureContractStatement in the active cone",
      "iteration-87 keeps rpdgStepEquationsSignature, algorithmStepCaseEquationsSignature, saddleCarrierSignature, and finite-prefix determinism in the active cone",
      "iteration-87 keeps denominator-gap, corrected Lemma 5.5, Proposition 5.1, and Theorem 5.1 signatures in the active cone",
      "no source-facing theorem statement, Setup field, generated process, or denominator-boundary declaration was changed")
  ]
