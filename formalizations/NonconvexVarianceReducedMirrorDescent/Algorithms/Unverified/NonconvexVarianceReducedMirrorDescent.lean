import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import SOptLib.Model.Bregman
import SOptLib.Model.Complexity
import SOptLib.Model.Filtration
import SOptLib.Model.Objective
import SOptLib.Model.Prox
import SOptLib.Model.Selection
import SOptLib.Model.StochasticOracle
import SOptLib.Glue.Algebra
import SOptLib.Glue.Analysis
import SOptLib.Glue.Probability
import SOptLib.Layer0.ConvexFOC
import SOptLib.Layer0.Oracle
import SOptLib.Layer1.Descent
import SOptLib.Layer1.Telescope

/-!
# Nonconvex Variance-Reduced Mirror Descent

Object-layer reconstruction of Lan's nonconvex variance-reduced mirror descent
method from Section 6.5 / Algorithm 6.6 of
*First-order and Stochastic Optimization Methods for Machine Learning*.

The file defines the paper's mathematical objects before proof work: the
finite-sum objective, composite objective, Bregman prox geometry, generalized
projected-gradient map, recursive variance-reduced estimator, and the generated
iterate/estimator state sequence.  Iterates and estimator values are definitions
from Algorithm 6.6, not setup witnesses.
-/

open scoped BigOperators Gradient InnerProductSpace
open MeasureTheory

namespace SGD.NonconvexVarianceReducedMirrorDescent

/-- Paper ambient variable space `ℝⁿ`, realized as Mathlib's finite Euclidean space.

No SOptLib match: searched Euclidean finite-dimensional space candidates and found
only auxiliary finite-dimensional norm-control lemmas; Mathlib `EuclideanSpace`
is the canonical object matching Section 6.5's `X ⊆ ℝⁿ` and Euclidean norm. -/
abbrev Ambient (d : ℕ) : Type :=
  EuclideanSpace ℝ (Fin d)

variable {d : ℕ} {ι : Type*}
variable [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Uniform finite average `(card ι)⁻¹ • ∑ i, g i`.

This is the literal finite-sum formula `f(x)=m⁻¹∑ᵢf_i(x)` in Section 6.5,
realized by SOptLib's canonical finite-uniform average primitive. -/
noncomputable abbrev finiteAverage {α β : Type*} [Fintype α]
    [AddCommMonoid β] [Module ℝ β] (g : α → β) : β :=
  SOptLib.finiteUniformAverage g

@[simp]
theorem finiteAverage_def {α β : Type*} [Fintype α]
    [AddCommMonoid β] [Module ℝ β] (g : α → β) :
    finiteAverage g = (Fintype.card α : ℝ)⁻¹ • Finset.sum Finset.univ g := by
  simpa [finiteAverage] using SOptLib.finiteUniformAverage_def (g := g)

/-- One-based output support `{1,...,N}` from Algorithm 6.6. -/
def outputWindow (N : ℕ) : Finset ℕ :=
  Finset.Icc 1 N

/-- Output-index subtype for the paper's one-based random index `R ∈ {1,...,N}`. -/
abbrev OutputIndex (N : ℕ) : Type :=
  {k : ℕ // k ∈ outputWindow N}

/-- Positive one-based iteration indices `k=1,2,...` used in Section 6.5.1. -/
abbrev PositiveIteration : Type :=
  {k : ℕ // 1 ≤ k}

/-- Unit weights on `{1,...,N}` are admissible for Algorithm 6.6's uniform output PMF. -/
theorem outputWindowWeightsAdmissible (N : ℕ) (hN : 0 < N) :
    SOptLib.FiniteWindowWeightsAdmissible (outputWindow N) (fun _ : ℕ => (1 : ℝ)) := by
  exact SOptLib.FiniteWindowWeightsAdmissible.const_one (outputWindow N)
    ⟨1, by simpa [outputWindow] using Nat.succ_le_of_lt hN⟩

/-- Uniform PMF for Algorithm 6.6's output index `R` on `{1,...,N}`. -/
noncomputable def uniformOutputPMF (N : ℕ) (hN : 0 < N) : PMF (OutputIndex N) :=
  SOptLib.uniformFiniteWindowPMF (outputWindow N)
    ⟨1, by simpa [outputWindow] using Nat.succ_le_of_lt hN⟩

/-- The uniform output PMF satisfies the finite-window normalized-mass spec. -/
theorem uniformOutputPMF_spec (N : ℕ) (hN : 0 < N) :
    SOptLib.FiniteWindowPMFSpec (outputWindow N) (fun _ : ℕ => (1 : ℝ))
      (uniformOutputPMF N hN) := by
  exact SOptLib.finiteWindowPMFSpec_of_normalizedFiniteWindowPMF
    (outputWindow N) (fun _ : ℕ => (1 : ℝ))
    (outputWindowWeightsAdmissible N hN)

/-- Real atom mass `q_i` of Algorithm 6.6's input probability distribution `Q`.

Mathlib `PMF` is the canonical probability-distribution object for the paper's
input `Q={q₁,...,q_m}`.  SOptLib `smoothnessImportancePMF` was considered but
rejected for the general algorithm input because it denotes the later Theorem
6.14 / Eq. (6.5.4) specialization, not Algorithm 6.6's arbitrary `Q`. -/
noncomputable def probabilityMass (Q : PMF ι) (i : ι) : ℝ :=
  (Q i).toReal

@[simp]
theorem probabilityMass_def (Q : PMF ι) (i : ι) :
    probabilityMass Q i = (Q i).toReal := by
  rfl

/-- Support subtype for Algorithm 6.6 samples drawn from `Q`.

No SOptLib match: searched `PMF support subtype positive atom probability
distribution` and scanned `SOptLib/Model/Selection.lean`,
`SOptLib/Model/BlockSampling.lean`, and `SOptLib/Model/StochasticOracle.lean`;
they provide PMF laws and finite windows but not the paper-specific support
bridge needed for Algorithm 6.6's displayed denominator `q_i m`. -/
abbrev DistributionSupport (Q : PMF ι) : Type _ :=
  {i : ι // 0 < probabilityMass Q i}

/-- A support-index sample carries the positivity of its Algorithm 6.6 atom. -/
theorem probabilityMass_pos_of_support (Q : PMF ι) (i : DistributionSupport Q) :
    0 < probabilityMass Q i.1 :=
  i.2

/-- The denominator `q_i m` in Algorithm 6.6 is positive for sampled support indices. -/
theorem probabilityMass_mul_card_pos_of_support (Q : PMF ι) (i : DistributionSupport Q) :
    0 < probabilityMass Q i * (Fintype.card ι : ℝ) := by
  exact mul_pos (probabilityMass_pos_of_support Q i)
    (by exact_mod_cast Fintype.card_pos_iff.mpr inferInstance)

/-- Inverse-probability weighted component gradient difference
`(q_i m)⁻¹(∇f_i(x)-∇f_i(y))` on sampled support indices.

This specializes SOptLib `importance_weighted_gradient_difference` to the
literal Algorithm 6.6 normalizer `m = Fintype.card ι`; the support subtype keeps
the paper's positive-denominator boundary visible without strengthening the
input PMF. -/
noncomputable def importanceWeightedGradientDifference
    {X G : Type*} [Sub G] [SMul ℝ G]
    (Q : PMF ι) (gradF : ι → X → G) (x y : X) (i : DistributionSupport Q) : G :=
  SOptLib.importance_weighted_gradient_difference
    (fun j : ι => probabilityMass Q j) (Fintype.card ι : ℝ) gradF x y i.1

@[simp]
theorem importanceWeightedGradientDifference_def
    {X G : Type*} [Sub G] [SMul ℝ G]
    (Q : PMF ι) (gradF : ι → X → G) (x y : X) (i : DistributionSupport Q) :
    importanceWeightedGradientDifference Q gradF x y i =
      ((probabilityMass Q i.1 * (Fintype.card ι : ℝ))⁻¹) •
        (gradF i.1 x - gradF i.1 y) := by
  simp [importanceWeightedGradientDifference,
    SOptLib.importance_weighted_gradient_difference_def]

/-- Feasible finite-sum composite problem data for Eq. (6.5.1).

The fields are source-level assumptions only: `X` is closed convex, `h` is the
simple convex term, component gradients are Lipschitz with constants `Lcomp`,
and `nu` is the distance-generating function satisfying Eq. (6.2.4).  No
iterate, estimator, projected-gradient value, or prox selector is stored here. -/
structure Setup where
  /-- Feasible set `X ⊆ ℝⁿ`. -/
  X : Set (Ambient d)
  /-- Section 6.5 assumes that `X` is convex. -/
  convex_X : Convex ℝ X
  /-- Section 6.5 assumes that `X` is closed. -/
  closed_X : IsClosed X
  /-- Finite-sum component functions `f_i`. -/
  component : ι → Ambient d → ℝ
  /-- Simple, possibly nonsmooth, convex term `h`. -/
  h : Ambient d → ℝ
  /-- Source assumption: `h` is convex on `X`. -/
  convex_h : ConvexOn ℝ X h
  /-- Component smoothness constants `L_i`. -/
  Lcomp : ι → ℝ
  /-- Source assumption: each component smoothness constant is positive. -/
  Lcomp_pos : ∀ i : ι, 0 < Lcomp i
  /-- Source-backed realization of the displayed component gradients on `X`. -/
  component_hasGradientAt :
    ∀ i : ι, ∀ x ∈ X, HasGradientAt (component i) (∇ (component i) x) x
  /-- Source assumption before Eq. (6.5.2): component gradients are `L_i`-Lipschitz on `X`. -/
  component_lipschitz_grad :
    ∀ i : ι, ∀ x ∈ X, ∀ y ∈ X,
      ‖∇ (component i) x - ∇ (component i) y‖ ≤ Lcomp i * ‖x - y‖
  /-- Smoothness scale `L = (1/m)∑ᵢ L_i` from Eq. (6.5.2). -/
  L : ℝ
  /-- Eq. (6.5.2), modeled by the canonical finite-uniform average formula. -/
  L_eq_average : L = finiteAverage Lcomp
  /-- Distance-generating potential `ν`. -/
  nu : Ambient d → ℝ
  /-- Section 6.2.1 states that the distance-generating function is continuously differentiable. -/
  nu_contDiffOn : ContDiffOn ℝ 1 nu X
  /-- Source-backed realization of the displayed gradient of the distance-generating function. -/
  nu_hasGradientAt : ∀ x ∈ X, HasGradientAt nu (∇ nu x) x
  /-- Source assumption Eq. (6.2.4): one-strong monotonicity of `∇ν` on `X`. -/
  dgf_strong :
    ∀ x ∈ X, ∀ z ∈ X,
      ‖x - z‖ ^ 2 ≤ ⟪x - z, ∇ nu x - ∇ nu z⟫_ℝ
  /-- Source assumption after Eq. (6.5.2): `Ψ` is bounded below over `X`. -/
  psi_bounded_below :
    ∃ lower : ℝ, ∀ x ∈ X,
      lower ≤ SOptLib.compositeObjective
        (fun y : Ambient d => finiteAverage (fun i : ι => component i y)) h x
  /-- Source assumption after Eq. (6.2.6): the generalized projection problem is
  solvable for every feasible base point, oracle vector, and positive stepsize. -/
  prox_solvable :
    ∀ (x : {x : Ambient d // x ∈ X}) (g : Ambient d) (γ : ℝ), 0 < γ →
      ∃ z : {x : Ambient d // x ∈ X},
        IsMinOn
            (SOptLib.proxObjective
            (fun a b : {x : Ambient d // x ∈ X} =>
              bregmanDivergence nu a.1 b.1)
            (fun u : {x : Ambient d // x ∈ X} => h u.1)
            (fun u : {x : Ambient d // x ∈ X} => u.1)
            x g γ)
          Set.univ z

/-- Feasible-point subtype for the paper carrier `X`. -/
abbrev Feasible (S : Setup (d := d) (ι := ι)) : Type _ :=
  {x : Ambient d // x ∈ S.X}

namespace Setup

variable (S : Setup (d := d) (ι := ι))

/-- Component gradient `∇f_i(x)`.

This is a local name for Mathlib's gradient notation; no SOptLib primitive is
needed because the paper object is exactly the component derivative appearing
in Algorithm 6.6. -/
noncomputable def componentGradient (i : ι) (x : Ambient d) : Ambient d :=
  ∇ (S.component i) x

/-- Finite-sum objective `f(x)=m⁻¹∑ᵢ f_i(x)` from Section 6.5.

Aligns with SOptLib `finiteUniformAverage`; candidate `compositeObjective` was
not enough by itself because Eq. (6.5.1) first defines the finite average `f`
before adding `h`. -/
noncomputable def finiteSumObjective (x : Ambient d) : ℝ :=
  finiteAverage (fun i : ι => S.component i x)

@[simp]
theorem finiteSumObjective_def (x : Ambient d) :
    finiteSumObjective S x =
      finiteAverage (fun i : ι => S.component i x) := by
  rfl

/-- Full finite-sum gradient `∇f(x)` represented as the average of component gradients.

This specializes SOptLib's finite-uniform average to the component-gradient
family used in Algorithm 6.6.  The calculus bridge identifying it with the
Mathlib gradient of `finiteSumObjective` is a theorem, not setup data. -/
noncomputable def fullGradient (x : Ambient d) : Ambient d :=
  finiteAverage (fun i : ι => componentGradient S i x)

@[simp]
theorem fullGradient_def (x : Ambient d) :
    fullGradient S x =
      finiteAverage (fun i : ι => ∇ (S.component i) x) := by
  rfl

/-- Composite objective `Ψ(x)=f(x)+h(x)` from Eq. (6.5.1).

This is the paper's objective aligned with SOptLib `compositeObjective`, whose
signature is exactly the pointwise additive wrapper needed here. -/
noncomputable def psi (x : Ambient d) : ℝ :=
  SOptLib.compositeObjective (finiteSumObjective S) S.h x

@[simp]
theorem psi_def (x : Ambient d) :
    psi S x = finiteSumObjective S x + S.h x := by
  rfl

/-- Paper optimum value `Ψ*` from Eq. (6.5.1), modeled as the feasible infimum.

SOptLib `ObjectiveMinimum.value` and `optimizerValueOfMinimum` were considered;
they require an attained minimizer, while Section 6.5 later only uses finiteness
of `Ψ*`.  The local infimum definition keeps the source-facing value canonical
without adding an unstated attainment hypothesis. -/
noncomputable def psiStar : ℝ :=
  SOptLib.objectiveInfimumValue S.X S.psi

/-- Proof obligation connecting the infimum model of `Ψ*` to the paper's lower-bound use. -/
theorem psiStar_le (x : Ambient d) (hx : x ∈ S.X) :
    psiStar S ≤ psi S x := by
  classical
  refine SOptLib.objectiveInfimumValue_le (X := S.X) (f := S.psi) ?_ hx
  rcases S.psi_bounded_below with ⟨lower, hlower⟩
  refine ⟨lower, ?_⟩
  rintro y ⟨z, hz, rfl⟩
  simpa [Setup.psi] using hlower z hz

/-- The aggregate smoothness scale is positive, derived from positive component constants. -/
theorem L_pos : 0 < S.L := by
  rw [S.L_eq_average]
  exact SOptLib.finiteUniformAverage_pos S.Lcomp S.Lcomp_pos

/-- Smoothness-proportional importance probability `q_i=L_i/(mL)` from Eq. (6.5.4).

This is SOptLib's canonical smoothness-importance weight specialized to the
component constants, finite cardinality, and aggregate smoothness scale. -/
noncomputable def importanceProbability (i : ι) : ℝ :=
  SOptLib.smoothnessImportanceWeight S.Lcomp (Fintype.card ι : ℝ) S.L i

@[simp]
theorem importanceProbability_def (i : ι) :
    importanceProbability S i = S.Lcomp i / ((Fintype.card ι : ℝ) * S.L) := by
  rfl

/-- Canonical smoothness-proportional PMF `Q={q_i}` from Eq. (6.5.4).

This uses SOptLib's canonical smoothness-importance PMF, whose atom formula is
the literal paper probability `q_i=L_i/(mL)`. -/
noncomputable def importancePMF : PMF ι := by
  classical
  have hcard_pos : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have havg :
      S.L = (Fintype.card ι : ℝ)⁻¹ * ∑ i : ι, S.Lcomp i := by
    simpa [finiteAverage, SOptLib.finiteUniformAverage, smul_eq_mul] using S.L_eq_average
  have hsum_ne : (∑ i : ι, S.Lcomp i) ≠ 0 := by
    have hsum_pos : 0 < ∑ i : ι, S.Lcomp i := by
      exact Finset.sum_pos (fun i _ => S.Lcomp_pos i) Finset.univ_nonempty
    exact ne_of_gt hsum_pos
  exact
    SOptLib.smoothnessImportancePMF S.Lcomp
      (fun i => le_of_lt (S.Lcomp_pos i)) hcard_pos havg hsum_ne

/-- The canonical PMF has the Algorithm 6.6 atom mass `q_i`. -/
theorem importancePMF_apply (i : ι) :
    importancePMF S i = ENNReal.ofReal (importanceProbability S i) := by
  classical
  have hcard_pos : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have havg :
      S.L = (Fintype.card ι : ℝ)⁻¹ * ∑ i : ι, S.Lcomp i := by
    simpa [finiteAverage, SOptLib.finiteUniformAverage, smul_eq_mul] using S.L_eq_average
  have hsum_ne : (∑ i : ι, S.Lcomp i) ≠ 0 := by
    have hsum_pos : 0 < ∑ i : ι, S.Lcomp i := by
      exact Finset.sum_pos (fun i _ => S.Lcomp_pos i) Finset.univ_nonempty
    exact ne_of_gt hsum_pos
  simpa [importancePMF, importanceProbability] using
    SOptLib.smoothnessImportancePMF_apply S.Lcomp
      (fun i => le_of_lt (S.Lcomp_pos i)) hcard_pos havg hsum_ne i

/-- The Eq. (6.5.4) atom masses are positive, so Algorithm 6.6's denominators
`q_i m` are well-defined for the theorem specialization. -/
theorem importancePMF_atom_toReal_pos (i : ι) :
    0 < (importancePMF S i).toReal := by
  classical
  have hcard_pos : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have havg :
      S.L = (Fintype.card ι : ℝ)⁻¹ * ∑ i : ι, S.Lcomp i := by
    simpa [finiteAverage, SOptLib.finiteUniformAverage, smul_eq_mul] using S.L_eq_average
  have hsum_ne : (∑ i : ι, S.Lcomp i) ≠ 0 := by
    have hsum_pos : 0 < ∑ i : ι, S.Lcomp i := by
      exact Finset.sum_pos (fun i _ => S.Lcomp_pos i) Finset.univ_nonempty
    exact ne_of_gt hsum_pos
  simpa [importancePMF] using
    SOptLib.smoothnessImportancePMF_atom_toReal_pos S.Lcomp
      (fun i => le_of_lt (S.Lcomp_pos i)) hcard_pos havg hsum_ne (S.Lcomp_pos i)

/-- Bregman prox function `V(z,x)=ν(x)-[ν(z)+⟪∇ν(z),x-z⟫]` from Eq. (6.2.5).

This is SOptLib's canonical `bregmanDivergence`; pre-search also found carrier
Bregman variants, but the paper's Section 6.5 works in Euclidean space and the
ambient three-term formula is the stated object. -/
noncomputable def bregman (z x : Ambient d) : ℝ :=
  bregmanDivergence S.nu z x

@[simp]
theorem bregman_def (z x : Ambient d) :
    bregman S z x = S.nu x - S.nu z - ⟪∇ S.nu z, x - z⟫_ℝ := by
  rfl

/-- Carrier version of the paper Bregman prox function. -/
noncomputable def feasibleBregman (z x : Feasible S) : ℝ :=
  bregman S z.1 x.1

@[simp]
theorem feasibleBregman_def (z x : Feasible S) :
    feasibleBregman S z x = bregman S z.1 x.1 := by
  rfl

/-- Composite prox objective `⟪g,u⟫ + γ⁻¹V(x,u)+h(u)` from Eq. (6.2.6).

This is a specialization of SOptLib `proxObjective`.  The plain SOptLib
`paperMirrorObjective` candidate was rejected for this object because it lacks
the simple composite term `h`; `proxObjective` includes exactly the inverse
stepsize Bregman term and additive `h` required by Eq. (6.2.6). -/
noncomputable def proxObjective (x : Feasible S) (g : Ambient d) (γ : ℝ)
    (u : Feasible S) : ℝ :=
  SOptLib.proxObjective (feasibleBregman S)
    (fun y : Feasible S => S.h y.1) (fun y : Feasible S => y.1) x g γ u

@[simp]
theorem proxObjective_def (x : Feasible S) (g : Ambient d) (γ : ℝ) (u : Feasible S) :
    proxObjective S x g γ u =
      ⟪g, u.1⟫_ℝ + γ⁻¹ * bregman S x.1 u.1 + S.h u.1 := by
  rfl

/-- Canonical selected prox point `x⁺` from Eq. (6.2.6).

The selector is a `Classical.choose` of the source-stated solvability
assumption, not a setup witness field.  The defining `IsMinOn` property is
exported as `proxPoint_isMin`. -/
noncomputable def proxPoint (x : Feasible S) (g : Ambient d) (γ : ℝ) (hγ : 0 < γ) :
    Feasible S :=
  Classical.choose (S.prox_solvable x g γ hγ)

/-- The canonical selected prox point satisfies the Eq. (6.2.6) argmin property. -/
theorem proxPoint_isMin (x : Feasible S) (g : Ambient d) (γ : ℝ) (hγ : 0 < γ) :
    IsMinOn (proxObjective S x g γ) Set.univ (proxPoint S x g γ hγ) := by
  simpa [proxPoint, proxObjective] using
    Classical.choose_spec (S.prox_solvable x g γ hγ)

/-- Algorithm 6.6 mirror step `x_{k+1}` as the canonical prox point. -/
noncomputable def mirrorStep (x : Feasible S) (G : Ambient d) (γ : ℝ) (hγ : 0 < γ) :
    Feasible S :=
  proxPoint S x G γ hγ

@[simp]
theorem mirrorStep_def (x : Feasible S) (G : Ambient d) (γ : ℝ) (hγ : 0 < γ) :
    mirrorStep S x G γ hγ = proxPoint S x G γ hγ := by
  rfl

/-- Totalized prox point used only to feed SOptLib's total projected-gradient wrapper.

For positive stepsizes this is the paper prox point; outside the paper domain it
returns the current point so the total function has no mathematical meaning
leaking into source-facing theorems. -/
noncomputable def proxPointTotal (x : Feasible S) (g : Ambient d) (γ : ℝ) : Feasible S :=
  if hγ : 0 < γ then proxPoint S x g γ hγ else x

@[simp]
theorem proxPointTotal_of_pos (x : Feasible S) (g : Ambient d) (γ : ℝ) (hγ : 0 < γ) :
    proxPointTotal S x g γ = proxPoint S x g γ hγ := by
  simp [proxPointTotal, hγ]

/-- Generalized projected-gradient mapping `P_X(x,g,γ)=γ⁻¹(x-x⁺)` from Eq. (6.2.7).

This specializes SOptLib `projectedGradient` to the canonical composite prox
point above; no projected-gradient value is stored in setup. -/
noncomputable def projectedGradient (x : Feasible S) (g : Ambient d) (γ : ℝ)
    (_hγ : 0 < γ) : Ambient d :=
  SOptLib.projectedGradient (fun y : Feasible S => y.1)
    (fun y q step => proxPointTotal S y q step) x g γ

@[simp]
theorem projectedGradient_def (x : Feasible S) (g : Ambient d) (γ : ℝ) (hγ : 0 < γ) :
    projectedGradient S x g γ hγ =
      γ⁻¹ • (x.1 - (proxPoint S x g γ hγ).1) := by
  simp [projectedGradient, SOptLib.projectedGradient, proxPointTotal, hγ]

/-- Exact generalized projected gradient `g_{X,k}=P_X(x_k,∇f(x_k),γ)`. -/
noncomputable def exactProjectedGradient (x : Feasible S) (γ : ℝ)
    (hγ : 0 < γ) : Ambient d :=
  projectedGradient S x (fullGradient S x.1) γ hγ

/-- Stochastic generalized projected gradient `\tilde g_{X,k}=P_X(x_k,G_k,γ)`. -/
noncomputable def stochasticProjectedGradient (x : Feasible S) (G : Ambient d) (γ : ℝ)
    (hγ : 0 < γ) : Ambient d :=
  projectedGradient S x G γ hγ

/-- Estimator error `δ_k=G_k-∇f(x_k)` from Section 6.5.1.

This reuses SOptLib `oracleEstimatorError`; the target field is the canonical
full finite-sum gradient, so sampled errors are derived objects. -/
noncomputable def estimatorError (x : Feasible S) (G : Ambient d) : Ambient d :=
  SOptLib.oracleEstimatorError (fun y : Feasible S => fullGradient S y.1) G x

@[simp]
theorem estimatorError_def (x : Feasible S) (G : Ambient d) :
    estimatorError S x G = G - fullGradient S x.1 := by
  rfl

/-- One-based epoch-start predicate for the grouping
`{1,...,T},{T+1,...,2T},...` in Section 6.5.1. -/
def isEpochStart (T k : ℕ) : Prop :=
  (k - 1) % T = 0

/-- Mini-batch samples for Algorithm 6.6, restricted to the support of the input law `Q`.

The source says samples are drawn according to `Q` and then divides by `q_i m`;
the support subtype records the denominator boundary for actually sampled atoms
without changing the Algorithm 6.6 input `Q` into a full-support distribution. -/
abbrev MiniBatch (Q : PMF ι) (b : ℕ) : Type _ :=
  Fin b → DistributionSupport Q

/-- Inverse-probability weighted mini-batch gradient difference from Algorithm 6.6.

The atom is the literal inverse-probability weighted gradient difference, and
the outer average is the canonical finite average over the sampled mini-batch.
The probability distribution `Q` is Algorithm 6.6 input; Eq. (6.5.4) is only a
later specialization. -/
noncomputable def miniBatchGradientDifference (Q : PMF ι) (b : ℕ)
    (sample : MiniBatch (ι := ι) Q b) (x xPrev : Feasible S) : Ambient d :=
  finiteAverage
    (fun r : Fin b =>
      importanceWeightedGradientDifference
        Q (componentGradient S)
        x.1 xPrev.1 (sample r))

@[simp]
theorem miniBatchGradientDifference_def (Q : PMF ι) (b : ℕ) (sample : MiniBatch (ι := ι) Q b)
    (x xPrev : Feasible S) :
    miniBatchGradientDifference S Q b sample x xPrev =
      finiteAverage
        (fun r : Fin b =>
          importanceWeightedGradientDifference
            Q (componentGradient S)
            x.1 xPrev.1 (sample r)) := by
  rfl

/-- Recursive variance-reduced estimator branch of Algorithm 6.6. -/
noncomputable def recursiveEstimator (Q : PMF ι) (b : ℕ)
    (sample : MiniBatch (ι := ι) Q b) (x xPrev : Feasible S) (GPrev : Ambient d) : Ambient d :=
  SOptLib.miniBatchRecursiveControlVariateEstimator
    (fun i : ι => probabilityMass Q i) (Fintype.card ι : ℝ) (componentGradient S)
    (fun r : Fin b => (sample r).1) x.1 xPrev.1 GPrev

@[simp]
theorem recursiveEstimator_def (Q : PMF ι) (b : ℕ) (sample : MiniBatch (ι := ι) Q b)
    (x xPrev : Feasible S) (GPrev : Ambient d) :
    recursiveEstimator S Q b sample x xPrev GPrev =
      miniBatchGradientDifference S Q b sample x xPrev + GPrev := by
  simp [recursiveEstimator, miniBatchGradientDifference, importanceWeightedGradientDifference,
    finiteAverage]

end Setup

/-- Algorithm 6.6 run parameters and sampled component-index stream.

The run stores source inputs (`x₁`, `γ`, `T`, `{θ_t}`, `b`, `Q`) and the mini-batch
sample path.  It does not store iterates or estimator values; those are
generated by `stateSeq`. -/
structure Run (S : Setup (d := d) (ι := ι)) where
  /-- Initial feasible point `x₁`. -/
  x₁ : Feasible S
  /-- Iteration horizon `N` in Algorithm 6.6. -/
  horizon : ℕ
  /-- The randomized output support `{1,...,N}` is nonempty. -/
  horizon_pos : 0 < horizon
  /-- Stepsize `γ`. -/
  gamma : ℝ
  /-- Positive-stepsize condition used in Eq. (6.2.6). -/
  gamma_pos : 0 < gamma
  /-- Epoch length `T`. -/
  T : ℕ
  /-- Source indexing uses nonempty epochs. -/
  T_pos : 0 < T
  /-- Algorithm 6.6 input sequence `{θ_t}`.  It is recorded as source input even
  though the printed update lines in Algorithm 6.6 do not subsequently use it. -/
  theta : PositiveIteration → ℝ
  /-- Mini-batch size `b`. -/
  batchSize : ℕ
  /-- Algorithm 6.6 samples mini-batches of positive size. -/
  batchSize_pos : 0 < batchSize
  /-- Algorithm 6.6 input probability distribution `Q={q₁,...,q_m}`. -/
  Q : PMF ι
  /-- Mini-batch component-index samples for each one-based estimator refresh. -/
  sample : ℕ → Setup.MiniBatch (ι := ι) Q batchSize

namespace Run

variable {S : Setup (d := d) (ι := ι)}
variable (R : Run S)

/-- Algorithm state carrying the current feasible iterate and current estimator. -/
structure State where
  x : Feasible S
  G : Ambient d

/-- Initial Algorithm 6.6 state: `G₁=∇f(x₁)` at the first epoch start. -/
noncomputable def initialState (R : Run S) : State (S := S) :=
  { x := R.x₁
    G := Setup.fullGradient S R.x₁.1 }

/-- One transition of Algorithm 6.6 from state `(x_k,G_k)` to `(x_{k+1},G_{k+1})`.

The next iterate is the canonical mirror step.  The next estimator is either the
full gradient at an epoch start or the recursive mini-batch control-variate
estimator from Algorithm 6.6. -/
noncomputable def nextState (R : Run S) (n : ℕ) (st : State (S := S)) : State (S := S) := by
  classical
  let xNext : Feasible S := Setup.mirrorStep S st.x st.G R.gamma R.gamma_pos
  let GNext : Ambient d :=
    if Setup.isEpochStart R.T (n + 2) then
      Setup.fullGradient S xNext.1
    else
      Setup.recursiveEstimator S R.Q R.batchSize (R.sample (n + 2)) xNext st.x st.G
  exact { x := xNext, G := GNext }

/-- Generated Algorithm 6.6 state sequence.  `stateSeq 0` represents `(x₁,G₁)`. -/
noncomputable def stateSeq (R : Run S) : ℕ → State (S := S)
  | 0 => initialState R
  | n + 1 => nextState R n (stateSeq R n)

/-- One-based iterate accessor `x_k`, generated from the state recursion. -/
noncomputable def iterate (k : ℕ) : Feasible S :=
  (stateSeq R (k - 1)).x

/-- One-based estimator accessor `G_k`, generated from the state recursion. -/
noncomputable def estimator (k : ℕ) : Ambient d :=
  (stateSeq R (k - 1)).G

@[simp]
theorem iterate_one :
    iterate R 1 = R.x₁ := by
  rfl

@[simp]
theorem estimator_one :
    estimator R 1 = Setup.fullGradient S R.x₁.1 := by
  rfl

/-- The generated next iterate satisfies the Algorithm 6.6 mirror update. -/
theorem next_iterate_eq_mirrorStep (n : ℕ) :
    (stateSeq R (n + 1)).x =
      Setup.mirrorStep S (stateSeq R n).x (stateSeq R n).G R.gamma R.gamma_pos := by
  rfl

/-- At an epoch start, the generated estimator is the full gradient branch of Algorithm 6.6. -/
theorem next_estimator_eq_fullGradient_of_epochStart
    (n : ℕ) (hstart : Setup.isEpochStart R.T (n + 2)) :
    (stateSeq R (n + 1)).G =
      Setup.fullGradient S (Setup.mirrorStep S (stateSeq R n).x (stateSeq R n).G
        R.gamma R.gamma_pos).1 := by
  classical
  change
    (if Setup.isEpochStart R.T (n + 2) then
        Setup.fullGradient S (Setup.mirrorStep S (stateSeq R n).x (stateSeq R n).G
          R.gamma R.gamma_pos).1
      else
        Setup.recursiveEstimator S R.Q R.batchSize (R.sample (n + 2))
          (Setup.mirrorStep S (stateSeq R n).x (stateSeq R n).G R.gamma R.gamma_pos)
          (stateSeq R n).x (stateSeq R n).G) =
      Setup.fullGradient S (Setup.mirrorStep S (stateSeq R n).x (stateSeq R n).G
        R.gamma R.gamma_pos).1
  simp [hstart]

/-- Away from an epoch start, the generated estimator is the recursive mini-batch branch
of Algorithm 6.6. -/
theorem next_estimator_eq_recursive_of_not_epochStart
    (n : ℕ) (hstart : ¬ Setup.isEpochStart R.T (n + 2)) :
    (stateSeq R (n + 1)).G =
      Setup.recursiveEstimator S R.Q R.batchSize (R.sample (n + 2))
        (Setup.mirrorStep S (stateSeq R n).x (stateSeq R n).G R.gamma R.gamma_pos)
        (stateSeq R n).x (stateSeq R n).G := by
  classical
  change
    (if Setup.isEpochStart R.T (n + 2) then
        Setup.fullGradient S (Setup.mirrorStep S (stateSeq R n).x (stateSeq R n).G
          R.gamma R.gamma_pos).1
      else
        Setup.recursiveEstimator S R.Q R.batchSize (R.sample (n + 2))
          (Setup.mirrorStep S (stateSeq R n).x (stateSeq R n).G R.gamma R.gamma_pos)
          (stateSeq R n).x (stateSeq R n).G) =
      Setup.recursiveEstimator S R.Q R.batchSize (R.sample (n + 2))
        (Setup.mirrorStep S (stateSeq R n).x (stateSeq R n).G R.gamma R.gamma_pos)
        (stateSeq R n).x (stateSeq R n).G
  simp [hstart]

/-- One-based generated iterate update at positive iteration indices. -/
theorem iterate_succ_eq_proxPoint (k : PositiveIteration) :
    iterate R (k.1 + 1) =
      Setup.proxPoint S (iterate R k.1) (estimator R k.1) R.gamma R.gamma_pos := by
  have hnext := next_iterate_eq_mirrorStep R (k.1 - 1)
  have hk_prev : k.1 - 1 + 1 = k.1 := Nat.sub_add_cancel k.2
  have hk_succ : k.1 + 1 - 1 = k.1 := Nat.succ_sub_one k.1
  simpa [iterate, estimator, Setup.mirrorStep_def, hk_prev, hk_succ] using hnext

/-- Exact projected-gradient certificate at generated iterate `x_k`. -/
noncomputable def exactGradientMapping (k : ℕ) : Ambient d :=
  Setup.exactProjectedGradient S (iterate R k) R.gamma R.gamma_pos

/-- Stochastic projected-gradient certificate at generated iterate `x_k` and estimator `G_k`. -/
noncomputable def stochasticGradientMapping (k : ℕ) : Ambient d :=
  Setup.stochasticProjectedGradient S (iterate R k) (estimator R k) R.gamma R.gamma_pos

/-- Generated estimator error `δ_k=G_k-∇f(x_k)`. -/
noncomputable def estimatorError (k : ℕ) : Ambient d :=
  Setup.estimatorError S (iterate R k) (estimator R k)

@[simp]
theorem estimatorError_def (k : ℕ) :
    estimatorError R k = estimator R k - Setup.fullGradient S (iterate R k).1 := by
  rfl

/-- Algorithm 6.6 output `x_R` for a selected one-based index `R ∈ {1,...,N}`. -/
noncomputable def output (idx : OutputIndex R.horizon) : Feasible S :=
  iterate R idx.1

/-- Uniform output law over `{1,...,N}` for this run. -/
noncomputable def outputPMF : PMF (OutputIndex R.horizon) :=
  uniformOutputPMF R.horizon R.horizon_pos

/-- The run output law has uniform finite-window masses. -/
theorem outputPMF_spec :
    SOptLib.FiniteWindowPMFSpec (outputWindow R.horizon) (fun _ : ℕ => (1 : ℝ))
      (outputPMF R) := by
  exact uniformOutputPMF_spec R.horizon R.horizon_pos

/-- Paper-facing theorem obligation for the finite-average gradient calculus bridge.

The source writes `∇f` for the gradient of `f=m⁻¹∑ᵢf_i`; this theorem is the
bridge from the canonical finite-average gradient object to Mathlib's gradient
of `finiteSumObjective`. -/
theorem fullGradient_hasGradientAt
    (x : Ambient d) (hx : x ∈ S.X) :
    HasGradientAt (Setup.finiteSumObjective S) (Setup.fullGradient S x) x := by
  simpa [Setup.finiteSumObjective, Setup.fullGradient, Setup.componentGradient] using
    SOptLib.finiteAverageObjective_hasGradientAt S.component
      (fun i y => Setup.componentGradient S i y) x
      (fun i => S.component_hasGradientAt i x hx)

/-- Composite prox optimality gives the scaled variational inequality used in
Lan Lemma 6.5.

Aligns with Lan Eq. (6.2.12)--(6.2.15): SOptLib candidates
`prox_scaled_variational_inequality_of_argmin`,
`prox_majorant_hasDerivWithinAt_zero`, and
`bregman_segment_difference_hasDerivWithinAt_zero` provide the calculus
pieces, while the local `Setup.proxPoint_isMin` and `S.convex_h` supply the
paper's composite prox minimizer and simple-term convexity. -/
private theorem prox_scaled_variational_inequality
    (x u : Feasible S) (g : Ambient d) (γ : ℝ) (hγ : 0 < γ) :
    let xp := Setup.proxPoint S x g γ hγ
    let dvec : Ambient d := u.1 - xp.1
    0 ≤
      γ * ⟪g, dvec⟫_ℝ +
        ⟪∇ S.nu xp.1 - ∇ S.nu x.1, dvec⟫_ℝ +
        γ * (S.h u.1 - S.h xp.1) := by
  classical
  let xp := Setup.proxPoint S x g γ hγ
  let dvec : Ambient d := u.1 - xp.1
  have hmin :
      IsMinOn
        (SOptLib.proxObjective
          (fun a b : Feasible S =>
            carrierBregmanFormula S.nu id (fun y : Ambient d => ∇ S.nu y) a.1 b.1)
          (fun y : Feasible S => S.h y.1)
          (fun y : Feasible S => y.1)
          x g γ)
        Set.univ xp := by
    simpa [xp, Setup.proxObjective, Setup.feasibleBregman, Setup.bregman,
      bregmanDivergence, carrierBregmanFormula, id] using
      Setup.proxPoint_isMin S x g γ hγ
  have hscaled :=
    composite_prox_scaled_variational_inequality_of_isMinOn
      (nu := S.nu) (h := S.h) (grad := fun y : Ambient d => ∇ S.nu y)
      S.convex_h x xp u g γ hγ (S.nu_hasGradientAt xp.1 xp.2) hmin
  simpa [xp, dvec] using hscaled

/-- Unscaled composite prox variational inequality used by Lan Lemma 6.5.

Aligns with Lan Eq. (6.2.12)--(6.2.15); it specializes SOptLib
`composite_prox_variational_inequality_of_isMinOn` after the local selected
prox point supplies the composite prox argmin certificate. -/
private theorem prox_variational_inequality
    (x u : Feasible S) (g : Ambient d) (γ : ℝ) (hγ : 0 < γ) :
    0 ≤
      ⟪g, u.1 - (Setup.proxPoint S x g γ hγ).1⟫_ℝ +
        γ⁻¹ * ⟪∇ S.nu (Setup.proxPoint S x g γ hγ).1 - ∇ S.nu x.1,
          u.1 - (Setup.proxPoint S x g γ hγ).1⟫_ℝ +
        (S.h u.1 - S.h (Setup.proxPoint S x g γ hγ).1) := by
  exact
    composite_prox_variational_inequality_of_isMinOn
      (nu := S.nu) (h := S.h) (grad := fun y : Ambient d => ∇ S.nu y)
      S.convex_h x (Setup.proxPoint S x g γ hγ) u g γ hγ
      (S.nu_hasGradientAt (Setup.proxPoint S x g γ hγ).1
        (Setup.proxPoint S x g γ hγ).2)
      (by
        simpa [Setup.proxObjective, Setup.feasibleBregman, Setup.bregman,
          bregmanDivergence, carrierBregmanFormula, id] using
          Setup.proxPoint_isMin S x g γ hγ)

/-- Prox descent inner-product bound used in Eq. (6.5.10).

This is Lemma 6.4's descent direction in the concrete composite prox model:
the existing variational inequality at `u = x`, together with Eq. (6.2.4)
strong monotonicity of the DGF, gives the lower bound on
`⟪g, x - x⁺⟫`. -/
private theorem proxPoint_descent_inner_bound
    (x : Feasible S) (g : Ambient d) (γ : ℝ) (hγ : 0 < γ) :
    γ⁻¹ * ‖x.1 - (Setup.proxPoint S x g γ hγ).1‖ ^ 2 +
        S.h (Setup.proxPoint S x g γ hγ).1 - S.h x.1 ≤
      ⟪g, x.1 - (Setup.proxPoint S x g γ hγ).1⟫_ℝ := by
  classical
  let xp := Setup.proxPoint S x g γ hγ
  have hvi :
      0 ≤
        ⟪g, x.1 - xp.1⟫_ℝ +
          γ⁻¹ * ⟪∇ S.nu xp.1 - ∇ S.nu x.1, x.1 - xp.1⟫_ℝ +
          (S.h x.1 - S.h xp.1) := by
    simpa [xp] using prox_variational_inequality (S := S) x x g γ hγ
  have hstrong :
      ‖xp.1 - x.1‖ ^ 2 ≤
        ⟪xp.1 - x.1, ∇ S.nu xp.1 - ∇ S.nu x.1⟫_ℝ :=
    S.dgf_strong xp.1 xp.2 x.1 x.2
  simpa [xp] using
    (prox_descent_inner_bound_of_variational
      (eval := fun y : Feasible S => y.1)
      (grad := fun y : Feasible S => ∇ S.nu y.1)
      (h := fun y : Feasible S => S.h y.1)
      (prox := xp) (x := x) (g := g) (gamma := γ) hγ hvi hstrong)

/-- Same-base prox points satisfy Lan Lemma 6.5 / Eq. (6.2.11).

Aligns with Lan Lemma 6.5: the SOptLib candidate
`prox_points_scaled_dist_le_oracle_dist_of_variational` exactly packages the
summation, cancellation, strong-monotonicity, and Cauchy-Schwarz algebra once
the local composite prox variational inequalities are supplied. -/
private theorem proxPoint_scaled_distance_le_oracle_distance
    (x : Feasible S) (g₁ g₂ : Ambient d) (γ : ℝ) (hγ : 0 < γ) :
    γ⁻¹ *
        ‖(Setup.proxPoint S x g₁ γ hγ).1 - (Setup.proxPoint S x g₂ γ hγ).1‖ ≤
      ‖g₁ - g₂‖ := by
  classical
  let p₁ := Setup.proxPoint S x g₁ γ hγ
  let p₂ := Setup.proxPoint S x g₂ γ hγ
  have hvi₁ :
      0 ≤
        ⟪g₁, p₂.1 - p₁.1⟫_ℝ +
          γ⁻¹ * ⟪∇ S.nu p₁.1 - ∇ S.nu x.1, p₂.1 - p₁.1⟫_ℝ +
          (S.h p₂.1 - S.h p₁.1) := by
    simpa [p₁, p₂] using
      (prox_variational_inequality (S := S) x p₂ g₁ γ hγ)
  have hvi₂ :
      0 ≤
        ⟪g₂, p₁.1 - p₂.1⟫_ℝ +
          γ⁻¹ * ⟪∇ S.nu p₂.1 - ∇ S.nu x.1, p₁.1 - p₂.1⟫_ℝ +
          (S.h p₁.1 - S.h p₂.1) := by
    simpa [p₁, p₂] using
      (prox_variational_inequality (S := S) x p₁ g₂ γ hγ)
  have hstrong :
      ‖p₁.1 - p₂.1‖ ^ 2 ≤
        ⟪p₁.1 - p₂.1, ∇ S.nu p₁.1 - ∇ S.nu p₂.1⟫_ℝ :=
    S.dgf_strong p₁.1 p₁.2 p₂.1 p₂.2
  simpa [p₁, p₂] using
    (prox_points_scaled_dist_le_oracle_dist_of_variational
      (fun y : Feasible S => y.1)
      (fun y : Feasible S => ∇ S.nu y.1)
      (fun y : Feasible S => S.h y.1)
      x p₁ p₂ g₁ g₂ γ hγ hvi₁ hvi₂ hstrong)

/-- Proposition 6.1 / Eq. (6.2.16) at this file's projected-gradient interface.

Aligns with Lan Proposition 6.1: SOptLib
`projectedGradient_lipschitz_oracle_of_prox_scaled_dist` supplies the pure
projected-gradient algebra, consumed with the local Lemma 6.5 prox-distance
bridge above. -/
private theorem projectedGradient_lipschitz_oracle
    (x : Feasible S) (g₁ g₂ : Ambient d) (γ : ℝ) (hγ : 0 < γ) :
    ‖Setup.projectedGradient S x g₁ γ hγ -
        Setup.projectedGradient S x g₂ γ hγ‖ ≤ ‖g₁ - g₂‖ := by
  have hprox :
      γ⁻¹ *
          ‖(fun y : Feasible S => y.1) (Setup.proxPointTotal S x g₁ γ) -
            (fun y : Feasible S => y.1) (Setup.proxPointTotal S x g₂ γ)‖ ≤
        ‖g₁ - g₂‖ := by
    simpa [Setup.proxPointTotal_of_pos S x g₁ γ hγ,
      Setup.proxPointTotal_of_pos S x g₂ γ hγ] using
      (proxPoint_scaled_distance_le_oracle_distance (S := S) x g₁ g₂ γ hγ)
  have h :=
    projectedGradient_lipschitz_oracle_of_prox_scaled_dist
      (fun y : Feasible S => y.1)
      (fun y q step => Setup.proxPointTotal S y q step)
      x g₁ g₂ γ hγ hprox
  simpa [Setup.projectedGradient, SOptLib.projectedGradient] using h

/-- Paper-facing theorem obligation for Eq. (6.5.3), derived from prox-map
Lipschitz continuity and the definition of `δ_k`.

The source introduces this notation only for one-based iteration indices
`k=1,2,...`, so the theorem is indexed by `PositiveIteration` rather than a
totalized natural-number case. -/
theorem gradient_mapping_perturbation (k : PositiveIteration) :
    ‖exactGradientMapping R k.1 - stochasticGradientMapping R k.1‖ ≤
      ‖estimatorError R k.1‖ := by
  simpa [Run.exactGradientMapping, Run.stochasticGradientMapping,
    Run.estimatorError, Setup.exactProjectedGradient, Setup.stochasticProjectedGradient,
    Setup.estimatorError, Setup.projectedGradient, norm_sub_rev] using
    (exact_projectedGradient_dist_le_oracle_projectedGradient_dist_add_residual
      (fun y : Feasible S => y.1)
      (fun y q step => Setup.proxPointTotal S y q step)
      (fun y : Feasible S => Setup.fullGradient S y.1)
      (Run.iterate R k.1) (Run.estimator R k.1) R.gamma R.gamma_pos
      (by
        simpa [Setup.proxPointTotal, R.gamma_pos] using
          (proxPoint_scaled_distance_le_oracle_distance (S := S)
            (Run.iterate R k.1)
            (Setup.fullGradient S (Run.iterate R k.1).1)
            (Run.estimator R k.1) R.gamma R.gamma_pos)))

/-- Squared form of the source perturbation split after Eq. (6.5.10).

This is the exact-gradient certificate estimate
`‖g_X,k‖² ≤ 2‖δ_k‖² + 2‖g̃_X,k‖²`, derived from Eq. (6.5.3) rather than
stored as a stochastic-run assumption. -/
private theorem exact_gradient_mapping_sq_le_stochastic_sq_add_error_sq
    (k : PositiveIteration) :
    ‖exactGradientMapping R k.1‖ ^ 2 ≤
      2 * ‖stochasticGradientMapping R k.1‖ ^ 2 +
        2 * ‖estimatorError R k.1‖ ^ 2 := by
  let exact : Ambient d := exactGradientMapping R k.1
  let stoch : Ambient d := stochasticGradientMapping R k.1
  let delta : Ambient d := estimatorError R k.1
  have hperturb : ‖exact - stoch‖ ≤ ‖delta‖ := by
    simpa [exact, stoch, delta] using gradient_mapping_perturbation R k
  have hdiff_sq : ‖exact - stoch‖ ^ 2 ≤ ‖delta‖ ^ 2 := by
    have hleft_nonneg : 0 ≤ ‖exact - stoch‖ := norm_nonneg _
    have hright_nonneg : 0 ≤ ‖delta‖ := norm_nonneg _
    nlinarith [hperturb, hleft_nonneg, hright_nonneg,
      sq_nonneg (‖delta‖ - ‖exact - stoch‖)]
  have hdecomp : exact = (exact - stoch) + stoch := by
    abel
  have hsplit :
      ‖exact‖ ^ 2 ≤ 2 * ‖exact - stoch‖ ^ 2 + 2 * ‖stoch‖ ^ 2 := by
    calc
      ‖exact‖ ^ 2 = ‖(exact - stoch) + stoch‖ ^ 2 :=
        congrArg (fun z : Ambient d => ‖z‖ ^ 2) hdecomp
      _ ≤ 2 * ‖exact - stoch‖ ^ 2 + 2 * ‖stoch‖ ^ 2 :=
        SOptLib.norm_add_sq_le_two_mul_norm_sq_add_two_mul_norm_sq
          (exact - stoch) stoch
  nlinarith

/-- Component-gradient evaluation count for an `N`-step Algorithm 6.6 run,
matching the Corollary 6.20 count `(m+bT)⌈N/T⌉`. -/
noncomputable def componentGradientEvaluationCount : ℕ :=
  SOptLib.singlePhaseEpochCallCount (Fintype.card ι) R.batchSize R.T R.horizon

/-- Corollary 6.20 real-valued complexity envelope with `T` in place of `√m`.

The source corollary specializes this with `T=√m`; the separate theorem below
records that source-facing specialization. -/
noncomputable def corollary620Rate (epsilon : ℝ) : ℝ :=
  (Fintype.card ι : ℝ) +
    (R.T : ℝ) * S.L * (Setup.psi S R.x₁.1 - Setup.psiStar S) / epsilon

end Run

/-- Stochastic Algorithm 6.6 run over an ambient sample space.

The fields are the source stochastic inputs: a sample law, i.i.d. mini-batches
according to the input probability distribution `Q`, and the deterministic
parameters used to generate each sample-path run.  The smoothness-proportional
Eq. (6.5.4) law is imposed only in theorem heads that cite that specialization.
Iterates, estimators, and outputs remain definitions from the generated run. -/
structure StochasticRun (S : Setup (d := d) (ι := ι))
    (Ω : Type*) [MeasurableSpace Ω] [MeasurableSpace ι] [MeasurableSingletonClass ι] where
  /-- Ambient probability/sample law for the Algorithm 6.6 randomness. -/
  P : Measure Ω
  /-- The sample law is a probability measure, matching the paper expectation space. -/
  P_isProbability : IsProbabilityMeasure P
  /-- Initial feasible point `x₁`. -/
  x₁ : Feasible S
  /-- Iteration horizon `N`. -/
  horizon : ℕ
  /-- The output support `{1,...,N}` is nonempty. -/
  horizon_pos : 0 < horizon
  /-- Stepsize `γ`. -/
  gamma : ℝ
  /-- Positive-stepsize condition used in Eq. (6.2.6). -/
  gamma_pos : 0 < gamma
  /-- Epoch length `T`. -/
  T : ℕ
  /-- Source indexing uses nonempty epochs. -/
  T_pos : 0 < T
  /-- Algorithm 6.6 input sequence `{θ_t}`. -/
  theta : PositiveIteration → ℝ
  /-- Mini-batch size `b`. -/
  batchSize : ℕ
  /-- Algorithm 6.6 samples mini-batches of positive size. -/
  batchSize_pos : 0 < batchSize
  /-- Algorithm 6.6 input probability distribution `Q={q₁,...,q_m}`. -/
  Q : PMF ι
  /-- Random mini-batch component-index samples. -/
  sample : Ω → ℕ → Setup.MiniBatch (ι := ι) Q batchSize
  /-- Algorithm 6.6 says to generate mini-batch samples according to `Q`; in Lean
  this records that each mini-batch is a measurable random variable. -/
  sample_batch_measurable :
    ∀ k : ℕ, Measurable (fun ω : Ω => sample ω k)
  /-- Every mini-batch coordinate has the input law `Q` after forgetting support evidence. -/
  sample_law :
    ∀ k : ℕ, ∀ r : Fin batchSize,
      Measure.map (fun ω : Ω => (sample ω k r).1) P = Q.toMeasure
  /-- Source statement that Algorithm 6.6 generates independent samples. -/
  sample_iIndep :
    ProbabilityTheory.iIndepFun
      (fun kr : ℕ × Fin batchSize => fun ω : Ω => (sample ω kr.1 kr.2).1) P

namespace StochasticRun

variable {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace ι] [MeasurableSingletonClass ι]
variable {S : Setup (d := d) (ι := ι)}
variable (SR : StochasticRun S Ω)

/-- The deterministic Algorithm 6.6 run realized by a sample point `ω`. -/
noncomputable def pathRun (ω : Ω) : Run S :=
  { x₁ := SR.x₁
    horizon := SR.horizon
    horizon_pos := SR.horizon_pos
    gamma := SR.gamma
    gamma_pos := SR.gamma_pos
    T := SR.T
    T_pos := SR.T_pos
    theta := SR.theta
    batchSize := SR.batchSize
    batchSize_pos := SR.batchSize_pos
    Q := SR.Q
    sample := SR.sample ω }

/-- Pair form of the generated state, used as a measurable finite-range key for
expectation well-definedness. -/
noncomputable def statePair (ω : Ω) (n : ℕ) : Feasible S × Ambient d :=
  ((Run.stateSeq (pathRun SR ω) n).x, (Run.stateSeq (pathRun SR ω) n).G)

/-- The generated state up to a finite horizon is a measurable finite-range
function of the finitely many sampled mini-batches used so far. -/
theorem statePair_measurable_finite_range (N n : ℕ) (hn : n ≤ N) :
    Measurable (fun ω : Ω => statePair SR ω n) ∧
      (Set.range (fun ω : Ω => statePair SR ω n)).Finite := by
  classical
  let process : ℕ → Ω → Feasible S × Ambient d :=
    fun m ω => statePair SR ω m
  let driver : ℕ → Ω → Setup.MiniBatch (ι := ι) SR.Q SR.batchSize :=
    fun j ω => SR.sample ω (j + 2)
  let step : ℕ → Feasible S × Ambient d →
      Setup.MiniBatch (ι := ι) SR.Q SR.batchSize → Feasible S × Ambient d :=
    fun j st sample =>
      let xNext : Feasible S := Setup.mirrorStep S st.1 st.2 SR.gamma SR.gamma_pos
      let GNext : Ambient d :=
        if Setup.isEpochStart SR.T (j + 2) then
          Setup.fullGradient S xNext.1
        else
          Setup.recursiveEstimator S SR.Q SR.batchSize sample xNext st.1 st.2
      (xNext, GNext)
  have h_init_meas : Measurable (process 0) := by
    simp [process, statePair, pathRun, Run.stateSeq, Run.initialState]
  have h_init_finite : (Set.range (process 0)).Finite := by
    refine (Set.finite_singleton
      (SR.x₁, Setup.fullGradient S SR.x₁.1)).subset ?_
    rintro z ⟨ω, rfl⟩
    simp [process, statePair, pathRun, Run.stateSeq, Run.initialState]
  have h_driver_meas :
      ∀ j : ℕ, j + 1 ≤ N → Measurable (driver j) := by
    intro j hj
    simpa [driver] using SR.sample_batch_measurable (j + 2)
  have h_driver_finite :
      ∀ j : ℕ, j + 1 ≤ N → (Set.range (driver j)).Finite := by
    intro j hj
    haveI : Finite (Setup.MiniBatch (ι := ι) SR.Q SR.batchSize) := inferInstance
    exact Set.toFinite (Set.range (driver j))
  have h_update :
      ∀ j : ℕ, j + 1 ≤ N →
        ∀ ω : Ω, process (j + 1) ω = step j (process j ω) (driver j ω) := by
    intro j hj ω
    simp [process, driver, step, statePair, pathRun, Run.stateSeq, Run.nextState]
  exact
    SOptLib.recursive_process_measurable_finite_range_wrt_history
      (mHist := inferInstance)
      (process := process)
      (driver := driver)
      (step := step)
      (N := N)
      (n := n)
      h_init_meas
      h_init_finite
      h_driver_meas
      h_driver_finite
      h_update
      hn

/-- The generated iterate at a fixed time is measurable and finite-range. -/
theorem iterate_measurable_finite_range (k : ℕ) :
    Measurable (fun ω : Ω => Run.iterate (pathRun SR ω) k) ∧
      (Set.range (fun ω : Ω => Run.iterate (pathRun SR ω) k)).Finite := by
  classical
  rcases statePair_measurable_finite_range SR (k - 1) (k - 1) le_rfl with
    ⟨hmeas, hfin⟩
  constructor
  · simpa [statePair, Run.iterate] using hmeas.fst
  · have hsubset :
        Set.range (fun ω : Ω => Run.iterate (pathRun SR ω) k) ⊆
          Prod.fst '' Set.range (fun ω : Ω => statePair SR ω (k - 1)) := by
      rintro x ⟨ω, rfl⟩
      exact ⟨statePair SR ω (k - 1), ⟨ω, rfl⟩, by simp [statePair, Run.iterate]⟩
    exact (hfin.image Prod.fst).subset hsubset

/-- Expected objective value `E[Ψ(x_k)]` for the generated stochastic process. -/
noncomputable def expectedPsi (k : ℕ) : ℝ :=
  SOptLib.expectation SR.P
    (fun ω : Ω => Setup.psi S (Run.iterate (pathRun SR ω) k).1)

/-- Expected squared exact projected-gradient mapping at iteration `k`. -/
noncomputable def expectedExactGradientMappingSq (k : ℕ) : ℝ :=
  SOptLib.expectation SR.P
    (fun ω : Ω => ‖Run.exactGradientMapping (pathRun SR ω) k‖ ^ 2)

/-- Expected squared stochastic projected-gradient mapping at iteration `k`.

No SOptLib match: searched `expected estimator error squared stochastic projected
gradient mapping displacement variance expectation`; SOptLib provides the
underlying `stochasticProjectedGradientMapping` and expectation primitives, but
not this Algorithm 6.6 generated-process expectation from Theorem 6.14. -/
noncomputable def expectedStochasticGradientMappingSq (k : ℕ) : ℝ :=
  SOptLib.expectation SR.P
    (fun ω : Ω => ‖Run.stochasticGradientMapping (pathRun SR ω) k‖ ^ 2)

/-- Expected squared estimator error `E[‖δ_k‖²]` from Lemma 6.10 and Theorem 6.14.

No SOptLib match: searched `expected estimator error squared stochastic projected
gradient mapping displacement variance expectation`; SOptLib provides
`oracleEstimatorError` and expectation primitives, while this definition ties
them to Algorithm 6.6's generated stochastic run. -/
noncomputable def expectedEstimatorErrorSq (k : ℕ) : ℝ :=
  SOptLib.expectation SR.P
    (fun ω : Ω => ‖Run.estimatorError (pathRun SR ω) k‖ ^ 2)

/-- Expected squared displacement `E[‖x_k-x_{k-1}‖²]` used in Lemma 6.10.

No SOptLib match: searched `expected estimator error squared stochastic projected
gradient mapping displacement variance expectation`; generic epoch-sum
telescopes exist in SOptLib, but the paper's displacement term is specific to
the generated Algorithm 6.6 iterates. -/
noncomputable def expectedDisplacementSq (k : ℕ) : ℝ :=
  SOptLib.expectation SR.P
    (fun ω : Ω =>
      ‖(Run.iterate (pathRun SR ω) k).1 -
          (Run.iterate (pathRun SR ω) (k - 1)).1‖ ^ 2)

/-- One-based epoch coordinate `(s,t) ↦ sT+t` used in Lemma 6.10 and Theorem 6.14.

No SOptLib match: searched `finite window telescope epoch descent one step
expected descent recurrence sum Icc`; SOptLib has generic finite-window and
epoch recurrences, but the paper's `(s,t)` notation is a local one-based
coordinate for Algorithm 6.6. -/
def epochIndex (s t : ℕ) : ℕ :=
  s * SR.T + t

/-- Erased mini-batch sample-coordinate stream used for strict-past freshness.

Algorithm 6.6 samples support-valued indices so the estimator denominator is
well-defined, while probability laws and independence are stated after erasing
the support proof.  This is the exact random variable appearing in
`StochasticRun.sample_law` and `StochasticRun.sample_iIndep`. -/
private def erasedSampleCoord (kr : ℕ × Fin SR.batchSize) (ω : Ω) : ι :=
  (SR.sample ω kr.1 kr.2).1

/-- Finite block of all mini-batch coordinates with sample time strictly before
`k`.  This is the generated strict-past sigma algebra for the current
mini-batch at time `k`. -/
private def strictPastMiniBatchBlock (k : ℕ) : Finset (ℕ × Fin SR.batchSize) :=
  (Finset.range k).product Finset.univ

/-- Sigma algebra generated by all erased mini-batch sample coordinates before
time `k`. -/
private noncomputable def strictPastMiniBatchMeasurableSpace (k : ℕ) :
    MeasurableSpace Ω :=
  SOptLib.sampleBlockMeasurableSpace (erasedSampleCoord SR)
    (strictPastMiniBatchBlock SR k)

private theorem erasedSampleCoord_measurable (kr : ℕ × Fin SR.batchSize) :
    Measurable (erasedSampleCoord SR kr) := by
  classical
  have hbatch : Measurable (fun ω : Ω => SR.sample ω kr.1) :=
    SR.sample_batch_measurable kr.1
  have hcoord :
      Measurable
        (fun sample : Setup.MiniBatch (ι := ι) SR.Q SR.batchSize =>
          (sample kr.2).1) := by
    fun_prop
  simpa [erasedSampleCoord] using hcoord.comp hbatch

private theorem strictPastMiniBatchBlock_subset_pastSet (k : ℕ) :
    ↑(strictPastMiniBatchBlock SR k) ⊆
      ({kr : ℕ × Fin SR.batchSize | kr.1 < k} : Set (ℕ × Fin SR.batchSize)) := by
  intro kr hkr
  rcases Finset.mem_product.mp hkr with ⟨hk, _hr⟩
  simpa using Finset.mem_range.mp hk

private theorem strictPastMiniBatchBlock_measurableSpace_le_iSup (k : ℕ) :
    strictPastMiniBatchMeasurableSpace SR k ≤
      (⨆ kr ∈ ({kr : ℕ × Fin SR.batchSize | kr.1 < k} :
          Set (ℕ × Fin SR.batchSize)),
        MeasurableSpace.comap (erasedSampleCoord SR kr)
          (by infer_instance : MeasurableSpace ι)) := by
  exact SOptLib.sampleBlockMeasurableSpace_le_iSup_of_subset
    (erasedSampleCoord SR) (strictPastMiniBatchBlock SR k)
    (strictPastMiniBatchBlock_subset_pastSet SR k)

/-- Generated state-pairs before time `k-1` are measurable from the strict-past
mini-batch block before current sample time `k`.

This is the source adaptedness bridge needed before applying the iid freshness
API to Lemma 6.10.  The proof uses the finite-range recursive-process
measurability theorem, avoiding any global measurability assumption on the
paper's prox selector. -/
private theorem statePair_strictPast_measurable
    (k n : ℕ) (hn : n + 2 ≤ k) :
    Measurable[
      strictPastMiniBatchMeasurableSpace SR k]
      (fun ω : Ω => statePair SR ω n) := by
  classical
  let process : ℕ → Ω → Feasible S × Ambient d :=
    fun m ω => statePair SR ω m
  let driver : ℕ → Ω → Setup.MiniBatch (ι := ι) SR.Q SR.batchSize :=
    fun j ω => SR.sample ω (j + 2)
  let step : ℕ → Feasible S × Ambient d →
      Setup.MiniBatch (ι := ι) SR.Q SR.batchSize → Feasible S × Ambient d :=
    fun j st sample =>
      let xNext : Feasible S := Setup.mirrorStep S st.1 st.2 SR.gamma SR.gamma_pos
      let GNext : Ambient d :=
        if Setup.isEpochStart SR.T (j + 2) then
          Setup.fullGradient S xNext.1
        else
          Setup.recursiveEstimator S SR.Q SR.batchSize sample xNext st.1 st.2
      (xNext, GNext)
  have h_init_meas :
      @Measurable Ω (Feasible S × Ambient d)
        (strictPastMiniBatchMeasurableSpace SR k) (by infer_instance) (process 0) := by
    change @Measurable Ω (Feasible S × Ambient d)
      (strictPastMiniBatchMeasurableSpace SR k) (by infer_instance)
      (fun _ : Ω => (SR.x₁, Setup.fullGradient S SR.x₁.1))
    exact measurable_const
  have h_init_finite : (Set.range (process 0)).Finite := by
    refine (Set.finite_singleton
      (SR.x₁, Setup.fullGradient S SR.x₁.1)).subset ?_
    rintro z ⟨ω, rfl⟩
    simp [process, statePair, pathRun, Run.stateSeq, Run.initialState]
  have h_driver_meas :
      ∀ j : ℕ, j + 1 ≤ n →
        @Measurable Ω (Setup.MiniBatch (ι := ι) SR.Q SR.batchSize)
          (strictPastMiniBatchMeasurableSpace SR k) (by infer_instance) (driver j) := by
    intro j hj
    have hjk : j + 2 < k := by omega
    have hcoord :
        ∀ r : Fin SR.batchSize,
          @Measurable Ω ι (strictPastMiniBatchMeasurableSpace SR k) (by infer_instance)
            (fun ω : Ω => erasedSampleCoord SR (j + 2, r) ω) := by
      intro r
      have hmem : (j + 2, r) ∈ strictPastMiniBatchBlock SR k := by
        exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr hjk, Finset.mem_univ r⟩
      exact measurable_iff_comap_le.mpr (by
        rw [strictPastMiniBatchMeasurableSpace, SOptLib.sampleBlockMeasurableSpace]
        exact le_iSup_of_le (⟨(j + 2, r), hmem⟩ :
          {q // q ∈ strictPastMiniBatchBlock SR k}) le_rfl)
    change @Measurable Ω (Setup.MiniBatch (ι := ι) SR.Q SR.batchSize)
      (strictPastMiniBatchMeasurableSpace SR k) (by infer_instance)
      (fun ω : Ω => SR.sample ω (j + 2))
    exact
      @SOptLib.measurable_pi_subtype_mk_of_val_measurable Ω (Fin SR.batchSize)
        (strictPastMiniBatchMeasurableSpace SR k)
        (fun _ : Fin SR.batchSize => ι)
        (fun _ : Fin SR.batchSize => inferInstance)
        (fun _ : Fin SR.batchSize => fun i : ι => 0 < probabilityMass SR.Q i)
        (fun ω : Ω => SR.sample ω (j + 2))
        (fun r => by
          simpa [erasedSampleCoord] using hcoord r)
  have h_driver_finite :
      ∀ j : ℕ, j + 1 ≤ n → (Set.range (driver j)).Finite := by
    intro j hj
    haveI : Finite (Setup.MiniBatch (ι := ι) SR.Q SR.batchSize) := inferInstance
    exact Set.toFinite (Set.range (driver j))
  have h_update :
      ∀ j : ℕ, j + 1 ≤ n →
        ∀ ω : Ω, process (j + 1) ω = step j (process j ω) (driver j ω) := by
    intro j hj ω
    simp [process, driver, step, statePair, pathRun, Run.stateSeq, Run.nextState]
  exact
    (SOptLib.recursive_process_measurable_finite_range_wrt_history
      (mHist := strictPastMiniBatchMeasurableSpace SR k)
      (process := process)
      (driver := driver)
      (step := step)
      (N := n)
      (n := n)
      h_init_meas
      h_init_finite
      h_driver_meas
      h_driver_finite
      h_update
      le_rfl).1

/-- Strict-past query key for Lemma 6.10: current iterate, previous iterate, and
previous estimator residual.  The current iterate `x_k` is computed before the
time-`k` mini-batch is read, so the key is a function of the generated state at
time `k-2`. -/
private noncomputable def oneStepVarianceQueryKey (k : ℕ) (ω : Ω) :
    Feasible S × Feasible S × Ambient d :=
  (Run.iterate (pathRun SR ω) k,
    Run.iterate (pathRun SR ω) (k - 1),
    Run.estimatorError (pathRun SR ω) (k - 1))

/-- The Lemma 6.10 strict-past query key is a measurable finite-range function of
the generated state before the current mini-batch is read. -/
private theorem oneStepVarianceQueryKey_measurable_finite_range
    (k : ℕ) (hk_two : 2 ≤ k) :
    Measurable (oneStepVarianceQueryKey SR k) ∧
      (Set.range (oneStepVarianceQueryKey SR k)).Finite := by
  classical
  let n : ℕ := k - 2
  have hstate :=
    statePair_measurable_finite_range SR n n le_rfl
  have hconst :
      ∀ ⦃ω ω' : Ω⦄, statePair SR ω n = statePair SR ω' n →
        oneStepVarianceQueryKey SR k ω = oneStepVarianceQueryKey SR k ω' := by
    intro ω ω' hpair
    have hxprev :
        Run.iterate (pathRun SR ω) (k - 1) =
          Run.iterate (pathRun SR ω') (k - 1) := by
      have hn_iter : k - 1 - 1 = n := by
        dsimp [n]
        omega
      simpa [statePair, Run.iterate, hn_iter] using congrArg Prod.fst hpair
    have hGprev :
        Run.estimator (pathRun SR ω) (k - 1) =
          Run.estimator (pathRun SR ω') (k - 1) := by
      have hn_est : k - 1 - 1 = n := by
        dsimp [n]
        omega
      simpa [statePair, Run.estimator, hn_est] using congrArg Prod.snd hpair
    have hxcurr :
        Run.iterate (pathRun SR ω) k =
          Run.iterate (pathRun SR ω') k := by
      have hn_one : n + 1 = k - 1 := by
        dsimp [n]
        omega
      have hnextω := Run.next_iterate_eq_mirrorStep (pathRun SR ω) n
      have hnextω' := Run.next_iterate_eq_mirrorStep (pathRun SR ω') n
      have hxprev_state :
          (Run.stateSeq (pathRun SR ω) n).x =
            (Run.stateSeq (pathRun SR ω') n).x := congrArg Prod.fst hpair
      have hGprev_state :
          (Run.stateSeq (pathRun SR ω) n).G =
            (Run.stateSeq (pathRun SR ω') n).G := congrArg Prod.snd hpair
      change (Run.stateSeq (pathRun SR ω) (k - 1)).x =
        (Run.stateSeq (pathRun SR ω') (k - 1)).x
      rw [← hn_one, hnextω, hnextω', hxprev_state, hGprev_state]
      simp [pathRun]
    have hdelta_prev :
        Run.estimatorError (pathRun SR ω) (k - 1) =
          Run.estimatorError (pathRun SR ω') (k - 1) := by
      change
        Run.estimator (pathRun SR ω) (k - 1) -
            Setup.fullGradient S (Run.iterate (pathRun SR ω) (k - 1)).1 =
          Run.estimator (pathRun SR ω') (k - 1) -
            Setup.fullGradient S (Run.iterate (pathRun SR ω') (k - 1)).1
      rw [hGprev, hxprev]
    rw [oneStepVarianceQueryKey, oneStepVarianceQueryKey, hxcurr, hxprev, hdelta_prev]
  constructor
  · exact measurable_of_finite_range_fiber_const hstate.1 hstate.2 hconst
  · exact Set.Finite.range_of_finite_range_fiber_const hstate.2 hconst

/-- The Lemma 6.10 one-step query key is fresh from the current mini-batch
coordinate, with the peer-coordinate variant needed by centered mini-batch
variance APIs. -/
private theorem pathRun_strict_past_freshness_for_epoch_sample
    (hmini_iIndep :
      ProbabilityTheory.iIndepFun
        (fun kr : ℕ × Fin SR.batchSize => fun ω : Ω => (SR.sample ω kr.1 kr.2).1)
        SR.P)
    (k : ℕ) (hk_two : 2 ≤ k) (r : Fin SR.batchSize) :
    ProbabilityTheory.IndepFun (oneStepVarianceQueryKey SR k)
        (fun ω : Ω => (SR.sample ω k r).1) SR.P ∧
      ∀ peer : Fin SR.batchSize, peer ≠ r →
        ProbabilityTheory.IndepFun
          (fun ω : Ω => (oneStepVarianceQueryKey SR k ω,
            (SR.sample ω k peer).1))
          (fun ω : Ω => (SR.sample ω k r).1) SR.P := by
  classical
  let pastSet : Set (ℕ × Fin SR.batchSize) :=
    {kr | kr.1 < k}
  have hkey_meas :
      Measurable[strictPastMiniBatchMeasurableSpace SR k]
        (oneStepVarianceQueryKey SR k) := by
    let n : ℕ := k - 2
    have hn_add_two : n + 2 = k := by
      dsimp [n]
      omega
    have hstate :
        Measurable[strictPastMiniBatchMeasurableSpace SR k]
          (fun ω : Ω => statePair SR ω n) := by
      simpa [hn_add_two] using
        statePair_strictPast_measurable SR k n (by omega)
    refine
      @measurable_of_finite_range_fiber_const Ω (Feasible S × Ambient d)
        (Feasible S × Feasible S × Ambient d)
        (strictPastMiniBatchMeasurableSpace SR k)
        (by infer_instance) (by infer_instance) (by infer_instance)
        (Y := fun ω : Ω => statePair SR ω n)
        (Z := oneStepVarianceQueryKey SR k)
        hstate ((statePair_measurable_finite_range SR n n le_rfl).2) ?_
    intro ω ω' hpair
    have hxprev :
        Run.iterate (pathRun SR ω) (k - 1) =
          Run.iterate (pathRun SR ω') (k - 1) := by
      have hn_iter : k - 1 - 1 = n := by omega
      simpa [statePair, Run.iterate, hn_iter] using congrArg Prod.fst hpair
    have hGprev :
        Run.estimator (pathRun SR ω) (k - 1) =
          Run.estimator (pathRun SR ω') (k - 1) := by
      have hn_est : k - 1 - 1 = n := by omega
      simpa [statePair, Run.estimator, hn_est] using congrArg Prod.snd hpair
    have hxcurr :
        Run.iterate (pathRun SR ω) k =
          Run.iterate (pathRun SR ω') k := by
      have hn_one : n + 1 = k - 1 := by omega
      have hnextω := Run.next_iterate_eq_mirrorStep (pathRun SR ω) n
      have hnextω' := Run.next_iterate_eq_mirrorStep (pathRun SR ω') n
      have hxprev_state :
          (Run.stateSeq (pathRun SR ω) n).x =
            (Run.stateSeq (pathRun SR ω') n).x := congrArg Prod.fst hpair
      have hGprev_state :
          (Run.stateSeq (pathRun SR ω) n).G =
            (Run.stateSeq (pathRun SR ω') n).G := congrArg Prod.snd hpair
      change (Run.stateSeq (pathRun SR ω) (k - 1)).x =
        (Run.stateSeq (pathRun SR ω') (k - 1)).x
      rw [← hn_one, hnextω, hnextω', hxprev_state, hGprev_state]
      simp [pathRun]
    have hdelta_prev :
        Run.estimatorError (pathRun SR ω) (k - 1) =
          Run.estimatorError (pathRun SR ω') (k - 1) := by
      change
        Run.estimator (pathRun SR ω) (k - 1) -
            Setup.fullGradient S (Run.iterate (pathRun SR ω) (k - 1)).1 =
          Run.estimator (pathRun SR ω') (k - 1) -
            Setup.fullGradient S (Run.iterate (pathRun SR ω') (k - 1)).1
      rw [hGprev, hxprev]
    rw [oneStepVarianceQueryKey, oneStepVarianceQueryKey, hxcurr, hxprev, hdelta_prev]
  have hstrict_le :
      strictPastMiniBatchMeasurableSpace SR k ≤
        (⨆ kr ∈ pastSet,
          MeasurableSpace.comap (erasedSampleCoord SR kr)
            (by infer_instance : MeasurableSpace ι)) := by
    simpa [pastSet] using
      strictPastMiniBatchBlock_measurableSpace_le_iSup SR k
  have hpast_current_disj :
      Disjoint pastSet ({(k, r)} : Set (ℕ × Fin SR.batchSize)) := by
    rw [Set.disjoint_left]
    intro kr hkr hcur
    rcases hcur with rfl
    exact (Nat.lt_asymm hkr hkr).elim
  rcases
    indepFun_prefixKey_current_of_iIndepFun
      (sampleCoord := erasedSampleCoord SR)
      (μ := SR.P)
      (hsampleCoord_meas := erasedSampleCoord_measurable SR)
      (hsampleCoord_iIndep := by simpa [erasedSampleCoord] using hmini_iIndep)
      (pastSet := pastSet)
      (strictPast := strictPastMiniBatchMeasurableSpace SR k)
      (prefixKey := oneStepVarianceQueryKey SR k)
      (current := (k, r))
      hkey_meas hstrict_le hpast_current_disj with
    ⟨hcurrent, hpeer⟩
  constructor
  · simpa [erasedSampleCoord] using hcurrent
  · intro peer hpeer_ne
    have hleft_disj :
        Disjoint (pastSet ∪ ({(k, peer)} : Set (ℕ × Fin SR.batchSize)))
          ({(k, r)} : Set (ℕ × Fin SR.batchSize)) := by
      rw [Set.disjoint_left]
      intro kr hleft hcur
      rcases hcur with rfl
      rcases hleft with hpast | hpeer_mem
      · exact (Nat.lt_asymm hpast hpast).elim
      · have hpair : (k, r) = (k, peer) := by
          simpa using hpeer_mem
        exact hpeer_ne (Prod.ext_iff.mp hpair).2.symm
    simpa [erasedSampleCoord] using hpeer (k, peer) hleft_disj

/-- At the first coordinate of every epoch, Algorithm 6.6 refreshes the estimator
to the exact finite-sum gradient, so the estimator error is zero.

Aligns with Lan Lemma 6.10 proof step `δ₁=0`.  Considered
`SOptLib.estimatorResidualProcess_epochStart_eq_zero`; the local `Run` accessors
make a direct specialization through `Run.next_estimator_eq_fullGradient_of_epochStart`
simpler and avoid introducing a separate process wrapper. -/
private theorem epochIndex_estimatorError_base_zero (s : ℕ) :
    ∀ ω : Ω, Run.estimatorError (pathRun SR ω) (epochIndex SR s 1) = 0 := by
  intro ω
  have hrefresh :
      Run.estimator (pathRun SR ω) (epochIndex SR s 1) =
        Setup.fullGradient S (Run.iterate (pathRun SR ω) (epochIndex SR s 1)).1 := by
    cases s with
    | zero =>
        simp [epochIndex, Run.estimator, Run.iterate, pathRun, Run.stateSeq,
          Run.initialState]
    | succ r =>
        let n : ℕ := (r + 1) * SR.T - 1
        have hprod_pos : 0 < (r + 1) * SR.T :=
          Nat.mul_pos (Nat.succ_pos r) SR.T_pos
        have hn_add : n + 1 = (r + 1) * SR.T := by
          dsimp [n]
          exact Nat.sub_add_cancel (Nat.succ_le_iff.mpr hprod_pos)
        have hn_two : n + 2 = (r + 1) * SR.T + 1 := by omega
        have hidx : epochIndex SR (r + 1) 1 = n + 2 := by
          simp [epochIndex, hn_two]
        have hstart : Setup.isEpochStart (pathRun SR ω).T (n + 2) := by
          have hzero : ((r + 1) * SR.T) % SR.T = 0 := by
            rw [Nat.mul_comm]
            exact Nat.mul_mod_right SR.T (r + 1)
          simp [Setup.isEpochStart, pathRun, hn_two, hzero]
        have hG := Run.next_estimator_eq_fullGradient_of_epochStart (pathRun SR ω) n hstart
        have hx := Run.next_iterate_eq_mirrorStep (pathRun SR ω) n
        simpa [Run.estimator, Run.iterate, hidx, hx] using hG
  simp [Run.estimatorError, Setup.estimatorError, hrefresh]

/-- Uniform output index law over `{1,...,N}` for the stochastic run. -/
noncomputable def outputPMF : PMF (OutputIndex SR.horizon) :=
  uniformOutputPMF SR.horizon SR.horizon_pos

/-- Joint law of the uniform output index and Algorithm 6.6 sample randomness. -/
noncomputable def outputJointMeasure : Measure (OutputIndex SR.horizon × Ω) :=
  SOptLib.selected_joint_measure (outputPMF SR) SR.P

/-- Stochastic output `x_R` from Algorithm 6.6. -/
noncomputable def output (q : OutputIndex SR.horizon × Ω) : Feasible S :=
  Run.output (pathRun SR q.2) q.1

/-- Exact projected-gradient mapping at the stochastic output `x_R`. -/
noncomputable def outputExactGradientMapping (q : OutputIndex SR.horizon × Ω) : Ambient d :=
  Run.exactGradientMapping (pathRun SR q.2) q.1.1

/-- Expected squared projected-gradient mapping at the stochastic output. -/
noncomputable def expectedOutputExactGradientMappingSq : ℝ :=
  SOptLib.expectation (outputJointMeasure SR)
    (fun q : OutputIndex SR.horizon × Ω => ‖outputExactGradientMapping SR q‖ ^ 2)

/-- Well-definedness obligation for `E[Ψ(x_k)]`.

This is a source-proof bridge: Theorem 6.14 uses genuine expectations, so
integrability of this generated-process random variable is kept as a named proof
obligation rather than hidden inside Lean's total integral notation. -/
theorem expectedPsi_wellDefined (k : ℕ) :
    SOptLib.expectationWellDefined SR.P
      (fun ω : Ω => Setup.psi S (Run.iterate (pathRun SR ω) k).1) := by
  rw [SOptLib.expectationWellDefined_iff_integrable]
  letI : IsProbabilityMeasure SR.P := SR.P_isProbability
  haveI : IsFiniteMeasure SR.P := inferInstance
  rcases iterate_measurable_finite_range SR k with ⟨hiter_meas, hiter_fin⟩
  exact
    integrable_of_finiteRange_factor
      (Y := fun ω : Ω => Run.iterate (pathRun SR ω) k)
      (Z := fun ω : Ω => Setup.psi S (Run.iterate (pathRun SR ω) k).1)
      hiter_meas hiter_fin
      (by
        intro ω ω' h
        simpa [h])

/-- Well-definedness obligation for `E[‖g_{X,k}‖²]`. -/
theorem expectedExactGradientMappingSq_wellDefined (k : ℕ) :
    SOptLib.expectationWellDefined SR.P
      (fun ω : Ω => ‖Run.exactGradientMapping (pathRun SR ω) k‖ ^ 2) := by
  rw [SOptLib.expectationWellDefined_iff_integrable]
  letI : IsProbabilityMeasure SR.P := SR.P_isProbability
  haveI : IsFiniteMeasure SR.P := inferInstance
  rcases iterate_measurable_finite_range SR k with ⟨hiter_meas, hiter_fin⟩
  exact
    integrable_of_finiteRange_factor
      (Y := fun ω : Ω => Run.iterate (pathRun SR ω) k)
      (Z := fun ω : Ω => ‖Run.exactGradientMapping (pathRun SR ω) k‖ ^ 2)
      hiter_meas hiter_fin
      (by
        intro ω ω' h
        change
          ‖Setup.exactProjectedGradient S (Run.iterate (pathRun SR ω) k)
              SR.gamma SR.gamma_pos‖ ^ 2 =
            ‖Setup.exactProjectedGradient S (Run.iterate (pathRun SR ω') k)
              SR.gamma SR.gamma_pos‖ ^ 2
        exact
          congrArg
            (fun x : Feasible S =>
              ‖Setup.exactProjectedGradient S x SR.gamma SR.gamma_pos‖ ^ 2)
            h)

/-- Well-definedness obligation for `E[‖\tilde g_{X,k}‖²]`.

The stochastic projected-gradient mapping depends only on the finite-range
generated state key `(x_k,G_k)`, so its expectation is a genuine finite-range
expectation rather than a total-integral fallback. -/
theorem expectedStochasticGradientMappingSq_wellDefined (k : ℕ) :
    SOptLib.expectationWellDefined SR.P
      (fun ω : Ω => ‖Run.stochasticGradientMapping (pathRun SR ω) k‖ ^ 2) := by
  rw [SOptLib.expectationWellDefined_iff_integrable]
  letI : IsProbabilityMeasure SR.P := SR.P_isProbability
  haveI : IsFiniteMeasure SR.P := inferInstance
  rcases statePair_measurable_finite_range SR (k - 1) (k - 1) le_rfl with
    ⟨hstate_meas, hstate_fin⟩
  exact
    integrable_of_finiteRange_factor
      (Y := fun ω : Ω => statePair SR ω (k - 1))
      (Z := fun ω : Ω => ‖Run.stochasticGradientMapping (pathRun SR ω) k‖ ^ 2)
      hstate_meas hstate_fin
      (by
        intro ω ω' h
        have hx :
            Run.iterate (pathRun SR ω) k =
              Run.iterate (pathRun SR ω') k := by
          simpa [statePair, Run.iterate] using congrArg Prod.fst h
        have hG :
            Run.estimator (pathRun SR ω) k =
              Run.estimator (pathRun SR ω') k := by
          simpa [statePair, Run.estimator] using congrArg Prod.snd h
        change
          ‖Setup.stochasticProjectedGradient S (Run.iterate (pathRun SR ω) k)
              (Run.estimator (pathRun SR ω) k) SR.gamma SR.gamma_pos‖ ^ 2 =
            ‖Setup.stochasticProjectedGradient S (Run.iterate (pathRun SR ω') k)
              (Run.estimator (pathRun SR ω') k) SR.gamma SR.gamma_pos‖ ^ 2
        rw [hx, hG])

/-- Squared stochastic projected-gradient expectations are nonnegative. -/
theorem expectedStochasticGradientMappingSq_nonneg (k : ℕ) :
    0 ≤ expectedStochasticGradientMappingSq SR k := by
  unfold expectedStochasticGradientMappingSq SOptLib.expectation
  exact integral_nonneg fun ω => sq_nonneg _

/-- Well-definedness obligation for `E[‖δ_k‖²]`.

The estimator error is a deterministic function of the same generated state key
`(x_k,G_k)` used by Algorithm 6.6. -/
theorem expectedEstimatorErrorSq_wellDefined (k : ℕ) :
    SOptLib.expectationWellDefined SR.P
      (fun ω : Ω => ‖Run.estimatorError (pathRun SR ω) k‖ ^ 2) := by
  rw [SOptLib.expectationWellDefined_iff_integrable]
  letI : IsProbabilityMeasure SR.P := SR.P_isProbability
  haveI : IsFiniteMeasure SR.P := inferInstance
  rcases statePair_measurable_finite_range SR (k - 1) (k - 1) le_rfl with
    ⟨hstate_meas, hstate_fin⟩
  exact
    integrable_of_finiteRange_factor
      (Y := fun ω : Ω => statePair SR ω (k - 1))
      (Z := fun ω : Ω => ‖Run.estimatorError (pathRun SR ω) k‖ ^ 2)
      hstate_meas hstate_fin
      (by
        intro ω ω' h
        have hx :
            Run.iterate (pathRun SR ω) k =
              Run.iterate (pathRun SR ω') k := by
          simpa [statePair, Run.iterate] using congrArg Prod.fst h
        have hG :
            Run.estimator (pathRun SR ω) k =
              Run.estimator (pathRun SR ω') k := by
          simpa [statePair, Run.estimator] using congrArg Prod.snd h
        change
          ‖Setup.estimatorError S (Run.iterate (pathRun SR ω) k)
              (Run.estimator (pathRun SR ω) k)‖ ^ 2 =
            ‖Setup.estimatorError S (Run.iterate (pathRun SR ω') k)
              (Run.estimator (pathRun SR ω') k)‖ ^ 2
        rw [hx, hG])

/-- Well-definedness obligation for `E[‖x_k-x_{k-1}‖²]`.

The displacement observable is determined by the finite product key
`(x_k,x_{k-1})`, obtained from the existing finite-range generated-iterate
interface. -/
theorem expectedDisplacementSq_wellDefined (k : ℕ) :
    SOptLib.expectationWellDefined SR.P
      (fun ω : Ω =>
        ‖(Run.iterate (pathRun SR ω) k).1 -
            (Run.iterate (pathRun SR ω) (k - 1)).1‖ ^ 2) := by
  rw [SOptLib.expectationWellDefined_iff_integrable]
  letI : IsProbabilityMeasure SR.P := SR.P_isProbability
  haveI : IsFiniteMeasure SR.P := inferInstance
  rcases iterate_measurable_finite_range SR k with ⟨hk_meas, hk_fin⟩
  rcases iterate_measurable_finite_range SR (k - 1) with ⟨hprev_meas, hprev_fin⟩
  let Y : Ω → Feasible S × Feasible S :=
    fun ω => (Run.iterate (pathRun SR ω) k,
      Run.iterate (pathRun SR ω) (k - 1))
  have hY_meas : Measurable Y := by
    exact hk_meas.prod hprev_meas
  have hY_fin : (Set.range Y).Finite := by
    have hsubset :
        Set.range Y ⊆
          (Set.range (fun ω : Ω => Run.iterate (pathRun SR ω) k)).prod
            (Set.range (fun ω : Ω => Run.iterate (pathRun SR ω) (k - 1))) := by
      rintro y ⟨ω, rfl⟩
      exact ⟨⟨ω, rfl⟩, ⟨ω, rfl⟩⟩
    exact (hk_fin.prod hprev_fin).subset hsubset
  exact
    integrable_of_finiteRange_factor
      (Y := Y)
      (Z := fun ω : Ω =>
        ‖(Run.iterate (pathRun SR ω) k).1 -
            (Run.iterate (pathRun SR ω) (k - 1)).1‖ ^ 2)
      hY_meas hY_fin
      (by
        intro ω ω' h
        have hk :
            Run.iterate (pathRun SR ω) k =
              Run.iterate (pathRun SR ω') k := by
          simpa [Y] using congrArg Prod.fst h
        have hprev :
            Run.iterate (pathRun SR ω) (k - 1) =
              Run.iterate (pathRun SR ω') (k - 1) := by
          simpa [Y] using congrArg Prod.snd h
        have hk_val :
            (Run.iterate (pathRun SR ω) k).1 =
              (Run.iterate (pathRun SR ω') k).1 :=
          congrArg Subtype.val hk
        have hprev_val :
            (Run.iterate (pathRun SR ω) (k - 1)).1 =
              (Run.iterate (pathRun SR ω') (k - 1)).1 :=
          congrArg Subtype.val hprev
        change
          ‖(Run.iterate (pathRun SR ω) k).1 -
              (Run.iterate (pathRun SR ω) (k - 1)).1‖ ^ 2 =
            ‖(Run.iterate (pathRun SR ω') k).1 -
              (Run.iterate (pathRun SR ω') (k - 1)).1‖ ^ 2
        rw [hk_val, hprev_val])

/-- Algorithm 6.6 displacement identity in expectation form.

For a positive one-based update index `k`, the generated mirror step gives
`x_{k+1}-x_k = -γ \tilde g_{X,k}`. This is the source identity used when
Lemma 6.10's displacement variance bound is substituted into the epoch descent
recursion. -/
theorem expectedDisplacementSq_succ_eq_gamma_sq_mul_stochasticGradientMappingSq
    (k : PositiveIteration) :
    expectedDisplacementSq SR (k.1 + 1) =
      SR.gamma ^ 2 * expectedStochasticGradientMappingSq SR k.1 := by
  classical
  unfold expectedDisplacementSq expectedStochasticGradientMappingSq SOptLib.expectation
  have hk_succ_pred : k.1 + 1 - 1 = k.1 := Nat.succ_sub_one k.1
  simpa [hk_succ_pred] using
    (integral_update_displacement_sq_eq_mul_integral_direction_sq
      (μ := SR.P)
      (x := fun ω : Ω => (Run.iterate (pathRun SR ω) k.1).1)
      (xNext := fun ω : Ω => (Run.iterate (pathRun SR ω) (k.1 + 1)).1)
      (g := fun ω : Ω => Run.stochasticGradientMapping (pathRun SR ω) k.1)
      (gamma := SR.gamma)
      (by
        intro ω
        let Rω := pathRun SR ω
        let x : Feasible S := Run.iterate Rω k.1
        let y : Feasible S := Run.iterate Rω (k.1 + 1)
        let stoch : Ambient d := Run.stochasticGradientMapping Rω k.1
        have hnext := Run.iterate_succ_eq_proxPoint Rω k
        have hstoch_def :
            stoch = SR.gamma⁻¹ • (x.1 - y.1) := by
          simp [Rω, x, y, stoch, Run.stochasticGradientMapping, pathRun,
            Setup.stochasticProjectedGradient, Setup.projectedGradient_def, hnext]
        have hgamma_ne : SR.gamma ≠ 0 := ne_of_gt SR.gamma_pos
        have hgamma_smul_stoch : SR.gamma • stoch = x.1 - y.1 := by
          rw [hstoch_def, smul_smul, mul_inv_cancel₀ hgamma_ne, one_smul]
        have hdisp : y.1 - x.1 = -(SR.gamma • stoch) := by
          calc
            y.1 - x.1 = -(x.1 - y.1) := by abel
            _ = -(SR.gamma • stoch) := by rw [← hgamma_smul_stoch]
        simpa [Rω, x, y, stoch] using hdisp))

/-- Deterministic coefficient simplification in Eq. (6.5.6).

Under the smoothness-proportional law `qᵢ=Lᵢ/(mL)`, the weighted second moment
of the inverse-probability component-gradient increment is bounded by
`L^2‖x-y‖^2`.  This packages Lemma 6.10 proof steps 5--7 at the source
granularity needed by the stochastic mini-batch variance route. -/
private theorem importance_weighted_atom_second_moment_bound
    (x y : Feasible S) :
    Finset.sum Finset.univ (fun i : ι =>
        probabilityMass (Setup.importancePMF S) i *
          ‖SOptLib.importance_weighted_gradient_difference
              (fun j : ι => probabilityMass (Setup.importancePMF S) j)
              (Fintype.card ι : ℝ) (Setup.componentGradient S) x.1 y.1 i‖ ^ 2) ≤
      S.L ^ 2 * ‖x.1 - y.1‖ ^ 2 := by
  classical
  let q : ι → ℝ := fun i => probabilityMass (Setup.importancePMF S) i
  let n : ℝ := Fintype.card ι
  have hn_pos : 0 < n := by
    have h : 0 < (Fintype.card ι : ℝ) := by
      exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
    simpa [n] using h
  have hL_pos : 0 < S.L := Setup.L_pos S
  have hL_average : S.L = n⁻¹ * ∑ i : ι, S.Lcomp i := by
    simpa [finiteAverage, SOptLib.finiteUniformAverage, smul_eq_mul, n] using
      S.L_eq_average
  have hq_smooth :
      ∀ i : ι, q i = SOptLib.smoothnessImportanceWeight S.Lcomp n S.L i := by
    intro i
    have hprob_pos : 0 < Setup.importanceProbability S i := by
      simpa [Setup.importanceProbability, n] using
        SOptLib.smoothnessImportanceWeight_pos (S.Lcomp_pos i) hn_pos hL_pos
    dsimp [q, probabilityMass]
    rw [Setup.importancePMF_apply,
      ENNReal.toReal_ofReal (le_of_lt hprob_pos)]
    rfl
  have hgrad_lipschitz :
      ∀ i : ι,
        ‖Setup.componentGradient S i y.1 - Setup.componentGradient S i x.1‖ ≤
          S.Lcomp i * ‖x.1 - y.1‖ := by
    intro i
    simpa [Setup.componentGradient, norm_sub_rev] using
      S.component_lipschitz_grad i y.1 y.2 x.1 x.2
  have hbound :=
    SOptLib.importance_weighted_gradient_difference_second_moment_le_smoothness
      (q := q) (Lcomp := S.Lcomp) (n := n) (L := S.L)
      (gradF := Setup.componentGradient S) (dist := fun z w => ‖z - w‖)
      (x := x.1) (y := y.1)
      hn_pos hL_average hq_smooth S.Lcomp_pos (norm_nonneg _) hgrad_lipschitz
  simpa [q, n] using hbound

/-- Centered deterministic atom budget behind Lemma 6.10 / Eq. (6.5.6).

This is the finite-sum algebra part of the source proof: the importance-weighted
gradient-difference atom has weighted mean `∇f(x)-∇f(y)`, hence centering by
that mean cannot increase its weighted second moment. -/
private theorem importance_weighted_centered_atom_second_moment_bound
    (x y : Feasible S) :
    Finset.sum Finset.univ (fun i : ι =>
        probabilityMass (Setup.importancePMF S) i *
          ‖SOptLib.importance_weighted_gradient_difference
              (fun j : ι => probabilityMass (Setup.importancePMF S) j)
              (Fintype.card ι : ℝ) (Setup.componentGradient S) x.1 y.1 i -
            (Setup.fullGradient S x.1 - Setup.fullGradient S y.1)‖ ^ 2) ≤
      S.L ^ 2 * ‖x.1 - y.1‖ ^ 2 := by
  classical
  let q : ι → ℝ := fun i => probabilityMass (Setup.importancePMF S) i
  let n : ℝ := Fintype.card ι
  have hqsum : Finset.sum Finset.univ q = 1 := by
    have hsum_enn :
        (Finset.sum Finset.univ (fun i : ι => Setup.importancePMF S i)) = 1 := by
      simpa [tsum_fintype] using (PMF.tsum_coe (Setup.importancePMF S))
    have hsum_real := congrArg ENNReal.toReal hsum_enn
    rw [ENNReal.toReal_sum, ENNReal.toReal_one] at hsum_real
    · simpa [q, probabilityMass] using hsum_real
    · intro i _hi
      exact ne_top_of_le_ne_top
        ENNReal.one_ne_top (PMF.coe_le_one (Setup.importancePMF S) i)
  have hn_pos : 0 < n := by
    have h : 0 < (Fintype.card ι : ℝ) := by
      exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
    simpa [n] using h
  have hn_ne : n ≠ 0 := ne_of_gt hn_pos
  have hq_ne : ∀ i : ι, q i ≠ 0 := by
    intro i
    exact ne_of_gt (by
      simpa [q, probabilityMass] using Setup.importancePMF_atom_toReal_pos S i)
  exact
    SOptLib.importance_weighted_centered_gradient_difference_second_moment_le
      (q := q) (n := n)
      (C := S.L ^ 2 * ‖x.1 - y.1‖ ^ 2)
      (gradF := Setup.componentGradient S) (x := x.1) (y := y.1)
      (mean := Setup.fullGradient S x.1 - Setup.fullGradient S y.1)
      hqsum hq_ne hn_ne
      (by
        simpa [q, n, Setup.fullGradient, finiteAverage, SOptLib.finiteUniformAverage])
      (by
        simpa [q, n] using importance_weighted_atom_second_moment_bound (S := S) x y)

/-- Fixed-fiber centering of the importance-weighted gradient-difference atom.

This is the vector zero-mean statement behind Lemma 6.10's
`E[ζᵢ]=∇f(x_t)-∇f(x_{t-1})`, expressed for the smoothness-proportional PMF
from Eq. (6.5.4). -/
private theorem importance_weighted_centered_atom_weighted_sum_eq_zero
    (x y : Feasible S) :
    Finset.sum Finset.univ (fun i : ι =>
        probabilityMass (Setup.importancePMF S) i •
          (SOptLib.importance_weighted_gradient_difference
              (fun j : ι => probabilityMass (Setup.importancePMF S) j)
              (Fintype.card ι : ℝ) (Setup.componentGradient S) x.1 y.1 i -
            (Setup.fullGradient S x.1 - Setup.fullGradient S y.1))) = 0 := by
  classical
  let q : ι → ℝ := fun i => probabilityMass (Setup.importancePMF S) i
  let n : ℝ := Fintype.card ι
  have hqsum : Finset.sum Finset.univ q = 1 := by
    have hsum_enn :
        (Finset.sum Finset.univ (fun i : ι => Setup.importancePMF S i)) = 1 := by
      simpa [tsum_fintype] using (PMF.tsum_coe (Setup.importancePMF S))
    have hsum_real := congrArg ENNReal.toReal hsum_enn
    rw [ENNReal.toReal_sum, ENNReal.toReal_one] at hsum_real
    · simpa [q, probabilityMass] using hsum_real
    · intro i _hi
      exact ne_top_of_le_ne_top
        ENNReal.one_ne_top (PMF.coe_le_one (Setup.importancePMF S) i)
  have hn_pos : 0 < n := by
    have h : 0 < (Fintype.card ι : ℝ) := by
      exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
    simpa [n] using h
  have hn_ne : n ≠ 0 := ne_of_gt hn_pos
  have hq_ne : ∀ i : ι, q i ≠ 0 := by
    intro i
    exact ne_of_gt (by
      simpa [q, probabilityMass] using Setup.importancePMF_atom_toReal_pos S i)
  have hmean :
      Finset.sum Finset.univ (fun i : ι =>
          q i •
            SOptLib.importance_weighted_gradient_difference q n
              (Setup.componentGradient S) x.1 y.1 i) =
        Setup.fullGradient S x.1 - Setup.fullGradient S y.1 := by
    have hsum :=
      SOptLib.finset_weighted_sum_importance_weighted_gradient_difference_eq_uniform_sum_sub
        (s := (Finset.univ : Finset ι))
        (q := q) (n := n) (gradF := Setup.componentGradient S)
        (x := x.1) (y := y.1)
        (by intro i _hi; exact hq_ne i) hn_ne
    simpa [q, n, Setup.fullGradient, finiteAverage, SOptLib.finiteUniformAverage]
      using hsum
  simpa [q, n] using
    finset_weighted_residual_sum_eq_zero
      (s := (Finset.univ : Finset ι)) (q := q)
      (a := fun i : ι =>
        SOptLib.importance_weighted_gradient_difference q n
          (Setup.componentGradient S) x.1 y.1 i)
      (μ := Setup.fullGradient S x.1 - Setup.fullGradient S y.1)
      hqsum hmean

/-- Source one-step variance recurrence inside an epoch, Eq. (6.5.6).

Aligns with Lan Lemma 6.10 proof steps defining `ζᵢ`, using the importance law
`qᵢ=Lᵢ/(mL)`, iid mini-batch centering, and component Lipschitz gradients.
Considered `SOptLib.recursiveEstimatorResidual_secondMoment_step_le_of_centered_minibatch`
and the finite importance-weighted mean lemma; this local bridge remains needed
to connect Algorithm 6.6's concrete `SR.sample` support-valued stream, `hQ`,
`hsample_law`, and `hsample_iIndep` to those abstract centered-minibatch
hypotheses without strengthening the public stochastic run model. -/
private theorem source_importance_minibatch_variance_step
    (hQ : SR.Q = Setup.importancePMF S)
    (hsample_law :
      ∀ k : ℕ, ∀ r : Fin SR.batchSize,
        Measure.map (fun ω : Ω => (SR.sample ω k r).1) SR.P = SR.Q.toMeasure)
    (hsample_iIndep :
      ProbabilityTheory.iIndepFun
        (fun kr : ℕ × Fin SR.batchSize => fun ω : Ω => (SR.sample ω kr.1 kr.2).1)
        SR.P)
    (s j : ℕ) (hj_two : 2 ≤ j) (hj_epoch : j ≤ SR.T) :
    expectedEstimatorErrorSq SR (epochIndex SR s j) ≤
      expectedEstimatorErrorSq SR (epochIndex SR s (j - 1)) +
        (S.L ^ 2 / (SR.batchSize : ℝ)) *
          expectedDisplacementSq SR (epochIndex SR s j) := by
  classical
  letI : IsProbabilityMeasure SR.P := SR.P_isProbability
  have hQ_atom_pos : ∀ i : ι, 0 < (Setup.importancePMF S i).toReal :=
    Setup.importancePMF_atom_toReal_pos S
  have hbatch_pos : 0 < SR.batchSize := SR.batchSize_pos
  have hprev_wd := expectedEstimatorErrorSq_wellDefined SR (epochIndex SR s (j - 1))
  have hcurr_wd := expectedEstimatorErrorSq_wellDefined SR (epochIndex SR s j)
  have hdisp_wd := expectedDisplacementSq_wellDefined SR (epochIndex SR s j)
  have hj_pos : 1 ≤ j := le_trans (by norm_num : 1 ≤ 2) hj_two
  have hnot_start : ¬ Setup.isEpochStart SR.T (epochIndex SR s j) := by
    intro hstart
    have hstep :
        SOptLib.stepOfIndex SR.T (epochIndex SR s j) = j := by
      simpa [epochIndex, SOptLib.global_index] using
        (SOptLib.stepOfIndex_mul_add_eq_of_pos_le
          (T := SR.T) (s := s) (j := j) hj_pos hj_epoch)
    have hstep_start :
        SOptLib.stepOfIndex SR.T (epochIndex SR s j) = 1 := by
      have hmod : (epochIndex SR s j - 1) % SR.T = 0 := by
        simpa [Setup.isEpochStart] using hstart
      rw [SOptLib.stepOfIndex_eq_mod_add_one, hmod]
    omega
  have hrecursive_estimator :
      ∀ ω : Ω,
        Run.estimator (pathRun SR ω) (epochIndex SR s j) =
          Setup.recursiveEstimator S SR.Q SR.batchSize (SR.sample ω (epochIndex SR s j))
            (Run.iterate (pathRun SR ω) (epochIndex SR s j))
            (Run.iterate (pathRun SR ω) (epochIndex SR s j - 1))
            (Run.estimator (pathRun SR ω) (epochIndex SR s j - 1)) := by
    intro ω
    let n : ℕ := epochIndex SR s j - 2
    have hk_two : 2 ≤ epochIndex SR s j := by
      unfold epochIndex
      omega
    have hn_two : n + 2 = epochIndex SR s j := by
      dsimp [n]
      omega
    have hn_one : n + 1 = epochIndex SR s j - 1 := by
      dsimp [n]
      omega
    have hn_pred : n = epochIndex SR s j - 1 - 1 := by
      dsimp [n]
      omega
    have hk_sub_add_one : epochIndex SR s j - 1 - 1 + 1 = epochIndex SR s j - 1 := by
      omega
    have hk_sub_add_two : epochIndex SR s j - 1 - 1 + 2 = epochIndex SR s j := by
      omega
    have hnot : ¬ Setup.isEpochStart (pathRun SR ω).T (n + 2) := by
      simpa [pathRun, hn_two] using hnot_start
    have hG := Run.next_estimator_eq_recursive_of_not_epochStart (pathRun SR ω) n hnot
    have hx := Run.next_iterate_eq_mirrorStep (pathRun SR ω) n
    rw [← hx] at hG
    simpa [Run.estimator, Run.iterate, pathRun, hn_two, hn_one, hn_pred,
      hk_sub_add_one, hk_sub_add_two] using hG
  have hresidual_raw :
      ∀ ω : Ω,
        Run.estimatorError (pathRun SR ω) (epochIndex SR s j) =
          Run.estimatorError (pathRun SR ω) (epochIndex SR s j - 1) +
            Setup.miniBatchGradientDifference S SR.Q SR.batchSize
              (SR.sample ω (epochIndex SR s j))
              (Run.iterate (pathRun SR ω) (epochIndex SR s j))
              (Run.iterate (pathRun SR ω) (epochIndex SR s j - 1)) -
            (Setup.fullGradient S (Run.iterate (pathRun SR ω) (epochIndex SR s j)).1 -
              Setup.fullGradient S (Run.iterate (pathRun SR ω) (epochIndex SR s j - 1)).1) := by
    intro ω
    simp [Run.estimatorError, Setup.estimatorError, hrecursive_estimator ω,
      Setup.recursiveEstimator]
    abel
  have himportance_atom_bound :
      ∀ ω : Ω,
        Finset.sum Finset.univ (fun i : ι =>
            probabilityMass (Setup.importancePMF S) i *
              ‖SOptLib.importance_weighted_gradient_difference
                  (fun j : ι => probabilityMass (Setup.importancePMF S) j)
                  (Fintype.card ι : ℝ) (Setup.componentGradient S)
                  (Run.iterate (pathRun SR ω) (epochIndex SR s j)).1
                  (Run.iterate (pathRun SR ω) (epochIndex SR s j - 1)).1 i‖ ^ 2) ≤
          S.L ^ 2 *
            ‖(Run.iterate (pathRun SR ω) (epochIndex SR s j)).1 -
                (Run.iterate (pathRun SR ω) (epochIndex SR s j - 1)).1‖ ^ 2 := by
    intro ω
    exact importance_weighted_atom_second_moment_bound (S := S)
      (Run.iterate (pathRun SR ω) (epochIndex SR s j))
      (Run.iterate (pathRun SR ω) (epochIndex SR s j - 1))
  have hk_two : 2 ≤ epochIndex SR s j := by
    unfold epochIndex
    omega
  have hstrict_past_freshness :
      ∀ r : Fin SR.batchSize,
        ProbabilityTheory.IndepFun (oneStepVarianceQueryKey SR (epochIndex SR s j))
            (fun ω : Ω => (SR.sample ω (epochIndex SR s j) r).1) SR.P ∧
          ∀ peer : Fin SR.batchSize, peer ≠ r →
            ProbabilityTheory.IndepFun
              (fun ω : Ω => (oneStepVarianceQueryKey SR (epochIndex SR s j) ω,
                (SR.sample ω (epochIndex SR s j) peer).1))
              (fun ω : Ω => (SR.sample ω (epochIndex SR s j) r).1) SR.P := by
    intro r
    exact pathRun_strict_past_freshness_for_epoch_sample SR
      hsample_iIndep (epochIndex SR s j) hk_two r
  let k : ℕ := epochIndex SR s j
  let deltaPrev : Ω → Ambient d :=
    fun ω => Run.estimatorError (pathRun SR ω) (k - 1)
  let deltaNext : Ω → Ambient d :=
    fun ω => Run.estimatorError (pathRun SR ω) k
  let xCurr : Ω → Ambient d :=
    fun ω => (Run.iterate (pathRun SR ω) k).1
  let xPrev : Ω → Ambient d :=
    fun ω => (Run.iterate (pathRun SR ω) (k - 1)).1
  let targetDiff : Ω → Ambient d :=
    fun ω => Setup.fullGradient S (xCurr ω) - Setup.fullGradient S (xPrev ω)
  let eps : Fin SR.batchSize → Ω → Ambient d :=
    fun r ω =>
      importanceWeightedGradientDifference SR.Q (Setup.componentGradient S)
        (xCurr ω) (xPrev ω) (SR.sample ω k r) - targetDiff ω
  have himportance_centered_atom_bound :
      ∀ ω : Ω,
        Finset.sum Finset.univ (fun i : ι =>
            probabilityMass (Setup.importancePMF S) i *
              ‖SOptLib.importance_weighted_gradient_difference
                  (fun j : ι => probabilityMass (Setup.importancePMF S) j)
                  (Fintype.card ι : ℝ) (Setup.componentGradient S)
                  (xCurr ω) (xPrev ω) i - targetDiff ω‖ ^ 2) ≤
          S.L ^ 2 * ‖xCurr ω - xPrev ω‖ ^ 2 := by
    intro ω
    simpa [targetDiff, xCurr, xPrev, k] using
      importance_weighted_centered_atom_second_moment_bound (S := S)
        (Run.iterate (pathRun SR ω) k)
        (Run.iterate (pathRun SR ω) (k - 1))
  let inc : Ω → Ambient d :=
    fun ω => ((SR.batchSize : ℝ)⁻¹) •
      Finset.sum Finset.univ (fun r : Fin SR.batchSize => eps r ω)
  have hinc_eq :
      inc = fun ω => ((SR.batchSize : ℝ)⁻¹) •
        Finset.sum Finset.univ (fun r : Fin SR.batchSize => eps r ω) := by
    rfl
  have hrec :
      Filter.EventuallyEq (ae SR.P) deltaNext (fun ω => deltaPrev ω + inc ω) := by
    refine Filter.Eventually.of_forall ?_
    intro ω
    have hcenter :=
      inv_card_smul_sum_sub_const_eq
        (s := (Finset.univ : Finset (Fin SR.batchSize)))
        (z := fun r : Fin SR.batchSize =>
          importanceWeightedGradientDifference SR.Q (Setup.componentGradient S)
            (xCurr ω) (xPrev ω) (SR.sample ω k r))
        (c := targetDiff ω)
        (by simpa [Finset.card_univ] using SR.batchSize_pos)
    have hinc_point :
        inc ω =
          Setup.miniBatchGradientDifference S SR.Q SR.batchSize (SR.sample ω k)
            ⟨xCurr ω, (Run.iterate (pathRun SR ω) k).2⟩
            ⟨xPrev ω, (Run.iterate (pathRun SR ω) (k - 1)).2⟩ -
            targetDiff ω := by
      dsimp [inc, eps, Setup.miniBatchGradientDifference, finiteAverage]
      simpa [Finset.card_univ] using hcenter
    have hraw := hresidual_raw ω
    change Run.estimatorError (pathRun SR ω) (epochIndex SR s j) =
      deltaPrev ω + inc ω
    rw [hraw, hinc_point]
    simp [deltaPrev, xCurr, xPrev, targetDiff, k]
    abel
  have hdeltaPrev_meas :
      AEStronglyMeasurable deltaPrev SR.P := by
    have hmeas :
        Measurable
          (fun ω : Ω => Run.estimatorError (pathRun SR ω) (k - 1)) := by
      rcases statePair_measurable_finite_range SR (k - 1 - 1) (k - 1 - 1)
          le_rfl with
        ⟨hstate_meas, hstate_fin⟩
      refine measurable_of_finite_range_fiber_const hstate_meas hstate_fin ?_
      intro ω ω' hstate
      have hx :
          Run.iterate (pathRun SR ω) (k - 1) =
            Run.iterate (pathRun SR ω') (k - 1) := by
        simpa [statePair, Run.iterate] using congrArg Prod.fst hstate
      have hG :
          Run.estimator (pathRun SR ω) (k - 1) =
            Run.estimator (pathRun SR ω') (k - 1) := by
        simpa [statePair, Run.estimator] using congrArg Prod.snd hstate
      change
        Setup.estimatorError S (Run.iterate (pathRun SR ω) (k - 1))
            (Run.estimator (pathRun SR ω) (k - 1)) =
          Setup.estimatorError S (Run.iterate (pathRun SR ω') (k - 1))
            (Run.estimator (pathRun SR ω') (k - 1))
      rw [hx, hG]
    simpa [deltaPrev] using hmeas.aestronglyMeasurable
  have hdeltaPrev_sq :
      Integrable (fun ω => ‖deltaPrev ω‖ ^ 2) SR.P := by
    simpa [deltaPrev, k] using
      (SOptLib.expectationWellDefined_iff_integrable
        (μ := SR.P)
        (Z := fun ω : Ω =>
          ‖Run.estimatorError (pathRun SR ω) (epochIndex SR s j - 1)‖ ^ 2)).mp
        (expectedEstimatorErrorSq_wellDefined SR (epochIndex SR s j - 1))
  have heps_meas :
      ∀ r ∈ (Finset.univ : Finset (Fin SR.batchSize)),
        AEStronglyMeasurable (eps r) SR.P := by
    intro r _hr
    have hxCurr_meas : Measurable xCurr := by
      simpa [xCurr, k] using (iterate_measurable_finite_range SR k).1.subtype_val
    have hxPrev_meas : Measurable xPrev := by
      simpa [xPrev, k] using (iterate_measurable_finite_range SR (k - 1)).1.subtype_val
    have hsample_meas : Measurable (fun ω : Ω => SR.sample ω k r) := by
      have hbatch : Measurable (fun ω : Ω => SR.sample ω k) :=
        SR.sample_batch_measurable k
      have hcoord :
          Measurable
            (fun sample : Setup.MiniBatch (ι := ι) SR.Q SR.batchSize => sample r) := by
        fun_prop
      exact hcoord.comp hbatch
    let Y : Ω → (Ambient d × Ambient d) × DistributionSupport SR.Q :=
      fun ω => ((xCurr ω, xPrev ω), SR.sample ω k r)
    have hY_meas : Measurable Y :=
      (hxCurr_meas.prodMk hxPrev_meas).prodMk hsample_meas
    have hY_fin : (Set.range Y).Finite := by
      have hxCurr_fin : (Set.range xCurr).Finite := by
        refine ((iterate_measurable_finite_range SR k).2.image Subtype.val).subset ?_
        intro z hz
        rcases hz with ⟨omega0, rfl⟩
        exact ⟨Run.iterate (pathRun SR omega0) k, ⟨omega0, rfl⟩, rfl⟩
      have hxPrev_fin : (Set.range xPrev).Finite := by
        refine ((iterate_measurable_finite_range SR (k - 1)).2.image Subtype.val).subset ?_
        intro z hz
        rcases hz with ⟨omega0, rfl⟩
        exact ⟨Run.iterate (pathRun SR omega0) (k - 1), ⟨omega0, rfl⟩, rfl⟩
      have hsample_fin : (Set.range fun ω : Ω => SR.sample ω k r).Finite := by
        haveI : Finite (DistributionSupport SR.Q) := inferInstance
        exact Set.toFinite _
      refine Set.Finite.subset ((hxCurr_fin.prod hxPrev_fin).prod hsample_fin) ?_
      intro z hz
      rcases hz with ⟨omega0, rfl⟩
      constructor
      · constructor
        · exact ⟨omega0, rfl⟩
        · exact ⟨omega0, rfl⟩
      · exact ⟨omega0, rfl⟩
    have hmeas : Measurable (eps r) := by
      refine measurable_of_finite_range_fiber_const hY_meas hY_fin ?_
      intro ω ω' hY
      have hx_curr : xCurr ω = xCurr ω' := congrArg (fun z => z.1.1) hY
      have hx_prev : xPrev ω = xPrev ω' := congrArg (fun z => z.1.2) hY
      have hsamp : SR.sample ω k r = SR.sample ω' k r := congrArg Prod.snd hY
      dsimp [eps, targetDiff]
      rw [hx_curr, hx_prev, hsamp]
    exact hmeas.aestronglyMeasurable
  have heps_diag :
      ∀ r ∈ (Finset.univ : Finset (Fin SR.batchSize)),
        Integrable (fun ω => ‖eps r ω‖ ^ 2) SR.P ∧
          ∫ ω, ‖eps r ω‖ ^ 2 ∂SR.P ≤
            S.L ^ 2 * ∫ ω, ‖xCurr ω - xPrev ω‖ ^ 2 ∂SR.P := by
    intro r _hr
    let A : Type := Feasible S × Feasible S × Ambient d
    let W : Ω → A := oneStepVarianceQueryKey SR k
    let Y : Ω → ι := fun ω => (SR.sample ω k r).1
    let ν : Measure ι := (Setup.importancePMF S).toMeasure
    let w : ι → ℝ := fun i => probabilityMass (Setup.importancePMF S) i
    let F : A → ι → ℝ := fun z i =>
      ‖SOptLib.importance_weighted_gradient_difference w (Fintype.card ι : ℝ)
          (Setup.componentGradient S) (z.1 : Feasible S).1 (z.2.1 : Feasible S).1 i -
        (Setup.fullGradient S (z.1 : Feasible S).1 -
          Setup.fullGradient S (z.2.1 : Feasible S).1)‖ ^ 2
    let bound : Ω → ℝ := fun ω => S.L ^ 2 * ‖xCurr ω - xPrev ω‖ ^ 2
    have hW_mf := oneStepVarianceQueryKey_measurable_finite_range SR k hk_two
    have hW_aemeas : AEMeasurable W SR.P := by
      simpa [W] using hW_mf.1.aemeasurable
    have hY_meas : Measurable Y := by
      have hsample_support_meas :
          Measurable (fun ω : Ω => SR.sample ω k r) := by
        have hbatch : Measurable (fun ω : Ω => SR.sample ω k) :=
          SR.sample_batch_measurable k
        have hcoord :
            Measurable
              (fun sample : Setup.MiniBatch (ι := ι) SR.Q SR.batchSize => sample r) := by
          fun_prop
        exact hcoord.comp hbatch
      simpa [Y] using measurable_subtype_coe.comp hsample_support_meas
    have hY_aemeas : AEMeasurable Y SR.P := hY_meas.aemeasurable
    have hmarg : Measure.map Y SR.P = ν := by
      simpa [Y, ν, hQ] using hsample_law k r
    have hnu_singleton : ∀ i : ι, ν.real ({i} : Set ι) = w i := by
      intro i
      dsimp [ν, w, probabilityMass]
      rw [measureReal_def]
      congr 1
      exact PMF.toMeasure_apply_singleton (Setup.importancePMF S) i
        (MeasurableSet.singleton i)
    have hF_int :
        Integrable (fun z : A × ι => F z.1 z.2) ((Measure.map W SR.P).prod ν) := by
      haveI : IsFiniteMeasure ν := by
        dsimp [ν]
        infer_instance
      exact
        integrable_prod_of_finite_left_map_fintype_right
          (W := W) hW_aemeas (by simpa [W] using hW_mf.2) ν F
    let weighted : A → ℝ := fun z =>
      Finset.univ.sum (fun i : ι => w i • F z i)
    have hweighted_map_int :
        Integrable weighted (Measure.map W SR.P) := by
      exact
        integrable_map_of_finite_range
          (W := W) hW_aemeas (by simpa [W] using hW_mf.2) weighted
    have hweighted_aestrong :
        AEStronglyMeasurable weighted (Measure.map W SR.P) :=
      hweighted_map_int.aestronglyMeasurable
    have hweighted_int :
        Integrable (fun ω : Ω => Finset.univ.sum (fun i : ι => w i • F (W ω) i))
          SR.P := by
      simpa [weighted] using
        (integrable_map_measure hweighted_map_int.aestronglyMeasurable hW_aemeas).mp
          hweighted_map_int
    have hdisp_int :
        Integrable (fun ω => ‖xCurr ω - xPrev ω‖ ^ 2) SR.P := by
      simpa [xCurr, xPrev, k] using
        (SOptLib.expectationWellDefined_iff_integrable
          (μ := SR.P)
          (Z := fun ω : Ω =>
            ‖(Run.iterate (pathRun SR ω) (epochIndex SR s j)).1 -
                (Run.iterate (pathRun SR ω) (epochIndex SR s j - 1)).1‖ ^ 2)).mp
          hdisp_wd
    have hbound_int : Integrable bound SR.P := by
      simpa [bound] using hdisp_int.const_mul (S.L ^ 2)
    have hpoint :
        ∀ᵐ ω ∂SR.P,
          Finset.univ.sum (fun i : ι => w i • F (W ω) i) ≤ bound ω := by
      refine Filter.Eventually.of_forall ?_
      intro ω
      simpa [W, F, w, bound, xCurr, xPrev, targetDiff, oneStepVarianceQueryKey] using
        himportance_centered_atom_bound ω
    have hle_raw :
        (∫ ω : Ω, F (W ω) (Y ω) ∂SR.P) ≤ ∫ ω : Ω, bound ω ∂SR.P := by
      exact
        integral_sample_le_integral_bound_of_indep_weighted_fiber_bound
          (P := SR.P) (W := W) (Y := Y) ν w F bound
          hW_aemeas hY_aemeas (hstrict_past_freshness r).1 hmarg
          hnu_singleton hF_int hweighted_aestrong hweighted_int hbound_int hpoint
    have hjoint :
        Measure.map (fun ω : Ω => (W ω, Y ω)) SR.P =
          (Measure.map W SR.P).prod ν := by
      have hprod :=
        ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
          hW_aemeas hY_aemeas
      simpa [hmarg] using hprod.mp (hstrict_past_freshness r).1
    have hFY_int :
        Integrable (fun ω : Ω => F (W ω) (Y ω)) SR.P := by
      let Z : Ω → A × ι := fun ω => (W ω, Y ω)
      have hZ_aemeas : AEMeasurable Z SR.P := hW_aemeas.prodMk hY_aemeas
      have hF_aestrong :
          AEStronglyMeasurable (fun z : A × ι => F z.1 z.2) (Measure.map Z SR.P) := by
        rw [hjoint]
        exact hF_int.aestronglyMeasurable
      have h_on_map :
          Integrable (fun z : A × ι => F z.1 z.2) (Measure.map Z SR.P) := by
        rwa [hjoint]
      simpa [Z] using
        (integrable_map_measure hF_aestrong hZ_aemeas).mp h_on_map
    have hsample_eq :
        (fun ω : Ω => F (W ω) (Y ω)) = fun ω => ‖eps r ω‖ ^ 2 := by
      funext ω
      simp [F, W, Y, eps, targetDiff, xCurr, xPrev,
        oneStepVarianceQueryKey, importanceWeightedGradientDifference, hQ, w]
    refine ⟨?_, ?_⟩
    · simpa [← hsample_eq] using hFY_int
    · calc
        ∫ ω, ‖eps r ω‖ ^ 2 ∂SR.P
            = ∫ ω, F (W ω) (Y ω) ∂SR.P := by
              rw [hsample_eq]
        _ ≤ ∫ ω, bound ω ∂SR.P := hle_raw
        _ = S.L ^ 2 * ∫ ω, ‖xCurr ω - xPrev ω‖ ^ 2 ∂SR.P := by
              simp [bound, integral_const_mul]
  have heps_cross :
      ∀ r ∈ (Finset.univ : Finset (Fin SR.batchSize)),
        ∀ q ∈ (Finset.univ : Finset (Fin SR.batchSize)), r ≠ q →
          ∫ ω, ⟪eps r ω, eps q ω⟫_ℝ ∂SR.P = 0 := by
    intro r _hr q _hq hrq
    let A : Type _ := (Feasible S × Feasible S × Ambient d) × ι
    let W : Ω → A :=
      fun ω => (oneStepVarianceQueryKey SR k ω, (SR.sample ω k q).1)
    let Y : Ω → ι := fun ω => (SR.sample ω k r).1
    let ν : Measure ι := (Setup.importancePMF S).toMeasure
    let w : ι → ℝ := fun i => probabilityMass (Setup.importancePMF S) i
    let atom : (Feasible S × Feasible S × Ambient d) → ι → Ambient d :=
      fun z i =>
        SOptLib.importance_weighted_gradient_difference w (Fintype.card ι : ℝ)
          (Setup.componentGradient S) (z.1 : Feasible S).1 (z.2.1 : Feasible S).1 i -
          (Setup.fullGradient S (z.1 : Feasible S).1 -
            Setup.fullGradient S (z.2.1 : Feasible S).1)
    let F : A → ι → ℝ := fun z i => ⟪atom z.1 i, atom z.1 z.2⟫_ℝ
    have hWkey_mf := oneStepVarianceQueryKey_measurable_finite_range SR k hk_two
    have hpeer_meas : Measurable (fun ω : Ω => (SR.sample ω k q).1) := by
      have hsample_support_meas :
          Measurable (fun ω : Ω => SR.sample ω k q) := by
        have hbatch : Measurable (fun ω : Ω => SR.sample ω k) :=
          SR.sample_batch_measurable k
        have hcoord :
            Measurable
              (fun sample : Setup.MiniBatch (ι := ι) SR.Q SR.batchSize => sample q) := by
          fun_prop
        exact hcoord.comp hbatch
      simpa using measurable_subtype_coe.comp hsample_support_meas
    have hW_meas : Measurable W := by
      simpa [W] using hWkey_mf.1.prodMk hpeer_meas
    have hW_aemeas : AEMeasurable W SR.P := hW_meas.aemeasurable
    have hW_fin : (Set.range W).Finite := by
      have hpeer_fin : (Set.range fun ω : Ω => (SR.sample ω k q).1).Finite :=
        Set.toFinite _
      refine (hWkey_mf.2.prod hpeer_fin).subset ?_
      intro z hz
      rcases hz with ⟨ω, rfl⟩
      exact ⟨⟨ω, rfl⟩, ⟨ω, rfl⟩⟩
    have hY_meas : Measurable Y := by
      have hsample_support_meas :
          Measurable (fun ω : Ω => SR.sample ω k r) := by
        have hbatch : Measurable (fun ω : Ω => SR.sample ω k) :=
          SR.sample_batch_measurable k
        have hcoord :
            Measurable
              (fun sample : Setup.MiniBatch (ι := ι) SR.Q SR.batchSize => sample r) := by
          fun_prop
        exact hcoord.comp hbatch
      simpa [Y] using measurable_subtype_coe.comp hsample_support_meas
    have hY_aemeas : AEMeasurable Y SR.P := hY_meas.aemeasurable
    have hmarg : Measure.map Y SR.P = ν := by
      simpa [Y, ν, hQ] using hsample_law k r
    have hnu_singleton : ∀ i : ι, ν.real ({i} : Set ι) = w i := by
      intro i
      dsimp [ν, w, probabilityMass]
      rw [measureReal_def]
      congr 1
      exact PMF.toMeasure_apply_singleton (Setup.importancePMF S) i
        (MeasurableSet.singleton i)
    have hF_int :
        Integrable (fun z : A × ι => F z.1 z.2) ((Measure.map W SR.P).prod ν) := by
      haveI : IsFiniteMeasure ν := by
        dsimp [ν]
        infer_instance
      exact
        integrable_prod_of_finite_left_map_fintype_right
          (W := W) hW_aemeas hW_fin ν F
    have hfiber_zero :
        ∀ z : A, Finset.univ.sum (fun i : ι => w i • F z i) = 0 := by
      intro z
      have hvec :
          Finset.sum Finset.univ (fun i : ι => w i • atom z.1 i) = 0 := by
        simpa [atom, w] using
          importance_weighted_centered_atom_weighted_sum_eq_zero (S := S)
            (z.1.1 : Feasible S) (z.1.2.1 : Feasible S)
      have hinner :=
        Finset.weighted_inner_sum_eq_zero_of_weighted_sum_eq_zero
          (s := (Finset.univ : Finset ι)) (q := w)
          (R := fun i : ι => atom z.1 i) (u := atom z.1 z.2) hvec
      simpa [F] using hinner
    have htransport :
        (∫ ω : Ω, F (W ω) (Y ω) ∂SR.P) =
          ∫ ω : Ω, Finset.univ.sum (fun i : ι => w i • F (W ω) i) ∂SR.P :=
      expectation_sample_eq_expectation_weighted_fiber_sum_of_indepFun
        (P := SR.P) (W := W) (Y := Y) ν w F
        hW_aemeas hY_aemeas
        ((hstrict_past_freshness r).2 q (by exact fun hqr => hrq hqr.symm))
        hmarg hnu_singleton hF_int
    calc
      ∫ ω, ⟪eps r ω, eps q ω⟫_ℝ ∂SR.P
          = ∫ ω : Ω, F (W ω) (Y ω) ∂SR.P := by
              refine integral_congr_ae (Filter.Eventually.of_forall ?_)
              intro ω
              simp [F, W, Y, atom, eps, targetDiff, xCurr, xPrev,
                oneStepVarianceQueryKey, importanceWeightedGradientDifference, hQ, w]
      _ = ∫ ω : Ω, Finset.univ.sum (fun i : ι => w i • F (W ω) i) ∂SR.P :=
              htransport
      _ = 0 := by
              calc
                ∫ ω : Ω, Finset.univ.sum (fun i : ι => w i • F (W ω) i) ∂SR.P
                    = ∫ _ω : Ω, (0 : ℝ) ∂SR.P := by
                        refine integral_congr_ae (Filter.Eventually.of_forall ?_)
                        intro ω
                        simpa [smul_eq_mul] using hfiber_zero (W ω)
                _ = 0 := by simp
  have hprev_increment_cross :
      ∫ ω, ⟪deltaPrev ω, inc ω⟫_ℝ ∂SR.P = 0 := by
    have hprev_eps_cross :
        ∀ r ∈ (Finset.univ : Finset (Fin SR.batchSize)),
          ∫ ω, ⟪deltaPrev ω, eps r ω⟫_ℝ ∂SR.P = 0 := by
      intro r _hr
      let A : Type := Feasible S × Feasible S × Ambient d
      let W : Ω → A := oneStepVarianceQueryKey SR k
      let Y : Ω → ι := fun ω => (SR.sample ω k r).1
      let ν : Measure ι := (Setup.importancePMF S).toMeasure
      let w : ι → ℝ := fun i => probabilityMass (Setup.importancePMF S) i
      let atom : A → ι → Ambient d :=
        fun z i =>
          SOptLib.importance_weighted_gradient_difference w (Fintype.card ι : ℝ)
            (Setup.componentGradient S) (z.1 : Feasible S).1 (z.2.1 : Feasible S).1 i -
            (Setup.fullGradient S (z.1 : Feasible S).1 -
              Setup.fullGradient S (z.2.1 : Feasible S).1)
      let F : A → ι → ℝ := fun z i => ⟪z.2.2, atom z i⟫_ℝ
      have hW_mf := oneStepVarianceQueryKey_measurable_finite_range SR k hk_two
      have hW_aemeas : AEMeasurable W SR.P := by
        simpa [W] using hW_mf.1.aemeasurable
      have hY_meas : Measurable Y := by
        have hsample_support_meas :
            Measurable (fun ω : Ω => SR.sample ω k r) := by
          have hbatch : Measurable (fun ω : Ω => SR.sample ω k) :=
            SR.sample_batch_measurable k
          have hcoord :
              Measurable
                (fun sample : Setup.MiniBatch (ι := ι) SR.Q SR.batchSize => sample r) := by
            fun_prop
          exact hcoord.comp hbatch
        simpa [Y] using measurable_subtype_coe.comp hsample_support_meas
      have hY_aemeas : AEMeasurable Y SR.P := hY_meas.aemeasurable
      have hmarg : Measure.map Y SR.P = ν := by
        simpa [Y, ν, hQ] using hsample_law k r
      have hnu_singleton : ∀ i : ι, ν.real ({i} : Set ι) = w i := by
        intro i
        dsimp [ν, w, probabilityMass]
        rw [measureReal_def]
        congr 1
        exact PMF.toMeasure_apply_singleton (Setup.importancePMF S) i
          (MeasurableSet.singleton i)
      have hF_int :
          Integrable (fun z : A × ι => F z.1 z.2) ((Measure.map W SR.P).prod ν) := by
        haveI : IsFiniteMeasure ν := by
          dsimp [ν]
          infer_instance
        exact
          integrable_prod_of_finite_left_map_fintype_right
            (W := W) hW_aemeas (by simpa [W] using hW_mf.2) ν F
      have hfiber_zero :
          ∀ z : A, Finset.univ.sum (fun i : ι => w i • F z i) = 0 := by
        intro z
        have hvec :
            Finset.sum Finset.univ (fun i : ι => w i • atom z i) = 0 := by
          simpa [atom, w] using
            importance_weighted_centered_atom_weighted_sum_eq_zero (S := S)
              (z.1 : Feasible S) (z.2.1 : Feasible S)
        have hinner :=
          Finset.weighted_inner_sum_eq_zero_of_weighted_sum_eq_zero
            (s := (Finset.univ : Finset ι)) (q := w)
            (R := fun i : ι => atom z i) (u := z.2.2) hvec
        simpa [F, real_inner_comm] using hinner
      have htransport :
          (∫ ω : Ω, F (W ω) (Y ω) ∂SR.P) =
            ∫ ω : Ω, Finset.univ.sum (fun i : ι => w i • F (W ω) i) ∂SR.P :=
        expectation_sample_eq_expectation_weighted_fiber_sum_of_indepFun
          (P := SR.P) (W := W) (Y := Y) ν w F
          hW_aemeas hY_aemeas (hstrict_past_freshness r).1
          hmarg hnu_singleton hF_int
      calc
        ∫ ω, ⟪deltaPrev ω, eps r ω⟫_ℝ ∂SR.P
            = ∫ ω : Ω, F (W ω) (Y ω) ∂SR.P := by
                refine integral_congr_ae (Filter.Eventually.of_forall ?_)
                intro ω
                simp [F, W, Y, atom, eps, deltaPrev, targetDiff, xCurr, xPrev,
                  oneStepVarianceQueryKey, importanceWeightedGradientDifference, hQ, w]
        _ = ∫ ω : Ω, Finset.univ.sum (fun i : ι => w i • F (W ω) i) ∂SR.P :=
                htransport
        _ = 0 := by
                calc
                  ∫ ω : Ω, Finset.univ.sum (fun i : ι => w i • F (W ω) i) ∂SR.P
                      = ∫ _ω : Ω, (0 : ℝ) ∂SR.P := by
                          refine integral_congr_ae (Filter.Eventually.of_forall ?_)
                          intro ω
                          simpa [smul_eq_mul] using hfiber_zero (W ω)
                  _ = 0 := by simp
    have havg_cross :
        ∫ ω,
            ⟪deltaPrev ω,
              ((SR.batchSize : ℝ)⁻¹) •
                Finset.sum (Finset.univ : Finset (Fin SR.batchSize))
                  (fun r => eps r ω)⟫_ℝ ∂SR.P = 0 :=
      pastResidual_inner_centeredMiniBatchAverage_integral_eq_zero
        (P := SR.P) (I := (Finset.univ : Finset (Fin SR.batchSize)))
        (m := SR.batchSize) (d := deltaPrev) (eps := eps)
        hdeltaPrev_meas heps_meas hdeltaPrev_sq
        (fun r hr => (heps_diag r hr).1) hprev_eps_cross
    simpa [inc] using havg_cross
  have hsource_step :
      ∫ ω, ‖deltaNext ω‖ ^ 2 ∂SR.P ≤
        ∫ ω, ‖deltaPrev ω‖ ^ 2 ∂SR.P +
          (S.L ^ 2 / (SR.batchSize : ℝ)) *
            ∫ ω, ‖xCurr ω - xPrev ω‖ ^ 2 ∂SR.P := by
    exact
      recursiveEstimatorResidual_secondMoment_step_le_of_centered_minibatch
        (μ := SR.P) (I := (Finset.univ : Finset (Fin SR.batchSize)))
        (b := SR.batchSize)
        (deltaPrev := deltaPrev) (deltaNext := deltaNext) (inc := inc)
        (eps := eps) (xPrev := xPrev) (xCurr := xCurr) (L := S.L)
        SR.batchSize_pos (by simp [Finset.card_univ])
        hdeltaPrev_meas heps_meas hdeltaPrev_sq heps_diag hinc_eq hrec
        heps_cross hprev_increment_cross
  have hidx_pred : epochIndex SR s j - 1 = epochIndex SR s (j - 1) := by
    unfold epochIndex
    omega
  simpa [expectedEstimatorErrorSq, expectedDisplacementSq, SOptLib.expectation,
    deltaPrev, deltaNext, xCurr, xPrev, k, hidx_pred] using hsource_step

/-- Compatibility wrapper for the previous private exact-decomposition leaf.

The source/public Lemma 6.10 route now consumes
`source_importance_minibatch_variance_step` directly; this declaration is kept
only to preserve the old private theorem name for local audits. -/
private theorem lemma_6_10_one_step_expected_estimator_error
    (hQ : SR.Q = Setup.importancePMF S)
    (hsample_law :
      ∀ k : ℕ, ∀ r : Fin SR.batchSize,
        Measure.map (fun ω : Ω => (SR.sample ω k r).1) SR.P = SR.Q.toMeasure)
    (hsample_iIndep :
      ProbabilityTheory.iIndepFun
        (fun kr : ℕ × Fin SR.batchSize => fun ω : Ω => (SR.sample ω kr.1 kr.2).1)
        SR.P)
    (s j : ℕ) (hj_two : 2 ≤ j) (hj_epoch : j ≤ SR.T) :
    expectedEstimatorErrorSq SR (epochIndex SR s j) ≤
      expectedEstimatorErrorSq SR (epochIndex SR s (j - 1)) +
        (S.L ^ 2 / (SR.batchSize : ℝ)) *
          expectedDisplacementSq SR (epochIndex SR s j) := by
  exact source_importance_minibatch_variance_step SR
    hQ hsample_law hsample_iIndep s j hj_two hj_epoch

/-- Product-law integrability of the selected squared certificate follows from
fiber integrability over every selected output time, plus the explicit product
a.e.-strong-measurability obligation for the generated process. -/
theorem expectedOutputExactGradientMappingSq_wellDefined_of_fibers
    (hprod_aesm :
      AEStronglyMeasurable
        (fun q : OutputIndex SR.horizon × Ω => ‖outputExactGradientMapping SR q‖ ^ 2)
        (outputJointMeasure SR)) :
    SOptLib.expectationWellDefined (outputJointMeasure SR)
      (fun q : OutputIndex SR.horizon × Ω => ‖outputExactGradientMapping SR q‖ ^ 2) := by
  classical
  letI : IsProbabilityMeasure SR.P := SR.P_isProbability
  haveI : SFinite SR.P := inferInstance
  rw [SOptLib.expectationWellDefined_iff_integrable]
  have hfiber :
      ∀ R : OutputIndex SR.horizon,
        Integrable
          (fun ω : Ω => ‖Run.exactGradientMapping (pathRun SR ω) R.1‖ ^ 2) SR.P := by
    intro R
    exact
      (SOptLib.expectationWellDefined_iff_integrable
        (μ := SR.P)
        (Z := fun ω : Ω => ‖Run.exactGradientMapping (pathRun SR ω) R.1‖ ^ 2)).mp
        (expectedExactGradientMappingSq_wellDefined SR R.1)
  have h :
      Integrable
        (fun q : OutputIndex SR.horizon × Ω =>
          ‖Run.exactGradientMapping (pathRun SR q.2) q.1.1‖ ^ 2)
        ((outputPMF SR).toMeasure.prod SR.P) := by
    exact
      PMF.integrable_prod_of_fiber_integrable
        (p := outputPMF SR) (μ := SR.P)
        (F := fun R (ω : Ω) => ‖Run.exactGradientMapping (pathRun SR ω) R.1‖ ^ 2)
        (by simpa [outputJointMeasure, SOptLib.selected_joint_measure,
          outputExactGradientMapping] using hprod_aesm)
        hfiber
  simpa [outputJointMeasure, SOptLib.selected_joint_measure,
    outputExactGradientMapping] using h

/-- Well-definedness obligation for the randomized-output expectation
`E[‖g_{X,R}‖²]`. -/
theorem expectedOutputExactGradientMappingSq_wellDefined :
    SOptLib.expectationWellDefined (outputJointMeasure SR)
      (fun q : OutputIndex SR.horizon × Ω => ‖outputExactGradientMapping SR q‖ ^ 2) := by
  refine expectedOutputExactGradientMappingSq_wellDefined_of_fibers SR ?_
  classical
  let Y : OutputIndex SR.horizon × Ω → OutputIndex SR.horizon × (Feasible S × Ambient d) :=
    fun q => (q.1, statePair SR q.2 (q.1.1 - 1))
  have hY_meas : Measurable Y := by
    have hstate : Measurable (fun q : OutputIndex SR.horizon × Ω =>
        statePair SR q.2 (q.1.1 - 1)) := by
      let idx : OutputIndex SR.horizon × Ω → OutputIndex SR.horizon := fun q => q.1
      let f : OutputIndex SR.horizon → OutputIndex SR.horizon × Ω →
          Feasible S × Ambient d :=
        fun R q => statePair SR q.2 (R.1 - 1)
      have hidx : Measurable idx := by
        simpa [idx] using
          (measurable_fst : Measurable (fun q : OutputIndex SR.horizon × Ω => q.1))
      have hf : ∀ R : OutputIndex SR.horizon, Measurable (f R) := by
        intro R
        have hfix : Measurable (fun ω : Ω => statePair SR ω (R.1 - 1)) :=
          (statePair_measurable_finite_range SR (R.1 - 1) (R.1 - 1) le_rfl).1
        simpa [f] using hfix.comp
          (measurable_snd : Measurable (fun q : OutputIndex SR.horizon × Ω => q.2))
      simpa [idx, f] using
        (measurable_countable_dispatch (idx := idx) (f := f) hidx hf)
    exact measurable_fst.prodMk hstate
  have hY_fin : (Set.range Y).Finite := by
    have hfiber : ∀ R : OutputIndex SR.horizon,
        (Set.range (fun ω : Ω => (R, statePair SR ω (R.1 - 1)))).Finite := by
      intro R
      have hfin := (statePair_measurable_finite_range SR (R.1 - 1) (R.1 - 1) le_rfl).2
      exact (hfin.image (fun z => (R, z))).subset (by
        rintro y ⟨ω, rfl⟩
        exact ⟨statePair SR ω (R.1 - 1), ⟨ω, rfl⟩, rfl⟩)
    have hUnion :
        (⋃ R : OutputIndex SR.horizon,
          Set.range (fun ω : Ω => (R, statePair SR ω (R.1 - 1)))).Finite := by
      exact Set.finite_iUnion hfiber
    refine hUnion.subset ?_
    rintro y ⟨q, rfl⟩
    exact Set.mem_iUnion.mpr ⟨q.1, ⟨q.2, by simp [Y]⟩⟩
  have hconst : ∀ q q', Y q = Y q' →
      ‖outputExactGradientMapping SR q‖ ^ 2 = ‖outputExactGradientMapping SR q'‖ ^ 2 := by
    intro q q' hkey
    have hpair : statePair SR q.2 (q.1.1 - 1) =
        statePair SR q'.2 (q'.1.1 - 1) := by
      simpa [Y] using congrArg Prod.snd hkey
    have hiter : Run.iterate (pathRun SR q.2) q.1.1 =
        Run.iterate (pathRun SR q'.2) q'.1.1 := by
      simpa [statePair, Run.iterate] using congrArg Prod.fst hpair
    have hmap : outputExactGradientMapping SR q = outputExactGradientMapping SR q' := by
      change Run.exactGradientMapping (pathRun SR q.2) q.1.1 =
        Run.exactGradientMapping (pathRun SR q'.2) q'.1.1
      unfold Run.exactGradientMapping
      rw [hiter]
      simp [pathRun]
    exact congrArg (fun v : Ambient d => ‖v‖ ^ 2) hmap
  have hmeas : Measurable
      (fun q : OutputIndex SR.horizon × Ω => ‖outputExactGradientMapping SR q‖ ^ 2) := by
    exact measurable_of_finite_range_fiber_const hY_meas hY_fin hconst
  exact hmeas.aestronglyMeasurable

/-- The uniform selected-output expectation expands to the finite average of
per-iteration expectations over `{1,...,N}`.

This is the concrete consumer of the SOptLib finite-window selection API.  Its
integrability premise is discharged through
`expectedExactGradientMappingSq_wellDefined`, exposing the exact remaining
well-definedness leaf needed by the randomized-output proof. -/
theorem expectedOutputExactGradientMappingSq_eq_uniform_sum :
    expectedOutputExactGradientMappingSq SR =
      (Finset.sum (outputWindow SR.horizon) (fun _ : ℕ => (1 : ℝ)))⁻¹ *
        Finset.sum (outputWindow SR.horizon)
          (fun k => (1 : ℝ) * expectedExactGradientMappingSq SR k) := by
  classical
  letI : IsProbabilityMeasure SR.P := SR.P_isProbability
  haveI : SFinite SR.P := inferInstance
  have hgap_int :
      ∀ R : {k : ℕ // k ∈ outputWindow SR.horizon},
        Integrable
          (fun ω : Ω => ‖Run.exactGradientMapping (pathRun SR ω) R.1‖ ^ 2) SR.P := by
    intro R
    exact
      (SOptLib.expectationWellDefined_iff_integrable
        (μ := SR.P)
        (Z := fun ω : Ω => ‖Run.exactGradientMapping (pathRun SR ω) R.1‖ ^ 2)).mp
        (expectedExactGradientMappingSq_wellDefined SR R.1)
  have h :=
    SOptLib.finiteWindowSelectedOutputExpectation_eq_weighted_sum
      (times := outputWindow SR.horizon)
      (α := fun _ : ℕ => (1 : ℝ))
      (P := SR.P)
      (x := fun k (ω : Ω) => Run.exactGradientMapping (pathRun SR ω) k)
      (gap := fun g : Ambient d => ‖g‖ ^ 2)
      (SOptLib.FiniteWindowWeightsAdmissible.nonneg
        (outputWindowWeightsAdmissible SR.horizon SR.horizon_pos))
      (SOptLib.FiniteWindowWeightsAdmissible.sum_pos
        (outputWindowWeightsAdmissible SR.horizon SR.horizon_pos))
      hgap_int
  simpa [expectedOutputExactGradientMappingSq, expectedExactGradientMappingSq,
    outputExactGradientMapping, outputJointMeasure, outputPMF, uniformOutputPMF,
    SOptLib.uniformFiniteWindowPMF, SOptLib.selected_joint_measure, SOptLib.expectation] using h

/-- Lemma 6.10 / Eq. (6.5.5), stated at the stochastic generated-process boundary.

This is the source-granularity variance bridge for Theorem 6.14.  Its explicit
inputs are exactly the existing Algorithm 6.6 stochastic facts: the smoothness
importance law `hQ`, the mini-batch coordinate laws, and i.i.d. sampling. -/
theorem lemma_6_10_epochwise_estimator_variance_bound
    (hQ : SR.Q = Setup.importancePMF S)
    (hsample_law :
      ∀ k : ℕ, ∀ r : Fin SR.batchSize,
        Measure.map (fun ω : Ω => (SR.sample ω k r).1) SR.P = SR.Q.toMeasure)
    (hsample_iIndep :
      ProbabilityTheory.iIndepFun
        (fun kr : ℕ × Fin SR.batchSize => fun ω : Ω => (SR.sample ω kr.1 kr.2).1)
        SR.P)
    (s t : ℕ) (ht_pos : 1 ≤ t) (ht_epoch : t ≤ SR.T) :
    expectedEstimatorErrorSq SR (epochIndex SR s t) ≤
      (S.L ^ 2 / (SR.batchSize : ℝ)) *
        Finset.sum (Finset.Icc 2 t)
          (fun i => expectedDisplacementSq SR (epochIndex SR s i)) := by
  classical
  letI : IsProbabilityMeasure SR.P := SR.P_isProbability
  have hQ_atom_pos : ∀ i : ι, 0 < (Setup.importancePMF S i).toReal :=
    Setup.importancePMF_atom_toReal_pos S
  have hsamples_law := hsample_law
  have hsamples_iIndep := hsample_iIndep
  have hdelta_wd := expectedEstimatorErrorSq_wellDefined SR (epochIndex SR s t)
  have hdisp_wd :
      ∀ i ∈ Finset.Icc 2 t,
        SOptLib.expectationWellDefined SR.P
          (fun ω : Ω =>
            ‖(Run.iterate (pathRun SR ω) (epochIndex SR s i)).1 -
                (Run.iterate (pathRun SR ω) (epochIndex SR s i - 1)).1‖ ^ 2) := by
    intro i hi
    exact expectedDisplacementSq_wellDefined SR (epochIndex SR s i)
  let delta : ℕ → Ω → Ambient d :=
    fun k ω => Run.estimatorError (pathRun SR ω) k
  let x : ℕ → Ω → Ambient d :=
    fun k ω => (Run.iterate (pathRun SR ω) k).1
  let Valid : ℕ → ℕ → Prop := fun s _ => s = s
  have hvalid_prefix :
      ∀ {s i j : ℕ}, i ≤ j → Valid s j → Valid s i := by
    intro s i j hij hj
    exact rfl
  have hbase :
      ∀ s : ℕ, Valid s 1 →
        ∫ ω, ‖delta (epochIndex SR s 1) ω‖ ^ 2 ∂SR.P ≤
          (S.L ^ 2 / (SR.batchSize : ℝ)) *
            ∫ ω, SOptLib.epochSquaredDifferenceSum x (epochIndex SR) s 1 ω ∂SR.P := by
    intro s _hs
    have hzero :
        (fun ω : Ω => ‖delta (epochIndex SR s 1) ω‖ ^ 2) = fun _ => 0 := by
      funext ω
      rw [show delta (epochIndex SR s 1) ω = 0 from
        epochIndex_estimatorError_base_zero SR s ω]
      simp
    simp [hzero, SOptLib.epochSquaredDifferenceSum]
  have hdelta_sq_int :
      ∀ s j : ℕ, 1 ≤ j → j ≤ SR.T → Valid s j →
        Integrable (fun ω => ‖delta (epochIndex SR s j) ω‖ ^ 2) SR.P := by
    intro s j _hj_pos _hj_T _hvalid
    exact
      (SOptLib.expectationWellDefined_iff_integrable
        (μ := SR.P)
        (Z := fun ω : Ω => ‖Run.estimatorError (pathRun SR ω) (epochIndex SR s j)‖ ^ 2)).mp
        (expectedEstimatorErrorSq_wellDefined SR (epochIndex SR s j))
  have hdiff_sq_int :
      ∀ s i : ℕ, 2 ≤ i → i ≤ SR.T → Valid s i →
        Integrable
          (fun ω => ‖x (epochIndex SR s i) ω - x (epochIndex SR s (i - 1)) ω‖ ^ 2)
          SR.P := by
    intro s i _hi_two _hi_T _hvalid
    have hidx_pred : epochIndex SR s i - 1 = epochIndex SR s (i - 1) := by
      unfold epochIndex
      omega
    exact
      (SOptLib.expectationWellDefined_iff_integrable
        (μ := SR.P)
        (Z := fun ω : Ω =>
          ‖(Run.iterate (pathRun SR ω) (epochIndex SR s i)).1 -
              (Run.iterate (pathRun SR ω) (epochIndex SR s (i - 1))).1‖ ^ 2)).mp
        (by simpa [hidx_pred] using
          expectedDisplacementSq_wellDefined SR (epochIndex SR s i))
  have hstep :
      ∀ s j : ℕ, 2 ≤ j → j ≤ SR.T → Valid s j →
        Integrable (fun ω => ‖delta (epochIndex SR s (j - 1)) ω‖ ^ 2) SR.P →
        ∫ ω, ‖delta (epochIndex SR s j) ω‖ ^ 2 ∂SR.P ≤
          ∫ ω, ‖delta (epochIndex SR s (j - 1)) ω‖ ^ 2 ∂SR.P +
            (S.L ^ 2 / (SR.batchSize : ℝ)) *
              ∫ ω, ‖x (epochIndex SR s j) ω - x (epochIndex SR s (j - 1)) ω‖ ^ 2 ∂SR.P := by
    intro s j hj_two hj_T _hvalid _hprev_int
    have hidx_pred : epochIndex SR s j - 1 = epochIndex SR s (j - 1) := by
      unfold epochIndex
      omega
    simpa [expectedEstimatorErrorSq, expectedDisplacementSq, SOptLib.expectation,
      delta, x, hidx_pred] using
      source_importance_minibatch_variance_step SR
        hQ hsamples_law hsamples_iIndep s j hj_two hj_T
  have haccum :
      ∫ ω, ‖delta (epochIndex SR s t) ω‖ ^ 2 ∂SR.P ≤
        (S.L ^ 2 / (SR.batchSize : ℝ)) *
          ∫ ω, SOptLib.epochSquaredDifferenceSum x (epochIndex SR) s t ω ∂SR.P :=
    epoch_recursive_estimator_second_moment_le_difference_sum
      (μ := SR.P) (delta := delta) (x := x) (index := epochIndex SR)
      (Valid := Valid) (T := SR.T) (c := S.L ^ 2 / (SR.batchSize : ℝ))
      hvalid_prefix hbase hdelta_sq_int hdiff_sq_int hstep s t ht_pos ht_epoch
      rfl
  have hsum_integral :
      ∫ ω, SOptLib.epochSquaredDifferenceSum x (epochIndex SR) s t ω ∂SR.P =
        Finset.sum (Finset.Icc 2 t)
          (fun i => expectedDisplacementSq SR (epochIndex SR s i)) := by
    unfold SOptLib.epochSquaredDifferenceSum expectedDisplacementSq SOptLib.expectation
    rw [integral_finset_sum]
    · refine Finset.sum_congr rfl ?_
      intro i hi
      have hi_two : 2 ≤ i := (Finset.mem_Icc.mp hi).1
      have hidx_pred : epochIndex SR s i - 1 = epochIndex SR s (i - 1) := by
        unfold epochIndex
        omega
      simp [x, hidx_pred]
    · intro i hi
      have hi_two : 2 ≤ i := (Finset.mem_Icc.mp hi).1
      have hidx_pred : epochIndex SR s i - 1 = epochIndex SR s (i - 1) := by
        unfold epochIndex
        omega
      exact
        (SOptLib.expectationWellDefined_iff_integrable
          (μ := SR.P)
          (Z := fun ω : Ω =>
            ‖(Run.iterate (pathRun SR ω) (epochIndex SR s i)).1 -
                (Run.iterate (pathRun SR ω) (epochIndex SR s (i - 1))).1‖ ^ 2)).mp
          (by simpa [hidx_pred] using hdisp_wd i hi)
  have haccum' := haccum
  rw [hsum_integral] at haccum'
  simpa [expectedEstimatorErrorSq, SOptLib.expectation, delta] using haccum'

/-- Raw smooth/prox descent before applying Young's inequality to the estimator
residual.

SOptLib's exported descent theorem packages the subsequent Young absorption.
Theorem 6.14 also needs this pre-Young form so the exact-gradient certificate
can share the same scalar budget as the residual inner product. -/
private theorem smooth_descent_of_approx_variational_step_with_estimator_error_raw
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (grad : E → E) (x y G : E) (gamma eta L : ℝ)
    (hsmooth :
      f y ≤ f x + ⟪grad x, y - x⟫_ℝ + (L / 2) * ‖y - x‖ ^ 2)
    (hproj :
      ⟪G, y - x⟫_ℝ ≤ eta - gamma⁻¹ * ‖y - x‖ ^ 2) :
    f y ≤
      f x - (gamma⁻¹ - L / 2) * ‖y - x‖ ^ 2 -
        ⟪G - grad x, y - x⟫_ℝ + eta := by
  exact
    _root_.smooth_descent_of_approx_variational_step_with_estimator_error_raw
      (f := f) (grad := grad) (x := x) (y := y) (G := G)
      (gamma := gamma) (eta := eta) (L := L) hsmooth hproj

/-- Scalar Young budget that justifies the printed one-step coefficient when the
exact-gradient certificate and estimator residual are absorbed together. -/
private theorem one_step_scalar_budget_with_perturbation
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {gamma p q : ℝ} (hgamma_pos : 0 < gamma) (hp : 0 < p) (hq : 0 < q)
    (hbudget : gamma + 4 * p ≤ 2 * p / q)
    {exact stoch delta : E}
    (hperturb : ‖exact - stoch‖ ≤ ‖delta‖) :
    p * ‖exact‖ ^ 2 + gamma * ⟪delta, stoch⟫_ℝ ≤
      2 * p * ‖stoch‖ ^ 2 + (gamma / (2 * q) + 2 * p) * ‖delta‖ ^ 2 := by
  exact norm_sq_add_inner_le_base_sq_add_err_sq_of_norm_sub_le_of_budget
    (gamma := gamma) (p := p) (q := q) (le_of_lt hgamma_pos) hp hq hbudget hperturb

/-- Theorem 6.14 one-step expected descent bridge, corresponding to Eq. (6.5.10)
plus the exact/stochastic projected-gradient perturbation split.

Eq. (6.5.10) contributes the `q / 2` loss in the stochastic-gradient
coefficient.  The next displayed source line omits that loss after adding the
exact-gradient certificate; this bridge keeps the Eq. (6.5.10) coefficient
visible instead of encoding the dropped term as a theorem-head assumption. -/
theorem theorem_6_14_one_step_expected_descent
    (hgamma : SR.gamma = 1 / S.L)
    (k : PositiveIteration) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    expectedPsi SR (k.1 + 1) + p * expectedExactGradientMappingSq SR k.1 ≤
      expectedPsi SR k.1 -
        (SR.gamma * (1 - S.L * SR.gamma / 2 - q / 2) - 2 * p) *
          expectedStochasticGradientMappingSq SR k.1 +
        (SR.gamma / (2 * q) + 2 * p) * expectedEstimatorErrorSq SR k.1 := by
  classical
  letI : IsProbabilityMeasure SR.P := SR.P_isProbability
  have hL_pos : 0 < S.L := Setup.L_pos S
  have hperturb :
      ∀ ω : Ω,
        ‖Run.exactGradientMapping (pathRun SR ω) k.1 -
            Run.stochasticGradientMapping (pathRun SR ω) k.1‖ ≤
          ‖Run.estimatorError (pathRun SR ω) k.1‖ := by
    intro ω
    exact Run.gradient_mapping_perturbation (pathRun SR ω) k
  have hexact_sq :
      ∀ ω : Ω,
        ‖Run.exactGradientMapping (pathRun SR ω) k.1‖ ^ 2 ≤
          2 * ‖Run.stochasticGradientMapping (pathRun SR ω) k.1‖ ^ 2 +
            2 * ‖Run.estimatorError (pathRun SR ω) k.1‖ ^ 2 := by
    intro ω
    exact Run.exact_gradient_mapping_sq_le_stochastic_sq_add_error_sq
      (pathRun SR ω) k
  have hpsi_next_wd := expectedPsi_wellDefined SR (k.1 + 1)
  have hpsi_cur_wd := expectedPsi_wellDefined SR k.1
  have hexact_wd := expectedExactGradientMappingSq_wellDefined SR k.1
  have hstoch_wd := expectedStochasticGradientMappingSq_wellDefined SR k.1
  have hdelta_wd := expectedEstimatorErrorSq_wellDefined SR k.1
  have hLavg :
      S.L = (Fintype.card ι : ℝ)⁻¹ *
        Finset.sum Finset.univ (fun i : ι => S.Lcomp i) := by
    simpa [finiteAverage, SOptLib.finiteUniformAverage, smul_eq_mul] using
      S.L_eq_average
  have hsmooth_path :
      ∀ ω : Ω,
        Setup.finiteSumObjective S (Run.iterate (pathRun SR ω) (k.1 + 1)).1 ≤
          Setup.finiteSumObjective S (Run.iterate (pathRun SR ω) k.1).1 +
            ⟪Setup.fullGradient S (Run.iterate (pathRun SR ω) k.1).1,
              (Run.iterate (pathRun SR ω) (k.1 + 1)).1 -
                (Run.iterate (pathRun SR ω) k.1).1⟫_ℝ +
            (S.L / 2) *
              ‖(Run.iterate (pathRun SR ω) (k.1 + 1)).1 -
                  (Run.iterate (pathRun SR ω) k.1).1‖ ^ 2 := by
    intro ω
    exact
      (by
        simpa [Setup.finiteSumObjective, Setup.fullGradient, Setup.componentGradient,
          finiteAverage] using
          SOptLib.finiteUniformAverage_smooth_quadratic_upper_bound_of_component_lipschitz
            (X := S.X) (F := S.component)
            (gradF := fun i : ι => Setup.componentGradient S i)
            (Lcomp := S.Lcomp) (L := S.L)
            S.convex_X hLavg
            (by
              intro i z hz
              simpa [Setup.componentGradient] using S.component_hasGradientAt i z hz)
            (by
              intro i z w hz hw
              simpa [Setup.componentGradient] using
                S.component_lipschitz_grad i z hz w hw)
            (x := (Run.iterate (pathRun SR ω) k.1).1)
            (y := (Run.iterate (pathRun SR ω) (k.1 + 1)).1)
            (Run.iterate (pathRun SR ω) k.1).2
            (Run.iterate (pathRun SR ω) (k.1 + 1)).2)
  have hprox_descent :
      ∀ ω : Ω,
        SR.gamma⁻¹ *
            ‖(Run.iterate (pathRun SR ω) k.1).1 -
                (Run.iterate (pathRun SR ω) (k.1 + 1)).1‖ ^ 2 +
            S.h (Run.iterate (pathRun SR ω) (k.1 + 1)).1 -
            S.h (Run.iterate (pathRun SR ω) k.1).1 ≤
          ⟪Run.estimator (pathRun SR ω) k.1,
            (Run.iterate (pathRun SR ω) k.1).1 -
              (Run.iterate (pathRun SR ω) (k.1 + 1)).1⟫_ℝ := by
    intro ω
    have hnext := Run.iterate_succ_eq_proxPoint (pathRun SR ω) k
    have hinner :=
      Run.proxPoint_descent_inner_bound (S := S)
        (Run.iterate (pathRun SR ω) k.1)
        (Run.estimator (pathRun SR ω) k.1)
        SR.gamma SR.gamma_pos
    simpa [hnext] using hinner
  have hq_over_gamma_pos : 0 < q / SR.gamma :=
    div_pos hq SR.gamma_pos
  have hpathwise_q_loss :
      ∀ ω : Ω,
        Setup.psi S (Run.iterate (pathRun SR ω) (k.1 + 1)).1 ≤
          Setup.psi S (Run.iterate (pathRun SR ω) k.1).1 -
            (SR.gamma * (1 - S.L * SR.gamma / 2 - q / 2)) *
              ‖Run.stochasticGradientMapping (pathRun SR ω) k.1‖ ^ 2 +
            (SR.gamma / (2 * q)) *
              ‖Run.estimatorError (pathRun SR ω) k.1‖ ^ 2 := by
    intro ω
    let Rω := pathRun SR ω
    let x : Feasible S := Run.iterate Rω k.1
    let y : Feasible S := Run.iterate Rω (k.1 + 1)
    let G : Ambient d := Run.estimator Rω k.1
    let stoch : Ambient d := Run.stochasticGradientMapping Rω k.1
    let delta : Ambient d := Run.estimatorError Rω k.1
    have hproj :
        ⟪G, y.1 - x.1⟫_ℝ ≤ S.h x.1 - S.h y.1 -
          SR.gamma⁻¹ * ‖y.1 - x.1‖ ^ 2 := by
      have hprox := hprox_descent ω
      have hinner_flip :
          ⟪G, y.1 - x.1⟫_ℝ = -⟪G, x.1 - y.1⟫_ℝ := by
        rw [← neg_sub x.1 y.1, inner_neg_right]
      have hnorm_flip : ‖x.1 - y.1‖ ^ 2 = ‖y.1 - x.1‖ ^ 2 := by
        rw [norm_sub_rev]
      dsimp [Rω, x, y, G] at hprox ⊢
      rw [hinner_flip, ← hnorm_flip]
      linarith
    have hf_descent :=
      smooth_descent_of_approx_variational_step_with_estimator_error
        (f := Setup.finiteSumObjective S)
        (grad := fun z : Ambient d => Setup.fullGradient S z)
        (x := x.1) (y := y.1) (G := G)
        (gamma := SR.gamma) (eta := S.h x.1 - S.h y.1)
        (L := S.L) (q := q / SR.gamma)
        hq_over_gamma_pos
        (by simpa [Rω, x, y] using hsmooth_path ω)
        hproj
    have hnext := Run.iterate_succ_eq_proxPoint Rω k
    have hstoch_def :
        stoch = SR.gamma⁻¹ • (x.1 - y.1) := by
      simpa [Rω, x, y, G, stoch, Run.stochasticGradientMapping,
        pathRun, Setup.stochasticProjectedGradient, Setup.projectedGradient_def, hnext]
    have hdelta_def :
        G - Setup.fullGradient S x.1 = delta := by
      rfl
    have hgamma_ne : SR.gamma ≠ 0 := ne_of_gt SR.gamma_pos
    have hgamma_smul_stoch : SR.gamma • stoch = x.1 - y.1 := by
      rw [hstoch_def, smul_smul, mul_inv_cancel₀ hgamma_ne, one_smul]
    have hdisp : y.1 - x.1 = -(SR.gamma • stoch) := by
      calc
        y.1 - x.1 = -(x.1 - y.1) := by abel
        _ = -(SR.gamma • stoch) := by rw [← hgamma_smul_stoch]
    have hdist_sq :
        ‖y.1 - x.1‖ ^ 2 = SR.gamma ^ 2 * ‖stoch‖ ^ 2 := by
      rw [hdisp, norm_neg, norm_smul, Real.norm_of_nonneg (le_of_lt SR.gamma_pos)]
      ring
    have hcoeff_disp :
        (SR.gamma⁻¹ - S.L / 2 - q / SR.gamma / 2) * ‖y.1 - x.1‖ ^ 2 =
          (SR.gamma * (1 - S.L * SR.gamma / 2 - q / 2)) *
            ‖stoch‖ ^ 2 := by
      rw [hdist_sq]
      field_simp [hgamma_ne]
    have hcoeff_err :
        1 / (2 * (q / SR.gamma)) *
            ‖G - (fun z : Ambient d => Setup.fullGradient S z) x.1‖ ^ 2 =
          (SR.gamma / (2 * q)) * ‖delta‖ ^ 2 := by
      rw [hdelta_def]
      field_simp [hgamma_ne, ne_of_gt hq]
    calc
      Setup.psi S y.1 =
          Setup.finiteSumObjective S y.1 + S.h y.1 := by
            simp [Setup.psi_def]
      _ ≤
          (Setup.finiteSumObjective S x.1 -
              (SR.gamma⁻¹ - S.L / 2 - q / SR.gamma / 2) *
                ‖y.1 - x.1‖ ^ 2 +
              1 / (2 * (q / SR.gamma)) *
                ‖G - (fun z : Ambient d => Setup.fullGradient S z) x.1‖ ^ 2 +
              (S.h x.1 - S.h y.1)) + S.h y.1 := by
            linarith
      _ =
          Setup.psi S x.1 -
            (SR.gamma * (1 - S.L * SR.gamma / 2 - q / 2)) * ‖stoch‖ ^ 2 +
            (SR.gamma / (2 * q)) * ‖delta‖ ^ 2 := by
            rw [Setup.psi_def, hcoeff_disp, hcoeff_err]
            ring
  -- Source route: finite-average smooth descent, estimator-error insertion,
  -- prox descent from Lemma 6.4, Young's inequality with `q`, and the
  -- squared perturbation inequality above with weight `p`; all expectations
  -- in this bridge are backed by the finite-range well-definedness facts above.
  have hpsi_next_int : Integrable
      (fun ω : Ω => Setup.psi S (Run.iterate (pathRun SR ω) (k.1 + 1)).1) SR.P :=
    (SOptLib.expectationWellDefined_iff_integrable
      (μ := SR.P)
      (Z := fun ω : Ω => Setup.psi S (Run.iterate (pathRun SR ω) (k.1 + 1)).1)).mp
      hpsi_next_wd
  have hpsi_cur_int : Integrable
      (fun ω : Ω => Setup.psi S (Run.iterate (pathRun SR ω) k.1).1) SR.P :=
    (SOptLib.expectationWellDefined_iff_integrable
      (μ := SR.P)
      (Z := fun ω : Ω => Setup.psi S (Run.iterate (pathRun SR ω) k.1).1)).mp
      hpsi_cur_wd
  have hexact_int : Integrable
      (fun ω : Ω => ‖Run.exactGradientMapping (pathRun SR ω) k.1‖ ^ 2) SR.P :=
    (SOptLib.expectationWellDefined_iff_integrable
      (μ := SR.P)
      (Z := fun ω : Ω => ‖Run.exactGradientMapping (pathRun SR ω) k.1‖ ^ 2)).mp
      hexact_wd
  have hstoch_int : Integrable
      (fun ω : Ω => ‖Run.stochasticGradientMapping (pathRun SR ω) k.1‖ ^ 2) SR.P :=
    (SOptLib.expectationWellDefined_iff_integrable
      (μ := SR.P)
      (Z := fun ω : Ω => ‖Run.stochasticGradientMapping (pathRun SR ω) k.1‖ ^ 2)).mp
      hstoch_wd
  have hdelta_int : Integrable
      (fun ω : Ω => ‖Run.estimatorError (pathRun SR ω) k.1‖ ^ 2) SR.P :=
    (SOptLib.expectationWellDefined_iff_integrable
      (μ := SR.P)
      (Z := fun ω : Ω => ‖Run.estimatorError (pathRun SR ω) k.1‖ ^ 2)).mp
      hdelta_wd
  have hpointwise :
      ∀ ω : Ω,
        Setup.psi S (Run.iterate (pathRun SR ω) (k.1 + 1)).1 +
            p * ‖Run.exactGradientMapping (pathRun SR ω) k.1‖ ^ 2 ≤
          Setup.psi S (Run.iterate (pathRun SR ω) k.1).1 -
            (SR.gamma * (1 - S.L * SR.gamma / 2 - q / 2) - 2 * p) *
              ‖Run.stochasticGradientMapping (pathRun SR ω) k.1‖ ^ 2 +
            (SR.gamma / (2 * q) + 2 * p) *
              ‖Run.estimatorError (pathRun SR ω) k.1‖ ^ 2 := by
    intro ω
    have hexact_mul :=
      mul_le_mul_of_nonneg_left (hexact_sq ω) (le_of_lt hp)
    have hpath := hpathwise_q_loss ω
    linarith
  let left : Ω → ℝ := fun ω =>
    Setup.psi S (Run.iterate (pathRun SR ω) (k.1 + 1)).1 +
      p * ‖Run.exactGradientMapping (pathRun SR ω) k.1‖ ^ 2
  let right : Ω → ℝ := fun ω =>
    Setup.psi S (Run.iterate (pathRun SR ω) k.1).1 -
      (SR.gamma * (1 - S.L * SR.gamma / 2 - q / 2) - 2 * p) *
        ‖Run.stochasticGradientMapping (pathRun SR ω) k.1‖ ^ 2 +
      (SR.gamma / (2 * q) + 2 * p) *
        ‖Run.estimatorError (pathRun SR ω) k.1‖ ^ 2
  have hleft_int : Integrable left SR.P :=
    hpsi_next_int.add (hexact_int.const_mul p)
  have hright_int : Integrable right SR.P :=
    (hpsi_cur_int.sub
        (hstoch_int.const_mul
          (SR.gamma * (1 - S.L * SR.gamma / 2 - q / 2) - 2 * p))).add
      (hdelta_int.const_mul (SR.gamma / (2 * q) + 2 * p))
  have hmono : ∫ ω, left ω ∂SR.P ≤ ∫ ω, right ω ∂SR.P := by
    exact MeasureTheory.integral_mono hleft_int hright_int hpointwise
  have hleft_eq :
      ∫ ω, left ω ∂SR.P =
        expectedPsi SR (k.1 + 1) + p * expectedExactGradientMappingSq SR k.1 := by
    dsimp [left]
    rw [MeasureTheory.integral_add hpsi_next_int (hexact_int.const_mul p)]
    simp [expectedPsi, expectedExactGradientMappingSq, SOptLib.expectation,
      MeasureTheory.integral_const_mul]
  have hright_eq :
      ∫ ω, right ω ∂SR.P =
        expectedPsi SR k.1 -
          (SR.gamma * (1 - S.L * SR.gamma / 2 - q / 2) - 2 * p) *
            expectedStochasticGradientMappingSq SR k.1 +
          (SR.gamma / (2 * q) + 2 * p) * expectedEstimatorErrorSq SR k.1 := by
    dsimp [right]
    calc
      ∫ ω : Ω,
          Setup.psi S (Run.iterate (pathRun SR ω) k.1).1 -
              (SR.gamma * (1 - S.L * SR.gamma / 2 - q / 2) - 2 * p) *
                ‖Run.stochasticGradientMapping (pathRun SR ω) k.1‖ ^ 2 +
            (SR.gamma / (2 * q) + 2 * p) *
              ‖Run.estimatorError (pathRun SR ω) k.1‖ ^ 2 ∂SR.P
          =
          ∫ ω : Ω,
            Setup.psi S (Run.iterate (pathRun SR ω) k.1).1 -
              (SR.gamma * (1 - S.L * SR.gamma / 2 - q / 2) - 2 * p) *
                ‖Run.stochasticGradientMapping (pathRun SR ω) k.1‖ ^ 2 ∂SR.P +
          ∫ ω : Ω,
            (SR.gamma / (2 * q) + 2 * p) *
              ‖Run.estimatorError (pathRun SR ω) k.1‖ ^ 2 ∂SR.P := by
            exact MeasureTheory.integral_add
              (f := fun ω : Ω =>
                Setup.psi S (Run.iterate (pathRun SR ω) k.1).1 -
                  (SR.gamma * (1 - S.L * SR.gamma / 2 - q / 2) - 2 * p) *
                    ‖Run.stochasticGradientMapping (pathRun SR ω) k.1‖ ^ 2)
              (g := fun ω : Ω =>
                (SR.gamma / (2 * q) + 2 * p) *
                  ‖Run.estimatorError (pathRun SR ω) k.1‖ ^ 2)
              (hpsi_cur_int.sub
                (hstoch_int.const_mul
                  (SR.gamma * (1 - S.L * SR.gamma / 2 - q / 2) - 2 * p)))
              (hdelta_int.const_mul (SR.gamma / (2 * q) + 2 * p))
      _ =
          (∫ ω : Ω, Setup.psi S (Run.iterate (pathRun SR ω) k.1).1 ∂SR.P -
            ∫ ω : Ω,
              (SR.gamma * (1 - S.L * SR.gamma / 2 - q / 2) - 2 * p) *
                ‖Run.stochasticGradientMapping (pathRun SR ω) k.1‖ ^ 2 ∂SR.P) +
          ∫ ω : Ω,
            (SR.gamma / (2 * q) + 2 * p) *
              ‖Run.estimatorError (pathRun SR ω) k.1‖ ^ 2 ∂SR.P := by
            rw [MeasureTheory.integral_sub
              (f := fun ω : Ω => Setup.psi S (Run.iterate (pathRun SR ω) k.1).1)
              (g := fun ω : Ω =>
                (SR.gamma * (1 - S.L * SR.gamma / 2 - q / 2) - 2 * p) *
                  ‖Run.stochasticGradientMapping (pathRun SR ω) k.1‖ ^ 2)
              hpsi_cur_int
              (hstoch_int.const_mul
                (SR.gamma * (1 - S.L * SR.gamma / 2 - q / 2) - 2 * p))]
      _ =
          expectedPsi SR k.1 -
            (SR.gamma * (1 - S.L * SR.gamma / 2 - q / 2) - 2 * p) *
              expectedStochasticGradientMappingSq SR k.1 +
            (SR.gamma / (2 * q) + 2 * p) * expectedEstimatorErrorSq SR k.1 := by
            simp [expectedPsi, expectedStochasticGradientMappingSq,
              expectedEstimatorErrorSq, SOptLib.expectation,
              MeasureTheory.integral_const_mul]
  calc
    expectedPsi SR (k.1 + 1) + p * expectedExactGradientMappingSq SR k.1
        = ∫ ω, left ω ∂SR.P := by rw [hleft_eq]
    _ ≤ ∫ ω, right ω ∂SR.P := hmono
    _ =
        expectedPsi SR k.1 -
          (SR.gamma * (1 - S.L * SR.gamma / 2 - q / 2) - 2 * p) *
            expectedStochasticGradientMappingSq SR k.1 +
          (SR.gamma / (2 * q) + 2 * p) * expectedEstimatorErrorSq SR k.1 := hright_eq

/-- Budgeted one-step expected descent bridge with the printed no-`q / 2`
coefficient.

The scalar side condition is not a source-facing setup assumption; it is the
route-local algebra that must hold for the exact projected-gradient certificate
and the estimator residual inner product to be absorbed together.  At the
paper's proof constants `p=1/(8L)`, `q=1/8`, and `γ=1/L`, this condition is
proved below. -/
private theorem theorem_6_14_one_step_expected_descent_with_scalar_budget
    (hgamma : SR.gamma = 1 / S.L)
    (k : PositiveIteration) (p q : ℝ) (hp : 0 < p) (hq : 0 < q)
    (hbudget : SR.gamma + 4 * p ≤ 2 * p / q) :
    expectedPsi SR (k.1 + 1) + p * expectedExactGradientMappingSq SR k.1 ≤
      expectedPsi SR k.1 -
        (SR.gamma * (1 - S.L * SR.gamma / 2) - 2 * p) *
          expectedStochasticGradientMappingSq SR k.1 +
        (SR.gamma / (2 * q) + 2 * p) * expectedEstimatorErrorSq SR k.1 := by
  classical
  letI : IsProbabilityMeasure SR.P := SR.P_isProbability
  have hperturb :
      ∀ ω : Ω,
        ‖Run.exactGradientMapping (pathRun SR ω) k.1 -
            Run.stochasticGradientMapping (pathRun SR ω) k.1‖ ≤
          ‖Run.estimatorError (pathRun SR ω) k.1‖ := by
    intro ω
    exact Run.gradient_mapping_perturbation (pathRun SR ω) k
  have hpsi_next_wd := expectedPsi_wellDefined SR (k.1 + 1)
  have hpsi_cur_wd := expectedPsi_wellDefined SR k.1
  have hexact_wd := expectedExactGradientMappingSq_wellDefined SR k.1
  have hstoch_wd := expectedStochasticGradientMappingSq_wellDefined SR k.1
  have hdelta_wd := expectedEstimatorErrorSq_wellDefined SR k.1
  have hLavg :
      S.L = (Fintype.card ι : ℝ)⁻¹ *
        Finset.sum Finset.univ (fun i : ι => S.Lcomp i) := by
    simpa [finiteAverage, SOptLib.finiteUniformAverage, smul_eq_mul] using
      S.L_eq_average
  have hsmooth_path :
      ∀ ω : Ω,
        Setup.finiteSumObjective S (Run.iterate (pathRun SR ω) (k.1 + 1)).1 ≤
          Setup.finiteSumObjective S (Run.iterate (pathRun SR ω) k.1).1 +
            ⟪Setup.fullGradient S (Run.iterate (pathRun SR ω) k.1).1,
              (Run.iterate (pathRun SR ω) (k.1 + 1)).1 -
                (Run.iterate (pathRun SR ω) k.1).1⟫_ℝ +
            (S.L / 2) *
              ‖(Run.iterate (pathRun SR ω) (k.1 + 1)).1 -
                  (Run.iterate (pathRun SR ω) k.1).1‖ ^ 2 := by
    intro ω
    exact
      (by
        simpa [Setup.finiteSumObjective, Setup.fullGradient, Setup.componentGradient,
          finiteAverage] using
          SOptLib.finiteUniformAverage_smooth_quadratic_upper_bound_of_component_lipschitz
            (X := S.X) (F := S.component)
            (gradF := fun i : ι => Setup.componentGradient S i)
            (Lcomp := S.Lcomp) (L := S.L)
            S.convex_X hLavg
            (by
              intro i z hz
              simpa [Setup.componentGradient] using S.component_hasGradientAt i z hz)
            (by
              intro i z w hz hw
              simpa [Setup.componentGradient] using
                S.component_lipschitz_grad i z hz w hw)
            (x := (Run.iterate (pathRun SR ω) k.1).1)
            (y := (Run.iterate (pathRun SR ω) (k.1 + 1)).1)
            (Run.iterate (pathRun SR ω) k.1).2
            (Run.iterate (pathRun SR ω) (k.1 + 1)).2)
  have hprox_descent :
      ∀ ω : Ω,
        SR.gamma⁻¹ *
            ‖(Run.iterate (pathRun SR ω) k.1).1 -
                (Run.iterate (pathRun SR ω) (k.1 + 1)).1‖ ^ 2 +
            S.h (Run.iterate (pathRun SR ω) (k.1 + 1)).1 -
            S.h (Run.iterate (pathRun SR ω) k.1).1 ≤
          ⟪Run.estimator (pathRun SR ω) k.1,
            (Run.iterate (pathRun SR ω) k.1).1 -
              (Run.iterate (pathRun SR ω) (k.1 + 1)).1⟫_ℝ := by
    intro ω
    have hnext := Run.iterate_succ_eq_proxPoint (pathRun SR ω) k
    have hinner :=
      Run.proxPoint_descent_inner_bound (S := S)
        (Run.iterate (pathRun SR ω) k.1)
        (Run.estimator (pathRun SR ω) k.1)
        SR.gamma SR.gamma_pos
    simpa [hnext] using hinner
  have hpointwise :
      ∀ ω : Ω,
        Setup.psi S (Run.iterate (pathRun SR ω) (k.1 + 1)).1 +
            p * ‖Run.exactGradientMapping (pathRun SR ω) k.1‖ ^ 2 ≤
          Setup.psi S (Run.iterate (pathRun SR ω) k.1).1 -
            (SR.gamma * (1 - S.L * SR.gamma / 2) - 2 * p) *
              ‖Run.stochasticGradientMapping (pathRun SR ω) k.1‖ ^ 2 +
            (SR.gamma / (2 * q) + 2 * p) *
              ‖Run.estimatorError (pathRun SR ω) k.1‖ ^ 2 := by
    intro ω
    let Rω := pathRun SR ω
    let x : Feasible S := Run.iterate Rω k.1
    let y : Feasible S := Run.iterate Rω (k.1 + 1)
    let G : Ambient d := Run.estimator Rω k.1
    let exact : Ambient d := Run.exactGradientMapping Rω k.1
    let stoch : Ambient d := Run.stochasticGradientMapping Rω k.1
    let delta : Ambient d := Run.estimatorError Rω k.1
    have hproj :
        ⟪G, y.1 - x.1⟫_ℝ ≤ S.h x.1 - S.h y.1 -
          SR.gamma⁻¹ * ‖y.1 - x.1‖ ^ 2 := by
      have hprox := hprox_descent ω
      have hinner_flip :
          ⟪G, y.1 - x.1⟫_ℝ = -⟪G, x.1 - y.1⟫_ℝ := by
        rw [← neg_sub x.1 y.1, inner_neg_right]
      have hnorm_flip : ‖x.1 - y.1‖ ^ 2 = ‖y.1 - x.1‖ ^ 2 := by
        rw [norm_sub_rev]
      dsimp [Rω, x, y, G] at hprox ⊢
      rw [hinner_flip, ← hnorm_flip]
      linarith
    have hpsi_eta :
        Setup.psi S y.1 ≤
            Setup.finiteSumObjective S y.1 + Setup.psi S x.1 -
            Setup.finiteSumObjective S x.1 - (S.h x.1 - S.h y.1) := by
      simp [Setup.psi_def]
      ring_nf
      exact le_rfl
    have hnext := Run.iterate_succ_eq_proxPoint Rω k
    have hstoch_def :
        stoch = SR.gamma⁻¹ • (x.1 - y.1) := by
      simpa [Rω, x, y, G, stoch, Run.stochasticGradientMapping,
        pathRun, Setup.stochasticProjectedGradient, Setup.projectedGradient_def, hnext]
    have hdelta_def :
        G - Setup.fullGradient S x.1 = delta := by
      rfl
    simpa [Rω, x, y, G, exact, stoch, delta] using
      pointwise_descent_with_exact_certificate_of_perturb_budget
        (psi := Setup.psi S)
        (f := Setup.finiteSumObjective S)
        (grad := fun z : Ambient d => Setup.fullGradient S z)
        (x := x.1) (y := y.1) (G := G) (exact := exact)
        (stoch := stoch) (delta := delta) (gamma := SR.gamma)
        (L := S.L) (p := p) (q := q) (eta := S.h x.1 - S.h y.1)
        SR.gamma_pos hp hq hbudget
        (by simpa [Rω, x, y] using hsmooth_path ω)
        hproj hpsi_eta hstoch_def hdelta_def
        (by simpa [Rω, exact, stoch, delta] using hperturb ω)
  have hpsi_next_int : Integrable
      (fun ω : Ω => Setup.psi S (Run.iterate (pathRun SR ω) (k.1 + 1)).1) SR.P :=
    (SOptLib.expectationWellDefined_iff_integrable
      (μ := SR.P)
      (Z := fun ω : Ω => Setup.psi S (Run.iterate (pathRun SR ω) (k.1 + 1)).1)).mp
      hpsi_next_wd
  have hpsi_cur_int : Integrable
      (fun ω : Ω => Setup.psi S (Run.iterate (pathRun SR ω) k.1).1) SR.P :=
    (SOptLib.expectationWellDefined_iff_integrable
      (μ := SR.P)
      (Z := fun ω : Ω => Setup.psi S (Run.iterate (pathRun SR ω) k.1).1)).mp
      hpsi_cur_wd
  have hexact_int : Integrable
      (fun ω : Ω => ‖Run.exactGradientMapping (pathRun SR ω) k.1‖ ^ 2) SR.P :=
    (SOptLib.expectationWellDefined_iff_integrable
      (μ := SR.P)
      (Z := fun ω : Ω => ‖Run.exactGradientMapping (pathRun SR ω) k.1‖ ^ 2)).mp
      hexact_wd
  have hstoch_int : Integrable
      (fun ω : Ω => ‖Run.stochasticGradientMapping (pathRun SR ω) k.1‖ ^ 2) SR.P :=
    (SOptLib.expectationWellDefined_iff_integrable
      (μ := SR.P)
      (Z := fun ω : Ω => ‖Run.stochasticGradientMapping (pathRun SR ω) k.1‖ ^ 2)).mp
      hstoch_wd
  have hdelta_int : Integrable
      (fun ω : Ω => ‖Run.estimatorError (pathRun SR ω) k.1‖ ^ 2) SR.P :=
    (SOptLib.expectationWellDefined_iff_integrable
      (μ := SR.P)
      (Z := fun ω : Ω => ‖Run.estimatorError (pathRun SR ω) k.1‖ ^ 2)).mp
      hdelta_wd
  let left : Ω → ℝ := fun ω =>
    Setup.psi S (Run.iterate (pathRun SR ω) (k.1 + 1)).1 +
      p * ‖Run.exactGradientMapping (pathRun SR ω) k.1‖ ^ 2
  let right : Ω → ℝ := fun ω =>
    Setup.psi S (Run.iterate (pathRun SR ω) k.1).1 -
      (SR.gamma * (1 - S.L * SR.gamma / 2) - 2 * p) *
        ‖Run.stochasticGradientMapping (pathRun SR ω) k.1‖ ^ 2 +
      (SR.gamma / (2 * q) + 2 * p) *
        ‖Run.estimatorError (pathRun SR ω) k.1‖ ^ 2
  have hleft_int : Integrable left SR.P :=
    hpsi_next_int.add (hexact_int.const_mul p)
  have hright_int : Integrable right SR.P :=
    (hpsi_cur_int.sub
        (hstoch_int.const_mul
          (SR.gamma * (1 - S.L * SR.gamma / 2) - 2 * p))).add
      (hdelta_int.const_mul (SR.gamma / (2 * q) + 2 * p))
  have hmono : ∫ ω, left ω ∂SR.P ≤ ∫ ω, right ω ∂SR.P := by
    exact MeasureTheory.integral_mono hleft_int hright_int hpointwise
  have hleft_eq :
      ∫ ω, left ω ∂SR.P =
        expectedPsi SR (k.1 + 1) + p * expectedExactGradientMappingSq SR k.1 := by
    dsimp [left]
    rw [MeasureTheory.integral_add hpsi_next_int (hexact_int.const_mul p)]
    simp [expectedPsi, expectedExactGradientMappingSq, SOptLib.expectation,
      MeasureTheory.integral_const_mul]
  have hright_eq :
      ∫ ω, right ω ∂SR.P =
        expectedPsi SR k.1 -
          (SR.gamma * (1 - S.L * SR.gamma / 2) - 2 * p) *
            expectedStochasticGradientMappingSq SR k.1 +
          (SR.gamma / (2 * q) + 2 * p) * expectedEstimatorErrorSq SR k.1 := by
    dsimp [right]
    calc
      ∫ ω : Ω,
          Setup.psi S (Run.iterate (pathRun SR ω) k.1).1 -
              (SR.gamma * (1 - S.L * SR.gamma / 2) - 2 * p) *
                ‖Run.stochasticGradientMapping (pathRun SR ω) k.1‖ ^ 2 +
            (SR.gamma / (2 * q) + 2 * p) *
              ‖Run.estimatorError (pathRun SR ω) k.1‖ ^ 2 ∂SR.P
          =
          ∫ ω : Ω,
            Setup.psi S (Run.iterate (pathRun SR ω) k.1).1 -
              (SR.gamma * (1 - S.L * SR.gamma / 2) - 2 * p) *
                ‖Run.stochasticGradientMapping (pathRun SR ω) k.1‖ ^ 2 ∂SR.P +
          ∫ ω : Ω,
            (SR.gamma / (2 * q) + 2 * p) *
              ‖Run.estimatorError (pathRun SR ω) k.1‖ ^ 2 ∂SR.P := by
            exact MeasureTheory.integral_add
              (f := fun ω : Ω =>
                Setup.psi S (Run.iterate (pathRun SR ω) k.1).1 -
                  (SR.gamma * (1 - S.L * SR.gamma / 2) - 2 * p) *
                    ‖Run.stochasticGradientMapping (pathRun SR ω) k.1‖ ^ 2)
              (g := fun ω : Ω =>
                (SR.gamma / (2 * q) + 2 * p) *
                  ‖Run.estimatorError (pathRun SR ω) k.1‖ ^ 2)
              (hpsi_cur_int.sub
                (hstoch_int.const_mul
                  (SR.gamma * (1 - S.L * SR.gamma / 2) - 2 * p)))
              (hdelta_int.const_mul (SR.gamma / (2 * q) + 2 * p))
      _ =
          (∫ ω : Ω, Setup.psi S (Run.iterate (pathRun SR ω) k.1).1 ∂SR.P -
            ∫ ω : Ω,
              (SR.gamma * (1 - S.L * SR.gamma / 2) - 2 * p) *
                ‖Run.stochasticGradientMapping (pathRun SR ω) k.1‖ ^ 2 ∂SR.P) +
          ∫ ω : Ω,
            (SR.gamma / (2 * q) + 2 * p) *
              ‖Run.estimatorError (pathRun SR ω) k.1‖ ^ 2 ∂SR.P := by
            rw [MeasureTheory.integral_sub
              (f := fun ω : Ω => Setup.psi S (Run.iterate (pathRun SR ω) k.1).1)
              (g := fun ω : Ω =>
                (SR.gamma * (1 - S.L * SR.gamma / 2) - 2 * p) *
                  ‖Run.stochasticGradientMapping (pathRun SR ω) k.1‖ ^ 2)
              hpsi_cur_int
              (hstoch_int.const_mul
                (SR.gamma * (1 - S.L * SR.gamma / 2) - 2 * p))]
      _ =
          expectedPsi SR k.1 -
            (SR.gamma * (1 - S.L * SR.gamma / 2) - 2 * p) *
              expectedStochasticGradientMappingSq SR k.1 +
            (SR.gamma / (2 * q) + 2 * p) * expectedEstimatorErrorSq SR k.1 := by
            simp [expectedPsi, expectedStochasticGradientMappingSq,
              expectedEstimatorErrorSq, SOptLib.expectation,
              MeasureTheory.integral_const_mul]
  calc
    expectedPsi SR (k.1 + 1) + p * expectedExactGradientMappingSq SR k.1
        = ∫ ω, left ω ∂SR.P := by rw [hleft_eq]
    _ ≤ ∫ ω, right ω ∂SR.P := hmono
    _ =
        expectedPsi SR k.1 -
          (SR.gamma * (1 - S.L * SR.gamma / 2) - 2 * p) *
            expectedStochasticGradientMappingSq SR k.1 +
          (SR.gamma / (2 * q) + 2 * p) * expectedEstimatorErrorSq SR k.1 := hright_eq

/-- Scalar coefficient supplied by the corrected one-step bridge at the paper's
auxiliary choices `p = 1/(8L)`, `q = 1/8`, and `γ = 1/L`.

This is the Lean-visible form of the source-boundary issue: keeping the
Eq. (6.5.10) `q / 2` loss gives `3/(16L)`, whereas the following source display
uses the no-q-loss value `1/(4L)`. -/
private theorem corrected_one_step_stochastic_coefficient_at_paper_constants
    (hgamma : SR.gamma = 1 / S.L) :
    SR.gamma * (1 - S.L * SR.gamma / 2 - (1 / 8 : ℝ) / 2) -
        2 * (1 / (8 * S.L)) =
      3 / (16 * S.L) := by
  have hL_pos : 0 < S.L := Setup.L_pos S
  have hL_ne : S.L ≠ 0 := ne_of_gt hL_pos
  rw [hgamma]
  field_simp [hL_ne]
  ring

/-- Estimator-error coefficient in the corrected one-step bridge at the paper's
auxiliary choices `p = 1/(8L)` and `q = 1/8`. -/
private theorem corrected_one_step_error_coefficient_at_paper_constants
    (hgamma : SR.gamma = 1 / S.L) :
    SR.gamma / (2 * (1 / 8 : ℝ)) + 2 * (1 / (8 * S.L)) =
      17 / (4 * S.L) := by
  have hL_pos : 0 < S.L := Setup.L_pos S
  have hL_ne : S.L ≠ 0 := ne_of_gt hL_pos
  rw [hgamma]
  field_simp [hL_ne]
  ring

/-- Stochastic-gradient coefficient in the budgeted no-`q / 2` one-step bridge
at the paper's auxiliary choices. -/
private theorem budgeted_one_step_stochastic_coefficient_at_paper_constants
    (hgamma : SR.gamma = 1 / S.L) :
    SR.gamma * (1 - S.L * SR.gamma / 2) -
        2 * (1 / (8 * S.L)) =
      1 / (4 * S.L) := by
  have hL_pos : 0 < S.L := Setup.L_pos S
  have hL_ne : S.L ≠ 0 := ne_of_gt hL_pos
  rw [hgamma]
  field_simp [hL_ne]
  ring

/-- The paper-constant one-step supplier for the printed Theorem 6.14 route.

This is the source-faithful repair of the proof gap after Eq. (6.5.10): the
`q / 2` loss is not erased arbitrarily, but absorbed together with the
`p‖g_X,k‖²` certificate under the proved scalar budget. -/
theorem theorem_6_14_one_step_expected_descent_at_paper_constants
    (hgamma : SR.gamma = 1 / S.L) (k : PositiveIteration) :
    expectedPsi SR (k.1 + 1) +
        (1 / (8 * S.L)) * expectedExactGradientMappingSq SR k.1 ≤
      expectedPsi SR k.1 -
        (1 / (4 * S.L)) * expectedStochasticGradientMappingSq SR k.1 +
        (17 / (4 * S.L)) * expectedEstimatorErrorSq SR k.1 := by
  have hL_pos : 0 < S.L := Setup.L_pos S
  have hL_ne : S.L ≠ 0 := ne_of_gt hL_pos
  have hp : 0 < (1 / (8 * S.L)) := by positivity
  have hq : 0 < (1 / 8 : ℝ) := by norm_num
  have hbudget :
      SR.gamma + 4 * (1 / (8 * S.L)) ≤
        2 * (1 / (8 * S.L)) / (1 / 8 : ℝ) := by
    rw [hgamma]
    field_simp [hL_ne]
    linarith [hL_pos]
  have h :=
    theorem_6_14_one_step_expected_descent_with_scalar_budget
      (SR := SR) hgamma k (1 / (8 * S.L)) (1 / 8 : ℝ) hp hq hbudget
  have hstoch :=
    budgeted_one_step_stochastic_coefficient_at_paper_constants (SR := SR) hgamma
  have herr :=
    corrected_one_step_error_coefficient_at_paper_constants (SR := SR) hgamma
  rw [hstoch, herr] at h
  simpa using h

/-- Terminal-epoch scalar coefficient forced by the corrected q-loss one-step
route under the theorem's batch choice `b=17T`.

The printed proof uses the no-q-loss value and obtains `1/(4LT)`.  Retaining the
`q / 2` term from Eq. (6.5.10) instead gives `(4 - T)/(16LT)`. -/
private theorem corrected_epoch_terminal_coefficient_at_batch_17T :
    3 / (16 * S.L) -
        17 * ((SR.T : ℝ) - 1) / (4 * S.L * (17 * (SR.T : ℝ))) =
      (4 - (SR.T : ℝ)) / (16 * S.L * (SR.T : ℝ)) := by
  have hL_pos : 0 < S.L := Setup.L_pos S
  have hT_pos : 0 < (SR.T : ℝ) := by
    exact_mod_cast SR.T_pos
  field_simp [hL_pos.ne', hT_pos.ne']
  ring

/-- The terminal coefficient appearing in the corrected epoch theorem after
rewriting the theorem hypothesis `b=17T`. -/
private theorem corrected_epoch_terminal_coefficient_at_paper_batch
    (hbatch : SR.batchSize = 17 * SR.T) :
    3 / (16 * S.L) -
        17 * ((SR.T : ℝ) - 1) / (4 * S.L * (SR.batchSize : ℝ)) =
      (4 - (SR.T : ℝ)) / (16 * S.L * (SR.T : ℝ)) := by
  have hbatch_real : (SR.batchSize : ℝ) = 17 * (SR.T : ℝ) := by
    exact_mod_cast hbatch
  rw [hbatch_real]
  exact corrected_epoch_terminal_coefficient_at_batch_17T (SR := SR)

/-- The corrected terminal-epoch coefficient cannot be the positive coefficient
claimed in the printed proof once the epoch length is at least four. -/
private theorem corrected_epoch_terminal_coefficient_not_pos_of_four_le_T
    (hT_large : 4 ≤ SR.T) :
    ¬ 0 <
      3 / (16 * S.L) -
        17 * ((SR.T : ℝ) - 1) / (4 * S.L * (17 * (SR.T : ℝ))) := by
  have hL_pos : 0 < S.L := Setup.L_pos S
  have hT_pos : 0 < (SR.T : ℝ) := by
    exact_mod_cast SR.T_pos
  have hden_pos : 0 < 16 * S.L * (SR.T : ℝ) := by positivity
  have hnum_nonpos : 4 - (SR.T : ℝ) ≤ 0 := by
    have hT_large_real : (4 : ℝ) ≤ (SR.T : ℝ) := by
      exact_mod_cast hT_large
    linarith
  have hfrac_nonpos :
      (4 - (SR.T : ℝ)) / (16 * S.L * (SR.T : ℝ)) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hnum_nonpos (le_of_lt hden_pos)
  have hcoeff_eq :=
    corrected_epoch_terminal_coefficient_at_batch_17T (SR := SR)
  intro hpos
  rw [hcoeff_eq] at hpos
  linarith

/-- Direct non-positivity certificate for the coefficient in the corrected epoch
theorem under the paper's batch-size hypothesis. -/
private theorem corrected_epoch_terminal_coefficient_at_paper_batch_not_pos_of_four_le_T
    (hbatch : SR.batchSize = 17 * SR.T) (hT_large : 4 ≤ SR.T) :
    ¬ 0 <
      3 / (16 * S.L) -
        17 * ((SR.T : ℝ) - 1) / (4 * S.L * (SR.batchSize : ℝ)) := by
  have hcoeff_eq :=
    corrected_epoch_terminal_coefficient_at_paper_batch (SR := SR) hbatch
  have hbase :=
    corrected_epoch_terminal_coefficient_not_pos_of_four_le_T (SR := SR) hT_large
  intro hpos
  rw [hcoeff_eq] at hpos
  exact hbase (by
    rw [corrected_epoch_terminal_coefficient_at_batch_17T (SR := SR)]
    exact hpos)

/-- Pure finite-sum telescope for the corrected residual epoch diagnostic.

This is the algebraic core of the source Eq. (6.5.11)--(6.5.12) summation:
after the one-step inequalities telescope, it remains only to bound the summed
estimator-error contribution by an explicit multiple of the stochastic-gradient
mass.  The helper is private and immediately consumed by the corrected epoch
theorem; it does not add a theorem-head assumption to the paper-facing route. -/
private theorem corrected_epoch_telescope_of_error_sum_bound
    (A E G D : ℕ → ℝ) (p c d errorCoeff : ℝ) (t : ℕ) (ht_pos : 1 ≤ t)
    (hstep :
      ∀ j ∈ Finset.Icc 1 t,
        A (j + 1) + p * E j ≤ A j - c * G j + d * D j)
    (herror :
      d * Finset.sum (Finset.Icc 1 t) D ≤
        errorCoeff * Finset.sum (Finset.Icc 1 t) G) :
    A (t + 1) + p * Finset.sum (Finset.Icc 1 t) E ≤
      A 1 - (c - errorCoeff) * Finset.sum (Finset.Icc 1 t) G := by
  exact sum_Icc_step_telescope_le_of_sum_budget A E G D p c d errorCoeff t ht_pos
    hstep herror

/-- Sharp finite predecessor-row bound used in Lan Eq. (6.5.11)--(6.5.12).

This specializes the source's lower-triangular double-sum count.  Considered
`sum_active_triangular_predecessor_le_card_mul_sum` from SOptLib/Glue/Algebra:
that lemma gives a `T *` active-prefix bound, but the present paper step needs
the sharper `(t - 1) *` coefficient coming from the zero first row in
`∑_{j=1}^t ∑_{i=2}^j`; the existing active-prefix statement does not expose
that zero-row refinement. -/
private theorem sum_Icc_predecessor_count_le_pred_mul_sum
    (a : ℕ → ℝ) (t : ℕ) (ht_pos : 1 ≤ t)
    (ha_nonneg : ∀ r ∈ Finset.Icc 1 t, 0 ≤ a r) :
    Finset.sum (Finset.Icc 1 t)
        (fun j => Finset.sum (Finset.Icc 2 j) (fun i => a (i - 1))) ≤
      ((t : ℝ) - 1) * Finset.sum (Finset.Icc 1 t) a := by
  simpa [nsmul_eq_mul, Nat.cast_sub ht_pos] using
    (_root_.sum_Icc_predecessor_count_le_pred_mul_sum (M := ℝ) a t ha_nonneg)

/-- Initial expected objective value for Algorithm 6.6.

This aligns with Theorem 6.14's Eq. (6.5.8) right endpoint: `x_1` is
deterministic in the generated stochastic run, so its expectation is the
initial composite objective value. -/
private theorem expectedPsi_one_eq_initial :
    expectedPsi SR 1 = Setup.psi S SR.x₁.1 := by
  classical
  letI : IsProbabilityMeasure SR.P := SR.P_isProbability
  simp [expectedPsi, SOptLib.expectation, pathRun]

/-- One-based prefix split used to sum Lan Eq. (6.5.13) across epochs.

No SOptLib match: searched `finite sum interval epoch prefix split Icc` and
`Finset sum Icc add interval split nat shifted`; checked
`SOptLib.sum_outputWindow_eq_sum_activeEpochSteps`, `SOptLib.stepOfIndex_*`,
and `Finset.sum_Icc_succ_top`.  The SOptLib theorem partitions a full output
window through active-step machinery, while Theorem 6.14 needs this literal
closed-prefix identity for `{1,...,a+t}` before decoding an arbitrary index. -/
private theorem sum_Icc_prefix_add_shift (A : ℕ → ℝ) (a t : ℕ) :
    Finset.sum (Finset.Icc 1 (a + t)) A =
      Finset.sum (Finset.Icc 1 a) A +
        Finset.sum (Finset.Icc 1 t) (fun j => A (a + j)) := by
  exact _root_.sum_Icc_one_add_eq_sum_Icc_one_add_shift A a t

/-- Estimator-error sum budget for the corrected residual epoch diagnostic.

This is the remaining finite-sum counting step after Lemma 6.10 has rewritten
each estimator-error term into predecessor stochastic-gradient masses.  It is a
strictly smaller leaf than the epoch descent theorem: no one-step descent,
objective telescope, or source-boundary decision remains here. -/
private theorem corrected_epoch_estimator_error_sum_bound
    (hgamma : SR.gamma = 1 / S.L) (hbatch : SR.batchSize = 17 * SR.T)
    (s t : ℕ) (ht_pos : 1 ≤ t)
    (hvariance_stoch :
      ∀ j ∈ Finset.Icc 1 t,
        expectedEstimatorErrorSq SR (epochIndex SR s j) ≤
          (S.L ^ 2 / (SR.batchSize : ℝ)) *
            Finset.sum (Finset.Icc 2 j)
              (fun i =>
                SR.gamma ^ 2 *
                  expectedStochasticGradientMappingSq SR (epochIndex SR s (i - 1)))) :
    (17 / (4 * S.L)) *
        Finset.sum (Finset.Icc 1 t)
          (fun j => expectedEstimatorErrorSq SR (epochIndex SR s j))
      ≤
    (17 * ((t : ℝ) - 1) / (4 * S.L * (SR.batchSize : ℝ))) *
        Finset.sum (Finset.Icc 1 t)
          (fun j => expectedStochasticGradientMappingSq SR (epochIndex SR s j)) := by
  have h :=
    sum_Icc_error_le_scaled_predecessor_mass
      (fun j => expectedEstimatorErrorSq SR (epochIndex SR s j))
      (fun j => expectedStochasticGradientMappingSq SR (epochIndex SR s j))
      (S.L ^ 2) (SR.gamma ^ 2) (SR.batchSize : ℝ) (17 / (4 * S.L)) t ht_pos
      (by
        rw [hgamma]
        field_simp [(Setup.L_pos S).ne'])
      (by exact_mod_cast SR.batchSize_pos)
      (by
        have hL_pos : 0 < S.L := Setup.L_pos S
        positivity)
      (fun r _hr => expectedStochasticGradientMappingSq_nonneg (SR := SR)
        (epochIndex SR s r))
      hvariance_stoch
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h

/-- Corrected epoch-form descent inequality obtained by retaining the q-loss
from Eq. (6.5.10).

This is the source-consistent replacement for the printed Eq. (6.5.13) route.
The residual stochastic-gradient term is exactly the coefficient left after
telescoping the corrected one-step inequality and substituting Lemma 6.10.  The
formal scalar facts above show why the printed proof cannot simply drop this
term under `b=17T` for arbitrary epoch length. -/
theorem theorem_6_14_corrected_epoch_descent
    (hgamma : SR.gamma = 1 / S.L) (hbatch : SR.batchSize = 17 * SR.T)
    (hvariance :
      ∀ s t : ℕ, 1 ≤ t → t ≤ SR.T →
        expectedEstimatorErrorSq SR (epochIndex SR s t) ≤
          (S.L ^ 2 / (SR.batchSize : ℝ)) *
            Finset.sum (Finset.Icc 2 t)
              (fun i => expectedDisplacementSq SR (epochIndex SR s i)))
    (honeStep :
      ∀ (k : PositiveIteration) (p q : ℝ), 0 < p → 0 < q →
        expectedPsi SR (k.1 + 1) + p * expectedExactGradientMappingSq SR k.1 ≤
          expectedPsi SR k.1 -
            (SR.gamma * (1 - S.L * SR.gamma / 2 - q / 2) - 2 * p) *
              expectedStochasticGradientMappingSq SR k.1 +
            (SR.gamma / (2 * q) + 2 * p) * expectedEstimatorErrorSq SR k.1)
    (s t : ℕ) (ht_pos : 1 ≤ t) (ht_epoch : t ≤ SR.T) :
    expectedPsi SR (epochIndex SR s (t + 1)) +
        (1 / (8 * S.L)) *
          Finset.sum (Finset.Icc 1 t)
            (fun j => expectedExactGradientMappingSq SR (epochIndex SR s j))
      ≤ expectedPsi SR (epochIndex SR s 1) -
        (3 / (16 * S.L) -
          17 * ((t : ℝ) - 1) / (4 * S.L * (SR.batchSize : ℝ))) *
            Finset.sum (Finset.Icc 1 t)
              (fun j => expectedStochasticGradientMappingSq SR (epochIndex SR s j)) := by
  classical
  letI : IsProbabilityMeasure SR.P := SR.P_isProbability
  have hL_pos : 0 < S.L := Setup.L_pos S
  have hp : 0 < (1 / (8 * S.L)) := by positivity
  have hq : 0 < (1 / 8 : ℝ) := by norm_num
  have hcorrected_stoch_coeff :
      SR.gamma * (1 - S.L * SR.gamma / 2 - (1 / 8 : ℝ) / 2) -
          2 * (1 / (8 * S.L)) =
        3 / (16 * S.L) :=
    corrected_one_step_stochastic_coefficient_at_paper_constants SR hgamma
  have hcorrected_error_coeff :
      SR.gamma / (2 * (1 / 8 : ℝ)) + 2 * (1 / (8 * S.L)) =
        17 / (4 * S.L) :=
    corrected_one_step_error_coefficient_at_paper_constants SR hgamma
  have hdisp_to_stoch :
      ∀ j ∈ Finset.Icc 2 t,
        expectedDisplacementSq SR (epochIndex SR s j) =
          SR.gamma ^ 2 *
            expectedStochasticGradientMappingSq SR (epochIndex SR s (j - 1)) := by
    intro j hj
    have hj_two : 2 ≤ j := (Finset.mem_Icc.mp hj).1
    have hpos : 1 ≤ epochIndex SR s (j - 1) := by
      unfold epochIndex
      omega
    let k : PositiveIteration := ⟨epochIndex SR s (j - 1), hpos⟩
    have hidx : k.1 + 1 = epochIndex SR s j := by
      dsimp [k]
      unfold epochIndex
      omega
    calc
      expectedDisplacementSq SR (epochIndex SR s j)
          = expectedDisplacementSq SR (k.1 + 1) := by rw [hidx]
      _ = SR.gamma ^ 2 *
            expectedStochasticGradientMappingSq SR k.1 :=
          expectedDisplacementSq_succ_eq_gamma_sq_mul_stochasticGradientMappingSq
            SR k
      _ = SR.gamma ^ 2 *
            expectedStochasticGradientMappingSq SR (epochIndex SR s (j - 1)) := by
          rfl
  have hvariance_stoch :
      expectedEstimatorErrorSq SR (epochIndex SR s t) ≤
        (S.L ^ 2 / (SR.batchSize : ℝ)) *
          Finset.sum (Finset.Icc 2 t)
            (fun i =>
              SR.gamma ^ 2 *
                expectedStochasticGradientMappingSq SR (epochIndex SR s (i - 1))) := by
    have hdisp_sum :
        Finset.sum (Finset.Icc 2 t)
            (fun i => expectedDisplacementSq SR (epochIndex SR s i)) =
          Finset.sum (Finset.Icc 2 t)
            (fun i =>
              SR.gamma ^ 2 *
                expectedStochasticGradientMappingSq SR (epochIndex SR s (i - 1))) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      exact hdisp_to_stoch i hi
    simpa [hdisp_sum] using hvariance s t ht_pos ht_epoch
  have hvariance_stoch_all :
      ∀ j ∈ Finset.Icc 1 t,
        expectedEstimatorErrorSq SR (epochIndex SR s j) ≤
          (S.L ^ 2 / (SR.batchSize : ℝ)) *
            Finset.sum (Finset.Icc 2 j)
              (fun i =>
                SR.gamma ^ 2 *
                  expectedStochasticGradientMappingSq SR (epochIndex SR s (i - 1))) := by
    intro j hj
    have hj_pos : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hj_le_t : j ≤ t := (Finset.mem_Icc.mp hj).2
    have hj_epoch : j ≤ SR.T := le_trans hj_le_t ht_epoch
    have hdisp_sum :
        Finset.sum (Finset.Icc 2 j)
            (fun i => expectedDisplacementSq SR (epochIndex SR s i)) =
          Finset.sum (Finset.Icc 2 j)
            (fun i =>
              SR.gamma ^ 2 *
                expectedStochasticGradientMappingSq SR (epochIndex SR s (i - 1))) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      have hi_in_t : i ∈ Finset.Icc 2 t := by
        exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hi).1,
          le_trans (Finset.mem_Icc.mp hi).2 hj_le_t⟩
      exact hdisp_to_stoch i hi_in_t
    simpa [hdisp_sum] using hvariance s j hj_pos hj_epoch
  have hstep :
      ∀ j ∈ Finset.Icc 1 t,
        expectedPsi SR (epochIndex SR s (j + 1)) +
            (1 / (8 * S.L)) *
              expectedExactGradientMappingSq SR (epochIndex SR s j) ≤
          expectedPsi SR (epochIndex SR s j) -
            (3 / (16 * S.L)) *
              expectedStochasticGradientMappingSq SR (epochIndex SR s j) +
            (17 / (4 * S.L)) *
              expectedEstimatorErrorSq SR (epochIndex SR s j) := by
    intro j hj
    have hj_pos : 1 ≤ epochIndex SR s j := by
      have hj_one : 1 ≤ j := (Finset.mem_Icc.mp hj).1
      unfold epochIndex
      omega
    let k : PositiveIteration := ⟨epochIndex SR s j, hj_pos⟩
    have hidx : k.1 + 1 = epochIndex SR s (j + 1) := by
      dsimp [k]
      unfold epochIndex
      omega
    have h := honeStep k (1 / (8 * S.L)) (1 / 8 : ℝ) hp hq
    rw [hcorrected_stoch_coeff, hcorrected_error_coeff] at h
    simpa [hidx, k] using h
  have herror :=
    corrected_epoch_estimator_error_sum_bound (SR := SR) hgamma hbatch s t ht_pos
      hvariance_stoch_all
  exact
    corrected_epoch_telescope_of_error_sum_bound
      (fun j => expectedPsi SR (epochIndex SR s j))
      (fun j => expectedExactGradientMappingSq SR (epochIndex SR s j))
      (fun j => expectedStochasticGradientMappingSq SR (epochIndex SR s j))
      (fun j => expectedEstimatorErrorSq SR (epochIndex SR s j))
      (1 / (8 * S.L)) (3 / (16 * S.L)) (17 / (4 * S.L))
      (17 * ((t : ℝ) - 1) / (4 * S.L * (SR.batchSize : ℝ)))
      t ht_pos hstep herror

/-- Source-gap certificate for the dropped stochastic-gradient term in the
printed proof of Theorem 6.14.

With the corrected Eq. (6.5.10) coefficient and the paper batch choice `b=17T`,
the terminal epoch coefficient is not positive once `T ≥ 4`.  Therefore the
printed no-residual epoch/global route is not recovered by simply dropping this
term. -/
theorem theorem_6_14_printed_epoch_drop_incompatible_with_corrected_q_loss
    (hbatch : SR.batchSize = 17 * SR.T) (hT_large : 4 ≤ SR.T) :
    ¬ 0 <
      3 / (16 * S.L) -
        17 * ((SR.T : ℝ) - 1) / (4 * S.L * (SR.batchSize : ℝ)) :=
  corrected_epoch_terminal_coefficient_at_paper_batch_not_pos_of_four_le_T
    (SR := SR) hbatch hT_large

/-- Same-granularity scalar source-gap certificate for the printed epoch drop.

The previous obstruction checked the paper's printed auxiliary choice `q = 1/8`.
This stronger scalar certificate rules out the natural repair "keep Eq.
(6.5.10)'s `q / 2` loss but choose a better positive Young parameter `q`":
at the concrete epoch length `T = 20` and batch choice `b = 17T`, the corrected
terminal stochastic-gradient coefficient is strictly negative for every
`q > 0` after normalizing by the positive factor `L`.

The normalized coefficient is
`(1/4 - q/2) - (1/(2q)+1/4) * ((T-1)/(17T))`, coming from
`p=1/(8L)`, `γ=1/L`, the corrected one-step q-loss coefficient, and Lemma 6.10.
Thus the source proof route cannot recover the printed Eq. (6.5.13) drop under
the theorem's `b=17T` by retuning `q`; a theorem-level correction or a different
source argument is required. -/
theorem theorem_6_14_corrected_q_loss_epoch_drop_incompatible_for_all_q_at_T20
    (q : ℝ) (hq : 0 < q) :
    (1 / 4 - q / 2) - (1 / (2 * q) + 1 / 4) * (19 / (17 * 20 : ℝ)) < 0 := by
  have hpoly_pos : 0 < 680 * q ^ 2 - 321 * q + 38 := by
    have hs : 0 ≤ (1360 * q - 321) ^ 2 := sq_nonneg (1360 * q - 321)
    nlinarith
  have hmul_eq :
      ((1 / 4 - q / 2) - (1 / (2 * q) + 1 / 4) * (19 / (17 * 20 : ℝ))) *
          (680 * q) =
        - (680 * q ^ 2 - 321 * q + 38) / 2 := by
    field_simp [ne_of_gt hq]
    ring
  have hmul_neg :
      ((1 / 4 - q / 2) - (1 / (2 * q) + 1 / 4) * (19 / (17 * 20 : ℝ))) *
          (680 * q) < 0 := by
    rw [hmul_eq]
    nlinarith
  have hscale_pos : 0 < 680 * q := by positivity
  nlinarith

/-- Epoch-form descent inequality printed as Eq. (6.5.13).

This route uses the proved paper-constant one-step scalar budget rather than
dropping the `q / 2` loss from Eq. (6.5.10) in isolation.  The remaining proof
work is the finite telescope of the specialized one-step inequality, substitution
of Lemma 6.10, and the paper's coefficient calculation under `b=17T`. -/
private theorem theorem_6_14_epoch_descent
    (hgamma : SR.gamma = 1 / S.L) (hbatch : SR.batchSize = 17 * SR.T)
    (hvariance :
      ∀ s t : ℕ, 1 ≤ t → t ≤ SR.T →
        expectedEstimatorErrorSq SR (epochIndex SR s t) ≤
          (S.L ^ 2 / (SR.batchSize : ℝ)) *
            Finset.sum (Finset.Icc 2 t)
              (fun i => expectedDisplacementSq SR (epochIndex SR s i)))
    (honeStep :
      ∀ (k : PositiveIteration),
        expectedPsi SR (k.1 + 1) +
            (1 / (8 * S.L)) * expectedExactGradientMappingSq SR k.1 ≤
          expectedPsi SR k.1 -
            (1 / (4 * S.L)) *
              expectedStochasticGradientMappingSq SR k.1 +
            (17 / (4 * S.L)) * expectedEstimatorErrorSq SR k.1)
    (s t : ℕ) (ht_pos : 1 ≤ t) (ht_epoch : t ≤ SR.T) :
    expectedPsi SR (epochIndex SR s (t + 1)) +
        (1 / (8 * S.L)) *
          Finset.sum (Finset.Icc 1 t)
            (fun j => expectedExactGradientMappingSq SR (epochIndex SR s j))
      ≤ expectedPsi SR (epochIndex SR s 1) := by
  classical
  letI : IsProbabilityMeasure SR.P := SR.P_isProbability
  -- Source route: telescope `honeStep` over `j=1,...,t`, rewrite Lemma 6.10's
  -- displacement sum with `expectedDisplacementSq_succ_eq_gamma_sq_mul_stochasticGradientMappingSq`,
  -- substitute `γ=1/L` and `b=17T`, then use `t ≤ T` to drop the resulting
  -- nonpositive stochastic-gradient correction.
  have hL_pos : 0 < S.L := Setup.L_pos S
  have hdisp_to_stoch :
      ∀ j ∈ Finset.Icc 2 t,
        expectedDisplacementSq SR (epochIndex SR s j) =
          SR.gamma ^ 2 *
            expectedStochasticGradientMappingSq SR (epochIndex SR s (j - 1)) := by
    intro j hj
    have hj_two : 2 ≤ j := (Finset.mem_Icc.mp hj).1
    have hpos : 1 ≤ epochIndex SR s (j - 1) := by
      unfold epochIndex
      omega
    let k : PositiveIteration := ⟨epochIndex SR s (j - 1), hpos⟩
    have hidx : k.1 + 1 = epochIndex SR s j := by
      dsimp [k]
      unfold epochIndex
      omega
    calc
      expectedDisplacementSq SR (epochIndex SR s j)
          = expectedDisplacementSq SR (k.1 + 1) := by rw [hidx]
      _ = SR.gamma ^ 2 *
            expectedStochasticGradientMappingSq SR k.1 :=
          expectedDisplacementSq_succ_eq_gamma_sq_mul_stochasticGradientMappingSq
            SR k
      _ = SR.gamma ^ 2 *
            expectedStochasticGradientMappingSq SR (epochIndex SR s (j - 1)) := by
          rfl
  have hvariance_stoch_all :
      ∀ j ∈ Finset.Icc 1 t,
        expectedEstimatorErrorSq SR (epochIndex SR s j) ≤
          (S.L ^ 2 / (SR.batchSize : ℝ)) *
            Finset.sum (Finset.Icc 2 j)
              (fun i =>
                SR.gamma ^ 2 *
                  expectedStochasticGradientMappingSq SR (epochIndex SR s (i - 1))) := by
    intro j hj
    have hj_pos : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hj_le_t : j ≤ t := (Finset.mem_Icc.mp hj).2
    have hj_epoch : j ≤ SR.T := le_trans hj_le_t ht_epoch
    have hdisp_sum :
        Finset.sum (Finset.Icc 2 j)
            (fun i => expectedDisplacementSq SR (epochIndex SR s i)) =
          Finset.sum (Finset.Icc 2 j)
            (fun i =>
              SR.gamma ^ 2 *
                expectedStochasticGradientMappingSq SR (epochIndex SR s (i - 1))) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      have hi_in_t : i ∈ Finset.Icc 2 t := by
        exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hi).1,
          le_trans (Finset.mem_Icc.mp hi).2 hj_le_t⟩
      exact hdisp_to_stoch i hi_in_t
    simpa [hdisp_sum] using hvariance s j hj_pos hj_epoch
  have hstep :
      ∀ j ∈ Finset.Icc 1 t,
        expectedPsi SR (epochIndex SR s (j + 1)) +
            (1 / (8 * S.L)) *
              expectedExactGradientMappingSq SR (epochIndex SR s j) ≤
          expectedPsi SR (epochIndex SR s j) -
            (1 / (4 * S.L)) *
              expectedStochasticGradientMappingSq SR (epochIndex SR s j) +
            (17 / (4 * S.L)) *
              expectedEstimatorErrorSq SR (epochIndex SR s j) := by
    intro j hj
    have hj_pos : 1 ≤ epochIndex SR s j := by
      have hj_one : 1 ≤ j := (Finset.mem_Icc.mp hj).1
      unfold epochIndex
      omega
    let k : PositiveIteration := ⟨epochIndex SR s j, hj_pos⟩
    have hidx : k.1 + 1 = epochIndex SR s (j + 1) := by
      dsimp [k]
      unfold epochIndex
      omega
    have h := honeStep k
    simpa [hidx, k] using h
  have herror :=
    corrected_epoch_estimator_error_sum_bound (SR := SR) hgamma hbatch s t ht_pos
      hvariance_stoch_all
  have htel :=
    corrected_epoch_telescope_of_error_sum_bound
      (fun j => expectedPsi SR (epochIndex SR s j))
      (fun j => expectedExactGradientMappingSq SR (epochIndex SR s j))
      (fun j => expectedStochasticGradientMappingSq SR (epochIndex SR s j))
      (fun j => expectedEstimatorErrorSq SR (epochIndex SR s j))
      (1 / (8 * S.L)) (1 / (4 * S.L)) (17 / (4 * S.L))
      (17 * ((t : ℝ) - 1) / (4 * S.L * (SR.batchSize : ℝ)))
      t ht_pos hstep herror
  have hbatch_real : (SR.batchSize : ℝ) = 17 * (SR.T : ℝ) := by
    exact_mod_cast hbatch
  have hT_pos : 0 < (SR.T : ℝ) := by
    exact_mod_cast SR.T_pos
  have ht_le_real : (t : ℝ) ≤ (SR.T : ℝ) := by
    exact_mod_cast ht_epoch
  have hcoeff_eq :
      1 / (4 * S.L) -
          17 * ((t : ℝ) - 1) / (4 * S.L * (SR.batchSize : ℝ)) =
        ((SR.T : ℝ) - (t : ℝ) + 1) / (4 * S.L * (SR.T : ℝ)) := by
    rw [hbatch_real]
    field_simp [hL_pos.ne', hT_pos.ne']
    ring
  have hcoeff_nonneg :
      0 ≤ 1 / (4 * S.L) -
          17 * ((t : ℝ) - 1) / (4 * S.L * (SR.batchSize : ℝ)) := by
    rw [hcoeff_eq]
    have hnum_nonneg : 0 ≤ (SR.T : ℝ) - (t : ℝ) + 1 := by
      linarith
    have hden_pos : 0 < 4 * S.L * (SR.T : ℝ) := by positivity
    exact div_nonneg hnum_nonneg (le_of_lt hden_pos)
  have hGsum_nonneg :
      0 ≤ Finset.sum (Finset.Icc 1 t)
        (fun j => expectedStochasticGradientMappingSq SR (epochIndex SR s j)) := by
    exact Finset.sum_nonneg
      (fun j _hj => expectedStochasticGradientMappingSq_nonneg (SR := SR) (epochIndex SR s j))
  have hres_nonneg :
      0 ≤ (1 / (4 * S.L) -
          17 * ((t : ℝ) - 1) / (4 * S.L * (SR.batchSize : ℝ))) *
        Finset.sum (Finset.Icc 1 t)
          (fun j => expectedStochasticGradientMappingSq SR (epochIndex SR s j)) := by
    exact mul_nonneg hcoeff_nonneg hGsum_nonneg
  linarith

/-- Final epoch-to-global summation step of Theorem 6.14, from Eq. (6.5.13) to
Eq. (6.5.8). -/
private theorem theorem_6_14_global_descent_from_epoch_descent
    (hEpoch :
      ∀ s t : ℕ, 1 ≤ t → t ≤ SR.T →
        expectedPsi SR (epochIndex SR s (t + 1)) +
            (1 / (8 * S.L)) *
              Finset.sum (Finset.Icc 1 t)
                (fun j => expectedExactGradientMappingSq SR (epochIndex SR s j))
          ≤ expectedPsi SR (epochIndex SR s 1)) :
    ∀ k : ℕ, 1 ≤ k →
      expectedPsi SR (k + 1) +
          (1 / (8 * S.L)) *
            Finset.sum (Finset.Icc 1 k) (fun j => expectedExactGradientMappingSq SR j)
        ≤ Setup.psi S SR.x₁.1 := by
  classical
  letI : IsProbabilityMeasure SR.P := SR.P_isProbability
  have hinitial : expectedPsi SR 1 ≤ Setup.psi S SR.x₁.1 := by
    rw [expectedPsi_one_eq_initial (SR := SR)]
  exact
    _root_.global_prefix_descent_of_epoch_descent
      (T := SR.T)
      (V := fun k => expectedPsi SR k)
      (G := fun k => expectedExactGradientMappingSq SR k)
      (initial := Setup.psi S SR.x₁.1)
      (c := 1 / (8 * S.L))
      SR.T_pos
      hinitial
      (by
        intro s t ht_pos ht_epoch
        simpa [epochIndex, SOptLib.global_index_def] using
          hEpoch s t ht_pos ht_epoch)

/-- Theorem 6.14 expected descent obligation, matching Eq. (6.5.8).

This is the source-granularity replacement for the retired deterministic
pathwise descent helper: the estimator cancellation used by Lemma 6.10 is
available only through `StochasticRun.sample_law` and `sample_iIndep`. -/
private theorem theorem_6_14_expected_descent_obligation
    (hQ : SR.Q = Setup.importancePMF S)
    (hgamma : SR.gamma = 1 / S.L) (hbatch : SR.batchSize = 17 * SR.T) :
    ∀ k : ℕ, 1 ≤ k →
      expectedPsi SR (k + 1) +
          (1 / (8 * S.L)) *
            Finset.sum (Finset.Icc 1 k) (fun j => expectedExactGradientMappingSq SR j)
        ≤ Setup.psi S SR.x₁.1 := by
  classical
  letI : IsProbabilityMeasure SR.P := SR.P_isProbability
  have hsamples_law := SR.sample_law
  have hsamples_iIndep := SR.sample_iIndep
  have hvariance :
      ∀ s t : ℕ, 1 ≤ t → t ≤ SR.T →
        expectedEstimatorErrorSq SR (epochIndex SR s t) ≤
          (S.L ^ 2 / (SR.batchSize : ℝ)) *
            Finset.sum (Finset.Icc 2 t)
              (fun i => expectedDisplacementSq SR (epochIndex SR s i)) := by
    intro s t ht_pos ht_epoch
    exact
      lemma_6_10_epochwise_estimator_variance_bound SR
        hQ hsamples_law hsamples_iIndep s t ht_pos ht_epoch
  have honeStep :
      ∀ (k : PositiveIteration),
        expectedPsi SR (k.1 + 1) +
            (1 / (8 * S.L)) * expectedExactGradientMappingSq SR k.1 ≤
          expectedPsi SR k.1 -
            (1 / (4 * S.L)) *
              expectedStochasticGradientMappingSq SR k.1 +
            (17 / (4 * S.L)) * expectedEstimatorErrorSq SR k.1 := by
    intro k
    exact theorem_6_14_one_step_expected_descent_at_paper_constants
      (SR := SR) hgamma k
  have hEpoch :
      ∀ s t : ℕ, 1 ≤ t → t ≤ SR.T →
        expectedPsi SR (epochIndex SR s (t + 1)) +
            (1 / (8 * S.L)) *
              Finset.sum (Finset.Icc 1 t)
                (fun j => expectedExactGradientMappingSq SR (epochIndex SR s j))
          ≤ expectedPsi SR (epochIndex SR s 1) := by
    intro s t ht_pos ht_epoch
    exact theorem_6_14_epoch_descent SR hgamma hbatch hvariance honeStep
      s t ht_pos ht_epoch
  exact theorem_6_14_global_descent_from_epoch_descent SR hEpoch

/-- Corrected Theorem 6.14 epoch supplier obtained from the stochastic process
assumptions, the q-loss one-step bridge, and Lemma 6.10.

This is the active source-consistent replacement route for the public theorem
chain.  It intentionally returns the residual epoch inequality rather than the
printed Eq. (6.5.13), because the coefficient obstruction above prevents the
residual term from being dropped under the paper constants. -/
theorem theorem_6_14_corrected_expected_descent_obligation
    (hQ : SR.Q = Setup.importancePMF S)
    (hgamma : SR.gamma = 1 / S.L) (hbatch : SR.batchSize = 17 * SR.T) :
    ∀ s t : ℕ, 1 ≤ t → t ≤ SR.T →
      expectedPsi SR (epochIndex SR s (t + 1)) +
          (1 / (8 * S.L)) *
            Finset.sum (Finset.Icc 1 t)
              (fun j => expectedExactGradientMappingSq SR (epochIndex SR s j))
        ≤ expectedPsi SR (epochIndex SR s 1) -
          (3 / (16 * S.L) -
            17 * ((t : ℝ) - 1) / (4 * S.L * (SR.batchSize : ℝ))) *
              Finset.sum (Finset.Icc 1 t)
                (fun j => expectedStochasticGradientMappingSq SR (epochIndex SR s j)) := by
  classical
  letI : IsProbabilityMeasure SR.P := SR.P_isProbability
  have hsamples_law := SR.sample_law
  have hsamples_iIndep := SR.sample_iIndep
  have hvariance :
      ∀ s t : ℕ, 1 ≤ t → t ≤ SR.T →
        expectedEstimatorErrorSq SR (epochIndex SR s t) ≤
          (S.L ^ 2 / (SR.batchSize : ℝ)) *
            Finset.sum (Finset.Icc 2 t)
              (fun i => expectedDisplacementSq SR (epochIndex SR s i)) := by
    intro s t ht_pos ht_epoch
    exact
      lemma_6_10_epochwise_estimator_variance_bound SR
        hQ hsamples_law hsamples_iIndep s t ht_pos ht_epoch
  have honeStep :
      ∀ (k : PositiveIteration) (p q : ℝ), 0 < p → 0 < q →
        expectedPsi SR (k.1 + 1) + p * expectedExactGradientMappingSq SR k.1 ≤
          expectedPsi SR k.1 -
            (SR.gamma * (1 - S.L * SR.gamma / 2 - q / 2) - 2 * p) *
              expectedStochasticGradientMappingSq SR k.1 +
            (SR.gamma / (2 * q) + 2 * p) * expectedEstimatorErrorSq SR k.1 := by
    intro k p q hp hq
    exact theorem_6_14_one_step_expected_descent (SR := SR) hgamma k p q hp hq
  intro s t ht_pos ht_epoch
  exact theorem_6_14_corrected_epoch_descent SR hgamma hbatch hvariance honeStep
    s t ht_pos ht_epoch

/-- Corrected theorem-level boundary for Theorem 6.14.

This packages the source-consistent q-loss residual epoch inequality together
with the compiled obstruction to the printed coefficient drop.  It is separate
from the canonical printed theorem name because the obstruction certifies the
paper proof route's coefficient failure, not a full feasible counterexample to
the printed theorem statement. -/
theorem theorem_6_14_corrected_iteration_bound
    (hQ : SR.Q = Setup.importancePMF S)
    (hgamma : SR.gamma = 1 / S.L) (hbatch : SR.batchSize = 17 * SR.T) :
    (∀ s t : ℕ, 1 ≤ t → t ≤ SR.T →
      expectedPsi SR (epochIndex SR s (t + 1)) +
          (1 / (8 * S.L)) *
            Finset.sum (Finset.Icc 1 t)
              (fun j => expectedExactGradientMappingSq SR (epochIndex SR s j))
        ≤ expectedPsi SR (epochIndex SR s 1) -
          (3 / (16 * S.L) -
            17 * ((t : ℝ) - 1) / (4 * S.L * (SR.batchSize : ℝ))) *
              Finset.sum (Finset.Icc 1 t)
                (fun j => expectedStochasticGradientMappingSq SR (epochIndex SR s j))) ∧
      (4 ≤ SR.T →
        ¬ 0 <
          3 / (16 * S.L) -
            17 * ((SR.T : ℝ) - 1) / (4 * S.L * (SR.batchSize : ℝ))) := by
  constructor
  · exact theorem_6_14_corrected_expected_descent_obligation SR hQ hgamma hbatch
  · intro hT_large
    exact theorem_6_14_printed_epoch_drop_incompatible_with_corrected_q_loss
      (SR := SR) hbatch hT_large

/-- Randomized-output consequence of Eq. (6.5.8), matching Eq. (6.5.9).

The source proof sets `k=N`, expands the uniform output law over `{1,...,N}`,
and uses `Ψ(x_{N+1}) ≥ Ψ*`. -/
theorem randomized_output_bound_from_expected_descent
    (hdescent :
      ∀ k : ℕ, 1 ≤ k →
        expectedPsi SR (k + 1) +
            (1 / (8 * S.L)) *
              Finset.sum (Finset.Icc 1 k) (fun j => expectedExactGradientMappingSq SR j)
          ≤ Setup.psi S SR.x₁.1) :
    expectedOutputExactGradientMappingSq SR
      ≤ (8 * S.L / SR.horizon) * (Setup.psi S SR.x₁.1 - Setup.psiStar S) := by
  classical
  letI : IsProbabilityMeasure SR.P := SR.P_isProbability
  haveI : SFinite SR.P := inferInstance
  have hlower_path :
      ∀ ω : Ω, Setup.psiStar S ≤
        Setup.psi S (Run.iterate (pathRun SR ω) (SR.horizon + 1)).1 := by
    intro ω
    exact Setup.psiStar_le S _ (Run.iterate (pathRun SR ω) (SR.horizon + 1)).2
  have hterminal : Setup.psiStar S ≤ expectedPsi SR (SR.horizon + 1) := by
    have hpsi_int : Integrable
        (fun ω : Ω => Setup.psi S (Run.iterate (pathRun SR ω) (SR.horizon + 1)).1)
        SR.P := by
      exact
        (SOptLib.expectationWellDefined_iff_integrable
          (μ := SR.P)
          (Z := fun ω : Ω =>
            Setup.psi S (Run.iterate (pathRun SR ω) (SR.horizon + 1)).1)).mp
          (expectedPsi_wellDefined SR (SR.horizon + 1))
    unfold expectedPsi SOptLib.expectation
    calc
      Setup.psiStar S = ∫ ω : Ω, Setup.psiStar S ∂SR.P := by
        simp
      _ ≤ ∫ ω : Ω,
            Setup.psi S (Run.iterate (pathRun SR ω) (SR.horizon + 1)).1 ∂SR.P := by
        refine integral_mono ?hconst hpsi_int ?hle
        · exact integrable_const _
        · exact fun ω => hlower_path ω
  have hout :
      expectedOutputExactGradientMappingSq SR =
        (SR.horizon : ℝ)⁻¹ *
          Finset.sum (Finset.Icc 1 SR.horizon)
            (fun j => expectedExactGradientMappingSq SR j) := by
    simpa [outputWindow, Finset.sum_const, smul_eq_mul] using
      (expectedOutputExactGradientMappingSq_eq_uniform_sum SR)
  have hL : 0 < S.L := Setup.L_pos S
  have hc_pos : 0 < 1 / (8 * S.L) := by
    positivity
  have hbound :=
    uniform_output_bound_of_expected_descent
      SR.horizon (1 / (8 * S.L)) (Setup.psi S SR.x₁.1) (Setup.psiStar S)
      (expectedOutputExactGradientMappingSq SR) (expectedPsi SR)
      (fun j => expectedExactGradientMappingSq SR j)
      SR.horizon_pos hc_pos
      (hdescent SR.horizon (Nat.succ_le_of_lt SR.horizon_pos))
      hterminal hout
  simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hbound

/-- Theorem 6.14 source-facing expected descent and randomized-output bound.

The canonical theorem name is kept for the printed paper statement, Eq.
(6.5.8) and Eq. (6.5.9).  The q-loss corrected residual route is recorded
separately in `theorem_6_14_corrected_expected_descent_obligation`; it is not
used here as a replacement for the printed theorem without a full source
correction/falsity protocol. -/
theorem theorem_6_14_iteration_bound
    (hQ : SR.Q = Setup.importancePMF S)
    (hgamma : SR.gamma = 1 / S.L) (hbatch : SR.batchSize = 17 * SR.T) :
    (∀ k : ℕ, 1 ≤ k →
      expectedPsi SR (k + 1) +
          (1 / (8 * S.L)) *
            Finset.sum (Finset.Icc 1 k) (fun j => expectedExactGradientMappingSq SR j)
        ≤ Setup.psi S SR.x₁.1) ∧
      expectedOutputExactGradientMappingSq SR
        ≤ (8 * S.L / SR.horizon) * (Setup.psi S SR.x₁.1 - Setup.psiStar S) := by
  have hdescent := theorem_6_14_expected_descent_obligation SR hQ hgamma hbatch
  constructor
  · exact hdescent
  · exact randomized_output_bound_from_expected_descent SR hdescent

/-- Component-gradient evaluation count for the stochastic Algorithm 6.6 run. -/
noncomputable def componentGradientEvaluationCount : ℕ :=
  SOptLib.singlePhaseEpochCallCount (Fintype.card ι) SR.batchSize SR.T SR.horizon

/-- Corollary 6.20 rate envelope
`m + T L [Ψ(x₁)-Ψ*] / ε`, specialized by the theorem assumption `T=√m`. -/
noncomputable def corollary620Rate (epsilon : ℝ) : ℝ :=
  (Fintype.card ι : ℝ) +
    (SR.T : ℝ) * S.L * (Setup.psi S SR.x₁.1 - Setup.psiStar S) / epsilon

/-- Corollary 6.20 source rate
`m + √m L [Ψ(x₁)-Ψ*] / ε`.

No SOptLib candidate represented the paper's epsilon-solution rate expression
itself; this local definition records the literal Corollary 6.20 bound. -/
noncomputable def corollary620SourceRate (epsilon : ℝ) : ℝ :=
  (Fintype.card ι : ℝ) +
    Real.sqrt (Fintype.card ι : ℝ) *
      S.L * (Setup.psi S SR.x₁.1 - Setup.psiStar S) / epsilon

/-- Real iteration budget chosen in the proof of Corollary 6.20:
`N = 8L[Ψ(x₁)-Ψ*]/ε`.

This is the source expression before any Lean natural-number rounding or
positive-horizon totalization. -/
noncomputable def corollary620RealIterationBudget (epsilon : ℝ) : ℝ :=
  (8 * S.L * (Setup.psi S SR.x₁.1 - Setup.psiStar S)) / epsilon

/-- Positive natural horizon realizing the Corollary 6.20 budget for Lean runs.

SOptLib positive-ceiling candidates such as `le_positive_ceil_max_one` were
considered as proof bridges, but this local definition is needed because the
paper-facing source object is the real budget `8L[Ψ(x₁)-Ψ*]/ε`; `max 1` is only
the executable positive-output support required by Algorithm 6.6's uniform
selection from `{1,...,N}`. -/
noncomputable def corollary620IterationHorizon (epsilon : ℝ) : ℕ :=
  max 1 (Nat.ceil (corollary620RealIterationBudget SR epsilon))

/-- The executable Corollary 6.20 horizon is positive. -/
theorem corollary620IterationHorizon_pos (epsilon : ℝ) :
    0 < corollary620IterationHorizon SR epsilon := by
  unfold corollary620IterationHorizon
  exact Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 _)

/-- Exact stopped component-gradient evaluation count used in the proof of
Corollary 6.20.

This specializes SOptLib `singlePhaseEpochCallCount` to the source proof formula
`(m+bT)⌈N/T⌉=(m+17T^2)⌈N/T⌉`, with `N` realized by the positive rounded
Corollary 6.20 budget rather than by an arbitrary longer ambient run horizon. -/
noncomputable def corollary620StoppedGradientEvaluationCount (epsilon : ℝ) : ℕ :=
  SOptLib.singlePhaseEpochCallCount
    (Fintype.card ι) (17 * SR.T) SR.T (corollary620IterationHorizon SR epsilon)

@[simp]
theorem corollary620StoppedGradientEvaluationCount_def (epsilon : ℝ) :
    corollary620StoppedGradientEvaluationCount SR epsilon =
      SOptLib.singlePhaseEpochCallCount
        (Fintype.card ι) (17 * SR.T) SR.T (corollary620IterationHorizon SR epsilon) := by
  rfl

/-- The stopped Corollary 6.20 count agrees with the generated run count when the
run is actually stopped at the Corollary 6.20 horizon and uses `b=17T`. -/
theorem componentGradientEvaluationCount_eq_corollary620Stopped
    (epsilon : ℝ)
    (hbatch : SR.batchSize = 17 * SR.T)
    (hhorizon : SR.horizon = corollary620IterationHorizon SR epsilon) :
    componentGradientEvaluationCount SR =
      corollary620StoppedGradientEvaluationCount SR epsilon := by
  simp [componentGradientEvaluationCount, corollary620StoppedGradientEvaluationCount,
    hbatch, hhorizon]

/-- Concrete universal envelope for the Corollary 6.20 Big-O display.

The coefficient is source-derived from the proof count
`(m+17T^2)⌈N/T⌉` and the choice
`N=8L[Ψ(x₁)-Ψ*]/ε`: with `T=√m`, the leading accuracy term contributes the
constant `18 * 8 = 144`.  The proof obligation below justifies the rounding and
positive-horizon slack; no theorem-local or per-instance Big-O constant is used. -/
noncomputable def corollary620GradientEvaluationEnvelope (epsilon : ℝ) : ℝ :=
  144 * corollary620SourceRate SR epsilon

/-- The stochastic output of Algorithm 6.6 is an `ε`-solution in the Corollary 6.20
sense when the expected squared generalized projected-gradient mapping is at most
`ε`. -/
def corollary620EpsilonSolution (epsilon : ℝ) : Prop :=
  expectedOutputExactGradientMappingSq SR ≤ epsilon

/-- Paper-facing theorem obligation for Corollary 6.20 with `T=√m`.

The conclusion includes the paper's epsilon-solution guarantee and a concrete
big-O-style gradient-evaluation envelope against the source rate expression.
The horizon assumption is the paper's stopped-budget choice, not a lower bound
that would allow the counted run to continue beyond the source proof's `N`. -/
theorem corollary_6_20_complexity
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hQ : SR.Q = Setup.importancePMF S)
    (hgamma : SR.gamma = 1 / S.L)
    (hbatch : SR.batchSize = 17 * SR.T)
    (hhorizon : SR.horizon = corollary620IterationHorizon SR epsilon)
    (hT : (SR.T : ℝ) ^ 2 = (Fintype.card ι : ℝ)) :
    corollary620EpsilonSolution SR epsilon ∧
      (componentGradientEvaluationCount SR : ℝ) ≤
        corollary620GradientEvaluationEnvelope SR epsilon := by
  have hmain := theorem_6_14_iteration_bound SR hQ hgamma hbatch
  constructor
  · unfold corollary620EpsilonSolution
    have hout := hmain.2
    rw [hhorizon] at hout
    have hgap_nonneg :
        0 ≤ Setup.psi S SR.x₁.1 - Setup.psiStar S := by
      have hstar := Setup.psiStar_le S SR.x₁.1 SR.x₁.2
      linarith
    have hrhs_le :
        (8 * S.L / (corollary620IterationHorizon SR epsilon : ℝ)) *
            (Setup.psi S SR.x₁.1 - Setup.psiStar S) ≤ epsilon := by
      have h :=
        div_natCast_max_one_ceil_div_le
          (8 * S.L * (Setup.psi S SR.x₁.1 - Setup.psiStar S)) epsilon hepsilon
      unfold corollary620IterationHorizon corollary620RealIterationBudget
      rw [div_mul_eq_mul_div]
      exact h
    exact le_trans hout hrhs_le
  · -- Remaining local leaf: specialize the stopped run count
    -- `(m + 17T^2)⌈N/T⌉` under `T = sqrt m` and bound the ceiling slack by the
    -- explicit envelope `144 * (m + sqrt(m)L[Ψ(x₁)-Ψ*]/ε)`.
    have hgap_nonneg :
        0 ≤ Setup.psi S SR.x₁.1 - Setup.psiStar S := by
      have hstar := Setup.psiStar_le S SR.x₁.1 SR.x₁.2
      linarith
    have hL_pos : 0 < S.L := Setup.L_pos S
    have hT_real_pos : 0 < (SR.T : ℝ) := by
      exact_mod_cast SR.T_pos
    have hT_real_ge_one : 1 ≤ (SR.T : ℝ) := by
      exact_mod_cast SR.T_pos
    have hsqrt_card :
        Real.sqrt (Fintype.card ι : ℝ) = (SR.T : ℝ) := by
      rw [← hT]
      exact Real.sqrt_sq (Nat.cast_nonneg SR.T)
    have hcount :
        (componentGradientEvaluationCount SR : ℝ) ≤
          (((17 : ℕ) : ℝ) + 1) * (Fintype.card ι : ℝ) *
            ((corollary620IterationHorizon SR epsilon : ℝ) /
                Real.sqrt (Fintype.card ι : ℝ) + 1) := by
      rw [componentGradientEvaluationCount, hbatch, hhorizon]
      simpa using
        (SOptLib.epoch_call_count_le_sqrt_bound_of_epoch_sq_eq_refresh
          (iterations := corollary620IterationHorizon SR epsilon)
          (refreshCalls := Fintype.card ι)
          (epochLength := SR.T)
          (ratio := 17)
          hT)
    have hbudget_nonneg :
        0 ≤ corollary620RealIterationBudget SR epsilon := by
      unfold corollary620RealIterationBudget
      positivity
    have hN_upper :
        (corollary620IterationHorizon SR epsilon : ℝ) ≤
          corollary620RealIterationBudget SR epsilon + 2 := by
      simpa [corollary620IterationHorizon] using
        natCast_max_one_ceil_le_add_two
          (corollary620RealIterationBudget SR epsilon) hbudget_nonneg
    have hN_eps_upper :
        (corollary620IterationHorizon SR epsilon : ℝ) * epsilon ≤
          8 * S.L * (Setup.psi S SR.x₁.1 - Setup.psiStar S) + 2 * epsilon := by
      have hmul := mul_le_mul_of_nonneg_right hN_upper (le_of_lt hepsilon)
      unfold corollary620RealIterationBudget at hmul
      field_simp [hepsilon.ne'] at hmul
      nlinarith
    have heps_le_Teps : epsilon ≤ (SR.T : ℝ) * epsilon := by
      simpa using
        (mul_le_mul_of_nonneg_right hT_real_ge_one (le_of_lt hepsilon))
    have hscalar :
        (((17 : ℕ) : ℝ) + 1) * (Fintype.card ι : ℝ) *
            ((corollary620IterationHorizon SR epsilon : ℝ) /
                Real.sqrt (Fintype.card ι : ℝ) + 1) ≤
          corollary620GradientEvaluationEnvelope SR epsilon := by
      unfold corollary620GradientEvaluationEnvelope corollary620SourceRate
        corollary620RealIterationBudget at *
      rw [hsqrt_card, ← hT]
      field_simp [hT_real_pos.ne', hepsilon.ne']
      ring_nf
      nlinarith [hN_eps_upper, heps_le_Teps]
    exact le_trans hcount hscalar

end StochasticRun

end SGD.NonconvexVarianceReducedMirrorDescent
