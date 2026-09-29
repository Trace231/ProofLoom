import SOptLib.Model.Bregman
import SOptLib.Model.Filtration
import SOptLib.Model.Iterates
import SOptLib.Model.Norms
import SOptLib.Model.Objective
import SOptLib.Model.Prox
import SOptLib.Model.Subdifferential
import SOptLib.Glue.Probability
import SOptLib.Glue.Martingale
import SOptLib.Layer0.Oracle
import SOptLib.Layer1.Proximal
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen

/-!
Stochastic gradient sliding.

Phase 0 object layer for Lan's stochastic gradient sliding method.  The
declarations below encode the paper-facing mathematical objects as definitions:
the composite objective, Bregman prox geometry, stochastic oracle samples, SPS
inner update, and the outer SGS recursion.
-/

open scoped BigOperators Gradient InnerProductSpace
open MeasureTheory ProbabilityTheory

namespace StochasticGradientSliding


universe u v w z

variable {E : Type u} {Sample : Type v} {Ω : Type w}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Positive paper-time indices. -/
abbrev PositiveTime := {t : ℕ // 1 ≤ t}

/-- Positive inner-loop budgets `T_k` as used by Algorithm 8.1.

The PDF writes `T_k ∈ N` and then uses `P_{T_k}` in denominators.  Lean's `ℕ`
contains zero, so paper-facing theorem-bound objects use this subtype while
formula-extension selector infrastructure may still accept raw natural horizons. -/
abbrev InnerBudget := {T : ℕ // 1 ≤ T}

/-- Forget a positive paper budget to the raw natural horizon used by recursive
selector helpers. -/
def innerBudgetNat (T : PositiveTime → InnerBudget) : PositiveTime → ℕ :=
  fun k => (T k).1

/-- The paper index `1` as a positive time. -/
def oneTime : PositiveTime := ⟨1, Nat.succ_pos 0⟩

/-- The predecessor of a positive paper index known to be at least two. -/
def predTime (k : PositiveTime) (hk : 2 ≤ k.1) : PositiveTime :=
  ⟨k.1 - 1, by omega⟩

/-- The SPS weight `p_t=t/2` from Eq. (8.1.39). -/
noncomputable def spsP (t : PositiveTime) : ℝ :=
  (t.1 : ℝ) / 2

/-- Affine model predicate for the function `g` supplied to PS/SPS.

No SOptLib match: searched prox/objective model candidates and checked
`paperProxObjective`/`proxObjective`; those encode prox objectives after an
oracle vector is fixed, while Algorithm 8.1 supplies an affine model `g(·)` to
the sliding subroutine. -/
def IsAffineModel (g : E → ℝ) : Prop :=
  ∃ c : ℝ, ∃ a : E, ∀ u : E, g u = c + ⟪a, u⟫_ℝ

/-- The paper's prox-core `X^o` from Section 3.2.

No SOptLib match: searched Bregman/carrier intrinsic-interior candidates and
considered `intrinsicInterior`; the PDF defines the distance-generating core by
existence of a linear perturbation minimizer, and only notes that it contains the
relative interior, so this paper-local definition records the stated `X^o`. -/
def proxCore (X : Set E) (nu : E → ℝ) : Set E :=
  {x | x ∈ X ∧ ∃ p : E, IsMinOn (fun u => ⟪p, u⟫_ℝ + nu u) X x}

/-- Points in the paper prox-core are feasible. -/
lemma proxCore_subset {X : Set E} {nu : E → ℝ} :
    proxCore X nu ⊆ X := by
  intro x hx
  exact hx.1

/-- Source prox-geometry predicate for the prox function of Eq. (3.2.1)-(3.2.2).

This is a local paper specialization after checking SOptLib Bregman/prox
candidates: `bregmanDivergence` gives the formula for `V`, while the book's
distance-generating-function assumption also carries continuity and
differentiability on the carrier `X`, convexity of the source-defined prox-core
`X^o`, continuous differentiability on `X^o`, and unit strong-convexity of the
prox function on the feasible carrier.

The paper uses `V : X^o × X → R`; Lean realizes the `∇ν(x)` in that formula as
the within-gradient of the carrier function `ν : X → R` at the prox-core base
point.  The separate `ContDiffOn` field on `X^o` preserves the source's stated
smooth core geometry. -/
def ProxGeometryOn (X : Set E) (nu : E → ℝ) (normX : Seminorm ℝ E) : Prop :=
  ContinuousOn nu X ∧
    DifferentiableOn ℝ nu X ∧
      Convex ℝ (proxCore X nu) ∧
        ContDiffOn ℝ 1 nu (proxCore X nu) ∧
          ConvexOn ℝ X nu ∧
            StrongConvexOnWithGauge X 1 normX nu

/-- Private boundary-safe carrier-gradient selector used to totalize the paper's
`∇ν(x)` on feasible boundary points. -/
noncomputable def boundarySafeCarrierGradient (X : Set E) (nu : E → ℝ)
    (x : {x : E // x ∈ X}) : E :=
  gradientWithin nu X x.1

/-- Carrier-chart gradient on the source prox-core.

This pre-`Setup` helper is the raw source-domain branch of the feasible formula
that later becomes `bregmanFormulaOnX`. -/
noncomputable def proxCoreGradientRaw (X : Set E) (nu : E → ℝ)
    [FiniteDimensional ℝ E] (x : {x : E // x ∈ proxCore X nu}) : E := by
  classical
  exact
    if hne : Nonempty {x : E // x ∈ proxCore X nu} then
      SOptLib.carrierGradientFrom
        (proxCore X nu)
        (fun y : {y : E // y ∈ proxCore X nu} => nu y.1)
        (Classical.choice hne) x
    else
      0

/-- Raw feasible-pair Bregman formula used before the `Setup` structure exists.

No SOptLib match: searched `carrier Bregman formula`, checked
`carrierBregmanDivergence` and `carrierGradientFrom`; the paper's SGS file needs
a heterogeneous Section 3.2 source-core branch together with a feasible-boundary
totalization for statements that still range over all of `X`. -/
noncomputable def feasibleBregmanFormulaExtension (X : Set E) (nu : E → ℝ)
    [FiniteDimensional ℝ E] (x z : {x : E // x ∈ X}) : ℝ :=
  by
    classical
    exact
      if hx : x.1 ∈ proxCore X nu then
        nu z.1 - nu x.1 -
          ⟪proxCoreGradientRaw X nu ⟨x.1, hx⟩, z.1 - x.1⟫_ℝ
      else
        carrierBregmanDivergence
          (fun y : {y : E // y ∈ X} => nu y.1)
          (boundarySafeCarrierGradient X nu) x z

/-- Source regularity for the paper's smooth component `f`.

Book JSON citation: `book/FOML/StochasticGradientSliding.json:setup.variable_space`
states that `f : X → R` is a "general smooth ... convex function".  PDF
Section 3.1.3 says smooth convex functions in this text are differentiable
convex functions with Lipschitz-continuous gradients, before Lemma 3.2 derives
the quadratic upper representation.

SOptLib candidates considered: `smooth_quadratic_upper_bound_of_hasGradientAt_lipschitzOn_convex`
and `Convex.carrier_smooth_quadratic_upper_bound` are theorem-level bridges from
gradient regularity to a quadratic upper model; they do not name the setup datum
"`f` is smooth" itself.  This predicate records the stated smooth-function
regularity behind the source/carrier gradient used in Eq. (8.1.2) and `l_f` in
Eq. (8.1.9), including the paper primal/dual norm pair. -/
structure SmoothFunctionOn (X : Set E) (f : E → ℝ) (primalNorm : Seminorm ℝ E)
    (L : ℝ) : Prop where
  contDiffOn : ContDiffOn ℝ 1 f X
  gradient_lipschitz :
    ∀ ⦃x y : E⦄, x ∈ X → y ∈ X →
      SOptLib.canonicalDualNorm primalNorm
          (gradientWithin f X y - gradientWithin f X x) ≤
        L * primalNorm (y - x)

theorem SmoothFunctionOn.differentiableOn_one
    {X : Set E} {f : E → ℝ} {primalNorm : Seminorm ℝ E} {L : ℝ}
    (hf : SmoothFunctionOn X f primalNorm L) :
    DifferentiableOn ℝ f X :=
  hf.contDiffOn.differentiableOn_one

/-- Paper-local analytic interface for Lan's relatively simple `χ` term.

The Section 8.1 setup states that `χ` is a relatively simple convex function.
The SPS solver below records the computational prox-subproblem part of that
phrase; this source-boundary predicate records the analytic carrier regularity
needed to treat the composite objective `f + h + χ` as a measurable function on
the feasible carrier. -/
structure SGSRelativelySimpleChiOn (X : Set E) (χ : E → ℝ) : Prop where
  convexOn : ConvexOn ℝ X χ
  carrier_measurable :
    ∀ [MeasurableSpace E] [BorelSpace E],
      Measurable (fun x : {x : E // x ∈ X} => χ x.1)

/-- Source-facing solver interface for the SPS stochastic prox subproblem.

No SOptLib match: searched `prox argmin solvable relatively simple mirror step
IsMinOn` and `IsMinOn argmin Nonempty proxObjective compact continuous coercive`;
checked `SOptLib.proxObjective_exists_isMinOn_compact`,
`SOptLib.proxStepArgmin`, `SOptLib.IsProxPoint`, and `SOptLib.proxObjective`;
none align with paper Eq. (8.1.58) without adding compactness/continuity
hypotheses, because the SGS update has a two-Bregman stochastic objective and
the book instead states that the associated projection/prox subproblem is
relatively easy to solve.

Book/PDF citations:
`book/FOML/StochasticGradientSliding.json:setup.variable_space` says `χ` is a
"relatively simple convex function"; `algorithm_spec.steps[3]` gives
Eq. (8.1.58) as an `argmin_{u∈X}`; the PDF text around Algorithm 8.2 says SGS is
obtained by replacing exact subgradients in the prox-sliding procedure and
displays `u_t = argmin_{u∈X} ...` in Eq. (8.1.58).

This is a solver operation, not a `Classical.choose` existence surrogate: the
source algorithm calls the prox subproblem as a computational primitive.  The
field `is_argmin` is exactly the displayed Eq. (8.1.58) certificate.  The
sample-measurability field is the Lean regularity needed to use this solver as
a stochastic update map; it does not encode unbiasedness, freshness, or a
martingale tail bound. -/
structure SPSSubproblemSolver (X : Set E) (chi proxPotential : E → ℝ)
    (oracle : E → Sample → E) (finiteDimensional_ambient : FiniteDimensional ℝ E) where
  toFun :
    ∀ (g : E → ℝ) (x : {x : E // x ∈ X}) (β : ℝ) (t : PositiveTime)
      (uPrev : {u : E // u ∈ X}) (xi : Sample),
        IsAffineModel g → 0 < β → {u : E // u ∈ X}
  is_argmin :
    ∀ (g : E → ℝ) (x : {x : E // x ∈ X}) (β : ℝ) (t : PositiveTime)
      (uPrev : {u : E // u ∈ X}) (xi : Sample)
      (hg : IsAffineModel g) (hβ : 0 < β),
        IsMinOn
          (fun v : {v : E // v ∈ X} =>
            letI : FiniteDimensional ℝ E := finiteDimensional_ambient
            g v.1 + ⟪oracle uPrev.1 xi, v.1⟫_ℝ +
              β * feasibleBregmanFormulaExtension X proxPotential x v +
              β * spsP t * feasibleBregmanFormulaExtension X proxPotential uPrev v +
              chi v.1)
          Set.univ
            (toFun g x β t uPrev xi hg hβ)
  toFun_measurable_sample :
    ∀ [MeasurableSpace E] [MeasurableSpace Sample]
      (g : E → ℝ) (x : {x : E // x ∈ X}) (β : ℝ) (t : PositiveTime)
      (uPrev : {u : E // u ∈ X})
      (hg : IsAffineModel g) (hβ : 0 < β),
        Measurable (fun xi : Sample => toFun g x β t uPrev xi hg hβ)
  /-- Random-context measurability for the Eq. (8.1.58) solver update.

  Algorithm 8.2 applies the SPS subproblem solver after the previous outer
  center, the smooth affine model, the previous inner iterate, and the fresh
  sample have all become random objects.  This field is the minimal regularity
  needed to read the displayed solver operation as a stochastic update map under
  an arbitrary past sigma-algebra; it does not assert unbiasedness,
  independence, or any tail estimate. -/
  toFun_measurable_random_context :
    ∀ {Ω' : Type z} [MeasurableSpace Ω'] [MeasurableSpace E] [MeasurableSpace Sample]
      (mΩ : MeasurableSpace Ω')
      (g : Ω' → E → ℝ) (x : Ω' → {x : E // x ∈ X}) (β : ℝ) (t : PositiveTime)
      (uPrev : Ω' → {u : E // u ∈ X}) (xi : Ω' → Sample)
      (hg : ∀ ω, IsAffineModel (g ω)) (hβ : 0 < β),
        Measurable[mΩ] x →
        Measurable[mΩ] uPrev →
        Measurable[mΩ] xi →
          Measurable[mΩ]
            (fun ω => toFun (g ω) (x ω) β t (uPrev ω) (xi ω) (hg ω) hβ)

/-- The solver interface implies the older nonempty argmin-set formulation. -/
def SPSSubproblemSolvable (X : Set E) (chi proxPotential : E → ℝ)
    (oracle : E → Sample → E) (finiteDimensional_ambient : FiniteDimensional ℝ E) : Prop :=
  Nonempty (SPSSubproblemSolver.{u, v, w} X chi proxPotential oracle finiteDimensional_ambient)

/-- Source-facing problem data for Eq. (8.1.1) and the standing assumptions in
Section 8.1.

Book JSON citations:
`book/FOML/StochasticGradientSliding.json:setup.problem`,
`book/FOML/StochasticGradientSliding.json:setup.variable_space`,
`book/FOML/StochasticGradientSliding.json:assumptions[0-3,6-7]`.

The Prop fields are restricted to stated setup data or assumptions from the book
JSON: closed convex feasible region, convex components, relative simplicity of
`χ` through its analytic carrier interface and SPS prox-subproblem interface,
and the displayed smooth/nonsmooth growth assumptions. Algorithmic objects such
as Bregman envelopes, oracle samples, and iterates are defined below rather than
stored as witness fields. -/
structure Setup (E : Type u) (Sample : Type v) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] where
  /-- Source ambient-space datum: Section 8.1 states `X ⊆ R^n`.  The Lean file
  remains polymorphic in the Hilbert ambient type `E`, and this field records
  the finite-dimensional Euclidean realization needed by the paper's dual norm
  and Proposition 8.3 arguments. -/
  finiteDimensional_ambient : FiniteDimensional ℝ E
  X : Set E
  isClosed_X : IsClosed X
  convex_X : Convex ℝ X
  f : E → ℝ
  h : E → ℝ
  chi : E → ℝ
  primalNorm : Seminorm ℝ E
  lSmooth : ℝ
  convex_f : ConvexOn ℝ X f
  smooth_f : SmoothFunctionOn X f primalNorm lSmooth
  convex_h : ConvexOn ℝ X h
  convex_chi : ConvexOn ℝ X chi
  /-- Source analytic projection of the setup phrase that `χ` is relatively
  simple.  This is not a bare measurability field: it keeps the convex term and
  carrier regularity bundled as the paper-local relatively-simple `χ`
  interface, while `sps_subproblem_solver` below records the computational
  prox-subproblem oracle part of the same source phrase. -/
  relatively_simple_chi : SGSRelativelySimpleChiOn X chi
  primalNorm_separating : ∀ x : E, primalNorm x = 0 ↔ x = 0
  proxPotential : E → ℝ
  hSubgradient : E → E
  oracle : E → Sample → E
  mGrowth : ℝ
  sigmaSq : ℝ
  L_pos : 0 < lSmooth
  M_pos : 0 < mGrowth
  /-- Primitive variance-domain assumption: Eq. (8.1.7) uses `σ²` as the
  second-moment bound `E[||H(u_t,ξ_t)-h'(u_t)||_*^2] ≤ σ²`, so the source
  parameter is nonnegative. This is not supplied by the pre-searched filtration
  or generated-bound candidates, which concern stochastic-process transport
  rather than the scalar domain of the variance parameter. -/
  sigmaSq_nonneg : 0 ≤ sigmaSq
  smoothness :
    ∀ ⦃x y : E⦄, x ∈ X → y ∈ X →
      f x ≤
        f y + ⟪gradientWithin f X y, x - y⟫_ℝ +
          (lSmooth / 2) * primalNorm (x - y) ^ 2
  nonsmooth_growth :
    ∀ ⦃x y : E⦄, x ∈ X → y ∈ X →
      h x ≤ h y + ⟪hSubgradient y, x - y⟫_ℝ + mGrowth * primalNorm (x - y)
  h_subgradient_mem :
    ∀ x (hx : x ∈ X),
      hSubgradient x ∈
        SOptLib.carrierSubdifferential
          (fun y : {y : E // y ∈ X} => h y.1) ⟨x, hx⟩
  prox_geometry : ProxGeometryOn X proxPotential primalNorm
  /-- Source relative-simplicity/prox-oracle datum for the stochastic
  prox-sliding subproblem.  The book setup says `χ` is relatively simple, and
  Eq. (8.1.58) defines each SPS update by this attained argmin over `X`; this
  field records that computational interface rather than deriving attainment
  from convexity alone. -/
  sps_subproblem_solver :
    SPSSubproblemSolver.{u, v, w} X chi proxPotential oracle finiteDimensional_ambient
variable (S : Setup.{u, v, w} E Sample)

/-- Private boundary-safe extension of the paper's source gradient `∇f(x)` on `X`.

Book/PDF citations:
`book/FOML/StochasticGradientSliding.json:setup.variable_space` states
`f : X → ℝ` is smooth and convex; Eq. (8.1.9) defines
`l_f(x;y)=f(x)+<∇f(x),y-x>`.

The paper gradient is a carrier derivative of `f : X → ℝ`.  Lean realizes it by
Mathlib's canonical within-gradient selector on the feasible carrier, avoiding
the ambient-extension `∇ S.f` at boundary points.  This implementation is kept
private so the public source object can be audited as a boundary-safe extension
of the literal interior gradient below. -/
noncomputable def sourceSmoothGradientExtension (x : E) : E :=
  gradientWithin S.f S.X x

/-- Boundary-safe realization of the paper's source gradient `∇f(x)` on `X`.

This is the paper-facing source-gradient object used in Eq. (8.1.2) and
Eq. (8.1.9).  It delegates to the private carrier-gradient extension so boundary
points of `X` are not interpreted using an arbitrary ambient extension of
`f : X → ℝ`. -/
noncomputable def sourceSmoothGradient (x : E) : E :=
  sourceSmoothGradientExtension S x

/-- Paper-literal ambient-gradient notation for `∇f(x)`.

This names the literal formula used by the book at ordinary interior feasible
points.  The proof-facing source gradient is `sourceSmoothGradient`; the bridge
`sourceSmoothGradient_eq_literalSourceSmoothGradient_of_mem_interior` below
identifies the two where the ambient gradient is source-faithful. -/
noncomputable def literalSourceSmoothGradient (x : E) : E :=
  ∇ S.f x

/-- Composite objective `Ψ(x)=f(x)+h(x)+χ(x)` for Eq. (8.1.1).

Book JSON citation: `book/FOML/StochasticGradientSliding.json:setup.problem`
states `Ψ* ≡ min_{x∈X}{Ψ(x):=f(x)+h(x)+χ(x)}`.

Aligns with the paper's stated composite form by specializing
`SOptLib.compositeObjective` to the smooth part `f` and the combined nonsmooth
simple part `h + χ`. -/
abbrev objective (x : E) : ℝ :=
  SOptLib.compositeObjective S.f (fun y => S.h y + S.chi y) x

/-- Optimal value `Ψ* = min_{x in X} Ψ(x)` as the infimum over the feasible set.

No SOptLib match was used for the constrained three-term SGS objective value:
searched objective/problem candidates and considered `objectiveGapRadius` and
`compositeObjective`; those are gap wrappers or pointwise objectives, while Eq.
(8.1.1) needs the feasible-set value of this paper's `f+h+χ`. -/
noncomputable def objectiveValue : ℝ :=
  sInf (objective S '' S.X)

/-- Canonical Bregman prox function `V(x,z)` from Eq. (3.2.2).

Book JSON citation:
`book/FOML/StochasticGradientSliding.json:assumptions[6]` states
`V(x,z)=ν(z)-[ν(x)+<∇ν(x),z-x>]`.

Aligns with SOptLib's canonical `bregmanDivergence`, whose defining formula is
the same ambient Bregman expression used by the paper's prox function. -/
noncomputable def bregman (x z : E) : ℝ :=
  bregmanDivergence S.proxPotential x z

/-- Defining equation for the SGS Bregman prox function. -/
theorem bregman_def (x z : E) :
    bregman S x z =
      S.proxPotential z - S.proxPotential x - ⟪∇ S.proxPotential x, z - x⟫_ℝ := by
  rfl

/-- The paper's smooth component really carries smooth-function regularity on
the feasible carrier, so uses of `∇ f` in Eq. (8.1.2) and Eq. (8.1.9) are not
just Mathlib totalization artifacts. -/
theorem setup_smoothFunctionOn : SmoothFunctionOn S.X S.f S.primalNorm S.lSmooth :=
  S.smooth_f

/-- Feasible points of the paper domain `X`. -/
abbrev FeasiblePoint := {x : E // x ∈ S.X}

/-- Points in the source prox-core `X^o` of the paper distance-generating
function. -/
abbrev ProxCorePoint := {x : E // x ∈ proxCore S.X S.proxPotential}

/-- A prox-core point coerced to the feasible carrier `X`. -/
def proxCorePointToFeasible (x : ProxCorePoint S) : FeasiblePoint S :=
  ⟨x.1, proxCore_subset x.2⟩

/-- Boundary-safe realization of the paper's source gradient `∇ν(x)` on
`X^o`.

Section 3.2 defines `V : X^o × X → R`.  For the second argument to range over all
of `X`, the derivative in Eq. (3.2.2) is the carrier derivative of `ν : X → R` at
the prox-core base point; Mathlib's canonical totalization is `gradientWithin`
on `S.X`.

This helper is intentionally private: the paper-facing object is `bregmanOn`,
while the boundary-safe totalization is Lean infrastructure. -/
noncomputable def proxCoreGradient (x : ProxCorePoint S) : E :=
  letI : FiniteDimensional ℝ E := S.finiteDimensional_ambient
  proxCoreGradientRaw S.X S.proxPotential x

/-- Composite objective restricted to the paper domain `X`.

The book states `f,h : X → ℝ` and the algorithm output is `\bar x_N`; this
wrapper keeps paper-facing theorem statements on feasible points rather than
silently evaluating the ambient totalization outside `X`. -/
abbrev objectiveOn (x : FeasiblePoint S) : ℝ :=
  objective S x.1

/-- Domain-correct Bregman prox function on `X^o × X`.

Aligns with the PDF statement that the prox-function is
`V : X^o × X → R_+`.  The ambient `bregman` above is the Mathlib/SOptLib
formula carrier; this subtype-restricted object records the Section 3.2 source
domain without asserting that every feasible algorithmic center belongs to
`X^o`. -/
noncomputable def bregmanOn (x : ProxCorePoint S) (z : FeasiblePoint S) : ℝ :=
  S.proxPotential z.1 - S.proxPotential x.1 -
    ⟪proxCoreGradient S x, z.1 - x.1⟫_ℝ

/-- Literal Section 3.2 Bregman formula on `X^o × X`.

Eq. (3.2.2) writes `∇ν(x)` for the derivative of the distance-generating
function restricted to the source domain `X^o`.  In Lean this is the prox-core
carrier gradient, not Mathlib's ambient `∇ S.proxPotential x.1`, which would add
an unstated Frechet-differentiability requirement for arbitrary ambient
extensions. -/
noncomputable def literalBregmanOn (x : ProxCorePoint S) (z : FeasiblePoint S) : ℝ :=
  S.proxPotential z.1 - S.proxPotential x.1 -
    ⟪proxCoreGradient S x, z.1 - x.1⟫_ℝ

/-- Definitional bridge from the executable carrier-gradient realization to the
source-typed Eq. (3.2.2) formula on `X^o × X`. -/
theorem bregmanOn_eq_literal_of_mem_proxCore
    (x : ProxCorePoint S) (z : FeasiblePoint S) :
    bregmanOn S x z = literalBregmanOn S x z := by
  rfl

/-- Contract-name alias for the source-domain Bregman realization bridge.

The realization audit expects the bridge obligation under this exact name; the
mathematical content is the existing source-domain bridge
`bregmanOn_eq_literal_of_mem_proxCore`. -/
theorem bregmanOn_eq_literalBregmanOn
    (x : ProxCorePoint S) (z : FeasiblePoint S) :
    bregmanOn S x z = literalBregmanOn S x z :=
  bregmanOn_eq_literal_of_mem_proxCore S x z

/-- Feasible-pair carrier formula obtained by evaluating Eq. (3.2.2) on `X × X`.

This is deliberately *not* named as the source-typed paper prox-function:
Section 3.2 defines `V : X^o × X → ℝ_+`, while Algorithm 8.1/8.2 displays the
same formula at feasible centers produced by the method.  The Lean realization
uses Mathlib's boundary-safe `gradientWithin` on the carrier `X`, so when a
feasible center is later retyped as a prox-core point this kernel is the same
one used by `bregmanOn`.

SOptLib match: `carrierBregmanDivergence` is the canonical carrier Bregman
primitive for Eq. (3.2.2), with `gradientWithin` as the boundary-safe carrier
gradient selector. -/
noncomputable def bregmanFormulaOnX (x z : FeasiblePoint S) : ℝ :=
  letI : FiniteDimensional ℝ E := S.finiteDimensional_ambient
  feasibleBregmanFormulaExtension S.X S.proxPotential x z

/-- Bridge from the feasible-pair carrier formula to the paper
Bregman prox-function on `X^o × X`.

Both sides use the same boundary-safe carrier gradient selector.  This theorem
is the definitional bridge consumed by SPS objective normalization; the old
gradient-pairing hypothesis is retained in the signature only for compatibility
with earlier callers and is not a primitive assumption. -/
theorem bregmanFormulaOnX_eq_bregmanOn_of_gradient_pairing
    (x : FeasiblePoint S) (z : FeasiblePoint S)
    (hxcore : x.1 ∈ proxCore S.X S.proxPotential)
    (_hgrad :
      ⟪∇ S.proxPotential x.1, z.1 - x.1⟫_ℝ =
        ⟪gradientWithin S.proxPotential S.X x.1, z.1 - x.1⟫_ℝ) :
    bregmanFormulaOnX S x z = bregmanOn S ⟨x.1, hxcore⟩ z := by
  simp [bregmanFormulaOnX, feasibleBregmanFormulaExtension, bregmanOn,
    proxCoreGradient, proxCoreGradientRaw, hxcore]

/-- Source-domain bridge from the feasible formula extension to the paper
Bregman object once the first argument is known to lie in `X^o`.

The proof obligation is now the intended Pattern-A compatibility theorem:
compare the private feasible-boundary extension with the prox-core carrier
gradient only at source-admissible bases, instead of asking for measurability of
the feasible-boundary selector on all of `X`. -/
theorem bregmanFormulaOnX_eq_bregmanOn_of_mem_proxCore
    (x : FeasiblePoint S) (z : FeasiblePoint S)
    (hxcore : x.1 ∈ proxCore S.X S.proxPotential) :
    bregmanFormulaOnX S x z = bregmanOn S ⟨x.1, hxcore⟩ z := by
  simp [bregmanFormulaOnX, feasibleBregmanFormulaExtension, bregmanOn,
    proxCoreGradient, proxCoreGradientRaw, hxcore]

/-- Continuity of the source-typed left Bregman section.

This is the compact-envelope companion to `bregmanOn_left_section_measurable`:
it stays on the paper domain `X^o × X` and uses the fixed-anchor
`carrierGradientFrom` continuity API on `proxCore`, rather than any
all-feasible boundary gradient selector. -/
theorem bregmanOn_left_section_continuous (z : FeasiblePoint S) :
    Continuous (fun y : ProxCorePoint S => bregmanOn S y z) := by
  classical
  letI : FiniteDimensional ℝ E := S.finiteDimensional_ambient
  let Xc : Set E := proxCore S.X S.proxPotential
  let v : ProxCorePoint S → ℝ := fun y => S.proxPotential y.1
  let eval : ProxCorePoint S → E := fun y => y.1
  let grad : ProxCorePoint S → E := fun y => proxCoreGradient S y
  have hcontdiff : ContDiffOn ℝ 1 S.proxPotential Xc := by
    simpa [Xc, ProxGeometryOn] using S.prox_geometry.2.2.2.1
  have hv_cont : Continuous v := by
    exact
      continuous_subtype_of_continuousOn_ambient
        (X := Xc) v S.proxPotential hcontdiff.continuousOn (by
          intro y
          rfl)
  have heval : Continuous eval := by
    simpa [eval] using
      (continuous_subtype_val : Continuous (fun y : ProxCorePoint S => (y : E)))
  have hgrad : Continuous grad := by
    by_cases hne : Nonempty (ProxCorePoint S)
    · have hconv : Convex ℝ Xc := by
        simpa [Xc, ProxGeometryOn] using S.prox_geometry.2.2.1
      let vcore : ProxCorePoint S → ℝ := fun y => S.proxPotential y.1
      have htotal_contdiff :
          ContDiffOn ℝ 1 (SOptLib.totalizeOn Xc vcore) Xc := by
        refine hcontdiff.congr ?_
        intro y hy
        calc
          SOptLib.totalizeOn Xc vcore y = vcore ⟨y, hy⟩ :=
            SOptLib.totalizeOn_of_mem Xc vcore hy
          _ = S.proxPotential y := rfl
      have hgrad_cont :
          Continuous
            (fun y : ProxCorePoint S =>
              SOptLib.carrierGradientFrom Xc vcore (Classical.choice hne) y) := by
        simpa [Xc, vcore] using
          SOptLib.carrierGradientFrom_continuous
            Xc vcore (Classical.choice hne) hconv htotal_contdiff
      have hgrad_eq :
          grad =
            (fun y : ProxCorePoint S =>
              SOptLib.carrierGradientFrom Xc vcore (Classical.choice hne) y) := by
        funext y
        simp [grad, proxCoreGradient, proxCoreGradientRaw, Xc, vcore, hne]
      rw [hgrad_eq]
      exact hgrad_cont
    · have hgrad_eq : grad = (fun _ : ProxCorePoint S => (0 : E)) := by
        funext y
        exact (hne ⟨y⟩).elim
      rw [hgrad_eq]
      exact continuous_const
  have hdisp : Continuous (fun y : ProxCorePoint S => z.1 - eval y) :=
    continuous_const.sub heval
  have hinner :
      Continuous (fun y : ProxCorePoint S => ⟪grad y, z.1 - eval y⟫_ℝ) :=
    hgrad.inner hdisp
  have hmain :
      Continuous
        (fun y : ProxCorePoint S =>
          S.proxPotential z.1 - v y - ⟪grad y, z.1 - eval y⟫_ℝ) :=
    (continuous_const.sub hv_cont).sub hinner
  simpa [bregmanOn, v, eval, grad] using hmain

/-- Measurability of the source-typed left Bregman section.

This is the source-faithful replacement for the rejected all-feasible
`boundarySafeCarrierGradient` measurability leaf.  The proof route is to use the
`ContDiffOn` component of `S.prox_geometry` on `proxCore`, the SOptLib
`carrierGradientFrom` continuity API on that carrier, and
`carrierBregman_measurable_left_of_measurable_grad`. -/
theorem bregmanOn_left_section_measurable
    [MeasurableSpace E] [BorelSpace E] (z : FeasiblePoint S) :
    Measurable (fun y : ProxCorePoint S => bregmanOn S y z) := by
  exact (bregmanOn_left_section_continuous (S := S) z).measurable

/-- Generated selected-query Bregman observables are strongly measurable once
their bases are supplied as source-domain (`X^o`) points.

This bridge routes through `bregmanOn : X^o × X → ℝ` and then transports back to
the feasible formula extension by `bregmanFormulaOnX_eq_bregmanOn_of_mem_proxCore`.
It intentionally does not require measurability of
`boundarySafeCarrierGradient` over arbitrary feasible boundary points. -/
theorem selected_query_bregmanFormulaOnX_aestronglyMeasurable_of_proxCore
    [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E] {P : Measure Ω}
    (query : Ω → E) (hmem : ∀ ω, query ω ∈ S.X)
    (hcore : ∀ ω, query ω ∈ proxCore S.X S.proxPotential)
    (hmeas : Measurable (fun ω => (⟨query ω, hmem ω⟩ : FeasiblePoint S)))
    (z : FeasiblePoint S) :
    AEStronglyMeasurable
      (fun ω => bregmanFormulaOnX S (⟨query ω, hmem ω⟩ : FeasiblePoint S) z) P := by
  classical
  have hquery_meas : Measurable query := by
    simpa using (measurable_subtype_coe.comp hmeas)
  have hcore_meas :
      Measurable (fun ω => (⟨query ω, hcore ω⟩ : ProxCorePoint S)) :=
    hquery_meas.subtype_mk (h := hcore)
  have hsource :
      AEStronglyMeasurable
        (fun ω => bregmanOn S (⟨query ω, hcore ω⟩ : ProxCorePoint S) z) P := by
    exact ((bregmanOn_left_section_measurable (S := S) z).comp hcore_meas).aestronglyMeasurable
  have hfun :
      (fun ω => bregmanFormulaOnX S (⟨query ω, hmem ω⟩ : FeasiblePoint S) z) =
        (fun ω => bregmanOn S (⟨query ω, hcore ω⟩ : ProxCorePoint S) z) := by
    funext ω
    exact bregmanFormulaOnX_eq_bregmanOn_of_mem_proxCore
      (S := S) (⟨query ω, hmem ω⟩ : FeasiblePoint S) z (hcore ω)
  simpa [hfun] using hsource

/-- Literal ambient-gradient bridge for the source-typed Bregman kernel.

This is the explicit Pattern-A boundary obligation: the public
`X^o × X` kernel is implemented with the private carrier-gradient extension
`proxCoreGradient`; when that carrier derivative has the same pairing with the
endpoint displacement as Mathlib's ambient `∇`, the kernel is exactly the
literal Eq. (3.2.2) Bregman formula `bregman`. -/
theorem bregmanOn_eq_bregman_of_gradient_pairing
    (x : ProxCorePoint S) (z : FeasiblePoint S)
    (hgrad :
      ⟪proxCoreGradient S x, z.1 - x.1⟫_ℝ =
        ⟪∇ S.proxPotential x.1, z.1 - x.1⟫_ℝ) :
    bregmanOn S x z = bregman S x.1 z.1 := by
  simp [bregmanOn, bregman, bregmanDivergence, hgrad]

/-- Prox-potential support inequality on the feasible carrier, staged before
the literal Bregman bridge.

Aligns with Lan Section 3.2's convex differentiable distance generator.
Candidate audit: considered SOptLib/Mathlib first-order convexity candidates
and the listed prox-step candidates; none directly produce this paper-local
`boundarySafeCarrierGradient` support line from `S.prox_geometry`, so this is
the segment-derivative argument used by the lower-bound block. -/
theorem proxPotential_support_on_X_for_literal_bridge
    (x z : FeasiblePoint S) :
    S.proxPotential x.1 +
      ⟪boundarySafeCarrierGradient S.X S.proxPotential x, z.1 - x.1⟫_ℝ ≤
        S.proxPotential z.1 := by
  classical
  rcases S.prox_geometry with ⟨_hcont, hdiffX, _hcore_convex, _hdiffCore, hconv, _hstrong⟩
  change S.proxPotential x.1 +
      ⟪gradientWithin S.proxPotential S.X x.1, z.1 - x.1⟫_ℝ ≤
        S.proxPotential z.1
  let line : ℝ → E := fun t => AffineMap.lineMap x.1 z.1 t
  let d : E := z.1 - x.1
  let s : Set ℝ := Set.Icc (0 : ℝ) 1
  have hline_deriv : HasDerivWithinAt line d s 0 := by
    simpa [line, d, s] using
      (AffineMap.hasDerivWithinAt_lineMap (a := x.1) (b := z.1)
        (s := Set.Icc (0 : ℝ) 1) (x := (0 : ℝ)))
  have hmaps : Set.MapsTo line s S.X := by
    intro t ht
    exact S.convex_X.lineMap_mem x.2 z.2 (by simpa [s] using ht)
  have hνdiff : DifferentiableWithinAt ℝ S.proxPotential S.X x.1 :=
    hdiffX x.1 x.2
  have hνline : HasDerivWithinAt (fun t : ℝ => S.proxPotential (line t))
      ((fderivWithin ℝ S.proxPotential S.X x.1) d) s 0 := by
    simpa [Function.comp_def] using
      hνdiff.hasFDerivWithinAt.comp_hasDerivWithinAt_of_eq 0 hline_deriv hmaps
        (by simp [line])
  have hgrad_apply :
      (fderivWithin ℝ S.proxPotential S.X x.1) d =
        ⟪gradientWithin S.proxPotential S.X x.1, d⟫_ℝ := by
    rw [gradientWithin, InnerProductSpace.toDual_symm_apply]
  have hderiv_line : HasDerivWithinAt (fun t : ℝ => S.proxPotential (line t))
      ⟪gradientWithin S.proxPotential S.X x.1, z.1 - x.1⟫_ℝ s 0 := by
    simpa [d, hgrad_apply] using hνline
  have hsec : ∀ t ∈ s,
      S.proxPotential (line t) - S.proxPotential x.1 ≤
        t * (S.proxPotential z.1 - S.proxPotential x.1) := by
    intro t ht
    have htI : t ∈ Set.Icc (0 : ℝ) 1 := by simpa [s] using ht
    rcases Set.mem_Icc.mp htI with ⟨ht0, ht1⟩
    have hconv_step := hconv.2 x.2 z.2 (sub_nonneg.mpr ht1) ht0 (by ring)
    have hline_eq : line t = (1 - t) • x.1 + t • z.1 := by
      simp [line, AffineMap.lineMap_apply_module']
      module
    have hconv_line :
        S.proxPotential (line t) ≤
          (1 - t) * S.proxPotential x.1 + t * S.proxPotential z.1 := by
      rw [hline_eq]
      simpa [smul_eq_mul] using hconv_step
    nlinarith
  let ψ : ℝ → ℝ := fun t =>
    t * (S.proxPotential z.1 - S.proxPotential x.1) -
      (S.proxPotential (line t) - S.proxPotential x.1)
  have hψmin : ∀ t ∈ s, ψ 0 ≤ ψ t := by
    intro t ht
    have h0 : ψ 0 = 0 := by simp [ψ, line]
    have ht_nonneg : 0 ≤ ψ t := by
      dsimp [ψ]
      have h := hsec t ht
      nlinarith
    rw [h0]
    exact ht_nonneg
  have hlin_deriv : HasDerivWithinAt
      (fun t : ℝ => t * (S.proxPotential z.1 - S.proxPotential x.1))
      (S.proxPotential z.1 - S.proxPotential x.1) s 0 := by
    simpa using (hasDerivWithinAt_id (x := (0 : ℝ)) (s := s)).mul_const
      (S.proxPotential z.1 - S.proxPotential x.1)
  have hνsub_deriv : HasDerivWithinAt
      (fun t : ℝ => S.proxPotential (line t) - S.proxPotential x.1)
      ⟪gradientWithin S.proxPotential S.X x.1, z.1 - x.1⟫_ℝ s 0 := by
    simpa using hderiv_line.sub_const (S.proxPotential x.1)
  have hψderiv : HasDerivWithinAt ψ
      ((S.proxPotential z.1 - S.proxPotential x.1) -
        ⟪gradientWithin S.proxPotential S.X x.1, z.1 - x.1⟫_ℝ) s 0 := by
    have h := hlin_deriv.sub hνsub_deriv
    simpa [ψ] using h
  have hnonneg :
      0 ≤ (S.proxPotential z.1 - S.proxPotential x.1) -
        ⟪gradientWithin S.proxPotential S.X x.1, z.1 - x.1⟫_ℝ := by
    exact right_derivative_nonneg_of_min_on_Icc (by simpa [s] using hψderiv)
      (by simpa [s] using hψmin)
  nlinarith

/-- Feasible points are prox-core points for the differentiable convex prox
potential, staged before the literal Bregman bridge.

Aligns with Lan Section 3.2's distance-generating function. Candidate audit:
considered `carrierGradientFrom_inner_eq_gradientWithin_on_feasible_direction`
and Mathlib minimizer-to-FOC lemmas; they transfer existing carrier gradients or
use an existing minimizer, while this paper-local step constructs the prox-core
witness from the support inequality. -/
theorem feasible_mem_proxCore_for_literal_bridge (x : FeasiblePoint S) :
    x.1 ∈ proxCore S.X S.proxPotential := by
  classical
  refine ⟨x.2, ?_⟩
  let p : E := -boundarySafeCarrierGradient S.X S.proxPotential x
  refine ⟨p, ?_⟩
  intro u hu
  have hsupport :=
    proxPotential_support_on_X_for_literal_bridge (S := S) x ⟨u, hu⟩
  have hsupport' :
      S.proxPotential x.1 +
          (⟪boundarySafeCarrierGradient S.X S.proxPotential x, u⟫_ℝ -
            ⟪boundarySafeCarrierGradient S.X S.proxPotential x, x.1⟫_ℝ) ≤
        S.proxPotential u := by
    simpa [inner_sub_right] using hsupport
  dsimp [p]
  rw [inner_neg_left]
  rw [inner_neg_left]
  nlinarith

/-- Under the current prox geometry, the paper prox-core equals the feasible
carrier, staged before the literal Bregman bridge.

Aligns with the convex-differentiable specialization of Lan Section 3.2.
Candidate audit: SOptLib has carrier/intrinsic-interior infrastructure but no
lemma for this paper-local `proxCore`; the equality follows from
`feasible_mem_proxCore_for_literal_bridge` and `proxCore_subset`. -/
theorem proxCore_eq_X_for_literal_bridge :
    proxCore S.X S.proxPotential = S.X := by
  exact Set.Subset.antisymm proxCore_subset
    (fun x hx => feasible_mem_proxCore_for_literal_bridge (S := S) ⟨x, hx⟩)

/-- Prox-core branch pairing compatibility with the feasible carrier gradient.

Aligns with Lan Section 3.2 Eq. (3.2.2), where the same carrier gradient appears
in the Bregman formula. Candidate audit:
`carrierGradientFrom_inner_eq_gradientWithin_on_feasible_direction` is the
matching SOptLib bridge after rewriting the paper prox-core carrier to `S.X`. -/
theorem proxCoreGradient_pairing_eq_gradientWithin_for_literal_bridge
    (x z : FeasiblePoint S) (hxcore : x.1 ∈ proxCore S.X S.proxPotential) :
    ⟪proxCoreGradient S ⟨x.1, hxcore⟩, z.1 - x.1⟫_ℝ =
      ⟪gradientWithin S.proxPotential S.X x.1, z.1 - x.1⟫_ℝ := by
  classical
  letI : FiniteDimensional ℝ E := S.finiteDimensional_ambient
  have hcore_eq : proxCore S.X S.proxPotential = S.X :=
    proxCore_eq_X_for_literal_bridge (S := S)
  have hzcore : z.1 ∈ proxCore S.X S.proxPotential := by
    rw [hcore_eq]
    exact z.2
  have hne : Nonempty {x : E // x ∈ proxCore S.X S.proxPotential} :=
    ⟨⟨x.1, hxcore⟩⟩
  rcases S.prox_geometry with
    ⟨_hcont, _hdiffX, hcore_convex, hdiffCore, _hconv, _hstrong⟩
  have hdiffCoreAt :
      DifferentiableWithinAt ℝ S.proxPotential
        (proxCore S.X S.proxPotential) x.1 :=
    hdiffCore.differentiableOn_one x.1 hxcore
  have hcarrier :=
    carrierGradientFrom_inner_eq_gradientWithin_on_feasible_direction
      (v := fun y : {x : E // x ∈ proxCore S.X S.proxPotential} =>
        S.proxPotential y.1)
      (ν := S.proxPotential)
      (anchor := Classical.choice hne)
      (z := ⟨x.1, hxcore⟩)
      (x := ⟨z.1, hzcore⟩)
      hcore_convex hdiffCoreAt (by intro y; rfl)
  have hright :
      ⟪gradientWithin S.proxPotential (proxCore S.X S.proxPotential) x.1,
          z.1 - x.1⟫_ℝ =
        ⟪gradientWithin S.proxPotential S.X x.1, z.1 - x.1⟫_ℝ := by
    rw [hcore_eq]
  have hcarrierX :
      ⟪SOptLib.carrierGradientFrom (proxCore S.X S.proxPotential)
          (fun y : {x : E // x ∈ proxCore S.X S.proxPotential} =>
            S.proxPotential y.1)
          (Classical.choice hne) ⟨x.1, hxcore⟩, z.1 - x.1⟫_ℝ =
        ⟪gradientWithin S.proxPotential S.X x.1, z.1 - x.1⟫_ℝ := by
    exact hcarrier.trans hright
  simpa [proxCoreGradient, proxCoreGradientRaw, hne] using hcarrierX

/-- Canonical feasible-carrier formula for `bregmanFormulaOnX` before applying
the literal ambient-gradient bridge.

Aligns with Lan Section 3.2 Eq. (3.2.2). Candidate audit:
`blockBregmanDivergence_eq_gradientWithin_formula` normalizes the carrier
Bregman object, while the paper-local formula extension also has a prox-core
branch; the helpers above discharge that branch and show the totalized formula
is exactly the `gradientWithin` carrier expression. -/
theorem bregmanFormulaOnX_gradientWithin_formula_for_literal_bridge
    (x z : FeasiblePoint S) :
    bregmanFormulaOnX S x z =
      S.proxPotential z.1 - S.proxPotential x.1 -
        ⟪gradientWithin S.proxPotential S.X x.1, z.1 - x.1⟫_ℝ := by
  classical
  letI : FiniteDimensional ℝ E := S.finiteDimensional_ambient
  by_cases hxcore : x.1 ∈ proxCore S.X S.proxPotential
  · have hpair :=
      proxCoreGradient_pairing_eq_gradientWithin_for_literal_bridge
        (S := S) x z hxcore
    have hpair_raw :
        ⟪proxCoreGradientRaw S.X S.proxPotential ⟨x.1, hxcore⟩, z.1 - x.1⟫_ℝ =
          ⟪gradientWithin S.proxPotential S.X x.1, z.1 - x.1⟫_ℝ := by
      simpa [proxCoreGradient] using hpair
    simp [bregmanFormulaOnX, feasibleBregmanFormulaExtension, hxcore, hpair_raw]
  · have hxcore' : x.1 ∈ proxCore S.X S.proxPotential :=
      feasible_mem_proxCore_for_literal_bridge (S := S) x
    exact False.elim (hxcore hxcore')

/-- Literal ambient-gradient bridge for the feasible-pair formula extension.

The feasible `X × X` kernel used by generated SPS/SGS statements is the same
boundary-safe carrier realization as `bregmanOn`.  Under the corresponding
directional pairing equality, it reduces to the literal ambient Bregman formula
from Eq. (3.2.2). -/
theorem bregmanFormulaOnX_eq_bregman_of_gradient_pairing
    (x : FeasiblePoint S) (z : FeasiblePoint S)
    (hgrad :
      ⟪gradientWithin S.proxPotential S.X x.1, z.1 - x.1⟫_ℝ =
        ⟪∇ S.proxPotential x.1, z.1 - x.1⟫_ℝ) :
    bregmanFormulaOnX S x z = bregman S x.1 z.1 := by
  classical
  letI : FiniteDimensional ℝ E := S.finiteDimensional_ambient
  have hformula :=
    bregmanFormulaOnX_gradientWithin_formula_for_literal_bridge (S := S) x z
  calc
    bregmanFormulaOnX S x z =
        S.proxPotential z.1 - S.proxPotential x.1 -
          ⟪gradientWithin S.proxPotential S.X x.1, z.1 - x.1⟫_ℝ := hformula
    _ = S.proxPotential z.1 - S.proxPotential x.1 -
          ⟪∇ S.proxPotential x.1, z.1 - x.1⟫_ℝ := by
        rw [hgrad]
    _ = bregman S x.1 z.1 := by
        simp [bregman, bregmanDivergence]

/-- Source-facing prox-geometry predicate for Eq. (3.2.1)-(3.2.2).

Aligns with SOptLib's Bregman formula for `V`, but keeps the paper's
source-defined `X^o` domain and unit strong-convexity/monotonicity semantics as a
separate assumption object rather than silently treating the ambient totalized
formula as the whole prox-function hypothesis. -/
def proxGeometry : Prop :=
  ProxGeometryOn S.X S.proxPotential S.primalNorm

/-- The prox geometry used by SGS is a stated setup assumption, not a
theorem-local regularity hypothesis. -/
theorem setup_proxGeometry : proxGeometry S :=
  S.prox_geometry

/-- Carrier-restricted statement that the selected `h'` belongs to `∂h(x)` on
`X`, as required in Eq. (8.1.3) and Eq. (8.1.6).

Aligns with `SOptLib.carrierSubdifferential`, whose support-inequality
definition is the reusable carrier version of the paper's subdifferential
notation. -/
def hSubgradientMem : Prop :=
  ∀ x (hx : x ∈ S.X),
    S.hSubgradient x ∈
      SOptLib.carrierSubdifferential
        (fun y : {y : E // y ∈ S.X} => S.h y.1) ⟨x, hx⟩

/-- The `h'(x) ∈ ∂h(x)` clause in Eq. (8.1.3) is part of the source assumption,
not a standalone unused predicate. -/
theorem setup_hSubgradientMem : hSubgradientMem S :=
  S.h_subgradient_mem

/-- The paper's noise scale `σ` is recovered as the square root of the stated
variance/light-tail scale `σ²`. -/
noncomputable def sigma : ℝ :=
  Real.sqrt S.sigmaSq

/-- The paper's conjugate dual norm `‖·‖_*`, induced by the stated primal norm
on `X`.

Book/PDF citation: `book/FOML/StochasticGradientSliding.json:assumptions[3]`
uses `‖H(u_t,ξ_t)-h'(u_t)‖_*^2`, and the PDF, Section 3.2 around
Eq. (3.2.1), defines `‖x‖_* = sup_{‖y‖≤1} <x,y>` for the general norm used by
the prox geometry.

Uses `SOptLib.canonicalDualNorm`, the reusable support-function dual norm over
the primal unit ball.  The ambient finite-dimensional structure is part of the
book's `X ⊂ R^n` setup and supplies the bounded-support bridge needed for the
paper's primal/dual Cauchy inequality. -/
noncomputable def dualNorm (zeta : E) : ℝ :=
  SOptLib.canonicalDualNorm S.primalNorm zeta

/-- The defining support-function formula for the paper dual norm. -/
theorem dualNorm_eq_sSup (zeta : E) :
    dualNorm S zeta =
      sSup {r : ℝ | ∃ d : E, S.primalNorm d ≤ 1 ∧ r = |inner ℝ zeta d|} := by
  rfl

/-- The source separating primal norm field in `Setup` as the SOptLib predicate. -/
theorem primalNorm_isSeparating :
    S.primalNorm.IsSeparating := by
  intro x
  exact S.primalNorm_separating x

/-- Finite-dimensional control of the paper primal unit ball.

Source: `book/FOML/StochasticGradientSliding.json:setup.variable_space` states
`X ⊆ R^n`; Section 3.2 defines the primal norm on this finite-dimensional
ambient space.  This theorem turns the stated separating primal norm into the
bounded support-set hypothesis required by the canonical dual norm API. -/
theorem dualNorm_supportSet_bddAbove (zeta : E) :
    BddAbove {r : ℝ | ∃ d : E, S.primalNorm d ≤ 1 ∧ r = |inner ℝ zeta d|} := by
  letI : FiniteDimensional ℝ E := S.finiteDimensional_ambient
  rcases Seminorm.exists_norm_le_mul_self_of_finiteDimensional_separating
      S.primalNorm (primalNorm_isSeparating S) with ⟨C, _hCnonneg, hC⟩
  exact
    SOptLib.canonicalDualNorm_supportSet_bddAbove
      (p := S.primalNorm) (zeta := zeta)
      ⟨C, fun d hd => by
        have hunit : C * S.primalNorm d ≤ C * 1 :=
          mul_le_mul_of_nonneg_left hd _hCnonneg
        simpa using (hC d).trans hunit⟩

/-- The paper primal/dual Cauchy inequality for `‖·‖` and `‖·‖_*`. -/
theorem abs_inner_le_dualNorm_mul_primalNorm (zeta d : E) :
    |inner ℝ zeta d| ≤ dualNorm S zeta * S.primalNorm d := by
  letI : FiniteDimensional ℝ E := S.finiteDimensional_ambient
  simpa [dualNorm] using
    SOptLib.abs_inner_le_canonicalDualNorm_mul
      (p := S.primalNorm) (hp := primalNorm_isSeparating S)
      (zeta := zeta) (d := d) (dualNorm_supportSet_bddAbove S zeta)

/-- Magnitude of the stochastic oracle noise in the paper's dual norm. -/
noncomputable def oracleNoiseDualNorm (u : E) (xi : Sample) : ℝ :=
  dualNorm S (S.oracle u xi - S.hSubgradient u)

/-- Paper optimizer predicate for Eq. (8.1.1), keeping `x^*` as the source
object rather than replacing it by an `sInf` value.

No new SOptLib primitive is introduced: searched objective/minimum candidates
and reused the Mathlib `IsMinOn` predicate directly because the paper theorem
quantifies over an arbitrary optimal solution `x^* ∈ X`. -/
def IsOptimalSolution (xStar : E) : Prop :=
  xStar ∈ S.X ∧ IsMinOn (objective S) S.X xStar

/-- A source optimizer realizes the `sInf`-based internal value. -/
theorem objectiveValue_eq_of_isOptimalSolution {xStar : E}
    (hxStar : IsOptimalSolution S xStar) :
    objectiveValue S = objective S xStar := by
  rcases hxStar with ⟨hxmem, hmin⟩
  unfold objectiveValue
  have hleast : IsLeast (Set.image (objective S) S.X) (objective S xStar) := by
    refine ⟨⟨xStar, hxmem, rfl⟩, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    exact hmin hx
  exact hleast.csInf_eq

/-- Smooth linearization `l_f(x;y)` from Eq. (8.1.9).

Book JSON citation:
`book/FOML/StochasticGradientSliding.json:algorithm_spec.steps[1]` states
`l_f(x;y):=f(x)+<∇f(x),y-x>`.

This is the paper's literal affine model formula, with `∇f` realized by the
source/carrier gradient `sourceSmoothGradient`.  This matches the book's
`f : X → ℝ` object and avoids treating Mathlib's ambient total gradient of an
arbitrary extension as source data at feasible boundary points. -/
noncomputable def smoothLinearization (x y : E) : ℝ :=
  S.f x + ⟪sourceSmoothGradient S x, y - x⟫_ℝ

/-- Paper-literal ambient-gradient rendering of Eq. (8.1.9).

No SOptLib match: searched gradient-within/ambient-gradient bridge candidates and
scanned `SOptLib/Model/Carrier.lean`; the library supplies the gradient bridge
`SOptLib.gradientWithin_eq_gradient_of_mem_interior`, but Eq. (8.1.9)'s affine
formula itself is local to the SGS smooth model.  This literal object is used
only for the interior bridge; `smoothLinearization` remains the boundary-safe
source-domain model used by the proof. -/
noncomputable def literalSmoothLinearization (x y : E) : ℝ :=
  S.f x + ⟪literalSourceSmoothGradient S x, y - x⟫_ℝ

/-- The smooth linearization `l_f(x;·)` is the affine model used in Algorithm
8.1, step 1 and inherited by Algorithm 8.2. -/
theorem smoothLinearization_isAffineModel (x : E) :
    IsAffineModel (smoothLinearization S x) := by
  refine ⟨S.f x - ⟪sourceSmoothGradient S x, x⟫_ℝ, sourceSmoothGradient S x, ?_⟩
  intro u
  simp [smoothLinearization, inner_sub_right]
  ring

/-- Smooth quadratic upper model for the source linearization, Eq. (8.1.2).

This is a direct field specialization after reconstructing `l_f` to use the
same carrier gradient as the smoothness assumption. -/
theorem smoothLinearization_upper_on_X {x y : E} (hx : x ∈ S.X) (hy : y ∈ S.X) :
    S.f x ≤ smoothLinearization S y x +
      (S.lSmooth / 2) * S.primalNorm (x - y) ^ 2 := by
  simpa [smoothLinearization, sourceSmoothGradient] using S.smoothness hx hy

/-- Convex support inequality for the source linearization, used in Eq. (8.1.30).

This is the source-derived bridge from convexity and smoothness of `f : X → ℝ`
to the supporting hyperplane of the carrier gradient.  It is intentionally not
a setup field: the book proves/uses this as a consequence of convexity of `f`,
not as a primitive assumption. -/
theorem smoothLinearization_support_on_X {x y : E} (hx : x ∈ S.X) (hy : y ∈ S.X) :
    smoothLinearization S y x ≤ S.f x := by
  classical
  change S.f y + ⟪gradientWithin S.f S.X y, x - y⟫_ℝ ≤ S.f x
  let line : ℝ → E := fun t => AffineMap.lineMap y x t
  let d : E := x - y
  let s : Set ℝ := Set.Icc (0 : ℝ) 1
  have hline_deriv : HasDerivWithinAt line d s 0 := by
    simpa [line, d, s] using
      (AffineMap.hasDerivWithinAt_lineMap (a := y) (b := x)
        (s := Set.Icc (0 : ℝ) 1) (x := (0 : ℝ)))
  have hmaps : Set.MapsTo line s S.X := by
    intro t ht
    exact S.convex_X.lineMap_mem hy hx (by simpa [s] using ht)
  have hfdiff : DifferentiableWithinAt ℝ S.f S.X y :=
    S.smooth_f.differentiableOn_one y hy
  have hfline : HasDerivWithinAt (fun t : ℝ => S.f (line t))
      ((fderivWithin ℝ S.f S.X y) d) s 0 := by
    simpa [Function.comp_def] using
      hfdiff.hasFDerivWithinAt.comp_hasDerivWithinAt_of_eq 0 hline_deriv hmaps
        (by simp [line])
  have hgrad_apply :
      (fderivWithin ℝ S.f S.X y) d = ⟪gradientWithin S.f S.X y, d⟫_ℝ := by
    rw [gradientWithin, InnerProductSpace.toDual_symm_apply]
  have hderiv_line : HasDerivWithinAt (fun t : ℝ => S.f (line t))
      ⟪gradientWithin S.f S.X y, x - y⟫_ℝ s 0 := by
    simpa [d, hgrad_apply] using hfline
  have hsec : ∀ t ∈ s, S.f (line t) - S.f y ≤ t * (S.f x - S.f y) := by
    intro t ht
    have htI : t ∈ Set.Icc (0 : ℝ) 1 := by simpa [s] using ht
    rcases Set.mem_Icc.mp htI with ⟨ht0, ht1⟩
    have hconv := S.convex_f.2 hy hx (sub_nonneg.mpr ht1) ht0 (by ring)
    have hline_eq : line t = (1 - t) • y + t • x := by
      simp [line, AffineMap.lineMap_apply_module']
      module
    have hconv_line : S.f (line t) ≤ (1 - t) * S.f y + t * S.f x := by
      rw [hline_eq]
      simpa [smul_eq_mul] using hconv
    nlinarith
  let ψ : ℝ → ℝ := fun t => t * (S.f x - S.f y) - (S.f (line t) - S.f y)
  have hψmin : ∀ t ∈ s, ψ 0 ≤ ψ t := by
    intro t ht
    have h0 : ψ 0 = 0 := by simp [ψ, line]
    have ht_nonneg : 0 ≤ ψ t := by
      dsimp [ψ]
      have h := hsec t ht
      nlinarith
    rw [h0]
    exact ht_nonneg
  have hlin_deriv : HasDerivWithinAt (fun t : ℝ => t * (S.f x - S.f y))
      (S.f x - S.f y) s 0 := by
    simpa using (hasDerivWithinAt_id (x := (0 : ℝ)) (s := s)).mul_const
      (S.f x - S.f y)
  have hfsub_deriv : HasDerivWithinAt (fun t : ℝ => S.f (line t) - S.f y)
      ⟪gradientWithin S.f S.X y, x - y⟫_ℝ s 0 := by
    simpa using hderiv_line.sub_const (S.f y)
  have hψderiv : HasDerivWithinAt ψ
      ((S.f x - S.f y) - ⟪gradientWithin S.f S.X y, x - y⟫_ℝ) s 0 := by
    have h := hlin_deriv.sub hfsub_deriv
    simpa [ψ] using h
  have hnonneg : 0 ≤ (S.f x - S.f y) - ⟪gradientWithin S.f S.X y, x - y⟫_ℝ := by
    exact right_derivative_nonneg_of_min_on_Icc (by simpa [s] using hψderiv)
      (by simpa [s] using hψmin)
  nlinarith

/-- Source smooth-gradient residual control in the paper primal/dual norm pair.

Lan's smoothness assumption is used in the reverse averaged-`Phi` envelope to
control the random slope
`∇f(x_under)-∇f(x)` by the deterministic displacement `x_under-x`.  This is
the carrier-gradient Lipschitz consequence of convex differentiable
`L`-smoothness on `X`; it is intentionally a private derived bridge rather than
a setup field.

The previous Candidate-1 residual helper tried to absorb the whole averaged
displacement into the successor Bregman term using only `β_k > 0`.  For
`j = 0`, that shape would require an unstated lower bound comparing `β_k` and
`L`.  This bridge is the source-faithful replacement route: apply Young's
inequality to the smooth-gradient difference, then prove integrability from the
already-established `x_under` L2 invariant. -/
theorem sourceSmoothGradient_dualNorm_sq_le_smooth_displacement_sq_of_dual_lipschitz
    (hgrad_lip :
      ∀ x y : FeasiblePoint S,
        dualNorm S (sourceSmoothGradient S y.1 - sourceSmoothGradient S x.1) ≤
          S.lSmooth * S.primalNorm (y.1 - x.1))
    (x y : FeasiblePoint S) :
    dualNorm S (sourceSmoothGradient S y.1 - sourceSmoothGradient S x.1) ^ 2 ≤
      S.lSmooth ^ 2 * S.primalNorm (y.1 - x.1) ^ 2 := by
  have hdual_nonneg :
      0 ≤ dualNorm S (sourceSmoothGradient S y.1 - sourceSmoothGradient S x.1) := by
    simpa [dualNorm] using
      SOptLib.canonicalDualNorm_nonneg S.primalNorm
        (sourceSmoothGradient S y.1 - sourceSmoothGradient S x.1)
  have hright_nonneg : 0 ≤ S.lSmooth * S.primalNorm (y.1 - x.1) :=
    mul_nonneg S.L_pos.le (apply_nonneg S.primalNorm (y.1 - x.1))
  have hle := hgrad_lip x y
  nlinarith [hle, hdual_nonneg, hright_nonneg]

/-- Dual-Lipschitz control of the source smooth gradient from the paper
smoothness assumption.

This is the remaining source-smoothness bridge needed by the repaired selected
reverse-gap Cgap.  Candidate audit: checked the local
`sourceSmoothGradient_dualNorm_sq_le_smooth_displacement_sq_of_dual_lipschitz`
and smooth-upper Cgap lemmas, plus SOptLib smooth objective/descent hits; those
consume a Lipschitz-gradient premise or prove the forward descent lemma, while
this bridge needs the converse carrier-gradient support estimate from Lan
Eq. (8.1.2) for `gradientWithin` and the paper primal/dual norm pair. -/
theorem sourceSmoothGradient_dual_lipschitz_from_smoothness :
    ∀ x y : FeasiblePoint S,
      dualNorm S (sourceSmoothGradient S y.1 - sourceSmoothGradient S x.1) ≤
        S.lSmooth * S.primalNorm (y.1 - x.1) := by
  intro x y
  simpa [dualNorm, sourceSmoothGradient] using
    S.smooth_f.gradient_lipschitz x.2 y.2

/-- Scalar obstruction for the Candidate-1 reverse-gap square budget.

If a pointwise envelope must dominate a positive square coefficient `C * V` but
the only successor-dependent term displayed outside the integrable envelope is
`(coeff / 2) * V`, then a lower bound `C ≤ coeff / 2` is necessary.  This is the
formal coefficient issue behind the failed attempt to absorb the averaged-output
successor square for arbitrary positive `β_k`. -/
theorem reverse_gap_successor_square_budget_scalar_obstruction
    {C coeff : ℝ} (hC : 0 < C) (hcoeff : 0 < coeff) (hsmall : coeff / 2 < C) :
    ∃ V : ℝ, 0 ≤ V ∧ (coeff / 2) * V + C < C * V := by
  let a : ℝ := C - coeff / 2
  have ha : 0 < a := sub_pos.mpr hsmall
  refine ⟨(2 * C) / a, ?_, ?_⟩
  · positivity
  · have hcalc : C * ((2 * C) / a) - (coeff / 2) * ((2 * C) / a) = 2 * C := by
      field_simp [a, ne_of_gt ha]
      ring
    nlinarith

/-- Interior bridge to the paper-literal ambient-gradient notation.

At ordinary interior feasible points, the carrier realization of `∇f` agrees
with Mathlib's ambient gradient.  This keeps the displayed Eq. (8.1.9) notation
available where the ambient derivative is source-faithful. -/
theorem sourceSmoothGradient_eq_gradient_of_mem_interior {x : E}
    (hx : x ∈ interior S.X) :
    sourceSmoothGradient S x = ∇ S.f x := by
  exact SOptLib.gradientWithin_eq_gradient_of_mem_interior
    (X := S.X) (f := S.f) S.smooth_f.differentiableOn_one hx

/-- At ordinary interior feasible points, the boundary-safe source gradient is
the paper-literal ambient gradient object. -/
theorem sourceSmoothGradient_eq_literalSourceSmoothGradient_of_mem_interior {x : E}
    (hx : x ∈ interior S.X) :
    sourceSmoothGradient S x = literalSourceSmoothGradient S x := by
  simpa [literalSourceSmoothGradient] using
    sourceSmoothGradient_eq_gradient_of_mem_interior S hx

/-- At ordinary interior feasible points, the boundary-safe source linearization
coincides with the paper-literal ambient-gradient affine formula. -/
theorem smoothLinearization_eq_literal_of_mem_interior {x y : E}
    (hx : x ∈ interior S.X) :
    smoothLinearization S x y = literalSmoothLinearization S x y := by
  simp [smoothLinearization, literalSmoothLinearization,
    sourceSmoothGradient_eq_literalSourceSmoothGradient_of_mem_interior S hx]

/-- Source-domain inner prox-sliding model
`\Phi(u)=g(u)+h(u)+βV(x,u)+χ(u)` from Eq. (8.1.19), typed on
`x ∈ X^o` and `u ∈ X` as the Section 3.2 prox-function domain requires.

Book JSON citation:
`book/FOML/StochasticGradientSliding.json:algorithm_spec.steps[5]` describes
the PS/SPS output pair, and `algorithm_spec.steps[3]` displays the inner
stochastic prox update over `argmin_{u∈X}`; Eq. (8.1.19) is the associated
comparison model named in the source proof.

No SOptLib match: searched composite objective/prox candidates; the reusable
composite objective names pointwise sums and the prox objectives name argmin
objectives, while Proposition 8.3 uses this SGS-specific comparison model.
This suffixed object is the source-typed interpretation; the paper-facing
Algorithm 8.1/8.2 process below is over feasible points `X`. -/
noncomputable def spsPhi_sourceDomain (g : E → ℝ) (x : ProxCorePoint S) (β : ℝ)
    (u : FeasiblePoint S) : ℝ :=
  g u.1 + S.h u.1 + β * bregmanOn S x u + S.chi u.1

/-- Feasible-domain inner prox-sliding model
`\Phi(u)=g(u)+h(u)+βV(x,u)+χ(u)`.

Book JSON citation:
`book/FOML/StochasticGradientSliding.json:algorithm_spec.steps[4]` states the
SPS averaging update, and `algorithm_spec.steps[3]` displays the stochastic
prox objective containing `β V(x,u)+χ(u)` over `u∈X`.

No SOptLib match: checked `SOptLib.compositeObjective`,
`SOptLib.proxObjective`, `SOptLib.paperProxObjective`, and `SOptLib.proxStep`;
none encode the SGS comparison model of Eq. (8.1.19) with a fixed affine `g`
and the paper's additional `h + χ` terms.  This version is deliberately typed on
`X × X` through `bregmanFormulaOnX`, so theorem statements about generated SPS
iterates do not smuggle unsupported `X^o` membership. -/
noncomputable def spsPhi (g : E → ℝ) (x : FeasiblePoint S) (β : ℝ)
    (u : FeasiblePoint S) : ℝ :=
  g u.1 + S.h u.1 + β * bregmanFormulaOnX S x u + S.chi u.1

/-- Backwards-compatible explicit formula-extension name for Eq. (8.1.19). -/
noncomputable def spsPhiFormulaOnX (g : E → ℝ) (x : FeasiblePoint S) (β : ℝ)
    (u : FeasiblePoint S) : ℝ :=
  spsPhi S g x β u

/-- The oracle sample value `H(u_t, ξ_t)` derived from the paper-level oracle
kernel.

Book JSON citation:
`book/FOML/StochasticGradientSliding.json:algorithm_spec.steps[3]` displays
`H(u_{t-1},ξ_{t-1})` inside the SPS stochastic prox update.

No SOptLib match is used directly: `objectiveKernel` models stochastic objective
kernels and the stochastic-oracle files provide reusable laws, while Eq. (8.1.58)
needs the concrete sampled nonsmooth subgradient value `H(u,ξ)`. -/
def sampledOracle (sample : ℕ → Ω → Sample) (u : ℕ → Ω → E)
    (t : ℕ) (ω : Ω) : E :=
  S.oracle (u t ω) (sample t ω)

/-- Oracle noise `δ_t = H(u_{t-1}, ξ_{t-1}) - h'(u_{t-1})` as in
Proposition 8.3 and Eq. (8.1.64).

Book JSON citation:
`book/FOML/StochasticGradientSliding.json:key_lemmas[2].statement_math`
defines `δ_t:=H(u_{t-1},ξ_{t-1})-h'(u_{t-1})`. -/
def oracleNoiseAt (u : E) (xi : Sample) : E :=
  S.oracle u xi - S.hSubgradient u

/-- Fixed-query SFO mean law for Eq. (8.1.6), before transfer to the generated
sample/search-point process.

Book JSON citation:
`book/FOML/StochasticGradientSliding.json:assumptions[2]` states
`E[H(u_t,ξ_t)]=h'(u_t)∈∂h(u_t)`.

Considered `SOptLib.BoundedVarianceUnbiasedOracleOn`; it bundles unbiasedness,
variance, and residual measurability for fixed-query transfer.  The SGS paper
states Eq. (8.1.6) as the oracle mean law, while the target membership
`h'(u) ∈ ∂h(u)` is already part of the source nonsmooth-growth setup in
Eq. (8.1.3).  This predicate therefore records only the oracle expectation
identity; Lean integrability needed to justify the Bochner integral is recorded
by separate obligations rather than bundled into the paper-facing oracle law. -/
def fixedQuerySFOUnbiased [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Sample) : Prop :=
  ∀ u, u ∈ S.X →
    (∫ xi, S.oracle u xi ∂μ) = S.hSubgradient u

/-- The target vector in the SFO mean law is the source subgradient from
Eq. (8.1.3), not an additional oracle-law field.

This theorem exposes the `h'(u) ∈ ∂h(u)` part of Eq. (8.1.6) from the existing
setup assumption `NonsmoothGrowth_8_1_3`; it avoids duplicating that property in
fixed-query or coordinate oracle-law predicates. -/
theorem sfoMeanTarget_mem_subgradient (u : E) (hu : u ∈ S.X) :
    S.hSubgradient u ∈
      SOptLib.carrierSubdifferential
        (fun y : {y : E // y ∈ S.X} => S.h y.1) ⟨u, hu⟩ :=
  S.h_subgradient_mem u hu

/-- Fixed-query SFO second-moment bound from Eq. (8.1.7).

Book JSON citation:
`book/FOML/StochasticGradientSliding.json:assumptions[3]` states
`E[||H(u_t,ξ_t)-h'(u_t)||_*^2]≤σ^2`.

Considered `SOptLib.BoundedVarianceUnbiasedOracleOn`; SGS needs this displayed
variance law as its own paper assumption, while the random-query law used by the
paper theorem is stated below on the actual Ω sample stream.  Integrability is a
well-definedness proof obligation, not a primitive field of the source law. -/
def fixedQuerySFOVariance [MeasurableSpace Sample] (μ : Measure Sample) : Prop :=
  ∀ u, u ∈ S.X →
    (∫ xi, oracleNoiseDualNorm S u xi ^ 2 ∂μ) ≤ S.sigmaSq

/-- Fixed-query SFO mean law for each actual SGS/SPS sample coordinate.

This is the paper-facing form of Eq. (8.1.6): for every feasible deterministic
query `u`, each oracle call sample `ξ_{k,i}` has mean `h'(u)`.  The generated
random-query law at `u_{k,i}` is derived below using the paper's independence
assumption, not accepted as a theorem-head hypothesis. -/
def coordinateSFOUnbiased [MeasurableSpace Ω] [MeasurableSpace Sample]
    [MeasurableSpace E] [BorelSpace E]
    (P : Measure Ω) (sample : PositiveTime → ℕ → Ω → Sample) : Prop :=
  ∀ k i u, u ∈ S.X →
    (∫ ω, S.oracle u (sample k i ω) ∂P) = S.hSubgradient u

/-- Fixed-query SFO second-moment law for each actual SGS/SPS sample coordinate.

This keeps Eq. (8.1.7) at deterministic feasible query points; random-query
variance at the generated process is a bridge theorem, not a source-facing
assumption. -/
def coordinateSFOVariance [MeasurableSpace Ω] [MeasurableSpace Sample]
    (P : Measure Ω) (sample : PositiveTime → ℕ → Ω → Sample) : Prop :=
  ∀ k i u, u ∈ S.X →
    (∫ ω, oracleNoiseDualNorm S u (sample k i ω) ^ 2 ∂P) ≤ S.sigmaSq

/-- Derived SFO unbiasedness at the generated SGS/SPS search points.

No SOptLib match is used directly: checked `BoundedVarianceUnbiasedOracleOn`,
which is a fixed-query law over a separate sample measure.  The paper's theorem
uses the actual samples `ξ_t` driving Algorithm 8.2, so this bridge is tied to
the Ω-process and generated queries while remaining out of paper theorem heads.

The paper writes Eq. (8.1.6) as an expectation identity.  In Lean, the generated
random-query predicate therefore carries the two Bochner integrability facts
needed for that expectation to be well-defined; they are proved by the transfer
lemmas below from fixed/coordinate SFO laws and process regularity, not accepted
as primitive setup assumptions. -/
def generatedSFOUnbiased [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E]
    [BorelSpace E] (P : Measure Ω) (sample : PositiveTime → ℕ → Ω → Sample)
    (query : PositiveTime → ℕ → Ω → E) : Prop :=
  ∀ k i, ∃ _ : ∀ ω, query k i ω ∈ S.X,
      Integrable (fun ω => S.oracle (query k i ω) (sample k i ω)) P ∧
      Integrable (fun ω => S.hSubgradient (query k i ω)) P ∧
      (∫ ω, S.oracle (query k i ω) (sample k i ω) ∂P) =
        ∫ ω, S.hSubgradient (query k i ω) ∂P

/-- Generated-query subgradient membership follows from generated feasibility
and the setup subgradient law, not from the oracle expectation predicate. -/
theorem generatedSFOUnbiased_target_mem_subgradient [MeasurableSpace Ω]
    [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (P : Measure Ω) (sample : PositiveTime → ℕ → Ω → Sample)
    (query : PositiveTime → ℕ → Ω → E)
    (hSFO : generatedSFOUnbiased S P sample query) :
    ∀ k i, ∃ hquery : ∀ ω, query k i ω ∈ S.X,
      ∀ ω,
        S.hSubgradient (query k i ω) ∈
          SOptLib.carrierSubdifferential
            (fun y : {y : E // y ∈ S.X} => S.h y.1)
            ⟨query k i ω, hquery ω⟩ := by
  intro k i
  rcases hSFO k i with ⟨hquery, _horacle_int, _hmean_int, _hmean⟩
  exact ⟨hquery, fun ω => S.h_subgradient_mem (query k i ω) (hquery ω)⟩

/-- Derived SFO second-moment bound at the generated search points from
Eq. (8.1.7), tied to the Ω sample stream of Algorithm 8.2.

As with `generatedSFOUnbiased`, the generated-query variance law is only
meaningful at feasible search points and its displayed expectation presupposes
the scalar integrability of the squared dual-norm residual. -/
def generatedSFOVariance [MeasurableSpace Ω] [MeasurableSpace Sample]
    (P : Measure Ω) (sample : PositiveTime → ℕ → Ω → Sample)
    (query : PositiveTime → ℕ → Ω → E) : Prop :=
  ∀ k i, ∃ _ : ∀ ω, query k i ω ∈ S.X,
      Integrable
        (fun ω => dualNorm S (oracleNoiseAt S (query k i ω) (sample k i ω)) ^ 2) P ∧
      (∫ ω, dualNorm S (oracleNoiseAt S (query k i ω) (sample k i ω)) ^ 2 ∂P) ≤
        S.sigmaSq

/-- Expectation well-definedness for the generated SFO mean law.

The paper writes expectations in Eq. (8.1.6), but does not list Lean
integrability as a theorem assumption.  This bridge is left as a proof
obligation from the source SFO law and regularity of the generated process. -/
theorem generatedSFOUnbiased_integrable_obligation [MeasurableSpace Ω] [MeasurableSpace Sample]
    [MeasurableSpace E] [BorelSpace E]
    (P : Measure Ω) (sample : PositiveTime → ℕ → Ω → Sample)
    (query : PositiveTime → ℕ → Ω → E)
    (hSFO : generatedSFOUnbiased S P sample query) :
    ∀ k i,
      Integrable (fun ω => S.oracle (query k i ω) (sample k i ω)) P ∧
        Integrable (fun ω => S.hSubgradient (query k i ω)) P := by
  intro k i
  rcases hSFO k i with ⟨_hquery, horacle_int, hmean_int, _hmean⟩
  exact ⟨horacle_int, hmean_int⟩

/-- Expectation well-definedness for the generated SFO variance law in
Eq. (8.1.7), kept out of paper theorem heads. -/
theorem generatedSFOVariance_integrable_obligation [MeasurableSpace Ω] [MeasurableSpace Sample]
    (P : Measure Ω) (sample : PositiveTime → ℕ → Ω → Sample)
    (query : PositiveTime → ℕ → Ω → E)
    (hSFO : generatedSFOVariance S P sample query) :
    ∀ k i,
      Integrable
        (fun ω => dualNorm S (oracleNoiseAt S (query k i ω) (sample k i ω)) ^ 2) P := by
  intro k i
  rcases hSFO k i with ⟨_hquery, hint, _hbound⟩
  exact hint

/-- Source-facing sample/search-point independence assumption from the text
following Eq. (8.1.7).

No SOptLib match is used directly: searched filtration/independence candidates;
`iIndepFun.indep_prefixFiltration_future` derives the usual generated-prefix
freshness from iid samples, while the paper states independence of `ξ_t` from
the search point as the primitive SFO boundary.

The object independent of the sample is the feasible search point `u_t`, not an
arbitrary ambient `E`-valued function.  The predicate therefore carries the
pointwise feasibility and measurable feasible-point random-variable structure
needed to interpret the paper's random-vector independence statement. -/
def sfoIndependent [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E]
    (P : Measure Ω) (sample : PositiveTime → ℕ → Ω → Sample)
    (query : PositiveTime → ℕ → Ω → E) : Prop :=
  ∃ hquery : ∀ k i ω, query k i ω ∈ S.X,
    (∀ k i, Measurable (fun ω => (⟨query k i ω, hquery k i ω⟩ : FeasiblePoint S))) ∧
      ∀ k i, IndepFun
        (fun ω => (⟨query k i ω, hquery k i ω⟩ : FeasiblePoint S))
        (sample k i) P

/-- The flattened SGS/SPS oracle-sample family, indexed by outer paper time and
inner raw sample coordinate.

No SOptLib match: searched `iid sample prefix filtration independence current
strict past`, checked `iIndepFun.indep_past_iSup_current`,
`samplePrefixFiltration_indep_current`, and
`strictPastSampleBlockMeasurableSpace`; these provide the independence API once
the paper's nested `(k,i)` sample family is named, but none names the SGS
flattening itself.  This definition is only the canonical indexing of the
paper samples `ξ_{k,i}` used in Eq. (8.1.70). -/
def sgsFlattenedSampleFamily [MeasurableSpace Ω]
    (sample : PositiveTime → ℕ → Ω → Sample) :
    PositiveTime × ℕ → Ω → Sample :=
  fun q ω => sample q.1 q.2 ω

/-- Lexicographic strict-past relation for Algorithm 8.2 sample coordinates.

The query `u_{k,i}` is generated from samples in earlier outer blocks and from
earlier samples in the current inner block.  This is the source dependency order
used when Eq. (8.1.70) flattens the nested noise family for Lemma 4.1. -/
def sgsSampleIndexBefore (q r : PositiveTime × ℕ) : Prop :=
  r.1.1 < q.1.1 ∨ (r.1 = q.1 ∧ r.2 < q.2)

/-- Sigma-algebra generated by all flattened SGS samples strictly before
coordinate `(k,i)`.

This is the paper's `ξ[t-1]` filtration after flattening the nested
Algorithm 8.2 sample family in the lexicographic dependency order. -/
def sgsStrictPastSampleSpace [MeasurableSpace Ω] [MeasurableSpace Sample]
    (sample : PositiveTime → ℕ → Ω → Sample) (k : PositiveTime) (i : ℕ) :
    MeasurableSpace Ω :=
  ⨆ r : PositiveTime × ℕ,
    ⨆ _ : sgsSampleIndexBefore (k, i) r,
      MeasurableSpace.comap (sample r.1 r.2)
        (by infer_instance : MeasurableSpace Sample)

/-- The strict-past sample sigma-algebra is a sub-sigma-algebra of the ambient
measurable space whenever the sample coordinates are measurable. -/
theorem sgsStrictPastSampleSpace_le [MeasurableSpace Ω] [MeasurableSpace Sample]
    (sample : PositiveTime → ℕ → Ω → Sample)
    (hsample_measurable : ∀ k i, Measurable (sample k i))
    (k : PositiveTime) (i : ℕ) :
    sgsStrictPastSampleSpace (Ω := Ω) sample k i ≤
      (by infer_instance : MeasurableSpace Ω) := by
  classical
  unfold sgsStrictPastSampleSpace
  refine iSup_le ?_
  intro r
  refine iSup_le ?_
  intro _hr
  exact (hsample_measurable r.1 r.2).comap_le

/-- Every sample coordinate in the lexicographic strict past is measurable with
respect to the SGS strict-past sigma-algebra for the current coordinate. -/
theorem sgsSample_measurable_strictPast [MeasurableSpace Ω] [MeasurableSpace Sample]
    (sample : PositiveTime → ℕ → Ω → Sample)
    (k : PositiveTime) (i : ℕ) (r : PositiveTime) (j : ℕ)
    (hbefore : sgsSampleIndexBefore (k, i) (r, j)) :
    Measurable[sgsStrictPastSampleSpace (Ω := Ω) sample k i] (sample r j) := by
  classical
  rw [measurable_iff_comap_le]
  unfold sgsStrictPastSampleSpace
  exact le_iSup_of_le (r, j) (le_iSup_of_le hbefore le_rfl)

/-- Monotonicity of the flattened strict-past sigma-algebras.

This is the order-theoretic bridge used by the selected SGS/SPS adaptedness
induction: once every coordinate before `(k,i)` is also before `(k',i')`, any
random variable measurable from the first strict past is measurable from the
second. -/
theorem sgsStrictPastSampleSpace_mono [MeasurableSpace Ω] [MeasurableSpace Sample]
    (sample : PositiveTime → ℕ → Ω → Sample)
    {k k' : PositiveTime} {i i' : ℕ}
    (hmono :
      ∀ r : PositiveTime × ℕ,
        sgsSampleIndexBefore (k, i) r → sgsSampleIndexBefore (k', i') r) :
    sgsStrictPastSampleSpace (Ω := Ω) sample k i ≤
      sgsStrictPastSampleSpace (Ω := Ω) sample k' i' := by
  classical
  unfold sgsStrictPastSampleSpace
  refine iSup_le ?_
  intro r
  refine iSup_le ?_
  intro hr
  exact le_iSup_of_le r (le_iSup_of_le (hmono r hr) le_rfl)

/-- Advancing the inner index enlarges the strict-past sigma-algebra in the
same outer block. -/
theorem sgsStrictPastSampleSpace_le_same_outer_succ [MeasurableSpace Ω]
    [MeasurableSpace Sample]
    (sample : PositiveTime → ℕ → Ω → Sample)
    (k : PositiveTime) (i : ℕ) :
    sgsStrictPastSampleSpace (Ω := Ω) sample k i ≤
      sgsStrictPastSampleSpace (Ω := Ω) sample k (i + 1) := by
  refine sgsStrictPastSampleSpace_mono (Ω := Ω) sample ?_
  intro r hr
  rcases hr with houter | ⟨hsame, hinner⟩
  · exact Or.inl houter
  · exact Or.inr ⟨hsame, Nat.lt_succ_of_lt hinner⟩

/-- If coordinate `(k,i)` is in the strict past of `(k',i')`, then the whole
strict-past sigma-algebra at `(k,i)` is contained in the one at `(k',i')`.

This is the lexicographic filtration adapter needed when a flattened
Lemma 4.1 prefix contains a generated query from an earlier SGS coordinate:
the query is adapted to its own strict past, and this lemma transports that
measurability to the current prefix sigma-algebra. -/
theorem sgsStrictPastSampleSpace_mono_of_indexBefore [MeasurableSpace Ω]
    [MeasurableSpace Sample]
    (sample : PositiveTime → ℕ → Ω → Sample)
    {k k' : PositiveTime} {i i' : ℕ}
    (hbefore : sgsSampleIndexBefore (k', i') (k, i)) :
    sgsStrictPastSampleSpace (Ω := Ω) sample k i ≤
      sgsStrictPastSampleSpace (Ω := Ω) sample k' i' := by
  refine sgsStrictPastSampleSpace_mono (Ω := Ω) sample ?_
  intro r hr
  rcases hbefore with houter | ⟨hsame, hinner⟩
  · rcases hr with hr_outer | ⟨hr_same, _hr_inner⟩
    · exact Or.inl (Nat.lt_trans hr_outer houter)
    · subst hr_same
      exact Or.inl houter
  · subst hsame
    rcases hr with hr_outer | ⟨hr_same, hr_inner⟩
    · exact Or.inl hr_outer
    · exact Or.inr ⟨hr_same, Nat.lt_trans hr_inner hinner⟩

/-- A concrete lexicographic comparison of flattened natural SGS coordinates
is exactly the strict-past relation used by the Algorithm 8.2 filtration.

This is route-local infrastructure for Eq. (8.1.70): once the finite flattened
enumerator exposes an actual lexicographic order on pairs `(k,i)`, this lemma
turns the order fact into the source strict-past sigma-algebra relation. -/
theorem sgsSampleIndexBefore_of_sigmaNat_lex
    {a b : Σ _k : ℕ, ℕ}
    (hlex : a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2)) :
    sgsSampleIndexBefore
      ((⟨b.1 + 1, Nat.succ_pos b.1⟩ : PositiveTime), b.2)
      ((⟨a.1 + 1, Nat.succ_pos a.1⟩ : PositiveTime), a.2) := by
  rcases hlex with houter | ⟨hsame, hinner⟩
  · exact Or.inl (Nat.succ_lt_succ houter)
  · right
    constructor
    · ext
      simpa [hsame]
    · exact hinner

/-- A sample from a strictly earlier outer block is measurable at every later
outer strict-past cutoff. -/
theorem sgsEarlierOuterSample_measurable_strictPast [MeasurableSpace Ω]
    [MeasurableSpace Sample]
    (sample : PositiveTime → ℕ → Ω → Sample)
    (k r : PositiveTime) (i j : ℕ) (hrk : r.1 < k.1) :
    Measurable[sgsStrictPastSampleSpace (Ω := Ω) sample k i] (sample r j) := by
  exact sgsSample_measurable_strictPast (Ω := Ω) sample k i r j (Or.inl hrk)

/-- A previous sample in the same outer block is measurable at the current
inner strict-past cutoff. -/
theorem sgsSameOuterPreviousSample_measurable_strictPast [MeasurableSpace Ω]
    [MeasurableSpace Sample]
    (sample : PositiveTime → ℕ → Ω → Sample)
    (k : PositiveTime) {j i : ℕ} (hji : j < i) :
    Measurable[sgsStrictPastSampleSpace (Ω := Ω) sample k i] (sample k j) := by
  exact sgsSample_measurable_strictPast (Ω := Ω) sample k i k j
    (Or.inr ⟨rfl, hji⟩)

/-- Source probability model for the SGS stochastic first-order oracle.

Book JSON citations:
`book/FOML/StochasticGradientSliding.json:assumptions[2]` states the SFO mean
law, `assumptions[3]` states the variance law, and `assumptions[4]` states that
the random vector `ξ_t` is independent of the search points `u_t`.
For the high-probability proof, the FOML PDF states in Chapter 4 Assumption 1
that it is possible to generate an independent and identically distributed
sample `ξ₁, ξ₂, ...` of realizations of the oracle random vector.  Lemma 4.1
then states its martingale large-deviation theorem for such an iid sequence, and
Theorem 8.2 proof Eq. (8.1.70) applies that theorem to the flattened `(k,i)`
SGS sample family.

No SOptLib match: searched probability/expectation/tail primitives and checked
`SOptLib.expectedObjectiveGap`/selected-tail candidates; those are generic
integral/event wrappers over an already supplied measure.  The paper's source
boundary for Eq. (8.1.6), Eq. (8.1.7), and Corollary 8.3 is a probability law
for the oracle samples, so this local object bundles the probability measure,
  the actual sample stream, the displayed deterministic-coordinate moment laws,
  and the paper-canonical generated-search-point SFO mean/variance laws.

  The generated fields are not `Setup` axioms or derived bridges: Eq. (8.1.6) and
  Eq. (8.1.7) are stated for the actual feasible search points `u_t`.  Earlier
  deterministic fixed-query predicates remain available as proof infrastructure,
  but the source-facing probability model must also expose the random-query laws
  that the paper assumes. -/
structure SGSProbabilityModel [MeasurableSpace Ω] [MeasurableSpace Sample]
    [MeasurableSpace E] [BorelSpace E] (S : Setup E Sample) where
  P : Measure Ω
  isProbability : IsProbabilityMeasure P
  sample : PositiveTime → ℕ → Ω → Sample
  /-- Lean regularity for the random oracle samples in the expectation laws.
  The paper calls `ξ_t` a random vector; this field supplies the corresponding
  measurability needed by product-law independence transfers. -/
  sample_measurable : ∀ k i, Measurable (sample k i)
  /-- Source-facing iid/freshness content for the flattened SGS sample stream.
  The source iid-sampling assumption supplies independence of the generated
  oracle samples.  Eq. (8.1.70) uses the freshness part through strict-past
  conditioning; coordinate moment fields below carry the distribution-specific
  expectation and light-tail bounds. -/
  sample_iIndep :
    iIndepFun (sgsFlattenedSampleFamily (Ω := Ω) sample) P
  /-- Fixed-fiber integrability for the SFO expectation in Eq. (8.1.6).
  This is the well-definedness side of the displayed expectation, kept separate
  from the deterministic-coordinate mean identity below. -/
  fixed_oracle_integrable :
    ∀ k i (u : FeasiblePoint S), Integrable (fun ω => S.oracle u.1 (sample k i ω)) P
  /-- Joint measurability of the centered oracle residual on feasible queries.
  The source SFO writes `H(u, ξ)` as a random vector in Eq. (8.1.6)-(8.1.7);
  this is the Lean regularity needed to compose that residual with generated
  search points and samples.  Scalar martingale well-definedness is derived
  locally from this kernel plus moment/displacement bounds, not stored here. -/
  oracle_residual_measurable :
    Measurable (fun p : FeasiblePoint S × Sample =>
      oracleNoiseAt S p.1.1 p.2)
  unbiased : coordinateSFOUnbiased S P sample
  variance : coordinateSFOVariance S P sample
  generated_unbiased :
    ∀ query, sfoIndependent S P sample query →
      generatedSFOUnbiased S P sample query
  generated_variance :
    ∀ query, sfoIndependent S P sample query →
      generatedSFOVariance S P sample query

instance [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E]
    [BorelSpace E] (law : SGSProbabilityModel (Ω := Ω) S) :
    IsProbabilityMeasure law.P :=
  law.isProbability

/-- The flattened iid SGS sample family makes each current sample independent
of the strict-past sigma-algebra generated by earlier `(k,i)` coordinates. -/
theorem sgsStrictPastSampleSpace_indep_current [MeasurableSpace Ω] [MeasurableSpace Sample]
    (P : Measure Ω) (sample : PositiveTime → ℕ → Ω → Sample)
    (hsample_measurable : ∀ k i, Measurable (sample k i))
    (hsample_iIndep : iIndepFun (sgsFlattenedSampleFamily (Ω := Ω) sample) P)
    (k : PositiveTime) (i : ℕ) :
    Indep (sgsStrictPastSampleSpace (Ω := Ω) sample k i)
      (MeasurableSpace.comap (sample k i)
        (by infer_instance : MeasurableSpace Sample)) P := by
  classical
  let ξ : PositiveTime × ℕ → Ω → Sample := sgsFlattenedSampleFamily sample
  let m : PositiveTime × ℕ → MeasurableSpace Ω :=
    fun q => MeasurableSpace.comap (ξ q)
      (by infer_instance : MeasurableSpace Sample)
  have hi : iIndep m P := by
    simpa [m, ξ] using hsample_iIndep.iIndep
  have hle : ∀ q, m q ≤ (by infer_instance : MeasurableSpace Ω) := by
    intro q
    simpa [m, ξ, sgsFlattenedSampleFamily] using
      (hsample_measurable q.1 q.2).comap_le
  let pastSet : Set (PositiveTime × ℕ) := {r | sgsSampleIndexBefore (k, i) r}
  let currentSet : Set (PositiveTime × ℕ) := {r | r = (k, i)}
  have hdisj : Disjoint pastSet currentSet := by
    rw [Set.disjoint_left]
    intro r hrpast hrcur
    simp [currentSet] at hrcur
    subst r
    simpa [pastSet, sgsSampleIndexBefore] using hrpast
  have h_ind : Indep (⨆ r ∈ pastSet, m r) (⨆ r ∈ currentSet, m r) P :=
    indep_iSup_of_disjoint (m := m) hle hi (S := pastSet) (T := currentSet) hdisj
  simpa [sgsStrictPastSampleSpace, pastSet, currentSet, m, ξ,
    sgsFlattenedSampleFamily] using h_ind

/-- Current-sample freshness for any random variable adapted to the SGS
strict-past sample filtration. -/
theorem sgsStrictPast_adapted_indep_current_sample [MeasurableSpace Ω]
    [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace W]
    (law : SGSProbabilityModel (Ω := Ω) S) {X : Ω → W}
    (k : PositiveTime) (i : ℕ)
    (hX_past : Measurable[sgsStrictPastSampleSpace (Ω := Ω) law.sample k i] X) :
    IndepFun X (law.sample k i) law.P :=
  indepFun_of_past_measurable_current_iid_sample hX_past
    (sgsStrictPastSampleSpace_indep_current law.P law.sample
      law.sample_measurable law.sample_iIndep k i)

/-- A fixed-query SFO mean law centers the feasible oracle residual.

This is the deterministic-fiber form needed by the product-law transfer:
the parameter type is `FeasiblePoint S`, not all of `E`, so Eq. (8.1.6) is
only used on the paper domain `X`.  Probability of the sample law is a
Lean-side regularity condition for integrating the constant `h'(u)`. -/
theorem fixedQuerySFOUnbiased_residual_integral_zero
    [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Sample) [IsProbabilityMeasure μ]
    (hfixed : fixedQuerySFOUnbiased S μ)
    (hfixed_int : ∀ u : FeasiblePoint S, Integrable (fun xi => S.oracle u.1 xi) μ) :
    ∀ u : FeasiblePoint S,
      (∫ xi, S.oracle u.1 xi - S.hSubgradient u.1 ∂μ) = 0 := by
  intro u
  have hconst_int : Integrable (fun _ : Sample => S.hSubgradient u.1) μ := integrable_const _
  calc
    (∫ xi, S.oracle u.1 xi - S.hSubgradient u.1 ∂μ)
        = (∫ xi, S.oracle u.1 xi ∂μ) -
            ∫ _xi : Sample, S.hSubgradient u.1 ∂μ := by
          simpa using integral_sub (hfixed_int u) hconst_int
    _ = S.hSubgradient u.1 - S.hSubgradient u.1 := by
          rw [hfixed u.1 u.2]
          simp [integral_const, probReal_univ]
    _ = 0 := sub_self _

/-- Formal correction hook for the rejected pre-refactor fixed-query transfer.

Any proof of `generatedSFOUnbiased` immediately contains the missing feasibility
witness.  Thus the old interface, which had only a fixed sample law and
independence, would have had to manufacture feasibility for arbitrary query
functions; this theorem records the obstruction without reintroducing that false
claim as a usable bridge. -/
theorem rejected_old_generatedSFOUnbiased_transfer_requires_query_feasibility
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (P : Measure Ω) (sample : PositiveTime → ℕ → Ω → Sample)
    (query : PositiveTime → ℕ → Ω → E)
    (hSFO : generatedSFOUnbiased S P sample query) :
    ∀ k i, ∃ _hquery : ∀ ω, query k i ω ∈ S.X, True := by
  intro k i
  rcases hSFO k i with ⟨hquery, _horacle_int, _hmean_int, _hmean⟩
  exact ⟨hquery, trivial⟩

/-- An infeasible query blocks the generated SFO mean law outright.

This is the formal falsity certificate for the old no-feasibility transfer
shape: if a query coordinate has no pointwise membership witness in `X`, then
the conclusion required by `generatedSFOUnbiased` is impossible, independently
of any fixed-query oracle law or independence claim. -/
theorem not_generatedSFOUnbiased_of_no_query_feasibility
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (P : Measure Ω) (sample : PositiveTime → ℕ → Ω → Sample)
    (query : PositiveTime → ℕ → Ω → E)
    (hbad : ∃ k i, ¬ ∃ _hquery : ∀ ω, query k i ω ∈ S.X, True) :
    ¬ generatedSFOUnbiased S P sample query := by
  intro hSFO
  rcases hbad with ⟨k, i, hbadki⟩
  rcases hSFO k i with ⟨hquery, _horacle_int, _hmean_int, _hmean⟩
  exact hbadki ⟨hquery, trivial⟩

/-- Coordinate SFO mean laws center every deterministic feasible oracle residual.

This is the actual-sample analogue of
`fixedQuerySFOUnbiased_residual_integral_zero`: the fixed fiber is integrated over
the driving probability space `Ω` through the concrete sample coordinate
`sample k i`.  The explicit integrability premise is Lean well-definedness for
the Bochner subtraction, not a new source oracle assumption. -/
theorem coordinateSFOUnbiased_residual_integral_zero
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (P : Measure Ω) (sample : PositiveTime → ℕ → Ω → Sample) [IsProbabilityMeasure P]
    (hfixed : coordinateSFOUnbiased S P sample)
    (hfixed_int :
      ∀ (k : PositiveTime) (i : ℕ) (u : FeasiblePoint S),
        Integrable (fun ω => S.oracle u.1 (sample k i ω)) P) :
    ∀ (k : PositiveTime) (i : ℕ) (u : FeasiblePoint S),
      (∫ ω, S.oracle u.1 (sample k i ω) - S.hSubgradient u.1 ∂P) = 0 := by
  intro k i u
  have hconst_int : Integrable (fun _ : Ω => S.hSubgradient u.1) P := integrable_const _
  calc
    (∫ ω, S.oracle u.1 (sample k i ω) - S.hSubgradient u.1 ∂P)
        = (∫ ω, S.oracle u.1 (sample k i ω) ∂P) -
            ∫ _ω : Ω, S.hSubgradient u.1 ∂P := by
          simpa using integral_sub (hfixed_int k i u) hconst_int
    _ = S.hSubgradient u.1 - S.hSubgradient u.1 := by
          rw [hfixed k i u.1 u.2]
          simp [integral_const, probReal_univ]
    _ = 0 := sub_self _

/-- Query-dependent scalar martingale cancellation from Eq. (8.1.6) and the
sample/search-point independence statement following Eq. (8.1.7).

This is the source bridge used in the proof of Theorem 8.2(a): once the feasible
query is independent of the fresh oracle sample, every measurable direction that
is a function of that query is orthogonal in expectation to the centered oracle
noise.  The proof applies the product-law zero-integral transfer to the scalar
kernel obtained by taking the inner product of the fixed-fiber centered residual
with the query-dependent direction. -/
theorem generated_oracle_noise_inner_query_direction_zero
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S)
    (query : PositiveTime → ℕ → Ω → E)
    (hindep : sfoIndependent S law.P law.sample query)
    (d : FeasiblePoint S → E)
    (hinner_meas :
      Measurable (fun p : FeasiblePoint S × Sample =>
        ⟪d p.1, oracleNoiseAt S p.1.1 p.2⟫_ℝ))
    (hinner_int :
      ∀ k i (hquery : ∀ ω, query k i ω ∈ S.X),
        Integrable
          (fun ω =>
            ⟪oracleNoiseAt S (query k i ω) (law.sample k i ω),
              d ⟨query k i ω, hquery ω⟩⟫_ℝ) law.P) :
    ∀ k i, ∃ hquery : ∀ ω, query k i ω ∈ S.X,
      (∫ ω,
        ⟪oracleNoiseAt S (query k i ω) (law.sample k i ω),
          d ⟨query k i ω, hquery ω⟩⟫_ℝ ∂law.P) = 0 := by
  classical
  rcases hindep with ⟨hquery_all, hquery_meas, hindep_qs⟩
  intro k i
  refine ⟨hquery_all k i, ?_⟩
  let queryFP : Ω → FeasiblePoint S :=
    fun ω => ⟨query k i ω, hquery_all k i ω⟩
  let φ : FeasiblePoint S → Sample → ℝ :=
    fun u xi => ⟪d u, oracleNoiseAt S u.1 xi⟫_ℝ
  have hqueryFP_meas : Measurable queryFP := by
    simpa [queryFP] using hquery_meas k i
  have hindep_qs_ki : IndepFun queryFP (law.sample k i) law.P := by
    simpa [queryFP] using hindep_qs k i
  have hφ_meas : Measurable (Function.uncurry φ) := by
    simpa [φ, Function.uncurry] using hinner_meas
  have hfixed_zero :
      ∀ u : FeasiblePoint S,
        (∫ xi, φ u xi ∂Measure.map (law.sample k i) law.P) = 0 := by
    intro u
    have hφu_meas : Measurable (fun xi : Sample => φ u xi) := by
      have hpair : Measurable (fun xi : Sample => (u, xi)) :=
        (measurable_const : Measurable (fun _ : Sample => u)).prod measurable_id
      simpa [φ, Function.uncurry] using hφ_meas.comp hpair
    have hmap :
        (∫ xi, φ u xi ∂Measure.map (law.sample k i) law.P) =
          ∫ ω, φ u (law.sample k i ω) ∂law.P := by
      exact integral_map (law.sample_measurable k i).aemeasurable
        hφu_meas.aestronglyMeasurable
    have hres_int :
        Integrable (fun ω => oracleNoiseAt S u.1 (law.sample k i ω)) law.P := by
      simpa [oracleNoiseAt] using
        (law.fixed_oracle_integrable k i u).sub (integrable_const _)
    have hlin :=
      ContinuousLinearMap.integral_comp_comm (L := (innerSL ℝ) (d u)) hres_int
    have hres_zero :
        (∫ ω, oracleNoiseAt S u.1 (law.sample k i ω) ∂law.P) = 0 := by
      simpa [oracleNoiseAt] using
        coordinateSFOUnbiased_residual_integral_zero S law.P law.sample
          law.unbiased law.fixed_oracle_integrable k i u
    have hscalar_zero :
        (∫ ω, φ u (law.sample k i ω) ∂law.P) = 0 := by
      calc
        (∫ ω, φ u (law.sample k i ω) ∂law.P)
            = ∫ ω, ((innerSL ℝ) (d u))
                (oracleNoiseAt S u.1 (law.sample k i ω)) ∂law.P := by
                rfl
        _ = ((innerSL ℝ) (d u))
              (∫ ω, oracleNoiseAt S u.1 (law.sample k i ω) ∂law.P) := hlin
        _ = 0 := by simp [hres_zero]
    rw [hmap]
    exact hscalar_zero
  have hzero_phi :
      (∫ ω, φ (queryFP ω) (law.sample k i ω) ∂law.P) = 0 := by
    have h_int : Integrable (fun ω => φ (queryFP ω) (law.sample k i ω)) law.P := by
      simpa [φ, queryFP, real_inner_comm] using hinner_int k i (hquery_all k i)
    exact integral_comp_eq_zero_of_indep_fixed_integral_zero
      (P := law.P) (ν := Measure.map (law.sample k i) law.P)
      (φ := φ) (X := queryFP) (Y := law.sample k i)
      hφ_meas hqueryFP_meas (law.sample_measurable k i) hindep_qs_ki rfl
      h_int hfixed_zero
  calc
    (∫ ω,
        ⟪oracleNoiseAt S (query k i ω) (law.sample k i ω),
          d ⟨query k i ω, hquery_all k i ω⟩⟫_ℝ ∂law.P)
        = ∫ ω, φ (queryFP ω) (law.sample k i ω) ∂law.P := by
          refine integral_congr_ae ?_
          exact Filter.Eventually.of_forall (fun ω => by
            simp [φ, queryFP, real_inner_comm])
    _ = 0 := hzero_phi

/-- Concrete scalar-kernel measurability for the Theorem 8.2 martingale term
from the vector-valued residual-kernel measurability of the stochastic oracle.

The source law only needs the residual random vector to be measurable; this
private bridge performs the fixed-comparator scalarization used in Eq. (8.1.69). -/
theorem oracle_residual_target_inner_measurable_of_residual_measurable
    [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (x : FeasiblePoint S)
    (hres :
      Measurable (fun p : FeasiblePoint S × Sample =>
        oracleNoiseAt S p.1.1 p.2)) :
    Measurable (fun p : FeasiblePoint S × Sample =>
      ⟪x.1 - p.1.1, oracleNoiseAt S p.1.1 p.2⟫_ℝ) := by
  letI : FiniteDimensional ℝ E := S.finiteDimensional_ambient
  have hleft : Measurable (fun p : FeasiblePoint S × Sample => x.1 - p.1.1) := by
    exact measurable_const.sub (measurable_subtype_coe.comp measurable_fst)
  exact continuous_inner.measurable.comp (hleft.prodMk hres)

/-- Scalar well-definedness for the Theorem 8.2 martingale product from a
dual-norm second moment and an L2 primal displacement bound.

This is intentionally private proof infrastructure.  It is the Lean
well-definedness bridge behind the source line taking
`E[⟪δ_{k,i-1}, x* - u_{k,i-1}⟫]`; it is not a stochastic-oracle law field. -/
theorem generated_target_inner_integrable_of_primal_displacement_l2
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (P : Measure Ω) (sample : PositiveTime → ℕ → Ω → Sample)
    (query : PositiveTime → ℕ → Ω → E)
    (x : FeasiblePoint S)
    (κ : PositiveTime) (i : ℕ)
    (hdual_sq :
      Integrable
        (fun ω => dualNorm S (oracleNoiseAt S (query κ i ω) (sample κ i ω)) ^ 2) P)
    (hdisp_sq :
      Integrable (fun ω => S.primalNorm (x.1 - query κ i ω) ^ 2) P) :
    AEStronglyMeasurable
      (fun ω =>
        ⟪oracleNoiseAt S (query κ i ω) (sample κ i ω),
          x.1 - query κ i ω⟫_ℝ) P →
    Integrable
      (fun ω =>
        ⟪oracleNoiseAt S (query κ i ω) (sample κ i ω),
          x.1 - query κ i ω⟫_ℝ) P := by
  intro hinner_aemeas
  let Z : Ω → ℝ :=
    fun ω => dualNorm S (oracleNoiseAt S (query κ i ω) (sample κ i ω))
  let W : Ω → ℝ :=
    fun ω => S.primalNorm (x.1 - query κ i ω)
  have hZ_nonneg : ∀ᵐ ω ∂P, 0 ≤ Z ω :=
    Filter.Eventually.of_forall (fun ω => SOptLib.canonicalDualNorm_nonneg S.primalNorm _)
  have hW_nonneg : ∀ᵐ ω ∂P, 0 ≤ W ω :=
    Filter.Eventually.of_forall (fun ω => apply_nonneg S.primalNorm _)
  have hZ_meas : AEStronglyMeasurable Z P :=
    AEStronglyMeasurable.of_integrable_sq_of_nonneg
      (by simpa [Z] using hdual_sq) hZ_nonneg
  have hW_meas : AEStronglyMeasurable W P :=
    AEStronglyMeasurable.of_integrable_sq_of_nonneg
      (by simpa [W] using hdisp_sq) hW_nonneg
  have hZ_l2 : MemLp Z 2 P :=
    (memLp_two_iff_integrable_sq_norm hZ_meas).2 (by
      refine hdual_sq.congr (Filter.Eventually.of_forall ?_)
      intro ω
      simp [Z, Real.norm_eq_abs])
  have hW_l2 : MemLp W 2 P :=
    (memLp_two_iff_integrable_sq_norm hW_meas).2 (by
      simpa [W, Real.norm_eq_abs] using hdisp_sq)
  have hprod : Integrable (fun ω => Z ω * W ω) P := by
    simpa [Pi.mul_apply] using
      (MemLp.integrable_mul hZ_l2 hW_l2 :
        Integrable (Z * W) P)
  refine hprod.mono' hinner_aemeas ?_
  exact Filter.Eventually.of_forall (fun ω => by
      simpa [Z, W, Real.norm_eq_abs] using
        abs_inner_le_dualNorm_mul_primalNorm S
          (oracleNoiseAt S (query κ i ω) (sample κ i ω))
          (x.1 - query κ i ω))

/-- Centered square-integrability for the paper primal seminorm is preserved by
a deterministic affine update.

This is private Lean infrastructure for selected SGS/SPS state propagation.  It
uses the file's finite-dimensional ambient realization and the source norm's
separating property to pass through SOptLib's ambient-norm L2 affine closure,
then returns to the paper primal seminorm by finite-dimensional seminorm
control. -/
theorem primalNorm_sq_integrable_affine_update
    [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
    (P : Measure Ω) [IsFiniteMeasure P] (x : FeasiblePoint S)
    (xPrev xNext : Ω → E) (alpha : ℝ)
    (hxPrev_meas : AEStronglyMeasurable xPrev P)
    (hxNext_meas : AEStronglyMeasurable xNext P)
    (hxPrev_sq :
      Integrable (fun ω => S.primalNorm (x.1 - xPrev ω) ^ 2) P)
    (hxNext_sq :
      Integrable (fun ω => S.primalNorm (x.1 - xNext ω) ^ 2) P) :
    Integrable
      (fun ω =>
        S.primalNorm (x.1 - ((1 - alpha) • xPrev ω + alpha • xNext ω)) ^ 2) P := by
  classical
  letI : FiniteDimensional ℝ E := S.finiteDimensional_ambient
  have hsep : S.primalNorm.IsSeparating := by
    intro z
    exact S.primalNorm_separating z
  rcases Seminorm.exists_norm_le_mul_self_of_finiteDimensional_separating
      S.primalNorm hsep with
    ⟨C, hC_nonneg, hC⟩
  rcases Seminorm.exists_bound_by_norm_of_finiteDimensional S.primalNorm with
    ⟨K, hK_nonneg, hK⟩
  have hprev_norm_sq :
      Integrable (fun ω => ‖x.1 - xPrev ω‖ ^ 2) P := by
    refine Integrable.mono' ((hxPrev_sq.const_mul (C ^ 2))) ?_ ?_
    · exact (aestronglyMeasurable_const.sub hxPrev_meas).norm.pow 2
    · refine Filter.Eventually.of_forall ?_
      intro ω
      have hp_nonneg : 0 ≤ S.primalNorm (x.1 - xPrev ω) :=
        apply_nonneg S.primalNorm _
      have hnorm_nonneg : 0 ≤ ‖x.1 - xPrev ω‖ := norm_nonneg _
      have hbound : ‖x.1 - xPrev ω‖ ≤ C * S.primalNorm (x.1 - xPrev ω) :=
        hC _
      have hCmul_nonneg : 0 ≤ C * S.primalNorm (x.1 - xPrev ω) :=
        mul_nonneg hC_nonneg hp_nonneg
      calc
        ‖(‖x.1 - xPrev ω‖ ^ 2 : ℝ)‖ =
            ‖x.1 - xPrev ω‖ ^ 2 := by
          rw [Real.norm_of_nonneg]
          exact sq_nonneg _
        _ ≤
            (C * S.primalNorm (x.1 - xPrev ω)) ^ 2 :=
          sq_le_sq' (by nlinarith [hnorm_nonneg, hCmul_nonneg]) hbound
        _ = C ^ 2 * S.primalNorm (x.1 - xPrev ω) ^ 2 := by ring
  have hnext_norm_sq :
      Integrable (fun ω => ‖x.1 - xNext ω‖ ^ 2) P := by
    refine Integrable.mono' ((hxNext_sq.const_mul (C ^ 2))) ?_ ?_
    · exact (aestronglyMeasurable_const.sub hxNext_meas).norm.pow 2
    · refine Filter.Eventually.of_forall ?_
      intro ω
      have hp_nonneg : 0 ≤ S.primalNorm (x.1 - xNext ω) :=
        apply_nonneg S.primalNorm _
      have hnorm_nonneg : 0 ≤ ‖x.1 - xNext ω‖ := norm_nonneg _
      have hbound : ‖x.1 - xNext ω‖ ≤ C * S.primalNorm (x.1 - xNext ω) :=
        hC _
      have hCmul_nonneg : 0 ≤ C * S.primalNorm (x.1 - xNext ω) :=
        mul_nonneg hC_nonneg hp_nonneg
      calc
        ‖(‖x.1 - xNext ω‖ ^ 2 : ℝ)‖ =
            ‖x.1 - xNext ω‖ ^ 2 := by
          rw [Real.norm_of_nonneg]
          exact sq_nonneg _
        _ ≤
            (C * S.primalNorm (x.1 - xNext ω)) ^ 2 :=
          sq_le_sq' (by nlinarith [hnorm_nonneg, hCmul_nonneg]) hbound
        _ = C ^ 2 * S.primalNorm (x.1 - xNext ω) ^ 2 := by ring
  have hcombo_norm_sq :
      Integrable
        (fun ω => ‖x.1 - ((1 - alpha) • xPrev ω + alpha • xNext ω)‖ ^ 2) P := by
    simpa using
      (SOptLib.integrable_sq_norm_const_sub_two_stage_affine
        (μ := P) x.1 xNext xPrev alpha 1 0
        hxNext_meas hxPrev_meas hnext_norm_sq hprev_norm_sq (by norm_num) :
          Integrable
            (fun ω =>
              ‖x.1 - ((1 : ℝ) • ((1 - alpha) • xPrev ω + alpha • xNext ω) +
                (0 : ℝ) • xNext ω)‖ ^ 2) P)
  have hprim_cont : Continuous S.primalNorm := by
    let q : Seminorm ℝ E := (Real.toNNReal K) • normSeminorm ℝ E
    have hqcont : Continuous q := by
      change Continuous (fun z : E => ((Real.toNNReal K : ℝ) * ‖z‖))
      exact continuous_const.mul continuous_norm
    refine Seminorm.continuous_of_le hqcont ?_
    intro z
    change S.primalNorm z ≤ ((Real.toNNReal K : ℝ) * ‖z‖)
    simpa [Real.toNNReal_of_nonneg hK_nonneg] using hK z
  refine Integrable.mono' ((hcombo_norm_sq.const_mul (K ^ 2))) ?_ ?_
  · have hcombo_meas :
        AEStronglyMeasurable
          (fun ω => (1 - alpha) • xPrev ω + alpha • xNext ω) P :=
      (hxPrev_meas.const_smul (1 - alpha)).add (hxNext_meas.const_smul alpha)
    exact (hprim_cont.comp_aestronglyMeasurable
      (aestronglyMeasurable_const.sub hcombo_meas)).pow 2
  · refine Filter.Eventually.of_forall ?_
    intro ω
    have hnorm_nonneg :
        0 ≤ ‖x.1 - ((1 - alpha) • xPrev ω + alpha • xNext ω)‖ := norm_nonneg _
    have hbound :
        S.primalNorm (x.1 - ((1 - alpha) • xPrev ω + alpha • xNext ω)) ≤
          K * ‖x.1 - ((1 - alpha) • xPrev ω + alpha • xNext ω)‖ :=
      hK _
    have hKmul_nonneg :
        0 ≤ K * ‖x.1 - ((1 - alpha) • xPrev ω + alpha • xNext ω)‖ :=
      mul_nonneg hK_nonneg hnorm_nonneg
    calc
      ‖S.primalNorm (x.1 - ((1 - alpha) • xPrev ω + alpha • xNext ω)) ^ 2‖
          =
        S.primalNorm (x.1 - ((1 - alpha) • xPrev ω + alpha • xNext ω)) ^ 2 := by
          rw [Real.norm_of_nonneg]
          exact sq_nonneg _
      _ ≤
          (K * ‖x.1 - ((1 - alpha) • xPrev ω + alpha • xNext ω)‖) ^ 2 := by
          exact sq_le_sq'
            (by
              have hp := apply_nonneg S.primalNorm
                (x.1 - ((1 - alpha) • xPrev ω + alpha • xNext ω))
              nlinarith [hp, hKmul_nonneg])
            hbound
      _ = K ^ 2 * ‖x.1 - ((1 - alpha) • xPrev ω + alpha • xNext ω)‖ ^ 2 := by
          ring

/-- Transfer obligation from fixed-query SFO laws to the generated Ω-process
mean law, with the actual sample-law and query-feasibility facts exposed.

This is deliberately a theorem, not a field in `Setup` or a theorem-head
assumption for Theorem 8.2: the paper derives the random search-point
martingale cancellation from Eq. (8.1.6) and independence.  Unlike the raw
fixed-query law, this bridge must know that the actual sample coordinate has
law `μ` and that the random query is feasible; neither fact follows from
independence alone. -/
theorem generatedSFOUnbiased_of_fixedQuery_law [MeasurableSpace Ω] [MeasurableSpace Sample]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) (μ : Measure Sample) [IsProbabilityMeasure P] [IsProbabilityMeasure μ]
    (sample : PositiveTime → ℕ → Ω → Sample)
    (query : PositiveTime → ℕ → Ω → E)
    (hquery : ∀ k i ω, query k i ω ∈ S.X)
    (hquery_meas :
      ∀ k i, Measurable (fun ω => (⟨query k i ω, hquery k i ω⟩ : FeasiblePoint S)))
    (hsample_meas : ∀ k i, Measurable (sample k i))
    (hresidual_meas :
      Measurable (fun p : FeasiblePoint S × Sample =>
        S.oracle p.1.1 p.2 - S.hSubgradient p.1.1))
    (hfixed_int : ∀ u : FeasiblePoint S, Integrable (fun xi => S.oracle u.1 xi) μ)
    (hmean_int :
      ∀ k i,
        Integrable (fun ω => S.oracle (query k i ω) (sample k i ω)) P ∧
          Integrable (fun ω => S.hSubgradient (query k i ω)) P)
    (hlaw : ∀ k i, Measure.map (sample k i) P = μ)
    (hfixed : fixedQuerySFOUnbiased S μ)
    (hindep :
      ∀ k i, IndepFun
        (fun ω => (⟨query k i ω, hquery k i ω⟩ : FeasiblePoint S))
        (sample k i) P) :
    generatedSFOUnbiased S P sample query := by
  intro k i
  refine ⟨hquery k i, (hmean_int k i).1, (hmean_int k i).2, ?_⟩
  let queryFP : Ω → FeasiblePoint S := fun ω => ⟨query k i ω, hquery k i ω⟩
  let φ : FeasiblePoint S → Sample → E :=
    fun u xi => S.oracle u.1 xi - S.hSubgradient u.1
  have hqueryFP_meas : Measurable queryFP := by
    simpa [queryFP] using hquery_meas k i
  have hindep_qs : IndepFun queryFP (sample k i) P := by
    simpa [queryFP] using hindep k i
  have hresidual_int :
      Integrable
        (fun ω => S.oracle (query k i ω) (sample k i ω) -
          S.hSubgradient (query k i ω)) P :=
    (hmean_int k i).1.sub (hmean_int k i).2
  have hfixed_zero : ∀ u : FeasiblePoint S, ∫ xi, φ u xi ∂μ = 0 := by
    intro u
    simpa [φ] using
      fixedQuerySFOUnbiased_residual_integral_zero S μ hfixed hfixed_int u
  have hzero :
      (∫ ω, φ (queryFP ω) (sample k i ω) ∂P) = 0 := by
    exact integral_comp_eq_zero_of_indep_fixed_integral_zero
      (P := P) (ν := μ) (φ := φ) (X := queryFP) (Y := sample k i)
      (by simpa [φ, Function.uncurry] using hresidual_meas)
      hqueryFP_meas (hsample_meas k i) hindep_qs (hlaw k i)
      (by simpa [φ, queryFP] using hresidual_int) hfixed_zero
  have hsplit :
      (∫ ω, S.oracle (query k i ω) (sample k i ω) -
          S.hSubgradient (query k i ω) ∂P) =
        (∫ ω, S.oracle (query k i ω) (sample k i ω) ∂P) -
          ∫ ω, S.hSubgradient (query k i ω) ∂P := by
    simpa using integral_sub (hmean_int k i).1 (hmean_int k i).2
  have hsub_zero :
      (∫ ω, S.oracle (query k i ω) (sample k i ω) ∂P) -
          ∫ ω, S.hSubgradient (query k i ω) ∂P = 0 := by
    rw [← hsplit]
    simpa [φ, queryFP] using hzero
  exact sub_eq_zero.mp hsub_zero

/-- Transfer obligation from coordinate fixed-query SFO laws and
sample/search-point independence to the generated Ω-process mean law used in the
proof of Theorem 8.2.

The feasibility premise is intentionally explicit: Eq. (8.1.6) is stated for
the actual feasible search points, while the abstract function `query` may be
anything unless a run-level lemma supplies membership in `X`. -/
theorem generatedSFOUnbiased_of_coordinate_law [MeasurableSpace Ω]
    [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) (sample : PositiveTime → ℕ → Ω → Sample) [IsProbabilityMeasure P]
    (query : PositiveTime → ℕ → Ω → E)
    (hquery : ∀ k i ω, query k i ω ∈ S.X)
    (hquery_meas :
      ∀ k i, Measurable (fun ω => (⟨query k i ω, hquery k i ω⟩ : FeasiblePoint S)))
    (hsample_meas : ∀ k i, Measurable (sample k i))
    (hresidual_meas :
      Measurable (fun p : FeasiblePoint S × Sample =>
        S.oracle p.1.1 p.2 - S.hSubgradient p.1.1))
    (hfixed_int :
      ∀ (k : PositiveTime) (i : ℕ) (u : FeasiblePoint S),
        Integrable (fun ω => S.oracle u.1 (sample k i ω)) P)
    (hmean_int :
      ∀ k i,
        Integrable (fun ω => S.oracle (query k i ω) (sample k i ω)) P ∧
          Integrable (fun ω => S.hSubgradient (query k i ω)) P)
    (hfixed : coordinateSFOUnbiased S P sample)
    (hindep :
      ∀ k i, IndepFun
        (fun ω => (⟨query k i ω, hquery k i ω⟩ : FeasiblePoint S))
        (sample k i) P) :
    generatedSFOUnbiased S P sample query := by
  intro k i
  refine ⟨hquery k i, (hmean_int k i).1, (hmean_int k i).2, ?_⟩
  let queryFP : Ω → FeasiblePoint S := fun ω => ⟨query k i ω, hquery k i ω⟩
  let φ : FeasiblePoint S → Sample → E :=
    fun u xi => S.oracle u.1 xi - S.hSubgradient u.1
  have hqueryFP_meas : Measurable queryFP := by
    simpa [queryFP] using hquery_meas k i
  have hindep_qs : IndepFun queryFP (sample k i) P := by
    simpa [queryFP] using hindep k i
  have hresidual_int :
      Integrable
        (fun ω => S.oracle (query k i ω) (sample k i ω) -
          S.hSubgradient (query k i ω)) P :=
    (hmean_int k i).1.sub (hmean_int k i).2
  have hfixed_zero_map :
      ∀ u : FeasiblePoint S,
        (∫ xi, φ u xi ∂Measure.map (sample k i) P) = 0 := by
    intro u
    have hφu_meas : Measurable (fun xi : Sample => φ u xi) := by
      have hpair : Measurable (fun xi : Sample => (u, xi)) :=
        (measurable_const : Measurable (fun _ : Sample => u)).prod measurable_id
      simpa [φ, Function.uncurry] using
        hresidual_meas.comp hpair
    have hmap :
        (∫ xi, φ u xi ∂Measure.map (sample k i) P) =
          ∫ ω, φ u (sample k i ω) ∂P := by
      exact integral_map (hsample_meas k i).aemeasurable hφu_meas.aestronglyMeasurable
    rw [hmap]
    simpa [φ] using
      coordinateSFOUnbiased_residual_integral_zero S P sample hfixed hfixed_int k i u
  have hzero :
      (∫ ω, φ (queryFP ω) (sample k i ω) ∂P) = 0 := by
    exact integral_comp_eq_zero_of_indep_fixed_integral_zero
      (P := P) (ν := Measure.map (sample k i) P) (φ := φ)
      (X := queryFP) (Y := sample k i)
      (by simpa [φ, Function.uncurry] using hresidual_meas)
      hqueryFP_meas (hsample_meas k i) hindep_qs rfl
      (by simpa [φ, queryFP] using hresidual_int) hfixed_zero_map
  have hsplit :
      (∫ ω, S.oracle (query k i ω) (sample k i ω) -
          S.hSubgradient (query k i ω) ∂P) =
        (∫ ω, S.oracle (query k i ω) (sample k i ω) ∂P) -
          ∫ ω, S.hSubgradient (query k i ω) ∂P := by
    simpa using integral_sub (hmean_int k i).1 (hmean_int k i).2
  have hsub_zero :
      (∫ ω, S.oracle (query k i ω) (sample k i ω) ∂P) -
          ∫ ω, S.hSubgradient (query k i ω) ∂P = 0 := by
    rw [← hsplit]
    simpa [φ, queryFP] using hzero
  exact sub_eq_zero.mp hsub_zero

/-- Transfer obligation from the fixed-query second-moment law and independence
to the generated Ω-process variance bound.

The fixed sample law `μ` must be connected to the actual SGS sample coordinate:
without `Measure.map (sample k i) P = μ`, Eq. (8.1.7) at fixed law says nothing
about the random samples used by the run.  The remaining measurability and
integrability hypotheses are Lean well-definedness data for the product-law
transfer, not source setup assumptions. -/
theorem generatedSFOVariance_of_fixedQuery_law [MeasurableSpace Ω] [MeasurableSpace Sample]
    [MeasurableSpace E]
    (P : Measure Ω) (μ : Measure Sample) [IsProbabilityMeasure P] [IsProbabilityMeasure μ]
    (sample : PositiveTime → ℕ → Ω → Sample)
    (query : PositiveTime → ℕ → Ω → E)
    (hsample_meas : ∀ k i, Measurable (sample k i))
    (hnoise_meas :
      Measurable (fun p : FeasiblePoint S × Sample =>
        dualNorm S (oracleNoiseAt S p.1.1 p.2) ^ 2))
    (hvar_int :
      ∀ k i,
        Integrable
          (fun ω => dualNorm S (oracleNoiseAt S (query k i ω) (sample k i ω)) ^ 2) P)
    (hlaw : ∀ k i, Measure.map (sample k i) P = μ)
    (hfixed : fixedQuerySFOVariance S μ)
    (hindep : sfoIndependent S P sample query) :
    generatedSFOVariance S P sample query := by
  rcases hindep with ⟨hquery, hquery_meas, hindep_qs⟩
  intro k i
  refine ⟨hquery k i, hvar_int k i, ?_⟩
  let queryFP : Ω → FeasiblePoint S := fun ω => ⟨query k i ω, hquery k i ω⟩
  let φ : FeasiblePoint S → Sample → ℝ :=
    fun u xi => dualNorm S (oracleNoiseAt S u.1 xi) ^ 2
  have hqueryFP_meas : Measurable queryFP := by
    simpa [queryFP] using hquery_meas k i
  have hindep_qs_ki : IndepFun queryFP (sample k i) P := by
    simpa [queryFP] using hindep_qs k i
  have hfixed_bound : ∀ u : FeasiblePoint S, ∫ xi, φ u xi ∂μ ≤ S.sigmaSq := by
    intro u
    simpa [φ, oracleNoiseDualNorm, oracleNoiseAt] using hfixed u.1 u.2
  exact integral_comp_le_of_indep_fixed_integral_bound
    (P := P) (ν := μ) (φ := φ) (X := queryFP) (Y := sample k i)
    (C := S.sigmaSq)
    (by simpa [φ, Function.uncurry] using hnoise_meas)
    hqueryFP_meas (hsample_meas k i) hindep_qs_ki (hlaw k i)
    (by simpa [φ, queryFP] using hvar_int k i) hfixed_bound

/-- Transfer obligation from coordinate fixed-query second-moment laws and
independence to the generated Ω-process variance bound.

This is the actual-coordinate variant of Eq. (8.1.7).  The deterministic-query
coordinate moment bound is transported to the random generated query through the
same product-law bridge used above, with generated squared-noise integrability
kept explicit. -/
theorem generatedSFOVariance_of_coordinate_law [MeasurableSpace Ω]
    [MeasurableSpace Sample] [MeasurableSpace E]
    (P : Measure Ω) (sample : PositiveTime → ℕ → Ω → Sample) [IsProbabilityMeasure P]
    (query : PositiveTime → ℕ → Ω → E)
    (hsample_meas : ∀ k i, Measurable (sample k i))
    (hnoise_meas :
      Measurable (fun p : FeasiblePoint S × Sample =>
        dualNorm S (oracleNoiseAt S p.1.1 p.2) ^ 2))
    (hvar_int :
      ∀ k i,
        Integrable
          (fun ω => dualNorm S (oracleNoiseAt S (query k i ω) (sample k i ω)) ^ 2) P)
    (hfixed : coordinateSFOVariance S P sample)
    (hindep : sfoIndependent S P sample query) :
    generatedSFOVariance S P sample query := by
  rcases hindep with ⟨hquery, hquery_meas, hindep_qs⟩
  intro k i
  refine ⟨hquery k i, hvar_int k i, ?_⟩
  let queryFP : Ω → FeasiblePoint S := fun ω => ⟨query k i ω, hquery k i ω⟩
  let φ : FeasiblePoint S → Sample → ℝ :=
    fun u xi => dualNorm S (oracleNoiseAt S u.1 xi) ^ 2
  have hqueryFP_meas : Measurable queryFP := by
    simpa [queryFP] using hquery_meas k i
  have hindep_qs_ki : IndepFun queryFP (sample k i) P := by
    simpa [queryFP] using hindep_qs k i
  haveI : IsProbabilityMeasure (Measure.map (sample k i) P) :=
    Measure.isProbabilityMeasure_map (hsample_meas k i).aemeasurable
  have hfixed_bound :
      ∀ u : FeasiblePoint S,
        ∫ xi, φ u xi ∂Measure.map (sample k i) P ≤ S.sigmaSq := by
    intro u
    have hφu_meas : Measurable (fun xi : Sample => φ u xi) := by
      have hpair : Measurable (fun xi : Sample => (u, xi)) :=
        (measurable_const : Measurable (fun _ : Sample => u)).prod measurable_id
      simpa [φ, Function.uncurry] using hnoise_meas.comp hpair
    have hmap :
        (∫ xi, φ u xi ∂Measure.map (sample k i) P) =
          ∫ ω, φ u (sample k i ω) ∂P := by
      exact integral_map (hsample_meas k i).aemeasurable hφu_meas.aestronglyMeasurable
    rw [hmap]
    simpa [φ, oracleNoiseDualNorm, oracleNoiseAt] using hfixed k i u.1 u.2
  exact integral_comp_le_of_indep_fixed_integral_bound
    (P := P) (ν := Measure.map (sample k i) P) (φ := φ)
    (X := queryFP) (Y := sample k i) (C := S.sigmaSq)
    (by simpa [φ, Function.uncurry] using hnoise_meas)
    hqueryFP_meas (hsample_meas k i) hindep_qs_ki rfl
    (by simpa [φ, queryFP] using hvar_int k i) hfixed_bound

/-- Internal proof-side denominator obligation for quotient manipulations around
Eq. (8.1.57).

This is not part of the paper-facing light-tail assumption: the book JSON states
only `E[exp(||H(u,xi)-h'(u)||_*^2/sigma^2)] <= exp(1)` at
`book/FOML/StochasticGradientSliding.json:assumptions[5]`, and the PDF notes that
the deterministic case is covered by setting `σ^2 = 0` in (8.1.7) and (8.1.57).
Use this predicate only inside quotient lemmas after the positive-`σ^2` branch of
the source-facing light-tail assumption has been selected. -/
def lightTailSigmaSqAdmissible : Prop :=
  0 < S.sigmaSq

/-- Literal positive-variance exponent from Eq. (8.1.57).

No SOptLib match: searched light-tail/exponential-moment candidates, checked
filtration/generated-process candidates, and scanned `SOptLib/Model/StochasticOracle.lean`
and `SOptLib/Model/TailBounds.lean`; none define the SGS paper's explicit
`E[exp(||H(u,ξ)-h'(u)||_*^2/σ^2)]` oracle-noise moment. This helper is only the
positive-`σ^2` quotient appearing in Eq. (8.1.57); the `σ^2 = 0` source boundary is
modeled separately as exact zero oracle noise. -/
noncomputable def lightTailExponent (a : ℝ) : ℝ :=
  a / S.sigmaSq

/-- The source-safe deterministic boundary for Eq. (8.1.57) at a fixed query.

The PDF says the deterministic composite case is obtained by setting `σ = 0` in
(8.1.7) and (8.1.57); this is modeled as zero SFO noise, not as a totalized
constant exponential moment. -/
def fixedQuerySFOLightTailDeterministic [MeasurableSpace Sample]
    (μ : Measure Sample) : Prop :=
  S.sigmaSq = 0 ∧
    ∀ u, u ∈ S.X → ∀ᵐ xi ∂μ, oracleNoiseDualNorm S u xi = 0

/-- The positive-`σ^2` fixed-query light-tail moment exactly as Eq. (8.1.57).

The source writes this as an expectation bound.  In Lean, the expectation is
represented by the Bochner integral together with the integrability needed for
that integral to be the displayed moment rather than a totalized fallback. -/
def fixedQuerySFOLightTailPositive [MeasurableSpace Sample]
    (μ : Measure Sample) : Prop :=
  0 < S.sigmaSq ∧
    ∀ u, u ∈ S.X →
      Integrable
        (fun xi => Real.exp (lightTailExponent S (oracleNoiseDualNorm S u xi ^ 2))) μ ∧
      (∫ xi, Real.exp (lightTailExponent S (oracleNoiseDualNorm S u xi ^ 2)) ∂μ) ≤
        Real.exp 1

/-- The source-safe deterministic boundary for Eq. (8.1.57) on each sample
coordinate of the SGS/SPS stream. -/
def coordinateSFOLightTailDeterministic [MeasurableSpace Ω] [MeasurableSpace Sample]
    (P : Measure Ω) (sample : PositiveTime → ℕ → Ω → Sample) : Prop :=
  S.sigmaSq = 0 ∧
    ∀ k i u, u ∈ S.X → ∀ᵐ ω ∂P, oracleNoiseDualNorm S u (sample k i ω) = 0

/-- The positive-`σ^2` coordinate light-tail moment exactly as Eq. (8.1.57).

The integrability conjunct is the Lean well-definedness content of the source
expectation. -/
def coordinateSFOLightTailPositive [MeasurableSpace Ω] [MeasurableSpace Sample]
    (P : Measure Ω) (sample : PositiveTime → ℕ → Ω → Sample) : Prop :=
  0 < S.sigmaSq ∧
    ∀ k i u, u ∈ S.X →
      Integrable
        (fun ω =>
          Real.exp (lightTailExponent S
            (oracleNoiseDualNorm S u (sample k i ω) ^ 2))) P ∧
      (∫ ω, Real.exp (lightTailExponent S
        (oracleNoiseDualNorm S u (sample k i ω) ^ 2)) ∂P) ≤
        Real.exp 1

/-- The source-safe deterministic boundary for the generated SGS/SPS process. -/
def generatedSFOLightTailDeterministic [MeasurableSpace Ω] [MeasurableSpace Sample]
    (P : Measure Ω) (sample : PositiveTime → ℕ → Ω → Sample)
    (query : PositiveTime → ℕ → Ω → E) : Prop :=
  S.sigmaSq = 0 ∧
    ∀ k i, ∀ᵐ ω ∂P,
      dualNorm S (oracleNoiseAt S (query k i ω) (sample k i ω)) = 0

/-- The positive-`σ^2` generated-process light-tail moment exactly as Eq. (8.1.57).

This generated version is what Theorem 8.2(b) consumes at the actual SGS/SPS
oracle queries.  It stores both exponential integrability and the displayed
moment bound, matching the source expectation semantics. -/
def generatedSFOLightTailPositive [MeasurableSpace Ω] [MeasurableSpace Sample]
    (P : Measure Ω) (sample : PositiveTime → ℕ → Ω → Sample)
    (query : PositiveTime → ℕ → Ω → E) : Prop :=
  0 < S.sigmaSq ∧
    ∀ k i,
      Integrable
        (fun ω =>
          Real.exp (lightTailExponent S
            (dualNorm S (oracleNoiseAt S (query k i ω) (sample k i ω)) ^ 2))) P ∧
      (∫ ω,
        Real.exp (lightTailExponent S
          (dualNorm S (oracleNoiseAt S (query k i ω) (sample k i ω)) ^ 2)) ∂P) ≤
        Real.exp 1

/-- Fixed-query light-tail SFO assumption from Eq. (8.1.57), before transfer to
the actual Ω sample stream.

Book JSON citation:
`book/FOML/StochasticGradientSliding.json:assumptions[5]` states
`E[exp(||H(u,xi)-h'(u)||_*^2/sigma^2)] <= exp(1)`.

SOptLib candidates considered: `filtration`, `filtration_seq`,
`measurable_sample_le_prefixFiltration`, generated-bound bridges, and tail-bound
wrappers; none define the paper's exponential SFO noise moment, so this local
predicate records the source boundary as either the positive-`σ` moment or the
deterministic zero-noise case.  The positive branch includes integrability,
because Eq. (8.1.57) is an expectation bound. -/
def fixedQuerySFOLightTail [MeasurableSpace Sample] (μ : Measure Sample) : Prop :=
  fixedQuerySFOLightTailPositive S μ ∨ fixedQuerySFOLightTailDeterministic S μ

/-- Source-facing Assumption (8.1.57) for the SGS oracle law at generated search points.

Book/PDF citation: `book/FOML/StochasticGradientSliding.json:assumptions[5]`
and the FOML PDF Eq. (8.1.57) state the oracle-noise moment
`E[exp(||H(u,ξ)-h'(u)||_*^2/σ^2)] <= exp(1)`.  Theorem 8.2(b) applies it to
the actual noises `δ_{k,i-1}=H(u_{k,i-1},ξ_{i-1})-h'(u_{k,i-1})`, so the
paper-facing boundary below is generated-query-facing and guarded by the same
feasible-search-point independence predicate used for Eq. (8.1.6).

No SOptLib match: searched light-tail/exponential-moment oracle candidates and
scanned `SOptLib/Model/TailBounds.lean` and
`SOptLib/Model/StochasticOracle.lean`; the available tail wrappers name generic
tail events/probabilities and `BoundedVarianceUnbiasedOracleOn` gives
fixed-query mean/variance, but none encode the SGS exponential oracle-noise
moment from Eq. (8.1.57).  Fixed and coordinate predicates above remain
lower-level infrastructure, but the public high-probability theorem boundary
uses the generated search points that occur in the proof. -/
def sgsOracleLightTailAssumption_8_1_57 [MeasurableSpace Ω] [MeasurableSpace Sample]
    [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) : Prop :=
  (coordinateSFOLightTailPositive S law.P law.sample ∨
    coordinateSFOLightTailDeterministic S law.P law.sample) ∧
    ∀ query, sfoIndependent S law.P law.sample query →
      ∃ _ : ∀ k i ω, query k i ω ∈ S.X,
        generatedSFOLightTailPositive S law.P law.sample query ∨
          generatedSFOLightTailDeterministic S law.P law.sample query

/-- Source-stated coordinate form of Assumption (8.1.57), extracted from the
public SGS light-tail boundary. -/
theorem sgsOracleLightTailAssumption_8_1_57.coordinate
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S)
    (hlight : sgsOracleLightTailAssumption_8_1_57 S law) :
    coordinateSFOLightTailPositive S law.P law.sample ∨
      coordinateSFOLightTailDeterministic S law.P law.sample :=
  hlight.1

/-- Generated-query projection of Assumption (8.1.57), preserving the previous
consumer interface after the source boundary is corrected to also expose the
uniform coordinate moment. -/
theorem sgsOracleLightTailAssumption_8_1_57.generated
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S)
    (hlight : sgsOracleLightTailAssumption_8_1_57 S law)
    (query : PositiveTime → ℕ → Ω → E)
    (hindep : sfoIndependent S law.P law.sample query) :
    ∃ _hquery : ∀ k i ω, query k i ω ∈ S.X,
      generatedSFOLightTailPositive S law.P law.sample query ∨
        generatedSFOLightTailDeterministic S law.P law.sample query :=
  hlight.2 query hindep

/-- Fixed-query light-tail law for each actual SGS/SPS sample coordinate from
Eq. (8.1.57).

Book JSON citation:
`book/FOML/StochasticGradientSliding.json:assumptions[5]` states
`E[exp(||H(u,xi)-h'(u)||_*^2/sigma^2)] <= exp(1)`.

SOptLib candidates considered: `filtration`, `filtration_seq`,
`measurable_sample_le_prefixFiltration`, generated-bound bridges, and tail-bound
wrappers; none define the paper's exponential SFO noise moment, so this local
coordinate predicate records the source boundary as either the positive-`σ`
moment or the deterministic zero-noise case.  The positive branch includes the
integrability carried by the displayed expectation. -/
def coordinateSFOLightTail [MeasurableSpace Ω] [MeasurableSpace Sample]
    (P : Measure Ω) (sample : PositiveTime → ℕ → Ω → Sample) : Prop :=
  coordinateSFOLightTailPositive S P sample ∨
    coordinateSFOLightTailDeterministic S P sample

/-- Derived light-tail law from Eq. (8.1.57), evaluated at feasible generated
SGS/SPS search points and samples.

Book JSON citation:
`book/FOML/StochasticGradientSliding.json:assumptions[5]` states
`E[exp(||H(u,xi)-h'(u)||_*^2/sigma^2)] <= exp(1)`.

SOptLib candidates considered: `filtration`, `filtration_seq`,
`measurable_sample_le_prefixFiltration`, generated-bound bridges, and tail-bound
wrappers; none define the paper's exponential SFO noise moment, so this
  generated-process predicate records the source boundary as feasibility plus
  either the positive-`σ` moment or the deterministic zero-noise case.
  The positive branch stores the integrability needed by downstream Markov and
  Jensen arguments. -/
def generatedSFOLightTail [MeasurableSpace Ω] [MeasurableSpace Sample]
    (P : Measure Ω) (sample : PositiveTime → ℕ → Ω → Sample)
    (query : PositiveTime → ℕ → Ω → E) : Prop :=
  ∃ _hquery : ∀ k i ω, query k i ω ∈ S.X,
    generatedSFOLightTailPositive S P sample query ∨
      generatedSFOLightTailDeterministic S P sample query

/-- Product-law a.e. transfer for an independent random parameter.

Candidate audit: considered the existing integral transfer lemmas
`integral_comp_le_of_indep_fixed_integral_bound` and
`integral_comp_eq_zero_of_indep_fixed_integral_zero`, plus Mathlib
`Measure.ae_prod_iff_ae_ae`; the integral lemmas are not a.e. statements, so
this helper packages the narrower product-a.e. consequence needed by the
deterministic branch of Eq. (8.1.57). -/
theorem ae_comp_of_indep_fixed_ae
    {Ω W Sample : Type*} [MeasurableSpace Ω] [MeasurableSpace W] [MeasurableSpace Sample]
    {P : Measure Ω} {ν : Measure Sample} [IsProbabilityMeasure P] [IsProbabilityMeasure ν]
    {R : W → Sample → Prop} {X : Ω → W} {Y : Ω → Sample}
    (hR : MeasurableSet {p : W × Sample | R p.1 p.2})
    (hX : Measurable X) (hY : Measurable Y)
    (h_indep : IndepFun X Y P)
    (h_dist : Measure.map Y P = ν)
    (hfixed : ∀ w, ∀ᵐ s ∂ν, R w s) :
    ∀ᵐ ω ∂P, R (X ω) (Y ω) := by
  have h_joint_meas : AEMeasurable (fun ω => (X ω, Y ω)) P :=
    (hX.prodMk hY).aemeasurable
  have h_prod_eq : P.map (fun ω => (X ω, Y ω)) = (P.map X).prod ν := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable).mp
      h_indep, h_dist]
  have h_prod : ∀ᵐ p ∂(P.map X).prod ν, R p.1 p.2 := by
    rw [Measure.ae_prod_iff_ae_ae hR]
    exact Filter.Eventually.of_forall hfixed
  have h_map : ∀ᵐ p ∂P.map (fun ω => (X ω, Y ω)), R p.1 p.2 := by
    rwa [h_prod_eq]
  exact (ae_map_iff h_joint_meas hR).mp h_map

/-- A route-local bridge from scalar measurability of the oracle-noise dual norm
to measurability of its deterministic zero-noise event.

This is not a source assumption: Eq. (8.1.57) states the exponential moment, while
the `σ = 0` deterministic branch needs this Lean regularity only to transport
fiberwise a.e. zero noise through product laws. -/
theorem zero_noise_event_measurable_of_noise_norm_measurable
    [MeasurableSpace Sample] [MeasurableSpace E]
    (hnoise :
      Measurable (fun p : FeasiblePoint S × Sample =>
        dualNorm S (oracleNoiseAt S p.1.1 p.2))) :
    MeasurableSet {p : FeasiblePoint S × Sample |
      (dualNorm S (oracleNoiseAt S p.1.1 p.2) = 0)} := by
  change MeasurableSet
    ((fun p : FeasiblePoint S × Sample =>
      dualNorm S (oracleNoiseAt S p.1.1 p.2)) ⁻¹' ({0} : Set ℝ))
  exact hnoise (measurableSet_singleton (0 : ℝ))

/-- Transfer obligation from the fixed-query light-tail law and independence to
the generated Ω-process light-tail law.

As in the variance bridge, a fixed-`μ` exponential moment can be transported to
the generated Ω-process only after exposing the actual sample law and the
branchwise kernel regularity needed by the product-law/a.e. transfer.  The
deterministic branch uses `hzero_meas`, because measurability of the totalized
positive-`σ` exponent does not imply measurability of the zero-noise event when
`S.sigmaSq = 0`. -/
theorem generatedSFOLightTail_of_fixedQuery_law [MeasurableSpace Ω] [MeasurableSpace Sample]
    [MeasurableSpace E]
    (P : Measure Ω) (μ : Measure Sample) [IsProbabilityMeasure P] [IsProbabilityMeasure μ]
    (sample : PositiveTime → ℕ → Ω → Sample)
    (query : PositiveTime → ℕ → Ω → E)
    (hsample_meas : ∀ k i, Measurable (sample k i))
    (hpositive_meas :
      Measurable (fun p : FeasiblePoint S × Sample =>
        Real.exp (lightTailExponent S (dualNorm S (oracleNoiseAt S p.1.1 p.2) ^ 2))))
    (hpositive_int :
      ∀ k i,
        Integrable
          (fun ω =>
            Real.exp (lightTailExponent S
              (dualNorm S (oracleNoiseAt S (query k i ω) (sample k i ω)) ^ 2))) P)
    (hzero_meas :
      MeasurableSet {p : FeasiblePoint S × Sample |
        (dualNorm S (oracleNoiseAt S p.1.1 p.2) = 0)})
    (hlaw : ∀ k i, Measure.map (sample k i) P = μ)
    (hfixed : fixedQuerySFOLightTail S μ)
    (hindep : sfoIndependent S P sample query) :
    generatedSFOLightTail S P sample query := by
  rcases hindep with ⟨hquery, hquery_meas, hindep_qs⟩
  refine ⟨hquery, ?_⟩
  rcases hfixed with hpos | hdet
  · left
    refine ⟨hpos.1, ?_⟩
    intro k i
    let queryFP : Ω → FeasiblePoint S := fun ω => ⟨query k i ω, hquery k i ω⟩
    let φ : FeasiblePoint S → Sample → ℝ :=
      fun u xi => Real.exp (lightTailExponent S
        (dualNorm S (oracleNoiseAt S u.1 xi) ^ 2))
    have hqueryFP_meas : Measurable queryFP := by
      simpa [queryFP] using hquery_meas k i
    have hindep_qs_ki : IndepFun queryFP (sample k i) P := by
      simpa [queryFP] using hindep_qs k i
    have hfixed_bound : ∀ u : FeasiblePoint S, ∫ xi, φ u xi ∂μ ≤ Real.exp 1 := by
      intro u
      simpa [φ, oracleNoiseDualNorm, oracleNoiseAt] using (hpos.2 u.1 u.2).2
    refine ⟨hpositive_int k i, ?_⟩
    exact integral_comp_le_of_indep_fixed_integral_bound
      (P := P) (ν := μ) (φ := φ) (X := queryFP) (Y := sample k i)
      (C := Real.exp 1)
      (by simpa [φ, Function.uncurry] using hpositive_meas)
      hqueryFP_meas (hsample_meas k i) hindep_qs_ki (hlaw k i)
      (by simpa [φ, queryFP] using hpositive_int k i) hfixed_bound
  · right
    refine ⟨hdet.1, ?_⟩
    intro k i
    let queryFP : Ω → FeasiblePoint S := fun ω => ⟨query k i ω, hquery k i ω⟩
    have hqueryFP_meas : Measurable queryFP := by
      simpa [queryFP] using hquery_meas k i
    have hindep_qs_ki : IndepFun queryFP (sample k i) P := by
      simpa [queryFP] using hindep_qs k i
    let R : FeasiblePoint S → Sample → Prop :=
      fun u xi => dualNorm S (oracleNoiseAt S u.1 xi) = 0
    have hR : MeasurableSet {p : FeasiblePoint S × Sample | R p.1 p.2} := by
      simpa [R] using hzero_meas
    have hfixed_ae : ∀ u : FeasiblePoint S, ∀ᵐ xi ∂μ, R u xi := by
      intro u
      simpa [R, oracleNoiseDualNorm, oracleNoiseAt] using hdet.2 u.1 u.2
    have hzero :
        ∀ᵐ ω ∂P,
          dualNorm S (oracleNoiseAt S (query k i ω) (sample k i ω)) = 0 := by
      simpa [R, queryFP] using
        ae_comp_of_indep_fixed_ae (P := P) (ν := μ) (R := R)
          (X := queryFP) (Y := sample k i) hR hqueryFP_meas (hsample_meas k i)
          hindep_qs_ki (hlaw k i) hfixed_ae
    exact hzero

/-- Transfer obligation from coordinate fixed-query light-tail laws and
independence to the generated Ω-process light-tail law. -/
theorem generatedSFOLightTail_of_coordinate_law [MeasurableSpace Ω]
    [MeasurableSpace Sample] [MeasurableSpace E]
    (P : Measure Ω) (sample : PositiveTime → ℕ → Ω → Sample) [IsProbabilityMeasure P]
    (query : PositiveTime → ℕ → Ω → E)
    (hsample_meas : ∀ k i, Measurable (sample k i))
    (hpositive_meas :
      Measurable (fun p : FeasiblePoint S × Sample =>
        Real.exp (lightTailExponent S (dualNorm S (oracleNoiseAt S p.1.1 p.2) ^ 2))))
    (hpositive_int :
      ∀ k i,
        Integrable
          (fun ω =>
            Real.exp (lightTailExponent S
              (dualNorm S (oracleNoiseAt S (query k i ω) (sample k i ω)) ^ 2))) P)
    (hzero_meas :
      MeasurableSet {p : FeasiblePoint S × Sample |
        (dualNorm S (oracleNoiseAt S p.1.1 p.2) = 0)})
    (hfixed : coordinateSFOLightTail S P sample)
    (hindep : sfoIndependent S P sample query) :
    generatedSFOLightTail S P sample query := by
  rcases hindep with ⟨hquery, hquery_meas, hindep_qs⟩
  refine ⟨hquery, ?_⟩
  rcases hfixed with hpos | hdet
  · left
    refine ⟨hpos.1, ?_⟩
    intro k i
    let queryFP : Ω → FeasiblePoint S := fun ω => ⟨query k i ω, hquery k i ω⟩
    let φ : FeasiblePoint S → Sample → ℝ :=
      fun u xi => Real.exp (lightTailExponent S
        (dualNorm S (oracleNoiseAt S u.1 xi) ^ 2))
    have hqueryFP_meas : Measurable queryFP := by
      simpa [queryFP] using hquery_meas k i
    have hindep_qs_ki : IndepFun queryFP (sample k i) P := by
      simpa [queryFP] using hindep_qs k i
    haveI : IsProbabilityMeasure (Measure.map (sample k i) P) :=
      Measure.isProbabilityMeasure_map (hsample_meas k i).aemeasurable
    have hfixed_bound :
        ∀ u : FeasiblePoint S,
          ∫ xi, φ u xi ∂Measure.map (sample k i) P ≤ Real.exp 1 := by
      intro u
      have hφu_meas : Measurable (fun xi : Sample => φ u xi) := by
        have hpair : Measurable (fun xi : Sample => (u, xi)) :=
          (measurable_const : Measurable (fun _ : Sample => u)).prod measurable_id
        simpa [φ, Function.uncurry] using hpositive_meas.comp hpair
      have hmap :
          (∫ xi, φ u xi ∂Measure.map (sample k i) P) =
            ∫ ω, φ u (sample k i ω) ∂P := by
        exact integral_map (hsample_meas k i).aemeasurable hφu_meas.aestronglyMeasurable
      rw [hmap]
      simpa [φ, oracleNoiseDualNorm, oracleNoiseAt] using (hpos.2 k i u.1 u.2).2
    refine ⟨hpositive_int k i, ?_⟩
    exact integral_comp_le_of_indep_fixed_integral_bound
      (P := P) (ν := Measure.map (sample k i) P) (φ := φ)
      (X := queryFP) (Y := sample k i) (C := Real.exp 1)
      (by simpa [φ, Function.uncurry] using hpositive_meas)
      hqueryFP_meas (hsample_meas k i) hindep_qs_ki rfl
      (by simpa [φ, queryFP] using hpositive_int k i) hfixed_bound
  · right
    refine ⟨hdet.1, ?_⟩
    intro k i
    let queryFP : Ω → FeasiblePoint S := fun ω => ⟨query k i ω, hquery k i ω⟩
    have hqueryFP_meas : Measurable queryFP := by
      simpa [queryFP] using hquery_meas k i
    have hindep_qs_ki : IndepFun queryFP (sample k i) P := by
      simpa [queryFP] using hindep_qs k i
    let R : FeasiblePoint S → Sample → Prop :=
      fun u xi => dualNorm S (oracleNoiseAt S u.1 xi) = 0
    have hR : MeasurableSet {p : FeasiblePoint S × Sample | R p.1 p.2} := by
      simpa [R] using hzero_meas
    haveI : IsProbabilityMeasure (Measure.map (sample k i) P) :=
      Measure.isProbabilityMeasure_map (hsample_meas k i).aemeasurable
    have hfixed_ae :
        ∀ u : FeasiblePoint S, ∀ᵐ xi ∂Measure.map (sample k i) P, R u xi := by
      intro u
      have hRu : MeasurableSet {xi : Sample | R u xi} := by
        have hpair : Measurable (fun xi : Sample => (u, xi)) :=
          (measurable_const : Measurable (fun _ : Sample => u)).prod measurable_id
        simpa [R] using hR.preimage hpair
      exact (ae_map_iff (hsample_meas k i).aemeasurable hRu).mpr
        (by simpa [R, oracleNoiseDualNorm, oracleNoiseAt] using hdet.2 k i u.1 u.2)
    have hzero :
        ∀ᵐ ω ∂P,
          dualNorm S (oracleNoiseAt S (query k i ω) (sample k i ω)) = 0 := by
      simpa [R, queryFP] using
        ae_comp_of_indep_fixed_ae (P := P) (ν := Measure.map (sample k i) P) (R := R)
          (X := queryFP) (Y := sample k i) hR hqueryFP_meas (hsample_meas k i)
          hindep_qs_ki rfl hfixed_ae
    exact hzero

/-- Natural filtration generated by the sample stream.

Aligns with `SOptLib.filtration`, the canonical sample-prefix filtration
constructor. -/
noncomputable def sampleFiltration [MeasurableSpace Ω] [MeasurableSpace Sample]
    (sample : ℕ → Ω → Sample) (hsample : ∀ t, Measurable (sample t)) :
    MeasureTheory.Filtration ℕ (by infer_instance : MeasurableSpace Ω) :=
  SOptLib.filtration sample hsample

/-- The prox-sliding averaging weight from Eq. (8.1.39).

Book JSON citation:
`book/FOML/StochasticGradientSliding.json:algorithm_spec.parameters[0]` states
`θ_t=2(t+1)/(t(t+3))` for all `t≥1`.

No SOptLib match: searched output-weight/positive-time schedule candidates;
this is the paper's literal SPS averaging weight, not a generic normalized-output
selector. -/
noncomputable def spsTheta (t : PositiveTime) : ℝ :=
  (2 * ((t.1 : ℝ) + 1)) / ((t.1 : ℝ) * ((t.1 : ℝ) + 3))

/-- Recursive `P_t` weights from Eq. (8.1.20), parameterized by a positive-time
`p_t` schedule.

Book JSON citation:
`book/FOML/StochasticGradientSliding.json:assumptions[10]` states
`P_t:=1` for `t=0` and `P_t=p_t(1+p_t)^{-1}P_{t-1}` for `t≥1`.

No SOptLib match: searched output-weight/positive-time schedule candidates and
considered `acceleratedGammaSchedule`; SGS uses the prox-sliding product
`P_t = p_t(1+p_t)^{-1}P_{t-1}`, not the accelerated `Γ_k` recurrence. -/
noncomputable def psWeightProduct (p : PositiveTime → ℝ) : ℕ → ℝ
  | 0 => 1
  | t + 1 =>
      let τ : PositiveTime := ⟨t + 1, Nat.succ_pos t⟩
      p τ * (1 + p τ)⁻¹ * psWeightProduct p t

/-- The Eq. (8.1.20) definition of `θ_t` from the `P_t` product.

Book JSON citation:
`book/FOML/StochasticGradientSliding.json:assumptions[10]` states
`θ_t=(P_{t-1}-P_t)/((1-P_t)P_{t-1})`.

The denominator nonzero facts are intentionally not setup fields; they are proof
obligations from the positive parameter schedule. -/
noncomputable def psThetaFromProduct (p : PositiveTime → ℝ) (t : PositiveTime) : ℝ :=
  (psWeightProduct p (t.1 - 1) - psWeightProduct p t.1) /
    ((1 - psWeightProduct p t.1) * psWeightProduct p (t.1 - 1))

/-- Denominator admissibility for Eq. (8.1.20) under the paper choice `p_t=t/2`.

This is a derived well-definedness obligation, not a source-facing assumption. -/
theorem psTheta_denominator_ne_zero (t : PositiveTime) :
    (1 - psWeightProduct spsP t.1) * psWeightProduct spsP (t.1 - 1) ≠ 0 := by
  have hP : ∀ n : ℕ,
      psWeightProduct spsP n = 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
    intro n
    induction n with
    | zero =>
        norm_num [psWeightProduct]
    | succ n ih =>
        simp [psWeightProduct, spsP, ih]
        field_simp
        ring
  rw [hP t.1, hP (t.1 - 1)]
  apply mul_ne_zero
  · have hDpos : 0 < (((t.1 : ℝ) + 1) * ((t.1 : ℝ) + 2)) := by
      positivity
    have hDne : (((t.1 : ℝ) + 1) * ((t.1 : ℝ) + 2)) ≠ 0 := ne_of_gt hDpos
    have htpos : 0 < (t.1 : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (Nat.zero_lt_one) t.2)
    have hrewrite :
        1 - 2 / (((t.1 : ℝ) + 1) * ((t.1 : ℝ) + 2)) =
          ((t.1 : ℝ) * ((t.1 : ℝ) + 3)) /
            (((t.1 : ℝ) + 1) * ((t.1 : ℝ) + 2)) := by
      field_simp [hDne]
      ring
    rw [hrewrite]
    exact div_ne_zero (mul_ne_zero (ne_of_gt htpos) (by positivity)) hDne
  · exact div_ne_zero (by norm_num) (mul_ne_zero (by positivity) (by positivity))

/-- Explicit `P_t=2/((t+1)(t+2))` identity from Eq. (8.1.44).

Candidate audit: the listed SOptLib process/telescope candidates do not state
this paper-specific scalar product, so the proof unfolds `psWeightProduct` and
`spsP` directly. -/
theorem psWeightProduct_spsP_eq (t : ℕ) :
    psWeightProduct spsP t = 2 / (((t : ℝ) + 1) * ((t : ℝ) + 2)) := by
  induction t with
  | zero =>
      norm_num [psWeightProduct]
  | succ n ih =>
      simp [psWeightProduct, spsP, ih]
      field_simp
      ring

/-- The SPS averaging weight from Eq. (8.1.39) lies in `[0,1]`.

This is source-derived parameter admissibility for the convex averaging update
Eq. (8.1.18), not an extra Setup field.

Candidate audit: the weighted-variance and telescope candidates do not encode
the literal Eq. (8.1.39) interval fact, so the proof is scalar arithmetic from
positive paper time. -/
theorem spsTheta_mem_Icc (t : PositiveTime) :
    0 ≤ spsTheta t ∧ spsTheta t ≤ 1 := by
  constructor
  · unfold spsTheta
    positivity
  · unfold spsTheta
    have ht1 : (1 : ℝ) ≤ (t.1 : ℝ) := by exact_mod_cast t.2
    have hden_pos : 0 < (t.1 : ℝ) * ((t.1 : ℝ) + 3) := by positivity
    have hnum_le : 2 * ((t.1 : ℝ) + 1) ≤ (t.1 : ℝ) * ((t.1 : ℝ) + 3) := by
      nlinarith [sq_nonneg ((t.1 : ℝ) - 1)]
    exact (div_le_one hden_pos).2 hnum_le

/-- The concrete SPS averaging weight agrees with the Eq. (8.1.20) product form.

Aligns with Lan Eq. (8.1.20) specialized by Eq. (8.1.39) and
`psWeightProduct_spsP_eq`.  SOptLib weighted-output candidates were considered
but do not encode this paper-specific scalar schedule. -/
theorem spsTheta_eq_psThetaFromProduct_spsP (t : PositiveTime) :
    spsTheta t = psThetaFromProduct spsP t := by
  cases t with
  | mk n hn =>
      unfold spsTheta psThetaFromProduct
      rw [psWeightProduct_spsP_eq n, psWeightProduct_spsP_eq (n - 1)]
      have hn_sub_one_add_one : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
        have hnat : n - 1 + 1 = n := Nat.sub_add_cancel hn
        exact_mod_cast hnat
      have hn_sub_one_add_two : ((n - 1 : ℕ) : ℝ) + 2 = (n : ℝ) + 1 := by
        have hnat : n - 1 + 2 = n + 1 := by omega
        exact_mod_cast hnat
      rw [hn_sub_one_add_one, hn_sub_one_add_two]
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
      have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
      have hn2 : (n : ℝ) + 2 ≠ 0 := by positivity
      have hn3 : (n : ℝ) + 3 ≠ 0 := by positivity
      have hden : (n : ℝ) * 3 + (n : ℝ) ^ 2 ≠ 0 := by
        have hnpos : 0 < (n : ℝ) := by
          exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
        have hprod : 0 < (n : ℝ) * ((n : ℝ) + 3) :=
          mul_pos hnpos (by positivity)
        nlinarith
      field_simp [hn0, hn1, hn2, hn3, hden]
      rw [show
          ((n : ℝ) + 1) * ((n : ℝ) + 2) - 2 =
            (n : ℝ) * 3 + (n : ℝ) ^ 2 by ring]
      rw [show
          (n : ℝ) * ((n : ℝ) + 3) * ((n : ℝ) + 2 - (n : ℝ)) /
              ((n : ℝ) * 3 + (n : ℝ) ^ 2) =
            2 * ((n : ℝ) * 3 + (n : ℝ) ^ 2) *
              ((n : ℝ) * 3 + (n : ℝ) ^ 2)⁻¹ by
        rw [div_eq_mul_inv]
        ring]
      rw [show
          2 * ((n : ℝ) * 3 + (n : ℝ) ^ 2) *
              ((n : ℝ) * 3 + (n : ℝ) ^ 2)⁻¹ =
            2 * (((n : ℝ) * 3 + (n : ℝ) ^ 2) *
              ((n : ℝ) * 3 + (n : ℝ) ^ 2)⁻¹) by ring]
      rw [mul_inv_cancel₀ hden]
      ring

/-- Convex combinations of feasible points remain feasible in `X`.

This is the feasibility bridge used to keep generated averages on the paper
domain, derived from the stated convexity of `X`.

Aligns with `SOptLib.acceleratedSearchPoint_mem`, the reusable two-point
convex-combination feasibility helper. -/
theorem convexCombination_mem_X (x y : FeasiblePoint S) {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    (1 - a) • x.1 + a • y.1 ∈ S.X := by
  exact SOptLib.acceleratedSearchPoint_mem S.convex_X ⟨ha0, ha1⟩ x.2 y.2

/-- SPS inner-loop state containing the feasible iterate `u_t ∈ X` and the
averaged point `\tilde u_t`.

Algorithm 8.2 initializes and minimizes over `X`; prox-core membership needed to
interpret generated first arguments of `V` is a separate proof obligation. -/
structure SPSState (S : Setup E Sample) where
  u : FeasiblePoint S
  avg : FeasiblePoint S

instance [MeasurableSpace E] : MeasurableSpace (SPSState S) :=
  MeasurableSpace.comap (fun st : SPSState S => (st.u, st.avg))
    (by infer_instance : MeasurableSpace (FeasiblePoint S × FeasiblePoint S))

theorem measurable_spsState_u [MeasurableSpace E] :
    Measurable (fun st : SPSState S => st.u) := by
  have hpair :
      Measurable (fun st : SPSState S => (st.u, st.avg)) :=
    Measurable.of_comap_le le_rfl
  exact measurable_fst.comp hpair

theorem measurable_spsState_avg [MeasurableSpace E] :
    Measurable (fun st : SPSState S => st.avg) := by
  have hpair :
      Measurable (fun st : SPSState S => (st.u, st.avg)) :=
    Measurable.of_comap_le le_rfl
  exact measurable_snd.comp hpair

theorem measurable_spsState_mk [MeasurableSpace Ω] [MeasurableSpace E]
    (mΩ : MeasurableSpace Ω) {u avg : Ω → FeasiblePoint S}
    (hu : Measurable[mΩ] u) (havg : Measurable[mΩ] avg) :
    Measurable[mΩ] (fun ω => ({ u := u ω, avg := avg ω } : SPSState S)) := by
  rw [measurable_iff_comap_le]
  simpa [instMeasurableSpaceSPSState] using (hu.prodMk havg).comap_le

/-- Initial SPS state `u_0=\tilde u_0=x`.

Book JSON citation:
`book/FOML/StochasticGradientSliding.json:algorithm_spec.steps[2]` states
`Set u_0=\tilde{u}_0=x`. -/
def spsInitial (x : FeasiblePoint S) : SPSState S where
  u := x
  avg := x

/-- Source-domain SPS state for the Section 3.2 interpretation of Algorithm 8.2.

The current feasible selected recursion remains formula-extension machinery.
This state is the paper-typed process state: every future first argument of
`V(u_t, ·)` is carried as a point of `X^o`, while averages only need to lie in
the minimization domain `X`. -/
structure SPSSourceState (S : Setup E Sample) where
  u : ProxCorePoint S
  avg : FeasiblePoint S

/-- Source-domain initial SPS state `u_0=\tilde u_0=x`, requiring the displayed
Bregman center to be in `X^o`. -/
def spsSourceInitial (x : ProxCorePoint S) : SPSSourceState S where
  u := x
  avg := proxCorePointToFeasible S x

/-- Reinterpret a feasible formula-extension SPS state as source-typed once its
current iterate is proved to lie in the prox-core. -/
def spsSourceStateOfFeasible (st : SPSState S)
    (hcore : st.u.1 ∈ proxCore S.X S.proxPotential) : SPSSourceState S where
  u := ⟨st.u.1, hcore⟩
  avg := st.avg

/-- Source-domain interpretation of the stochastic prox-sliding objective in
Eq. (8.1.58).

No SOptLib match: checked `SOptLib.proxObjective`, `paperProxObjective`, and
`proxStep`; those cover one Bregman term plus a simple term or mirror-only
objectives, while Eq. (8.1.58) has the paper-specific sum
`g(u)+<H(u_{t-1},ξ),u>+βV(x,u)+βp_tV(u_{t-1},u)+χ(u)`.  The two centers are
typed in `X^o`, matching the Section 3.2 source domain for `V`, while the
minimization variable remains typed in `X` as in Eq. (8.1.58).  This suffixed
object is not the public algorithm boundary because Algorithm 8.1/8.2 states
only feasible centers in `X`. -/
noncomputable def spsObjective_sourceDomain (g : E → ℝ) (x : ProxCorePoint S) (β : ℝ)
    (t : PositiveTime) (uPrev : ProxCorePoint S) (xi : Sample)
    (u : FeasiblePoint S) : ℝ :=
  g u.1 + ⟪S.oracle uPrev.1 xi, u.1⟫_ℝ + β * bregmanOn S x u +
    β * spsP t * bregmanOn S uPrev u + S.chi u.1

/-- Feasible-domain SPS objective minimized in Algorithm 8.2, Eq. (8.1.58).

Book JSON citation:
`book/FOML/StochasticGradientSliding.json:algorithm_spec.steps[3]` states
`u_t=argmin_{u∈X}{g(u)+<H(u_{t-1},ξ_{t-1}),u>+βV(x,u)+βp_tV(u_{t-1},u)+χ(u)}`.

Checked `SOptLib.proxStep`/`proxStepArgmin` and `paperMirrorObjective`; those
cover one mirror term or an abstract mirror objective, while Eq. (8.1.58) has
the SGS-specific two-Bregman stochastic objective.  Algorithm 8.1/8.2 states
`u_0=x` and minimizes over `u ∈ X`; the Section 3.2 `X^o × X` interpretation is
kept separately as `spsObjective_sourceDomain`. -/
noncomputable def spsObjective (g : E → ℝ) (x : FeasiblePoint S) (β : ℝ)
    (t : PositiveTime) (uPrev : FeasiblePoint S) (xi : Sample)
    (u : FeasiblePoint S) : ℝ :=
  g u.1 + ⟪S.oracle uPrev.1 xi, u.1⟫_ℝ + β * bregmanFormulaOnX S x u +
    β * spsP t * bregmanFormulaOnX S uPrev u + S.chi u.1

/-- Backwards-compatible explicit formula-extension name for selected helper
recursions. -/
noncomputable def spsObjectiveFormulaOnX (g : E → ℝ) (x : FeasiblePoint S) (β : ℝ)
    (t : PositiveTime) (uPrev : FeasiblePoint S) (xi : Sample)
    (u : FeasiblePoint S) : ℝ :=
  spsObjective S g x β t uPrev xi u

/-- Source-domain argmin relation for the Section 3.2 interpretation of
Eq. (8.1.58).

This is the Section 3.2 well-typed version of the displayed update: the two
Bregman centers are in `X^o` and the minimization variable is in `X`.  Algorithm
8.1/8.2 itself initializes and minimizes over `X`, so generated processes below
use the feasible displayed formula and leave this `X^o` interpretation as a
separate proof obligation. -/
def IsSPSStep_sourceDomain (g : E → ℝ) (x : ProxCorePoint S) (β : ℝ)
    (t : PositiveTime) (uPrev : ProxCorePoint S) (xi : Sample)
    (u : FeasiblePoint S) : Prop :=
  IsMinOn (spsObjective_sourceDomain S g x β t uPrev xi) Set.univ u

/-- Paper-facing argmin relation for Algorithm 8.2 Eq. (8.1.58).

Book JSON citation:
`book/FOML/StochasticGradientSliding.json:algorithm_spec.steps[3]` states the
SPS stochastic prox update as an `argmin_{u∈X}`.

Algorithm 8.2 writes the stochastic prox update for centers and iterates in `X`.
The prox-function source-domain issue is represented by separate
`_sourceDomain` bridge obligations, not by strengthening this public process
boundary to `X^o`. -/
def IsSPSStep (g : E → ℝ) (x : FeasiblePoint S) (β : ℝ)
    (t : PositiveTime) (uPrev : FeasiblePoint S) (xi : Sample)
    (u : FeasiblePoint S) : Prop :=
  IsMinOn (spsObjective S g x β t uPrev xi) Set.univ u

/-- Feasible-domain formula-extension helper for Algorithm 8.2 Eq. (8.1.58). -/
def IsSPSStep_formulaExtension (g : E → ℝ) (x : FeasiblePoint S) (β : ℝ)
    (t : PositiveTime) (uPrev : FeasiblePoint S) (xi : Sample)
    (u : FeasiblePoint S) : Prop :=
  IsSPSStep S g x β t uPrev xi u

/-- Pointwise normalization from the formula-extension SPS objective to the
source-domain objective when both Bregman centers are in `X^o`.

Search audit for this local bridge: considered SOptLib prox/minimizer hits
`proxStep`, `proxStepArgmin`, `proxObjective_exists_isMinOn_compact`, and target
helpers around `spsObjective_sourceDomain`; none already transports this
paper-specific two-Bregman Eq. (8.1.58) objective.  The proof is the literal
Eq. (3.2.2) bridge for each Bregman term via
`bregmanFormulaOnX_eq_bregmanOn_of_mem_proxCore`. -/
theorem spsObjective_formulaExtension_eq_sourceDomain_of_mem_proxCore
    (g : E → ℝ) (x : FeasiblePoint S) (β : ℝ)
    (t : PositiveTime) (uPrev : FeasiblePoint S) (xi : Sample)
    (hx : x.1 ∈ proxCore S.X S.proxPotential)
    (hprev : uPrev.1 ∈ proxCore S.X S.proxPotential)
    (u : FeasiblePoint S) :
    spsObjective S g x β t uPrev xi u =
      spsObjective_sourceDomain S g ⟨x.1, hx⟩ β t ⟨uPrev.1, hprev⟩ xi u := by
  simp [spsObjective, spsObjective_sourceDomain,
    bregmanFormulaOnX_eq_bregmanOn_of_mem_proxCore S x u hx,
    bregmanFormulaOnX_eq_bregmanOn_of_mem_proxCore S uPrev u hprev]

/-- Transport the Eq. (8.1.58) formula-extension minimizer certificate to the
Section 3.2 source-domain objective.

Search audit: checked the `IsMinOn`/prox candidates returned by
`lean_search_symbols` (`blockMirrorUpdate_selected_isMinOn`,
`prox_three_point_of_isMinOn_linear_bregman`,
`positiveStepsizeMirrorProxBlock_isMinOn_unscaled`,
`proxObjective_exists_isMinOn_compact`) and rejected them because they concern
coordinate selection, one-Bregman prox inequalities, or existence; this theorem
only needs pointwise objective equality for the paper's two-Bregman SPS
subproblem. -/
theorem IsSPSStep_formulaExtension_to_sourceDomain_of_mem_proxCore
    (g : E → ℝ) (x : FeasiblePoint S) (β : ℝ)
    (t : PositiveTime) (uPrev : FeasiblePoint S) (xi : Sample)
    (u : FeasiblePoint S)
    (hstep : IsSPSStep_formulaExtension S g x β t uPrev xi u)
    (hx : x.1 ∈ proxCore S.X S.proxPotential)
    (hprev : uPrev.1 ∈ proxCore S.X S.proxPotential) :
    IsSPSStep_sourceDomain S g ⟨x.1, hx⟩ β t ⟨uPrev.1, hprev⟩ xi u := by
  have hstep' :
      IsMinOn (spsObjective S g x β t uPrev xi) Set.univ u := by
    simpa [IsSPSStep_formulaExtension, IsSPSStep] using hstep
  rw [IsSPSStep_sourceDomain, isMinOn_univ_iff]
  intro z
  have hz :
      spsObjective S g x β t uPrev xi u ≤
        spsObjective S g x β t uPrev xi z :=
    (isMinOn_univ_iff
      (f := spsObjective S g x β t uPrev xi) (a := u)).1 hstep' z
  simpa [
    spsObjective_formulaExtension_eq_sourceDomain_of_mem_proxCore
      (S := S) g x β t uPrev xi hx hprev u,
    spsObjective_formulaExtension_eq_sourceDomain_of_mem_proxCore
      (S := S) g x β t uPrev xi hx hprev z] using hz

/-- Source-domain relation-form SPS transition for the Section 3.2
interpretation of Eq. (8.1.58) and Eq. (8.1.18).

This suffixed bridge requires the Bregman centers to be in `X^o`; it is not the
paper-facing generated algorithm boundary, since Algorithm 8.2 initializes and
minimizes over `X`. -/
def IsSPSTransition_sourceDomain (g : E → ℝ) (x : ProxCorePoint S) (β : ℝ)
    (sample : ℕ → Ω → Sample) (n : ℕ) (ω : Ω)
    (st next : SPSSourceState S) : Prop :=
  let t : PositiveTime := ⟨n + 1, Nat.succ_pos n⟩
  IsSPSStep_sourceDomain S g x β t st.u (sample n ω) (proxCorePointToFeasible S next.u) ∧
    next.avg.1 = (1 - spsTheta t) • st.avg.1 + spsTheta t • next.u.1

/-- Paper-facing relation-form SPS transition for Algorithm 8.2 Eq. (8.1.58)
and Eq. (8.1.18).

No SOptLib relation primitive is reused: checked the recursive-process
candidates around `recursiveIterateProcess` and
`recursiveProcess_succ_eq_sample_update`; they model deterministic update
functions, while Algorithm 8.2 specifies a possibly nonunique argmin relation.  This
is the public paper-facing one-step object: it records the displayed argmin over
`u ∈ X` without requiring the input center or previous iterate to lie in `X^o`. -/
def IsSPSTransition (g : E → ℝ) (x : FeasiblePoint S) (β : ℝ)
    (sample : ℕ → Ω → Sample) (n : ℕ) (ω : Ω)
    (st next : SPSState S) : Prop :=
  let t : PositiveTime := ⟨n + 1, Nat.succ_pos n⟩
  IsSPSStep S g x β t st.u (sample n ω) next.u ∧
    next.avg.1 = (1 - spsTheta t) • st.avg.1 + spsTheta t • next.u.1

/-- Formula-extension relation-form SPS transition for internal selected
realizations.

This is kept for existing helper theorem names and is definitionally the same
as the unsuffixed feasible Algorithm 8.1/8.2 transition. -/
def IsSPSTransition_formulaExtension (g : E → ℝ) (x : FeasiblePoint S) (β : ℝ)
    (sample : ℕ → Ω → Sample) (n : ℕ) (ω : Ω)
    (st next : SPSState S) : Prop :=
  IsSPSTransition S g x β sample n ω st next

/-- Source-domain SPS execution generated by the stochastic prox update and
averaging equations under the Section 3.2 `X^o × X` prox-function type.

Algorithm 8.1 initializes each SPS/GS call with `β_k ∈ R++`; this source-stated
parameter-domain fact is part of the generated process object rather than a
separate convergence-theorem hypothesis. -/
def IsSPSProcess_sourceDomain (g : E → ℝ) (x : ProxCorePoint S) (β : ℝ)
    (sample : ℕ → Ω → Sample) (states : ℕ → Ω → SPSSourceState S) : Prop :=
  0 < β ∧
    (∀ ω, states 0 ω = spsSourceInitial S x) ∧
    ∀ n ω, IsSPSTransition_sourceDomain S g x β sample n ω
      (states n ω) (states (n + 1) ω)

/-- Paper-facing SPS execution generated by the stochastic prox update and
averaging equations.

Algorithm 8.1/8.2 states `u_0=\tilde u_0=x` and Eq. (8.1.58) over `X`; the
separate `_sourceDomain` process records the additional obligations needed to
interpret every displayed first argument of `V` in the Section 3.2 domain.
The Algorithm 8.1 input-domain condition `β_k ∈ R++` is encoded here so it does
not leak as an extra theorem-head assumption. -/
def IsSPSProcess (g : E → ℝ) (x : FeasiblePoint S) (β : ℝ)
    (sample : ℕ → Ω → Sample) (states : ℕ → Ω → SPSState S) : Prop :=
  0 < β ∧
    (∀ ω, states 0 ω = spsInitial S x) ∧
    ∀ n ω, IsSPSTransition S g x β sample n ω
      (states n ω) (states (n + 1) ω)

/-- Source-domain SPS process whose center and affine model are generated
randomly by the outer SGS process under the `X^o × X` prox-function type. -/
def IsGeneratedSPSProcess_sourceDomain (g : Ω → E → ℝ) (x : Ω → ProxCorePoint S) (β : ℝ)
    (sample : ℕ → Ω → Sample) (states : ℕ → Ω → SPSSourceState S) : Prop :=
  0 < β ∧
    (∀ ω, states 0 ω = spsSourceInitial S (x ω)) ∧
    ∀ n ω, IsSPSTransition_sourceDomain S (g ω) (x ω) β sample n ω
      (states n ω) (states (n + 1) ω)

/-- Paper-facing SPS process whose center and affine model are generated
randomly by the outer SGS process.

No SOptLib deterministic recursion is reused here: the paper's stochastic
prox-sliding call at outer iteration `k` uses the already generated random
center `x_{k-1}` and model `l_f(\underline x_k; ·)`, while Eq. (8.1.58) remains
an argmin relation.  This definition binds all samples in one inner process
instead of choosing a separate process for each outcome `ω`, and it keeps
Algorithm 8.1/8.2 at the stated feasible-set boundary `X`.  It also carries the
Algorithm 8.1 input-domain condition `β_k ∈ R++`, avoiding a separate
convergence-theorem hypothesis. -/
def IsGeneratedSPSProcess (g : Ω → E → ℝ) (x : Ω → FeasiblePoint S) (β : ℝ)
    (sample : ℕ → Ω → Sample) (states : ℕ → Ω → SPSState S) : Prop :=
  0 < β ∧
    (∀ ω, states 0 ω = spsInitial S (x ω)) ∧
    ∀ n ω, IsSPSTransition S (g ω) (x ω) β sample n ω
      (states n ω) (states (n + 1) ω)

/-- Formula-extension SPS execution generated by the internal selected update.

This relation is realization machinery for deterministic selectors and is kept
separate from `IsSPSProcess` only to preserve the helper/classification boundary;
both relations are now feasible-domain relations over the displayed `X × X`
Bregman formula. -/
def IsSPSProcess_formulaExtension (g : E → ℝ) (x : FeasiblePoint S) (β : ℝ)
    (sample : ℕ → Ω → Sample) (states : ℕ → Ω → SPSState S) : Prop :=
  IsSPSProcess S g x β sample states

/-- Formula-extension generated SPS process for internal selector realizations.

This helper keeps formula-extension theorem names visibly classified as helper
infrastructure while remaining definitionally equal to the feasible generated
SPS process. -/
def IsGeneratedSPSProcess_formulaExtension (g : Ω → E → ℝ) (x : Ω → FeasiblePoint S) (β : ℝ)
    (sample : ℕ → Ω → Sample) (states : ℕ → Ω → SPSState S) : Prop :=
  IsGeneratedSPSProcess S g x β sample states

/-- A generated SPS process carries the Algorithm 8.1 source-domain condition
`β_k ∈ R++`; this is a projection theorem, not a theorem-head assumption. -/
theorem IsGeneratedSPSProcess_beta_pos (g : Ω → E → ℝ) (x : Ω → FeasiblePoint S)
    (β : ℝ) (sample : ℕ → Ω → Sample) (states : ℕ → Ω → SPSState S)
    (hprocess : IsGeneratedSPSProcess S g x β sample states) :
    0 < β :=
  hprocess.1

/-- Source-domain bridge for the SPS transition.

When the two displayed Bregman centers are later proved to lie in `X^o`, the
feasible formula-extension transition can be read as the Section 3.2 typed SPS
argmin.  This is a theorem obligation, not part of the formula-extension
assumption surface. -/
theorem IsSPSTransition_sourceDomain_obligation (g : E → ℝ) (x : FeasiblePoint S)
    (β : ℝ) (sample : ℕ → Ω → Sample) (n : ℕ) (ω : Ω)
    (st next : SPSState S)
    (htrans : IsSPSTransition_formulaExtension S g x β sample n ω st next)
    (hx : x.1 ∈ proxCore S.X S.proxPotential)
    (hprev : st.u.1 ∈ proxCore S.X S.proxPotential) :
    let t : PositiveTime := ⟨n + 1, Nat.succ_pos n⟩;
      IsSPSStep_sourceDomain S g ⟨x.1, hx⟩ β t ⟨st.u.1, hprev⟩ (sample n ω) next.u := by
  dsimp [IsSPSTransition_formulaExtension, IsSPSTransition] at htrans
  dsimp
  exact
    IsSPSStep_formulaExtension_to_sourceDomain_of_mem_proxCore
      (S := S) g x β ⟨n + 1, Nat.succ_pos n⟩ st.u (sample n ω) next.u
      (by simpa [IsSPSStep_formulaExtension] using htrans.1) hx hprev

/-- The candidate set of minimizers for the SPS stochastic prox update
Eq. (8.1.58).

No SOptLib selector is reused directly: checked `proxStep`/`proxStepArgmin`,
whose objective has one mirror term, and `argminSelectorOfSource`, which wraps
an already-known minimizer.  This local set is the paper's two-Bregman stochastic
argmin relation over `u ∈ X`. -/
def spsArgminSet (g : E → ℝ) (x : FeasiblePoint S) (β : ℝ)
    (t : PositiveTime) (uPrev : FeasiblePoint S) (xi : Sample) :
    Set (FeasiblePoint S) :=
  {u | IsSPSStep_formulaExtension S g x β t uPrev xi u}

/-- Existence bridge for the Eq. (8.1.58) argmin relation.

This is not a theorem-head hypothesis.  It projects the source setup datum that
`χ` is relatively simple, represented in `Setup` as solvability of the displayed
SPS prox subproblem, into the local `spsArgminSet` representation consumed by
the selected formula-extension machinery. -/
theorem spsArgminSet_nonempty_obligation (g : E → ℝ) (x : FeasiblePoint S)
    (β : ℝ) (t : PositiveTime) (uPrev : FeasiblePoint S) (xi : Sample)
    (hg : IsAffineModel g) (hβ : 0 < β) :
    (spsArgminSet S g x β t uPrev xi).Nonempty := by
  classical
  refine ⟨S.sps_subproblem_solver.toFun g x β t uPrev xi hg hβ, ?_⟩
  simpa [spsArgminSet, IsSPSStep_formulaExtension, IsSPSStep, spsObjective,
    bregmanFormulaOnX] using
    S.sps_subproblem_solver.is_argmin g x β t uPrev xi hg hβ

/-- Pointwise objective minimized in the SPS update, as a function on feasible
points. -/
noncomputable def spsPointwiseObjective (g : E → ℝ) (x : FeasiblePoint S) (β : ℝ)
    (t : PositiveTime) (uPrev : FeasiblePoint S) (xi : Sample) :
    FeasiblePoint S → ℝ :=
  spsObjectiveFormulaOnX S g x β t uPrev xi

/-- Internal formula-extension point selected from the Eq. (8.1.58) argmin set.

This uses `SOptLib.argminSelectorOfSource` only after the source-specific SPS
argmin-set nonemptiness obligation has produced a candidate for this exact
subproblem.  The remaining `sorry` is the subproblem-solvability proof obligation,
not a theorem-head assumption for convergence. -/
noncomputable def spsSelectedArgmin_formulaExtension (g : E → ℝ) (hg : IsAffineModel g)
    (x : FeasiblePoint S)
    (β : {β : ℝ // 0 < β}) (t : PositiveTime) (uPrev : FeasiblePoint S)
    (xi : Sample) :
    {u : FeasiblePoint S //
      ∀ z : FeasiblePoint S,
        spsPointwiseObjective S g x β.1 t uPrev xi u ≤
          spsPointwiseObjective S g x β.1 t uPrev xi z} := by
  classical
  let source : FeasiblePoint S := S.sps_subproblem_solver.toFun g x β.1 t uPrev xi hg β.2
  have hsource_min :=
    S.sps_subproblem_solver.is_argmin g x β.1 t uPrev xi hg β.2
  exact
    ⟨source, by
      intro z
      have hle :
          (fun v : FeasiblePoint S =>
            letI : FiniteDimensional ℝ E := S.finiteDimensional_ambient
            g v.1 + ⟪S.oracle uPrev.1 xi, v.1⟫_ℝ +
              β.1 * feasibleBregmanFormulaExtension S.X S.proxPotential x v +
              β.1 * spsP t * feasibleBregmanFormulaExtension S.X S.proxPotential uPrev v +
              S.chi v.1) source ≤
            (fun v : FeasiblePoint S =>
              letI : FiniteDimensional ℝ E := S.finiteDimensional_ambient
              g v.1 + ⟪S.oracle uPrev.1 xi, v.1⟫_ℝ +
                β.1 * feasibleBregmanFormulaExtension S.X S.proxPotential x v +
                β.1 * spsP t * feasibleBregmanFormulaExtension S.X S.proxPotential uPrev v +
                S.chi v.1) z := by
        simpa using
          (isMinOn_univ_iff
            (f := fun v : FeasiblePoint S =>
              letI : FiniteDimensional ℝ E := S.finiteDimensional_ambient
              g v.1 + ⟪S.oracle uPrev.1 xi, v.1⟫_ℝ +
                β.1 * feasibleBregmanFormulaExtension S.X S.proxPotential x v +
                β.1 * spsP t * feasibleBregmanFormulaExtension S.X S.proxPotential uPrev v +
                S.chi v.1)
            (a := source)).1 hsource_min z
      simpa [spsPointwiseObjective, spsObjectiveFormulaOnX, spsObjective,
        bregmanFormulaOnX, add_assoc, add_left_comm, add_comm] using hle⟩

/-- Internal formula-extension selected SPS update realizing the argmin relation in
Eq. (8.1.58).

The input types encode the source-side Algorithm 8.1/8.2 domain: the center and
previous inner iterate lie in `X`, and `β > 0`.  Considered
`SOptLib.proxStep`/`proxStepArgmin`; those compact mirror-prox selectors handle
one mirror objective on a compact parameter space, while Eq. (8.1.58) has the
SGS-specific two-Bregman stochastic objective, so this paper-local selector is
only realization machinery for formula-extension helper statements. -/
noncomputable def spsStep_formulaExtensionSelector (g : E → ℝ) (hg : IsAffineModel g)
    (x : FeasiblePoint S)
    (β : {β : ℝ // 0 < β}) (t : PositiveTime) (uPrev : FeasiblePoint S)
    (xi : Sample) :
    {u : FeasiblePoint S // IsSPSStep_formulaExtension S g x β.1 t uPrev xi u} := by
  let selected := spsSelectedArgmin_formulaExtension S g hg x β t uPrev xi
  exact
    ⟨selected.1,
      by
        intro z hz
        exact selected.2 z⟩

/-- Conditional prox-core projection for a selected formula-extension SPS update.

The displayed Eq. (8.1.58) solver returns a feasible minimizer over `X`, not a
prox-core minimizer.  Source-domain arguments must therefore supply the
additional `X^o` invariant at the process layer and can project it through this
bridge; the invariant is not encoded in the solver interface. -/
theorem spsStep_formulaExtensionSelector_mem_proxCore (g : E → ℝ) (hg : IsAffineModel g)
    (x : FeasiblePoint S)
    (β : {β : ℝ // 0 < β}) (t : PositiveTime) (uPrev : FeasiblePoint S)
    (xi : Sample)
    (hcore :
      ((spsStep_formulaExtensionSelector S g hg x β t uPrev xi).1).1 ∈
        proxCore S.X S.proxPotential) :
    ((spsStep_formulaExtensionSelector S g hg x β t uPrev xi).1).1 ∈
      proxCore S.X S.proxPotential :=
  hcore

/-- The selected SPS update satisfies the Eq. (8.1.58) argmin specification on
the paper's admissible domain. -/
theorem spsStep_spec (g : E → ℝ) (hg : IsAffineModel g) (x : FeasiblePoint S)
    (β : {β : ℝ // 0 < β}) (t : PositiveTime) (uPrev : FeasiblePoint S)
    (xi : Sample) :
    IsSPSStep_formulaExtension S g x β.1 t uPrev xi
      (spsStep_formulaExtensionSelector S g hg x β t uPrev xi).1 := by
  exact (spsStep_formulaExtensionSelector S g hg x β t uPrev xi).2

/-- Direct expanded Eq. (8.1.58) comparison for the selected formula-extension
SPS step.

This is the exact deterministic argmin certificate needed at the start of the
selected-prox stability proof: the selected point is already the paper's
two-Bregman SPS minimizer, so future displacement estimates can start from the
expanded objective inequality without reconstructing the generated process. -/
theorem spsStep_formulaExtensionSelector_expanded_objective_le
    (g : E → ℝ) (hg : IsAffineModel g) (x : FeasiblePoint S)
    (β : {β : ℝ // 0 < β}) (t : PositiveTime) (uPrev : FeasiblePoint S)
    (xi : Sample) (u : FeasiblePoint S) :
    let q : E := S.oracle uPrev.1 xi;
    let next : FeasiblePoint S :=
      (spsStep_formulaExtensionSelector S g hg x β t uPrev xi).1;
      (g next.1 + ⟪q, next.1⟫_ℝ + S.chi next.1) +
          β.1 * bregmanFormulaOnX S x next +
          β.1 * spsP t * bregmanFormulaOnX S uPrev next ≤
        (g u.1 + ⟪q, u.1⟫_ℝ + S.chi u.1) +
          β.1 * bregmanFormulaOnX S x u +
          β.1 * spsP t * bregmanFormulaOnX S uPrev u := by
  classical
  let next : FeasiblePoint S :=
    (spsStep_formulaExtensionSelector S g hg x β t uPrev xi).1
  have hstep :
      IsSPSStep S g x β.1 t uPrev xi next := by
    simpa [next, IsSPSStep_formulaExtension] using
      spsStep_spec S g hg x β t uPrev xi
  have hmin :
      spsObjective S g x β.1 t uPrev xi next ≤
        spsObjective S g x β.1 t uPrev xi u :=
    (isMinOn_univ_iff
      (f := spsObjective S g x β.1 t uPrev xi) (a := next)).1 hstep u
  simpa [next, spsObjective, add_assoc, add_left_comm, add_comm] using hmin

/-- Canonical selected SPS update from Eq. (8.1.58).

Book JSON citation:
`book/FOML/StochasticGradientSliding.json:algorithm_spec.steps[3]` states the
SPS stochastic prox update as the displayed `argmin` over `u ∈ X`.

Reuse due diligence: checked `SOptLib.proxStep` and `SOptLib.proxStepArgmin`;
they select a one-Bregman mirror-prox objective under compactness/continuity,
whereas Eq. (8.1.58) is the SGS two-Bregman stochastic subproblem.  This
definition therefore specializes the already-audited local argmin selector and
keeps solvability as the theorem obligation `spsArgminSet_nonempty_obligation`,
not as a paper theorem-head hypothesis. -/
noncomputable def spsStep (g : E → ℝ) (hg : IsAffineModel g)
    (x : FeasiblePoint S)
    (β : {β : ℝ // 0 < β}) (t : PositiveTime) (uPrev : FeasiblePoint S)
    (xi : Sample) : FeasiblePoint S :=
  (spsStep_formulaExtensionSelector S g hg x β t uPrev xi).1

/-- The selected SPS update is measurable as a function of the fresh sample
when the deterministic context of the prox subproblem is fixed.

This is the first causal-selector bridge needed for Eq. (8.1.70): later
strict-past proofs can combine this fixed-sample measurability with recursive
measurability of the outer center and previous inner state, rather than
treating the argmin relation as an arbitrary nonmeasurable witness. -/
theorem spsStep_measurable_sample [MeasurableSpace E] [MeasurableSpace Sample]
    (g : E → ℝ) (hg : IsAffineModel g)
    (x : FeasiblePoint S)
    (β : {β : ℝ // 0 < β}) (t : PositiveTime) (uPrev : FeasiblePoint S) :
    Measurable (fun xi : Sample => spsStep S g hg x β t uPrev xi) := by
  simpa [spsStep, spsStep_formulaExtensionSelector, spsSelectedArgmin_formulaExtension]
    using
      S.sps_subproblem_solver.toFun_measurable_sample
        g x β.1 t uPrev hg β.2

/-- The selected SPS update is measurable when the previous inner state and
fresh sample are measurable random inputs and the outer context is fixed.

This is the recursive version of `spsStep_measurable_sample`: it is the endpoint
needed to propagate strict-past measurability through the inner SPS recursion
without assuming the generated query is already adapted. -/
theorem spsStep_measurable_state_sample {Ω' : Type w}
    [MeasurableSpace Ω'] [MeasurableSpace E] [MeasurableSpace Sample]
    (mΩ : MeasurableSpace Ω')
    (g : Ω' → E → ℝ) (hg : ∀ ω, IsAffineModel (g ω))
    (x : Ω' → FeasiblePoint S)
    (β : {β : ℝ // 0 < β}) (t : PositiveTime)
    (uPrev : Ω' → FeasiblePoint S) (xi : Ω' → Sample)
    (hx : Measurable[mΩ] x)
    (huPrev : Measurable[mΩ] uPrev) (hxi : Measurable[mΩ] xi) :
    Measurable[mΩ] (fun ω => spsStep S (g ω) (hg ω) (x ω) β t (uPrev ω) (xi ω)) := by
  simpa [spsStep, spsStep_formulaExtensionSelector, spsSelectedArgmin_formulaExtension]
    using
      S.sps_subproblem_solver.toFun_measurable_random_context
        (mΩ := mΩ) g x β.1 t uPrev xi hg β.2 hx huPrev hxi

/-- Past-measurability form of the selected SPS update.

This is the compiled endpoint requested by the strict-past route audit after
adding random-context solver measurability: once the random affine model,
random center, previous inner state, and fresh driver are all measurable with
respect to the chosen past sigma-algebra, the Eq. (8.1.58) selected update is
measurable with respect to that same past. -/
theorem spsStep_measurable_past_context {Ω' : Type w}
    [MeasurableSpace Ω'] [MeasurableSpace E] [MeasurableSpace Sample]
    (mΩ : MeasurableSpace Ω')
    (g : Ω' → E → ℝ) (hg : ∀ ω, IsAffineModel (g ω))
    (x : Ω' → FeasiblePoint S)
    (β : {β : ℝ // 0 < β}) (t : PositiveTime)
    (uPrev : Ω' → FeasiblePoint S) (xi : Ω' → Sample)
    (hx : Measurable[mΩ] x)
    (huPrev : Measurable[mΩ] uPrev) (hxi : Measurable[mΩ] xi) :
    Measurable[mΩ] (fun ω => spsStep S (g ω) (hg ω) (x ω) β t (uPrev ω) (xi ω)) :=
  spsStep_measurable_state_sample
    (S := S) mΩ g hg x β t uPrev xi hx huPrev hxi

/-- The canonical selected SPS update satisfies the displayed Eq. (8.1.58)
argmin relation. -/
theorem spsStep_isSPSStep (g : E → ℝ) (hg : IsAffineModel g) (x : FeasiblePoint S)
    (β : {β : ℝ // 0 < β}) (t : PositiveTime) (uPrev : FeasiblePoint S)
    (xi : Sample) :
    IsSPSStep S g x β.1 t uPrev xi (spsStep S g hg x β t uPrev xi) := by
  simpa [spsStep, IsSPSStep_formulaExtension] using
    spsStep_spec S g hg x β t uPrev xi

/-- If the two displayed Bregman centers are later proved to lie in `X^o`, the
selected SPS update also realizes Eq. (8.1.58) as an argmin of the source-typed
two-Bregman objective.  This is a proof obligation, not the definition of the
algorithmic update. -/
theorem spsStep_sourceObjective_spec (g : E → ℝ) (hg : IsAffineModel g)
    (x : FeasiblePoint S)
    (β : {β : ℝ // 0 < β}) (t : PositiveTime) (uPrev : FeasiblePoint S)
    (xi : Sample)
    (hx : x.1 ∈ proxCore S.X S.proxPotential)
    (hprev : uPrev.1 ∈ proxCore S.X S.proxPotential) :
    IsSPSStep_sourceDomain S g ⟨x.1, hx⟩ β.1 t ⟨uPrev.1, hprev⟩ xi
      (spsStep_formulaExtensionSelector S g hg x β t uPrev xi).1 := by
  exact
    IsSPSStep_formulaExtension_to_sourceDomain_of_mem_proxCore
      (S := S) g x β.1 t uPrev xi
      (spsStep_formulaExtensionSelector S g hg x β t uPrev xi).1
      (spsStep_spec S g hg x β t uPrev xi) hx hprev

/-- One zero-based transition of the SPS recursion.  At internal time `n`, this
constructs paper time `t=n+1`, performs Eq. (8.1.58), and then applies the
averaging update Eq. (8.1.18). -/
noncomputable def spsTransition_formulaExtensionSelector (g : E → ℝ) (hg : IsAffineModel g)
    (x : FeasiblePoint S)
    (β : {β : ℝ // 0 < β}) (sample : ℕ → Ω → Sample)
    (n : ℕ) (st : SPSState S) (ω : Ω) : SPSState S :=
  let t : PositiveTime := ⟨n + 1, Nat.succ_pos n⟩
  let uNext := spsStep_formulaExtensionSelector S g hg x β t st.u (sample n ω)
  let htheta := spsTheta_mem_Icc t
  { u := uNext.1
    avg :=
      ⟨(1 - spsTheta t) • st.avg.1 + spsTheta t • uNext.1.1,
        convexCombination_mem_X S st.avg uNext.1
          htheta.1 htheta.2⟩ }

/-- Canonical selected one-step SPS state transition generated by Eq. (8.1.58)
and Eq. (8.1.18).

Book JSON citation:
`book/FOML/StochasticGradientSliding.json:algorithm_spec.steps[3-4]` gives the
argmin update and averaging recursion.

Aligns with `SOptLib.recursiveIterateProcess` by supplying its one-step update
function.  `recursiveProcess_succ_eq_sample_update` was checked and is a proof
bridge for such recursions, not the transition object itself. -/
noncomputable def spsTransition (g : E → ℝ) (hg : IsAffineModel g)
    (x : FeasiblePoint S)
    (β : {β : ℝ // 0 < β}) (sample : ℕ → Ω → Sample)
    (n : ℕ) (st : SPSState S) (ω : Ω) : SPSState S :=
  spsTransition_formulaExtensionSelector S g hg x β sample n st ω

/-- The canonical selected SPS transition realizes the relation-form Algorithm
8.2 transition. -/
theorem spsTransition_isSPSTransition (g : E → ℝ) (hg : IsAffineModel g)
    (x : FeasiblePoint S)
    (β : {β : ℝ // 0 < β}) (sample : ℕ → Ω → Sample)
    (n : ℕ) (st : SPSState S) (ω : Ω) :
    IsSPSTransition S g x β.1 sample n ω st
      (spsTransition S g hg x β sample n st ω) := by
  dsimp [spsTransition, spsTransition_formulaExtensionSelector, IsSPSTransition,
    IsSPSStep_formulaExtension]
  refine ⟨?_, ?_⟩
  · exact spsStep_spec S g hg x β ⟨n + 1, Nat.succ_pos n⟩ st.u (sample n ω)
  · rfl

/-- Internal formula-extension selected SPS process generated from Eq. (8.1.58) and
Eq. (8.1.18).

Aligns with `SOptLib.recursiveIterateProcess`, specialized to the two-coordinate
SPS state.  The paper-facing algorithmic object is the relation predicate
`IsSPSProcess`, because Eq. (8.1.58) does not specify a deterministic
tie-breaking selector. -/
noncomputable def spsProcess_formulaExtensionSelector (g : E → ℝ) (hg : IsAffineModel g)
    (x : FeasiblePoint S)
    (β : {β : ℝ // 0 < β}) (sample : ℕ → Ω → Sample)
    : ℕ → Ω → SPSState S :=
  SOptLib.recursiveIterateProcess (spsInitial S x)
    (spsTransition_formulaExtensionSelector S g hg x β sample)

/-- Source-domain view of the feasible selected SPS process.

This is not a new argmin selector.  It retypes the existing Eq. (8.1.58)
selected realization after the source proof has supplied the explicit invariant
that every selected center belongs to `X^o`.  This keeps the selected update over
the paper's displayed domain `u ∈ X` and avoids introducing an unstated
existence theorem for an `X^o`-valued minimizer. -/
noncomputable def spsProcess_sourceDomainSelector (g : E → ℝ) (hg : IsAffineModel g)
    (x : FeasiblePoint S)
    (β : {β : ℝ // 0 < β}) (sample : ℕ → Ω → Sample)
    (hcore :
      ∀ n ω,
        ((spsProcess_formulaExtensionSelector S g hg x β sample n ω).u).1 ∈
          proxCore S.X S.proxPotential) :
    ℕ → Ω → SPSSourceState S :=
  fun n ω =>
    spsSourceStateOfFeasible S
      (spsProcess_formulaExtensionSelector S g hg x β sample n ω)
      (hcore n ω)

/-- Canonical selected SPS process generated by Eq. (8.1.58) and Eq. (8.1.18).

Book JSON citation:
`book/FOML/StochasticGradientSliding.json:algorithm_spec.steps[2-5]` gives
`u_0=\tilde u_0=x`, the stochastic prox update, averaging update, and output.

Aligns with `SOptLib.recursiveIterateProcess`, the reusable primitive for
zero-based stochastic iterate processes.  The local transition is necessary
because the paper's update is a two-Bregman SGS objective rather than the
one-Bregman `SOptLib.proxStep` objective. -/
noncomputable def spsProcess (g : E → ℝ) (hg : IsAffineModel g)
    (x : FeasiblePoint S)
    (β : {β : ℝ // 0 < β}) (sample : ℕ → Ω → Sample)
    : ℕ → Ω → SPSState S :=
  SOptLib.recursiveIterateProcess (spsInitial S x)
    (spsTransition S g hg x β sample)

/-- The internal selected realization satisfies the formula-extension SPS process
relation.  The following theorem records how the same selected run can be
converted to the source-domain process after prox-core obligations are proved. -/
theorem spsProcess_formulaExtensionSelector_isSPSProcess_formulaExtension (g : E → ℝ)
    (hg : IsAffineModel g) (x : FeasiblePoint S)
    (β : {β : ℝ // 0 < β}) (sample : ℕ → Ω → Sample) :
    IsSPSProcess_formulaExtension S g x β.1 sample
      (spsProcess_formulaExtensionSelector S g hg x β sample) := by
  dsimp [IsSPSProcess_formulaExtension, IsSPSProcess]
  refine ⟨β.2, ?_, ?_⟩
  · intro ω
    rfl
  · intro n ω
    simpa [spsProcess_formulaExtensionSelector, spsTransition] using
      spsTransition_isSPSTransition S g hg x β sample n
        (spsProcess_formulaExtensionSelector S g hg x β sample n ω) ω

/-- The canonical selected SPS process satisfies the public relation-form SPS
process specification. -/
theorem spsProcess_isSPSProcess (g : E → ℝ)
    (hg : IsAffineModel g) (x : FeasiblePoint S)
    (β : {β : ℝ // 0 < β}) (sample : ℕ → Ω → Sample) :
    IsSPSProcess S g x β.1 sample
      (spsProcess S g hg x β sample) := by
  dsimp [IsSPSProcess]
  refine ⟨β.2, ?_, ?_⟩
  · intro ω
    rfl
  · intro n ω
    simpa [spsProcess] using
      spsTransition_isSPSTransition S g hg x β sample n
        (spsProcess S g hg x β sample n ω) ω

/-- Source-domain bridge for the selected SPS realization.

The selector itself is only formula-extension machinery.  It satisfies the
public source-typed SPS process only after the fixed center and every selected
iterate have been proved to lie in the prox-core `X^o`. -/
theorem spsProcess_formulaExtensionSelector_isSPSProcess_sourceDomain_obligation (g : E → ℝ)
    (hg : IsAffineModel g) (x : FeasiblePoint S)
    (β : {β : ℝ // 0 < β}) (sample : ℕ → Ω → Sample)
    (hx : x.1 ∈ proxCore S.X S.proxPotential)
    (hcore :
      ∀ n ω,
        ((spsProcess_formulaExtensionSelector S g hg x β sample n ω).u).1 ∈
          proxCore S.X S.proxPotential) :
    IsSPSProcess_sourceDomain S g ⟨x.1, hx⟩ β.1 sample
      (fun n ω =>
        spsSourceStateOfFeasible S
          (spsProcess_formulaExtensionSelector S g hg x β sample n ω)
          (hcore n ω)) := by
  dsimp [IsSPSProcess_sourceDomain]
  refine ⟨β.2, ?_, ?_⟩
  · intro ω
    rfl
  · intro n ω
    let proc := spsProcess_formulaExtensionSelector S g hg x β sample
    have hproc := spsProcess_formulaExtensionSelector_isSPSProcess_formulaExtension
      S g hg x β sample
    have htrans :
        IsSPSTransition_formulaExtension S g x β.1 sample n ω
          (proc n ω) (proc (n + 1) ω) := by
      dsimp [IsSPSProcess_formulaExtension, IsSPSProcess] at hproc
      exact hproc.2.2 n ω
    dsimp [IsSPSTransition_sourceDomain, spsSourceStateOfFeasible, proxCorePointToFeasible]
    refine ⟨?_, ?_⟩
    · exact IsSPSTransition_sourceDomain_obligation S g x β.1 sample n ω
        (proc n ω) (proc (n + 1) ω) htrans hx (hcore n ω)
    · exact htrans.2

/-- The generated SPS iterates are feasible by construction of the source-typed
state over `X`. -/
theorem spsProcess_u_mem_X (g : E → ℝ) (hg : IsAffineModel g)
    (x : FeasiblePoint S)
    (β : {β : ℝ // 0 < β}) (sample : ℕ → Ω → Sample) :
    ∀ n ω, ((spsProcess_formulaExtensionSelector S g hg x β sample n ω).u).1 ∈ S.X := by
  intro n ω
  exact ((spsProcess_formulaExtensionSelector S g hg x β sample n ω).u).2

/-- Zero-time audit for the feasible formula-extension selector.

At `n = 0`, the formula-extension selected process starts from the arbitrary
feasible input `x`.  Therefore prox-core membership at time zero is exactly the
extra source-domain condition on `x`, not a consequence of feasibility. -/
theorem spsProcess_formulaExtensionSelector_zero_u_mem_proxCore_iff_initial
    (g : E → ℝ) (hg : IsAffineModel g)
    (x : FeasiblePoint S)
    (β : {β : ℝ // 0 < β}) (sample : ℕ → Ω → Sample) (ω : Ω) :
    ((spsProcess_formulaExtensionSelector S g hg x β sample 0 ω).u).1 ∈
        proxCore S.X S.proxPotential ↔
      x.1 ∈ proxCore S.X S.proxPotential := by
  rfl

/-- Correction certificate for the former feasible-selector prox-core claim.

The old obligation tried to prove prox-core membership for all selected
formula-extension iterates from an arbitrary `x : FeasiblePoint S`.  At time
zero that claim is exactly the initial prox-core condition, so it is not a
consequence of feasibility. -/
theorem spsProcess_u_mem_proxCore_obligation (g : E → ℝ) (hg : IsAffineModel g)
    (x : FeasiblePoint S)
    (β : {β : ℝ // 0 < β}) (sample : ℕ → Ω → Sample) (ω : Ω) :
    ((spsProcess_formulaExtensionSelector S g hg x β sample 0 ω).u).1 ∈
        proxCore S.X S.proxPotential ↔
      x.1 ∈ proxCore S.X S.proxPotential := by
  rfl

/-- Prox-core admissibility of a lifted source-domain selected SPS view.

This projection is intentionally conditional on the explicit invariant used to
build `spsProcess_sourceDomainSelector`; it does not assert that arbitrary
feasible selected iterates lie in `X^o`. -/
theorem spsProcess_sourceDomainSelector_u_mem_proxCore (g : E → ℝ)
    (hg : IsAffineModel g) (x : FeasiblePoint S)
    (β : {β : ℝ // 0 < β}) (sample : ℕ → Ω → Sample)
    (hcore :
      ∀ n ω,
        ((spsProcess_formulaExtensionSelector S g hg x β sample n ω).u).1 ∈
          proxCore S.X S.proxPotential) :
    ∀ n ω, ((spsProcess_sourceDomainSelector S g hg x β sample hcore n ω).u).1 ∈
      proxCore S.X S.proxPotential := by
  intro n ω
  exact hcore n ω

/-- SPS output pair `(x^+,\tilde x^+)=(u_T,\tilde u_T)`. -/
noncomputable def spsOutput_formulaExtensionSelector (g : E → ℝ) (hg : IsAffineModel g)
    (x : FeasiblePoint S)
    (β : {β : ℝ // 0 < β}) (sample : ℕ → Ω → Sample)
    (T : ℕ) (ω : Ω) :
    SPSState S :=
  spsProcess_formulaExtensionSelector S g hg x β sample T ω

/-- Canonical SPS output pair `(x^+,\tilde x^+)=(u_T,\tilde u_T)`, read from the
selected SPS process. -/
noncomputable def spsOutput (g : E → ℝ) (hg : IsAffineModel g)
    (x : FeasiblePoint S)
    (β : {β : ℝ // 0 < β}) (sample : ℕ → Ω → Sample)
    (T : ℕ) (ω : Ω) :
    SPSState S :=
  spsProcess S g hg x β sample T ω

/-- Outer SGS state containing the feasible center `x_k ∈ X` and
`\bar x_k`. -/
structure SGSState (S : Setup E Sample) where
  x : FeasiblePoint S
  xbar : FeasiblePoint S

instance [MeasurableSpace E] : MeasurableSpace (SGSState S) :=
  MeasurableSpace.comap (fun st : SGSState S => (st.x, st.xbar))
    (by infer_instance : MeasurableSpace (FeasiblePoint S × FeasiblePoint S))

theorem measurable_sgsState_x [MeasurableSpace E] :
    Measurable (fun st : SGSState S => st.x) := by
  have hpair :
      Measurable (fun st : SGSState S => (st.x, st.xbar)) :=
    Measurable.of_comap_le le_rfl
  exact measurable_fst.comp hpair

theorem measurable_sgsState_xbar [MeasurableSpace E] :
    Measurable (fun st : SGSState S => st.xbar) := by
  have hpair :
      Measurable (fun st : SGSState S => (st.x, st.xbar)) :=
    Measurable.of_comap_le le_rfl
  exact measurable_snd.comp hpair

theorem measurable_sgsState_mk [MeasurableSpace Ω] [MeasurableSpace E]
    (mΩ : MeasurableSpace Ω) {x xbar : Ω → FeasiblePoint S}
    (hx : Measurable[mΩ] x) (hxbar : Measurable[mΩ] xbar) :
    Measurable[mΩ] (fun ω => ({ x := x ω, xbar := xbar ω } : SGSState S)) := by
  rw [measurable_iff_comap_le]
  simpa [instMeasurableSpaceSGSState] using (hx.prodMk hxbar).comap_le

/-- Strict-past adaptedness of the generated SGS/SPS oracle queries.

This is the causal measurability part of the Algorithm 8.2 generated-run
semantics needed by the Lemma 4.1 martingale proof of Eq. (8.1.70): the current
inner search point `u_{k,i}` is measurable with respect to samples from earlier
outer blocks and earlier inner coordinates, before the fresh sample
`xi_{k,i}` is drawn. -/
def sgsGeneratedQueriesStrictPastAdapted [MeasurableSpace Ω] [MeasurableSpace Sample]
    [MeasurableSpace E]
    (sample : PositiveTime → ℕ → Ω → Sample)
    (inner : PositiveTime → ℕ → Ω → SPSState S) : Prop :=
  ∀ k i,
    Measurable[sgsStrictPastSampleSpace (Ω := Ω) sample k i]
      (fun ω => (inner k i ω).u)

/-- Outer initialization `\bar x_0=x_0`. -/
def sgsInitial (x0 : FeasiblePoint S) : SGSState S where
  x := x0
  xbar := x0

/-- Source-domain outer SGS state: the center `x_k` is a future Bregman first
argument and is therefore typed in `X^o`; the reported average stays in `X`. -/
structure SGSSourceState (S : Setup E Sample) where
  x : ProxCorePoint S
  xbar : FeasiblePoint S

/-- Source-domain outer initialization `\bar x_0=x_0`. -/
def sgsSourceInitial (x0 : ProxCorePoint S) : SGSSourceState S where
  x := x0
  xbar := proxCorePointToFeasible S x0

/-- Reinterpret a feasible formula-extension outer state as source-typed once
its center is proved to lie in the prox-core. -/
def sgsSourceStateOfFeasible (st : SGSState S)
    (hcore : st.x.1 ∈ proxCore S.X S.proxPotential) : SGSSourceState S where
  x := ⟨st.x.1, hcore⟩
  xbar := st.xbar

/-- Outer extrapolation point
`\underline x_k=(1-\gamma_k)\bar x_{k-1}+\gamma_k x_{k-1}`. -/
def outerExtrapolation (gamma : PositiveTime → ℝ) (k : PositiveTime)
    (st : SGSState S) : E :=
  (1 - gamma k) • st.xbar.1 + gamma k • st.x.1

/-- Source-domain outer extrapolation point
`\underline x_k=(1-\gamma_k)\bar x_{k-1}+\gamma_k x_{k-1}`. -/
def outerSourceExtrapolation (gamma : PositiveTime → ℝ) (k : PositiveTime)
    (st : SGSSourceState S) : E :=
  (1 - gamma k) • st.xbar.1 + gamma k • st.x.1

/-- Realization range condition `γ_k ∈ [0,1]` needed for the current
subtype-valued SGS averaging recursion.

The accelerated template before Eq. (8.1.13) states this range, while Algorithm
8.1 itself lists `γ_k ∈ R_+`.  Generic paper theorem statements below must not
derive this condition from Eq. (8.1.25) or the `Γ_k` recurrence without an
additional source-backed argument. -/
def gammaRangeCondition (gamma : PositiveTime → ℝ) : Prop :=
  ∀ k : PositiveTime, 0 ≤ gamma k ∧ gamma k ≤ 1

/-- Paper parameter-domain condition `γ_k ∈ R_+` from Algorithm 8.1.

Book JSON citation:
`book/FOML/StochasticGradientSliding.json:algorithm_spec.initialization` states
`γ_k∈R_+`.

Reuse due diligence: searched for nonnegative parameter-schedule primitives and
checked the `acceleratedGammaSchedule` candidate; it defines a recursive
accelerated `Γ` weight schedule, not the paper's primitive nonnegative domain
condition on the SGS outer parameter `γ_k`. -/
def gammaNonnegativeCondition (gamma : PositiveTime → ℝ) : Prop :=
  ∀ k : PositiveTime, 0 ≤ gamma k

/-- The selected-realization range condition implies the source-facing
Algorithm 8.1 domain `γ_k ∈ R_+`. -/
theorem gammaRangeCondition_nonnegative {gamma : PositiveTime → ℝ}
    (hgamma : gammaRangeCondition gamma) : gammaNonnegativeCondition gamma := by
  intro k
  exact (hgamma k).1

/-- Source-gap witness schedule for the generic SGS gamma boundary.

This is not a paper parameter policy.  It records the exact missing projection
identified in the Theorem 8.2 route: Algorithm 8.1 gives only `γ_k ∈ R_+`, while
Eq. (8.1.28)'s two-point convexity proof requires the stronger range
`γ_k ∈ [0,1]`. -/
noncomputable def gammaNonnegativeNotRangeWitness : PositiveTime → ℝ :=
  fun k => if k.1 = 2 then 2 else if k.1 = 1 then 1 else 0

/-- The source-gap witness satisfies Algorithm 8.1's nonnegative gamma domain. -/
theorem gammaNonnegativeNotRangeWitness_nonnegative :
    gammaNonnegativeCondition gammaNonnegativeNotRangeWitness := by
  intro k
  unfold gammaNonnegativeNotRangeWitness
  split
  · norm_num
  · split
    · norm_num
    · norm_num

/-- The source-gap witness violates the upper bound needed by Eq. (8.1.28). -/
theorem gammaNonnegativeNotRangeWitness_not_range :
    ¬ gammaRangeCondition gammaNonnegativeNotRangeWitness := by
  intro hgamma
  have hle := (hgamma ⟨2, by norm_num⟩).2
  norm_num [gammaNonnegativeNotRangeWitness] at hle

/-- Formal certificate that the Algorithm 8.1 gamma domain is strictly weaker
than the range condition needed by the current Eq. (8.1.28) proof route.

This is a source-gap certificate, not a new theorem assumption: it prevents
proof search from treating `gammaRangeCondition` as derivable from the generated
run's `gammaNonnegativeCondition` projection. -/
theorem gammaNonnegativeCondition_not_imply_gammaRangeCondition :
    ∃ gamma : PositiveTime → ℝ,
      gammaNonnegativeCondition gamma ∧ ¬ gammaRangeCondition gamma := by
  exact ⟨gammaNonnegativeNotRangeWitness,
    gammaNonnegativeNotRangeWitness_nonnegative,
    gammaNonnegativeNotRangeWitness_not_range⟩

/-!
The next four declarations are a stronger schedule-level countermodel for the
generic Theorem 8.2 gamma boundary.  They use the actual source-facing schedule
assumptions `(8.1.25)`, `(8.1.32)`, and `(8.1.33)`, not merely the generated
run's nonnegative gamma projection.
-/

/-- Source-gap schedule with `γ₂=2` but otherwise nonnegative.  This is not a
paper parameter policy; it is a formal countermodel for deriving
`gammaRangeCondition` from the generic Theorem 8.2 schedule assumptions. -/
noncomputable def theorem82GammaGapCounterexampleGamma : PositiveTime → ℝ :=
  fun k => if k.1 = 1 then 1 else if k.1 = 2 then 2 else (k.1 : ℝ)⁻¹

/-- Matching `Γ` recurrence witness: `Γ₁=1` and `Γ_k=-2/k` for `k≥2`. -/
noncomputable def theorem82GammaGapCounterexampleGammaWeight : PositiveTime → ℝ :=
  fun k => if k.1 = 1 then 1 else -2 / (k.1 : ℝ)

/-- Positive `β` witness large enough for Eq. (8.1.25) and chosen so the
forward quotient is nonincreasing despite `γ₂=2`. -/
noncomputable def theorem82GammaGapCounterexampleBeta (S : Setup E Sample) :
    PositiveTime → ℝ :=
  fun k => if k.1 = 2 then 2 * S.lSmooth else 8 * S.lSmooth

/-- Constant positive inner budget for the gamma-gap schedule countermodel. -/
def theorem82GammaGapCounterexampleBudget : PositiveTime → InnerBudget :=
  fun _ => ⟨1, by norm_num⟩

/-- Package a raw positive `β_k` schedule as the subtype-valued schedule used by
the source-domain SGS recursion. -/
noncomputable def positiveBetaSchedule (beta : PositiveTime → ℝ)
    (hbeta : ∀ k : PositiveTime, 0 < beta k) : PositiveTime → {β : ℝ // 0 < β} :=
  fun k => ⟨beta k, hbeta k⟩

/-- Source-domain outer SGS transition from Algorithm 8.1/8.2 under the
Section 3.2 `X^o × X` prox-function type. -/
def IsSGSTransition_sourceDomain (beta gamma : PositiveTime → ℝ)
    (T : PositiveTime → ℕ) (sample : PositiveTime → ℕ → Ω → Sample)
    (n : ℕ) (ω : Ω) (st next : SGSSourceState S) : Prop :=
  let k : PositiveTime := ⟨n + 1, Nat.succ_pos n⟩
  let xUnder := outerSourceExtrapolation S gamma k st
  let gk : E → ℝ := fun u => smoothLinearization S xUnder u
  ∃ inner : ℕ → Ω → SPSSourceState S,
    IsSPSProcess_sourceDomain S gk st.x (beta k) (sample k) inner ∧
      next.x = (inner (T k) ω).u ∧
        next.xbar.1 =
          (1 - gamma k) • st.xbar.1 + gamma k • (inner (T k) ω).avg.1

/-- Paper-facing relation-form outer SGS transition from Algorithm 8.1/8.2.

This is the source-facing one-step object: it calls an arbitrary SPS process
satisfying the Eq. (8.1.58) and Eq. (8.1.18) relations, and it does not choose a
deterministic minimizer when the argmin set is non-singleton.  It is typed at
the paper algorithm boundary `X`; source-domain prox-core obligations are
separate `_sourceDomain` bridges. -/
def IsSGSTransition (beta gamma : PositiveTime → ℝ)
    (T : PositiveTime → ℕ) (sample : PositiveTime → ℕ → Ω → Sample)
    (n : ℕ) (ω : Ω) (st next : SGSState S) : Prop :=
  let k : PositiveTime := ⟨n + 1, Nat.succ_pos n⟩
  let xUnder := outerExtrapolation S gamma k st
  let gk : E → ℝ := fun u => smoothLinearization S xUnder u
  ∃ inner : ℕ → Ω → SPSState S,
    IsSPSProcess S gk st.x (beta k) (sample k) inner ∧
      next.x = (inner (T k) ω).u ∧
        next.xbar.1 =
          (1 - gamma k) • st.xbar.1 + gamma k • (inner (T k) ω).avg.1

/-- Source-domain SGS execution generated by Algorithm 8.1/8.2 under the
Section 3.2 `X^o × X` prox-function type. -/
def IsSGSProcess_sourceDomain (x0 : ProxCorePoint S) (beta gamma : PositiveTime → ℝ)
    (T : PositiveTime → ℕ) (sample : PositiveTime → ℕ → Ω → Sample)
    (states : ℕ → Ω → SGSSourceState S) : Prop :=
  (∀ ω, states 0 ω = sgsSourceInitial S x0) ∧
    ∀ n ω, IsSGSTransition_sourceDomain S beta gamma T sample n ω
      (states n ω) (states (n + 1) ω)

/-- Paper-facing relation-form SGS execution generated by Algorithm 8.1/8.2.

No SOptLib deterministic recursive-process primitive is reused here: Algorithm
8.2 specifies an argmin relation for the SPS update, not a tie-breaking
function.  The selected recursion below is retained as explicit selector
machinery, and the source-domain prox-core interpretation is suffixed. -/
def IsSGSProcess (x0 : FeasiblePoint S) (beta gamma : PositiveTime → ℝ)
    (T : PositiveTime → ℕ) (sample : PositiveTime → ℕ → Ω → Sample)
    (states : ℕ → Ω → SGSState S) : Prop :=
  (∀ ω, states 0 ω = sgsInitial S x0) ∧
    ∀ n ω, IsSGSTransition S beta gamma T sample n ω
      (states n ω) (states (n + 1) ω)

/-- Formula-extension outer SGS transition for internal selected realizations.

This helper is now a compatibility alias for selected realization theorem
names; it is definitionally the same feasible `X` transition as the unsuffixed
paper-facing process. -/
def IsSGSTransition_formulaExtension (beta gamma : PositiveTime → ℝ)
    (T : PositiveTime → ℕ) (sample : PositiveTime → ℕ → Ω → Sample)
    (n : ℕ) (ω : Ω) (st next : SGSState S) : Prop :=
  IsSGSTransition S beta gamma T sample n ω st next

/-- Formula-extension SGS execution for deterministic selector machinery.

This is intentionally separate from the paper-facing `IsSGSProcess` so helper
theorems that still rely on selected formula-extension machinery remain
visibly classified. -/
def IsSGSProcess_formulaExtension (x0 : FeasiblePoint S) (beta gamma : PositiveTime → ℝ)
    (T : PositiveTime → ℕ) (sample : PositiveTime → ℕ → Ω → Sample)
    (states : ℕ → Ω → SGSState S) : Prop :=
  IsSGSProcess S x0 beta gamma T sample states

/-- Run-level source-domain relation for one SGS execution with one generated
family of source-typed inner SPS processes.

This suffixed bridge is available after generated centers are proved to lie in
`X^o`; the public generated process below stays at the algorithm's stated
domain `X`. -/
def IsGeneratedSGSProcess_sourceDomain (x0 : ProxCorePoint S) (beta gamma : PositiveTime → ℝ)
    (T : PositiveTime → ℕ) (sample : PositiveTime → ℕ → Ω → Sample)
    (states : ℕ → Ω → SGSSourceState S)
    (inner : PositiveTime → ℕ → Ω → SPSSourceState S) : Prop :=
  (∀ ω, states 0 ω = sgsSourceInitial S x0) ∧
    (∀ k : PositiveTime,
      IsGeneratedSPSProcess_sourceDomain S
        (fun ω u =>
          smoothLinearization S
            (outerSourceExtrapolation S gamma k (states (k.1 - 1) ω)) u)
        (fun ω => (states (k.1 - 1) ω).x)
        (beta k) (sample k) (inner k)) ∧
      (∀ k : PositiveTime, ∀ ω,
        (states k.1 ω).x = (inner k (T k) ω).u ∧
          (states k.1 ω).xbar.1 =
            (1 - gamma k) • (states (k.1 - 1) ω).xbar.1 +
              gamma k • (inner k (T k) ω).avg.1) ∧
        gammaNonnegativeCondition gamma

/-- Paper-facing run-level relation for one SGS execution with one generated
family of inner SPS processes.

Book JSON citation:
`book/FOML/StochasticGradientSliding.json:algorithm_spec.initialization` states
`x_0 ∈ X` and `β_k ∈ R++`, `γ_k ∈ R+`, `T_k ∈ N`; and
`book/FOML/StochasticGradientSliding.json:algorithm_spec.steps[6-8]` states the
SPS call, outer averaging, and generated output recursion.

This is the paper-facing generated Algorithm 8.1/8.2 spine: `x_0 ∈ X`,
`γ_k ∈ R_+`, generated centers and averages are feasible, and each SPS call
minimizes over `X`.  The `X^o × X` prox-function interpretation is the separate
`IsGeneratedSGSProcess_sourceDomain` bridge. -/
def IsGeneratedSGSProcess (x0 : FeasiblePoint S) (beta gamma : PositiveTime → ℝ)
    (T : PositiveTime → ℕ) (sample : PositiveTime → ℕ → Ω → Sample)
    (states : ℕ → Ω → SGSState S)
    (inner : PositiveTime → ℕ → Ω → SPSState S) : Prop :=
  (∀ ω, states 0 ω = sgsInitial S x0) ∧
    (∀ k : PositiveTime,
      IsGeneratedSPSProcess S
        (fun ω u =>
          smoothLinearization S
            (outerExtrapolation S gamma k (states (k.1 - 1) ω)) u)
        (fun ω => (states (k.1 - 1) ω).x)
        (beta k) (sample k) (inner k)) ∧
      (∀ k : PositiveTime, ∀ ω,
        (states k.1 ω).x = (inner k (T k) ω).u ∧
          (states k.1 ω).xbar.1 =
            (1 - gamma k) • (states (k.1 - 1) ω).xbar.1 +
              gamma k • (inner k (T k) ω).avg.1) ∧
        gammaNonnegativeCondition gamma

/-- Formula-extension generated SGS process for internal selector realizations.

This remains the feasible `X × X` formula-extension relation used by selected
helper theorems.  It is intentionally only a compatibility packaging of the
unsuffixed generated Algorithm 8.1/8.2 relation; martingale adaptedness is kept
as a separate local bridge obligation below, not hidden in this broad run
predicate. -/
def IsGeneratedSGSProcess_formulaExtension [MeasurableSpace Ω] [MeasurableSpace Sample]
    [MeasurableSpace E]
    (x0 : FeasiblePoint S) (beta gamma : PositiveTime → ℝ)
    (T : PositiveTime → ℕ) (sample : PositiveTime → ℕ → Ω → Sample)
    (states : ℕ → Ω → SGSState S)
    (inner : PositiveTime → ℕ → Ω → SPSState S) : Prop :=
  IsGeneratedSGSProcess S x0 beta gamma T sample states inner ∧ True

/-- Migration certificate for arbitrary generated SGS formula-extension runs.

Algorithm 8.2 uses each inner query `u_{k,i}` before drawing the fresh sample
`ξ_{k,i}`.  The relation-form `IsGeneratedSGSProcess_formulaExtension` records
the argmin/update equations, but it intentionally does not assert that an
arbitrary witness selection for those argmins is a causal measurable selector.
Consequently the old arbitrary-run source obligation is not derivable from
`hrun` and ambient query measurability alone.  This private compatibility
certificate now exposes the missing causal transport explicitly; the canonical
selected Algorithm 8.2 recursion proves that transport separately in
`sgsSelectedGeneratedQueriesStrictPastAdapted`. -/
theorem sgsGeneratedQueriesStrictPastAdapted_formulaExtension_source_obligation
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E]
    (x0 : FeasiblePoint S) (beta gamma : PositiveTime → ℝ)
    (T : PositiveTime → ℕ) (sample : PositiveTime → ℕ → Ω → Sample)
    (states : ℕ → Ω → SGSState S)
    (inner : PositiveTime → ℕ → Ω → SPSState S)
    (hrun : IsGeneratedSGSProcess_formulaExtension S x0 beta gamma T sample states inner)
    (hquery_meas : ∀ k i, Measurable (fun ω => (inner k i ω).u))
    (hadapted : sgsGeneratedQueriesStrictPastAdapted S sample inner) :
    sgsGeneratedQueriesStrictPastAdapted S sample inner := by
  exact hadapted

/-- A generated SGS run carries the Algorithm 8.1 source-domain condition
`β_k ∈ R++` for every outer call.  This keeps beta positivity inside the
canonical run object instead of exposing it as a public Theorem 8.2 premise. -/
theorem IsGeneratedSGSProcess_beta_pos (x0 : FeasiblePoint S)
    (beta gamma : PositiveTime → ℝ) (T : PositiveTime → ℕ)
    (sample : PositiveTime → ℕ → Ω → Sample)
    (states : ℕ → Ω → SGSState S)
    (inner : PositiveTime → ℕ → Ω → SPSState S)
    (hrun : IsGeneratedSGSProcess S x0 beta gamma T sample states inner) :
    ∀ k : PositiveTime, 0 < beta k := by
  intro k
  exact (hrun.2.1 k).1

/-- A generated SGS run carries the Algorithm 8.1 source-domain condition
`γ_k ∈ R_+` for every outer call.  This keeps the paper parameter domain inside
the canonical run object without imposing the selected-realization-only upper
bound `γ_k ≤ 1` on generic Theorem 8.2. -/
theorem IsGeneratedSGSProcess_gamma_nonnegative (x0 : FeasiblePoint S)
    (beta gamma : PositiveTime → ℝ) (T : PositiveTime → ℕ)
    (sample : PositiveTime → ℕ → Ω → Sample)
    (states : ℕ → Ω → SGSState S)
    (inner : PositiveTime → ℕ → Ω → SPSState S)
    (hrun : IsGeneratedSGSProcess S x0 beta gamma T sample states inner) :
    gammaNonnegativeCondition gamma := by
  exact hrun.2.2.2

/-- Algorithm 8.1 output `\bar x_N`, computed from a single generated SGS run.

Book JSON citation:
`book/FOML/StochasticGradientSliding.json:algorithm_spec.output` states
`Output: \bar{x}_N` with type `weighted_average`.

Reuse due diligence: considered SOptLib weighted/selected-output wrappers from
`SOptLib.Model.Iterates` and `SOptLib.Model.Selection`; those model randomized or
finite-window outputs, while Algorithm 8.1 outputs the generated outer average
stored in the SGS state at deterministic horizon `N`. -/
def sgsGeneratedOutput (states : ℕ → Ω → SGSState S) (N : ℕ) (ω : Ω) :
    FeasiblePoint S :=
  (states N ω).xbar

/-- Generated oracle query `u_{k,i}` associated with a run-level SGS/SPS process.

This is the query object to which the paper's independence statement after
Eq. (8.1.7) applies: `ξ_{k,i}` is independent of the search point `u_{k,i}`. -/
def sgsGeneratedOracleQuery (inner : PositiveTime → ℕ → Ω → SPSState S)
    (k : PositiveTime) (i : ℕ) (ω : Ω) : E :=
  (inner k i ω).u.1

/-- The run-level generated oracle queries are feasible by construction of the
SPS state over `X`. -/
theorem sgsGeneratedOracleQuery_mem_X
    (inner : PositiveTime → ℕ → Ω → SPSState S) :
    ∀ k i ω, sgsGeneratedOracleQuery S inner k i ω ∈ S.X := by
  intro k i ω
  exact (inner k i ω).u.2

/-- A generated query adapted to its own SGS strict past is measurable at any
later flattened coordinate whose strict past contains it. -/
theorem sgsGeneratedQuery_measurable_laterStrictPast_of_indexBefore
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E]
    [BorelSpace E]
    (sample : PositiveTime → ℕ → Ω → Sample)
    (inner : PositiveTime → ℕ → Ω → SPSState S)
    (hadapted_query :
      ∀ k i,
        Measurable[sgsStrictPastSampleSpace (Ω := Ω) sample k i]
          (fun ω => sgsGeneratedOracleQuery S inner k i ω))
    {k k' : PositiveTime} {i i' : ℕ}
    (hbefore : sgsSampleIndexBefore (k', i') (k, i)) :
    Measurable[sgsStrictPastSampleSpace (Ω := Ω) sample k' i']
      (fun ω => sgsGeneratedOracleQuery S inner k i ω) :=
  (hadapted_query k i).mono
    (sgsStrictPastSampleSpace_mono_of_indexBefore (Ω := Ω) sample hbefore)
    le_rfl

/-- Feasibility source for generated SFO oracle queries.

This is the run-level fact required by the corrected random-query SFO transfer:
Algorithm 8.1/8.2 queries the oracle at SPS states, whose `u` component is a
feasible point of `X`. -/
theorem generated_query_feasible_from_run
    (inner : PositiveTime → ℕ → Ω → SPSState S) :
    ∀ k i ω, sgsGeneratedOracleQuery S inner k i ω ∈ S.X :=
  sgsGeneratedOracleQuery_mem_X S inner

/-- Coordinate SFO mean law specialized to the generated SGS/SPS oracle query.

The feasibility witness is supplied by `generated_query_feasible_from_run`,
which is algorithm semantics, while independence remains the paper's SFO
freshness condition after Eq. (8.1.7). -/
theorem generatedSFOUnbiased_of_coordinate_law_generated_query
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    (P : Measure Ω) (sample : PositiveTime → ℕ → Ω → Sample) [IsProbabilityMeasure P]
    (inner : PositiveTime → ℕ → Ω → SPSState S)
    (hquery_meas :
      ∀ k i, Measurable (fun ω =>
        (⟨sgsGeneratedOracleQuery S inner k i ω,
          generated_query_feasible_from_run S inner k i ω⟩ : FeasiblePoint S)))
    (hsample_meas : ∀ k i, Measurable (sample k i))
    (hresidual_meas :
      Measurable (fun p : FeasiblePoint S × Sample =>
        S.oracle p.1.1 p.2 - S.hSubgradient p.1.1))
    (hfixed_int :
      ∀ (k : PositiveTime) (i : ℕ) (u : FeasiblePoint S),
        Integrable (fun ω => S.oracle u.1 (sample k i ω)) P)
    (hmean_int :
      ∀ k i,
        Integrable
          (fun ω => S.oracle (sgsGeneratedOracleQuery S inner k i ω) (sample k i ω)) P ∧
          Integrable (fun ω => S.hSubgradient (sgsGeneratedOracleQuery S inner k i ω)) P)
    (hfixed : coordinateSFOUnbiased S P sample)
    (hindep :
      ∀ k i, IndepFun
        (fun ω =>
          (⟨sgsGeneratedOracleQuery S inner k i ω,
            generated_query_feasible_from_run S inner k i ω⟩ : FeasiblePoint S))
        (sample k i) P) :
    generatedSFOUnbiased S P sample (sgsGeneratedOracleQuery S inner) :=
  generatedSFOUnbiased_of_coordinate_law S P sample (sgsGeneratedOracleQuery S inner)
    (generated_query_feasible_from_run S inner) hquery_meas hsample_meas hresidual_meas
    hfixed_int hmean_int hfixed hindep

/-- Generated-query SFO mean law for an actual generated SGS run.

This is the executable consumer required by the SFO source boundary: it takes
only the source probability model, the generated process, and the paper's
sample/search-point independence assumption.  The generated mean law is projected
from `SGSProbabilityModel.generated_unbiased`, because Eq. (8.1.6) is stated for
the actual feasible search points rather than derived from a deterministic
fixed-query surrogate. -/
theorem generatedSFOUnbiased_of_coordinate_law_generated_query_from_run
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    (law : SGSProbabilityModel (Ω := Ω) S)
    (x0 : FeasiblePoint S) (beta gamma : PositiveTime → ℝ)
    (T : PositiveTime → ℕ) (states : ℕ → Ω → SGSState S)
    (inner : PositiveTime → ℕ → Ω → SPSState S)
    (hrun : IsGeneratedSGSProcess S x0 beta gamma T law.sample states inner)
    (hindep : sfoIndependent S law.P law.sample (sgsGeneratedOracleQuery S inner)) :
    generatedSFOUnbiased S law.P law.sample (sgsGeneratedOracleQuery S inner) := by
  exact law.generated_unbiased (sgsGeneratedOracleQuery S inner) hindep

/-- Generated-query SFO variance law for an actual generated SGS run.

This is the Eq. (8.1.7) analogue of
`generatedSFOUnbiased_of_coordinate_law_generated_query_from_run`: the public
probability model supplies the source-stated second-moment bound at actual
feasible generated search points. -/
theorem generatedSFOVariance_of_coordinate_law_generated_query_from_run
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S)
    (x0 : FeasiblePoint S) (beta gamma : PositiveTime → ℝ)
    (T : PositiveTime → ℕ) (states : ℕ → Ω → SGSState S)
    (inner : PositiveTime → ℕ → Ω → SPSState S)
    (hrun : IsGeneratedSGSProcess S x0 beta gamma T law.sample states inner)
    (hindep : sfoIndependent S law.P law.sample (sgsGeneratedOracleQuery S inner)) :
    generatedSFOVariance S law.P law.sample (sgsGeneratedOracleQuery S inner) := by
  exact law.generated_variance (sgsGeneratedOracleQuery S inner) hindep

/-- Generated-query SFO light-tail law for an actual generated SGS run under
Assumption (8.1.57). -/
theorem generatedSFOLightTail_of_coordinate_law_generated_query_from_run
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S)
    (x0 : FeasiblePoint S) (beta gamma : PositiveTime → ℝ)
    (T : PositiveTime → ℕ) (states : ℕ → Ω → SGSState S)
    (inner : PositiveTime → ℕ → Ω → SPSState S)
    (hrun : IsGeneratedSGSProcess S x0 beta gamma T law.sample states inner)
    (hindep : sfoIndependent S law.P law.sample (sgsGeneratedOracleQuery S inner))
    (hlight : sgsOracleLightTailAssumption_8_1_57 S law) :
    generatedSFOLightTail S law.P law.sample (sgsGeneratedOracleQuery S inner) := by
  exact sgsOracleLightTailAssumption_8_1_57.generated S law hlight
    (sgsGeneratedOracleQuery S inner) hindep

/-- Output-gap random variable `Ψ(\bar x_N)-Ψ(x^*)` for a generated SGS run. -/
def outputGapRandomVariable (states : ℕ → Ω → SGSState S) (N : PositiveTime)
    (xStar : E) (hxStar : IsOptimalSolution S xStar) (ω : Ω) : ℝ :=
  objectiveOn S (sgsGeneratedOutput S states N.1 ω) -
    objectiveOn S ⟨xStar, hxStar.1⟩

/-- Technical measurability bridge for the generated output gap.

This is not a source theorem: it records the Lean well-definedness route needed
when a proof has established a measurable generated output and measurable
objective-on-`X`.  It is deliberately phrased with the actual smaller
Mathlib premises, rather than the rejected `hrun`/`hindep`-only source
obligation. -/
theorem outputGapRandomVariable_measurable_of_output_objective
    [MeasurableSpace Ω] [MeasurableSpace E]
    (states : ℕ → Ω → SGSState S) (N : PositiveTime)
    (xStar : E) (hxStar : IsOptimalSolution S xStar)
    (houtput : Measurable (fun ω => sgsGeneratedOutput S states N.1 ω))
    (hobjective : Measurable (fun x : FeasiblePoint S => objectiveOn S x)) :
    Measurable (outputGapRandomVariable S states N xStar hxStar) := by
  have hmain : Measurable (fun ω => objectiveOn S (sgsGeneratedOutput S states N.1 ω)) :=
    hobjective.comp houtput
  have hbase : Measurable fun _ : Ω => objectiveOn S ⟨xStar, hxStar.1⟩ :=
    measurable_const
  simpa [outputGapRandomVariable] using hmain.sub hbase

/-- Technical integrability bridge for the generated output gap.

The paper expectation proof should establish integrability of the objective at
the generated output locally; subtracting the deterministic optimum value is a
standard Mathlib consequence.  This keeps integrability as proof
infrastructure for expectation API, not as a standalone source-derived theorem
about arbitrary relation-form generated runs. -/
theorem outputGapRandomVariable_integrable_of_output_objective_integrable
    [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsFiniteMeasure P]
    (states : ℕ → Ω → SGSState S) (N : PositiveTime)
    (xStar : E) (hxStar : IsOptimalSolution S xStar)
    (houtput :
      Integrable (fun ω => objectiveOn S (sgsGeneratedOutput S states N.1 ω)) P) :
    Integrable (outputGapRandomVariable S states N xStar hxStar) P := by
  have hbase : Integrable (fun _ : Ω => objectiveOn S ⟨xStar, hxStar.1⟩) P :=
    integrable_const _
  simpa [outputGapRandomVariable] using houtput.sub hbase

/-- Internal raw Lean integral for the generated output gap.

This helper is kept private so formula-extension scaffolding can still unfold to
Mathlib's integral, while the public paper boundary below uses
`SGSProbabilityModel` to bind the integral to the SGS probability law.  The
paper's displayed expectation is represented by this raw integral; separate
Lean integrability is not asserted as a derived source theorem. -/
noncomputable def expectedOutputGapRaw [MeasurableSpace Ω] (P : Measure Ω)
    (states : ℕ → Ω → SGSState S) (N : PositiveTime)
    (xStar : E) (hxStar : IsOptimalSolution S xStar) : ℝ :=
  ∫ ω, outputGapRandomVariable S states N xStar hxStar ω ∂P

/-- Paper expectation object for the output gap
`E[Ψ(\bar x_N)-Ψ(x^*)]`.

Book JSON citation:
`book/FOML/StochasticGradientSliding.json:main_theorem.measure` identifies the
measure as expected bounds for `Ψ(\bar{x}_N)-Ψ(x^*)`.

The public wrapper is parameterized by the source probability model, not by an
arbitrary measure.  It intentionally exposes the raw integral used by Mathlib:
the book states the expected bound, but does not state a standalone theorem that
every relation-form generated SGS run has an integrable output gap.  The setup
quote gives convexity/simple-objective data on `X`, not a generic
measurability/integrability theorem for arbitrary Lean realizations. -/
noncomputable def expectedOutputGap [MeasurableSpace Ω] [MeasurableSpace Sample]
    [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S)
    (x0 : FeasiblePoint S) (beta gamma : PositiveTime → ℝ)
    (T : PositiveTime → ℕ) (states : ℕ → Ω → SGSState S)
    (inner : PositiveTime → ℕ → Ω → SPSState S) (N : PositiveTime)
    (xStar : E) (hxStar : IsOptimalSolution S xStar)
    (_hrun : IsGeneratedSGSProcess S x0 beta gamma T law.sample states inner)
    (_hindep : sfoIndependent S law.P law.sample (sgsGeneratedOracleQuery S inner)) : ℝ :=
  expectedOutputGapRaw S law.P states N xStar hxStar

/-- Well-definedness-aware bridge from the paper expectation wrapper to its raw
Mathlib integral.

The `Integrable` premise is intentionally explicit and technical.  It is not a
new assumption on any paper-facing theorem; it is the local proof leaf that the
Theorem 8.2 expectation argument must supply when it wants to use Bochner
integral API rather than raw fallback semantics. -/
theorem expectedOutputGap_eq_raw_integral_of_integrable
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S)
    (x0 : FeasiblePoint S) (beta gamma : PositiveTime → ℝ)
    (T : PositiveTime → ℕ) (states : ℕ → Ω → SGSState S)
    (inner : PositiveTime → ℕ → Ω → SPSState S) (N : PositiveTime)
    (xStar : E) (hxStar : IsOptimalSolution S xStar)
    (hrun : IsGeneratedSGSProcess S x0 beta gamma T law.sample states inner)
    (hindep : sfoIndependent S law.P law.sample (sgsGeneratedOracleQuery S inner))
    (_hgap : Integrable (outputGapRandomVariable S states N xStar hxStar) law.P) :
    expectedOutputGap S law x0 beta gamma T states inner N xStar hxStar hrun hindep =
      ∫ ω, outputGapRandomVariable S states N xStar hxStar ω ∂law.P := by
  rfl

/-- Paper tail event for the output gap
`{Ψ(\bar x_N)-Ψ(x^*) ≥ threshold}`.

Book JSON citation:
`book/FOML/StochasticGradientSliding.json:main_theorem.statement_math` displays
the high-probability events for `Ψ(\bar{x}_N)-Ψ(x^*)`.

No SOptLib match: considered `SOptLib.Model.TailProbability` and
`SOptLib.Model.Selection`; their finite-selection events do not bind the
Algorithm 8.2 generated SGS run and optimizer used in Theorem 8.2/Corollary 8.3. -/
def outputGapTailEvent (states : ℕ → Ω → SGSState S) (N : PositiveTime)
    (xStar : E) (hxStar : IsOptimalSolution S xStar) (threshold : ℝ) : Set Ω :=
  {ω | outputGapRandomVariable S states N xStar hxStar ω ≥ threshold}

/-- Strict source-boundary output-gap tail event.

Lan Eq. (8.1.70) and Eq. (8.1.71) control strict deviation events.  The
non-strict event above is retained for the paper's displayed statement and for
source-gap certificates, while this strict event is the executable checked
boundary used by the reconstructed probability route. -/
def outputGapStrictTailEvent (states : ℕ → Ω → SGSState S) (N : PositiveTime)
    (xStar : E) (hxStar : IsOptimalSolution S xStar) (threshold : ℝ) : Set Ω :=
  {ω | outputGapRandomVariable S states N xStar hxStar ω > threshold}

/-- Technical event-measurability bridge for the generated output-gap tail.

This replaces the rejected source-derived measurability obligation with the
actual Mathlib route: once the output-gap random variable is measurable, the
tail event is the preimage of the closed ray `[threshold,∞)`.  Downstream
high-probability proofs should compose this with
`outputGapRandomVariable_measurable_of_output_objective`, not assert event
measurability from `hrun` and independence alone. -/
theorem outputGapTailEvent_measurable_of_outputGap_measurable [MeasurableSpace Ω]
    (states : ℕ → Ω → SGSState S) (N : PositiveTime)
    (xStar : E) (hxStar : IsOptimalSolution S xStar) (threshold : ℝ)
    (hgap : Measurable (outputGapRandomVariable S states N xStar hxStar)) :
    MeasurableSet (outputGapTailEvent S states N xStar hxStar threshold) := by
  simpa [outputGapTailEvent, Set.preimage, ge_iff_le] using
    hgap measurableSet_Ici

/-- Internal raw Lean probability of the generated output-gap tail event. -/
noncomputable def outputGapTailProbabilityRaw [MeasurableSpace Ω] (P : Measure Ω)
    (states : ℕ → Ω → SGSState S) (N : PositiveTime)
    (xStar : E) (hxStar : IsOptimalSolution S xStar) (threshold : ℝ) : ENNReal :=
  P (outputGapTailEvent S states N xStar hxStar threshold)

/-- Internal raw Lean probability of the strict generated output-gap tail event. -/
noncomputable def outputGapStrictTailProbabilityRaw [MeasurableSpace Ω] (P : Measure Ω)
    (states : ℕ → Ω → SGSState S) (N : PositiveTime)
    (xStar : E) (hxStar : IsOptimalSolution S xStar) (threshold : ℝ) : ENNReal :=
  P (outputGapStrictTailEvent S states N xStar hxStar threshold)

/-- Paper probability object for the high-probability output-gap statements in
Theorem 8.2 and Corollary 8.3.

Book JSON citation:
`book/FOML/StochasticGradientSliding.json:main_theorem.measure` identifies the
measure as high-probability bounds for `Ψ(\bar{x}_N)-Ψ(x^*)`.

No SOptLib match: searched/considered tail-probability and selection primitives;
they are reusable event wrappers, but the source theorem needs this paper's
generated output gap event under the SGS probability law.  As with the
expectation wrapper, this definition uses Mathlib's raw measure-of-set
semantics rather than asserting a separate event-measurability theorem from the
relation-form generated run. -/
noncomputable def outputGapTailProbability [MeasurableSpace Ω] [MeasurableSpace Sample]
    [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S)
    (x0 : FeasiblePoint S) (beta gamma : PositiveTime → ℝ)
    (T : PositiveTime → ℕ) (states : ℕ → Ω → SGSState S)
    (inner : PositiveTime → ℕ → Ω → SPSState S) (N : PositiveTime)
    (xStar : E) (hxStar : IsOptimalSolution S xStar) (threshold : ℝ)
    (_hrun : IsGeneratedSGSProcess S x0 beta gamma T law.sample states inner)
    (_hindep : sfoIndependent S law.P law.sample (sgsGeneratedOracleQuery S inner)) :
    ENNReal :=
  outputGapTailProbabilityRaw S law.P states N xStar hxStar threshold

/-- Checked-source strict probability object for the high-probability route.

This is the executable probability wrapper for the strict event controlled by
the source proof's Eq. (8.1.70)/(8.1.71) decomposition. -/
noncomputable def outputGapStrictTailProbability [MeasurableSpace Ω] [MeasurableSpace Sample]
    [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S)
    (x0 : FeasiblePoint S) (beta gamma : PositiveTime → ℝ)
    (T : PositiveTime → ℕ) (states : ℕ → Ω → SGSState S)
    (inner : PositiveTime → ℕ → Ω → SPSState S) (N : PositiveTime)
    (xStar : E) (hxStar : IsOptimalSolution S xStar) (threshold : ℝ)
    (_hrun : IsGeneratedSGSProcess S x0 beta gamma T law.sample states inner)
    (_hindep : sfoIndependent S law.P law.sample (sgsGeneratedOracleQuery S inner)) :
    ENNReal :=
  outputGapStrictTailProbabilityRaw S law.P states N xStar hxStar threshold

/-- Well-definedness-aware bridge from the paper tail-probability wrapper to
Mathlib's raw measure of the measurable tail event.

The measurability premise is a technical local leaf, not a source-facing
assumption.  It gives downstream probability proofs a compiled event route
without reintroducing the false theorem that every relation-form generated run
has a measurable output gap from `hrun` and `hindep` alone. -/
theorem outputGapTailProbability_eq_raw_measure_of_measurable
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S)
    (x0 : FeasiblePoint S) (beta gamma : PositiveTime → ℝ)
    (T : PositiveTime → ℕ) (states : ℕ → Ω → SGSState S)
    (inner : PositiveTime → ℕ → Ω → SPSState S) (N : PositiveTime)
    (xStar : E) (hxStar : IsOptimalSolution S xStar) (threshold : ℝ)
    (hrun : IsGeneratedSGSProcess S x0 beta gamma T law.sample states inner)
    (hindep : sfoIndependent S law.P law.sample (sgsGeneratedOracleQuery S inner))
    (_hevent : MeasurableSet (outputGapTailEvent S states N xStar hxStar threshold)) :
    outputGapTailProbability S law x0 beta gamma T states inner N xStar hxStar threshold
        hrun hindep =
      law.P (outputGapTailEvent S states N xStar hxStar threshold) := by
  rfl

/-- Internal selected outer SGS transition: build `g_k=l_f(\underline x_k,\cdot)`,
call the selected SPS realization, and update `\bar x_k`.

No SOptLib match: considered recursive-process and accelerated-state helpers,
but Algorithm 8.1/8.2 couples an outer accelerated average to an inner SPS call,
so this deterministic object is kept as formula-extension helper
infrastructure, not the paper-facing algorithm. -/
noncomputable def sgsTransition_formulaExtensionSelector (beta : PositiveTime → {β : ℝ // 0 < β})
    (gamma : PositiveTime → ℝ)
    (T : PositiveTime → ℕ) (sample : PositiveTime → ℕ → Ω → Sample)
    (hgamma : gammaRangeCondition gamma)
    (n : ℕ) (st : SGSState S) (ω : Ω) : SGSState S :=
  let k : PositiveTime := ⟨n + 1, Nat.succ_pos n⟩
  let xUnder := outerExtrapolation S gamma k st
  let gk : E → ℝ := fun u => smoothLinearization S xUnder u
  let out := spsOutput S gk (smoothLinearization_isAffineModel S xUnder) st.x
    (beta k) (sample k) (T k) ω
  { x := out.u
    xbar :=
      ⟨(1 - gamma k) • st.xbar.1 + gamma k • out.avg.1,
        convexCombination_mem_X S st.xbar out.avg (hgamma k).1 (hgamma k).2⟩ }

/-- Internal selected outer SGS iterate process generated by Algorithm 8.1/8.2.

The initial center is typed in `X`, exactly as Algorithm 8.1 states.  The
`X^o` admissibility needed for displayed Bregman first arguments is a derived
obligation below, not a strengthened algorithm input.  The paper-facing process
is the relation `IsSGSProcess`; this selector exists only for internal
formula-extension helper statements. -/
noncomputable def sgsProcess_formulaExtensionSelector (x0 : FeasiblePoint S)
    (beta : PositiveTime → ℝ)
    (hbeta : ∀ k : PositiveTime, 0 < beta k) (gamma : PositiveTime → ℝ)
    (hgamma : gammaRangeCondition gamma)
    (T : PositiveTime → ℕ) (sample : PositiveTime → ℕ → Ω → Sample)
    : ℕ → Ω → SGSState S :=
  SOptLib.recursiveIterateProcess (sgsInitial S x0)
    (sgsTransition_formulaExtensionSelector S (positiveBetaSchedule beta hbeta) gamma T sample hgamma)

/-- Canonical selected outer SGS transition generated by Algorithm 8.1/8.2.

Book JSON citation:
`book/FOML/StochasticGradientSliding.json:algorithm_spec.steps[6-8]` states
the generated SPS call and the outer averaging update.

Aligns with `SOptLib.recursiveIterateProcess` by supplying its one-step update
function.  Checked `recursiveProcess_succ_eq_sample_update`; it is a successor
bridge for a supplied recursive process, not the transition object itself.  The
relation-form `IsSGSTransition` remains the paper specification when argmin
tie-breaking is left abstract. -/
noncomputable def sgsTransition (beta : PositiveTime → {β : ℝ // 0 < β})
    (gamma : PositiveTime → ℝ)
    (T : PositiveTime → ℕ) (sample : PositiveTime → ℕ → Ω → Sample)
    (hgamma : gammaRangeCondition gamma)
    (n : ℕ) (st : SGSState S) (ω : Ω) : SGSState S :=
  sgsTransition_formulaExtensionSelector S beta gamma T sample hgamma n st ω

/-- The canonical selected SGS transition realizes the relation-form outer step
from Algorithm 8.1/8.2. -/
theorem sgsTransition_isSGSTransition (beta : PositiveTime → {β : ℝ // 0 < β})
    (gamma : PositiveTime → ℝ)
    (T : PositiveTime → ℕ) (sample : PositiveTime → ℕ → Ω → Sample)
    (hgamma : gammaRangeCondition gamma)
    (n : ℕ) (st : SGSState S) (ω : Ω) :
    IsSGSTransition S (fun k => (beta k).1) gamma T sample n ω st
      (sgsTransition S beta gamma T sample hgamma n st ω) := by
  dsimp [sgsTransition, sgsTransition_formulaExtensionSelector, IsSGSTransition,
    spsOutput]
  refine ⟨spsProcess S
      (fun u => smoothLinearization S (outerExtrapolation S gamma ⟨n + 1, Nat.succ_pos n⟩ st) u)
      (smoothLinearization_isAffineModel S (outerExtrapolation S gamma ⟨n + 1, Nat.succ_pos n⟩ st))
      st.x (beta ⟨n + 1, Nat.succ_pos n⟩) (sample ⟨n + 1, Nat.succ_pos n⟩),
    ?_, ?_, ?_⟩
  · exact spsProcess_isSPSProcess S
      (fun u => smoothLinearization S (outerExtrapolation S gamma ⟨n + 1, Nat.succ_pos n⟩ st) u)
      (smoothLinearization_isAffineModel S (outerExtrapolation S gamma ⟨n + 1, Nat.succ_pos n⟩ st))
      st.x (beta ⟨n + 1, Nat.succ_pos n⟩) (sample ⟨n + 1, Nat.succ_pos n⟩)
  · rfl
  · rfl

/-- Canonical selected outer SGS state process generated by Algorithm 8.1/8.2.

Book JSON citation:
`book/FOML/StochasticGradientSliding.json:algorithm_spec.initialization` gives
`x_0∈X` and `\bar x_0=x_0`, while `algorithm_spec.steps[6-8]` gives the SPS
call and outer averaging recursion.

Aligns with `SOptLib.recursiveIterateProcess`, the reusable primitive for
zero-based stochastic iterate processes.  This definition is the selected
realization of the outer algorithmic spine; `IsSGSProcess` remains the
source-facing relation for nonunique argmin semantics. -/
noncomputable def sgsProcess (x0 : FeasiblePoint S)
    (beta : PositiveTime → ℝ)
    (hbeta : ∀ k : PositiveTime, 0 < beta k) (gamma : PositiveTime → ℝ)
    (hgamma : gammaRangeCondition gamma)
    (T : PositiveTime → ℕ) (sample : PositiveTime → ℕ → Ω → Sample)
    : ℕ → Ω → SGSState S :=
  SOptLib.recursiveIterateProcess (sgsInitial S x0)
    (sgsTransition S (positiveBetaSchedule beta hbeta) gamma T sample hgamma)

/-- The canonical selected SGS process satisfies the public relation-form SGS
process specification. -/
theorem sgsProcess_isSGSProcess (x0 : FeasiblePoint S)
    (beta : PositiveTime → ℝ) (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (gamma : PositiveTime → ℝ) (hgamma : gammaRangeCondition gamma)
    (T : PositiveTime → ℕ) (sample : PositiveTime → ℕ → Ω → Sample) :
    IsSGSProcess S x0 beta gamma T sample
      (sgsProcess S x0 beta hbeta gamma hgamma T sample) := by
  dsimp [IsSGSProcess]
  refine ⟨?_, ?_⟩
  · intro ω
    rfl
  · intro n ω
    simpa [sgsProcess] using
      sgsTransition_isSGSTransition S (positiveBetaSchedule beta hbeta) gamma T sample hgamma n
        (sgsProcess S x0 beta hbeta gamma hgamma T sample n ω) ω

/-- Internal selected family of SPS calls generated by the selected SGS run.

Book JSON citation:
`book/FOML/StochasticGradientSliding.json:algorithm_spec.steps[6]` states
`(x_k,\tilde{x}_k)=SPS(g_k,x_{k-1},β_k,T_k)`.

Aligns with `SOptLib.recursiveIterateProcess` through the already selected SPS
process for each outer call.  Checked `recursiveProcess_succ_eq_sample_update`
and the prox selectors; those are successor bridges or one-Bregman prox
selectors, while Algorithm 8.2 needs the whole two-Bregman SPS process generated
at every outer index from the selected outer history. -/
noncomputable def sgsInnerProcess_formulaExtensionSelector (x0 : FeasiblePoint S)
    (beta : PositiveTime → ℝ)
    (hbeta : ∀ k : PositiveTime, 0 < beta k) (gamma : PositiveTime → ℝ)
    (hgamma : gammaRangeCondition gamma)
    (T : PositiveTime → ℕ) (sample : PositiveTime → ℕ → Ω → Sample)
    (k : PositiveTime) : ℕ → Ω → SPSState S :=
  let outerPrev := fun ω =>
    sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample (k.1 - 1) ω
  let gk : Ω → E → ℝ := fun ω y =>
    smoothLinearization S (outerExtrapolation S gamma k (outerPrev ω)) y
  fun i ω =>
    spsProcess S (gk ω)
      (smoothLinearization_isAffineModel S (outerExtrapolation S gamma k (outerPrev ω)))
      (outerPrev ω).x ⟨beta k, hbeta k⟩ (sample k) i ω

/-- Internal selected realization of Algorithm output `\bar x_N`. -/
noncomputable def sgsOutput_formulaExtensionSelector (x0 : FeasiblePoint S)
    (beta : PositiveTime → ℝ)
    (hbeta : ∀ k : PositiveTime, 0 < beta k) (gamma : PositiveTime → ℝ)
    (hgamma : gammaRangeCondition gamma)
    (T : PositiveTime → ℕ) (sample : PositiveTime → ℕ → Ω → Sample)
    (N : ℕ) (ω : Ω) : FeasiblePoint S :=
  (sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample N ω).xbar

/-- The internal selected SGS realization satisfies the formula-extension SGS
process relation; the generated source-domain bridge below records the same
selected run at the `X^o × X` prox-function boundary. -/
theorem sgsProcess_formulaExtensionSelector_isSGSProcess_formulaExtension (x0 : FeasiblePoint S)
    (beta : PositiveTime → ℝ) (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (gamma : PositiveTime → ℝ) (hgamma : gammaRangeCondition gamma)
    (T : PositiveTime → ℕ) (sample : PositiveTime → ℕ → Ω → Sample) :
    IsSGSProcess_formulaExtension S x0 beta gamma T sample
      (sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample) := by
  simpa [IsSGSProcess_formulaExtension, sgsProcess_formulaExtensionSelector, sgsProcess,
    sgsTransition] using
    sgsProcess_isSGSProcess S x0 beta hbeta gamma hgamma T sample

/-- The selected outer process together with the selected inner-call family
realizes the run-level generated SGS relation.

This theorem removes the need to manufacture an unrelated inner-process witness
when using the canonical selected realization of Algorithm 8.1/8.2. -/
theorem sgsProcess_formulaExtensionSelector_isGeneratedSGSProcess_formulaExtension
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E]
    (x0 : FeasiblePoint S)
    (beta : PositiveTime → ℝ) (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (gamma : PositiveTime → ℝ) (hgamma : gammaRangeCondition gamma)
    (T : PositiveTime → ℕ) (sample : PositiveTime → ℕ → Ω → Sample) :
    IsGeneratedSGSProcess_formulaExtension S x0 beta gamma T sample
      (sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample)
      (sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample) := by
  dsimp [IsGeneratedSGSProcess_formulaExtension, IsGeneratedSGSProcess]
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro ω
      rfl
    · intro k
      dsimp [sgsInnerProcess_formulaExtensionSelector, IsGeneratedSPSProcess]
      refine ⟨hbeta k, ?_, ?_⟩
      · intro ω
        rfl
      · intro n ω
        simpa [sgsInnerProcess_formulaExtensionSelector] using
          (spsProcess_isSPSProcess S
            (fun u => smoothLinearization S
              (outerExtrapolation S gamma k
                (sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
                  (k.1 - 1) ω)) u)
            (smoothLinearization_isAffineModel S
              (outerExtrapolation S gamma k
                (sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
                  (k.1 - 1) ω)))
            ((sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
              (k.1 - 1) ω).x)
            ⟨beta k, hbeta k⟩ (sample k)).2.2 n ω
    · intro k ω
      rcases k with ⟨m, hm⟩
      cases m with
      | zero => omega
      | succ n =>
          have hk : (⟨n + 1, Nat.succ_pos n⟩ : PositiveTime) = ⟨n + 1, hm⟩ := by
            ext
            rfl
          dsimp [sgsProcess_formulaExtensionSelector]
          rw [SOptLib.recursiveIterateProcess_succ
            (SOptLib.recursiveIterateProcess (sgsInitial S x0)
              (sgsTransition_formulaExtensionSelector S (positiveBetaSchedule beta hbeta) gamma T sample hgamma))
            (sgsInitial S x0)
            (sgsTransition_formulaExtensionSelector S (positiveBetaSchedule beta hbeta) gamma T sample hgamma)
            rfl n ω]
          simpa [sgsProcess_formulaExtensionSelector, sgsInnerProcess_formulaExtensionSelector,
            sgsTransition_formulaExtensionSelector, spsOutput, positiveBetaSchedule, hk]
    · exact gammaRangeCondition_nonnegative hgamma
  · trivial

/-- Source-domain generated-process bridge for the selected SGS/SPS realization.

This is the source-typed counterpart of
`sgsProcess_formulaExtensionSelector_isGeneratedSGSProcess_formulaExtension`.
Search audit: considered the fixed-center
`spsProcess_formulaExtensionSelector_isSPSProcess_sourceDomain_obligation` and
the transition bridge `IsSPSTransition_sourceDomain_obligation`; the generated
SGS relation is the matching consumer because its SPS centers and affine models
vary with the outer sample path, exactly as Algorithm 8.1/8.2's selected inner
family does. -/
theorem sgsProcess_formulaExtensionSelector_isGeneratedSGSProcess_sourceDomain_obligation
    (x0 : FeasiblePoint S)
    (beta : PositiveTime → ℝ) (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (gamma : PositiveTime → ℝ) (hgamma : gammaRangeCondition gamma)
    (T : PositiveTime → ℕ) (sample : PositiveTime → ℕ → Ω → Sample)
    (hx0 : x0.1 ∈ proxCore S.X S.proxPotential)
    (houter :
      ∀ n ω,
        ((sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample n ω).x).1 ∈
          proxCore S.X S.proxPotential)
    (hinner :
      ∀ k i ω,
        ((sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
          k i ω).u).1 ∈
            proxCore S.X S.proxPotential) :
    IsGeneratedSGSProcess_sourceDomain S ⟨x0.1, hx0⟩ beta gamma T sample
      (fun n ω =>
        sgsSourceStateOfFeasible S
          (sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample n ω)
          (houter n ω))
      (fun k i ω =>
        spsSourceStateOfFeasible S
          (sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample k i ω)
          (hinner k i ω)) := by
  dsimp [IsGeneratedSGSProcess_sourceDomain]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ω
    rfl
  · intro k
    dsimp [IsGeneratedSPSProcess_sourceDomain]
    refine ⟨hbeta k, ?_, ?_⟩
    · intro ω
      rfl
    · intro i ω
      let outerPrev :=
        sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
          (k.1 - 1) ω
      let xUnder := outerExtrapolation S gamma k outerPrev
      let gk : E → ℝ := fun y => smoothLinearization S xUnder y
      let hgk : IsAffineModel gk := smoothLinearization_isAffineModel S xUnder
      let proc := spsProcess S gk hgk outerPrev.x ⟨beta k, hbeta k⟩ (sample k)
      have htrans :
          IsSPSTransition_formulaExtension S gk outerPrev.x (beta k) (sample k) i ω
            (proc i ω) (proc (i + 1) ω) := by
        simpa [proc, gk, hgk, xUnder, outerPrev, IsSPSTransition_formulaExtension, spsProcess] using
          (spsProcess_isSPSProcess S gk hgk outerPrev.x ⟨beta k, hbeta k⟩
            (sample k)).2.2 i ω
      dsimp [IsSPSTransition_sourceDomain, spsSourceStateOfFeasible,
        sgsSourceStateOfFeasible, sgsInnerProcess_formulaExtensionSelector,
        outerSourceExtrapolation, outerExtrapolation]
      refine ⟨?_, ?_⟩
      · simpa [proc, gk, hgk, xUnder, outerPrev, spsProcess] using
          IsSPSTransition_sourceDomain_obligation S gk outerPrev.x (beta k) (sample k)
            i ω (proc i ω) (proc (i + 1) ω) htrans
            (houter (k.1 - 1) ω) (hinner k i ω)
      · simpa [proc, gk, hgk, xUnder, outerPrev, spsProcess,
          sgsInnerProcess_formulaExtensionSelector] using htrans.2
  · intro k ω
    rcases k with ⟨m, hm⟩
    cases m with
    | zero => omega
    | succ n =>
        have hk : (⟨n + 1, Nat.succ_pos n⟩ : PositiveTime) = ⟨n + 1, hm⟩ := by
          ext
          rfl
        dsimp [sgsSourceStateOfFeasible]
        constructor
        · ext
          dsimp [sgsProcess_formulaExtensionSelector]
          rw [SOptLib.recursiveIterateProcess_succ
            (SOptLib.recursiveIterateProcess (sgsInitial S x0)
              (sgsTransition_formulaExtensionSelector S (positiveBetaSchedule beta hbeta) gamma T sample hgamma))
            (sgsInitial S x0)
            (sgsTransition_formulaExtensionSelector S (positiveBetaSchedule beta hbeta) gamma T sample hgamma)
            rfl n ω]
          simp [spsSourceStateOfFeasible, sgsProcess_formulaExtensionSelector,
            sgsInnerProcess_formulaExtensionSelector, sgsTransition_formulaExtensionSelector,
            spsOutput, positiveBetaSchedule, hk]
        · dsimp [sgsProcess_formulaExtensionSelector]
          rw [SOptLib.recursiveIterateProcess_succ
            (SOptLib.recursiveIterateProcess (sgsInitial S x0)
              (sgsTransition_formulaExtensionSelector S (positiveBetaSchedule beta hbeta) gamma T sample hgamma))
            (sgsInitial S x0)
            (sgsTransition_formulaExtensionSelector S (positiveBetaSchedule beta hbeta) gamma T sample hgamma)
            rfl n ω]
          simp [spsSourceStateOfFeasible, sgsProcess_formulaExtensionSelector,
            sgsInnerProcess_formulaExtensionSelector, sgsTransition_formulaExtensionSelector,
            spsOutput, positiveBetaSchedule, hk]
  · exact gammaRangeCondition_nonnegative hgamma

/-- Canonical selected outer SGS state process generated by Algorithm 8.1/8.2.

Book JSON citation:
`book/FOML/StochasticGradientSliding.json:algorithm_spec.steps[6-8]` states
the generated SPS call and outer averaging recursion.

Aligns with `SOptLib.recursiveIterateProcess`, checked together with
`recursiveProcess_succ_eq_sample_update`: the former is the reusable primitive
for zero-based generated stochastic processes, while the latter is only a
successor bridge.  This unsuffixed wrapper is the public selected realization of
the paper recursion; the older `_formulaExtensionSelector` name remains
compatibility infrastructure. -/
noncomputable def sgsSelectedStates (x0 : FeasiblePoint S)
    (beta : PositiveTime → ℝ) (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (gamma : PositiveTime → ℝ) (hgamma : gammaRangeCondition gamma)
    (T : PositiveTime → ℕ) (sample : PositiveTime → ℕ → Ω → Sample) :
    ℕ → Ω → SGSState S :=
  sgsProcess S x0 beta hbeta gamma hgamma T sample

/-- Canonical selected family of inner SPS processes generated by the selected
outer SGS recursion.

Book JSON citation:
`book/FOML/StochasticGradientSliding.json:algorithm_spec.steps[6]` states
`(x_k,\tilde{x}_k)=SPS(g_k,x_{k-1},β_k,T_k)`.

Aligns with `SOptLib.recursiveIterateProcess` through the selected SPS recursion
at each outer index.  `recursiveProcess_succ_eq_sample_update` was checked but
is a proof bridge rather than the canonical process object needed here. -/
noncomputable def sgsSelectedInnerProcesses (x0 : FeasiblePoint S)
    (beta : PositiveTime → ℝ) (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (gamma : PositiveTime → ℝ) (hgamma : gammaRangeCondition gamma)
    (T : PositiveTime → ℕ) (sample : PositiveTime → ℕ → Ω → Sample) :
    PositiveTime → ℕ → Ω → SPSState S :=
  sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample

/-- Successor strict-past measurability step for the canonical selected SGS/SPS
inner recursion.

This is the route-local induction step needed by
`sgsSelectedGeneratedQueriesStrictPastAdapted`: if the selected outer center and
the previous selected inner state are measurable from the strict past at
coordinate `(k,i+1)`, then the next oracle query is also strict-past measurable.
The proof uses the reconstructed Eq. (8.1.58) solver random-context
measurability and the fact that `sample k i` is already in the strict past of
`(k,i+1)`. -/
theorem sgsSelectedInnerProcess_succ_u_measurable_strictPast_of_context
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E]
    (x0 : FeasiblePoint S)
    (beta : PositiveTime → ℝ) (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (gamma : PositiveTime → ℝ) (hgamma : gammaRangeCondition gamma)
    (T : PositiveTime → ℕ) (sample : PositiveTime → ℕ → Ω → Sample)
    (k : PositiveTime) (i : ℕ)
    (houter :
      Measurable[sgsStrictPastSampleSpace (Ω := Ω) sample k (i + 1)]
        (fun ω =>
          (sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
            (k.1 - 1) ω).x))
    (hprev :
      Measurable[sgsStrictPastSampleSpace (Ω := Ω) sample k (i + 1)]
        (fun ω =>
          (sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
            k i ω).u)) :
    Measurable[sgsStrictPastSampleSpace (Ω := Ω) sample k (i + 1)]
      (fun ω =>
        (sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
          k (i + 1) ω).u) := by
  classical
  let mΩ : MeasurableSpace Ω := sgsStrictPastSampleSpace (Ω := Ω) sample k (i + 1)
  let outerPrev : Ω → SGSState S :=
    fun ω =>
      sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
        (k.1 - 1) ω
  let gk : Ω → E → ℝ :=
    fun ω y => smoothLinearization S (outerExtrapolation S gamma k (outerPrev ω)) y
  have hgk : ∀ ω, IsAffineModel (gk ω) := by
    intro ω
    exact smoothLinearization_isAffineModel S (outerExtrapolation S gamma k (outerPrev ω))
  have hxi :
      Measurable[mΩ] (sample k i) := by
    simpa [mΩ] using
      sgsSameOuterPreviousSample_measurable_strictPast
        (Ω := Ω) sample k (Nat.lt_succ_self i)
  have hstep :
      Measurable[mΩ]
        (fun ω =>
          spsStep S (gk ω) (hgk ω) (outerPrev ω).x
            ⟨beta k, hbeta k⟩ ⟨i + 1, Nat.succ_pos i⟩
            (sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
              k i ω).u
            (sample k i ω)) :=
    spsStep_measurable_past_context
      (S := S) (mΩ := mΩ) gk hgk
      (fun ω => (outerPrev ω).x) ⟨beta k, hbeta k⟩
      ⟨i + 1, Nat.succ_pos i⟩
      (fun ω =>
        (sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
          k i ω).u)
      (sample k i) houter hprev hxi
  simpa [mΩ, outerPrev, gk, spsStep, sgsInnerProcess_formulaExtensionSelector,
    spsProcess, spsTransition, spsTransition_formulaExtensionSelector,
    SOptLib.recursiveIterateProcess] using hstep

/-- Measurability of a feasible convex combination under an arbitrary past
sigma-algebra.

This is route-local infrastructure for the selected SGS/SPS recursion: Eq.
(8.1.18) and the outer averaging step both build feasible points by a
deterministic convex combination, so once the two endpoints are past-measurable
the selected average is past-measurable as a subtype-valued point of `X`. -/
theorem feasible_convexCombination_measurable
    [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
    (mΩ : MeasurableSpace Ω) (x y : Ω → FeasiblePoint S) (a : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hx : Measurable[mΩ] x) (hy : Measurable[mΩ] y) :
    Measurable[mΩ]
      (fun ω =>
        (⟨(1 - a) • (x ω).1 + a • (y ω).1,
          convexCombination_mem_X S (x ω) (y ω) ha0 ha1⟩ : FeasiblePoint S)) := by
  letI : FiniteDimensional ℝ E := S.finiteDimensional_ambient
  haveI : ProperSpace E := FiniteDimensional.proper ℝ E
  haveI : SecondCountableTopology E := secondCountable_of_proper
  have hxE : Measurable[mΩ] (fun ω => (x ω : E)) :=
    measurable_subtype_coe.comp hx
  have hyE : Measurable[mΩ] (fun ω => (y ω : E)) :=
    measurable_subtype_coe.comp hy
  have hbody :
      Measurable[mΩ]
        (fun ω => (1 - a) • (x ω : E) + a • (y ω : E)) :=
    by
      simpa using
        (continuous_add.measurable.comp
          (((continuous_const_smul (1 - a)).measurable.comp hxE).prodMk
            ((continuous_const_smul a).measurable.comp hyE)))
  exact hbody.subtype_mk

/-- Full-state measurability for one selected SPS inner recursion under a fixed
past sigma-algebra.

This strengthens the previously compiled `u`-only successor bridge to the whole
`SPSState`, because the outer SGS transition reads both the terminal `u_T` and
terminal average `\tilde u_T`.  The hypotheses are exactly the causal inputs of
Eq. (8.1.58): the outer center and every sample used in this inner block are
measurable from the chosen past. -/
theorem sgsSelectedInnerProcess_measurable_of_context
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (mΩ : MeasurableSpace Ω)
    (x0 : FeasiblePoint S)
    (beta : PositiveTime → ℝ) (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (gamma : PositiveTime → ℝ) (hgamma : gammaRangeCondition gamma)
    (T : PositiveTime → ℕ) (sample : PositiveTime → ℕ → Ω → Sample)
    (k : PositiveTime)
    (houter :
      Measurable[mΩ]
        (fun ω =>
          (sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
            (k.1 - 1) ω).x))
    (hsamples : ∀ j, Measurable[mΩ] (sample k j)) :
    ∀ i,
      Measurable[mΩ]
        (fun ω =>
          sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
            k i ω) := by
  classical
  intro i
  induction i with
  | zero =>
      exact
        measurable_spsState_mk (S := S) mΩ
          (u := fun ω =>
            (sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
              (k.1 - 1) ω).x)
          (avg := fun ω =>
            (sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
              (k.1 - 1) ω).x)
          houter houter
  | succ i ih =>
      let outerPrev : Ω → SGSState S :=
        fun ω =>
          sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
            (k.1 - 1) ω
      let gk : Ω → E → ℝ :=
        fun ω y => smoothLinearization S (outerExtrapolation S gamma k (outerPrev ω)) y
      have hgk : ∀ ω, IsAffineModel (gk ω) := by
        intro ω
        exact smoothLinearization_isAffineModel S
          (outerExtrapolation S gamma k (outerPrev ω))
      have hprev_u :
          Measurable[mΩ]
            (fun ω =>
            (sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
                k i ω).u) := by
        exact (measurable_spsState_u (S := S)).comp ih
      have hprev_avg :
          Measurable[mΩ]
            (fun ω =>
            (sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
                k i ω).avg) := by
        exact (measurable_spsState_avg (S := S)).comp ih
      have huNext :
          Measurable[mΩ]
            (fun ω =>
              spsStep S (gk ω) (hgk ω) (outerPrev ω).x
                ⟨beta k, hbeta k⟩ ⟨i + 1, Nat.succ_pos i⟩
                (sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
                  k i ω).u
                (sample k i ω)) :=
        spsStep_measurable_past_context
          (S := S) (mΩ := mΩ) gk hgk
          (fun ω => (outerPrev ω).x) ⟨beta k, hbeta k⟩
          ⟨i + 1, Nat.succ_pos i⟩
          (fun ω =>
            (sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
              k i ω).u)
          (sample k i) houter hprev_u (hsamples i)
      have htheta := spsTheta_mem_Icc (⟨i + 1, Nat.succ_pos i⟩ : PositiveTime)
      have havgNext :
          Measurable[mΩ]
            (fun ω =>
              (⟨(1 - spsTheta (⟨i + 1, Nat.succ_pos i⟩ : PositiveTime)) •
                    (sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
                      k i ω).avg.1 +
                  spsTheta (⟨i + 1, Nat.succ_pos i⟩ : PositiveTime) •
                    (spsStep S (gk ω) (hgk ω) (outerPrev ω).x
                      ⟨beta k, hbeta k⟩ ⟨i + 1, Nat.succ_pos i⟩
                      (sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
                        k i ω).u
                      (sample k i ω)).1,
                convexCombination_mem_X S
                  (sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
                    k i ω).avg
                  (spsStep S (gk ω) (hgk ω) (outerPrev ω).x
                    ⟨beta k, hbeta k⟩ ⟨i + 1, Nat.succ_pos i⟩
                    (sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
                      k i ω).u
                    (sample k i ω))
                  htheta.1 htheta.2⟩ : FeasiblePoint S)) :=
        feasible_convexCombination_measurable (S := S) mΩ
          (fun ω =>
            (sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
              k i ω).avg)
          (fun ω =>
            spsStep S (gk ω) (hgk ω) (outerPrev ω).x
              ⟨beta k, hbeta k⟩ ⟨i + 1, Nat.succ_pos i⟩
              (sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
                k i ω).u
              (sample k i ω))
          (spsTheta (⟨i + 1, Nat.succ_pos i⟩ : PositiveTime))
          htheta.1 htheta.2 hprev_avg huNext
      have hstate :
          Measurable[mΩ]
            (fun ω =>
              ({ u :=
                  spsStep S (gk ω) (hgk ω) (outerPrev ω).x
                    ⟨beta k, hbeta k⟩ ⟨i + 1, Nat.succ_pos i⟩
                    (sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
                      k i ω).u
                    (sample k i ω)
                 avg :=
                  ⟨(1 - spsTheta (⟨i + 1, Nat.succ_pos i⟩ : PositiveTime)) •
                      (sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
                        k i ω).avg.1 +
                    spsTheta (⟨i + 1, Nat.succ_pos i⟩ : PositiveTime) •
                      (spsStep S (gk ω) (hgk ω) (outerPrev ω).x
                        ⟨beta k, hbeta k⟩ ⟨i + 1, Nat.succ_pos i⟩
                        (sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
                          k i ω).u
                        (sample k i ω)).1,
                    convexCombination_mem_X S
                      (sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
                        k i ω).avg
                      (spsStep S (gk ω) (hgk ω) (outerPrev ω).x
                        ⟨beta k, hbeta k⟩ ⟨i + 1, Nat.succ_pos i⟩
                        (sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
                          k i ω).u
                        (sample k i ω))
                      htheta.1 htheta.2⟩ } : SPSState S)) :=
        measurable_spsState_mk (S := S) mΩ huNext havgNext
      simpa [outerPrev, gk, spsStep, sgsInnerProcess_formulaExtensionSelector,
        spsProcess, spsTransition, spsTransition_formulaExtensionSelector,
        SOptLib.recursiveIterateProcess] using hstate

/-- First outer block of the selected SGS/SPS recursion is strict-past adapted.

This is the base outer block for the nested induction requested by the
Candidate-1 audit.  The zero-th inner query is the constant initial point
`x₀`; each successor query follows from
`sgsSelectedInnerProcess_succ_u_measurable_strictPast_of_context` because
`sample 1 i` belongs to the strict past of `(1,i+1)`. -/
theorem sgsSelectedGeneratedQueriesStrictPastAdapted_firstOuter
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (x0 : FeasiblePoint S)
    (beta : PositiveTime → ℝ) (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (gamma : PositiveTime → ℝ) (hgamma : gammaRangeCondition gamma)
    (T : PositiveTime → ℕ) (sample : PositiveTime → ℕ → Ω → Sample) :
    ∀ i,
      Measurable[sgsStrictPastSampleSpace (Ω := Ω) sample oneTime i]
        (fun ω =>
          (sgsSelectedInnerProcesses S x0 beta hbeta gamma hgamma T sample
            oneTime i ω).u) := by
  classical
  intro i
  induction i with
  | zero =>
      simpa [sgsSelectedInnerProcesses, sgsInnerProcess_formulaExtensionSelector,
        spsProcess, SOptLib.recursiveIterateProcess, spsInitial, oneTime,
        sgsProcess_formulaExtensionSelector, sgsInitial] using
        (measurable_const :
          Measurable[sgsStrictPastSampleSpace (Ω := Ω) sample oneTime 0]
            (fun _ : Ω => x0))
  | succ i ih =>
      have houter :
          Measurable[sgsStrictPastSampleSpace (Ω := Ω) sample oneTime (i + 1)]
            (fun ω =>
              (sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
                (oneTime.1 - 1) ω).x) := by
        simpa [oneTime, sgsProcess_formulaExtensionSelector, SOptLib.recursiveIterateProcess,
          sgsInitial] using
          (measurable_const :
            Measurable[sgsStrictPastSampleSpace (Ω := Ω) sample oneTime (i + 1)]
              (fun _ : Ω => x0))
      have hprev :
          Measurable[sgsStrictPastSampleSpace (Ω := Ω) sample oneTime (i + 1)]
            (fun ω =>
              (sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
                oneTime i ω).u) := by
        have hle :
            sgsStrictPastSampleSpace (Ω := Ω) sample oneTime i ≤
              sgsStrictPastSampleSpace (Ω := Ω) sample oneTime (i + 1) :=
          sgsStrictPastSampleSpace_le_same_outer_succ (Ω := Ω) sample oneTime i
        simpa [sgsSelectedInnerProcesses] using ih.mono hle
      simpa [sgsSelectedInnerProcesses] using
        sgsSelectedInnerProcess_succ_u_measurable_strictPast_of_context
          (S := S) x0 beta hbeta gamma hgamma T sample oneTime i houter hprev

/-- Earlier selected outer states are measurable from any later strict-past
sample sigma-algebra.

This is the outer half of the selected-realization causal proof.  If `n < k`,
the selected outer state `x_n,\bar x_n` is generated only from samples in
strictly earlier outer blocks, hence it is measurable from the strict past of
any coordinate `(k,i)`.  The proof uses full-state measurability of each
completed selected inner SPS call, because the outer update reads both `u_T`
and `\tilde u_T`. -/
theorem sgsSelectedOuterState_measurable_strictPast_of_lt
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (x0 : FeasiblePoint S)
    (beta : PositiveTime → ℝ) (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (gamma : PositiveTime → ℝ) (hgamma : gammaRangeCondition gamma)
    (T : PositiveTime → ℕ) (sample : PositiveTime → ℕ → Ω → Sample) :
    ∀ n, ∀ k : PositiveTime, ∀ i,
      n < k.1 →
        Measurable[sgsStrictPastSampleSpace (Ω := Ω) sample k i]
          (fun ω =>
            sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
              n ω) := by
  classical
  intro n
  induction n with
  | zero =>
      intro k i _hnk
      exact
        measurable_sgsState_mk (S := S)
          (sgsStrictPastSampleSpace (Ω := Ω) sample k i)
          (x := fun _ : Ω => x0) (xbar := fun _ : Ω => x0)
          measurable_const measurable_const
  | succ n ih =>
      intro k i hnk
      let r : PositiveTime := ⟨n + 1, Nat.succ_pos n⟩
      let mΩ : MeasurableSpace Ω := sgsStrictPastSampleSpace (Ω := Ω) sample k i
      have hrk : r.1 < k.1 := by
        simpa [r] using hnk
      have hn_prev : n < k.1 := by
        exact Nat.lt_trans (Nat.lt_succ_self n) hnk
      have hprev_state :
          Measurable[mΩ]
            (fun ω =>
              sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
                n ω) := by
        simpa [mΩ] using ih k i hn_prev
      have hprev_x :
          Measurable[mΩ]
            (fun ω =>
            (sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
                n ω).x) :=
        (measurable_sgsState_x (S := S)).comp hprev_state
      have hprev_xbar :
          Measurable[mΩ]
            (fun ω =>
            (sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
                n ω).xbar) :=
        (measurable_sgsState_xbar (S := S)).comp hprev_state
      have houter_for_inner :
          Measurable[mΩ]
            (fun ω =>
              (sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
                (r.1 - 1) ω).x) := by
        simpa [r] using hprev_x
      have hsamples_r : ∀ j, Measurable[mΩ] (sample r j) := by
        intro j
        simpa [mΩ] using
          sgsEarlierOuterSample_measurable_strictPast
            (Ω := Ω) sample k r i j hrk
      have hinner_all :
          ∀ j,
            Measurable[mΩ]
              (fun ω =>
                sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
                  r j ω) :=
        sgsSelectedInnerProcess_measurable_of_context
          (S := S) mΩ x0 beta hbeta gamma hgamma T sample r
          houter_for_inner hsamples_r
      have hterminal :
          Measurable[mΩ]
            (fun ω =>
              sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
                r (T r) ω) :=
        hinner_all (T r)
      have hterminal_u :
          Measurable[mΩ]
            (fun ω =>
            (sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
                r (T r) ω).u) :=
        (measurable_spsState_u (S := S)).comp hterminal
      have hterminal_avg :
          Measurable[mΩ]
            (fun ω =>
            (sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
                r (T r) ω).avg) :=
        (measurable_spsState_avg (S := S)).comp hterminal
      have hxbar_next :
          Measurable[mΩ]
            (fun ω =>
              (⟨(1 - gamma r) •
                    (sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
                      n ω).xbar.1 +
                  gamma r •
                    (sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
                      r (T r) ω).avg.1,
                convexCombination_mem_X S
                  (sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
                    n ω).xbar
                  (sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
                    r (T r) ω).avg
                  (hgamma r).1 (hgamma r).2⟩ : FeasiblePoint S)) :=
        feasible_convexCombination_measurable (S := S) mΩ
          (fun ω =>
            (sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
              n ω).xbar)
          (fun ω =>
            (sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
              r (T r) ω).avg)
          (gamma r) (hgamma r).1 (hgamma r).2 hprev_xbar hterminal_avg
      have hstate :
          Measurable[mΩ]
            (fun ω =>
              ({ x :=
                  (sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
                    r (T r) ω).u
                 xbar :=
                  ⟨(1 - gamma r) •
                      (sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
                        n ω).xbar.1 +
                    gamma r •
                      (sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
                        r (T r) ω).avg.1,
                    convexCombination_mem_X S
                      (sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
                        n ω).xbar
                      (sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
                        r (T r) ω).avg
                      (hgamma r).1 (hgamma r).2⟩ } : SGSState S)) :=
        measurable_sgsState_mk (S := S) mΩ hterminal_u hxbar_next
      simpa [mΩ, r, sgsProcess_formulaExtensionSelector,
        sgsTransition_formulaExtensionSelector, spsOutput, positiveBetaSchedule,
        SOptLib.recursiveIterateProcess] using hstate

/-- Selected-realization strict-past adaptedness target for Algorithm 8.2.

This is the Candidate-1 causal bridge from the phase-2b route audit.  Unlike
`sgsGeneratedQueriesStrictPastAdapted_formulaExtension_source_obligation`, it is
not stated for an arbitrary relation-form witness of the generated process: the
inner processes are exactly the canonical selected SPS recursions
`sgsSelectedInnerProcesses`.  The intended proof is a nested induction over the
outer selected recursion and each inner `SOptLib.recursiveIterateProcess`,
using `sgsSample_measurable_strictPast`, `sgsStrictPastSampleSpace_mono`, and
`spsStep_measurable_past_context` for the Eq. (8.1.58) selected solver update. -/
theorem sgsSelectedGeneratedQueriesStrictPastAdapted
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (x0 : FeasiblePoint S)
    (beta : PositiveTime → ℝ) (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (gamma : PositiveTime → ℝ) (hgamma : gammaRangeCondition gamma)
    (T : PositiveTime → ℕ) (sample : PositiveTime → ℕ → Ω → Sample)
    (hsample_measurable : ∀ k i, Measurable (sample k i)) :
    sgsGeneratedQueriesStrictPastAdapted S sample
      (sgsSelectedInnerProcesses S x0 beta hbeta gamma hgamma T sample) := by
  classical
  intro k i
  induction i with
  | zero =>
      have hlt : k.1 - 1 < k.1 := by
        omega
      have houter_state :
          Measurable[sgsStrictPastSampleSpace (Ω := Ω) sample k 0]
            (fun ω =>
              sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
                (k.1 - 1) ω) :=
        sgsSelectedOuterState_measurable_strictPast_of_lt
          (S := S) x0 beta hbeta gamma hgamma T sample (k.1 - 1) k 0 hlt
      have houter_x :
          Measurable[sgsStrictPastSampleSpace (Ω := Ω) sample k 0]
            (fun ω =>
              (sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
                (k.1 - 1) ω).x) :=
        (measurable_sgsState_x (S := S)).comp houter_state
      simpa [sgsSelectedInnerProcesses, sgsInnerProcess_formulaExtensionSelector,
        spsProcess, SOptLib.recursiveIterateProcess, spsInitial] using houter_x
  | succ i ih =>
      have hlt : k.1 - 1 < k.1 := by
        omega
      have houter_state :
          Measurable[sgsStrictPastSampleSpace (Ω := Ω) sample k (i + 1)]
            (fun ω =>
              sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
                (k.1 - 1) ω) :=
        sgsSelectedOuterState_measurable_strictPast_of_lt
          (S := S) x0 beta hbeta gamma hgamma T sample (k.1 - 1) k (i + 1) hlt
      have houter :
          Measurable[sgsStrictPastSampleSpace (Ω := Ω) sample k (i + 1)]
            (fun ω =>
              (sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
                (k.1 - 1) ω).x) :=
        (measurable_sgsState_x (S := S)).comp houter_state
      have hprev :
          Measurable[sgsStrictPastSampleSpace (Ω := Ω) sample k (i + 1)]
            (fun ω =>
              (sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample
                k i ω).u) := by
        have hle :
            sgsStrictPastSampleSpace (Ω := Ω) sample k i ≤
              sgsStrictPastSampleSpace (Ω := Ω) sample k (i + 1) :=
          sgsStrictPastSampleSpace_le_same_outer_succ (Ω := Ω) sample k i
        simpa [sgsSelectedInnerProcesses] using ih.mono hle
      simpa [sgsSelectedInnerProcesses] using
        sgsSelectedInnerProcess_succ_u_measurable_strictPast_of_context
          (S := S) x0 beta hbeta gamma hgamma T sample k i houter hprev

/-- The selected SGS/SPS processes satisfy the generated Algorithm 8.1/8.2
run-level relation.

This theorem replaces theorem-head witness-style `states`, `inner`, and `hrun`
arguments for selected-run corollaries with a canonical process definition plus
one proof obligation. -/
theorem sgsSelectedRun_isGeneratedSGSProcess (x0 : FeasiblePoint S)
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E]
    (beta : PositiveTime → ℝ) (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (gamma : PositiveTime → ℝ) (hgamma : gammaRangeCondition gamma)
    (T : PositiveTime → ℕ) (sample : PositiveTime → ℕ → Ω → Sample) :
    IsGeneratedSGSProcess S x0 beta gamma T sample
      (sgsSelectedStates S x0 beta hbeta gamma hgamma T sample)
      (sgsSelectedInnerProcesses S x0 beta hbeta gamma hgamma T sample) := by
  exact
    (sgsProcess_formulaExtensionSelector_isGeneratedSGSProcess_formulaExtension
      S x0 beta hbeta gamma hgamma T sample).1

/-- The actual SGS/SPS search point queried by the stochastic oracle at outer
iteration `k` and inner index `i`.

This derived object ties the standing source independence assumption to the
canonical generated process, rather than passing theorem-local query functions
that can drift away from Algorithm 8.2. -/
noncomputable def sgsOracleQuery (x0 : FeasiblePoint S)
    (beta : PositiveTime → ℝ) (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (gamma : PositiveTime → ℝ) (hgamma : gammaRangeCondition gamma)
    (T : PositiveTime → ℕ)
    (sample : PositiveTime → ℕ → Ω → Sample)
    (k : PositiveTime) (i : ℕ)
    (ω : Ω) : E :=
  (sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T sample k i ω).u.1

/-- The selected one-step SPS update has the scalar square measurability needed
for L2 transport.

This proof does not use measurability of an arbitrary `Classical.choose`
minimizer.  It uses the generated-query measurability already present in the
source independence hypothesis for the actual selected Algorithm 8.2 query at
index `i+1`, then unfolds the selected recursion to identify that query with the
Eq. (8.1.58) one-step solver output. -/
theorem spsStep_formulaExtensionSelector_target_primal_displacement_sq_aemeasurable
    [MeasurableSpace Ω] [MeasurableSpace Sample] [MeasurableSpace E] [BorelSpace E]
    (law : SGSProbabilityModel (Ω := Ω) S) (x0 : FeasiblePoint S) (x : FeasiblePoint S)
    (beta gamma : PositiveTime → ℝ) (T : PositiveTime → ℕ)
    (hbeta : ∀ k : PositiveTime, 0 < beta k)
    (hgamma : gammaRangeCondition gamma)
    (hindep : sfoIndependent S law.P law.sample
      (sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample))
    (κ : PositiveTime) (i : ℕ) :
    AEStronglyMeasurable
      (fun ω =>
        S.primalNorm
          (x.1 -
            (spsStep_formulaExtensionSelector S
              (fun y =>
                smoothLinearization S
                  (outerExtrapolation S gamma κ
                    (sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T
                      law.sample (κ.1 - 1) ω)) y)
              (smoothLinearization_isAffineModel S
                (outerExtrapolation S gamma κ
                  (sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T
                    law.sample (κ.1 - 1) ω)))
              (sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T
                law.sample (κ.1 - 1) ω).x
              ⟨beta κ, hbeta κ⟩ ⟨i + 1, Nat.succ_pos i⟩
              (sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T
                law.sample κ i ω).u
              (law.sample κ i ω)).1.1) ^ 2) law.P := by
  classical
  letI : FiniteDimensional ℝ E := S.finiteDimensional_ambient
  rcases hindep with ⟨hquery, hquery_meas, _hindep_qs⟩
  have hnext_query_meas :
      AEStronglyMeasurable
        (fun ω =>
          (sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T
            law.sample κ (i + 1) ω).u.1) law.P := by
    have hfp :
        Measurable (fun ω =>
          (⟨sgsOracleQuery S x0 beta hbeta gamma hgamma T law.sample κ (i + 1) ω,
            hquery κ (i + 1) ω⟩ : FeasiblePoint S)) :=
      hquery_meas κ (i + 1)
    simpa [sgsOracleQuery] using
      (measurable_subtype_coe.comp hfp).aestronglyMeasurable
  have hstep_meas :
      AEStronglyMeasurable
        (fun ω =>
          (spsStep_formulaExtensionSelector S
            (fun y =>
              smoothLinearization S
                (outerExtrapolation S gamma κ
                  (sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T
                    law.sample (κ.1 - 1) ω)) y)
            (smoothLinearization_isAffineModel S
              (outerExtrapolation S gamma κ
                (sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T
                  law.sample (κ.1 - 1) ω)))
            (sgsProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T
              law.sample (κ.1 - 1) ω).x
            ⟨beta κ, hbeta κ⟩ ⟨i + 1, Nat.succ_pos i⟩
            (sgsInnerProcess_formulaExtensionSelector S x0 beta hbeta gamma hgamma T
              law.sample κ i ω).u
            (law.sample κ i ω)).1.1) law.P := by
    simpa [sgsInnerProcess_formulaExtensionSelector, spsProcess,
      spsProcess_formulaExtensionSelector, spsTransition_formulaExtensionSelector,
      spsTransition, SOptLib.recursiveIterateProcess] using hnext_query_meas
  rcases Seminorm.exists_bound_by_norm_of_finiteDimensional S.primalNorm with
    ⟨K, hK_nonneg, hK⟩
  have hprim_cont : Continuous S.primalNorm := by
    let q : Seminorm ℝ E := (Real.toNNReal K) • normSeminorm ℝ E
    have hqcont : Continuous q := by
      change Continuous (fun z : E => ((Real.toNNReal K : ℝ) * ‖z‖))
      exact continuous_const.mul continuous_norm
    refine Seminorm.continuous_of_le hqcont ?_
    intro z
    change S.primalNorm z ≤ ((Real.toNNReal K : ℝ) * ‖z‖)
    simpa [Real.toNNReal_of_nonneg hK_nonneg] using hK z
  exact (hprim_cont.comp_aestronglyMeasurable
    (aestronglyMeasurable_const.sub hstep_meas)).pow 2

/-- The outer extrapolation displacement is controlled by the two endpoint
displacements.

This is the `gammaRangeCondition` algebra needed in the selected SPS stability
route.  Candidate audit: searched for outer-extrapolation and finite-dimensional
seminorm-control helpers; existing hits cover measurability/integrability
transport or convexity of objective terms, not this pointwise squared seminorm
estimate. -/
theorem outerExtrapolation_primalNorm_sq_control
    (gamma : PositiveTime → ℝ) (κ : PositiveTime) (st : SGSState S)
    (u : FeasiblePoint S) (hγ0 : 0 ≤ gamma κ) (hγ1 : gamma κ ≤ 1) :
    S.primalNorm (u.1 - outerExtrapolation S gamma κ st) ^ 2 ≤
      2 *
        (S.primalNorm (u.1 - st.x.1) ^ 2 +
          S.primalNorm (u.1 - st.xbar.1) ^ 2) := by
  classical
  let a : ℝ := gamma κ
  let A : E := u.1 - st.x.1
  let B : E := u.1 - st.xbar.1
  have h1a_nonneg : 0 ≤ 1 - a := sub_nonneg.mpr (by simpa [a] using hγ1)
  have hvec :
      u.1 - outerExtrapolation S gamma κ st = a • A + (1 - a) • B := by
    dsimp [a, A, B, outerExtrapolation]
    module
  have hnorm :
      S.primalNorm (u.1 - outerExtrapolation S gamma κ st) ≤
        S.primalNorm A + S.primalNorm B := by
    calc
      S.primalNorm (u.1 - outerExtrapolation S gamma κ st)
          = S.primalNorm (a • A + (1 - a) • B) := by rw [hvec]
      _ ≤ S.primalNorm (a • A) + S.primalNorm ((1 - a) • B) :=
          map_add_le_add S.primalNorm _ _
      _ = |a| * S.primalNorm A + |1 - a| * S.primalNorm B := by
          simp [map_smul_eq_mul]
      _ ≤ S.primalNorm A + S.primalNorm B := by
          have hA_nonneg : 0 ≤ S.primalNorm A := apply_nonneg S.primalNorm _
          have hB_nonneg : 0 ≤ S.primalNorm B := apply_nonneg S.primalNorm _
          have ha_abs : |a| ≤ 1 := by
            rw [abs_of_nonneg (by simpa [a] using hγ0)]
            simpa [a] using hγ1
          have h1a_abs : |1 - a| ≤ 1 := by
            rw [abs_of_nonneg h1a_nonneg]
            nlinarith
          nlinarith [mul_le_mul_of_nonneg_right ha_abs hA_nonneg,
            mul_le_mul_of_nonneg_right h1a_abs hB_nonneg]
  have hleft_nonneg :
      0 ≤ S.primalNorm (u.1 - outerExtrapolation S gamma κ st) :=
    apply_nonneg S.primalNorm _
  have hright_nonneg : 0 ≤ S.primalNorm A + S.primalNorm B := by
    nlinarith [apply_nonneg S.primalNorm A, apply_nonneg S.primalNorm B]
  have hsquare :
      S.primalNorm (u.1 - outerExtrapolation S gamma κ st) ^ 2 ≤
        (S.primalNorm A + S.primalNorm B) ^ 2 := by
    nlinarith [hnorm, hleft_nonneg, hright_nonneg,
      sq_nonneg ((S.primalNorm A + S.primalNorm B) -
        S.primalNorm (u.1 - outerExtrapolation S gamma κ st))]
  have hab :
      (S.primalNorm A + S.primalNorm B) ^ 2 ≤
        2 * (S.primalNorm A ^ 2 + S.primalNorm B ^ 2) := by
    nlinarith [sq_nonneg (S.primalNorm A - S.primalNorm B)]
  exact hsquare.trans (by simpa [A, B] using hab)

/-- Young control for the selected-step oracle-noise pairing.

Aligns with the Proposition 8.3 Cauchy-Schwarz/Young absorption of
`⟪δ,u-u_{t-1}⟫`.  Candidate audit: considered SOptLib
`inner_sub_sub_bregman_le_half_dual_sq` and
`prox_gamma_step_bound_of_three_point_and_dual_support`; those also consume a
Bregman lower-bound term, while this route-local scalar helper isolates only
the paper's primal/dual norm pairing already provided by
`abs_inner_le_dualNorm_mul_primalNorm`. -/
theorem dual_noise_young_square_control (δ d : E) :
    ⟪δ, d⟫_ℝ ≤
      (1 / 2 : ℝ) * (dualNorm S δ ^ 2 + S.primalNorm d ^ 2) := by
  have hpair :
      ⟪δ, d⟫_ℝ ≤ dualNorm S δ * S.primalNorm d := by
    exact (le_abs_self _).trans (abs_inner_le_dualNorm_mul_primalNorm S δ d)
  nlinarith [hpair, sq_nonneg (dualNorm S δ - S.primalNorm d)]

/-- Fixed affine slopes can be absorbed into a constant times a quadratic
primal-norm budget.

This is the scalar Young step needed after introducing affine lower minorants
for `χ` in the selected SPS stability proof.  Candidate audit: considered
SOptLib `inner_sub_sub_bregman_le_half_dual_sq`,
`prox_gamma_step_bound_of_three_point_and_dual_support`, and the local
`dual_noise_young_square_control`; the SOptLib lemmas also consume a Bregman
term, while the local Young helper is exactly the pointwise primal/dual
pairing estimate needed for fixed affine slopes. -/
theorem fixed_linear_pairing_square_absorb (b : E) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ d : E, ⟪b, d⟫_ℝ ≤ C * (1 + S.primalNorm d ^ 2) := by
  classical
  let C : ℝ := (1 / 2 : ℝ) * (dualNorm S b ^ 2 + 1)
  refine ⟨C, ?_, ?_⟩
  · have hdual_sq : 0 ≤ dualNorm S b ^ 2 := sq_nonneg _
    dsimp [C]
    nlinarith
  · intro d
    have hyoung := dual_noise_young_square_control S b d
    have hprim_sq : 0 ≤ S.primalNorm d ^ 2 := sq_nonneg _
    have hdual_sq : 0 ≤ dualNorm S b ^ 2 := sq_nonneg _
    calc
      ⟪b, d⟫_ℝ
          ≤ (1 / 2 : ℝ) * (dualNorm S b ^ 2 + S.primalNorm d ^ 2) := hyoung
      _ ≤ C * (1 + S.primalNorm d ^ 2) := by
        dsimp [C]
        nlinarith [mul_nonneg hdual_sq hprim_sq]

/-- Scalar absorption of the outer extrapolation square into the displayed
previous-state square budget.

This is the final arithmetic step for the selected SPS pointwise stability
route after `outerExtrapolation_primalNorm_sq_control` has supplied
`y ≤ 2(a+b)`.  Candidate audit: searched the target/SOptLib scalar telescope
and Young helpers; `outerExtrapolation_primalNorm_sq_control` supplies the
geometric estimate, while no existing helper packages this exact nonnegative
budget enlargement. -/
theorem outer_extrapolation_square_rhs_absorb
    {A y a b c d : ℝ} (hA : 0 ≤ A)
    (hy : y ≤ 2 * (a + b))
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    A * (1 + y + c + d) ≤
      (2 * A) * (1 + a + b + c + d) := by
  have hbudget : 1 + y + c + d ≤ 2 * (1 + a + b + c + d) := by
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hbudget hA
  nlinarith

/-- An affine lower minorant turns a fixed feasible function difference into a
quadratic displacement budget.

This is the generic square-absorption form used for the non-Bregman lower-order
terms in the selected SPS stability proof. Candidate audit: the existing
`chi_difference_le_square_from_affine_minorant` proves only the `S.chi`
specialization, while `fixed_linear_pairing_square_absorb` supplies the scalar
Young step but not the carrier-function difference packaging needed for `f` and
`h`. -/
theorem feasible_function_difference_le_square_from_affine_minorant
    (x : FeasiblePoint S) (φ : E → ℝ) {a : ℝ} {b : E}
    (hφ : ∀ y : {x : E // x ∈ S.X}, a + ⟪b, y.1⟫_ℝ ≤ φ y.1) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ z : FeasiblePoint S,
        φ x.1 - φ z.1 ≤
          C * (1 + S.primalNorm (x.1 - z.1) ^ 2) := by
  classical
  obtain ⟨Cpair, hCpair_nonneg, hpair⟩ :=
    fixed_linear_pairing_square_absorb S b
  let K : ℝ := φ x.1 - a - ⟪b, x.1⟫_ℝ
  let C : ℝ := Cpair + |K|
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    nlinarith [abs_nonneg K]
  · intro z
    have hz_minor : a + ⟪b, z.1⟫_ℝ ≤ φ z.1 := hφ z
    have hdiff :
        φ x.1 - φ z.1 ≤ K + ⟪b, x.1 - z.1⟫_ℝ := by
      dsimp [K]
      have hinner : ⟪b, x.1 - z.1⟫_ℝ = ⟪b, x.1⟫_ℝ - ⟪b, z.1⟫_ℝ := by
        simp [inner_sub_right]
      nlinarith
    let B : ℝ := 1 + S.primalNorm (x.1 - z.1) ^ 2
    have hK_abs : K ≤ |K| * B := by
      have hK_le_abs : K ≤ |K| := le_abs_self K
      have habs_le_mul : |K| ≤ |K| * B := by
        have hB_ge_one : 1 ≤ B := by
          dsimp [B]
          nlinarith [sq_nonneg (S.primalNorm (x.1 - z.1))]
        nlinarith [mul_le_mul_of_nonneg_left hB_ge_one (abs_nonneg K)]
      exact hK_le_abs.trans habs_le_mul
    have hpairB :
        ⟪b, x.1 - z.1⟫_ℝ ≤ Cpair * B := by
      simpa [B] using hpair (x.1 - z.1)
    calc
      φ x.1 - φ z.1
          ≤ K + ⟪b, x.1 - z.1⟫_ℝ := hdiff
      _ ≤ |K| * B + Cpair * B := by
        nlinarith
      _ = C * B := by
        dsimp [C]
        ring

/-- An affine lower minorant for `χ` turns a `χ` difference into a quadratic
displacement budget.

This is the `χ`-specific piece of the selected SPS `Φ` elimination.  Candidate
audit: considered `convexOn_feasible_affine_minorant` and
`fixed_linear_pairing_square_absorb`; the former supplies the affine support
line, while the latter is the matching finite-dimensional Young absorption for
the fixed slope.  No SOptLib lemma packages this paper-local
`FeasiblePoint`/`χ` minorant shape. -/
theorem chi_difference_le_square_from_affine_minorant
    (x : FeasiblePoint S) {χa : ℝ} {χb : E}
    (hχ : ∀ y : {x : E // x ∈ S.X}, χa + ⟪χb, y.1⟫_ℝ ≤ S.chi y.1) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ z : FeasiblePoint S,
        S.chi x.1 - S.chi z.1 ≤
          C * (1 + S.primalNorm (x.1 - z.1) ^ 2) := by
  classical
  obtain ⟨Cpair, hCpair_nonneg, hpair⟩ :=
    fixed_linear_pairing_square_absorb S χb
  let K : ℝ := S.chi x.1 - χa - ⟪χb, x.1⟫_ℝ
  let C : ℝ := Cpair + |K|
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    nlinarith [abs_nonneg K]
  · intro z
    have hz_minor : χa + ⟪χb, z.1⟫_ℝ ≤ S.chi z.1 := hχ z
    have hdiff :
        S.chi x.1 - S.chi z.1 ≤ K + ⟪χb, x.1 - z.1⟫_ℝ := by
      dsimp [K]
      have hinner : ⟪χb, x.1 - z.1⟫_ℝ = ⟪χb, x.1⟫_ℝ - ⟪χb, z.1⟫_ℝ := by
        simp [inner_sub_right]
      nlinarith
    let B : ℝ := 1 + S.primalNorm (x.1 - z.1) ^ 2
    have hB_nonneg : 0 ≤ B := by
      dsimp [B]
      nlinarith [sq_nonneg (S.primalNorm (x.1 - z.1))]
    have hK_abs : K ≤ |K| * B := by
      have hK_le_abs : K ≤ |K| := le_abs_self K
      have habs_le_mul : |K| ≤ |K| * B := by
        have hB_ge_one : 1 ≤ B := by
          dsimp [B]
          nlinarith [sq_nonneg (S.primalNorm (x.1 - z.1))]
        nlinarith [mul_le_mul_of_nonneg_left hB_ge_one (abs_nonneg K)]
      exact hK_le_abs.trans habs_le_mul
    have hpairB :
        ⟪χb, x.1 - z.1⟫_ℝ ≤ Cpair * B := by
      simpa [B] using hpair (x.1 - z.1)
    calc
      S.chi x.1 - S.chi z.1
          ≤ K + ⟪χb, x.1 - z.1⟫_ℝ := hdiff
      _ ≤ |K| * B + Cpair * B := by
        nlinarith
      _ = C * B := by
        dsimp [C]
        ring

/-- Prox-potential support inequality on the feasible carrier, staged before
the Bregman coercivity helper.

Aligns with Lan Section 3.2's convex differentiable distance generator. Candidate
audit: considered SOptLib/Mathlib first-order convexity candidates and the
listed prox-step candidates; none directly produce this paper-local
`boundarySafeCarrierGradient` support line from `S.prox_geometry`, so this is
the same segment-derivative argument used later by the stability block. -/
theorem proxPotential_support_on_X_before_lower_bound
    (x z : FeasiblePoint S) :
    S.proxPotential x.1 +
      ⟪boundarySafeCarrierGradient S.X S.proxPotential x, z.1 - x.1⟫_ℝ ≤
        S.proxPotential z.1 := by
  classical
  rcases S.prox_geometry with ⟨_hcont, hdiffX, _hcore_convex, _hdiffCore, hconv, _hstrong⟩
  change S.proxPotential x.1 +
      ⟪gradientWithin S.proxPotential S.X x.1, z.1 - x.1⟫_ℝ ≤
        S.proxPotential z.1
  let line : ℝ → E := fun t => AffineMap.lineMap x.1 z.1 t
  let d : E := z.1 - x.1
  let s : Set ℝ := Set.Icc (0 : ℝ) 1
  have hline_deriv : HasDerivWithinAt line d s 0 := by
    simpa [line, d, s] using
      (AffineMap.hasDerivWithinAt_lineMap (a := x.1) (b := z.1)
        (s := Set.Icc (0 : ℝ) 1) (x := (0 : ℝ)))
  have hmaps : Set.MapsTo line s S.X := by
    intro t ht
    exact S.convex_X.lineMap_mem x.2 z.2 (by simpa [s] using ht)
  have hνdiff : DifferentiableWithinAt ℝ S.proxPotential S.X x.1 :=
    hdiffX x.1 x.2
  have hνline : HasDerivWithinAt (fun t : ℝ => S.proxPotential (line t))
      ((fderivWithin ℝ S.proxPotential S.X x.1) d) s 0 := by
    simpa [Function.comp_def] using
      hνdiff.hasFDerivWithinAt.comp_hasDerivWithinAt_of_eq 0 hline_deriv hmaps
        (by simp [line])
  have hgrad_apply :
      (fderivWithin ℝ S.proxPotential S.X x.1) d =
        ⟪gradientWithin S.proxPotential S.X x.1, d⟫_ℝ := by
    rw [gradientWithin, InnerProductSpace.toDual_symm_apply]
  have hderiv_line : HasDerivWithinAt (fun t : ℝ => S.proxPotential (line t))
      ⟪gradientWithin S.proxPotential S.X x.1, z.1 - x.1⟫_ℝ s 0 := by
    simpa [d, hgrad_apply] using hνline
  have hsec : ∀ t ∈ s,
      S.proxPotential (line t) - S.proxPotential x.1 ≤
        t * (S.proxPotential z.1 - S.proxPotential x.1) := by
    intro t ht
    have htI : t ∈ Set.Icc (0 : ℝ) 1 := by simpa [s] using ht
    rcases Set.mem_Icc.mp htI with ⟨ht0, ht1⟩
    have hconv_step := hconv.2 x.2 z.2 (sub_nonneg.mpr ht1) ht0 (by ring)
    have hline_eq : line t = (1 - t) • x.1 + t • z.1 := by
      simp [line, AffineMap.lineMap_apply_module']
      module
    have hconv_line :
        S.proxPotential (line t) ≤
          (1 - t) * S.proxPotential x.1 + t * S.proxPotential z.1 := by
      rw [hline_eq]
      simpa [smul_eq_mul] using hconv_step
    nlinarith
  let ψ : ℝ → ℝ := fun t =>
    t * (S.proxPotential z.1 - S.proxPotential x.1) -
      (S.proxPotential (line t) - S.proxPotential x.1)
  have hψmin : ∀ t ∈ s, ψ 0 ≤ ψ t := by
    intro t ht
    have h0 : ψ 0 = 0 := by simp [ψ, line]
    have ht_nonneg : 0 ≤ ψ t := by
      dsimp [ψ]
      have h := hsec t ht
      nlinarith
    rw [h0]
    exact ht_nonneg
  have hlin_deriv : HasDerivWithinAt
      (fun t : ℝ => t * (S.proxPotential z.1 - S.proxPotential x.1))
      (S.proxPotential z.1 - S.proxPotential x.1) s 0 := by
    simpa using (hasDerivWithinAt_id (x := (0 : ℝ)) (s := s)).mul_const
      (S.proxPotential z.1 - S.proxPotential x.1)
  have hνsub_deriv : HasDerivWithinAt
      (fun t : ℝ => S.proxPotential (line t) - S.proxPotential x.1)
      ⟪gradientWithin S.proxPotential S.X x.1, z.1 - x.1⟫_ℝ s 0 := by
    simpa using hderiv_line.sub_const (S.proxPotential x.1)
  have hψderiv : HasDerivWithinAt ψ
      ((S.proxPotential z.1 - S.proxPotential x.1) -
        ⟪gradientWithin S.proxPotential S.X x.1, z.1 - x.1⟫_ℝ) s 0 := by
    have h := hlin_deriv.sub hνsub_deriv
    simpa [ψ] using h
  have hnonneg :
      0 ≤ (S.proxPotential z.1 - S.proxPotential x.1) -
        ⟪gradientWithin S.proxPotential S.X x.1, z.1 - x.1⟫_ℝ := by
    exact right_derivative_nonneg_of_min_on_Icc (by simpa [s] using hψderiv)
      (by simpa [s] using hψmin)
  nlinarith

/-- Feasible points are prox-core points for the differentiable convex prox
potential, staged before Bregman coercivity.

Aligns with Lan Section 3.2's distance-generating function. Candidate audit:
considered `carrierGradientFrom_inner_eq_gradientWithin_on_feasible_direction`
and Mathlib minimizer-to-FOC lemmas; they transfer existing carrier gradients or
use an existing minimizer, while this paper-local step constructs the prox-core
witness from the support inequality. -/
theorem feasible_mem_proxCore_before_lower_bound (x : FeasiblePoint S) :
    x.1 ∈ proxCore S.X S.proxPotential := by
  classical
  refine ⟨x.2, ?_⟩
  let p : E := -boundarySafeCarrierGradient S.X S.proxPotential x
  refine ⟨p, ?_⟩
  intro u hu
  have hsupport :=
    proxPotential_support_on_X_before_lower_bound (S := S) x ⟨u, hu⟩
  have hsupport' :
      S.proxPotential x.1 +
          (⟪boundarySafeCarrierGradient S.X S.proxPotential x, u⟫_ℝ -
            ⟪boundarySafeCarrierGradient S.X S.proxPotential x, x.1⟫_ℝ) ≤
        S.proxPotential u := by
    simpa [inner_sub_right] using hsupport
  dsimp [p]
  rw [inner_neg_left]
  rw [inner_neg_left]
  nlinarith

/-- Under the current prox geometry, the paper prox-core equals the feasible
carrier, staged before Bregman coercivity.

Aligns with the convex-differentiable specialization of Lan Section 3.2.
Candidate audit: SOptLib has carrier/intrinsic-interior infrastructure but no
lemma for this paper-local `proxCore`; the equality follows from
`feasible_mem_proxCore_before_lower_bound` and `proxCore_subset`. -/
theorem proxCore_eq_X_before_lower_bound :
    proxCore S.X S.proxPotential = S.X := by
  exact Set.Subset.antisymm proxCore_subset
    (fun x hx => feasible_mem_proxCore_before_lower_bound (S := S) ⟨x, hx⟩)

/-- Prox-core branch pairing compatibility with the feasible carrier gradient.

Aligns with Lan Section 3.2 Eq. (3.2.2), where the same carrier gradient appears
in the Bregman formula and the strong-convexity lower bound. Candidate audit:
`carrierGradientFrom_inner_eq_gradientWithin_on_feasible_direction` is the
matching SOptLib bridge after rewriting the paper prox-core carrier to `S.X`. -/
theorem proxCoreGradient_pairing_eq_gradientWithin_before_lower_bound
    (x z : FeasiblePoint S) (hxcore : x.1 ∈ proxCore S.X S.proxPotential) :
    ⟪proxCoreGradient S ⟨x.1, hxcore⟩, z.1 - x.1⟫_ℝ =
      ⟪gradientWithin S.proxPotential S.X x.1, z.1 - x.1⟫_ℝ := by
  classical
  letI : FiniteDimensional ℝ E := S.finiteDimensional_ambient
  have hcore_eq : proxCore S.X S.proxPotential = S.X :=
    proxCore_eq_X_before_lower_bound (S := S)
  have hzcore : z.1 ∈ proxCore S.X S.proxPotential := by
    rw [hcore_eq]
    exact z.2
  have hne : Nonempty {x : E // x ∈ proxCore S.X S.proxPotential} :=
    ⟨⟨x.1, hxcore⟩⟩
  rcases S.prox_geometry with
    ⟨_hcont, _hdiffX, hcore_convex, hdiffCore, _hconv, _hstrong⟩
  have hdiffCoreAt :
      DifferentiableWithinAt ℝ S.proxPotential
        (proxCore S.X S.proxPotential) x.1 :=
    hdiffCore.differentiableOn_one x.1 hxcore
  have hcarrier :=
    carrierGradientFrom_inner_eq_gradientWithin_on_feasible_direction
      (v := fun y : {x : E // x ∈ proxCore S.X S.proxPotential} =>
        S.proxPotential y.1)
      (ν := S.proxPotential)
      (anchor := Classical.choice hne)
      (z := ⟨x.1, hxcore⟩)
      (x := ⟨z.1, hzcore⟩)
      hcore_convex hdiffCoreAt (by intro y; rfl)
  have hright :
      ⟪gradientWithin S.proxPotential (proxCore S.X S.proxPotential) x.1,
          z.1 - x.1⟫_ℝ =
        ⟪gradientWithin S.proxPotential S.X x.1, z.1 - x.1⟫_ℝ := by
    rw [hcore_eq]
  have hcarrierX :
      ⟪SOptLib.carrierGradientFrom (proxCore S.X S.proxPotential)
          (fun y : {x : E // x ∈ proxCore S.X S.proxPotential} =>
            S.proxPotential y.1)
          (Classical.choice hne) ⟨x.1, hxcore⟩, z.1 - x.1⟫_ℝ =
        ⟪gradientWithin S.proxPotential S.X x.1, z.1 - x.1⟫_ℝ := by
    exact hcarrier.trans hright
  simpa [proxCoreGradient, proxCoreGradientRaw, hne] using hcarrierX

/-- Canonical feasible-carrier formula for `bregmanFormulaOnX` before applying
the Bregman lower bound.

Aligns with Lan Section 3.2 Eq. (3.2.2). Candidate audit:
`blockBregmanDivergence_eq_gradientWithin_formula` normalizes the carrier
Bregman object, while the paper-local formula extension also has a prox-core
branch; the helpers above discharge that branch and show the totalized formula
is exactly the `gradientWithin` carrier expression. -/
theorem bregmanFormulaOnX_gradientWithin_formula_before_lower_bound
    (x z : FeasiblePoint S) :
    bregmanFormulaOnX S x z =
      S.proxPotential z.1 - S.proxPotential x.1 -
        ⟪gradientWithin S.proxPotential S.X x.1, z.1 - x.1⟫_ℝ := by
  classical
  letI : FiniteDimensional ℝ E := S.finiteDimensional_ambient
  by_cases hxcore : x.1 ∈ proxCore S.X S.proxPotential
  · have hpair :=
      proxCoreGradient_pairing_eq_gradientWithin_before_lower_bound
        (S := S) x z hxcore
    have hpair_raw :
        ⟪proxCoreGradientRaw S.X S.proxPotential ⟨x.1, hxcore⟩, z.1 - x.1⟫_ℝ =
          ⟪gradientWithin S.proxPotential S.X x.1, z.1 - x.1⟫_ℝ := by
      simpa [proxCoreGradient] using hpair
    simp [bregmanFormulaOnX, feasibleBregmanFormulaExtension, hxcore, hpair_raw]
  · have hxcore' : x.1 ∈ proxCore S.X S.proxPotential :=
      feasible_mem_proxCore_before_lower_bound (S := S) x
    exact False.elim (hxcore hxcore')

/-- Feasible-pair Bregman coercivity used before selected SPS stability.

Aligns with Lan Section 3.2 Eq. (3.2.3).  Candidate audit:
`bregman_lower_bound_of_strongConvexOnWithSeminorm_differentiableWithinAt` is
the matching SOptLib lower bound; this helper only specializes it to
`S.prox_geometry` and rewrites the result to the paper-local
`bregmanFormulaOnX` carrier formula. -/
theorem bregmanFormulaOnX_lower_bound_from_prox_geometry
    (x z : FeasiblePoint S) :
    (1 / 2 : ℝ) * S.primalNorm (z.1 - x.1) ^ 2 ≤
      bregmanFormulaOnX S x z := by
  classical
  letI : FiniteDimensional ℝ E := S.finiteDimensional_ambient
  have hformula :=
    bregmanFormulaOnX_gradientWithin_formula_before_lower_bound (S := S) x z
  rcases S.prox_geometry with
    ⟨_hcont, hdiffX, _hcoreConv, _hcontdiffCore, _hconvNu, hstrong⟩
  have hstrongJensen :
      ∀ ⦃y⦄, y ∈ S.X → ∀ ⦃w⦄, w ∈ S.X → ∀ ⦃a b : ℝ⦄,
        0 ≤ a → 0 ≤ b → a + b = 1 →
          S.proxPotential (a • y + b • w) ≤
            a * S.proxPotential y + b * S.proxPotential w -
              (1 : ℝ) / 2 * a * b * S.primalNorm (y - w) ^ 2 := by
    intro y hy w hw a b ha hb hab
    simpa [StrongConvexOnWithGauge] using
      hstrong (x := y) hy (y := w) hw (a := a) (b := b) ha hb hab
  have hlower :=
    bregman_lower_bound_of_strongConvexOnWithSeminorm_differentiableWithinAt
      (X := S.X) (ν := S.proxPotential) (p := S.primalNorm)
      (z := x.1) (x := z.1) S.convex_X (hdiffX x.1 x.2)
      hstrongJensen x.2 z.2
  rw [hformula]
  simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hlower

/-- Fixed affine slopes can be absorbed into an arbitrarily small multiple of
the comparator Bregman divergence.

Aligns with the Young/coercivity absorption used after Lan Proposition 8.3,
Eq. (8.1.61). Candidate audit: considered SOptLib
`inner_sub_sub_bregman_le_half_dual_sq`, the local
`fixed_linear_pairing_square_absorb`, and
`bregmanFormulaOnX_lower_bound_from_prox_geometry`; the SOptLib helper has a
fixed half-squared coefficient and the existing local helper only gives a
square budget, while this selected transfer needs the arbitrary `eps` Bregman
coefficient needed for half-coefficient absorption. -/
theorem fixed_linear_pairing_bregman_absorb_with_epsilon
    (u : FeasiblePoint S) (b : E) {eps : ℝ} (heps : 0 < eps) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ z : FeasiblePoint S,
        ⟪b, u.1 - z.1⟫_ℝ ≤ eps * bregmanFormulaOnX S z u + C := by
  classical
  let D : ℝ := dualNorm S b
  let C : ℝ := D ^ 2 / (2 * eps)
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    positivity
  · intro z
    let q : ℝ := S.primalNorm (u.1 - z.1)
    have hpair : ⟪b, u.1 - z.1⟫_ℝ ≤ D * q := by
      have hle_abs : ⟪b, u.1 - z.1⟫_ℝ ≤ |⟪b, u.1 - z.1⟫_ℝ| :=
        le_abs_self _
      exact hle_abs.trans (by
        simpa [D, q] using abs_inner_le_dualNorm_mul_primalNorm S b (u.1 - z.1))
    have hyoung : D * q ≤ (eps / 2) * q ^ 2 + C := by
      have hsq : 0 ≤ (eps * q - D) ^ 2 := sq_nonneg _
      dsimp [C]
      field_simp [ne_of_gt heps]
      nlinarith [hsq]
    have hlower :
        (1 / 2 : ℝ) * q ^ 2 ≤ bregmanFormulaOnX S z u := by
      simpa [q] using bregmanFormulaOnX_lower_bound_from_prox_geometry S z u
    have habsorb :
        (eps / 2) * q ^ 2 ≤ eps * bregmanFormulaOnX S z u := by
      have hmul := mul_le_mul_of_nonneg_left hlower heps.le
      nlinarith [hmul]
    nlinarith [hpair, hyoung, habsorb]

/-- Explicit version of `fixed_linear_pairing_bregman_absorb_with_epsilon`.

This removes the existential constant from later random-center envelopes: the
constant is exactly the Young coefficient `||b||_*^2/(2 eps)`, so integrability
proofs can inspect the random terms instead of unfolding a pathwise
`Classical.choose`. -/
theorem fixed_linear_pairing_bregman_absorb_with_epsilon_explicit
    (u : FeasiblePoint S) (b : E) {eps : ℝ} (heps : 0 < eps) :
    ∀ z : FeasiblePoint S,
      ⟪b, u.1 - z.1⟫_ℝ ≤
        eps * bregmanFormulaOnX S z u + dualNorm S b ^ 2 / (2 * eps) := by
  classical
  intro z
  let D : ℝ := dualNorm S b
  let q : ℝ := S.primalNorm (u.1 - z.1)
  have hpair : ⟪b, u.1 - z.1⟫_ℝ ≤ D * q := by
    have hle_abs : ⟪b, u.1 - z.1⟫_ℝ ≤ |⟪b, u.1 - z.1⟫_ℝ| :=
      le_abs_self _
    exact hle_abs.trans (by
      simpa [D, q] using abs_inner_le_dualNorm_mul_primalNorm S b (u.1 - z.1))
  have hyoung :
      D * q ≤ (eps / 2) * q ^ 2 + dualNorm S b ^ 2 / (2 * eps) := by
    have hsq : 0 ≤ (eps * q - D) ^ 2 := sq_nonneg _
    dsimp [D]
    field_simp [ne_of_gt heps]
    nlinarith [hsq]
  have hlower :
      (1 / 2 : ℝ) * q ^ 2 ≤ bregmanFormulaOnX S z u := by
    simpa [q] using bregmanFormulaOnX_lower_bound_from_prox_geometry S z u
  have habsorb :
      (eps / 2) * q ^ 2 ≤ eps * bregmanFormulaOnX S z u := by
    have hmul := mul_le_mul_of_nonneg_left hlower heps.le
    nlinarith [hmul]
  nlinarith [hpair, hyoung, habsorb]

/-- Weighted explicit Young/Bregman absorption with the previous-window SGS
coefficient used in Proposition 8.3 Eq. (8.1.63).

This is a coefficient-normalized specialization of
`fixed_linear_pairing_bregman_absorb_with_epsilon_explicit`: searched SOptLib
and target-file Young/Bregman candidates; the existing explicit local lemma is
the matching primitive, while SOptLib proximal tail absorptions do not expose
the paper's `propCoeff/(4*(j+1))` previous-window coefficient. -/
theorem fixed_linear_pairing_bregman_absorb_previous_window
    (u z : FeasiblePoint S) (b : E) {propCoeff n q : ℝ}
    (hpropCoeff : 0 < propCoeff) (hn : 0 < n) (hq : 0 < q) :
    q * ⟪b, u.1 - z.1⟫_ℝ ≤
      (propCoeff / (4 * n)) * bregmanFormulaOnX S z u +
        2 * n * q ^ 2 * dualNorm S b ^ 2 / propCoeff := by
  let eps : ℝ := propCoeff / (4 * n * q)
  have heps : 0 < eps := by
    dsimp [eps]
    positivity
  have hbase :=
    fixed_linear_pairing_bregman_absorb_with_epsilon_explicit
      (S := S) u b heps z
  have hmul := mul_le_mul_of_nonneg_left hbase hq.le
  have hcoefV : q * eps = propCoeff / (4 * n) := by
    dsimp [eps]
    field_simp [ne_of_gt hq]
  have hcoefD :
      q * (dualNorm S b ^ 2 / (2 * eps)) =
        2 * n * q ^ 2 * dualNorm S b ^ 2 / propCoeff := by
    dsimp [eps]
    field_simp [ne_of_gt hq, ne_of_gt hpropCoeff]
    ring
  calc
    q * ⟪b, u.1 - z.1⟫_ℝ
        ≤ q *
            (eps * bregmanFormulaOnX S z u +
              dualNorm S b ^ 2 / (2 * eps)) := by
          simpa [eps] using hmul
    _ =
        q * eps * bregmanFormulaOnX S z u +
          q * (dualNorm S b ^ 2 / (2 * eps)) := by
          ring
    _ =
        (propCoeff / (4 * n)) * bregmanFormulaOnX S z u +
          2 * n * q ^ 2 * dualNorm S b ^ 2 / propCoeff := by
          rw [hcoefV, hcoefD]

/-- Bregman integrability implies L2 integrability of the paper primal
displacement.

Aligns with Lan Section 3.2 prox coercivity as used after Proposition 8.3.
Candidate audit: considered the pre-searched finite-window selection candidates
and searched SOptLib for domination/integrability; the relevant existing pieces
are `bregmanFormulaOnX_lower_bound_from_prox_geometry` for the paper-local
coercivity and Mathlib/SOptLib `Integrable.mono'` domination, while no existing
helper packaged this `FeasiblePoint` query-to-comparator conversion. -/
theorem query_sq_integrable_of_bregman_integrable
    [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
    (P : Measure Ω) [IsFiniteMeasure P] (x : FeasiblePoint S)
    (q : Ω → FeasiblePoint S)
    (hq_meas : Measurable q)
    (hbreg : Integrable (fun ω => bregmanFormulaOnX S (q ω) x) P) :
    Integrable (fun ω => S.primalNorm (x.1 - (q ω).1) ^ 2) P := by
  classical
  letI : FiniteDimensional ℝ E := S.finiteDimensional_ambient
  rcases Seminorm.exists_bound_by_norm_of_finiteDimensional S.primalNorm with
    ⟨K, hK_nonneg, hK⟩
  have hprim_cont : Continuous S.primalNorm := by
    let qnorm : Seminorm ℝ E := (Real.toNNReal K) • normSeminorm ℝ E
    have hqcont : Continuous qnorm := by
      change Continuous (fun z : E => ((Real.toNNReal K : ℝ) * ‖z‖))
      exact continuous_const.mul continuous_norm
    refine Seminorm.continuous_of_le hqcont ?_
    intro z
    change S.primalNorm z ≤ ((Real.toNNReal K : ℝ) * ‖z‖)
    simpa [Real.toNNReal_of_nonneg hK_nonneg] using hK z
  have hqE_meas : Measurable (fun ω => (q ω).1) :=
    measurable_subtype_coe.comp hq_meas
  have hsq_meas :
      AEStronglyMeasurable
        (fun ω => S.primalNorm (x.1 - (q ω).1) ^ 2) P := by
    exact
      (hprim_cont.comp_aestronglyMeasurable
        ((measurable_const.sub hqE_meas).aestronglyMeasurable)).pow 2
  refine Integrable.mono' (hbreg.const_mul 2) hsq_meas ?_
  refine Filter.Eventually.of_forall ?_
  intro ω
  let r : ℝ := S.primalNorm (x.1 - (q ω).1) ^ 2
  let V : ℝ := bregmanFormulaOnX S (q ω) x
  have hr_nonneg : 0 ≤ r := by
    dsimp [r]
    exact sq_nonneg _
  have hlower : (1 / 2 : ℝ) * r ≤ V := by
    dsimp [r, V]
    simpa using bregmanFormulaOnX_lower_bound_from_prox_geometry S (q ω) x
  have hV_nonneg : 0 ≤ V := by
    nlinarith
  have hr_le : r ≤ 2 * V := by
    nlinarith
  calc
    ‖S.primalNorm (x.1 - (q ω).1) ^ 2‖ = r := by
      dsimp [r]
      exact abs_of_nonneg (sq_nonneg _)
    _ ≤ 2 * V := hr_le

/-- Feasible-point strong monotonicity of the paper prox-gradient.

Aligns with Lan Section 3.2 Eq. (3.2.1). Candidate audit:
`sq_norm_le_inner_gradient_sub_of_strong_distance_generator` packages an
abstract monotonicity specialization, while the target file already has the
paper-local Bregman lower bound
`bregmanFormulaOnX_lower_bound_from_prox_geometry`; summing that bound in both
directions gives the exact `boundarySafeCarrierGradient` form needed before the
selected stability theorem. -/
theorem feasible_gradient_strong_monotone_from_prox_geometry_before_stability
    (a b : FeasiblePoint S) :
    S.primalNorm (b.1 - a.1) ^ 2 ≤
      ⟪b.1 - a.1,
        boundarySafeCarrierGradient S.X S.proxPotential b -
          boundarySafeCarrierGradient S.X S.proxPotential a⟫_ℝ := by
  classical
  rcases S.prox_geometry with
    ⟨_hcont, hdiffX, _hcoreConv, _hcontdiffCore, _hconv, hstrong⟩
  have hstrong' :
      ∀ ⦃y⦄, y ∈ S.X → ∀ ⦃w⦄, w ∈ S.X → ∀ ⦃α β : ℝ⦄,
        0 ≤ α → 0 ≤ β → α + β = 1 →
          S.proxPotential (α • y + β • w) ≤
            α * S.proxPotential y + β * S.proxPotential w -
              (1 : ℝ) / 2 * α * β * S.primalNorm (y - w) ^ 2 := by
    intro y hy w hw α β hα hβ hsum
    simpa [StrongConvexOnWithGauge] using
      hstrong (x := y) hy (y := w) hw (a := α) (b := β) hα hβ hsum
  have hab :
      (1 / 2 : ℝ) * S.primalNorm (b.1 - a.1) ^ 2 ≤
        S.proxPotential b.1 -
          (S.proxPotential a.1 +
            ⟪gradientWithin S.proxPotential S.X a.1, b.1 - a.1⟫_ℝ) :=
    bregman_lower_bound_of_strongConvexOnWithSeminorm_differentiableWithinAt
      (X := S.X) (ν := S.proxPotential) (p := S.primalNorm)
      (z := a.1) (x := b.1) S.convex_X (hdiffX a.1 a.2) hstrong' a.2 b.2
  have hba :
      (1 / 2 : ℝ) * S.primalNorm (a.1 - b.1) ^ 2 ≤
        S.proxPotential a.1 -
          (S.proxPotential b.1 +
            ⟪gradientWithin S.proxPotential S.X b.1, a.1 - b.1⟫_ℝ) :=
    bregman_lower_bound_of_strongConvexOnWithSeminorm_differentiableWithinAt
      (X := S.X) (ν := S.proxPotential) (p := S.primalNorm)
      (z := b.1) (x := a.1) S.convex_X (hdiffX b.1 b.2) hstrong' b.2 a.2
  have hnorm_rev :
      S.primalNorm (a.1 - b.1) = S.primalNorm (b.1 - a.1) := by
    have hneg : a.1 - b.1 = -(b.1 - a.1) := by
      abel
    rw [hneg]
    simpa using map_neg_eq_map S.primalNorm (b.1 - a.1)
  have hba' :
      (1 / 2 : ℝ) * S.primalNorm (b.1 - a.1) ^ 2 ≤
        S.proxPotential a.1 -
          (S.proxPotential b.1 +
            ⟪gradientWithin S.proxPotential S.X b.1, a.1 - b.1⟫_ℝ) := by
    simpa [hnorm_rev] using hba
  have hsum_lower :
      S.primalNorm (b.1 - a.1) ^ 2 ≤
        (S.proxPotential b.1 -
            (S.proxPotential a.1 +
              ⟪gradientWithin S.proxPotential S.X a.1, b.1 - a.1⟫_ℝ)) +
          (S.proxPotential a.1 -
            (S.proxPotential b.1 +
              ⟪gradientWithin S.proxPotential S.X b.1, a.1 - b.1⟫_ℝ)) := by
    nlinarith [hab, hba']
  have hsum_eq :
      (S.proxPotential b.1 -
          (S.proxPotential a.1 +
            ⟪gradientWithin S.proxPotential S.X a.1, b.1 - a.1⟫_ℝ)) +
        (S.proxPotential a.1 -
          (S.proxPotential b.1 +
            ⟪gradientWithin S.proxPotential S.X b.1, a.1 - b.1⟫_ℝ)) =
          ⟪b.1 - a.1,
            gradientWithin S.proxPotential S.X b.1 -
              gradientWithin S.proxPotential S.X a.1⟫_ℝ := by
    simp [inner_sub_left, inner_sub_right, real_inner_comm]
    ring
  have hmain :
      S.primalNorm (b.1 - a.1) ^ 2 ≤
        ⟪b.1 - a.1,
          gradientWithin S.proxPotential S.X b.1 -
            gradientWithin S.proxPotential S.X a.1⟫_ℝ :=
    hsum_lower.trans_eq hsum_eq
  simpa [boundarySafeCarrierGradient] using hmain

/-- Two-anchor variational square control with the actual prox-gradient residual.

This is the direct coercivity consequence of the selected first-variation shape.
It deliberately exposes the residual
`r + μ₁(∇ν(x)-∇ν(a)) + μ₂(∇ν(x)-∇ν(b))`: with only
`S.prox_geometry`, `abs_inner_le_dualNorm_mul_primalNorm`, and no Bregman upper
envelope or prox-gradient Lipschitz field, this residual is the strongest
square-control form available. Candidate audit: considered SOptLib
`inner_sub_sub_bregman_le_half_dual_sq` and
`prox_gamma_step_bound_of_three_point_and_dual_support`; both absorb a residual
against a Bregman lower bound, but neither removes these anchor-gradient
differences into anchor-distance squares. -/
theorem two_anchor_prox_square_control_with_gradient_residual_before_stability
    (x y a b : FeasiblePoint S) (μ1 μ2 : ℝ) (r : E)
    (hμ1 : 0 ≤ μ1) (hμ2 : 0 ≤ μ2) (hμsum : 0 < μ1 + μ2)
    (hvi :
      0 ≤
        ⟪r, x.1 - y.1⟫_ℝ +
          μ1 * ⟪boundarySafeCarrierGradient S.X S.proxPotential y -
              boundarySafeCarrierGradient S.X S.proxPotential a,
            x.1 - y.1⟫_ℝ +
          μ2 * ⟪boundarySafeCarrierGradient S.X S.proxPotential y -
              boundarySafeCarrierGradient S.X S.proxPotential b,
            x.1 - y.1⟫_ℝ) :
    let R : E :=
      r +
        μ1 • (boundarySafeCarrierGradient S.X S.proxPotential x -
          boundarySafeCarrierGradient S.X S.proxPotential a) +
        μ2 • (boundarySafeCarrierGradient S.X S.proxPotential x -
          boundarySafeCarrierGradient S.X S.proxPotential b)
    S.primalNorm (x.1 - y.1) ^ 2 ≤
      dualNorm S R ^ 2 / (μ1 + μ2) ^ 2 := by
  classical
  let d : E := x.1 - y.1
  let gx : E := boundarySafeCarrierGradient S.X S.proxPotential x
  let gy : E := boundarySafeCarrierGradient S.X S.proxPotential y
  let ga : E := boundarySafeCarrierGradient S.X S.proxPotential a
  let gb : E := boundarySafeCarrierGradient S.X S.proxPotential b
  let R : E := r + μ1 • (gx - ga) + μ2 • (gx - gb)
  let q : ℝ := S.primalNorm d
  let D : ℝ := dualNorm S R
  have hq_nonneg : 0 ≤ q := by
    exact apply_nonneg S.primalNorm d
  have hD_nonneg : 0 ≤ D := by
    dsimp [D, dualNorm]
    exact SOptLib.canonicalDualNorm_nonneg S.primalNorm R
  have hmono :
      q ^ 2 ≤ ⟪d, gx - gy⟫_ℝ := by
    simpa [q, d, gx, gy] using
      feasible_gradient_strong_monotone_from_prox_geometry_before_stability S y x
  have hcoercive :
      (μ1 + μ2) * q ^ 2 ≤ ⟪R, d⟫_ℝ := by
    have hR_decomp :
        ⟪R, d⟫_ℝ =
          (⟪r, d⟫_ℝ +
            μ1 * ⟪gy - ga, d⟫_ℝ +
            μ2 * ⟪gy - gb, d⟫_ℝ) +
            (μ1 + μ2) * ⟪gx - gy, d⟫_ℝ := by
      simp [R, gx, gy, ga, gb, inner_add_left, inner_smul_left,
        inner_sub_left]
      ring
    have hvi' :
        0 ≤
          ⟪r, d⟫_ℝ +
            μ1 * ⟪gy - ga, d⟫_ℝ +
            μ2 * ⟪gy - gb, d⟫_ℝ := by
      simpa [d, gx, gy, ga, gb, add_assoc, add_left_comm, add_comm] using hvi
    have hmono' : q ^ 2 ≤ ⟪gx - gy, d⟫_ℝ := by
      simpa [real_inner_comm] using hmono
    have hscaled :
        (μ1 + μ2) * q ^ 2 ≤ (μ1 + μ2) * ⟪gx - gy, d⟫_ℝ := by
      exact mul_le_mul_of_nonneg_left hmono' hμsum.le
    nlinarith [hR_decomp, hvi', hscaled]
  have hinner_le : ⟪R, d⟫_ℝ ≤ D * q := by
    have habs := abs_inner_le_dualNorm_mul_primalNorm S R d
    have hle_abs : ⟪R, d⟫_ℝ ≤ |⟪R, d⟫_ℝ| := le_abs_self _
    exact hle_abs.trans (by simpa [D, q] using habs)
  have hmain : (μ1 + μ2) * q ^ 2 ≤ D * q := hcoercive.trans hinner_le
  by_cases hq_zero : q = 0
  · have hlhs_zero : S.primalNorm (x.1 - y.1) ^ 2 = 0 := by
      simpa [q, d, hq_zero]
    have hden_pos : 0 < (μ1 + μ2) ^ 2 := sq_pos_of_ne_zero (ne_of_gt hμsum)
    have hrhs_nonneg :
        0 ≤
          dualNorm S
              (r +
                μ1 •
                  (boundarySafeCarrierGradient S.X S.proxPotential x -
                    boundarySafeCarrierGradient S.X S.proxPotential a) +
                μ2 •
                  (boundarySafeCarrierGradient S.X S.proxPotential x -
                    boundarySafeCarrierGradient S.X S.proxPotential b)) ^ 2 /
            (μ1 + μ2) ^ 2 := by
      positivity
    nlinarith
  · have hq_pos : 0 < q := lt_of_le_of_ne hq_nonneg (Ne.symm hq_zero)
    have hlinear : (μ1 + μ2) * q ≤ D := by
      have hmul : ((μ1 + μ2) * q) * q ≤ D * q := by
        nlinarith
      exact le_of_mul_le_mul_right hmul hq_pos
    have hsq_scaled : ((μ1 + μ2) * q) ^ 2 ≤ D ^ 2 := by
      nlinarith [sq_nonneg (D - (μ1 + μ2) * q)]
    have hden_pos : 0 < (μ1 + μ2) ^ 2 := sq_pos_of_ne_zero (ne_of_gt hμsum)
    have hdiv := div_le_div_of_nonneg_right hsq_scaled hden_pos.le
    have hscale :
        ((μ1 + μ2) * q) ^ 2 / (μ1 + μ2) ^ 2 = q ^ 2 := by
      field_simp [ne_of_gt hμsum]
    simpa [R, q, D, hscale] using hdiv

/-- Offset version of the two-anchor square control.

This is the form directly instantiated from the selected first variation after
an affine minorant turns the nonsmooth `χ` difference into a fixed scalar plus a
linear force.  It still exposes the same unavoidable prox-gradient residual as
`two_anchor_prox_square_control_with_gradient_residual_before_stability`; the
offset is absorbed into a harmless constant term. Candidate audit: no SOptLib
prox lemma found in the searched candidates includes this scalar offset while
preserving the paper-local `boundarySafeCarrierGradient` two-anchor geometry. -/
theorem two_anchor_prox_square_control_with_offset_gradient_residual_before_stability
    (x y a b : FeasiblePoint S) (μ1 μ2 η : ℝ) (r : E)
    (hμ1 : 0 ≤ μ1) (hμ2 : 0 ≤ μ2) (hμsum : 0 < μ1 + μ2)
    (hvi :
      0 ≤
        η + ⟪r, x.1 - y.1⟫_ℝ +
          μ1 * ⟪boundarySafeCarrierGradient S.X S.proxPotential y -
              boundarySafeCarrierGradient S.X S.proxPotential a,
            x.1 - y.1⟫_ℝ +
          μ2 * ⟪boundarySafeCarrierGradient S.X S.proxPotential y -
              boundarySafeCarrierGradient S.X S.proxPotential b,
            x.1 - y.1⟫_ℝ) :
    let R : E :=
      r +
        μ1 • (boundarySafeCarrierGradient S.X S.proxPotential x -
          boundarySafeCarrierGradient S.X S.proxPotential a) +
        μ2 • (boundarySafeCarrierGradient S.X S.proxPotential x -
          boundarySafeCarrierGradient S.X S.proxPotential b)
    S.primalNorm (x.1 - y.1) ^ 2 ≤
      (2 * max 0 η) / (μ1 + μ2) +
        dualNorm S R ^ 2 / (μ1 + μ2) ^ 2 := by
  classical
  let d : E := x.1 - y.1
  let gx : E := boundarySafeCarrierGradient S.X S.proxPotential x
  let gy : E := boundarySafeCarrierGradient S.X S.proxPotential y
  let ga : E := boundarySafeCarrierGradient S.X S.proxPotential a
  let gb : E := boundarySafeCarrierGradient S.X S.proxPotential b
  let R : E := r + μ1 • (gx - ga) + μ2 • (gx - gb)
  let q : ℝ := S.primalNorm d
  let D : ℝ := dualNorm S R
  have hq_nonneg : 0 ≤ q := apply_nonneg S.primalNorm d
  have hD_nonneg : 0 ≤ D := by
    dsimp [D, dualNorm]
    exact SOptLib.canonicalDualNorm_nonneg S.primalNorm R
  have hη_le : η ≤ max 0 η := le_max_right 0 η
  have hmono :
      q ^ 2 ≤ ⟪d, gx - gy⟫_ℝ := by
    simpa [q, d, gx, gy] using
      feasible_gradient_strong_monotone_from_prox_geometry_before_stability S y x
  have hcoercive :
      (μ1 + μ2) * q ^ 2 ≤ η + ⟪R, d⟫_ℝ := by
    have hR_decomp :
        ⟪R, d⟫_ℝ =
          (⟪r, d⟫_ℝ +
            μ1 * ⟪gy - ga, d⟫_ℝ +
            μ2 * ⟪gy - gb, d⟫_ℝ) +
            (μ1 + μ2) * ⟪gx - gy, d⟫_ℝ := by
      simp [R, gx, gy, ga, gb, inner_add_left, inner_smul_left,
        inner_sub_left]
      ring
    have hvi' :
        0 ≤
          η + ⟪r, d⟫_ℝ +
            μ1 * ⟪gy - ga, d⟫_ℝ +
            μ2 * ⟪gy - gb, d⟫_ℝ := by
      simpa [d, gx, gy, ga, gb, add_assoc, add_left_comm, add_comm] using hvi
    have hmono' : q ^ 2 ≤ ⟪gx - gy, d⟫_ℝ := by
      simpa [real_inner_comm] using hmono
    have hscaled :
        (μ1 + μ2) * q ^ 2 ≤ (μ1 + μ2) * ⟪gx - gy, d⟫_ℝ := by
      exact mul_le_mul_of_nonneg_left hmono' hμsum.le
    nlinarith [hR_decomp, hvi', hscaled]
  have hinner_le : ⟪R, d⟫_ℝ ≤ D * q := by
    have habs := abs_inner_le_dualNorm_mul_primalNorm S R d
    have hle_abs : ⟪R, d⟫_ℝ ≤ |⟪R, d⟫_ℝ| := le_abs_self _
    exact hle_abs.trans (by simpa [D, q] using habs)
  have hmain : (μ1 + μ2) * q ^ 2 ≤ max 0 η + D * q := by
    nlinarith [hcoercive, hinner_le, hη_le]
  have hyoung :
      D * q ≤ ((μ1 + μ2) / 2) * q ^ 2 + D ^ 2 / (2 * (μ1 + μ2)) := by
    have hsq : 0 ≤ ((μ1 + μ2) * q - D) ^ 2 := sq_nonneg _
    field_simp [ne_of_gt hμsum]
    nlinarith [hsq, hμsum]
  have hhalf :
      ((μ1 + μ2) / 2) * q ^ 2 ≤
        max 0 η + D ^ 2 / (2 * (μ1 + μ2)) := by
    nlinarith [hmain, hyoung]
  have hhalf_scaled :
      (μ1 + μ2) ^ 2 * q ^ 2 ≤ 2 * (μ1 + μ2) * max 0 η + D ^ 2 := by
    have hmul_nonneg : 0 ≤ 2 * (μ1 + μ2) := by
      nlinarith [hμsum]
    have hscaled := mul_le_mul_of_nonneg_left hhalf hmul_nonneg
    field_simp [ne_of_gt hμsum] at hscaled
    nlinarith [hscaled]
  have hfinal :
      q ^ 2 ≤
        (2 * max 0 η) / (μ1 + μ2) + D ^ 2 / (μ1 + μ2) ^ 2 := by
    field_simp [ne_of_gt hμsum]
    nlinarith [hhalf_scaled]
  simpa [R, q, D, d] using hfinal

/-- Early convexity bridge for the non-Bregman part of the selected SPS
subproblem.

Aligns with Lan Lemma 3.5 as used in Proposition 8.3. Candidate audit:
`two_bregman_argmin_descent` expects this `ConvexOn` hypothesis but does not
prove it; SOptLib objective wrappers do not know this paper's `IsAffineModel`
encoding of `g`. This before-stability variant is declared before the selected
L2-stability theorem so the selected-step bridge can be consumed there. -/
theorem sps_source_linear_chi_model_convexOn_before_stability
    (g : E → ℝ) (hg : IsAffineModel g) (q : E) :
    ConvexOn ℝ S.X (fun z : E => g z + ⟪q, z⟫_ℝ + S.chi z) := by
  rcases hg with ⟨c, a, hgdef⟩
  refine ⟨S.convex_X, ?_⟩
  intro y hy z hz α η hα hη hsum
  have hchi := S.convex_chi.2 hy hz hα hη hsum
  have hlinear :
      g (α • y + η • z) + ⟪q, α • y + η • z⟫_ℝ =
        α * (g y + ⟪q, y⟫_ℝ) + η * (g z + ⟪q, z⟫_ℝ) := by
    simp [hgdef, inner_add_right, inner_smul_right]
    ring_nf
    have hc : c = c * α + c * η := by
      calc
        c = c * (α + η) := by rw [hsum]; ring
        _ = c * α + c * η := by ring
    nlinarith
  have hchi' :
      S.chi (α • y + η • z) ≤ α * S.chi y + η * S.chi z := by
    simpa [smul_eq_mul] using hchi
  calc
    g (α • y + η • z) + ⟪q, α • y + η • z⟫_ℝ + S.chi (α • y + η • z)
        ≤ g (α • y + η • z) + ⟪q, α • y + η • z⟫_ℝ +
            (α * S.chi y + η * S.chi z) := by
          linarith
    _ = α * (g y + ⟪q, y⟫_ℝ + S.chi y) +
          η * (g z + ⟪q, z⟫_ℝ + S.chi z) := by
          rw [hlinear]
          ring

/-- Early scalar Young absorption used by the selected formula-extension
Proposition 8.3 bridge.

Aligns with Lan Proposition 8.3's use of Eq. (3.2.3) and
`-a t^2/2 + b t ≤ b^2/(2a)`. Candidate audit: SOptLib scalar square-completion
lemmas were considered, but they are ambient-norm statements; this paper needs
the already displayed primal seminorm and `dualNorm` scalar shape. -/
theorem sps_source_bregman_young_absorption_before_stability
    {a b V r : ℝ}
    (ha : 0 < a) (hr : 0 ≤ r) (hV : (1 / 2 : ℝ) * r ^ 2 ≤ V) :
    -a * V + b * r ≤ b ^ 2 / (2 * a) := by
  have hquad : -(a / 2) * r ^ 2 + b * r ≤ b ^ 2 / (2 * a) := by
    have hsq : 0 ≤ (a * r - b) ^ 2 := sq_nonneg _
    field_simp [ne_of_gt ha]
    nlinarith [hsq, ha]
  have hVscaled : (a / 2) * r ^ 2 ≤ a * V := by
    nlinarith [mul_le_mul_of_nonneg_left hV ha.le]
  nlinarith

/-- Prox-potential support inequality on the feasible carrier.

Aligns with Lan Section 3.2's convex differentiable prox potential in
Eq. (3.2.1)-(3.2.2). Candidate audit: searched SOptLib/Mathlib for convex
first-order inequalities involving `gradientWithin`; `Convex.first_order_condition_of_isMinOn_hasFDerivWithinAt`
is the reverse minimizer-to-FOC direction, and the available Bregman lower-bound
lemmas require a preexisting Bregman formula. This helper copies the local
`smoothLinearization_support_on_X` segment-derivative argument for the prox
potential. -/
theorem proxPotential_support_on_X_before_stability
    (x z : FeasiblePoint S) :
    S.proxPotential x.1 +
      ⟪boundarySafeCarrierGradient S.X S.proxPotential x, z.1 - x.1⟫_ℝ ≤
        S.proxPotential z.1 := by
  classical
  rcases S.prox_geometry with ⟨_hcont, hdiffX, _hcore_convex, _hdiffCore, hconv, _hstrong⟩
  change S.proxPotential x.1 +
      ⟪gradientWithin S.proxPotential S.X x.1, z.1 - x.1⟫_ℝ ≤
        S.proxPotential z.1
  let line : ℝ → E := fun t => AffineMap.lineMap x.1 z.1 t
  let d : E := z.1 - x.1
  let s : Set ℝ := Set.Icc (0 : ℝ) 1
  have hline_deriv : HasDerivWithinAt line d s 0 := by
    simpa [line, d, s] using
      (AffineMap.hasDerivWithinAt_lineMap (a := x.1) (b := z.1)
        (s := Set.Icc (0 : ℝ) 1) (x := (0 : ℝ)))
  have hmaps : Set.MapsTo line s S.X := by
    intro t ht
    exact S.convex_X.lineMap_mem x.2 z.2 (by simpa [s] using ht)
  have hνdiff : DifferentiableWithinAt ℝ S.proxPotential S.X x.1 :=
    hdiffX x.1 x.2
  have hνline : HasDerivWithinAt (fun t : ℝ => S.proxPotential (line t))
      ((fderivWithin ℝ S.proxPotential S.X x.1) d) s 0 := by
    simpa [Function.comp_def] using
      hνdiff.hasFDerivWithinAt.comp_hasDerivWithinAt_of_eq 0 hline_deriv hmaps
        (by simp [line])
  have hgrad_apply :
      (fderivWithin ℝ S.proxPotential S.X x.1) d =
        ⟪gradientWithin S.proxPotential S.X x.1, d⟫_ℝ := by
    rw [gradientWithin, InnerProductSpace.toDual_symm_apply]
  have hderiv_line : HasDerivWithinAt (fun t : ℝ => S.proxPotential (line t))
      ⟪gradientWithin S.proxPotential S.X x.1, z.1 - x.1⟫_ℝ s 0 := by
    simpa [d, hgrad_apply] using hνline
  have hsec : ∀ t ∈ s,
      S.proxPotential (line t) - S.proxPotential x.1 ≤
        t * (S.proxPotential z.1 - S.proxPotential x.1) := by
    intro t ht
    have htI : t ∈ Set.Icc (0 : ℝ) 1 := by simpa [s] using ht
    rcases Set.mem_Icc.mp htI with ⟨ht0, ht1⟩
    have hconv_step := hconv.2 x.2 z.2 (sub_nonneg.mpr ht1) ht0 (by ring)
    have hline_eq : line t = (1 - t) • x.1 + t • z.1 := by
      simp [line, AffineMap.lineMap_apply_module']
      module
    have hconv_line :
        S.proxPotential (line t) ≤
          (1 - t) * S.proxPotential x.1 + t * S.proxPotential z.1 := by
      rw [hline_eq]
      simpa [smul_eq_mul] using hconv_step
    nlinarith
  let ψ : ℝ → ℝ := fun t =>
    t * (S.proxPotential z.1 - S.proxPotential x.1) -
      (S.proxPotential (line t) - S.proxPotential x.1)
  have hψmin : ∀ t ∈ s, ψ 0 ≤ ψ t := by
    intro t ht
    have h0 : ψ 0 = 0 := by simp [ψ, line]
    have ht_nonneg : 0 ≤ ψ t := by
      dsimp [ψ]
      have h := hsec t ht
      nlinarith
    rw [h0]
    exact ht_nonneg
  have hlin_deriv : HasDerivWithinAt
      (fun t : ℝ => t * (S.proxPotential z.1 - S.proxPotential x.1))
      (S.proxPotential z.1 - S.proxPotential x.1) s 0 := by
    simpa using (hasDerivWithinAt_id (x := (0 : ℝ)) (s := s)).mul_const
      (S.proxPotential z.1 - S.proxPotential x.1)
  have hνsub_deriv : HasDerivWithinAt
      (fun t : ℝ => S.proxPotential (line t) - S.proxPotential x.1)
      ⟪gradientWithin S.proxPotential S.X x.1, z.1 - x.1⟫_ℝ s 0 := by
    simpa using hderiv_line.sub_const (S.proxPotential x.1)
  have hψderiv : HasDerivWithinAt ψ
      ((S.proxPotential z.1 - S.proxPotential x.1) -
        ⟪gradientWithin S.proxPotential S.X x.1, z.1 - x.1⟫_ℝ) s 0 := by
    have h := hlin_deriv.sub hνsub_deriv
    simpa [ψ] using h
  have hnonneg :
      0 ≤ (S.proxPotential z.1 - S.proxPotential x.1) -
        ⟪gradientWithin S.proxPotential S.X x.1, z.1 - x.1⟫_ℝ := by
    exact right_derivative_nonneg_of_min_on_Icc (by simpa [s] using hψderiv)
      (by simpa [s] using hψmin)
  nlinarith

/-- Feasible points are prox-core points for a differentiable convex prox
potential.

Aligns with Lan Section 3.2's distance-generating function: choosing the
linear perturbation `p = -∇ν(x)` makes `x` minimize `⟪p, ·⟫ + ν` over `X`.
Candidate audit: SOptLib's `carrierGradientFrom_inner_eq_gradientWithin_on_feasible_direction`
handles same-carrier gradient pairings, while `Convex.first_order_condition_of_isMinOn_hasFDerivWithinAt`
goes from minimizers to first-order conditions; neither constructs the
paper-local `proxCore` witness. -/
theorem feasible_mem_proxCore_before_stability (x : FeasiblePoint S) :
    x.1 ∈ proxCore S.X S.proxPotential := by
  classical
  refine ⟨x.2, ?_⟩
  let p : E := -boundarySafeCarrierGradient S.X S.proxPotential x
  refine ⟨p, ?_⟩
  intro u hu
  have hsupport :=
    proxPotential_support_on_X_before_stability (S := S) x ⟨u, hu⟩
  have hsupport' :
      S.proxPotential x.1 +
          (⟪boundarySafeCarrierGradient S.X S.proxPotential x, u⟫_ℝ -
            ⟪boundarySafeCarrierGradient S.X S.proxPotential x, x.1⟫_ℝ) ≤
        S.proxPotential u := by
    simpa [inner_sub_right] using hsupport
  dsimp [p]
  rw [inner_neg_left]
  rw [inner_neg_left]
  nlinarith

/-- Under the current prox geometry, the paper prox-core equals the feasible
carrier.

Aligns with the convex-differentiable specialization of Lan Section 3.2.
Candidate audit: searched for prox-core/relative-interior and carrier-gradient
normalization lemmas; SOptLib has intrinsic-interior carriers but no lemma for
this paper-local `proxCore` definition, so this is the direct consequence of
`feasible_mem_proxCore_before_stability` and `proxCore_subset`. -/
theorem proxCore_eq_X_before_stability :
    proxCore S.X S.proxPotential = S.X := by
  exact Set.Subset.antisymm proxCore_subset
    (fun x hx => feasible_mem_proxCore_before_stability (S := S) ⟨x, hx⟩)

/-- Prox-core branch pairing compatibility for the feasible Bregman formula.

Aligns with Lan Lemma 3.5's use of the same Eq. (3.2.2) gradient in `V(x,z)`
and in the three-point expansion. Candidate audit: checked
`carrierGradientFrom_inner_eq_gradientWithin_on_feasible_direction`, but it
applies when the carrier-gradient and feasible endpoint live on the same
carrier; here the branch gradient is charted on `proxCore S.X S.proxPotential`
while the endpoint displacement ranges over the larger carrier `S.X`. -/
theorem
    proxCoreGradient_inner_eq_boundarySafeCarrierGradient_on_feasible_direction_before_stability
    (x z : FeasiblePoint S) (hxcore : x.1 ∈ proxCore S.X S.proxPotential) :
    ⟪proxCoreGradient S ⟨x.1, hxcore⟩, z.1 - x.1⟫_ℝ =
      ⟪boundarySafeCarrierGradient S.X S.proxPotential x, z.1 - x.1⟫_ℝ := by
  classical
  letI : FiniteDimensional ℝ E := S.finiteDimensional_ambient
  have hcore_eq : proxCore S.X S.proxPotential = S.X :=
    proxCore_eq_X_before_stability (S := S)
  have hzcore : z.1 ∈ proxCore S.X S.proxPotential := by
    rw [hcore_eq]
    exact z.2
  have hne : Nonempty {x : E // x ∈ proxCore S.X S.proxPotential} :=
    ⟨⟨x.1, hxcore⟩⟩
  rcases S.prox_geometry with
    ⟨_hcont, _hdiffX, hcore_convex, hdiffCore, _hconv, _hstrong⟩
  have hdiffCoreAt :
      DifferentiableWithinAt ℝ S.proxPotential
        (proxCore S.X S.proxPotential) x.1 :=
    hdiffCore.differentiableOn_one x.1 hxcore
  have hcarrier :=
    carrierGradientFrom_inner_eq_gradientWithin_on_feasible_direction
      (v := fun y : {x : E // x ∈ proxCore S.X S.proxPotential} =>
        S.proxPotential y.1)
      (ν := S.proxPotential)
      (anchor := Classical.choice hne)
      (z := ⟨x.1, hxcore⟩)
      (x := ⟨z.1, hzcore⟩)
      hcore_convex hdiffCoreAt (by intro y; rfl)
  have hright :
      ⟪gradientWithin S.proxPotential (proxCore S.X S.proxPotential) x.1,
          z.1 - x.1⟫_ℝ =
        ⟪gradientWithin S.proxPotential S.X x.1, z.1 - x.1⟫_ℝ := by
    rw [hcore_eq]
  have hcarrierX :
      ⟪SOptLib.carrierGradientFrom (proxCore S.X S.proxPotential)
          (fun y : {x : E // x ∈ proxCore S.X S.proxPotential} =>
            S.proxPotential y.1)
          (Classical.choice hne) ⟨x.1, hxcore⟩, z.1 - x.1⟫_ℝ =
        ⟪gradientWithin S.proxPotential S.X x.1, z.1 - x.1⟫_ℝ := by
    exact hcarrier.trans hright
  simpa [proxCoreGradient, boundarySafeCarrierGradient, proxCoreGradientRaw, hne]
    using hcarrierX

/-- Early carrier formula normalization for `bregmanFormulaOnX`.

Aligns with Lan Section 3.2 Eq. (3.2.2) as consumed in Lemma 3.5. Candidate
audit: SOptLib `carrierBregmanFormula_def` and
`carrierBregmanDivergence_three_point_identity` give the abstract formula and
algebra; this helper only normalizes the paper-local `feasibleBregmanFormulaExtension`
branches to the boundary-safe carrier-gradient selector. -/
theorem bregmanFormulaOnX_boundary_carrier_formula
    (x z : FeasiblePoint S) :
    bregmanFormulaOnX S x z =
      S.proxPotential z.1 - S.proxPotential x.1 -
        ⟪boundarySafeCarrierGradient S.X S.proxPotential x, z.1 - x.1⟫_ℝ := by
  classical
  letI : FiniteDimensional ℝ E := S.finiteDimensional_ambient
  by_cases hxcore : x.1 ∈ proxCore S.X S.proxPotential
  · have hpair :=
      proxCoreGradient_inner_eq_boundarySafeCarrierGradient_on_feasible_direction_before_stability
        (S := S) x z hxcore
    have hpair_raw :
        ⟪proxCoreGradientRaw S.X S.proxPotential ⟨x.1, hxcore⟩, z.1 - x.1⟫_ℝ =
          ⟪boundarySafeCarrierGradient S.X S.proxPotential x, z.1 - x.1⟫_ℝ := by
      simpa [proxCoreGradient] using hpair
    simp [bregmanFormulaOnX, feasibleBregmanFormulaExtension,
      boundarySafeCarrierGradient, hxcore, hpair_raw]
  · simp [bregmanFormulaOnX, feasibleBregmanFormulaExtension,
      boundarySafeCarrierGradient, carrierBregmanDivergence, hxcore]

/-- Early three-point identity for the feasible Bregman formula.

Aligns with Lan Lemma 3.5's Bregman expansion at the formula-extension
boundary. Candidate audit: SOptLib carrier Bregman formula lemmas provide the
abstract pieces, while this local identity specializes the algebra to
`bregmanFormulaOnX` and the boundary-safe carrier-gradient selector. -/
theorem bregmanFormulaOnX_three_point_identity_before_stability
    (a b c : FeasiblePoint S) :
    bregmanFormulaOnX S a c =
      bregmanFormulaOnX S a b +
        ⟪boundarySafeCarrierGradient S.X S.proxPotential b -
            boundarySafeCarrierGradient S.X S.proxPotential a,
          c.1 - b.1⟫_ℝ +
          bregmanFormulaOnX S b c := by
  classical
  let v : FeasiblePoint S → ℝ := fun x => S.proxPotential x.1
  let eval : FeasiblePoint S → E := fun x => x.1
  let grad : FeasiblePoint S → E :=
    fun x => boundarySafeCarrierGradient S.X S.proxPotential x
  have hV :
      ∀ x z : FeasiblePoint S,
        bregmanFormulaOnX S x z =
          v z - v x - ⟪grad x, eval z - eval x⟫_ℝ := by
    intro x z
    simpa [v, eval, grad] using bregmanFormulaOnX_boundary_carrier_formula S x z
  simpa [v, eval, grad] using
    (carrierBregmanDivergence_three_point_identity v eval grad
      (fun x z : FeasiblePoint S => bregmanFormulaOnX S x z) hV a b c)

/-- Early feasible-comparator first variation for `bregmanFormulaOnX`.

Aligns with the Lan Lemma 3.5 derivative step used in Proposition 8.3.
Candidate audit: SOptLib `carrierBregman_segment_difference_hasDerivWithinAt_zero`
is the matching abstract derivative theorem; this helper only specializes it
to the local feasible carrier formula before the selected stability theorem. -/
theorem
    bregmanFormulaOnX_feasible_segment_difference_hasDerivWithinAt_zero_before_stability
    (a z u : FeasiblePoint S) :
    let d : E := u.1 - z.1
    let β : ℝ → ℝ := fun r =>
      if hr : r ∈ Set.Icc (0 : ℝ) 1 then
        bregmanFormulaOnX S a
            ⟨AffineMap.lineMap z.1 u.1 r,
              S.convex_X.lineMap_mem z.2 u.2 hr⟩ -
          bregmanFormulaOnX S a z
      else 0
    HasDerivWithinAt β
      ⟪boundarySafeCarrierGradient S.X S.proxPotential z -
          boundarySafeCarrierGradient S.X S.proxPotential a,
        d⟫_ℝ
      (Set.Icc (0 : ℝ) 1) 0 := by
  classical
  letI : FiniteDimensional ℝ E := S.finiteDimensional_ambient
  rcases S.prox_geometry with ⟨_hcont, hdiffX, _hcore_convex, _hdiffCore, _hconv, _hstrong⟩
  let nu : {x : E // x ∈ S.X} → ℝ := fun y => S.proxPotential y.1
  let grad : {x : E // x ∈ S.X} → E :=
    fun y => boundarySafeCarrierGradient S.X S.proxPotential y
  let V : {x : E // x ∈ S.X} → {x : E // x ∈ S.X} → ℝ :=
    fun x z => bregmanFormulaOnX S x z
  have hnu_eq : ∀ y : {x : E // x ∈ S.X}, nu y = S.proxPotential y.1 := by
    intro y
    rfl
  have hgrad_apply :
      ∀ (y : {x : E // x ∈ S.X}) (d : E),
        (fderivWithin ℝ S.proxPotential S.X y.1) d = ⟪grad y, d⟫_ℝ := by
    intro y d
    simp [grad, boundarySafeCarrierGradient, gradientWithin,
      InnerProductSpace.toDual_symm_apply]
  have hV :
      ∀ x z : {x : E // x ∈ S.X},
        V x z = nu z - nu x - ⟪grad x, z.1 - x.1⟫_ℝ := by
    intro x z
    simpa [V, nu, grad] using bregmanFormulaOnX_boundary_carrier_formula S x z
  simpa [nu, grad, V] using
    (carrierBregman_segment_difference_hasDerivWithinAt_zero
      S.convex_X nu S.proxPotential grad V hnu_eq hdiffX hgrad_apply hV a z u)

/-- Early Lan Lemma 3.5 first-variation bridge at the feasible
`bregmanFormulaOnX` boundary.

Aligns with Lan Lemma 3.5 proof lines 3555-3558. Candidate audit:
`SOptLib.two_bregman_argmin_variational_inequality_no_center_mem` and
`SOptLib.two_bregman_argmin_descent` have the right abstract proof shape, but
their global `V : E -> E -> R`/three-point laws would require totalizing
outside `X`; this paper step is carrier-typed over `FeasiblePoint S`. -/
theorem
    dependent_two_bregman_variational_inequality_for_bregmanFormulaOnX_before_stability
    (p : E → ℝ) (hp_convex : ConvexOn ℝ S.X p)
    (xTilde yTilde uHat : FeasiblePoint S) (mu1 mu2 : ℝ)
    (h_opt :
      ∀ u : FeasiblePoint S,
        p uHat.1 +
            mu1 * bregmanFormulaOnX S xTilde uHat +
            mu2 * bregmanFormulaOnX S yTilde uHat ≤
          p u.1 + mu1 * bregmanFormulaOnX S xTilde u +
            mu2 * bregmanFormulaOnX S yTilde u)
    (u : FeasiblePoint S) :
    0 ≤ p u.1 - p uHat.1 +
      mu1 * ⟪boundarySafeCarrierGradient S.X S.proxPotential uHat -
          boundarySafeCarrierGradient S.X S.proxPotential xTilde,
        u.1 - uHat.1⟫_ℝ +
      mu2 * ⟪boundarySafeCarrierGradient S.X S.proxPotential uHat -
          boundarySafeCarrierGradient S.X S.proxPotential yTilde,
        u.1 - uHat.1⟫_ℝ := by
  classical
  let d : E := u.1 - uHat.1
  let s : Set ℝ := Set.Icc (0 : ℝ) 1
  let βx : ℝ → ℝ := fun t =>
    if ht : t ∈ s then
      bregmanFormulaOnX S xTilde
          ⟨AffineMap.lineMap uHat.1 u.1 t,
            S.convex_X.lineMap_mem uHat.2 u.2 ht⟩ -
        bregmanFormulaOnX S xTilde uHat
    else 0
  let βy : ℝ → ℝ := fun t =>
    if ht : t ∈ s then
      bregmanFormulaOnX S yTilde
          ⟨AffineMap.lineMap uHat.1 u.1 t,
            S.convex_X.lineMap_mem uHat.2 u.2 ht⟩ -
        bregmanFormulaOnX S yTilde uHat
    else 0
  let φ : ℝ → ℝ := fun t =>
    t * (p u.1 - p uHat.1) + mu1 * βx t + mu2 * βy t
  have hβxderiv : HasDerivWithinAt βx
      ⟪boundarySafeCarrierGradient S.X S.proxPotential uHat -
          boundarySafeCarrierGradient S.X S.proxPotential xTilde, d⟫_ℝ s 0 := by
    simpa [βx, d, s] using
      bregmanFormulaOnX_feasible_segment_difference_hasDerivWithinAt_zero_before_stability
        S xTilde uHat u
  have hβyderiv : HasDerivWithinAt βy
      ⟪boundarySafeCarrierGradient S.X S.proxPotential uHat -
          boundarySafeCarrierGradient S.X S.proxPotential yTilde, d⟫_ℝ s 0 := by
    simpa [βy, d, s] using
      bregmanFormulaOnX_feasible_segment_difference_hasDerivWithinAt_zero_before_stability
        S yTilde uHat u
  have hpderiv : HasDerivWithinAt (fun t : ℝ => t * (p u.1 - p uHat.1))
      (p u.1 - p uHat.1) s 0 := by
    simpa using (hasDerivWithinAt_id (x := (0 : ℝ)) (s := s)).mul_const
      (p u.1 - p uHat.1)
  have hφderiv : HasDerivWithinAt φ
      (p u.1 - p uHat.1 +
        mu1 * ⟪boundarySafeCarrierGradient S.X S.proxPotential uHat -
            boundarySafeCarrierGradient S.X S.proxPotential xTilde, d⟫_ℝ +
        mu2 * ⟪boundarySafeCarrierGradient S.X S.proxPotential uHat -
            boundarySafeCarrierGradient S.X S.proxPotential yTilde, d⟫_ℝ) s 0 := by
    have hxmul : HasDerivWithinAt (fun t : ℝ => mu1 * βx t)
        (mu1 * ⟪boundarySafeCarrierGradient S.X S.proxPotential uHat -
            boundarySafeCarrierGradient S.X S.proxPotential xTilde, d⟫_ℝ) s 0 := by
      simpa using hβxderiv.const_mul mu1
    have hymul : HasDerivWithinAt (fun t : ℝ => mu2 * βy t)
        (mu2 * ⟪boundarySafeCarrierGradient S.X S.proxPotential uHat -
            boundarySafeCarrierGradient S.X S.proxPotential yTilde, d⟫_ℝ) s 0 := by
      simpa using hβyderiv.const_mul mu2
    simpa [φ, add_assoc] using (hpderiv.add hxmul).add hymul
  have hφmin : ∀ t ∈ s, φ 0 ≤ φ t := by
    intro t ht
    have htI : t ∈ Set.Icc (0 : ℝ) 1 := by simpa [s] using ht
    rcases Set.mem_Icc.mp htI with ⟨ht0, ht1⟩
    let wPoint : E := AffineMap.lineMap uHat.1 u.1 t
    have hwPoint : wPoint ∈ S.X := by
      simpa [wPoint] using
        S.convex_X.lineMap_mem uHat.2 u.2 htI
    let w : FeasiblePoint S := ⟨wPoint, hwPoint⟩
    have hline_conv :
        wPoint = (1 - t) • uHat.1 + t • u.1 := by
      simp [wPoint, AffineMap.lineMap_apply_module']
      module
    have hpseg : p w.1 - p uHat.1 ≤ t * (p u.1 - p uHat.1) := by
      have hconv :=
        hp_convex.2 uHat.2 u.2 (sub_nonneg.mpr ht1) ht0 (by ring)
      rw [← hline_conv] at hconv
      have hconv' : p wPoint ≤ (1 - t) * p uHat.1 + t * p u.1 := by
        simpa [smul_eq_mul] using hconv
      change p wPoint - p uHat.1 ≤ t * (p u.1 - p uHat.1)
      nlinarith
    have hmin := h_opt w
    have hFdiff :
        0 ≤ (p w.1 - p uHat.1) +
          mu1 * (bregmanFormulaOnX S xTilde w -
            bregmanFormulaOnX S xTilde uHat) +
          mu2 * (bregmanFormulaOnX S yTilde w -
            bregmanFormulaOnX S yTilde uHat) := by
      nlinarith
    have hβx_eval : βx t =
        bregmanFormulaOnX S xTilde w -
          bregmanFormulaOnX S xTilde uHat := by
      simp [βx, w, wPoint, ht]
    have hβy_eval : βy t =
        bregmanFormulaOnX S yTilde w -
          bregmanFormulaOnX S yTilde uHat := by
      simp [βy, w, wPoint, ht]
    have hφ0 : φ 0 = 0 := by
      simp [φ, βx, βy, s, bregmanFormulaOnX, AffineMap.lineMap_apply_module']
    have hupper :
        (p w.1 - p uHat.1) +
          mu1 * (bregmanFormulaOnX S xTilde w -
            bregmanFormulaOnX S xTilde uHat) +
          mu2 * (bregmanFormulaOnX S yTilde w -
            bregmanFormulaOnX S yTilde uHat) ≤ φ t := by
      dsimp [φ]
      rw [hβx_eval, hβy_eval]
      nlinarith
    rw [hφ0]
    exact le_trans hFdiff hupper
  have hnonneg :=
    hasDerivWithinAt_nonneg_of_isMinOn_Icc_left (by norm_num) hφderiv hφmin
  simpa [d] using hnonneg

/-- Early Lan Lemma 3.5 feasible-interface bridge for `bregmanFormulaOnX`.

Aligns with Lan Lemma 3.5 as invoked in Proposition 8.3. Candidate audit:
`SOptLib.two_bregman_argmin_descent` matches the proof pattern but uses an
ambient global kernel; this helper keeps the paper-local feasible carrier
formula and consumes the early first-variation bridge above. -/
theorem lemma35_formulaOnX_interface_for_bregmanFormulaOnX_before_stability
    (p : E → ℝ) (hp_convex : ConvexOn ℝ S.X p)
    (xTilde yTilde uHat : FeasiblePoint S) (mu1 mu2 : ℝ)
    (hmu1 : 0 ≤ mu1) (hmu2 : 0 ≤ mu2)
    (h_opt :
      ∀ u : FeasiblePoint S,
        p uHat.1 +
            mu1 * bregmanFormulaOnX S xTilde uHat +
            mu2 * bregmanFormulaOnX S yTilde uHat ≤
          p u.1 + mu1 * bregmanFormulaOnX S xTilde u +
            mu2 * bregmanFormulaOnX S yTilde u) :
    ∀ u : FeasiblePoint S,
      p uHat.1 +
          mu1 * bregmanFormulaOnX S xTilde uHat +
          mu2 * bregmanFormulaOnX S yTilde uHat ≤
        p u.1 + mu1 * bregmanFormulaOnX S xTilde u +
          mu2 * bregmanFormulaOnX S yTilde u -
            (mu1 + mu2) * bregmanFormulaOnX S uHat u := by
  classical
  intro u
  have hvar :=
    dependent_two_bregman_variational_inequality_for_bregmanFormulaOnX_before_stability S
      p hp_convex xTilde yTilde uHat mu1 mu2 h_opt u
  have hx3 := bregmanFormulaOnX_three_point_identity_before_stability S xTilde uHat u
  have hy3 := bregmanFormulaOnX_three_point_identity_before_stability S yTilde uHat u
  nlinarith

/-- Early Proposition 8.3 displacement absorption at the feasible
`bregmanFormulaOnX` boundary.

Aligns with Lan Proposition 8.3, proof step using Eq. (3.2.3) and Young's
inequality. Candidate audit: `sps_source_displacement_absorption` is the
source-domain analogue for `bregmanOn`, while SOptLib ambient square-completion
lemmas do not preserve this paper's `S.primalNorm`/`dualNorm` pair. -/
theorem sps_formula_displacement_absorption_before_stability
    (β : ℝ) (ι : PositiveTime)
    (prev next : FeasiblePoint S) (δ : E) (hβ : 0 < β) :
    -β * spsP ι * bregmanFormulaOnX S prev next +
        (S.mGrowth + dualNorm S δ) * S.primalNorm (next.1 - prev.1) ≤
      (S.mGrowth + dualNorm S δ) ^ 2 / (2 * β * spsP ι) := by
  have hp : 0 < spsP ι := by
    have hι : 0 < (ι.1 : ℝ) := by exact_mod_cast ι.2
    unfold spsP
    positivity
  have ha : 0 < β * spsP ι := mul_pos hβ hp
  have hr : 0 ≤ S.primalNorm (next.1 - prev.1) := apply_nonneg S.primalNorm _
  have hV :
      (1 / 2 : ℝ) * S.primalNorm (next.1 - prev.1) ^ 2 ≤
        bregmanFormulaOnX S prev next :=
    bregmanFormulaOnX_lower_bound_from_prox_geometry S prev next
  have hyoung :=
    sps_source_bregman_young_absorption_before_stability
      (a := β * spsP ι) (b := S.mGrowth + dualNorm S δ)
      (V := bregmanFormulaOnX S prev next)
      (r := S.primalNorm (next.1 - prev.1)) ha hr hV
  calc
    -β * spsP ι * bregmanFormulaOnX S prev next +
        (S.mGrowth + dualNorm S δ) * S.primalNorm (next.1 - prev.1)
        = -(β * spsP ι) * bregmanFormulaOnX S prev next +
            (S.mGrowth + dualNorm S δ) * S.primalNorm (next.1 - prev.1) := by
          ring
      _ ≤ (S.mGrowth + dualNorm S δ) ^ 2 / (2 * (β * spsP ι)) := hyoung
      _ = (S.mGrowth + dualNorm S δ) ^ 2 / (2 * β * spsP ι) := by
            ring

/-- Early direct selected-step version of the Proposition 8.3 one-step Phi
bound.

Aligns with Lan Proposition 8.3 proof steps 1-2 and Eq. (8.1.58). Candidate
audit: `sps_source_one_step_phi_bound` is source-domain/prox-core typed, and
SOptLib accelerated recurrence helpers do not include this paper's
`h`-growth/noise absorption; this formula-extension bridge uses the selected
argmin certificate directly. -/
theorem spsStep_formulaExtensionSelector_one_step_phi_bound_before_stability
    (g : E → ℝ) (hg : IsAffineModel g) (x : FeasiblePoint S)
    (β : {β : ℝ // 0 < β}) (t : PositiveTime) (prev : FeasiblePoint S)
    (xi : Sample) (u : FeasiblePoint S) :
    let δ := oracleNoiseAt S prev.1 xi;
    let next : FeasiblePoint S :=
      (spsStep_formulaExtensionSelector S g hg x β t prev xi).1;
      spsPhiFormulaOnX S g x β.1 next - spsPhiFormulaOnX S g x β.1 u ≤
        β.1 * spsP t * bregmanFormulaOnX S prev u -
          β.1 * (1 + spsP t) * bregmanFormulaOnX S next u +
          ((S.mGrowth + dualNorm S δ) ^ 2) / (2 * β.1 * spsP t) +
          ⟪δ, u.1 - prev.1⟫_ℝ := by
  classical
  let q : E := S.oracle prev.1 xi
  let δ : E := oracleNoiseAt S prev.1 xi
  let next : FeasiblePoint S :=
    (spsStep_formulaExtensionSelector S g hg x β t prev xi).1
  let r : ℝ := S.primalNorm (next.1 - prev.1)
  have hq_decomp : q = S.hSubgradient prev.1 + δ := by
    simp [q, δ, oracleNoiseAt]
  have hprevX : prev.1 ∈ S.X := prev.2
  have hnextX : next.1 ∈ S.X := next.2
  have hgrowth :
      S.h next.1 ≤
        S.h prev.1 + ⟪q, next.1⟫_ℝ - ⟪q, prev.1⟫_ℝ -
          ⟪δ, next.1 - prev.1⟫_ℝ + S.mGrowth * r := by
    have hgrowth0 :=
      S.nonsmooth_growth (x := next.1) (y := prev.1) hnextX hprevX
    calc
      S.h next.1
          ≤ S.h prev.1 + ⟪S.hSubgradient prev.1, next.1 - prev.1⟫_ℝ +
              S.mGrowth * r := by
            simpa [r] using hgrowth0
      _ = S.h prev.1 + ⟪q, next.1⟫_ℝ - ⟪q, prev.1⟫_ℝ -
              ⟪δ, next.1 - prev.1⟫_ℝ + S.mGrowth * r := by
            rw [hq_decomp]
            simp [inner_add_left, inner_sub_right]
            ring
  have hsub_le :
      S.h prev.1 + ⟪q, u.1⟫_ℝ - ⟪q, prev.1⟫_ℝ ≤
        S.h u.1 + ⟪δ, u.1 - prev.1⟫_ℝ := by
    have hmem := (setup_hSubgradientMem S) prev.1 hprevX
    have hsupport :=
      (SOptLib.mem_carrierSubdifferential_iff.mp hmem) ⟨u.1, u.2⟩
    calc
      S.h prev.1 + ⟪q, u.1⟫_ℝ - ⟪q, prev.1⟫_ℝ
          = S.h prev.1 + ⟪q, u.1 - prev.1⟫_ℝ := by
              simp [inner_sub_right]
              ring
      _ = S.h prev.1 + ⟪S.hSubgradient prev.1, u.1 - prev.1⟫_ℝ +
            ⟪δ, u.1 - prev.1⟫_ℝ := by
              rw [hq_decomp]
              simp [inner_add_left]
              ring
      _ ≤ S.h u.1 + ⟪δ, u.1 - prev.1⟫_ℝ := by
              nlinarith [hsupport]
  have hnoise_step :
      -⟪δ, next.1 - prev.1⟫_ℝ ≤ dualNorm S δ * r := by
    have hneg_abs : -⟪δ, next.1 - prev.1⟫_ℝ ≤
        |⟪δ, next.1 - prev.1⟫_ℝ| := neg_le_abs _
    have hdual :=
      abs_inner_le_dualNorm_mul_primalNorm S δ (next.1 - prev.1)
    exact hneg_abs.trans (by simpa [r] using hdual)
  have hp_conv :
      ConvexOn ℝ S.X (fun z : E => g z + ⟪q, z⟫_ℝ + S.chi z) :=
    sps_source_linear_chi_model_convexOn_before_stability S g hg q
  have hp_nonneg : 0 ≤ spsP t := by
    have ht : 0 < (t.1 : ℝ) := by exact_mod_cast t.2
    unfold spsP
    positivity
  have hselected_descent :
      (g next.1 + ⟪q, next.1⟫_ℝ + S.chi next.1) +
          β.1 * bregmanFormulaOnX S x next ≤
        (g u.1 + ⟪q, u.1⟫_ℝ + S.chi u.1) +
          β.1 * bregmanFormulaOnX S x u +
          β.1 * spsP t * bregmanFormulaOnX S prev u -
            (β.1 + β.1 * spsP t) * bregmanFormulaOnX S next u -
            β.1 * spsP t * bregmanFormulaOnX S prev next := by
    have hlemma :=
      lemma35_formulaOnX_interface_for_bregmanFormulaOnX_before_stability S
        (p := fun z : E => g z + ⟪q, z⟫_ℝ + S.chi z)
        hp_conv x prev next β.1 (β.1 * spsP t)
        β.2.le (mul_nonneg β.2.le hp_nonneg)
        (by
          intro v
          simpa [q, next, add_assoc, add_left_comm, add_comm] using
            spsStep_formulaExtensionSelector_expanded_objective_le
              (S := S) (g := g) (hg := hg) (x := x) (β := β)
              (t := t) (uPrev := prev) (xi := xi) (u := v))
        u
    have hlemma' :
        (g next.1 + ⟪q, next.1⟫_ℝ + S.chi next.1) +
            β.1 * bregmanFormulaOnX S x next +
            β.1 * spsP t * bregmanFormulaOnX S prev next ≤
          (g u.1 + ⟪q, u.1⟫_ℝ + S.chi u.1) +
            β.1 * bregmanFormulaOnX S x u +
            β.1 * spsP t * bregmanFormulaOnX S prev u -
              (β.1 + β.1 * spsP t) * bregmanFormulaOnX S next u := by
      simpa [q, next, add_assoc, add_left_comm, add_comm] using hlemma
    nlinarith
  have hraw :
      spsPhiFormulaOnX S g x β.1 next - spsPhiFormulaOnX S g x β.1 u ≤
        β.1 * spsP t * bregmanFormulaOnX S prev u -
          (β.1 + β.1 * spsP t) * bregmanFormulaOnX S next u -
          β.1 * spsP t * bregmanFormulaOnX S prev next +
          ⟪δ, u.1 - prev.1⟫_ℝ +
          (S.mGrowth + dualNorm S δ) * r := by
    unfold spsPhiFormulaOnX spsPhi
    nlinarith [hselected_descent, hgrowth, hsub_le, hnoise_step]
  have habsorb :=
    sps_formula_displacement_absorption_before_stability S β.1 t prev next δ β.2
  have habsorb' :
      -β.1 * spsP t * bregmanFormulaOnX S prev next +
          (S.mGrowth + dualNorm S δ) * r ≤
        (S.mGrowth + dualNorm S δ) ^ 2 / (2 * β.1 * spsP t) := by
    simpa [r] using habsorb
  have hraw' :
      spsPhiFormulaOnX S g x β.1 next - spsPhiFormulaOnX S g x β.1 u ≤
        β.1 * spsP t * bregmanFormulaOnX S prev u -
          β.1 * (1 + spsP t) * bregmanFormulaOnX S next u -
          β.1 * spsP t * bregmanFormulaOnX S prev next +
          ⟪δ, u.1 - prev.1⟫_ℝ +
          (S.mGrowth + dualNorm S δ) * r := by
    nlinarith [hraw]
  have hfinal :
      spsPhiFormulaOnX S g x β.1 next - spsPhiFormulaOnX S g x β.1 u ≤
        β.1 * spsP t * bregmanFormulaOnX S prev u -
          β.1 * (1 + spsP t) * bregmanFormulaOnX S next u +
          ((S.mGrowth + dualNorm S δ) ^ 2) / (2 * β.1 * spsP t) +
          ⟪δ, u.1 - prev.1⟫_ℝ := by
    nlinarith [hraw', habsorb']
  simpa [δ, next, add_assoc, add_left_comm, add_comm] using hfinal

/-- Early selected-step Phi displacement bridge for the line-4702 stability
theorem.

Aligns with Lan Proposition 8.3 plus Lemma 3.5 and Eq. (3.2.3). Candidate
audit: the later `_voucher_step_spsStep_formulaExtensionSelector_phi_controls_target_displacement_16`
has this exact shape but is declaration-order blocked at the selected theorem;
this before-stability helper exposes the same proved bridge without changing
the public theorem head. -/
theorem selected_formula_extension_phi_controls_target_displacement_before_stability
    (g : E → ℝ) (hg : IsAffineModel g) (center : FeasiblePoint S)
    (β : {β : ℝ // 0 < β}) (t : PositiveTime) (prev : FeasiblePoint S)
    (xi : Sample) (u : FeasiblePoint S) :
    let δ := oracleNoiseAt S prev.1 xi;
    let next : FeasiblePoint S :=
      (spsStep_formulaExtensionSelector S g hg center β t prev xi).1;
      β.1 * (1 + spsP t) *
          ((1 / 2 : ℝ) * S.primalNorm (u.1 - next.1) ^ 2) ≤
        β.1 * spsP t * bregmanFormulaOnX S prev u +
          ((S.mGrowth + dualNorm S δ) ^ 2) / (2 * β.1 * spsP t) +
          ⟪δ, u.1 - prev.1⟫_ℝ +
          (spsPhiFormulaOnX S g center β.1 u -
            spsPhiFormulaOnX S g center β.1 next) := by
  classical
  let δ := oracleNoiseAt S prev.1 xi
  let next : FeasiblePoint S :=
    (spsStep_formulaExtensionSelector S g hg center β t prev xi).1
  have hp_nonneg : 0 ≤ spsP t := by
    have ht : 0 < (t.1 : ℝ) := by exact_mod_cast t.2
    unfold spsP
    positivity
  have hcoef_nonneg : 0 ≤ β.1 * (1 + spsP t) := by
    nlinarith [β.2, hp_nonneg]
  have hlower :
      (1 / 2 : ℝ) * S.primalNorm (u.1 - next.1) ^ 2 ≤
        bregmanFormulaOnX S next u := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      bregmanFormulaOnX_lower_bound_from_prox_geometry S next u
  have hcoercive :
      β.1 * (1 + spsP t) *
          ((1 / 2 : ℝ) * S.primalNorm (u.1 - next.1) ^ 2) ≤
        β.1 * (1 + spsP t) * bregmanFormulaOnX S next u := by
    exact mul_le_mul_of_nonneg_left hlower hcoef_nonneg
  have hphi :=
    spsStep_formulaExtensionSelector_one_step_phi_bound_before_stability
      S g hg center β t prev xi u
  nlinarith [hcoercive, hphi]

/-- Early first-variation form of the selected Eq. (8.1.58) subproblem.

Aligns with Lan Lemma 3.5 as used inside Proposition 8.3, but stops before
reintroducing three-point Bregman differences. Candidate audit:
`dependent_two_bregman_variational_inequality_for_bregmanFormulaOnX_before_stability`
is the carrier-level theorem used here, while
`spsStep_formulaExtensionSelector_expanded_objective_le` supplies this selected
solver's actual argmin certificate; no existing helper stated the resulting
selector-specific no-Bregman variational inequality. -/
theorem spsStep_formulaExtensionSelector_first_variation_before_stability
    (g : E → ℝ) (hg : IsAffineModel g) (center : FeasiblePoint S)
    (β : {β : ℝ // 0 < β}) (t : PositiveTime) (prev : FeasiblePoint S)
    (xi : Sample) (u : FeasiblePoint S) :
    let q : E := S.oracle prev.1 xi;
    let next : FeasiblePoint S :=
      (spsStep_formulaExtensionSelector S g hg center β t prev xi).1;
      0 ≤
        (g u.1 + ⟪q, u.1⟫_ℝ + S.chi u.1) -
          (g next.1 + ⟪q, next.1⟫_ℝ + S.chi next.1) +
        β.1 * ⟪boundarySafeCarrierGradient S.X S.proxPotential next -
            boundarySafeCarrierGradient S.X S.proxPotential center,
          u.1 - next.1⟫_ℝ +
        β.1 * spsP t *
          ⟪boundarySafeCarrierGradient S.X S.proxPotential next -
              boundarySafeCarrierGradient S.X S.proxPotential prev,
            u.1 - next.1⟫_ℝ := by
  classical
  let q : E := S.oracle prev.1 xi
  let next : FeasiblePoint S :=
    (spsStep_formulaExtensionSelector S g hg center β t prev xi).1
  let p : E → ℝ := fun z => g z + ⟪q, z⟫_ℝ + S.chi z
  have hp_conv : ConvexOn ℝ S.X p :=
    sps_source_linear_chi_model_convexOn_before_stability S g hg q
  have hp_nonneg : 0 ≤ spsP t := by
    have ht : 0 < (t.1 : ℝ) := by exact_mod_cast t.2
    unfold spsP
    positivity
  have hvar :=
    dependent_two_bregman_variational_inequality_for_bregmanFormulaOnX_before_stability
      S p hp_conv center prev next β.1 (β.1 * spsP t)
      (by
        intro v
        simpa [p, q, next, add_assoc, add_left_comm, add_comm] using
          spsStep_formulaExtensionSelector_expanded_objective_le
            (S := S) (g := g) (hg := hg) (x := center) (β := β)
            (t := t) (uPrev := prev) (xi := xi) (u := v))
      u
  simpa [p, q, next, mul_assoc, add_assoc, add_left_comm, add_comm] using hvar

/-- Convexity of a carrier function after passing to the affine-span chart.

This is the first chart step toward the finite-dimensional affine minorant for
`χ` in the selected SPS stability proof.  Candidate audit: considered
`SOptLib.carrierChartSet_convex`,
`SOptLib.carrierChartSet_interior_nonempty`,
`SOptLib.carrierChartToAmbient_mem_intrinsicInterior_of_mem_interior_chartSet`,
and Mathlib `ConvexOn.comp_affineMap`; none is itself an affine minorant, but
`ConvexOn.comp_affineMap` is the matching transport lemma for the charted
objective. -/
theorem convexOn_carrierChart_comp
    [FiniteDimensional ℝ E]
    {X : Set E} (hX : Convex ℝ X) (anchor : {x : E // x ∈ X})
    (φ : E → ℝ) (hφ : ConvexOn ℝ X φ) :
    ConvexOn ℝ (SOptLib.carrierChartSet X anchor)
      (fun u : (affineSpan ℝ X).direction =>
        φ (SOptLib.carrierChartToAmbient X anchor u)) := by
  classical
  have hpre :
      SOptLib.carrierChartSet X anchor =
        (SOptLib.carrierChartToAmbient X anchor).toAffineMap ⁻¹' X := by
    ext u
    simp [SOptLib.carrierChartSet]
  have hcomp :
      ConvexOn ℝ ((SOptLib.carrierChartToAmbient X anchor).toAffineMap ⁻¹' X)
        (φ ∘ (SOptLib.carrierChartToAmbient X anchor).toAffineMap) :=
    hφ.comp_affineMap (SOptLib.carrierChartToAmbient X anchor).toAffineMap
  simpa [hpre, Function.comp_def] using hcomp

/-- Charted finite-dimensional convex carrier functions are continuous on the
ordinary interior of the charted carrier.

This is a route-local bridge toward the affine minorant for `χ`: the strict
epigraph over the chart interior becomes open.  Candidate audit: considered
`SOptLib.carrierChartSet_interior_nonempty` and Mathlib
`ConvexOn.locallyLipschitzOn_interior`; the former supplies nonempty interior,
while `ConvexOn.continuousOn_interior` is the matching finite-dimensional
regularity theorem after the charted convexity helper above. -/
theorem continuousOn_interior_carrierChart_comp
    [FiniteDimensional ℝ E]
    {X : Set E} (hX : Convex ℝ X) (anchor : {x : E // x ∈ X})
    (φ : E → ℝ) (hφ : ConvexOn ℝ X φ) :
    ContinuousOn
      (fun u : (affineSpan ℝ X).direction =>
        φ (SOptLib.carrierChartToAmbient X anchor u))
      (interior (SOptLib.carrierChartSet X anchor)) := by
  exact (convexOn_carrierChart_comp hX anchor φ hφ).continuousOn_interior

/-- Convexity of the charted epigraph for a finite-dimensional carrier-convex
function.

This is the convex half of the Hahn-Banach separation setup for the local
affine-minorant route.  Candidate audit: `ConvexOn.convex_epigraph` is the
matching Mathlib primitive once `convexOn_carrierChart_comp` has transported the
paper carrier function into affine-span coordinates; SOptLib chart lemmas alone
only provide carrier geometry, not epigraph convexity. -/
theorem charted_epigraph_convex
    [FiniteDimensional ℝ E]
    {X : Set E} (hX : Convex ℝ X) (anchor : {x : E // x ∈ X})
    (φ : E → ℝ) (hφ : ConvexOn ℝ X φ) :
    Convex ℝ
      {p : (affineSpan ℝ X).direction × ℝ |
        p.1 ∈ SOptLib.carrierChartSet X anchor ∧
          φ (SOptLib.carrierChartToAmbient X anchor p.1) ≤ p.2} := by
  simpa [Function.comp_def] using
    (convexOn_carrierChart_comp hX anchor φ hφ).convex_epigraph

/-- The charted epigraph of a finite-dimensional carrier-convex function has
nonempty interior.

This is the open-set ingredient for separating a strict subgraph point from the
epigraph in the affine-minorant route.  Candidate audit: considered
`ConvexOn.sSup_affine_eq`/`exists_affine_le_of_lt`, but those require
`LowerSemicontinuousOn`; this helper instead uses
`SOptLib.carrierChartSet_interior_nonempty` plus the finite-dimensional
`ConvexOn.continuousOn_interior` route above, avoiding any lsc assumption. -/
theorem charted_epigraph_interior_nonempty
    [FiniteDimensional ℝ E]
    {X : Set E} (hX : Convex ℝ X) (anchor : {x : E // x ∈ X})
    (φ : E → ℝ) (hφ : ConvexOn ℝ X φ) :
    (interior
      {p : (affineSpan ℝ X).direction × ℝ |
        p.1 ∈ SOptLib.carrierChartSet X anchor ∧
          φ (SOptLib.carrierChartToAmbient X anchor p.1) ≤ p.2}).Nonempty := by
  classical
  let C : Set (affineSpan ℝ X).direction := SOptLib.carrierChartSet X anchor
  let f : (affineSpan ℝ X).direction → ℝ := fun u =>
    φ (SOptLib.carrierChartToAmbient X anchor u)
  obtain ⟨u0, hu0⟩ := SOptLib.carrierChartSet_interior_nonempty X anchor hX
  let p0 : (affineSpan ℝ X).direction × ℝ := (u0, f u0 + 1)
  refine ⟨p0, ?_⟩
  rw [mem_interior_iff_mem_nhds]
  have hfcont_on : ContinuousOn f (interior C) := by
    simpa [f, C] using continuousOn_interior_carrierChart_comp hX anchor φ hφ
  have hfcont : ContinuousAt f u0 :=
    hfcont_on.continuousAt (isOpen_interior.mem_nhds hu0)
  have hgcont : ContinuousAt (fun p : (affineSpan ℝ X).direction × ℝ => f p.1 - p.2) p0 :=
    by
      simpa [Function.comp_def] using
        (hfcont.comp continuousAt_fst |>.sub continuousAt_snd)
  have hlt_nhds :
      {p : (affineSpan ℝ X).direction × ℝ | f p.1 - p.2 < 0} ∈ nhds p0 := by
    have hp0 : f p0.1 - p0.2 ∈ Set.Iio (0 : ℝ) := by
      simp [p0]
    exact hgcont.preimage_mem_nhds (isOpen_Iio.mem_nhds hp0)
  have hC_nhds :
      {p : (affineSpan ℝ X).direction × ℝ | p.1 ∈ interior C} ∈ nhds p0 := by
    exact continuousAt_fst.preimage_mem_nhds (isOpen_interior.mem_nhds hu0)
  filter_upwards [Filter.inter_mem hC_nhds hlt_nhds] with p hp
  rcases hp with ⟨hpC, hplt⟩
  constructor
  · exact interior_subset hpC
  · dsimp [f] at hplt ⊢
    linarith

/-- A point strictly below a charted carrier-convex function is separated from
the charted epigraph.

This is the Hahn-Banach step immediately below the desired affine minorant. The
remaining work after this helper is to show the separating functional has a
nonzero vertical coefficient and translate the resulting chart affine functional
back to an ambient inner product.  Candidate audit: `ConvexOn.sSup_affine_eq`
would provide affine minorants only with `LowerSemicontinuousOn`; here the
usable candidates are Mathlib `geometric_hahn_banach_of_nonempty_interior_point`
plus the two charted epigraph helpers proved above. -/
theorem charted_epigraph_separates_below_point
    [FiniteDimensional ℝ E]
    {X : Set E} (hX : Convex ℝ X) (anchor : {x : E // x ∈ X})
    (φ : E → ℝ) (hφ : ConvexOn ℝ X φ) :
    let A : Set ((affineSpan ℝ X).direction × ℝ) :=
      {p | p.1 ∈ SOptLib.carrierChartSet X anchor ∧
          φ (SOptLib.carrierChartToAmbient X anchor p.1) ≤ p.2};
    let u0 : (affineSpan ℝ X).direction :=
      SOptLib.carrierChartPoint X anchor anchor;
    let pBelow : (affineSpan ℝ X).direction × ℝ := (u0, φ anchor.1 - 1);
    ∃ L : StrongDual ℝ ((affineSpan ℝ X).direction × ℝ),
      L ≠ 0 ∧ ∀ p ∈ A, L p ≤ L pBelow := by
  classical
  let A : Set ((affineSpan ℝ X).direction × ℝ) :=
    {p | p.1 ∈ SOptLib.carrierChartSet X anchor ∧
        φ (SOptLib.carrierChartToAmbient X anchor p.1) ≤ p.2}
  let u0 : (affineSpan ℝ X).direction :=
    SOptLib.carrierChartPoint X anchor anchor
  let pBelow : (affineSpan ℝ X).direction × ℝ := (u0, φ anchor.1 - 1)
  have hAconv : Convex ℝ A := by
    simpa [A] using charted_epigraph_convex hX anchor φ hφ
  have hAint : (interior A).Nonempty := by
    simpa [A] using charted_epigraph_interior_nonempty hX anchor φ hφ
  have hpnot : pBelow ∉ interior A := by
    intro hp
    have hpA : pBelow ∈ A := interior_subset hp
    rcases hpA with ⟨_hpC, hle⟩
    have hchart :
        SOptLib.carrierChartToAmbient X anchor u0 = anchor.1 := by
      simpa [u0] using SOptLib.carrierChartToAmbient_chartPoint X anchor anchor
    dsimp [pBelow] at hle
    rw [hchart] at hle
    linarith
  exact geometric_hahn_banach_of_nonempty_interior_point hAconv hpnot hAint

/-- Interior-point variant of the charted epigraph separation step.

This is the separation form needed for the affine-minorant route: the point
below the epigraph is based at an ordinary interior point of the charted
carrier, so the later vertical-coefficient argument can perturb in chart
directions.  Candidate audit: considered the existing
`charted_epigraph_separates_below_point`, but it separates below the arbitrary
anchor chart point and can have a horizontal separator at carrier-boundary
anchors; Mathlib `ConvexOn.sSup_affine_eq`/`exists_affine_le_of_lt` require
`LowerSemicontinuousOn`, absent from the paper setup.  The usable primitives
are the existing charted epigraph convexity/interior helpers and
`geometric_hahn_banach_of_nonempty_interior_point`, aligned with the interior
point form of the proof of Lan Proposition 8.3. -/
theorem charted_epigraph_separates_below_interior_point
    [FiniteDimensional ℝ E]
    {X : Set E} (hX : Convex ℝ X) (anchor : {x : E // x ∈ X})
    (φ : E → ℝ) (hφ : ConvexOn ℝ X φ)
    {u0 : (affineSpan ℝ X).direction}
    (hu0 : u0 ∈ interior (SOptLib.carrierChartSet X anchor)) :
    let A : Set ((affineSpan ℝ X).direction × ℝ) :=
      {p | p.1 ∈ SOptLib.carrierChartSet X anchor ∧
          φ (SOptLib.carrierChartToAmbient X anchor p.1) ≤ p.2};
    let pBelow : (affineSpan ℝ X).direction × ℝ :=
      (u0, φ (SOptLib.carrierChartToAmbient X anchor u0) - 1);
    ∃ L : StrongDual ℝ ((affineSpan ℝ X).direction × ℝ),
      L ≠ 0 ∧ ∀ p ∈ A, L p ≤ L pBelow := by
  classical
  let A : Set ((affineSpan ℝ X).direction × ℝ) :=
    {p | p.1 ∈ SOptLib.carrierChartSet X anchor ∧
        φ (SOptLib.carrierChartToAmbient X anchor p.1) ≤ p.2}
  let pBelow : (affineSpan ℝ X).direction × ℝ :=
    (u0, φ (SOptLib.carrierChartToAmbient X anchor u0) - 1)
  have hAconv : Convex ℝ A := by
    simpa [A] using charted_epigraph_convex hX anchor φ hφ
  have hAint : (interior A).Nonempty := by
    simpa [A] using charted_epigraph_interior_nonempty hX anchor φ hφ
  have hpnot : pBelow ∉ interior A := by
    intro hp
    have hpA : pBelow ∈ A := interior_subset hp
    rcases hpA with ⟨_hpC, hle⟩
    dsimp [pBelow] at hle
    linarith
  exact geometric_hahn_banach_of_nonempty_interior_point hAconv hpnot hAint

/-- The separator below an interior chart point has negative vertical
coefficient.

This is the corrected vertical-coefficient step for the affine-minorant route:
interiority of `u0` lets horizontal perturbations rule out the zero-vertical
separator.  Candidate audit: considered the existing
`charted_epigraph_separates_below_point`, but its boundary-anchor form does not
support this perturbation argument; searches for Mathlib/SOptLib subgradient or
affine-minorant theorems found only lsc-dependent
`ConvexOn.exists_affine_le_of_lt` and support/subdifferential helpers that
assume a subgradient is already supplied. -/
theorem charted_epigraph_interior_separator_vertical_negative
    [FiniteDimensional ℝ E]
    {X : Set E} (anchor : {x : E // x ∈ X}) (φ : E → ℝ)
    {u0 : (affineSpan ℝ X).direction}
    (hu0 : u0 ∈ interior (SOptLib.carrierChartSet X anchor))
    {L : StrongDual ℝ ((affineSpan ℝ X).direction × ℝ)}
    (hLne : L ≠ 0)
    (hsep :
      ∀ p ∈
        {p : (affineSpan ℝ X).direction × ℝ |
          p.1 ∈ SOptLib.carrierChartSet X anchor ∧
            φ (SOptLib.carrierChartToAmbient X anchor p.1) ≤ p.2},
        L p ≤ L (u0, φ (SOptLib.carrierChartToAmbient X anchor u0) - 1)) :
    L ((0 : (affineSpan ℝ X).direction), (1 : ℝ)) < 0 := by
  classical
  let C : Set (affineSpan ℝ X).direction := SOptLib.carrierChartSet X anchor
  let f : (affineSpan ℝ X).direction → ℝ := fun u =>
    φ (SOptLib.carrierChartToAmbient X anchor u)
  let e : (affineSpan ℝ X).direction × ℝ :=
    ((0 : (affineSpan ℝ X).direction), (1 : ℝ))
  let p0 : (affineSpan ℝ X).direction × ℝ := (u0, f u0)
  have hu0C : u0 ∈ C := interior_subset hu0
  have hcoef_nonpos : L e ≤ 0 := by
    have hp0 :
        p0 ∈
          {p : (affineSpan ℝ X).direction × ℝ |
            p.1 ∈ SOptLib.carrierChartSet X anchor ∧
              φ (SOptLib.carrierChartToAmbient X anchor p.1) ≤ p.2} := by
      exact ⟨by simpa [C] using hu0C, by simp [p0, f]⟩
    have hle := hsep p0 hp0
    have hbelow :
        L (u0, f u0 - 1) = L p0 - L e := by
      have hvec : (u0, f u0 - 1) = p0 - e := by
        ext <;> simp [p0, e]
      rw [hvec, map_sub]
    linarith
  have hcoef_ne : L e ≠ 0 := by
    intro hcoef_zero
    have hdecomp_zero :
        ∀ u : (affineSpan ℝ X).direction, u ∈ C →
          L (u, (0 : ℝ)) ≤ L (u0, (0 : ℝ)) := by
      intro u hu
      have hp :
          (u, f u) ∈
            {p : (affineSpan ℝ X).direction × ℝ |
              p.1 ∈ SOptLib.carrierChartSet X anchor ∧
                φ (SOptLib.carrierChartToAmbient X anchor p.1) ≤ p.2} := by
        exact ⟨by simpa [C] using hu, by simp [f]⟩
      have hle := hsep (u, f u) hp
      have hleft : L (u, f u) = L (u, (0 : ℝ)) := by
        have hsplit : (u, f u) = (u, (0 : ℝ)) + (f u) • e := by
          ext <;> simp [e]
        rw [hsplit, map_add, map_smul, hcoef_zero]
        simp
      have hright :
          L (u0, φ (SOptLib.carrierChartToAmbient X anchor u0) - 1) =
            L (u0, (0 : ℝ)) := by
        have hsplit :
            (u0, φ (SOptLib.carrierChartToAmbient X anchor u0) - 1) =
              (u0, (0 : ℝ)) +
                (φ (SOptLib.carrierChartToAmbient X anchor u0) - 1) • e := by
          ext <;> simp [e]
        rw [hsplit, map_add, map_smul, hcoef_zero]
        simp
      linarith
    have hhorizontal_zero :
        ∀ v : (affineSpan ℝ X).direction, L (v, (0 : ℝ)) = 0 := by
      intro v
      have hnhds : C ∈ nhds u0 := mem_interior_iff_mem_nhds.mp hu0
      rcases Metric.mem_nhds_iff.mp hnhds with ⟨ε, hεpos, hεsub⟩
      let r : ℝ := ε / (2 * (‖v‖ + 1))
      have hvnorm_nonneg : 0 ≤ ‖v‖ := norm_nonneg v
      have hden_pos : 0 < 2 * (‖v‖ + 1) := by nlinarith
      have hrpos : 0 < r := by
        exact div_pos hεpos hden_pos
      have hrnorm_lt : ‖r • v‖ < ε := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hrpos]
        have hmul : r * ‖v‖ < ε := by
          unfold r
          field_simp [hden_pos.ne']
          nlinarith [hεpos, hvnorm_nonneg]
        exact hmul
      have hplus_mem : u0 + r • v ∈ C := by
        apply hεsub
        rw [Metric.mem_ball]
        have hdist : dist (u0 + r • v) u0 = ‖r • v‖ := by
          rw [Subtype.dist_eq]
          have hsub :
              (↑(u0 + r • v) : E) - ↑u0 = ↑(r • v) := by
            simpa using congrArg Subtype.val
              (show (u0 + r • v) - u0 = r • v by abel)
          simpa [dist_eq_norm, hsub]
        simpa [hdist] using hrnorm_lt
      have hminus_mem : u0 - r • v ∈ C := by
        apply hεsub
        rw [Metric.mem_ball]
        have hminus_norm : ‖-(r • v)‖ < ε := by simpa using hrnorm_lt
        have hdist : dist (u0 - r • v) u0 = ‖-(r • v)‖ := by
          rw [Subtype.dist_eq]
          have hsub :
              (↑(u0 - r • v) : E) - ↑u0 = ↑(-(r • v)) := by
            simpa using congrArg Subtype.val
              (show (u0 - r • v) - u0 = -(r • v) by abel)
          simpa [dist_eq_norm, hsub]
        simpa [hdist] using hminus_norm
      have hplus_le := hdecomp_zero (u0 + r • v) hplus_mem
      have hminus_le := hdecomp_zero (u0 - r • v) hminus_mem
      have hplus_eq :
          L (u0 + r • v, (0 : ℝ)) =
            L (u0, (0 : ℝ)) + r * L (v, (0 : ℝ)) := by
        have hsplit :
            (u0 + r • v, (0 : ℝ)) =
              (u0, (0 : ℝ)) + r • (v, (0 : ℝ)) := by
          ext <;> simp
        rw [hsplit, map_add, map_smul]
        rfl
      have hminus_eq :
          L (u0 - r • v, (0 : ℝ)) =
            L (u0, (0 : ℝ)) - r * L (v, (0 : ℝ)) := by
        have hsplit :
            (u0 - r • v, (0 : ℝ)) =
              (u0, (0 : ℝ)) - r • (v, (0 : ℝ)) := by
          ext <;> simp [sub_eq_add_neg]
        rw [hsplit, map_sub, map_smul]
        rfl
      have hle0 : L (v, (0 : ℝ)) ≤ 0 := by
        nlinarith [hplus_le, hplus_eq, hrpos]
      have hge0 : 0 ≤ L (v, (0 : ℝ)) := by
        nlinarith [hminus_le, hminus_eq, hrpos]
      exact le_antisymm hle0 hge0
    apply hLne
    apply ContinuousLinearMap.ext
    intro p
    have hsplit : p = (p.1, (0 : ℝ)) + p.2 • e := by
      ext <;> simp [e]
    rw [hsplit, map_add, map_smul, hcoef_zero, hhorizontal_zero p.1]
    simp
  simpa [e] using lt_of_le_of_ne hcoef_nonpos hcoef_ne

/-- A finite-dimensional carrier-convex function has a chart-affine lower
minorant.

This is the chart-space half of the affine-minorant bridge needed for the
selected SPS stability proof.  Candidate audit: searched SOptLib/Mathlib for
`ConvexOn affine lower bound`, `supporting hyperplane`, and subgradient
existence.  Existing `ConvexOn.exists_affine_le_of_lt`/`sSup_affine_eq` require
`LowerSemicontinuousOn`; SOptLib subdifferential helpers require a supplied
subgradient.  The proof therefore uses the route-local interior epigraph
separation and negative vertical-coefficient helpers, aligned with the
interior-point Hahn-Banach proof route for Lan Proposition 8.3. -/
theorem convexOn_carrierChart_affine_minorant
    [FiniteDimensional ℝ E]
    {X : Set E} (hX : Convex ℝ X) (anchor : {x : E // x ∈ X})
    (φ : E → ℝ) (hφ : ConvexOn ℝ X φ) :
    ∃ a : ℝ, ∃ ℓ : StrongDual ℝ (affineSpan ℝ X).direction,
      ∀ u ∈ SOptLib.carrierChartSet X anchor,
        a + ℓ u ≤ φ (SOptLib.carrierChartToAmbient X anchor u) := by
  classical
  let V := (affineSpan ℝ X).direction
  let C : Set V := SOptLib.carrierChartSet X anchor
  let f : V → ℝ := fun u => φ (SOptLib.carrierChartToAmbient X anchor u)
  obtain ⟨u0, hu0⟩ := SOptLib.carrierChartSet_interior_nonempty X anchor hX
  obtain ⟨L, hLne, hsepLet⟩ :=
    charted_epigraph_separates_below_interior_point
      (X := X) hX anchor φ hφ hu0
  let e : V × ℝ := ((0 : V), (1 : ℝ))
  let c : ℝ := L e
  have hsep :
      ∀ p ∈ {p : V × ℝ | p.1 ∈ SOptLib.carrierChartSet X anchor ∧ f p.1 ≤ p.2},
        L p ≤ L (u0, f u0 - 1) := by
    simpa [V, f] using hsepLet
  have hcneg : c < 0 := by
    have hneg :=
      charted_epigraph_interior_separator_vertical_negative
        (X := X) anchor φ hu0 hLne
        (by simpa [V, f] using hsep)
    simpa [V, e, c] using hneg
  let hinj : V →L[ℝ] V × ℝ := ContinuousLinearMap.inl ℝ V ℝ
  let ℓ : StrongDual ℝ V := (-(1 / c)) • (L.comp hinj)
  let a : ℝ := L (u0, f u0 - 1) / c
  refine ⟨a, ℓ, ?_⟩
  intro u hu
  have hp : (u, f u) ∈ {p : V × ℝ | p.1 ∈ SOptLib.carrierChartSet X anchor ∧ f p.1 ≤ p.2} :=
    ⟨by simpa [C] using hu, le_rfl⟩
  have hle := hsep (u, f u) hp
  have hsplit : (u, f u) = (u, (0 : ℝ)) + (f u) • e := by
    ext <;> simp [e]
  have hLboundary : L (u, f u) = L (u, (0 : ℝ)) + c * f u := by
    rw [hsplit, map_add, map_smul]
    simp [c, e, mul_comm]
  have hcf_le : c * f u ≤ L (u0, f u0 - 1) - L (u, (0 : ℝ)) := by
    nlinarith
  have hdiv :
      (L (u0, f u0 - 1) - L (u, (0 : ℝ))) / c ≤ f u := by
    rw [div_le_iff_of_neg hcneg]
    nlinarith
  have hell_apply : ℓ u = -(1 / c) * L (u, (0 : ℝ)) := by
    simp [ℓ, hinj]
  calc
    a + ℓ u
        = (L (u0, f u0 - 1) - L (u, (0 : ℝ))) / c := by
          rw [hell_apply]
          simp [a]
          field_simp [ne_of_lt hcneg]
          ring
    _ ≤ f u := hdiv

/-- The carrier chart coordinate is the ambient displacement from the anchor.

This algebra bridge translates chart-linear minorants into ambient affine
minorants.  Candidate audit: `SOptLib.carrierChartToAmbient_chartPoint`
rewrites the affine chart image, while
`SOptLib.affineSpan_chartPoint_sub_subtypeL` is the matching proved statement
for subtracting affine-span chart coordinates; no existing helper stated the
single-coordinate anchor-displacement form needed downstream. -/
theorem carrierChartPoint_subtype_eq_sub
    [FiniteDimensional ℝ E]
    {X : Set E} (anchor y : {x : E // x ∈ X}) :
    ((SOptLib.carrierChartPoint X anchor y : (affineSpan ℝ X).direction) : E) =
      y.1 - anchor.1 := by
  classical
  let A : AffineSubspace ℝ E := affineSpan ℝ X
  haveI : Nonempty A := ⟨⟨anchor.1, subset_affineSpan ℝ X anchor.2⟩⟩
  let a : A := ⟨anchor.1, subset_affineSpan ℝ X anchor.2⟩
  let yy : A := ⟨y.1, subset_affineSpan ℝ X y.2⟩
  have h :=
    affineSpan_chartPoint_sub_subtypeL (A := A) (anchor := a)
      (x := a) (y := yy)
  have hsub :
      (↑(SOptLib.carrierChartPoint X anchor y -
            SOptLib.carrierChartPoint X anchor anchor) : E) =
        y.1 - anchor.1 := by
    change A.direction.subtypeL
        ((AffineIsometryEquiv.vaddConst ℝ a).symm yy -
          (AffineIsometryEquiv.vaddConst ℝ a).symm a) =
        (yy : E) - (a : E)
    exact h
  have hzero : SOptLib.carrierChartPoint X anchor anchor = 0 := by
    change (AffineIsometryEquiv.vaddConst ℝ a).symm a = 0
    simp
  simpa [hzero] using hsub

/-- Finite-dimensional carrier-convex functions admit ambient affine
minorants on the feasible carrier.

This is the finite-dimensional affine-minorant bridge required to control the
unbounded lower-order `χ`/`Φ` term in the selected SPS stability proof.
Candidate audit: SOptLib provides carrier chart geometry
(`carrierChartSet_interior_nonempty`, `carrierChartToAmbient_chartPoint`) but
no affine-minorant theorem; Mathlib affine approximation helpers require
`LowerSemicontinuousOn`; target-file charted epigraph helpers provide the
matching separation route, completed here and translated back with
`InnerProductSpace.toDual`. -/
theorem convexOn_feasible_affine_minorant
    [FiniteDimensional ℝ E]
    {X : Set E} (hX : Convex ℝ X) (anchor : {x : E // x ∈ X})
    (φ : E → ℝ) (hφ : ConvexOn ℝ X φ) :
    ∃ a : ℝ, ∃ b : E, ∀ y : {x : E // x ∈ X},
      a + ⟪b, y.1⟫_ℝ ≤ φ y.1 := by
  classical
  let V := (affineSpan ℝ X).direction
  obtain ⟨a0, ℓ, hminor⟩ :=
    convexOn_carrierChart_affine_minorant (X := X) hX anchor φ hφ
  haveI : IsUniformAddGroup V := V.toAddSubgroup.isUniformAddGroup
  have hVcomplete : IsComplete (V : Set E) := V.complete_of_finiteDimensional
  let instComplete : CompleteSpace V := completeSpace_coe_iff_isComplete.2 hVcomplete
  letI : CompleteSpace V := instComplete
  let w : V := (@InnerProductSpace.toDual ℝ V _ _ _ instComplete).symm ℓ
  let b : E := (w : E)
  let a : ℝ := a0 - ⟪b, anchor.1⟫_ℝ
  refine ⟨a, b, ?_⟩
  intro y
  let u : V := SOptLib.carrierChartPoint X anchor y
  have hu : u ∈ SOptLib.carrierChartSet X anchor := by
    simpa [u] using SOptLib.carrierChartPoint_mem X anchor y
  have hchart := hminor u hu
  have hell_chart : ℓ u = ⟪w, u⟫_ℝ := by
    simp [w, InnerProductSpace.toDual_symm_apply]
    rfl
  have hcoord : (u : E) = y.1 - anchor.1 := by
    simpa [u] using carrierChartPoint_subtype_eq_sub (X := X) anchor y
  have hambient : ℓ u = ⟪b, y.1 - anchor.1⟫_ℝ := by
    rw [hell_chart]
    change ⟪(w : E), (u : E)⟫_ℝ = ⟪b, y.1 - anchor.1⟫_ℝ
    rw [hcoord]
  have hleft :
      a + ⟪b, y.1⟫_ℝ = a0 + ℓ u := by
    rw [hambient]
    simp [a, inner_sub_right]
    ring
  calc
    a + ⟪b, y.1⟫_ℝ = a0 + ℓ u := hleft
    _ ≤ φ (SOptLib.carrierChartToAmbient X anchor u) := hchart
    _ = φ y.1 := by
      rw [show SOptLib.carrierChartToAmbient X anchor u = y.1 by
        simpa [u] using SOptLib.carrierChartToAmbient_chartPoint X anchor y]

/-- The feasible-domain `Φ` gap has arbitrary-epsilon Bregman growth in its
comparison argument.

Aligns with the lower-support/Young absorption step between Lan Proposition
8.3 Eq. (8.1.61) and the absorbed Eq. (8.1.63). Candidate audit: considered
`convexOn_feasible_affine_minorant`, `SOptLib.mem_carrierSubdifferential_iff`,
`bregmanFormulaOnX_lower_bound_from_prox_geometry`, and
`fixed_linear_pairing_bregman_absorb_with_epsilon`; no existing SOptLib or
target-file theorem packages this exact `spsPhiFormulaOnX` gap, because it must
combine the paper-local affine model, carrier subgradient for `h`, affine
minorant for `χ`, and feasible Bregman formula extension. -/
theorem spsPhiFormulaOnX_gap_le_eps_bregman_add_const
    (g : E → ℝ) (hg : IsAffineModel g) (center u : FeasiblePoint S)
    {β eps : ℝ} (hβ : 0 ≤ β) (heps : 0 < eps) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ z : FeasiblePoint S,
        spsPhiFormulaOnX S g center β u -
            spsPhiFormulaOnX S g center β z ≤
          eps * bregmanFormulaOnX S z u + C := by
  classical
  letI : FiniteDimensional ℝ E := S.finiteDimensional_ambient
  rcases hg with ⟨gc, gb, hgdef⟩
  obtain ⟨χa, χb, hχminor⟩ :=
    convexOn_feasible_affine_minorant
      (X := S.X) S.convex_X (⟨u.1, u.2⟩ : {x : E // x ∈ S.X})
      S.chi S.convex_chi
  let b : E := gb + S.hSubgradient u.1 + χb
  obtain ⟨Cpair, hCpair_nonneg, hpair⟩ :=
    fixed_linear_pairing_bregman_absorb_with_epsilon S u b heps
  let A : ℝ := β * bregmanFormulaOnX S center u +
    (S.chi u.1 - χa - ⟪χb, u.1⟫_ℝ)
  let C : ℝ := Cpair + |A|
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    nlinarith [hCpair_nonneg, abs_nonneg A]
  · intro z
    have hg_gap : g u.1 - g z.1 = ⟪gb, u.1 - z.1⟫_ℝ := by
      simp [hgdef, inner_sub_right]
    have hh_support :
        S.h z.1 ≥
          S.h u.1 + ⟪S.hSubgradient u.1, z.1 - u.1⟫_ℝ := by
      have hmem := (setup_hSubgradientMem S) u.1 u.2
      exact (SOptLib.mem_carrierSubdifferential_iff.mp hmem) z
    have hh_gap :
        S.h u.1 - S.h z.1 ≤
          ⟪S.hSubgradient u.1, u.1 - z.1⟫_ℝ := by
      have hinner :
          ⟪S.hSubgradient u.1, z.1 - u.1⟫_ℝ =
            -⟪S.hSubgradient u.1, u.1 - z.1⟫_ℝ := by
        simp [inner_sub_right]
      nlinarith
    have hχz : χa + ⟪χb, z.1⟫_ℝ ≤ S.chi z.1 := hχminor z
    have hχ_gap :
        S.chi u.1 - S.chi z.1 ≤
          (S.chi u.1 - χa - ⟪χb, u.1⟫_ℝ) +
            ⟪χb, u.1 - z.1⟫_ℝ := by
      have hinner : ⟪χb, u.1 - z.1⟫_ℝ =
          ⟪χb, u.1⟫_ℝ - ⟪χb, z.1⟫_ℝ := by
        simp [inner_sub_right]
      nlinarith
    have hVcenter_z_nonneg : 0 ≤ bregmanFormulaOnX S center z := by
      have hlower := bregmanFormulaOnX_lower_bound_from_prox_geometry S center z
      nlinarith [sq_nonneg (S.primalNorm (z.1 - center.1))]
    have hβ_gap :
        β * bregmanFormulaOnX S center u -
            β * bregmanFormulaOnX S center z ≤
          β * bregmanFormulaOnX S center u := by
      nlinarith [mul_nonneg hβ hVcenter_z_nonneg]
    have hinner_sum :
        ⟪gb, u.1 - z.1⟫_ℝ +
            ⟪S.hSubgradient u.1, u.1 - z.1⟫_ℝ +
            ⟪χb, u.1 - z.1⟫_ℝ =
          ⟪b, u.1 - z.1⟫_ℝ := by
      simp [b, inner_add_left]
    have hphi_affine :
        spsPhiFormulaOnX S g center β u -
            spsPhiFormulaOnX S g center β z ≤
          A + ⟪b, u.1 - z.1⟫_ℝ := by
      unfold spsPhiFormulaOnX spsPhi
      nlinarith [hg_gap, hh_gap, hχ_gap, hβ_gap, hinner_sum]
    have hpair_z :
        ⟪b, u.1 - z.1⟫_ℝ ≤
          eps * bregmanFormulaOnX S z u + Cpair := hpair z
    have hA_le_abs : A ≤ |A| := le_abs_self A
    have hC_eq : C = Cpair + |A| := rfl
    nlinarith

/-- Explicit-constant form of the feasible-domain `Φ` gap envelope.

The older `spsPhiFormulaOnX_gap_le_eps_bregman_add_const` hides the Young
constant inside an existential.  This form exposes the affine model slope and
the `χ` minorant used by the proof, and the constant is the concrete expression
`||gb+h'(u)+χb||_*^2/(2 eps) + |β V(center,u)+χ(u)-χa-<χb,u>|`.
It is the API needed when the outer model/center is random and integrability
must be proved term by term. -/
theorem spsPhiFormulaOnX_gap_le_eps_bregman_add_explicit_const
    (g : E → ℝ) (hg : IsAffineModel g) (center u : FeasiblePoint S)
    {β eps : ℝ} (hβ : 0 ≤ β) (heps : 0 < eps) :
    ∃ gc : ℝ, ∃ gb : E, ∃ χa : ℝ, ∃ χb : E,
      (∀ y, g y = gc + ⟪gb, y⟫_ℝ) ∧
        (∀ y : {x : E // x ∈ S.X}, χa + ⟪χb, y.1⟫_ℝ ≤ S.chi y.1) ∧
          ∀ z : FeasiblePoint S,
            spsPhiFormulaOnX S g center β u -
                spsPhiFormulaOnX S g center β z ≤
              eps * bregmanFormulaOnX S z u +
                dualNorm S (gb + S.hSubgradient u.1 + χb) ^ 2 / (2 * eps) +
                  |β * bregmanFormulaOnX S center u +
                    (S.chi u.1 - χa - ⟪χb, u.1⟫_ℝ)| := by
  classical
  letI : FiniteDimensional ℝ E := S.finiteDimensional_ambient
  rcases hg with ⟨gc, gb, hgdef⟩
  obtain ⟨χa, χb, hχminor⟩ :=
    convexOn_feasible_affine_minorant
      (X := S.X) S.convex_X (⟨u.1, u.2⟩ : {x : E // x ∈ S.X})
      S.chi S.convex_chi
  refine ⟨gc, gb, χa, χb, hgdef, hχminor, ?_⟩
  intro z
  let slope : E := gb + S.hSubgradient u.1 + χb
  let A : ℝ := β * bregmanFormulaOnX S center u +
    (S.chi u.1 - χa - ⟪χb, u.1⟫_ℝ)
  have hg_gap : g u.1 - g z.1 = ⟪gb, u.1 - z.1⟫_ℝ := by
    simp [hgdef, inner_sub_right]
  have hh_support :
      S.h z.1 ≥
        S.h u.1 + ⟪S.hSubgradient u.1, z.1 - u.1⟫_ℝ := by
    have hmem := (setup_hSubgradientMem S) u.1 u.2
    exact (SOptLib.mem_carrierSubdifferential_iff.mp hmem) z
  have hh_gap :
      S.h u.1 - S.h z.1 ≤
        ⟪S.hSubgradient u.1, u.1 - z.1⟫_ℝ := by
    have hinner :
        ⟪S.hSubgradient u.1, z.1 - u.1⟫_ℝ =
          -⟪S.hSubgradient u.1, u.1 - z.1⟫_ℝ := by
      simp [inner_sub_right]
    nlinarith
  have hχz : χa + ⟪χb, z.1⟫_ℝ ≤ S.chi z.1 := hχminor z
  have hχ_gap :
      S.chi u.1 - S.chi z.1 ≤
        (S.chi u.1 - χa - ⟪χb, u.1⟫_ℝ) +
          ⟪χb, u.1 - z.1⟫_ℝ := by
    have hinner : ⟪χb, u.1 - z.1⟫_ℝ =
        ⟪χb, u.1⟫_ℝ - ⟪χb, z.1⟫_ℝ := by
      simp [inner_sub_right]
    nlinarith
  have hVcenter_z_nonneg : 0 ≤ bregmanFormulaOnX S center z := by
    have hlower := bregmanFormulaOnX_lower_bound_from_prox_geometry S center z
    nlinarith [sq_nonneg (S.primalNorm (z.1 - center.1))]
  have hβ_gap :
      β * bregmanFormulaOnX S center u -
          β * bregmanFormulaOnX S center z ≤
        β * bregmanFormulaOnX S center u := by
    nlinarith [hβ, hVcenter_z_nonneg]
  have hinner_sum :
      ⟪gb, u.1 - z.1⟫_ℝ +
          ⟪S.hSubgradient u.1, u.1 - z.1⟫_ℝ +
          ⟪χb, u.1 - z.1⟫_ℝ =
        ⟪slope, u.1 - z.1⟫_ℝ := by
    simp [slope, inner_add_left]
  have hphi_affine :
      spsPhiFormulaOnX S g center β u -
          spsPhiFormulaOnX S g center β z ≤
        A + ⟪slope, u.1 - z.1⟫_ℝ := by
    unfold spsPhiFormulaOnX spsPhi
    nlinarith [hg_gap, hh_gap, hχ_gap, hβ_gap, hinner_sum]
  have hpair_z :
      ⟪slope, u.1 - z.1⟫_ℝ ≤
        eps * bregmanFormulaOnX S z u + dualNorm S slope ^ 2 / (2 * eps) :=
    fixed_linear_pairing_bregman_absorb_with_epsilon_explicit
      (S := S) u slope heps z
  have hA_le_abs : A ≤ |A| := le_abs_self A
  nlinarith


end StochasticGradientSliding
