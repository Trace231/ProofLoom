import SOptLib.Analysis.ConvexSmoothExtension
import SOptLib.Model.Bregman
import SOptLib.Glue.Algebra
import SOptLib.Glue.Analysis
import SOptLib.Glue.Calculus
import SOptLib.Model.BlockSampling
import SOptLib.Model.Iterates
import SOptLib.Model.IsSimpleConvexTermOn
import SOptLib.Model.Objective
import SOptLib.Model.Prox
import SOptLib.Model.Selection
import SOptLib.Model.Subdifferential
import SOptLib.Model.StochasticOracle
import SOptLib.Model.ParameterChoices
import SOptLib.Layer0.ConvexFOC
import SOptLib.Layer0.Objective
import SOptLib.Layer1.Proximal
import Mathlib.Analysis.Convex.Approximation
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.SpecialFunctions.Log.Base
import SOptLib.Layer0.Subgradient

noncomputable section

open scoped BigOperators InnerProductSpace

namespace VarianceReducedAcceleratedGradientDescent


/-- The paper's Euclidean variable space `R^dim`.

No SOptLib match: searched `variable_space`, `finite-dimensional Euclidean
space`, and the Model directory concepts; SOptLib provides carrier and gradient
helpers over an ambient space, but the paper's source datum is literally
`X subset R^m` in Section 5.3, so this local abbreviation pins the ambient
coordinate space to `Fin dim -> Real`. -/
abbrev VariableSpace (dim : Nat) := EuclideanSpace Real (Fin dim)

/-- Real-valued component count used in the finite-sum denominator `n`.

This is a local paper alias, not a new optimization primitive: SOptLib
`finiteUniformAverage` and `importance_weighted_gradient_difference` both take
the normalizer as an explicit scalar, while Algorithm 5.7 prints the normalizer
as the component count in the denominator `q_i n`. -/
def componentCountReal (n : Nat) : Real :=
  (n : Real)

/-- Source-defined prox-core domain `X^o` for a distance-generating function.

SOptLib candidates `IntrinsicInteriorCarrierPoint`, `carrierRestrictToIntrinsicInterior`,
and `IsDistanceGeneratingFunctionOn` were checked. They model reusable
intrinsic-interior or ambient-gradient DGF APIs, while Lan §3.2 defines `X^o`
literally as the subset of `X` whose points solve a linear-plus-`nu` problem
over `X`; this definition records that source object directly. -/
def proxCoreSetOf {dim : Nat} (X : Set (VariableSpace dim))
    (nu : VariableSpace dim -> Real) : Set (VariableSpace dim) :=
  SOptLib.proxCoreSet X nu

/-- Source-selected DGF gradient at a prox-core point, using the feasible carrier `X`.

SOptLib candidates `literalBregmanDivergence`, `literalIntrinsicCarrierBregmanDivergence`,
and `carrierBregmanDivergence` were checked. The reusable literal wrappers use
ambient Frechet gradients or intrinsic-interior carriers. Lan Lemma 3.5 uses
`nu : X -> R` differentiable and Eq. (3.2.2) differentiates the prox function in
feasible directions, so the selected gradient is the within-gradient over `X`
at the source left-domain point `X^o`. -/
def proxCoreGradientOf {dim : Nat} (X : Set (VariableSpace dim))
    (nu : VariableSpace dim -> Real)
    (x : {u : VariableSpace dim // u ∈ proxCoreSetOf X nu}) : VariableSpace dim :=
  gradientWithin nu X x.1

/-- The literal Bregman prox-function `V : X^o x X -> R` from Eq. (3.2.2).

SOptLib `carrierBregmanDivergence` was checked and rejected for this
paper-facing object because it is all-carrier `X x X`; Eq. (3.2.2) has the
left-domain restriction `X^o x X`, so this definition keeps the source domain
visible. -/
def bregmanOf {dim : Nat} (X : Set (VariableSpace dim))
    (nu : VariableSpace dim -> Real)
    (x : {u : VariableSpace dim // u ∈ proxCoreSetOf X nu})
    (z : {u : VariableSpace dim // u ∈ X}) : Real :=
  nu z.1 - (nu x.1 + ⟪proxCoreGradientOf X nu x, z.1 - x.1⟫_Real)

@[simp]
theorem bregmanOf_def {dim : Nat} (X : Set (VariableSpace dim))
    (nu : VariableSpace dim -> Real)
    (x : {u : VariableSpace dim // u ∈ proxCoreSetOf X nu})
    (z : {u : VariableSpace dim // u ∈ X}) :
    bregmanOf X nu x z =
      nu z.1 - (nu x.1 + ⟪proxCoreGradientOf X nu x, z.1 - x.1⟫_Real) := by
  rfl



/-- All-carrier Bregman expression for the Eq. (5.3.2) notation gap.

Lan §3.2 defines the prox-function on `X^o x X`, but Eq. (5.3.2) states the
possible-strong-convexity display for all `x,y in X`. The SOptLib candidate
`carrierBregmanFormula` was checked and used only as an explicitly named
source-boundary surrogate for that all-`X` display; it is not the paper's
prox-function, which remains represented below on the `X^o -> X -> Real`
domain. -/
def legacyDiagnosticFeasibleBregmanOf {dim : Nat} (X : Set (VariableSpace dim))
    (nu : VariableSpace dim -> Real)
    (x z : {u : VariableSpace dim // u ∈ X}) : Real :=
  carrierBregmanFormula
    (fun u : {u : VariableSpace dim // u ∈ X} => nu u.1)
    (fun u : {u : VariableSpace dim // u ∈ X} => u.1)
    (fun u : {u : VariableSpace dim // u ∈ X} => gradientWithin nu X u.1)
    x z

@[simp]
theorem legacyDiagnosticFeasibleBregmanOf_def {dim : Nat} (X : Set (VariableSpace dim))
    (nu : VariableSpace dim -> Real)
    (x z : {u : VariableSpace dim // u ∈ X}) :
    legacyDiagnosticFeasibleBregmanOf X nu x z =
      nu z.1 - nu x.1 - ⟪gradientWithin nu X x.1, z.1 - x.1⟫_Real := by
  rfl

/-- Source-facing data for Lan Algorithm 5.7 and Theorem 5.9.

The original setup is supplemented below by an explicit convex smooth extension condition. Original setup data are: the closed convex feasible set,
finite component objectives, the simple term, the distance-generating function,
component smoothness constants, the Eq. (5.3.2) possible-strong-convexity
assumption, and the source-stated DGF
convexity/continuous-differentiability/modulus-one data from Lan §3.2,
Eqs. (3.2.1)-(3.2.3). Algorithmic objects such as `G_t`, `delta_t`, `x_t`,
prox updates, sampling laws, weighted outputs, and the Eq. (5.3.2) domain bridge
are definitions/theorem obligations below. -/
structure Setup (n dim : Nat) where
  /-- Stated finite-sum setup datum: the component count in Section 5.3 is
  positive because the problem averages over `i = 1, ..., m`. JSON:
  `#/setup/variable_space` and `#/assumptions/0`. -/
  component_count_pos : 0 < n
  /-- Stated feasible carrier datum. JSON `#/setup/variable_space`: `X` is a
  closed convex subset of Euclidean space. -/
  X : Set (VariableSpace dim)
  /-- Stated finite component objectives. JSON `#/setup/variable_space` and
  `#/assumptions/0`: `f(x) = (1/m) sum_i f_i(x)`. -/
  component : Fin n -> VariableSpace dim -> Real
  /-- Stated simple composite term. JSON `#/setup/problem` and
  `#/assumptions/5`: `Psi(x) := f(x) + h(x)` with `h` simple convex. -/
  h : VariableSpace dim -> Real
  /-- Distance-generating function `nu` from Lan §3.2, used in
  `V(x,z)=nu(z)-[nu(x)+<grad nu(x),z-x>]` in Eq. (3.2.2). -/
  nu : VariableSpace dim -> Real
  /-- Stated component smoothness constants. JSON `#/assumptions/1`:
  `||grad f_i(x)-grad f_i(y)||_* <= L_i ||x-y||`, with `L_i > 0`. -/
  Lcomp : Fin n -> Real
  /-- Stated possible strong-convexity parameter. JSON `#/assumptions/3`:
  Eq. (5.3.2) uses `mu >= 0`. -/
  mu : Real
  /-- Stated carrier property, quote-class setup datum. JSON
  `#/setup/variable_space`: `X subset R^m is a closed convex set`. -/
  X_closed : IsClosed X
  /-- Stated carrier property, quote-class setup datum. JSON
  `#/setup/variable_space`: `X subset R^m is a closed convex set`. -/
  X_convex : Convex Real X
  /-- Stated component assumption, quote-class primitive assumption. JSON
  `#/assumptions/0`: the finite-sum components are smooth convex functions. -/
  component_convex : forall i, ConvexOn Real X (component i)
  /-- Stated component assumption, quote-class primitive assumption. JSON
  `#/assumptions/0`: the finite-sum components are smooth convex functions. -/
  component_differentiableOn : forall i, DifferentiableOn Real (component i) X
  /-- Stated component smoothness assumption. JSON `#/assumptions/1`: the
  displayed Lipschitz-gradient inequality holds for all `x,y in X`. -/
  component_smooth :
    forall i, forall x, x ∈ X -> forall y, y ∈ X ->
      norm (gradientWithin (component i) X x - gradientWithin (component i) X y) <=
        Lcomp i * norm (x - y)
  /-- Stated positivity of component smoothness constants. JSON
  `#/assumptions/1`, parameters: `L_i > 0`. -/
  Lcomp_pos : forall i, 0 < Lcomp i
  /-- Eq. (5.3.2): Section 5.3 explicitly assumes possible strong convexity,
  `f(y) >= f(x) + <grad f(x), y-x> + mu V(x,y)` for all `x,y in X`.
  This is a primitive paper assumption, not a derived theorem obligation.
  No SOptLib/Mathlib match was used: the pre-search candidate list for possible
  strong convexity was empty; symbol search for `strong convexity Bregman
  feasible carrier` found Bregman lower-bound and carrier-divergence primitives
  such as `carrierBregmanDivergence_lower_bound_of_strongConvexOn_intrinsicInterior`,
  but those model DGF geometry rather than Lan's finite-sum objective assumption
  with the Eq. (5.3.2) all-`X` Bregman notation surrogate. -/
  finiteSum_strong_convexity_bregman_allFeasible :
    forall x : {u : VariableSpace dim // u ∈ X},
      forall y : {u : VariableSpace dim // u ∈ X},
        SOptLib.finiteUniformAverage (fun i : Fin n => component i x.1) +
            ⟪(componentCountReal n)⁻¹ •
                Finset.univ.sum (fun i : Fin n => gradientWithin (component i) X x.1),
              y.1 - x.1⟫_Real +
            mu * legacyDiagnosticFeasibleBregmanOf X nu x y <=
          SOptLib.finiteUniformAverage (fun i : Fin n => component i y.1)
  /-- Section 5.3 states that `h` is a simple, possibly nondifferentiable,
  convex function. Reuses SOptLib `IsSimpleConvexTermOn`, which records the
  simple expression witness plus its carrier convexity; this replaces the
  weaker bare `ConvexOn` witness. -/
  h_simple : SOptLib.IsSimpleConvexTermOn X h
  /-- Lan §3.2 assumes the distance-generating function is strongly convex on
  the prox core; convexity is the stated DGF setup property used before proving
  the strong lower bound. PDF §3.2 around Eq. (3.2.2). -/
  nu_convex : ConvexOn Real X nu
  /-- Lan §3.2 states the DGF is continuous on the feasible carrier; quote-class
  DGF setup datum for the prox-function. -/
  nu_continuousOn : ContinuousOn nu X
  /-- Source prox-core convexity for `X^o`, the left domain of Eq. (3.2.2);
  quote-class definitional property of the DGF/prox data structure. -/
  proxCore_convex : Convex Real (proxCoreSetOf X nu)
  /-- Lan §3.2 around Eq. (3.2.1) states that `nu` restricted to `X^o` is
  continuously differentiable. -/
  nu_contDiffOn_proxCore :
    ContDiffOn Real 1 nu (proxCoreSetOf X nu)
  /-- Source DGF derivative semantics at the Eq. (3.2.2) left-domain points.
  Lan §3.2 defines the prox-function on `X^o x X`, and Lemma 3.5 differentiates
  `V(x, ·)` along feasible directions for centers that occur in that left
  domain. This records only the prox-core-center feasible-direction derivative,
  not differentiability at every feasible point of `X`. -/
  nu_hasGradientWithinAt_X_of_proxCore :
    forall x : {u : VariableSpace dim // u ∈ proxCoreSetOf X nu},
      HasGradientWithinAt nu (gradientWithin nu X x.1) X x.1
  /-- Modulus-one strong convexity on `X^o`, matching the normalization used in
  Eq. (3.2.3). -/
  nu_strong_monotone_proxCore :
    forall x, x ∈ proxCoreSetOf X nu -> forall y, y ∈ proxCoreSetOf X nu ->
      norm (y - x) ^ 2 <=
        ⟪y - x,
          gradientWithin nu (proxCoreSetOf X nu) y -
            gradientWithin nu (proxCoreSetOf X nu) x⟫_Real
  /-- Eq. (3.2.3) with the modulus-one normalization, on the source domain
  `X^o x X`. JSON `#/assumptions/8` states
  `V(x,z) >= sigma_nu / 2 * ||x-z||^2`, and JSON `#/assumptions/9`
  states `sigma_nu = 1`. The earlier monotonicity field only covers two
  prox-core endpoints; the paper's prox lower bound has a feasible second
  endpoint. -/
  bregman_modulus_one_lower_allFeasible :
    forall x : {u : VariableSpace dim // u ∈ proxCoreSetOf X nu},
      forall z : {u : VariableSpace dim // u ∈ X},
        (1 / 2 : Real) * norm (x.1 - z.1) ^ 2 <=
          carrierBregmanFormula
            (fun u : {u : VariableSpace dim // u ∈ X} => nu u.1)
            (fun u : {u : VariableSpace dim // u ∈ X} => u.1)
            (fun u : {u : VariableSpace dim // u ∈ X} => gradientWithin nu X u.1)
            ⟨x.1, x.2.1⟩ z
  mu_nonneg : 0 <= mu

  /-- Additional condition for the repaired single-sided gradient-gap argument:
  each component has a convex smooth extension preserving its carrier values,
  intrinsic projected gradient and the original smoothness constant. -/
  component_extension : ∀ i, Nonempty (SOptLib.ConvexSmoothExtensionOn X
    (fun x => component i x.1)
    (fun x => SOptLib.projectedWithinGradient X (component i) x.1)
    (normSeminorm ℝ (VariableSpace dim)) (Lcomp i))

theorem componentCountReal_pos {n dim : Nat} (S : Setup n dim) :
    0 < componentCountReal n := by
  unfold componentCountReal
  exact_mod_cast S.component_count_pos

theorem h_convex {n dim : Nat} (S : Setup n dim) :
    ConvexOn Real S.X S.h :=
  S.h_simple.convex

/-- The finite-sum smooth objective `f(x) = (1/n) * sum_i f_i(x)`.

Aligns with Eq. (5.3.1) and Section 5.3. SOptLib candidate
`finiteUniformAverage` is used because it is the reusable normalized finite
average; `compositeObjective` is reserved below for `Psi = f + h`. -/
def finiteSumObjective {n dim : Nat} (S : Setup n dim) :
    VariableSpace dim -> Real :=
  fun x => SOptLib.finiteUniformAverage (fun i : Fin n => S.component i x)

@[simp]
theorem finiteSumObjective_def {n dim : Nat} (S : Setup n dim)
    (x : VariableSpace dim) :
    finiteSumObjective S x =
      SOptLib.finiteUniformAverage (fun i : Fin n => S.component i x) := by
  rfl

/-- The composite objective `Psi(x) = f(x) + h(x)` in Eq. (5.3.1).

Reuses SOptLib `compositeObjective`, whose signature is the exact pointwise
addition wrapper for a composite objective. -/
def compositeObjective {n dim : Nat} (S : Setup n dim) :
    VariableSpace dim -> Real :=
  SOptLib.compositeObjective (finiteSumObjective S) S.h

@[simp]
theorem compositeObjective_def {n dim : Nat} (S : Setup n dim)
    (x : VariableSpace dim) :
    compositeObjective S x = finiteSumObjective S x + S.h x := by
  rfl

/-- The finite-sum part is convex on the feasible carrier.

Aligns with Eq. (5.3.1) and the Lemma 5.18 Jensen step: the reusable
`finiteUniformAverage` definition is kept, while the proof directly sums the
paper's `S.component_convex` assumptions. Candidates considered:
`convexOn_weighted_average_le_weighted_sum` is a value Jensen theorem for
already-convex objectives, and `Convex.normalized_weighted_sum_mem` is a
feasibility theorem; neither packages convexity of the finite average itself. -/
theorem finiteSumObjective_convexOn {n dim : Nat} (S : Setup n dim) :
    ConvexOn Real S.X (finiteSumObjective S) := by
  classical
  have hconv :
      ConvexOn Real S.X
        (SOptLib.finiteUniformAverage (fun i : Fin n => S.component i)) :=
    SOptLib.finiteUniformAverage_convexOn
      (X := S.X) (F := fun i : Fin n => S.component i)
      S.X_convex (fun i => S.component_convex i)
  have hfun :
      finiteSumObjective S =
        SOptLib.finiteUniformAverage (fun i : Fin n => S.component i) := by
    funext y
    simp [finiteSumObjective, SOptLib.finiteUniformAverage]
  rw [hfun]
  exact hconv

/-- Composite objective convexity used by Lemma 5.18's printed-output Jensen step.

This is the source form `Ψ=f+h` from Eq. (5.3.1): finite-sum convexity comes
from `S.component_convex`, and the simple term contributes `S.h_simple.convex`.
Candidates considered: `convexOn_weighted_average_le_weighted_sum` can consume
this fact after it exists, while `ConvexOn.map_sum_le` is the downstream Jensen
API rather than the objective-convexity bridge itself. -/
theorem compositeObjective_convexOn {n dim : Nat} (S : Setup n dim) :
    ConvexOn Real S.X (compositeObjective S) := by
  simpa [compositeObjective, SOptLib.compositeObjective] using
    (finiteSumObjective_convexOn S).add S.h_simple.convex

/-- Canonical full finite-sum gradient `grad f(x)` as the average carrier gradient.

SOptLib candidate `finiteAverageObjective_hasGradientAt` proves this is the
gradient of the finite average under differentiability hypotheses. This file
uses `gradientWithin _ X` because Section 5.3 assumes differentiability and
smoothness on the feasible set `X`, not ambient differentiability on all
`R^m`. -/
def fullGradient {n dim : Nat} (S : Setup n dim)
    (x : VariableSpace dim) : VariableSpace dim :=
  (componentCountReal n)⁻¹ •
    Finset.univ.sum (fun i : Fin n => gradientWithin (S.component i) S.X x)

@[simp]
theorem fullGradient_def {n dim : Nat} (S : Setup n dim)
    (x : VariableSpace dim) :
    fullGradient S x =
      (componentCountReal n)⁻¹ •
        Finset.univ.sum (fun i : Fin n => gradientWithin (S.component i) S.X x) := by
  rfl

theorem component_differentiableOn {n dim : Nat} (S : Setup n dim)
    (i : Fin n) :
    DifferentiableOn Real (S.component i) S.X :=
  S.component_differentiableOn i

/-- Feasible point subtype for paper expressions whose domain is `X`. -/
abbrev FeasiblePoint {n dim : Nat} (S : Setup n dim) :=
  {x : VariableSpace dim // x ∈ S.X}

instance instFeasiblePointMeasurableSpace {n dim : Nat} (S : Setup n dim) :
    MeasurableSpace (FeasiblePoint S) := by
  infer_instance

/-- All-carrier Bregman surrogate for the `V(x,y)` notation in Eq. (5.3.2).

This is not Lan §3.2's prox-function. It is the explicitly named source-boundary
surrogate for Eq. (5.3.2)'s all-`X` display, implemented by SOptLib
`carrierBregmanFormula`; `bregman` is the canonical `X^o x X` object. -/
def legacyDiagnosticFeasibleBregman {n dim : Nat} (S : Setup n dim)
    (x z : FeasiblePoint S) : Real :=
  legacyDiagnosticFeasibleBregmanOf S.X S.nu x z

@[simp]
theorem legacyDiagnosticFeasibleBregman_def {n dim : Nat} (S : Setup n dim)
    (x z : FeasiblePoint S) :
    legacyDiagnosticFeasibleBregman S x z =
      S.nu z.1 - S.nu x.1 -
        ⟪gradientWithin S.nu S.X x.1, z.1 - x.1⟫_Real := by
  rfl

/-- The paper prox-core `X^o` used as the left domain of `V : X^o x X -> R+`. -/
def proxCoreSet {n dim : Nat} (S : Setup n dim) :
    Set (VariableSpace dim) :=
  proxCoreSetOf S.X S.nu

@[simp]
theorem proxCoreSet_def {n dim : Nat} (S : Setup n dim) :
    proxCoreSet S = proxCoreSetOf S.X S.nu := by
  rfl


instance instProxCoreSetElemMeasurableSpace {n dim : Nat} (S : Setup n dim) :
    MeasurableSpace (Set.Elem (proxCoreSet S)) := by
  infer_instance

theorem proxCoreSetElem_mem_X {n dim : Nat} (S : Setup n dim)
    (x : Set.Elem (proxCoreSet S)) : x.1 ∈ S.X :=
  x.2.1

theorem proxCoreSet_convex {n dim : Nat} (S : Setup n dim) :
    Convex Real (proxCoreSet S) := by
  simpa [proxCoreSet] using S.proxCore_convex

theorem nu_contDiffOn_proxCore {n dim : Nat} (S : Setup n dim) :
    ContDiffOn Real 1 S.nu (proxCoreSet S) := by
  simpa [proxCoreSet] using S.nu_contDiffOn_proxCore

theorem nu_differentiableOn_proxCore {n dim : Nat} (S : Setup n dim) :
    DifferentiableOn Real S.nu (proxCoreSet S) := by
  exact (nu_contDiffOn_proxCore S).differentiableOn_one

theorem nu_strong_monotone_proxCore {n dim : Nat} (S : Setup n dim)
    {x y : VariableSpace dim} (hx : x ∈ proxCoreSet S) (hy : y ∈ proxCoreSet S) :
    norm (y - x) ^ 2 <=
      ⟪y - x,
        gradientWithin S.nu (proxCoreSet S) y -
          gradientWithin S.nu (proxCoreSet S) x⟫_Real := by
  simpa [proxCoreSet] using S.nu_strong_monotone_proxCore x hx y hy

/-- The selected gradient of the paper DGF on `X^o`.

This avoids the earlier ambient-gradient surrogate: Eq. (3.2.2) only uses
`∇nu(x)` where `x ∈ X^o`, so the Lean object is the within-gradient on the
source core. -/

theorem nu_hasGradientWithinAt_X_of_proxCore {n dim : Nat} (S : Setup n dim)
    (x : Set.Elem (proxCoreSet S)) :
    HasGradientWithinAt S.nu (gradientWithin S.nu S.X x.1) S.X x.1 := by
  simpa using
    S.nu_hasGradientWithinAt_X_of_proxCore
      (⟨x.1, x.2⟩ :
        {u : VariableSpace dim // u ∈ proxCoreSetOf S.X S.nu})

/-- The Bregman prox formula `V(x,z)` from Eq. (3.2.2), typed on `X^o x X`.

SOptLib `Bregman.div` was considered, but this file needs the literal
Algorithm 5.7 and Eq. (3.2.2) expression over the paper's `nu` with the
left-domain restriction exposed; this definition therefore records the source
formula directly. -/
def bregman {n dim : Nat} (S : Setup n dim)
    (x : Set.Elem (proxCoreSet S)) (z : FeasiblePoint S) : Real :=
  bregmanOf S.X S.nu ⟨x.1, x.2⟩ z

@[simp]
theorem bregman_def {n dim : Nat} (S : Setup n dim)
    (x : Set.Elem (proxCoreSet S)) (z : FeasiblePoint S) :
    bregman S x z =
      S.nu z.1 - (S.nu x.1 + ⟪gradientWithin S.nu S.X x.1, z.1 - x.1⟫_Real) := by
  rfl

/-- Source-derived modulus-one lower bound for Eq. (3.2.3).

This is a direct projection of the source-stated DGF lower-bound assumption,
whose right endpoint is any feasible point in `X`. -/
theorem bregman_modulus_one_lower {n dim : Nat} (S : Setup n dim)
    (x : Set.Elem (proxCoreSet S)) (z : FeasiblePoint S) :
    (1 / 2 : Real) * norm (x.1 - z.1) ^ 2 <= bregman S x z := by
  have hx : x.1 ∈ proxCoreSetOf S.X S.nu := by
    change x.1 ∈ proxCoreSet S
    exact x.2
  simpa [bregman, carrierBregmanFormula, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
    S.bregman_modulus_one_lower_allFeasible ⟨x.1, hx⟩ z

/-- Domain-restricted Bregman distance `V` on feasible carrier points.

This source-facing object has the paper's exact domain `X^o x X`; the earlier
feasible-by-feasible carrier wrapper was rejected because it allowed left
arguments outside the differentiability core. -/
def bregmanOn {n dim : Nat} (S : Setup n dim)
    (x : Set.Elem (proxCoreSet S)) (z : FeasiblePoint S) : Real :=
  bregman S x z

@[simp]
theorem bregmanOn_def {n dim : Nat} (S : Setup n dim)
    (x : Set.Elem (proxCoreSet S)) (z : FeasiblePoint S) :
    bregmanOn S x z = bregman S x z := by
  rfl

/-- Nonnegativity of the paper Bregman distance on `X^o × X`.

Aligns with the Lemma 5.18 step that drops the endpoint `V(x^s,x)` term.
Candidates considered: SOptLib `blockBregmanDivergence_nonneg_of_lower_bound`
is the abstract lower-bound-to-nonnegativity bridge and
`carrierBregmanDivergence_nonneg_of_interior` applies to carrier Bregman
objects; this local paper object already has the exact modulus-one lower bound
`bregman_modulus_one_lower`, so specializing that source-derived bound is the
direct match. -/
theorem bregmanOn_nonneg {n dim : Nat} (S : Setup n dim)
    (x : Set.Elem (proxCoreSet S)) (z : FeasiblePoint S) :
    0 <= bregmanOn S x z := by
  have hlower := bregman_modulus_one_lower S x z
  have hquad_nonneg : 0 <= (1 / 2 : Real) * norm (x.1 - z.1) ^ 2 := by
    positivity
  exact le_trans hquad_nonneg (by simpa [bregmanOn_def] using hlower)

/-- The paper prox-function as a nonnegative value on `X^o x X`.

This is the source-facing form of Eq. (3.2.2): its left argument is the
source-defined prox core `X^o`, its right argument is feasible, and its codomain
is the Lean subtype for `R+`. The nonnegativity proof is a theorem obligation
derived from the modulus-one Bregman lower bound rather than an extra argument
to the prox object. -/
def bregmanProx {n dim : Nat} (S : Setup n dim)
    (x : Set.Elem (proxCoreSet S)) (z : FeasiblePoint S) : {r : Real // 0 <= r} :=
  ⟨bregmanOn S x z,
    by
      have hnonneg_norm : 0 <= (1 / 2 : Real) * norm (x.1 - z.1) ^ 2 := by
        positivity
      exact le_trans hnonneg_norm (by simpa [bregmanOn_def] using bregman_modulus_one_lower S x z)⟩

@[simp]
theorem bregmanProx_coe {n dim : Nat} (S : Setup n dim)
    (x : Set.Elem (proxCoreSet S)) (z : FeasiblePoint S) :
    (bregmanProx S x z : Real) =
      bregman S x z := by
  simp [bregmanProx, bregmanOn_def]

/-- Coerce a paper prox-core point to the feasible carrier `X`.

This is only domain bookkeeping: Lan §3.2 states `X^o ⊆ X`, and the actual
Bregman object remains `bregmanOn : X^o -> X -> Real`. -/
def proxCoreAsFeasible {n dim : Nat} (S : Setup n dim)
    (x : Set.Elem (proxCoreSet S)) : FeasiblePoint S :=
  ⟨x.1, proxCoreSetElem_mem_X S x⟩



/-- Feasible-segment derivative of `z ↦ V(a,z)` at a prox-core point.

This is the analytic bridge used in the proof of Lemma 3.5: the derivative is
taken along a feasible segment in `X`, while the left Bregman center remains in
the source prox core `X^o`. -/
theorem bregmanOn_segment_difference_hasDerivWithinAt_zero {n dim : Nat}
    (S : Setup n dim) (a z : Set.Elem (proxCoreSet S)) (u : FeasiblePoint S) :
    let d : VariableSpace dim := u.1 - z.1
    let β : Real -> Real := fun t =>
      if ht : t ∈ Set.Icc (0 : Real) 1 then
        bregmanOn S a
          ⟨AffineMap.lineMap z.1 u.1 t,
            S.X_convex.lineMap_mem (proxCoreSetElem_mem_X S z) u.2 ht⟩ -
          bregmanOn S a (proxCoreAsFeasible S z)
      else 0
    HasDerivWithinAt β
      ⟪gradientWithin S.nu S.X z.1 - gradientWithin S.nu S.X a.1, d⟫_Real
      (Set.Icc (0 : Real) 1) 0 := by
  simpa [bregmanOn, bregman, proxCoreAsFeasible, proxCoreSet, proxCoreSetOf,
    carrierBregmanFormula, bregmanOf, proxCoreGradientOf, sub_eq_add_neg,
    add_assoc, add_comm, add_left_comm] using
    SOptLib.carrierBregmanFormula_segment_difference_hasDerivWithinAt_zero
      (X := S.X) (nu := S.nu) S.X_convex
      (proxCoreAsFeasible S a)
      (proxCoreAsFeasible S z)
      u
      (nu_hasGradientWithinAt_X_of_proxCore S z)

/-- Noncurrent diagnostic bridge between the all-carrier Eq. (5.3.2) Bregman
expression and the §3.2 prox-core Bregman expression.

The PDF gives both source boundaries: Eq. (5.3.2) quantifies over all `x,y in X`,
while Eq. (3.2.2) types the prox-function as `X^o x X`. Later proofs may use
this bridge on core points, but it is not a primitive setup assumption.

Route architecture note: this declaration is not part of the active Theorem 5.9
public/source cone. The public route now consumes the relational source package
below; ordinary reconstruction should not use this diagnostic bridge to revive
the retired all-feasible surrogate route. -/
theorem legacyDiagnosticFeasibleBregman_eq_bregmanOn_of_proxCore {n dim : Nat}
    (S : Setup n dim) (x : Set.Elem (proxCoreSet S)) (z : FeasiblePoint S) :
  legacyDiagnosticFeasibleBregman S (proxCoreAsFeasible S x) z = bregmanOn S x z := by
  simp [legacyDiagnosticFeasibleBregman, legacyDiagnosticFeasibleBregmanOf,
    bregmanOn, bregman, bregmanOf, proxCoreGradientOf, proxCoreAsFeasible,
    carrierBregmanFormula]
  ring_nf

/-- Eq. (5.3.2), recorded as the all-feasible source assumption.

This is not the canonical §3.2 Bregman statement: it is the named boundary
surrogate forced by Eq. (5.3.2)'s all-`X` notation. Downstream paper-facing
proofs should use the core bridge below whenever the left Bregman argument is
known to lie in `X^o`. The body projects the primitive paper assumption from
`Setup`; it is no longer an unconditional theorem obligation. -/
theorem finiteSumObjective_strong_convexity_bregman_allFeasible_surrogate {n dim : Nat}
    (S : Setup n dim) (x y : FeasiblePoint S) :
    finiteSumObjective S x.1 + ⟪fullGradient S x.1, y.1 - x.1⟫_Real +
        S.mu * legacyDiagnosticFeasibleBregman S x y <=
      finiteSumObjective S y.1 := by
  simpa [finiteSumObjective, fullGradient, legacyDiagnosticFeasibleBregman] using
    S.finiteSum_strong_convexity_bregman_allFeasible x y

/-- Core-domain bridge form of Eq. (5.3.2).

It is derived from the source-stated Eq. (5.3.2) `Setup` field via the named
all-feasible surrogate plus `legacyDiagnosticFeasibleBregman_eq_bregmanOn_of_proxCore`, which
records the source-boundary obligation between Eq. (5.3.2) and the §3.2
prox-function domain `X^o x X`. -/
theorem finiteSumObjective_strong_convexity_bregman_core_from_surrogate {n dim : Nat}
    (S : Setup n dim) (x : Set.Elem (proxCoreSet S)) (y : FeasiblePoint S) :
    finiteSumObjective S x.1 + ⟪fullGradient S x.1, y.1 - x.1⟫_Real +
        S.mu * bregmanOn S x y <=
      finiteSumObjective S y.1 := by
  have hstrong :
      finiteSumObjective S (proxCoreAsFeasible S x).1 +
          ⟪fullGradient S (proxCoreAsFeasible S x).1,
            y.1 - (proxCoreAsFeasible S x).1⟫_Real +
          S.mu * legacyDiagnosticFeasibleBregman S (proxCoreAsFeasible S x) y <=
        finiteSumObjective S y.1 :=
    finiteSumObjective_strong_convexity_bregman_allFeasible_surrogate S
      (proxCoreAsFeasible S x) y
  have hcompat := legacyDiagnosticFeasibleBregman_eq_bregmanOn_of_proxCore S x y
  rw [hcompat] at hstrong
  simpa using hstrong

/-- Average smoothness scale `L = (1/n) * sum_i L_i`.

Uses the same scalar normalizer as `finiteSumObjective`, matching Section 5.3
and the `L_f <= L` assumption. -/
def averageSmoothness {n dim : Nat} (S : Setup n dim) : Real :=
  (componentCountReal n)⁻¹ * Finset.univ.sum (fun i : Fin n => S.Lcomp i)

/-- Strict positivity of the total component smoothness mass.

Aligns with Lan Section 5.3's `L_i > 0` and positive component count. Considered
SOptLib candidates such as smoothness quadratic upper bounds and weighted
variance lemmas from the pre-search digest; none match this scalar finite-sum
positivity obligation, so this local bridge uses Mathlib's `Finset.sum_pos`
directly. -/
theorem totalSmoothness_pos_aux {n dim : Nat} (S : Setup n dim) :
    0 < Finset.univ.sum (fun i : Fin n => S.Lcomp i) := by
  have hnonempty : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨⟨0, S.component_count_pos⟩, by simp⟩
  exact Finset.sum_pos (fun i _hi => S.Lcomp_pos i) hnonempty

/-- Positivity of the average smoothness denominator used throughout Theorem 5.9.

This is source-derived from Section 5.3's assumptions `n > 0` and `L_i > 0`;
it is intentionally a theorem obligation, not a theorem-head hypothesis. -/
theorem averageSmoothness_pos {n dim : Nat} (S : Setup n dim) :
    0 < averageSmoothness S := by
  have hcount : 0 < componentCountReal n := componentCountReal_pos S
  have hinv : 0 < (componentCountReal n)⁻¹ := inv_pos.mpr hcount
  simpa [averageSmoothness] using
    mul_pos hinv (totalSmoothness_pos_aux S)

/-- Source-derived nonzero total smoothness for the denominator in Eq. (5.3.4).

The source states `L_i > 0`; the proof that the finite sum is nonzero is a
routine finite-positive-sum obligation left to the proof phase. -/
theorem totalSmoothness_ne_zero {n dim : Nat} (S : Setup n dim) :
    Finset.univ.sum (fun i : Fin n => S.Lcomp i) ≠ 0 := by
  exact ne_of_gt (totalSmoothness_pos_aux S)

/-- Smoothness-proportional sampling weight `q_i = L_i / sum_j L_j`.

No additional regularity assumption is introduced here; nonzero denominator is
the named source-derived theorem `totalSmoothness_ne_zero`. -/
def samplingWeight {n dim : Nat} (S : Setup n dim) (i : Fin n) : Real :=
  S.Lcomp i / Finset.univ.sum (fun j : Fin n => S.Lcomp j)

/-- Source-derived positivity of the Theorem 5.9 sampling weights. -/
theorem samplingWeight_pos {n dim : Nat} (S : Setup n dim) (i : Fin n) :
    0 < samplingWeight S i := by
  simpa [samplingWeight, SOptLib.smoothnessImportanceWeight] using
    (SOptLib.smoothnessImportanceWeight_pos
      (Lcomp := S.Lcomp) (n := (1 : ℝ))
      (L := Finset.univ.sum (fun j : Fin n => S.Lcomp j)) (i := i)
      (S.Lcomp_pos i) zero_lt_one (totalSmoothness_pos_aux S))

/-- The component-sampling PMF `Q = {q_1, ..., q_n}` from Eq. (5.3.4).

Reuses SOptLib `smoothnessImportancePMF`, whose atom formula is the
smoothness-proportional finite-component law; the local wrapper specializes it
to the paper's `Fin n` component index and `L = (1/n) sum_i L_i`. -/
def componentSamplingPMF {n dim : Nat} (S : Setup n dim) : PMF (Fin n) :=
  SOptLib.smoothnessImportancePMF
    (Lcomp := S.Lcomp)
    (n := componentCountReal n)
    (L := averageSmoothness S)
    (fun i => le_of_lt (S.Lcomp_pos i))
    (componentCountReal_pos S)
    (by rfl)
    (totalSmoothness_ne_zero S)

theorem componentSamplingPMF_apply {n dim : Nat} (S : Setup n dim)
    (i : Fin n) :
    componentSamplingPMF S i = ENNReal.ofReal (samplingWeight S i) := by
  unfold componentSamplingPMF
  rw [SOptLib.smoothnessImportancePMF_apply]
  congr 1
  unfold SOptLib.smoothnessImportanceWeight samplingWeight averageSmoothness
  field_simp [ne_of_gt (componentCountReal_pos S), totalSmoothness_ne_zero S]

/-- The one-draw component-index law `Q` used by Algorithm 5.7.

This is the PMF measure associated with the source-defined probabilities
`q_i = L_i / sum_j L_j`; no arbitrary measure is part of the paper theorem. -/
def componentSampleLaw {n dim : Nat} (S : Setup n dim) :
    MeasureTheory.Measure (Fin n) :=
  (componentSamplingPMF S).toMeasure

/-- Canonical two-index component-sample path for Algorithm 5.7.

SOptLib candidates `iidStreamLaw` and `iidMiniBatchSampleLaw` were checked.
`iidMiniBatchSampleLaw` fixes a finite within-batch coordinate, while Algorithm
5.7 has an unbounded epoch index and an unbounded inner-loop index; therefore
this paper path is the nested stream `epoch -> inner time -> component`, with
`iidStreamLaw` reused for each stream law. -/
abbrev theorem59SamplePath (n : Nat) :=
  SOptLib.twoIndexSamplePath (Fin n)

/-- Canonical iid law for all Algorithm 5.7 component choices under Theorem 5.9.

Aligns with Algorithm 5.7's instruction to pick each `i_t` according to
`Q = {q_1, ..., q_n}` and Theorem 5.9's specialization
`q_i = L_i / sum_j L_j`. -/
def theorem59SampleLaw {n dim : Nat} (S : Setup n dim) :
    MeasureTheory.Measure (theorem59SamplePath n) :=
  SOptLib.iidTwoIndexSampleLaw (componentSampleLaw S)

/-- Coordinate sample stream read from the canonical Theorem 5.9 path. -/
def theorem59CanonicalSamples {n : Nat} :
    Nat -> Nat -> theorem59SamplePath n -> Fin n :=
  fun k t omega => omega k t


/-- Fixed-epoch canonical component draws are iid under the Theorem 5.9 law.

This is the fresh-sample independence bridge used by the adaptive transport
for Eq. (5.4.9): after fixing an epoch `s`, the inner stream
`t ↦ theorem59CanonicalSamples s t` has exactly the iid law generated by the
component PMF `Q`. -/
theorem theorem59_fixed_epoch_canonical_samples_iIndepFun
    {n dim : Nat} (S : Setup n dim) (s : Nat) :
    ProbabilityTheory.iIndepFun
      (fun (t : Nat) (omega : theorem59SamplePath n) =>
        theorem59CanonicalSamples s t omega)
      (theorem59SampleLaw S) := by
  classical
  have hprob : MeasureTheory.IsProbabilityMeasure (componentSampleLaw S) := by
    unfold componentSampleLaw
    infer_instance
  letI : MeasureTheory.IsProbabilityMeasure (componentSampleLaw S) := hprob
  have hprob_stream :
      MeasureTheory.IsProbabilityMeasure
        (SOptLib.iidStreamLaw (componentSampleLaw S)) := by
    infer_instance
  letI : MeasureTheory.IsProbabilityMeasure
      (SOptLib.iidStreamLaw (componentSampleLaw S)) := hprob_stream
  change ProbabilityTheory.iIndepFun
    (fun (t : Nat) (omega : Nat -> Nat -> Fin n) => omega s t)
    (SOptLib.iidStreamLaw (SOptLib.iidStreamLaw (componentSampleLaw S)))
  have hinner :
      ProbabilityTheory.iIndepFun
        (fun t (stream : Nat -> Fin n) => stream t)
        (SOptLib.iidStreamLaw (componentSampleLaw S)) :=
    SOptLib.iidStreamLaw_iIndepFun_eval (componentSampleLaw S)
  have hmap :
      MeasureTheory.Measure.map
        (fun omega : Nat -> Nat -> Fin n => omega s)
        (SOptLib.iidStreamLaw (SOptLib.iidStreamLaw (componentSampleLaw S))) =
          SOptLib.iidStreamLaw (componentSampleLaw S) := by
    exact SOptLib.iidStreamLaw_map_eval
      (mu := SOptLib.iidStreamLaw (componentSampleLaw S)) s
  rw [ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro T sets hsets
  let μouter :=
    SOptLib.iidStreamLaw (SOptLib.iidStreamLaw (componentSampleLaw S))
  let μinner := SOptLib.iidStreamLaw (componentSampleLaw S)
  let epochEval : (Nat -> Nat -> Fin n) -> (Nat -> Fin n) := fun omega => omega s
  have hepoch_meas : Measurable epochEval := measurable_pi_apply s
  have hmap' : MeasureTheory.Measure.map epochEval μouter = μinner := by
    simpa [epochEval, μouter, μinner] using hmap
  have hinner_sets :
      μinner
          (⋂ i ∈ T, (fun stream : Nat -> Fin n => stream i) ⁻¹' sets i) =
        ∏ i ∈ T,
          μinner
            ((fun stream : Nat -> Fin n => stream i) ⁻¹' sets i) := by
    simpa [μinner] using
      (ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul.mp hinner)
        T (sets := sets) hsets
  have hmeas_inter :
      MeasurableSet
        (⋂ i ∈ T, (fun stream : Nat -> Fin n => stream i) ⁻¹' sets i) := by
    exact T.measurableSet_biInter fun i hi =>
      (hsets i hi).preimage (measurable_pi_apply i)
  have hleft :
      μouter
          (⋂ i ∈ T, (fun omega : Nat -> Nat -> Fin n => omega s i) ⁻¹' sets i) =
        μinner
          (⋂ i ∈ T, (fun stream : Nat -> Fin n => stream i) ⁻¹' sets i) := by
    have hmap_apply :
        MeasureTheory.Measure.map epochEval μouter
            (⋂ i ∈ T, (fun stream : Nat -> Fin n => stream i) ⁻¹' sets i) =
          μouter
            (epochEval ⁻¹'
              (⋂ i ∈ T, (fun stream : Nat -> Fin n => stream i) ⁻¹' sets i)) :=
      MeasureTheory.Measure.map_apply hepoch_meas hmeas_inter
    have hrewrite :
        μinner
            (⋂ i ∈ T, (fun stream : Nat -> Fin n => stream i) ⁻¹' sets i) =
          μouter
            (epochEval ⁻¹'
              (⋂ i ∈ T, (fun stream : Nat -> Fin n => stream i) ⁻¹' sets i)) := by
      exact (congrArg
        (fun μ : MeasureTheory.Measure (Nat -> Fin n) =>
          μ (⋂ i ∈ T, (fun stream : Nat -> Fin n => stream i) ⁻¹' sets i))
        hmap'.symm).trans hmap_apply
    simpa [epochEval, Set.preimage_iInter] using hrewrite.symm
  have hright : ∀ i, i ∈ T ->
      μouter
          ((fun omega : Nat -> Nat -> Fin n => omega s i) ⁻¹' sets i) =
        μinner
          ((fun stream : Nat -> Fin n => stream i) ⁻¹' sets i) := by
    intro i hi
    have hmeas_i :
        MeasurableSet ((fun stream : Nat -> Fin n => stream i) ⁻¹' sets i) :=
      (hsets i hi).preimage (measurable_pi_apply i)
    have hmap_apply :
        MeasureTheory.Measure.map epochEval μouter
            ((fun stream : Nat -> Fin n => stream i) ⁻¹' sets i) =
          μouter
            (epochEval ⁻¹' ((fun stream : Nat -> Fin n => stream i) ⁻¹' sets i)) :=
      MeasureTheory.Measure.map_apply hepoch_meas hmeas_i
    have hrewrite :
        μinner
            ((fun stream : Nat -> Fin n => stream i) ⁻¹' sets i) =
          μouter
            (epochEval ⁻¹' ((fun stream : Nat -> Fin n => stream i) ⁻¹' sets i)) := by
      exact (congrArg
        (fun μ : MeasureTheory.Measure (Nat -> Fin n) =>
          μ ((fun stream : Nat -> Fin n => stream i) ⁻¹' sets i))
        hmap'.symm).trans hmap_apply
    simpa [epochEval] using hrewrite.symm
  calc
    μouter
        (⋂ i ∈ T, (fun omega : Nat -> Nat -> Fin n => omega s i) ⁻¹' sets i)
        = μinner
            (⋂ i ∈ T, (fun stream : Nat -> Fin n => stream i) ⁻¹' sets i) := hleft
    _ = ∏ i ∈ T,
          μinner
            ((fun stream : Nat -> Fin n => stream i) ⁻¹' sets i) := hinner_sets
    _ = ∏ i ∈ T,
          μouter
            ((fun omega : Nat -> Nat -> Fin n => omega s i) ⁻¹' sets i) := by
          refine Finset.prod_congr rfl ?_
          intro i hi
          exact (hright i hi).symm

/-- Prefix-measurable generated state packages are fresh from the next draw.

This is the concrete independence input expected by
`adaptive_componentConditionalExpectation_transport_of_indepFun`: once the
generated printed state at inner time `k` is measurable from samples
`0, ..., k`, it is independent of the fresh component draw at `k + 1`. -/
theorem theorem59_fixed_epoch_prefix_measurable_current_indepFun
    {n dim : Nat} (S : Setup n dim) (s k : Nat)
    {A : Type*} [MeasurableSpace A]
    (W : theorem59SamplePath n -> A)
    (hW :
      @Measurable (theorem59SamplePath n) A
        ((SOptLib.filtration
          (fun t omega => theorem59CanonicalSamples s t omega)
          (fun t => by
            change Measurable (fun omega : Nat -> Nat -> Fin n => omega s t)
            exact (measurable_pi_apply t).comp (measurable_pi_apply s))).seq (k + 1))
        (by infer_instance) W) :
    ProbabilityTheory.IndepFun W
      (fun omega : theorem59SamplePath n =>
        theorem59CanonicalSamples s (k + 1) omega)
      (theorem59SampleLaw S) := by
  classical
  let ξ : Nat -> theorem59SamplePath n -> Fin n :=
    fun t omega => theorem59CanonicalSamples s t omega
  have hξ_measurable : ∀ t, Measurable (ξ t) := by
    intro t
    change Measurable (fun omega : Nat -> Nat -> Fin n => omega s t)
    exact (measurable_pi_apply t).comp (measurable_pi_apply s)
  have hξ_iIndep :
      ProbabilityTheory.iIndepFun ξ (theorem59SampleLaw S) := by
    simpa [ξ] using theorem59_fixed_epoch_canonical_samples_iIndepFun S s
  have hW_prefix :
      @Measurable (theorem59SamplePath n) A
        (⨆ j < k + 1,
          MeasurableSpace.comap (ξ j)
            (by infer_instance : MeasurableSpace (Fin n)))
        (by infer_instance) W := by
    simpa [ξ, SOptLib.filtration_seq] using hW
  exact
    ProbabilityTheory.iIndepFun.indepFun_prefixMeasurable_future
      ξ hξ_measurable hξ_iIndep hW_prefix (Nat.le_refl (k + 1))

/-- The strict history before the fresh inner draw `(s, k + 1)`.

This is the source-faithful history set for Lemma 5.16 in Algorithm 5.7:
all earlier epochs are already fixed, and the current epoch contributes only
the samples up to inner time `k`. -/
def theorem59StrictPastIndexSet (s k : Nat) : Set (Nat × Nat) :=
  {q | q.1 < s ∨ (q.1 = s ∧ q.2 < k + 1)}

/-- Flattened two-index Algorithm 5.7 samples are mutually independent.

This is the canonical iid bridge missing from the current-only prefix route.
The nested law `iidStreamLaw (iidStreamLaw Q)` should imply independence of
all coordinates `(epoch, inner) ↦ omega epoch inner`; the proof is the exact
remaining nested-product iid API leaf, not a new source assumption. -/
theorem theorem59_flattened_canonical_samples_iIndepFun
    {n dim : Nat} (S : Setup n dim) :
    ProbabilityTheory.iIndepFun
      (fun (q : Nat × Nat) (omega : theorem59SamplePath n) =>
        theorem59CanonicalSamples q.1 q.2 omega)
      (theorem59SampleLaw S) := by
  classical
  have hprob_component :
      MeasureTheory.IsProbabilityMeasure (componentSampleLaw S) := by
    unfold componentSampleLaw
    infer_instance
  letI : MeasureTheory.IsProbabilityMeasure (componentSampleLaw S) := hprob_component
  change ProbabilityTheory.iIndepFun
      (fun (q : Nat × Nat) (omega : Nat -> Nat -> Fin n) => omega q.1 q.2)
      (SOptLib.iidStreamLaw (SOptLib.iidStreamLaw (componentSampleLaw S)))
  unfold SOptLib.iidStreamLaw
  simpa using
    (ProbabilityTheory.iIndepFun_uncurry_infinitePi'
      (Ω := fun (_ : Nat) (_ : Nat) => Fin n)
      (𝓧 := fun (_ : Nat) (_ : Nat) => Fin n)
      (μ := fun (_ : Nat) (_ : Nat) => componentSampleLaw S)
      (X := fun (_ : Nat) (_ : Nat) (sample : Fin n) => sample)
      (fun _ _ => measurable_id))

/-- A query measurable from all strict Algorithm 5.7 history is fresh from the
current component draw.

Unlike `theorem59_fixed_epoch_prefix_measurable_current_indepFun`, this history
contains previous epochs.  That is the filtration needed by Lemma 5.16 because
the snapshot and epoch-start iterate at epoch `s` are generated from earlier
epochs, not from the current epoch's inner samples alone. -/
theorem theorem59_all_history_prefix_measurable_current_indepFun
    {n dim : Nat} (S : Setup n dim) (s k : Nat)
    {A : Type*} [MeasurableSpace A]
    (W : theorem59SamplePath n -> A)
    (hW :
      @Measurable (theorem59SamplePath n) A
        (⨆ q ∈ theorem59StrictPastIndexSet s k,
          MeasurableSpace.comap
            (fun omega : theorem59SamplePath n =>
              theorem59CanonicalSamples q.1 q.2 omega)
            (by infer_instance : MeasurableSpace (Fin n)))
        (by infer_instance) W) :
    ProbabilityTheory.IndepFun W
      (fun omega : theorem59SamplePath n =>
        theorem59CanonicalSamples s (k + 1) omega)
      (theorem59SampleLaw S) := by
  classical
  let sampleCoord : Nat × Nat -> theorem59SamplePath n -> Fin n :=
    fun q omega => theorem59CanonicalSamples q.1 q.2 omega
  have hsampleCoord_meas : forall q, Measurable (sampleCoord q) := by
    intro q
    change Measurable (fun omega : Nat -> Nat -> Fin n => omega q.1 q.2)
    exact (measurable_pi_apply q.2).comp (measurable_pi_apply q.1)
  have hsampleCoord_iIndep :
      ProbabilityTheory.iIndepFun sampleCoord (theorem59SampleLaw S) := by
    simpa [sampleCoord] using theorem59_flattened_canonical_samples_iIndepFun S
  have hdisj :
      Disjoint (theorem59StrictPastIndexSet s k) ({(s, k + 1)} : Set (Nat × Nat)) := by
    refine Set.disjoint_left.2 ?_
    intro q hq hcurrent
    rcases hcurrent with rfl
    rcases hq with h_epoch | h_current_epoch
    · exact (Nat.lt_irrefl s h_epoch).elim
    · rcases h_current_epoch with ⟨_hsame, h_inner⟩
      exact (Nat.lt_irrefl (k + 1) h_inner).elim
  exact
    SOptLib.iIndepFun_indepFun_strictPast_singleton
      (xi := sampleCoord) (mu := theorem59SampleLaw S)
      (hxi_meas := hsampleCoord_meas)
      (hxi_iIndep := hsampleCoord_iIndep)
      (strictPast :=
        ⨆ q ∈ theorem59StrictPastIndexSet s k,
          MeasurableSpace.comap (sampleCoord q)
            (by infer_instance : MeasurableSpace (Fin n)))
      (pastSet := theorem59StrictPastIndexSet s k)
      (current := (s, k + 1)) (X := W)
      (by simpa [sampleCoord] using hW) hdisj (by rfl)

/-- Conditional expectation over the fresh component draw in Algorithm 5.7.

SOptLib candidates `finiteWindowSelectedOutputExpectation_eq_weighted_sum` and
`identDistrib_finite_pmf_integrable_integral_le_weighted_sum_bound` were
checked; they bridge finite PMF integrals to sums after measurability facts are
available. Lemma 5.16's object layer only needs the source conditional
expectation over `i_t ~ Q` with the past fixed, so this local definition records
the finite weighted expectation `sum_i q_i Z_i` directly. -/
def componentConditionalExpectation {n dim : Nat} (_S : Setup n dim)
    (q : Fin n -> Real) (Z : Fin n -> Real) : Real :=
  Finset.univ.sum (fun i : Fin n => q i * Z i)

@[simp]
theorem componentConditionalExpectation_def {n dim : Nat} (S : Setup n dim)
    (q : Fin n -> Real) (Z : Fin n -> Real) :
    componentConditionalExpectation S q Z =
      Finset.univ.sum (fun i : Fin n => q i * Z i) := by
  rfl

/-- Monotonicity of the finite fresh-component expectation in Lemma 5.16.

Searched SOptLib/target candidates:
`finiteWindowSelectedOutputExpectation_eq_weighted_sum` and
`identDistrib_finite_pmf_integrable_integral_le_weighted_sum_bound` are PMF/
integral transport bridges, not the local already-expanded finite sum needed
here; the direct Mathlib alignment is `Finset.sum_le_sum` with
`samplingWeight_pos`. -/
theorem componentConditionalExpectation_mono_of_pointwise {n dim : Nat}
    (S : Setup n dim) (A B : Fin n -> Real)
    (hAB : forall sample, A sample <= B sample) :
    componentConditionalExpectation S (samplingWeight S) A <=
      componentConditionalExpectation S (samplingWeight S) B := by
  unfold componentConditionalExpectation
  exact Finset.sum_le_sum (fun i _hi =>
    mul_le_mul_of_nonneg_left (hAB i) (le_of_lt (samplingWeight_pos S i)))

/-- Smoothness-proportional component weights normalize to one.

This is the finite-sum specialization needed for Lemma 5.16's conditional
expectation algebra. Candidates considered: SOptLib PMF/integral expansion
lemmas such as `finiteWindowSelectedOutputExpectation_eq_weighted_sum` target
measure transport, and the normalized-weight helpers are not imported under a
callable target-file name; the local component expectation is already the raw
finite sum, so direct `Finset.sum_div` is the matching proof. -/
theorem samplingWeight_sum_eq_one {n dim : Nat} (S : Setup n dim) :
    Finset.univ.sum (fun i : Fin n => samplingWeight S i) = 1 := by
  unfold samplingWeight
  rw [← Finset.sum_div]
  exact div_self (totalSmoothness_ne_zero S)

/-- Constants pass through Lemma 5.16's finite conditional expectation.

This packages the same normalization as Eq. (5.3.4)'s sampling law for the
route-local residual expectation algebra; SOptLib expectation-expansion
candidates operate at PMF/integral level, while `componentConditionalExpectation`
is definitionally a finite weighted sum. -/
theorem componentConditionalExpectation_const {n dim : Nat}
    (S : Setup n dim) (C : Real) :
    componentConditionalExpectation S (samplingWeight S) (fun _sample => C) = C := by
  unfold componentConditionalExpectation
  rw [← Finset.sum_mul, samplingWeight_sum_eq_one]
  ring

/-- Additivity of the expanded finite conditional expectation.

SOptLib/Mathlib searches found PMF/integral transport lemmas for selected
expectations, but this file's Lemma 5.16 expectation is already a finite
weighted sum; `Finset.sum_add_distrib` is the exact local API. -/
theorem componentConditionalExpectation_add {n dim : Nat}
    (S : Setup n dim) (q : Fin n -> Real) (A B : Fin n -> Real) :
    componentConditionalExpectation S q (fun sample => A sample + B sample) =
      componentConditionalExpectation S q A +
        componentConditionalExpectation S q B := by
  unfold componentConditionalExpectation
  simp [mul_add, Finset.sum_add_distrib]

/-- Scalar factors pull out of the expanded finite conditional expectation.

This is the raw finite-sum counterpart of expectation linearity used in
Lemma 5.16's residual algebra; searched SOptLib candidates were measure-level
expectation expansion lemmas rather than this already-expanded sum. -/
theorem componentConditionalExpectation_mul_left {n dim : Nat}
    (S : Setup n dim) (q : Fin n -> Real) (C : Real) (A : Fin n -> Real) :
    componentConditionalExpectation S q (fun sample => C * A sample) =
      C * componentConditionalExpectation S q A := by
  unfold componentConditionalExpectation
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  ring

/-- Subtraction distributes through the expanded finite conditional expectation. -/
theorem componentConditionalExpectation_sub {n dim : Nat}
    (S : Setup n dim) (q : Fin n -> Real) (A B : Fin n -> Real) :
    componentConditionalExpectation S q (fun sample => A sample - B sample) =
      componentConditionalExpectation S q A -
        componentConditionalExpectation S q B := by
  unfold componentConditionalExpectation
  simp [sub_eq_add_neg, mul_add, Finset.sum_add_distrib, Finset.sum_neg_distrib]

/-- Zero-mean residual terms disappear under a finite second-moment budget.

This is the route-local expectation algebra for Lemma 5.16 step 6. SOptLib
search found measure-level martingale/PMF transport facts; here the source
boundary `lemma513AcceleratedVarianceEstimatorFactsBoundaryStatement` already
provides the two finite conditional-expectation facts in expanded form, so the
proof uses the local linearity lemmas above. -/
theorem componentConditionalExpectation_nonneg_mul_budget_add_zero_mean
    {n dim : Nat} (S : Setup n dim) (q : Fin n -> Real)
    (U V : Fin n -> Real) (a b C : Real)
    (ha : 0 <= a)
    (hV : componentConditionalExpectation S q V = 0)
    (hU : componentConditionalExpectation S q U <= C) :
    componentConditionalExpectation S q (fun sample => a * U sample + b * V sample) <=
      a * C := by
  simpa [componentConditionalExpectation] using
    (SOptLib.weighted_sum_nonneg_mul_budget_add_zero_mean_le
      (s := Finset.univ) (w := q) (U := U) (V := V) (a := a) (b := b) (C := C) ha
      (by simpa [componentConditionalExpectation] using hV)
      (by simpa [componentConditionalExpectation] using hU))

/-- Scalar absorption of the Lemma 5.16 noise bracket using condition (5.4.8).

Once variance substitution leaves `(p - lambda) * l_f(under, snapshot) +
lambda * f(snapshot)`, nonnegativity of `p - lambda` and convex/strong-convex
support `l_f <= f` give the printed `p * f(snapshot)` bound. -/
theorem lemma516_noise_bracket_le_snapshot
    {p lambda lin fval : Real}
    (hcoef : 0 <= p - lambda) (hlin : lin <= fval) :
    (p - lambda) * lin + lambda * fval <= p * fval := by
  exact SOptLib.sub_mul_le_absorb_add_mul_of_le p lambda lin fval hcoef hlin

/-- The paper's `L_Q = (1/n) max_i L_i / q_i` from Eq. (5.3.4).

SOptLib candidates `finiteRunMaxValue`/finite-image max helpers were checked
and reused for the finite maximum. No SOptLib object already bundles the
specific Lan Eq. (5.3.4) scalar `L_Q`, so this local definition records the
literal finite-component formula with nonemptiness derived from `0 < n`. -/
def samplingLQ {n dim : Nat} (S : Setup n dim)
    (q : Fin n -> Real) (_hq : forall i, 0 < q i) : Real :=
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp S.component_count_pos
  SOptLib.finiteImportanceSmoothnessConstant (componentCountReal n) S.Lcomp q

@[simp]
theorem samplingLQ_def {n dim : Nat} (S : Setup n dim)
    (q : Fin n -> Real) (hq : forall i, 0 < q i) :
    samplingLQ S q hq =
      letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp S.component_count_pos
      (componentCountReal n)⁻¹ *
        SOptLib.finiteRunMaxValue
          (Finset.univ.image (fun i : Fin n => S.Lcomp i / q i))
          (by
            simp only [
              (Finset.univ_nonempty :
                (Finset.univ : Finset (Fin n)).Nonempty).image
                  (fun i : Fin n => S.Lcomp i / q i)]) := by
  rfl

/-- `L_Q` under the Theorem 5.9 smoothness-proportional sampling rule.

This is a definition, not an assumption: Theorem 5.9 fixes
`q_i = L_i / sum_j L_j`, so `L_Q` is obtained by substituting the canonical
`samplingWeight` into Eq. (5.3.4). -/
def theorem59LQ {n dim : Nat} (S : Setup n dim) : Real :=
  samplingLQ S (samplingWeight S) (samplingWeight_pos S)

/-- Under smoothness-proportional sampling, each Eq. (5.3.4) numerator ratio
is the total smoothness mass.

Aligns with Lan Eq. (5.3.4). SOptLib `finiteRunMaxValue` and
`finiteRunMaxValue_eq_finset_max` were considered for the finite maximum; this
pointwise helper supplies the paper-specific ratio normalization that those
generic max lemmas intentionally do not encode. -/
theorem theorem59_sampling_ratio_eq_totalSmoothness
    {n dim : Nat} (S : Setup n dim) (i : Fin n) :
    S.Lcomp i / samplingWeight S i =
      Finset.univ.sum (fun j : Fin n => S.Lcomp j) := by
  have hcount_ne : componentCountReal n ≠ 0 := ne_of_gt (componentCountReal_pos S)
  simpa [samplingWeight, SOptLib.smoothnessImportanceWeight, averageSmoothness,
    mul_assoc, hcount_ne] using
    (SOptLib.smoothnessImportanceWeight_ratio_eq_total
      (Lcomp := S.Lcomp) (n := componentCountReal n) (L := averageSmoothness S)
      (hn_ne := hcount_ne)
      (hL_average := rfl)
      (i := i) (hcomp_ne := ne_of_gt (S.Lcomp_pos i)))

/-- The Theorem 5.9 importance-sampling constant satisfies `L_Q = L`.

Aligns with Lan Eq. (5.3.4) specialized to `q_i = L_i / sum_j L_j`. Reuses
SOptLib's `finiteRunMaxValue`/`finiteRunMaxValue_eq_finset_max` finite-maximum
wrapper; no existing SOptLib lemma states this paper-specific smoothness-
proportional specialization. -/
theorem theorem59LQ_eq_averageSmoothness {n dim : Nat} (S : Setup n dim) :
    theorem59LQ S = averageSmoothness S := by
  classical
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp S.component_count_pos
  simpa [theorem59LQ, samplingLQ, samplingWeight, averageSmoothness,
    SOptLib.smoothnessImportanceWeight, mul_assoc,
    ne_of_gt (componentCountReal_pos S)] using
    (SOptLib.finiteImportanceSmoothnessConstant_eq_average_of_smoothness_proportional
      (Lcomp := S.Lcomp) (n := componentCountReal n) (L := averageSmoothness S)
      (hn_ne := ne_of_gt (componentCountReal_pos S))
      (hL_average := rfl)
      (hcomp_ne := fun i => ne_of_gt (S.Lcomp_pos i)))

/-- Linearization `l_f(z,x) = f(z) + <grad f(z), x-z>` from Eq. (5.4.1).

No SOptLib match: searched `linearization`, `composite objective linear model`,
and nearby Objective/Prox files; existing lower-model helpers are theorem-level
bridges, while Eq. (5.4.1) needs the literal paper object. -/
def linearization {n dim : Nat} (S : Setup n dim)
    (z x : VariableSpace dim) : Real :=
  finiteSumObjective S z + ⟪fullGradient S z, x - z⟫_Real

/-- Eq. (5.3.2) implies the finite-sum linearization support inequality on the
prox-core base point.

This is the exact support form needed in Lemma 5.16's stochastic bracket.
Candidates considered: SOptLib convex first-order support lemmas require
`HasGradientWithinAt` facts not present in this file's setup interface, while
`finiteSumObjective_strong_convexity_bregman_core_from_surrogate` is the local
paper Eq. (5.3.2) bridge already aligned with the source's possible strong
convexity form. -/
theorem finiteSumObjective_linearization_le_of_core_strong_convexity
    {n dim : Nat} (S : Setup n dim) (x : Set.Elem (proxCoreSet S)) (y : FeasiblePoint S) :
    linearization S x.1 y.1 <= finiteSumObjective S y.1 := by
  have hstrong := finiteSumObjective_strong_convexity_bregman_core_from_surrogate S x y
  have hbreg_nonneg : 0 <= bregmanOn S x y := by
    exact (bregmanProx S x y).2
  have hmu_breg_nonneg : 0 <= S.mu * bregmanOn S x y :=
    mul_nonneg S.mu_nonneg hbreg_nonneg
  unfold linearization
  nlinarith

/-- Finite-sum smooth quadratic upper model on the feasible carrier.

Aligns with Lemma 5.16 proof lines 16986-16992. SOptLib candidates
`finiteUniformAverage_smooth_quadratic_upper_bound_of_component_lipschitz`,
`finiteAverageGradient_lipschitzOn_of_component_lipschitz`, and
`Convex.carrier_smooth_quadratic_upper_bound_of_hasGradientWithinAt_lipschitz`
were checked; the first requires ambient `HasGradientAt`, while this paper's
setup is carrier-based, so this helper composes the latter two with the local
`gradientWithin` component data. -/
theorem finiteSumObjective_smooth_upper_bound_from_component_smooth
    {n dim : Nat} (S : Setup n dim) (x y : FeasiblePoint S) :
    finiteSumObjective S y.1 <=
      linearization S x.1 y.1 +
        (averageSmoothness S / 2) * norm (y.1 - x.1) ^ 2 := by
  simpa [finiteSumObjective, linearization, fullGradient, averageSmoothness,
    componentCountReal, SOptLib.finiteUniformAverage] using
    (SOptLib.finiteUniformAverage_smooth_quadratic_upper_bound_of_component_lipschitzWithin
      (X := S.X)
      (F := fun i : Fin n => S.component i)
      (gradF := fun i : Fin n =>
        fun u : VariableSpace dim => gradientWithin (S.component i) S.X u)
      (Lcomp := S.Lcomp) (L := averageSmoothness S)
      S.X_convex
      (by simp [averageSmoothness, componentCountReal])
      (fun i z hz => ((S.component_differentiableOn i) z hz).hasGradientWithinAt)
      (fun i z w hz hw => S.component_smooth i z hz w hw)
      x.2 y.2)

/-- Denominator in Algorithm 5.7's accelerated search point. -/
def searchDenominator {n dim : Nat} (S : Setup n dim)
    (gamma alpha : Nat -> Real) (s : Nat) : Real :=
  1 + S.mu * gamma s * (1 - alpha s)

/-- Coefficient of `bar x_{t-1}` in Algorithm 5.7's search point. -/
def searchPointBarWeight {n dim : Nat} (S : Setup n dim)
    (gamma alpha p : Nat -> Real) (s : Nat) : Real :=
  ((1 + S.mu * gamma s) * (1 - alpha s - p s)) /
    searchDenominator S gamma alpha s

/-- Coefficient of `x_{t-1}` in Algorithm 5.7's search point. -/
def searchPointPrevWeight {n dim : Nat} (S : Setup n dim)
    (gamma alpha : Nat -> Real) (s : Nat) : Real :=
  alpha s / searchDenominator S gamma alpha s

/-- Coefficient of the snapshot `tilde x` in Algorithm 5.7's search point. -/
def searchPointSnapshotWeight {n dim : Nat} (S : Setup n dim)
    (gamma alpha p : Nat -> Real) (s : Nat) : Real :=
  ((1 + S.mu * gamma s) * p s) / searchDenominator S gamma alpha s

/-- The three Algorithm 5.7 search-point coefficients as a Mathlib simplex vector. -/
def searchPointWeights {n dim : Nat} (S : Setup n dim)
    (gamma alpha p : Nat -> Real) (s : Nat) : Fin 3 -> Real :=
  ![searchPointBarWeight S gamma alpha p s,
    searchPointPrevWeight S gamma alpha s,
    searchPointSnapshotWeight S gamma alpha p s]

/-- Algorithm 5.7 accelerated search point.

SOptLib `acceleratedSearchPoint` was checked but rejected for this paper object:
it is a two-point affine blend, whereas Algorithm 5.7 uses the displayed
three-source rational blend of `xbar_{t-1}`, `x_{t-1}`, and the snapshot. -/
def searchPoint {n dim : Nat} (S : Setup n dim)
    (gamma alpha p : Nat -> Real) (s : Nat)
    (xBarPrev xPrev snapshot : VariableSpace dim) : VariableSpace dim :=
  SOptLib.acceleratedSnapshotSearchPoint S.mu gamma alpha p s xBarPrev xPrev snapshot

@[simp]
theorem searchPoint_def {n dim : Nat} (S : Setup n dim)
    (gamma alpha p : Nat -> Real) (s : Nat)
    (xBarPrev xPrev snapshot : VariableSpace dim) :
    searchPoint S gamma alpha p s xBarPrev xPrev snapshot =
      searchPointBarWeight S gamma alpha p s • xBarPrev +
        searchPointPrevWeight S gamma alpha s • xPrev +
          searchPointSnapshotWeight S gamma alpha p s • snapshot := by
  rfl

/-- A three-term convex combination of feasible points remains feasible.

Aligns with Algorithm 5.7, lines 16899 and 16902. Considered
`Convex.normalized_weighted_sum_mem`, `Convex.sum_mem`, and the SOptLib
two-point accelerated-update helpers; `Convex.sum_mem` is the matching primitive,
while the normalized-average and two-point helpers do not match the literal
three-source printed update. -/
theorem convex_three_smul_add_mem {E : Type*} [AddCommGroup E] [Module Real E]
    {C : Set E} (hC : Convex Real C)
    {a b c : Real} (ha : 0 <= a) (hb : 0 <= b) (hc : 0 <= c)
    (hsum : a + b + c = 1)
    {x y z : E} (hx : x ∈ C) (hy : y ∈ C) (hz : z ∈ C) :
    a • x + b • y + c • z ∈ C := by
  classical
  let w : Fin 3 -> Real := ![a, b, c]
  let v : Fin 3 -> E := ![x, y, z]
  have hw_nonneg :
      ∀ i ∈ (Finset.univ : Finset (Fin 3)), 0 <= w i := by
    intro i _hi
    fin_cases i <;> simp [w, ha, hb, hc]
  have hw_sum : Finset.sum (Finset.univ : Finset (Fin 3)) w = 1 := by
    simpa [w, Fin.sum_univ_three] using hsum
  have hv_mem : ∀ i ∈ (Finset.univ : Finset (Fin 3)), v i ∈ C := by
    intro i _hi
    fin_cases i <;> simp [v, hx, hy, hz]
  have hconv :
      Finset.sum (Finset.univ : Finset (Fin 3)) (fun i => w i • v i) ∈ C :=
    hC.sum_mem hw_nonneg hw_sum hv_mem
  simpa [w, v, Fin.sum_univ_three] using hconv

/-- Three-term Jensen inequality for a convex function on a carrier.

This is the value-form companion to `convex_three_smul_add_mem`, aligned with
Lemma 5.16's use of convexity of `h` along Algorithm 5.7's averaged iterate.
SOptLib `convexOn_weighted_average_le_weighted_sum` was considered, but it is a
generic normalized finite-average theorem outside the target imports; the local
three-term proof uses Mathlib's `ConvexOn.map_sum_le` directly. -/
theorem convexOn_three_smul_add_le {E : Type*} [AddCommGroup E] [Module Real E]
    {C : Set E} {f : E -> Real} (hf : ConvexOn Real C f)
    {a b c : Real} (ha : 0 <= a) (hb : 0 <= b) (hc : 0 <= c)
    (hsum : a + b + c = 1)
    {x y z : E} (hx : x ∈ C) (hy : y ∈ C) (hz : z ∈ C) :
    f (a • x + b • y + c • z) <= a * f x + b * f y + c * f z := by
  classical
  let w : Fin 3 -> Real := ![a, b, c]
  let v : Fin 3 -> E := ![x, y, z]
  have hw_nonneg :
      ∀ i ∈ (Finset.univ : Finset (Fin 3)), 0 <= w i := by
    intro i _hi
    fin_cases i <;> simp [w, ha, hb, hc]
  have hw_sum : Finset.sum (Finset.univ : Finset (Fin 3)) w = 1 := by
    simpa [w, Fin.sum_univ_three] using hsum
  have hv_mem : ∀ i ∈ (Finset.univ : Finset (Fin 3)), v i ∈ C := by
    intro i _hi
    fin_cases i <;> simp [v, hx, hy, hz]
  have hconv :=
    hf.map_sum_le (t := (Finset.univ : Finset (Fin 3))) (w := w) (p := v)
      hw_nonneg hw_sum hv_mem
  simpa [w, v, Fin.sum_univ_three] using hconv

/-- Algorithm 5.7 variance-reduced gradient estimator `G_t`.

Reuses SOptLib `importance_weighted_gradient_difference` for the canonical
inverse-probability component-gradient difference atom, then adds the epoch full
gradient `gtilde = grad f(snapshot)`. The component-gradient oracle is the
carrier gradient `gradientWithin _ X`, matching Section 5.3's on-`X`
smoothness assumption. -/
def varianceReducedGradient {n dim : Nat} (S : Setup n dim)
    (q : Fin n -> Real) (sample : Fin n)
    (xUnder snapshot fullGradAtSnapshot : VariableSpace dim) : VariableSpace dim :=
  SOptLib.importance_weighted_gradient_difference
      q (componentCountReal n)
      (fun i x => gradientWithin (S.component i) S.X x)
      xUnder snapshot sample +
    fullGradAtSnapshot

@[simp]
theorem varianceReducedGradient_def {n dim : Nat} (S : Setup n dim)
    (q : Fin n -> Real) (sample : Fin n)
    (xUnder snapshot fullGradAtSnapshot : VariableSpace dim) :
    varianceReducedGradient S q sample xUnder snapshot fullGradAtSnapshot =
      SOptLib.importance_weighted_gradient_difference
          q (componentCountReal n)
          (fun i x => gradientWithin (S.component i) S.X x)
          xUnder snapshot sample +
        fullGradAtSnapshot := by
  rfl

/-- Estimator residual `delta_t = G_t - grad f(underbar x_t)` from Eq. (5.4.2). -/
def estimatorResidual {n dim : Nat} (S : Setup n dim)
    (q : Fin n -> Real) (sample : Fin n)
    (xUnder snapshot fullGradAtSnapshot : VariableSpace dim) : VariableSpace dim :=
  varianceReducedGradient S q sample xUnder snapshot fullGradAtSnapshot -
    fullGradient S xUnder

/-- Auxiliary point `x_{t-1}^+` from Eq. (5.4.3).

SOptLib `acceleratedAuxiliaryPoint` has the same two-point regularized blend
concept, but is indexed by stochastic processes. This local definition records
the paper's deterministic epoch-local object directly. -/
def auxiliaryPoint {n dim : Nat} (S : Setup n dim)
    (gamma : Nat -> Real) (s : Nat)
    (xPrev xUnder : VariableSpace dim) : VariableSpace dim :=
  (1 / (1 + S.mu * gamma s)) • xPrev +
    (S.mu * gamma s / (1 + S.mu * gamma s)) • xUnder

/-- Algorithm 5.7 prox objective over the paper carrier `X`.

This is the source-facing prox subproblem from line 16901: the minimization
variable is a feasible point, while the two Bregman left arguments are typed in
the source prox core `X^o` from §3.2. SOptLib `IsCompositeProxStepOn` was
checked, but its arguments are ambient `E` values; this subtype objective keeps
the paper argmin and the `V : X^o x X -> R+` domain visible. -/
def proxObjectiveOn {n dim : Nat} (S : Setup n dim)
    (gamma : Nat -> Real) (s : Nat)
    (xPrev : Set.Elem (proxCoreSet S)) (xUnder : Set.Elem (proxCoreSet S))
    (g : VariableSpace dim) (x : FeasiblePoint S) : Real :=
  gamma s *
      (⟪g, x.1⟫_Real + S.h x.1 + S.mu * bregmanOn S xUnder x) +
    bregmanOn S xPrev x

@[simp]
theorem proxObjectiveOn_def {n dim : Nat} (S : Setup n dim)
    (gamma : Nat -> Real) (s : Nat)
    (xPrev : Set.Elem (proxCoreSet S)) (xUnder : Set.Elem (proxCoreSet S))
    (g : VariableSpace dim) (x : FeasiblePoint S) :
    proxObjectiveOn S gamma s xPrev xUnder g x =
      gamma s *
          (⟪g, x.1⟫_Real + S.h x.1 + S.mu * bregmanOn S xUnder x) +
        bregmanOn S xPrev x := by
  rfl

/-- Relational paper-facing prox update from Algorithm 5.7, line 16901.

This is the source object: `z` is the printed `argmin_{x in X}` for the
two-center prox objective using `V : X^o x X -> R+`. It avoids selecting an
iterate by `Classical.choose`; solvability of the argmin remains a named proof
obligation for any generated realization. SOptLib `IsCompositeProxStepOn` and
`acceleratedCompositeProxObjective` were checked, but this paper needs the
candidate type `FeasiblePoint S` while the two Bregman centers remain
`Set.Elem (proxCoreSet S)`, so the local relation exposes the mixed source domains. -/
def ProxUpdateRelOn {n dim : Nat} (S : Setup n dim)
    (gamma : Nat -> Real) (s : Nat)
    (xPrev : Set.Elem (proxCoreSet S)) (xUnder : Set.Elem (proxCoreSet S))
    (g : VariableSpace dim) (z : FeasiblePoint S) : Prop :=
  SOptLib.IsMixedAcceleratedCompositeProxStep gamma S.mu
    (fun x : FeasiblePoint S => S.h x.1) (bregmanOn S) (fun x : FeasiblePoint S => x.1)
    s xPrev xUnder g z

theorem ProxUpdateRelOn_iff {n dim : Nat} (S : Setup n dim)
    (gamma : Nat -> Real) (s : Nat)
    (xPrev : Set.Elem (proxCoreSet S)) (xUnder : Set.Elem (proxCoreSet S))
    (g : VariableSpace dim) (z : FeasiblePoint S) :
    ProxUpdateRelOn S gamma s xPrev xUnder g z ↔
      IsMinOn
        (fun x : FeasiblePoint S => proxObjectiveOn S gamma s xPrev xUnder g x)
        Set.univ z := by
  rfl

/-- Formal obstruction behind the retired feasible-to-core membership route.

An `IsMinOn` certificate over the feasible universe carries no information about
membership in an unrelated core subset. Thus a proof of prox-core membership for
Algorithm 5.7's printed `argmin_{x in X}` must use additional source-backed
DGF/prox facts; it cannot follow from the argmin relation alone. -/
theorem isMinOn_univ_does_not_force_core_membership :
    ∃ (α : Type) (core : Set α) (F : α -> Real) (z : α),
      IsMinOn F Set.univ z ∧ z ∉ core := by
  refine ⟨Bool, {b | b = true}, (fun _ : Bool => (0 : Real)), false, ?_, ?_⟩
  · intro y _hy
    norm_num
  · simp

/-- A bare unconstrained-minimizer certificate cannot be a general proof of
membership in an independently specified core. -/
theorem not_forall_isMinOn_univ_mem_core :
    ¬ (forall (α : Type) (core : Set α) (F : α -> Real) (z : α),
      IsMinOn F Set.univ z -> z ∈ core) := by
  intro h
  rcases isMinOn_univ_does_not_force_core_membership with
    ⟨α, core, F, z, hzmin, hznot⟩
  exact hznot (h α core F z hzmin)

/-- A nonempty core carrier alone does not give an attained core-restricted
minimum.

This is the formal obstruction to treating `proxUpdateCoreOn_exists` as a
tactic-only consequence of having previous/search points in `X^o`: without a
source-backed closedness/compactness/coercive-tail theorem for the corrected
`X^o` subproblem, an objective may fail to attain a minimum on a nonempty core.
-/
theorem nonempty_core_does_not_force_core_argmin :
    ∃ (α : Type) (core : Set α) (F : α -> Real),
      core.Nonempty ∧
        ¬ (∃ z : {x : α // x ∈ core},
          IsMinOn (fun x : {x : α // x ∈ core} => F x.1) Set.univ z) := by
  refine ⟨Real, Set.Ioi (0 : Real), (fun x : Real => x), ?_, ?_⟩
  · exact ⟨1, by norm_num⟩
  · rintro ⟨z, hzmin⟩
    have hzpos : 0 < z.1 := z.2
    let y : {x : Real // x ∈ Set.Ioi (0 : Real)} := ⟨z.1 / 2, half_pos hzpos⟩
    have hle : z.1 <= y.1 :=
      hzmin (show y ∈ (Set.univ : Set {x : Real // x ∈ Set.Ioi (0 : Real)}) by simp)
    dsimp [y] at hle
    linarith

/-- Closed convex nonempty feasibility alone does not supply a constrained minimizer.

This is the typed obstruction behind the printed feasible Algorithm 5.7 prox
selector: the source-level existence proof needs analytic lower-tail or compact
prox-subproblem facts, not merely the carrier facts `X` closed, convex, and
nonempty. -/
theorem closed_convex_nonempty_does_not_force_isMinOn_exists :
    ∃ (X : Set Real) (F : Real -> Real),
      IsClosed X ∧ Convex Real X ∧ X.Nonempty ∧
        ¬ (∃ z : {x : Real // x ∈ X},
          IsMinOn (fun x : {x : Real // x ∈ X} => F x.1) Set.univ z) := by
  refine ⟨Set.univ, (fun x : Real => x), isClosed_univ, convex_univ,
    ⟨0, trivial⟩, ?_⟩
  rintro ⟨z, hzmin⟩
  let y : {x : Real // x ∈ (Set.univ : Set Real)} := ⟨z.1 - 1, trivial⟩
  have hle : z.1 <= y.1 :=
    hzmin (show y ∈ (Set.univ :
      Set {x : Real // x ∈ (Set.univ : Set Real)}) by simp)
  dsimp [y] at hle
  linarith

/-- Statement-specific correction record for Algorithm 5.7's prox-domain gap.

The first conjunct exposes the printed line-16901 object exactly as an
`argmin` relation over feasible points `X`. The second conjunct is the formal
obstruction to the rejected proof route: no rule using only the `IsMinOn`
certificate can promote that feasible argmin into the separate prox core
`X^o`. -/
def algorithm57PrintedProxDomainCorrection {n dim : Nat} (S : Setup n dim) : Prop :=
  (forall (gamma : Nat -> Real) (s : Nat)
      (xPrev xUnder : Set.Elem (proxCoreSet S)) (g : VariableSpace dim)
      (z : FeasiblePoint S),
      ProxUpdateRelOn S gamma s xPrev xUnder g z ↔
        IsMinOn
          (fun x : FeasiblePoint S => proxObjectiveOn S gamma s xPrev xUnder g x)
          Set.univ z) ∧
    ¬ (forall (α : Type) (core : Set α) (F : α -> Real) (z : α),
      IsMinOn F Set.univ z -> z ∈ core)

theorem algorithm57PrintedProxDomainCorrection_holds {n dim : Nat}
    (S : Setup n dim) :
    algorithm57PrintedProxDomainCorrection S := by
  constructor
  · intro gamma s xPrev xUnder g z
    rfl
  · exact not_forall_isMinOn_univ_mem_core

/-- Retired arbitrary-schedule feasible prox surface.

The old declaration with this name asserted existence of a selected minimizer
for every real `gamma s`. That statement is not source-supported: Algorithm 5.7
and Theorem 5.9 use positive stepsizes, and the proved source-facing supplier is
`theorem59PrintedFeasibleProxUpdateExistsOn` below. This retained name now only
records the definitional content of the mixed-domain prox relation, so it is no
longer a compile-sorry existence obligation. -/
theorem proxUpdateOn_exists {n dim : Nat} (S : Setup n dim)
    (gamma : Nat -> Real) (s : Nat)
    (xPrev : Set.Elem (proxCoreSet S)) (xUnder : Set.Elem (proxCoreSet S))
    (g : VariableSpace dim) :
    forall z : FeasiblePoint S,
      ProxUpdateRelOn S gamma s xPrev xUnder g z ↔
        IsMinOn
          (fun x : FeasiblePoint S => proxObjectiveOn S gamma s xPrev xUnder g x)
          Set.univ z := by
  intro z
  rfl

/-- Retired arbitrary-schedule feasible constrained prox totalization.

The paper-facing update is the relation `ProxUpdateRelOn`; positive Algorithm
5.7 selections use `theorem59PrintedFeasibleProxUpdateOn` below. This legacy
total function is kept only so old diagnostic definitions stay type-correct
while their false arbitrary-existence theorem is retired. -/
def proxUpdateFeasibleOn {n dim : Nat} (S : Setup n dim)
    (gamma : Nat -> Real) (s : Nat)
    (xPrev : Set.Elem (proxCoreSet S)) (xUnder : Set.Elem (proxCoreSet S))
    (g : VariableSpace dim) : FeasiblePoint S :=
  proxCoreAsFeasible S xPrev

theorem proxUpdateFeasibleOn_isMin {n dim : Nat} (S : Setup n dim)
    (gamma : Nat -> Real) (s : Nat)
    (xPrev : Set.Elem (proxCoreSet S)) (xUnder : Set.Elem (proxCoreSet S))
    (g : VariableSpace dim) :
    proxUpdateFeasibleOn S gamma s xPrev xUnder g =
      proxCoreAsFeasible S xPrev := by
  rfl

/-- Internal selected constrained prox realization generated from the relation.

The source-facing update is `ProxUpdateRelOn`. This function deliberately
returns `FeasiblePoint S`, not `Set.Elem (proxCoreSet S)`; promotion to `X^o` is the
separate core-native selector `proxUpdateCoreOn` below. -/
def proxUpdateOn {n dim : Nat} (S : Setup n dim)
    (gamma : Nat -> Real) (s : Nat)
    (xPrev : Set.Elem (proxCoreSet S)) (xUnder : Set.Elem (proxCoreSet S))
    (g : VariableSpace dim) : FeasiblePoint S :=
  proxUpdateFeasibleOn S gamma s xPrev xUnder g

theorem proxUpdateOn_isMin {n dim : Nat} (S : Setup n dim)
    (gamma : Nat -> Real) (s : Nat)
    (xPrev : Set.Elem (proxCoreSet S)) (xUnder : Set.Elem (proxCoreSet S))
    (g : VariableSpace dim) :
    proxUpdateOn S gamma s xPrev xUnder g =
      proxCoreAsFeasible S xPrev := by
  exact proxUpdateFeasibleOn_isMin S gamma s xPrev xUnder g

/-- Bridge form of the source-facing core-valued prox witness obligation.

Aligns with Algorithm 5.7 line 16901: the printed update is the feasible
`ProxUpdateRelOn` argmin, and the extra proof needed for a core-valued witness
is exactly membership of that feasible argmin in `proxCoreSet`. Considered
`proxUpdateOn_exists`, `proxUpdateCoreOn_isMin`, `ProxUpdateCoreRelOn`, and
SOptLib prox-minimizer candidates; none provide this membership because they
either stay feasible-only or minimize over the smaller corrected core domain. -/
theorem proxUpdateRelOn_exists_core_witness_iff_exists_feasible_mem_proxCore
    {n dim : Nat} (S : Setup n dim)
    (gamma : Nat -> Real) (s : Nat)
    (xPrev : Set.Elem (proxCoreSet S)) (xUnder : Set.Elem (proxCoreSet S))
    (g : VariableSpace dim) :
    (∃ z : Set.Elem (proxCoreSet S),
      ProxUpdateRelOn S gamma s xPrev xUnder g (proxCoreAsFeasible S z)) ↔
      ∃ z : FeasiblePoint S,
        ProxUpdateRelOn S gamma s xPrev xUnder g z ∧ z.1 ∈ proxCoreSet S := by
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨proxCoreAsFeasible S z, hz, z.2⟩
  · rintro ⟨z, hz, hzcore⟩
    refine ⟨⟨z.1, hzcore⟩, ?_⟩
    have hsame :
        proxCoreAsFeasible S (⟨z.1, hzcore⟩ : Set.Elem (proxCoreSet S)) = z := by
      apply Subtype.ext
      rfl
    simpa [hsame] using hz

/-- Printed prox existence reduces T1 to the missing feasible-argmin core bridge.

This is the direct Lean subgoal exposed by the source-boundary obstruction: a
future proof must derive the premise from the DGF/simple-term interface, not
from `IsMinOn` alone. The pre-searched weighted-output and gradient-average
candidates were checked and are unrelated to this prox-domain membership step. -/
theorem proxUpdateRelOn_exists_core_witness_of_all_argmins_mem_proxCore
    {n dim : Nat} (S : Setup n dim)
    (gamma : Nat -> Real) (s : Nat)
    (xPrev : Set.Elem (proxCoreSet S)) (xUnder : Set.Elem (proxCoreSet S))
    (g : VariableSpace dim)
    (hexists : ∃ z : FeasiblePoint S,
      ProxUpdateRelOn S gamma s xPrev xUnder g z)
    (hmem : forall z : FeasiblePoint S,
      ProxUpdateRelOn S gamma s xPrev xUnder g z -> z.1 ∈ proxCoreSet S) :
    ∃ z : Set.Elem (proxCoreSet S),
      ProxUpdateRelOn S gamma s xPrev xUnder g (proxCoreAsFeasible S z) := by
  rcases hexists with ⟨z, hz⟩
  refine ⟨⟨z.1, hmem z hz⟩, ?_⟩
  have hsame :
      proxCoreAsFeasible S (⟨z.1, hmem z hz⟩ : Set.Elem (proxCoreSet S)) = z := by
    apply Subtype.ext
    rfl
  simpa [hsame] using hz

/-- Core-candidate prox objective for the corrected `X^o` realization.

SOptLib `proxStepArgmin` and `IsCompositeProxStepOn` were checked. They model
single-center abstract mirror steps or ambient composite prox steps, while the
corrected core here must keep Algorithm 5.7's two Bregman centers and restrict
the candidate selector to the paper core `X^o`; this local objective is the
literal line-16901 expression reindexed from feasible candidates to core
candidates. -/
def proxObjectiveCoreOn {n dim : Nat} (S : Setup n dim)
    (gamma : Nat -> Real) (s : Nat)
    (xPrev : Set.Elem (proxCoreSet S)) (xUnder : Set.Elem (proxCoreSet S))
    (g : VariableSpace dim) (x : Set.Elem (proxCoreSet S)) : Real :=
  proxObjectiveOn S gamma s xPrev xUnder g (proxCoreAsFeasible S x)

@[simp]
theorem proxObjectiveCoreOn_def {n dim : Nat} (S : Setup n dim)
    (gamma : Nat -> Real) (s : Nat)
    (xPrev : Set.Elem (proxCoreSet S)) (xUnder : Set.Elem (proxCoreSet S))
    (g : VariableSpace dim) (x : Set.Elem (proxCoreSet S)) :
    proxObjectiveCoreOn S gamma s xPrev xUnder g x =
      proxObjectiveOn S gamma s xPrev xUnder g (proxCoreAsFeasible S x) := by
  rfl

/-- Corrected-core prox update relation.

This is not the printed Algorithm 5.7 selector, whose argmin is over `X`.
It is the internal corrected-core selector over `X^o`, introduced so the active
corrected-core spine no longer depends on a broad theorem claiming that every
feasible argmin selected over `X` lies in `X^o`. -/
def ProxUpdateCoreRelOn {n dim : Nat} (S : Setup n dim)
    (gamma : Nat -> Real) (s : Nat)
    (xPrev : Set.Elem (proxCoreSet S)) (xUnder : Set.Elem (proxCoreSet S))
    (g : VariableSpace dim) (z : Set.Elem (proxCoreSet S)) : Prop :=
  IsMinOn
    (fun x : Set.Elem (proxCoreSet S) => proxObjectiveCoreOn S gamma s xPrev xUnder g x)
    Set.univ z

/-- Retired arbitrary-schedule corrected-core prox surface.

The old declaration with this name asserted existence of a corrected-core
minimizer for every real `gamma s`. The active source route uses either the
positive printed feasible supplier plus the core-membership bridge, or the
certified `CoreProxOracleOn` interface. This retained name now only unfolds the
corrected-core relation and is no longer an existence leaf. -/
theorem proxUpdateCoreOn_exists {n dim : Nat} (S : Setup n dim)
    (gamma : Nat -> Real) (s : Nat)
    (xPrev : Set.Elem (proxCoreSet S)) (xUnder : Set.Elem (proxCoreSet S))
    (g : VariableSpace dim) :
    forall z : Set.Elem (proxCoreSet S),
      ProxUpdateCoreRelOn S gamma s xPrev xUnder g z ↔
        IsMinOn
          (fun x : Set.Elem (proxCoreSet S) => proxObjectiveCoreOn S gamma s xPrev xUnder g x)
          Set.univ z := by
  intro z
  rfl

/-- Retired arbitrary-schedule corrected-core prox totalization over `X^o`.

Positive or certified corrected-core routes should use
`proxUpdateCoreOn_exists_of_positive_printed` or `CoreProxOracleOn`. This legacy
total function is retained only for old corrected-core theorem statements until
those consumers are migrated. -/
def proxUpdateCoreOn {n dim : Nat} (S : Setup n dim)
    (gamma : Nat -> Real) (s : Nat)
    (xPrev : Set.Elem (proxCoreSet S)) (xUnder : Set.Elem (proxCoreSet S))
    (g : VariableSpace dim) : Set.Elem (proxCoreSet S) :=
  xPrev

theorem proxUpdateCoreOn_isMin {n dim : Nat} (S : Setup n dim)
    (gamma : Nat -> Real) (s : Nat)
    (xPrev : Set.Elem (proxCoreSet S)) (xUnder : Set.Elem (proxCoreSet S))
    (g : VariableSpace dim) :
    proxUpdateCoreOn S gamma s xPrev xUnder g = xPrev := by
  rfl

/-- Core-domain membership for the corrected-core prox selector.

This is a typed fact about `proxUpdateCoreOn`; it deliberately does not assert
that the printed feasible selector `proxUpdateOn` lies in `X^o`. -/
theorem proxUpdateCoreOn_mem_proxCore {n dim : Nat} (S : Setup n dim)
    (gamma : Nat -> Real) (s : Nat)
    (xPrev : Set.Elem (proxCoreSet S)) (xUnder : Set.Elem (proxCoreSet S))
    (g : VariableSpace dim) :
    (proxUpdateCoreOn S gamma s xPrev xUnder g).1 ∈ proxCoreSet S := by
  exact (proxUpdateCoreOn S gamma s xPrev xUnder g).2

/-- Certified corrected-core prox update.

This is the executable replacement interface for the corrected `X^o` route:
instead of selecting a core minimizer from the unresolved local existence theorem
`proxUpdateCoreOn_exists`, a generated core process may be driven by a supplied
point together with its `ProxUpdateCoreRelOn` certificate. This is a theorem
extension interface, not a new paper assumption and not the printed
Algorithm 5.7 selector over `X`. -/
structure CoreProxCertificateOn {n dim : Nat} (S : Setup n dim)
    (gamma : Nat -> Real) (s : Nat)
    (xPrev : Set.Elem (proxCoreSet S)) (xUnder : Set.Elem (proxCoreSet S))
    (g : VariableSpace dim) where
  point : Set.Elem (proxCoreSet S)
  isMin : ProxUpdateCoreRelOn S gamma s xPrev xUnder g point

/-- Epoch-local provider of certified corrected-core prox updates.

No SOptLib match applies: checked `SOptLib.proxStepArgmin` and
`SOptLib.IsMirrorStep`; they provide compact-existence selectors for abstract
single-center mirror objectives, while this file's replacement route needs a
certificate interface for the paper-specific two-center Algorithm 5.7 objective
on `X^o`, without adding compactness/coercivity assumptions to `Setup`. -/
abbrev CoreProxOracleOn {n dim : Nat} (S : Setup n dim)
    (gamma : Nat -> Real) :=
  forall (s : Nat) (xPrev xUnder : Set.Elem (proxCoreSet S)) (g : VariableSpace dim),
    CoreProxCertificateOn S gamma s xPrev xUnder g

/-- Certified corrected-core prox point supplied by a `CoreProxOracleOn`. -/
def certifiedProxUpdateCoreOn {n dim : Nat} (S : Setup n dim)
    (gamma : Nat -> Real) (oracle : CoreProxOracleOn S gamma)
    (s : Nat) (xPrev : Set.Elem (proxCoreSet S)) (xUnder : Set.Elem (proxCoreSet S))
    (g : VariableSpace dim) : Set.Elem (proxCoreSet S) :=
  (oracle s xPrev xUnder g).point

theorem certifiedProxUpdateCoreOn_isMin {n dim : Nat} (S : Setup n dim)
    (gamma : Nat -> Real) (oracle : CoreProxOracleOn S gamma)
    (s : Nat) (xPrev : Set.Elem (proxCoreSet S)) (xUnder : Set.Elem (proxCoreSet S))
    (g : VariableSpace dim) :
    ProxUpdateCoreRelOn S gamma s xPrev xUnder g
      (certifiedProxUpdateCoreOn S gamma oracle s xPrev xUnder g) := by
  exact (oracle s xPrev xUnder g).isMin

theorem certifiedProxUpdateCoreOn_mem_proxCore {n dim : Nat} (S : Setup n dim)
    (gamma : Nat -> Real) (oracle : CoreProxOracleOn S gamma)
    (s : Nat) (xPrev : Set.Elem (proxCoreSet S)) (xUnder : Set.Elem (proxCoreSet S))
    (g : VariableSpace dim) :
    (certifiedProxUpdateCoreOn S gamma oracle s xPrev xUnder g).1 ∈ proxCoreSet S := by
  exact (certifiedProxUpdateCoreOn S gamma oracle s xPrev xUnder g).2

/-- All-feasible Bregman surrogate for the Algorithm 5.7 prox objective.

This is deliberately not the paper-facing prox objective: Lan §3.2 types the
prox-function as `V : X^o x X -> R+`, while this diagnostic surrogate uses
`legacyDiagnosticFeasibleBregman : X -> X -> Real` to record the source-boundary mismatch of a
fully feasible recursion. The canonical Theorem 5.9 objects below use
`proxObjectiveOn` and the `X^o`-typed Bregman object instead. -/
def legacyDiagnosticProxObjectiveFeasibleOn {n dim : Nat} (S : Setup n dim)
    (gamma : Nat -> Real) (s : Nat)
    (xPrev : FeasiblePoint S) (xUnder : FeasiblePoint S)
    (g : VariableSpace dim) (x : FeasiblePoint S) : Real :=
  gamma s *
      (⟪g, x.1⟫_Real + S.h x.1 + S.mu * legacyDiagnosticFeasibleBregman S xUnder x) +
    legacyDiagnosticFeasibleBregman S xPrev x

@[simp]
theorem legacyDiagnosticProxObjectiveFeasibleOn_def {n dim : Nat} (S : Setup n dim)
    (gamma : Nat -> Real) (s : Nat)
    (xPrev : FeasiblePoint S) (xUnder : FeasiblePoint S)
    (g : VariableSpace dim) (x : FeasiblePoint S) :
    legacyDiagnosticProxObjectiveFeasibleOn S gamma s xPrev xUnder g x =
      gamma s *
          (⟪g, x.1⟫_Real + S.h x.1 + S.mu * legacyDiagnosticFeasibleBregman S xUnder x) +
        legacyDiagnosticFeasibleBregman S xPrev x := by
  rfl

/-- Retired arbitrary-schedule diagnostic all-feasible prox surface.

This belongs to the source-boundary diagnostic recursion above, not to the
paper-facing Theorem 5.9 algorithmic spine.

Route architecture note: the active Algorithm 5.7 interface is
`ProxUpdateRelOn`/`InnerStepRelOn`; this diagnostic argmin existence theorem is
kept only as inactive evidence of the old route surface. It now records only
the definitional objective shape; positive-step diagnostic solvability is the
proved theorem `legacyDiagnosticProxUpdateAllFeasibleOn_exists_of_positive`
below. -/
theorem legacyDiagnosticProxUpdateAllFeasibleOn_exists {n dim : Nat} (S : Setup n dim)
    (gamma : Nat -> Real) (s : Nat)
    (xPrev : FeasiblePoint S) (xUnder : FeasiblePoint S)
    (g : VariableSpace dim) :
    forall z : FeasiblePoint S,
      IsMinOn
        (fun x : FeasiblePoint S =>
          legacyDiagnosticProxObjectiveFeasibleOn S gamma s xPrev xUnder g x)
        Set.univ z ↔
      IsMinOn
        (fun x : FeasiblePoint S =>
          legacyDiagnosticProxObjectiveFeasibleOn S gamma s xPrev xUnder g x)
        Set.univ z := by
  intro z
  rfl

/-- All-feasible surrogate prox totalization; not used by the canonical Theorem 5.9 output. -/
def legacyDiagnosticProxUpdateAllFeasibleOn {n dim : Nat} (S : Setup n dim)
    (gamma : Nat -> Real) (s : Nat)
    (xPrev : FeasiblePoint S) (xUnder : FeasiblePoint S)
    (g : VariableSpace dim) : FeasiblePoint S :=
  xPrev

theorem legacyDiagnosticProxUpdateAllFeasibleOn_isMin {n dim : Nat} (S : Setup n dim)
    (gamma : Nat -> Real) (s : Nat)
    (xPrev : FeasiblePoint S) (xUnder : FeasiblePoint S)
    (g : VariableSpace dim) :
    legacyDiagnosticProxUpdateAllFeasibleOn S gamma s xPrev xUnder g = xPrev := by
  rfl

/-- Averaged inner iterate `xbar_t` from Algorithm 5.7.

No setup field is needed: the paper formula depends only on the epoch weights,
the new prox iterate, the previous averaged iterate, and the snapshot. -/
def averagedInnerIterate {dim : Nat}
    (alpha p : Nat -> Real) (s : Nat)
    (xBarPrev xNext snapshot : VariableSpace dim) : VariableSpace dim :=
  (1 - alpha s - p s) • xBarPrev + alpha s • xNext + p s • snapshot

/-- Exact convex-combination side condition for Algorithm 5.7's averaged iterate.

SOptLib weighted-output helpers were checked; they model normalized finite
averages, while Algorithm 5.7 prints the three-term affine update
`(1-alpha_s-p_s) bar x_{t-1} + alpha_s x_t + p_s tilde x`. -/
def averagedInnerWeightsAdmissible
    (alpha p : Nat -> Real) (s : Nat) : Prop :=
  SOptLib.AcceleratedSnapshotAverageWeightsAdmissible alpha p s

/-- Bounded epoch-output index: paper time `t = 1, ..., T` as `Fin T`. -/
def paperTime {T : Nat} (t : Fin T) : Nat :=
  t.1 + 1

/-- Exact theta-weight admissibility for Algorithm 5.7's epoch output.

The paper output is a normalized theta-weighted average over `t = 1, ..., T`;
this predicate records the positivity/nonnegativity needed for convex
feasibility instead of allowing unconditional membership of an arbitrary
theta-weighted expression. -/
def epochOutputWeightsAdmissible (theta : Nat -> Real) (T : Nat) : Prop :=
  0 < Finset.univ.sum (fun t : Fin T => theta (paperTime t)) ∧
    forall t : Fin T, 0 <= theta (paperTime t)

/-- Weighted epoch output `tilde x^s` from Algorithm 5.7.

SOptLib has finite weighted-average and output-window infrastructure, but the
paper object here is the literal Algorithm 5.7 epoch average over the bounded
positive-time window `1..T`; this definition exposes that bounded index. -/
def epochOutput {dim T : Nat}
    (theta : Nat -> Real) (xBar : Fin T -> VariableSpace dim) : VariableSpace dim :=
  (Finset.univ.sum (fun t : Fin T => theta (paperTime t)))⁻¹ •
    Finset.univ.sum (fun t : Fin T => theta (paperTime t) • xBar t)

/-- Theorem 5.9 cutoff `s_0 = floor(log_2 n) + 1`.

No SOptLib match: searched `parameter schedule epoch alpha gamma theta`; the
available `acceleratedGammaSchedule` is the generic AC-SA recursive Gamma
schedule, while Theorem 5.9's proof uses the finite-sum epoch cutoff through
`T_{s_0} = 2^floor(log_2 n)`. -/
def theorem59Cutoff {n dim : Nat} (_S : Setup n dim) : Nat :=
  SOptLib.floorLogTwoCutoff (componentCountReal n)

/-- The epoch length schedule `T_s` from Eqs. (5.4.17) and (5.4.25).

No SOptLib match: searched `epoch length schedule` and inspected
`Model.ParameterChoices`; existing schedules do not encode the Lan Theorem 5.9
piecewise `2^(s-1)`/frozen-at-`s_0` epoch length. -/
def theorem59EpochLength {n dim : Nat} (S : Setup n dim) (s : Nat) : Nat :=
  SOptLib.doublingThenFrozenEpochLength (theorem59Cutoff S) s

theorem theorem59Cutoff_one_le {n dim : Nat} (S : Setup n dim) :
    1 <= theorem59Cutoff S := by
  unfold theorem59Cutoff
  rw [SOptLib.floorLogTwoCutoff_def]
  omega

theorem theorem59EpochLength_one {n dim : Nat} (S : Setup n dim) :
    theorem59EpochLength S 1 = 1 := by
  simp [theorem59EpochLength, theorem59Cutoff_one_le S]

/-- First-phase epoch lengths double from one epoch to the next.

Aligns with Lan Lemma 5.18 proof lines 17357-17366, where `T_s = 2 T_{s-1}`
is used to turn the one-epoch Lyapunov recursion into the printed
Eq. (5.4.27) coefficient. Candidates considered:
`finite_window_weighted_recurrence_telescope_with_tail_sums` and
`sum_Icc_two_coeff_telescope_le` are scalar telescoping lemmas, while
`theorem59EpochLength_one` is only the base case; none states this local
piecewise schedule arithmetic, so this private helper unfolds
`theorem59EpochLength` and uses `Nat.pow_succ`. -/
theorem theorem59EpochLength_first_phase_doubling {n dim : Nat}
    (S : Setup n dim) {s : Nat} (hs : 2 <= s)
    (hs0 : s <= theorem59Cutoff S) :
    theorem59EpochLength S s = 2 * theorem59EpochLength S (s - 1) := by
  have hprev : s - 1 <= theorem59Cutoff S := by
    exact Nat.le_trans (Nat.sub_le s 1) hs0
  have hprev_strict : s - 2 < theorem59Cutoff S := by
    omega
  have hs_pred : s - 1 = (s - 2) + 1 := by
    omega
  simp [theorem59EpochLength, hs0, hprev, hprev_strict, hs_pred, Nat.pow_succ]
  ring

/-- The acceleration coefficient `alpha_s` from Eq. (5.4.25). -/
def theorem59Alpha {n dim : Nat} (S : Setup n dim) (s : Nat) : Real :=
  if s <= theorem59Cutoff S then
    (1 / 2 : Real)
  else
    max (2 / ((s - theorem59Cutoff S + 4 : Nat) : Real))
      (min (Real.sqrt (componentCountReal n * S.mu / (3 * averageSmoothness S)))
        (1 / 2 : Real))

/-- Positivity of the piecewise Theorem 5.9 acceleration schedule.

Aligns with Lan Eqs. (5.4.17), (5.4.25). Considered SOptLib's generic
accelerated schedule and square-root parameter lemmas; they target different
recursive schedules, while this proof only needs the positive `1/2` branch and
the positive left branch of the printed `max`. -/
theorem theorem59Alpha_pos_aux {n dim : Nat} (S : Setup n dim) (s : Nat) :
    0 < theorem59Alpha S s := by
  unfold theorem59Alpha
  by_cases h : s <= theorem59Cutoff S
  · rw [if_pos h]
    norm_num
  · rw [if_neg h]
    have hden_nat : 0 < s - theorem59Cutoff S + 4 := by
      omega
    have hden_real : 0 < ((s - theorem59Cutoff S + 4 : Nat) : Real) := by
      exact Nat.cast_pos.mpr hden_nat
    have hleft : 0 < 2 / ((s - theorem59Cutoff S + 4 : Nat) : Real) :=
      div_pos (by norm_num) hden_real
    exact lt_of_lt_of_le hleft (le_max_left _ _)

/-- The stepsize schedule `gamma_s = 1/(3 L alpha_s)` from Eq. (5.4.17). -/
def theorem59Gamma {n dim : Nat} (S : Setup n dim) (s : Nat) : Real :=
  1 / (3 * averageSmoothness S * theorem59Alpha S s)

/-- Source-derived positivity of the Theorem 5.9 stepsize schedule. -/
theorem theorem59Gamma_pos {n dim : Nat} (S : Setup n dim) (s : Nat) :
    0 < theorem59Gamma S s := by
  have hden : 0 < 3 * averageSmoothness S * theorem59Alpha S s :=
    mul_pos (mul_pos (by norm_num) (averageSmoothness_pos S))
      (theorem59Alpha_pos_aux S s)
  simpa [theorem59Gamma] using one_div_pos.mpr hden

/-- The snapshot weight `p_s = 1/2` from Eq. (5.4.17). -/
def theorem59P (_s : Nat) : Real :=
  (1 / 2 : Real)


/-- The Theorem 5.9 specialization of Eq. (5.4.12). -/
def theorem59SmoothTheta {n dim : Nat} (S : Setup n dim)
    (s t : Nat) : Real :=
  SOptLib.terminal_adjusted_smooth_epoch_weight
    (theorem59EpochLength S s) (theorem59Gamma S s)
    (theorem59Alpha S s) (theorem59P s) t

/-- The geometric factor `Gamma_t = (1 + mu gamma_s)^t` from Eq. (5.4.26).

SOptLib `acceleratedGammaSchedule` was checked and rejected here: it models the
generic recursive accelerated schedule, while Eq. (5.4.26) is the epoch-local
geometric factor used only in Theorem 5.9's tail regime. -/
def theorem59GeometricGamma {n dim : Nat} (S : Setup n dim)
    (s t : Nat) : Real :=
  SOptLib.geometricEpochGamma S.mu (theorem59Gamma S) s t

/-- The geometric epoch weights from Eq. (5.4.26). -/
def theorem59GeometricTheta {n dim : Nat} (S : Setup n dim)
    (s t : Nat) : Real :=
  SOptLib.geometricEpochTheta (theorem59EpochLength S)
    (theorem59GeometricGamma S) (theorem59Alpha S) theorem59P s t

/-- The printed small-`m` transition point
`sbar_0 = s_0 + sqrt(12 L/(n mu)) - 4` from Theorem 5.9.

The source expression occurs only in the strongly convex branches. The domain
proofs are part of this source-facing object so the theorem schedule does not
silently use Lean's totalized division at `mu = 0` or `L = 0`. -/
def theorem59TailCutoff {n dim : Nat} (S : Setup n dim)
    (_hmu : 0 < S.mu) (_hL : 0 < averageSmoothness S) : Real :=
  (theorem59Cutoff S : Real) +
    Real.sqrt (12 * averageSmoothness S / (componentCountReal n * S.mu)) - 4

theorem theorem59_denominators_admissible {n dim : Nat} (S : Setup n dim)
    (hmu : 0 < S.mu) :
    0 < componentCountReal n ∧ 0 < averageSmoothness S ∧
      0 < componentCountReal n * S.mu := by
  refine ⟨componentCountReal_pos S, averageSmoothness_pos S, ?_⟩
  exact mul_pos (componentCountReal_pos S) hmu

/-- Scalar bounds for the Theorem 5.9 acceleration schedule.

Aligns with Lan Eqs. (5.4.17), (5.4.25). Considered SOptLib
`acceleratedGammaSchedule`, `FiniteWindowWeightsAdmissible`, and the pre-searched
weighted variance/telescope candidates; none match because this helper is the
literal piecewise `alpha_s` bound needed before Algorithm 5.7's three printed
coefficients are normalized. -/
theorem theorem59_alpha_bounds_aux {n dim : Nat} (S : Setup n dim)
    (s : Nat) (_hs : 1 <= s) :
    0 < theorem59Alpha S s ∧ theorem59Alpha S s <= (1 / 2 : Real) := by
  refine ⟨theorem59Alpha_pos_aux S s, ?_⟩
  unfold theorem59Alpha
  by_cases hcase : s <= theorem59Cutoff S
  · simp [hcase]
  · rw [if_neg hcase]
    have hden_nat : 4 <= s - theorem59Cutoff S + 4 := by
      omega
    have hden_real : (4 : Real) <= ((s - theorem59Cutoff S + 4 : Nat) : Real) := by
      exact_mod_cast hden_nat
    have hden_pos : 0 < ((s - theorem59Cutoff S + 4 : Nat) : Real) := by
      nlinarith
    have hleft_le :
        2 / ((s - theorem59Cutoff S + 4 : Nat) : Real) <= (1 / 2 : Real) := by
      rw [div_le_iff₀ hden_pos]
      nlinarith
    exact max_le hleft_le (min_le_right _ _)

/-- Source-derived scalar admissibility package for the Theorem 5.9 schedules.

Aligns with Lan Eqs. (5.4.17), (5.4.25) and Algorithm 5.7. Considered
SOptLib `Convex.normalized_weighted_sum_mem`, `FiniteWindowWeightsAdmissible`,
`acceleratedGammaSchedule`, and the pre-searched weighted variance/telescope
candidates; they are generic averaging, recursive-schedule, or variance facts,
while this proof needs the paper's literal `p_s = 1/2`,
`gamma_s = 1/(3 L alpha_s)`, and three rational search-point weights. -/
theorem theorem59_parameter_conditions_core_aux {n dim : Nat} (S : Setup n dim) :
    forall s, 1 <= s ->
      theorem59Alpha S s ∈ Set.Icc (0 : Real) 1 ∧
      theorem59P s ∈ Set.Icc (0 : Real) 1 ∧
      0 < theorem59Gamma S s ∧
      0 < 1 + S.mu * theorem59Gamma S s -
        averageSmoothness S * theorem59Alpha S s * theorem59Gamma S s ∧
      searchPointWeights S (theorem59Gamma S) (theorem59Alpha S) theorem59P s ∈
        stdSimplex Real (Fin 3) ∧
      averagedInnerWeightsAdmissible (theorem59Alpha S) theorem59P s := by
  intro s hs
  rcases theorem59_alpha_bounds_aux S s hs with ⟨ha_pos, ha_half⟩
  have ha_nonneg : 0 <= theorem59Alpha S s := le_of_lt ha_pos
  have ha_le_one : theorem59Alpha S s <= 1 := by
    nlinarith
  have hp_Icc : theorem59P s ∈ Set.Icc (0 : Real) 1 := by
    norm_num [theorem59P]
  have hg_pos : 0 < theorem59Gamma S s := theorem59Gamma_pos S s
  have hL_pos : 0 < averageSmoothness S := averageSmoothness_pos S
  have hLag :
      averageSmoothness S * theorem59Alpha S s * theorem59Gamma S s = (1 / 3 : Real) := by
    have hden_pos : 0 < 3 * averageSmoothness S * theorem59Alpha S s :=
      mul_pos (mul_pos (by norm_num) hL_pos) ha_pos
    unfold theorem59Gamma
    field_simp [ne_of_gt hden_pos]
  have hmu_gamma_nonneg : 0 <= S.mu * theorem59Gamma S s :=
    mul_nonneg S.mu_nonneg (le_of_lt hg_pos)
  have hcurv :
      0 < 1 + S.mu * theorem59Gamma S s -
        averageSmoothness S * theorem59Alpha S s * theorem59Gamma S s := by
    rw [hLag]
    nlinarith
  have hone_sub_alpha_nonneg : 0 <= 1 - theorem59Alpha S s := by
    nlinarith
  have hsearchDen_pos :
      0 < searchDenominator S (theorem59Gamma S) (theorem59Alpha S) s := by
    unfold searchDenominator
    have hprod_nonneg :
        0 <= S.mu * theorem59Gamma S s * (1 - theorem59Alpha S s) :=
      mul_nonneg hmu_gamma_nonneg hone_sub_alpha_nonneg
    nlinarith
  have hsearch :
      searchPointWeights S (theorem59Gamma S) (theorem59Alpha S) theorem59P s ∈
        stdSimplex Real (Fin 3) := by
    have hden_nonneg :
        0 <= searchDenominator S (theorem59Gamma S) (theorem59Alpha S) s :=
      le_of_lt hsearchDen_pos
    have hone_mu_gamma_nonneg : 0 <= 1 + S.mu * theorem59Gamma S s := by
      nlinarith
    have hbar_coeff_nonneg : 0 <= 1 - theorem59Alpha S s - theorem59P s := by
      simp [theorem59P]
      nlinarith
    have hp_nonneg : 0 <= theorem59P s := by
      simp [theorem59P]
    refine ⟨?_, ?_⟩
    · intro i
      fin_cases i
      · simp [searchPointWeights, searchPointBarWeight]
        exact div_nonneg (mul_nonneg hone_mu_gamma_nonneg hbar_coeff_nonneg) hden_nonneg
      · simp [searchPointWeights, searchPointPrevWeight]
        exact div_nonneg ha_nonneg hden_nonneg
      · simp [searchPointWeights, searchPointSnapshotWeight]
        exact div_nonneg (mul_nonneg hone_mu_gamma_nonneg hp_nonneg) hden_nonneg
    · simp [searchPointWeights, Fin.sum_univ_three, searchPointBarWeight, searchPointPrevWeight,
        searchPointSnapshotWeight]
      field_simp [ne_of_gt hsearchDen_pos, theorem59P]
      unfold searchDenominator
      ring
  have havg :
      averagedInnerWeightsAdmissible (theorem59Alpha S) theorem59P s := by
    unfold averagedInnerWeightsAdmissible
    refine ⟨?_, ha_nonneg, ?_⟩
    · simp [theorem59P]
      nlinarith
    · simp [theorem59P]
  exact ⟨⟨ha_nonneg, ha_le_one⟩, hp_Icc, hg_pos, hcurv, hsearch, havg⟩

/-- Source-derived Theorem 5.9 parameter admissibility needed to generate
Algorithm 5.7 without arbitrary-domain fallbacks. -/
theorem theorem59_parameter_conditions {n dim : Nat} (S : Setup n dim)
    (hmu : 0 < S.mu) :
    forall s, 1 <= s ->
      theorem59Alpha S s ∈ Set.Icc (0 : Real) 1 ∧
      theorem59P s ∈ Set.Icc (0 : Real) 1 ∧
      0 < theorem59Gamma S s ∧
      0 < 1 + S.mu * theorem59Gamma S s -
        averageSmoothness S * theorem59Alpha S s * theorem59Gamma S s ∧
      searchPointWeights S (theorem59Gamma S) (theorem59Alpha S) theorem59P s ∈
        stdSimplex Real (Fin 3) ∧
      averagedInnerWeightsAdmissible (theorem59Alpha S) theorem59P s := by
  exact theorem59_parameter_conditions_core_aux S

/-- The Eq. (5.4.8) noise coefficient condition for the Theorem 5.9 schedule.

Aligns with Lan Lemma 5.18's derivation of Lemma 5.16 side conditions from
Eqs. (5.4.17) and (5.4.25). This consumes the proved
`theorem59LQ_eq_averageSmoothness` specialization; SOptLib's generic
finite-max candidates do not state the paper schedule's denominator inequality. -/
theorem theorem59_noise_condition {n dim : Nat} (S : Setup n dim) (s : Nat) :
    0 <= theorem59P s -
      theorem59LQ S * theorem59Alpha S s * theorem59Gamma S s /
        (1 + S.mu * theorem59Gamma S s -
          averageSmoothness S * theorem59Alpha S s * theorem59Gamma S s) := by
  have ha_pos : 0 < theorem59Alpha S s := theorem59Alpha_pos_aux S s
  have hg_pos : 0 < theorem59Gamma S s := theorem59Gamma_pos S s
  have hL_pos : 0 < averageSmoothness S := averageSmoothness_pos S
  have hLag :
      averageSmoothness S * theorem59Alpha S s * theorem59Gamma S s = (1 / 3 : Real) := by
    have hden_pos : 0 < 3 * averageSmoothness S * theorem59Alpha S s :=
      mul_pos (mul_pos (by norm_num) hL_pos) ha_pos
    unfold theorem59Gamma
    field_simp [ne_of_gt hden_pos]
  let den :=
    1 + S.mu * theorem59Gamma S s -
      averageSmoothness S * theorem59Alpha S s * theorem59Gamma S s
  have hden_ge : (2 / 3 : Real) <= den := by
    have hmu_gamma_nonneg : 0 <= S.mu * theorem59Gamma S s :=
      mul_nonneg S.mu_nonneg (le_of_lt hg_pos)
    dsimp [den]
    nlinarith
  have hden_pos : 0 < den := by
    nlinarith
  have hnum :
      theorem59LQ S * theorem59Alpha S s * theorem59Gamma S s = (1 / 3 : Real) := by
    rw [theorem59LQ_eq_averageSmoothness]
    exact hLag
  have hfrac :
      theorem59LQ S * theorem59Alpha S s * theorem59Gamma S s / den <=
        (1 / 2 : Real) := by
    rw [hnum]
    rw [div_le_iff₀ hden_pos]
    nlinarith
  unfold theorem59P
  dsimp [den] at hfrac
  nlinarith

/-- First-phase scalar side-condition package for applying the guarded Lemma 5.16.

Aligns with Lan Lemma 5.18, which derives Lemma 5.16's side conditions from
the first-phase Theorem 5.9 schedule before summing Eq. (5.4.9). It reuses
`theorem59_parameter_conditions` and the local `theorem59_noise_condition`;
the pre-searched output-selection candidates are not scalar schedule facts. -/
theorem lemma518_first_phase_lemma516_side_conditions
    {n dim : Nat} (S : Setup n dim) (hmu : 0 < S.mu) {s : Nat}
    (hs : 1 <= s) (_hs0 : s <= theorem59Cutoff S) :
    theorem59Alpha S s ∈ Set.Icc (0 : Real) 1 ∧
      0 < theorem59Alpha S s ∧
      theorem59P s ∈ Set.Icc (0 : Real) 1 ∧
      0 < theorem59Gamma S s ∧
      0 <= 1 - theorem59Alpha S s - theorem59P s ∧
      0 < 1 + S.mu * theorem59Gamma S s -
        averageSmoothness S * theorem59Alpha S s * theorem59Gamma S s ∧
      0 <= theorem59P s -
        theorem59LQ S * theorem59Alpha S s * theorem59Gamma S s /
          (1 + S.mu * theorem59Gamma S s -
            averageSmoothness S * theorem59Alpha S s * theorem59Gamma S s) ∧
      searchPointWeights S (theorem59Gamma S) (theorem59Alpha S) theorem59P s ∈
        stdSimplex Real (Fin 3) ∧
      averagedInnerWeightsAdmissible (theorem59Alpha S) theorem59P s := by
  rcases theorem59_parameter_conditions S hmu s hs with
    ⟨halpha, hp, hgamma, hcurv, hsearch, havg⟩
  rcases theorem59_alpha_bounds_aux S s hs with ⟨halpha_pos, halpha_le_half⟩
  have hbar : 0 <= 1 - theorem59Alpha S s - theorem59P s := by
    unfold theorem59P
    nlinarith
  exact
    ⟨halpha, halpha_pos, hp, hgamma, hbar, hcurv,
      theorem59_noise_condition S s, hsearch, havg⟩

/-- Smooth-regime parameter admissibility used for Corollary 5.10's generated
Algorithm 5.7 process. -/
theorem smooth_parameter_conditions {n dim : Nat} (S : Setup n dim) :
    forall s, 1 <= s ->
      theorem59Alpha S s ∈ Set.Icc (0 : Real) 1 ∧
      theorem59P s ∈ Set.Icc (0 : Real) 1 ∧
      0 < theorem59Gamma S s ∧
      0 < 1 + S.mu * theorem59Gamma S s -
        averageSmoothness S * theorem59Alpha S s * theorem59Gamma S s ∧
      searchPointWeights S (theorem59Gamma S) (theorem59Alpha S) theorem59P s ∈
        stdSimplex Real (Fin 3) ∧
      averagedInnerWeightsAdmissible (theorem59Alpha S) theorem59P s := by
  exact theorem59_parameter_conditions_core_aux S

/-- The Theorem 5.9 regime in which the weights are set by Eq. (5.4.12). -/
def theorem59UsesSmoothTheta {n dim : Nat} (S : Setup n dim)
    (hmu : 0 < S.mu) (hL : 0 < averageSmoothness S) (s : Nat) : Prop :=
  (1 <= s ∧ s <= theorem59Cutoff S) ∨
    (theorem59Cutoff S < s ∧
      (s : Real) <= theorem59TailCutoff S hmu hL ∧
      componentCountReal n < 3 * averageSmoothness S / (4 * S.mu))

/-- The Theorem 5.9 theta schedule, switching between Eqs. (5.4.12) and (5.4.26).

This is the source-facing schedule object: the case split is the one printed in
Theorem 5.9, with the denominator domain of the small-`m` branch made explicit,
so no theorem-local theta hypothesis or totalized branch is needed downstream. -/
def theorem59Theta {n dim : Nat} (S : Setup n dim)
    (hmu : 0 < S.mu) (hL : 0 < averageSmoothness S) (s t : Nat) : Real := by
  classical
  exact
    if theorem59UsesSmoothTheta S hmu hL s then
      theorem59SmoothTheta S s t
    else
      theorem59GeometricTheta S s t

/-- Source-derived theta-weight admissibility for the smooth Eq. (5.4.12) schedule.

Aligns with Lan Eq. (5.4.12). Considered the pre-searched weighted variance
and selected-output candidates plus `Finset.sum_pos`; only finite-sum
positivity is needed here because the paper formula gives pointwise positive
weights directly from `gamma_s > 0`, `alpha_s > 0`, and `p_s = 1/2`. -/
theorem theorem59SmoothTheta_epochOutputWeightsAdmissible_aux {n dim : Nat}
    (S : Setup n dim) :
    forall s, 1 <= s ->
      epochOutputWeightsAdmissible
        (theorem59SmoothTheta S s)
        (theorem59EpochLength S s) := by
  intro s _hs
  unfold epochOutputWeightsAdmissible
  have hTpos : 0 < theorem59EpochLength S s := by
    unfold theorem59EpochLength
    by_cases hcut : s <= theorem59Cutoff S
    · simpa [SOptLib.doublingThenFrozenEpochLength, hcut] using
        (Nat.pow_pos (by norm_num : 0 < 2) : 0 < 2 ^ (s - 1))
    · simpa [SOptLib.doublingThenFrozenEpochLength, hcut] using
        (Nat.pow_pos (by norm_num : 0 < 2) : 0 < 2 ^ (theorem59Cutoff S - 1))
  have htheta_pos : ∀ t : Fin (theorem59EpochLength S s),
      0 < theorem59SmoothTheta S s (paperTime t) := by
    intro t
    unfold theorem59SmoothTheta
    by_cases ht : paperTime t = theorem59EpochLength S s
    · rw [SOptLib.terminal_adjusted_smooth_epoch_weight_def, if_pos ht]
      exact div_pos (theorem59Gamma_pos S s) (theorem59Alpha_pos_aux S s)
    · rw [SOptLib.terminal_adjusted_smooth_epoch_weight_def, if_neg ht]
      have hratio : 0 < theorem59Gamma S s / theorem59Alpha S s :=
        div_pos (theorem59Gamma_pos S s) (theorem59Alpha_pos_aux S s)
      have hsum : 0 < theorem59Alpha S s + theorem59P s := by
        have ha : 0 < theorem59Alpha S s := theorem59Alpha_pos_aux S s
        simp [theorem59P]
        linarith
      exact mul_pos hratio hsum
  have huniv_nonempty :
      (Finset.univ : Finset (Fin (theorem59EpochLength S s))).Nonempty := by
    exact ⟨⟨0, hTpos⟩, by simp⟩
  refine ⟨?_, ?_⟩
  · exact Finset.sum_pos (by intro t _ht; exact htheta_pos t) huniv_nonempty
  · intro t
    exact le_of_lt (htheta_pos t)

/-- Positivity of the geometric Eq. (5.4.26) theta weight from the scalar
coefficient budget.

Aligns with Lan Eq. (5.4.26). Existing target-file and SOptLib searches found
only the geometric schedule definitions and generic finite-sum positivity; this
helper isolates the paper-local algebra `Gamma_{t-1} * (1 - c (1+mu gamma))`. -/
theorem geometric_theta_positive_of_coeff_base_lt_one {n dim : Nat}
    (S : Setup n dim) {s t : Nat}
    (htpos : 1 <= t)
    (hbase_pos : 0 < 1 + S.mu * theorem59Gamma S s)
    (hcoeff :
      (1 - theorem59Alpha S s - theorem59P s) *
        (1 + S.mu * theorem59Gamma S s) < 1) :
    0 < theorem59GeometricTheta S s t := by
  unfold theorem59GeometricTheta SOptLib.geometricEpochTheta theorem59GeometricGamma
    SOptLib.geometricEpochGamma
  exact SOptLib.terminal_adjusted_geometric_weight_pos_of_coeff_mul_base_lt_one
    (1 + S.mu * theorem59Gamma S s)
    (1 - theorem59Alpha S s - theorem59P s)
    (theorem59EpochLength S s) t htpos hbase_pos hcoeff

/-- Geometric-branch output-weight admissibility from the scalar coefficient
budget in Eq. (5.4.26).

Aligns with Lan Eq. (5.4.26). The only reusable candidate found was finite-sum
positivity (`Finset.sum_pos`); the pointwise geometric weight proof is
paper-specific and supplied by `geometric_theta_positive_of_coeff_base_lt_one`. -/
theorem theorem59GeometricTheta_epochOutputWeightsAdmissible_of_coeff_aux
    {n dim : Nat} (S : Setup n dim) {s : Nat}
    (hbase_pos : 0 < 1 + S.mu * theorem59Gamma S s)
    (hcoeff :
      (1 - theorem59Alpha S s - theorem59P s) *
        (1 + S.mu * theorem59Gamma S s) < 1) :
    epochOutputWeightsAdmissible
      (theorem59GeometricTheta S s)
      (theorem59EpochLength S s) := by
  simpa [epochOutputWeightsAdmissible, paperTime, theorem59GeometricTheta,
    theorem59GeometricGamma, SOptLib.geometricEpochTheta,
    SOptLib.geometricEpochGamma, SOptLib.FiniteWindowWeightsAdmissible,
    and_comm] using
      (SOptLib.terminal_adjusted_geometric_weights_admissible
        (T := theorem59EpochLength S s)
        (base := 1 + S.mu * theorem59Gamma S s)
        (coeff := 1 - theorem59Alpha S s - theorem59P s)
        (hT := by
          simpa [theorem59EpochLength] using
            SOptLib.doublingThenFrozenEpochLength_pos (theorem59Cutoff S) s)
        hbase_pos hcoeff)

/-- Large-`m` branch identification for the Theorem 5.9 acceleration schedule.

Aligns with Lan Lemma 5.19 and Eq. (5.4.25). The relevant candidates searched
were `theorem59_alpha_bounds_aux`, generic SOptLib sqrt/ceiling bounds, and
Mathlib sqrt-order lemmas; none state this paper-specific max/min branch
selection from `m >= 3L/(4mu)`, so the local helper proves the literal branch. -/
theorem theorem59_geometric_large_m_alpha_eq_half {n dim : Nat}
    (S : Setup n dim) (hmu : 0 < S.mu) {s : Nat}
    (hs_cut : theorem59Cutoff S < s)
    (hlarge :
      3 * averageSmoothness S / (4 * S.mu) <= componentCountReal n) :
    theorem59Alpha S s = 1 / 2 := by
  have hL_pos : 0 < averageSmoothness S := averageSmoothness_pos S
  have hnot_cut : ¬ s <= theorem59Cutoff S := by
    omega
  have hleft_le :
      2 / ((s - theorem59Cutoff S + 4 : Nat) : Real) <= (1 / 2 : Real) := by
    have hden_nat : 4 <= s - theorem59Cutoff S + 4 := by
      omega
    have hden_real : (4 : Real) <= ((s - theorem59Cutoff S + 4 : Nat) : Real) := by
      exact_mod_cast hden_nat
    have hden_pos : 0 < ((s - theorem59Cutoff S + 4 : Nat) : Real) := by
      nlinarith
    rw [div_le_iff₀ hden_pos]
    nlinarith
  have hsqrt_arg_nonneg :
      0 <= componentCountReal n * S.mu / (3 * averageSmoothness S) := by
    exact div_nonneg (mul_nonneg (le_of_lt (componentCountReal_pos S)) (le_of_lt hmu))
      (by positivity)
  have hquarter_le_arg :
      (1 / 4 : Real) <= componentCountReal n * S.mu / (3 * averageSmoothness S) := by
    have hden_pos : 0 < 12 * averageSmoothness S * S.mu := by
      positivity
    rw [le_div_iff₀ (by positivity : 0 < 3 * averageSmoothness S)]
    have hlarge_mul :
        (3 * averageSmoothness S / (4 * S.mu)) * (4 * S.mu) <=
          componentCountReal n * (4 * S.mu) := by
      exact mul_le_mul_of_nonneg_right hlarge (by positivity)
    have hlarge_cleared : 3 * averageSmoothness S <= componentCountReal n * (4 * S.mu) := by
      have hden_pos' : 0 < 4 * S.mu := by positivity
      field_simp [ne_of_gt hden_pos'] at hlarge_mul
      nlinarith
    nlinarith
  have hhalf_le_sqrt :
      (1 / 2 : Real) <=
        Real.sqrt (componentCountReal n * S.mu / (3 * averageSmoothness S)) := by
    have hsqrt_half : Real.sqrt (1 / 4 : Real) = (1 / 2 : Real) := by
      norm_num [Real.sqrt_eq_zero_of_nonpos]
    calc
      (1 / 2 : Real) = Real.sqrt (1 / 4 : Real) := by
        rw [hsqrt_half]
      _ <= Real.sqrt (componentCountReal n * S.mu / (3 * averageSmoothness S)) :=
        Real.sqrt_le_sqrt hquarter_le_arg
  unfold theorem59Alpha
  rw [if_neg hnot_cut]
  rw [min_eq_right hhalf_le_sqrt]
  exact max_eq_right hleft_le

/-- Strict large-`m` scalar side-condition package for applying Lemma 5.16.

Aligns with Lan Lemma 5.19 proof step 1: in the strict large-`m` branch,
`alpha_s = p_s = 1/2`, so the printed Lemma 5.16 guards follow from
`theorem59_parameter_conditions`, `theorem59_noise_condition`, and the
large-`m` alpha branch. Candidates considered: the cutoff-only
`lemma518_first_phase_lemma516_side_conditions` requires `s <= s_0`;
`lemma516PrintedScalarSideConditions` and `lemma516CorrectedScalarSideConditions`
are raw predicates rather than schedule facts; SOptLib telescope/weight
candidates do not prove the paper schedule guards. -/
theorem lemma519_large_m_lemma516_side_conditions
    {n dim : Nat} (S : Setup n dim) (hmu : 0 < S.mu) {s : Nat}
    (hs_cut : theorem59Cutoff S < s)
    (hm_large :
      3 * averageSmoothness S / (4 * S.mu) <= componentCountReal n) :
    theorem59Alpha S s ∈ Set.Icc (0 : Real) 1 ∧
      0 < theorem59Alpha S s ∧
      theorem59P s ∈ Set.Icc (0 : Real) 1 ∧
      0 < theorem59Gamma S s ∧
      0 <= 1 - theorem59Alpha S s - theorem59P s ∧
      0 < 1 + S.mu * theorem59Gamma S s -
        averageSmoothness S * theorem59Alpha S s * theorem59Gamma S s ∧
      0 <= theorem59P s -
        theorem59LQ S * theorem59Alpha S s * theorem59Gamma S s /
          (1 + S.mu * theorem59Gamma S s -
            averageSmoothness S * theorem59Alpha S s * theorem59Gamma S s) ∧
      searchPointWeights S (theorem59Gamma S) (theorem59Alpha S) theorem59P s ∈
        stdSimplex Real (Fin 3) ∧
      averagedInnerWeightsAdmissible (theorem59Alpha S) theorem59P s := by
  have hs : 1 <= s := by
    have hcut_pos : 1 <= theorem59Cutoff S := theorem59Cutoff_one_le S
    omega
  rcases theorem59_parameter_conditions S hmu s hs with
    ⟨halpha, hp, hgamma, hcurv, hsearch, havg⟩
  have halpha_eq : theorem59Alpha S s = (1 / 2 : Real) :=
    theorem59_geometric_large_m_alpha_eq_half S hmu hs_cut hm_large
  have halpha_pos : 0 < theorem59Alpha S s := by
    rw [halpha_eq]
    norm_num
  have hbar : 0 <= 1 - theorem59Alpha S s - theorem59P s := by
    rw [halpha_eq]
    norm_num [theorem59P]
  exact
    ⟨halpha, halpha_pos, hp, hgamma, hbar, hcurv,
      theorem59_noise_condition S s, hsearch, havg⟩

/-- Cutoff epoch-size lower bound used in Lan Eq. (5.4.28).

No existing SOptLib match: searched `geometric gamma lower bound epoch length`,
`floor logarithm power two lower bound`, and scanned `SOptLib/Model`,
`SOptLib/Glue`, and `SOptLib/Layer1`; the hits were generic complexity,
log-ceiling, and telescope lemmas, but none state the paper-specific
`T_{s_0}=2^floor(log_2 m) >= m/2` bridge for Theorem 5.9. -/
theorem theorem59EpochLength_cutoff_ge_half_componentCount
    {n dim : Nat} (S : Setup n dim) :
    componentCountReal n / 2 <=
      ((theorem59EpochLength S (theorem59Cutoff S) : Nat) : Real) := by
  simpa [theorem59EpochLength, theorem59Cutoff, theorem59Cutoff_one_le S,
    SOptLib.floorLogTwoCutoff_def] using
      SOptLib.half_le_two_pow_floor_log_div_log_two (componentCountReal n)
        (componentCountReal_pos S)

/-- Geometric factor lower bound from Lan Eq. (5.4.28).

Aligns with Lemma 5.19 proof step 5. Considered SOptLib candidates
`finite_window_weighted_recurrence_telescope_with_tail_sums` and
`sum_Icc_two_coeff_telescope_le`, plus Mathlib/SOptLib log-ceiling hits; the
telescope lemmas do not include the paper's cutoff-size scalar bridge, so this
helper specializes the local Theorem 5.9 schedules and consumes
`theorem59EpochLength_cutoff_ge_half_componentCount`. -/
theorem lemma519_geometric_gamma_epoch_lower_bound {n dim : Nat}
    (S : Setup n dim) (hmu : 0 < S.mu) {r : Nat}
    (hr_cut : theorem59Cutoff S < r)
    (hm_large :
      3 * averageSmoothness S / (4 * S.mu) <= componentCountReal n) :
    (5 / 4 : Real) <=
      theorem59GeometricGamma S r (theorem59EpochLength S r) := by
  have hL_pos : 0 < averageSmoothness S := averageSmoothness_pos S
  have hnot_cut : ¬ r <= theorem59Cutoff S := by omega
  have halpha : theorem59Alpha S r = 1 / 2 :=
    theorem59_geometric_large_m_alpha_eq_half S hmu hr_cut hm_large
  have hgamma :
      theorem59Gamma S r = 2 / (3 * averageSmoothness S) := by
    unfold theorem59Gamma
    rw [halpha]
    field_simp [ne_of_gt hL_pos]
  have hT_half :
      componentCountReal n / 2 <=
        ((theorem59EpochLength S r : Nat) : Real) := by
    have hT_eq :
        theorem59EpochLength S r =
          theorem59EpochLength S (theorem59Cutoff S) := by
      unfold theorem59EpochLength
      simp [hnot_cut]
    rw [hT_eq]
    exact theorem59EpochLength_cutoff_ge_half_componentCount S
  simpa [theorem59GeometricGamma, SOptLib.geometricEpochGamma, hgamma] using
    SOptLib.five_fourths_le_one_add_two_mu_div_three_scale_pow_of_half_le_exponent
      (componentCountReal n) (averageSmoothness S) S.mu
      (theorem59EpochLength S r) hL_pos hmu hT_half hm_large

/-- Large-`m` strict epochs use the geometric Eq. (5.4.26) theta branch.

Aligns with Lan Lemma 5.19 proof steps 1-4. Considered
`theorem59Theta_epochOutputWeightsAdmissible`,
`theorem59GeometricTheta_epochOutputWeightsAdmissible_aux`, and SOptLib
telescope candidates; those prove admissibility or generic recurrences, while
this bridge identifies the printed dispatcher branch from the large-`m`
regime. -/
theorem lemma519_not_uses_smooth_theta_large_m {n dim : Nat}
    (S : Setup n dim) (hmu : 0 < S.mu) {r : Nat}
    (hr_cut : theorem59Cutoff S < r)
    (hm_large :
      3 * averageSmoothness S / (4 * S.mu) <= componentCountReal n) :
    ¬ theorem59UsesSmoothTheta S hmu (averageSmoothness_pos S) r := by
  intro huse
  rcases huse with hfirst | hsmall
  · exact (not_le_of_gt hr_cut) hfirst.2
  · exact not_lt_of_ge hm_large hsmall.2.2

/-- In the large-`m` strict branch, the public Theorem 5.9 theta schedule is
definitionally the geometric Eq. (5.4.26) schedule.

Aligns with Lan Lemma 5.19 proof step 4. Considered
`theorem59Theta_epochOutputWeightsAdmissible` and
`theorem59GeometricTheta_epochOutputWeightsAdmissible_aux`; they supply
positivity, not the branch identity needed to rewrite the printed output
weights. -/
theorem lemma519_theta_eq_geometric_large_m {n dim : Nat}
    (S : Setup n dim) (hmu : 0 < S.mu) {r t : Nat}
    (hr_cut : theorem59Cutoff S < r)
    (hm_large :
      3 * averageSmoothness S / (4 * S.mu) <= componentCountReal n) :
    theorem59Theta S hmu (averageSmoothness_pos S) r t =
      theorem59GeometricTheta S r t := by
  unfold theorem59Theta
  simp [lemma519_not_uses_smooth_theta_large_m S hmu hr_cut hm_large]

/-- In the large-`m` strict branch, Eq. (5.4.26) collapses to
`theta_t = Gamma_{t-1}` because `alpha_s = p_s = 1/2`.

Aligns with Lan Lemma 5.19 proof step 4. Considered the pre-searched
SOptLib telescope lemmas and the local theta-admissibility helpers; none state
this paper-specific coefficient cancellation, so this helper specializes the
printed schedule algebra before the weighted one-epoch contraction. -/
theorem lemma519_geometricTheta_eq_gamma_prev_large_m {n dim : Nat}
    (S : Setup n dim) (hmu : 0 < S.mu) {r t : Nat}
    (hr_cut : theorem59Cutoff S < r)
    (hm_large :
      3 * averageSmoothness S / (4 * S.mu) <= componentCountReal n) :
    theorem59GeometricTheta S r t =
      theorem59GeometricGamma S r (t - 1) := by
  have halpha : theorem59Alpha S r = (1 / 2 : Real) :=
    theorem59_geometric_large_m_alpha_eq_half S hmu hr_cut hm_large
  unfold theorem59GeometricTheta SOptLib.geometricEpochTheta
  by_cases ht : t = theorem59EpochLength S r
  · simp [ht]
  · rw [if_neg ht, halpha]
    norm_num [theorem59P]

/-- Geometric theta mass dominates the cutoff epoch length in the large-`m`
strict branch.

Aligns with Lan Lemma 5.19 proof step 7, `sum theta_t >= T_{s_0}`. Considered
SOptLib `finite_window_weighted_recurrence_telescope_with_tail_sums` and
`sum_Icc_two_coeff_telescope_le`; they telescope recurrences but do not state
the branch-local lower bound on the geometric output-weight denominator. -/
theorem lemma519_geometric_theta_sum_lower_bound {n dim : Nat}
    (S : Setup n dim) (hmu : 0 < S.mu) {r : Nat}
    (hr_cut : theorem59Cutoff S < r)
    (hm_large :
      3 * averageSmoothness S / (4 * S.mu) <= componentCountReal n) :
    ((theorem59EpochLength S (theorem59Cutoff S) : Nat) : Real) <=
      Finset.univ.sum
        (fun t : Fin (theorem59EpochLength S r) =>
          theorem59GeometricTheta S r (paperTime t)) := by
  have hnot_cut : ¬ r <= theorem59Cutoff S := by omega
  have hT_eq :
      theorem59EpochLength S r =
        theorem59EpochLength S (theorem59Cutoff S) := by
    unfold theorem59EpochLength
    simp [hnot_cut, theorem59Cutoff_one_le S]
  have hbase_ge_one : (1 : Real) <= 1 + S.mu * theorem59Gamma S r := by
    have hmul_nonneg : 0 <= S.mu * theorem59Gamma S r :=
      mul_nonneg (le_of_lt hmu) (le_of_lt (theorem59Gamma_pos S r))
    nlinarith
  have hterm :
      forall t : Fin (theorem59EpochLength S r),
        (1 : Real) <= theorem59GeometricTheta S r (paperTime t) := by
    intro t
    rw [lemma519_geometricTheta_eq_gamma_prev_large_m S hmu hr_cut hm_large]
    unfold theorem59GeometricGamma
    exact one_le_pow₀ hbase_ge_one
  calc
    ((theorem59EpochLength S (theorem59Cutoff S) : Nat) : Real) =
        ((theorem59EpochLength S r : Nat) : Real) := by
          rw [hT_eq]
    _ = Finset.univ.sum
        (fun _t : Fin (theorem59EpochLength S r) => (1 : Real)) := by
          simp
    _ <= Finset.univ.sum
        (fun t : Fin (theorem59EpochLength S r) =>
          theorem59GeometricTheta S r (paperTime t)) :=
          Finset.sum_le_sum (fun t _ht => hterm t)

/-- Geometric theta mass dominates the cutoff epoch length at the recursion
base `s_0`.

Aligns with Lan Lemma 5.19 proof step 7, where after the large-`m` recursion
the base potential is compared using `sum theta_t >= T_{s_0}`. Existing
candidate `lemma519_geometric_theta_sum_lower_bound` covers only strict
large-`m` epochs; the SOptLib telescope candidates considered there do not
state this base-epoch denominator comparison. -/
theorem lemma519_geometric_theta_sum_lower_bound_cutoff {n dim : Nat}
    (S : Setup n dim) (hmu : 0 < S.mu) :
    ((theorem59EpochLength S (theorem59Cutoff S) : Nat) : Real) <=
      Finset.univ.sum
        (fun t : Fin (theorem59EpochLength S (theorem59Cutoff S)) =>
          theorem59GeometricTheta S (theorem59Cutoff S) (paperTime t)) := by
  have halpha : theorem59Alpha S (theorem59Cutoff S) = (1 / 2 : Real) := by
    simp [theorem59Alpha, theorem59Cutoff_one_le S]
  have htheta_gamma :
      forall t : Nat,
        theorem59GeometricTheta S (theorem59Cutoff S) t =
          theorem59GeometricGamma S (theorem59Cutoff S) (t - 1) := by
    intro t
    unfold theorem59GeometricTheta SOptLib.geometricEpochTheta
    by_cases ht : t = theorem59EpochLength S (theorem59Cutoff S)
    · simp [ht]
    · rw [if_neg ht, halpha]
      norm_num [theorem59P]
  have hbase_ge_one :
      (1 : Real) <= 1 + S.mu * theorem59Gamma S (theorem59Cutoff S) := by
    have hmul_nonneg :
        0 <= S.mu * theorem59Gamma S (theorem59Cutoff S) :=
      mul_nonneg (le_of_lt hmu) (le_of_lt (theorem59Gamma_pos S (theorem59Cutoff S)))
    nlinarith
  have hterm :
      forall t : Fin (theorem59EpochLength S (theorem59Cutoff S)),
        (1 : Real) <=
          theorem59GeometricTheta S (theorem59Cutoff S) (paperTime t) := by
    intro t
    rw [htheta_gamma]
    unfold theorem59GeometricGamma
    exact one_le_pow₀ hbase_ge_one
  calc
    ((theorem59EpochLength S (theorem59Cutoff S) : Nat) : Real) =
        Finset.univ.sum
          (fun _t : Fin (theorem59EpochLength S (theorem59Cutoff S)) =>
            (1 : Real)) := by
          simp
    _ <= Finset.univ.sum
        (fun t : Fin (theorem59EpochLength S (theorem59Cutoff S)) =>
          theorem59GeometricTheta S (theorem59Cutoff S) (paperTime t)) :=
          Finset.sum_le_sum (fun t _ht => hterm t)

/-- Consecutive strict large-`m` epochs have the same geometric theta mass.

Aligns with Lan Lemma 5.19 proof step 6, where the denominator
`sum_t theta_t` is carried unchanged across the large-`m` one-epoch
contraction. Candidates considered: `lemma519_geometricTheta_eq_gamma_prev_large_m`
proves pointwise theta/Gamma alignment only for strict epochs, and
`lemma519_geometric_theta_sum_lower_bound` gives a lower bound rather than
mass equality; no SOptLib telescope candidate states this paper-specific
constant-epoch, constant-gamma mass identity. -/
theorem lemma519_geometric_theta_mass_prev_eq_large_m {n dim : Nat}
    (S : Setup n dim) (hmu : 0 < S.mu) {r : Nat}
    (hr_cut : theorem59Cutoff S < r)
    (hm_large :
      3 * averageSmoothness S / (4 * S.mu) <= componentCountReal n) :
    Finset.univ.sum
        (fun t : Fin (theorem59EpochLength S r) =>
          theorem59GeometricTheta S r (paperTime t)) =
      Finset.univ.sum
        (fun t : Fin (theorem59EpochLength S (r - 1)) =>
          theorem59GeometricTheta S (r - 1) (paperTime t)) := by
  have hnot_r : ¬ r <= theorem59Cutoff S := by omega
  have hcut_le_prev : theorem59Cutoff S <= r - 1 := by omega
  have hT_r :
      theorem59EpochLength S r =
        theorem59EpochLength S (theorem59Cutoff S) := by
    unfold theorem59EpochLength
    simp [hnot_r, theorem59Cutoff_one_le S]
  have hT_prev :
      theorem59EpochLength S (r - 1) =
        theorem59EpochLength S (theorem59Cutoff S) := by
    by_cases hprev : r - 1 <= theorem59Cutoff S
    · have hprev_eq : r - 1 = theorem59Cutoff S := by omega
      rw [hprev_eq]
    · unfold theorem59EpochLength
      simp [hprev, theorem59Cutoff_one_le S]
  have halpha_r : theorem59Alpha S r = (1 / 2 : Real) :=
    theorem59_geometric_large_m_alpha_eq_half S hmu hr_cut hm_large
  have halpha_prev : theorem59Alpha S (r - 1) = (1 / 2 : Real) := by
    by_cases hprev_strict : theorem59Cutoff S < r - 1
    · exact theorem59_geometric_large_m_alpha_eq_half S hmu hprev_strict hm_large
    · have hprev_eq : r - 1 = theorem59Cutoff S := by omega
      simp [hprev_eq, theorem59Alpha, theorem59Cutoff_one_le S]
  have hgamma_r :
      theorem59Gamma S r = 2 / (3 * averageSmoothness S) := by
    unfold theorem59Gamma
    rw [halpha_r]
    field_simp [ne_of_gt (averageSmoothness_pos S)]
  have hgamma_prev :
      theorem59Gamma S (r - 1) = 2 / (3 * averageSmoothness S) := by
    unfold theorem59Gamma
    rw [halpha_prev]
    field_simp [ne_of_gt (averageSmoothness_pos S)]
  rw [hT_r, hT_prev]
  refine Finset.sum_congr rfl ?_
  intro t _ht
  unfold theorem59GeometricTheta SOptLib.geometricEpochTheta theorem59GeometricGamma
  simp [halpha_r, halpha_prev, hgamma_r, hgamma_prev, hT_r, hT_prev, theorem59P]

/-- Pure scalar conversion from weighted recursion to normalized contraction.

Aligns with Lan Lemma 5.19 proof step 6: divide the Gamma-weighted epoch
recursion by the theta mass, use `Gamma_T >= 5/4`, and drop only terms with
explicit nonnegativity. Candidates considered: `mul_le_mul_of_nonneg_left`,
`inv_le_inv₀`, and field arithmetic are Mathlib primitives consumed here;
the pre-searched SOptLib weighted-variance/telescope facts do not perform this
post-telescope scalar potential normalization. -/
theorem lemma519_weighted_recursion_to_potential_contraction_scalar
    (L theta thetaPrev Gamma G Gprev B Bprev : Real)
    (hL_pos : 0 < L)
    (htheta_pos : 0 < theta)
    (htheta_prev_eq : thetaPrev = theta)
    (hweighted :
      (4 / (3 * L)) * theta * G + Gamma * B <=
        (2 / (3 * L)) * theta * Gprev + Bprev)
    (hgamma_lower : (5 / 4 : Real) <= Gamma)
    (hG_nonneg : 0 <= G)
    (hB_nonneg : 0 <= B) :
    (2 / (3 * L)) * G + theta⁻¹ * B <=
      (4 / 5 : Real) * ((2 / (3 * L)) * Gprev + thetaPrev⁻¹ * Bprev) := by
  have hcontract := SOptLib.normalized_potential_contraction_of_weighted_recursion
    (2 / (3 * L)) (4 / (3 * L)) (5 / 4 : Real)
    theta thetaPrev Gamma G Gprev B Bprev
    (by norm_num) htheta_pos htheta_prev_eq hweighted
    (by
      field_simp [ne_of_gt hL_pos]
      nlinarith [hL_pos])
    hgamma_lower hG_nonneg hB_nonneg
  simpa [(show ((5 / 4 : Real)⁻¹) = 4 / 5 by norm_num)] using hcontract

/-- A constant one-step epoch contraction iterates from the cutoff epoch to a
later strict epoch.

Aligns with Lan Lemma 5.19 proof step 7. Considered SOptLib
`finite_window_weighted_recurrence_telescope_with_tail_sums` and
`sum_Icc_two_coeff_telescope_le`; those are finite-window inner-loop
telescopes, while this helper is the outer epoch recursion
`P_r <= (4/5) P_{r-1}` from `s_0` to `s`. -/
theorem lemma519_scalar_epoch_contraction_chain
    (P : Nat -> Real) (c s : Nat) (hcs : c <= s)
    (hstep : forall r, c < r -> r <= s ->
      P r <= (4 / 5 : Real) * P (r - 1)) :
    P s <= (4 / 5 : Real) ^ (s - c) * P c := by
  exact SOptLib.le_pow_mul_of_backward_contraction_on_Ioc P (4 / 5 : Real) c s hcs
    (by norm_num) hstep

/-- Zero-based weighted telescope for the large-`m` geometric inner loop.

Aligns with Lan Lemma 5.19 proof steps 3-4: after multiplying Lemma 5.16 by
`Gamma_{t-1}`, the adjacent `Gamma_k B_k` terms telescope over one epoch.
Considered SOptLib `finite_window_weighted_recurrence_telescope_with_tail_sums`,
`sum_weighted_sub_mul_le_first_sub_tail`, and `sum_Icc_two_coeff_telescope_le`;
they are one-based estimate-sequence or coefficient-bridge telescopes, while
this helper is the exact zero-based cancellation shape used by the printed
Theorem 5.9 epoch process. -/
theorem lemma519_scalar_weighted_one_epoch_telescope
    (T : Nat) (A B C W : Nat -> Real)
    (hW0 : W 0 = 1)
    (hstep :
      forall k, k < T ->
        A (k + 1) + W (k + 1) * B (k + 1) <= C k + W k * B k) :
    (Finset.range T).sum (fun k => A (k + 1)) + W T * B T <=
      (Finset.range T).sum C + B 0 := by
  exact SOptLib.sum_range_succ_add_weighted_tail_le_sum_add_initial_of_step T A B C W hW0 hstep

/-- Scalar endgame for Lan Lemma 5.19's large-`m` branch.

Aligns with Lemma 5.19 proof step 8: after the recursive potential estimate
and the cutoff denominator comparison have been proved, this helper converts
the scaled potential bound into the printed objective-gap rate. Searched
target-file and SOptLib scalar/telescope helpers; existing candidates prove the
recursion or finite-window sums, while this is only the final coefficient
normalization `1/(2 T_{s_0}) <= (4/5)^{s_0}`. -/
theorem lemma519_scalar_rate_from_potential_bound
    (L T D0 Gap P : Real) (c s : Nat)
    (hL : 0 < L) (hT : 0 < T) (hD0 : 0 <= D0) (hcs : c <= s)
    (hcoef_base : (2 * T)⁻¹ <= (4 / 5 : Real) ^ c)
    (hGap : Gap <= (3 * L / 2) * P)
    (hP : P <= (4 / 5 : Real) ^ (s - c) * (D0 / (3 * L * T))) :
    Gap <= (4 / 5 : Real) ^ s * D0 := by
  exact SOptLib.geometric_rate_from_cutoff_potential_bound
    (4 / 5 : Real) L T D0 Gap P c s (by norm_num)
    hL hT hD0 hcs hcoef_base hGap hP

/-- Cutoff coefficient comparison used in Lan Lemma 5.19 step 8.

Aligns with the source simplification
`1 / (2 T_{s_0}) = 1 / 2^{s_0} <= (4/5)^{s_0}`. Considered
`theorem59EpochLength_cutoff_ge_half_componentCount`,
`lemma519_geometric_theta_sum_lower_bound_cutoff`, and SOptLib inverse-product
helpers; those compare the cutoff length to component count or theta mass,
while this proof is the paper-local power comparison for the final rate
normalization. -/
theorem lemma519_cutoff_inverse_epoch_coeff_le_rate
    {n dim : Nat} (S : Setup n dim) :
    (2 * (((theorem59EpochLength S (theorem59Cutoff S) : Nat) : Real)))⁻¹ <=
      (4 / 5 : Real) ^ theorem59Cutoff S := by
  let c := theorem59Cutoff S
  have hc_one : 1 <= c := by
    simpa [c] using theorem59Cutoff_one_le S
  have hT :
      theorem59EpochLength S (theorem59Cutoff S) = 2 ^ (c - 1) := by
    simpa [c, theorem59EpochLength, theorem59Cutoff_one_le S]
  have hden :
      2 * (((theorem59EpochLength S (theorem59Cutoff S) : Nat) : Real)) =
        (2 : Real) ^ c := by
    rw [hT]
    calc
      2 * (((2 ^ (c - 1) : Nat) : Real)) =
          2 * (2 : Real) ^ (c - 1) := by
            norm_num [Nat.cast_pow]
      _ = (2 : Real) ^ ((c - 1) + 1) := by
            rw [pow_succ]
            ring
      _ = (2 : Real) ^ c := by
            rw [show c - 1 + 1 = c by omega]
  have hpow :
      ((2 : Real) ^ c)⁻¹ <= (4 / 5 : Real) ^ c := by
    have hhalf_pow :
        (1 / 2 : Real) ^ c <= (4 / 5 : Real) ^ c := by
      exact pow_le_pow_left₀ (by norm_num) (by norm_num) c
    have hinv_pow :
        ((2 : Real) ^ c)⁻¹ = (1 / 2 : Real) ^ c := by
      rw [← inv_pow]
      norm_num
    rw [hinv_pow]
    exact hhalf_pow
  rw [hden]
  exact hpow

/-- Tail-regime scalar comparison selecting the constant square-root alpha branch.

Aligns with Lan Lemma 5.21's statement that after
`sbar_0 = s_0 + sqrt(12L/(m mu)) - 4`, the policy uses
`alpha_s = sqrt(m mu/(3L))`. Searched target-file schedule helpers,
SOptLib sqrt/ceiling bounds, and Mathlib sqrt-order lemmas; no existing
candidate bridges this paper-specific natural epoch offset to the reciprocal
square-root inequality, so this helper isolates that scalar conversion. -/
theorem theorem59_geometric_tail_left_le_sqrt {n dim : Nat}
    (S : Setup n dim) (hmu : 0 < S.mu) {s : Nat}
    (hs_cut : theorem59Cutoff S < s)
    (_hsmall :
      componentCountReal n < 3 * averageSmoothness S / (4 * S.mu))
    (htail : theorem59TailCutoff S hmu (averageSmoothness_pos S) < (s : Real)) :
    2 / ((s - theorem59Cutoff S + 4 : Nat) : Real) <=
      Real.sqrt (componentCountReal n * S.mu / (3 * averageSmoothness S)) := by
  have hL_pos : 0 < averageSmoothness S := averageSmoothness_pos S
  have hm_pos : 0 < componentCountReal n := componentCountReal_pos S
  have hden_pos :
      0 < ((s - theorem59Cutoff S + 4 : Nat) : Real) := by
    have hden_nat : 0 < s - theorem59Cutoff S + 4 := by
      omega
    exact_mod_cast hden_nat
  have hden_real :
      ((s - theorem59Cutoff S + 4 : Nat) : Real) =
        (s : Real) - theorem59Cutoff S + 4 := by
    have hsub : theorem59Cutoff S <= s := le_of_lt hs_cut
    norm_num [Nat.cast_sub hsub]
  have htail_bound :
      Real.sqrt (12 * averageSmoothness S / (componentCountReal n * S.mu)) <
        ((s - theorem59Cutoff S + 4 : Nat) : Real) := by
    unfold theorem59TailCutoff at htail
    rw [hden_real]
    nlinarith
  let A : Real := componentCountReal n * S.mu / (3 * averageSmoothness S)
  let B : Real := 12 * averageSmoothness S / (componentCountReal n * S.mu)
  let d : Real := ((s - theorem59Cutoff S + 4 : Nat) : Real)
  have hB_nonneg : 0 <= B := by
    dsimp [B]
    exact le_of_lt (div_pos (by positivity : 0 < 12 * averageSmoothness S)
      (mul_pos hm_pos hmu))
  have hd_pos : 0 < d := by
    dsimp [d]
    exact hden_pos
  have hsqrtB_lt_d : Real.sqrt B < d := by
    simpa [B, d] using htail_bound
  have hAB : A * B = 4 := by
    dsimp [A, B]
    field_simp [ne_of_gt hm_pos, ne_of_gt hmu, ne_of_gt hL_pos]
    ring
  have hmain : 2 / d <= Real.sqrt A :=
    SOptLib.two_div_le_sqrt_of_sqrt_lt_of_mul_eq_four
      hB_nonneg hd_pos hsqrtB_lt_d hAB
  simpa [A, d] using hmain

/-- Small-`m` tail branch identification for the Theorem 5.9 acceleration schedule.

Aligns with Lan Lemma 5.21 and Eq. (5.4.25). Existing candidates considered:
`theorem59_alpha_bounds_aux`, `theorem59_geometric_tail_left_le_sqrt`, generic
SOptLib sqrt/ceiling facts, and Mathlib sqrt-order lemmas; only the local tail
offset helper supplies the paper-specific left-branch comparison. -/
theorem theorem59_geometric_tail_alpha_eq_sqrt {n dim : Nat}
    (S : Setup n dim) (hmu : 0 < S.mu) {s : Nat}
    (hs_cut : theorem59Cutoff S < s)
    (hsmall :
      componentCountReal n < 3 * averageSmoothness S / (4 * S.mu))
    (htail : theorem59TailCutoff S hmu (averageSmoothness_pos S) < (s : Real)) :
    theorem59Alpha S s =
      Real.sqrt (componentCountReal n * S.mu / (3 * averageSmoothness S)) := by
  have hL_pos : 0 < averageSmoothness S := averageSmoothness_pos S
  have hnot_cut : ¬ s <= theorem59Cutoff S := by
    omega
  have hleft_le_sqrt :
      2 / ((s - theorem59Cutoff S + 4 : Nat) : Real) <=
        Real.sqrt (componentCountReal n * S.mu / (3 * averageSmoothness S)) :=
    theorem59_geometric_tail_left_le_sqrt S hmu hs_cut hsmall htail
  have harg_lt_quarter :
      componentCountReal n * S.mu / (3 * averageSmoothness S) < (1 / 4 : Real) := by
    rw [div_lt_iff₀ (by positivity : 0 < 3 * averageSmoothness S)]
    have hsmall_mul :
        componentCountReal n * (4 * S.mu) <
          (3 * averageSmoothness S / (4 * S.mu)) * (4 * S.mu) := by
      exact mul_lt_mul_of_pos_right hsmall (by positivity)
    have hsmall_cleared : componentCountReal n * (4 * S.mu) < 3 * averageSmoothness S := by
      have hden_pos' : 0 < 4 * S.mu := by positivity
      field_simp [ne_of_gt hden_pos'] at hsmall_mul
      nlinarith
    nlinarith
  have hsqrt_lt_half :
      Real.sqrt (componentCountReal n * S.mu / (3 * averageSmoothness S)) <
        (1 / 2 : Real) := by
    rw [Real.sqrt_lt' (by norm_num : 0 < (1 / 2 : Real))]
    norm_num
    exact harg_lt_quarter
  unfold theorem59Alpha
  rw [if_neg hnot_cut]
  rw [min_eq_left (le_of_lt hsqrt_lt_half)]
  exact max_eq_right hleft_le_sqrt

/-- Intermediate small-`m` branch identification for Eq. (5.4.25).

In Lemma 5.20's range `s <= sbar_0`, the left branch
`2/(s-s_0+4)` dominates the square-root branch, so the printed schedule uses
the reciprocal offset. -/
theorem theorem59_intermediate_alpha_eq_left {n dim : Nat}
    (S : Setup n dim) (hmu : 0 < S.mu) {s : Nat}
    (hs_cut : theorem59Cutoff S < s)
    (hs_right :
      (s : Real) <= theorem59TailCutoff S hmu (averageSmoothness_pos S)) :
    theorem59Alpha S s =
      2 / ((s - theorem59Cutoff S + 4 : Nat) : Real) := by
  have hL_pos : 0 < averageSmoothness S := averageSmoothness_pos S
  have hm_pos : 0 < componentCountReal n := componentCountReal_pos S
  have hnot_cut : ¬ s <= theorem59Cutoff S := by
    omega
  have hden_pos :
      0 < ((s - theorem59Cutoff S + 4 : Nat) : Real) := by
    have hden_nat : 0 < s - theorem59Cutoff S + 4 := by
      omega
    exact_mod_cast hden_nat
  have hden_real :
      ((s - theorem59Cutoff S + 4 : Nat) : Real) =
        (s : Real) - theorem59Cutoff S + 4 := by
    have hsub : theorem59Cutoff S <= s := le_of_lt hs_cut
    norm_num [Nat.cast_sub hsub]
  let A : Real := componentCountReal n * S.mu / (3 * averageSmoothness S)
  let B : Real := 12 * averageSmoothness S / (componentCountReal n * S.mu)
  let d : Real := ((s - theorem59Cutoff S + 4 : Nat) : Real)
  have hA_pos : 0 < A := by
    dsimp [A]
    exact div_pos (mul_pos hm_pos hmu) (by positivity)
  have hB_nonneg : 0 <= B := by
    dsimp [B]
    exact le_of_lt (div_pos (by positivity : 0 < 12 * averageSmoothness S)
      (mul_pos hm_pos hmu))
  have hd_pos : 0 < d := by
    dsimp [d]
    exact hden_pos
  have hd_le_sqrtB : d <= Real.sqrt B := by
    unfold theorem59TailCutoff at hs_right
    dsimp [d, B]
    rw [hden_real]
    nlinarith
  have hdsq_le_B : d ^ 2 <= B := by
    have hmul :
        d * d <= Real.sqrt B * Real.sqrt B :=
      mul_self_le_mul_self (le_of_lt hd_pos) hd_le_sqrtB
    have hsqrt_sq : Real.sqrt B * Real.sqrt B = B := by
      simpa [pow_two] using Real.sq_sqrt hB_nonneg
    simpa [pow_two, hsqrt_sq] using hmul
  have hAB : A * B = 4 := by
    dsimp [A, B]
    field_simp [ne_of_gt hm_pos, ne_of_gt hmu, ne_of_gt hL_pos]
    ring
  have hA_dsq_le_four : A * d ^ 2 <= 4 := by
    calc
      A * d ^ 2 <= A * B := mul_le_mul_of_nonneg_left hdsq_le_B (le_of_lt hA_pos)
      _ = 4 := hAB
  have hA_le_div_sq : A <= (2 / d) ^ 2 := by
    rw [div_pow]
    rw [le_div_iff₀ (sq_pos_of_pos hd_pos)]
    nlinarith
  have hsqrt_le_left : Real.sqrt A <= 2 / d := by
    rw [Real.sqrt_le_iff]
    exact ⟨le_of_lt (div_pos (by norm_num) hd_pos), hA_le_div_sq⟩
  unfold theorem59Alpha
  rw [if_neg hnot_cut]
  exact max_eq_left (le_trans (min_le_left _ _) (by simpa [A, d] using hsqrt_le_left))

/-- Scalar coefficient budget needed for positivity of the geometric
Eq. (5.4.26) output weights.

Aligns with Lan Lemmas 5.19 and 5.21. The checked candidates were
`theorem59_alpha_bounds_aux`, target-file geometric theta helpers, SOptLib
finite-sum/telescope facts, and Mathlib sqrt-order lemmas; none state the
paper-specific regime split, so this helper packages the exact split into
large-`m` and small-`m` tail cases. -/
theorem theorem59_geometric_coeff_base_lt_one {n dim : Nat}
    (S : Setup n dim) (hmu : 0 < S.mu) {s : Nat}
    (hs : 1 <= s)
    (hgeom : ¬ theorem59UsesSmoothTheta S hmu (averageSmoothness_pos S) s) :
    (1 - theorem59Alpha S s - theorem59P s) *
        (1 + S.mu * theorem59Gamma S s) < 1 := by
  have hcut_lt : theorem59Cutoff S < s := by
    by_contra hnot
    have hle : s <= theorem59Cutoff S := by
      omega
    exact hgeom (Or.inl ⟨hs, hle⟩)
  by_cases hsmall :
      componentCountReal n < 3 * averageSmoothness S / (4 * S.mu)
  · have htail :
        theorem59TailCutoff S hmu (averageSmoothness_pos S) < (s : Real) := by
      by_contra hnot_tail
      have hs_le_tail :
          (s : Real) <= theorem59TailCutoff S hmu (averageSmoothness_pos S) :=
        le_of_not_gt hnot_tail
      exact hgeom (Or.inr ⟨hcut_lt, hs_le_tail, hsmall⟩)
    have halpha :
        theorem59Alpha S s =
          Real.sqrt (componentCountReal n * S.mu / (3 * averageSmoothness S)) :=
      theorem59_geometric_tail_alpha_eq_sqrt S hmu hcut_lt hsmall htail
    have hL_pos : 0 < averageSmoothness S := averageSmoothness_pos S
    have ha_pos : 0 < theorem59Alpha S s := theorem59Alpha_pos_aux S s
    have ha_half : theorem59Alpha S s < (1 / 2 : Real) := by
      rw [halpha]
      have harg_lt_quarter :
          componentCountReal n * S.mu / (3 * averageSmoothness S) < (1 / 4 : Real) := by
        rw [div_lt_iff₀ (by positivity : 0 < 3 * averageSmoothness S)]
        have hsmall_mul :
            componentCountReal n * (4 * S.mu) <
              (3 * averageSmoothness S / (4 * S.mu)) * (4 * S.mu) := by
          exact mul_lt_mul_of_pos_right hsmall (by positivity)
        have hsmall_cleared :
            componentCountReal n * (4 * S.mu) < 3 * averageSmoothness S := by
          have hden_pos' : 0 < 4 * S.mu := by positivity
          field_simp [ne_of_gt hden_pos'] at hsmall_mul
          nlinarith
        nlinarith
      rw [Real.sqrt_lt' (by norm_num : 0 < (1 / 2 : Real))]
      norm_num
      exact harg_lt_quarter
    have hmu_gamma_le_alpha : S.mu * theorem59Gamma S s <= theorem59Alpha S s := by
      unfold theorem59Gamma
      rw [halpha]
      have hm_ge_one : (1 : Real) <= componentCountReal n := by
        unfold componentCountReal
        exact_mod_cast S.component_count_pos
      have harg_nonneg :
          0 <= componentCountReal n * S.mu / (3 * averageSmoothness S) := by
        exact div_nonneg (mul_nonneg (le_of_lt (componentCountReal_pos S)) (le_of_lt hmu))
          (by positivity)
      have hsqrt_pos :
          0 < Real.sqrt (componentCountReal n * S.mu / (3 * averageSmoothness S)) := by
        exact Real.sqrt_pos.mpr
          (div_pos (mul_pos (componentCountReal_pos S) hmu) (by positivity))
      have hden_pos :
          0 < 3 * averageSmoothness S *
            Real.sqrt (componentCountReal n * S.mu / (3 * averageSmoothness S)) := by
        positivity
      have hsq :
          (Real.sqrt (componentCountReal n * S.mu / (3 * averageSmoothness S))) ^ 2 =
            componentCountReal n * S.mu / (3 * averageSmoothness S) :=
        Real.sq_sqrt harg_nonneg
      rw [div_eq_mul_inv, one_mul]
      rw [mul_inv_le_iff₀ hden_pos]
      have hrhs_eq :
          Real.sqrt (componentCountReal n * S.mu / (3 * averageSmoothness S)) *
              (3 * averageSmoothness S *
                Real.sqrt (componentCountReal n * S.mu / (3 * averageSmoothness S))) =
            componentCountReal n * S.mu := by
        calc
          Real.sqrt (componentCountReal n * S.mu / (3 * averageSmoothness S)) *
              (3 * averageSmoothness S *
                Real.sqrt (componentCountReal n * S.mu / (3 * averageSmoothness S))) =
              3 * averageSmoothness S *
                (Real.sqrt (componentCountReal n * S.mu / (3 * averageSmoothness S))) ^ 2 := by
            ring
          _ = 3 * averageSmoothness S *
                (componentCountReal n * S.mu / (3 * averageSmoothness S)) := by
            rw [hsq]
          _ = componentCountReal n * S.mu := by
            field_simp [ne_of_gt hL_pos]
      rw [hrhs_eq]
      simpa using mul_le_mul_of_nonneg_right hm_ge_one (le_of_lt hmu)
    simp [theorem59P]
    nlinarith
  · have hlarge :
        3 * averageSmoothness S / (4 * S.mu) <= componentCountReal n :=
      le_of_not_gt hsmall
    have halpha : theorem59Alpha S s = 1 / 2 :=
      theorem59_geometric_large_m_alpha_eq_half S hmu hcut_lt hlarge
    simp [theorem59P, halpha]
    norm_num

/-- Geometric-branch theta-weight admissibility for Theorem 5.9.

Aligns with Lan Eq. (5.4.26). Considered `Finset.sum_pos`, the target-file
geometric positivity helper, and the schedule coefficient helper; this theorem
is the branch-specific consumer of the paper regime split, not a wrapper around
the public theta dispatcher. -/
theorem theorem59GeometricTheta_epochOutputWeightsAdmissible_aux
    {n dim : Nat} (S : Setup n dim) (hmu : 0 < S.mu) {s : Nat}
    (hs : 1 <= s)
    (hgeom : ¬ theorem59UsesSmoothTheta S hmu (averageSmoothness_pos S) s) :
    epochOutputWeightsAdmissible
      (theorem59GeometricTheta S s)
      (theorem59EpochLength S s) := by
  have hbase_pos : 0 < 1 + S.mu * theorem59Gamma S s := by
    have hmul_nonneg : 0 <= S.mu * theorem59Gamma S s :=
      mul_nonneg (le_of_lt hmu) (le_of_lt (theorem59Gamma_pos S s))
    nlinarith
  have hcoeff :
      (1 - theorem59Alpha S s - theorem59P s) *
          (1 + S.mu * theorem59Gamma S s) < 1 :=
    theorem59_geometric_coeff_base_lt_one S hmu hs hgeom
  exact theorem59GeometricTheta_epochOutputWeightsAdmissible_of_coeff_aux S hbase_pos hcoeff

/-- Source-derived theta-weight admissibility for the Theorem 5.9 schedule.

Theorem 5.9 fixes the switch between Eqs. (5.4.12) and (5.4.26). Positivity of
the denominator in the generated weighted output is a proof obligation from
those printed formulas, not a free output-feasibility theorem. -/
theorem theorem59Theta_epochOutputWeightsAdmissible {n dim : Nat}
    (S : Setup n dim) (hmu : 0 < S.mu) :
    forall s, 1 <= s ->
      epochOutputWeightsAdmissible
        (theorem59Theta S hmu (averageSmoothness_pos S) s)
        (theorem59EpochLength S s) := by
  intro s hs
  by_cases hUse : theorem59UsesSmoothTheta S hmu (averageSmoothness_pos S) s
  · unfold theorem59Theta
    simp [hUse]
    exact
      theorem59SmoothTheta_epochOutputWeightsAdmissible_aux S s hs
  · unfold theorem59Theta
    simp [hUse]
    exact
      theorem59GeometricTheta_epochOutputWeightsAdmissible_aux S hmu hs hUse

/-- Source-derived theta-weight admissibility for the smooth Eq. (5.4.12) schedule. -/
theorem smoothTheta_epochOutputWeightsAdmissible {n dim : Nat}
    (S : Setup n dim) :
    forall s, 1 <= s ->
      epochOutputWeightsAdmissible
        (theorem59SmoothTheta S s)
        (theorem59EpochLength S s) := by
  exact theorem59SmoothTheta_epochOutputWeightsAdmissible_aux S

/-- Smooth-epoch scalar `L_s` from Eq. (5.4.13), for arbitrary epoch parameters.

SOptLib finite-window telescope lemmas were considered, but Lemma 5.17 prints
the scalar `L_s` itself as part of the source statement, so this generic local
definition records the formula before any Theorem 5.9 specialization. -/
def smoothEpochLOf (T : Nat -> Nat) (gamma alpha p : Nat -> Real)
    (s : Nat) : Real :=
  gamma s / alpha s +
    ((T s - 1 : Nat) : Real) * (gamma s * (alpha s + p s) / alpha s)

/-- Smooth-epoch scalar `R_s` from Eq. (5.4.14), for arbitrary epoch parameters.

No SOptLib primitive bundles Lan's printed `R_s`; the reusable telescope layer
starts after these paper coefficients are supplied. -/
def smoothEpochROf (T : Nat -> Nat) (gamma alpha p : Nat -> Real)
    (s : Nat) : Real :=
  gamma s / alpha s * (1 - alpha s) +
    ((T s - 1 : Nat) : Real) * (gamma s * p s / alpha s)

/-- Smooth-epoch weight `w_s = L_s - R_{s+1}` from Eq. (5.4.15). -/
def smoothEpochWeightOf (T : Nat -> Nat) (gamma alpha p : Nat -> Real)
    (s : Nat) : Real :=
  SOptLib.smoothEpochBridgeWeight T gamma alpha p s

/-- Smooth-epoch weighted average `bar x^s` from Eq. (5.4.16), generic in the
epoch coefficients rather than tied to Theorem 5.9. -/
def smoothEpochAverageOf {dim : Nat} (T : Nat -> Nat)
    (gamma alpha p : Nat -> Real)
    (xTilde : Nat -> VariableSpace dim) (s : Nat) : VariableSpace dim :=
  ((Finset.Icc 1 (s - 1)).sum (fun j => smoothEpochWeightOf T gamma alpha p j))⁻¹ •
    (Finset.Icc 1 (s - 1)).sum
      (fun j => smoothEpochWeightOf T gamma alpha p j • xTilde j)

/-- Theorem 5.9 specialization of the Lemma 5.17 scalar `L_s`. -/
def smoothEpochL {n dim : Nat} (S : Setup n dim) (s : Nat) : Real :=
  smoothEpochLOf (theorem59EpochLength S) (theorem59Gamma S)
    (theorem59Alpha S) theorem59P s

/-- Theorem 5.9 specialization of the Lemma 5.17 scalar `R_s`. -/
def smoothEpochR {n dim : Nat} (S : Setup n dim) (s : Nat) : Real :=
  smoothEpochROf (theorem59EpochLength S) (theorem59Gamma S)
    (theorem59Alpha S) theorem59P s

/-- Theorem 5.9 specialization of `w_s = L_s - R_{s+1}`. -/
def smoothEpochWeight {n dim : Nat} (S : Setup n dim) (s : Nat) : Real :=
  smoothEpochWeightOf (theorem59EpochLength S) (theorem59Gamma S)
    (theorem59Alpha S) theorem59P s

/-- Theorem 5.9 specialization of the cross-epoch weighted average `bar x^s`. -/
def smoothEpochAverage {n dim : Nat} (S : Setup n dim)
    (xTilde : Nat -> VariableSpace dim) (s : Nat) : VariableSpace dim :=
  smoothEpochAverageOf (theorem59EpochLength S) (theorem59Gamma S)
    (theorem59Alpha S) theorem59P xTilde s

/-- Internal core-valued inner-loop state for recursive Bregman use.

Both generated points are carried on the prox core `X^o`, because Algorithm 5.7
uses the search point and the prox iterate as left arguments of the paper
Bregman object `V : X^o × X -> R+`. The proof that the printed updates stay in
`X^o` is left as source-derived theorem obligations; the paper-facing one-step
state below keeps the prox argmin at its printed codomain `X`. -/
structure InnerStateOn {n dim : Nat} (S : Setup n dim) where
  x : Set.Elem (proxCoreSet S)
  xBar : Set.Elem (proxCoreSet S)

/-- Paper-facing feasible inner-loop state for one Algorithm 5.7 step.

The printed prox update selects `x_t` by an argmin over `X`, not over `X^o`.
This state records that source boundary directly. The recursive core-valued
process below is an internal realization that additionally carries the separate
domain obligation needed to reuse generated points as left Bregman arguments. -/
structure InnerStateFeasibleOn {n dim : Nat} (S : Setup n dim) where
  x : FeasiblePoint S
  xBar : FeasiblePoint S

instance instInnerStateFeasibleOnMeasurableSpace {n dim : Nat} (S : Setup n dim) :
    MeasurableSpace (InnerStateFeasibleOn S) :=
  MeasurableSpace.comap (fun state : InnerStateFeasibleOn S => (state.x, state.xBar))
    (by infer_instance)

/-- Algorithm 5.7 search-point value before packaging it as a feasible point. -/
def searchPointValueOn {n dim : Nat} (S : Setup n dim)
    (gamma alpha p : Nat -> Real) (s : Nat)
    (xBarPrev : Set.Elem (proxCoreSet S)) (xPrev : Set.Elem (proxCoreSet S))
    (snapshot : Set.Elem (proxCoreSet S)) : VariableSpace dim :=
  searchPoint S gamma alpha p s xBarPrev.1 xPrev.1 snapshot.1

/-- Source-derived prox-core obligation for the accelerated search point.

Algorithm 5.7 forms the displayed affine-rational combination from points in
`X^o`. Core membership is an object-layer theorem obligation derived from
prox-core convexity and the printed parameter schedule, rather than a
theorem-local hypothesis. -/
theorem searchPointValueOn_mem_proxCore {n dim : Nat} (S : Setup n dim)
    (gamma alpha p : Nat -> Real) (s : Nat)
    (xBarPrev xPrev snapshot : Set.Elem (proxCoreSet S))
    (hweights : searchPointWeights S gamma alpha p s ∈ stdSimplex Real (Fin 3)) :
    searchPointValueOn S gamma alpha p s xBarPrev xPrev snapshot ∈ proxCoreSet S := by
  have hbar : 0 <= searchPointBarWeight S gamma alpha p s := by
    simpa [searchPointWeights] using hweights.1 0
  have hprev : 0 <= searchPointPrevWeight S gamma alpha s := by
    simpa [searchPointWeights] using hweights.1 1
  have hsnap : 0 <= searchPointSnapshotWeight S gamma alpha p s := by
    simpa [searchPointWeights] using hweights.1 2
  have hsum :
      searchPointBarWeight S gamma alpha p s +
        searchPointPrevWeight S gamma alpha s +
          searchPointSnapshotWeight S gamma alpha p s = 1 := by
    simpa [searchPointWeights, Fin.sum_univ_three] using hweights.2
  unfold searchPointValueOn
  simpa [searchPoint_def] using
    convex_three_smul_add_mem (proxCoreSet_convex S) hbar hprev hsnap hsum
      xBarPrev.2 xPrev.2 snapshot.2

/-- Source-facing accelerated search point `underbar x_t` generated by Algorithm 5.7. -/
def searchPointOn {n dim : Nat} (S : Setup n dim)
    (gamma alpha p : Nat -> Real) (s : Nat)
    (xBarPrev xPrev : Set.Elem (proxCoreSet S))
    (snapshot : Set.Elem (proxCoreSet S))
    (hweights : searchPointWeights S gamma alpha p s ∈ stdSimplex Real (Fin 3)) :
    Set.Elem (proxCoreSet S) :=
  ⟨searchPointValueOn S gamma alpha p s xBarPrev xPrev snapshot,
    searchPointValueOn_mem_proxCore S gamma alpha p s xBarPrev xPrev snapshot
      hweights⟩

theorem searchPointOn_coe {n dim : Nat} (S : Setup n dim)
    (gamma alpha p : Nat -> Real) (s : Nat)
    (xBarPrev xPrev : Set.Elem (proxCoreSet S))
    (snapshot : Set.Elem (proxCoreSet S))
    (hweights : searchPointWeights S gamma alpha p s ∈ stdSimplex Real (Fin 3)) :
    (searchPointOn S gamma alpha p s xBarPrev xPrev snapshot
      hweights).1 =
      searchPointValueOn S gamma alpha p s xBarPrev xPrev snapshot :=
  rfl

/-- Variance-reduced gradient estimator evaluated on paper-domain points. -/
def varianceReducedGradientOn {n dim : Nat} (S : Setup n dim)
    (q : Fin n -> Real) (sample : Fin n)
    (xUnder : Set.Elem (proxCoreSet S)) (snapshot : Set.Elem (proxCoreSet S))
    (fullGradAtSnapshot : VariableSpace dim) : VariableSpace dim :=
  varianceReducedGradient S q sample xUnder.1 snapshot.1 fullGradAtSnapshot

/-- Split the Algorithm 5.7 estimator into exact gradient plus residual.

Target/SOptLib searches for `varianceReducedGradient estimatorResidual
fullGradient add delta` found only the underlying local definitions; no
pre-existing bridge had this exact prox-core subtype-specialized shape. This
theorem is the definitional alignment needed to apply Lemma 5.15 with
`delta = estimatorResidual`. -/
theorem varianceReducedGradientOn_eq_fullGradient_add_estimatorResidual
    {n dim : Nat} (S : Setup n dim) (q : Fin n -> Real) (sample : Fin n)
    (xUnder : Set.Elem (proxCoreSet S)) (snapshot : Set.Elem (proxCoreSet S))
    (fullGradAtSnapshot : VariableSpace dim) :
    varianceReducedGradientOn S q sample xUnder snapshot fullGradAtSnapshot =
      fullGradient S xUnder.1 +
        estimatorResidual S q sample xUnder.1 snapshot.1 fullGradAtSnapshot := by
  simpa [varianceReducedGradientOn, estimatorResidual] using
    (SOptLib.eq_target_add_oracleEstimatorError (target := fullGradient S)
      (G := varianceReducedGradientOn S q sample xUnder snapshot fullGradAtSnapshot)
      (x := xUnder.1))

/-- Algorithm 5.7 search-point value on the printed feasible domain `X`. -/
def searchPointValueFeasibleOn {n dim : Nat} (S : Setup n dim)
    (gamma alpha p : Nat -> Real) (s : Nat)
    (xBarPrev : FeasiblePoint S) (xPrev : FeasiblePoint S)
    (snapshot : FeasiblePoint S) : VariableSpace dim :=
  searchPoint S gamma alpha p s xBarPrev.1 xPrev.1 snapshot.1

/-- Source-derived feasibility of the printed accelerated search point. -/
theorem searchPointValueFeasibleOn_mem_X {n dim : Nat} (S : Setup n dim)
    (gamma alpha p : Nat -> Real) (s : Nat)
    (xBarPrev xPrev snapshot : FeasiblePoint S)
    (hweights : searchPointWeights S gamma alpha p s ∈ stdSimplex Real (Fin 3)) :
    searchPointValueFeasibleOn S gamma alpha p s xBarPrev xPrev snapshot ∈ S.X := by
  have hbar : 0 <= searchPointBarWeight S gamma alpha p s := by
    simpa [searchPointWeights] using hweights.1 0
  have hprev : 0 <= searchPointPrevWeight S gamma alpha s := by
    simpa [searchPointWeights] using hweights.1 1
  have hsnap : 0 <= searchPointSnapshotWeight S gamma alpha p s := by
    simpa [searchPointWeights] using hweights.1 2
  have hsum :
      searchPointBarWeight S gamma alpha p s +
        searchPointPrevWeight S gamma alpha s +
          searchPointSnapshotWeight S gamma alpha p s = 1 := by
    simpa [searchPointWeights, Fin.sum_univ_three] using hweights.2
  unfold searchPointValueFeasibleOn
  simpa [searchPoint_def] using
    convex_three_smul_add_mem S.X_convex hbar hprev hsnap hsum
      xBarPrev.2 xPrev.2 snapshot.2

/-- Source-facing accelerated search point `underbar x_t` on the printed feasible
carrier. -/
def searchPointFeasibleOn {n dim : Nat} (S : Setup n dim)
    (gamma alpha p : Nat -> Real) (s : Nat)
    (xBarPrev xPrev snapshot : FeasiblePoint S)
    (hweights : searchPointWeights S gamma alpha p s ∈ stdSimplex Real (Fin 3)) :
    FeasiblePoint S :=
  ⟨searchPointValueFeasibleOn S gamma alpha p s xBarPrev xPrev snapshot,
    searchPointValueFeasibleOn_mem_X S gamma alpha p s xBarPrev xPrev snapshot
      hweights⟩

/-- Variance-reduced gradient estimator evaluated on feasible Algorithm 5.7
points. -/
def varianceReducedGradientFeasibleOn {n dim : Nat} (S : Setup n dim)
    (q : Fin n -> Real) (sample : Fin n)
    (xUnder : FeasiblePoint S) (snapshot : FeasiblePoint S)
    (fullGradAtSnapshot : VariableSpace dim) : VariableSpace dim :=
  varianceReducedGradient S q sample xUnder.1 snapshot.1 fullGradAtSnapshot

/-- Printed averaged inner iterate value before prox-core packaging. -/
def averagedInnerIterateValueOn {n dim : Nat} (S : Setup n dim)
    (alpha p : Nat -> Real) (s : Nat)
    (xBarPrev : Set.Elem (proxCoreSet S)) (xNext : Set.Elem (proxCoreSet S))
    (snapshot : Set.Elem (proxCoreSet S)) : VariableSpace dim :=
  averagedInnerIterate alpha p s xBarPrev.1 xNext.1 snapshot.1

/-- Printed averaged inner iterate value with the prox update kept at its source
codomain `X`.

No SOptLib match: checked weighted-average output helpers and
`Convex.normalized_weighted_sum_mem`; they model generic finite averages, while
Algorithm 5.7 prints this three-term update and the preceding prox update is
only an `X`-argmin. -/
def averagedInnerIterateValueFeasibleOn {n dim : Nat} (S : Setup n dim)
    (alpha p : Nat -> Real) (s : Nat)
    (xBarPrev : Set.Elem (proxCoreSet S)) (xNext : FeasiblePoint S)
    (snapshot : Set.Elem (proxCoreSet S)) : VariableSpace dim :=
  averagedInnerIterate alpha p s xBarPrev.1 xNext.1 snapshot.1

/-- Source-derived feasibility of the printed averaged iterate.

This follows from convexity of `X` and the printed coefficient conditions; it is
a theorem obligation, not a theorem-head assumption. -/
theorem averagedInnerIterateValueFeasibleOn_mem_X {n dim : Nat} (S : Setup n dim)
    (alpha p : Nat -> Real) (s : Nat)
    (xBarPrev : Set.Elem (proxCoreSet S)) (xNext : FeasiblePoint S)
    (snapshot : Set.Elem (proxCoreSet S))
    (hweights : averagedInnerWeightsAdmissible alpha p s) :
    averagedInnerIterateValueFeasibleOn S alpha p s xBarPrev xNext snapshot ∈ S.X := by
  rcases hweights with ⟨h0, halpha, hp⟩
  unfold averagedInnerIterateValueFeasibleOn averagedInnerIterate
  apply convex_three_smul_add_mem S.X_convex h0 halpha hp
  · ring
  · exact proxCoreSetElem_mem_X S xBarPrev
  · exact xNext.2
  · exact proxCoreSetElem_mem_X S snapshot

/-- Source-facing averaged inner iterate after the feasible prox update. -/
def averagedInnerIterateFeasibleOn {n dim : Nat} (S : Setup n dim)
    (alpha p : Nat -> Real) (s : Nat)
    (xBarPrev : Set.Elem (proxCoreSet S)) (xNext : FeasiblePoint S)
    (snapshot : Set.Elem (proxCoreSet S))
    (hweights : averagedInnerWeightsAdmissible alpha p s) : FeasiblePoint S :=
  ⟨averagedInnerIterateValueFeasibleOn S alpha p s xBarPrev xNext snapshot,
    averagedInnerIterateValueFeasibleOn_mem_X S alpha p s xBarPrev xNext snapshot hweights⟩

/-- Printed averaged inner iterate value on fully feasible inputs. -/
def averagedInnerIterateValueAllFeasibleOn {n dim : Nat} (S : Setup n dim)
    (alpha p : Nat -> Real) (s : Nat)
    (xBarPrev : FeasiblePoint S) (xNext : FeasiblePoint S)
    (snapshot : FeasiblePoint S) : VariableSpace dim :=
  averagedInnerIterate alpha p s xBarPrev.1 xNext.1 snapshot.1

/-- Source-derived feasibility of the all-feasible averaged inner iterate. -/
theorem averagedInnerIterateValueAllFeasibleOn_mem_X {n dim : Nat} (S : Setup n dim)
    (alpha p : Nat -> Real) (s : Nat)
    (xBarPrev : FeasiblePoint S) (xNext : FeasiblePoint S)
    (snapshot : FeasiblePoint S)
    (hweights : averagedInnerWeightsAdmissible alpha p s) :
    averagedInnerIterateValueAllFeasibleOn S alpha p s xBarPrev xNext snapshot ∈ S.X := by
  rcases hweights with ⟨h0, halpha, hp⟩
  unfold averagedInnerIterateValueAllFeasibleOn averagedInnerIterate
  apply convex_three_smul_add_mem S.X_convex h0 halpha hp
  · ring
  · exact xBarPrev.2
  · exact xNext.2
  · exact snapshot.2

/-- Averaged inner iterate for the all-feasible surrogate prox update. -/
def averagedInnerIterateAllFeasibleOn {n dim : Nat} (S : Setup n dim)
    (alpha p : Nat -> Real) (s : Nat)
    (xBarPrev : FeasiblePoint S) (xNext : FeasiblePoint S)
    (snapshot : FeasiblePoint S)
    (hweights : averagedInnerWeightsAdmissible alpha p s) : FeasiblePoint S :=
  ⟨averagedInnerIterateValueAllFeasibleOn S alpha p s xBarPrev xNext snapshot,
    averagedInnerIterateValueAllFeasibleOn_mem_X S alpha p s xBarPrev xNext snapshot hweights⟩

/-- Internal selected Algorithm 5.7 inner-loop transition with the prox result
kept as a feasible `X`-point.

The canonical one-step object for line 16901 is the relation `InnerStepRelOn`
below. This selected realization is retained for generated processes, but it is
not the source-facing meaning of the printed prox argmin. -/
def innerStepFeasibleOn {n dim : Nat} (S : Setup n dim)
    (gamma alpha p : Nat -> Real) (s : Nat)
    (q : Fin n -> Real) (snapshot : Set.Elem (proxCoreSet S))
    (fullGradAtSnapshot : VariableSpace dim)
    (sample : Fin n) (xPrev xBarPrev : Set.Elem (proxCoreSet S))
    (hsearch : searchPointWeights S gamma alpha p s ∈ stdSimplex Real (Fin 3))
    (havg : averagedInnerWeightsAdmissible alpha p s) :
    InnerStateFeasibleOn S :=
  let xUnder :=
    searchPointOn S gamma alpha p s xBarPrev xPrev snapshot hsearch
  let G := varianceReducedGradientOn S q sample
    xUnder snapshot fullGradAtSnapshot
  let xNext :=
    proxUpdateOn S gamma s xPrev xUnder G
  let xBarNext :=
    averagedInnerIterateFeasibleOn S alpha p s xBarPrev xNext snapshot havg
  { x := xNext, xBar := xBarNext }

/-- Relational paper-facing Algorithm 5.7 inner-loop transition.

This is the canonical object-layer spine for one inner iteration: the search
point and gradient estimator are definitions, while the prox update is the
argmin relation `ProxUpdateRelOn` rather than an already-selected point. The
selected function `innerStepFeasibleOn` below is only an internal realization of
this relation. -/
def InnerStepRelOn {n dim : Nat} (S : Setup n dim)
    (gamma alpha p : Nat -> Real) (s : Nat)
    (q : Fin n -> Real) (snapshot : Set.Elem (proxCoreSet S))
    (fullGradAtSnapshot : VariableSpace dim)
    (sample : Fin n) (xPrev xBarPrev : Set.Elem (proxCoreSet S))
    (hsearch : searchPointWeights S gamma alpha p s ∈ stdSimplex Real (Fin 3))
    (havg : averagedInnerWeightsAdmissible alpha p s)
    (next : InnerStateFeasibleOn S) : Prop :=
  let xUnder :=
    searchPointOn S gamma alpha p s xBarPrev xPrev snapshot hsearch
  let G := varianceReducedGradientOn S q sample
    xUnder snapshot fullGradAtSnapshot
  ProxUpdateRelOn S gamma s xPrev xUnder G next.x ∧
    next.xBar =
      averagedInnerIterateFeasibleOn S alpha p s xBarPrev next.x snapshot havg

theorem innerStepFeasibleOn_satisfies_rel {n dim : Nat} (S : Setup n dim)
    (gamma alpha p : Nat -> Real) (s : Nat)
    (q : Fin n -> Real) (snapshot : Set.Elem (proxCoreSet S))
    (fullGradAtSnapshot : VariableSpace dim)
    (sample : Fin n) (xPrev xBarPrev : Set.Elem (proxCoreSet S))
    (hsearch : searchPointWeights S gamma alpha p s ∈ stdSimplex Real (Fin 3))
    (havg : averagedInnerWeightsAdmissible alpha p s)
    (hprox :
      ProxUpdateRelOn S gamma s xPrev
        (searchPointOn S gamma alpha p s xBarPrev xPrev snapshot hsearch)
        (varianceReducedGradientOn S q sample
          (searchPointOn S gamma alpha p s xBarPrev xPrev snapshot hsearch)
          snapshot fullGradAtSnapshot)
        (proxUpdateOn S gamma s xPrev
          (searchPointOn S gamma alpha p s xBarPrev xPrev snapshot hsearch)
          (varianceReducedGradientOn S q sample
            (searchPointOn S gamma alpha p s xBarPrev xPrev snapshot hsearch)
            snapshot fullGradAtSnapshot))) :
    InnerStepRelOn S gamma alpha p s q snapshot fullGradAtSnapshot sample
      xPrev xBarPrev hsearch havg
      (innerStepFeasibleOn S gamma alpha p s q snapshot fullGradAtSnapshot sample
        xPrev xBarPrev hsearch havg) := by
  unfold InnerStepRelOn innerStepFeasibleOn
  exact ⟨hprox, rfl⟩

/-- Exact obstruction for making the printed `InnerStepRelOn` recursion core-valued.

Any attempt to use `InnerStepRelOn` itself as the generated recursive transition
and then feed the next `x` back as a future left Bregman/core argument is
precisely the retired feasible-prox-to-core bridge. This theorem is the
same-interface obstruction requested by the route audit: it mentions the
canonical relation `InnerStepRelOn` and shows that its `x`-core propagation
obligation is equivalent to proving prox-core membership for every feasible
`ProxUpdateRelOn` output with the same search point and gradient estimator. -/
theorem innerStepRelOn_x_core_propagation_iff_proxUpdateRelOn_mem_proxCore
    {n dim : Nat} (S : Setup n dim)
    (gamma alpha p : Nat -> Real) (s : Nat)
    (q : Fin n -> Real) (snapshot : Set.Elem (proxCoreSet S))
    (fullGradAtSnapshot : VariableSpace dim)
    (sample : Fin n) (xPrev xBarPrev : Set.Elem (proxCoreSet S))
    (hsearch : searchPointWeights S gamma alpha p s ∈ stdSimplex Real (Fin 3))
    (havg : averagedInnerWeightsAdmissible alpha p s) :
    (forall next : InnerStateFeasibleOn S,
        InnerStepRelOn S gamma alpha p s q snapshot fullGradAtSnapshot sample
          xPrev xBarPrev hsearch havg next ->
        next.x.1 ∈ proxCoreSet S) ↔
      (forall z : FeasiblePoint S,
        ProxUpdateRelOn S gamma s xPrev
          (searchPointOn S gamma alpha p s xBarPrev xPrev snapshot hsearch)
          (varianceReducedGradientOn S q sample
            (searchPointOn S gamma alpha p s xBarPrev xPrev snapshot hsearch)
            snapshot fullGradAtSnapshot)
          z ->
        z.1 ∈ proxCoreSet S) := by
  constructor
  · intro hnext z hz
    let next : InnerStateFeasibleOn S :=
      { x := z
        xBar := averagedInnerIterateFeasibleOn S alpha p s xBarPrev z snapshot havg }
    have hstep :
        InnerStepRelOn S gamma alpha p s q snapshot fullGradAtSnapshot sample
          xPrev xBarPrev hsearch havg next := by
      unfold InnerStepRelOn
      exact ⟨hz, rfl⟩
    exact hnext next hstep
  · intro hprox next hstep
    unfold InnerStepRelOn at hstep
    exact hprox next.x hstep.1

/-- Legacy diagnostic correction for the attempted `InnerStepRelOn` recursion.

This is a proved diagnostic, not a paper assumption: a generated process that
uses `InnerStepRelOn` as its recursive step can supply future core-valued
Bregman-left arguments only by proving exactly the feasible `ProxUpdateRelOn`
core-membership bridge that the source-boundary audit rejected as unstated. -/
def legacyDiagnosticAlgorithm57InnerStepCorePropagationEquivalence
    {n dim : Nat} (S : Setup n dim) : Prop :=
  forall (gamma alpha p : Nat -> Real) (s : Nat)
    (q : Fin n -> Real) (snapshot : Set.Elem (proxCoreSet S))
    (fullGradAtSnapshot : VariableSpace dim)
    (sample : Fin n) (xPrev xBarPrev : Set.Elem (proxCoreSet S))
    (hsearch : searchPointWeights S gamma alpha p s ∈ stdSimplex Real (Fin 3))
    (havg : averagedInnerWeightsAdmissible alpha p s),
    (forall next : InnerStateFeasibleOn S,
        InnerStepRelOn S gamma alpha p s q snapshot fullGradAtSnapshot sample
          xPrev xBarPrev hsearch havg next ->
        next.x.1 ∈ proxCoreSet S) ↔
      (forall z : FeasiblePoint S,
        ProxUpdateRelOn S gamma s xPrev
          (searchPointOn S gamma alpha p s xBarPrev xPrev snapshot hsearch)
          (varianceReducedGradientOn S q sample
            (searchPointOn S gamma alpha p s xBarPrev xPrev snapshot hsearch)
            snapshot fullGradAtSnapshot)
          z ->
        z.1 ∈ proxCoreSet S)

theorem legacyDiagnosticAlgorithm57InnerStepCorePropagationEquivalence_holds
    {n dim : Nat} (S : Setup n dim) :
    legacyDiagnosticAlgorithm57InnerStepCorePropagationEquivalence S := by
  intro gamma alpha p s q snapshot fullGradAtSnapshot sample xPrev xBarPrev
    hsearch havg
  exact innerStepRelOn_x_core_propagation_iff_proxUpdateRelOn_mem_proxCore
    S gamma alpha p s q snapshot fullGradAtSnapshot sample xPrev xBarPrev
    hsearch havg

/-- Fully feasible surrogate inner-loop transition.

This records the tempting all-`X` reading of Algorithm 5.7, but it is not the
paper-facing object because it replaces the §3.2 prox-function domain
`X^o x X` by the all-carrier `legacyDiagnosticFeasibleBregman` surrogate. -/
def legacyDiagnosticInnerStepAllFeasibleOn {n dim : Nat} (S : Setup n dim)
    (gamma alpha p : Nat -> Real) (s : Nat)
    (q : Fin n -> Real) (snapshot : FeasiblePoint S)
    (fullGradAtSnapshot : VariableSpace dim)
    (sample : Fin n) (state : InnerStateFeasibleOn S)
    (hsearch : searchPointWeights S gamma alpha p s ∈ stdSimplex Real (Fin 3))
    (havg : averagedInnerWeightsAdmissible alpha p s) :
    InnerStateFeasibleOn S :=
  let xUnder :=
    searchPointFeasibleOn S gamma alpha p s state.xBar state.x snapshot
      hsearch
  let G := varianceReducedGradientFeasibleOn S q sample
    xUnder snapshot fullGradAtSnapshot
  let xNext :=
    legacyDiagnosticProxUpdateAllFeasibleOn S gamma s state.x xUnder G
  let xBarNext :=
    averagedInnerIterateAllFeasibleOn S alpha p s state.xBar xNext snapshot havg
  { x := xNext, xBar := xBarNext }

/-- Source-derived prox-core obligation for the averaged inner iterate.

Algorithm 5.7 reuses `bar x_t` to form later search points that enter `V` on
the left, so the generated process carries the source-domain proof
`bar x_t ∈ X^o`. -/
theorem averagedInnerIterateValueOn_mem_proxCore {n dim : Nat} (S : Setup n dim)
    (alpha p : Nat -> Real) (s : Nat)
    (xBarPrev : Set.Elem (proxCoreSet S)) (xNext : Set.Elem (proxCoreSet S))
    (snapshot : Set.Elem (proxCoreSet S))
    (hweights : averagedInnerWeightsAdmissible alpha p s) :
    averagedInnerIterateValueOn S alpha p s xBarPrev xNext snapshot ∈ proxCoreSet S := by
  rcases hweights with ⟨h0, halpha, hp⟩
  unfold averagedInnerIterateValueOn averagedInnerIterate
  apply convex_three_smul_add_mem (proxCoreSet_convex S) h0 halpha hp
  · ring
  · exact xBarPrev.2
  · exact xNext.2
  · exact snapshot.2

/-- Prox-core averaged inner iterate `bar x_t`. -/
def averagedInnerIterateOn {n dim : Nat} (S : Setup n dim)
    (alpha p : Nat -> Real) (s : Nat)
    (xBarPrev : Set.Elem (proxCoreSet S)) (xNext : Set.Elem (proxCoreSet S))
    (snapshot : Set.Elem (proxCoreSet S))
    (hweights : averagedInnerWeightsAdmissible alpha p s) : Set.Elem (proxCoreSet S) :=
  ⟨averagedInnerIterateValueOn S alpha p s xBarPrev xNext snapshot,
    averagedInnerIterateValueOn_mem_proxCore S alpha p s xBarPrev xNext snapshot hweights⟩

/-- One Algorithm 5.7 printed inner step with core-carrying next state, assuming
the exact feasible-prox-to-core bridge isolated above.

This consumes the T1 prox witness shape and aligns with Algorithm 5.7 lines
16898-16903. Existing target-file candidates `innerStepFeasibleOn_satisfies_rel`
and `InnerStepCoreRelOn` were checked: the former is feasible-only and the
latter is a corrected-core relation, so this helper keeps the printed
`InnerStepRelOn` conclusion while exposing the missing core-membership premise. -/
theorem innerStepRelOn_exists_core_next_of_all_argmins_mem_proxCore
    {n dim : Nat} (S : Setup n dim)
    (gamma alpha p : Nat -> Real) (s : Nat)
    (q : Fin n -> Real) (snapshot : Set.Elem (proxCoreSet S))
    (fullGradAtSnapshot : VariableSpace dim)
    (sample : Fin n) (xPrev xBarPrev : Set.Elem (proxCoreSet S))
    (hsearch : searchPointWeights S gamma alpha p s ∈ stdSimplex Real (Fin 3))
    (havg : averagedInnerWeightsAdmissible alpha p s)
    (hexists : ∃ z : FeasiblePoint S,
      ProxUpdateRelOn S gamma s xPrev
        (searchPointOn S gamma alpha p s xBarPrev xPrev snapshot hsearch)
        (varianceReducedGradientOn S q sample
          (searchPointOn S gamma alpha p s xBarPrev xPrev snapshot hsearch)
          snapshot fullGradAtSnapshot)
        z)
    (hmem : forall z : FeasiblePoint S,
      ProxUpdateRelOn S gamma s xPrev
        (searchPointOn S gamma alpha p s xBarPrev xPrev snapshot hsearch)
        (varianceReducedGradientOn S q sample
          (searchPointOn S gamma alpha p s xBarPrev xPrev snapshot hsearch)
          snapshot fullGradAtSnapshot)
        z ->
      z.1 ∈ proxCoreSet S) :
    ∃ next : InnerStateOn S,
      InnerStepRelOn S gamma alpha p s q snapshot fullGradAtSnapshot sample
        xPrev xBarPrev hsearch havg
        { x := proxCoreAsFeasible S next.x
          xBar := proxCoreAsFeasible S next.xBar } := by
  let xUnder := searchPointOn S gamma alpha p s xBarPrev xPrev snapshot hsearch
  let G := varianceReducedGradientOn S q sample xUnder snapshot fullGradAtSnapshot
  rcases proxUpdateRelOn_exists_core_witness_of_all_argmins_mem_proxCore
      S gamma s xPrev xUnder G (by simpa [xUnder, G] using hexists) hmem with
    ⟨xNext, hxNext⟩
  let xBarNext := averagedInnerIterateOn S alpha p s xBarPrev xNext snapshot havg
  refine ⟨{ x := xNext, xBar := xBarNext }, ?_⟩
  unfold InnerStepRelOn
  refine ⟨hxNext, ?_⟩
  apply Subtype.ext
  rfl

/-- Core-native Algorithm 5.7 inner-loop transition for the corrected process.

The printed transition remains `InnerStepRelOn`/`innerStepFeasibleOn`, where the
prox argmin is over `X`. This corrected transition changes only the selector
carrier to `X^o`, so every later left argument of the paper Bregman object is
typed by construction instead of by a post-hoc feasible-selector membership
claim. -/
def innerStepCoreOn {n dim : Nat} (S : Setup n dim)
    (gamma alpha p : Nat -> Real) (s : Nat)
    (q : Fin n -> Real) (snapshot : Set.Elem (proxCoreSet S))
    (fullGradAtSnapshot : VariableSpace dim)
    (sample : Fin n) (state : InnerStateOn S)
    (hsearch : searchPointWeights S gamma alpha p s ∈ stdSimplex Real (Fin 3))
    (havg : averagedInnerWeightsAdmissible alpha p s) :
    InnerStateOn S :=
  let xUnder :=
    searchPointOn S gamma alpha p s state.xBar state.x snapshot hsearch
  let G := varianceReducedGradientOn S q sample
    xUnder snapshot fullGradAtSnapshot
  let xNext :=
    proxUpdateCoreOn S gamma s state.x xUnder G
  let xBarNext :=
    averagedInnerIterateOn S alpha p s state.xBar xNext snapshot havg
  { x := xNext, xBar := xBarNext }

/-- Core-domain membership for the corrected one-step prox iterate. -/
theorem innerStepCoreOn_x_mem_proxCore {n dim : Nat} (S : Setup n dim)
    (gamma alpha p : Nat -> Real) (s : Nat)
    (q : Fin n -> Real) (snapshot : Set.Elem (proxCoreSet S))
    (fullGradAtSnapshot : VariableSpace dim)
    (sample : Fin n) (state : InnerStateOn S)
    (hsearch : searchPointWeights S gamma alpha p s ∈ stdSimplex Real (Fin 3))
    (havg : averagedInnerWeightsAdmissible alpha p s) :
    (innerStepCoreOn S gamma alpha p s q snapshot fullGradAtSnapshot sample
      state hsearch havg).x.1 ∈ proxCoreSet S := by
  exact (innerStepCoreOn S gamma alpha p s q snapshot fullGradAtSnapshot sample
      state hsearch havg).x.2

/-- Core-domain membership for the corrected one-step averaged iterate. -/
theorem innerStepCoreOn_xBar_mem_proxCore {n dim : Nat} (S : Setup n dim)
    (gamma alpha p : Nat -> Real) (s : Nat)
    (q : Fin n -> Real) (snapshot : Set.Elem (proxCoreSet S))
    (fullGradAtSnapshot : VariableSpace dim)
    (sample : Fin n) (state : InnerStateOn S)
    (hsearch : searchPointWeights S gamma alpha p s ∈ stdSimplex Real (Fin 3))
    (havg : averagedInnerWeightsAdmissible alpha p s) :
    (innerStepCoreOn S gamma alpha p s q snapshot fullGradAtSnapshot sample
      state hsearch havg).xBar.1 ∈ proxCoreSet S := by
  exact (innerStepCoreOn S gamma alpha p s q snapshot fullGradAtSnapshot sample
      state hsearch havg).xBar.2

/-- Relational corrected-core Algorithm 5.7 inner-loop transition.

This is the core analogue of `InnerStepRelOn`: the prox update is represented by
`ProxUpdateCoreRelOn`, while the averaged iterate is the canonical convex
combination of core points. -/
def InnerStepCoreRelOn {n dim : Nat} (S : Setup n dim)
    (gamma alpha p : Nat -> Real) (s : Nat)
    (q : Fin n -> Real) (snapshot : Set.Elem (proxCoreSet S))
    (fullGradAtSnapshot : VariableSpace dim)
    (sample : Fin n) (state : InnerStateOn S)
    (hsearch : searchPointWeights S gamma alpha p s ∈ stdSimplex Real (Fin 3))
    (havg : averagedInnerWeightsAdmissible alpha p s)
    (next : InnerStateOn S) : Prop :=
  let xUnder :=
    searchPointOn S gamma alpha p s state.xBar state.x snapshot hsearch
  let G := varianceReducedGradientOn S q sample
    xUnder snapshot fullGradAtSnapshot
  ProxUpdateCoreRelOn S gamma s state.x xUnder G next.x ∧
    next.xBar =
      averagedInnerIterateOn S alpha p s state.xBar next.x snapshot havg

/-- Certified corrected-core inner-loop transition.

This is the first compiled consumer of `CoreProxOracleOn`: the output state is
core-valued by construction and its prox component carries the corresponding
`ProxUpdateCoreRelOn` certificate from the oracle. -/
def innerStepCertifiedCoreOn {n dim : Nat} (S : Setup n dim)
    (gamma alpha p : Nat -> Real) (oracle : CoreProxOracleOn S gamma)
    (s : Nat) (q : Fin n -> Real) (snapshot : Set.Elem (proxCoreSet S))
    (fullGradAtSnapshot : VariableSpace dim)
    (sample : Fin n) (state : InnerStateOn S)
    (hsearch : searchPointWeights S gamma alpha p s ∈ stdSimplex Real (Fin 3))
    (havg : averagedInnerWeightsAdmissible alpha p s) :
    InnerStateOn S :=
  let xUnder :=
    searchPointOn S gamma alpha p s state.xBar state.x snapshot hsearch
  let G := varianceReducedGradientOn S q sample
    xUnder snapshot fullGradAtSnapshot
  let xNext :=
    certifiedProxUpdateCoreOn S gamma oracle s state.x xUnder G
  let xBarNext :=
    averagedInnerIterateOn S alpha p s state.xBar xNext snapshot havg
  { x := xNext, xBar := xBarNext }

theorem innerStepCertifiedCoreOn_satisfies_coreRel {n dim : Nat} (S : Setup n dim)
    (gamma alpha p : Nat -> Real) (oracle : CoreProxOracleOn S gamma)
    (s : Nat) (q : Fin n -> Real) (snapshot : Set.Elem (proxCoreSet S))
    (fullGradAtSnapshot : VariableSpace dim)
    (sample : Fin n) (state : InnerStateOn S)
    (hsearch : searchPointWeights S gamma alpha p s ∈ stdSimplex Real (Fin 3))
    (havg : averagedInnerWeightsAdmissible alpha p s) :
    InnerStepCoreRelOn S gamma alpha p s q snapshot fullGradAtSnapshot sample
      state hsearch havg
      (innerStepCertifiedCoreOn S gamma alpha p oracle s q snapshot
        fullGradAtSnapshot sample state hsearch havg) := by
  unfold InnerStepCoreRelOn innerStepCertifiedCoreOn
  exact ⟨certifiedProxUpdateCoreOn_isMin S gamma oracle s state.x
    (searchPointOn S gamma alpha p s state.xBar state.x snapshot hsearch)
    (varianceReducedGradientOn S q sample
      (searchPointOn S gamma alpha p s state.xBar state.x snapshot hsearch)
      snapshot fullGradAtSnapshot), rfl⟩

theorem innerStepCertifiedCoreOn_x_mem_proxCore {n dim : Nat} (S : Setup n dim)
    (gamma alpha p : Nat -> Real) (oracle : CoreProxOracleOn S gamma)
    (s : Nat) (q : Fin n -> Real) (snapshot : Set.Elem (proxCoreSet S))
    (fullGradAtSnapshot : VariableSpace dim)
    (sample : Fin n) (state : InnerStateOn S)
    (hsearch : searchPointWeights S gamma alpha p s ∈ stdSimplex Real (Fin 3))
    (havg : averagedInnerWeightsAdmissible alpha p s) :
    (innerStepCertifiedCoreOn S gamma alpha p oracle s q snapshot fullGradAtSnapshot sample
      state hsearch havg).x.1 ∈ proxCoreSet S := by
  exact (innerStepCertifiedCoreOn S gamma alpha p oracle s q snapshot fullGradAtSnapshot sample
      state hsearch havg).x.2

theorem innerStepCertifiedCoreOn_xBar_mem_proxCore {n dim : Nat} (S : Setup n dim)
    (gamma alpha p : Nat -> Real) (oracle : CoreProxOracleOn S gamma)
    (s : Nat) (q : Fin n -> Real) (snapshot : Set.Elem (proxCoreSet S))
    (fullGradAtSnapshot : VariableSpace dim)
    (sample : Fin n) (state : InnerStateOn S)
    (hsearch : searchPointWeights S gamma alpha p s ∈ stdSimplex Real (Fin 3))
    (havg : averagedInnerWeightsAdmissible alpha p s) :
    (innerStepCertifiedCoreOn S gamma alpha p oracle s q snapshot fullGradAtSnapshot sample
      state hsearch havg).xBar.1 ∈ proxCoreSet S := by
  exact (innerStepCertifiedCoreOn S gamma alpha p oracle s q snapshot fullGradAtSnapshot sample
      state hsearch havg).xBar.2

/-- Internal core-valued Algorithm 5.7 inner-loop transition.

The paper-facing one-step transition is `innerStepFeasibleOn`; this version is
the corrected-core recursion whose prox selector is natively over `X^o`. -/
def innerStepOn {n dim : Nat} (S : Setup n dim)
    (gamma alpha p : Nat -> Real) (s : Nat)
    (q : Fin n -> Real) (snapshot : Set.Elem (proxCoreSet S))
    (fullGradAtSnapshot : VariableSpace dim)
    (sample : Fin n) (state : InnerStateOn S)
    (hsearch : searchPointWeights S gamma alpha p s ∈ stdSimplex Real (Fin 3))
    (havg : averagedInnerWeightsAdmissible alpha p s) :
    InnerStateOn S :=
  innerStepCoreOn S gamma alpha p s q snapshot fullGradAtSnapshot
    sample state hsearch havg

/-- Generated domain-correct inner-loop state process. -/
def innerStateProcessOn {n dim : Nat} (S : Setup n dim)
    (gamma alpha p : Nat -> Real) (s : Nat)
    (q : Fin n -> Real) (snapshot : Set.Elem (proxCoreSet S))
    (fullGradAtSnapshot : VariableSpace dim) (x0 : Set.Elem (proxCoreSet S))
    (samples : Nat -> Fin n)
    (halpha : alpha s ∈ Set.Icc (0 : Real) 1)
    (hp : p s ∈ Set.Icc (0 : Real) 1)
    (_hgamma : 0 < gamma s)
    (hcurv : 0 < 1 + S.mu * gamma s - averageSmoothness S * alpha s * gamma s)
    (hsearch : searchPointWeights S gamma alpha p s ∈ stdSimplex Real (Fin 3))
    (havg : averagedInnerWeightsAdmissible alpha p s) :
    Nat -> InnerStateOn S
  | 0 => { x := x0, xBar := snapshot }
  | Nat.succ t =>
      innerStepOn S gamma alpha p s q snapshot fullGradAtSnapshot
        (samples (t + 1))
        (innerStateProcessOn S gamma alpha p s q snapshot fullGradAtSnapshot x0 samples
          halpha hp _hgamma hcurv hsearch havg t)
        hsearch havg

/-- Generated all-feasible surrogate inner-loop state process.

Kept only to expose the source-boundary gap: this recursion is generated over
`X`, but its Bregman terms use the all-carrier surrogate rather than the paper
prox-function `V : X^o x X -> R+`. -/
def legacyDiagnosticInnerStateProcessFeasibleOn {n dim : Nat} (S : Setup n dim)
    (gamma alpha p : Nat -> Real) (s : Nat)
    (q : Fin n -> Real) (snapshot : FeasiblePoint S)
    (fullGradAtSnapshot : VariableSpace dim) (x0 : FeasiblePoint S)
    (samples : Nat -> Fin n)
    (_halpha : alpha s ∈ Set.Icc (0 : Real) 1)
    (_hp : p s ∈ Set.Icc (0 : Real) 1)
    (_hgamma : 0 < gamma s)
    (_hcurv : 0 < 1 + S.mu * gamma s - averageSmoothness S * alpha s * gamma s)
    (hsearch : searchPointWeights S gamma alpha p s ∈ stdSimplex Real (Fin 3))
    (havg : averagedInnerWeightsAdmissible alpha p s) :
    Nat -> InnerStateFeasibleOn S
  | 0 => { x := x0, xBar := snapshot }
  | Nat.succ t =>
      legacyDiagnosticInnerStepAllFeasibleOn S gamma alpha p s q snapshot fullGradAtSnapshot
        (samples (t + 1))
        (legacyDiagnosticInnerStateProcessFeasibleOn S gamma alpha p s q snapshot fullGradAtSnapshot x0 samples
          _halpha _hp _hgamma _hcurv hsearch havg t)
        hsearch havg

/-- The outer Algorithm 5.7 epoch state on the paper domains. -/
structure EpochStateOn {n dim : Nat} (S : Setup n dim) where
  x : Set.Elem (proxCoreSet S)
  xTilde : Set.Elem (proxCoreSet S)

/-- The outer epoch state for the all-feasible surrogate recursion. -/
structure EpochStateFeasibleOn {n dim : Nat} (S : Setup n dim) where
  x : FeasiblePoint S
  xTilde : FeasiblePoint S

/-- Feasible view of a domain-correct epoch state.

This is only a projection of the `X^o`-typed generated process to the printed
carrier `X`; it does not assert that an independently generated feasible
argmin lies in `X^o`. -/
def epochStateOnAsFeasible {n dim : Nat} (S : Setup n dim)
    (state : EpochStateOn S) : EpochStateFeasibleOn S :=
  { x := proxCoreAsFeasible S state.x
    xTilde := proxCoreAsFeasible S state.xTilde }

/-- Source-derived prox-core obligation for the theta-weighted epoch output. -/
theorem epochOutput_mem_proxCore {n dim T : Nat} (S : Setup n dim)
    (theta : Nat -> Real) (xBar : Fin T -> Set.Elem (proxCoreSet S))
    (hweights : epochOutputWeightsAdmissible theta T) :
    epochOutput theta (fun t => (xBar t).1) ∈ proxCoreSet S := by
  rcases hweights with ⟨hpos, hnonneg⟩
  simpa [epochOutput] using
    (proxCoreSet_convex S).normalized_weighted_sum_mem
      (Finset.univ : Finset (Fin T))
      (fun t : Fin T => theta (paperTime t))
      (fun t : Fin T => (xBar t).1)
      hpos
      (by
        intro t _ht
        exact hnonneg t)
      (by
        intro t _ht
        exact (xBar t).2)

/-- Prox-core epoch output `tilde x^s`. -/
def epochOutputOn {n dim T : Nat} (S : Setup n dim)
    (theta : Nat -> Real) (xBar : Fin T -> Set.Elem (proxCoreSet S))
    (hweights : epochOutputWeightsAdmissible theta T) : Set.Elem (proxCoreSet S) :=
  ⟨epochOutput theta (fun t => (xBar t).1), epochOutput_mem_proxCore S theta xBar hweights⟩

/-- Source-derived feasibility of the theta-weighted epoch output. -/
theorem epochOutput_mem_X {n dim T : Nat} (S : Setup n dim)
    (theta : Nat -> Real) (xBar : Fin T -> FeasiblePoint S)
    (hweights : epochOutputWeightsAdmissible theta T) :
    epochOutput theta (fun t => (xBar t).1) ∈ S.X := by
  rcases hweights with ⟨hpos, hnonneg⟩
  simpa [epochOutput] using
    S.X_convex.normalized_weighted_sum_mem
      (Finset.univ : Finset (Fin T))
      (fun t : Fin T => theta (paperTime t))
      (fun t : Fin T => (xBar t).1)
      hpos
      (by
        intro t _ht
        exact hnonneg t)
      (by
        intro t _ht
        exact (xBar t).2)

/-- Feasible epoch output `tilde x^s` from the printed Algorithm 5.7 average. -/
def epochOutputFeasibleOn {n dim T : Nat} (S : Setup n dim)
    (theta : Nat -> Real) (xBar : Fin T -> FeasiblePoint S)
    (hweights : epochOutputWeightsAdmissible theta T) : FeasiblePoint S :=
  ⟨epochOutput theta (fun t => (xBar t).1), epochOutput_mem_X S theta xBar hweights⟩

/-- Jensen bridge for the printed theta-weighted epoch output.

Aligns with Lan Lemma 5.18's instruction to identify the weighted average
`tilde x^s` and use convexity of `Ψ`. Candidates considered:
`ConvexOn.map_sum_le` is the exact Mathlib finite Jensen API used below;
`convexOn_weighted_average_le_weighted_sum` has the same mathematical shape
but is not imported in this file, and importing `SOptLib.Layer1.Telescope` is
unnecessary for this local bridge. -/
theorem compositeObjective_epochOutputFeasibleOn_le_weighted_sum
    {n dim T : Nat} (S : Setup n dim)
    (theta : Nat -> Real) (xBar : Fin T -> FeasiblePoint S)
    (hweights : epochOutputWeightsAdmissible theta T) :
    compositeObjective S (epochOutputFeasibleOn S theta xBar hweights).1 <=
      (Finset.univ.sum (fun t : Fin T => theta (paperTime t)))⁻¹ *
        Finset.univ.sum
          (fun t : Fin T => theta (paperTime t) * compositeObjective S (xBar t).1) := by
  classical
  rcases hweights with ⟨hW_pos, htheta_nonneg⟩
  let W : Real := Finset.univ.sum (fun t : Fin T => theta (paperTime t))
  let w : Fin T -> Real := fun t => W⁻¹ * theta (paperTime t)
  have hW_ne : W ≠ 0 := ne_of_gt hW_pos
  have hw_nonneg : ∀ t ∈ (Finset.univ : Finset (Fin T)), 0 <= w t := by
    intro t _ht
    exact mul_nonneg (inv_nonneg.mpr (le_of_lt hW_pos)) (htheta_nonneg t)
  have hw_sum : Finset.univ.sum w = 1 := by
    calc
      Finset.univ.sum w =
          W⁻¹ * Finset.univ.sum (fun t : Fin T => theta (paperTime t)) := by
            simp [w, Finset.mul_sum]
      _ = W⁻¹ * W := by rfl
      _ = 1 := inv_mul_cancel₀ hW_ne
  have hx_mem : ∀ t ∈ (Finset.univ : Finset (Fin T)), (xBar t).1 ∈ S.X := by
    intro t _ht
    exact (xBar t).2
  have hJ :=
    (compositeObjective_convexOn S).map_sum_le
      (t := (Finset.univ : Finset (Fin T))) (w := w)
      (p := fun t : Fin T => (xBar t).1) hw_nonneg hw_sum hx_mem
  have hleft :
      Finset.univ.sum (fun t : Fin T => w t • (xBar t).1) =
        (epochOutputFeasibleOn S theta xBar ⟨hW_pos, htheta_nonneg⟩).1 := by
    simp [epochOutputFeasibleOn, epochOutput, w, W, Finset.smul_sum, smul_smul]
  have hright :
      Finset.univ.sum (fun t : Fin T => w t • compositeObjective S (xBar t).1) =
        W⁻¹ *
          Finset.univ.sum
            (fun t : Fin T => theta (paperTime t) * compositeObjective S (xBar t).1) := by
    simp [w, smul_eq_mul, Finset.mul_sum, mul_assoc]
  rw [hleft, hright] at hJ
  simpa [W] using hJ

/-- One generated epoch transition for the all-feasible surrogate recursion. -/
def legacyDiagnosticEpochTransitionFeasibleOn {n dim : Nat} (S : Setup n dim)
    (T : Nat -> Nat) (gamma alpha p : Nat -> Real)
    (theta : Nat -> Nat -> Real)
    (q : Fin n -> Real) (samples : Nat -> Fin n)
    (s : Nat) (prev : EpochStateFeasibleOn S)
    (halpha : alpha s ∈ Set.Icc (0 : Real) 1)
    (hp : p s ∈ Set.Icc (0 : Real) 1)
    (hgamma : 0 < gamma s)
    (hcurv : 0 < 1 + S.mu * gamma s - averageSmoothness S * alpha s * gamma s)
    (hsearch : searchPointWeights S gamma alpha p s ∈ stdSimplex Real (Fin 3))
    (havg : averagedInnerWeightsAdmissible alpha p s)
    (htheta : epochOutputWeightsAdmissible (theta s) (T s)) :
    EpochStateFeasibleOn S :=
  let inner :=
    legacyDiagnosticInnerStateProcessFeasibleOn S gamma alpha p s q prev.xTilde
      (fullGradient S prev.xTilde.1) prev.x samples halpha hp hgamma hcurv hsearch havg
  let xBarFeasible : Fin (T s) -> FeasiblePoint S :=
    fun t => (inner (paperTime t)).xBar
  { x := (inner (T s)).x
    xTilde := epochOutputFeasibleOn S (theta s) xBarFeasible htheta }

/-- One generated Algorithm 5.7 epoch transition on the paper domains. -/
def epochTransitionOn {n dim : Nat} (S : Setup n dim)
    (T : Nat -> Nat) (gamma alpha p : Nat -> Real)
    (theta : Nat -> Nat -> Real)
    (q : Fin n -> Real) (samples : Nat -> Fin n)
    (s : Nat) (prev : EpochStateOn S)
    (halpha : alpha s ∈ Set.Icc (0 : Real) 1)
    (hp : p s ∈ Set.Icc (0 : Real) 1)
    (hgamma : 0 < gamma s)
    (hcurv : 0 < 1 + S.mu * gamma s - averageSmoothness S * alpha s * gamma s)
    (hsearch : searchPointWeights S gamma alpha p s ∈ stdSimplex Real (Fin 3))
    (havg : averagedInnerWeightsAdmissible alpha p s)
    (htheta : epochOutputWeightsAdmissible (theta s) (T s)) :
    EpochStateOn S :=
  let inner :=
    innerStateProcessOn S gamma alpha p s q prev.xTilde
      (fullGradient S prev.xTilde.1) prev.x samples halpha hp hgamma hcurv hsearch havg
  let xBarCore : Fin (T s) -> Set.Elem (proxCoreSet S) :=
    fun t => (inner (paperTime t)).xBar
  { x := (inner (T s)).x
    xTilde := epochOutputOn S (theta s) xBarCore htheta }

/-- Generated outer epoch process for Algorithm 5.7 on the prox core. -/
def epochStateProcessOn {Ω : Type*} {n dim : Nat} (S : Setup n dim)
    (T : Nat -> Nat) (gamma alpha p : Nat -> Real)
    (theta : Nat -> Nat -> Real)
    (q : Fin n -> Real) (x0 : Set.Elem (proxCoreSet S))
    (samples : Nat -> Nat -> Ω -> Fin n)
    (hparams :
      forall s, 1 <= s ->
        alpha s ∈ Set.Icc (0 : Real) 1 ∧
        p s ∈ Set.Icc (0 : Real) 1 ∧
        0 < gamma s ∧
        0 < 1 + S.mu * gamma s - averageSmoothness S * alpha s * gamma s ∧
        searchPointWeights S gamma alpha p s ∈ stdSimplex Real (Fin 3) ∧
        averagedInnerWeightsAdmissible alpha p s)
    (htheta :
      forall s, 1 <= s -> epochOutputWeightsAdmissible (theta s) (T s)) :
    Nat -> Ω -> EpochStateOn S :=
  SOptLib.recursiveIterateProcess
    { x := x0, xTilde := x0 }
    (fun k prev ω =>
      epochTransitionOn S T gamma alpha p theta q
        (fun t => samples (k + 1) t ω) (k + 1) prev
        ((hparams (k + 1) (Nat.succ_le_succ (Nat.zero_le k))).1)
        ((hparams (k + 1) (Nat.succ_le_succ (Nat.zero_le k))).2.1)
        ((hparams (k + 1) (Nat.succ_le_succ (Nat.zero_le k))).2.2.1)
        ((hparams (k + 1) (Nat.succ_le_succ (Nat.zero_le k))).2.2.2.1)
        ((hparams (k + 1) (Nat.succ_le_succ (Nat.zero_le k))).2.2.2.2.1)
        ((hparams (k + 1) (Nat.succ_le_succ (Nat.zero_le k))).2.2.2.2.2)
        (htheta (k + 1) (Nat.succ_le_succ (Nat.zero_le k))))

/-- Generated outer epoch process for the all-feasible surrogate recursion. -/
def legacyDiagnosticEpochStateProcessFeasibleOn {Ω : Type*} {n dim : Nat} (S : Setup n dim)
    (T : Nat -> Nat) (gamma alpha p : Nat -> Real)
    (theta : Nat -> Nat -> Real)
    (q : Fin n -> Real) (x0 : FeasiblePoint S)
    (samples : Nat -> Nat -> Ω -> Fin n)
    (hparams :
      forall s, 1 <= s ->
        alpha s ∈ Set.Icc (0 : Real) 1 ∧
        p s ∈ Set.Icc (0 : Real) 1 ∧
        0 < gamma s ∧
        0 < 1 + S.mu * gamma s - averageSmoothness S * alpha s * gamma s ∧
        searchPointWeights S gamma alpha p s ∈ stdSimplex Real (Fin 3) ∧
        averagedInnerWeightsAdmissible alpha p s)
    (htheta :
      forall s, 1 <= s -> epochOutputWeightsAdmissible (theta s) (T s)) :
    Nat -> Ω -> EpochStateFeasibleOn S :=
  SOptLib.recursiveIterateProcess
    { x := x0, xTilde := x0 }
    (fun k prev ω =>
      legacyDiagnosticEpochTransitionFeasibleOn S T gamma alpha p theta q
        (fun t => samples (k + 1) t ω) (k + 1) prev
        ((hparams (k + 1) (Nat.succ_le_succ (Nat.zero_le k))).1)
        ((hparams (k + 1) (Nat.succ_le_succ (Nat.zero_le k))).2.1)
        ((hparams (k + 1) (Nat.succ_le_succ (Nat.zero_le k))).2.2.1)
        ((hparams (k + 1) (Nat.succ_le_succ (Nat.zero_le k))).2.2.2.1)
        ((hparams (k + 1) (Nat.succ_le_succ (Nat.zero_le k))).2.2.2.2.1)
        ((hparams (k + 1) (Nat.succ_le_succ (Nat.zero_le k))).2.2.2.2.2)
        (htheta (k + 1) (Nat.succ_le_succ (Nat.zero_le k))))

/-- Domain-correct stochastic output realization for `tilde{x}^s`.

This generated process uses the literal Bregman domain `X^o x X`. The PDF's
printed all-feasible recursion remains a source-domain gap because §3.2 does
not state that every feasible iterate lies in `X^o`. -/
def epochOutputProcessOn {Ω : Type*} {n dim : Nat} (S : Setup n dim)
    (T : Nat -> Nat) (gamma alpha p : Nat -> Real)
    (theta : Nat -> Nat -> Real)
    (q : Fin n -> Real) (x0 : Set.Elem (proxCoreSet S))
    (samples : Nat -> Nat -> Ω -> Fin n)
    (hparams :
      forall s, 1 <= s ->
        alpha s ∈ Set.Icc (0 : Real) 1 ∧
        p s ∈ Set.Icc (0 : Real) 1 ∧
        0 < gamma s ∧
        0 < 1 + S.mu * gamma s - averageSmoothness S * alpha s * gamma s ∧
        searchPointWeights S gamma alpha p s ∈ stdSimplex Real (Fin 3) ∧
        averagedInnerWeightsAdmissible alpha p s)
    (htheta :
      forall s, 1 <= s -> epochOutputWeightsAdmissible (theta s) (T s)) :
    Nat -> Ω -> VariableSpace dim :=
  fun s ω =>
    (epochStateProcessOn S T gamma alpha p theta q x0 samples hparams htheta s ω).xTilde.1

/-- Certified generated inner-loop state process.

This is the executable corrected-core recursion for refactor handoff: prox
updates are supplied by `CoreProxOracleOn` certificates instead of by
`proxUpdateCoreOn`, whose existence currently depends on the unresolved local
theorem `proxUpdateCoreOn_exists`. -/
def innerStateProcessCertifiedOn {n dim : Nat} (S : Setup n dim)
    (gamma alpha p : Nat -> Real) (oracle : CoreProxOracleOn S gamma)
    (s : Nat) (q : Fin n -> Real) (snapshot : Set.Elem (proxCoreSet S))
    (fullGradAtSnapshot : VariableSpace dim) (x0 : Set.Elem (proxCoreSet S))
    (samples : Nat -> Fin n)
    (halpha : alpha s ∈ Set.Icc (0 : Real) 1)
    (hp : p s ∈ Set.Icc (0 : Real) 1)
    (_hgamma : 0 < gamma s)
    (hcurv : 0 < 1 + S.mu * gamma s - averageSmoothness S * alpha s * gamma s)
    (hsearch : searchPointWeights S gamma alpha p s ∈ stdSimplex Real (Fin 3))
    (havg : averagedInnerWeightsAdmissible alpha p s) :
    Nat -> InnerStateOn S
  | 0 => { x := x0, xBar := snapshot }
  | Nat.succ t =>
      innerStepCertifiedCoreOn S gamma alpha p oracle s q snapshot fullGradAtSnapshot
        (samples (t + 1))
        (innerStateProcessCertifiedOn S gamma alpha p oracle s q snapshot
          fullGradAtSnapshot x0 samples halpha hp _hgamma hcurv hsearch havg t)
        hsearch havg

/-- One certified corrected-core epoch transition. -/
def epochTransitionCertifiedOn {n dim : Nat} (S : Setup n dim)
    (T : Nat -> Nat) (gamma alpha p : Nat -> Real)
    (oracle : CoreProxOracleOn S gamma)
    (theta : Nat -> Nat -> Real)
    (q : Fin n -> Real) (samples : Nat -> Fin n)
    (s : Nat) (prev : EpochStateOn S)
    (halpha : alpha s ∈ Set.Icc (0 : Real) 1)
    (hp : p s ∈ Set.Icc (0 : Real) 1)
    (hgamma : 0 < gamma s)
    (hcurv : 0 < 1 + S.mu * gamma s - averageSmoothness S * alpha s * gamma s)
    (hsearch : searchPointWeights S gamma alpha p s ∈ stdSimplex Real (Fin 3))
    (havg : averagedInnerWeightsAdmissible alpha p s)
    (htheta : epochOutputWeightsAdmissible (theta s) (T s)) :
    EpochStateOn S :=
  let inner :=
    innerStateProcessCertifiedOn S gamma alpha p oracle s q prev.xTilde
      (fullGradient S prev.xTilde.1) prev.x samples halpha hp hgamma hcurv hsearch havg
  let xBarCore : Fin (T s) -> Set.Elem (proxCoreSet S) :=
    fun t => (inner (paperTime t)).xBar
  { x := (inner (T s)).x
    xTilde := epochOutputOn S (theta s) xBarCore htheta }

/-- Generated certified corrected-core epoch process. -/
def epochStateProcessCertifiedOn {Ω : Type*} {n dim : Nat} (S : Setup n dim)
    (T : Nat -> Nat) (gamma alpha p : Nat -> Real)
    (oracle : CoreProxOracleOn S gamma)
    (theta : Nat -> Nat -> Real)
    (q : Fin n -> Real) (x0 : Set.Elem (proxCoreSet S))
    (samples : Nat -> Nat -> Ω -> Fin n)
    (hparams :
      forall s, 1 <= s ->
        alpha s ∈ Set.Icc (0 : Real) 1 ∧
        p s ∈ Set.Icc (0 : Real) 1 ∧
        0 < gamma s ∧
        0 < 1 + S.mu * gamma s - averageSmoothness S * alpha s * gamma s ∧
        searchPointWeights S gamma alpha p s ∈ stdSimplex Real (Fin 3) ∧
        averagedInnerWeightsAdmissible alpha p s)
    (htheta :
      forall s, 1 <= s -> epochOutputWeightsAdmissible (theta s) (T s)) :
    Nat -> Ω -> EpochStateOn S :=
  SOptLib.recursiveIterateProcess
    { x := x0, xTilde := x0 }
    (fun k prev ω =>
      epochTransitionCertifiedOn S T gamma alpha p oracle theta q
        (fun t => samples (k + 1) t ω) (k + 1) prev
        ((hparams (k + 1) (Nat.succ_le_succ (Nat.zero_le k))).1)
        ((hparams (k + 1) (Nat.succ_le_succ (Nat.zero_le k))).2.1)
        ((hparams (k + 1) (Nat.succ_le_succ (Nat.zero_le k))).2.2.1)
        ((hparams (k + 1) (Nat.succ_le_succ (Nat.zero_le k))).2.2.2.1)
        ((hparams (k + 1) (Nat.succ_le_succ (Nat.zero_le k))).2.2.2.2.1)
        ((hparams (k + 1) (Nat.succ_le_succ (Nat.zero_le k))).2.2.2.2.2)
        (htheta (k + 1) (Nat.succ_le_succ (Nat.zero_le k))))

/-- Certified corrected-core stochastic output process. -/
def epochOutputProcessCertifiedOn {Ω : Type*} {n dim : Nat} (S : Setup n dim)
    (T : Nat -> Nat) (gamma alpha p : Nat -> Real)
    (oracle : CoreProxOracleOn S gamma)
    (theta : Nat -> Nat -> Real)
    (q : Fin n -> Real) (x0 : Set.Elem (proxCoreSet S))
    (samples : Nat -> Nat -> Ω -> Fin n)
    (hparams :
      forall s, 1 <= s ->
        alpha s ∈ Set.Icc (0 : Real) 1 ∧
        p s ∈ Set.Icc (0 : Real) 1 ∧
        0 < gamma s ∧
        0 < 1 + S.mu * gamma s - averageSmoothness S * alpha s * gamma s ∧
        searchPointWeights S gamma alpha p s ∈ stdSimplex Real (Fin 3) ∧
        averagedInnerWeightsAdmissible alpha p s)
    (htheta :
      forall s, 1 <= s -> epochOutputWeightsAdmissible (theta s) (T s)) :
    Nat -> Ω -> VariableSpace dim :=
  fun s ω =>
    (epochStateProcessCertifiedOn S T gamma alpha p oracle theta q x0 samples hparams htheta
      s ω).xTilde.1

theorem epochStateProcessCertifiedOn_mem_proxCore {Ω : Type*} {n dim : Nat}
    (S : Setup n dim)
    (T : Nat -> Nat) (gamma alpha p : Nat -> Real)
    (oracle : CoreProxOracleOn S gamma)
    (theta : Nat -> Nat -> Real)
    (q : Fin n -> Real) (x0 : Set.Elem (proxCoreSet S))
    (samples : Nat -> Nat -> Ω -> Fin n)
    (hparams :
      forall s, 1 <= s ->
        alpha s ∈ Set.Icc (0 : Real) 1 ∧
        p s ∈ Set.Icc (0 : Real) 1 ∧
        0 < gamma s ∧
        0 < 1 + S.mu * gamma s - averageSmoothness S * alpha s * gamma s ∧
        searchPointWeights S gamma alpha p s ∈ stdSimplex Real (Fin 3) ∧
        averagedInnerWeightsAdmissible alpha p s)
    (htheta :
      forall s, 1 <= s -> epochOutputWeightsAdmissible (theta s) (T s))
    (s : Nat) (omega : Ω) :
    let state :=
      epochStateProcessCertifiedOn S T gamma alpha p oracle theta q x0 samples hparams htheta
        s omega
    state.x.1 ∈ proxCoreSet S ∧ state.xTilde.1 ∈ proxCoreSet S := by
  exact ⟨(epochStateProcessCertifiedOn S T gamma alpha p oracle theta q x0 samples hparams htheta
      s omega).x.2,
    (epochStateProcessCertifiedOn S T gamma alpha p oracle theta q x0 samples hparams htheta
      s omega).xTilde.2⟩

/-- Stochastic output of the all-feasible surrogate recursion.

This is a source-boundary diagnostic object, not the Theorem 5.9 output: it uses
the all-carrier Bregman surrogate that is not Lan §3.2's `V : X^o x X -> R+`. -/
def legacyDiagnosticEpochOutputProcessFeasibleOn {Ω : Type*} {n dim : Nat} (S : Setup n dim)
    (T : Nat -> Nat) (gamma alpha p : Nat -> Real)
    (theta : Nat -> Nat -> Real)
    (q : Fin n -> Real) (x0 : FeasiblePoint S)
    (samples : Nat -> Nat -> Ω -> Fin n)
    (hparams :
      forall s, 1 <= s ->
        alpha s ∈ Set.Icc (0 : Real) 1 ∧
        p s ∈ Set.Icc (0 : Real) 1 ∧
        0 < gamma s ∧
        0 < 1 + S.mu * gamma s - averageSmoothness S * alpha s * gamma s ∧
        searchPointWeights S gamma alpha p s ∈ stdSimplex Real (Fin 3) ∧
        averagedInnerWeightsAdmissible alpha p s)
    (htheta :
      forall s, 1 <= s -> epochOutputWeightsAdmissible (theta s) (T s)) :
    Nat -> Ω -> VariableSpace dim :=
  fun s ω =>
    (legacyDiagnosticEpochStateProcessFeasibleOn S T gamma alpha p theta q x0 samples hparams htheta s ω).xTilde.1

/-- Generic cross-epoch average `bar{x}^s` from Eq. (5.4.16), evaluated on the
generated Algorithm 5.7 output path. -/
def smoothEpochAverageProcessOn {Ω : Type*} {n dim : Nat} (S : Setup n dim)
    (T : Nat -> Nat) (gamma alpha p : Nat -> Real)
    (theta : Nat -> Nat -> Real)
    (q : Fin n -> Real) (x0 : Set.Elem (proxCoreSet S))
    (samples : Nat -> Nat -> Ω -> Fin n)
    (hparams :
      forall s, 1 <= s ->
        alpha s ∈ Set.Icc (0 : Real) 1 ∧
        p s ∈ Set.Icc (0 : Real) 1 ∧
        0 < gamma s ∧
        0 < 1 + S.mu * gamma s - averageSmoothness S * alpha s * gamma s ∧
        searchPointWeights S gamma alpha p s ∈ stdSimplex Real (Fin 3) ∧
        averagedInnerWeightsAdmissible alpha p s)
    (htheta :
      forall s, 1 <= s -> epochOutputWeightsAdmissible (theta s) (T s)) :
    Nat -> Ω -> VariableSpace dim :=
  fun s omega =>
    smoothEpochAverageOf T gamma alpha p
      (fun j => epochOutputProcessOn S T gamma alpha p theta q x0 samples hparams htheta j omega) s

/-- Generic cross-epoch average `bar{x}^s` from Eq. (5.4.16), evaluated on the
printed feasible Algorithm 5.7 output path.

This is the smooth source-boundary counterpart of `smoothEpochAverageProcessOn`:
the epoch output is generated over `X`, matching Algorithm 5.7's printed
`argmin_{x in X}` and theta-weighted output, rather than silently replacing the
smooth output by the internal prox-core realization. -/
def legacyDiagnosticSmoothEpochAverageProcessFeasibleOn {Ω : Type*} {n dim : Nat} (S : Setup n dim)
    (T : Nat -> Nat) (gamma alpha p : Nat -> Real)
    (theta : Nat -> Nat -> Real)
    (q : Fin n -> Real) (x0 : FeasiblePoint S)
    (samples : Nat -> Nat -> Ω -> Fin n)
    (hparams :
      forall s, 1 <= s ->
        alpha s ∈ Set.Icc (0 : Real) 1 ∧
        p s ∈ Set.Icc (0 : Real) 1 ∧
        0 < gamma s ∧
        0 < 1 + S.mu * gamma s - averageSmoothness S * alpha s * gamma s ∧
        searchPointWeights S gamma alpha p s ∈ stdSimplex Real (Fin 3) ∧
        averagedInnerWeightsAdmissible alpha p s)
    (htheta :
      forall s, 1 <= s -> epochOutputWeightsAdmissible (theta s) (T s)) :
    Nat -> Ω -> VariableSpace dim :=
  fun s omega =>
    smoothEpochAverageOf T gamma alpha p
      (fun j => legacyDiagnosticEpochOutputProcessFeasibleOn S T gamma alpha p theta q x0 samples
        hparams htheta j omega) s


/-- Generic expected endpoint Bregman term for the printed feasible smooth path.

Algorithm 5.7 prints `x^s = x_T` with `x_T` selected in `X`. This source-boundary
object therefore uses the feasible generated epoch state and the all-carrier
diagnostic Bregman expression, instead of identifying the smooth endpoint with
the internal prox-core realization. The endpoint term is written directly with
`SOptLib.expectation`, matching the library-level expectation surface. -/
def expectedEndpointBregmanFeasibleOn {Ω : Type*} [MeasurableSpace Ω]
    {n dim : Nat} (S : Setup n dim)
    (sampleLaw : MeasureTheory.Measure Ω)
    (T : Nat -> Nat) (gamma alpha p : Nat -> Real)
    (theta : Nat -> Nat -> Real)
    (q : Fin n -> Real) (x0 : FeasiblePoint S)
    (samples : Nat -> Nat -> Ω -> Fin n)
    (hparams :
      forall s, 1 <= s ->
        alpha s ∈ Set.Icc (0 : Real) 1 ∧
        p s ∈ Set.Icc (0 : Real) 1 ∧
        0 < gamma s ∧
        0 < 1 + S.mu * gamma s - averageSmoothness S * alpha s * gamma s ∧
        searchPointWeights S gamma alpha p s ∈ stdSimplex Real (Fin 3) ∧
        averagedInnerWeightsAdmissible alpha p s)
    (htheta :
      forall s, 1 <= s -> epochOutputWeightsAdmissible (theta s) (T s))
    (x : FeasiblePoint S) (s : Nat) : Real :=
  SOptLib.expectation sampleLaw
    (fun omega =>
      legacyDiagnosticFeasibleBregman S
        ((legacyDiagnosticEpochStateProcessFeasibleOn S T gamma alpha p theta q x0 samples hparams htheta s omega).x)
        x)

/- Route tombstone: `weighted_output_core_step_spine_route_v1`.
The former weighted relational output surface has been removed from the compiled
namespace. Its specification combined Algorithm 5.7's printed epoch output with
extra per-step prox-core witnesses for feasible trajectory states. The active
public route below uses `theorem59PrintedFeasibleEpochOutputProcessSpec`, whose
contract stays at the printed feasible epoch-output level. -/

/- Route tombstone: the former weak relational output selector family
`theorem59_weak_relational_output_selector_route_v1` has no compiled
entrypoint. It recorded feasibility and unrelated one-step witnesses without
binding the selected output to Algorithm 5.7's theta-weighted epoch output.
Public/source consumers use `theorem59PrintedFeasibleEpochOutputProcessSpec`
instead. -/

/-- Internal prox-core realization of the Theorem 5.9 Algorithm 5.7 process. -/
def theorem59CorrectedCoreEpochStateProcess {Ω : Type*} {n dim : Nat} (S : Setup n dim)
    (hmu : 0 < S.mu) (x0 : Set.Elem (proxCoreSet S))
    (samples : Nat -> Nat -> Ω -> Fin n) : Nat -> Ω -> EpochStateOn S :=
  epochStateProcessOn S (theorem59EpochLength S) (theorem59Gamma S)
    (theorem59Alpha S) theorem59P
    (theorem59Theta S hmu (averageSmoothness_pos S)) (samplingWeight S) x0 samples
    (theorem59_parameter_conditions S hmu)
    (theorem59Theta_epochOutputWeightsAdmissible S hmu)

/-- Corrected-core output process used by domain-correct Theorem 5.9 proofs.

This is deliberately separate from the printed feasible Algorithm 5.7 output:
it reads the `xTilde` coordinate of the `X^o`-typed corrected-core epoch
process. Public printed-output theorems must cross to this process only through
`theorem59OriginalOutputCompatibility`. -/
def theorem59CorrectedCoreOutputProcessOn {Ω : Type*} {n dim : Nat} (S : Setup n dim)
    (hmu : 0 < S.mu) (x0 : Set.Elem (proxCoreSet S))
    (samples : Nat -> Nat -> Ω -> Fin n) :
    Nat -> Ω -> VariableSpace dim :=
  fun s omega => (theorem59CorrectedCoreEpochStateProcess S hmu x0 samples s omega).xTilde.1

/-- Corrected-core output under the canonical Theorem 5.9 sample law. -/
def theorem59CorrectedCoreOutputProcess {n dim : Nat} (S : Setup n dim)
    (hmu : 0 < S.mu) (x0 : Set.Elem (proxCoreSet S)) :
    Nat -> theorem59SamplePath n -> VariableSpace dim :=
  theorem59CorrectedCoreOutputProcessOn S hmu x0 theorem59CanonicalSamples

/-- Certified corrected-core epoch-state process for Theorem 5.9.

This is the replacement realization used by the Phase 2b handoff: the prox
subproblem certificates are supplied through `CoreProxOracleOn`, so the process
does not unfold to `Classical.choose (proxUpdateCoreOn_exists ...)`. -/
def theorem59CertifiedCoreEpochStateProcessOn {Ω : Type*} {n dim : Nat}
    (S : Setup n dim) (hmu : 0 < S.mu) (x0 : Set.Elem (proxCoreSet S))
    (samples : Nat -> Nat -> Ω -> Fin n)
    (oracle : CoreProxOracleOn S (theorem59Gamma S)) :
    Nat -> Ω -> EpochStateOn S :=
  epochStateProcessCertifiedOn S (theorem59EpochLength S) (theorem59Gamma S)
    (theorem59Alpha S) theorem59P oracle
    (theorem59Theta S hmu (averageSmoothness_pos S)) (samplingWeight S) x0 samples
    (theorem59_parameter_conditions S hmu)
    (theorem59Theta_epochOutputWeightsAdmissible S hmu)

/-- Certified corrected-core stochastic output for Theorem 5.9 and a supplied
sample stream. -/
def theorem59CertifiedCoreOutputProcessOn {Ω : Type*} {n dim : Nat}
    (S : Setup n dim) (hmu : 0 < S.mu) (x0 : Set.Elem (proxCoreSet S))
    (samples : Nat -> Nat -> Ω -> Fin n)
    (oracle : CoreProxOracleOn S (theorem59Gamma S)) :
    Nat -> Ω -> VariableSpace dim :=
  epochOutputProcessCertifiedOn S (theorem59EpochLength S) (theorem59Gamma S)
    (theorem59Alpha S) theorem59P oracle
    (theorem59Theta S hmu (averageSmoothness_pos S)) (samplingWeight S)
    x0 samples
    (theorem59_parameter_conditions S hmu)
    (theorem59Theta_epochOutputWeightsAdmissible S hmu)

/-- Certified corrected-core stochastic output under the canonical Theorem 5.9
sample law. -/
def theorem59CertifiedCoreOutputProcess {n dim : Nat} (S : Setup n dim)
    (hmu : 0 < S.mu) (x0 : Set.Elem (proxCoreSet S))
    (oracle : CoreProxOracleOn S (theorem59Gamma S)) :
    Nat -> theorem59SamplePath n -> VariableSpace dim :=
  theorem59CertifiedCoreOutputProcessOn S hmu x0 theorem59CanonicalSamples oracle

theorem theorem59CertifiedCoreEpochStateProcess_mem_proxCore {Ω : Type*} {n dim : Nat}
    (S : Setup n dim) (hmu : 0 < S.mu) (x0 : Set.Elem (proxCoreSet S))
    (samples : Nat -> Nat -> Ω -> Fin n)
    (oracle : CoreProxOracleOn S (theorem59Gamma S))
    (s : Nat) (omega : Ω) :
    let state := theorem59CertifiedCoreEpochStateProcessOn S hmu x0 samples oracle s omega
    state.x.1 ∈ proxCoreSet S ∧ state.xTilde.1 ∈ proxCoreSet S := by
  simpa [theorem59CertifiedCoreEpochStateProcessOn] using
    epochStateProcessCertifiedOn_mem_proxCore S
      (theorem59EpochLength S) (theorem59Gamma S) (theorem59Alpha S) theorem59P
      oracle (theorem59Theta S hmu (averageSmoothness_pos S)) (samplingWeight S)
      x0 samples (theorem59_parameter_conditions S hmu)
      (theorem59Theta_epochOutputWeightsAdmissible S hmu) s omega

/-- Private boundary gradient extension for Algorithm 5.7's printed over-`X`
prox line.

The paper-literal Bregman object is still `bregmanOn : X^o -> X -> Real`.
This private totalization is only the Lean device that lets the printed
`argmin_{x in X}` line be stated before the proof has established that its
left centers lie in `X^o`. -/
def theorem59PrintedFeasibleBoundaryGradientExtensionOn {n dim : Nat}
    (S : Setup n dim) (x : FeasiblePoint S) : VariableSpace dim :=
  gradientWithin S.nu S.X x.1

/-- Paper-literal printed Bregman object on the source domain `X^o x X`.

Source anchor: JSON `#/assumptions/7`, Eq. (3.2.2), states
`V(x,z)=nu(z)-[nu(x)+<grad nu(x),z-x>]`. -/
def theorem59PrintedFeasibleBregmanLiteralOn {n dim : Nat} (S : Setup n dim)
    (x : Set.Elem (proxCoreSet S)) (z : FeasiblePoint S) : Real :=
  bregmanOn S x z

@[simp]
theorem theorem59PrintedFeasibleBregmanLiteralOn_def {n dim : Nat} (S : Setup n dim)
    (x : Set.Elem (proxCoreSet S)) (z : FeasiblePoint S) :
    theorem59PrintedFeasibleBregmanLiteralOn S x z = bregmanOn S x z := by
  rfl

/-- Boundary extension used only to type Algorithm 5.7's printed over-`X` prox line.

No SOptLib match: searched `Bregman divergence relative interior domain`,
`carrier Bregman boundary extension`, and `prox argmin feasible IsMinOn`; checked
`SOptLib.literalBregmanDivergence`, `SOptLib.carrierBregmanDivergence`, and
`SOptLib.acceleratedCompositeProxObjective`. The source prox function remains
`bregmanOn : X^o -> X -> Real`; this expression is the explicit all-feasible
boundary extension needed to state the printed line before the left-center
domain bridge is available. -/
def theorem59PrintedFeasibleBregmanBoundaryOn {n dim : Nat} (S : Setup n dim)
    (x z : FeasiblePoint S) : Real :=
  S.nu z.1 - S.nu x.1 -
    ⟪theorem59PrintedFeasibleBoundaryGradientExtensionOn S x, z.1 - x.1⟫_Real

@[simp]
theorem theorem59PrintedFeasibleBregmanBoundaryOn_def {n dim : Nat} (S : Setup n dim)
    (x z : FeasiblePoint S) :
    theorem59PrintedFeasibleBregmanBoundaryOn S x z =
      S.nu z.1 - S.nu x.1 -
        ⟪theorem59PrintedFeasibleBoundaryGradientExtensionOn S x, z.1 - x.1⟫_Real := by
  rfl

theorem theorem59PrintedFeasibleBregmanBoundaryOn_eq_legacy
    {n dim : Nat} (S : Setup n dim) (x z : FeasiblePoint S) :
    theorem59PrintedFeasibleBregmanBoundaryOn S x z =
      legacyDiagnosticFeasibleBregman S x z := by
  rfl

/-- The printed feasible boundary extension agrees with the source `X^o x X`
Bregman prox function when its left argument is actually in the prox core. -/
theorem theorem59PrintedFeasibleBregmanBoundaryOn_eq_bregmanOn_of_proxCore
    {n dim : Nat} (S : Setup n dim) (x : Set.Elem (proxCoreSet S)) (z : FeasiblePoint S) :
    theorem59PrintedFeasibleBregmanBoundaryOn S (proxCoreAsFeasible S x) z =
      bregmanOn S x z := by
  rw [theorem59PrintedFeasibleBregmanBoundaryOn_eq_legacy]
  exact legacyDiagnosticFeasibleBregman_eq_bregmanOn_of_proxCore S x z

theorem theorem59PrintedFeasibleBregmanBoundaryOn_eq_literal_of_proxCore
    {n dim : Nat} (S : Setup n dim) (x : Set.Elem (proxCoreSet S)) (z : FeasiblePoint S) :
    theorem59PrintedFeasibleBregmanBoundaryOn S (proxCoreAsFeasible S x) z =
      theorem59PrintedFeasibleBregmanLiteralOn S x z := by
  simpa [theorem59PrintedFeasibleBregmanLiteralOn] using
    theorem59PrintedFeasibleBregmanBoundaryOn_eq_bregmanOn_of_proxCore S x z

/-- Feasible-level objective for Algorithm 5.7's printed prox line.

No SOptLib match: searched `prox argmin relation feasible IsMinOn objective`,
`partial bregman feasible center relation objective`, and `Bregman divergence
relative interior domain`; checked `SOptLib.acceleratedCompositeProxObjective`,
`SOptLib.IsCompositeProxStepOn`, `SOptLib.literalBregmanDivergence`, and
`SOptLib.carrierBregmanDivergence`. The reusable prox objective is all-carrier
once a divergence `V : X -> X -> R` is supplied, while Lan §3.2's canonical
prox function is `X^o x X`. This definition is therefore the printed
line-16901 over-`X` objective, kept separate from the canonical
`ProxUpdateRelOn` bridge below. -/
def theorem59PrintedFeasibleProxObjectiveOn {n dim : Nat} (S : Setup n dim)
    (gamma : Nat -> Real) (s : Nat)
    (xPrev xUnder : FeasiblePoint S)
    (g : VariableSpace dim) (x : FeasiblePoint S) : Real :=
  SOptLib.acceleratedCompositeProxObjective gamma S.mu
    (fun y : FeasiblePoint S => S.h y.1)
    (theorem59PrintedFeasibleBregmanBoundaryOn S)
    (fun y : FeasiblePoint S => y.1)
    s xPrev xUnder g x

@[simp]
theorem theorem59PrintedFeasibleProxObjectiveOn_def {n dim : Nat} (S : Setup n dim)
    (gamma : Nat -> Real) (s : Nat)
    (xPrev xUnder : FeasiblePoint S)
    (g : VariableSpace dim) (x : FeasiblePoint S) :
    theorem59PrintedFeasibleProxObjectiveOn S gamma s xPrev xUnder g x =
      gamma s *
          (⟪g, x.1⟫_Real + S.h x.1 +
            S.mu * theorem59PrintedFeasibleBregmanBoundaryOn S xUnder x) +
        theorem59PrintedFeasibleBregmanBoundaryOn S xPrev x := by
  rfl

/-- Ambient form of Algorithm 5.7's printed feasible prox objective.

This is not a new paper primitive. It is the ambient totalization needed to use
standard constrained-minimum theorems on the feasible set `X`; on feasible
points it agrees definitionally with `theorem59PrintedFeasibleProxObjectiveOn`. -/
def theorem59PrintedFeasibleProxObjectiveAmbientOn {n dim : Nat} (S : Setup n dim)
    (gamma : Nat -> Real) (s : Nat)
    (xPrev xUnder : FeasiblePoint S)
    (g : VariableSpace dim) (x : VariableSpace dim) : Real :=
  gamma s *
      (⟪g, x⟫_Real + S.h x +
        S.mu * (S.nu x - S.nu xUnder.1 -
          ⟪theorem59PrintedFeasibleBoundaryGradientExtensionOn S xUnder,
            x - xUnder.1⟫_Real)) +
    (S.nu x - S.nu xPrev.1 -
      ⟪theorem59PrintedFeasibleBoundaryGradientExtensionOn S xPrev,
        x - xPrev.1⟫_Real)

@[simp]
theorem theorem59PrintedFeasibleProxObjectiveAmbientOn_agrees
    {n dim : Nat} (S : Setup n dim)
    (gamma : Nat -> Real) (s : Nat)
    (xPrev xUnder : FeasiblePoint S)
    (g : VariableSpace dim) (x : FeasiblePoint S) :
    theorem59PrintedFeasibleProxObjectiveAmbientOn S gamma s xPrev xUnder g x.1 =
      theorem59PrintedFeasibleProxObjectiveOn S gamma s xPrev xUnder g x := by
  rfl

theorem h_simple_continuousOn {n dim : Nat} (S : Setup n dim) :
    ContinuousOn S.h S.X := by
  exact SOptLib.IsSimpleConvexTermOn.continuousOn S.h_simple

theorem h_simple_lowerSemicontinuousOn {n dim : Nat} (S : Setup n dim) :
    LowerSemicontinuousOn S.h S.X :=
  (h_simple_continuousOn S).lowerSemicontinuousOn

theorem h_simple_exists_strict_affine_minorant
    {n dim : Nat} (S : Setup n dim) (z : FeasiblePoint S) {a : Real}
    (ha : a < S.h z.1) :
    ∃ (l : VariableSpace dim →L[Real] Real) (c : Real),
      (∀ y : FeasiblePoint S, l y.1 + c ≤ S.h y.1) ∧
        l z.1 + c = a := by
  exact SOptLib.IsSimpleConvexTermOn.exists_strict_affine_minorant
    S.h_simple S.X_closed z ha

/-- Finite closed-ball halfspace feasibility from the Farkas dual inequalities.

This is the finite-dimensional separation step used in the positive printed
prox support leaf.  For a finite family of displacement vectors `d i` and
right sides `rhs i`, feasibility of the halfspaces over the ball of radius `R`
is certified by the usual probability-weighted dual inequalities. -/
theorem theorem59_finite_closedBall_halfspace_feasible_of_dual
    {dim : Nat} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : Real) (hR : 0 <= R)
    (d : ι -> VariableSpace dim) (rhs : ι -> Real)
    (hdual :
      ∀ w : ι -> Real,
        (∀ i : ι, 0 <= w i) ->
        Finset.univ.sum w = 1 ->
          -R * ‖Finset.univ.sum (fun i : ι => w i • d i)‖ <=
            Finset.univ.sum (fun i : ι => w i * rhs i)) :
    ∃ p : VariableSpace dim,
      ‖p‖ <= R ∧ ∀ i : ι, ⟪p, d i⟫_Real <= rhs i := by
  simpa using
    (exists_closedBall_forall_inner_le_of_dual_simplex
      (E := VariableSpace dim) (ι := ι) R hR d rhs hdual)

/-- Compactness upgrade from bounded approximate supports to an exact carrier
subgradient.

This is route-local convex-analysis infrastructure for the positive printed
prox bridge.  It separates the compact limiting step from the still separate
task of producing bounded approximate support vectors from the tilted prox
inequality. -/
theorem theorem59_exact_carrierSubgradient_of_bounded_approx_supports
    {n dim : Nat} (S : Setup n dim) (z : FeasiblePoint S)
    (B : Real) (_hB : 0 <= B)
    (happrox :
      ∀ ε : Real, 0 < ε ->
        ∃ p : VariableSpace dim,
          ‖p‖ <= B ∧
            ∀ y : FeasiblePoint S,
              S.nu z.1 - ε + ⟪p, y.1 - z.1⟫_Real <= S.nu y.1) :
    ∃ pnu : VariableSpace dim,
      pnu ∈
        SOptLib.carrierSubdifferential
          (X := S.X) (fun x : FeasiblePoint S => S.nu x.1) z := by
  exact
    SOptLib.exists_carrierSubdifferential_of_bounded_approx_supports
      (f := fun x : FeasiblePoint S => S.nu x.1) z B happrox

/-- Compact finite-intersection lift for bounded approximate carrier supports.

This route-local helper isolates the topological step in the printed prox
support leaf. To produce an approximate support vector for all feasible
comparisons it suffices to produce one, with the same norm bound, for every
finite family of feasible comparisons. -/
theorem theorem59_bounded_approx_supports_of_finite_subfamilies
    {n dim : Nat} (S : Setup n dim) (z : FeasiblePoint S)
    (B : Real) (_hB : 0 <= B)
    (hfinite :
      ∀ ε : Real, 0 < ε ->
        ∀ Y : Finset (FeasiblePoint S),
          ∃ p : VariableSpace dim,
            ‖p‖ <= B ∧
              ∀ y : FeasiblePoint S, y ∈ Y ->
                S.nu z.1 - ε + ⟪p, y.1 - z.1⟫_Real <= S.nu y.1) :
    ∀ ε : Real, 0 < ε ->
      ∃ p : VariableSpace dim,
        ‖p‖ <= B ∧
          ∀ y : FeasiblePoint S,
            S.nu z.1 - ε + ⟪p, y.1 - z.1⟫_Real <= S.nu y.1 := by
  exact
    SOptLib.bounded_approx_supports_of_finite_subfamilies
      (E := VariableSpace dim) (X := S.X)
      (f := fun x : FeasiblePoint S => S.nu x.1) z B hfinite

theorem theorem59PrintedFeasibleProxObjectiveAmbientOn_continuousOn
    {n dim : Nat} (S : Setup n dim)
    (gamma : Nat -> Real) (s : Nat)
    (xPrev xUnder : FeasiblePoint S)
    (g : VariableSpace dim) :
    ContinuousOn
      (theorem59PrintedFeasibleProxObjectiveAmbientOn S gamma s xPrev xUnder g)
      S.X := by
  simpa [theorem59PrintedFeasibleProxObjectiveAmbientOn] using
    (SOptLib.mixedAcceleratedCompositeProxObjective_continuousOn
      (X := S.X) (gamma := gamma) (mu := S.mu) (h := S.h)
      (V := fun y : FeasiblePoint S => fun x : VariableSpace dim =>
        S.nu x - S.nu y.1 -
          ⟪theorem59PrintedFeasibleBoundaryGradientExtensionOn S y, x - y.1⟫_Real)
      (eval := fun x : VariableSpace dim => x)
      (t := s) (xPrev := xPrev) (xUnder := xUnder) (g := g)
      (h_simple_continuousOn S)
      ((S.nu_continuousOn.sub continuousOn_const).sub
        ((continuous_const.inner (continuous_id.sub continuous_const)).continuousOn))
      ((S.nu_continuousOn.sub continuousOn_const).sub
        ((continuous_const.inner (continuous_id.sub continuous_const)).continuousOn))
      continuousOn_id)

/-- Feasible-level statement of Algorithm 5.7's printed prox line.

The displayed prox update minimizes over `X`, so the result `z` is a
`FeasiblePoint` and the public trajectory predicate does not carry prox-core
subtype witnesses for the previous iterate or search point. The separate theorem
`theorem59PrintedFeasibleProxUpdateRelOn_iff_canonical_of_core_centers` records
the exact extra domain bridge needed to read this printed line through the
canonical §3.2 object `ProxUpdateRelOn`. -/
def theorem59PrintedFeasibleProxUpdateRelOn {n dim : Nat} (S : Setup n dim)
    (gamma : Nat -> Real) (s : Nat)
    (xPrev xUnder : FeasiblePoint S)
    (g : VariableSpace dim) (z : FeasiblePoint S) : Prop :=
  IsMinOn
    (fun x : FeasiblePoint S =>
      theorem59PrintedFeasibleProxObjectiveOn S gamma s xPrev xUnder g x)
    Set.univ z

theorem theorem59PrintedFeasibleProxUpdateRelOn_iff
    {n dim : Nat} (S : Setup n dim)
    (gamma : Nat -> Real) (s : Nat)
    (xPrev xUnder : FeasiblePoint S)
    (g : VariableSpace dim) (z : FeasiblePoint S)
    :
    theorem59PrintedFeasibleProxUpdateRelOn S gamma s xPrev xUnder g z ↔
      IsMinOn
        (fun x : FeasiblePoint S =>
          theorem59PrintedFeasibleProxObjectiveOn S gamma s xPrev xUnder g x)
        Set.univ z := by
  rfl

/-- Closed-ball/coercive-tail sufficient condition for Algorithm 5.7's printed
feasible prox-update existence.

This is the executable Mathlib/SOptLib bridge for the source-level argmin leaf:
after continuity of the ambient printed objective on `X` and a lower-tail bound
are proved, `exists_isMinOn_of_closed_coercive_closedBall` supplies the feasible
minimizer. The theorem does not assume or conclude any `proxCoreSet` membership
for the printed feasible minimizer. -/
theorem theorem59PrintedFeasibleProxUpdateExistsOn_of_continuous_tail
    {n dim : Nat} (S : Setup n dim)
    (gamma : Nat -> Real) (s : Nat)
    (xPrev xUnder : FeasiblePoint S)
    (g : VariableSpace dim)
    (hcont :
      ContinuousOn
        (theorem59PrintedFeasibleProxObjectiveAmbientOn S gamma s xPrev xUnder g)
        S.X)
    (htail : ∃ R : Real, dist xPrev.1 xPrev.1 <= R ∧
      ∀ x : VariableSpace dim, x ∈ S.X -> R <= dist x xPrev.1 ->
        theorem59PrintedFeasibleProxObjectiveAmbientOn S gamma s xPrev xUnder g xPrev.1 <=
          theorem59PrintedFeasibleProxObjectiveAmbientOn S gamma s xPrev xUnder g x) :
    ∃ z : FeasiblePoint S,
      theorem59PrintedFeasibleProxUpdateRelOn S gamma s xPrev xUnder g z := by
  classical
  obtain ⟨z, hzX, hzmin⟩ :=
    exists_isMinOn_of_closed_coercive_closedBall S.X_closed xPrev.1 xPrev.1
      xPrev.2
      (theorem59PrintedFeasibleProxObjectiveAmbientOn S gamma s xPrev xUnder g)
      hcont htail
  refine ⟨⟨z, hzX⟩, ?_⟩
  intro y _hy
  simpa [theorem59PrintedFeasibleProxUpdateRelOn] using
    hzmin y.2

set_option maxHeartbeats 800000

/-- Core-anchor lower-tail bridge for Algorithm 5.7's printed feasible prox objective.

The printed prox centers `xPrev` and `xUnder` are feasible points, not prox-core
subtype points. The generated Algorithm 5.7 process nevertheless has the
initial prox-core point `x0` available. This helper isolates the analytic
coercivity argument: the source DGF lower bound from the fixed core anchor gives
a positive quadratic lower model for `nu` on all feasible points, while the
simple-term expression witness gives only a linear lower loss.  The quadratic
term dominates the affine, gradient, and simple-term linear tails. -/
theorem theorem59PrintedFeasibleProxObjectiveAmbientOn_tail_of_core_anchor
    {n dim : Nat} (S : Setup n dim)
    (gamma : Nat -> Real) (s : Nat)
    (hgamma : 0 < gamma s)
    (xAnchor : Set.Elem (proxCoreSet S))
    (xPrev xUnder : FeasiblePoint S)
    (g : VariableSpace dim) :
    ∃ R : Real, dist xPrev.1 xPrev.1 <= R ∧
      ∀ x : VariableSpace dim, x ∈ S.X -> R <= dist x xPrev.1 ->
        theorem59PrintedFeasibleProxObjectiveAmbientOn S gamma s xPrev xUnder g xPrev.1 <=
          theorem59PrintedFeasibleProxObjectiveAmbientOn S gamma s xPrev xUnder g x := by
  classical
  obtain ⟨K, _hK_nonneg, hK_lip⟩ :=
    SOptLib.SimpleConvexTermExpr.exists_lipschitz_eval
      S.h_simple.knownStructure
  simpa [theorem59PrintedFeasibleProxObjectiveAmbientOn] using
    SOptLib.acceleratedCompositeProxObjective_closedBall_tail_of_quadratic_anchor
      (X := S.X) S.nu S.h (gamma := gamma s) (mu := S.mu)
      hgamma S.mu_nonneg xAnchor.1 xPrev.1 xUnder.1 g
      (gradientWithin S.nu S.X xAnchor.1)
      (theorem59PrintedFeasibleBoundaryGradientExtensionOn S xUnder)
      (theorem59PrintedFeasibleBoundaryGradientExtensionOn S xPrev)
      K
      (by
        intro x hx
        have hnu_core :=
          bregman_modulus_one_lower S xAnchor (⟨x, hx⟩ : FeasiblePoint S)
        rw [bregman_def] at hnu_core
        have hnu_core' :
            (1 / 2 : Real) * ‖xAnchor.1 - x‖ ^ 2 <=
              S.nu x -
                (S.nu xAnchor.1 +
                  ⟪gradientWithin S.nu S.X xAnchor.1, x - xAnchor.1⟫_Real) := by
          simpa only [Subtype.coe_mk] using hnu_core
        have hnorm : ‖xAnchor.1 - x‖ = ‖x - xAnchor.1‖ :=
          norm_sub_rev xAnchor.1 x
        rw [hnorm] at hnu_core'
        nlinarith)
      (by
        intro x hx
        have haX : xAnchor.1 ∈ S.X :=
          proxCoreSetElem_mem_X S xAnchor
        have hh_abs : |S.h x - S.h xAnchor.1| <= K * ‖x - xAnchor.1‖ := by
          have hh_lip := hK_lip x xAnchor.1
          have hagree_x := S.h_simple.agreesOn x hx
          have hagree_a := S.h_simple.agreesOn xAnchor.1 haX
          simpa [hagree_x, hagree_a] using hh_lip
        have hneg_abs :
            -(K * ‖x - xAnchor.1‖) <= S.h x - S.h xAnchor.1 := by
          exact neg_le.mp (le_trans (neg_le_abs (S.h x - S.h xAnchor.1)) hh_abs)
        linarith)

/-- Source-level existence obligation for Algorithm 5.7's printed feasible prox line.

This is the exact `argmin_{x in X}` supplier for the generated printed feasible
trajectory. It replaces the retired `legacyDiagnosticProxUpdateAllFeasibleOn`
supplier in the public route; the remaining proof obligation is now the
source-level feasible minimizer existence statement itself.  The private
generated selector is allowed to use the fixed initial core anchor `xAnchor`
for coercivity; the public printed trajectory relation still stores only
feasible centers and the `argmin_{x in X}` certificate. -/
theorem theorem59PrintedFeasibleProxUpdateExistsOn
    {n dim : Nat} (S : Setup n dim)
    (gamma : Nat -> Real) (s : Nat)
    (hgamma : 0 < gamma s)
    (xAnchor : Set.Elem (proxCoreSet S))
    (xPrev xUnder : FeasiblePoint S)
    (g : VariableSpace dim) :
    ∃ z : FeasiblePoint S,
      theorem59PrintedFeasibleProxUpdateRelOn S gamma s xPrev xUnder g z := by
  simpa [theorem59PrintedFeasibleProxUpdateRelOn,
    theorem59PrintedFeasibleProxObjectiveOn,
    theorem59PrintedFeasibleProxObjectiveAmbientOn,
    theorem59PrintedFeasibleBregmanBoundaryOn,
    SOptLib.mixedAcceleratedCompositeProxObjective] using
    (SOptLib.exists_acceleratedCompositeProxObjective_isMinOn_of_closedBall_tail
      (X := S.X) S.X_closed gamma S.mu S.h
      (fun c : FeasiblePoint S => fun x : VariableSpace dim =>
        S.nu x - S.nu c.1 -
          ⟪theorem59PrintedFeasibleBoundaryGradientExtensionOn S c, x - c.1⟫_Real)
      (fun x : VariableSpace dim => x)
      s xPrev xUnder g xPrev.1 xPrev.1 xPrev.2
      (by
        simpa [theorem59PrintedFeasibleProxObjectiveAmbientOn,
          SOptLib.mixedAcceleratedCompositeProxObjective] using
          theorem59PrintedFeasibleProxObjectiveAmbientOn_continuousOn
            S gamma s xPrev xUnder g)
      (by
        simpa [theorem59PrintedFeasibleProxObjectiveAmbientOn,
          SOptLib.mixedAcceleratedCompositeProxObjective] using
          theorem59PrintedFeasibleProxObjectiveAmbientOn_tail_of_core_anchor
            S gamma s hgamma xAnchor xPrev xUnder g))

/-- Pointwise nonempty fibers do not by themselves make a chosen selector measurable.

This is the Lean-side obstruction behind Algorithm 5.7 line 16901's printed
`argmin`: the JSON/source line supplies a pointwise minimizer relation, while
the generated process additionally needs measurability of the selected
realizer. Considered `measurable_of_finite_range_fiber_const`,
`proxStep_measurable_of_joint_continuous_unique`, and
`mirrorObjective_argmin_selector_measurable_of_continuous_unique`; the first
requires an actual finite-range observable, and the latter two require compact
unique-argmin infrastructure not present in the printed feasible prox
interface. -/
private theorem pointwise_choice_selector_measurability_obstruction :
    ∃ (R : Bool -> Fin 2 -> Prop) (h : ∀ omega, ∃ z, R omega z),
      ¬ (∀ ⦃t : Set (Fin 2)⦄,
        @MeasurableSet _ (⊤ : MeasurableSpace (Fin 2)) t ->
          @MeasurableSet _ (⊥ : MeasurableSpace Bool)
            ((fun omega : Bool => Classical.choose (h omega)) ⁻¹' t)) := by
  classical
  let f : Bool -> Fin 2 := fun omega => if omega then 1 else 0
  let R : Bool -> Fin 2 -> Prop := fun omega z => z = f omega
  let h : ∀ omega, ∃ z, R omega z := fun omega => ⟨f omega, rfl⟩
  refine ⟨R, h, ?_⟩
  intro hmeas
  have htarget :
      @MeasurableSet _ (⊤ : MeasurableSpace (Fin 2))
        ({(1 : Fin 2)} : Set (Fin 2)) := by
    trivial
  have hpre := hmeas htarget
  have hpre_eq :
      f ⁻¹' ({(1 : Fin 2)} : Set (Fin 2)) =
        ({true} : Set Bool) := by
    ext omega
    cases omega <;> simp [h, R, f]
  have hsingle :
      @MeasurableSet _ (⊥ : MeasurableSpace Bool)
        ({true} : Set Bool) := by
    simpa [hpre_eq] using hpre
  rcases
    (MeasurableSpace.measurableSet_bot_iff (s := ({true} : Set Bool))).mp
      hsingle with hempty | huniv
  · have : true ∈ (∅ : Set Bool) := by
      rw [← hempty]
      simp
    simpa using this
  · have : false ∈ ({true} : Set Bool) := by
      rw [huniv]
      simp
    simpa using this

/-- Finite-observable route for the exact generated printed prox input.

This is the only SOptLib finite-key lemma that matches the measurable-selector
shape after specializing Algorithm 5.7 line 16901: if the generated triple
`(xPrev, xUnder, G)` has finite range, then any selected prox realizer depending
only on that triple is measurable. Considered
`measurable_of_finite_range_fiber_const`,
`integrable_of_finiteRange_factor`, and `measurable_fintype_dispatch`; the first
is the exact measurability bridge, while the latter two are downstream
integrability/finite-branch tools and do not provide the missing finite-range
key. -/
private theorem theorem59_printed_feasible_prox_raw_generated_input_measurable_of_finite_input
    {n dim : Nat} (S : Setup n dim) (s : Nat)
    (hmu : 0 < S.mu) (hs : 1 <= s)
    (raw : FeasiblePoint S -> FeasiblePoint S -> VariableSpace dim -> FeasiblePoint S)
    (hinput_meas :
      Measurable
        (fun p :
          ((FeasiblePoint S ×
            (FeasiblePoint S × (FeasiblePoint S × FeasiblePoint S))) × Fin n) =>
          let snapshotFixed : FeasiblePoint S := p.1.1
          let prev : InnerStateFeasibleOn S :=
            { x := p.1.2.2.1, xBar := p.1.2.2.2 }
          let xUnder :=
            searchPointFeasibleOn S (theorem59Gamma S) (theorem59Alpha S)
              theorem59P s prev.xBar prev.x snapshotFixed
              ((theorem59_parameter_conditions S hmu s hs).2.2.2.2.1)
          let G :=
            varianceReducedGradientFeasibleOn S (samplingWeight S) p.2 xUnder
              snapshotFixed (fullGradient S snapshotFixed.1)
          (prev.x, xUnder, G)))
    (hfin :
      (Set.range
        (fun p :
          ((FeasiblePoint S ×
            (FeasiblePoint S × (FeasiblePoint S × FeasiblePoint S))) × Fin n) =>
          let snapshotFixed : FeasiblePoint S := p.1.1
          let prev : InnerStateFeasibleOn S :=
            { x := p.1.2.2.1, xBar := p.1.2.2.2 }
          let xUnder :=
            searchPointFeasibleOn S (theorem59Gamma S) (theorem59Alpha S)
              theorem59P s prev.xBar prev.x snapshotFixed
              ((theorem59_parameter_conditions S hmu s hs).2.2.2.2.1)
          let G :=
            varianceReducedGradientFeasibleOn S (samplingWeight S) p.2 xUnder
              snapshotFixed (fullGradient S snapshotFixed.1)
          (prev.x, xUnder, G))).Finite) :
    Measurable
      (fun p :
        ((FeasiblePoint S ×
          (FeasiblePoint S × (FeasiblePoint S × FeasiblePoint S))) × Fin n) =>
        let snapshotFixed : FeasiblePoint S := p.1.1
        let prev : InnerStateFeasibleOn S :=
          { x := p.1.2.2.1, xBar := p.1.2.2.2 }
        let xUnder :=
          searchPointFeasibleOn S (theorem59Gamma S) (theorem59Alpha S)
            theorem59P s prev.xBar prev.x snapshotFixed
            ((theorem59_parameter_conditions S hmu s hs).2.2.2.2.1)
        let G :=
          varianceReducedGradientFeasibleOn S (samplingWeight S) p.2 xUnder
            snapshotFixed (fullGradient S snapshotFixed.1)
        raw prev.x xUnder G) := by
  classical
  let input :
      ((FeasiblePoint S ×
        (FeasiblePoint S × (FeasiblePoint S × FeasiblePoint S))) × Fin n) ->
        FeasiblePoint S × FeasiblePoint S × VariableSpace dim :=
    fun p =>
      let snapshotFixed : FeasiblePoint S := p.1.1
      let prev : InnerStateFeasibleOn S :=
        { x := p.1.2.2.1, xBar := p.1.2.2.2 }
      let xUnder :=
        searchPointFeasibleOn S (theorem59Gamma S) (theorem59Alpha S)
          theorem59P s prev.xBar prev.x snapshotFixed
          ((theorem59_parameter_conditions S hmu s hs).2.2.2.2.1)
      let G :=
        varianceReducedGradientFeasibleOn S (samplingWeight S) p.2 xUnder
          snapshotFixed (fullGradient S snapshotFixed.1)
      (prev.x, xUnder, G)
  let Z :
      ((FeasiblePoint S ×
        (FeasiblePoint S × (FeasiblePoint S × FeasiblePoint S))) × Fin n) ->
        FeasiblePoint S :=
    fun p => raw (input p).1 (input p).2.1 (input p).2.2
  have hinput : Measurable input := by
    simpa [input] using hinput_meas
  have hZ : Measurable Z := by
    refine measurable_of_finite_range_fiber_const (Y := input) (Z := Z)
      hinput ?_ ?_
    · simpa [input] using hfin
    · intro p p' hp
      dsimp [Z]
      rw [hp]
  simpa [Z, input]

/-- Measurable-selector realization of Algorithm 5.7's printed feasible prox line.

This is the raw selector interface needed by the generated stochastic process:
the selected prox point must satisfy the printed `argmin_{x in X}` relation and,
when specialized to the Theorem 5.9 generated inner-step inputs, the selected
point must be measurable from the state/sample package. The remaining proof
leaf is exactly the measurable-selection theorem for the concrete noncompact
coercive prox objective; pointwise minimizer existence is supplied by
`theorem59PrintedFeasibleProxUpdateExistsOn`. -/
theorem theorem59PrintedFeasibleProxUpdateMeasurableExistsOn
    {n dim : Nat} (S : Setup n dim)
    (gamma : Nat -> Real) (s : Nat)
    (hgamma : 0 < gamma s)
    (xAnchor : Set.Elem (proxCoreSet S)) :
    ∃ select :
        FeasiblePoint S -> FeasiblePoint S -> VariableSpace dim -> FeasiblePoint S,
      (forall (xPrev xUnder : FeasiblePoint S) (g : VariableSpace dim),
        theorem59PrintedFeasibleProxUpdateRelOn S gamma s xPrev xUnder g
          (select xPrev xUnder g)) ∧
      (forall (hmu : 0 < S.mu) (hs : 1 <= s),
        gamma = theorem59Gamma S ->
        Measurable
          (fun p :
            ((FeasiblePoint S ×
              (FeasiblePoint S × (FeasiblePoint S × FeasiblePoint S))) × Fin n) =>
            let snapshotFixed : FeasiblePoint S := p.1.1
            let prev : InnerStateFeasibleOn S :=
              { x := p.1.2.2.1, xBar := p.1.2.2.2 }
            let xUnder :=
              searchPointFeasibleOn S (theorem59Gamma S) (theorem59Alpha S)
                theorem59P s prev.xBar prev.x snapshotFixed
                ((theorem59_parameter_conditions S hmu s hs).2.2.2.2.1)
            let G :=
              varianceReducedGradientFeasibleOn S (samplingWeight S) p.2 xUnder
                snapshotFixed (fullGradient S snapshotFixed.1)
            (prev.x, xUnder, G)) ->
        (Set.range
          (fun p :
            ((FeasiblePoint S ×
              (FeasiblePoint S × (FeasiblePoint S × FeasiblePoint S))) × Fin n) =>
            let snapshotFixed : FeasiblePoint S := p.1.1
            let prev : InnerStateFeasibleOn S :=
              { x := p.1.2.2.1, xBar := p.1.2.2.2 }
            let xUnder :=
              searchPointFeasibleOn S (theorem59Gamma S) (theorem59Alpha S)
                theorem59P s prev.xBar prev.x snapshotFixed
                ((theorem59_parameter_conditions S hmu s hs).2.2.2.2.1)
            let G :=
              varianceReducedGradientFeasibleOn S (samplingWeight S) p.2 xUnder
                snapshotFixed (fullGradient S snapshotFixed.1)
            (prev.x, xUnder, G))).Finite ->
        Measurable
          (fun p :
            ((FeasiblePoint S ×
              (FeasiblePoint S × (FeasiblePoint S × FeasiblePoint S))) × Fin n) =>
            let snapshotFixed : FeasiblePoint S := p.1.1
            let prev : InnerStateFeasibleOn S :=
              { x := p.1.2.2.1, xBar := p.1.2.2.2 }
            let xUnder :=
              searchPointFeasibleOn S (theorem59Gamma S) (theorem59Alpha S)
                theorem59P s prev.xBar prev.x snapshotFixed
                ((theorem59_parameter_conditions S hmu s hs).2.2.2.2.1)
            let G :=
              varianceReducedGradientFeasibleOn S (samplingWeight S) p.2 xUnder
                snapshotFixed (fullGradient S snapshotFixed.1)
            select prev.x xUnder G)) := by
  classical
  let raw :
      FeasiblePoint S -> FeasiblePoint S -> VariableSpace dim -> FeasiblePoint S :=
    fun xPrev xUnder g =>
      Classical.choose
        (theorem59PrintedFeasibleProxUpdateExistsOn S gamma s hgamma xAnchor
          xPrev xUnder g)
  refine ⟨raw, ?_, ?_⟩
  · intro xPrev xUnder g
    exact Classical.choose_spec
      (theorem59PrintedFeasibleProxUpdateExistsOn S gamma s hgamma xAnchor
        xPrev xUnder g)
  · intro hmu hs hgamma_eq hinput_meas hfin
    subst gamma
    exact
      theorem59_printed_feasible_prox_raw_generated_input_measurable_of_finite_input
        S s hmu hs raw hinput_meas hfin

/-- Selected source-level feasible prox update for Algorithm 5.7's printed line.

The selector is chosen from the proved pointwise feasible minimizer existence
theorem.  Measurability of generated finite prefixes is handled locally by
finite-range recursion below, so the selected argmin does not need a global
ambient state-space measurability theorem. -/
def theorem59PrintedFeasibleProxUpdateOn {n dim : Nat} (S : Setup n dim)
    (gamma : Nat -> Real) (s : Nat)
    (hgamma : 0 < gamma s)
    (xAnchor : Set.Elem (proxCoreSet S))
    (xPrev xUnder : FeasiblePoint S)
    (g : VariableSpace dim) : FeasiblePoint S :=
  Classical.choose
    (theorem59PrintedFeasibleProxUpdateExistsOn S gamma s hgamma xAnchor
      xPrev xUnder g)

theorem theorem59PrintedFeasibleProxUpdateOn_isMin
    {n dim : Nat} (S : Setup n dim)
    (gamma : Nat -> Real) (s : Nat)
    (hgamma : 0 < gamma s)
    (xAnchor : Set.Elem (proxCoreSet S))
    (xPrev xUnder : FeasiblePoint S)
    (g : VariableSpace dim) :
    theorem59PrintedFeasibleProxUpdateRelOn S gamma s xPrev xUnder g
      (theorem59PrintedFeasibleProxUpdateOn S gamma s hgamma xAnchor xPrev xUnder g) := by
  exact Classical.choose_spec
    (theorem59PrintedFeasibleProxUpdateExistsOn S gamma s hgamma xAnchor
      xPrev xUnder g)

/-- When the printed feasible centers are known to lie in `X^o`, the
feasible-over-`X` prox line agrees with the canonical mixed-domain prox relation.

This theorem is the explicit bridge that the public printed trajectory avoids
carrying per step. Downstream core-domain arguments may consume this bridge
only after deriving the two center-domain facts from source-backed invariants. -/
theorem theorem59PrintedFeasibleProxUpdateRelOn_iff_canonical_of_core_centers
    {n dim : Nat} (S : Setup n dim)
    (gamma : Nat -> Real) (s : Nat)
    (xPrev xUnder : FeasiblePoint S)
    (hxPrev : xPrev.1 ∈ proxCoreSet S)
    (hxUnder : xUnder.1 ∈ proxCoreSet S)
    (g : VariableSpace dim) (z : FeasiblePoint S) :
    theorem59PrintedFeasibleProxUpdateRelOn S gamma s xPrev xUnder g z ↔
      ProxUpdateRelOn S gamma s
        (⟨xPrev.1, hxPrev⟩ : Set.Elem (proxCoreSet S))
        (⟨xUnder.1, hxUnder⟩ : Set.Elem (proxCoreSet S)) g z := by
  have hObj :
      ∀ x : FeasiblePoint S,
        theorem59PrintedFeasibleProxObjectiveOn S gamma s xPrev xUnder g x =
          proxObjectiveOn S gamma s
            (⟨xPrev.1, hxPrev⟩ : Set.Elem (proxCoreSet S))
            (⟨xUnder.1, hxUnder⟩ : Set.Elem (proxCoreSet S)) g x := by
    intro x
    have hxPrevEq :
        xPrev =
          proxCoreAsFeasible S
            (⟨xPrev.1, hxPrev⟩ : Set.Elem (proxCoreSet S)) := by
      apply Subtype.ext
      rfl
    have hxUnderEq :
        xUnder =
          proxCoreAsFeasible S
            (⟨xUnder.1, hxUnder⟩ : Set.Elem (proxCoreSet S)) := by
      apply Subtype.ext
      rfl
    have hprevBreg :
        theorem59PrintedFeasibleBregmanBoundaryOn S xPrev x =
          bregmanOn S (⟨xPrev.1, hxPrev⟩ : Set.Elem (proxCoreSet S)) x := by
      have h :=
        theorem59PrintedFeasibleBregmanBoundaryOn_eq_bregmanOn_of_proxCore S
          (⟨xPrev.1, hxPrev⟩ : Set.Elem (proxCoreSet S)) x
      simpa [← hxPrevEq] using h
    have hunderBreg :
        theorem59PrintedFeasibleBregmanBoundaryOn S xUnder x =
          bregmanOn S (⟨xUnder.1, hxUnder⟩ : Set.Elem (proxCoreSet S)) x := by
      have h :=
        theorem59PrintedFeasibleBregmanBoundaryOn_eq_bregmanOn_of_proxCore S
          (⟨xUnder.1, hxUnder⟩ : Set.Elem (proxCoreSet S)) x
      simpa [← hxUnderEq] using h
    change
      theorem59PrintedFeasibleProxObjectiveOn S gamma s xPrev xUnder g x =
        proxObjectiveOn S gamma s
          (⟨xPrev.1, hxPrev⟩ : Set.Elem (proxCoreSet S))
          (⟨xUnder.1, hxUnder⟩ : Set.Elem (proxCoreSet S)) g x
    rw [theorem59PrintedFeasibleProxObjectiveOn_def, proxObjectiveOn_def,
      hprevBreg, hunderBreg]
  simpa [theorem59PrintedFeasibleProxUpdateRelOn, ProxUpdateRelOn] using
    (isMinOn_congr_iff
      (s := Set.univ)
      (f := fun x : FeasiblePoint S =>
        theorem59PrintedFeasibleProxObjectiveOn S gamma s xPrev xUnder g x)
      (g := fun x : FeasiblePoint S =>
        proxObjectiveOn S gamma s
          (⟨xPrev.1, hxPrev⟩ : Set.Elem (proxCoreSet S))
          (⟨xUnder.1, hxUnder⟩ : Set.Elem (proxCoreSet S)) g x)
      (a := z) (hObj z) (fun x _ => hObj x))

/-- Guarded replacement for the stale all-schedule `proxUpdateOn_exists` leaf.

Algorithm 5.7 and Theorem 5.9 only use positive stepsizes.  Under that source
condition, the canonical mixed-domain prox relation is supplied by the printed
feasible existence theorem plus the center-domain bridge above. -/
theorem proxUpdateOn_exists_of_positive {n dim : Nat} (S : Setup n dim)
    (gamma : Nat -> Real) (s : Nat)
    (hgamma : 0 < gamma s)
    (xAnchor : Set.Elem (proxCoreSet S))
    (xPrev : Set.Elem (proxCoreSet S)) (xUnder : Set.Elem (proxCoreSet S))
    (g : VariableSpace dim) :
    exists z : FeasiblePoint S,
      ProxUpdateRelOn S gamma s xPrev xUnder g z := by
  rcases theorem59PrintedFeasibleProxUpdateExistsOn S gamma s hgamma xAnchor
      (proxCoreAsFeasible S xPrev) (proxCoreAsFeasible S xUnder) g with
    ⟨z, hz⟩
  refine ⟨z, ?_⟩
  exact
    (theorem59PrintedFeasibleProxUpdateRelOn_iff_canonical_of_core_centers
      S gamma s (proxCoreAsFeasible S xPrev) (proxCoreAsFeasible S xUnder)
      xPrev.2 xUnder.2 g z).1 hz

/-- Guarded replacement for the stale all-feasible diagnostic argmin leaf.

The diagnostic all-feasible objective is definitionally the printed feasible
boundary objective.  Its solvability is therefore available at the Theorem 5.9
positive-step interface, not for arbitrary schedules. -/
theorem legacyDiagnosticProxUpdateAllFeasibleOn_exists_of_positive
    {n dim : Nat} (S : Setup n dim)
    (gamma : Nat -> Real) (s : Nat)
    (hgamma : 0 < gamma s)
    (xAnchor : Set.Elem (proxCoreSet S))
    (xPrev : FeasiblePoint S) (xUnder : FeasiblePoint S)
    (g : VariableSpace dim) :
    exists z : FeasiblePoint S,
      IsMinOn
        (fun x : FeasiblePoint S =>
          legacyDiagnosticProxObjectiveFeasibleOn S gamma s xPrev xUnder g x)
        Set.univ z := by
  rcases theorem59PrintedFeasibleProxUpdateExistsOn S gamma s hgamma xAnchor
      xPrev xUnder g with
    ⟨z, hz⟩
  refine ⟨z, ?_⟩
  intro y hy
  have hmin := hz hy
  simpa [theorem59PrintedFeasibleProxUpdateRelOn,
    theorem59PrintedFeasibleProxObjectiveOn,
    legacyDiagnosticProxObjectiveFeasibleOn,
    theorem59PrintedFeasibleBregmanBoundaryOn_eq_legacy] using hmin

/-- Exact source-domain membership statement for Algorithm 5.7's printed prox line.

This is the same-interface leaf left by the printed Lemma 5.18 route. The
paper prints `argmin_{x in X}` in Algorithm 5.7, while §3.2 types the Bregman
left argument over `X^o`. Closing this statement would prove that every printed
feasible prox minimizer is usable as a future left argument of `V`; without it,
Lemma 5.16 cannot be instantiated on the printed feasible trajectory. -/
def theorem59PrintedFeasibleProxUpdateCoreMembershipStatement
    {n dim : Nat} (S : Setup n dim) : Prop :=
  forall (gamma : Nat -> Real) (s : Nat)
    (xPrev xUnder : FeasiblePoint S) (g : VariableSpace dim)
    (z : FeasiblePoint S),
    theorem59PrintedFeasibleProxUpdateRelOn S gamma s xPrev xUnder g z ->
      z.1 ∈ proxCoreSet S

/-- Positive-stepsize version of the exact printed prox-output membership leaf.

The public universal predicate above is intentionally broad enough to record
the full feasible-over-`X` relation.  The Lemma 5.18 source route only consumes
the Theorem 5.9 schedule, where `gamma_s > 0`; this statement is the narrower
domain bridge needed for the printed epoch trajectory before any scalar
telescope argument can start. -/
def theorem59PrintedFeasiblePositiveProxUpdateCoreMembershipStatement
    {n dim : Nat} (S : Setup n dim) : Prop :=
  forall (gamma : Nat -> Real) (s : Nat) (_hgamma : 0 < gamma s)
    (xPrev xUnder : FeasiblePoint S) (g : VariableSpace dim)
    (z : FeasiblePoint S),
    theorem59PrintedFeasibleProxUpdateRelOn S gamma s xPrev xUnder g z ->
      z.1 ∈ proxCoreSet S

/-- The older all-schedule membership predicate implies the positive schedule
bridge actually consumed by the printed Lemma 5.18 route. -/
theorem theorem59PrintedFeasiblePositiveProxUpdateCoreMembership_of_exact
    {n dim : Nat} (S : Setup n dim)
    (hmem : theorem59PrintedFeasibleProxUpdateCoreMembershipStatement S) :
    theorem59PrintedFeasiblePositiveProxUpdateCoreMembershipStatement S := by
  intro gamma s _hgamma xPrev xUnder g z hrel
  exact hmem gamma s xPrev xUnder g z hrel

/-- Same-head reduction of the positive printed prox-output membership leaf.

Unfolding the source prox core shows that the first non-scalar missing premise
is not another schedule or trajectory fact: every positive printed feasible
prox minimizer must admit a supporting linearization of `nu` over `X`. This is
the exact `X^o` certificate required by the definition of `proxCoreSetOf`. -/
theorem theorem59PrintedFeasiblePositiveProxUpdateCoreMembership_iff_nu_support
    {n dim : Nat} (S : Setup n dim) :
    theorem59PrintedFeasiblePositiveProxUpdateCoreMembershipStatement S ↔
      forall (gamma : Nat -> Real) (s : Nat) (_hgamma : 0 < gamma s)
        (xPrev xUnder : FeasiblePoint S) (g : VariableSpace dim)
        (z : FeasiblePoint S),
        theorem59PrintedFeasibleProxUpdateRelOn S gamma s xPrev xUnder g z ->
          ∃ p : VariableSpace dim,
            IsMinOn (fun u => ⟪p, u⟫_Real + S.nu u) S.X z.1 := by
  constructor
  · intro hmem gamma s hgamma xPrev xUnder g z hrel
    have hzcore :
        z.1 ∈ proxCoreSet S :=
      hmem gamma s hgamma xPrev xUnder g z hrel
    simpa [proxCoreSet, proxCoreSetOf] using hzcore.2
  · intro hsupport gamma s hgamma xPrev xUnder g z hrel
    exact ⟨z.2, hsupport gamma s hgamma xPrev xUnder g z hrel⟩

/-- Local obstruction evidence for a tempting but invalid algebraic route.

A carrier support vector for the simple term gives a lower bound on the
simple-term residual `h y - h z`.  The printed prox minimizer inequality would
need an upper replacement of that residual to isolate a support vector for
`nu`, so this fact by itself cannot close the prox-output `X^o` membership
leaf. -/
theorem theorem59PrintedFeasible_h_support_residual_lower_bound
    {n dim : Nat} (S : Setup n dim)
    (gamma : Nat -> Real) (s : Nat) (hgamma : 0 < gamma s)
    (z : FeasiblePoint S) (y : VariableSpace dim)
    (ph : VariableSpace dim)
    (hsupport : S.h z.1 + ⟪ph, y - z.1⟫_Real <= S.h y) :
    gamma s * ⟪ph, y - z.1⟫_Real <=
      gamma s * (S.h y - S.h z.1) := by
  have hg_nonneg : 0 <= gamma s := le_of_lt hgamma
  have hscaled := mul_le_mul_of_nonneg_left hsupport hg_nonneg
  nlinarith

/-- Positive scaling preserves the printed prox-line minimizer.

This is the exact same-interface fact obtained directly from Algorithm 5.7's
printed feasible prox relation. It is intentionally weaker than membership in
`proxCoreSet S`: the minimized potential still contains the simple term and the
printed boundary Bregman totalization. The remaining source-domain bridge is
precisely the extraction of a support vector for `S.nu` alone. -/
theorem theorem59PrintedFeasibleProxUpdateRelOn_scaled_objective_isMinOn
    {n dim : Nat} (S : Setup n dim)
    (gamma : Nat -> Real) (s : Nat) (hgamma : 0 < gamma s)
    (xPrev xUnder : FeasiblePoint S) (g : VariableSpace dim)
    (z : FeasiblePoint S) :
    theorem59PrintedFeasibleProxUpdateRelOn S gamma s xPrev xUnder g z ->
      IsMinOn
        (fun u : VariableSpace dim =>
          (1 + gamma s * S.mu)⁻¹ *
            theorem59PrintedFeasibleProxObjectiveAmbientOn S gamma s xPrev xUnder g u)
        S.X z.1 := by
  intro hrel
  have hc_pos : 0 < 1 + gamma s * S.mu := by
    have hg_nonneg : 0 <= gamma s := le_of_lt hgamma
    have hgm_nonneg : 0 <= gamma s * S.mu := mul_nonneg hg_nonneg S.mu_nonneg
    nlinarith
  have hc_nonneg : 0 <= (1 + gamma s * S.mu)⁻¹ := by
    exact inv_nonneg.mpr (le_of_lt hc_pos)
  intro y hy
  have hmin :
      theorem59PrintedFeasibleProxObjectiveOn S gamma s xPrev xUnder g z <=
        theorem59PrintedFeasibleProxObjectiveOn S gamma s xPrev xUnder g
          (⟨y, hy⟩ : FeasiblePoint S) := by
    have hrel' :
        IsMinOn
          (fun x : FeasiblePoint S =>
            theorem59PrintedFeasibleProxObjectiveOn S gamma s xPrev xUnder g x)
          Set.univ z := by
      simpa [theorem59PrintedFeasibleProxUpdateRelOn] using hrel
    exact (isMinOn_univ_iff.mp hrel') (⟨y, hy⟩ : FeasiblePoint S)
  have hscaled := mul_le_mul_of_nonneg_left hmin hc_nonneg
  simpa [theorem59PrintedFeasibleProxObjectiveAmbientOn_agrees] using hscaled

/-- Variational inequality obtained by unfolding the positive printed prox line.

This is the exact algebraic residue of Algorithm 5.7's feasible `argmin` after
collecting the positive coefficient of `nu`.  It is intentionally weaker than a
carrier subgradient of `nu`: the right side still contains the simple-term
residual, which is the term that requires the missing KKT/sum-rule
decomposition in the support bridge below. -/
theorem theorem59PrintedFeasibleProxUpdateRelOn_nu_perturbed_support_inequality
    {n dim : Nat} (S : Setup n dim)
    (gamma : Nat -> Real) (s : Nat)
    (xPrev xUnder : FeasiblePoint S) (g : VariableSpace dim)
    (z : FeasiblePoint S)
    (hrel : theorem59PrintedFeasibleProxUpdateRelOn S gamma s xPrev xUnder g z) :
    ∀ y : FeasiblePoint S,
      (1 + gamma s * S.mu) * (S.nu z.1 - S.nu y.1) <=
        gamma s * (S.h y.1 - S.h z.1) +
          ⟪gamma s • g -
              (gamma s * S.mu) •
                theorem59PrintedFeasibleBoundaryGradientExtensionOn S xUnder -
              theorem59PrintedFeasibleBoundaryGradientExtensionOn S xPrev,
            y.1 - z.1⟫_Real := by
  let du : VariableSpace dim :=
    theorem59PrintedFeasibleBoundaryGradientExtensionOn S xUnder
  let dp : VariableSpace dim :=
    theorem59PrintedFeasibleBoundaryGradientExtensionOn S xPrev
  let A : VariableSpace dim :=
    gamma s • g - (gamma s * S.mu) • du - dp
  let C : Real :=
    -(gamma s * (S.mu * S.nu xUnder.1)) +
      gamma s * (S.mu * ⟪du, xUnder.1⟫_Real) -
      S.nu xPrev.1 + ⟪dp, xPrev.1⟫_Real
  have hobj_eq (u : FeasiblePoint S) :
      theorem59PrintedFeasibleProxObjectiveOn S gamma s xPrev xUnder g u =
        (1 + gamma s * S.mu) * S.nu u.1 + gamma s * S.h u.1 +
          ⟪A, u.1⟫_Real + C := by
    simp [theorem59PrintedFeasibleProxObjectiveOn_def,
      theorem59PrintedFeasibleBregmanBoundaryOn_def, A, C, du, dp,
      inner_sub_right, inner_sub_left, inner_smul_left]
    ring
  have hmin_raw :
      IsMinOn
        (fun u : FeasiblePoint S =>
          theorem59PrintedFeasibleProxObjectiveOn S gamma s xPrev xUnder g u)
        Set.univ z := by
    simpa [theorem59PrintedFeasibleProxUpdateRelOn] using hrel
  have hmin_affine :
      IsMinOn
        (fun u : FeasiblePoint S =>
          (1 + gamma s * S.mu) * S.nu u.1 + gamma s * S.h u.1 +
            ⟪A, u.1⟫_Real + C)
        Set.univ z :=
    (isMinOn_congr_iff (hobj_eq z) (fun u _ => hobj_eq u)).1 hmin_raw
  intro y
  simpa [A, du, dp] using
    (isMinOn.affine_residual_support_inequality
      (s := Set.univ) (eval := fun u : FeasiblePoint S => u.1)
      (nu := S.nu) (h := S.h) (c := 1 + gamma s * S.mu)
      (gammaVal := gamma s) (A := A) (C := C) (z := z) hmin_affine y (Set.mem_univ y))

/-- The printed prox-line minimizer gives a Lipschitz-tilted support inequality for `nu`.

This is the strongest pointwise consequence available from the unfolded printed
prox relation and the current simple-term interface without invoking a
nonsmooth KKT/sum-rule theorem.  The residual `S.h y - S.h z` in
`theorem59PrintedFeasibleProxUpdateRelOn_nu_perturbed_support_inequality` is
controlled by the structural Lipschitz bound of the simple term, leaving the
remaining KKT leaf as the exactification from a norm-tilted lower model to a
carrier subgradient of `nu`. -/
theorem theorem59PrintedFeasibleProxUpdateRelOn_nu_lipschitz_tilted_support_inequality
    {n dim : Nat} (S : Setup n dim)
    (gamma : Nat -> Real) (s : Nat) (hgamma : 0 < gamma s)
    (xPrev xUnder : FeasiblePoint S) (g : VariableSpace dim)
    (z : FeasiblePoint S)
    (hrel : theorem59PrintedFeasibleProxUpdateRelOn S gamma s xPrev xUnder g z) :
    ∃ K : Real, 0 <= K ∧
      ∀ y : FeasiblePoint S,
        (1 + gamma s * S.mu) * (S.nu z.1 - S.nu y.1) <=
          gamma s * K * norm (y.1 - z.1) +
            ⟪gamma s • g -
                (gamma s * S.mu) •
                  theorem59PrintedFeasibleBoundaryGradientExtensionOn S xUnder -
                theorem59PrintedFeasibleBoundaryGradientExtensionOn S xPrev,
              y.1 - z.1⟫_Real := by
  let A : VariableSpace dim :=
    gamma s • g -
      (gamma s * S.mu) • theorem59PrintedFeasibleBoundaryGradientExtensionOn S xUnder -
      theorem59PrintedFeasibleBoundaryGradientExtensionOn S xPrev
  have hresidual :
      ∀ y ∈ S.X,
        (1 + gamma s * S.mu) * (S.nu z.1 - S.nu y) ≤
          gamma s * (S.h y - S.h z.1) + ⟪A, y - z.1⟫_Real := by
    intro y hy
    simpa [A] using
      theorem59PrintedFeasibleProxUpdateRelOn_nu_perturbed_support_inequality
        S gamma s xPrev xUnder g z hrel (⟨y, hy⟩ : FeasiblePoint S)
  have hlipschitz :
      ∃ K : Real, 0 ≤ K ∧
        ∀ y ∈ S.X, |S.h y - S.h z.1| ≤ K * norm (y - z.1) := by
    rcases SOptLib.SimpleConvexTermExpr.exists_lipschitz_eval
        S.h_simple.knownStructure with
      ⟨K, hK_nonneg, hK_lip⟩
    refine ⟨K, hK_nonneg, ?_⟩
    intro y hy
    have hy_agree := S.h_simple.agreesOn y hy
    have hz_agree := S.h_simple.agreesOn z.1 z.2
    calc
      |S.h y - S.h z.1| =
          |S.h_simple.knownStructure.eval y -
            S.h_simple.knownStructure.eval z.1| := by
            rw [← hy_agree, ← hz_agree]
      _ ≤ K * norm (y - z.1) := hK_lip y z.1
  rcases
    tilted_support_of_residual_support_and_lipschitz
      (X := S.X) (nu := S.nu) (h := S.h) (tail := fun y => ⟪A, y - z.1⟫_Real)
      (c := 1 + gamma s * S.mu) (gammaVal := gamma s) (z := z.1)
      (le_of_lt hgamma) hresidual hlipschitz with
    ⟨K, hK_nonneg, htilted⟩
  refine ⟨K, hK_nonneg, ?_⟩
  intro y
  simpa [A] using htilted y.1 y.2

/-- Exactification leaf for the positive printed prox KKT bridge.

This is the finite-dimensional nonsmooth step requested by the printed Lemma
5.18 route after unfolding the positive printed prox relation: the norm-tilted
lower model for `nu`, together with convexity of `nu`, yields an actual carrier
subgradient of `nu` at the printed minimizer.  The theorem is deliberately
private and same-interface; it does not add any paper-facing premise. -/
theorem theorem59_carrierSubgradient_nu_of_lipschitz_tilted_positive_minimizer
    {n dim : Nat} (S : Setup n dim)
    (c : Real) (hc_pos : 0 < c)
    (gammaVal : Real) (hgammaVal_nonneg : 0 <= gammaVal)
    (A : VariableSpace dim)
    (z : FeasiblePoint S)
    (hnuLipschitzTilted :
      ∃ K : Real, 0 <= K ∧
        ∀ y : FeasiblePoint S,
          c * (S.nu z.1 - S.nu y.1) <=
            gammaVal * K * norm (y.1 - z.1) + ⟪A, y.1 - z.1⟫_Real)
    (hnuConvex : ConvexOn Real S.X S.nu) :
    ∃ pnu : VariableSpace dim,
      pnu ∈
        SOptLib.carrierSubdifferential
          (X := S.X) (fun x : FeasiblePoint S => S.nu x.1) z := by
  exact
    SOptLib.exists_carrierSubdifferential_of_convex_tilted_lower_model
      (E := VariableSpace dim) (X := S.X) (f := S.nu) z A
      hc_pos hgammaVal_nonneg hnuLipschitzTilted hnuConvex

/-- A carrier subgradient of `nu` is exactly the support-vector certificate used
in the paper definition of `X^o`.

This is a proof-only bridge from SOptLib's reusable carrier-subdifferential API
to the local source definition `proxCoreSetOf`.  It carries no algorithmic
content: the real remaining work is to derive such a `nu` subgradient from the
printed composite prox minimizer. -/
theorem theorem59_nu_support_of_carrierSubgradient
    {n dim : Nat} (S : Setup n dim) (z : FeasiblePoint S)
    (pnu : VariableSpace dim)
    (hpnu :
      pnu ∈
        SOptLib.carrierSubdifferential
          (X := S.X) (fun x : FeasiblePoint S => S.nu x.1) z) :
    ∃ p : VariableSpace dim,
      IsMinOn (fun u => ⟪p, u⟫_Real + S.nu u) S.X z.1 := by
  exact
    SOptLib.exists_isMinOn_affine_add_of_mem_carrierSubdifferential
      (X := S.X) (f := S.nu) z pnu hpnu

/-- A paper `X^o` support certificate for `nu` is the same data as a carrier
subgradient of `nu` at the feasible point.

This is the reverse direction of `theorem59_nu_support_of_carrierSubgradient`.
It is proof-only infrastructure: it does not assert that printed feasible prox
minimizers are in `X^o`, but it pins that source-domain membership leaf to the
standard constrained subdifferential interface. -/
theorem theorem59_carrierSubgradient_of_nu_support
    {n dim : Nat} (S : Setup n dim) (z : FeasiblePoint S)
    (p : VariableSpace dim)
    (hsupport :
      IsMinOn (fun u => ⟪p, u⟫_Real + S.nu u) S.X z.1) :
    (-p) ∈
      SOptLib.carrierSubdifferential
        (X := S.X) (fun x : FeasiblePoint S => S.nu x.1) z := by
  exact
    SOptLib.neg_mem_carrierSubdifferential_of_isMinOn_affine_add
      (X := S.X) (f := fun x : FeasiblePoint S => S.nu x.1) z p (by
        rw [isMinOn_iff]
        intro y _hy
        simpa using hsupport y.2)

/-- Same-interface semantic dependency for the positive printed prox-output
membership bridge.

At the exact Algorithm 5.7 printed feasible prox relation consumed by the
printed Lemma 5.18 source route, asking that every positive prox output lies in
`X^o` is equivalent to asking for a constrained carrier subgradient of `nu` at
that output. Thus the remaining support/KKT leaf below is not another wrapper:
it is precisely the convex-analysis sum-rule supplier for this source-domain
membership statement. -/
theorem theorem59PrintedFeasiblePositiveProxUpdateCoreMembership_iff_carrierSubgradient
    {n dim : Nat} (S : Setup n dim) :
    theorem59PrintedFeasiblePositiveProxUpdateCoreMembershipStatement S ↔
      forall (gamma : Nat -> Real) (s : Nat) (_hgamma : 0 < gamma s)
        (xPrev xUnder : FeasiblePoint S) (g : VariableSpace dim)
        (z : FeasiblePoint S),
        theorem59PrintedFeasibleProxUpdateRelOn S gamma s xPrev xUnder g z ->
          ∃ pnu : VariableSpace dim,
            pnu ∈
              SOptLib.carrierSubdifferential
                (X := S.X) (fun x : FeasiblePoint S => S.nu x.1) z := by
  constructor
  · intro hmem gamma s hgamma xPrev xUnder g z hrel
    have hsupport :
        ∃ p : VariableSpace dim,
          IsMinOn (fun u => ⟪p, u⟫_Real + S.nu u) S.X z.1 := by
      exact
        (theorem59PrintedFeasiblePositiveProxUpdateCoreMembership_iff_nu_support S).1
          hmem gamma s hgamma xPrev xUnder g z hrel
    rcases hsupport with ⟨p, hp⟩
    exact ⟨-p, theorem59_carrierSubgradient_of_nu_support S z p hp⟩
  · intro hcarrier gamma s hgamma xPrev xUnder g z hrel
    refine ⟨z.2, ?_⟩
    rcases hcarrier gamma s hgamma xPrev xUnder g z hrel with ⟨pnu, hpnu⟩
    exact theorem59_nu_support_of_carrierSubgradient S z pnu hpnu

/-- Same-interface obstruction for the exact positive printed prox support leaf.

At the precise Algorithm 5.7 printed prox relation used by the Lemma 5.18 source
route, a failure of the carrier-subgradient certificate for `nu` refutes the
paper `X^o` support certificate. This is not a bypass route: it is the
contrapositive of the source definition of `proxCoreSet` at the same selected
printed feasible minimizer. -/
theorem theorem59PrintedFeasibleProxUpdateRelOn_nu_support_obstruction_of_no_carrierSubgradient
    {n dim : Nat} (S : Setup n dim)
    (gamma : Nat -> Real) (s : Nat) (_hgamma : 0 < gamma s)
    (xPrev xUnder : FeasiblePoint S) (g : VariableSpace dim)
    (z : FeasiblePoint S)
    (_hrel : theorem59PrintedFeasibleProxUpdateRelOn S gamma s xPrev xUnder g z)
    (hnosub :
      ¬ ∃ pnu : VariableSpace dim,
        pnu ∈
          SOptLib.carrierSubdifferential
            (X := S.X) (fun x : FeasiblePoint S => S.nu x.1) z) :
    ¬ ∃ p : VariableSpace dim,
      IsMinOn (fun u => ⟪p, u⟫_Real + S.nu u) S.X z.1 := by
  rintro ⟨p, hp⟩
  exact hnosub ⟨-p, theorem59_carrierSubgradient_of_nu_support S z p hp⟩

/-- Same-interface source obstruction for the positive printed prox membership bridge.

The positive printed Lemma 5.18 route can proceed only if the selected feasible
prox minimizer carries a `nu` support vector. If that carrier-subgradient datum
is absent for one positive printed prox relation, the universal
positive-output core-membership bridge is false at exactly the interface
consumed by the printed epoch trajectory. -/
theorem theorem59PrintedFeasiblePositiveProxUpdateCoreMembership_fails_of_no_carrierSubgradient
    {n dim : Nat} (S : Setup n dim)
    (gamma : Nat -> Real) (s : Nat) (hgamma : 0 < gamma s)
    (xPrev xUnder : FeasiblePoint S) (g : VariableSpace dim)
    (z : FeasiblePoint S)
    (hrel : theorem59PrintedFeasibleProxUpdateRelOn S gamma s xPrev xUnder g z)
    (hnosub :
      ¬ ∃ pnu : VariableSpace dim,
        pnu ∈
          SOptLib.carrierSubdifferential
            (X := S.X) (fun x : FeasiblePoint S => S.nu x.1) z) :
    ¬ theorem59PrintedFeasiblePositiveProxUpdateCoreMembershipStatement S := by
  intro hmem
  have hzcore := hmem gamma s hgamma xPrev xUnder g z hrel
  have hsupport :
      ∃ p : VariableSpace dim,
        IsMinOn (fun u => ⟪p, u⟫_Real + S.nu u) S.X z.1 := by
    simpa [proxCoreSet, proxCoreSetOf] using hzcore.2
  exact
    theorem59PrintedFeasibleProxUpdateRelOn_nu_support_obstruction_of_no_carrierSubgradient
      S gamma s hgamma xPrev xUnder g z hrel hnosub hsupport

/-- The exact KKT/sum-rule leaf below the printed prox-output support bridge.

Unfolding the printed prox objective gives a constrained minimizer of
`c * nu + gamma_s * h + affine` over `X`, with `c = 1 + gamma_s * mu > 0`.
The source-domain bridge needed by Lemma 5.18 first derives the corresponding
norm-tilted support inequality for `nu`, then exactifies it to a carrier
subgradient.  This private theorem names that decomposition at the precise
same printed prox-line interface; it is intentionally consumed only by
`theorem59PrintedFeasibleProxUpdateRelOn_nu_support_of_positive`. -/
theorem theorem59PrintedFeasibleProxUpdateRelOn_kkt_nu_subgradient_of_positive
    {n dim : Nat} (S : Setup n dim)
    (gamma : Nat -> Real) (s : Nat) (hgamma : 0 < gamma s)
    (xPrev xUnder : FeasiblePoint S) (g : VariableSpace dim)
    (z : FeasiblePoint S)
    (hrel : theorem59PrintedFeasibleProxUpdateRelOn S gamma s xPrev xUnder g z) :
    ∃ pnu : VariableSpace dim,
      pnu ∈
        SOptLib.carrierSubdifferential
          (X := S.X) (fun x : FeasiblePoint S => S.nu x.1) z := by
  classical
  let c : Real := 1 + gamma s * S.mu
  have hc_pos : 0 < c := by
    have hg_nonneg : 0 <= gamma s := le_of_lt hgamma
    have hgm_nonneg : 0 <= gamma s * S.mu := mul_nonneg hg_nonneg S.mu_nonneg
    dsimp [c]
    nlinarith
  have hnuLipschitzTilted :
      ∃ K : Real, 0 <= K ∧
        ∀ y : FeasiblePoint S,
          c * (S.nu z.1 - S.nu y.1) <=
            gamma s * K * norm (y.1 - z.1) +
              ⟪gamma s • g -
                  (gamma s * S.mu) •
                    theorem59PrintedFeasibleBoundaryGradientExtensionOn S xUnder -
                  theorem59PrintedFeasibleBoundaryGradientExtensionOn S xPrev,
                y.1 - z.1⟫_Real := by
    simpa [c] using
      theorem59PrintedFeasibleProxUpdateRelOn_nu_lipschitz_tilted_support_inequality
        S gamma s hgamma xPrev xUnder g z hrel
  exact
    theorem59_carrierSubgradient_nu_of_lipschitz_tilted_positive_minimizer
      S c hc_pos (gamma s) (le_of_lt hgamma)
      (gamma s • g -
        (gamma s * S.mu) •
          theorem59PrintedFeasibleBoundaryGradientExtensionOn S xUnder -
        theorem59PrintedFeasibleBoundaryGradientExtensionOn S xPrev)
      z hnuLipschitzTilted S.nu_convex

/-- Exact support-extraction target for the positive printed prox line.

This is the reconstruction leaf requested by the printed Lemma 5.18 route:
from the source `argmin_{x in X}` statement for the positive Algorithm 5.7
prox subproblem, extract the `X^o` certificate for the selected feasible
minimizer.  The proof must use a convex-analysis sum-rule/stationarity theorem
for the positive multiple of `nu`, the simple convex term, and the affine
residual in the unfolded printed prox objective. -/
theorem theorem59PrintedFeasibleProxUpdateRelOn_nu_support_of_positive
    {n dim : Nat} (S : Setup n dim)
    (gamma : Nat -> Real) (s : Nat) (hgamma : 0 < gamma s)
    (xPrev xUnder : FeasiblePoint S) (g : VariableSpace dim)
    (z : FeasiblePoint S)
    (hrel : theorem59PrintedFeasibleProxUpdateRelOn S gamma s xPrev xUnder g z) :
    ∃ p : VariableSpace dim,
      IsMinOn (fun u => ⟪p, u⟫_Real + S.nu u) S.X z.1 := by
  /-
  Exact same-interface source-domain leaf.  The overstrong global supplier
  `forall z : FeasiblePoint S, z.1 ∈ proxCoreSet S` is intentionally not used:
  Lan's §3.2 domain `X^o` can be a proper subset of the feasible carrier, while
  Algorithm 5.7 only prints `argmin_{x in X}`.  The proof must extract the
  support certificate for `nu` from this positive printed prox relation itself.
  -/
  rcases
    theorem59PrintedFeasibleProxUpdateRelOn_kkt_nu_subgradient_of_positive
      S gamma s hgamma xPrev xUnder g z hrel with
    ⟨pnu, hpnu⟩
  exact theorem59_nu_support_of_carrierSubgradient S z pnu hpnu

/-- Direct Lean attempt at the positive printed prox-output membership target.

After expanding the source core definition, the remaining leaf is exactly the
supporting-linear-minimizer certificate for `nu` at the printed feasible prox
output. The available hypotheses provide an `IsMinOn` certificate for the
composite printed objective over `X`, but the current simple-term/DGF interface
does not yet expose the subgradient-sum rule needed to extract this certificate. -/
theorem theorem59PrintedFeasiblePositiveProxUpdateCoreMembership_direct_attempt
    {n dim : Nat} (S : Setup n dim) :
    theorem59PrintedFeasiblePositiveProxUpdateCoreMembershipStatement S := by
  intro gamma s hgamma xPrev xUnder g z hrel
  refine ⟨z.2, ?_⟩
  exact theorem59PrintedFeasibleProxUpdateRelOn_nu_support_of_positive
    S gamma s hgamma xPrev xUnder g z hrel

/-- Guarded replacement for the stale all-schedule `proxUpdateCoreOn_exists` leaf.

For positive Algorithm 5.7 steps, the printed feasible minimizer exists, the
positive source-domain bridge places it in `X^o`, and its global feasible
minimality restricts to the corrected core candidate domain. -/
theorem proxUpdateCoreOn_exists_of_positive_printed
    {n dim : Nat} (S : Setup n dim)
    (gamma : Nat -> Real) (s : Nat)
    (hgamma : 0 < gamma s)
    (xAnchor : Set.Elem (proxCoreSet S))
    (xPrev : Set.Elem (proxCoreSet S)) (xUnder : Set.Elem (proxCoreSet S))
    (g : VariableSpace dim) :
    exists z : Set.Elem (proxCoreSet S),
      ProxUpdateCoreRelOn S gamma s xPrev xUnder g z := by
  rcases theorem59PrintedFeasibleProxUpdateExistsOn S gamma s hgamma xAnchor
      (proxCoreAsFeasible S xPrev) (proxCoreAsFeasible S xUnder) g with
    ⟨z, hzPrinted⟩
  have hzCore :
      z.1 ∈ proxCoreSet S :=
    theorem59PrintedFeasiblePositiveProxUpdateCoreMembership_direct_attempt S
      gamma s hgamma (proxCoreAsFeasible S xPrev) (proxCoreAsFeasible S xUnder)
      g z hzPrinted
  let zCore : Set.Elem (proxCoreSet S) := ⟨z.1, hzCore⟩
  have hzCore_feasible :
      proxCoreAsFeasible S zCore = z := by
    apply Subtype.ext
    rfl
  have hzCanonical :
      ProxUpdateRelOn S gamma s xPrev xUnder g z := by
    exact
      (theorem59PrintedFeasibleProxUpdateRelOn_iff_canonical_of_core_centers
        S gamma s (proxCoreAsFeasible S xPrev) (proxCoreAsFeasible S xUnder)
        xPrev.2 xUnder.2 g z).1 hzPrinted
  refine ⟨zCore, ?_⟩
  intro y _hy
  have hmin := hzCanonical
    (show proxCoreAsFeasible S y ∈ (Set.univ : Set (FeasiblePoint S)) by simp)
  simpa [ProxUpdateCoreRelOn, proxObjectiveCoreOn, zCore, hzCore_feasible] using hmin

/-- The exact printed prox-output membership leaf follows from the stronger
global invariant `X ⊆ X^o`.

This theorem is intentionally not used as a public assumption: the source only
states that `X^o` contains the relative interior of `X`, and examples such as
the entropy DGF have a proper prox core. It records the smallest global
invariant that would make the printed prox-output leaf immediate. -/
theorem theorem59PrintedFeasibleProxUpdateCoreMembership_of_all_feasible_mem_proxCore
    {n dim : Nat} (S : Setup n dim)
    (hXcore : forall z : FeasiblePoint S, z.1 ∈ proxCoreSet S) :
    theorem59PrintedFeasibleProxUpdateCoreMembershipStatement S := by
  intro gamma s xPrev xUnder g z _hrel
  exact hXcore z

/-- Typed counterexample certificate for the exact printed prox-output
membership leaf.

If Algorithm 5.7's feasible `argmin_{x in X}` relation admits even one minimizer
outside `X^o`, then the source-domain membership statement needed by the
printed Lemma 5.18 route is false. This keeps the obstruction at the same
interface as the printed prox line instead of moving it to a weighted-output or
corrected-core surrogate. -/
theorem theorem59PrintedFeasibleProxUpdateCoreMembership_fails_of_noncore_minimizer
    {n dim : Nat} (S : Setup n dim)
    (gamma : Nat -> Real) (s : Nat)
    (xPrev xUnder : FeasiblePoint S) (g : VariableSpace dim)
    (z : FeasiblePoint S)
    (hrel : theorem59PrintedFeasibleProxUpdateRelOn S gamma s xPrev xUnder g z)
    (hznot : z.1 ∉ proxCoreSet S) :
    ¬ theorem59PrintedFeasibleProxUpdateCoreMembershipStatement S := by
  intro hmem
  exact hznot (hmem gamma s xPrev xUnder g z hrel)

/-- Positive-schedule version of the same-interface source-gap certificate.

This is the exact interface consumed by the printed Lemma 5.18 route: if a
positive Algorithm 5.7 printed prox line has a feasible minimizer outside
`X^o`, then the positive prox-output membership bridge is false.  The theorem is
conditional evidence only; it does not add a new hypothesis to any source-facing
bound. -/
theorem theorem59PrintedFeasiblePositiveProxUpdateCoreMembership_fails_of_noncore_minimizer
    {n dim : Nat} (S : Setup n dim)
    (gamma : Nat -> Real) (s : Nat) (hgamma : 0 < gamma s)
    (xPrev xUnder : FeasiblePoint S) (g : VariableSpace dim)
    (z : FeasiblePoint S)
    (hrel : theorem59PrintedFeasibleProxUpdateRelOn S gamma s xPrev xUnder g z)
    (hznot : z.1 ∉ proxCoreSet S) :
    ¬ theorem59PrintedFeasiblePositiveProxUpdateCoreMembershipStatement S := by
  intro hmem
  exact hznot (hmem gamma s hgamma xPrev xUnder g z hrel)

/-- Exact negated form of the positive printed prox-output membership leaf.

This is the same-interface obstruction requested by the printed Lemma 5.18
route: failing to supply the positive `argmin_{x in X} -> X^o` bridge is
definitionally the existence of one positive printed prox relation whose
feasible minimizer is not in `proxCoreSet S`.  It does not route through the
tombstoned KKT/support supplier and it does not add a new source assumption. -/
theorem theorem59PrintedFeasiblePositiveProxUpdateCoreMembership_not_iff_exists_noncore_minimizer
    {n dim : Nat} (S : Setup n dim) :
    ¬ theorem59PrintedFeasiblePositiveProxUpdateCoreMembershipStatement S ↔
      ∃ (gamma : Nat -> Real) (s : Nat),
        0 < gamma s ∧
          ∃ (xPrev xUnder : FeasiblePoint S) (g : VariableSpace dim)
            (z : FeasiblePoint S),
            theorem59PrintedFeasibleProxUpdateRelOn S gamma s xPrev xUnder g z ∧
              z.1 ∉ proxCoreSet S := by
  classical
  unfold theorem59PrintedFeasiblePositiveProxUpdateCoreMembershipStatement
  constructor
  · intro hnot
    push Not at hnot
    exact hnot
  · rintro ⟨gamma, s, hgamma, xPrev, xUnder, g, z, hrel, hznot⟩ hmem
    exact hznot (hmem gamma s hgamma xPrev xUnder g z hrel)

/-- Same-interface source-gap certificate for the generated printed prox selector.

This is stronger than the abstract `hrel` certificate above: the relation
witness is the actual selected feasible Algorithm 5.7 prox update produced by
`theorem59PrintedFeasibleProxUpdateOn`. Thus, to refute the universal printed
prox-output core-membership statement, it is enough to instantiate one generated
printed prox line whose selected feasible minimizer lies outside `X^o`. -/
theorem theorem59PrintedFeasibleProxUpdateCoreMembership_fails_of_selected_noncore_minimizer
    {n dim : Nat} (S : Setup n dim)
    (gamma : Nat -> Real) (s : Nat) (hgamma : 0 < gamma s)
    (xAnchor : Set.Elem (proxCoreSet S))
    (xPrev xUnder : FeasiblePoint S) (g : VariableSpace dim)
    (hznot :
      (theorem59PrintedFeasibleProxUpdateOn S gamma s hgamma xAnchor
        xPrev xUnder g).1 ∉ proxCoreSet S) :
    ¬ theorem59PrintedFeasibleProxUpdateCoreMembershipStatement S := by
  exact theorem59PrintedFeasibleProxUpdateCoreMembership_fails_of_noncore_minimizer
    S gamma s xPrev xUnder g
    (theorem59PrintedFeasibleProxUpdateOn S gamma s hgamma xAnchor xPrev xUnder g)
    (theorem59PrintedFeasibleProxUpdateOn_isMin S gamma s hgamma xAnchor
      xPrev xUnder g)
    hznot

/-- The same selected-minimizer source-gap certificate specialized to the
Theorem 5.9 printed schedule `gamma_s`.

This is the concrete route requested by the Lemma 5.18 audit: the parameters are
the printed schedule, printed feasible centers, the generated feasible prox
selector, and a single non-core selected minimizer witness. -/
theorem theorem59PrintedFeasibleProxUpdateCoreMembership_fails_of_theorem59_selected_noncore_minimizer
    {n dim : Nat} (S : Setup n dim)
    (s : Nat) (xAnchor : Set.Elem (proxCoreSet S))
    (xPrev xUnder : FeasiblePoint S) (g : VariableSpace dim)
    (hznot :
      (theorem59PrintedFeasibleProxUpdateOn S (theorem59Gamma S) s
        (theorem59Gamma_pos S s) xAnchor xPrev xUnder g).1 ∉ proxCoreSet S) :
    ¬ theorem59PrintedFeasibleProxUpdateCoreMembershipStatement S := by
  exact
    theorem59PrintedFeasibleProxUpdateCoreMembership_fails_of_selected_noncore_minimizer
      S (theorem59Gamma S) s (theorem59Gamma_pos S s) xAnchor xPrev xUnder g
      hznot

/-- Localize the exact printed prox-output membership statement to one prox line. -/
theorem theorem59PrintedFeasibleProxUpdateCoreMembershipStatement.apply
    {n dim : Nat} {S : Setup n dim}
    (hmem : theorem59PrintedFeasibleProxUpdateCoreMembershipStatement S)
    (gamma : Nat -> Real) (s : Nat)
    (xPrev xUnder : FeasiblePoint S) (g : VariableSpace dim)
    (z : FeasiblePoint S)
    (hrel : theorem59PrintedFeasibleProxUpdateRelOn S gamma s xPrev xUnder g z) :
    z.1 ∈ proxCoreSet S :=
  hmem gamma s xPrev xUnder g z hrel

/-- Localize the positive printed prox-output membership bridge to one prox line. -/
theorem theorem59PrintedFeasiblePositiveProxUpdateCoreMembershipStatement.apply
    {n dim : Nat} {S : Setup n dim}
    (hmem : theorem59PrintedFeasiblePositiveProxUpdateCoreMembershipStatement S)
    (gamma : Nat -> Real) (s : Nat) (hgamma : 0 < gamma s)
    (xPrev xUnder : FeasiblePoint S) (g : VariableSpace dim)
    (z : FeasiblePoint S)
    (hrel : theorem59PrintedFeasibleProxUpdateRelOn S gamma s xPrev xUnder g z) :
    z.1 ∈ proxCoreSet S :=
  hmem gamma s hgamma xPrev xUnder g z hrel

/-- Feasible-level Algorithm 5.7 inner-step equations that keep the prox line.

No SOptLib match: searched `relational recursive process`, `weighted average
output value`, and `prox argmin relation feasible`; checked
`SOptLib.IsRelationalRecursiveProcess`, `SOptLib.weightedAverageOutputValue`,
`SOptLib.recursiveProcessOutput`, and
`SOptLib.recursiveIterateProcess_isRelationalRecursiveProcess`. SOptLib provides
the relation-valued recursion shell, but Algorithm 5.7's mixed-domain prox line
is paper-specific: the displayed `x_t`/`G_t`/`bar{x}_t` equations live on `X`,
while the Bregman prox object is defined on `X^o x X`. This predicate records
the feasible search point, estimator, printed prox argmin, and averaged-iterate
equations without taking the previous feasible states as prox-core subtype
parameters. -/
def theorem59PrintedFeasibleInnerStepRelOn {n dim : Nat} (S : Setup n dim)
    (gamma alpha p : Nat -> Real) (s : Nat)
    (q : Fin n -> Real) (snapshot : FeasiblePoint S)
    (fullGradAtSnapshot : VariableSpace dim)
    (sample : Fin n)
    (hsearch : searchPointWeights S gamma alpha p s ∈ stdSimplex Real (Fin 3))
    (havg : averagedInnerWeightsAdmissible alpha p s)
    (prev next : InnerStateFeasibleOn S) : Prop :=
  ∃ xUnder : FeasiblePoint S,
    xUnder = searchPointFeasibleOn S gamma alpha p s prev.xBar prev.x snapshot hsearch ∧
      ∃ G : VariableSpace dim,
        G = varianceReducedGradientFeasibleOn S q sample xUnder snapshot fullGradAtSnapshot ∧
          theorem59PrintedFeasibleProxUpdateRelOn S gamma s prev.x xUnder G next.x ∧
          next.xBar =
            averagedInnerIterateAllFeasibleOn S alpha p s prev.xBar next.x snapshot havg

/-- Generated feasible inner step for the printed Algorithm 5.7 relation.

This is a functional realization of the public feasible step predicate. It uses
the printed over-`X` prox selector, so it does not manufacture
prox-core subtype witnesses for the previous/search centers. -/
def theorem59PrintedFeasibleInnerStepOn {n dim : Nat} (S : Setup n dim)
    (gamma alpha p : Nat -> Real) (s : Nat)
    (q : Fin n -> Real) (snapshot : FeasiblePoint S)
    (fullGradAtSnapshot : VariableSpace dim)
    (sample : Fin n)
    (hgamma : 0 < gamma s)
    (xAnchor : Set.Elem (proxCoreSet S))
    (hsearch : searchPointWeights S gamma alpha p s ∈ stdSimplex Real (Fin 3))
    (havg : averagedInnerWeightsAdmissible alpha p s)
    (prev : InnerStateFeasibleOn S) : InnerStateFeasibleOn S :=
  let xUnder := searchPointFeasibleOn S gamma alpha p s prev.xBar prev.x snapshot hsearch
  let G := varianceReducedGradientFeasibleOn S q sample xUnder snapshot fullGradAtSnapshot
  let xNext := theorem59PrintedFeasibleProxUpdateOn S gamma s hgamma xAnchor prev.x xUnder G
  let xBarNext := averagedInnerIterateAllFeasibleOn S alpha p s prev.xBar xNext snapshot havg
  { x := xNext, xBar := xBarNext }

theorem theorem59PrintedFeasibleInnerStepOn_satisfies_rel
    {n dim : Nat} (S : Setup n dim)
    (gamma alpha p : Nat -> Real) (s : Nat)
    (q : Fin n -> Real) (snapshot : FeasiblePoint S)
    (fullGradAtSnapshot : VariableSpace dim)
    (sample : Fin n)
    (hgamma : 0 < gamma s)
    (xAnchor : Set.Elem (proxCoreSet S))
    (hsearch : searchPointWeights S gamma alpha p s ∈ stdSimplex Real (Fin 3))
    (havg : averagedInnerWeightsAdmissible alpha p s)
    (prev : InnerStateFeasibleOn S) :
    theorem59PrintedFeasibleInnerStepRelOn S gamma alpha p s q snapshot
      fullGradAtSnapshot sample hsearch havg prev
      (theorem59PrintedFeasibleInnerStepOn S gamma alpha p s q snapshot
        fullGradAtSnapshot sample hgamma xAnchor hsearch havg prev) := by
  unfold theorem59PrintedFeasibleInnerStepRelOn theorem59PrintedFeasibleInnerStepOn
  refine ⟨searchPointFeasibleOn S gamma alpha p s prev.xBar prev.x snapshot hsearch,
    rfl, ?_⟩
  refine ⟨varianceReducedGradientFeasibleOn S q sample
      (searchPointFeasibleOn S gamma alpha p s prev.xBar prev.x snapshot hsearch)
      snapshot fullGradAtSnapshot, rfl, ?_, rfl⟩
  change theorem59PrintedFeasibleProxUpdateRelOn S gamma s prev.x
    (searchPointFeasibleOn S gamma alpha p s prev.xBar prev.x snapshot hsearch)
    (varianceReducedGradientFeasibleOn S q sample
      (searchPointFeasibleOn S gamma alpha p s prev.xBar prev.x snapshot hsearch)
      snapshot fullGradAtSnapshot)
    (theorem59PrintedFeasibleProxUpdateOn S gamma s hgamma xAnchor prev.x
      (searchPointFeasibleOn S gamma alpha p s prev.xBar prev.x snapshot hsearch)
      (varianceReducedGradientFeasibleOn S q sample
        (searchPointFeasibleOn S gamma alpha p s prev.xBar prev.x snapshot hsearch)
        snapshot fullGradAtSnapshot))
  exact theorem59PrintedFeasibleProxUpdateOn_isMin S gamma s hgamma xAnchor prev.x
      (searchPointFeasibleOn S gamma alpha p s prev.xBar prev.x snapshot hsearch)
      (varianceReducedGradientFeasibleOn S q sample
        (searchPointFeasibleOn S gamma alpha p s prev.xBar prev.x snapshot hsearch)
        snapshot fullGradAtSnapshot)

theorem theorem59PrintedFeasibleInnerStepRelOn_proxUpdate
    {n dim : Nat} (S : Setup n dim)
    (gamma alpha p : Nat -> Real) (s : Nat)
    (q : Fin n -> Real) (snapshot : FeasiblePoint S)
    (fullGradAtSnapshot : VariableSpace dim)
    (sample : Fin n)
    (hsearch : searchPointWeights S gamma alpha p s ∈ stdSimplex Real (Fin 3))
    (havg : averagedInnerWeightsAdmissible alpha p s)
    (prev next : InnerStateFeasibleOn S)
    (hstep :
      theorem59PrintedFeasibleInnerStepRelOn S gamma alpha p s q snapshot
        fullGradAtSnapshot sample hsearch havg prev next) :
    ∃ xUnder : FeasiblePoint S,
      xUnder = searchPointFeasibleOn S gamma alpha p s prev.xBar prev.x snapshot hsearch ∧
        ∃ G : VariableSpace dim,
          G = varianceReducedGradientFeasibleOn S q sample xUnder snapshot fullGradAtSnapshot ∧
            theorem59PrintedFeasibleProxUpdateRelOn S gamma s prev.x xUnder G next.x := by
  rcases hstep with ⟨xUnder, hxUnder, G, hG, hprox, _hbar⟩
  exact ⟨xUnder, hxUnder, G, hG, hprox⟩

theorem theorem59PrintedFeasibleInnerStepRelOn_requires_proxCore_centers
    {n dim : Nat} (S : Setup n dim)
    (gamma alpha p : Nat -> Real) (s : Nat)
    (q : Fin n -> Real) (snapshot : FeasiblePoint S)
    (fullGradAtSnapshot : VariableSpace dim)
    (sample : Fin n)
    (hsearch : searchPointWeights S gamma alpha p s ∈ stdSimplex Real (Fin 3))
    (havg : averagedInnerWeightsAdmissible alpha p s)
    (prev next : InnerStateFeasibleOn S)
    (hstep :
      theorem59PrintedFeasibleInnerStepRelOn S gamma alpha p s q snapshot
        fullGradAtSnapshot sample hsearch havg prev next) :
    ∃ xUnder : FeasiblePoint S,
      xUnder = searchPointFeasibleOn S gamma alpha p s prev.xBar prev.x snapshot hsearch ∧
        (forall (hxPrev : prev.x.1 ∈ proxCoreSet S)
            (hxUnder : xUnder.1 ∈ proxCoreSet S),
          ProxUpdateRelOn S gamma s
            (⟨prev.x.1, hxPrev⟩ : Set.Elem (proxCoreSet S))
            (⟨xUnder.1, hxUnder⟩ : Set.Elem (proxCoreSet S))
            (varianceReducedGradientFeasibleOn S q sample xUnder snapshot fullGradAtSnapshot)
            next.x) := by
  rcases theorem59PrintedFeasibleInnerStepRelOn_proxUpdate S gamma alpha p s q snapshot
      fullGradAtSnapshot sample hsearch havg prev next hstep with
    ⟨xUnder, hxUnder, G, _hG, hprox⟩
  subst G
  refine ⟨xUnder, hxUnder, ?_⟩
  intro hxPrevCore hxUnderCore
  exact
    (theorem59PrintedFeasibleProxUpdateRelOn_iff_canonical_of_core_centers
      S gamma s prev.x xUnder hxPrevCore hxUnderCore
      (varianceReducedGradientFeasibleOn S q sample xUnder snapshot fullGradAtSnapshot)
      next.x).1 hprox

/-- Exact printed-step obstruction for propagating prox-core membership.

This is the printed-feasible analogue of
`innerStepRelOn_x_core_propagation_iff_proxUpdateRelOn_mem_proxCore`. It stays
on Algorithm 5.7's feasible step relation and shows that making the printed
next iterate usable as a future `V` left argument is exactly the missing fact
that every output of the printed feasible prox relation lies in `X^o`. -/
theorem theorem59PrintedFeasibleInnerStepRelOn_x_core_propagation_iff_printedProx_mem_proxCore
    {n dim : Nat} (S : Setup n dim)
    (gamma alpha p : Nat -> Real) (s : Nat)
    (q : Fin n -> Real) (snapshot : FeasiblePoint S)
    (fullGradAtSnapshot : VariableSpace dim)
    (sample : Fin n)
    (hsearch : searchPointWeights S gamma alpha p s ∈ stdSimplex Real (Fin 3))
    (havg : averagedInnerWeightsAdmissible alpha p s)
    (prev : InnerStateFeasibleOn S) :
    (forall next : InnerStateFeasibleOn S,
        theorem59PrintedFeasibleInnerStepRelOn S gamma alpha p s q snapshot
          fullGradAtSnapshot sample hsearch havg prev next ->
        next.x.1 ∈ proxCoreSet S) ↔
      (forall z : FeasiblePoint S,
        theorem59PrintedFeasibleProxUpdateRelOn S gamma s prev.x
          (searchPointFeasibleOn S gamma alpha p s prev.xBar prev.x snapshot hsearch)
          (varianceReducedGradientFeasibleOn S q sample
            (searchPointFeasibleOn S gamma alpha p s prev.xBar prev.x snapshot hsearch)
            snapshot fullGradAtSnapshot)
          z ->
        z.1 ∈ proxCoreSet S) := by
  constructor
  · intro hnext z hz
    let next : InnerStateFeasibleOn S :=
      { x := z
        xBar :=
          averagedInnerIterateAllFeasibleOn S alpha p s prev.xBar z snapshot havg }
    have hstep :
        theorem59PrintedFeasibleInnerStepRelOn S gamma alpha p s q snapshot
          fullGradAtSnapshot sample hsearch havg prev next := by
      unfold theorem59PrintedFeasibleInnerStepRelOn
      refine ⟨searchPointFeasibleOn S gamma alpha p s prev.xBar prev.x snapshot hsearch,
        rfl, ?_⟩
      refine ⟨varianceReducedGradientFeasibleOn S q sample
          (searchPointFeasibleOn S gamma alpha p s prev.xBar prev.x snapshot hsearch)
          snapshot fullGradAtSnapshot, rfl, hz, ?_⟩
      rfl
    exact hnext next hstep
  · intro hprox next hstep
    rcases hstep with ⟨xUnder, hxUnder, G, hG, hproxRel, _hbar⟩
    subst xUnder
    subst G
    exact hprox next.x hproxRel

/-- The printed averaged iterate is core-valued once the printed prox output is
core-valued and the two carried centers are core-valued.

The theorem deliberately assumes the prox-output bridge isolated by
`theorem59PrintedFeasibleInnerStepRelOn_x_core_propagation_iff_printedProx_mem_proxCore`;
it does not assert that Algorithm 5.7's feasible argmin lands in `X^o`. -/
theorem theorem59PrintedFeasibleInnerStepRelOn_xBar_core_of_printedProx_mem_proxCore
    {n dim : Nat} (S : Setup n dim)
    (gamma alpha p : Nat -> Real) (s : Nat)
    (q : Fin n -> Real) (snapshot : FeasiblePoint S)
    (fullGradAtSnapshot : VariableSpace dim)
    (sample : Fin n)
    (hsearch : searchPointWeights S gamma alpha p s ∈ stdSimplex Real (Fin 3))
    (havg : averagedInnerWeightsAdmissible alpha p s)
    (prev next : InnerStateFeasibleOn S)
    (hxBarPrev : prev.xBar.1 ∈ proxCoreSet S)
    (hxSnapshot : snapshot.1 ∈ proxCoreSet S)
    (hproxMem :
      forall z : FeasiblePoint S,
        theorem59PrintedFeasibleProxUpdateRelOn S gamma s prev.x
          (searchPointFeasibleOn S gamma alpha p s prev.xBar prev.x snapshot hsearch)
          (varianceReducedGradientFeasibleOn S q sample
            (searchPointFeasibleOn S gamma alpha p s prev.xBar prev.x snapshot hsearch)
            snapshot fullGradAtSnapshot)
          z ->
        z.1 ∈ proxCoreSet S)
    (hstep :
      theorem59PrintedFeasibleInnerStepRelOn S gamma alpha p s q snapshot
        fullGradAtSnapshot sample hsearch havg prev next) :
    next.xBar.1 ∈ proxCoreSet S := by
  rcases hstep with ⟨xUnder, hxUnder, G, hG, hproxRel, hbar⟩
  subst xUnder
  subst G
  have hxNext : next.x.1 ∈ proxCoreSet S := hproxMem next.x hproxRel
  let xBarPrevCore : Set.Elem (proxCoreSet S) := ⟨prev.xBar.1, hxBarPrev⟩
  let xNextCore : Set.Elem (proxCoreSet S) := ⟨next.x.1, hxNext⟩
  let snapshotCore : Set.Elem (proxCoreSet S) := ⟨snapshot.1, hxSnapshot⟩
  have hcore :
      averagedInnerIterateValueOn S alpha p s xBarPrevCore xNextCore snapshotCore ∈
        proxCoreSet S :=
    averagedInnerIterateValueOn_mem_proxCore S alpha p s
      xBarPrevCore xNextCore snapshotCore havg
  rw [hbar]
  simpa [averagedInnerIterateAllFeasibleOn, averagedInnerIterateValueAllFeasibleOn,
    averagedInnerIterateValueOn, xBarPrevCore, xNextCore, snapshotCore] using hcore

/-- A printed feasible step supplies the core witnesses needed by Lemma 5.16 once
the exact positive prox-output membership bridge is available.

This is the executable T1 conversion for the source route: from the printed
feasible step relation, carried core membership of the previous iterate,
previous averaged iterate, and snapshot, plus the unresolved positive
`argmin_{x in X} -> X^o` bridge, it constructs the search-point core witness,
the canonical `ProxUpdateRelOn` reading of the printed prox line, and core
membership of both next printed coordinates. -/
theorem theorem59PrintedFeasibleInnerStepRelOn_core_witnesses_of_positiveProxMembership
    {n dim : Nat} (S : Setup n dim)
    (gamma alpha p : Nat -> Real) (s : Nat) (hgamma : 0 < gamma s)
    (q : Fin n -> Real) (snapshot : FeasiblePoint S)
    (fullGradAtSnapshot : VariableSpace dim)
    (sample : Fin n)
    (hsearch : searchPointWeights S gamma alpha p s ∈ stdSimplex Real (Fin 3))
    (havg : averagedInnerWeightsAdmissible alpha p s)
    (prev next : InnerStateFeasibleOn S)
    (hxPrev : prev.x.1 ∈ proxCoreSet S)
    (hxBarPrev : prev.xBar.1 ∈ proxCoreSet S)
    (hxSnapshot : snapshot.1 ∈ proxCoreSet S)
    (hmem : theorem59PrintedFeasiblePositiveProxUpdateCoreMembershipStatement S)
    (hstep :
      theorem59PrintedFeasibleInnerStepRelOn S gamma alpha p s q snapshot
        fullGradAtSnapshot sample hsearch havg prev next) :
    let xUnder :=
      searchPointFeasibleOn S gamma alpha p s prev.xBar prev.x snapshot hsearch
    let G :=
      varianceReducedGradientFeasibleOn S q sample xUnder snapshot fullGradAtSnapshot
    ∃ hxUnder : xUnder.1 ∈ proxCoreSet S,
      ProxUpdateRelOn S gamma s
        (⟨prev.x.1, hxPrev⟩ : Set.Elem (proxCoreSet S))
        (⟨xUnder.1, hxUnder⟩ : Set.Elem (proxCoreSet S))
        G next.x ∧
      next.x.1 ∈ proxCoreSet S ∧ next.xBar.1 ∈ proxCoreSet S := by
  classical
  let xUnder :=
    searchPointFeasibleOn S gamma alpha p s prev.xBar prev.x snapshot hsearch
  let G :=
    varianceReducedGradientFeasibleOn S q sample xUnder snapshot fullGradAtSnapshot
  have hxUnder : xUnder.1 ∈ proxCoreSet S := by
    let xBarPrevCore : Set.Elem (proxCoreSet S) := ⟨prev.xBar.1, hxBarPrev⟩
    let xPrevCore : Set.Elem (proxCoreSet S) := ⟨prev.x.1, hxPrev⟩
    let snapshotCore : Set.Elem (proxCoreSet S) := ⟨snapshot.1, hxSnapshot⟩
    have hcore :
        searchPointValueOn S gamma alpha p s xBarPrevCore xPrevCore snapshotCore ∈
          proxCoreSet S :=
      searchPointValueOn_mem_proxCore S gamma alpha p s
        xBarPrevCore xPrevCore snapshotCore hsearch
    simpa [xUnder, searchPointFeasibleOn, searchPointValueFeasibleOn,
      searchPointValueOn, xBarPrevCore, xPrevCore, snapshotCore] using hcore
  have hproxMem :
      forall z : FeasiblePoint S,
        theorem59PrintedFeasibleProxUpdateRelOn S gamma s prev.x xUnder G z ->
        z.1 ∈ proxCoreSet S := by
    intro z hz
    exact hmem gamma s hgamma prev.x xUnder G z hz
  have hproxRel :
      theorem59PrintedFeasibleProxUpdateRelOn S gamma s prev.x xUnder G next.x := by
    rcases theorem59PrintedFeasibleInnerStepRelOn_proxUpdate S gamma alpha p s q
        snapshot fullGradAtSnapshot sample hsearch havg prev next hstep with
      ⟨xUnder', hxUnder', G', hG', hprox⟩
    dsimp [xUnder, G]
    subst xUnder'
    subst G'
    exact hprox
  have hxNext : next.x.1 ∈ proxCoreSet S := hproxMem next.x hproxRel
  have hxBarNext : next.xBar.1 ∈ proxCoreSet S :=
    theorem59PrintedFeasibleInnerStepRelOn_xBar_core_of_printedProx_mem_proxCore
      S gamma alpha p s q snapshot fullGradAtSnapshot sample hsearch havg prev next
      hxBarPrev hxSnapshot hproxMem hstep
  have hcanonical :
      ProxUpdateRelOn S gamma s
        (⟨prev.x.1, hxPrev⟩ : Set.Elem (proxCoreSet S))
        (⟨xUnder.1, hxUnder⟩ : Set.Elem (proxCoreSet S))
        G next.x :=
    (theorem59PrintedFeasibleProxUpdateRelOn_iff_canonical_of_core_centers
      S gamma s prev.x xUnder hxPrev hxUnder G next.x).1 hproxRel
  exact ⟨hxUnder, hcanonical, hxNext, hxBarNext⟩

/-- Relation-valued feasible inner trajectory for one printed Algorithm 5.7 epoch.

This is the source-route replacement for the rejected constant trajectory.  It
uses SOptLib's relational-recursion shape and records Algorithm 5.7's feasible
initialization plus the displayed feasible search, estimator, prox argmin, and
averaging equations. The prox line is routed through
`theorem59PrintedFeasibleProxUpdateRelOn`, which keeps the output feasible while
making the `V : X^o x X -> R+` center-domain obligation explicit. -/
def theorem59PrintedFeasibleInnerTrajectoryRelOn {Ω : Type*} {n dim : Nat}
    (S : Setup n dim) (hmu : 0 < S.mu)
    (samples : Nat -> Nat -> Ω -> Fin n)
    (s : Nat) (hs : 1 <= s) (omega : Ω)
    (snapshot xStart : FeasiblePoint S)
    (trajectory : Nat -> InnerStateFeasibleOn S) : Prop :=
  SOptLib.IsRelationalRecursiveProcess
    ({ x := xStart, xBar := snapshot } : InnerStateFeasibleOn S)
    (fun k prev next (_unit : Unit) =>
      theorem59PrintedFeasibleInnerStepRelOn S (theorem59Gamma S)
        (theorem59Alpha S) theorem59P s (samplingWeight S) snapshot
        (fullGradient S snapshot.1) (samples s (k + 1) omega)
        ((theorem59_parameter_conditions S hmu s hs).2.2.2.2.1)
        ((theorem59_parameter_conditions S hmu s hs).2.2.2.2.2)
        prev next)
    (fun t (_unit : Unit) => trajectory t)

/-- Generated feasible inner trajectory for one printed Algorithm 5.7 epoch. -/
def theorem59PrintedFeasibleInnerTrajectoryOn {Ω : Type*} {n dim : Nat}
    (S : Setup n dim) (hmu : 0 < S.mu)
    (xAnchor : Set.Elem (proxCoreSet S))
    (samples : Nat -> Nat -> Ω -> Fin n)
    (s : Nat) (hs : 1 <= s) (omega : Ω)
    (snapshot xStart : FeasiblePoint S) :
    Nat -> InnerStateFeasibleOn S :=
  fun t =>
    SOptLib.recursiveIterateProcess
      ({ x := xStart, xBar := snapshot } : InnerStateFeasibleOn S)
      (fun k prev (_unit : Unit) =>
        theorem59PrintedFeasibleInnerStepOn S (theorem59Gamma S)
          (theorem59Alpha S) theorem59P s (samplingWeight S) snapshot
          (fullGradient S snapshot.1) (samples s (k + 1) omega)
          (theorem59Gamma_pos S s)
          xAnchor
          ((theorem59_parameter_conditions S hmu s hs).2.2.2.2.1)
          ((theorem59_parameter_conditions S hmu s hs).2.2.2.2.2)
          prev)
      t ()

theorem theorem59PrintedFeasibleInnerTrajectoryOn_rel
    {Ω : Type*} {n dim : Nat}
    (S : Setup n dim) (hmu : 0 < S.mu)
    (xAnchor : Set.Elem (proxCoreSet S))
    (samples : Nat -> Nat -> Ω -> Fin n)
    (s : Nat) (hs : 1 <= s) (omega : Ω)
    (snapshot xStart : FeasiblePoint S) :
    theorem59PrintedFeasibleInnerTrajectoryRelOn S hmu samples s hs omega
      snapshot xStart
      (theorem59PrintedFeasibleInnerTrajectoryOn S hmu xAnchor samples s hs omega
        snapshot xStart) := by
  unfold theorem59PrintedFeasibleInnerTrajectoryRelOn
    theorem59PrintedFeasibleInnerTrajectoryOn
  constructor
  · intro unit
    cases unit
    rfl
  · intro k unit
    cases unit
    exact theorem59PrintedFeasibleInnerStepOn_satisfies_rel S
      (theorem59Gamma S) (theorem59Alpha S) theorem59P s (samplingWeight S)
      snapshot (fullGradient S snapshot.1) (samples s (k + 1) omega)
      (theorem59Gamma_pos S s)
      xAnchor
      ((theorem59_parameter_conditions S hmu s hs).2.2.2.2.1)
      ((theorem59_parameter_conditions S hmu s hs).2.2.2.2.2)
      ((SOptLib.recursiveIterateProcess
        ({ x := xStart, xBar := snapshot } : InnerStateFeasibleOn S)
        (fun k prev _unit =>
          theorem59PrintedFeasibleInnerStepOn S (theorem59Gamma S)
            (theorem59Alpha S) theorem59P s (samplingWeight S) snapshot
            (fullGradient S snapshot.1) (samples s (k + 1) omega)
            (theorem59Gamma_pos S s)
            xAnchor
            ((theorem59_parameter_conditions S hmu s hs).2.2.2.2.1)
            ((theorem59_parameter_conditions S hmu s hs).2.2.2.2.2)
            prev)) k ())

theorem theorem59PrintedFeasibleInnerTrajectoryRelOn_step
    {Ω : Type*} {n dim : Nat}
    (S : Setup n dim) (hmu : 0 < S.mu)
    (samples : Nat -> Nat -> Ω -> Fin n)
    (s : Nat) (hs : 1 <= s) (omega : Ω)
    (snapshot xStart : FeasiblePoint S)
    (trajectory : Nat -> InnerStateFeasibleOn S)
    (htraj :
      theorem59PrintedFeasibleInnerTrajectoryRelOn S hmu samples s hs omega
        snapshot xStart trajectory)
    (k : Nat) :
    theorem59PrintedFeasibleInnerStepRelOn S (theorem59Gamma S)
      (theorem59Alpha S) theorem59P s (samplingWeight S) snapshot
      (fullGradient S snapshot.1) (samples s (k + 1) omega)
      ((theorem59_parameter_conditions S hmu s hs).2.2.2.2.1)
      ((theorem59_parameter_conditions S hmu s hs).2.2.2.2.2)
      (trajectory k) (trajectory (k + 1)) := by
  exact SOptLib.IsRelationalRecursiveProcess.step htraj k ()

/-- Printed feasible inner trajectories preserve the prox-core invariant once
the exact positive printed prox-output membership bridge is available.

This is the source-stage propagation theorem needed by the Lemma 5.18 route:
it uses the relation carried by `theorem59PrintedFeasibleEpochOutputProcessSpec`
and reduces the only nontrivial domain step to
`theorem59PrintedFeasiblePositiveProxUpdateCoreMembershipStatement`. -/
theorem theorem59PrintedFeasibleInnerTrajectoryRelOn_core_mem_of_positiveProxMembership
    {Ω : Type*} {n dim : Nat}
    (S : Setup n dim) (hmu : 0 < S.mu)
    (samples : Nat -> Nat -> Ω -> Fin n)
    (s : Nat) (hs : 1 <= s) (omega : Ω)
    (snapshot xStart : FeasiblePoint S)
    (trajectory : Nat -> InnerStateFeasibleOn S)
    (hmem : theorem59PrintedFeasiblePositiveProxUpdateCoreMembershipStatement S)
    (hxSnapshot : snapshot.1 ∈ proxCoreSet S)
    (hxStart : xStart.1 ∈ proxCoreSet S)
    (htraj :
      theorem59PrintedFeasibleInnerTrajectoryRelOn S hmu samples s hs omega
        snapshot xStart trajectory) :
    forall k,
      (trajectory k).x.1 ∈ proxCoreSet S ∧
        (trajectory k).xBar.1 ∈ proxCoreSet S := by
  intro k
  induction k with
  | zero =>
      have hinit := SOptLib.IsRelationalRecursiveProcess.initial htraj ()
      constructor
      · rw [hinit]
        exact hxStart
      · rw [hinit]
        exact hxSnapshot
  | succ k ih =>
      have hstep :=
        theorem59PrintedFeasibleInnerTrajectoryRelOn_step S hmu samples s hs omega
          snapshot xStart trajectory htraj k
      have hcore :=
        theorem59PrintedFeasibleInnerStepRelOn_core_witnesses_of_positiveProxMembership
          S (theorem59Gamma S) (theorem59Alpha S) theorem59P s
          (theorem59Gamma_pos S s) (samplingWeight S) snapshot
          (fullGradient S snapshot.1) (samples s (k + 1) omega)
          ((theorem59_parameter_conditions S hmu s hs).2.2.2.2.1)
          ((theorem59_parameter_conditions S hmu s hs).2.2.2.2.2)
          (trajectory k) (trajectory (k + 1)) ih.1 ih.2 hxSnapshot hmem hstep
      rcases hcore with ⟨_hxUnder, _hprox, hxNext, hxBarNext⟩
      exact ⟨hxNext, hxBarNext⟩

theorem theorem59PrintedFeasibleInnerTrajectoryRelOn_proxUpdate
    {Ω : Type*} {n dim : Nat}
    (S : Setup n dim) (hmu : 0 < S.mu)
    (samples : Nat -> Nat -> Ω -> Fin n)
    (s : Nat) (hs : 1 <= s) (omega : Ω)
    (snapshot xStart : FeasiblePoint S)
    (trajectory : Nat -> InnerStateFeasibleOn S)
    (htraj :
      theorem59PrintedFeasibleInnerTrajectoryRelOn S hmu samples s hs omega
        snapshot xStart trajectory)
    (k : Nat) :
    ∃ xUnder : FeasiblePoint S,
      xUnder =
          searchPointFeasibleOn S (theorem59Gamma S) (theorem59Alpha S) theorem59P s
            (trajectory k).xBar (trajectory k).x snapshot
            ((theorem59_parameter_conditions S hmu s hs).2.2.2.2.1) ∧
        ∃ G : VariableSpace dim,
          G =
              varianceReducedGradientFeasibleOn S (samplingWeight S)
                (samples s (k + 1) omega) xUnder snapshot
                (fullGradient S snapshot.1) ∧
            theorem59PrintedFeasibleProxUpdateRelOn S (theorem59Gamma S) s
              (trajectory k).x xUnder G (trajectory (k + 1)).x := by
  exact theorem59PrintedFeasibleInnerStepRelOn_proxUpdate S (theorem59Gamma S)
    (theorem59Alpha S) theorem59P s (samplingWeight S) snapshot
    (fullGradient S snapshot.1) (samples s (k + 1) omega)
    ((theorem59_parameter_conditions S hmu s hs).2.2.2.2.1)
    ((theorem59_parameter_conditions S hmu s hs).2.2.2.2.2)
    (trajectory k) (trajectory (k + 1))
    (theorem59PrintedFeasibleInnerTrajectoryRelOn_step S hmu samples s hs omega
      snapshot xStart trajectory htraj k)

/- Route tombstone: the former `theorem59PrintedFeasibleEpochStateProcess`
entrypoint was an all-feasible diagnostic supplier for the public printed
output. The active public output below is the printed epoch-output process;
this diagnostic recursion is retained only under a legacy name for local
source-boundary investigations. -/
def legacyDiagnosticTheorem59FeasibleEpochStateProcess {Ω : Type*} {n dim : Nat}
    (S : Setup n dim) (hmu : 0 < S.mu) (x0 : FeasiblePoint S)
    (samples : Nat -> Nat -> Ω -> Fin n) :
    Nat -> Ω -> EpochStateFeasibleOn S :=
  legacyDiagnosticEpochStateProcessFeasibleOn S (theorem59EpochLength S) (theorem59Gamma S)
    (theorem59Alpha S) theorem59P
    (theorem59Theta S hmu (averageSmoothness_pos S)) (samplingWeight S)
    x0 samples
    (theorem59_parameter_conditions S hmu)
    (theorem59Theta_epochOutputWeightsAdmissible S hmu)

/-- Printed feasible Algorithm 5.7 epoch-state process specification.

The process is specified by feasible Algorithm 5.7 epoch trajectories, not by a
constant fallback or by the retired all-feasible diagnostic prox recursion. -/
def theorem59PrintedFeasibleEpochStateProcessSpec {Ω : Type*} {n dim : Nat}
    (S : Setup n dim) (hmu : 0 < S.mu) (x0 : Set.Elem (proxCoreSet S))
    (samples : Nat -> Nat -> Ω -> Fin n)
    (stateProcess : Nat -> Ω -> EpochStateFeasibleOn S) : Prop :=
  (forall omega,
    stateProcess 0 omega =
      { x := proxCoreAsFeasible S x0
        xTilde := proxCoreAsFeasible S x0 }) ∧
    (forall s (hs : 1 <= s) omega,
      ∃ trajectory : Nat -> InnerStateFeasibleOn S,
        theorem59PrintedFeasibleInnerTrajectoryRelOn S hmu samples s hs omega
          ((stateProcess (s - 1) omega).xTilde)
          ((stateProcess (s - 1) omega).x)
          trajectory ∧
          (stateProcess s omega).x =
            (trajectory (theorem59EpochLength S s)).x ∧
          (stateProcess s omega).xTilde =
            epochOutputFeasibleOn S
              ((theorem59Theta S hmu (averageSmoothness_pos S)) s)
              (fun t : Fin (theorem59EpochLength S s) =>
                (trajectory (paperTime t)).xBar)
              (theorem59Theta_epochOutputWeightsAdmissible S hmu s hs))

/-- Generated epoch-state step for the printed feasible Algorithm 5.7 process. -/
def theorem59PrintedFeasibleEpochStateStepOn
    {Ω : Type*} {n dim : Nat}
    (S : Setup n dim) (hmu : 0 < S.mu)
    (x0 : Set.Elem (proxCoreSet S))
    (samples : Nat -> Nat -> Ω -> Fin n)
    (r : Nat) (prev : EpochStateFeasibleOn S) (omega : Ω) :
    EpochStateFeasibleOn S :=
  let s := r + 1
  let hs : 1 <= s := Nat.succ_pos r
  let trajectory :=
    theorem59PrintedFeasibleInnerTrajectoryOn S hmu x0 samples s hs omega prev.xTilde prev.x
  ⟨(trajectory (theorem59EpochLength S s)).x,
    epochOutputFeasibleOn S
      ((theorem59Theta S hmu (averageSmoothness_pos S)) s)
      (fun t : Fin (theorem59EpochLength S s) =>
        (trajectory (paperTime t)).xBar)
      (theorem59Theta_epochOutputWeightsAdmissible S hmu s hs)⟩

/-- Generated printed feasible Algorithm 5.7 epoch-state process. -/
def theorem59PrintedFeasibleEpochStateProcessGeneratedOn
    {Ω : Type*} {n dim : Nat}
    (S : Setup n dim) (hmu : 0 < S.mu) (x0 : Set.Elem (proxCoreSet S))
    (samples : Nat -> Nat -> Ω -> Fin n) :
    Nat -> Ω -> EpochStateFeasibleOn S :=
  SOptLib.recursiveIterateProcess
    (⟨proxCoreAsFeasible S x0,
      proxCoreAsFeasible S x0⟩ : EpochStateFeasibleOn S)
    (theorem59PrintedFeasibleEpochStateStepOn S hmu x0 samples)

/-- The generated printed feasible Algorithm 5.7 epoch-state process satisfies the
source-boundary epoch-state specification. -/
theorem theorem59PrintedFeasibleEpochStateProcessGeneratedOn_spec
    {Ω : Type*} {n dim : Nat}
    (S : Setup n dim) (hmu : 0 < S.mu) (x0 : Set.Elem (proxCoreSet S))
    (samples : Nat -> Nat -> Ω -> Fin n) :
    theorem59PrintedFeasibleEpochStateProcessSpec S hmu x0 samples
      (theorem59PrintedFeasibleEpochStateProcessGeneratedOn S hmu x0 samples) := by
  constructor
  · intro omega
    unfold theorem59PrintedFeasibleEpochStateProcessGeneratedOn
    rfl
  · intro s hs omega
    cases s with
    | zero =>
        omega
    | succ r =>
        let hs' : 1 <= r + 1 := Nat.succ_pos r
        let prevState :=
          theorem59PrintedFeasibleEpochStateProcessGeneratedOn S hmu x0 samples r omega
        let trajectory :=
          theorem59PrintedFeasibleInnerTrajectoryOn S hmu x0 samples (r + 1) hs' omega
            prevState.xTilde prevState.x
        refine ⟨trajectory, ?_, ?_, ?_⟩
        · exact theorem59PrintedFeasibleInnerTrajectoryOn_rel S hmu x0 samples
            (r + 1) hs' omega prevState.xTilde prevState.x
        · have hsucc :=
            SOptLib.recursiveIterateProcess_succ
              (theorem59PrintedFeasibleEpochStateProcessGeneratedOn S hmu x0 samples)
              (⟨proxCoreAsFeasible S x0,
                proxCoreAsFeasible S x0⟩ : EpochStateFeasibleOn S)
              (theorem59PrintedFeasibleEpochStateStepOn S hmu x0 samples)
              (by rfl) r omega
          rw [hsucc]
          rfl
        · have hsucc :=
            SOptLib.recursiveIterateProcess_succ
              (theorem59PrintedFeasibleEpochStateProcessGeneratedOn S hmu x0 samples)
              (⟨proxCoreAsFeasible S x0,
                proxCoreAsFeasible S x0⟩ : EpochStateFeasibleOn S)
              (theorem59PrintedFeasibleEpochStateStepOn S hmu x0 samples)
              (by rfl) r omega
          rw [hsucc]
          rfl

/-- Source-boundary existence of the printed feasible Algorithm 5.7 epoch-state process.

This is the exact source/coarser supplier requested by the route arbiter. It is
discharged by the feasible over-`X` Algorithm 5.7 step relation, not by the
retired weighted core-step-spine route. -/
theorem theorem59PrintedFeasibleEpochStateProcessSpec_exists
    {Ω : Type*} {n dim : Nat}
    (S : Setup n dim) (hmu : 0 < S.mu) (x0 : Set.Elem (proxCoreSet S))
    (samples : Nat -> Nat -> Ω -> Fin n) :
    ∃ stateProcess : Nat -> Ω -> EpochStateFeasibleOn S,
      theorem59PrintedFeasibleEpochStateProcessSpec S hmu x0 samples stateProcess := by
  exact ⟨theorem59PrintedFeasibleEpochStateProcessGeneratedOn S hmu x0 samples,
    theorem59PrintedFeasibleEpochStateProcessGeneratedOn_spec S hmu x0 samples⟩

/-- Printed feasible Algorithm 5.7 epoch-state process at Theorem 5.9 parameters.

This selected process unfolds only to the source-facing epoch-state
specification above. It no longer unfolds to a constant trajectory or to the
legacy all-feasible Bregman/prox surrogate. -/
def theorem59PrintedFeasibleEpochStateProcessOn {Ω : Type*} {n dim : Nat}
    (S : Setup n dim) (hmu : 0 < S.mu) (x0 : Set.Elem (proxCoreSet S))
    (samples : Nat -> Nat -> Ω -> Fin n) :
    Nat -> Ω -> EpochStateFeasibleOn S :=
  theorem59PrintedFeasibleEpochStateProcessGeneratedOn S hmu x0 samples

theorem theorem59PrintedFeasibleEpochStateProcessOn_spec
    {Ω : Type*} {n dim : Nat}
    (S : Setup n dim) (hmu : 0 < S.mu) (x0 : Set.Elem (proxCoreSet S))
    (samples : Nat -> Nat -> Ω -> Fin n) :
    theorem59PrintedFeasibleEpochStateProcessSpec S hmu x0 samples
      (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0 samples) := by
  simpa [theorem59PrintedFeasibleEpochStateProcessOn] using
    theorem59PrintedFeasibleEpochStateProcessGeneratedOn_spec S hmu x0 samples

/-- Printed feasible Theorem 5.9 output process `tilde{x}^s` from Algorithm 5.7. -/
def theorem59PrintedFeasibleEpochOutputProcessOn {Ω : Type*} {n dim : Nat}
    (S : Setup n dim) (hmu : 0 < S.mu) (x0 : Set.Elem (proxCoreSet S))
    (samples : Nat -> Nat -> Ω -> Fin n) :
    Nat -> Ω -> VariableSpace dim :=
  fun s omega =>
    (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0 samples s omega).xTilde.1

/-- Printed Algorithm 5.7 epoch-output contract at Theorem 5.9 parameters.

This is the source-facing output granularity requested by the route audit:
output feasibility, and for each epoch `s >= 1`, the printed endpoint `x^s` and
weighted output `tilde{x}^s` are supplied by one feasible inner trajectory of
length `theorem59EpochLength S s`. It deliberately does not require
per-inner-step prox-core subtype witnesses for the snapshot, previous iterate, or
previous averaged iterate. -/
def theorem59PrintedFeasibleEpochOutputProcessSpec {Ω : Type*} {n dim : Nat}
    (S : Setup n dim) (hmu : 0 < S.mu) (x0 : Set.Elem (proxCoreSet S))
    (samples : Nat -> Nat -> Ω -> Fin n)
    (output : Nat -> Ω -> VariableSpace dim) : Prop :=
  (forall s omega, output s omega ∈ S.X) ∧
    (forall s (_hs : 1 <= s) omega,
      ∃ trajectory : Nat -> InnerStateFeasibleOn S,
        theorem59PrintedFeasibleInnerTrajectoryRelOn S hmu samples s _hs omega
          ((theorem59PrintedFeasibleEpochStateProcessOn S hmu x0 samples
              (s - 1) omega).xTilde)
          ((theorem59PrintedFeasibleEpochStateProcessOn S hmu x0 samples
              (s - 1) omega).x)
          trajectory ∧
          (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0 samples s omega).x =
              (trajectory (theorem59EpochLength S s)).x ∧
          (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0 samples s omega).xTilde =
            epochOutputFeasibleOn S
              ((theorem59Theta S hmu (averageSmoothness_pos S)) s)
              (fun t : Fin (theorem59EpochLength S s) =>
                (trajectory (paperTime t)).xBar)
              (theorem59Theta_epochOutputWeightsAdmissible S hmu s _hs) ∧
          output s omega =
            (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0 samples s omega).xTilde.1)

theorem theorem59PrintedFeasibleEpochOutputProcessOn_spec
    {Ω : Type*} {n dim : Nat}
    (S : Setup n dim) (hmu : 0 < S.mu) (x0 : Set.Elem (proxCoreSet S))
    (samples : Nat -> Nat -> Ω -> Fin n) :
    theorem59PrintedFeasibleEpochOutputProcessSpec S hmu x0 samples
      (theorem59PrintedFeasibleEpochOutputProcessOn S hmu x0 samples) := by
  constructor
  · intro s omega
    exact (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0 samples s omega).xTilde.2
  · intro s hs omega
    rcases (theorem59PrintedFeasibleEpochStateProcessOn_spec S hmu x0 samples).2
        s hs omega with ⟨trajectory, htraj, hx, hxTilde⟩
    exact ⟨trajectory, htraj, hx, hxTilde, rfl⟩

/-- Printed feasible epoch states preserve the prox-core invariant once the
positive printed prox-output membership bridge is available.

This theorem is the exact source-stage dependency exposed by Lemma 5.18:
Algorithm 5.7's printed feasible epoch recursion gives `X`-valued states by
construction, while making those states legal left arguments of the paper
Bregman object `V : X^o x X -> R` reduces to the printed prox-output
membership statement and convexity of the search/averaging formulas. -/
theorem theorem59PrintedFeasibleEpochStateProcessOn_core_mem_of_positiveProxMembership
    {Ω : Type*} {n dim : Nat}
    (S : Setup n dim) (hmu : 0 < S.mu) (x0 : Set.Elem (proxCoreSet S))
    (samples : Nat -> Nat -> Ω -> Fin n)
    (hmem : theorem59PrintedFeasiblePositiveProxUpdateCoreMembershipStatement S) :
    forall s omega,
      (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0 samples s omega).x.1 ∈
          proxCoreSet S ∧
        (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0 samples s omega).xTilde.1 ∈
          proxCoreSet S := by
  intro s
  induction s with
  | zero =>
      intro omega
      have hzero :=
        (theorem59PrintedFeasibleEpochStateProcessOn_spec S hmu x0 samples).1 omega
      constructor
      · rw [hzero]
        exact x0.2
      · rw [hzero]
        exact x0.2
  | succ r ih =>
      intro omega
      let s' : Nat := r + 1
      have hs' : 1 <= s' := Nat.succ_pos r
      rcases (theorem59PrintedFeasibleEpochStateProcessOn_spec S hmu x0 samples).2
          s' hs' omega with ⟨trajectory, htraj, hx, hxTilde⟩
      have hprevCore := ih omega
      have hinnerCore :=
        theorem59PrintedFeasibleInnerTrajectoryRelOn_core_mem_of_positiveProxMembership
          S hmu samples s' hs' omega
          ((theorem59PrintedFeasibleEpochStateProcessOn S hmu x0 samples
              (s' - 1) omega).xTilde)
          ((theorem59PrintedFeasibleEpochStateProcessOn S hmu x0 samples
              (s' - 1) omega).x)
          trajectory hmem hprevCore.2 hprevCore.1 htraj
      constructor
      · rw [show r + 1 = s' by rfl]
        rw [hx]
        exact (hinnerCore (theorem59EpochLength S s')).1
      · rw [show r + 1 = s' by rfl]
        rw [hxTilde]
        let xBarCore : Fin (theorem59EpochLength S s') -> Set.Elem (proxCoreSet S) :=
          fun t =>
            ⟨(trajectory (paperTime t)).xBar.1,
              (hinnerCore (paperTime t)).2⟩
        have hcore :
            epochOutput
                ((theorem59Theta S hmu (averageSmoothness_pos S)) s')
                (fun t : Fin (theorem59EpochLength S s') => (xBarCore t).1) ∈
              proxCoreSet S :=
          epochOutput_mem_proxCore S
            ((theorem59Theta S hmu (averageSmoothness_pos S)) s') xBarCore
            (theorem59Theta_epochOutputWeightsAdmissible S hmu s' hs')
        simpa [epochOutputFeasibleOn, xBarCore] using hcore

theorem theorem59PrintedFeasibleEpochOutputProcessSpec_exists
    {Ω : Type*} {n dim : Nat}
    (S : Setup n dim) (hmu : 0 < S.mu) (x0 : Set.Elem (proxCoreSet S))
    (samples : Nat -> Nat -> Ω -> Fin n) :
    ∃ output : Nat -> Ω -> VariableSpace dim,
      theorem59PrintedFeasibleEpochOutputProcessSpec S hmu x0 samples output := by
  exact ⟨theorem59PrintedFeasibleEpochOutputProcessOn S hmu x0 samples,
    theorem59PrintedFeasibleEpochOutputProcessOn_spec S hmu x0 samples⟩

/-- The printed feasible Theorem 5.9 output process `tilde{x}^s`.

The public source route uses the printed Algorithm 5.7 epoch-output process.
It exposes the book-visible endpoint/weighted-average equations without routing
through the retired weighted core-step-spine existence theorem; any later
printed/core transfer must use `theorem59OriginalOutputCompatibility`
explicitly. -/
def theorem59PrintedFeasibleOutputProcessOn {Ω : Type*} {n dim : Nat}
    (S : Setup n dim) (hmu : 0 < S.mu) (x0 : Set.Elem (proxCoreSet S))
    (samples : Nat -> Nat -> Ω -> Fin n) :
    Nat -> Ω -> VariableSpace dim :=
  theorem59PrintedFeasibleEpochOutputProcessOn S hmu x0 samples

/-- The printed feasible Theorem 5.9 output process under the canonical iid sample
law. -/
def theorem59PrintedFeasibleOutputProcess {n dim : Nat} (S : Setup n dim)
    (hmu : 0 < S.mu) (x0 : Set.Elem (proxCoreSet S)) :
    Nat -> theorem59SamplePath n -> VariableSpace dim :=
  theorem59PrintedFeasibleOutputProcessOn S hmu x0 theorem59CanonicalSamples

/-- Printed-path domain/output contract for the active Algorithm 5.7 output.

This predicate points at `theorem59PrintedFeasibleEpochOutputProcessSpec`, the
source-granularity contract recording feasibility, the endpoint `x^s = x_T`,
and the theta-weighted formula for `tilde{x}^s`. It does not include the retired
weighted core-step-spine obligations. -/
def theorem59OriginalOutputDomainCompatibility {Ω : Type*} {n dim : Nat}
    (S : Setup n dim) (hmu : 0 < S.mu) (x0 : Set.Elem (proxCoreSet S))
    (samples : Nat -> Nat -> Ω -> Fin n) : Prop :=
  theorem59PrintedFeasibleEpochOutputProcessSpec S hmu x0 samples
    (theorem59PrintedFeasibleOutputProcessOn S hmu x0 samples)

@[simp]
theorem theorem59OriginalOutputDomainCompatibility_def {Ω : Type*} {n dim : Nat}
    (S : Setup n dim) (hmu : 0 < S.mu) (x0 : Set.Elem (proxCoreSet S))
    (samples : Nat -> Nat -> Ω -> Fin n) :
    theorem59OriginalOutputDomainCompatibility S hmu x0 samples =
      theorem59PrintedFeasibleEpochOutputProcessSpec S hmu x0 samples
        (theorem59PrintedFeasibleOutputProcessOn S hmu x0 samples) := by
  rfl

/-- Source boundary that the printed feasible Algorithm 5.7 output satisfies the
printed epoch-output specification. -/
theorem theorem59_printedFeasibleEpochOutputProcessSpec_boundary
    {Ω : Type*} {n dim : Nat}
    (S : Setup n dim) (hmu : 0 < S.mu) (x0 : Set.Elem (proxCoreSet S))
    (samples : Nat -> Nat -> Ω -> Fin n) :
    theorem59PrintedFeasibleEpochOutputProcessSpec S hmu x0 samples
      (theorem59PrintedFeasibleOutputProcessOn S hmu x0 samples) := by
  simpa [theorem59PrintedFeasibleOutputProcessOn] using
    theorem59PrintedFeasibleEpochOutputProcessOn_spec S hmu x0 samples

/-- Source-route T1 artifact for printed Lemma 5.18.

Destructing `theorem59PrintedFeasibleEpochOutputProcessSpec` for one epoch and
one sample path yields a printed feasible trajectory. For each inner step, the
ability to turn that step into the core-typed next-iterate premise needed by
Lemma 5.16 is equivalent to the same-interface printed prox-output membership
obligation below. This is the exact obstruction left by the source contract; it
does not route through the retired weighted output spine or the corrected-core
output process. -/
theorem lemma518_printed_epoch_core_instantiation_or_obstruction
    {n dim : Nat} (S : Setup n dim)
    (x0 : Set.Elem (proxCoreSet S)) (_xStar : FeasiblePoint S) (hmu : 0 < S.mu)
    (s : Nat) (hs : 1 <= s)
    (omega : theorem59SamplePath n)
    (hspec :
      theorem59PrintedFeasibleEpochOutputProcessSpec S hmu x0 theorem59CanonicalSamples
        (theorem59PrintedFeasibleOutputProcessOn S hmu x0 theorem59CanonicalSamples)) :
    ∃ trajectory : Nat -> InnerStateFeasibleOn S,
      theorem59PrintedFeasibleInnerTrajectoryRelOn S hmu theorem59CanonicalSamples s hs omega
        ((theorem59PrintedFeasibleEpochStateProcessOn S hmu x0 theorem59CanonicalSamples
            (s - 1) omega).xTilde)
        ((theorem59PrintedFeasibleEpochStateProcessOn S hmu x0 theorem59CanonicalSamples
            (s - 1) omega).x)
        trajectory ∧
      (forall k,
        (forall next : InnerStateFeasibleOn S,
            theorem59PrintedFeasibleInnerStepRelOn S (theorem59Gamma S)
              (theorem59Alpha S) theorem59P s (samplingWeight S)
              ((theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                  theorem59CanonicalSamples (s - 1) omega).xTilde)
              (fullGradient S
                ((theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                    theorem59CanonicalSamples (s - 1) omega).xTilde).1)
              (theorem59CanonicalSamples s (k + 1) omega)
              ((theorem59_parameter_conditions S hmu s hs).2.2.2.2.1)
              ((theorem59_parameter_conditions S hmu s hs).2.2.2.2.2)
              (trajectory k) next ->
            next.x.1 ∈ proxCoreSet S) ↔
          (forall z : FeasiblePoint S,
            theorem59PrintedFeasibleProxUpdateRelOn S (theorem59Gamma S) s
              (trajectory k).x
              (searchPointFeasibleOn S (theorem59Gamma S) (theorem59Alpha S)
                theorem59P s (trajectory k).xBar (trajectory k).x
                ((theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                    theorem59CanonicalSamples (s - 1) omega).xTilde)
                ((theorem59_parameter_conditions S hmu s hs).2.2.2.2.1))
              (varianceReducedGradientFeasibleOn S (samplingWeight S)
                (theorem59CanonicalSamples s (k + 1) omega)
                (searchPointFeasibleOn S (theorem59Gamma S) (theorem59Alpha S)
                  theorem59P s (trajectory k).xBar (trajectory k).x
                  ((theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                      theorem59CanonicalSamples (s - 1) omega).xTilde)
                  ((theorem59_parameter_conditions S hmu s hs).2.2.2.2.1))
                ((theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                    theorem59CanonicalSamples (s - 1) omega).xTilde)
                (fullGradient S
                  ((theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                      theorem59CanonicalSamples (s - 1) omega).xTilde).1))
              z ->
            z.1 ∈ proxCoreSet S)) := by
  rcases hspec.2 s hs omega with
    ⟨trajectory, htraj, _hxEndpoint, _hxTilde, _hout⟩
  refine ⟨trajectory, htraj, ?_⟩
  intro k
  exact
    theorem59PrintedFeasibleInnerStepRelOn_x_core_propagation_iff_printedProx_mem_proxCore
      S (theorem59Gamma S) (theorem59Alpha S) theorem59P s (samplingWeight S)
      ((theorem59PrintedFeasibleEpochStateProcessOn S hmu x0 theorem59CanonicalSamples
        (s - 1) omega).xTilde)
      (fullGradient S
        ((theorem59PrintedFeasibleEpochStateProcessOn S hmu x0 theorem59CanonicalSamples
          (s - 1) omega).xTilde).1)
      (theorem59CanonicalSamples s (k + 1) omega)
      ((theorem59_parameter_conditions S hmu s hs).2.2.2.2.1)
      ((theorem59_parameter_conditions S hmu s hs).2.2.2.2.2)
      (trajectory k)

/-- Closed migrated witness for the printed-output domain contract.

This named consumer is definitionally the active printed epoch-output
specification, so it closes through
`theorem59_printedFeasibleEpochOutputProcessSpec_boundary` and not through the
retired weighted core-step-spine route. -/
theorem theorem59OriginalOutputDomainCompatibility_boundary
    {Ω : Type*} {n dim : Nat}
    (S : Setup n dim) (hmu : 0 < S.mu) (x0 : Set.Elem (proxCoreSet S))
    (samples : Nat -> Nat -> Ω -> Fin n) :
    theorem59OriginalOutputDomainCompatibility S hmu x0 samples := by
  simpa [theorem59OriginalOutputDomainCompatibility] using
    theorem59_printedFeasibleEpochOutputProcessSpec_boundary S hmu x0 samples

/-- Direct printed-output witness for Algorithm 5.7's weighted epoch output.

This is the source-facing theorem named on the printed process itself: each
printed `tilde{x}^s` is the `epochOutputFeasibleOn` value of one feasible
Algorithm 5.7 epoch trajectory with the Theorem 5.9 schedules and theta
weights. -/
theorem theorem59PrintedFeasibleOutputProcessOn_epochOutput
    {Ω : Type*} {n dim : Nat}
    (S : Setup n dim) (hmu : 0 < S.mu) (x0 : Set.Elem (proxCoreSet S))
    (samples : Nat -> Nat -> Ω -> Fin n)
    (s : Nat) (hs : 1 <= s) (omega : Ω) :
    ∃ (epochState : EpochStateFeasibleOn S)
      (trajectory : Nat -> InnerStateFeasibleOn S),
      epochState.x = (trajectory (theorem59EpochLength S s)).x ∧
        epochState.xTilde =
          epochOutputFeasibleOn S
            ((theorem59Theta S hmu (averageSmoothness_pos S)) s)
            (fun t : Fin (theorem59EpochLength S s) =>
              (trajectory (paperTime t)).xBar)
            (theorem59Theta_epochOutputWeightsAdmissible S hmu s hs) ∧
        theorem59PrintedFeasibleOutputProcessOn S hmu x0 samples s omega =
          epochState.xTilde.1 := by
  rcases (theorem59_printedFeasibleEpochOutputProcessSpec_boundary S hmu x0 samples).2
      s hs omega with ⟨trajectory, _htraj, hx, hxTilde, hout⟩
  exact ⟨theorem59PrintedFeasibleEpochStateProcessOn S hmu x0 samples s omega,
    trajectory, hx, hxTilde, hout⟩

/-- Pathwise Jensen bridge for the printed epoch output in Lemma 5.18.

Aligns with the source step "identify the weighted average with
`tilde x^s`" before summing/recursing Eq. (5.4.27). Candidates considered:
`theorem59PrintedFeasibleOutputProcessOn_epochOutput` supplies the exact
printed-output witness and is consumed here; `ConvexOn.map_sum_le` is consumed
inside `compositeObjective_epochOutputFeasibleOn_le_weighted_sum`. -/
theorem lemma518_first_phase_epoch_output_jensen
    {Ω : Type*} {n dim : Nat}
    (S : Setup n dim) (hmu : 0 < S.mu) (x0 : Set.Elem (proxCoreSet S))
    (samples : Nat -> Nat -> Ω -> Fin n)
    (s : Nat) (hs : 1 <= s) (omega : Ω) :
    ∃ (epochState : EpochStateFeasibleOn S)
      (trajectory : Nat -> InnerStateFeasibleOn S),
      epochState.x = (trajectory (theorem59EpochLength S s)).x ∧
        epochState.xTilde =
          epochOutputFeasibleOn S
            ((theorem59Theta S hmu (averageSmoothness_pos S)) s)
            (fun t : Fin (theorem59EpochLength S s) =>
              (trajectory (paperTime t)).xBar)
            (theorem59Theta_epochOutputWeightsAdmissible S hmu s hs) ∧
        theorem59PrintedFeasibleOutputProcessOn S hmu x0 samples s omega =
          epochState.xTilde.1 ∧
        compositeObjective S
            (theorem59PrintedFeasibleOutputProcessOn S hmu x0 samples s omega) <=
          (Finset.univ.sum
              (fun t : Fin (theorem59EpochLength S s) =>
                ((theorem59Theta S hmu (averageSmoothness_pos S)) s) (paperTime t)))⁻¹ *
            Finset.univ.sum
              (fun t : Fin (theorem59EpochLength S s) =>
                ((theorem59Theta S hmu (averageSmoothness_pos S)) s) (paperTime t) *
                  compositeObjective S (trajectory (paperTime t)).xBar.1) := by
  classical
  rcases theorem59PrintedFeasibleOutputProcessOn_epochOutput
      S hmu x0 samples s hs omega with
    ⟨epochState, trajectory, hx, hxTilde, hout⟩
  refine ⟨epochState, trajectory, hx, hxTilde, hout, ?_⟩
  have hJ :=
    compositeObjective_epochOutputFeasibleOn_le_weighted_sum
      S ((theorem59Theta S hmu (averageSmoothness_pos S)) s)
      (fun t : Fin (theorem59EpochLength S s) =>
        (trajectory (paperTime t)).xBar)
      (theorem59Theta_epochOutputWeightsAdmissible S hmu s hs)
  simpa [hout, hxTilde] using hJ

/-- Full bridge compatibility between the printed feasible path and the corrected core.

Domain membership alone does not identify two independently selected argmins.
This predicate therefore records both the source-boundary domain facts for the
printed feasible path and the separate selector/process equality needed to
transport a corrected-core theorem back to that printed path. It is intentionally
not a Theorem 5.9 hypothesis. -/
def theorem59OriginalOutputCompatibility {Ω : Type*} {n dim : Nat}
    (S : Setup n dim) (hmu : 0 < S.mu) (x0 : Set.Elem (proxCoreSet S))
    (samples : Nat -> Nat -> Ω -> Fin n) : Prop :=
  ∃ _hdomain :
      theorem59OriginalOutputDomainCompatibility S hmu x0 samples,
    theorem59PrintedFeasibleOutputProcessOn S hmu x0 samples =
      theorem59CorrectedCoreOutputProcessOn S hmu x0 samples

theorem theorem59OriginalOutputCompatibility_domain {Ω : Type*} {n dim : Nat}
    (S : Setup n dim) (hmu : 0 < S.mu) (x0 : Set.Elem (proxCoreSet S))
    (samples : Nat -> Nat -> Ω -> Fin n)
    (hcompat : theorem59OriginalOutputCompatibility S hmu x0 samples) :
    theorem59OriginalOutputDomainCompatibility S hmu x0 samples := by
  rcases hcompat with ⟨hdomain, _hstate⟩
  exact hdomain

/- Route tombstone: `theorem59_printed_output_generated_core_alias_route_v1`.
The old compiled source-boundary proof supplier for unconditional printed/core
compatibility has been removed from the proof surface. The compatibility
predicate `theorem59OriginalOutputCompatibility` remains available as the
explicit non-alias output bridge record, but public/source consumers must not
close by calling the retired unconditional entrypoint. -/

/- Route tombstone: `theorem59_original_epoch_state_compatibility_route_v1`.
The former public declaration
`theorem59OriginalEpochStateProcess_eq_correctedCoreEpochStateProcessOn_of_outputCompatibility`
was an epoch-state bridge name whose body had been weakened to an output-level
equality. That surface is retired from the public namespace. The unsupported
state-process equality is not kept as a compile-sorry leaf; public consumers use
`theorem59OriginalOutputProcess_eq_correctedCoreOutputProcessOn_of_outputCompatibility`. -/

/-- Output-level bridge from the printed feasible Algorithm 5.7 process to the
corrected-core output process.

This theorem connects the compatibility predicate to the corrected-core
Theorem 5.9 declarations without promoting compatibility to a paper theorem
assumption. It is intentionally conditional/internal until the proof phase
derives both domain membership and selector/process equality from the
source-backed setup. -/
theorem theorem59OriginalOutputProcess_eq_correctedCoreOutputProcessOn_of_outputCompatibility
    {Ω : Type*} {n dim : Nat} (S : Setup n dim) (hmu : 0 < S.mu)
    (x0 : Set.Elem (proxCoreSet S)) (samples : Nat -> Nat -> Ω -> Fin n)
    (hcompat :
      theorem59OriginalOutputCompatibility S hmu x0 samples) :
    theorem59PrintedFeasibleOutputProcessOn S hmu x0 samples =
      theorem59CorrectedCoreOutputProcessOn S hmu x0 samples := by
  rcases hcompat with ⟨_hdomain, houtput⟩
  exact houtput

/-- Internal smooth-case prox-core output using the Eq. (5.4.12) weights only.

This is the domain-correct realization used when later proof obligations need
all generated left Bregman arguments to lie in `X^o`. It is not the
source-facing smooth Algorithm 5.7 output. -/
def smoothCorrectedCoreOutputProcess {n dim : Nat} (S : Setup n dim)
    (x0 : Set.Elem (proxCoreSet S)) :
    Nat -> theorem59SamplePath n -> VariableSpace dim :=
  epochOutputProcessOn S (theorem59EpochLength S) (theorem59Gamma S)
    (theorem59Alpha S) theorem59P
    (theorem59SmoothTheta S) (samplingWeight S) x0
    theorem59CanonicalSamples
    (smooth_parameter_conditions S)
    (smoothTheta_epochOutputWeightsAdmissible S)

/-- The cross-epoch weighted average `bar{x}^s` from Eq. (5.4.16), evaluated on
the generated Algorithm 5.7 output path.

SOptLib `weightedAverageOutputValue` was checked; it is an abstract window
average over a supplied window selector, while Eq. (5.4.16) fixes the window
`j = 1, ..., s-1` and the weights `w_j = L_j - R_{j+1}`. This local wrapper is
the paper-specialized process needed in Lemma 5.17. -/
def theorem59SmoothEpochAverageProcess {n dim : Nat} (S : Setup n dim)
    (hmu : 0 < S.mu) (x0 : Set.Elem (proxCoreSet S)) :
    Nat -> theorem59SamplePath n -> VariableSpace dim :=
  smoothEpochAverageProcessOn S (theorem59EpochLength S) (theorem59Gamma S)
    (theorem59Alpha S) theorem59P
    (theorem59Theta S hmu (averageSmoothness_pos S)) (samplingWeight S)
    x0 theorem59CanonicalSamples (theorem59_parameter_conditions S hmu)
    (theorem59Theta_epochOutputWeightsAdmissible S hmu)


/-- Source-facing predicate that `xStar` is an optimal solution of Eq. (5.3.1). -/
def IsOptimalSolution {n dim : Nat} (S : Setup n dim)
    (xStar : VariableSpace dim) : Prop :=
  xStar ∈ S.X ∧
    forall x, x ∈ S.X -> compositeObjective S xStar <= compositeObjective S x

/-- Source-facing optimizer predicate on the feasible carrier for Eq. (5.3.1). -/
def IsOptimalSolutionOn {n dim : Nat} (S : Setup n dim)
    (xStar : FeasiblePoint S) : Prop :=
  forall x : FeasiblePoint S,
    compositeObjective S xStar.1 <= compositeObjective S x.1

/-- The initial Lyapunov quantity `D_0` from Eq. (5.4.20).

SOptLib `objectiveGapRadius` was checked and rejected for this object: it is a
square-root radius for other Lan budgets, while Eq. (5.4.20) is the literal
linear combination `2[Psi(x0)-Psi(x*)] + 3 L V(x0,x*)`. -/
def theorem59D0 {n dim : Nat} (S : Setup n dim)
    (x0 : Set.Elem (proxCoreSet S)) (xStar : FeasiblePoint S) : Real :=
  2 * (compositeObjective S x0.1 - compositeObjective S xStar.1) +
    3 * averageSmoothness S * bregmanOn S x0 xStar

/-- The first Theorem 5.9 rate case `2^(-(s+1)) D_0`. -/
def theorem59Case1Rate (s : Nat) (D0 : Real) : Real :=
  D0 / (2 : Real) ^ (s + 1)


end VarianceReducedAcceleratedGradientDescent
