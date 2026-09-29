import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Topology.Basic

open MeasureTheory
open Topology
open scoped Gradient InnerProductSpace

namespace SOptLib

/-- Ambient totalization of a carrier-defined function, using `0` off the carrier.

This extends a function defined on the subtype `{x // x ∈ X}` to the ambient
space by applying the subtype function on points in `X` and returning zero
outside `X`.

Layer: Model | Concept: Objective
Proof: (definitional construction; subtype-to-ambient objective wrapper with
  zero extension off the feasible carrier)
Source: Mathlib Set subtype and decidable if-then-else APIs
Used in: stochastic mirror descent objective evaluation on ambient iterates
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
noncomputable def carrierTotalizeOn
    {E α : Type*} [Zero α] (X : Set E) (f : {x : E // x ∈ X} → α) : E → α :=
  by
    classical
    exact fun x => if hx : x ∈ X then f ⟨x, hx⟩ else 0

/-- Ambient totalization alias for functions defined on a carrier subtype.

`totalizeOn X f` is the short model-facing name for the canonical extension of
a carrier-subtype function to the ambient space.

Layer: Model | Concept: Carrier
Proof: (definitional construction; short alias for canonical carrier subtype
  function totalization to the ambient space)
Source: Mathlib set subtype and function coercion APIs
Used in: stochastic mirror descent carrier and intrinsic-interior objectives
  totalized from the feasible subtype to the ambient space
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
noncomputable def totalizeOn
    {E α : Type*} [Zero α] (X : Set E) (f : {x : E // x ∈ X} → α) : E → α :=
  carrierTotalizeOn X f

/-- The short carrier totalization alias is definitionally equal to the canonical carrier totalization.

This lemma records that `totalizeOn` is only a short name for `carrierTotalizeOn`,
so carrier-restricted maps can be normalized to the canonical totalization form.

Layer: Model | Gap: Level 0 (carrier totalization alias normalization)
Proof: by rfl after unfolding `totalizeOn`
Source: Mathlib subtype functions and definitional equality APIs
Used in: stochastic mirror descent carrier-restricted objective and oracle totalization
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem totalizeOn_eq_carrierTotalizeOn
    {E α : Type*} [Zero α] (X : Set E) (f : {x : E // x ∈ X} → α) :
    totalizeOn X f = carrierTotalizeOn X f := by
  rfl

/-- A carrier totalization evaluates to the original subtype function on carrier points.

For a function defined on the carrier subtype `{x // x ∈ X}`, `totalizeOn X f`
agrees with `f` at every ambient point `x` equipped with a proof `x ∈ X`.

Layer: Model | Gap: Level 0 (carrier totalization membership agreement)
Proof: by simplification after unfolding `totalizeOn` and `carrierTotalizeOn`;
  the membership proof selects the carrier branch.
Source: Mathlib subtype coercions and `Set` membership simplification APIs
Used in: stochastic mirror descent intrinsic-interior carrier totalization
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic mirror descent -/
@[simp]
theorem totalizeOn_of_mem
    {E α : Type*} [Zero α] (X : Set E) (f : {x : E // x ∈ X} → α)
    {x : E} (hx : x ∈ X) :
    totalizeOn X f x = f ⟨x, hx⟩ := by
  classical
  simp [totalizeOn, carrierTotalizeOn, hx]

/-- Restrict a carrier-indexed function to the intrinsic interior of the carrier.

Given a function defined on the subtype `{x // x ∈ X}`, this definition reindexes it
over `{x // x ∈ intrinsicInterior ℝ X}` using the inclusion
`intrinsicInterior ℝ X ⊆ X`.

Layer: Model | Concept: Carrier
Proof: (definitional construction; subtype restriction along the intrinsic
  interior subset of the carrier)
Source: Mathlib convex geometry intrinsic interior and subtype coercion APIs
Used in: stochastic mirror descent carrier function restricted to intrinsic
  interior before prox-step totalization
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
noncomputable def restrictToInterior
    {E α : Type*} [NormedAddCommGroup E] [Module ℝ E]
    (X : Set E) (f : {x : E // x ∈ X} → α) :
    {x : E // x ∈ intrinsicInterior ℝ X} → α :=
  fun x => f ⟨x.1, intrinsicInterior_subset x.2⟩

/-- Totalizing a carrier-defined map returns zero outside the carrier.

If `x ∉ X`, the totalized extension of a function defined on the subtype
`{x // x ∈ X}` takes the default zero value at `x`.

Layer: Model | Gap: Level 0 (off-carrier totalization value)
Proof: by simplification after unfolding `totalizeOn` and `carrierTotalizeOn`,
  using `hx` to select the off-carrier branch.
Source: Mathlib Set membership, Subtype, and simplification APIs
Used in: stochastic mirror descent carrier totalization for partial-domain
  prox and objective maps
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
@[simp]
theorem totalizeOn_of_not_mem
    {E α : Type*} [Zero α] (X : Set E) (f : {x : E // x ∈ X} → α)
    {x : E} (hx : x ∉ X) :
    totalizeOn X f x = 0 := by
  classical
  simp [totalizeOn, carrierTotalizeOn, hx]

/-- Restrict a carrier-defined function to the intrinsic interior of its carrier.

This turns a function on the feasible carrier `X` into a function on the
intrinsic-interior carrier by coercing each intrinsic-interior point back into
`X`.

Layer: Model | Concept: Carrier
Proof: (definitional construction; subtype precomposition along
  `intrinsicInterior_subset`)
Source: Mathlib convex geometry intrinsic-interior subset API
Used in: stochastic mirror descent objectives restricted to the feasible
  relative interior
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
noncomputable def carrierRestrictToIntrinsicInterior
    {E α : Type*} [NormedAddCommGroup E] [Module ℝ E]
    (X : Set E) (f : {x : E // x ∈ X} → α) :
    {x : E // x ∈ intrinsicInterior ℝ X} → α :=
  fun x => f ⟨x.1, intrinsicInterior_subset x.2⟩

/-- Ambient totalization of a carrier-defined function on the intrinsic interior carrier.

Layer: Model | Concept: Carrier
Proof: (definitional construction; restricts the carrier function to
  `intrinsicInterior ℝ X` and applies the ambient carrier totalization wrapper)
Source: Mathlib convex geometry intrinsic interior and Set subtype APIs
Used in: stochastic mirror descent objectives evaluated after restricting to
  intrinsic interior candidate carriers
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
noncomputable def carrierTotalizeOnIntrinsicInterior
    {E α : Type*} [NormedAddCommGroup E] [Module ℝ E] [Zero α]
    (X : Set E) (f : {x : E // x ∈ X} → α) : E → α :=
  carrierTotalizeOn (intrinsicInterior ℝ X) (carrierRestrictToIntrinsicInterior X f)

/-- Ambient totalization of a carrier function restricted to intrinsic interior points.

`totalizeOnInterior X f` extends a function on the carrier subtype `{x // x ∈ X}`
to an ambient function on `E` by using the intrinsic-interior carrier
totalization.

Layer: Model | Concept: Carrier totalization
Proof: (definitional construction; ambient wrapper for intrinsic-interior
  carrier totalization)
Source: Mathlib convex geometry and subtype carrier APIs
Used in: stochastic mirror descent ambient totalization of
  intrinsic-interior restrictions
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
noncomputable def totalizeOnInterior
    {E α : Type*} [NormedAddCommGroup E] [Module ℝ E] [Zero α]
    (X : Set E) (f : {x : E // x ∈ X} → α) : E → α :=
  carrierTotalizeOnIntrinsicInterior X f

/-- Intrinsic-interior totalization agrees with the carrier function on-domain.

For a point `x` in `intrinsicInterior ℝ X`, the totalized intrinsic-interior
carrier evaluates to the original carrier function at the corresponding subtype
point of `X`.

Layer: Model | Gap: Level 0 (intrinsic-interior carrier totalization agreement)
Proof: by simplification after unfolding `carrierTotalizeOnIntrinsicInterior`,
  `carrierRestrictToIntrinsicInterior`, and `carrierTotalizeOn`; membership in
  `X` is supplied by `intrinsicInterior_subset`.
Source: Mathlib convex geometry intrinsic interior and subtype APIs
Used in: stochastic mirror descent objective and prox maps evaluated on the
  intrinsic carrier domain
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
@[simp]
theorem carrierTotalizeOnIntrinsicInterior_of_mem
    {E α : Type*} [NormedAddCommGroup E] [Module ℝ E] [Zero α]
    (X : Set E) (f : {x : E // x ∈ X} → α)
    {x : E} (hx : x ∈ intrinsicInterior ℝ X) :
    carrierTotalizeOnIntrinsicInterior X f x = f ⟨x, intrinsicInterior_subset hx⟩ := by
  classical
  simp [carrierTotalizeOnIntrinsicInterior, carrierRestrictToIntrinsicInterior,
    carrierTotalizeOn, hx]

/-- Intrinsic-interior totalization agrees with the carrier function at interior points.

For a feasible carrier `X`, the ambient totalization `totalizeOnInterior X f`
recovers the original subtype-valued carrier function `f` whenever
`x ∈ intrinsicInterior ℝ X`.

Layer: Model | Gap: Level 0 (intrinsic-interior carrier totalization agreement)
Proof: direct wrapper around `carrierTotalizeOnIntrinsicInterior_of_mem`, using
  `intrinsicInterior_subset` to coerce the ambient point back into the carrier
  subtype.
Source: Mathlib convex geometry intrinsic interior and subtype coercion APIs
Used in: stochastic mirror descent carrier totalization for prox-domain objectives
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic mirror descent -/
@[simp]
theorem totalizeOnInterior_of_mem
    {E α : Type*} [NormedAddCommGroup E] [Module ℝ E] [Zero α]
    (X : Set E) (f : {x : E // x ∈ X} → α)
    {x : E} (hx : x ∈ intrinsicInterior ℝ X) :
    totalizeOnInterior X f x = f ⟨x, intrinsicInterior_subset hx⟩ := by
  exact carrierTotalizeOnIntrinsicInterior_of_mem X f hx

/-- Paper-facing convexity predicate for a function defined on a feasible carrier.

`ConvexOnCarrier X f` records convexity of the subtype-domain objective by
totalizing it to the ambient space through `carrierTotalizeOn`, so Mathlib
convexity APIs can be applied directly to carrier-defined functions.

Layer: Model | Concept: Objective
Proof: (definitional construction; ambient totalization of a carrier-domain
  objective followed by Mathlib `ConvexOn` on the carrier set)
Source: Mathlib convex analysis for real inner product spaces and subtype
  carrier totalization
Used in: stochastic mirror descent convexity assumptions for carrier-defined
  objectives on intrinsic feasible domains
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
def ConvexOnCarrier
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X : Set E) (f : {x : E // x ∈ X} → ℝ) : Prop :=
  ConvexOn ℝ X (carrierTotalizeOn X f)

/-- Carrier convexity is exactly Mathlib convexity of the ambient totalized function.

`ConvexOnCarrier X f` unfolds to `ConvexOn ℝ X (carrierTotalizeOn X f)`, exposing
the paper-facing carrier predicate to Mathlib convex-analysis search.

Layer: Model | Gap: Level 0 (carrier convexity predicate unfolding)
Proof: by rfl after unfolding ConvexOnCarrier
Source: Mathlib convex analysis `ConvexOn` APIs for real inner product spaces
Used in: stochastic mirror descent feasible-carrier convex objective hypotheses
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic mirror descent -/
theorem convexOnCarrier_iff
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X : Set E} {f : {x : E // x ∈ X} → ℝ} :
    ConvexOnCarrier X f ↔ ConvexOn ℝ X (carrierTotalizeOn X f) := by
  rfl

/-- Paper-facing `C¹` regularity predicate for carrier objectives on intrinsic interiors.

For an objective `v` defined only on the feasible carrier `X`, this predicate
records `C¹` regularity of its totalization on `intrinsicInterior ℝ X` and on
the carrier itself.

Layer: Model | Concept: Carrier
Proof: (definitional construction; conjunction of `ContDiffOn` regularity for
  carrier totalizations on the intrinsic interior and on the carrier)
Source: Mathlib `ContDiffOn` calculus on sets and convex intrinsic-interior APIs
Used in: stochastic mirror descent carrier regularity hypotheses for prox-step
  differentiation on the intrinsic interior
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
def ContDiffOnInterior
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X : Set E) (v : {x : E // x ∈ X} → ℝ) : Prop :=
  ContDiffOn ℝ 1 (carrierTotalizeOnIntrinsicInterior X v) (intrinsicInterior ℝ X) ∧
    ContDiffOn ℝ 1 (carrierTotalizeOn X v) X

/-- Lan's carrier `C¹` hypothesis gives differentiability on the intrinsic interior.

If the carrier value function is continuously differentiable on the intrinsic
interior of `X`, then its totalized representative is differentiable on that
same intrinsic interior.

Layer: Model | Gap: Level 0 (continuous differentiability implies
  differentiability on carrier interior)
Proof: Apply Mathlib's `ContDiffOn.differentiableOn_one` API to the smoothness
  component stored in `ContDiffOnInterior`.
Source: Mathlib smooth calculus on normed spaces and `ContDiffOn`
  differentiability APIs
Used in: stochastic mirror descent carrier regularity for Bregman prox steps
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem ContDiffOnInterior.differentiableOn
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X : Set E} {v : {x : E // x ∈ X} → ℝ}
    (hv : ContDiffOnInterior X v) :
    DifferentiableOn ℝ (carrierTotalizeOnIntrinsicInterior X v) (intrinsicInterior ℝ X) := by
  exact hv.1.differentiableOn_one

/-- The subtype carrier of feasible points lying in the topological interior.

Layer: Model | Concept: Bregman interior carrier for feasible prox centers
Proof: (definitional construction; subtype of points whose witness is
  membership in `interior X`)
Source: Mathlib topology Set interior and subtype APIs
Used in: stochastic mirror descent feasibility bookkeeping for interior
  iterates and Bregman prox centers
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
abbrev InteriorCarrierPoint
    {E : Type*} [TopologicalSpace E] (X : Set E) : Type _ :=
  {x : E // x ∈ interior X}

/-- A point of the interior carrier belongs to the topological interior.

Layer: Model | Gap: Level 0 (interior carrier membership projection)
Proof: subtype property projection; the membership witness is the second
  component of the carrier point.
Source: Mathlib topology Set interior and subtype APIs
Used in: stochastic mirror descent feasibility bookkeeping for interior
  iterates and prox centers
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem InteriorCarrierPoint.mem_interior
    {E : Type*} [TopologicalSpace E] {X : Set E}
    (x : InteriorCarrierPoint X) :
    (x : E) ∈ interior X :=
  x.2

/-- The carrier type of feasible points restricted to the intrinsic interior of a set.

Layer: Model | Concept: carrier for intrinsic-interior feasible domains
Proof: (definitional construction; subtype wrapper storing
  `x ∈ intrinsicInterior ℝ X` as the carrier witness)
Source: Mathlib convex analysis intrinsic-interior APIs
Used in: stochastic mirror descent feasible-domain carrier construction
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
abbrev IntrinsicInteriorCarrierPoint
    {E : Type*} [NormedAddCommGroup E] [Module ℝ E] (X : Set E) : Type _ :=
  {x : E // x ∈ intrinsicInterior ℝ X}

/-- A carrier point belongs to the intrinsic interior of its feasible set.

Layer: Model | Gap: Level 0 (intrinsic-interior carrier membership projection)
Proof: direct projection from the `IntrinsicInteriorCarrierPoint` witness `x.2`,
  exposing the stored intrinsic-interior membership under the coercion to `E`.
Source: Mathlib convex analysis intrinsic-interior APIs
Used in: stochastic mirror descent carrier-domain feasibility checks
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem IntrinsicInteriorCarrierPoint.mem_intrinsicInterior
    {E : Type*} [NormedAddCommGroup E] [Module ℝ E] {X : Set E}
    (x : IntrinsicInteriorCarrierPoint X) :
    (x : E) ∈ intrinsicInterior ℝ X :=
  x.2

/-- Paper-facing differentiability predicate for a carrier-defined objective on its
intrinsic interior.

`DifferentiableOnInterior X v` records differentiability of the totalized
carrier function on `intrinsicInterior ℝ X`, matching the stochastic mirror
descent requirement that the prox geometry be differentiable on the feasible
carrier's intrinsic interior.

Layer: Model | Concept: Carrier
Proof: (definitional construction; intrinsic-interior totalization of a
  subtype-valued carrier function followed by Mathlib `DifferentiableOn`)
Source: Mathlib differentiability-on API for normed real vector spaces
Used in: stochastic mirror descent prox geometry differentiability on the
  intrinsic interior of the feasible carrier
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
def DifferentiableOnInterior
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X : Set E) (v : {x : E // x ∈ X} → ℝ) : Prop :=
  DifferentiableOn ℝ (carrierTotalizeOnIntrinsicInterior X v) (intrinsicInterior ℝ X)

/-- The carrier differentiability predicate is exactly Mathlib differentiability on the
intrinsic-interior totalization.

This rewrites Lan's paper-facing `C¹` carrier condition into the raw
`DifferentiableOn` statement used by Mathlib on `intrinsicInterior ℝ X`.

Layer: Model | Gap: Level 0 (carrier differentiability predicate unfolding)
Proof: by rfl after unfolding `DifferentiableOnInterior`
Source: Mathlib analysis/calculus differentiability on sets and convex intrinsic interior APIs
Used in: stochastic mirror descent carrier regularity assumptions on the feasible-set interior
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic mirror descent -/
theorem differentiableOnInterior_iff
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X : Set E} {v : {x : E // x ∈ X} → ℝ} :
    DifferentiableOnInterior X v ↔
      DifferentiableOn ℝ (carrierTotalizeOnIntrinsicInterior X v) (intrinsicInterior ℝ X) := by
  rfl

/-- A `C¹`-on-interior carrier hypothesis yields differentiability on the intrinsic interior.

Lan's smooth carrier assumption packaged as `ContDiffOnInterior X v` exposes the
paper-facing `DifferentiableOnInterior X v` predicate needed for mirror-map
reasoning on feasible points.

Layer: Model | Gap: Level 0 (interior differentiability projection)
Proof: direct field projection from the `ContDiffOnInterior` record using
  `hv.differentiableOn`.
Source: Mathlib differentiability-on APIs for normed inner product spaces
Used in: stochastic mirror descent mirror-map differentiability on the feasible
  carrier interior
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem ContDiffOnInterior.differentiableOnInterior
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X : Set E} {v : {x : E // x ∈ X} → ℝ}
    (hv : ContDiffOnInterior X v) :
    DifferentiableOnInterior X v := by
  exact hv.differentiableOn

/-- Paper-facing strong-convexity predicate for a carrier-totalized objective.

`StrongConvexOnInterior X μ v` states that the subtype objective `v`, whose
domain is the feasible carrier `X`, is `μ`-strongly convex after totalization to
the intrinsic interior of `X`.

Layer: Model | Concept: Objective
Proof: (definitional construction; raw Mathlib `StrongConvexOn` statement on
  `intrinsicInterior ℝ X` for the carrier totalization)
Source: Mathlib convex analysis APIs for strong convexity and intrinsic interior
Used in: stochastic mirror descent assumptions on strong convexity over the
  intrinsic interior of the feasible carrier
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
def StrongConvexOnInterior
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X : Set E) (μ : ℝ) (v : {x : E // x ∈ X} → ℝ) : Prop :=
  StrongConvexOn (intrinsicInterior ℝ X) μ (carrierTotalizeOnIntrinsicInterior X v)

/-- Carrier interior strong convexity is exactly Mathlib strong convexity on the intrinsic interior.

The carrier-local predicate `StrongConvexOnInterior X μ v` unfolds to
`StrongConvexOn` over `intrinsicInterior ℝ X` for the totalized carrier
function.

Layer: Model | Gap: Level 0 (carrier intrinsic-interior strong-convexity equivalence)
Proof: by rfl after unfolding `StrongConvexOnInterior`; the statement is the
  definitional bridge to Mathlib's `StrongConvexOn` predicate.
Source: Mathlib convex analysis APIs for strong convexity on sets and intrinsic interiors
Used in: stochastic mirror descent carrier geometry assumptions for prox-step analysis
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem strongConvexOnInterior_iff
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X : Set E} {μ : ℝ} {v : {x : E // x ∈ X} → ℝ} :
    StrongConvexOnInterior X μ v ↔
      StrongConvexOn (intrinsicInterior ℝ X) μ (carrierTotalizeOnIntrinsicInterior X v) := by
  rfl

/-- Fixed affine-span direction chart for a carrier.

For a nonempty carrier `X`, choosing an anchor point identifies the direction
space of `affineSpan ℝ X` with the affine span itself by translation.

Layer: Model | Concept: Carrier relative_calculus chart
Proof: (definitional construction; anchor-based affine isometry chart from
  affine-span directions to the carrier affine span)
Source: Mathlib affine subspace, affine isometry, and finite-dimensional
  topology APIs
Used in: stochastic mirror descent relative calculus on a fixed carrier
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
noncomputable def carrierAffineSpanChart
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (X : Set E) (anchor : {x : E // x ∈ X}) :
    (affineSpan ℝ X).direction ≃ₜ affineSpan ℝ X := by
  classical
  let A : AffineSubspace ℝ E := affineSpan ℝ X
  haveI : Nonempty A := ⟨⟨anchor.1, subset_affineSpan ℝ X anchor.2⟩⟩
  haveI : IsClosed ((A.direction : Submodule ℝ E) : Set E) :=
    A.direction.closed_of_finiteDimensional
  haveI : IsUniformAddGroup A.direction := A.direction.toAddSubgroup.isUniformAddGroup
  haveI : CompleteSpace A.direction := FiniteDimensional.complete ℝ A.direction
  let a : A := ⟨anchor.1, subset_affineSpan ℝ X anchor.2⟩
  exact (AffineIsometryEquiv.vaddConst ℝ a).toContinuousAffineEquiv.toHomeomorph

/-- Continuous affine map from affine-span chart coordinates back to the ambient carrier space.

The map fixes an anchor in `X`, interprets chart coordinates in
`(affineSpan ℝ X).direction`, translates them inside the affine span, and then
forgets the affine-subspace subtype into the ambient Hilbert space.

Layer: Model | Concept: Carrier chart
Proof: (definitional construction; anchor-based affine chart composed with the
  affine-span subtype continuous affine map)
Source: Mathlib affine subspaces, finite-dimensional closed submodules, and
  continuous affine maps
Used in: relative-calculus carrier chart for stochastic mirror descent
  feasible-set arguments
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
noncomputable def carrierChartToAmbient
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (X : Set E) (anchor : {x : E // x ∈ X}) :
    (affineSpan ℝ X).direction →ᴬ[ℝ] E := by
  classical
  let A : AffineSubspace ℝ E := affineSpan ℝ X
  haveI : Nonempty A := ⟨⟨anchor.1, subset_affineSpan ℝ X anchor.2⟩⟩
  haveI : IsClosed ((A.direction : Submodule ℝ E) : Set E) :=
    A.direction.closed_of_finiteDimensional
  haveI : IsUniformAddGroup A.direction := A.direction.toAddSubgroup.isUniformAddGroup
  letI : CompleteSpace A.direction := FiniteDimensional.complete ℝ A.direction
  let a : A := ⟨anchor.1, subset_affineSpan ℝ X anchor.2⟩
  exact A.subtypeA.comp
    ((AffineIsometryEquiv.vaddConst ℝ a).toContinuousAffineEquiv.toContinuousAffineMap)

/-- Feasible carrier transported to the fixed affine-span direction chart.

The charted carrier is the preimage of `X` under the affine-span
chart-to-ambient map, so optimization statements can be phrased in the linear
direction space while retaining membership in the original feasible set.

Layer: Model | Concept: relative_calculus carrier chart
Proof: (definitional construction; preimage of the feasible carrier under the
  affine-span chart-to-ambient map)
Source: Mathlib affine geometry `affineSpan` and set preimage APIs
Used in: stochastic mirror descent relative-calculus setup for feasible carrier
  constraints
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
def carrierChartSet
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (X : Set E) (anchor : {x : E // x ∈ X}) :
    Set (affineSpan ℝ X).direction :=
  (carrierChartToAmbient X anchor) ⁻¹' X

/-- The ambient chart map is the affine-span chart followed by subtype inclusion. -/
@[simp] theorem carrierChartToAmbient_apply
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (X : Set E) (anchor : {x : E // x ∈ X}) (u : (affineSpan ℝ X).direction) :
    carrierChartToAmbient X anchor u =
      ((carrierAffineSpanChart X anchor u : affineSpan ℝ X) : E) := by
  rfl

/-- Membership in the charted carrier is membership of the ambient chart image in the
carrier. -/
@[simp] theorem mem_carrierChartSet_iff
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (X : Set E) (anchor : {x : E // x ∈ X}) (u : (affineSpan ℝ X).direction) :
    u ∈ carrierChartSet X anchor ↔
      ((carrierAffineSpanChart X anchor u : affineSpan ℝ X) : E) ∈ X := by
  rfl

/-- Carrier function totalized on the ambient space and transported to the fixed
affine-span chart.

Given a carrier set `X`, a subtype-valued carrier function `f`, and an anchor
for the affine-span chart, `carrierChartFunction X f anchor` evaluates the
ambient totalization `totalizeOn X f` at the chart image of each direction.

Layer: Model | Concept: Carrier
Proof: (definitional construction; carrier totalization composed with the
  affine-span chart-to-ambient map)
Source: Mathlib affine span, finite-dimensional inner-product, and subtype APIs
Used in: stochastic mirror descent ContDiffOn regularity for the carrier
  function totalized and composed with the affine-span chart
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
noncomputable def carrierChartFunction
    {E α : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [Zero α] (X : Set E) (f : {x : E // x ∈ X} → α) (anchor : {x : E // x ∈ X}) :
    (affineSpan ℝ X).direction → α :=
  fun u => totalizeOn X f (carrierChartToAmbient X anchor u)

/-- The charted carrier function is the ambient totalization evaluated at the chart
image. -/
@[simp] theorem carrierChartFunction_apply
    {E α : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [Zero α] (X : Set E) (f : {x : E // x ∈ X} → α) (anchor : {x : E // x ∈ X})
    (u : (affineSpan ℝ X).direction) :
    carrierChartFunction X f anchor u = totalizeOn X f (carrierChartToAmbient X anchor u) :=
  rfl

/-- Smoothness of a carrier-totalized function transports to the fixed affine-span chart.

If the totalized carrier function is `ContDiffOn` on the ambient feasible set
`X`, then precomposing with the affine chart from chart coordinates back into
the ambient space is `ContDiffOn` on the carrier chart set.

Layer: Model | Gap: Level 1 (affine carrier chart smoothness transport)
Proof: Apply `ContDiffOn.comp` to compose the ambient smoothness hypothesis with
  the smooth continuous affine chart map; the chart-set membership condition
  supplies the required image containment.
Source: Mathlib `ContDiffOn` composition and `ContinuousAffineMap.contDiff`
  calculus APIs
Used in: stochastic mirror descent carrier-coordinate smoothness for prox and
  objective terms on the feasible affine span
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem carrierChartFunction_contDiffOn
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {n : WithTop ℕ∞}
    (X : Set E) (f : {x : E // x ∈ X} → F) (anchor : {x : E // x ∈ X})
    (hf : ContDiffOn ℝ n (totalizeOn X f) X) :
    ContDiffOn ℝ n (carrierChartFunction X f anchor) (carrierChartSet X anchor) := by
  simpa [carrierChartFunction, carrierChartSet, Function.comp_def] using
    hf.comp ((ContinuousAffineMap.contDiff (carrierChartToAmbient X anchor)).contDiffOn)
      (by intro u hu; exact hu)

/-- Coordinates of a feasible point in the fixed affine-span direction chart.

For a feasible carrier `X` with an anchor point, `carrierChartPoint X anchor x`
is the direction-vector coordinate of `x` obtained by applying the inverse of
the fixed affine-span chart to the subtype point of `affineSpan ℝ X`.

Layer: Model | Concept: Carrier
Proof: (definitional construction; inverse affine-span chart applied to the
  feasible point embedded in `affineSpan ℝ X` using `subset_affineSpan`).
Source: Mathlib affine subspace direction and affineSpan APIs
Used in: stochastic mirror descent coordinate representation of feasible
  iterates in the fixed carrier chart
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
noncomputable def carrierChartPoint
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (X : Set E) (anchor x : {x : E // x ∈ X}) :
    (affineSpan ℝ X).direction :=
  (carrierAffineSpanChart X anchor).symm ⟨x.1, subset_affineSpan ℝ X x.2⟩

/-- The fixed affine-span coordinate map is continuous on the feasible carrier subtype.

The map sending a feasible point to its coordinates in the anchor-based affine-span
chart is continuous, so carrier coordinates can be used in topological arguments.

Layer: Model | Gap: Level 0 (carrier subtype chart continuity)
Proof: build the continuous inclusion from the feasible subtype into the affine span
  using `Continuous.subtype_mk`, then compose with continuity of the inverse affine
  chart.
Source: Mathlib topology of subtypes and continuous affine equivalences
Used in: stochastic mirror descent carrier-coordinate continuity for feasible iterates
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic mirror descent -/
theorem carrierChartPoint_continuous
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (X : Set E) (anchor : {x : E // x ∈ X}) :
    Continuous (fun x : {x : E // x ∈ X} => carrierChartPoint X anchor x) := by
  let A : AffineSubspace ℝ E := affineSpan ℝ X
  let toSpan : {x : E // x ∈ X} → A := fun x =>
    ⟨x.1, subset_affineSpan ℝ X x.2⟩
  have htoSpan : Continuous toSpan :=
    Continuous.subtype_mk continuous_subtype_val (fun x => subset_affineSpan ℝ X x.2)
  have hchart : Continuous (fun y : A => (carrierAffineSpanChart X anchor).symm y) :=
    (carrierAffineSpanChart X anchor).symm.continuous
  change Continuous (fun x : {x : E // x ∈ X} =>
    (carrierAffineSpanChart X anchor).symm ⟨x.1, subset_affineSpan ℝ X x.2⟩)
  exact hchart.comp htoSpan

/-- The fixed affine-span coordinate of a feasible point lies in the charted carrier. -/
@[simp] theorem carrierChartPoint_mem
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (X : Set E) (anchor x : {x : E // x ∈ X}) :
    carrierChartPoint X anchor x ∈ carrierChartSet X anchor := by
  rw [carrierChartSet]
  change carrierChartToAmbient X anchor (carrierChartPoint X anchor x) ∈ X
  rw [carrierChartToAmbient_apply]
  simp [carrierChartPoint]

/-- Intrinsic-interior feasible points become ordinary interior points in the carrier chart.

For a feasible point `x ∈ X`, membership in `intrinsicInterior ℝ X` transports
through the fixed affine-span homeomorphism to membership of `carrierChartPoint`
in the topological interior of `carrierChartSet`.

Layer: Model | Gap: Level 1 (intrinsic interior to chart interior transport)
Proof: unfold intrinsic interior via `mem_intrinsicInterior`, identify the
  affine-span point for `x`, and move interior membership across the
  `carrierAffineSpanChart` homeomorphism using `Homeomorph.preimage_interior`.
Source: Mathlib topology homeomorphism APIs and affine-subspace intrinsic interior
Used in: stochastic mirror descent feasible-carrier chart reduction
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic mirror descent -/
theorem carrierChartPoint_mem_interior_chartSet_of_intrinsicInterior
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (X : Set E) (anchor x : {x : E // x ∈ X})
    (hx : x.1 ∈ intrinsicInterior ℝ X) :
    carrierChartPoint X anchor x ∈ interior (carrierChartSet X anchor) := by
  rcases (mem_intrinsicInterior.mp hx) with ⟨y, hy, hyx⟩
  let A : AffineSubspace ℝ E := affineSpan ℝ X
  let e : A.direction ≃ₜ A := carrierAffineSpanChart X anchor
  have hy_eq : y = (⟨x.1, subset_affineSpan ℝ X x.2⟩ : A) := by
    ext
    simpa using hyx
  have hy' : y ∈ interior ((fun z : A => (z : E)) ⁻¹' X) := hy
  have hpre : e.symm y ∈ e ⁻¹' interior ((fun z : A => (z : E)) ⁻¹' X) := by
    simpa only [Set.mem_preimage, Homeomorph.apply_symm_apply] using hy'
  have hpre' :
      e.symm y ∈ interior (e ⁻¹' ((fun z : A => (z : E)) ⁻¹' X)) := by
    simpa [e.preimage_interior] using hpre
  have hrewrite :
      e ⁻¹' ((fun z : A => (z : E)) ⁻¹' X) = carrierChartSet X anchor := by
    ext u
    simp [e, carrierChartSet]
  have hpoint :
      carrierChartPoint X anchor x = e.symm y := by
    subst hy_eq
    rfl
  simpa [hpoint, hrewrite] using hpre'

/-- Convex feasible carriers remain convex in the fixed affine-span chart.

If the ambient feasible set `X` is convex, then its coordinate carrier
`carrierChartSet X anchor` is convex after transport through the chart anchored
at a feasible point.

Layer: Model | Gap: Level 0 (convexity of affine chart carrier)
Proof: Unfold `carrierChartSet` and apply `Convex.affine_preimage` to the
  affine map underlying `carrierChartToAmbient`.
Source: Mathlib convex sets and affine-map preimage APIs
Used in: stochastic mirror descent feasible carrier chart convexity
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem carrierChartSet_convex
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (X : Set E) (anchor : {x : E // x ∈ X}) (hX : Convex ℝ X) :
    Convex ℝ (carrierChartSet X anchor) := by
  simpa [carrierChartSet] using
    hX.affine_preimage (carrierChartToAmbient X anchor).toAffineMap

/-- A nonempty convex carrier has nonempty ordinary interior in its affine-span chart.

Transporting a convex feasible set `X` through `carrierChartSet X anchor` turns
relative nonemptiness of the intrinsic interior into ordinary interior
nonemptiness in the fixed direction coordinates of `affineSpan ℝ X`.

Layer: Model | Gap: Level 1 (carrier chart interior nonemptiness)
Proof: use `Set.Nonempty.intrinsicInterior` for a nonempty convex finite
  dimensional carrier, unpack `mem_intrinsicInterior`, then transfer interior
  membership across the affine-span homeomorphism via `Homeomorph.preimage_interior`.
Source: Mathlib convex intrinsic interior and homeomorph interior APIs
Used in: stochastic mirror descent carrier-chart feasible-domain setup
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem carrierChartSet_interior_nonempty
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (X : Set E) (anchor : {x : E // x ∈ X}) (hX : Convex ℝ X) :
    (interior (carrierChartSet X anchor)).Nonempty := by
  have hrel : (intrinsicInterior ℝ X).Nonempty := by
    exact Set.Nonempty.intrinsicInterior hX ⟨anchor.1, anchor.2⟩
  rcases hrel with ⟨x, hx⟩
  rcases (mem_intrinsicInterior.mp hx) with ⟨y, hy, rfl⟩
  let A : AffineSubspace ℝ E := affineSpan ℝ X
  let e : A.direction ≃ₜ A := carrierAffineSpanChart X anchor
  refine ⟨e.symm y, ?_⟩
  have hy' : y ∈ interior ((fun z : A => (z : E)) ⁻¹' X) := hy
  have hpre : e.symm y ∈ e ⁻¹' interior ((fun z : A => (z : E)) ⁻¹' X) := by
    simpa only [Set.mem_preimage, Homeomorph.apply_symm_apply] using hy'
  have hpre' :
      e.symm y ∈ interior (e ⁻¹' ((fun z : A => (z : E)) ⁻¹' X)) := by
    simpa [e.preimage_interior] using hpre
  have hrewrite :
      e ⁻¹' ((fun z : A => (z : E)) ⁻¹' X) = carrierChartSet X anchor := by
    ext u
    simp [e, carrierChartSet]
  simpa [hrewrite] using hpre'

/-- A convex feasible carrier is uniquely differentiable in its fixed affine-span chart.

Transporting the feasible set to the chart determined by `anchor` gives a convex
set with nonempty interior, so Mathlib's convex-set criterion yields
`UniqueDiffOn ℝ (carrierChartSet X anchor)`.

Layer: Model | Gap: Level 0 (unique differentiability of convex carrier chart)
Proof: apply `uniqueDiffOn_convex` to the chart convexity lemma and the chart
  nonempty-interior lemma.
Source: Mathlib convex analysis and unique differentiability APIs
Used in: stochastic mirror descent intrinsic-gradient chart differentiability
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem carrierChartSet_uniqueDiffOn
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (X : Set E) (anchor : {x : E // x ∈ X}) (hX : Convex ℝ X) :
    UniqueDiffOn ℝ (carrierChartSet X anchor) := by
  exact uniqueDiffOn_convex
    (carrierChartSet_convex X anchor hX)
    (carrierChartSet_interior_nonempty X anchor hX)

/-- The affine span of a feasible carrier set.

This abbreviation names the intrinsic affine subspace generated by the feasible
carrier, so relative-calculus and chart lemmas can refer to the carrier's ambient
affine geometry uniformly.

Layer: Model | Concept: Carrier affine hull
Proof: (definitional construction; carrier-facing wrapper around Mathlib
  `affineSpan ℝ X`)
Source: Mathlib affine subspace and affine span APIs
Used in: stochastic mirror descent intrinsic-gradient coordinates on the feasible carrier
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic mirror descent -/
abbrev carrierAffineSpan
    {E : Type*} [NormedAddCommGroup E] [Module ℝ E] (X : Set E) :
    AffineSubspace ℝ E :=
  affineSpan ℝ X

/-- The carrier chart fixes coordinates on the affine span of the feasible set.

This compatibility alias exposes `carrierAffineSpanChart` under the carrier-facing
name used by relative-calculus lemmas.

Layer: Model | Concept: Carrier relative_calculus chart
Proof: (definitional construction; compatibility alias wrapping
  `carrierAffineSpanChart` as the fixed affineSpan direction chart for a carrier)
Source: Mathlib affine subspace direction and finite-dimensional topology APIs
Used in: stochastic mirror descent relative-calculus coordinates for feasible carrier points
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic mirror descent -/
noncomputable def carrierChart
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (X : Set E) (anchor : {x : E // x ∈ X}) :
    (carrierAffineSpan X).direction ≃ₜ carrierAffineSpan X :=
  carrierAffineSpanChart X anchor

/-- The ambient chart sends the fixed-chart coordinate of a feasible point back to that
point. -/
@[simp] theorem carrierChartToAmbient_chartPoint
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (X : Set E) (anchor x : {x : E // x ∈ X}) :
    carrierChartToAmbient X anchor (carrierChartPoint X anchor x) = x.1 := by
  rw [carrierChartToAmbient_apply]
  simp [carrierChartPoint]

/-- Chart-interior points of a feasible carrier map to ambient intrinsic-interior points.

For the fixed affine-span chart anchored in `X`, membership in the ordinary
interior of `carrierChartSet X anchor` gives membership in
`intrinsicInterior ℝ X` after returning to the ambient space.

Layer: Model | Gap: Level 1 (affine-span chart interior to intrinsic interior)
Proof: rewrite the chart carrier as the preimage of `X` under the affine-span
  homeomorphism, transfer interior membership with `Homeomorph.preimage_interior`,
  then use the resulting affine-span point as the intrinsic-interior witness.
Source: Mathlib topology homeomorph interior API and convex intrinsic-interior definitions
Used in: stochastic mirror descent boundary-safe affine-span gradient selector
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem carrierChartToAmbient_mem_intrinsicInterior_of_mem_interior_chartSet
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (X : Set E) (anchor : {x : E // x ∈ X})
    {u : (affineSpan ℝ X).direction}
    (hu : u ∈ interior (carrierChartSet X anchor)) :
    carrierChartToAmbient X anchor u ∈ intrinsicInterior ℝ X := by
  let A : AffineSubspace ℝ E := affineSpan ℝ X
  let e : A.direction ≃ₜ A := carrierAffineSpanChart X anchor
  have hrewrite :
      e ⁻¹' ((fun z : A => (z : E)) ⁻¹' X) = carrierChartSet X anchor := by
    ext w
    simp [e, carrierChartSet]
  have hu' :
      u ∈ interior (e ⁻¹' ((fun z : A => (z : E)) ⁻¹' X)) := by
    simpa [hrewrite] using hu
  have hu_pre :
      u ∈ e ⁻¹' interior ((fun z : A => (z : E)) ⁻¹' X) := by
    simpa [e.preimage_interior] using hu'
  exact ⟨e u, hu_pre, by simp [e]⟩

/-- Boundary-safe carrier gradient obtained from `gradientWithin` on the affine-span chart.

For a real-valued function on a feasible carrier `X`, `carrierGradientFrom X v anchor x`
computes the chart-space `gradientWithin` at `x` inside the direction space of
`affineSpan ℝ X`, then includes that relative gradient back into the ambient
Hilbert space.

Layer: Model | Concept: Carrier relative_gradient
Proof: (definitional construction; affine-span carrier chart, finite-dimensional
  completeness for the direction space, and subtype inclusion of `gradientWithin`)
Source: Mathlib affine subspaces, finite-dimensional Hilbert spaces, and
  differentiability gradient APIs
Used in: stochastic mirror descent relative gradient at boundary-safe carrier
  points
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
noncomputable def carrierGradientFrom
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (X : Set E) (v : {x : E // x ∈ X} → ℝ) (anchor x : {x : E // x ∈ X}) : E := by
  classical
  let A : AffineSubspace ℝ E := affineSpan ℝ X
  haveI : Nonempty A := ⟨⟨anchor.1, subset_affineSpan ℝ X anchor.2⟩⟩
  haveI : IsClosed ((A.direction : Submodule ℝ E) : Set E) :=
    A.direction.closed_of_finiteDimensional
  haveI : IsUniformAddGroup A.direction := A.direction.toAddSubgroup.isUniformAddGroup
  letI : CompleteSpace A.direction := FiniteDimensional.complete ℝ A.direction
  let T : Set A.direction := carrierChartSet X anchor
  let f : A.direction → ℝ := carrierChartFunction X v anchor
  let u : A.direction := carrierChartPoint X anchor x
  have hcomp : CompleteSpace A.direction := inferInstance
  exact (A.direction.subtypeL) (@gradientWithin ℝ A.direction _ _ _ hcomp f T u)

/-- Boundary-safe carrier gradient anchored at the evaluation point.

The carrier gradient is the fixed-anchor carrier gradient specialized to use
the evaluated intrinsic-interior point as its own anchor, giving the notation
used for relative-gradient expressions on the feasible carrier.

Layer: Model | Concept: Objective
Proof: (definitional construction; evaluation-point specialization of the
  fixed-anchor carrier gradient wrapper)
Source: Mathlib finite-dimensional inner product space and subtype APIs
Used in: stochastic mirror descent relative-gradient notation on the carrier
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
noncomputable def carrierGradient
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (X : Set E) (v : {x : E // x ∈ X} → ℝ) (x : {x : E // x ∈ X}) : E :=
  carrierGradientFrom X v x x

/-- Fixed-anchor carrier gradient evaluated on the intrinsic-interior carrier.

This is the relative carrier gradient used at points known to lie in
`intrinsicInterior X`, coerced through the carrier subset before applying
`carrierGradientFrom`.

Layer: Model | Concept: Carrier
Proof: (definitional construction; restricts an intrinsic-interior carrier
  point to the ambient carrier subtype and applies the fixed-anchor carrier
  gradient)
Source: Mathlib finite-dimensional inner product spaces and set-subtype APIs
Used in: stochastic mirror descent relative-gradient evaluation on the
  intrinsic-interior carrier
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
noncomputable def carrierIntrinsicGradient
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (X : Set E) (v : {x : E // x ∈ X} → ℝ) (anchor : {x : E // x ∈ X})
    (x : IntrinsicInteriorCarrierPoint X) : E :=
  carrierGradientFrom X v anchor ⟨x.1, intrinsicInterior_subset x.2⟩

/-- The intrinsic-interior carrier gradient is the carrier gradient on the restricted carrier.

For a point represented in the intrinsic-interior carrier subtype, the intrinsic
gradient wrapper agrees definitionally with `carrierGradientFrom` after coercing
the point through `intrinsicInterior_subset`.

Layer: Model | Gap: Level 0 (carrier gradient intrinsic restriction)
Proof: by rfl after unfolding carrierIntrinsicGradient.
Source: Mathlib subtype coercions and Set subset APIs
Used in: stochastic mirror descent carrier-gradient boundary extension
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem carrierIntrinsicGradient_eq_carrierGradientFrom
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (X : Set E) (v : {x : E // x ∈ X} → ℝ) (anchor : {x : E // x ∈ X})
    (x : IntrinsicInteriorCarrierPoint X) :
    carrierIntrinsicGradient X v anchor x =
      carrierGradientFrom X v anchor ⟨x.1, intrinsicInterior_subset x.2⟩ := by
  rfl

/-- Boundary extension of the carrier gradient agrees with the intrinsic-interior form.

Layer: Model | Gap: Level 0 (intrinsic-interior gradient extension bridge)
Proof: rewrite with `carrierIntrinsicGradient_eq_carrierGradientFrom`, the
  definitional bridge from the ambient carrier gradient extension to the
  intrinsic-interior gradient.
Source: Mathlib subtype coercions and set membership rewriting APIs
Used in: stochastic mirror descent intrinsic-interior gradient extension
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem carrierGradientFrom_eq_intrinsicGradient
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {X : Set E} (v : {x : E // x ∈ X} → ℝ) (anchor : {x : E // x ∈ X})
    (x : IntrinsicInteriorCarrierPoint X) :
    carrierGradientFrom X v anchor ⟨x.1, intrinsicInterior_subset x.2⟩ =
      carrierIntrinsicGradient X v anchor x := by
  rw [carrierIntrinsicGradient_eq_carrierGradientFrom]

/-- The affine-span carrier chart has the same within derivative as the ambient
intrinsic-interior objective on feasible directions.

For a value function on a constrained carrier `X`, the derivative of the charted
objective at the carrier chart point, applied to the affine-span displacement
from `x` to `z`, agrees with the ambient `fderivWithin` of `totalizeOnInterior X v`
on the displacement `z.1 - x.1`.

Layer: Model | Gap: Level 1 (carrier chart within-derivative compatibility)
Proof: restricts the chart domain to its interior, identifies the charted
  objective with `totalizeOnInterior` after the affine carrier chart, and applies
  Mathlib `fderivWithin` congruence and affine-composition APIs. Intrinsic
  interior membership supplies the local unique-differentiability and
  differentiability hypotheses.
Source: Mathlib calculus on normed spaces and finite-dimensional affine subspace topology APIs
Used in: stochastic mirror descent carrier reduction from charted feasible
  directions to ambient intrinsic-interior derivatives
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic mirror descent -/
theorem carrierChart_fderivWithin_eq_intrinsicInterior_fderivWithin_on_feasible_direction
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (X : Set E) (v : {x : E // x ∈ X} → ℝ) (anchor x z : {x : E // x ∈ X})
    (hvInt : ContDiffOn ℝ 1 (totalizeOnInterior X v) (intrinsicInterior ℝ X))
    (hx : x.1 ∈ intrinsicInterior ℝ X) :
    (fderivWithin ℝ (carrierChartFunction X v anchor) (carrierChartSet X anchor)
        (carrierChartPoint X anchor x))
      (⟨z.1 - x.1,
          AffineSubspace.vsub_mem_direction
            (subset_affineSpan ℝ X z.2) (subset_affineSpan ℝ X x.2)⟩ :
        (affineSpan ℝ X).direction) =
      (fderivWithin ℝ (totalizeOnInterior X v) (intrinsicInterior ℝ X) x.1)
        (z.1 - x.1) := by
  classical
  let A : AffineSubspace ℝ E := affineSpan ℝ X
  haveI : Nonempty A := ⟨⟨anchor.1, subset_affineSpan ℝ X anchor.2⟩⟩
  haveI : IsClosed ((A.direction : Submodule ℝ E) : Set E) :=
    A.direction.closed_of_finiteDimensional
  haveI : IsUniformAddGroup A.direction := A.direction.toAddSubgroup.isUniformAddGroup
  letI : CompleteSpace A.direction := FiniteDimensional.complete ℝ A.direction
  let T : Set A.direction := carrierChartSet X anchor
  let u : A.direction := carrierChartPoint X anchor x
  let du : A.direction :=
    ⟨z.1 - x.1,
      AffineSubspace.vsub_mem_direction
        (subset_affineSpan ℝ X z.2) (subset_affineSpan ℝ X x.2)⟩
  let L : A.direction →ᴬ[ℝ] E := carrierChartToAmbient X anchor
  let g : E → ℝ := totalizeOnInterior X v
  have hu : u ∈ interior T := by
    simpa [A, T, u] using
      carrierChartPoint_mem_interior_chartSet_of_intrinsicInterior X anchor x hx
  have hsrcUniq : UniqueDiffWithinAt ℝ (interior T) u := by
    exact uniqueDiffWithinAt_of_mem_nhds (IsOpen.mem_nhds isOpen_interior hu)
  have hTnhds : interior T ∈ 𝓝 u := IsOpen.mem_nhds isOpen_interior hu
  have hleft_restrict :
      fderivWithin ℝ (carrierChartFunction X v anchor) T u =
        fderivWithin ℝ (carrierChartFunction X v anchor) (interior T) u := by
    have h := fderivWithin_inter (𝕜 := ℝ) (f := carrierChartFunction X v anchor)
      (s := T) (t := interior T) (x := u) hTnhds
    rw [Set.inter_eq_right.mpr interior_subset] at h
    exact h.symm
  have heq_on : Set.EqOn (carrierChartFunction X v anchor)
      (fun y : A.direction => g (L y)) (interior T) := by
    intro y hy
    have hyI : carrierChartToAmbient X anchor y ∈ intrinsicInterior ℝ X := by
      simpa [A, T] using
        carrierChartToAmbient_mem_intrinsicInterior_of_mem_interior_chartSet X anchor hy
    have hyX : carrierChartToAmbient X anchor y ∈ X := intrinsicInterior_subset hyI
    calc
      carrierChartFunction X v anchor y =
          totalizeOn X v (carrierChartToAmbient X anchor y) := rfl
      _ = v ⟨carrierChartToAmbient X anchor y, hyX⟩ := by
        exact totalizeOn_of_mem X v hyX
      _ = totalizeOnInterior X v (carrierChartToAmbient X anchor y) := by
        symm
        exact totalizeOnInterior_of_mem X v hyI
      _ = g (L y) := rfl
  have hleft_congr :
      fderivWithin ℝ (carrierChartFunction X v anchor) (interior T) u =
        fderivWithin ℝ (fun y : A.direction => g (L y)) (interior T) u := by
    exact fderivWithin_congr' heq_on hu
  have hLu : L u = x.1 := by
    simpa [A, L, u] using carrierChartToAmbient_chartPoint X anchor x
  have hgdiff : DifferentiableWithinAt ℝ g (intrinsicInterior ℝ X) (L u) := by
    rw [hLu]
    exact hvInt.differentiableOn_one x.1 hx
  have hLhas : HasFDerivWithinAt (fun y : A.direction => L y) L.contLinear
      (interior T) u := by
    rw [L.decomp]
    exact L.contLinear.hasFDerivWithinAt.add_const (L 0)
  have hLdiff : DifferentiableWithinAt ℝ (fun y : A.direction => L y) (interior T) u :=
    hLhas.differentiableWithinAt
  have hmap : Set.MapsTo (fun y : A.direction => L y) (interior T)
      (intrinsicInterior ℝ X) := by
    intro y hy
    simpa [A, T, L] using
      carrierChartToAmbient_mem_intrinsicInterior_of_mem_interior_chartSet X anchor hy
  have hcomp :
      fderivWithin ℝ (fun y : A.direction => g (L y)) (interior T) u =
        (fderivWithin ℝ g (intrinsicInterior ℝ X) (L u)).comp
          (fderivWithin ℝ (fun y : A.direction => L y) (interior T) u) := by
    exact fderivWithin_comp' (x := u) hgdiff hLdiff hmap hsrcUniq
  have hLder :
      fderivWithin ℝ (fun y : A.direction => L y) (interior T) u = L.contLinear := by
    exact hLhas.fderivWithin hsrcUniq
  have hLlin : L.contLinear du = L du - L 0 := by
    simpa [vsub_eq_sub] using L.contLinear_map_vsub du 0
  have hLdu_apply : L du = (du : E) + anchor.1 := by
    let a : A := ⟨anchor.1, subset_affineSpan ℝ X anchor.2⟩
    change (((AffineIsometryEquiv.vaddConst ℝ a).toContinuousAffineEquiv.toContinuousAffineMap
        du : A) : E) = (du : E) + anchor.1
    simp [a]
  have hLzero : L 0 = anchor.1 := by
    let a : A := ⟨anchor.1, subset_affineSpan ℝ X anchor.2⟩
    change (((AffineIsometryEquiv.vaddConst ℝ a).toContinuousAffineEquiv.toContinuousAffineMap
        (0 : A.direction) : A) : E) = anchor.1
    simp [a]
  have hLdu : L.contLinear du = z.1 - x.1 := by
    rw [hLlin, hLdu_apply, hLzero]
    simp [du]
  change (fderivWithin ℝ (carrierChartFunction X v anchor) T u) du =
    (fderivWithin ℝ g (intrinsicInterior ℝ X) x.1) (z.1 - x.1)
  calc
    (fderivWithin ℝ (carrierChartFunction X v anchor) T u) du
        = (fderivWithin ℝ (fun y : A.direction => g (L y)) (interior T) u) du := by
          rw [hleft_restrict, hleft_congr]
    _ = ((fderivWithin ℝ g (intrinsicInterior ℝ X) (L u)).comp
          (fderivWithin ℝ (fun y : A.direction => L y) (interior T) u)) du := by
          rw [hcomp]
    _ = (fderivWithin ℝ g (intrinsicInterior ℝ X) x.1) (z.1 - x.1) := by
          rw [hLder]
          simp [ContinuousLinearMap.comp_apply, hLdu, hLu]

/-- The carrier-relative gradient selected in a fixed affine-span chart is continuous.

If `X` is convex and the totalized carrier potential `v` is `C¹` on `X`, then the
affine-span chart gradient `carrierGradientFrom X v anchor` is continuous on the
carrier subtype.

Layer: Model | Gap: Level 1 (carrier chart gradient continuity)
Proof: pass to the affine-span direction chart, use `UniqueDiffOn` for convex
  chart sets and `ContDiffOn.continuousOn_fderivWithin` to get continuity of
  the within derivative. Convert derivatives to gradients by the Riesz
  equivalence and compose with the continuous chart point map and subtype
  inclusion.
Source: Mathlib finite-dimensional smooth calculus, convex `UniqueDiffOn`, and
  continuous linear map APIs
Used in: stochastic mirror descent carrier-gradient continuity for prox-step
  displacement identities
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem carrierGradientFrom_continuous
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (X : Set E) (v : {x : E // x ∈ X} → ℝ) (anchor : {x : E // x ∈ X})
    (hX : Convex ℝ X) (hv : ContDiffOn ℝ 1 (totalizeOn X v) X) :
    Continuous (fun x : {x : E // x ∈ X} => carrierGradientFrom X v anchor x) := by
  classical
  let A : AffineSubspace ℝ E := affineSpan ℝ X
  haveI : Nonempty A := ⟨⟨anchor.1, subset_affineSpan ℝ X anchor.2⟩⟩
  haveI : IsClosed ((A.direction : Submodule ℝ E) : Set E) :=
    A.direction.closed_of_finiteDimensional
  haveI : IsUniformAddGroup A.direction := A.direction.toAddSubgroup.isUniformAddGroup
  let instComplete : CompleteSpace A.direction := FiniteDimensional.complete ℝ A.direction
  let T : Set A.direction := carrierChartSet X anchor
  let f : A.direction → ℝ := carrierChartFunction X v anchor
  let grad : A.direction → A.direction :=
    fun u => @gradientWithin ℝ A.direction _ _ _ instComplete f T u
  have hTuniq : UniqueDiffOn ℝ T := carrierChartSet_uniqueDiffOn X anchor hX
  have hf : ContDiffOn ℝ 1 f T := carrierChartFunction_contDiffOn X v anchor hv
  have hfder : ContinuousOn (fderivWithin ℝ f T) T := by
    exact hf.continuousOn_fderivWithin hTuniq (by norm_num)
  have hgradT : ContinuousOn grad T := by
    let dual := @InnerProductSpace.toDual ℝ A.direction _ _ _ instComplete
    have hdual :
        ContinuousOn (dual.symm ∘ fderivWithin ℝ f T) T :=
      Continuous.comp_continuousOn dual.symm.continuous hfder
    simpa [grad, gradientWithin, dual, Function.comp_def] using hdual
  have hpoint : Continuous (fun x : {x : E // x ∈ X} => carrierChartPoint X anchor x) :=
    carrierChartPoint_continuous X anchor
  have hgrad :
      Continuous (fun x : {x : E // x ∈ X} =>
        grad (carrierChartPoint X anchor x)) := by
    exact hgradT.comp_continuous hpoint (fun x => carrierChartPoint_mem X anchor x)
  have hsubtype :
      Continuous (fun u : A.direction => (A.direction.subtypeL) u) :=
    (A.direction.subtypeL).continuous
  change Continuous (fun x : {x : E // x ∈ X} =>
    A.direction.subtypeL (grad (carrierChartPoint X anchor x)))
  exact hsubtype.comp hgrad

/-- Affine-span carrier gradients pair with feasible displacements like the ambient
`gradientWithin` on the intrinsic-interior realization of the carrier potential.

Layer: Model | Gap: Level 1 (carrier-gradient pairing transfer)
Proof: reduce the carrier gradient inner product to the chart `fderivWithin`,
  transport it through the intrinsic-interior chart derivative identity, and
  rewrite the ambient derivative using the real Riesz representation behind
  `gradientWithin`.
Source: Mathlib finite-dimensional affine subspaces, intrinsic interior, and
  inner-product duality APIs
Used in: stochastic mirror descent carrier-gradient first-order condition on
  intrinsic-interior feasible displacements
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem carrierGradientFrom_inner_eq_gradientWithin_intrinsicInterior
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {X : Set E} (v : {x : E // x ∈ X} → ℝ) (vInterior : E → ℝ)
    (anchor x z : {x : E // x ∈ X})
    (_hX : Convex ℝ X)
    (hvInt : ContDiffOn ℝ 1 vInterior (intrinsicInterior ℝ X))
    (hvInterior :
      ∀ {y : E} (hy : y ∈ intrinsicInterior ℝ X),
        vInterior y = v ⟨y, intrinsicInterior_subset hy⟩)
    (hx : x.1 ∈ intrinsicInterior ℝ X) :
    ⟪carrierGradientFrom X v anchor x, z.1 - x.1⟫_ℝ =
      ⟪gradientWithin vInterior (intrinsicInterior ℝ X) x.1, z.1 - x.1⟫_ℝ := by
  classical
  let A : AffineSubspace ℝ E := affineSpan ℝ X
  haveI : Nonempty A := ⟨⟨anchor.1, subset_affineSpan ℝ X anchor.2⟩⟩
  haveI : IsClosed ((A.direction : Submodule ℝ E) : Set E) :=
    A.direction.closed_of_finiteDimensional
  haveI : IsUniformAddGroup A.direction := A.direction.toAddSubgroup.isUniformAddGroup
  let instComplete : CompleteSpace A.direction := FiniteDimensional.complete ℝ A.direction
  letI : CompleteSpace A.direction := instComplete
  let T : Set A.direction := carrierChartSet X anchor
  let f : A.direction → ℝ := carrierChartFunction X v anchor
  let u : A.direction := carrierChartPoint X anchor x
  let du : A.direction :=
    ⟨z.1 - x.1,
      AffineSubspace.vsub_mem_direction
        (subset_affineSpan ℝ X z.2) (subset_affineSpan ℝ X x.2)⟩
  have hdu_sub : (A.direction.subtypeL) du = z.1 - x.1 := rfl
  have hvInt' : ContDiffOn ℝ 1 (totalizeOnInterior X v) (intrinsicInterior ℝ X) := by
    refine hvInt.congr ?_
    intro y hy
    exact (totalizeOnInterior_of_mem X v hy).trans (hvInterior hy).symm
  have hchart :
      (fderivWithin ℝ f T u) du =
        (fderivWithin ℝ vInterior (intrinsicInterior ℝ X) x.1) (z.1 - x.1) := by
    have hbase := carrierChart_fderivWithin_eq_intrinsicInterior_fderivWithin_on_feasible_direction
      (X := X) (v := v) (anchor := anchor) (x := x) (z := z) hvInt' hx
    have hder_congr :
        fderivWithin ℝ (totalizeOnInterior X v) (intrinsicInterior ℝ X) x.1 =
          fderivWithin ℝ vInterior (intrinsicInterior ℝ X) x.1 := by
      exact (fderivWithin_congr' (fun y hy => (hvInterior hy).trans
        (totalizeOnInterior_of_mem X v hy).symm) hx).symm
    simpa [A, T, f, u, du, hder_congr] using hbase
  have hcomp : CompleteSpace A.direction := instComplete
  calc
    ⟪carrierGradientFrom X v anchor x, z.1 - x.1⟫_ℝ
        = (fderivWithin ℝ f T u) du := by
          unfold carrierGradientFrom
          rw [← hdu_sub]
          change
            ⟪((@gradientWithin ℝ A.direction _ _ _ hcomp f T u : A.direction) : E),
              (du : E)⟫_ℝ =
              (fderivWithin ℝ f T u) du
          rw [← A.direction.coe_inner
            (@gradientWithin ℝ A.direction _ _ _ hcomp f T u) du]
          simp [gradientWithin]
          rfl
    _ = (fderivWithin ℝ vInterior (intrinsicInterior ℝ X) x.1)
          (z.1 - x.1) := hchart
    _ = ⟪gradientWithin vInterior (intrinsicInterior ℝ X) x.1,
          z.1 - x.1⟫_ℝ := by
          rw [gradientWithin]
          exact
            (InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := E)
              (x := z.1 - x.1)
              (y := fderivWithin ℝ vInterior (intrinsicInterior ℝ X) x.1)).symm

/-- The carrier gradient extension agrees with the ambient gradient at an interior point.

At a topological-interior base point of a convex carrier, `carrierGradientFrom`
recovers the ordinary ambient gradient of any `C¹` ambient extension agreeing
with the carrier potential on the intrinsic interior.

Layer: Model | Gap: Level 1 (carrier gradient bridge to ambient gradient)
Proof: `gradientWithin` is rewritten to the ambient gradient using
  `fderivWithin_of_mem_nhds`, since the intrinsic interior is a neighborhood at
  an interior point. Equality of vectors follows by testing inner products in
  arbitrary directions, moving a small positive distance inside `X`, applying
  `carrierGradientFrom_inner_eq_gradientWithin_intrinsicInterior`, and canceling
  the scalar step size.
Source: Mathlib finite-dimensional calculus, neighborhoods of interior points,
  and intrinsic-interior convex geometry APIs
Used in: stochastic mirror descent Bregman bridge from carrier gradients to
  ambient gradients at interior prox bases
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem carrierGradientFrom_eq_gradient_of_mem_interior
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {X : Set E} (v : {x : E // x ∈ X} → ℝ) (vInterior : E → ℝ)
    (anchor : {x : E // x ∈ X}) (x : {x : E // x ∈ interior X})
    (hX : Convex ℝ X) (hcont : ContDiffOn ℝ 1 vInterior (intrinsicInterior ℝ X))
    (hvInterior : ∀ {y : E} (hy : y ∈ intrinsicInterior ℝ X),
      vInterior y = v ⟨y, intrinsicInterior_subset hy⟩) :
    carrierGradientFrom X v anchor ⟨x.1, interior_subset x.2⟩ = ∇ vInterior x.1 := by
  classical
  let x' : {x : E // x ∈ X} := ⟨x.1, interior_subset x.2⟩
  have hs_nhds : intrinsicInterior ℝ X ∈ 𝓝 x.1 := by
    exact Filter.mem_of_superset (isOpen_interior.mem_nhds x.2)
      (fun w hw => interior_subset_intrinsicInterior hw)
  have hgw : gradientWithin vInterior (intrinsicInterior ℝ X) x.1 = ∇ vInterior x.1 := by
    rw [gradientWithin, gradient, fderivWithin_of_mem_nhds hs_nhds]
  apply ext_inner_right ℝ
  intro y
  obtain ⟨ε, hεpos, hεsub⟩ :=
    Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp x.2)
  let a : ℝ := ε / (2 * (‖y‖ + 1))
  have hden_pos : 0 < 2 * (‖y‖ + 1) := by
    nlinarith [norm_nonneg y]
  have ha_pos : 0 < a := by
    dsimp [a]
    positivity
  have hmul_lt : a * ‖y‖ < ε := by
    have hnorm_lt : ‖y‖ < 2 * (‖y‖ + 1) := by
      nlinarith [norm_nonneg y]
    dsimp [a]
    rw [div_mul_eq_mul_div]
    rw [div_lt_iff₀ hden_pos]
    nlinarith [hεpos, hnorm_lt]
  have hzmem : x.1 + a • y ∈ X := by
    apply hεsub
    rw [Metric.mem_ball, dist_eq_norm]
    have hsub : x.1 + a • y - x.1 = a • y := by abel
    rw [hsub, norm_smul]
    simpa [Real.norm_eq_abs, abs_of_pos ha_pos] using hmul_lt
  let z : {x : E // x ∈ X} := ⟨x.1 + a • y, hzmem⟩
  have hinner :
      ⟪carrierGradientFrom X v anchor x', z.1 - x.1⟫_ℝ =
        ⟪gradientWithin vInterior (intrinsicInterior ℝ X) x.1, z.1 - x.1⟫_ℝ := by
    simpa [carrierGradientFrom] using
      carrierGradientFrom_inner_eq_gradientWithin_intrinsicInterior
        (X := X) (v := v) (vInterior := vInterior) anchor x' z hX hcont
        (by
          intro y hy
          simpa using hvInterior hy) (interior_subset_intrinsicInterior x.2)
  have hdisp : z.1 - x.1 = a • y := by
    dsimp [z]
    abel
  have hcancel :
      a * ⟪carrierGradientFrom X v anchor x', y⟫_ℝ =
        a * ⟪gradientWithin vInterior (intrinsicInterior ℝ X) x.1, y⟫_ℝ := by
    simpa [hdisp, inner_smul_right] using hinner
  have hcancel' := mul_left_cancel₀ (ne_of_gt ha_pos) hcancel
  simpa [hgw] using hcancel'

/-- Ambient totalization of a carrier potential to the surrounding space.

The potential `v`, originally defined only on feasible points of `X`, is exposed
as an ambient function `E → ℝ` by totalizing it on `X`. This lets stochastic
mirror descent state potential and prox expressions over the ambient carrier
while preserving the feasible-point interpretation.

Layer: Model | Concept: Objective
Proof: (definitional construction; ambient wrapper for a subtype-indexed
  carrier potential using `totalizeOn`).
Source: Mathlib Set and Subtype coercion APIs
Used in: stochastic mirror descent totalized carrier potential on the feasible
  set `X`
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
noncomputable def carrierPotentialAmbient
    {E : Type*} (X : Set E) (v : {x : E // x ∈ X} → ℝ) : E → ℝ :=
  totalizeOn X v

/-- The ambient carrier potential restricts to the intrinsic carrier potential on feasible points.

For a feasible point `x ∈ X`, the ambient totalization
`carrierPotentialAmbient X v` evaluates to the original subtype-indexed
potential `v ⟨x, hx⟩`.

Layer: Model | Gap: Level 0 (carrier potential ambient restriction)
Proof: applies the set-totalization membership rule `totalizeOn_of_mem`, using
  the feasible-point witness to identify the ambient value with the subtype
  value.
Source: Mathlib Set and Subtype APIs
Used in: stochastic mirror descent transfer between ambient iterates and
  carrier-restricted potentials
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
@[simp]
theorem carrierPotentialAmbient_of_mem
    {E : Type*} (X : Set E) (v : {x : E // x ∈ X} → ℝ)
    {x : E} (hx : x ∈ X) :
    carrierPotentialAmbient X v x = v ⟨x, hx⟩ := by
  exact totalizeOn_of_mem X v hx

/-- Ambient totalization of a carrier potential restricted to the intrinsic interior.

This wraps a potential on feasible carrier points as an ambient-space function by
using the intrinsic-interior totalization convention for `X`.

Layer: Model | Concept: Objective
Proof: (definitional construction; ambient carrier-potential wrapper via
  `totalizeOnInterior`)
Source: Mathlib convex geometry and subtype/set coercion APIs
Used in: stochastic mirror descent potential evaluation on intrinsic-interior
  feasible points
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
noncomputable def carrierPotentialInteriorAmbient
    {E : Type*} [NormedAddCommGroup E] [Module ℝ E]
    (X : Set E) (v : {x : E // x ∈ X} → ℝ) : E → ℝ :=
  totalizeOnInterior X v

/-- The intrinsic-interior ambient carrier potential evaluates to the original
subtype potential on intrinsic-interior feasible points.

Layer: Model | Gap: Level 0 (carrier potential interior evaluation)
Proof: by rfl after unfolding through `totalizeOnInterior_of_mem`, using
  `intrinsicInterior_subset` to coerce an intrinsic-interior point into `X`.
Source: Mathlib convex geometry intrinsic-interior and subtype coercion APIs
Used in: stochastic mirror descent carrier potential evaluation on feasible
  interior iterates
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
@[simp]
theorem carrierPotentialInteriorAmbient_of_mem
    {E : Type*} [NormedAddCommGroup E] [Module ℝ E]
    (X : Set E) (v : {x : E // x ∈ X} → ℝ)
    {x : E} (hx : x ∈ intrinsicInterior ℝ X) :
    carrierPotentialInteriorAmbient X v x = v ⟨x, intrinsicInterior_subset hx⟩ := by
  exact totalizeOnInterior_of_mem X v hx

/-- The ambient carrier potential is `C¹` on the intrinsic interior.

If a carrier satisfies `ContDiffOnInterior X v`, then its ambient interior
totalization has `ContDiffOn ℝ 1` regularity on `intrinsicInterior ℝ X`.

Layer: Model | Gap: Level 0 (intrinsic-interior carrier potential smoothness)
Proof: unfold the carrier totalization definitions and use the `ContDiffOn`
  component of `ContDiffOnInterior`; `simpa` transports it to the ambient form.
Source: Mathlib analysis/calculus/cont_diff on sets and intrinsic-interior set APIs
Used in: stochastic mirror descent distance-generating function regularity on the prox domain
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem carrierPotential_contDiffOn_intrinsicInterior
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X : Set E} {v : {x : E // x ∈ X} → ℝ}
    (h : ContDiffOnInterior X v) :
    ContDiffOn ℝ 1 (carrierPotentialInteriorAmbient X v) (intrinsicInterior ℝ X) := by
  simpa [carrierPotentialInteriorAmbient, totalizeOnInterior,
    carrierTotalizeOnIntrinsicInterior] using h.1

/-- A carrier potential remains strongly convex on the intrinsic interior after
ambient totalization.

If the subtype carrier potential is `μ`-strongly convex on the intrinsic interior
of `X`, then its ambient totalization `carrierPotentialInteriorAmbient X v` is
`μ`-strongly convex on `intrinsicInterior ℝ X`.

Layer: Model | Gap: Level 0 (intrinsic-interior carrier strong-convexity transport)
Proof: by simpa after unfolding `StrongConvexOnInterior`,
  `carrierPotentialInteriorAmbient`, `totalizeOnInterior`, and
  `carrierTotalizeOnIntrinsicInterior`.
Source: Mathlib convex analysis APIs for strong convexity on sets and intrinsic
  interiors
Used in: stochastic mirror descent distance-generating function interior
  strong-convexity check
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem carrierPotential_strongConvexOn_intrinsicInterior
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X : Set E} {v : {x : E // x ∈ X} → ℝ} {μ : ℝ}
    (h : StrongConvexOnInterior X μ v) :
    StrongConvexOn (intrinsicInterior ℝ X) μ (carrierPotentialInteriorAmbient X v) := by
  simpa [StrongConvexOnInterior, carrierPotentialInteriorAmbient, totalizeOnInterior,
    carrierTotalizeOnIntrinsicInterior] using h

/-- The displacement between two feasible carrier points lies in the carrier affine-span direction.

For carrier points `x z : {x : E // x ∈ X}`, the feasible difference `z.1 - x.1`
belongs to `(affineSpan ℝ X).direction`.

Layer: Model | Gap: Level 0 (carrier feasible-difference direction)
Proof: place both subtype points in `affineSpan ℝ X` using `subset_affineSpan`,
  then apply `AffineSubspace.vsub_mem_direction`.
Source: Mathlib affine geometry affine-span and affine-subspace direction APIs
Used in: stochastic mirror descent feasible-difference direction bookkeeping
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem vsub_mem_carrierAffineSpan_direction
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (X : Set E) (x z : {x : E // x ∈ X}) :
    z.1 - x.1 ∈ (affineSpan ℝ X).direction := by
  exact AffineSubspace.vsub_mem_direction
    (subset_affineSpan ℝ X z.2) (subset_affineSpan ℝ X x.2)

/-- Carrier `C¹` regularity bundles ambient within-`C¹` smoothness, subtype continuity, and
continuous within-gradient selection.

For a carrier function `φ : {x // x ∈ X} → ℝ` and an ambient realization
`Φ : E → ℝ`, this predicate records the three regularity facts used by
carrier-level smooth optimization: `Φ` is `C¹` on `X`, `φ` is continuous in the
subtype topology, and the selected within-gradient is continuous on the carrier.

Layer: Model | Concept: Carrier
Proof: (definitional construction; bundled carrier smoothness predicate from ambient within-differentiability and subtype continuity)
Source: Mathlib within differentiability, subtype topology, and inner-product gradient APIs
Used in: nonconvex stochastic mirror descent carrier smoothness assumptions for objective and distance-generating functions
Book citation: book/FOML/StochasticMirrorDescent.json#/setup/variable_space/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
def ContDiffOnCarrier
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (X : Set E) (φ : {x : E // x ∈ X} → ℝ) (Φ : E → ℝ) : Prop :=
  ContDiffOn ℝ 1 Φ X ∧
    Continuous φ ∧
    Continuous (fun x : {x : E // x ∈ X} =>
      gradientWithin Φ X x.1)

/-- At an interior point, the within-gradient selector equals the ambient gradient.

If a real-valued function is differentiable on a set `X`, then at any ordinary
topological interior point of `X` the within derivative is an unrestricted
derivative, so Mathlib's `gradientWithin` selector agrees with `∇`.

Layer: Model | Gap: Level 1 (within-gradient interior reduction)
Proof: convert the differentiability-on hypothesis to a within-gradient at `x`,
  use that `X ∈ 𝓝 x` from `x ∈ interior X`, and promote the within derivative to
  an ambient derivative before applying uniqueness of the gradient selector.
Source: Mathlib inner-product-space calculus, Fréchet derivatives, and
  topological interior neighborhood APIs
Used in: nonconvex stochastic mirror descent carrier-gradient bridge to the
  literal ambient gradient at interior prox bases
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, two-phase randomized stochastic mirror descent -/
theorem gradientWithin_eq_gradient_of_mem_interior
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {X : Set E} {f : E → ℝ} {x : E}
    (hf : DifferentiableOn ℝ f X) (hx : x ∈ interior X) :
    gradientWithin f X x = ∇ f x := by
  have hxX : x ∈ X := interior_subset hx
  have hnhds : X ∈ 𝓝 x := by
    exact Filter.mem_of_superset (isOpen_interior.mem_nhds hx) interior_subset
  have hwithin : HasGradientWithinAt f (gradientWithin f X x) X x :=
    (hf x hxX).hasGradientWithinAt
  have hambient : HasGradientAt f (gradientWithin f X x) x := by
    rw [hasGradientAt_iff_hasFDerivAt]
    exact hwithin.hasFDerivWithinAt.hasFDerivAt hnhds
  exact hambient.gradient.symm

/-- Carrier `C¹` regularity makes the selected within-gradient continuous on the carrier.

The carrier smoothness predicate stores the ambient within-`C¹` fact, the
subtype continuity of the carrier function, and the continuity of the
`gradientWithin` selector; this theorem exposes the selector component as a
library-style lemma.

Layer: Model | Gap: Level 0 (carrier gradient continuity projection)
Proof: project the continuous `gradientWithin` component from the bundled
  carrier smoothness predicate.
Source: Mathlib within differentiability and inner-product gradient APIs
Used in: nonconvex stochastic mirror descent objective-gradient measurability
  and stochastic-oracle composition
Book citation: book/FOML/StochasticMirrorDescent.json#/setup/variable_space/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem carrierGradient_continuous_of_carrierContDiffOn
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {X : Set E} {φ : {x : E // x ∈ X} → ℝ} {Φ : E → ℝ}
    (hφ :
      ContDiffOn ℝ 1 Φ X ∧
        Continuous φ ∧
        Continuous (fun x : {x : E // x ∈ X} => gradientWithin Φ X x.1)) :
    Continuous (fun x : {x : E // x ∈ X} => gradientWithin Φ X x.1) := by
  exact hφ.2.2

/-- A boundary-safe objective carrier gradient agrees with the ambient gradient at interior points.

If the carrier-gradient selector is implemented by Mathlib's `gradientWithin`
for an ambient representative `F`, then `C¹` regularity of `F` on the carrier
identifies that selected gradient with the ordinary ambient gradient at every
topological interior point.

Layer: Model | Gap: Level 1 (objective carrier-gradient interior bridge)
Proof: rewrite the abstract carrier-gradient selector to `gradientWithin`, then
  apply the interior reduction theorem for within-gradients using the
  differentiability supplied by `ContDiffOn`.
Source: Mathlib inner-product-space calculus, within-gradient, and topological
  interior APIs
Used in: nonconvex stochastic mirror descent objective-gradient bridge at
  interior feasible iterates
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, two-phase randomized stochastic mirror descent -/
theorem objectiveCarrierGradient_eq_literal_of_interior
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (carrierGrad :
      (X : Set E) → ({x : E // x ∈ X} → ℝ) → {x : E // x ∈ X} → E)
    {X : Set E} {f : {x : E // x ∈ X} → ℝ} {F : E → ℝ}
    (hF : ContDiffOn ℝ 1 F X)
    (hcarrier :
      ∀ y : {x : E // x ∈ X}, carrierGrad X f y = gradientWithin F X y.1)
    (x : {x : E // x ∈ interior X}) :
    carrierGrad X f ⟨x.1, interior_subset x.2⟩ = ∇ F x.1 := by
  rw [hcarrier]
  exact gradientWithin_eq_gradient_of_mem_interior (X := X) (f := F)
    hF.differentiableOn_one x.2

/-- A stored carrier-gradient Lipschitz assumption gives the corresponding pointwise bound.

This abstracts the carrier subtype away from the stochastic mirror descent
setup: only an evaluation map into the normed ambient space, a selected gradient
map, and the Lipschitz bound are needed.

Layer: Model | Gap: Level 0 (carrier-gradient Lipschitz assumption projection)
Proof: specialize the abstract Lipschitz-gradient hypothesis at the two carrier
  points.
Source: Mathlib normed additive groups and metric Lipschitz-style inequalities
Used in: nonconvex stochastic mirror descent smooth objective-gradient bound
  before the descent inequality
Book citation: book/FOML/StochasticMirrorDescent.json#/assumptions/0/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic mirror descent -/
theorem carrierGradient_lipschitz_of_assumption
    {P E : Type*} [NormedAddCommGroup E]
    (grad : P → E) (eval : P → E) (L : ℝ)
    (h_lipschitz : ∀ x y : P, ‖grad y - grad x‖ ≤ L * ‖eval y - eval x‖)
    (x y : P) :
    ‖grad y - grad x‖ ≤ L * ‖eval y - eval x‖ := by
  exact h_lipschitz x y

/-- Carrier-defined convex functions have Haar-null-measurable ambient sublevels.

If a function on the carrier subtype is convex after the canonical ambient
totalization, then every finite-dimensional ambient sublevel cut out on the
carrier is null-measurable for additive Haar volume.

Layer: Model | Gap: Level 1 (carrier convex sublevel Haar null-measurability)
Proof: `ConvexOn.convex_le` identifies the carrier sublevel as a convex set;
  Mathlib's finite-dimensional convex-measure theorem makes convex sets
  null-measurable for additive Haar volume.
Source: Mathlib convex analysis and Haar measure APIs for finite-dimensional
  normed real vector spaces
Used in: nonconvex stochastic mirror descent simple convex term sublevel
  regularity for route-local measurability
Book citation: book/FOML/StochasticMirrorDescent.json#/setup/variable_space/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic mirror descent -/
theorem carrierConvexOn_sublevel_nullMeasurable_volume
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [MeasureTheory.Measure.IsAddHaarMeasure μ]
    (X : Set E) (h : {x : E // x ∈ X} → ℝ) (r : ℝ)
    (hh : ConvexOn ℝ X (SOptLib.totalizeOn X h)) :
    NullMeasurableSet
      {x : E | x ∈ X ∧ SOptLib.totalizeOn X h x ≤ r} μ := by
  simpa using (hh.convex_le r).nullMeasurableSet μ

/-- Boundary-safe carrier gradient of a distance-generating function.

For a feasible carrier `X`, a distance-generating function `nu : X -> R`, and
an abstract boundary-safe carrier-gradient selector, this names the selected
gradient value used in Bregman mirror-descent geometry.

Layer: Model | Concept: Carrier gradient
Proof: (definitional construction; carrier subtype function evaluated through
  an abstract boundary-safe gradient selector)
Source: Mathlib inner product spaces, set subtypes, and gradient-selector APIs
Used in: nonconvex stochastic mirror descent Bregman prox objective and
  strong-convexity gradient monotonicity
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, two-phase randomized stochastic mirror descent -/
noncomputable def distanceGeneratorCarrierGradient
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (carrierGrad :
      (X : Set E) → ({x : E // x ∈ X} → ℝ) → {x : E // x ∈ X} → E)
    (X : Set E) (nu : {x : E // x ∈ X} → ℝ)
    (x : {x : E // x ∈ X}) : E :=
  carrierGrad X nu x

/-- Carrier `C¹` regularity makes the distance-generator carrier gradient continuous.

The distance-generator gradient used in Bregman geometry is only a named
wrapper around the boundary-safe carrier within-gradient selector.  A bundled
carrier `C¹` hypothesis therefore supplies continuity of this named wrapper.

Layer: Model | Gap: Level 0 (distance-generator carrier gradient continuity)
Proof: unfold the distance-generator carrier-gradient wrapper and project the
  continuous within-gradient component from the carrier `C¹` hypothesis.
Source: Mathlib within differentiability and inner-product gradient APIs
Used in: nonconvex stochastic mirror descent prox-step continuity through
  Bregman distance-generator gradient continuity
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, two-phase randomized stochastic mirror descent -/
theorem distanceGeneratorCarrierGradient_continuous
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {X : Set E} {nu : {x : E // x ∈ X} → ℝ} {Nu : E → ℝ}
    (hnu :
      ContDiffOn ℝ 1 Nu X ∧
        Continuous nu ∧
        Continuous (fun x : {x : E // x ∈ X} => gradientWithin Nu X x.1)) :
    Continuous
      (distanceGeneratorCarrierGradient
        (fun Y _ x => gradientWithin Nu Y x.1) X nu) := by
  simpa [distanceGeneratorCarrierGradient] using
    carrierGradient_continuous_of_carrierContDiffOn (X := X) (φ := nu) (Φ := Nu) hnu

/-- The distance-generator carrier gradient agrees with the ambient gradient on interior points.

If a boundary-safe carrier-gradient selector is implemented by Mathlib's
`gradientWithin` for an ambient realization `Nu`, then differentiability of
`Nu` on the carrier makes the selected distance-generator gradient equal to the
ordinary ambient gradient at every topological-interior feasible point.

Layer: Model | Gap: Level 1 (distance-generator interior gradient bridge)
Proof: unfold the distance-generator wrapper, rewrite the carrier selector to
  `gradientWithin`, and use the interior reduction theorem for within-gradients.
Source: Mathlib inner-product-space calculus, within-gradient, and topological
  interior APIs
Used in: nonconvex stochastic mirror descent Bregman distance-generator gradient
  bridge at interior prox bases
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, two-phase randomized stochastic mirror descent -/
theorem distanceGeneratorCarrierGradient_eq_literal_of_interior
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (carrierGrad :
      (X : Set E) → ({x : E // x ∈ X} → ℝ) → {x : E // x ∈ X} → E)
    {X : Set E} {nu : {x : E // x ∈ X} → ℝ} {Nu : E → ℝ}
    (hNu : DifferentiableOn ℝ Nu X)
    (hcarrier :
      ∀ y : {x : E // x ∈ X}, carrierGrad X nu y = gradientWithin Nu X y.1)
    (x : {x : E // x ∈ interior X}) :
    distanceGeneratorCarrierGradient carrierGrad X nu ⟨x.1, interior_subset x.2⟩ =
      ∇ Nu x.1 := by
  rw [distanceGeneratorCarrierGradient, hcarrier]
  exact gradientWithin_eq_gradient_of_mem_interior (X := X) (f := Nu) hNu x.2

/-- Literal ambient gradient of a totalized carrier objective at an interior feasible point.

For a carrier `X`, an ambient realization `nuAmbient : E -> R`, and a point
known to lie in `interior X`, this names the ordinary Fréchet-gradient selector
used when no boundary-safe within-gradient extension is needed.

Layer: Model | Concept: Objective gradient
Proof: (definitional construction; ambient Fréchet-gradient selector evaluated
  at the representative of an interior carrier subtype point)
Source: Mathlib inner-product-space calculus and gradient notation APIs
Used in: nonconvex stochastic mirror descent distance-generator gradient on
  feasible interior points
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, two-phase randomized stochastic mirror descent -/
noncomputable def literalInteriorGradient
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {X : Set E} (nuAmbient : E → ℝ) (x : {x : E // x ∈ interior X}) : E :=
  ∇ nuAmbient x.1

end SOptLib

open scoped ENNReal

namespace PiLp

/-- Assembling all continuous coordinate projections of a `PiLp` point recovers the point.

For a dependent `PiLp` product, the canonical continuous linear projections
`PiLp.proj p E i` give exactly the coordinates whose `WithLp.toLp` assembly is
the original product point.

Layer: Model | Gap: Level 0 (PiLp coordinate projection assembly)
Proof: reduce the continuous projection API to the underlying `WithLp`
coordinate function and apply the definitional inverse law `WithLp.toLp_ofLp`.
Source: Mathlib `PiLp` continuous coordinate projections and `WithLp` equivalence APIs
Used in: stochastic block mirror descent reassembly of a product iterate from
  block coordinate projections
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem piLpBlockAssemble_coord
    {𝕜 : Type*} [Semiring 𝕜] {ι : Type*} {p : ℝ≥0∞} (E : ι → Type*)
    [∀ i, SeminormedAddCommGroup (E i)] [∀ i, Module 𝕜 (E i)]
    (x : PiLp p E) :
    WithLp.toLp p (fun i => PiLp.proj (𝕜 := 𝕜) p E i x) = x := by
  simp [PiLp.proj]

/-- A continuous coordinate projection applied after dependent `PiLp` assembly returns that coordinate.

For a dependent product assembled by `WithLp.toLp`, projecting with the canonical
continuous linear map `PiLp.proj p E i` recovers the original `i`th coordinate.

Layer: Model | Gap: Level 0 (PiLp coordinate projection after assembly)
Proof: unfold the continuous projection API to the underlying coordinate
  function and apply the definitional coordinate law for `WithLp.toLp`.
Source: Mathlib `PiLp` continuous coordinate projections and `WithLp` coordinate APIs
Used in: stochastic block mirror descent extraction of a sampled block from an
  assembled product iterate
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem proj_toLp
    {𝕜 : Type*} [Semiring 𝕜] {ι : Type*} {p : ℝ≥0∞} (E : ι → Type*)
    [∀ i, SeminormedAddCommGroup (E i)] [∀ i, Module 𝕜 (E i)]
    (y : ∀ i, E i) (i : ι) :
    PiLp.proj (𝕜 := 𝕜) p E i (WithLp.toLp p y) = y i := by
  simp [PiLp.proj]

end PiLp

namespace SOptLib

/-- Carrier-chart gradients pair with feasible displacements like an ambient
`gradientWithin` for a differentiable realization on the same carrier.

If a carrier-defined function `v` agrees on `X` with an ambient realization
`ν`, then the fixed-anchor carrier gradient at any feasible base point `z`
has the same inner product against every feasible displacement `x - z` as
Mathlib's `gradientWithin ν X z`.

Layer: Model | Gap: Level 1 (boundary-safe carrier-gradient pairing transfer)
Proof: unfold the carrier gradient to the affine-span chart derivative, use
  within-derivative congruence and the affine chart chain rule to transport
  the derivative to `ν` on `X`, then rewrite both derivatives through the real
  Riesz representation behind `gradientWithin`.
Source: Mathlib finite-dimensional affine subspaces, within-derivative chain
  rule, convex unique-differentiability, and inner-product duality APIs
Used in: stochastic block mirror descent boundary-safe block Bregman formula
  and carrier-gradient prox optimality
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/assumptions/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem carrierGradientFrom_inner_eq_gradientWithin_on_feasible_direction
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {X : Set E} (v : {x : E // x ∈ X} → ℝ) (ν : E → ℝ)
    (anchor z x : {x : E // x ∈ X}) (hX : Convex ℝ X)
    (hνdiff : DifferentiableWithinAt ℝ ν X z.1)
    (hv_eq : ∀ y : {x : E // x ∈ X}, v y = ν y.1) :
    ⟪SOptLib.carrierGradientFrom X v anchor z, x.1 - z.1⟫_ℝ =
      ⟪gradientWithin ν X z.1, x.1 - z.1⟫_ℝ := by
  classical
  let A : AffineSubspace ℝ E := affineSpan ℝ X
  haveI : Nonempty A := ⟨⟨anchor.1, subset_affineSpan ℝ X anchor.2⟩⟩
  haveI : IsClosed ((A.direction : Submodule ℝ E) : Set E) :=
    A.direction.closed_of_finiteDimensional
  haveI : IsUniformAddGroup A.direction := A.direction.toAddSubgroup.isUniformAddGroup
  let instComplete : CompleteSpace A.direction := FiniteDimensional.complete ℝ A.direction
  letI : CompleteSpace A.direction := instComplete
  let T : Set A.direction := SOptLib.carrierChartSet X anchor
  let f : A.direction → ℝ := SOptLib.carrierChartFunction X v anchor
  let u : A.direction := SOptLib.carrierChartPoint X anchor z
  let du : A.direction :=
    ⟨x.1 - z.1,
      AffineSubspace.vsub_mem_direction
        (subset_affineSpan ℝ X x.2) (subset_affineSpan ℝ X z.2)⟩
  have hdu_sub : (A.direction.subtypeL) du = x.1 - z.1 := rfl
  have hTuniq : UniqueDiffOn ℝ T := SOptLib.carrierChartSet_uniqueDiffOn X anchor hX
  let L : A.direction →ᴬ[ℝ] E := SOptLib.carrierChartToAmbient X anchor
  have hu : u ∈ T := by
    simpa [A, T, u] using SOptLib.carrierChartPoint_mem X anchor z
  have heq_on : Set.EqOn f (fun y : A.direction => ν (L y)) T := by
    intro y hy
    have hyX : L y ∈ X := by
      simpa [A, T, L] using hy
    calc
      f y = SOptLib.totalizeOn X v (L y) := rfl
      _ = v ⟨L y, hyX⟩ := by
        exact SOptLib.totalizeOn_of_mem X v hyX
      _ = ν (L y) := hv_eq ⟨L y, hyX⟩
  have hleft_congr :
      fderivWithin ℝ f T u =
        fderivWithin ℝ (fun y : A.direction => ν (L y)) T u := by
    exact fderivWithin_congr' heq_on hu
  have hLu : L u = z.1 := by
    simpa [A, L, u] using SOptLib.carrierChartToAmbient_chartPoint X anchor z
  have hgdiff : DifferentiableWithinAt ℝ ν X (L u) := by
    simpa [hLu] using hνdiff
  have hLhas : HasFDerivWithinAt (fun y : A.direction => L y) L.contLinear T u := by
    rw [L.decomp]
    exact L.contLinear.hasFDerivWithinAt.add_const (L 0)
  have hLdiff : DifferentiableWithinAt ℝ (fun y : A.direction => L y) T u :=
    hLhas.differentiableWithinAt
  have hmap : Set.MapsTo (fun y : A.direction => L y) T X := by
    intro y hy
    simpa [A, T, L] using hy
  have hsrcUniq : UniqueDiffWithinAt ℝ T u := hTuniq u hu
  have hcomp :
      fderivWithin ℝ (fun y : A.direction => ν (L y)) T u =
        (fderivWithin ℝ ν X (L u)).comp
          (fderivWithin ℝ (fun y : A.direction => L y) T u) := by
    exact fderivWithin_comp' (x := u) hgdiff hLdiff hmap hsrcUniq
  have hLder :
      fderivWithin ℝ (fun y : A.direction => L y) T u = L.contLinear := by
    exact hLhas.fderivWithin hsrcUniq
  have hLlin : L.contLinear du = L du - L 0 := by
    simpa [vsub_eq_sub] using L.contLinear_map_vsub du 0
  have hLdu_apply : L du = (du : E) + anchor.1 := by
    let a : A := ⟨anchor.1, subset_affineSpan ℝ X anchor.2⟩
    change (((AffineIsometryEquiv.vaddConst ℝ a).toContinuousAffineEquiv.toContinuousAffineMap
        du : A) : E) = (du : E) + anchor.1
    simp [a]
  have hLzero : L 0 = anchor.1 := by
    let a : A := ⟨anchor.1, subset_affineSpan ℝ X anchor.2⟩
    change (((AffineIsometryEquiv.vaddConst ℝ a).toContinuousAffineEquiv.toContinuousAffineMap
        (0 : A.direction) : A) : E) = anchor.1
    simp [a]
  have hLdu : L.contLinear du = x.1 - z.1 := by
    rw [hLlin, hLdu_apply, hLzero]
    simp [du]
  have hchart :
      (fderivWithin ℝ f T u) du =
        (fderivWithin ℝ ν X z.1) (x.1 - z.1) := by
    calc
      (fderivWithin ℝ f T u) du =
          (fderivWithin ℝ (fun y : A.direction => ν (L y)) T u) du := by
            rw [hleft_congr]
      _ = ((fderivWithin ℝ ν X (L u)).comp
            (fderivWithin ℝ (fun y : A.direction => L y) T u)) du := by
            rw [hcomp]
      _ = (fderivWithin ℝ ν X z.1) (x.1 - z.1) := by
            rw [hLder]
            simp [ContinuousLinearMap.comp_apply, hLdu, hLu]
  have hcompA : CompleteSpace A.direction := instComplete
  calc
    ⟪SOptLib.carrierGradientFrom X v anchor z, x.1 - z.1⟫_ℝ
        = (fderivWithin ℝ f T u) du := by
          unfold SOptLib.carrierGradientFrom
          rw [← hdu_sub]
          change
            ⟪((@gradientWithin ℝ A.direction _ _ _ hcompA f T u : A.direction) : E),
              (du : E)⟫_ℝ =
              (fderivWithin ℝ f T u) du
          rw [← A.direction.coe_inner
            (@gradientWithin ℝ A.direction _ _ _ hcompA f T u) du]
          simp [gradientWithin]
          rfl
    _ = (fderivWithin ℝ ν X z.1) (x.1 - z.1) := hchart
    _ = ⟪gradientWithin ν X z.1, x.1 - z.1⟫_ℝ := by
          rw [gradientWithin]
          exact
            (InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := E)
              (x := x.1 - z.1)
              (y := fderivWithin ℝ ν X z.1)).symm

end SOptLib

/-- Carrier-chart gradients pair with feasible displacements like an ambient
`gradientWithin` for a differentiable realization on the same carrier.

If a carrier-defined function `v` agrees on `X` with an ambient realization
`ν`, then the fixed-anchor carrier gradient at any feasible base point `z`
has the same inner product against every feasible displacement `x - z` as
Mathlib's `gradientWithin ν X z`.

Layer: Model | Gap: Level 1 (boundary-safe carrier-gradient pairing transfer)
Proof: unfold the carrier gradient to the affine-span chart derivative, use
  within-derivative congruence and the affine chart chain rule to transport
  the derivative to `ν` on `X`, then rewrite both derivatives through the real
  Riesz representation behind `gradientWithin`.
Source: Mathlib finite-dimensional affine subspaces, within-derivative chain
  rule, convex unique-differentiability, and inner-product duality APIs
Used in: stochastic block mirror descent boundary-safe block Bregman formula
  and carrier-gradient prox optimality
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/assumptions/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem carrierGradientFrom_inner_eq_gradientWithin_on_feasible_direction
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {X : Set E} (v : {x : E // x ∈ X} → ℝ) (ν : E → ℝ)
    (anchor z x : {x : E // x ∈ X}) (hX : Convex ℝ X)
    (hνdiff : DifferentiableWithinAt ℝ ν X z.1)
    (hv_eq : ∀ y : {x : E // x ∈ X}, v y = ν y.1) :
    ⟪SOptLib.carrierGradientFrom X v anchor z, x.1 - z.1⟫_ℝ =
      ⟪gradientWithin ν X z.1, x.1 - z.1⟫_ℝ :=
  SOptLib.carrierGradientFrom_inner_eq_gradientWithin_on_feasible_direction
    v ν anchor z x hX hνdiff hv_eq

namespace SOptLib

/-- The fixed-anchor carrier gradient lies in the affine-span direction subspace.

For any carrier-subtype objective, `carrierGradientFrom X v anchor x` is built by
including a relative gradient from `(affineSpan ℝ X).direction`, so it has no
component outside that direction.

Layer: Model | Gap: Level 0 (carrier relative-gradient direction membership)
Proof: unfold `carrierGradientFrom`; the result is the value of the direction
  subtype linear inclusion, so simplification discharges subspace membership.
Source: Mathlib affine subspaces, submodule subtype linear maps, and
  inner-product gradient APIs
Used in: carrier-gradient normal-component elimination for randomized
  accelerated proximal-point and mirror-descent gradient estimates
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
theorem carrierGradientFrom_mem_direction
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {X : Set E} (v : {x : E // x ∈ X} → ℝ)
    (anchor x : {x : E // x ∈ X}) :
    carrierGradientFrom X v anchor x ∈ (affineSpan ℝ X).direction := by
  classical
  unfold carrierGradientFrom
  simp

/-- A quadratic-regularized carrier gradient stays in the carrier affine-span direction.

If the base carrier gradient is tangent to the affine span of `X`, then adding
the squared-distance regularizer gradient centered at a feasible point is still
tangent to the same affine span.

Layer: Model | Gap: Level 1 (carrier regularized-gradient direction membership)
Proof: combine the assumed base-gradient membership with the feasible
  displacement membership from `vsub_mem_carrierAffineSpan_direction`, then use
  submodule closure under scalar multiplication and addition.
Source: Mathlib affine-subspace direction submodules and real normed-module
  algebra
Used in: randomized accelerated proximal-point regularized component-gradient
  normal-component elimination
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
theorem carrier_regularizedGradient_mem_affineSpan_direction
    {E : Type*} [NormedAddCommGroup E] [Module ℝ E]
    {X : Set E} (g : {x : E // x ∈ X} → E) (μ : ℝ)
    {z : E} (hz : z ∈ X) (x : {x : E // x ∈ X})
    (hg : g x ∈ (affineSpan ℝ X).direction) :
    g x + (2 * μ) • (x.1 - z) ∈ (affineSpan ℝ X).direction := by
  have hquad_base : x.1 - z ∈ (affineSpan ℝ X).direction := by
    simpa using vsub_mem_carrierAffineSpan_direction X ⟨z, hz⟩ x
  have hquad : (2 * μ) • (x.1 - z) ∈ (affineSpan ℝ X).direction :=
    ((affineSpan ℝ X).direction).smul_mem (2 * μ) hquad_base
  exact ((affineSpan ℝ X).direction).add_mem hg hquad

/-- The canonical carrier gradient differentiates the canonical ambient totalization.

For a carrier-subtype objective `f`, if the zero-extended ambient realization
`carrierTotalizeOn X f` is differentiable within a convex carrier at `x`, then
the boundary-safe `carrierGradient X f x` is a Mathlib `HasGradientWithinAt`
gradient of that totalization on the carrier.

Layer: Model | Gap: Level 1 (carrier-gradient derivative semantics)
Proof: start from Mathlib's `gradientWithin` derivative supplied by the
  pointwise differentiability hypothesis, then use the SOptLib carrier-gradient
  feasible-direction pairing bridge to replace `gradientWithin` by the canonical
  `carrierGradient` in the little-o characterization.
Source: Mathlib within-gradient calculus and SOptLib affine-span carrier-gradient APIs
Used in: randomized accelerated proximal-point component derivative bridge for
  carrier-totalized objectives
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
theorem carrierGradient_hasGradientWithinAt_of_totalizeOn
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {X : Set E} (f : {x : E // x ∈ X} → ℝ)
    (x : {x : E // x ∈ X}) (hX : Convex ℝ X)
    (hdiff : DifferentiableWithinAt ℝ (carrierTotalizeOn X f) X x.1) :
    HasGradientWithinAt (carrierTotalizeOn X f) (carrierGradient X f x) X x.1 := by
  have hwithin :
      HasGradientWithinAt (carrierTotalizeOn X f)
        (gradientWithin (carrierTotalizeOn X f) X x.1) X x.1 :=
    hdiff.hasGradientWithinAt
  rw [hasGradientWithinAt_iff_isLittleO] at hwithin ⊢
  refine (Asymptotics.isLittleO_congr ?_ Filter.EventuallyEq.rfl).mp hwithin
  exact eventually_nhdsWithin_of_forall (fun y hy => by
    have hinner :=
      carrierGradientFrom_inner_eq_gradientWithin_on_feasible_direction
        (X := X) (v := f) (ν := carrierTotalizeOn X f) x x ⟨y, hy⟩ hX hdiff
        (by
          intro u
          simp [carrierTotalizeOn, u.2])
    change
      carrierTotalizeOn X f y - carrierTotalizeOn X f x.1 -
          ⟪gradientWithin (carrierTotalizeOn X f) X x.1, y - x.1⟫_ℝ =
        carrierTotalizeOn X f y - carrierTotalizeOn X f x.1 -
          ⟪carrierGradient X f x, y - x.1⟫_ℝ
    rw [← hinner]
    simp [carrierGradient])

end SOptLib
