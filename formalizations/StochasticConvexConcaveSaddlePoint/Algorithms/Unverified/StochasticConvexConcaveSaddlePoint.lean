import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Bounded
import SOptLib
import SOptLib.Model.Bregman
import SOptLib.Model.Carrier
import SOptLib.Model.Iterates
import SOptLib.Model.Norms
import SOptLib.Model.Objective
import SOptLib.Model.Prox
import SOptLib.Model.Saddle
import SOptLib.Model.StochasticOracle
import SOptLib.Model.Subdifferential
import SOptLib.Glue.Probability
import SOptLib.Layer0.ConvexFOC
import SOptLib.Layer0.Oracle
import SOptLib.Layer0.Objective
import SOptLib.Layer0.Subgradient
import SOptLib.Layer1.Descent
import SOptLib.Layer1.Proximal
import SOptLib.Layer1.Telescope

open MeasureTheory
open ProbabilityTheory
open scoped BigOperators InnerProductSpace

/-!
# Stochastic Convex-Concave Saddle Point

Object-layer model for Lan, Section 4.3.1.  The exported declarations keep the
algorithmic objects as definitions: product carrier `Z`, product oracle `G`, product
distance generator `ν`, its Bregman prox function `V`, the canonical mirror-prox
update, the generated iterate process, and the weighted output.
-/

namespace StochasticConvexConcaveSaddlePoint

variable {EX EY Sample : Type*}
variable [NormedAddCommGroup EX] [InnerProductSpace ℝ EX] [FiniteDimensional ℝ EX]
variable [NormedAddCommGroup EY] [InnerProductSpace ℝ EY] [FiniteDimensional ℝ EY]
variable [MeasurableSpace Sample]

local instance instEXMeasurableSpace : MeasurableSpace EX :=
  borel EX

local instance instEXBorelSpace : BorelSpace EX :=
  ⟨rfl⟩

local instance instEYMeasurableSpace : MeasurableSpace EY :=
  borel EY

local instance instEYBorelSpace : BorelSpace EY :=
  ⟨rfl⟩

/-- Ambient product space for `z = (x,y)`, with the componentwise Hilbert pairing. -/
abbrev Ambient (EX EY : Type*) :=
  WithLp 2 (EX × EY)

local instance instAmbientMeasurableSpace : MeasurableSpace (Ambient EX EY) :=
  borel (Ambient EX EY)

local instance instAmbientBorelSpace : BorelSpace (Ambient EX EY) :=
  ⟨rfl⟩

/-- The paper product carrier `X × Y`, as a set in the ambient product space. -/
def productCarrierOf (X : Set EX) (Y : Set EY) : Set (Ambient EX EY) :=
  {z | z.fst ∈ X ∧ z.snd ∈ Y}

/-- Totalized product payoff used only to state Lipschitz continuity on `X × Y`.

The value outside `X × Y` is irrelevant because all source-facing Lipschitz
claims restrict to `productCarrierOf X Y`. -/
noncomputable def productExpectedPayoffTotalized
    {X : Set EX} {Y : Set EY} {Ξ : Set Sample}
    (P : Measure {ξ : Sample // ξ ∈ Ξ})
    (Phi : {x : EX // x ∈ X} → {y : EY // y ∈ Y} → {ξ : Sample // ξ ∈ Ξ} → ℝ)
    (z : Ambient EX EY) : ℝ := by
  classical
  exact
    if hz : z ∈ productCarrierOf X Y then
      ∫ ξ, Phi ⟨z.fst, hz.1⟩ ⟨z.snd, hz.2⟩ ξ ∂P
    else
      0

/-- Source payoff expectation `φ(x,y) = ∫_Ξ Φ(x,y,ξ) dP(ξ)`. -/
noncomputable def expectedPayoff
    {X : Set EX} {Y : Set EY} {Ξ : Set Sample}
    (P : Measure {ξ : Sample // ξ ∈ Ξ})
    (Phi : {x : EX // x ∈ X} → {y : EY // y ∈ Y} → {ξ : Sample // ξ ∈ Ξ} → ℝ)
    (x : {x : EX // x ∈ X}) (y : {y : EY // y ∈ Y}) : ℝ :=
  ∫ ξ, Phi x y ξ ∂P

/-- Stated finite-valuedness of the payoff expectation. -/
def expectedPayoffWellDefined
    {X : Set EX} {Y : Set EY} {Ξ : Set Sample}
    (P : Measure {ξ : Sample // ξ ∈ Ξ})
    (Phi : {x : EX // x ∈ X} → {y : EY // y ∈ Y} → {ξ : Sample // ξ ∈ Ξ} → ℝ) :
    Prop :=
  ∀ x y, Integrable (fun ξ => Phi x y ξ) P


/-- The source set `Xᵒ` associated with a distance-generating function.

Section 3.2 defines `Xᵒ` as the feasible points that solve some linearized
DGF subproblem `argmin_{u∈X} [pᵀu + ν(u)]`. -/
def sourceDGFCore
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X : Set E) (nu : {x : E // x ∈ X} → ℝ) : Set E :=
  {x | ∃ hx : x ∈ X, ∃ p : E, ∀ u : {u : E // u ∈ X},
    ⟪p, x⟫_ℝ + nu ⟨x, hx⟩ ≤ ⟪p, u.1⟫_ℝ + nu u}

/-- Points of the paper core `Xᵒ`. -/
abbrev SourceDGFCorePoint
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X : Set E) (nu : {x : E // x ∈ X} → ℝ) :=
  {x : E // x ∈ sourceDGFCore X nu}

/-- Coercion from `Xᵒ` back to the feasible carrier `X`. -/
noncomputable def sourceDGFCoreToCarrier
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X : Set E} {nu : {x : E // x ∈ X} → ℝ}
    (x : SourceDGFCorePoint X nu) : {x : E // x ∈ X} :=
  ⟨x.1, Classical.choose x.2⟩

/-- Source-selected ambient gradient for a carrier distance generator.

The paper writes `∇ν(x)` as part of the DGF/prox interface.  The default Lean
realization is the boundary-safe projected within-gradient below, while product
DGFs can register their canonical scaled product gradient. -/
class SourceDGFGradientSelector
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (X : Set E) (nu : {x : E // x ∈ X} → ℝ) where
  grad : E → E

/-- Boundary-safe ambient gradient extension of a carrier DGF on the feasible
carrier `X`.

The paper only uses `∇ν(x)` through pairings with feasible displacements.  The
canonical Lean representative is therefore the affine-span projected
within-gradient on the carrier: it removes arbitrary normal components that
Mathlib's raw `gradientWithin` may choose on lower-dimensional carriers while
preserving all feasible-direction pairings. -/
private noncomputable def sourceDGFGradientWithinExtension
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (X : Set E) (nu : {x : E // x ∈ X} → ℝ) (x : E) : E :=
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  SOptLib.projectedWithinGradient X (SOptLib.totalizeOn X nu) x

/-- Default source-gradient selector for an arbitrary carrier DGF. -/
private noncomputable instance (priority := 10) defaultSourceDGFGradientSelector
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (X : Set E) (nu : {x : E // x ∈ X} → ℝ) :
    SourceDGFGradientSelector X nu where
  grad := sourceDGFGradientWithinExtension X nu

/-- Ambient carrier-tangent gradient of a carrier DGF. -/
noncomputable def sourceDGFGradient
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (X : Set E) (nu : {x : E // x ∈ X} → ℝ) [SourceDGFGradientSelector X nu]
    (x : E) : E :=
  SourceDGFGradientSelector.grad (X := X) (nu := nu) x

theorem sourceDGFGradient_apply
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (X : Set E) (nu : {x : E // x ∈ X} → ℝ) [SourceDGFGradientSelector X nu]
    (x : E) :
    sourceDGFGradient X nu x =
      SourceDGFGradientSelector.grad (X := X) (nu := nu) x := by
  rfl

/-- Literal ambient gradient of a carrier DGF where the paper gradient is an
ordinary unrestricted gradient. -/
noncomputable def sourceDGFLiteralGradient
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (X : Set E) (nu : {x : E // x ∈ X} → ℝ) (x : E) : E :=
  gradient (SOptLib.totalizeOn X nu) x

/-- The default carrier-tangent DGF gradient preserves Mathlib's within-gradient
pairings against feasible displacements. -/
theorem sourceDGFGradientWithinExtension_inner_eq_gradientWithin_on_feasible_direction
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {X : Set E} {nu : {x : E // x ∈ X} → ℝ}
    (z x : {x : E // x ∈ X}) :
    ⟪sourceDGFGradientWithinExtension X nu z.1, x.1 - z.1⟫_ℝ =
      ⟪gradientWithin (SOptLib.totalizeOn X nu) X z.1, x.1 - z.1⟫_ℝ := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  simpa [sourceDGFGradientWithinExtension] using
    (SOptLib.projectedWithinGradient_inner_eq_gradientWithin_of_vsub_mem_direction
      (X := X) (f := SOptLib.totalizeOn X nu) (w := z.1) (y := x.1) (z := z.1)
      x.2 z.2)

/-- The default boundary-safe source-gradient selector is a true within-gradient
representative whenever the carrier totalization is differentiable within the
feasible carrier at the base point. -/
theorem sourceDGFGradientWithinExtension_hasGradientWithinAt
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {X : Set E} {nu : {x : E // x ∈ X} → ℝ}
    (z : {x : E // x ∈ X})
    (hdiff : DifferentiableWithinAt ℝ (SOptLib.totalizeOn X nu) X z.1) :
    HasGradientWithinAt (SOptLib.totalizeOn X nu)
      (sourceDGFGradientWithinExtension X nu z.1) X z.1 := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  simpa [sourceDGFGradientWithinExtension] using
    (SOptLib.projectedWithinGradient_hasGradientWithinAt X
      (SOptLib.totalizeOn X nu) z hdiff)

/-- Prox function `V : Xᵒ × X → ℝ` associated with a carrier DGF. -/
noncomputable def sourceDGFProx
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {X : Set E} (nu : {x : E // x ∈ X} → ℝ) [SourceDGFGradientSelector X nu]
    (x : SourceDGFCorePoint X nu) (z : {z : E // z ∈ X}) : ℝ :=
  nu z - nu (sourceDGFCoreToCarrier x) -
    ⟪sourceDGFGradient X nu x.1, z.1 - x.1⟫_ℝ


/-- Source-faithful distance-generating-function predicate with modulus one.

This records the Section 3.2 boundary: convexity and continuity on `X`,
convexity of `Xᵒ`, continuous differentiability at `Xᵒ` points along feasible
carrier directions in `X`, and the modulus-one strong-convexity monotonicity
inequality with respect to the paper norm `p`.
It also records the displayed diameter maximum `(3.2.4)`, which is a source
well-definedness clause rather than a consequence of the preceding local
regularity fields in this Lean realization. -/
noncomputable def sourceDGFModulusOne
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (X : Set E) (p : E → ℝ) (nu : {x : E // x ∈ X} → ℝ)
    [SourceDGFGradientSelector X nu] :
    Prop :=
  ConvexOn ℝ X (SOptLib.totalizeOn X nu) ∧
    ContinuousOn (SOptLib.totalizeOn X nu) X ∧
    Convex ℝ (sourceDGFCore X nu) ∧
    ContDiffOn ℝ 1 (SOptLib.totalizeOn X nu) (sourceDGFCore X nu) ∧
    Continuous (fun x : SourceDGFCorePoint X nu => sourceDGFGradient X nu x.1) ∧
    (∀ x, x ∈ sourceDGFCore X nu →
      HasGradientWithinAt (SOptLib.totalizeOn X nu) (sourceDGFGradient X nu x)
        X x) ∧
    (∀ x, x ∈ sourceDGFCore X nu → ∀ x', x' ∈ sourceDGFCore X nu →
      p (x' - x) ^ 2 ≤
        ⟪sourceDGFGradient X nu x' - sourceDGFGradient X nu x, x' - x⟫_ℝ) ∧
    ∃ p : SourceDGFCorePoint X nu × {z : E // z ∈ X},
      IsMaxOn (fun q : SourceDGFCorePoint X nu × {z : E // z ∈ X} =>
        sourceDGFProx nu q.1 q.2) Set.univ p

theorem sourceDGFModulusOne.diameter_attained
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {X : Set E} {p : E → ℝ} {nu : {x : E // x ∈ X} → ℝ}
    [SourceDGFGradientSelector X nu]
    (hdgf : sourceDGFModulusOne X p nu) :
    ∃ p : SourceDGFCorePoint X nu × {z : E // z ∈ X},
      IsMaxOn (fun q : SourceDGFCorePoint X nu × {z : E // z ∈ X} =>
        sourceDGFProx nu q.1 q.2) Set.univ p := by
  rcases hdgf with ⟨_, _, _, _, _, _, _, hdiam⟩
  exact hdiam

theorem sourceDGFModulusOne.convexOn
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {X : Set E} {p : E → ℝ} {nu : {x : E // x ∈ X} → ℝ}
    [SourceDGFGradientSelector X nu]
    (hdgf : sourceDGFModulusOne X p nu) :
    ConvexOn ℝ X (SOptLib.totalizeOn X nu) := by
  exact hdgf.1

theorem sourceDGFModulusOne.continuousOn
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {X : Set E} {p : E → ℝ} {nu : {x : E // x ∈ X} → ℝ}
    [SourceDGFGradientSelector X nu]
    (hdgf : sourceDGFModulusOne X p nu) :
    ContinuousOn (SOptLib.totalizeOn X nu) X := by
  exact hdgf.2.1

theorem sourceDGFModulusOne.core_convex
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {X : Set E} {p : E → ℝ} {nu : {x : E // x ∈ X} → ℝ}
    [SourceDGFGradientSelector X nu]
    (hdgf : sourceDGFModulusOne X p nu) :
    Convex ℝ (sourceDGFCore X nu) := by
  exact hdgf.2.2.1

theorem sourceDGFModulusOne.contDiffOn_core
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {X : Set E} {p : E → ℝ} {nu : {x : E // x ∈ X} → ℝ}
    [SourceDGFGradientSelector X nu]
    (hdgf : sourceDGFModulusOne X p nu) :
    ContDiffOn ℝ 1 (SOptLib.totalizeOn X nu) (sourceDGFCore X nu) := by
  exact hdgf.2.2.2.1

theorem sourceDGFModulusOne.selectedGradient_continuous
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {X : Set E} {p : E → ℝ} {nu : {x : E // x ∈ X} → ℝ}
    [SourceDGFGradientSelector X nu]
    (hdgf : sourceDGFModulusOne X p nu) :
    Continuous (fun x : SourceDGFCorePoint X nu => sourceDGFGradient X nu x.1) := by
  exact hdgf.2.2.2.2.1

theorem sourceDGFModulusOne.gradient_hasGradientWithinAt
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {X : Set E} {p : E → ℝ} {nu : {x : E // x ∈ X} → ℝ}
    [SourceDGFGradientSelector X nu]
    (hdgf : sourceDGFModulusOne X p nu)
    {x : E} (hx : x ∈ sourceDGFCore X nu) :
    HasGradientWithinAt (SOptLib.totalizeOn X nu) (sourceDGFGradient X nu x)
      X x := by
  exact hdgf.2.2.2.2.2.1 x hx

theorem sourceDGFModulusOne.monotone
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {X : Set E} {p : E → ℝ} {nu : {x : E // x ∈ X} → ℝ}
    [SourceDGFGradientSelector X nu]
    (hdgf : sourceDGFModulusOne X p nu) :
    ∀ x, x ∈ sourceDGFCore X nu → ∀ x', x' ∈ sourceDGFCore X nu →
      p (x' - x) ^ 2 ≤
        ⟪sourceDGFGradient X nu x' - sourceDGFGradient X nu x, x' - x⟫_ℝ := by
  exact hdgf.2.2.2.2.2.2.1

/-- Existence of the source diameter maximum
`D_{X,ν}² = max_{x₁∈Xᵒ,x∈X} V(x₁,x)`.

This is a source-facing well-definedness bridge from the DGF and compact carrier
assumptions, not a primitive setup datum. -/
theorem sourceDGFDiameterSq_exists
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {X : Set E} {p : E → ℝ} {nu : {x : E // x ∈ X} → ℝ}
    [SourceDGFGradientSelector X nu]
    (_hX_nonempty : X.Nonempty) (_hX_bounded : Bornology.IsBounded X)
    (_hX_closed : IsClosed X) (_hdgf : sourceDGFModulusOne X p nu) :
    ∃ d2 : ℝ, ∃ x₁ : SourceDGFCorePoint X nu, ∃ x : {x : E // x ∈ X},
      d2 = sourceDGFProx nu x₁ x ∧
        ∀ y₁ : SourceDGFCorePoint X nu, ∀ y : {y : E // y ∈ X},
          sourceDGFProx nu y₁ y ≤ d2 := by
  rcases _hdgf.diameter_attained with ⟨pmax, hpmax⟩
  refine ⟨sourceDGFProx nu pmax.1 pmax.2, pmax.1, pmax.2, rfl, ?_⟩
  intro y₁ y
  exact (isMaxOn_univ_iff.mp hpmax) (y₁, y)


/-- Canonical squared DGF diameter `D_{X,ν}²`.

The paper writes this quantity as a maximum.  The Lean definition uses the
order-theoretic supremum of the same prox-value set; the separate theorem
`sourceDGFDiameterSq_exists` is the attained-maximum bridge. -/
noncomputable def sourceDGFDiameterSq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {X : Set E} (p : E → ℝ) (nu : {x : E // x ∈ X} → ℝ)
    [SourceDGFGradientSelector X nu]
    (_hX_nonempty : X.Nonempty) (_hX_bounded : Bornology.IsBounded X)
    (_hX_closed : IsClosed X) (_hdgf : sourceDGFModulusOne X p nu) : ℝ :=
  sSup (Set.image2 (fun q : SourceDGFCorePoint X nu => fun x : {x : E // x ∈ X} => sourceDGFProx nu q x) Set.univ Set.univ)

/-- Canonical DGF diameter `D_{X,ν}`. -/
noncomputable def sourceDGFDiameter
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {X : Set E} (p : E → ℝ) (nu : {x : E // x ∈ X} → ℝ)
    [SourceDGFGradientSelector X nu]
    (hX_nonempty : X.Nonempty) (hX_bounded : Bornology.IsBounded X)
    (hX_closed : IsClosed X) (hdgf : sourceDGFModulusOne X p nu) : ℝ :=
  Real.sqrt (sourceDGFDiameterSq p nu hX_nonempty hX_bounded hX_closed hdgf)

/-- The supremal squared diameter is realized by the Section 3.2 diameter
maximizer recorded in the DGF contract. -/
theorem sourceDGFDiameterSq_eq_attained
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {X : Set E} {p : E → ℝ} {nu : {x : E // x ∈ X} → ℝ}
    [SourceDGFGradientSelector X nu]
    (hX_nonempty : X.Nonempty) (hX_bounded : Bornology.IsBounded X)
    (hX_closed : IsClosed X) (hdgf : sourceDGFModulusOne X p nu) :
    ∃ x₁ : SourceDGFCorePoint X nu, ∃ x : {x : E // x ∈ X},
      sourceDGFDiameterSq p nu hX_nonempty hX_bounded hX_closed hdgf =
          sourceDGFProx nu x₁ x ∧
        ∀ y₁ : SourceDGFCorePoint X nu, ∀ y : {y : E // y ∈ X},
          sourceDGFProx nu y₁ y ≤
          sourceDGFDiameterSq p nu hX_nonempty hX_bounded hX_closed hdgf := by
  rcases hdgf.diameter_attained with ⟨pmax, hpmax⟩
  let x₁ : SourceDGFCorePoint X nu := pmax.1
  let x : {x : E // x ∈ X} := pmax.2
  let d2 : ℝ := sourceDGFProx nu x₁ x
  have hd2 : d2 = sourceDGFProx nu x₁ x := rfl
  have hmax : ∀ y₁ : SourceDGFCorePoint X nu, ∀ y : {y : E // y ∈ X},
      sourceDGFProx nu y₁ y ≤ d2 := by
    intro y₁ y
    simpa [x₁, x, d2] using (isMaxOn_univ_iff.mp hpmax) (y₁, y)
  let S : Set ℝ := Set.image2 (fun q : SourceDGFCorePoint X nu => fun x : {x : E // x ∈ X} => sourceDGFProx nu q x) Set.univ Set.univ
  have hS_nonempty : S.Nonempty := by
    refine ⟨sourceDGFProx nu x₁ x, ?_⟩
    exact Set.mem_image2_of_mem (Set.mem_univ x₁) (Set.mem_univ x)
  have hS_bdd : BddAbove S := by
    refine ⟨d2, ?_⟩
    rintro r ⟨q, _hq, y, _hy, rfl⟩
    exact hmax q y
  have hle : sSup S ≤ d2 := by
    refine csSup_le hS_nonempty ?_
    rintro r ⟨q, _hq, y, _hy, rfl⟩
    exact hmax q y
  have hge : d2 ≤ sSup S := by
    rw [hd2]
    exact le_csSup hS_bdd (Set.mem_image2_of_mem (Set.mem_univ x₁) (Set.mem_univ x))
  have hsup : sSup S = d2 := le_antisymm hle hge
  refine ⟨x₁, x, ?_, ?_⟩
  · rw [sourceDGFDiameterSq, hsup, hd2]
  · intro y₁ y
    simpa [sourceDGFDiameterSq, S, hsup] using hmax y₁ y

/-- If a declared prox pair maximizes all source prox values, then the supremal
squared diameter is exactly that declared value. -/
theorem sourceDGFDiameterSq_eq_of_attained_value
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {X : Set E} {p : E → ℝ} {nu : {x : E // x ∈ X} → ℝ}
    [SourceDGFGradientSelector X nu]
    (hX_nonempty : X.Nonempty) (hX_bounded : Bornology.IsBounded X)
    (hX_closed : IsClosed X) (hdgf : sourceDGFModulusOne X p nu)
    {d2 : ℝ} {x₁ : SourceDGFCorePoint X nu} {x : {x : E // x ∈ X}}
    (hd2 : d2 = sourceDGFProx nu x₁ x)
    (hmax : ∀ y₁ : SourceDGFCorePoint X nu, ∀ y : {y : E // y ∈ X},
      sourceDGFProx nu y₁ y ≤ d2) :
    sourceDGFDiameterSq p nu hX_nonempty hX_bounded hX_closed hdgf = d2 ∧
      ∀ y₁ : SourceDGFCorePoint X nu, ∀ y : {y : E // y ∈ X},
        sourceDGFProx nu y₁ y ≤
          sourceDGFDiameterSq p nu hX_nonempty hX_bounded hX_closed hdgf := by
  simpa [sourceDGFDiameterSq, Set.image2, Set.range, Function.uncurry] using
    (sSup_range_uncurry_eq_of_attained_upper_bound
      (V := fun q : SourceDGFCorePoint X nu => fun x : {x : E // x ∈ X} =>
        sourceDGFProx nu q x)
      (hd := hd2) (hupper := hmax))

/-- Product norm formula `(4.3.3)` from the source, parameterized by the two
component diameter constants. -/
noncomputable def sourceProductNorm
    (normX : Seminorm ℝ EX) (normY : Seminorm ℝ EY) (DX DY : ℝ)
    (z : Ambient EX EY) : ℝ :=
  Real.sqrt ((normX z.fst) ^ 2 / (2 * DX ^ 2) +
    (normY z.snd) ^ 2 / (2 * DY ^ 2))


/-- Product DGF formula
`ν(x,y) = ν_X(x)/(2D_X^2) + ν_Y(y)/(2D_Y^2)` from Section 4.3.1. -/
noncomputable def sourceProductDGF
    (X : Set EX) (Y : Set EY)
    (nuX : {x : EX // x ∈ X} → ℝ) (nuY : {y : EY // y ∈ Y} → ℝ)
    (DX DY : ℝ) (z : {z : Ambient EX EY // z ∈ productCarrierOf X Y}) : ℝ :=
  nuX ⟨z.1.fst, z.2.1⟩ / (2 * DX ^ 2) +
    nuY ⟨z.1.snd, z.2.2⟩ / (2 * DY ^ 2)

/-- Source-facing setup data for the stochastic convex-concave saddle-point model.

The primitive fields are exactly problem data, algorithm parameters, and stated
carrier assumptions from Section 4.3.  Objects such as `Z`, `G`, `ν`, `V`, `z₁`,
the prox update, iterates, and weighted outputs are defined below from these fields. -/
structure Setup (EX EY Sample : Type*)
    [NormedAddCommGroup EX] [InnerProductSpace ℝ EX] [FiniteDimensional ℝ EX]
    [NormedAddCommGroup EY] [InnerProductSpace ℝ EY] [FiniteDimensional ℝ EY]
    [MeasurableSpace Sample] where
  /-- `book/FOML/StochasticConvexConcaveSaddlePoint.json#/assumptions/0/description`:
  `X ⊂ Rn` is nonempty bounded closed convex. -/
  X : Set EX
  /-- `book/FOML/StochasticConvexConcaveSaddlePoint.json#/assumptions/0/description`:
  `Y ⊂ Rm` is nonempty bounded closed convex. -/
  Y : Set EY
  /-- `book/FOML/StochasticConvexConcaveSaddlePoint.json#/assumptions/0/description`:
  the law of `ξ` is supported on `Ξ`. -/
  Ξ : Set Sample
  /-- Probability law `P` of the source random vector, modeled directly on the support
  subtype `Ξ`. -/
  P : Measure {ξ : Sample // ξ ∈ Ξ}
  /-- `book/FOML/StochasticConvexConcaveSaddlePoint.json#/assumptions/1/description`:
  stochastic payoff kernel `Φ : X × Y × Ξ → ℝ`. -/
  Phi : {x : EX // x ∈ X} → {y : EY // y ∈ Y} → {ξ : Sample // ξ ∈ Ξ} → ℝ
  /-- Component stochastic oracle `G_x(x,y,ξ)` from Assumption 7. -/
  Gx : {x : EX // x ∈ X} → {y : EY // y ∈ Y} → {ξ : Sample // ξ ∈ Ξ} → EX
  /-- Component stochastic oracle `G_y(x,y,ξ)` from Assumption 7. -/
  Gy : {x : EX // x ∈ X} → {y : EY // y ∈ Y} → {ξ : Sample // ξ ∈ Ξ} → EY
  /-- Mean `x`-component `g_x(x,y)` from Assumption 7. -/
  gx : {x : EX // x ∈ X} → {y : EY // y ∈ Y} → EX
  /-- Mean `y`-component `g_y(x,y)` from Assumption 7. -/
  gy : {x : EX // x ∈ X} → {y : EY // y ∈ Y} → EY
  /-- Paper norm `‖·‖_X`, represented by its seminorm structure plus separation below. -/
  normX : Seminorm ℝ EX
  /-- Paper norm `‖·‖_Y`, represented by its seminorm structure plus separation below. -/
  normY : Seminorm ℝ EY
  /-- Distance-generating function `ν_X : X → ℝ`, modulus one. -/
  nuX : {x : EX // x ∈ X} → ℝ
  /-- Distance-generating function `ν_Y : Y → ℝ`, modulus one. -/
  nuY : {y : EY // y ∈ Y} → ℝ
  /-- Component oracle bound constant `M_X` from (4.3.2). -/
  MX : ℝ
  /-- Component oracle bound constant `M_Y` from (4.3.2). -/
  MY : ℝ
  /-- Stepsizes `γ_t`, indexed by positive paper time. -/
  gamma : {t : ℕ // 1 ≤ t} → ℝ
  /-- Quote class: stated setup datum.
  `book/FOML/StochasticConvexConcaveSaddlePoint.json#/assumptions/0/description`:
  `X ⊂ Rn` is "nonempty bounded closed convex". -/
  hX_nonempty : X.Nonempty
  /-- Quote class: stated setup datum.
  `book/FOML/StochasticConvexConcaveSaddlePoint.json#/assumptions/0/description`:
  `Y ⊂ Rm` is "nonempty bounded closed convex". -/
  hY_nonempty : Y.Nonempty
  /-- Quote class: stated setup datum.
  `book/FOML/StochasticConvexConcaveSaddlePoint.json#/assumptions/0/description`:
  `X ⊂ Rn` is "nonempty bounded closed convex". -/
  hX_bounded : Bornology.IsBounded X
  /-- Quote class: stated setup datum.
  `book/FOML/StochasticConvexConcaveSaddlePoint.json#/assumptions/0/description`:
  `Y ⊂ Rm` is "nonempty bounded closed convex". -/
  hY_bounded : Bornology.IsBounded Y
  /-- Quote class: stated setup datum.
  `book/FOML/StochasticConvexConcaveSaddlePoint.json#/assumptions/0/description`:
  `X ⊂ Rn` is "nonempty bounded closed convex". -/
  hX_closed : IsClosed X
  /-- Quote class: stated setup datum.
  `book/FOML/StochasticConvexConcaveSaddlePoint.json#/assumptions/0/description`:
  `Y ⊂ Rm` is "nonempty bounded closed convex". -/
  hY_closed : IsClosed Y
  /-- Quote class: stated setup datum.
  `book/FOML/StochasticConvexConcaveSaddlePoint.json#/assumptions/0/description`:
  `X ⊂ Rn` is "nonempty bounded closed convex". -/
  hX_convex : Convex ℝ X
  /-- Quote class: stated setup datum.
  `book/FOML/StochasticConvexConcaveSaddlePoint.json#/assumptions/0/description`:
  `Y ⊂ Rm` is "nonempty bounded closed convex". -/
  hY_convex : Convex ℝ Y
  /-- Quote class: stated setup datum.
  `book/FOML/StochasticConvexConcaveSaddlePoint.json#/assumptions/0/description`:
  `ξ` is a random vector with probability distribution `P` supported on `Ξ`. -/
  hP_prob : IsProbabilityMeasure P
  /-- Quote class: stated assumption.
  `book/FOML/StochasticConvexConcaveSaddlePoint.json#/assumptions/1/description`:
  for all `x ∈ X`, `y ∈ Y`, the expectation is well defined and finite valued. -/
  hPhi_integrable : expectedPayoffWellDefined P Phi
  /-- Quote class: stated assumption.
  `book/FOML/StochasticConvexConcaveSaddlePoint.json#/assumptions/1/description`:
  for every `ξ ∈ Ξ`, `Φ(x,y,ξ)` is convex in `x ∈ X`. -/
  hPhi_convex_x : ∀ y ξ, ConvexOn ℝ X (SOptLib.totalizeOn X (fun x => Phi x y ξ))
  /-- Quote class: stated assumption.
  `book/FOML/StochasticConvexConcaveSaddlePoint.json#/assumptions/1/description`:
  for every `ξ ∈ Ξ`, `Φ(x,y,ξ)` is concave in `y ∈ Y`. -/
  hPhi_concave_y : ∀ x ξ,
    ConvexOn ℝ Y (fun y => -(SOptLib.totalizeOn Y (fun y' => Phi x y' ξ) y))
  /-- Quote class: stated assumption.
  `book/FOML/StochasticConvexConcaveSaddlePoint.json#/assumptions/2/description`:
  `φ(·,·)` is Lipschitz continuous on `X × Y`. -/
  hphi_lipschitz : ∃ K : NNReal,
    LipschitzOnWith K
      (fun z : Ambient EX EY => by
        classical
        exact if hz :
            z ∈ ((WithLp.ofLp : WithLp 2 (EX × EY) → EX × EY) ⁻¹' (Set.prod X Y)) then
          ∫ ξ, Phi ⟨z.fst, hz.1⟩ ⟨z.snd, hz.2⟩ ξ ∂P
        else
          0)
      (((WithLp.ofLp : WithLp 2 (EX × EY) → EX × EY) ⁻¹' (Set.prod X Y)))
  /-- Quote class: definitional property of paper data structure.
  `book/FOML/StochasticConvexConcaveSaddlePoint.json#/assumptions/6/math`:
  product norm formulas use component norms `‖·‖_X` and `‖·‖_Y`. -/
  hnormX_separating : normX.IsSeparating
  /-- Quote class: definitional property of paper data structure.
  `book/FOML/StochasticConvexConcaveSaddlePoint.json#/assumptions/6/math`:
  product norm formulas use component norms `‖·‖_X` and `‖·‖_Y`. -/
  hnormY_separating : normY.IsSeparating
  /-- Quote class: stated setup datum.
  `book/FOML/StochasticConvexConcaveSaddlePoint.json#/assumptions/5/description`:
  `ν_X` is a distance-generating function of modulus one with respect to `‖·‖_X`. -/
  hnuX_dgf_mod_one : sourceDGFModulusOne X normX nuX
  /-- Quote class: stated setup datum.
  `book/FOML/StochasticConvexConcaveSaddlePoint.json#/assumptions/5/description`:
  `ν_Y` is a distance-generating function of modulus one with respect to `‖·‖_Y`. -/
  hnuY_dgf_mod_one : sourceDGFModulusOne Y normY nuY
  /-- Quote class: stated setup datum.
  `book/FOML/StochasticConvexConcaveSaddlePoint.json#/assumptions/5/description`
  introduces `D_X ≡ D_{X,ν_X}` via Section 3.2; the PDF Section 3.2 line before
  `(3.2.4)` states: "The following quantity DX > 0 will be used frequently". -/
  hDX_pos : 0 < sourceDGFDiameter normX nuX hX_nonempty hX_bounded hX_closed
    hnuX_dgf_mod_one
  /-- Quote class: stated setup datum.
  `book/FOML/StochasticConvexConcaveSaddlePoint.json#/assumptions/5/description`
  introduces `D_Y ≡ D_{Y,ν_Y}` via Section 3.2; Section 4.3.1 then uses it in
  the denominator of the product norm `(4.3.3)`. -/
  hDY_pos : 0 < sourceDGFDiameter normY nuY hY_nonempty hY_bounded hY_closed
    hnuY_dgf_mod_one
  /-- Quote class: stated assumption.
  PDF `First-order and stochastic optimization methods for machine learning.pdf`,
  Section 4.3.1 around `(4.3.2)`: "there exist positive constants `M_X^2`". -/
  hMX_pos : 0 < MX
  /-- Quote class: stated assumption.
  PDF `First-order and stochastic optimization methods for machine learning.pdf`,
  Section 4.3.1 around `(4.3.2)`: "there exist positive constants `M_Y^2`". -/
  hMY_pos : 0 < MY
  /-- Quote class: stated assumption.
  `book/FOML/StochasticConvexConcaveSaddlePoint.json#/assumptions/3/description`:
  Assumption 7 states that `g(x,y)` is well defined from the oracle expectations. -/
  hGx_integrable : ∀ x y, Integrable (fun ξ => Gx x y ξ) P
  /-- Quote class: stated assumption.
  `book/FOML/StochasticConvexConcaveSaddlePoint.json#/assumptions/3/description`:
  Assumption 7 states that `g(x,y)` is well defined from the oracle expectations. -/
  hGy_integrable : ∀ x y, Integrable (fun ξ => Gy x y ξ) P
  /-- Quote class: stated assumption.
  `book/FOML/StochasticConvexConcaveSaddlePoint.json#/assumptions/3/math`:
  `g_x(x,y) := E[G_x(x,y,ξ)]`. -/
  hgx_eq_expectation : ∀ x y, gx x y = ∫ ξ, Gx x y ξ ∂P
  /-- Quote class: stated assumption.
  `book/FOML/StochasticConvexConcaveSaddlePoint.json#/assumptions/3/math`:
  the product mean oracle has `-E[G_y(x,y,ξ)]` in its second component. -/
  hgy_eq_expectation : ∀ x y, gy x y = ∫ ξ, Gy x y ξ ∂P
  /-- Quote class: stated assumption / formal stochastic-oracle regularity.
  `book/FOML/StochasticConvexConcaveSaddlePoint.json#/assumptions/3/description`:
  Assumption 7 introduces a stochastic first-order oracle returning
  `G_x(x,y,ξ)`.  Joint measurability is the Lean regularity needed for this
  returned value to be sampled along generated random queries. -/
  hGx_joint_measurable :
    Measurable
      (fun p : (({x : EX // x ∈ X} × {y : EY // y ∈ Y}) × {ξ : Sample // ξ ∈ Ξ}) =>
        Gx p.1.1 p.1.2 p.2)
  /-- Quote class: stated assumption / formal stochastic-oracle regularity.
  `book/FOML/StochasticConvexConcaveSaddlePoint.json#/assumptions/3/description`:
  Assumption 7 introduces a stochastic first-order oracle returning
  `G_y(x,y,ξ)`.  Joint measurability is the Lean regularity needed for this
  returned value to be sampled along generated random queries. -/
  hGy_joint_measurable :
    Measurable
      (fun p : (({x : EX // x ∈ X} × {y : EY // y ∈ Y}) × {ξ : Sample // ξ ∈ Ξ}) =>
        Gy p.1.1 p.1.2 p.2)
  /-- Quote class: stated assumption.
  `book/FOML/StochasticConvexConcaveSaddlePoint.json#/assumptions/3/description`:
  Assumption 7 states `g_x(x,y) ∈ ∂_x φ(x,y)`. -/
  hgx_subgradient : ∀ x y,
    gx x y ∈ SOptLib.carrierSubdifferential
      (X := X) (fun x' => expectedPayoff P Phi x' y) x
  /-- Quote class: stated assumption.
  `book/FOML/StochasticConvexConcaveSaddlePoint.json#/assumptions/3/description`:
  Assumption 7 states `-g_y(x,y) ∈ ∂_y(-φ(x,y))`. -/
  hgy_subgradient : ∀ x y,
    (-gy x y) ∈ SOptLib.carrierSubdifferential
      (X := Y) (fun y' => -expectedPayoff P Phi x y') y
  /-- `book/FOML/StochasticConvexConcaveSaddlePoint.json#/assumptions/4/math`:
  `(4.3.2)` states the expected squared dual-norm bound for `G_x`; the
  integrability conjunct records that the source expectation is well defined. -/
  hGx_second_moment : ∀ x y,
    Integrable (fun ξ => (SOptLib.canonicalDualNorm normX (Gx x y ξ)) ^ 2) P ∧
      ∫ ξ, (SOptLib.canonicalDualNorm normX (Gx x y ξ)) ^ 2 ∂P ≤ MX ^ 2
  /-- `book/FOML/StochasticConvexConcaveSaddlePoint.json#/assumptions/4/math`:
  `(4.3.2)` states the expected squared dual-norm bound for `G_y`; the
  integrability conjunct records that the source expectation is well defined. -/
  hGy_second_moment : ∀ x y,
    Integrable (fun ξ => (SOptLib.canonicalDualNorm normY (Gy x y ξ)) ^ 2) P ∧
      ∫ ξ, (SOptLib.canonicalDualNorm normY (Gy x y ξ)) ^ 2 ∂P ≤ MY ^ 2
  /-- Quote class: stated algorithm parameter regime.
  PDF `First-order and stochastic optimization methods for machine learning.pdf`,
  Section 3.1 around the mirror-descent update says `γ_t > 0`; Section 4.3.1 then
  specializes to positive constant/decreasing policies recorded in
  `book/FOML/StochasticConvexConcaveSaddlePoint.json#/algorithm_spec/parameters`. -/
  hgamma_pos : ∀ t : {t : ℕ // 1 ≤ t}, 0 < gamma t

namespace Setup

variable (setup : Setup EX EY Sample)

/-- Paper time indices `t = 1, 2, ...`. -/
abbrev Time : Type _ :=
  {t : ℕ // 1 ≤ t}

/-- Paper sample carrier `Ξ`. -/
abbrev SamplePoint : Type _ :=
  {ξ : Sample // ξ ∈ setup.Ξ}

/-- Canonical sample path for the iid stream `(ξ_t)`.  Coordinate `0` is paper
time `1`. -/
abbrev SamplePath : Type _ :=
  ℕ → setup.SamplePoint

/-- The paper product carrier `Z := X × Y`. -/
def jointCarrier : Set (Ambient EX EY) :=
  ((WithLp.ofLp : WithLp 2 (EX × EY) → EX × EY) ⁻¹' (setup.X ×ˢ setup.Y))

/-- Feasible saddle-point state `z ∈ Z`. -/
abbrev Point : Type _ :=
  {z : Ambient EX EY // z ∈ setup.jointCarrier}

/-- The `x` projection of a feasible product state, as an element of `X`. -/
def xPoint (z : setup.Point) : {x : EX // x ∈ setup.X} :=
  ⟨z.1.fst, z.2.1⟩

/-- The `y` projection of a feasible product state, as an element of `Y`. -/
def yPoint (z : setup.Point) : {y : EY // y ∈ setup.Y} :=
  ⟨z.1.snd, z.2.2⟩


theorem phi_def (x : {x : EX // x ∈ setup.X}) (y : {y : EY // y ∈ setup.Y}) :
    (fun x y => SOptLib.objectiveExpectation setup.P (fun xy ξ => setup.Phi xy.1 xy.2 ξ) id (x, y)) x y = ∫ ξ, setup.Phi x y ξ ∂setup.P := by
  rfl

/-- The paper's finite-valuedness/integrability assumption for `φ`. -/
theorem phi_integrable (x : {x : EX // x ∈ setup.X}) (y : {y : EY // y ∈ setup.Y}) :
    Integrable (fun ξ => setup.Phi x y ξ) setup.P :=
  setup.hPhi_integrable x y

/-- Source assumption: for every sample, `Φ(·,y,ξ)` is convex on `X`. -/
theorem Phi_convex_in_x (y : {y : EY // y ∈ setup.Y}) (ξ : setup.SamplePoint) :
    ConvexOn ℝ setup.X (SOptLib.totalizeOn setup.X (fun x => setup.Phi x y ξ)) :=
  setup.hPhi_convex_x y ξ

/-- Source assumption: for every sample, `Φ(x,·,ξ)` is concave on `Y`. -/
theorem Phi_concave_in_y (x : {x : EX // x ∈ setup.X}) (ξ : setup.SamplePoint) :
    ConvexOn ℝ setup.Y
      (fun y => -(SOptLib.totalizeOn setup.Y (fun y' => setup.Phi x y' ξ) y)) :=
  setup.hPhi_concave_y x ξ

/-- Derived convexity of the expected payoff in the primal variable. -/
theorem phi_convex_in_x (y : {y : EY // y ∈ setup.Y}) :
    ConvexOn ℝ setup.X (SOptLib.totalizeOn setup.X (fun x => (fun x y => SOptLib.objectiveExpectation setup.P (fun xy ξ => setup.Phi xy.1 xy.2 ξ) id (x, y)) x y)) := by
  have hcarrier :
      SOptLib.ConvexOnCarrier setup.X
        (fun x : {x : EX // x ∈ setup.X} => ∫ ξ, setup.Phi x y ξ ∂setup.P) := by
    refine SOptLib.ConvexOnCarrier.integral setup.X (fun x ξ => setup.Phi x y ξ) setup.P
      setup.hX_convex ?_ ?_
    · intro ξ
      simpa [SOptLib.ConvexOnCarrier, SOptLib.totalizeOn_eq_carrierTotalizeOn] using
        setup.Phi_convex_in_x y ξ
    · intro x
      exact setup.phi_integrable x y
  simpa [SOptLib.ConvexOnCarrier, SOptLib.totalizeOn_eq_carrierTotalizeOn, SOptLib.objectiveExpectation_def,
    expectedPayoff] using hcarrier

/-- Derived concavity of the expected payoff in the dual variable. -/
theorem phi_concave_in_y (x : {x : EX // x ∈ setup.X}) :
    ConvexOn ℝ setup.Y
      (fun y => -(SOptLib.totalizeOn setup.Y (fun y' => (fun x y => SOptLib.objectiveExpectation setup.P (fun xy ξ => setup.Phi xy.1 xy.2 ξ) id (x, y)) x y') y)) := by
  have hcarrier :
      SOptLib.ConvexOnCarrier setup.Y
        (fun y : {y : EY // y ∈ setup.Y} => ∫ ξ, -setup.Phi x y ξ ∂setup.P) := by
    refine SOptLib.ConvexOnCarrier.integral setup.Y (fun y ξ => -setup.Phi x y ξ) setup.P
      setup.hY_convex ?_ ?_
    · intro ξ
      unfold SOptLib.ConvexOnCarrier
      refine ⟨setup.hY_convex, ?_⟩
      intro y hy z hz a b ha hb hab
      have hmix : a • y + b • z ∈ setup.Y := setup.hY_convex hy hz ha hb hab
      have hineq := (setup.Phi_concave_in_y x ξ).2 hy hz ha hb hab
      simpa [SOptLib.totalizeOn, SOptLib.carrierTotalizeOn, hmix, hy, hz] using hineq
    · intro y
      exact (setup.phi_integrable x y).neg
  have hconv :
      ConvexOn ℝ setup.Y
        (SOptLib.carrierTotalizeOn setup.Y
          (fun y : {y : EY // y ∈ setup.Y} => ∫ ξ, -setup.Phi x y ξ ∂setup.P)) := by
    simpa [SOptLib.ConvexOnCarrier] using hcarrier
  refine ⟨setup.hY_convex, ?_⟩
  intro y hy z hz a b ha hb hab
  have hmix : a • y + b • z ∈ setup.Y := setup.hY_convex hy hz ha hb hab
  have hineq := hconv.2 hy hz ha hb hab
  simpa [SOptLib.totalizeOn, SOptLib.carrierTotalizeOn, hmix, hy, hz, SOptLib.objectiveExpectation_def,
    expectedPayoff, integral_neg] using hineq

/-- Source assumption: `φ(·,·)` is Lipschitz continuous on `X × Y`. -/
theorem phi_lipschitz :
    ∃ K : NNReal,
      LipschitzOnWith K
        (fun z : Ambient EX EY => by
          classical
          exact if hz : z ∈ setup.jointCarrier then
            expectedPayoff setup.P setup.Phi ⟨z.fst, hz.1⟩ ⟨z.snd, hz.2⟩
          else
            0)
        setup.jointCarrier := by
  simpa [Setup.jointCarrier] using setup.hphi_lipschitz

/-- Assumption 7 well-definedness for the `x` oracle expectation. -/
theorem Gx_integrable (x : {x : EX // x ∈ setup.X}) (y : {y : EY // y ∈ setup.Y}) :
    Integrable (fun ξ => setup.Gx x y ξ) setup.P :=
  setup.hGx_integrable x y

/-- Assumption 7 well-definedness for the `y` oracle expectation. -/
theorem Gy_integrable (x : {x : EX // x ∈ setup.X}) (y : {y : EY // y ∈ setup.Y}) :
    Integrable (fun ξ => setup.Gy x y ξ) setup.P :=
  setup.hGy_integrable x y

/-- Source expectation in `(4.3.2)` is well defined for the `x`-oracle square. -/
theorem Gx_second_moment_integrable
    (x : {x : EX // x ∈ setup.X}) (y : {y : EY // y ∈ setup.Y}) :
    Integrable
      (fun ξ => (SOptLib.canonicalDualNorm setup.normX (setup.Gx x y ξ)) ^ 2) setup.P :=
  (setup.hGx_second_moment x y).1

/-- `(4.3.2)` component second-moment bound for `G_x`. -/
theorem Gx_second_moment_bound
    (x : {x : EX // x ∈ setup.X}) (y : {y : EY // y ∈ setup.Y}) :
    ∫ ξ, (SOptLib.canonicalDualNorm setup.normX (setup.Gx x y ξ)) ^ 2 ∂setup.P ≤
      setup.MX ^ 2 :=
  (setup.hGx_second_moment x y).2

/-- Source expectation in `(4.3.2)` is well defined for the `y`-oracle square. -/
theorem Gy_second_moment_integrable
    (x : {x : EX // x ∈ setup.X}) (y : {y : EY // y ∈ setup.Y}) :
    Integrable
      (fun ξ => (SOptLib.canonicalDualNorm setup.normY (setup.Gy x y ξ)) ^ 2) setup.P :=
  (setup.hGy_second_moment x y).1

/-- `(4.3.2)` component second-moment bound for `G_y`. -/
theorem Gy_second_moment_bound
    (x : {x : EX // x ∈ setup.X}) (y : {y : EY // y ∈ setup.Y}) :
    ∫ ξ, (SOptLib.canonicalDualNorm setup.normY (setup.Gy x y ξ)) ^ 2 ∂setup.P ≤
      setup.MY ^ 2 :=
  (setup.hGy_second_moment x y).2

/-- Source assumption: `ν_X` is a modulus-one DGF relative to `‖·‖_X`. -/
theorem nuX_dgf_modulus_one :
    sourceDGFModulusOne setup.X setup.normX setup.nuX :=
  setup.hnuX_dgf_mod_one

/-- Source assumption: `ν_Y` is a modulus-one DGF relative to `‖·‖_Y`. -/
theorem nuY_dgf_modulus_one :
    sourceDGFModulusOne setup.Y setup.normY setup.nuY :=
  setup.hnuY_dgf_mod_one

/-- Canonical `D_X ≡ D_{X,ν_X}` selected from the Section 3.2 maximum. -/
noncomputable def DX : ℝ :=
  sourceDGFDiameter setup.normX setup.nuX setup.hX_nonempty setup.hX_bounded
    setup.hX_closed setup.hnuX_dgf_mod_one

/-- Canonical `D_Y ≡ D_{Y,ν_Y}` selected from the Section 3.2 maximum. -/
noncomputable def DY : ℝ :=
  sourceDGFDiameter setup.normY setup.nuY setup.hY_nonempty setup.hY_bounded
    setup.hY_closed setup.hnuY_dgf_mod_one

/-- Squared source diameter selected for `X`. -/
noncomputable def DX2 : ℝ :=
  sourceDGFDiameterSq setup.normX setup.nuX setup.hX_nonempty setup.hX_bounded
    setup.hX_closed setup.hnuX_dgf_mod_one

/-- Squared source diameter selected for `Y`. -/
noncomputable def DY2 : ℝ :=
  sourceDGFDiameterSq setup.normY setup.nuY setup.hY_nonempty setup.hY_bounded
    setup.hY_closed setup.hnuY_dgf_mod_one

theorem DX_def :
    setup.DX = Real.sqrt setup.DX2 := by
  rfl

theorem DY_def :
    setup.DY = Real.sqrt setup.DY2 := by
  rfl

theorem DX_sq_eq_DX2 : setup.DX ^ 2 = setup.DX2 := by
  have hsqrt : 0 < Real.sqrt setup.DX2 := by
    simpa [Setup.DX, Setup.DX2, sourceDGFDiameter] using setup.hDX_pos
  have hDX2_nonneg : 0 ≤ setup.DX2 := le_of_lt ((Real.sqrt_pos).1 hsqrt)
  simpa [Setup.DX, Setup.DX2, sourceDGFDiameter] using Real.sq_sqrt hDX2_nonneg

theorem DY_sq_eq_DY2 : setup.DY ^ 2 = setup.DY2 := by
  have hsqrt : 0 < Real.sqrt setup.DY2 := by
    simpa [Setup.DY, Setup.DY2, sourceDGFDiameter] using setup.hDY_pos
  have hDY2_nonneg : 0 ≤ setup.DY2 := le_of_lt ((Real.sqrt_pos).1 hsqrt)
  simpa [Setup.DY, Setup.DY2, sourceDGFDiameter] using Real.sq_sqrt hDY2_nonneg

/-- Assumption 7, projected as a theorem: `g_x(x,y)=E[G_x(x,y,ξ)]`. -/
theorem gx_eq_expectation (x : {x : EX // x ∈ setup.X}) (y : {y : EY // y ∈ setup.Y}) :
    setup.gx x y = ∫ ξ, setup.Gx x y ξ ∂setup.P :=
  setup.hgx_eq_expectation x y

/-- Assumption 7, projected as a theorem: `g_y(x,y)=E[G_y(x,y,ξ)]`. -/
theorem gy_eq_expectation (x : {x : EX // x ∈ setup.X}) (y : {y : EY // y ∈ setup.Y}) :
    setup.gy x y = ∫ ξ, setup.Gy x y ξ ∂setup.P :=
  setup.hgy_eq_expectation x y

/-- Assumption 7, projected as a theorem: `g_x(x,y) ∈ ∂_x φ(x,y)`. -/
theorem gx_mem_subgradient (x : {x : EX // x ∈ setup.X}) (y : {y : EY // y ∈ setup.Y}) :
    setup.gx x y ∈ SOptLib.carrierSubdifferential
      (X := setup.X) (fun x' => (fun x y => SOptLib.objectiveExpectation setup.P (fun xy ξ => setup.Phi xy.1 xy.2 ξ) id (x, y)) x' y) x :=
  setup.hgx_subgradient x y

/-- Assumption 7, projected as a theorem: `-g_y(x,y) ∈ ∂_y(-φ(x,y))`. -/
theorem neg_gy_mem_subgradient (x : {x : EX // x ∈ setup.X})
    (y : {y : EY // y ∈ setup.Y}) :
    (-setup.gy x y) ∈ SOptLib.carrierSubdifferential
      (X := setup.Y) (fun y' => -(fun x y => SOptLib.objectiveExpectation setup.P (fun xy ξ => setup.Phi xy.1 xy.2 ξ) id (x, y)) x y') y :=
  setup.hgy_subgradient x y

/-- The product carrier unfolds to the paper formula `Z = X × Y`. -/
@[simp]
theorem jointCarrier_def (z : Ambient EX EY) :
    z ∈ setup.jointCarrier ↔ z.fst ∈ setup.X ∧ z.snd ∈ setup.Y := by
  rfl

/-- The product carrier is nonempty because both component carriers are nonempty. -/
theorem jointCarrier_nonempty : setup.jointCarrier.Nonempty := by
  rcases setup.hX_nonempty with ⟨x, hx⟩
  rcases setup.hY_nonempty with ⟨y, hy⟩
  exact ⟨WithLp.toLp 2 (x, y), hx, hy⟩

/-- The canonical iid sample-path law with marginal `P`. -/
noncomputable def pathMeasure : Measure setup.SamplePath :=
  SOptLib.iidStreamLaw setup.P

/-- Coordinate sample `ξ_t` read from the canonical iid stream. -/
def sampleAt (t : Time) (ω : setup.SamplePath) : setup.SamplePoint :=
  ω (t.1 - 1)

/-- The canonical iid path law is a probability measure. -/
theorem pathMeasure_isProbabilityMeasure : IsProbabilityMeasure setup.pathMeasure := by
  letI : IsProbabilityMeasure setup.P := setup.hP_prob
  simpa [Setup.pathMeasure] using (SOptLib.iidStreamLaw_isProbabilityMeasure setup.P)

/-- Every paper-time coordinate of the canonical stream has marginal law `P`. -/
theorem sampleAt_law (t : Time) :
    Measure.map (setup.sampleAt t) setup.pathMeasure = setup.P := by
  letI : IsProbabilityMeasure setup.P := setup.hP_prob
  simpa [Setup.pathMeasure, Setup.sampleAt] using
    (SOptLib.iidStreamLaw_map_eval setup.P (t.1 - 1))

/-- Coordinate samples of the canonical iid stream are measurable. -/
theorem sampleAt_measurable (t : Time) :
    Measurable (setup.sampleAt t) := by
  simpa [Setup.sampleAt] using
    (measurable_pi_apply (t.1 - 1) :
      Measurable (fun ω : setup.SamplePath => ω (t.1 - 1)))

/-- Coordinate samples of the canonical iid stream are a.e. measurable. -/
theorem sampleAt_aemeasurable (t : Time) :
    AEMeasurable (setup.sampleAt t) setup.pathMeasure :=
  (setup.sampleAt_measurable t).aemeasurable

/-- The stochastic product oracle
`G(x,y,ξ) = [G_x(x,y,ξ); -G_y(x,y,ξ)]` from Assumption 7. -/
def stochasticOracle (z : setup.Point) (ξ : setup.SamplePoint) : Ambient EX EY :=
  WithLp.toLp 2
    (setup.Gx (setup.xPoint z) (setup.yPoint z) ξ,
      -setup.Gy (setup.xPoint z) (setup.yPoint z) ξ)

/-- The mean product oracle
`g(x,y) = [g_x(x,y); -g_y(x,y)]` from Assumption 7. -/
def meanOracle (z : setup.Point) : Ambient EX EY :=
  WithLp.toLp 2
    (setup.gx (setup.xPoint z) (setup.yPoint z),
      -setup.gy (setup.xPoint z) (setup.yPoint z))

@[simp]
theorem stochasticOracle_def (z : setup.Point) (ξ : setup.SamplePoint) :
    setup.stochasticOracle z ξ =
      WithLp.toLp 2
        (setup.Gx (setup.xPoint z) (setup.yPoint z) ξ,
          -setup.Gy (setup.xPoint z) (setup.yPoint z) ξ) := by
  rfl

@[simp]
theorem meanOracle_def (z : setup.Point) :
    setup.meanOracle z =
      WithLp.toLp 2
        (setup.gx (setup.xPoint z) (setup.yPoint z),
          -setup.gy (setup.xPoint z) (setup.yPoint z)) := by
  rfl


/-- Measurability of the feasible product-coordinate map `z ↦ (x,y)`. -/
private theorem pointXY_measurable :
    Measurable (fun z : setup.Point => (setup.xPoint z, setup.yPoint z)) := by
  have hz : Measurable (fun z : setup.Point => (z : Ambient EX EY)) :=
    measurable_subtype_coe
  have hxval : Measurable (fun z : setup.Point => (z : Ambient EX EY).fst) :=
    (WithLp.continuous_fst 2 EX EY).measurable.comp hz
  have hyval : Measurable (fun z : setup.Point => (z : Ambient EX EY).snd) :=
    (WithLp.continuous_snd 2 EX EY).measurable.comp hz
  have hx : Measurable (fun z : setup.Point => setup.xPoint z) := by
    change Measurable
      (fun z : setup.Point => (⟨(z : Ambient EX EY).fst, z.2.1⟩ :
        {x : EX // x ∈ setup.X}))
    exact hxval.subtype_mk
  have hy : Measurable (fun z : setup.Point => setup.yPoint z) := by
    change Measurable
      (fun z : setup.Point => (⟨(z : Ambient EX EY).snd, z.2.2⟩ :
        {y : EY // y ∈ setup.Y}))
    exact hyval.subtype_mk
  exact hx.prod hy

/-- Joint measurability of the product stochastic oracle `G(z,ξ)`. -/
theorem stochasticOracle_measurable :
    Measurable (fun p : setup.Point × setup.SamplePoint =>
      setup.stochasticOracle p.1 p.2) := by
  classical
  let q :
      setup.Point × setup.SamplePoint →
        ({x : EX // x ∈ setup.X} × {y : EY // y ∈ setup.Y}) × setup.SamplePoint :=
    fun p => ((setup.xPoint p.1, setup.yPoint p.1), p.2)
  have hq : Measurable q := by
    unfold q
    exact ((setup.pointXY_measurable).comp measurable_fst).prod measurable_snd
  have hx :
      Measurable (fun p : setup.Point × setup.SamplePoint =>
        setup.Gx (setup.xPoint p.1) (setup.yPoint p.1) p.2) := by
    simpa [q] using setup.hGx_joint_measurable.comp hq
  have hy :
      Measurable (fun p : setup.Point × setup.SamplePoint =>
        setup.Gy (setup.xPoint p.1) (setup.yPoint p.1) p.2) := by
    simpa [q] using setup.hGy_joint_measurable.comp hq
  have hpair :
      Measurable (fun p : setup.Point × setup.SamplePoint =>
        (setup.Gx (setup.xPoint p.1) (setup.yPoint p.1) p.2,
          -setup.Gy (setup.xPoint p.1) (setup.yPoint p.1) p.2)) :=
    hx.prod hy.neg
  simpa [Setup.stochasticOracle] using
    (WithLp.prod_continuous_toLp 2 EX EY).measurable.comp hpair

/-- Measurability of the `x` component of the deterministic mean oracle. -/
theorem gx_measurable :
    Measurable (fun p : {x : EX // x ∈ setup.X} × {y : EY // y ∈ setup.Y} =>
      setup.gx p.1 p.2) := by
  letI : IsProbabilityMeasure setup.P := setup.hP_prob
  have hg_eq :
      ∀ p : {x : EX // x ∈ setup.X} × {y : EY // y ∈ setup.Y},
        setup.gx p.1 p.2 =
          ∫ ξ, setup.Gx p.1 p.2 ξ ∂setup.P := by
    intro p
    exact setup.hgx_eq_expectation p.1 p.2
  simpa using
    (oracleMean_measurable_of_eq_integral
      (μ := setup.P)
      (G := fun p : {x : EX // x ∈ setup.X} × {y : EY // y ∈ setup.Y} =>
        fun ξ : setup.SamplePoint => setup.Gx p.1 p.2 ξ)
      (g := fun p : {x : EX // x ∈ setup.X} × {y : EY // y ∈ setup.Y} =>
        setup.gx p.1 p.2)
      setup.hGx_joint_measurable hg_eq)

/-- Measurability of the `y` component of the deterministic mean oracle. -/
theorem gy_measurable :
    Measurable (fun p : {x : EX // x ∈ setup.X} × {y : EY // y ∈ setup.Y} =>
      setup.gy p.1 p.2) := by
  letI : IsProbabilityMeasure setup.P := setup.hP_prob
  have hg_eq :
      ∀ p : {x : EX // x ∈ setup.X} × {y : EY // y ∈ setup.Y},
        setup.gy p.1 p.2 =
          ∫ ξ, setup.Gy p.1 p.2 ξ ∂setup.P := by
    intro p
    exact setup.hgy_eq_expectation p.1 p.2
  simpa using
    (oracleMean_measurable_of_eq_integral
      (μ := setup.P)
      (G := fun p : {x : EX // x ∈ setup.X} × {y : EY // y ∈ setup.Y} =>
        fun ξ : setup.SamplePoint => setup.Gy p.1 p.2 ξ)
      (g := fun p : {x : EX // x ∈ setup.X} × {y : EY // y ∈ setup.Y} =>
        setup.gy p.1 p.2)
      setup.hGy_joint_measurable hg_eq)

/-- Measurability of the deterministic product mean oracle `g(z)`. -/
theorem meanOracle_measurable :
    Measurable (fun z : setup.Point => setup.meanOracle z) := by
  have hx :
      Measurable (fun z : setup.Point =>
        setup.gx (setup.xPoint z) (setup.yPoint z)) :=
    setup.gx_measurable.comp setup.pointXY_measurable
  have hy :
      Measurable (fun z : setup.Point =>
        setup.gy (setup.xPoint z) (setup.yPoint z)) :=
    setup.gy_measurable.comp setup.pointXY_measurable
  have hpair :
      Measurable (fun z : setup.Point =>
        (setup.gx (setup.xPoint z) (setup.yPoint z),
          -setup.gy (setup.xPoint z) (setup.yPoint z))) :=
    hx.prod hy.neg
  simpa [Setup.meanOracle] using
    (WithLp.prod_continuous_toLp 2 EX EY).measurable.comp hpair

/-- The scaled product norm `(4.3.3)`. -/
noncomputable def productNorm (z : Ambient EX EY) : ℝ :=
  sourceProductNorm setup.normX setup.normY setup.DX setup.DY z

/-- The scaled product dual norm `(4.3.4)`. -/
noncomputable def productDualNorm (zeta : Ambient EX EY) : ℝ :=
  Real.sqrt
    (2 * setup.DX ^ 2 * (SOptLib.canonicalDualNorm setup.normX zeta.fst) ^ 2 +
      2 * setup.DY ^ 2 * (SOptLib.canonicalDualNorm setup.normY zeta.snd) ^ 2)

@[simp]
theorem productNorm_def (z : Ambient EX EY) :
    setup.productNorm z =
      Real.sqrt
        ((setup.normX z.fst) ^ 2 / (2 * setup.DX ^ 2) +
          (setup.normY z.snd) ^ 2 / (2 * setup.DY ^ 2)) := by
  rfl

@[simp]
theorem productDualNorm_def (zeta : Ambient EX EY) :
    setup.productDualNorm zeta =
      Real.sqrt
        (2 * setup.DX ^ 2 * (SOptLib.canonicalDualNorm setup.normX zeta.fst) ^ 2 +
          2 * setup.DY ^ 2 * (SOptLib.canonicalDualNorm setup.normY zeta.snd) ^ 2) := by
  rfl

/-- Product oracle second-moment constant `M`, with `M^2 = 2D_X^2M_X^2+2D_Y^2M_Y^2`. -/
noncomputable def M : ℝ :=
  Real.sqrt (2 * setup.DX ^ 2 * setup.MX ^ 2 + 2 * setup.DY ^ 2 * setup.MY ^ 2)

/-- The radicand named by the paper as `M^2`. -/
noncomputable def M2 : ℝ :=
  2 * setup.DX ^ 2 * setup.MX ^ 2 + 2 * setup.DY ^ 2 * setup.MY ^ 2

theorem M_def :
    setup.M = Real.sqrt (2 * setup.DX ^ 2 * setup.MX ^ 2 +
      2 * setup.DY ^ 2 * setup.MY ^ 2) := by
  simp [Setup.M]

theorem M2_def :
    setup.M2 = 2 * setup.DX ^ 2 * setup.MX ^ 2 + 2 * setup.DY ^ 2 * setup.MY ^ 2 := by
  rfl

/-- The square identity implicit in the paper notation `=: M^2`. -/
theorem M_sq_eq_M2 : setup.M ^ 2 = setup.M2 := by
  simpa [Setup.M, Setup.M2] using Real.sq_sqrt
    (show 0 ≤ 2 * setup.DX ^ 2 * setup.MX ^ 2 +
        2 * setup.DY ^ 2 * setup.MY ^ 2 by
      positivity)

private theorem canonicalDualNorm_neg
    {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℝ B]
    (p : Seminorm ℝ B) (v : B) :
    SOptLib.canonicalDualNorm p (-v) = SOptLib.canonicalDualNorm p v := by
  rw [SOptLib.canonicalDualNorm_eq_sSup, SOptLib.canonicalDualNorm_eq_sSup]
  congr 1
  ext r
  constructor
  · rintro ⟨d, hd, rfl⟩
    refine ⟨d, hd, ?_⟩
    simp
  · rintro ⟨d, hd, rfl⟩
    refine ⟨d, hd, ?_⟩
    simp

private theorem productDualNorm_sq_stochasticOracle_eq
    (z : setup.Point) (ξ : setup.SamplePoint) :
    (setup.productDualNorm (setup.stochasticOracle z ξ)) ^ 2 =
      2 * setup.DX ^ 2 *
          (SOptLib.canonicalDualNorm setup.normX
            (setup.Gx (setup.xPoint z) (setup.yPoint z) ξ)) ^ 2 +
        2 * setup.DY ^ 2 *
          (SOptLib.canonicalDualNorm setup.normY
            (setup.Gy (setup.xPoint z) (setup.yPoint z) ξ)) ^ 2 := by
  rw [Setup.productDualNorm_def, Setup.stochasticOracle_def]
  rw [Real.sq_sqrt]
  · simp [canonicalDualNorm_neg]
  · positivity

/-- Derived positivity of the product oracle-bound constant. -/
theorem M_pos : 0 < setup.M := by
  rw [Setup.M]
  apply Real.sqrt_pos_of_pos
  have hDX : 0 < setup.DX := by
    simpa [Setup.DX] using setup.hDX_pos
  have hDY : 0 < setup.DY := by
    simpa [Setup.DY] using setup.hDY_pos
  have hXterm : 0 < 2 * setup.DX ^ 2 * setup.MX ^ 2 := by
    exact mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) (sq_pos_of_pos hDX))
      (sq_pos_of_pos setup.hMX_pos)
  have hYterm : 0 < 2 * setup.DY ^ 2 * setup.MY ^ 2 := by
    exact mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) (sq_pos_of_pos hDY))
      (sq_pos_of_pos setup.hMY_pos)
  exact add_pos hXterm hYterm

/-- Derived positivity of the `X` DGF diameter constant. -/
theorem DX_pos : 0 < setup.DX := by
  simpa [Setup.DX] using setup.hDX_pos

/-- Derived positivity of the `Y` DGF diameter constant. -/
theorem DY_pos : 0 < setup.DY := by
  simpa [Setup.DY] using setup.hDY_pos

/-- Product-space second-moment expectation in `(4.3.5)` is well defined. -/
theorem product_oracle_second_moment_integrable (z : setup.Point) :
    Integrable (fun ξ => (setup.productDualNorm (setup.stochasticOracle z ξ)) ^ 2) setup.P := by
  let Xsq : setup.SamplePoint → ℝ := fun ξ =>
    (SOptLib.canonicalDualNorm setup.normX
      (setup.Gx (setup.xPoint z) (setup.yPoint z) ξ)) ^ 2
  let Ysq : setup.SamplePoint → ℝ := fun ξ =>
    (SOptLib.canonicalDualNorm setup.normY
      (setup.Gy (setup.xPoint z) (setup.yPoint z) ξ)) ^ 2
  have hx : Integrable Xsq setup.P := by
    simpa [Xsq] using setup.Gx_second_moment_integrable (setup.xPoint z) (setup.yPoint z)
  have hy : Integrable Ysq setup.P := by
    simpa [Ysq] using setup.Gy_second_moment_integrable (setup.xPoint z) (setup.yPoint z)
  refine ((hx.const_mul (2 * setup.DX ^ 2)).add
    (hy.const_mul (2 * setup.DY ^ 2))).congr ?_
  exact Filter.Eventually.of_forall (fun ξ => by
    simpa [Xsq, Ysq] using (productDualNorm_sq_stochasticOracle_eq (setup := setup) z ξ).symm)

/-- Product-space second-moment bound `(4.3.5)`, derived from the component bounds. -/
theorem product_oracle_second_moment_bound (z : setup.Point) :
    ∫ ξ, (setup.productDualNorm (setup.stochasticOracle z ξ)) ^ 2 ∂setup.P ≤ setup.M ^ 2 := by
  let Xsq : setup.SamplePoint → ℝ := fun ξ =>
    (SOptLib.canonicalDualNorm setup.normX
      (setup.Gx (setup.xPoint z) (setup.yPoint z) ξ)) ^ 2
  let Ysq : setup.SamplePoint → ℝ := fun ξ =>
    (SOptLib.canonicalDualNorm setup.normY
      (setup.Gy (setup.xPoint z) (setup.yPoint z) ξ)) ^ 2
  have hx_int : Integrable Xsq setup.P := by
    simpa [Xsq] using setup.Gx_second_moment_integrable (setup.xPoint z) (setup.yPoint z)
  have hy_int : Integrable Ysq setup.P := by
    simpa [Ysq] using setup.Gy_second_moment_integrable (setup.xPoint z) (setup.yPoint z)
  have hx_bound : ∫ ξ, Xsq ξ ∂setup.P ≤ setup.MX ^ 2 := by
    simpa [Xsq] using setup.Gx_second_moment_bound (setup.xPoint z) (setup.yPoint z)
  have hy_bound : ∫ ξ, Ysq ξ ∂setup.P ≤ setup.MY ^ 2 := by
    simpa [Ysq] using setup.Gy_second_moment_bound (setup.xPoint z) (setup.yPoint z)
  rw [setup.M_sq_eq_M2, Setup.M2]
  calc
    ∫ ξ, (setup.productDualNorm (setup.stochasticOracle z ξ)) ^ 2 ∂setup.P
        = ∫ ξ, 2 * setup.DX ^ 2 * Xsq ξ + 2 * setup.DY ^ 2 * Ysq ξ ∂setup.P := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (fun ξ => by
            simpa [Xsq, Ysq] using productDualNorm_sq_stochasticOracle_eq (setup := setup) z ξ)
    _ = 2 * setup.DX ^ 2 * ∫ ξ, Xsq ξ ∂setup.P +
          2 * setup.DY ^ 2 * ∫ ξ, Ysq ξ ∂setup.P := by
          rw [MeasureTheory.integral_add (hx_int.const_mul (2 * setup.DX ^ 2))
            (hy_int.const_mul (2 * setup.DY ^ 2))]
          rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    _ ≤ 2 * setup.DX ^ 2 * setup.MX ^ 2 + 2 * setup.DY ^ 2 * setup.MY ^ 2 := by
          have hcx : 0 ≤ 2 * setup.DX ^ 2 := by positivity
          have hcy : 0 ≤ 2 * setup.DY ^ 2 := by positivity
          exact add_le_add (mul_le_mul_of_nonneg_left hx_bound hcx)
            (mul_le_mul_of_nonneg_left hy_bound hcy)

/-- Expectation over the generated stochastic process. -/
noncomputable def pathExpectation (F : setup.SamplePath → ℝ) : ℝ :=
  ∫ ω, F ω ∂setup.pathMeasure

/-- Product distance-generating function
`ν(z) := ν_X(x)/(2D_X^2) + ν_Y(y)/(2D_Y^2)`. -/
noncomputable def productPotential (z : setup.Point) : ℝ :=
  sourceProductDGF setup.X setup.Y setup.nuX setup.nuY setup.DX setup.DY z

/-- The paper product potential is the local source product DGF specialized to
`D_X` and `D_Y`. -/
theorem productPotential_eq_sourceProductDGF (z : setup.Point) :
    setup.productPotential z =
      sourceProductDGF setup.X setup.Y setup.nuX setup.nuY setup.DX setup.DY z := by
  rfl

@[simp]
theorem productDGF_def (z : setup.Point) :
    setup.productPotential z =
      setup.nuX (setup.xPoint z) / (2 * setup.DX ^ 2) +
        setup.nuY (setup.yPoint z) / (2 * setup.DY ^ 2) := by
  rfl
/-- Canonical source-selected gradient for the scaled product DGF.

For `ν(z)=ν_X(x)/(2D_X^2)+ν_Y(y)/(2D_Y^2)`, the paper gradient is the scaled
product of the component DGF gradients. -/
private noncomputable instance (priority := 2000) productDGFGradientSelector :
    SourceDGFGradientSelector setup.jointCarrier setup.productPotential where
  grad z :=
    WithLp.toLp 2
      (((2 * setup.DX ^ 2)⁻¹) • sourceDGFGradient setup.X setup.nuX z.fst,
        ((2 * setup.DY ^ 2)⁻¹) • sourceDGFGradient setup.Y setup.nuY z.snd)

private theorem productDGFGradientSelector_apply (z : Ambient EX EY) :
    sourceDGFGradient setup.jointCarrier setup.productPotential z =
      WithLp.toLp 2
        (((2 * setup.DX ^ 2)⁻¹) • sourceDGFGradient setup.X setup.nuX z.fst,
          ((2 * setup.DY ^ 2)⁻¹) • sourceDGFGradient setup.Y setup.nuY z.snd) := by
  rfl

/-- Source prox-domain base points `Zᵒ` for the product DGF. -/
abbrev InteriorPoint : Type _ :=
  SourceDGFCorePoint setup.jointCarrier setup.productPotential

/-- Coercion from the product source core `Zᵒ` to the feasible carrier `Z`. -/
noncomputable def interiorPointToPoint (z : setup.InteriorPoint) : setup.Point :=
  sourceDGFCoreToCarrier z

/-- Measurability of the canonical coercion from `Zᵒ` to `Z`. -/
theorem interiorPointToPoint_measurable :
    Measurable (setup.interiorPointToPoint) := by
  change Measurable
    (fun z : setup.InteriorPoint =>
      (⟨(z : Ambient EX EY), Classical.choose z.2⟩ : setup.Point))
  exact (measurable_subtype_coe : Measurable (fun z : setup.InteriorPoint =>
    (z : Ambient EX EY))).subtype_mk

/-- The product DGF core is `Zᵒ = Xᵒ × Yᵒ`. -/
theorem productDGF_core_eq :
    sourceDGFCore setup.jointCarrier setup.productPotential =
      {z : Ambient EX EY |
        z.fst ∈ sourceDGFCore setup.X setup.nuX ∧
          z.snd ∈ sourceDGFCore setup.Y setup.nuY} := by
  classical
  have scaled_core_ineq_of_div_ineq :
      ∀ {a b c d s : ℝ}, 0 < s → a + b / s ≤ c + d / s → s * a + b ≤ s * c + d := by
    intro a b c d s hs h
    have hsne : s ≠ 0 := ne_of_gt hs
    have hm := mul_le_mul_of_nonneg_left h (le_of_lt hs)
    field_simp [hsne] at hm
    linarith
  have div_ineq_of_core_ineq :
      ∀ {a b c d s : ℝ}, 0 < s → a + b ≤ c + d → s⁻¹ * a + b / s ≤ s⁻¹ * c + d / s := by
    intro a b c d s hs h
    have hsne : s ≠ 0 := ne_of_gt hs
    have hmul := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (le_of_lt hs))
    field_simp [hsne] at hmul ⊢
    linarith
  ext z
  constructor
  · intro hz
    rcases hz with ⟨hzProd, p, hmin⟩
    have hzcomp := (setup.jointCarrier_def z).1 hzProd
    constructor
    · refine ⟨hzcomp.1, (2 * setup.DX ^ 2) • p.fst, ?_⟩
      intro u
      let uz : setup.Point :=
        ⟨WithLp.toLp 2 (u.1, z.snd), (setup.jointCarrier_def _).2 ⟨u.2, hzcomp.2⟩⟩
      have htest := hmin uz
      have htest' :
          ⟪p.fst, z.fst⟫_ℝ +
              (⟪p.snd, z.snd⟫_ℝ +
                (setup.nuX ⟨z.fst, hzcomp.1⟩ / (2 * setup.DX ^ 2) +
                  setup.nuY ⟨z.snd, hzcomp.2⟩ / (2 * setup.DY ^ 2))) ≤
            ⟪p.fst, u.1⟫_ℝ +
              (⟪p.snd, z.snd⟫_ℝ +
                (setup.nuX u / (2 * setup.DX ^ 2) +
                  setup.nuY ⟨z.snd, hzcomp.2⟩ / (2 * setup.DY ^ 2))) := by
        simpa [uz, Setup.productPotential, Setup.xPoint, Setup.yPoint, WithLp.prod_inner_apply,
          add_assoc, add_left_comm, add_comm] using htest
      have hred :
          ⟪p.fst, z.fst⟫_ℝ + setup.nuX ⟨z.fst, hzcomp.1⟩ / (2 * setup.DX ^ 2) ≤
            ⟪p.fst, u.1⟫_ℝ + setup.nuX u / (2 * setup.DX ^ 2) := by
        linarith
      have hs : 0 < 2 * setup.DX ^ 2 := by
        nlinarith [setup.DX_pos]
      have hscaled := scaled_core_ineq_of_div_ineq (s := 2 * setup.DX ^ 2) hs hred
      simpa [real_inner_smul_left, mul_add, add_assoc, add_left_comm, add_comm] using hscaled
    · refine ⟨hzcomp.2, (2 * setup.DY ^ 2) • p.snd, ?_⟩
      intro u
      let uz : setup.Point :=
        ⟨WithLp.toLp 2 (z.fst, u.1), (setup.jointCarrier_def _).2 ⟨hzcomp.1, u.2⟩⟩
      have htest := hmin uz
      have htest' :
          ⟪p.fst, z.fst⟫_ℝ + ⟪p.snd, z.snd⟫_ℝ +
              (setup.nuX ⟨z.fst, hzcomp.1⟩ / (2 * setup.DX ^ 2) +
                setup.nuY ⟨z.snd, hzcomp.2⟩ / (2 * setup.DY ^ 2)) ≤
            ⟪p.fst, z.fst⟫_ℝ + ⟪p.snd, u.1⟫_ℝ +
              (setup.nuX ⟨z.fst, hzcomp.1⟩ / (2 * setup.DX ^ 2) +
                setup.nuY u / (2 * setup.DY ^ 2)) := by
        simpa [uz, Setup.productPotential, Setup.xPoint, Setup.yPoint, WithLp.prod_inner_apply]
          using htest
      have hred :
          ⟪p.snd, z.snd⟫_ℝ + setup.nuY ⟨z.snd, hzcomp.2⟩ / (2 * setup.DY ^ 2) ≤
            ⟪p.snd, u.1⟫_ℝ + setup.nuY u / (2 * setup.DY ^ 2) := by
        linarith
      have hs : 0 < 2 * setup.DY ^ 2 := by
        nlinarith [setup.DY_pos]
      have hscaled := scaled_core_ineq_of_div_ineq (s := 2 * setup.DY ^ 2) hs hred
      simpa [real_inner_smul_left, mul_add, add_assoc, add_left_comm, add_comm] using hscaled
  · intro hxy
    rcases hxy with ⟨hx, hy⟩
    rcases hx with ⟨hxmem, px, hxmin⟩
    rcases hy with ⟨hymem, py, hymin⟩
    let hprod : z ∈ setup.jointCarrier := (setup.jointCarrier_def z).2 ⟨hxmem, hymem⟩
    let q : Ambient EX EY :=
      WithLp.toLp 2 (((2 * setup.DX ^ 2)⁻¹ • px), ((2 * setup.DY ^ 2)⁻¹ • py))
    refine ⟨hprod, q, ?_⟩
    intro u
    have hsx : 0 < 2 * setup.DX ^ 2 := by
      nlinarith [setup.DX_pos]
    have hsy : 0 < 2 * setup.DY ^ 2 := by
      nlinarith [setup.DY_pos]
    have hxcore := hxmin (setup.xPoint u)
    have hycore := hymin (setup.yPoint u)
    have hxdiv := div_ineq_of_core_ineq (s := 2 * setup.DX ^ 2) hsx hxcore
    have hydiv := div_ineq_of_core_ineq (s := 2 * setup.DY ^ 2) hsy hycore
    have hadd := add_le_add hxdiv hydiv
    calc
      ⟪q, z⟫_ℝ + setup.productPotential ⟨z, hprod⟩
          = ((2 * setup.DX ^ 2)⁻¹ * ⟪px, z.fst⟫_ℝ +
              setup.nuX ⟨z.fst, hxmem⟩ / (2 * setup.DX ^ 2)) +
            ((2 * setup.DY ^ 2)⁻¹ * ⟪py, z.snd⟫_ℝ +
              setup.nuY ⟨z.snd, hymem⟩ / (2 * setup.DY ^ 2)) := by
            simp only [q, Setup.productDGF_def, Setup.xPoint, Setup.yPoint,
              WithLp.prod_inner_apply, WithLp.ofLp_fst, WithLp.ofLp_snd, real_inner_smul_left]
            ring
      _ ≤ ((2 * setup.DX ^ 2)⁻¹ * ⟪px, (setup.xPoint u).1⟫_ℝ +
              setup.nuX (setup.xPoint u) / (2 * setup.DX ^ 2)) +
            ((2 * setup.DY ^ 2)⁻¹ * ⟪py, (setup.yPoint u).1⟫_ℝ +
              setup.nuY (setup.yPoint u) / (2 * setup.DY ^ 2)) := hadd
      _ = ⟪q, u.1⟫_ℝ + setup.productPotential u := by
            simp only [q, Setup.productDGF_def, Setup.xPoint, Setup.yPoint,
              WithLp.prod_inner_apply, WithLp.ofLp_fst, WithLp.ofLp_snd, real_inner_smul_left]
            ring

/-- Boundedness of the product feasible carrier, derived from component boundedness. -/
theorem jointCarrier_bounded : Bornology.IsBounded setup.jointCarrier := by
  rw [Setup.jointCarrier]
  change
    (((WithLp.ofLp : WithLp 2 (EX × EY) → EX × EY) ⁻¹'
        (Set.prod setup.X setup.Y))ᶜ) ∈
      Filter.comap (WithLp.ofLp : WithLp 2 (EX × EY) → EX × EY)
        (Bornology.cobounded (EX × EY))
  rw [Filter.mem_comap]
  refine ⟨(Set.prod setup.X setup.Y)ᶜ, setup.hX_bounded.prod setup.hY_bounded, ?_⟩
  intro z hz
  simpa [Set.mem_compl_iff, Set.mem_prod] using hz

/-- Closedness of the product feasible carrier, derived from component closedness. -/
theorem jointCarrier_closed : IsClosed setup.jointCarrier := by
  simpa [Setup.jointCarrier, Set.prod_eq, Set.preimage, Set.mem_setOf_eq] using
    ((setup.hX_closed.preimage (WithLp.continuous_fst 2 EX EY)).inter
      (setup.hY_closed.preimage (WithLp.continuous_snd 2 EX EY)))

/-- Convexity of the product feasible carrier `Z = X × Y`. -/
theorem jointCarrier_convex : Convex ℝ setup.jointCarrier := by
  rw [Setup.jointCarrier]
  intro z hz w hw a b ha hb hab
  constructor
  · simpa using setup.hX_convex hz.1 hw.1 ha hb hab
  · simpa using setup.hY_convex hz.2 hw.2 ha hb hab

/-- Continuity of the selected product DGF gradient on `Zᵒ`.

This is the product-space consequence of the Section 3.2 DGF interface: the
component selected gradients are continuous on `Xᵒ` and `Yᵒ`, and the product
DGF selector is the scaled product of those gradients. -/
theorem productDGF_selectedGradient_continuous :
    Continuous (fun z : setup.InteriorPoint =>
      sourceDGFGradient setup.jointCarrier setup.productPotential z.1) := by
  classical
  have hcoreXY : ∀ z : setup.InteriorPoint,
      z.1.fst ∈ sourceDGFCore setup.X setup.nuX ∧
        z.1.snd ∈ sourceDGFCore setup.Y setup.nuY := by
    intro z
    simpa [setup.productDGF_core_eq] using z.2
  have hXmap : Continuous
      (fun z : setup.InteriorPoint =>
        (⟨z.1.fst, (hcoreXY z).1⟩ : SourceDGFCorePoint setup.X setup.nuX)) := by
    exact Continuous.subtype_mk
      ((WithLp.continuous_fst 2 EX EY).comp continuous_subtype_val)
      (fun z => (hcoreXY z).1)
  have hYmap : Continuous
      (fun z : setup.InteriorPoint =>
        (⟨z.1.snd, (hcoreXY z).2⟩ : SourceDGFCorePoint setup.Y setup.nuY)) := by
    exact Continuous.subtype_mk
      ((WithLp.continuous_snd 2 EX EY).comp continuous_subtype_val)
      (fun z => (hcoreXY z).2)
  have hXgrad : Continuous
      (fun z : setup.InteriorPoint => sourceDGFGradient setup.X setup.nuX z.1.fst) := by
    simpa using setup.hnuX_dgf_mod_one.selectedGradient_continuous.comp hXmap
  have hYgrad : Continuous
      (fun z : setup.InteriorPoint => sourceDGFGradient setup.Y setup.nuY z.1.snd) := by
    simpa using setup.hnuY_dgf_mod_one.selectedGradient_continuous.comp hYmap
  have hpair : Continuous
      (fun z : setup.InteriorPoint =>
        (((2 * setup.DX ^ 2)⁻¹) • sourceDGFGradient setup.X setup.nuX z.1.fst,
          ((2 * setup.DY ^ 2)⁻¹) • sourceDGFGradient setup.Y setup.nuY z.1.snd)) :=
    (hXgrad.const_smul _).prodMk (hYgrad.const_smul _)
  have hwith : Continuous
      (fun z : setup.InteriorPoint =>
        WithLp.toLp 2
          (((2 * setup.DX ^ 2)⁻¹) • sourceDGFGradient setup.X setup.nuX z.1.fst,
            ((2 * setup.DY ^ 2)⁻¹) • sourceDGFGradient setup.Y setup.nuY z.1.snd)) := by
    exact (WithLp.prod_continuous_toLp 2 EX EY).comp hpair
  simpa [setup.productDGFGradientSelector_apply] using hwith

/-- On `Z`, the totalized product DGF is the scaled sum of component totalizations. -/
theorem productDGF_totalize_eq_on_carrier (z : Ambient EX EY)
    (hz : z ∈ setup.jointCarrier) :
    SOptLib.totalizeOn setup.jointCarrier setup.productPotential z =
      SOptLib.totalizeOn setup.X setup.nuX z.fst / (2 * setup.DX ^ 2) +
        SOptLib.totalizeOn setup.Y setup.nuY z.snd / (2 * setup.DY ^ 2) := by
  have hzcomp := (setup.jointCarrier_def z).1 hz
  rw [SOptLib.totalizeOn_of_mem setup.jointCarrier setup.productPotential hz]
  rw [SOptLib.totalizeOn_of_mem setup.X setup.nuX hzcomp.1]
  rw [SOptLib.totalizeOn_of_mem setup.Y setup.nuY hzcomp.2]
  simp [Setup.productDGF_def, Setup.xPoint, Setup.yPoint]

/-- The product DGF is convex on `Z`, derived from component DGF convexity. -/
theorem productDGF_convexOn :
    ConvexOn ℝ setup.jointCarrier (SOptLib.totalizeOn setup.jointCarrier setup.productPotential) := by
  have hXconv := setup.hnuX_dgf_mod_one.convexOn
  have hYconv := setup.hnuY_dgf_mod_one.convexOn
  have hDXs : 0 < 2 * setup.DX ^ 2 := by
    nlinarith [setup.DX_pos]
  have hDYs : 0 < 2 * setup.DY ^ 2 := by
    nlinarith [setup.DY_pos]
  refine ⟨setup.jointCarrier_convex, ?_⟩
  intro z hz w hw a b ha hb hab
  have hmix : a • z + b • w ∈ setup.jointCarrier :=
    setup.jointCarrier_convex hz hw ha hb hab
  have hxineq := hXconv.2 hz.1 hw.1 ha hb hab
  have hyineq := hYconv.2 hz.2 hw.2 ha hb hab
  have hxscaled :
      SOptLib.totalizeOn setup.X setup.nuX (a • z.fst + b • w.fst) /
          (2 * setup.DX ^ 2) ≤
        (a * SOptLib.totalizeOn setup.X setup.nuX z.fst +
            b * SOptLib.totalizeOn setup.X setup.nuX w.fst) / (2 * setup.DX ^ 2) := by
    exact div_le_div_of_nonneg_right hxineq (le_of_lt hDXs)
  have hyscaled :
      SOptLib.totalizeOn setup.Y setup.nuY (a • z.snd + b • w.snd) /
          (2 * setup.DY ^ 2) ≤
        (a * SOptLib.totalizeOn setup.Y setup.nuY z.snd +
            b * SOptLib.totalizeOn setup.Y setup.nuY w.snd) / (2 * setup.DY ^ 2) := by
    exact div_le_div_of_nonneg_right hyineq (le_of_lt hDYs)
  calc
    SOptLib.totalizeOn setup.jointCarrier setup.productPotential (a • z + b • w)
        = SOptLib.totalizeOn setup.X setup.nuX (a • z.fst + b • w.fst) /
              (2 * setup.DX ^ 2) +
            SOptLib.totalizeOn setup.Y setup.nuY (a • z.snd + b • w.snd) /
              (2 * setup.DY ^ 2) := by
          simpa using setup.productDGF_totalize_eq_on_carrier (a • z + b • w) hmix
    _ ≤ (a * SOptLib.totalizeOn setup.X setup.nuX z.fst +
            b * SOptLib.totalizeOn setup.X setup.nuX w.fst) / (2 * setup.DX ^ 2) +
        (a * SOptLib.totalizeOn setup.Y setup.nuY z.snd +
            b * SOptLib.totalizeOn setup.Y setup.nuY w.snd) / (2 * setup.DY ^ 2) := by
          exact add_le_add hxscaled hyscaled
    _ = a * SOptLib.totalizeOn setup.jointCarrier setup.productPotential z +
        b * SOptLib.totalizeOn setup.jointCarrier setup.productPotential w := by
          rw [setup.productDGF_totalize_eq_on_carrier z hz,
            setup.productDGF_totalize_eq_on_carrier w hw]
          ring

/-- The product DGF is continuous on `Z`, derived from component DGF continuity. -/
theorem productDGF_continuousOn :
    ContinuousOn (SOptLib.totalizeOn setup.jointCarrier setup.productPotential)
      setup.jointCarrier := by
  have hXcont := setup.hnuX_dgf_mod_one.continuousOn
  have hYcont := setup.hnuY_dgf_mod_one.continuousOn
  have hxcont : ContinuousOn
      (fun z : Ambient EX EY => SOptLib.totalizeOn setup.X setup.nuX z.fst)
      setup.jointCarrier := by
    exact hXcont.comp (WithLp.continuous_fst 2 EX EY).continuousOn (fun _ hz => hz.1)
  have hycont : ContinuousOn
      (fun z : Ambient EX EY => SOptLib.totalizeOn setup.Y setup.nuY z.snd)
      setup.jointCarrier := by
    exact hYcont.comp (WithLp.continuous_snd 2 EX EY).continuousOn (fun _ hz => hz.2)
  have hsumcont : ContinuousOn
      (fun z : Ambient EX EY =>
        SOptLib.totalizeOn setup.X setup.nuX z.fst / (2 * setup.DX ^ 2) +
          SOptLib.totalizeOn setup.Y setup.nuY z.snd / (2 * setup.DY ^ 2))
      setup.jointCarrier := by
    exact (hxcont.div_const _).add (hycont.div_const _)
  exact hsumcont.congr (fun z hz => setup.productDGF_totalize_eq_on_carrier z hz)

/-- The product DGF is `C¹` on `Zᵒ`, derived from component DGF `C¹` regularity. -/
theorem productDGF_contDiffOn_core :
    ContDiffOn ℝ 1 (SOptLib.totalizeOn setup.jointCarrier setup.productPotential)
      (sourceDGFCore setup.jointCarrier setup.productPotential) := by
  have hXc1 := setup.hnuX_dgf_mod_one.contDiffOn_core
  have hYc1 := setup.hnuY_dgf_mod_one.contDiffOn_core
  have hcoreCarrier : ∀ {z : Ambient EX EY},
      z ∈ sourceDGFCore setup.jointCarrier setup.productPotential → z ∈ setup.jointCarrier := by
    intro z hz
    rcases hz with ⟨hzC, _p, _hmin⟩
    exact hzC
  have hcoreXY : ∀ {z : Ambient EX EY},
      z ∈ sourceDGFCore setup.jointCarrier setup.productPotential →
        z.fst ∈ sourceDGFCore setup.X setup.nuX ∧
          z.snd ∈ sourceDGFCore setup.Y setup.nuY := by
    intro z hz
    simpa [setup.productDGF_core_eq] using hz
  have hxc1pre : ContDiffOn ℝ 1
      (fun z : Ambient EX EY => SOptLib.totalizeOn setup.X setup.nuX z.fst)
      ((fun z : Ambient EX EY => z.fst) ⁻¹' sourceDGFCore setup.X setup.nuX) := by
    simpa [Function.comp_def] using
      (hXc1.comp_continuousLinearMap
        (WithLp.fstL (p := 2) (𝕜 := ℝ) (α := EX) (β := EY)))
  have hyc1pre : ContDiffOn ℝ 1
      (fun z : Ambient EX EY => SOptLib.totalizeOn setup.Y setup.nuY z.snd)
      ((fun z : Ambient EX EY => z.snd) ⁻¹' sourceDGFCore setup.Y setup.nuY) := by
    simpa [Function.comp_def] using
      (hYc1.comp_continuousLinearMap
        (WithLp.sndL (p := 2) (𝕜 := ℝ) (α := EX) (β := EY)))
  have hxc1prod : ContDiffOn ℝ 1
      (fun z : Ambient EX EY => SOptLib.totalizeOn setup.X setup.nuX z.fst)
      (sourceDGFCore setup.jointCarrier setup.productPotential) := by
    exact hxc1pre.mono (fun _ hz => (hcoreXY hz).1)
  have hyc1prod : ContDiffOn ℝ 1
      (fun z : Ambient EX EY => SOptLib.totalizeOn setup.Y setup.nuY z.snd)
      (sourceDGFCore setup.jointCarrier setup.productPotential) := by
    exact hyc1pre.mono (fun _ hz => (hcoreXY hz).2)
  have hsumc1 : ContDiffOn ℝ 1
      (fun z : Ambient EX EY =>
        SOptLib.totalizeOn setup.X setup.nuX z.fst / (2 * setup.DX ^ 2) +
          SOptLib.totalizeOn setup.Y setup.nuY z.snd / (2 * setup.DY ^ 2))
      (sourceDGFCore setup.jointCarrier setup.productPotential) := by
    exact (hxc1prod.div_const _).add (hyc1prod.div_const _)
  exact hsumc1.congr
    (fun z hz => setup.productDGF_totalize_eq_on_carrier z (hcoreCarrier hz))

/-- Convexity of the source core of the product DGF, using
`Zᵒ = Xᵒ × Yᵒ`. -/
theorem productDGF_core_convex :
    Convex ℝ (sourceDGFCore setup.jointCarrier setup.productPotential) := by
  rw [setup.productDGF_core_eq]
  intro z hz w hw a b ha hb hab
  constructor
  · exact setup.hnuX_dgf_mod_one.core_convex hz.1 hw.1 ha hb hab
  · exact setup.hnuY_dgf_mod_one.core_convex hz.2 hw.2 ha hb hab

/-- The scaled product selector is a genuine within-gradient representative of
the product DGF on the source core.

This is the semantic counterpart to `productDGFGradientSelector_apply`: the
selected product gradient is not only definitionally convenient, it is obtained
from the component DGF gradient certificates and the product DGF formula. -/
private theorem productDGF_gradient_hasGradientWithinAt :
    ∀ z, z ∈ sourceDGFCore setup.jointCarrier setup.productPotential →
      HasGradientWithinAt (SOptLib.totalizeOn setup.jointCarrier setup.productPotential)
        (sourceDGFGradient setup.jointCarrier setup.productPotential z)
        setup.jointCarrier z := by
  classical
  intro z hz
  let S : Set (Ambient EX EY) := setup.jointCarrier
  let Fscaled : Ambient EX EY → ℝ := fun w =>
    SOptLib.totalizeOn setup.X setup.nuX w.fst / (2 * setup.DX ^ 2) +
      SOptLib.totalizeOn setup.Y setup.nuY w.snd / (2 * setup.DY ^ 2)
  have hzxy :
      z.fst ∈ sourceDGFCore setup.X setup.nuX ∧
        z.snd ∈ sourceDGFCore setup.Y setup.nuY := by
    simpa [setup.productDGF_core_eq] using hz
  have hXgrad :
      HasGradientWithinAt (SOptLib.totalizeOn setup.X setup.nuX)
        (sourceDGFGradient setup.X setup.nuX z.fst)
        setup.X z.fst :=
    setup.hnuX_dgf_mod_one.gradient_hasGradientWithinAt hzxy.1
  have hYgrad :
      HasGradientWithinAt (SOptLib.totalizeOn setup.Y setup.nuY)
        (sourceDGFGradient setup.Y setup.nuY z.snd)
        setup.Y z.snd :=
    setup.hnuY_dgf_mod_one.gradient_hasGradientWithinAt hzxy.2
  have hfst : HasFDerivWithinAt (fun w : Ambient EX EY => w.fst)
      (WithLp.fstL (p := 2) (𝕜 := ℝ) (α := EX) (β := EY)) S z := by
    exact (WithLp.fstL (p := 2) (𝕜 := ℝ) (α := EX) (β := EY)).hasFDerivWithinAt
  have hsnd : HasFDerivWithinAt (fun w : Ambient EX EY => w.snd)
      (WithLp.sndL (p := 2) (𝕜 := ℝ) (α := EX) (β := EY)) S z := by
    exact (WithLp.sndL (p := 2) (𝕜 := ℝ) (α := EX) (β := EY)).hasFDerivWithinAt
  have hmaps_fst :
      Set.MapsTo (fun w : Ambient EX EY => w.fst) S setup.X := by
    intro w hw
    exact hw.1
  have hmaps_snd :
      Set.MapsTo (fun w : Ambient EX EY => w.snd) S setup.Y := by
    intro w hw
    exact hw.2
  have hXf : HasFDerivWithinAt
      (fun w : Ambient EX EY => SOptLib.totalizeOn setup.X setup.nuX w.fst)
      ((InnerProductSpace.toDual ℝ EX (sourceDGFGradient setup.X setup.nuX z.fst)).comp
        (WithLp.fstL (p := 2) (𝕜 := ℝ) (α := EX) (β := EY))) S z := by
    simpa [Function.comp_def] using hXgrad.hasFDerivWithinAt.comp z hfst hmaps_fst
  have hYf : HasFDerivWithinAt
      (fun w : Ambient EX EY => SOptLib.totalizeOn setup.Y setup.nuY w.snd)
      ((InnerProductSpace.toDual ℝ EY (sourceDGFGradient setup.Y setup.nuY z.snd)).comp
        (WithLp.sndL (p := 2) (𝕜 := ℝ) (α := EX) (β := EY))) S z := by
    simpa [Function.comp_def] using hYgrad.hasFDerivWithinAt.comp z hsnd hmaps_snd
  have hsum := (hXf.const_mul ((2 * setup.DX ^ 2)⁻¹)).add
    (hYf.const_mul ((2 * setup.DY ^ 2)⁻¹))
  have hscaled : HasGradientWithinAt Fscaled
      (WithLp.toLp 2
        (((2 * setup.DX ^ 2)⁻¹) • sourceDGFGradient setup.X setup.nuX z.fst,
          ((2 * setup.DY ^ 2)⁻¹) • sourceDGFGradient setup.Y setup.nuY z.snd)) S z := by
    rw [hasGradientWithinAt_iff_hasFDerivWithinAt]
    convert hsum using 1
    · funext w
      dsimp [Fscaled]
      ring_nf
    · ext d
      simp [WithLp.prod_inner_apply, real_inner_smul_left]
  have hprod_eq : ∀ w ∈ S,
      SOptLib.totalizeOn setup.jointCarrier setup.productPotential w = Fscaled w := by
    intro w hw
    exact setup.productDGF_totalize_eq_on_carrier w hw
  have hzS : z ∈ S := Classical.choose hz
  simpa [S, Fscaled, setup.productDGFGradientSelector_apply] using
    hscaled.congr_of_mem hprod_eq hzS

/-- Iteration-7 compiler voucher for the product-gradient pairing split: the
source formula and `C¹` hypotheses needed by the remaining within-gradient
chain-rule leaf are present at both core endpoints. -/
private theorem _voucher_attempt_productDGF_gradient_pairing_split_7_context
    {x x' : Ambient EX EY}
    (hx : x ∈ sourceDGFCore setup.jointCarrier setup.productPotential)
    (hx' : x' ∈ sourceDGFCore setup.jointCarrier setup.productPotential) :
    ContDiffOn ℝ 1 (SOptLib.totalizeOn setup.jointCarrier setup.productPotential)
        (sourceDGFCore setup.jointCarrier setup.productPotential) ∧
      SOptLib.totalizeOn setup.jointCarrier setup.productPotential x =
          SOptLib.totalizeOn setup.X setup.nuX x.fst / (2 * setup.DX ^ 2) +
            SOptLib.totalizeOn setup.Y setup.nuY x.snd / (2 * setup.DY ^ 2) ∧
      SOptLib.totalizeOn setup.jointCarrier setup.productPotential x' =
          SOptLib.totalizeOn setup.X setup.nuX x'.fst / (2 * setup.DX ^ 2) +
            SOptLib.totalizeOn setup.Y setup.nuY x'.snd / (2 * setup.DY ^ 2) := by
  have hxZ : x ∈ setup.jointCarrier := Classical.choose hx
  have hx'Z : x' ∈ setup.jointCarrier := Classical.choose hx'
  exact ⟨setup.productDGF_contDiffOn_core,
    setup.productDGF_totalize_eq_on_carrier x hxZ,
    setup.productDGF_totalize_eq_on_carrier x' hx'Z⟩

/-- Iteration-7 compiler voucher for the product-gradient displacement split:
the product formula, component-core membership, and product `C¹` input are all
available for a prox base point and an arbitrary feasible endpoint. -/
private theorem _voucher_attempt_productDGF_gradient_displacement_split_7_context
    (z : setup.InteriorPoint) (u : setup.Point) :
    ContDiffOn ℝ 1 (SOptLib.totalizeOn setup.jointCarrier setup.productPotential)
        (sourceDGFCore setup.jointCarrier setup.productPotential) ∧
      (z.1.fst ∈ sourceDGFCore setup.X setup.nuX ∧
        z.1.snd ∈ sourceDGFCore setup.Y setup.nuY) ∧
      SOptLib.totalizeOn setup.jointCarrier setup.productPotential z.1 =
          SOptLib.totalizeOn setup.X setup.nuX z.1.fst / (2 * setup.DX ^ 2) +
            SOptLib.totalizeOn setup.Y setup.nuY z.1.snd / (2 * setup.DY ^ 2) ∧
      SOptLib.totalizeOn setup.jointCarrier setup.productPotential u.1 =
          SOptLib.totalizeOn setup.X setup.nuX u.1.fst / (2 * setup.DX ^ 2) +
            SOptLib.totalizeOn setup.Y setup.nuY u.1.snd / (2 * setup.DY ^ 2) := by
  have hzZ : z.1 ∈ setup.jointCarrier := Classical.choose z.2
  have hzxy :
      z.1.fst ∈ sourceDGFCore setup.X setup.nuX ∧
        z.1.snd ∈ sourceDGFCore setup.Y setup.nuY := by
    simpa [setup.productDGF_core_eq] using z.2
  exact ⟨setup.productDGF_contDiffOn_core, hzxy,
    setup.productDGF_totalize_eq_on_carrier z.1 hzZ,
    setup.productDGF_totalize_eq_on_carrier u.1 u.2⟩



/-- Component-scaled product prox expression from the source product
normalization paragraph. -/
private noncomputable def productDGFComponentProxSum
    (z : setup.InteriorPoint) (u : setup.Point) : ℝ :=
  sourceDGFProx setup.nuX
      ⟨z.1.fst, by
        have hz := (show z.1 ∈ sourceDGFCore setup.jointCarrier setup.productPotential from z.2)
        have hzxy :
            z.1.fst ∈ sourceDGFCore setup.X setup.nuX ∧
              z.1.snd ∈ sourceDGFCore setup.Y setup.nuY := by
          simpa [setup.productDGF_core_eq] using hz
        exact hzxy.1⟩
      (setup.xPoint u) / (2 * setup.DX ^ 2) +
    sourceDGFProx setup.nuY
      ⟨z.1.snd, by
        have hz := (show z.1 ∈ sourceDGFCore setup.jointCarrier setup.productPotential from z.2)
        have hzxy :
            z.1.fst ∈ sourceDGFCore setup.X setup.nuX ∧
              z.1.snd ∈ sourceDGFCore setup.Y setup.nuY := by
          simpa [setup.productDGF_core_eq] using hz
        exact hzxy.2⟩
      (setup.yPoint u) / (2 * setup.DY ^ 2)


/-- The selected-gradient displacement equality that is necessary and
sufficient for the current generic `sourceDGFProx` realization to satisfy the
source product prox scaling formula. -/
private def productDGFGradientDisplacementSplit
    (z : setup.InteriorPoint) (u : setup.Point) : Prop :=
  ⟪sourceDGFGradient setup.jointCarrier setup.productPotential z.1, u.1 - z.1⟫_ℝ =
    ⟪sourceDGFGradient setup.X setup.nuX z.1.fst, u.1.fst - z.1.fst⟫_ℝ /
        (2 * setup.DX ^ 2) +
      ⟪sourceDGFGradient setup.Y setup.nuY z.1.snd, u.1.snd - z.1.snd⟫_ℝ /
        (2 * setup.DY ^ 2)


/-- Product selected-gradient feasible-displacement split from the source-selected
product DGF gradient.

The product DGF registers the paper's canonical gradient
`(∇ν_X/(2D_X^2), ∇ν_Y/(2D_Y^2))`, so this bridge is now inner-product algebra
rather than a full-carrier `gradientWithin` product rule. -/
private theorem productDGFGradientDisplacementSplit_of_carrier_projected :
    ∀ z : setup.InteriorPoint, ∀ u : setup.Point,
      setup.productDGFGradientDisplacementSplit z u := by
  classical
  intro z u
  simp [productDGFGradientDisplacementSplit, setup.productDGFGradientSelector_apply,
    WithLp.prod_inner_apply, real_inner_smul_left]
  ring_nf

/-- Product-gradient pairing against a feasible displacement, routed through
the source-selected product gradient rather than the obsolete raw-core
`gradientWithin` voucher branch. -/
private theorem productDGF_gradient_displacement_split
    (z : setup.InteriorPoint) (u : setup.Point) :
    ⟪sourceDGFGradient setup.jointCarrier setup.productPotential z.1, u.1 - z.1⟫_ℝ =
      ⟪sourceDGFGradient setup.X setup.nuX z.1.fst, u.1.fst - z.1.fst⟫_ℝ /
          (2 * setup.DX ^ 2) +
        ⟪sourceDGFGradient setup.Y setup.nuY z.1.snd, u.1.snd - z.1.snd⟫_ℝ /
          (2 * setup.DY ^ 2) := by
  exact setup.productDGFGradientDisplacementSplit_of_carrier_projected z u

/-- Product-gradient pairing on two core endpoints follows from the feasible
displacement split applied in both directions. -/
private theorem productDGF_gradient_pairing_split_of_displacement_split
    (hdisp : ∀ z : setup.InteriorPoint, ∀ u : setup.Point,
      setup.productDGFGradientDisplacementSplit z u)
    {x x' : Ambient EX EY}
    (hx : x ∈ sourceDGFCore setup.jointCarrier setup.productPotential)
    (hx' : x' ∈ sourceDGFCore setup.jointCarrier setup.productPotential) :
    ⟪sourceDGFGradient setup.jointCarrier setup.productPotential x' -
        sourceDGFGradient setup.jointCarrier setup.productPotential x, x' - x⟫_ℝ =
    ⟪sourceDGFGradient setup.X setup.nuX x'.fst -
          sourceDGFGradient setup.X setup.nuX x.fst, x'.fst - x.fst⟫_ℝ /
          (2 * setup.DX ^ 2) +
        ⟪sourceDGFGradient setup.Y setup.nuY x'.snd -
          sourceDGFGradient setup.Y setup.nuY x.snd, x'.snd - x.snd⟫_ℝ /
          (2 * setup.DY ^ 2) := by
  classical
  exact SOptLib.inner_product_product_gradient_pairing_split_of_displacement_split
    (core := sourceDGFCore setup.jointCarrier setup.productPotential)
    (carrier := setup.jointCarrier)
    (fullGrad := sourceDGFGradient setup.jointCarrier setup.productPotential)
    (gradX := sourceDGFGradient setup.X setup.nuX)
    (gradY := sourceDGFGradient setup.Y setup.nuY)
    (sx := 2 * setup.DX ^ 2) (sy := 2 * setup.DY ^ 2)
    (hcore_subset := by
      intro z hz
      exact Classical.choose hz)
    (hdisp := by
      intro z hz u hu
      let zz : setup.InteriorPoint := ⟨z, hz⟩
      let uu : setup.Point := ⟨u, hu⟩
      simpa [productDGFGradientDisplacementSplit, zz, uu] using hdisp zz uu)
    hx hx'

/-- Exact product-gradient pairing split needed for the source statement that
the scaled product DGF has modulus one, now supplied by the source-selected
feasible-displacement split. -/
private theorem productDGF_gradient_pairing_split
    {x x' : Ambient EX EY}
    (hx : x ∈ sourceDGFCore setup.jointCarrier setup.productPotential)
    (hx' : x' ∈ sourceDGFCore setup.jointCarrier setup.productPotential) :
    ⟪sourceDGFGradient setup.jointCarrier setup.productPotential x' -
        sourceDGFGradient setup.jointCarrier setup.productPotential x, x' - x⟫_ℝ =
      ⟪sourceDGFGradient setup.X setup.nuX x'.fst -
          sourceDGFGradient setup.X setup.nuX x.fst, x'.fst - x.fst⟫_ℝ /
          (2 * setup.DX ^ 2) +
        ⟪sourceDGFGradient setup.Y setup.nuY x'.snd -
          sourceDGFGradient setup.Y setup.nuY x.snd, x'.snd - x.snd⟫_ℝ /
          (2 * setup.DY ^ 2) := by
  exact setup.productDGF_gradient_pairing_split_of_displacement_split
    setup.productDGFGradientDisplacementSplit_of_carrier_projected hx hx'

/-- Product DGF monotonicity with modulus one, obtained from component
modulus-one inequalities and a source-selected feasible-displacement split. -/
private theorem productDGF_modulus_one_monotone_of_displacement_split
    (hdisp : ∀ z : setup.InteriorPoint, ∀ u : setup.Point,
      setup.productDGFGradientDisplacementSplit z u) :
    ∀ x, x ∈ sourceDGFCore setup.jointCarrier setup.productPotential →
      ∀ x', x' ∈ sourceDGFCore setup.jointCarrier setup.productPotential →
        setup.productNorm (x' - x) ^ 2 ≤
          ⟪sourceDGFGradient setup.jointCarrier setup.productPotential x' -
              sourceDGFGradient setup.jointCarrier setup.productPotential x, x' - x⟫_ℝ := by
  intro x hx x' hx'
  have hcoreXY_x :
      x.fst ∈ sourceDGFCore setup.X setup.nuX ∧
        x.snd ∈ sourceDGFCore setup.Y setup.nuY := by
    simpa [setup.productDGF_core_eq] using hx
  have hcoreXY_x' :
      x'.fst ∈ sourceDGFCore setup.X setup.nuX ∧
        x'.snd ∈ sourceDGFCore setup.Y setup.nuY := by
    simpa [setup.productDGF_core_eq] using hx'
  have hXmono := setup.hnuX_dgf_mod_one.monotone x.fst hcoreXY_x.1
    x'.fst hcoreXY_x'.1
  have hYmono := setup.hnuY_dgf_mod_one.monotone x.snd hcoreXY_x.2
    x'.snd hcoreXY_x'.2
  have hDXs_nonneg : 0 ≤ 2 * setup.DX ^ 2 := by positivity
  have hDYs_nonneg : 0 ≤ 2 * setup.DY ^ 2 := by positivity
  rw [Setup.productNorm_def, Real.sq_sqrt]
  · rw [setup.productDGF_gradient_pairing_split_of_displacement_split hdisp hx hx']
    exact add_le_add
      (div_le_div_of_nonneg_right hXmono hDXs_nonneg)
      (div_le_div_of_nonneg_right hYmono hDYs_nonneg)
  · positivity

/-- Typed same-interface obstruction for the current `sourceDGFProx` model.

After unfolding the paper Bregman formula, the source product prox scaling
statement is equivalent to the selected-gradient feasible-displacement split.
Thus any proof of `productDGF_prox_eq_scaled_sum` under the current generic
gradient realization must supply exactly this selected-gradient contract rather
than only the scalar product DGF formula. -/
private theorem productDGF_prox_eq_scaled_sum_iff_gradient_displacement_split
    (z : setup.InteriorPoint) (u : setup.Point) :
    sourceDGFProx setup.productPotential z u = setup.productDGFComponentProxSum z u ↔
      setup.productDGFGradientDisplacementSplit z u := by
  classical
  have hzxy :
      z.1.fst ∈ sourceDGFCore setup.X setup.nuX ∧
        z.1.snd ∈ sourceDGFCore setup.Y setup.nuY := by
    simpa [setup.productDGF_core_eq] using z.2
  let zX : SourceDGFCorePoint setup.X setup.nuX := ⟨z.1.fst, hzxy.1⟩
  let zY : SourceDGFCorePoint setup.Y setup.nuY := ⟨z.1.snd, hzxy.2⟩
  let gx : ℝ :=
    ⟪sourceDGFGradient setup.X setup.nuX z.1.fst, u.1.fst - z.1.fst⟫_ℝ
  let gy : ℝ :=
    ⟪sourceDGFGradient setup.Y setup.nuY z.1.snd, u.1.snd - z.1.snd⟫_ℝ
  let gp : ℝ :=
    ⟪sourceDGFGradient setup.jointCarrier setup.productPotential z.1, u.1 - z.1⟫_ℝ
  constructor
  · intro hprox
    change gp = gx / (2 * setup.DX ^ 2) + gy / (2 * setup.DY ^ 2)
    have h := hprox
    simp only [productDGFComponentProxSum, sourceDGFProx, sourceDGFCoreToCarrier,
      Setup.productDGF_def, Setup.xPoint, Setup.yPoint] at h
    change
        setup.nuX (setup.xPoint u) / (2 * setup.DX ^ 2) +
            setup.nuY (setup.yPoint u) / (2 * setup.DY ^ 2) -
          (setup.nuX (sourceDGFCoreToCarrier zX) / (2 * setup.DX ^ 2) +
            setup.nuY (sourceDGFCoreToCarrier zY) / (2 * setup.DY ^ 2)) - gp =
        (setup.nuX (setup.xPoint u) - setup.nuX (sourceDGFCoreToCarrier zX) - gx) /
            (2 * setup.DX ^ 2) +
          (setup.nuY (setup.yPoint u) - setup.nuY (sourceDGFCoreToCarrier zY) - gy) /
            (2 * setup.DY ^ 2) at h
    ring_nf at h ⊢
    linarith
  · intro hgrad
    change sourceDGFProx setup.productPotential z u = setup.productDGFComponentProxSum z u
    simp only [productDGFComponentProxSum, sourceDGFProx, sourceDGFCoreToCarrier,
      Setup.productDGF_def, Setup.xPoint, Setup.yPoint]
    change
        setup.nuX (setup.xPoint u) / (2 * setup.DX ^ 2) +
            setup.nuY (setup.yPoint u) / (2 * setup.DY ^ 2) -
          (setup.nuX (sourceDGFCoreToCarrier zX) / (2 * setup.DX ^ 2) +
            setup.nuY (sourceDGFCoreToCarrier zY) / (2 * setup.DY ^ 2)) - gp =
        (setup.nuX (setup.xPoint u) - setup.nuX (sourceDGFCoreToCarrier zX) - gx) /
            (2 * setup.DX ^ 2) +
          (setup.nuY (setup.yPoint u) - setup.nuY (sourceDGFCoreToCarrier zY) - gy) /
            (2 * setup.DY ^ 2)
    have hgrad' : gp = gx / (2 * setup.DX ^ 2) + gy / (2 * setup.DY ^ 2) := by
      simpa [productDGFGradientDisplacementSplit, gx, gy, gp] using hgrad
    rw [hgrad']
    ring

/-- Product prox scaling induced by
`ν(z)=ν_X(x)/(2D_X^2)+ν_Y(y)/(2D_Y^2)`.

This is the source-level bridge that turns component diameter-attainment into
the product diameter-attainment and `D_Z=1` calculations. -/
theorem productDGF_prox_eq_scaled_sum (z : setup.InteriorPoint) (u : setup.Point) :
    sourceDGFProx setup.productPotential z u =
      sourceDGFProx setup.nuX
          ⟨z.1.fst, by
            have hz := (show z.1 ∈ sourceDGFCore setup.jointCarrier setup.productPotential from z.2)
            have hzxy :
                z.1.fst ∈ sourceDGFCore setup.X setup.nuX ∧
                  z.1.snd ∈ sourceDGFCore setup.Y setup.nuY := by
              simpa [setup.productDGF_core_eq] using hz
            exact hzxy.1⟩
          (setup.xPoint u) / (2 * setup.DX ^ 2) +
        sourceDGFProx setup.nuY
          ⟨z.1.snd, by
            have hz := (show z.1 ∈ sourceDGFCore setup.jointCarrier setup.productPotential from z.2)
            have hzxy :
                z.1.fst ∈ sourceDGFCore setup.X setup.nuX ∧
                  z.1.snd ∈ sourceDGFCore setup.Y setup.nuY := by
              simpa [setup.productDGF_core_eq] using hz
            exact hzxy.2⟩
          (setup.yPoint u) / (2 * setup.DY ^ 2) := by
  classical
  have h := (setup.productDGF_prox_eq_scaled_sum_iff_gradient_displacement_split z u).2
    (setup.productDGFGradientDisplacementSplit_of_carrier_projected z u)
  simpa [productDGFComponentProxSum] using h

/-- Product DGF monotonicity with modulus one, obtained from component
modulus-one inequalities and the product-gradient pairing split. -/
private theorem productDGF_modulus_one_monotone :
    ∀ x, x ∈ sourceDGFCore setup.jointCarrier setup.productPotential →
      ∀ x', x' ∈ sourceDGFCore setup.jointCarrier setup.productPotential →
        setup.productNorm (x' - x) ^ 2 ≤
          ⟪sourceDGFGradient setup.jointCarrier setup.productPotential x' -
              sourceDGFGradient setup.jointCarrier setup.productPotential x, x' - x⟫_ℝ := by
  intro x hx x' hx'
  have hcoreXY_x :
      x.fst ∈ sourceDGFCore setup.X setup.nuX ∧
        x.snd ∈ sourceDGFCore setup.Y setup.nuY := by
    simpa [setup.productDGF_core_eq] using hx
  have hcoreXY_x' :
      x'.fst ∈ sourceDGFCore setup.X setup.nuX ∧
        x'.snd ∈ sourceDGFCore setup.Y setup.nuY := by
    simpa [setup.productDGF_core_eq] using hx'
  have hXmono := setup.hnuX_dgf_mod_one.monotone x.fst hcoreXY_x.1
    x'.fst hcoreXY_x'.1
  have hYmono := setup.hnuY_dgf_mod_one.monotone x.snd hcoreXY_x.2
    x'.snd hcoreXY_x'.2
  have hDXs_nonneg : 0 ≤ 2 * setup.DX ^ 2 := by positivity
  have hDYs_nonneg : 0 ≤ 2 * setup.DY ^ 2 := by positivity
  have hDXs_pos : 0 < 2 * setup.DX ^ 2 := by nlinarith [setup.DX_pos]
  have hDYs_pos : 0 < 2 * setup.DY ^ 2 := by nlinarith [setup.DY_pos]
  rw [Setup.productNorm_def, Real.sq_sqrt]
  · rw [setup.productDGF_gradient_pairing_split hx hx']
    exact add_le_add
      (div_le_div_of_nonneg_right hXmono hDXs_nonneg)
      (div_le_div_of_nonneg_right hYmono hDYs_nonneg)
  · positivity

/-- Explicit product-diameter maximizer and value obtained from the component
diameter maximizers, parameterized by the product prox scaling bridge. -/
private theorem productDGF_diameter_scaled_component_max_of_prox
    (hprox : ∀ z : setup.InteriorPoint, ∀ u : setup.Point,
      sourceDGFProx setup.productPotential z u = setup.productDGFComponentProxSum z u) :
    ∃ zmax : setup.InteriorPoint, ∃ umax : setup.Point,
      sourceDGFProx setup.productPotential zmax umax =
          setup.DX2 / (2 * setup.DX ^ 2) + setup.DY2 / (2 * setup.DY ^ 2) ∧
        ∀ q : setup.InteriorPoint, ∀ r : setup.Point,
          sourceDGFProx setup.productPotential q r ≤
            setup.DX2 / (2 * setup.DX ^ 2) + setup.DY2 / (2 * setup.DY ^ 2) := by
  classical
  rcases sourceDGFDiameterSq_eq_attained setup.hX_nonempty setup.hX_bounded
      setup.hX_closed setup.hnuX_dgf_mod_one with
    ⟨x₁, x, hDX2, hXmax⟩
  rcases sourceDGFDiameterSq_eq_attained setup.hY_nonempty setup.hY_bounded
      setup.hY_closed setup.hnuY_dgf_mod_one with
    ⟨y₁, y, hDY2, hYmax⟩
  let zmax : setup.InteriorPoint :=
    ⟨WithLp.toLp 2 (x₁.1, y₁.1), by
      rw [setup.productDGF_core_eq]
      exact ⟨x₁.2, y₁.2⟩⟩
  let umax : setup.Point :=
    ⟨WithLp.toLp 2 (x.1, y.1), by
      simpa [Setup.jointCarrier] using
        (show (x.1, y.1) ∈ setup.X ×ˢ setup.Y from ⟨x.2, y.2⟩)⟩
  refine ⟨zmax, umax, ?_, ?_⟩
  · rw [hprox zmax umax]
    have hxprox :
        sourceDGFProx setup.nuX ⟨WithLp.fst zmax.1, by
          have hz := (show zmax.1 ∈ sourceDGFCore setup.jointCarrier setup.productPotential from zmax.2)
          have hzxy :
              zmax.1.fst ∈ sourceDGFCore setup.X setup.nuX ∧
                zmax.1.snd ∈ sourceDGFCore setup.Y setup.nuY := by
            simpa [setup.productDGF_core_eq] using hz
          exact hzxy.1⟩ (setup.xPoint umax) =
          sourceDGFProx setup.nuX x₁ x := by
      simp [zmax, umax, Setup.xPoint]
    have hyprox :
        sourceDGFProx setup.nuY ⟨WithLp.snd zmax.1, by
          have hz := (show zmax.1 ∈ sourceDGFCore setup.jointCarrier setup.productPotential from zmax.2)
          have hzxy :
              zmax.1.fst ∈ sourceDGFCore setup.X setup.nuX ∧
                zmax.1.snd ∈ sourceDGFCore setup.Y setup.nuY := by
            simpa [setup.productDGF_core_eq] using hz
          exact hzxy.2⟩ (setup.yPoint umax) =
          sourceDGFProx setup.nuY y₁ y := by
      simp [zmax, umax, Setup.yPoint]
    rw [productDGFComponentProxSum, hxprox, hyprox, ← hDX2, ← hDY2]
    rfl
  · intro q r
    have hqxy :
        q.1.fst ∈ sourceDGFCore setup.X setup.nuX ∧
          q.1.snd ∈ sourceDGFCore setup.Y setup.nuY := by
      simpa [setup.productDGF_core_eq] using q.2
    have hxle :
        sourceDGFProx setup.nuX ⟨q.1.fst, hqxy.1⟩ (setup.xPoint r) ≤ setup.DX2 :=
      hXmax ⟨q.1.fst, hqxy.1⟩ (setup.xPoint r)
    have hyle :
        sourceDGFProx setup.nuY ⟨q.1.snd, hqxy.2⟩ (setup.yPoint r) ≤ setup.DY2 :=
      hYmax ⟨q.1.snd, hqxy.2⟩ (setup.yPoint r)
    have hDXs_nonneg : 0 ≤ 2 * setup.DX ^ 2 := by positivity
    have hDYs_nonneg : 0 ≤ 2 * setup.DY ^ 2 := by positivity
    rw [hprox q r]
    exact add_le_add
      (div_le_div_of_nonneg_right hxle hDXs_nonneg)
      (div_le_div_of_nonneg_right hyle hDYs_nonneg)

/-- Explicit product-diameter maximizer and value obtained from the component
diameter maximizers. -/
private theorem productDGF_diameter_scaled_component_max :
    ∃ zmax : setup.InteriorPoint, ∃ umax : setup.Point,
      sourceDGFProx setup.productPotential zmax umax =
          setup.DX2 / (2 * setup.DX ^ 2) + setup.DY2 / (2 * setup.DY ^ 2) ∧
        ∀ q : setup.InteriorPoint, ∀ r : setup.Point,
          sourceDGFProx setup.productPotential q r ≤
            setup.DX2 / (2 * setup.DX ^ 2) + setup.DY2 / (2 * setup.DY ^ 2) := by
  refine setup.productDGF_diameter_scaled_component_max_of_prox ?_
  intro z u
  simpa [productDGFComponentProxSum] using setup.productDGF_prox_eq_scaled_sum z u

/-- Product realization of the Section 3.2 diameter maximum for
`ν(z)=ν_X(x)/(2D_X^2)+ν_Y(y)/(2D_Y^2)`.

The proof combines the two component diameter-attainment witnesses with the
product prox scaling calculation. -/
private theorem productDGF_diameter_attained :
    ∃ p : setup.InteriorPoint × setup.Point,
      IsMaxOn (fun q : setup.InteriorPoint × setup.Point =>
        sourceDGFProx setup.productPotential q.1 q.2) Set.univ p := by
  rcases setup.productDGF_diameter_scaled_component_max with ⟨zmax, umax, hmax_eq, hmax⟩
  refine ⟨(zmax, umax), ?_⟩
  rw [isMaxOn_univ_iff]
  intro q
  rw [hmax_eq]
  exact hmax q.1 q.2

/-- Product DGF modulus-one theorem assembled from the proved regularity
bridges and the named product monotonicity/diameter bridges. -/
private theorem productDGF_modulus_one_bridge :
    sourceDGFModulusOne setup.jointCarrier setup.productNorm setup.productPotential := by
  exact ⟨setup.productDGF_convexOn, setup.productDGF_continuousOn, setup.productDGF_core_convex,
    setup.productDGF_contDiffOn_core,
    setup.productDGF_selectedGradient_continuous,
    setup.productDGF_gradient_hasGradientWithinAt,
    setup.productDGF_modulus_one_monotone,
    setup.productDGF_diameter_attained⟩

/-- Source-level product DGF normalization from Section 4.3.1.

The paper states this as one formula-level fact: for
`ν(z) = ν_X(x)/(2D_X^2) + ν_Y(y)/(2D_Y^2)`, the product DGF has modulus one,
`Zᵒ = Xᵒ × Yᵒ`, and `D_Z = 1`.  Keeping these conclusions together prevents
downstream proofs from depending on the generic attained-diameter branch. -/
theorem productDGF_normalization_source_api :
    ∃ hprod : sourceDGFModulusOne setup.jointCarrier setup.productNorm setup.productPotential,
      sourceDGFCore setup.jointCarrier setup.productPotential =
          {z : Ambient EX EY |
            z.fst ∈ sourceDGFCore setup.X setup.nuX ∧
              z.snd ∈ sourceDGFCore setup.Y setup.nuY} ∧
        sourceDGFDiameter setup.productNorm setup.productPotential setup.jointCarrier_nonempty
          setup.jointCarrier_bounded setup.jointCarrier_closed hprod = 1 := by
  classical
  let hprod : sourceDGFModulusOne setup.jointCarrier setup.productNorm setup.productPotential :=
    setup.productDGF_modulus_one_bridge
  refine ⟨hprod, setup.productDGF_core_eq, ?_⟩
  have hsq :
      sourceDGFDiameterSq setup.productNorm setup.productPotential setup.jointCarrier_nonempty
        setup.jointCarrier_bounded setup.jointCarrier_closed hprod =
        setup.DX2 / (2 * setup.DX ^ 2) + setup.DY2 / (2 * setup.DY ^ 2) := by
    rcases setup.productDGF_diameter_scaled_component_max with ⟨zmax, umax, hmax_eq, hmax⟩
    exact (sourceDGFDiameterSq_eq_of_attained_value setup.jointCarrier_nonempty
      setup.jointCarrier_bounded setup.jointCarrier_closed hprod hmax_eq.symm hmax).1
  rw [sourceDGFDiameter, hsq]
  rw [Real.sqrt_eq_one]
  rw [← setup.DX_sq_eq_DX2, ← setup.DY_sq_eq_DY2]
  have hDX_ne : setup.DX ≠ 0 := ne_of_gt setup.DX_pos
  have hDY_ne : setup.DY ≠ 0 := ne_of_gt setup.DY_pos
  field_simp [hDX_ne, hDY_ne]
  norm_num

/-- Source-normalized product diameter `D_Z = 1`.

This is the `D_Z` conclusion in the Product_DGF_normalization paragraph, proved
at theorem scope rather than stored as primitive setup data. -/
theorem productDGF_DZ_eq_one
    (hprod : sourceDGFModulusOne setup.jointCarrier setup.productNorm setup.productPotential) :
    sourceDGFDiameter setup.productNorm setup.productPotential setup.jointCarrier_nonempty
      setup.jointCarrier_bounded setup.jointCarrier_closed hprod = 1 := by
  classical
  have hsrc := (Classical.choose_spec setup.productDGF_normalization_source_api).2
  simpa [sourceDGFDiameter, sourceDGFDiameterSq] using hsrc

/-- Product DGF normalization from Section 4.3.1: `D_Z = 1`, as a bridge
separate from the product modulus proof. -/
private theorem productDGF_diameter_eq_one_bridge
    (hprod : sourceDGFModulusOne setup.jointCarrier setup.productNorm setup.productPotential) :
    sourceDGFDiameter setup.productNorm setup.productPotential setup.jointCarrier_nonempty
      setup.jointCarrier_bounded setup.jointCarrier_closed hprod = 1 :=
  setup.productDGF_DZ_eq_one hprod

/-- The product `ν` is the modulus-one DGF on `Z` described after `(4.3.4)`. -/
theorem productDGF_modulus_one :
    sourceDGFModulusOne setup.jointCarrier setup.productNorm setup.productPotential :=
  Classical.choose setup.productDGF_normalization_source_api

/-- Product DGF normalization from Section 4.3.1: `D_Z = 1`. -/
theorem productDGF_diameter_eq_one :
    sourceDGFDiameter setup.productNorm setup.productPotential setup.jointCarrier_nonempty
      setup.jointCarrier_bounded setup.jointCarrier_closed setup.productDGF_modulus_one = 1 := by
  classical
  have hsrc := (Classical.choose_spec setup.productDGF_normalization_source_api).2
  simpa [sourceDGFDiameter, sourceDGFDiameterSq] using hsrc

/-- Existence of Lan's initial point: a minimizer of `ν` on `Z` that belongs to `Zᵒ`.

This is derived from the stated closed, bounded, nonempty feasible sets and the
distance-generating-function regularity; it is intentionally not a `Setup` field. -/
theorem initialPoint_exists :
    ∃ z : setup.InteriorPoint, IsMinOn setup.productPotential Set.univ (setup.interiorPointToPoint z) := by
  simpa [sourceDGFCore, Setup.interiorPointToPoint, sourceDGFCoreToCarrier] using
    (SOptLib.sourceDGFCorePoint_exists_isMinOn_of_compact
      (X := setup.jointCarrier) (nu := setup.productPotential)
      (hcompact := by
        simpa [Setup.Point] using
          (isCompact_univ_subtype_of_isClosed_isBounded setup.jointCarrier_closed
            setup.jointCarrier_bounded))
      setup.jointCarrier_nonempty setup.productDGF_continuousOn)


/-- The feasible-carrier view of the initial point `z₁`. -/
noncomputable def initialPoint : setup.Point :=
  setup.interiorPointToPoint (Classical.choose setup.initialPoint_exists)

/-- The selected initial point satisfies the source initialization condition. -/
theorem initialPoint_isMinOn :
    IsMinOn setup.productPotential Set.univ setup.initialPoint := by
  exact Classical.choose_spec setup.initialPoint_exists

/-- Source gradient of the product distance generator on `Zᵒ`. -/
noncomputable def productDGFGradient (z : setup.InteriorPoint) : Ambient EX EY :=
  sourceDGFGradient setup.jointCarrier setup.productPotential z.1

/-- Continuity of the product DGF gradient in the notation used by the prox
function. -/
theorem productDGFGradient_continuous :
    Continuous (fun z : setup.InteriorPoint => setup.productDGFGradient z) := by
  simpa [Setup.productDGFGradient] using setup.productDGF_selectedGradient_continuous

/-- The prox function `V(z,u) : Zᵒ × Z → ℝ` associated with `ν` and `Z`. -/
noncomputable def proxFunction (z : setup.InteriorPoint) (u : setup.Point) : ℝ :=
  sourceDGFProx setup.productPotential z u

/-- Expanded Bregman formula for the product prox function. -/
theorem proxFunction_def (z : setup.InteriorPoint) (u : setup.Point) :
    setup.proxFunction z u =
      setup.productPotential u - setup.productPotential (setup.interiorPointToPoint z) -
        ⟪setup.productDGFGradient z, u.1 - z.1⟫_ℝ := by
  rfl

/-- Compactness of the product feasible carrier `Z`.

This is a theorem from the stated closed and bounded finite-dimensional carriers,
not an additional setup assumption. -/
theorem point_univ_isCompact : IsCompact (Set.univ : Set setup.Point) := by
  simpa [Setup.Point] using
    (isCompact_univ_subtype_of_isClosed_isBounded setup.jointCarrier_closed
      setup.jointCarrier_bounded)

/-- Continuity of the product prox function used to select the canonical argmin. -/
theorem proxFunction_continuous :
    Continuous (fun p : setup.InteriorPoint × setup.Point => setup.proxFunction p.1 p.2) := by
  classical
  have hnu_point : Continuous (fun u : setup.Point => setup.productPotential u) := by
    refine continuous_subtype_of_continuousOn_ambient
      (X := setup.jointCarrier) setup.productPotential
      (SOptLib.totalizeOn setup.jointCarrier setup.productPotential)
      setup.productDGF_continuousOn ?_
    intro x
    exact SOptLib.totalizeOn_of_mem setup.jointCarrier setup.productPotential x.2
  have hcore_to_point : Continuous (fun z : setup.InteriorPoint =>
      setup.interiorPointToPoint z) := by
    change Continuous (fun z : setup.InteriorPoint =>
      (⟨z.1, Classical.choose z.2⟩ : setup.Point))
    exact Continuous.subtype_mk continuous_subtype_val (fun z => Classical.choose z.2)
  have hnu_u : Continuous
      (fun p : setup.InteriorPoint × setup.Point => setup.productPotential p.2) :=
    hnu_point.comp continuous_snd
  have hnu_z : Continuous
      (fun p : setup.InteriorPoint × setup.Point =>
        setup.productPotential (setup.interiorPointToPoint p.1)) :=
    hnu_point.comp (hcore_to_point.comp continuous_fst)
  have hgrad : Continuous
      (fun p : setup.InteriorPoint × setup.Point => setup.productDGFGradient p.1) :=
    setup.productDGFGradient_continuous.comp continuous_fst
  have hu : Continuous
      (fun p : setup.InteriorPoint × setup.Point => (p.2 : setup.Point).1) :=
    continuous_subtype_val.comp continuous_snd
  have hz : Continuous
      (fun p : setup.InteriorPoint × setup.Point => (p.1 : setup.InteriorPoint).1) :=
    continuous_subtype_val.comp continuous_fst
  have hdisp : Continuous
      (fun p : setup.InteriorPoint × setup.Point => p.2.1 - p.1.1) :=
    hu.sub hz
  have hinner : Continuous
      (fun p : setup.InteriorPoint × setup.Point =>
        ⟪setup.productDGFGradient p.1, p.2.1 - p.1.1⟫_ℝ) :=
    hgrad.inner hdisp
  simpa [setup.proxFunction_def] using (hnu_u.sub hnu_z).sub hinner

/-- Continuity of the ambient evaluation map from feasible states. -/
theorem pointEval_continuous :
    Continuous (fun z : setup.Point => z.1) := by
  exact continuous_subtype_val

/-- Mirror-prox objective minimized in one stochastic mirror-descent step. -/
noncomputable def mirrorStepObjective
    (z : setup.InteriorPoint) (g : Ambient EX EY) (γ : ℝ) (u : setup.Point) : ℝ :=
  SOptLib.literalMirrorObjective setup.proxFunction (fun u : setup.Point => u.1) z g γ u

/-- The carrier argmin for the one-step stochastic mirror descent update exists. -/
theorem mirrorStepPoint_exists (z : setup.InteriorPoint) (g : Ambient EX EY) (γ : ℝ) :
    ∃ u : setup.Point, IsMinOn (setup.mirrorStepObjective z g γ) Set.univ u := by
  classical
  have hV : Continuous (fun u : setup.Point => setup.proxFunction z u) :=
    setup.proxFunction_continuous.comp (continuous_const.prodMk continuous_id)
  have hlin : Continuous (fun u : setup.Point => γ * ⟪g, u.1⟫_ℝ) :=
    continuous_const.mul (continuous_const.inner setup.pointEval_continuous)
  have hobj : Continuous (setup.mirrorStepObjective z g γ) := by
    simpa [Setup.mirrorStepObjective, SOptLib.literalMirrorObjective] using hlin.add hV
  have hcompact : IsCompact (Set.univ : Set setup.Point) := setup.point_univ_isCompact
  have hne : (Set.univ : Set setup.Point).Nonempty := by
    rcases setup.jointCarrier_nonempty with ⟨p, hp⟩
    exact ⟨⟨p, hp⟩, by simp⟩
  rcases hcompact.exists_isMinOn hne hobj.continuousOn with ⟨u, _huuniv, humin⟩
  exact ⟨u, humin⟩

/-- Canonical carrier-valued mirror step selected by the source argmin problem. -/
noncomputable def mirrorStepPoint
    (z : setup.InteriorPoint) (g : Ambient EX EY) (γ : ℝ) : setup.Point :=
  SOptLib.literalMirrorStep
    (Vlit := setup.proxFunction)
    (eval := fun u : setup.Point => u.1)
    (hcompact := setup.point_univ_isCompact)
    (hne := by
      rcases setup.jointCarrier_nonempty with ⟨p, hp⟩
      exact ⟨⟨p, hp⟩, by simp⟩)
    (heval := setup.pointEval_continuous)
    (x := z)
    (by
      first
      | exact setup.proxFunction_continuous
      | exact setup.proxFunction_continuous.comp (continuous_const.prodMk continuous_id))
    (g := g) (gamma := γ)

/-- The selected carrier point satisfies the source argmin predicate. -/
theorem mirrorStepPoint_isMinOn (z : setup.InteriorPoint) (g : Ambient EX EY) (γ : ℝ) :
    IsMinOn (setup.mirrorStepObjective z g γ) Set.univ
      (setup.mirrorStepPoint z g γ) := by
  simpa [Setup.mirrorStepObjective, Setup.mirrorStepPoint] using
    (SOptLib.literalMirrorStep_isMinOn
      (Vlit := setup.proxFunction)
      (eval := fun u : setup.Point => u.1)
      (hcompact := setup.point_univ_isCompact)
      (hne := by
        rcases setup.jointCarrier_nonempty with ⟨p, hp⟩
        exact ⟨⟨p, hp⟩, by simp⟩)
      (heval := setup.pointEval_continuous)
      (x := z)
      (by
        first
        | exact setup.proxFunction_continuous
        | exact setup.proxFunction_continuous.comp (continuous_const.prodMk continuous_id))
      (g := g) (gamma := γ))

/-- The selected prox minimizer lies in `Zᵒ`, by the definition of the source core. -/
theorem mirrorStepPoint_mem_core
    (z : setup.InteriorPoint) (g : Ambient EX EY) (γ : ℝ) :
    (setup.mirrorStepPoint z g γ).1 ∈ sourceDGFCore setup.jointCarrier setup.productPotential := by
  classical
  let m : setup.Point := setup.mirrorStepPoint z g γ
  let grad : Ambient EX EY := setup.productDGFGradient z
  refine ⟨m.2, γ • g - grad, ?_⟩
  intro u
  have hmin := (isMinOn_univ_iff.mp (setup.mirrorStepPoint_isMinOn z g γ)) u
  have hmin' :
      γ * ⟪g, m.1⟫_ℝ +
          (setup.productPotential m - setup.productPotential (setup.interiorPointToPoint z) -
            (⟪grad, m.1⟫_ℝ - ⟪grad, z.1⟫_ℝ)) ≤
        γ * ⟪g, u.1⟫_ℝ +
          (setup.productPotential u - setup.productPotential (setup.interiorPointToPoint z) -
            (⟪grad, u.1⟫_ℝ - ⟪grad, z.1⟫_ℝ)) := by
    simpa [m, grad, Setup.mirrorStepObjective, SOptLib.literalMirrorObjective,
      setup.proxFunction_def, inner_sub_right] using hmin
  have htarget :
      γ * ⟪g, m.1⟫_ℝ - ⟪grad, m.1⟫_ℝ + setup.productPotential m ≤
        γ * ⟪g, u.1⟫_ℝ - ⟪grad, u.1⟫_ℝ + setup.productPotential u := by
    nlinarith [hmin']
  have hm_inner :
      ⟪γ • g - grad, m.1⟫_ℝ = γ * ⟪g, m.1⟫_ℝ - ⟪grad, m.1⟫_ℝ := by
    simp [sub_eq_add_neg, inner_add_left, inner_neg_left, real_inner_smul_left,
      mul_add]
  have hu_inner :
      ⟪γ • g - grad, u.1⟫_ℝ = γ * ⟪g, u.1⟫_ℝ - ⟪grad, u.1⟫_ℝ := by
    simp [sub_eq_add_neg, inner_add_left, inner_neg_left, real_inner_smul_left,
      mul_add]
  calc
    ⟪γ • g - grad, m.1⟫_ℝ + setup.productPotential m
        = γ * ⟪g, m.1⟫_ℝ - ⟪grad, m.1⟫_ℝ + setup.productPotential m := by
          rw [hm_inner]
    _ ≤ γ * ⟪g, u.1⟫_ℝ - ⟪grad, u.1⟫_ℝ + setup.productPotential u := htarget
    _ = ⟪γ • g - grad, u.1⟫_ℝ + setup.productPotential u := by
          rw [hu_inner]

/-- Canonical one-step stochastic mirror descent update in the prox domain `Zᵒ`. -/
noncomputable def mirrorStep
    (z : setup.InteriorPoint) (g : Ambient EX EY) (γ : ℝ) : setup.InteriorPoint :=
  ⟨(setup.mirrorStepPoint z g γ).1, setup.mirrorStepPoint_mem_core z g γ⟩

/-- Carrier view of the canonical mirror step. -/
theorem mirrorStep_toPoint
    (z : setup.InteriorPoint) (g : Ambient EX EY) (γ : ℝ) :
    setup.interiorPointToPoint (setup.mirrorStep z g γ) =
      setup.mirrorStepPoint z g γ := by
  ext
  rfl

/-- Expanded minimization theorem for the canonical mirror step. -/
theorem mirrorStep_minimizes (z : setup.InteriorPoint) (y : setup.Point)
    (g : Ambient EX EY) (γ : ℝ) :
    γ * ⟪g, (setup.interiorPointToPoint (setup.mirrorStep z g γ)).1⟫_ℝ +
        setup.proxFunction z (setup.interiorPointToPoint (setup.mirrorStep z g γ)) ≤
      γ * ⟪g, y.1⟫_ℝ + setup.proxFunction z y := by
  have h := setup.mirrorStepPoint_isMinOn z g γ
  have hle := (isMinOn_univ_iff.mp h) y
  simpa [Setup.mirrorStepObjective, SOptLib.literalMirrorObjective,
    setup.mirrorStep_toPoint z g γ] using hle

private theorem mirrorStepObjective_minimizer_mem_core
    (z : setup.InteriorPoint) (g : Ambient EX EY) (γ : ℝ) (m : setup.Point)
    (hm : ∀ y : setup.Point,
      setup.mirrorStepObjective z g γ m ≤ setup.mirrorStepObjective z g γ y) :
    m.1 ∈ sourceDGFCore setup.jointCarrier setup.productPotential := by
  classical
  let grad : Ambient EX EY := setup.productDGFGradient z
  refine ⟨m.2, γ • g - grad, ?_⟩
  intro u
  have hmin := hm u
  have hmin' :
      γ * ⟪g, m.1⟫_ℝ +
          (setup.productPotential m - setup.productPotential (setup.interiorPointToPoint z) -
            (⟪grad, m.1⟫_ℝ - ⟪grad, z.1⟫_ℝ)) ≤
        γ * ⟪g, u.1⟫_ℝ +
          (setup.productPotential u - setup.productPotential (setup.interiorPointToPoint z) -
            (⟪grad, u.1⟫_ℝ - ⟪grad, z.1⟫_ℝ)) := by
    simpa [grad, Setup.mirrorStepObjective, SOptLib.literalMirrorObjective,
      setup.proxFunction_def, inner_sub_right] using hmin
  have htarget :
      γ * ⟪g, m.1⟫_ℝ - ⟪grad, m.1⟫_ℝ + setup.productPotential m ≤
        γ * ⟪g, u.1⟫_ℝ - ⟪grad, u.1⟫_ℝ + setup.productPotential u := by
    nlinarith [hmin']
  have hm_inner :
      ⟪γ • g - grad, m.1⟫_ℝ = γ * ⟪g, m.1⟫_ℝ - ⟪grad, m.1⟫_ℝ := by
    simp [sub_eq_add_neg, inner_add_left, inner_neg_left, real_inner_smul_left,
      mul_add]
  have hu_inner :
      ⟪γ • g - grad, u.1⟫_ℝ = γ * ⟪g, u.1⟫_ℝ - ⟪grad, u.1⟫_ℝ := by
    simp [sub_eq_add_neg, inner_add_left, inner_neg_left, real_inner_smul_left,
      mul_add]
  calc
    ⟪γ • g - grad, m.1⟫_ℝ + setup.productPotential m
        = γ * ⟪g, m.1⟫_ℝ - ⟪grad, m.1⟫_ℝ + setup.productPotential m := by
          rw [hm_inner]
    _ ≤ γ * ⟪g, u.1⟫_ℝ - ⟪grad, u.1⟫_ℝ + setup.productPotential u := htarget
    _ = ⟪γ • g - grad, u.1⟫_ℝ + setup.productPotential u := by
          rw [hu_inner]

private theorem mirrorStepObjective_totalize_segment_hasDerivWithinAt_zero
    (y : setup.InteriorPoint) (u : setup.Point) :
    HasDerivWithinAt
      (fun t : ℝ =>
        SOptLib.totalizeOn setup.jointCarrier setup.productPotential
          (AffineMap.lineMap y.1 u.1 t))
      ⟪setup.productDGFGradient y, u.1 - y.1⟫_ℝ
      (Set.Icc (0 : ℝ) 1) 0 := by
  let s : Set ℝ := Set.Icc (0 : ℝ) 1
  let line : ℝ → Ambient EX EY := fun t => AffineMap.lineMap y.1 u.1 t
  let d : Ambient EX EY := u.1 - y.1
  have hgrad_core :
      HasGradientWithinAt
        (SOptLib.totalizeOn setup.jointCarrier setup.productPotential)
        (sourceDGFGradient setup.jointCarrier setup.productPotential y.1)
        setup.jointCarrier y.1 :=
    setup.productDGF_modulus_one.gradient_hasGradientWithinAt y.2
  have hline_deriv_s : HasDerivWithinAt line d s 0 := by
    simpa [line, d] using
      (AffineMap.hasDerivWithinAt_lineMap (a := y.1) (b := u.1)
        (s := s) (x := (0 : ℝ)))
  have hmaps :
      Set.MapsTo line s setup.jointCarrier := by
    intro t ht
    exact setup.jointCarrier_convex.lineMap_mem (Classical.choose y.2) u.2 ht
  have hbase : y.1 = line 0 := by
    simp [line, AffineMap.lineMap_apply_module']
  have hν_s :
      HasDerivWithinAt
        (fun t : ℝ =>
          SOptLib.totalizeOn setup.jointCarrier setup.productPotential (line t))
        ⟪setup.productDGFGradient y, d⟫_ℝ s 0 := by
    have hcomp := hgrad_core.hasFDerivWithinAt.comp_hasDerivWithinAt_of_eq
      0 hline_deriv_s hmaps hbase
    simpa [Function.comp_def, d, Setup.productDGFGradient] using hcomp
  simpa [line, d, s] using hν_s

private theorem mirrorStepObjective_minimizer_first_variation_nonneg
    (z : setup.InteriorPoint) (g : Ambient EX EY) (γ : ℝ) (m q : setup.Point)
    (hm : ∀ y : setup.Point,
      setup.mirrorStepObjective z g γ m ≤ setup.mirrorStepObjective z g γ y) :
    0 ≤
      γ * ⟪g, q.1 - m.1⟫_ℝ +
        (⟪setup.productDGFGradient
              ⟨m.1, setup.mirrorStepObjective_minimizer_mem_core z g γ m hm⟩,
            q.1 - m.1⟫_ℝ -
          ⟪setup.productDGFGradient z, q.1 - m.1⟫_ℝ) := by
  classical
  let y : setup.InteriorPoint :=
    ⟨m.1, setup.mirrorStepObjective_minimizer_mem_core z g γ m hm⟩
  have hy_point : setup.interiorPointToPoint y = m := by
    ext
    rfl
  have hmin :
      γ * ⟪g, y.1⟫_ℝ +
          setup.proxFunction z (setup.interiorPointToPoint y) ≤
        γ * ⟪g, q.1⟫_ℝ + setup.proxFunction z q := by
    simpa [hy_point, Setup.mirrorStepObjective, SOptLib.literalMirrorObjective] using
      hm q
  have hconv := setup.jointCarrier_convex
  let s : Set ℝ := Set.Icc (0 : ℝ) 1
  let line : ℝ → Ambient EX EY := fun t => AffineMap.lineMap y.1 q.1 t
  have hline_mem : ∀ t ∈ s, line t ∈ setup.jointCarrier := by
    intro t ht
    exact hconv.lineMap_mem (Classical.choose y.2) q.2 ht
  let segmentPoint : (t : ℝ) → t ∈ s → setup.Point :=
    fun t ht => ⟨line t, hline_mem t ht⟩
  let φ : ℝ → ℝ := fun t =>
    if ht : t ∈ s then
      γ * ⟪g, line t⟫_ℝ + setup.proxFunction z (segmentPoint t ht)
    else 0
  have hφmin : ∀ t ∈ s, φ 0 ≤ φ t := by
    intro t ht
    have h0 : (0 : ℝ) ∈ s := by
      norm_num [s]
    have hseg0 : segmentPoint 0 h0 = setup.interiorPointToPoint y := by
      ext
      simp [segmentPoint, line, AffineMap.lineMap_apply_module',
        Setup.interiorPointToPoint, sourceDGFCoreToCarrier]
    have hφ0 :
        φ 0 =
          γ * ⟪g, y.1⟫_ℝ +
            setup.proxFunction z (setup.interiorPointToPoint y) := by
      dsimp [φ]
      rw [dif_pos h0, hseg0]
      simp [line, AffineMap.lineMap_apply_module']
    have hφt :
        φ t =
          γ * ⟪g, line t⟫_ℝ + setup.proxFunction z (segmentPoint t ht) := by
      dsimp [φ]
      rw [dif_pos ht]
    have hmin_t :
        γ * ⟪g, y.1⟫_ℝ +
            setup.proxFunction z (setup.interiorPointToPoint y) ≤
          γ * ⟪g, line t⟫_ℝ + setup.proxFunction z (segmentPoint t ht) := by
      have hmt := hm (segmentPoint t ht)
      simpa [hy_point, segmentPoint, Setup.mirrorStepObjective,
        SOptLib.literalMirrorObjective] using hmt
    rw [hφ0, hφt]
    exact hmin_t
  have hφderiv :
      HasDerivWithinAt φ
        (γ * ⟪g, q.1 - y.1⟫_ℝ +
          (⟪setup.productDGFGradient y, q.1 - y.1⟫_ℝ -
            ⟪setup.productDGFGradient z, q.1 - y.1⟫_ℝ))
        s 0 := by
    let d : Ambient EX EY := q.1 - y.1
    have hνseg :
        HasDerivWithinAt
          (fun t : ℝ => SOptLib.totalizeOn setup.jointCarrier setup.productPotential (line t))
          ⟪setup.productDGFGradient y, d⟫_ℝ s 0 := by
      simpa [line, s, d] using
        setup.mirrorStepObjective_totalize_segment_hasDerivWithinAt_zero y q
    let β : ℝ → ℝ := fun t =>
      if ht : t ∈ s then
        setup.proxFunction z (segmentPoint t ht) -
          setup.proxFunction z (setup.interiorPointToPoint y)
      else 0
    have hβ : HasDerivWithinAt β
        (⟪setup.productDGFGradient y, d⟫_ℝ -
          ⟪setup.productDGFGradient z, d⟫_ℝ) s 0 := by
      let expr : ℝ → ℝ := fun t =>
        (SOptLib.totalizeOn setup.jointCarrier setup.productPotential (line t) -
          SOptLib.totalizeOn setup.jointCarrier setup.productPotential y.1) -
          t * ⟪setup.productDGFGradient z, d⟫_ℝ
      have hlin : HasDerivWithinAt
          (fun t : ℝ => t * ⟪setup.productDGFGradient z, d⟫_ℝ)
          ⟪setup.productDGFGradient z, d⟫_ℝ s 0 := by
        simpa using (hasDerivWithinAt_id (x := (0 : ℝ)) (s := s)).mul_const
          ⟪setup.productDGFGradient z, d⟫_ℝ
      have hexpr : HasDerivWithinAt expr
          (⟪setup.productDGFGradient y, d⟫_ℝ -
            ⟪setup.productDGFGradient z, d⟫_ℝ) s 0 := by
        exact
          (hνseg.sub_const
            (SOptLib.totalizeOn setup.jointCarrier setup.productPotential y.1)).sub hlin
      have heq : ∀ t ∈ s, β t = expr t := by
        intro t ht
        have htI : t ∈ s := ht
        have hline_sub : line t - y.1 = t • d := by
          simp [line, d, AffineMap.lineMap_apply_module']
        have htotal_line :
            SOptLib.totalizeOn setup.jointCarrier setup.productPotential (line t) =
              setup.productPotential (segmentPoint t htI) := by
          simpa [segmentPoint] using
            (SOptLib.totalizeOn_of_mem setup.jointCarrier setup.productPotential
              (hline_mem t htI))
        have htotal_y :
            SOptLib.totalizeOn setup.jointCarrier setup.productPotential y.1 =
              setup.productPotential (setup.interiorPointToPoint y) := by
          simpa [Setup.interiorPointToPoint, sourceDGFCoreToCarrier] using
            (SOptLib.totalizeOn_of_mem setup.jointCarrier setup.productPotential
              (Classical.choose y.2))
        dsimp [β, expr]
        rw [dif_pos htI, setup.proxFunction_def z (segmentPoint t htI),
          setup.proxFunction_def z (setup.interiorPointToPoint y), ← htotal_line,
          ← htotal_y]
        have hseg_coe : (segmentPoint t htI).1 = line t := rfl
        have hy_coe : (setup.interiorPointToPoint y).1 = y.1 := rfl
        rw [hseg_coe, hy_coe]
        have hz_split : line t - z.1 = (line t - y.1) + (y.1 - z.1) := by
          abel
        rw [hz_split, inner_add_right, hline_sub, real_inner_smul_right]
        simp [WithLp.prod_inner_apply]
        ring
      exact hexpr.congr heq (by
        have h0 : (0 : ℝ) ∈ s := by norm_num [s]
        exact heq 0 h0)
    let proxAlong : ℝ → ℝ := fun t =>
      if ht : t ∈ s then setup.proxFunction z (segmentPoint t ht) else 0
    have hprox : HasDerivWithinAt proxAlong
        (⟪setup.productDGFGradient y, d⟫_ℝ -
          ⟪setup.productDGFGradient z, d⟫_ℝ) s 0 := by
      have htmp := hβ.add_const (setup.proxFunction z (setup.interiorPointToPoint y))
      refine htmp.congr ?_ ?_
      · intro t ht
        dsimp [proxAlong, β]
        rw [dif_pos ht, dif_pos ht]
        ring
      · have h0 : (0 : ℝ) ∈ s := by norm_num [s]
        dsimp [proxAlong, β]
        rw [dif_pos h0, dif_pos h0]
        ring
    have hlin_obj : HasDerivWithinAt (fun t : ℝ => γ * ⟪g, line t⟫_ℝ)
        (γ * ⟪g, d⟫_ℝ) s 0 := by
      have hinner_aff :
          ∀ t : ℝ, ⟪g, line t⟫_ℝ = ⟪g, y.1⟫_ℝ + t * ⟪g, d⟫_ℝ := by
        intro t
        simp [line, d, AffineMap.lineMap_apply_module', inner_add_right,
          real_inner_smul_right]
        ring
      have hbase : HasDerivWithinAt
          (fun t : ℝ => ⟪g, y.1⟫_ℝ + t * ⟪g, d⟫_ℝ)
          ⟪g, d⟫_ℝ s 0 := by
        simpa using ((hasDerivWithinAt_id (x := (0 : ℝ)) (s := s)).mul_const
          ⟪g, d⟫_ℝ).const_add ⟪g, y.1⟫_ℝ
      have hinner : HasDerivWithinAt (fun t : ℝ => ⟪g, line t⟫_ℝ)
          ⟪g, d⟫_ℝ s 0 := by
        refine hbase.congr ?_ ?_
        · intro t _ht
          exact hinner_aff t
        · exact hinner_aff 0
      simpa using hinner.const_mul γ
    have hsum := hlin_obj.add hprox
    simpa [d] using hsum.congr (by
      intro t ht
      dsimp [φ, proxAlong]
      rw [dif_pos ht, dif_pos ht]) (by
      have h0 : (0 : ℝ) ∈ s := by norm_num [s]
      dsimp [φ, proxAlong]
      rw [dif_pos h0, dif_pos h0])
  have hnonneg := right_derivative_nonneg_of_min_on_Icc (φ := φ) hφderiv hφmin
  simpa [y, s] using hnonneg

private theorem mirrorStepObjective_minimizer_variational_inequality
    (z : setup.InteriorPoint) (g : Ambient EX EY) (γ : ℝ) (m q : setup.Point)
    (hm : ∀ y : setup.Point,
      setup.mirrorStepObjective z g γ m ≤ setup.mirrorStepObjective z g γ y) :
    0 ≤
      ⟪γ • g +
          setup.productDGFGradient
            ⟨m.1, setup.mirrorStepObjective_minimizer_mem_core z g γ m hm⟩ -
          setup.productDGFGradient z,
        q.1 - m.1⟫_ℝ := by
  classical
  let y : setup.InteriorPoint :=
    ⟨m.1, setup.mirrorStepObjective_minimizer_mem_core z g γ m hm⟩
  have hfirst :=
    setup.mirrorStepObjective_minimizer_first_variation_nonneg z g γ m q hm
  have hinner :
      ⟪γ • g + setup.productDGFGradient y - setup.productDGFGradient z,
        q.1 - y.1⟫_ℝ =
        γ * ⟪g, q.1 - y.1⟫_ℝ +
          ⟪setup.productDGFGradient y, q.1 - y.1⟫_ℝ -
            ⟪setup.productDGFGradient z, q.1 - y.1⟫_ℝ := by
    rw [inner_sub_left, inner_add_left, real_inner_smul_left]
  rw [hinner]
  ring_nf at hfirst ⊢
  exact hfirst

private theorem productNorm_sq_nonpos_eq_zero
    {w : Ambient EX EY} (h : setup.productNorm w ^ 2 ≤ 0) :
    w = 0 := by
  have hsq : setup.productNorm w ^ 2 = 0 := le_antisymm h (sq_nonneg _)
  have hrad_nonneg :
      0 ≤
        (setup.normX w.fst) ^ 2 / (2 * setup.DX ^ 2) +
          (setup.normY w.snd) ^ 2 / (2 * setup.DY ^ 2) := by
    exact add_nonneg
      (div_nonneg (sq_nonneg _) (by positivity))
      (div_nonneg (sq_nonneg _) (by positivity))
  have hsum :
      (setup.normX w.fst) ^ 2 / (2 * setup.DX ^ 2) +
          (setup.normY w.snd) ^ 2 / (2 * setup.DY ^ 2) = 0 := by
    simpa [Setup.productNorm_def, hrad_nonneg] using hsq
  have hDXden_pos : 0 < 2 * setup.DX ^ 2 := by
    have hDX : 0 < setup.DX := setup.DX_pos
    nlinarith [sq_pos_of_pos hDX]
  have hDYden_pos : 0 < 2 * setup.DY ^ 2 := by
    have hDY : 0 < setup.DY := setup.DY_pos
    nlinarith [sq_pos_of_pos hDY]
  have hXterm_nonneg : 0 ≤ (setup.normX w.fst) ^ 2 / (2 * setup.DX ^ 2) :=
    div_nonneg (sq_nonneg _) (le_of_lt hDXden_pos)
  have hYterm_nonneg : 0 ≤ (setup.normY w.snd) ^ 2 / (2 * setup.DY ^ 2) :=
    div_nonneg (sq_nonneg _) (le_of_lt hDYden_pos)
  have hXterm_zero :
      (setup.normX w.fst) ^ 2 / (2 * setup.DX ^ 2) = 0 := by
    nlinarith
  have hYterm_zero :
      (setup.normY w.snd) ^ 2 / (2 * setup.DY ^ 2) = 0 := by
    nlinarith
  have hXsq_zero : (setup.normX w.fst) ^ 2 = 0 := by
    rcases div_eq_zero_iff.mp hXterm_zero with hnum | hden
    · exact hnum
    · exact False.elim ((ne_of_gt hDXden_pos) hden)
  have hYsq_zero : (setup.normY w.snd) ^ 2 = 0 := by
    rcases div_eq_zero_iff.mp hYterm_zero with hnum | hden
    · exact hnum
    · exact False.elim ((ne_of_gt hDYden_pos) hden)
  have hXzero : w.fst = 0 := by
    exact (setup.hnormX_separating w.fst).mp (sq_eq_zero_iff.mp hXsq_zero)
  have hYzero : w.snd = 0 := by
    exact (setup.hnormY_separating w.snd).mp (sq_eq_zero_iff.mp hYsq_zero)
  apply (WithLp.ofLp_injective (p := 2))
  change (w.fst, w.snd) = (0, 0)
  simp [hXzero, hYzero]

/-- Uniqueness of the compact mirror-prox argmin selected in one stochastic
mirror-descent step.

This is the exact source-side strict-convexity leaf needed by the measurable
selector theorem: two carrier points minimizing the same linear-plus-Bregman
objective must coincide.  The intended proof applies the product DGF
modulus-one monotonicity and the first-order variational inequality for
carrier Bregman objectives. -/
theorem mirrorStepPoint_argmin_unique
    (z : setup.InteriorPoint) (g : Ambient EX EY) (γ : ℝ)
    (u v : setup.Point)
    (hu : ∀ y : setup.Point,
      setup.mirrorStepObjective z g γ u ≤ setup.mirrorStepObjective z g γ y)
    (hv : ∀ y : setup.Point,
      setup.mirrorStepObjective z g γ v ≤ setup.mirrorStepObjective z g γ y) :
    u = v := by
  classical
  have hu_core :
      u.1 ∈ sourceDGFCore setup.jointCarrier setup.productPotential :=
    setup.mirrorStepObjective_minimizer_mem_core z g γ u hu
  have hv_core :
      v.1 ∈ sourceDGFCore setup.jointCarrier setup.productPotential :=
    setup.mirrorStepObjective_minimizer_mem_core z g γ v hv
  let uI : setup.InteriorPoint := ⟨u.1, hu_core⟩
  let vI : setup.InteriorPoint := ⟨v.1, hv_core⟩
  have huv :
      0 ≤
        ⟪γ • g + setup.productDGFGradient uI - setup.productDGFGradient z,
          v.1 - u.1⟫_ℝ := by
    simpa [uI] using
      setup.mirrorStepObjective_minimizer_variational_inequality z g γ u v hu
  have hvu :
      0 ≤
        ⟪γ • g + setup.productDGFGradient vI - setup.productDGFGradient z,
          u.1 - v.1⟫_ℝ := by
    simpa [vI] using
      setup.mirrorStepObjective_minimizer_variational_inequality z g γ v u hv
  have hsum_nonneg :
      0 ≤
        ⟪γ • g + setup.productDGFGradient uI - setup.productDGFGradient z,
          v.1 - u.1⟫_ℝ +
        ⟪γ • g + setup.productDGFGradient vI - setup.productDGFGradient z,
          u.1 - v.1⟫_ℝ := add_nonneg huv hvu
  have hsum_eq :
      ⟪γ • g + setup.productDGFGradient uI - setup.productDGFGradient z,
          v.1 - u.1⟫_ℝ +
        ⟪γ • g + setup.productDGFGradient vI - setup.productDGFGradient z,
          u.1 - v.1⟫_ℝ =
        -⟪setup.productDGFGradient vI - setup.productDGFGradient uI,
          v.1 - u.1⟫_ℝ := by
    have hrev : u.1 - v.1 = -(v.1 - u.1) := by
      abel
    rw [hrev, inner_neg_right]
    simp [inner_add_left, inner_sub_left]
  have hgrad_nonpos :
      ⟪setup.productDGFGradient vI - setup.productDGFGradient uI,
        v.1 - u.1⟫_ℝ ≤ 0 := by
    nlinarith
  have hmono :
      setup.productNorm (v.1 - u.1) ^ 2 ≤
        ⟪setup.productDGFGradient vI - setup.productDGFGradient uI,
          v.1 - u.1⟫_ℝ := by
    simpa [uI, vI, Setup.productDGFGradient] using
      setup.productDGF_modulus_one.monotone u.1 hu_core v.1 hv_core
  have hnorm_nonpos : setup.productNorm (v.1 - u.1) ^ 2 ≤ 0 := by
    linarith
  have hdiff : v.1 - u.1 = 0 :=
    setup.productNorm_sq_nonpos_eq_zero hnorm_nonpos
  apply Subtype.ext
  exact (sub_eq_zero.mp hdiff).symm

/-- Mixed-domain continuity of the selected carrier-valued mirror step.

This is the actual compact unique-argmin selector interface requested by the
cross-term reconstruction: the parameter is `(z, G(z,ξ))` and the candidate
space is the compact carrier `Z`. -/
theorem mirrorStepPoint_continuous
    (γ : ℝ) :
    Continuous
      (fun p : setup.InteriorPoint × Ambient EX EY =>
        setup.mirrorStepPoint p.1 p.2 γ) := by
  classical
  letI : CompactSpace setup.Point := isCompact_univ_iff.mp setup.point_univ_isCompact
  let F : (setup.InteriorPoint × Ambient EX EY) → setup.Point → ℝ :=
    fun p u => setup.mirrorStepObjective p.1 p.2 γ u
  refine continuous_argmin_of_compact_unique
    (P := setup.InteriorPoint × Ambient EX EY) (K := setup.Point)
    (F := F)
    (sel := fun p => setup.mirrorStepPoint p.1 p.2 γ) ?_ ?_ ?_
  · have hlin : Continuous
        (fun q : (setup.InteriorPoint × Ambient EX EY) × setup.Point =>
          γ * ⟪q.1.2, q.2.1⟫_ℝ) :=
      continuous_const.mul
        ((continuous_snd.comp continuous_fst).inner
          (setup.pointEval_continuous.comp continuous_snd))
    have hprox : Continuous
        (fun q : (setup.InteriorPoint × Ambient EX EY) × setup.Point =>
          setup.proxFunction q.1.1 q.2) :=
      setup.proxFunction_continuous.comp
        ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
    simpa [F, Setup.mirrorStepObjective, SOptLib.literalMirrorObjective] using
      hlin.add hprox
  · intro p y
    exact (isMinOn_univ_iff.mp (setup.mirrorStepPoint_isMinOn p.1 p.2 γ)) y
  · intro p u v hu hv
    exact setup.mirrorStepPoint_argmin_unique p.1 p.2 γ u v hu hv

/-- Zero-based update kernel for the generated stochastic process.

Counter `n` represents paper time `t = n + 1`, so the update uses `ξ_{n+1}` and
`γ_{n+1}`. -/
noncomputable def iterateStep
    (n : ℕ) (z : setup.InteriorPoint) (ω : setup.SamplePath) : setup.InteriorPoint :=
  let t := SOptLib.natSuccPositiveTime n
  let zCarrier := setup.interiorPointToPoint z
  setup.mirrorStep z (setup.stochasticOracle zCarrier (setup.sampleAt t ω)) (setup.gamma t)

/-- Generated zero-based process with `z_0` representing the paper point `z₁`. -/
noncomputable def iterateCoreProcess : ℕ → setup.SamplePath → setup.InteriorPoint :=
  SOptLib.recursive_process_from_random_initial (fun _ω => (Classical.choose setup.initialPoint_exists))
    setup.iterateStep

/-- Carrier-valued generated zero-based process. -/
noncomputable def iterateProcess : ℕ → setup.SamplePath → setup.Point :=
  fun n ω => setup.interiorPointToPoint (setup.iterateCoreProcess n ω)

/-- Paper-time iterate view `z_t`, where positive time `t` is represented by
zero-based recursion counter `t - 1`. -/
noncomputable def iterate (t : Time) : setup.SamplePath → setup.Point :=
  fun ω => setup.iterateProcess (t.1 - 1) ω

@[simp]
theorem iterateCoreProcess_zero :
    setup.iterateCoreProcess 0 = fun _ω => (Classical.choose setup.initialPoint_exists) := by
  rfl

@[simp]
theorem iterateCoreProcess_succ (n : ℕ) (ω : setup.SamplePath) :
    setup.iterateCoreProcess (n + 1) ω =
      setup.mirrorStep (setup.iterateCoreProcess n ω)
        (setup.stochasticOracle (setup.iterateProcess n ω)
          (setup.sampleAt (SOptLib.natSuccPositiveTime n) ω))
        (setup.gamma (SOptLib.natSuccPositiveTime n)) := by
  rfl

@[simp]
theorem iterateProcess_zero :
    setup.iterateProcess 0 = fun _ω => setup.initialPoint := by
  rfl

theorem iterateProcess_succ (n : ℕ) (ω : setup.SamplePath) :
    setup.iterateProcess (n + 1) ω =
      setup.interiorPointToPoint
        (setup.mirrorStep (setup.iterateCoreProcess n ω)
          (setup.stochasticOracle (setup.iterateProcess n ω)
            (setup.sampleAt (SOptLib.natSuccPositiveTime n) ω))
          (setup.gamma (SOptLib.natSuccPositiveTime n))) := by
  rfl

@[simp]
theorem iterate_one (ω : setup.SamplePath) :
    setup.iterate SOptLib.positiveTimeOne ω = setup.initialPoint := by
  rfl

/-- Oracle residual `Δ_t := G(z_t, ξ_t) - g(z_t)` from the proof of Lemma 4.6. -/
noncomputable def oracleNoise (t : Time) (ω : setup.SamplePath) : Ambient EX EY :=
  setup.stochasticOracle (setup.iterate t ω) (setup.sampleAt t ω) -
    setup.meanOracle (setup.iterate t ω)

theorem oracleNoise_def (t : Time) (ω : setup.SamplePath) :
    setup.oracleNoise t ω =
      setup.stochasticOracle (setup.iterate t ω) (setup.sampleAt t ω) -
        setup.meanOracle (setup.iterate t ω) := by
  rfl

private theorem fixed_fiber_stochastic_oracle_integrable (z : setup.Point) :
    Integrable (fun ξ => setup.stochasticOracle z ξ) setup.P := by
  letI : IsProbabilityMeasure setup.P := setup.hP_prob
  have hGx :
      Integrable
        (fun ξ => setup.Gx (setup.xPoint z) (setup.yPoint z) ξ) setup.P := by
    exact setup.Gx_integrable (setup.xPoint z) (setup.yPoint z)
  have hGy :
      Integrable
        (fun ξ => setup.Gy (setup.xPoint z) (setup.yPoint z) ξ) setup.P := by
    exact setup.Gy_integrable (setup.xPoint z) (setup.yPoint z)
  have hGyNeg :
      Integrable
        (fun ξ => -setup.Gy (setup.xPoint z) (setup.yPoint z) ξ) setup.P := by
    simpa only using hGy.neg
  have hpair :
      Integrable
        (fun ξ =>
          (setup.Gx (setup.xPoint z) (setup.yPoint z) ξ,
            -setup.Gy (setup.xPoint z) (setup.yPoint z) ξ)) setup.P := by
    exact hGx.prodMk hGyNeg
  simpa [Setup.stochasticOracle] using
    (ContinuousLinearMap.integrable_comp
      ((WithLp.prodContinuousLinearEquiv (p := 2) (𝕜 := ℝ) EX EY).symm :
        (EX × EY) →L[ℝ] Ambient EX EY) hpair)

private theorem fixed_fiber_stochastic_oracle_integral_eq_mean (z : setup.Point) :
    (∫ ξ, setup.stochasticOracle z ξ ∂setup.P) = setup.meanOracle z := by
  letI : IsProbabilityMeasure setup.P := setup.hP_prob
  have hGx :
      Integrable
        (fun ξ => setup.Gx (setup.xPoint z) (setup.yPoint z) ξ) setup.P := by
    exact setup.Gx_integrable (setup.xPoint z) (setup.yPoint z)
  have hGy :
      Integrable
        (fun ξ => setup.Gy (setup.xPoint z) (setup.yPoint z) ξ) setup.P := by
    exact setup.Gy_integrable (setup.xPoint z) (setup.yPoint z)
  have hGyNeg :
      Integrable
        (fun ξ => -setup.Gy (setup.xPoint z) (setup.yPoint z) ξ) setup.P := by
    simpa only using hGy.neg
  have hpairIntegral :
      (∫ ξ,
          (setup.Gx (setup.xPoint z) (setup.yPoint z) ξ,
            -setup.Gy (setup.xPoint z) (setup.yPoint z) ξ) ∂setup.P) =
        (∫ ξ, setup.Gx (setup.xPoint z) (setup.yPoint z) ξ ∂setup.P,
          -∫ ξ, setup.Gy (setup.xPoint z) (setup.yPoint z) ξ ∂setup.P) := by
    rw [integral_pair
      (f := fun ξ => setup.Gx (setup.xPoint z) (setup.yPoint z) ξ)
      (g := fun ξ => -setup.Gy (setup.xPoint z) (setup.yPoint z) ξ)
      hGx hGyNeg, integral_neg]
  calc
    ∫ ξ, setup.stochasticOracle z ξ ∂setup.P
        = ∫ ξ,
            WithLp.toLp 2
              (setup.Gx (setup.xPoint z) (setup.yPoint z) ξ,
                -setup.Gy (setup.xPoint z) (setup.yPoint z) ξ) ∂setup.P := by
            rfl
    _ = WithLp.toLp 2
          (∫ ξ,
            (setup.Gx (setup.xPoint z) (setup.yPoint z) ξ,
              -setup.Gy (setup.xPoint z) (setup.yPoint z) ξ) ∂setup.P) := by
            simpa using
              (ContinuousLinearEquiv.integral_comp_comm
                ((WithLp.prodContinuousLinearEquiv (p := 2) (𝕜 := ℝ) EX EY).symm)
                (fun ξ =>
                  (setup.Gx (setup.xPoint z) (setup.yPoint z) ξ,
                    -setup.Gy (setup.xPoint z) (setup.yPoint z) ξ)))
    _ = setup.meanOracle z := by
            rw [hpairIntegral]
            simp [Setup.meanOracle, setup.gx_eq_expectation, setup.gy_eq_expectation]

/-- Fixed-query centering of the product oracle residual, derived from
Assumption 7's component mean identities.

This is the deterministic fiber version of `E[Δ_t | ξ_[t-1]] = 0` before it is
transported to a random, strict-past query. -/
theorem fixed_fiber_product_residual_centered (z : setup.Point) :
    ∫ ξ, setup.stochasticOracle z ξ - setup.meanOracle z ∂setup.P = 0 := by
  letI : IsProbabilityMeasure setup.P := setup.hP_prob
  have hOracle : Integrable (fun ξ => setup.stochasticOracle z ξ) setup.P :=
    fixed_fiber_stochastic_oracle_integrable (setup := setup) z
  have hMean :
      (∫ ξ, setup.stochasticOracle z ξ ∂setup.P) = setup.meanOracle z :=
    fixed_fiber_stochastic_oracle_integral_eq_mean (setup := setup) z
  rw [MeasureTheory.integral_sub hOracle (integrable_const (setup.meanOracle z)), hMean]
  simp

/-- Fixed-query integrability of the product oracle residual.

This packages the component Bochner-integrability fields from Assumption 7 in
the product-space residual form used by random-query cancellation lemmas. -/
theorem fixed_fiber_product_residual_integrable (z : setup.Point) :
    Integrable (fun ξ => setup.stochasticOracle z ξ - setup.meanOracle z) setup.P := by
  letI : IsProbabilityMeasure setup.P := setup.hP_prob
  exact (fixed_fiber_stochastic_oracle_integrable (setup := setup) z).sub
    (integrable_const (setup.meanOracle z))

/-- Product-law measurability of the product oracle residual kernel.

This is the law-scoped regularity premise needed to transport Assumption 7's
fixed-query centering to a random query.  It is separated from the martingale
cross-term statement so the remaining obligation is the exact oracle-interface
regularity gap, not the final Lemma 4.6 cancellation. -/
theorem oracle_residual_product_measurable :
    Measurable
      (fun p : (setup.Point × Ambient EX EY) × setup.SamplePoint =>
        setup.stochasticOracle p.1.1 p.2 - setup.meanOracle p.1.1) := by
  classical
  let q :
      ((setup.Point × Ambient EX EY) × setup.SamplePoint) →
        ({x : EX // x ∈ setup.X} × {y : EY // y ∈ setup.Y}) × setup.SamplePoint :=
    fun p => ((setup.xPoint p.1.1, setup.yPoint p.1.1), p.2)
  have hq : Measurable q := by
    have hp : Measurable
        (fun p : (setup.Point × Ambient EX EY) × setup.SamplePoint => p.1.1) :=
      measurable_fst.comp measurable_fst
    have hz : Measurable
        (fun p : (setup.Point × Ambient EX EY) × setup.SamplePoint =>
          (p.1.1 : setup.Point).1) :=
      measurable_subtype_coe.comp hp
    have hxval : Measurable
        (fun p : (setup.Point × Ambient EX EY) × setup.SamplePoint =>
          (p.1.1 : setup.Point).1.fst) :=
      (WithLp.continuous_fst 2 EX EY).measurable.comp hz
    have hyval : Measurable
        (fun p : (setup.Point × Ambient EX EY) × setup.SamplePoint =>
          (p.1.1 : setup.Point).1.snd) :=
      (WithLp.continuous_snd 2 EX EY).measurable.comp hz
    have hxPoint : Measurable
        (fun p : (setup.Point × Ambient EX EY) × setup.SamplePoint =>
          setup.xPoint p.1.1) := by
      change Measurable
        (fun p : (setup.Point × Ambient EX EY) × setup.SamplePoint =>
          (⟨(p.1.1 : setup.Point).1.fst, (p.1.1 : setup.Point).2.1⟩ :
            {x : EX // x ∈ setup.X}))
      exact hxval.subtype_mk
    have hyPoint : Measurable
        (fun p : (setup.Point × Ambient EX EY) × setup.SamplePoint =>
          setup.yPoint p.1.1) := by
      change Measurable
        (fun p : (setup.Point × Ambient EX EY) × setup.SamplePoint =>
          (⟨(p.1.1 : setup.Point).1.snd, (p.1.1 : setup.Point).2.2⟩ :
            {y : EY // y ∈ setup.Y}))
      exact hyval.subtype_mk
    unfold q
    exact (hxPoint.prod hyPoint).prod measurable_snd
  let qxy :
      ((setup.Point × Ambient EX EY) × setup.SamplePoint) →
        {x : EX // x ∈ setup.X} × {y : EY // y ∈ setup.Y} :=
    fun p => (setup.xPoint p.1.1, setup.yPoint p.1.1)
  have hqxy : Measurable qxy := by
    simpa [qxy, q] using (measurable_fst.comp hq)
  have hx :
      Measurable
        (fun p : (setup.Point × Ambient EX EY) × setup.SamplePoint =>
          setup.Gx (setup.xPoint p.1.1) (setup.yPoint p.1.1) p.2 -
            setup.gx (setup.xPoint p.1.1) (setup.yPoint p.1.1)) := by
    have hG :
        Measurable
          (fun p : (setup.Point × Ambient EX EY) × setup.SamplePoint =>
            setup.Gx (setup.xPoint p.1.1) (setup.yPoint p.1.1) p.2) := by
      simpa [q] using setup.hGx_joint_measurable.comp hq
    have hg :
        Measurable
          (fun p : (setup.Point × Ambient EX EY) × setup.SamplePoint =>
            setup.gx (setup.xPoint p.1.1) (setup.yPoint p.1.1)) := by
      simpa [qxy] using setup.gx_measurable.comp hqxy
    exact hG.sub hg
  have hy :
      Measurable
        (fun p : (setup.Point × Ambient EX EY) × setup.SamplePoint =>
          setup.Gy (setup.xPoint p.1.1) (setup.yPoint p.1.1) p.2 -
            setup.gy (setup.xPoint p.1.1) (setup.yPoint p.1.1)) := by
    have hG :
        Measurable
          (fun p : (setup.Point × Ambient EX EY) × setup.SamplePoint =>
            setup.Gy (setup.xPoint p.1.1) (setup.yPoint p.1.1) p.2) := by
      simpa [q] using setup.hGy_joint_measurable.comp hq
    have hg :
        Measurable
          (fun p : (setup.Point × Ambient EX EY) × setup.SamplePoint =>
            setup.gy (setup.xPoint p.1.1) (setup.yPoint p.1.1)) := by
      simpa [qxy] using setup.gy_measurable.comp hqxy
    exact hG.sub hg
  have hpair :
      Measurable
        (fun p : (setup.Point × Ambient EX EY) × setup.SamplePoint =>
          (setup.Gx (setup.xPoint p.1.1) (setup.yPoint p.1.1) p.2 -
              setup.gx (setup.xPoint p.1.1) (setup.yPoint p.1.1),
            -(setup.Gy (setup.xPoint p.1.1) (setup.yPoint p.1.1) p.2 -
              setup.gy (setup.xPoint p.1.1) (setup.yPoint p.1.1)))) :=
    hx.prod hy.neg
  have htoLp :
      Measurable
        (fun p : (setup.Point × Ambient EX EY) × setup.SamplePoint =>
          WithLp.toLp 2
            (setup.Gx (setup.xPoint p.1.1) (setup.yPoint p.1.1) p.2 -
                setup.gx (setup.xPoint p.1.1) (setup.yPoint p.1.1),
              -(setup.Gy (setup.xPoint p.1.1) (setup.yPoint p.1.1) p.2 -
                setup.gy (setup.xPoint p.1.1) (setup.yPoint p.1.1)))) :=
    (WithLp.prod_continuous_toLp 2 EX EY).measurable.comp hpair
  convert htoLp using 1
  ext p
  simp only [Setup.stochasticOracle, Setup.meanOracle]
  rw [sub_eq_add_neg]
  rw [← WithLp.toLp_neg, ← WithLp.toLp_add]
  simp [Setup.xPoint, Setup.yPoint, sub_eq_add_neg, Prod.mk_add_mk, add_comm]

private theorem canonicalDualNorm_supportSet_bddAbove_of_separating
    {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
    (p : Seminorm ℝ B) (hp : p.IsSeparating) (zeta : B) :
    BddAbove {r : ℝ | ∃ u : B, p u ≤ 1 ∧ r = |inner ℝ zeta u|} := by
  rcases Seminorm.exists_norm_le_mul_self_of_finiteDimensional_separating p hp with
    ⟨C, hC_nonneg, hC⟩
  refine SOptLib.canonicalDualNorm_supportSet_bddAbove p zeta ⟨C, ?_⟩
  intro u hu
  calc
    ‖u‖ ≤ C * p u := hC u
    _ ≤ C * 1 := mul_le_mul_of_nonneg_left hu hC_nonneg
    _ = C := by ring

private theorem canonicalDualNorm_unitBall_control_of_separating
    {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
    (p : Seminorm ℝ B) (hp : p.IsSeparating) :
    ∃ C : ℝ, ∀ u : B, p u ≤ 1 → ‖u‖ ≤ C := by
  rcases Seminorm.exists_norm_le_mul_self_of_finiteDimensional_separating p hp with
    ⟨C, hC_nonneg, hC⟩
  refine ⟨C, ?_⟩
  intro u hu
  calc
    ‖u‖ ≤ C * p u := hC u
    _ ≤ C * 1 := mul_le_mul_of_nonneg_left hu hC_nonneg
    _ = C := by ring

private theorem component_dual_norm_residual_sq_integrable_bound
    {Ω B : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (p : Seminorm ℝ B) (hp : p.IsSeparating)
    (Y : Ω → B) (target : B) (M : ℝ)
    (hY_int : Integrable Y μ)
    (htarget : target = ∫ ω, Y ω ∂μ)
    (hY_sq_int : Integrable (fun ω => (SOptLib.canonicalDualNorm p (Y ω)) ^ 2) μ)
    (hY_sq_bound : ∫ ω, (SOptLib.canonicalDualNorm p (Y ω)) ^ 2 ∂μ ≤ M ^ 2) :
    Integrable (fun ω => (SOptLib.canonicalDualNorm p (Y ω - target)) ^ 2) μ ∧
      ∫ ω, (SOptLib.canonicalDualNorm p (Y ω - target)) ^ 2 ∂μ ≤ 4 * M ^ 2 := by
  have hcontrol : ∃ C : ℝ, ∀ u : B, p u ≤ 1 → ‖u‖ ≤ C :=
    canonicalDualNorm_unitBall_control_of_separating p hp
  exact
    canonicalDualNorm_residual_sq_integrable_and_integral_le_of_mean_secondMoment
      (μ := μ) p hcontrol Y target M
      hY_int htarget hY_sq_int hY_sq_bound

private theorem product_dual_norm_sq_residual_components
    (z : setup.Point) (ξ : setup.SamplePoint) :
    (setup.productDualNorm (setup.stochasticOracle z ξ - setup.meanOracle z)) ^ 2 =
      2 * setup.DX ^ 2 *
          (SOptLib.canonicalDualNorm setup.normX
            (setup.Gx (setup.xPoint z) (setup.yPoint z) ξ -
              setup.gx (setup.xPoint z) (setup.yPoint z))) ^ 2 +
        2 * setup.DY ^ 2 *
          (SOptLib.canonicalDualNorm setup.normY
            (setup.Gy (setup.xPoint z) (setup.yPoint z) ξ -
              setup.gy (setup.xPoint z) (setup.yPoint z))) ^ 2 := by
  have hres :
      setup.stochasticOracle z ξ - setup.meanOracle z =
        WithLp.toLp 2
          (setup.Gx (setup.xPoint z) (setup.yPoint z) ξ -
              setup.gx (setup.xPoint z) (setup.yPoint z),
            -(setup.Gy (setup.xPoint z) (setup.yPoint z) ξ -
              setup.gy (setup.xPoint z) (setup.yPoint z))) := by
    rw [Setup.stochasticOracle_def, Setup.meanOracle_def]
    rw [sub_eq_add_neg, ← WithLp.toLp_neg, ← WithLp.toLp_add]
    simp [sub_eq_add_neg, Prod.mk_add_mk, add_comm, add_left_comm, add_assoc]
  rw [hres, Setup.productDualNorm_def]
  rw [Real.sq_sqrt (by
    simp only [WithLp.toLp_fst, WithLp.toLp_snd]
    positivity)]
  simp only [WithLp.toLp_fst, WithLp.toLp_snd]
  rw [canonicalDualNorm_neg]

/-- Fixed-query square-integrability of the product oracle residual in the
source product dual norm `‖Δ‖_*` used in Lemma 4.6. -/
theorem fixed_fiber_product_residual_norm_sq_integrable (z : setup.Point) :
    Integrable
      (fun ξ =>
        (setup.productDualNorm (setup.stochasticOracle z ξ - setup.meanOracle z)) ^ 2)
      setup.P := by
  letI : IsProbabilityMeasure setup.P := setup.hP_prob
  let XresSq : setup.SamplePoint → ℝ := fun ξ =>
    (SOptLib.canonicalDualNorm setup.normX
      (setup.Gx (setup.xPoint z) (setup.yPoint z) ξ -
        setup.gx (setup.xPoint z) (setup.yPoint z))) ^ 2
  let YresSq : setup.SamplePoint → ℝ := fun ξ =>
    (SOptLib.canonicalDualNorm setup.normY
      (setup.Gy (setup.xPoint z) (setup.yPoint z) ξ -
        setup.gy (setup.xPoint z) (setup.yPoint z))) ^ 2
  have hx :
      Integrable XresSq setup.P := by
    simpa [XresSq] using
      (component_dual_norm_residual_sq_integrable_bound
        (μ := setup.P) setup.normX setup.hnormX_separating
        (fun ξ => setup.Gx (setup.xPoint z) (setup.yPoint z) ξ)
        (setup.gx (setup.xPoint z) (setup.yPoint z)) setup.MX
        (setup.Gx_integrable (setup.xPoint z) (setup.yPoint z))
        (setup.gx_eq_expectation (setup.xPoint z) (setup.yPoint z))
        (setup.Gx_second_moment_integrable (setup.xPoint z) (setup.yPoint z))
        (setup.Gx_second_moment_bound (setup.xPoint z) (setup.yPoint z))).1
  have hy :
      Integrable YresSq setup.P := by
    simpa [YresSq] using
      (component_dual_norm_residual_sq_integrable_bound
        (μ := setup.P) setup.normY setup.hnormY_separating
        (fun ξ => setup.Gy (setup.xPoint z) (setup.yPoint z) ξ)
        (setup.gy (setup.xPoint z) (setup.yPoint z)) setup.MY
        (setup.Gy_integrable (setup.xPoint z) (setup.yPoint z))
        (setup.gy_eq_expectation (setup.xPoint z) (setup.yPoint z))
        (setup.Gy_second_moment_integrable (setup.xPoint z) (setup.yPoint z))
        (setup.Gy_second_moment_bound (setup.xPoint z) (setup.yPoint z))).1
  refine ((hx.const_mul (2 * setup.DX ^ 2)).add
    (hy.const_mul (2 * setup.DY ^ 2))).congr ?_
  exact Filter.Eventually.of_forall (fun ξ => by
    simpa [XresSq, YresSq] using
      (product_dual_norm_sq_residual_components (setup := setup) z ξ).symm)

/-- Uniform fixed-query product-dual-square residual bound from Lemma 4.6.

The paper proves the corresponding `Δ_t` second-moment estimate from
Assumption 7 and the product oracle moment bound before using the martingale
cross term. -/
theorem fixed_fiber_product_residual_norm_sq_bound (z : setup.Point) :
    ∫ ξ,
        (setup.productDualNorm (setup.stochasticOracle z ξ - setup.meanOracle z)) ^ 2
        ∂setup.P ≤
      4 * setup.M ^ 2 := by
  letI : IsProbabilityMeasure setup.P := setup.hP_prob
  let XresSq : setup.SamplePoint → ℝ := fun ξ =>
    (SOptLib.canonicalDualNorm setup.normX
      (setup.Gx (setup.xPoint z) (setup.yPoint z) ξ -
        setup.gx (setup.xPoint z) (setup.yPoint z))) ^ 2
  let YresSq : setup.SamplePoint → ℝ := fun ξ =>
    (SOptLib.canonicalDualNorm setup.normY
      (setup.Gy (setup.xPoint z) (setup.yPoint z) ξ -
        setup.gy (setup.xPoint z) (setup.yPoint z))) ^ 2
  have hx_pair :
      Integrable XresSq setup.P ∧
        ∫ ξ, XresSq ξ ∂setup.P ≤ 4 * setup.MX ^ 2 := by
    simpa [XresSq] using
      (component_dual_norm_residual_sq_integrable_bound
        (μ := setup.P) setup.normX setup.hnormX_separating
        (fun ξ => setup.Gx (setup.xPoint z) (setup.yPoint z) ξ)
        (setup.gx (setup.xPoint z) (setup.yPoint z)) setup.MX
        (setup.Gx_integrable (setup.xPoint z) (setup.yPoint z))
        (setup.gx_eq_expectation (setup.xPoint z) (setup.yPoint z))
        (setup.Gx_second_moment_integrable (setup.xPoint z) (setup.yPoint z))
        (setup.Gx_second_moment_bound (setup.xPoint z) (setup.yPoint z)))
  have hy_pair :
      Integrable YresSq setup.P ∧
        ∫ ξ, YresSq ξ ∂setup.P ≤ 4 * setup.MY ^ 2 := by
    simpa [YresSq] using
      (component_dual_norm_residual_sq_integrable_bound
        (μ := setup.P) setup.normY setup.hnormY_separating
        (fun ξ => setup.Gy (setup.xPoint z) (setup.yPoint z) ξ)
        (setup.gy (setup.xPoint z) (setup.yPoint z)) setup.MY
        (setup.Gy_integrable (setup.xPoint z) (setup.yPoint z))
        (setup.gy_eq_expectation (setup.xPoint z) (setup.yPoint z))
        (setup.Gy_second_moment_integrable (setup.xPoint z) (setup.yPoint z))
        (setup.Gy_second_moment_bound (setup.xPoint z) (setup.yPoint z)))
  rw [setup.M_sq_eq_M2, Setup.M2]
  calc
    ∫ ξ,
        (setup.productDualNorm (setup.stochasticOracle z ξ - setup.meanOracle z)) ^ 2
        ∂setup.P
        = ∫ ξ, 2 * setup.DX ^ 2 * XresSq ξ +
            2 * setup.DY ^ 2 * YresSq ξ ∂setup.P := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (fun ξ => by
            simpa [XresSq, YresSq] using
              product_dual_norm_sq_residual_components (setup := setup) z ξ)
    _ = 2 * setup.DX ^ 2 * ∫ ξ, XresSq ξ ∂setup.P +
          2 * setup.DY ^ 2 * ∫ ξ, YresSq ξ ∂setup.P := by
          rw [MeasureTheory.integral_add (hx_pair.1.const_mul (2 * setup.DX ^ 2))
            (hy_pair.1.const_mul (2 * setup.DY ^ 2))]
          rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    _ ≤ 2 * setup.DX ^ 2 * (4 * setup.MX ^ 2) +
          2 * setup.DY ^ 2 * (4 * setup.MY ^ 2) := by
          have hcx : 0 ≤ 2 * setup.DX ^ 2 := by positivity
          have hcy : 0 ≤ 2 * setup.DY ^ 2 := by positivity
          exact add_le_add (mul_le_mul_of_nonneg_left hx_pair.2 hcx)
            (mul_le_mul_of_nonneg_left hy_pair.2 hcy)
    _ = 4 * (2 * setup.DX ^ 2 * setup.MX ^ 2 +
          2 * setup.DY ^ 2 * setup.MY ^ 2) := by ring

/-- Auxiliary `v`-sequence used in (4.3.12), initialized at `z₁` and updated with
`ζ_t = -γ_t Δ_t`. -/
noncomputable def auxiliaryDeltaStep (n : ℕ) (v : setup.InteriorPoint)
    (ω : setup.SamplePath) : setup.InteriorPoint :=
  let t := SOptLib.natSuccPositiveTime n
  setup.mirrorStep v (-(setup.oracleNoise t ω)) (setup.gamma t)

/-- Generated auxiliary core process `v_t ∈ Zᵒ` from Lemma 4.6. -/
noncomputable def auxiliaryCoreProcess : ℕ → setup.SamplePath → setup.InteriorPoint :=
  SOptLib.recursive_process_from_random_initial (fun _ω => (Classical.choose setup.initialPoint_exists))
    setup.auxiliaryDeltaStep

/-- Carrier-valued auxiliary process. -/
noncomputable def auxiliaryProcess : ℕ → setup.SamplePath → setup.Point :=
  fun n ω => setup.interiorPointToPoint (setup.auxiliaryCoreProcess n ω)

/-- Paper-time auxiliary iterate view. -/
noncomputable def auxiliaryIterate (t : Time) : setup.SamplePath → setup.Point :=
  fun ω => setup.auxiliaryProcess (t.1 - 1) ω

@[simp]
theorem auxiliaryCoreProcess_zero :
    setup.auxiliaryCoreProcess 0 = fun _ω : setup.SamplePath => (Classical.choose setup.initialPoint_exists) := by
  rfl

@[simp]
theorem auxiliaryCoreProcess_succ (n : ℕ) (ω : setup.SamplePath) :
    setup.auxiliaryCoreProcess (n + 1) ω =
      setup.mirrorStep (setup.auxiliaryCoreProcess n ω)
        (-(setup.oracleNoise (SOptLib.natSuccPositiveTime n) ω))
        (setup.gamma (SOptLib.natSuccPositiveTime n)) := by
  rfl

@[simp]
theorem auxiliaryProcess_zero :
    setup.auxiliaryProcess 0 = fun _ω : setup.SamplePath => setup.initialPoint := by
  rfl

theorem auxiliaryProcess_succ (n : ℕ) (ω : setup.SamplePath) :
    setup.auxiliaryProcess (n + 1) ω =
      setup.interiorPointToPoint
        (setup.mirrorStep (setup.auxiliaryCoreProcess n ω)
          (-(setup.oracleNoise (SOptLib.natSuccPositiveTime n) ω))
          (setup.gamma (SOptLib.natSuccPositiveTime n))) := by
  rfl

/-- Random query and direction used in the martingale term of Lemma 4.6.

The first component is the past iterate `z_t`; the second is the
query-dependent direction `γ_t (z_t - v_t)`.  This is the source proof line
"`z_t` and `v_t` are deterministic functions of `ξ_[t-1]`" packaged in the
shape expected by the random-query oracle-residual API. -/
noncomputable def crossTermQuery (t : Time) (ω : setup.SamplePath) :
    setup.Point × Ambient EX EY :=
  (setup.iterate t ω,
    setup.gamma t • ((setup.iterate t ω).1 - (setup.auxiliaryIterate t ω).1))

@[simp]
theorem crossTermQuery_fst (t : Time) (ω : setup.SamplePath) :
    (setup.crossTermQuery t ω).1 = setup.iterate t ω := by
  rfl

@[simp]
theorem crossTermQuery_snd (t : Time) (ω : setup.SamplePath) :
    (setup.crossTermQuery t ω).2 =
      setup.gamma t • ((setup.iterate t ω).1 - (setup.auxiliaryIterate t ω).1) := by
  rfl

/-- Product-law a.e.-strong measurability of the residual kernel at the
cross-term query law. -/
theorem oracle_residual_product_aestronglyMeasurable (t : Time) :
    AEStronglyMeasurable
      (fun p : (setup.Point × Ambient EX EY) × setup.SamplePoint =>
        setup.stochasticOracle p.1.1 p.2 - setup.meanOracle p.1.1)
      ((Measure.map (setup.crossTermQuery t) setup.pathMeasure).prod setup.P) := by
  exact (oracle_residual_product_measurable (setup := setup)).aestronglyMeasurable

/-- Prox-selector measurability bridge for the mixed-domain update
`Zᵒ × E → Zᵒ`.

The current mirror step is an argmin selected from the paper's compact
mirror-prox subproblem.  Measurability of this selected update is the missing
process-interface fact needed to derive strict-past adaptedness of both
`iterate` and `auxiliaryIterate`; it should be proved from compactness,
continuity, and uniqueness of the strongly convex prox objective, not assumed in
the theorem head. -/
theorem mirrorStep_aemeasurable_bridge
    (γ : ℝ) :
    Measurable
      (fun p : setup.InteriorPoint × Ambient EX EY =>
        setup.mirrorStep p.1 p.2 γ) := by
  have hpoint :
      Measurable
        (fun p : setup.InteriorPoint × Ambient EX EY =>
          setup.mirrorStepPoint p.1 p.2 γ) :=
    (setup.mirrorStepPoint_continuous γ).measurable
  have hambient :
      Measurable
        (fun p : setup.InteriorPoint × Ambient EX EY =>
          (setup.mirrorStepPoint p.1 p.2 γ).1) :=
    measurable_subtype_coe.comp hpoint
  change Measurable
    (fun p : setup.InteriorPoint × Ambient EX EY =>
      (⟨(setup.mirrorStepPoint p.1 p.2 γ).1,
          setup.mirrorStepPoint_mem_core p.1 p.2 γ⟩ : setup.InteriorPoint))
  exact hambient.subtype_mk

/-- One-step update kernel for the generated stochastic mirror descent process,
with state in `Zᵒ` and driver the current sample. -/
noncomputable def stochasticMirrorUpdate (γ : ℝ)
    (p : setup.InteriorPoint × setup.SamplePoint) : setup.InteriorPoint :=
  setup.mirrorStep p.1
    (setup.stochasticOracle (setup.interiorPointToPoint p.1) p.2) γ

/-- Measurability of the generated stochastic mirror-descent update kernel. -/
theorem stochasticMirrorUpdate_measurable (γ : ℝ) :
    Measurable (setup.stochasticMirrorUpdate γ) := by
  have hcarrier :
      Measurable (fun p : setup.InteriorPoint × setup.SamplePoint =>
        setup.interiorPointToPoint p.1) :=
    setup.interiorPointToPoint_measurable.comp measurable_fst
  have horacle :
      Measurable (fun p : setup.InteriorPoint × setup.SamplePoint =>
        setup.stochasticOracle (setup.interiorPointToPoint p.1) p.2) :=
    setup.stochasticOracle_measurable.comp (hcarrier.prodMk measurable_snd)
  simpa [Setup.stochasticMirrorUpdate] using
    (setup.mirrorStep_aemeasurable_bridge γ).comp (measurable_fst.prodMk horacle)

/-- One-step update kernel for the auxiliary `v_t` process, with driver the
current oracle residual. -/
noncomputable def auxiliaryMirrorUpdate (γ : ℝ)
    (p : setup.InteriorPoint × Ambient EX EY) : setup.InteriorPoint :=
  setup.mirrorStep p.1 (-p.2) γ

/-- Measurability of the auxiliary mirror-update kernel. -/
theorem auxiliaryMirrorUpdate_measurable (γ : ℝ) :
    Measurable (setup.auxiliaryMirrorUpdate γ) := by
  have hdriver : Measurable (fun p : setup.InteriorPoint × Ambient EX EY => -p.2) :=
    measurable_snd.neg
  simpa [Setup.auxiliaryMirrorUpdate] using
    (setup.mirrorStep_aemeasurable_bridge γ).comp (measurable_fst.prodMk hdriver)

/-- Strict-past measurability of the paper iterate `z_t`.

This is the process half of the source statement that `z_t` is a deterministic
function of `ξ_[t-1]`.  The intended proof instantiates
`SOptLib.recursive_process_measurable_wrt_sample_prefix` with
`iterateCoreProcess`, using joint oracle measurability and
`mirrorStep_aemeasurable_bridge` as the measurable update kernel. -/
theorem iterate_strictPast_measurable (t : Time) :
    Measurable[
      (⨆ j < t.1 - 1,
        MeasurableSpace.comap (fun ω : setup.SamplePath => ω j)
          (by infer_instance : MeasurableSpace setup.SamplePoint))]
      (setup.iterate t) := by
  let past : ℕ → MeasurableSpace setup.SamplePath :=
    fun n => ⨆ j < n,
      MeasurableSpace.comap (fun ω : setup.SamplePath => ω j)
        (by infer_instance : MeasurableSpace setup.SamplePoint)
  let driver : ℕ → setup.SamplePath → setup.SamplePoint :=
    fun j ω => ω j
  let step : ℕ → setup.InteriorPoint → setup.SamplePoint → setup.InteriorPoint :=
    fun j z ξ =>
      setup.mirrorStep z (setup.stochasticOracle (setup.interiorPointToPoint z) ξ)
        (setup.gamma (SOptLib.natSuccPositiveTime j))
  have hinit : Measurable[past (t.1 - 1)] (setup.iterateCoreProcess 0) := by
    simpa [Setup.iterateCoreProcess_zero] using
      (measurable_const :
        Measurable[past (t.1 - 1)]
          (fun _ω : setup.SamplePath => (Classical.choose setup.initialPoint_exists)))
  have hdriver :
      ∀ j, j + 1 ≤ t.1 - 1 →
        Measurable[past (t.1 - 1)] (driver j) := by
    intro j hj
    have hjlt : j < t.1 - 1 := Nat.lt_of_succ_le hj
    have hξ : ∀ n, Measurable (fun ω : setup.SamplePath => ω n) := by
      intro n
      exact (measurable_pi_apply n :
        Measurable (fun ω : setup.SamplePath => ω n))
    simpa [past, driver, SOptLib.filtration] using
      (SOptLib.measurable_sample_of_lt_prefixFiltration
        (ξ := fun n (ω : setup.SamplePath) => ω n) hξ hjlt)
  have hstep :
      ∀ j, j + 1 ≤ t.1 - 1 →
        Measurable (fun p : setup.InteriorPoint × setup.SamplePoint =>
          step j p.1 p.2) := by
    intro j _hj
    simpa [step] using
      setup.stochasticMirrorUpdate_measurable (setup.gamma (SOptLib.natSuccPositiveTime j))
  have hupdate :
      ∀ j, j + 1 ≤ t.1 - 1 →
        setup.iterateCoreProcess (j + 1) =
          fun ω => step j (setup.iterateCoreProcess j ω) (driver j ω) := by
    intro j _hj
    funext ω
    simp [step, driver, Setup.iterateProcess,
      Setup.sampleAt, SOptLib.natSuccPositiveTime]
  have hcore :
      Measurable[past (t.1 - 1)] (setup.iterateCoreProcess (t.1 - 1)) :=
    SOptLib.recursiveProcess_measurable_wrt_strictPast
      (past := past)
      (process := setup.iterateCoreProcess)
      (driver := driver)
      (step := step)
      (k := t.1 - 1)
      (N := t.1 - 1)
      hinit (fun j hj _hprocess => hdriver j hj) hstep hupdate (t.1 - 1) le_rfl
  have hpoint : Measurable[past (t.1 - 1)] (setup.iterateProcess (t.1 - 1)) :=
    setup.interiorPointToPoint_measurable.comp hcore
  simpa [past, Setup.iterate, Setup.iterateProcess] using hpoint

/-- Strict-past measurability of the auxiliary process `v_t`.

This is the auxiliary half of the source statement that `v_t` is a deterministic
function of `ξ_[t-1]`.  The intended proof is another
`SOptLib.recursive_process_measurable_wrt_sample_prefix` induction, with the
driver at step `j` built from the already strict-past measurable `z_{j+1}` and
the coordinate sample `ξ_{j+1}`. -/
theorem auxiliaryIterate_strictPast_measurable (t : Time) :
    Measurable[
      (⨆ j < t.1 - 1,
        MeasurableSpace.comap (fun ω : setup.SamplePath => ω j)
          (by infer_instance : MeasurableSpace setup.SamplePoint))]
      (setup.auxiliaryIterate t) := by
  let past : ℕ → MeasurableSpace setup.SamplePath :=
    fun n => ⨆ j < n,
      MeasurableSpace.comap (fun ω : setup.SamplePath => ω j)
        (by infer_instance : MeasurableSpace setup.SamplePoint)
  let sample : ℕ → setup.SamplePath → setup.SamplePoint :=
    fun j ω => ω j
  let current : ℕ → setup.SamplePath → setup.Point :=
    fun j => setup.iterate (SOptLib.natSuccPositiveTime j)
  let step : ℕ → setup.InteriorPoint → Ambient EX EY → setup.InteriorPoint :=
    fun j v Δ =>
      setup.mirrorStep v (-Δ) (setup.gamma (SOptLib.natSuccPositiveTime j))
  have hpast_mono : ∀ {a b : ℕ}, a ≤ b → past a ≤ past b := by
    intro a b hab
    dsimp [past]
    exact iSup₂_mono' fun j hj => ⟨j, lt_of_lt_of_le hj hab, le_rfl⟩
  have hinit : Measurable[past (t.1 - 1)] (setup.auxiliaryCoreProcess 0) := by
    simpa [Setup.auxiliaryCoreProcess_zero] using
      (measurable_const :
        Measurable[past (t.1 - 1)]
          (fun _ω : setup.SamplePath => (Classical.choose setup.initialPoint_exists)))
  have hsample :
      ∀ j, j + 1 ≤ t.1 - 1 →
        Measurable[past (t.1 - 1)] (sample j) := by
    intro j hj
    have hξ : ∀ n, Measurable (fun ω : setup.SamplePath => ω n) := by
      intro n
      exact (measurable_pi_apply n :
        Measurable (fun ω : setup.SamplePath => ω n))
    simpa [past, sample, SOptLib.filtration] using
      (SOptLib.measurable_sample_of_lt_prefixFiltration
        (ξ := fun n (ω : setup.SamplePath) => ω n) hξ (Nat.lt_of_succ_le hj))
  have hcurrent :
      ∀ j, j + 1 ≤ t.1 - 1 →
        Measurable[past j] (current j) := by
    intro j _hj
    simpa [past, current, SOptLib.natSuccPositiveTime] using
      setup.iterate_strictPast_measurable (SOptLib.natSuccPositiveTime j)
  have hstep :
      ∀ j, j + 1 ≤ t.1 - 1 →
        Measurable (fun p : setup.InteriorPoint × Ambient EX EY =>
          step j p.1 p.2) := by
    intro j _hj
    simpa [step, Setup.auxiliaryMirrorUpdate] using
      setup.auxiliaryMirrorUpdate_measurable (setup.gamma (SOptLib.natSuccPositiveTime j))
  have hupdate :
      ∀ j, j + 1 ≤ t.1 - 1 →
        setup.auxiliaryCoreProcess (j + 1) =
          fun ω =>
            step j (setup.auxiliaryCoreProcess j ω)
              (setup.stochasticOracle (current j ω) (sample j ω) -
                setup.meanOracle (current j ω)) := by
    intro j _hj
    funext ω
    simp [step, current, sample, Setup.oracleNoise, Setup.sampleAt,
      SOptLib.natSuccPositiveTime]
  simpa [past, Setup.auxiliaryIterate, Setup.auxiliaryProcess] using
    auxiliaryResidualProcess_measurable_wrt_strictPast
      (past := past)
      (sample := sample)
      (current := current)
      (aux := setup.auxiliaryCoreProcess)
      (project := setup.interiorPointToPoint)
      (G := setup.stochasticOracle)
      (target := setup.meanOracle)
      (step := step)
      (N := t.1 - 1)
      hpast_mono hinit hsample hcurrent setup.stochasticOracle_measurable
      setup.meanOracle_measurable hstep hupdate setup.interiorPointToPoint_measurable

/-- Source bridge for the paper claim that `z_t` and `v_t` are deterministic
functions of the strict sample past.

The intended proof uses `mirrorStep_aemeasurable_bridge`, the recursive-process
prefix measurability API, and iid prefix/future independence.  It is kept as a
separate bridge so downstream martingale cancellation consumes an adapted
random query rather than taking adaptedness as a theorem-local hypothesis. -/
theorem crossTermQuery_strictPast_source_bridge (t : Time) :
    Measurable[
      (⨆ j < t.1 - 1,
        MeasurableSpace.comap (fun ω : setup.SamplePath => ω j)
          (by infer_instance : MeasurableSpace setup.SamplePoint))]
      (setup.crossTermQuery t) := by
  let mpast : MeasurableSpace setup.SamplePath :=
    (⨆ j < t.1 - 1,
      MeasurableSpace.comap (fun ω : setup.SamplePath => ω j)
        (by infer_instance : MeasurableSpace setup.SamplePoint))
  have hiter : Measurable[mpast] (setup.iterate t) :=
    setup.iterate_strictPast_measurable t
  have haux : Measurable[mpast] (setup.auxiliaryIterate t) :=
    setup.auxiliaryIterate_strictPast_measurable t
  have hiter_val : Measurable[mpast] (fun ω => (setup.iterate t ω).1) :=
    measurable_subtype_coe.comp hiter
  have haux_val : Measurable[mpast] (fun ω => (setup.auxiliaryIterate t ω).1) :=
    measurable_subtype_coe.comp haux
  have hdir : Measurable[mpast]
      (fun ω => setup.gamma t • ((setup.iterate t ω).1 -
        (setup.auxiliaryIterate t ω).1)) := by
    exact (continuous_const_smul (setup.gamma t)).measurable.comp
      (hiter_val.sub haux_val)
  simpa [mpast, Setup.crossTermQuery] using hiter.prod hdir

/-- Ambient a.e. measurability of the Lemma 4.6 cross-term query. -/
theorem crossTermQuery_measurable (t : Time) :
    Measurable (setup.crossTermQuery t) := by
  let mpast : MeasurableSpace setup.SamplePath :=
    (⨆ j < t.1 - 1,
      MeasurableSpace.comap (fun ω : setup.SamplePath => ω j)
        (by infer_instance : MeasurableSpace setup.SamplePoint))
  have hle : mpast ≤ (MeasurableSpace.pi : MeasurableSpace setup.SamplePath) := by
    dsimp [mpast]
    refine iSup_le ?_
    intro j
    refine iSup_le ?_
    intro _hj
    have hcoord :
        @Measurable setup.SamplePath setup.SamplePoint
          (MeasurableSpace.pi : MeasurableSpace setup.SamplePath)
          (by infer_instance : MeasurableSpace setup.SamplePoint)
          (fun ω : setup.SamplePath => ω j) := by
      exact
        (@measurable_pi_apply ℕ (fun _ : ℕ => setup.SamplePoint)
          (fun _ : ℕ => (by infer_instance : MeasurableSpace setup.SamplePoint)) j)
    exact hcoord.comap_le
  exact
    @Measurable.of_measurableSpace_le
      setup.SamplePath (setup.Point × Ambient EX EY)
      (MeasurableSpace.pi : MeasurableSpace setup.SamplePath)
      (by infer_instance : MeasurableSpace (setup.Point × Ambient EX EY))
      mpast (setup.crossTermQuery t)
      (setup.crossTermQuery_strictPast_source_bridge t) hle

/-- Ambient a.e. measurability of the Lemma 4.6 cross-term query. -/
theorem crossTermQuery_aemeasurable (t : Time) :
    AEMeasurable (setup.crossTermQuery t) setup.pathMeasure := by
  exact (setup.crossTermQuery_measurable t).aemeasurable

/-- The cross-term query is independent of the fresh sample coordinate `ξ_t`.

This is the executable iid-stream form of the source proof line that `z_t` and
`v_t` are deterministic functions of the strict past `ξ_[t-1]`. -/
theorem crossTermQuery_indep_sampleAt (t : Time) :
    IndepFun (setup.crossTermQuery t) (setup.sampleAt t) setup.pathMeasure := by
  letI : IsProbabilityMeasure setup.P := setup.hP_prob
  simpa [Setup.pathMeasure, Setup.sampleAt] using
    (ProbabilityTheory.iIndepFun.indepFun_prefixMeasurable_future
      (ξ := fun n (ω : setup.SamplePath) => ω n)
      (hξ_measurable := fun n => (measurable_pi_apply n :
        Measurable (fun ω : setup.SamplePath => ω n)))
      (hξ_iIndep := SOptLib.iidStreamLaw_iIndepFun_eval setup.P)
      (wt := setup.crossTermQuery t)
      (n := t.1 - 1)
      (i := t.1 - 1)
      (setup.crossTermQuery_strictPast_source_bridge t)
      le_rfl)

/-- L2 side condition for the random direction `γ_t (z_t - v_t)` in the
cross-term query. -/
theorem crossTermQuery_direction_sq_integrable (t : Time) :
    Integrable (fun ω => ‖(setup.crossTermQuery t ω).2‖ ^ 2) setup.pathMeasure := by
  letI : IsProbabilityMeasure setup.pathMeasure := setup.pathMeasure_isProbabilityMeasure
  have hf_meas : AEStronglyMeasurable
      (fun ω => (setup.crossTermQuery t ω).2) setup.pathMeasure := by
    exact (measurable_snd.comp (setup.crossTermQuery_measurable t)).aestronglyMeasurable
  letI : CompactSpace setup.Point := isCompact_univ_iff.mp setup.point_univ_isCompact
  have hcompact_pair : IsCompact (Set.univ : Set (setup.Point × setup.Point)) := by
    simpa using (isCompact_univ : IsCompact (Set.univ : Set (setup.Point × setup.Point)))
  have hcont : ContinuousOn
      (fun p : setup.Point × setup.Point => ‖p.1.1 - p.2.1‖) Set.univ := by
    have hfst : Continuous (fun p : setup.Point × setup.Point => (p.1 : Ambient EX EY)) := by
      exact continuous_subtype_val.comp continuous_fst
    have hsnd : Continuous (fun p : setup.Point × setup.Point => (p.2 : Ambient EX EY)) := by
      exact continuous_subtype_val.comp continuous_snd
    exact (hfst.sub hsnd).norm.continuousOn
  rcases exists_nonneg_norm_bound_of_isCompact_of_continuousOn
      (fun p : setup.Point × setup.Point => ‖p.1.1 - p.2.1‖)
      hcompact_pair hcont with ⟨D, _hD_nonneg, hD_bound⟩
  have hdiam : ∀ {a b : Ambient EX EY},
      a ∈ setup.jointCarrier → b ∈ setup.jointCarrier → ‖a - b‖ ≤ D := by
    intro a b ha hb
    have h := hD_bound (⟨a, ha⟩, ⟨b, hb⟩)
      (by simp : (⟨a, ha⟩, ⟨b, hb⟩) ∈ (Set.univ : Set (setup.Point × setup.Point)))
    simpa [Real.norm_of_nonneg (norm_nonneg (a - b))] using h
  have hbounded :
      ∀ᵐ ω ∂setup.pathMeasure, ‖(setup.crossTermQuery t ω).2‖ ≤ ‖setup.gamma t‖ * D := by
    refine Filter.Eventually.of_forall ?_
    intro ω
    have hdiff :
        ‖(setup.iterate t ω).1 - (setup.auxiliaryIterate t ω).1‖ ≤ D :=
      hdiam (setup.iterate t ω).2 (setup.auxiliaryIterate t ω).2
    simpa [Setup.crossTermQuery, norm_smul] using
      (mul_le_mul_of_nonneg_left hdiff (norm_nonneg (setup.gamma t)))
  exact (SOptLib.integrable_sq_norm_of_ae_bound hf_meas hbounded).1

private theorem productDualNorm_continuous :
    Continuous (fun zeta : Ambient EX EY => setup.productDualNorm zeta) := by
  have hcontrolX := canonicalDualNorm_unitBall_control_of_separating
    setup.normX setup.hnormX_separating
  have hcontrolY := canonicalDualNorm_unitBall_control_of_separating
    setup.normY setup.hnormY_separating
  have hdualX :
      Continuous (fun zeta : EX =>
        SOptLib.canonicalDualNorm setup.normX zeta) :=
    SOptLib.canonicalDualNorm_continuous setup.normX hcontrolX.choose_spec
  have hdualY :
      Continuous (fun zeta : EY =>
        SOptLib.canonicalDualNorm setup.normY zeta) :=
    SOptLib.canonicalDualNorm_continuous setup.normY hcontrolY.choose_spec
  have hx :
      Continuous (fun zeta : Ambient EX EY =>
        (SOptLib.canonicalDualNorm setup.normX zeta.fst) ^ 2) :=
    (hdualX.comp (WithLp.continuous_fst 2 EX EY)).pow 2
  have hy :
      Continuous (fun zeta : Ambient EX EY =>
        (SOptLib.canonicalDualNorm setup.normY zeta.snd) ^ 2) :=
    (hdualY.comp (WithLp.continuous_snd 2 EX EY)).pow 2
  have hrad :
      Continuous (fun zeta : Ambient EX EY =>
        2 * setup.DX ^ 2 *
            (SOptLib.canonicalDualNorm setup.normX zeta.fst) ^ 2 +
          2 * setup.DY ^ 2 *
            (SOptLib.canonicalDualNorm setup.normY zeta.snd) ^ 2) :=
    (continuous_const.mul hx).add (continuous_const.mul hy)
  simpa [Setup.productDualNorm_def] using Real.continuous_sqrt.comp hrad

private theorem seminorm_continuous_of_finiteDimensional
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
    (p : Seminorm ℝ B) :
    Continuous (fun x : B => p x) := by
  exact Seminorm.continuous_of_finiteDimensional p

private theorem productNorm_continuous :
    Continuous (fun z : Ambient EX EY => setup.productNorm z) := by
  have hx :
      Continuous (fun z : Ambient EX EY => (setup.normX z.fst) ^ 2) :=
    ((seminorm_continuous_of_finiteDimensional setup.normX).comp
      (WithLp.continuous_fst 2 EX EY)).pow 2
  have hy :
      Continuous (fun z : Ambient EX EY => (setup.normY z.snd) ^ 2) :=
    ((seminorm_continuous_of_finiteDimensional setup.normY).comp
      (WithLp.continuous_snd 2 EX EY)).pow 2
  have hrad :
      Continuous (fun z : Ambient EX EY =>
        (setup.normX z.fst) ^ 2 / (2 * setup.DX ^ 2) +
          (setup.normY z.snd) ^ 2 / (2 * setup.DY ^ 2)) :=
    (hx.div_const (2 * setup.DX ^ 2)).add (hy.div_const (2 * setup.DY ^ 2))
  simpa [Setup.productNorm_def] using Real.continuous_sqrt.comp hrad

/-- Random-query product-dual-square integrability for the oracle residual
`Δ_t = G(z_t,ξ_t)-g(z_t)`.

This is the fixed-fiber `E‖Δ‖_*^2` estimate transported through the strict-past
query and fresh iid sample used in Lemma 4.6. -/
theorem oracleNoise_productDualNorm_sq_integrable (t : Time) :
    Integrable
      (fun ω => (setup.productDualNorm (setup.oracleNoise t ω)) ^ 2)
      setup.pathMeasure := by
  letI : IsProbabilityMeasure setup.pathMeasure := setup.pathMeasure_isProbabilityMeasure
  have hres_sq_prod :
      AEStronglyMeasurable
        (fun p : (setup.Point × Ambient EX EY) × setup.SamplePoint =>
          setup.productDualNorm
            (setup.stochasticOracle p.1.1 p.2 - setup.meanOracle p.1.1) ^ 2)
        ((Measure.map (setup.crossTermQuery t) setup.pathMeasure).prod setup.P) := by
    have hres := oracle_residual_product_aestronglyMeasurable (setup := setup) t
    have hdual :
        AEStronglyMeasurable
          (fun p : (setup.Point × Ambient EX EY) × setup.SamplePoint =>
            setup.productDualNorm
              (setup.stochasticOracle p.1.1 p.2 - setup.meanOracle p.1.1))
          ((Measure.map (setup.crossTermQuery t) setup.pathMeasure).prod setup.P) :=
      (productDualNorm_continuous (setup := setup)).comp_aestronglyMeasurable hres
    simpa [pow_two] using hdual.pow 2
  have htransfer :=
    randomQuery_oracleResidual_gauge_sq_integrable_and_integral_le_of_indep_fixed
      (P := setup.pathMeasure)
      (query := setup.crossTermQuery t) (sample := setup.sampleAt t)
      (residual := fun q ξ => setup.stochasticOracle q.1 ξ - setup.meanOracle q.1)
      (gauge := setup.productDualNorm) (C := 4 * setup.M ^ 2)
      (by simpa [setup.sampleAt_law t] using hres_sq_prod)
      (crossTermQuery_aemeasurable (setup := setup) t)
      (setup.sampleAt_aemeasurable t)
      (crossTermQuery_indep_sampleAt (setup := setup) t)
      (fun q => by
        constructor
        · simpa [setup.sampleAt_law t] using
            setup.fixed_fiber_product_residual_norm_sq_integrable q.1
        · simpa [setup.sampleAt_law t] using setup.fixed_fiber_product_residual_norm_sq_bound q.1)
  simpa [Setup.oracleNoise] using htransfer.1

theorem stochasticOracle_productDualNorm_sq_integrable_and_integral_bound (t : Time) :
    Integrable
        (fun ω =>
          (setup.productDualNorm
            (setup.stochasticOracle (setup.iterate t ω) (setup.sampleAt t ω))) ^ 2)
        setup.pathMeasure ∧
      ∫ ω,
          (setup.productDualNorm
            (setup.stochasticOracle (setup.iterate t ω) (setup.sampleAt t ω))) ^ 2
          ∂setup.pathMeasure ≤ setup.M ^ 2 := by
  letI : IsProbabilityMeasure setup.pathMeasure := setup.pathMeasure_isProbabilityMeasure
  have htransfer :=
    randomQuery_oracle_gauge_sq_integrable_and_integral_le_of_indep_fixed
      (P := setup.pathMeasure) (ν := setup.P)
      (query := setup.crossTermQuery t) (sample := setup.sampleAt t)
      (G := fun q ξ => setup.stochasticOracle q.1 ξ)
      (gauge := setup.productDualNorm) (C := setup.M ^ 2)
      (by
        have horacle_meas :
            Measurable
              (fun p : (setup.Point × Ambient EX EY) × setup.SamplePoint =>
                setup.stochasticOracle p.1.1 p.2) :=
          setup.stochasticOracle_measurable.comp
            ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
        have hdual :
            AEStronglyMeasurable
              (fun p : (setup.Point × Ambient EX EY) × setup.SamplePoint =>
                setup.productDualNorm (setup.stochasticOracle p.1.1 p.2))
              ((Measure.map (setup.crossTermQuery t) setup.pathMeasure).prod setup.P) :=
          (productDualNorm_continuous (setup := setup)).comp_aestronglyMeasurable
            horacle_meas.aestronglyMeasurable
        simpa [pow_two] using hdual.pow 2)
      (crossTermQuery_aemeasurable (setup := setup) t)
      (setup.sampleAt_aemeasurable t)
      (crossTermQuery_indep_sampleAt (setup := setup) t)
      (setup.sampleAt_law t)
      (fun q => by
        constructor
        · simpa using setup.product_oracle_second_moment_integrable q.1
        · simpa using setup.product_oracle_second_moment_bound q.1)
  simpa [Setup.crossTermQuery] using htransfer

theorem oracleNoise_productDualNorm_sq_integral_bound (t : Time) :
    ∫ ω, (setup.productDualNorm (setup.oracleNoise t ω)) ^ 2 ∂setup.pathMeasure ≤
      4 * setup.M ^ 2 := by
  letI : IsProbabilityMeasure setup.pathMeasure := setup.pathMeasure_isProbabilityMeasure
  have hres_sq_prod :
      AEStronglyMeasurable
        (fun p : (setup.Point × Ambient EX EY) × setup.SamplePoint =>
          setup.productDualNorm
            (setup.stochasticOracle p.1.1 p.2 - setup.meanOracle p.1.1) ^ 2)
        ((Measure.map (setup.crossTermQuery t) setup.pathMeasure).prod setup.P) := by
    have hres := oracle_residual_product_aestronglyMeasurable (setup := setup) t
    have hdual :
        AEStronglyMeasurable
          (fun p : (setup.Point × Ambient EX EY) × setup.SamplePoint =>
            setup.productDualNorm
              (setup.stochasticOracle p.1.1 p.2 - setup.meanOracle p.1.1))
          ((Measure.map (setup.crossTermQuery t) setup.pathMeasure).prod setup.P) :=
      (productDualNorm_continuous (setup := setup)).comp_aestronglyMeasurable hres
    simpa [pow_two] using hdual.pow 2
  have htransfer :=
    randomQuery_oracleResidual_gauge_sq_integrable_and_integral_le_of_indep_fixed
      (P := setup.pathMeasure)
      (query := setup.crossTermQuery t) (sample := setup.sampleAt t)
      (residual := fun q ξ => setup.stochasticOracle q.1 ξ - setup.meanOracle q.1)
      (gauge := setup.productDualNorm) (C := 4 * setup.M ^ 2)
      (by simpa [setup.sampleAt_law t] using hres_sq_prod)
      (crossTermQuery_aemeasurable (setup := setup) t)
      (setup.sampleAt_aemeasurable t)
      (crossTermQuery_indep_sampleAt (setup := setup) t)
      (fun q => by
        constructor
        · simpa [setup.sampleAt_law t] using
            setup.fixed_fiber_product_residual_norm_sq_integrable q.1
        · simpa [setup.sampleAt_law t] using setup.fixed_fiber_product_residual_norm_sq_bound q.1)
  simpa [Setup.oracleNoise] using htransfer.2

private theorem weighted_two_term_mul_le_sqrt
    {a b c d α β : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hα : 0 < α) (hβ : 0 < β) :
    a * c + b * d ≤
      Real.sqrt (α * a ^ 2 + β * b ^ 2) *
        Real.sqrt (c ^ 2 / α + d ^ 2 / β) :=
by
  exact
    SOptLib.mul_add_mul_le_sqrt_weighted_sq_mul_sqrt_inv_weighted_sq
      (a := a) (b := b) (c := c) (d := d) (alpha := α) (beta := β)
      hα hβ

private theorem abs_inner_le_productDualNorm_mul_productNorm
    (zeta d : Ambient EX EY) :
    |⟪zeta, d⟫_ℝ| ≤ setup.productDualNorm zeta * setup.productNorm d := by
  let ux : ℝ := SOptLib.canonicalDualNorm setup.normX zeta.fst
  let uy : ℝ := SOptLib.canonicalDualNorm setup.normY zeta.snd
  let px : ℝ := setup.normX d.fst
  let py : ℝ := setup.normY d.snd
  have hx_support :
      |⟪zeta.fst, d.fst⟫_ℝ| ≤ ux * px := by
    simpa [ux, px] using
      (SOptLib.abs_inner_le_canonicalDualNorm_mul
        setup.normX setup.hnormX_separating
        (zeta := zeta.fst) (d := d.fst)
        (canonicalDualNorm_supportSet_bddAbove_of_separating
          setup.normX setup.hnormX_separating zeta.fst))
  have hy_support :
      |⟪zeta.snd, d.snd⟫_ℝ| ≤ uy * py := by
    simpa [uy, py] using
      (SOptLib.abs_inner_le_canonicalDualNorm_mul
        setup.normY setup.hnormY_separating
        (zeta := zeta.snd) (d := d.snd)
        (canonicalDualNorm_supportSet_bddAbove_of_separating
          setup.normY setup.hnormY_separating zeta.snd))
  have hsplit :
      |⟪zeta, d⟫_ℝ| ≤ |⟪zeta.fst, d.fst⟫_ℝ| + |⟪zeta.snd, d.snd⟫_ℝ| := by
    rw [WithLp.prod_inner_apply]
    exact abs_add_le _ _
  have hcomponent :
      |⟪zeta, d⟫_ℝ| ≤ ux * px + uy * py :=
    hsplit.trans (add_le_add hx_support hy_support)
  have hweighted :
      ux * px + uy * py ≤
        setup.productDualNorm zeta * setup.productNorm d := by
    have hDX : 0 < 2 * setup.DX ^ 2 := by
      nlinarith [setup.DX_pos]
    have hDY : 0 < 2 * setup.DY ^ 2 := by
      nlinarith [setup.DY_pos]
    have h :=
      weighted_two_term_mul_le_sqrt
        (a := ux) (b := uy) (c := px) (d := py)
        (α := 2 * setup.DX ^ 2) (β := 2 * setup.DY ^ 2)
        (SOptLib.canonicalDualNorm_nonneg setup.normX zeta.fst)
        (SOptLib.canonicalDualNorm_nonneg setup.normY zeta.snd)
        (apply_nonneg setup.normX d.fst)
        (apply_nonneg setup.normY d.snd)
        hDX hDY
    simpa [Setup.productDualNorm_def, Setup.productNorm_def, ux, uy, px, py] using h
  exact hcomponent.trans hweighted

private theorem crossTermQuery_direction_productNorm_sq_integrable (t : Time) :
    Integrable
      (fun ω => (setup.productNorm ((setup.crossTermQuery t ω).2)) ^ 2)
      setup.pathMeasure := by
  letI : IsProbabilityMeasure setup.pathMeasure := setup.pathMeasure_isProbabilityMeasure
  have hmeas :
      AEStronglyMeasurable
        (fun ω =>
          setup.productNorm
            (setup.gamma t • ((setup.iterate t ω).1 - (setup.auxiliaryIterate t ω).1)))
        setup.pathMeasure := by
    have hdir :
        AEStronglyMeasurable
          (fun ω => (setup.crossTermQuery t ω).2) setup.pathMeasure :=
      (measurable_snd.comp (setup.crossTermQuery_measurable t)).aestronglyMeasurable
    simpa [Setup.crossTermQuery] using
      (productNorm_continuous (setup := setup)).comp_aestronglyMeasurable hdir
  letI : CompactSpace setup.Point := isCompact_univ_iff.mp setup.point_univ_isCompact
  have hcompact_pair : IsCompact (Set.univ : Set (setup.Point × setup.Point)) := by
    simpa using (isCompact_univ : IsCompact (Set.univ : Set (setup.Point × setup.Point)))
  simpa [Setup.crossTermQuery] using
    (integrable_sq_compact_pair_continuous_gauge_smul_sub
      (μ := setup.pathMeasure)
      (eval := fun z : setup.Point => (z : Ambient EX EY))
      (gauge := setup.productNorm)
      (η := setup.gamma t)
      (x := setup.iterate t)
      (y := setup.auxiliaryIterate t)
      hcompact_pair
      continuous_subtype_val
      (productNorm_continuous (setup := setup))
      (fun _ => by simp [Setup.productNorm_def])
      hmeas)

/-- Source-dual integrability side condition for the Lemma 4.6 martingale cross
term.

The intended proof combines the product-dual residual second moment
`E‖Δ_t‖_*^2 ≤ 4M^2`, the paper primal-dual support bound
`|⟪Δ_t,d_t⟫| ≤ ‖Δ_t‖_* ‖d_t‖`, and the product-norm boundedness of the feasible
direction `d_t = γ_t (z_t-v_t)`.  This is deliberately not routed through an
ambient Hilbert residual L2 assumption. -/
theorem oracleNoise_cross_term_dual_integrable (t : Time) :
    Integrable
        (fun ω =>
          ⟪setup.oracleNoise t ω, (setup.crossTermQuery t ω).2⟫_ℝ)
        setup.pathMeasure := by
  exact
    integrable_inner_of_abs_inner_le_mul_sq_integrable_gauges
      (μ := setup.pathMeasure)
      (zeta := fun ω => setup.oracleNoise t ω)
      (d := fun ω => (setup.crossTermQuery t ω).2)
      (A := fun ω => setup.productDualNorm (setup.oracleNoise t ω))
      (B := fun ω => setup.productNorm ((setup.crossTermQuery t ω).2))
      (by
        have hquery_meas :
            Measurable (fun ω : setup.SamplePath => (setup.crossTermQuery t ω).1) :=
          measurable_fst.comp (setup.crossTermQuery_measurable t)
        have horacle_meas :
            Measurable
              (fun ω =>
                setup.stochasticOracle (setup.crossTermQuery t ω).1 (setup.sampleAt t ω)) :=
          setup.stochasticOracle_measurable.comp
            (hquery_meas.prodMk (setup.sampleAt_measurable t))
        have hmean_meas :
            Measurable
              (fun ω =>
                setup.meanOracle (setup.crossTermQuery t ω).1) :=
          setup.meanOracle_measurable.comp hquery_meas
        have hres_meas :
            Measurable
              (fun ω =>
                setup.stochasticOracle (setup.crossTermQuery t ω).1 (setup.sampleAt t ω) -
                  setup.meanOracle (setup.crossTermQuery t ω).1) :=
          horacle_meas.sub hmean_meas
        simpa [Setup.oracleNoise] using hres_meas.aestronglyMeasurable)
      ((measurable_snd.comp (setup.crossTermQuery_measurable t)).aestronglyMeasurable)
      (setup.oracleNoise_productDualNorm_sq_integrable t)
      (setup.crossTermQuery_direction_productNorm_sq_integrable t)
      (Filter.Eventually.of_forall (fun _ω => by simp [Setup.productDualNorm_def]))
      (Filter.Eventually.of_forall (fun _ω => by simp [Setup.productNorm_def]))
      (Filter.Eventually.of_forall (fun ω =>
        abs_inner_le_productDualNorm_mul_productNorm (setup := setup)
          (setup.oracleNoise t ω) ((setup.crossTermQuery t ω).2)))

/-- Lemma 4.6 martingale cross term in random-query orientation.

The integrand is `⟪Δ_t, γ_t(z_t-v_t)⟫`, the exact shape produced by applying
the source-dual random-query oracle-residual cancellation route after
discharging fixed-fiber centering, product-law residual measurability,
strict-past adaptedness, and source-dual integrability. -/
theorem oracleNoise_cross_term_random_query_l2 (t : Time) :
    Integrable
        (fun ω =>
          ⟪setup.oracleNoise t ω, (setup.crossTermQuery t ω).2⟫_ℝ)
        setup.pathMeasure ∧
      setup.pathExpectation
        (fun ω =>
          ⟪setup.oracleNoise t ω, (setup.crossTermQuery t ω).2⟫_ℝ) = 0 := by
  letI : IsProbabilityMeasure setup.pathMeasure := setup.pathMeasure_isProbabilityMeasure
  letI : IsProbabilityMeasure setup.P := setup.hP_prob
  letI : IsFiniteMeasure setup.P := inferInstance
  letI : SigmaFinite setup.P := MeasureTheory.IsFiniteMeasure.toSigmaFinite setup.P
  letI : SFinite setup.P := inferInstance
  have hzero :
      ∫ ω,
          ⟪(setup.crossTermQuery t ω).2,
            setup.stochasticOracle (setup.crossTermQuery t ω).1 (setup.sampleAt t ω) -
              setup.meanOracle (setup.crossTermQuery t ω).1⟫_ℝ ∂setup.pathMeasure = 0 := by
    simpa using
      randomQuery_inner_oracleResidual_integral_eq_zero_of_fixed_zero
      (P := setup.pathMeasure) (ν := setup.P)
      (query := setup.crossTermQuery t) (sample := setup.sampleAt t)
      (residual := fun q ξ => setup.stochasticOracle q.1 ξ - setup.meanOracle q.1)
      (d := fun q : setup.Point × Ambient EX EY => q.2)
      (oracle_residual_product_measurable (setup := setup))
      measurable_snd
      (setup.crossTermQuery_measurable t)
      (setup.sampleAt_measurable t)
      (crossTermQuery_indep_sampleAt (setup := setup) t)
      (setup.sampleAt_law t)
      (fun q => setup.fixed_fiber_product_residual_integrable q.1)
      (fun q => setup.fixed_fiber_product_residual_centered q.1)
  refine ⟨setup.oracleNoise_cross_term_dual_integrable t, ?_⟩
  unfold Setup.pathExpectation
  rw [← hzero]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun ω => by
    simp [Setup.oracleNoise, Setup.crossTermQuery, real_inner_comm])

/-- Well-definedness of the Lemma 4.6 martingale cross-term expectation.

The paper derives this cross term from past-measurability of `z_t, v_t` and
conditional centering of `Δ_t`; Lean exposes the integrability obligation
separately so the displayed equality cannot rely on totalized integral fallback. -/
theorem oracleNoise_cross_term_integrable (t : Time) :
    Integrable
      (fun ω =>
        setup.gamma t *
          ⟪(setup.iterate t ω).1 - (setup.auxiliaryIterate t ω).1,
            setup.oracleNoise t ω⟫_ℝ) setup.pathMeasure := by
  refine (setup.oracleNoise_cross_term_random_query_l2 t).1.congr ?_
  exact Filter.Eventually.of_forall (fun ω => by
    simp [Setup.crossTermQuery, real_inner_comm, real_inner_smul_right]
    ring)

/-- Lemma 4.6 proof boundary: the martingale cross term is integrable and has
zero expectation under the canonical iid sample stream. -/
theorem oracleNoise_cross_term_zero (t : Time) :
    Integrable
        (fun ω =>
          setup.gamma t *
            ⟪(setup.iterate t ω).1 - (setup.auxiliaryIterate t ω).1,
              setup.oracleNoise t ω⟫_ℝ) setup.pathMeasure ∧
      setup.pathExpectation (fun ω =>
        setup.gamma t *
          ⟪(setup.iterate t ω).1 - (setup.auxiliaryIterate t ω).1,
            setup.oracleNoise t ω⟫_ℝ) = 0 := by
  refine ⟨setup.oracleNoise_cross_term_integrable t, ?_⟩
  have h := (setup.oracleNoise_cross_term_random_query_l2 t).2
  unfold Setup.pathExpectation at h ⊢
  rw [← h]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun ω => by
    simp [Setup.crossTermQuery, real_inner_comm, real_inner_smul_right]
    ring)

/-- Output times `1, ..., j` for the paper weighted average. -/
def outputTimes (j : ℕ) : Finset Time :=
  SOptLib.positiveTimeOutputWindowTimes 1 j (by norm_num)

/-- Denominator `∑_{t=1}^j γ_t` in the paper output. -/
noncomputable def outputWeightSum (j : ℕ) : ℝ :=
  Finset.sum (outputTimes j) setup.gamma

/-- Positivity of the output denominator for nonempty positive-time windows. -/
theorem outputWeightSum_pos {j : ℕ} (hj : 1 ≤ j) :
    0 < setup.outputWeightSum j := by
  simpa [Setup.outputWeightSum, Setup.outputTimes] using
    (SOptLib.positiveTimeOutputWindow (γ := setup.gamma) setup.hgamma_pos
      (start := 1) (stop := j) (by norm_num) hj)

/-- The paper weighted-average output
`z̃_j = (∑_{t=1}^j γ_t)⁻¹ ∑_{t=1}^j γ_t z_t`. -/
noncomputable def weightedAverageOutput (j : ℕ) (hj : 1 ≤ j) : setup.SamplePath → setup.Point :=
  SOptLib.weightedOutputAverage setup.jointCarrier
    (fun _ : Unit => outputTimes j)
    setup.gamma
    (fun t ω => (setup.iterate t ω).1)
    (fun _ : Unit => setup.outputWeightSum j)
    setup.jointCarrier_convex
    (by
      intro _ t _ht
      exact le_of_lt (setup.hgamma_pos t))
    (by
      intro _ t _ht ω
      exact (setup.iterate t ω).2)
    (by
      intro _
      exact setup.outputWeightSum_pos hj)
    (by
      intro _
      rfl)
    ()

/-- The weighted output unfolds to the source formula `(4.3.7)`. -/
theorem weightedAverageOutput_def (j : ℕ) (hj : 1 ≤ j) (ω : setup.SamplePath) :
    (setup.weightedAverageOutput j hj ω).1 =
      (setup.outputWeightSum j)⁻¹ •
        Finset.sum (outputTimes j) (fun t => setup.gamma t • (setup.iterate t ω).1) := by
  rfl

/-- Existence of an attained maximizer for `max_{y∈Y} φ(x,y)`. -/
theorem maxPhiYPoint_exists (x : {x : EX // x ∈ setup.X}) :
    ∃ y : {y : EY // y ∈ setup.Y}, ∀ y' : {y : EY // y ∈ setup.Y},
      (fun x y => SOptLib.objectiveExpectation setup.P (fun xy ξ => setup.Phi xy.1 xy.2 ξ) id (x, y)) x y' ≤ (fun x y => SOptLib.objectiveExpectation setup.P (fun xy ξ => setup.Phi xy.1 xy.2 ξ) id (x, y)) x y := by
  classical
  rcases setup.phi_lipschitz with ⟨K, hLip⟩
  let payoff : Ambient EX EY → ℝ := fun z => by
    classical
    exact if hz : z ∈ setup.jointCarrier then
      expectedPayoff setup.P setup.Phi ⟨z.fst, hz.1⟩ ⟨z.snd, hz.2⟩
    else
      0
  have hsliceContOn :
      ContinuousOn
        (fun y : EY => payoff (WithLp.toLp 2 (x.1, y)))
        setup.Y := by
    have hmap : Continuous
        (fun y : EY => (WithLp.toLp 2 (x.1, y) : Ambient EX EY)) := by
      exact (WithLp.prod_continuous_toLp 2 EX EY).comp (Continuous.prodMk_right x.1)
    exact hLip.continuousOn.comp hmap.continuousOn (by
      intro y hy
      exact (setup.jointCarrier_def _).2 ⟨x.2, hy⟩)
  have hcompact : IsCompact setup.Y :=
    Metric.isCompact_of_isClosed_isBounded setup.hY_closed setup.hY_bounded
  rcases hcompact.exists_isMaxOn setup.hY_nonempty hsliceContOn with
    ⟨y, hymem, hymax⟩
  refine ⟨⟨y, hymem⟩, ?_⟩
  intro y'
  have hpayoff_eq (u : {y : EY // y ∈ setup.Y}) :
      payoff (WithLp.toLp 2 (x.1, u.1)) =
        (fun x y => SOptLib.objectiveExpectation setup.P
          (fun xy ξ => setup.Phi xy.1 xy.2 ξ) id (x, y)) x u := by
    have hz : WithLp.toLp 2 (x.1, u.1) ∈ setup.jointCarrier := by
      exact (setup.jointCarrier_def _).2 ⟨x.2, u.2⟩
    simp [payoff, SOptLib.objectiveExpectation_def, expectedPayoff, hz]
  simpa [hpayoff_eq y', hpayoff_eq ⟨y, hymem⟩] using hymax y'.2

/-- Selected maximizer realizing `max_{y∈Y} φ(x,y)`. -/
noncomputable def maxPhiYPoint (x : {x : EX // x ∈ setup.X}) : {y : EY // y ∈ setup.Y} :=
  Classical.choose (setup.maxPhiYPoint_exists x)

/-- `max_{y ∈ Y} φ(x,y)` in the paper's error measure, using the attained maximum. -/
noncomputable def maxPhiY (x : {x : EX // x ∈ setup.X}) : ℝ :=
  (fun x y => SOptLib.objectiveExpectation setup.P (fun xy ξ => setup.Phi xy.1 xy.2 ξ) id (x, y)) x (setup.maxPhiYPoint x)

/-- The selected value realizes the displayed maximum over `Y`. -/
theorem maxPhiY_isMax (x : {x : EX // x ∈ setup.X}) (y : {y : EY // y ∈ setup.Y}) :
    (fun x y => SOptLib.objectiveExpectation setup.P (fun xy ξ => setup.Phi xy.1 xy.2 ξ) id (x, y)) x y ≤ setup.maxPhiY x := by
  exact Classical.choose_spec (setup.maxPhiYPoint_exists x) y

/-- Existence of an attained minimizer for `min_{x∈X} φ(x,y)`. -/
theorem minPhiXPoint_exists (y : {y : EY // y ∈ setup.Y}) :
    ∃ x : {x : EX // x ∈ setup.X}, ∀ x' : {x : EX // x ∈ setup.X},
      (fun x y => SOptLib.objectiveExpectation setup.P (fun xy ξ => setup.Phi xy.1 xy.2 ξ) id (x, y)) x y ≤ (fun x y => SOptLib.objectiveExpectation setup.P (fun xy ξ => setup.Phi xy.1 xy.2 ξ) id (x, y)) x' y := by
  classical
  rcases setup.phi_lipschitz with ⟨K, hLip⟩
  let payoff : Ambient EX EY → ℝ := fun z => by
    classical
    exact if hz : z ∈ setup.jointCarrier then
      expectedPayoff setup.P setup.Phi ⟨z.fst, hz.1⟩ ⟨z.snd, hz.2⟩
    else
      0
  have hsliceContOn :
      ContinuousOn
        (fun x : EX => payoff (WithLp.toLp 2 (x, y.1)))
        setup.X := by
    have hmap : Continuous
        (fun x : EX => (WithLp.toLp 2 (x, y.1) : Ambient EX EY)) := by
      exact (WithLp.prod_continuous_toLp 2 EX EY).comp (Continuous.prodMk_left y.1)
    exact hLip.continuousOn.comp hmap.continuousOn (by
      intro x hx
      exact (setup.jointCarrier_def _).2 ⟨hx, y.2⟩)
  have hcont : Continuous (fun x : {x : EX // x ∈ setup.X} => (fun x y => SOptLib.objectiveExpectation setup.P (fun xy ξ => setup.Phi xy.1 xy.2 ξ) id (x, y)) x y) := by
    refine continuous_subtype_of_continuousOn_ambient
      (X := setup.X)
      (fun x : {x : EX // x ∈ setup.X} => (fun x y => SOptLib.objectiveExpectation setup.P (fun xy ξ => setup.Phi xy.1 xy.2 ξ) id (x, y)) x y)
      (fun x : EX => payoff (WithLp.toLp 2 (x, y.1)))
      hsliceContOn ?_
    intro x
    have hz : WithLp.toLp 2 (x.1, y.1) ∈ setup.jointCarrier := by
      exact (setup.jointCarrier_def _).2 ⟨x.2, y.2⟩
    simp [payoff, SOptLib.objectiveExpectation_def, expectedPayoff, hz]
  have hcompact : IsCompact (Set.univ : Set {x : EX // x ∈ setup.X}) := by
    simpa using isCompact_univ_subtype_of_isClosed_isBounded setup.hX_closed
      setup.hX_bounded
  have hne : (Set.univ : Set {x : EX // x ∈ setup.X}).Nonempty := by
    rcases setup.hX_nonempty with ⟨x, hx⟩
    exact ⟨⟨x, hx⟩, by simp⟩
  rcases hcompact.exists_isMinOn hne hcont.continuousOn with ⟨x0, _hxuniv, hxmin⟩
  refine ⟨x0, ?_⟩
  intro x'
  exact hxmin (by simp : x' ∈ (Set.univ : Set {x : EX // x ∈ setup.X}))

/-- Selected minimizer realizing `min_{x∈X} φ(x,y)`. -/
noncomputable def minPhiXPoint (y : {y : EY // y ∈ setup.Y}) : {x : EX // x ∈ setup.X} :=
  Classical.choose (setup.minPhiXPoint_exists y)

/-- `min_{x ∈ X} φ(x,y)` in the paper's error measure, using the attained minimum. -/
noncomputable def minPhiX (y : {y : EY // y ∈ setup.Y}) : ℝ :=
  (fun x y => SOptLib.objectiveExpectation setup.P (fun xy ξ => setup.Phi xy.1 xy.2 ξ) id (x, y)) (setup.minPhiXPoint y) y

/-- The selected value realizes the displayed minimum over `X`. -/
theorem minPhiX_isMin (y : {y : EY // y ∈ setup.Y}) (x : {x : EX // x ∈ setup.X}) :
    setup.minPhiX y ≤ (fun x y => SOptLib.objectiveExpectation setup.P (fun xy ξ => setup.Phi xy.1 xy.2 ξ) id (x, y)) x y := by
  exact Classical.choose_spec (setup.minPhiXPoint_exists y) x

/-- Paper saddle-point error
`ε_φ(z̃) = max_y φ(x̃,y) - min_x φ(x,ỹ)`. -/
noncomputable def epsilonPhi (z : setup.Point) : ℝ :=
  setup.maxPhiY (setup.xPoint z) - setup.minPhiX (setup.yPoint z)

theorem epsilonPhi_def (z : setup.Point) :
    setup.epsilonPhi z =
      setup.maxPhiY (setup.xPoint z) - setup.minPhiX (setup.yPoint z) := by
  rfl

/-- Sum of squared stepsizes over the paper window `1, ..., j`. -/
noncomputable def sumGammaSq (j : ℕ) : ℝ :=
  Finset.sum (outputTimes j) (fun t => setup.gamma t ^ 2)

/-- Regret-like summand from `(4.3.8)` and Lemma 4.6. -/
noncomputable def regretSum (j : ℕ) (ω : setup.SamplePath) (z : setup.Point) : ℝ :=
  Finset.sum (outputTimes j) (fun t =>
    setup.gamma t *
      ⟪setup.meanOracle (setup.iterate t ω), (setup.iterate t ω).1 - z.1⟫_ℝ)

/-- Existence of an attained maximizer for the regret-like sum over `Z`. -/
theorem maxRegretPoint_exists (j : ℕ) (ω : setup.SamplePath) :
    ∃ z : setup.Point, ∀ z' : setup.Point, setup.regretSum j ω z' ≤ setup.regretSum j ω z := by
  classical
  have hcont : Continuous (fun z : setup.Point => setup.regretSum j ω z) := by
    unfold Setup.regretSum
    apply continuous_finset_sum
    intro t ht
    exact continuous_const.mul
      (continuous_const.inner (continuous_const.sub setup.pointEval_continuous))
  have hcompact : IsCompact (Set.univ : Set setup.Point) := setup.point_univ_isCompact
  have hne : (Set.univ : Set setup.Point).Nonempty := by
    rcases setup.jointCarrier_nonempty with ⟨z, hz⟩
    exact ⟨⟨z, hz⟩, by simp⟩
  rcases hcompact.exists_isMaxOn hne hcont.continuousOn with ⟨z, _hzuniv, hzmax⟩
  exact ⟨z, fun z' => hzmax (by simp : z' ∈ (Set.univ : Set setup.Point))⟩

/-- Selected maximizer for the source expression
`max_{z∈Z} ∑ γ_t g(z_t)^T(z_t-z)`. -/
noncomputable def maxRegretPoint (j : ℕ) (ω : setup.SamplePath) : setup.Point :=
  Classical.choose (setup.maxRegretPoint_exists j ω)

/-- The source maximum `max_{z∈Z} ∑ γ_t g(z_t)^T(z_t-z)`. -/
noncomputable def maxRegretSum (j : ℕ) (ω : setup.SamplePath) : ℝ :=
  setup.regretSum j ω (setup.maxRegretPoint j ω)

/-- The selected regret value realizes the displayed maximum over `Z`. -/
theorem maxRegretSum_isMax (j : ℕ) (ω : setup.SamplePath) (z : setup.Point) :
    setup.regretSum j ω z ≤ setup.maxRegretSum j ω := by
  exact Classical.choose_spec (setup.maxRegretPoint_exists j ω) z

theorem regretSum_def (j : ℕ) (ω : setup.SamplePath) (z : setup.Point) :
    setup.regretSum j ω z =
      Finset.sum (outputTimes j) (fun t =>
        setup.gamma t *
          ⟪setup.meanOracle (setup.iterate t ω), (setup.iterate t ω).1 - z.1⟫_ℝ) := by
  rfl

/-- One-iterate saddle gap bound from the component subgradient assumptions,
identified with the product mean-oracle pairing. -/
private theorem single_iterate_phi_gap_le_meanOracle_inner
    (zt u : setup.Point) :
    (fun x y => SOptLib.objectiveExpectation setup.P (fun xy ξ => setup.Phi xy.1 xy.2 ξ) id (x, y)) (setup.xPoint zt) (setup.yPoint u) -
        (fun x y => SOptLib.objectiveExpectation setup.P (fun xy ξ => setup.Phi xy.1 xy.2 ξ) id (x, y)) (setup.xPoint u) (setup.yPoint zt) ≤
      ⟪setup.meanOracle zt, zt.1 - u.1⟫_ℝ := by
  let L : {x : EX // x ∈ setup.X} → {y : EY // y ∈ setup.Y} → ℝ :=
    fun x y => SOptLib.objectiveExpectation setup.P
      (fun xy ξ => setup.Phi xy.1 xy.2 ξ) id (x, y)
  have hgap :=
    SOptLib.saddleGap_le_inner_signed_subgradient
      (L := L) (evalX := fun x : {x : EX // x ∈ setup.X} => x.1)
      (evalY := fun y : {y : EY // y ∈ setup.Y} => y.1)
      (gx := setup.gx) (gy := setup.gy)
      (zt := (setup.xPoint zt, setup.yPoint zt))
      (u := (setup.xPoint u, setup.yPoint u))
      (by
        intro x
        exact (SOptLib.mem_carrierSubdifferential_iff.mp
          (setup.gx_mem_subgradient (setup.xPoint zt) (setup.yPoint zt))) x)
      (by
        intro y
        exact (SOptLib.mem_carrierSubdifferential_iff.mp
          (setup.neg_gy_mem_subgradient (setup.xPoint zt) (setup.yPoint zt))) y)
  simpa [L, SOptLib.saddleGap, Setup.meanOracle_def, Setup.xPoint, Setup.yPoint,
    WithLp.prod_inner_apply, WithLp.ofLp_fst, WithLp.ofLp_snd, WithLp.sub_fst,
    WithLp.sub_snd, WithLp.toLp_fst, WithLp.toLp_snd] using hgap

/-- Weighted form of the one-iterate subgradient bound, followed by the selected
maximum over the product carrier. -/
private theorem weighted_phi_gap_le_inv_maxRegret
    (j : ℕ) (hj : 1 ≤ j) (ω : setup.SamplePath) (u : setup.Point) :
    (setup.outputWeightSum j)⁻¹ *
        Finset.sum (outputTimes j) (fun t =>
          setup.gamma t *
            ((fun x y => SOptLib.objectiveExpectation setup.P (fun xy ξ => setup.Phi xy.1 xy.2 ξ) id (x, y)) (setup.xPoint (setup.iterate t ω)) (setup.yPoint u) -
              (fun x y => SOptLib.objectiveExpectation setup.P (fun xy ξ => setup.Phi xy.1 xy.2 ξ) id (x, y)) (setup.xPoint u) (setup.yPoint (setup.iterate t ω)))) ≤
      (setup.outputWeightSum j)⁻¹ * setup.maxRegretSum j ω := by
  exact weighted_gap_sum_le_inv_max_regret_of_pointwise_le
    (times := outputTimes j) (gamma := setup.gamma)
    (gap := fun t =>
      (fun x y => SOptLib.objectiveExpectation setup.P (fun xy ξ => setup.Phi xy.1 xy.2 ξ) id (x, y))
          (setup.xPoint (setup.iterate t ω)) (setup.yPoint u) -
        (fun x y => SOptLib.objectiveExpectation setup.P (fun xy ξ => setup.Phi xy.1 xy.2 ξ) id (x, y))
          (setup.xPoint u) (setup.yPoint (setup.iterate t ω)))
    (regretTerm := fun t =>
      ⟪setup.meanOracle (setup.iterate t ω), (setup.iterate t ω).1 - u.1⟫_ℝ)
    (weightSum := setup.outputWeightSum j) (maxRegret := setup.maxRegretSum j ω)
    (fun t _ht => le_of_lt (setup.hgamma_pos t))
    (setup.outputWeightSum_pos hj)
    (fun t _ht => setup.single_iterate_phi_gap_le_meanOracle_inner (setup.iterate t ω) u)
    (by
      rw [← setup.regretSum_def j ω u]
      exact setup.maxRegretSum_isMax j ω u)

/-- The paper iterate is measurable for the full sample-path sigma-algebra. -/
private theorem iterate_measurable (t : Time) :
    Measurable (setup.iterate t) := by
  let mpast : MeasurableSpace setup.SamplePath :=
    (⨆ j < t.1 - 1,
      MeasurableSpace.comap (fun ω : setup.SamplePath => ω j)
        (by infer_instance : MeasurableSpace setup.SamplePoint))
  have hle : mpast ≤ (MeasurableSpace.pi : MeasurableSpace setup.SamplePath) := by
    dsimp [mpast]
    refine iSup_le ?_
    intro j
    refine iSup_le ?_
    intro _hj
    have hcoord :
        @Measurable setup.SamplePath setup.SamplePoint
          (MeasurableSpace.pi : MeasurableSpace setup.SamplePath)
          (by infer_instance : MeasurableSpace setup.SamplePoint)
          (fun ω : setup.SamplePath => ω j) := by
      exact
        (@measurable_pi_apply ℕ (fun _ : ℕ => setup.SamplePoint)
          (fun _ : ℕ => (by infer_instance : MeasurableSpace setup.SamplePoint)) j)
    exact hcoord.comap_le
  exact
    @Measurable.of_measurableSpace_le
      setup.SamplePath setup.Point
      (MeasurableSpace.pi : MeasurableSpace setup.SamplePath)
      (by infer_instance : MeasurableSpace setup.Point)
      mpast (setup.iterate t)
      (setup.iterate_strictPast_measurable t) hle

/-- Fixed-comparator measurability of the regret-like finite sum. -/
private theorem regretSum_measurable (j : ℕ) (z : setup.Point) :
    Measurable (fun ω => setup.regretSum j ω z) := by
  rw [show (fun ω => setup.regretSum j ω z) =
      fun ω => Finset.sum (outputTimes j) (fun t =>
        setup.gamma t *
          ⟪setup.meanOracle (setup.iterate t ω), (setup.iterate t ω).1 - z.1⟫_ℝ) by
    funext ω
    rw [setup.regretSum_def j ω z]]
  refine Finset.measurable_sum _ ?_
  intro t ht
  have hiter : Measurable (setup.iterate t) :=
    setup.iterate_measurable t
  have hmean : Measurable (fun ω : setup.SamplePath =>
      setup.meanOracle (setup.iterate t ω)) :=
    setup.meanOracle_measurable.comp hiter
  have hiter_val : Measurable (fun ω : setup.SamplePath => (setup.iterate t ω).1) :=
    measurable_subtype_coe.comp hiter
  have hdisp : Measurable (fun ω : setup.SamplePath => (setup.iterate t ω).1 - z.1) :=
    hiter_val.sub measurable_const
  have hinner_cont : Continuous (fun p : Ambient EX EY × Ambient EX EY =>
      ⟪p.1, p.2⟫_ℝ) :=
    continuous_fst.inner continuous_snd
  have hinner : Measurable (fun ω : setup.SamplePath =>
      ⟪setup.meanOracle (setup.iterate t ω), (setup.iterate t ω).1 - z.1⟫_ℝ) :=
    by
      simpa [Function.comp_def] using hinner_cont.measurable.comp (hmean.prodMk hdisp)
  exact measurable_const.mul hinner

/-- Continuity of the regret-like finite sum in the comparison point. -/
private theorem regretSum_continuous_comparator (j : ℕ) (ω : setup.SamplePath) :
    Continuous (fun z : setup.Point => setup.regretSum j ω z) := by
  unfold Setup.regretSum
  apply continuous_finset_sum
  intro t ht
  exact continuous_const.mul
    (continuous_const.inner (continuous_const.sub setup.pointEval_continuous))

/-- Measurability of the compact maximum value in Lemma 4.6.

The proof avoids measurability of the nonunique selected argmax.  Instead, it
identifies the maximum over the compact carrier with the supremum over a
countable dense sequence of fixed comparators. -/
private theorem maxRegretSum_measurable (j : ℕ) :
    Measurable (fun ω => setup.maxRegretSum j ω) := by
  classical
  have hne : Nonempty setup.Point := by
    rcases setup.jointCarrier_nonempty with ⟨z, hz⟩
    exact ⟨⟨z, hz⟩⟩
  letI : Inhabited setup.Point := Classical.inhabited_of_nonempty hne
  letI : CompactSpace setup.Point := isCompact_univ_iff.mp setup.point_univ_isCompact
  haveI : TopologicalSpace.SeparableSpace setup.Point := by infer_instance
  let u : ℕ → setup.Point := TopologicalSpace.denseSeq setup.Point
  let F : setup.SamplePath → ℝ := fun ω => ⨆ n : ℕ, setup.regretSum j ω (u n)
  have hDenseRange : DenseRange u := by
    exact TopologicalSpace.denseRange_denseSeq (α := setup.Point)
  have hDense : Dense (Set.range u) := hDenseRange
  have hF_meas : Measurable F := by
    dsimp [F]
    exact Measurable.iSup (fun n => setup.regretSum_measurable j (u n))
  have hEq : (fun ω : setup.SamplePath => setup.maxRegretSum j ω) = F := by
    funext ω
    apply le_antisymm
    · have hbounded : BddAbove (Set.range (fun n : ℕ => setup.regretSum j ω (u n))) := by
        exact ⟨setup.maxRegretSum j ω, by
          rintro y ⟨n, rfl⟩
          exact setup.maxRegretSum_isMax j ω (u n)⟩
      have hall : ∀ z : setup.Point, setup.regretSum j ω z ≤ F ω := by
        intro z
        refine le_of_continuousOn_of_dense_le
          (f := fun _ : setup.Point => F ω)
          (g := fun z : setup.Point => setup.regretSum j ω z)
          (s := Set.range u) ?_ hDense ?_ z
        · exact (continuous_const.sub
            (setup.regretSum_continuous_comparator j ω)).continuousOn
        · intro x hx
          rcases hx with ⟨n, rfl⟩
          dsimp [F]
          exact le_ciSup hbounded n
      simpa [Setup.maxRegretSum] using hall (setup.maxRegretPoint j ω)
    · dsimp [F]
      exact ciSup_le fun n => setup.maxRegretSum_isMax j ω (u n)
  rw [hEq]
  exact hF_meas


/-- Uniform product-dual bound for the deterministic mean oracle. -/
private theorem meanOracle_productDualNorm_le_M (z : setup.Point) :
    setup.productDualNorm (setup.meanOracle z) ≤ setup.M := by
  letI : IsProbabilityMeasure setup.P := setup.hP_prob
  simpa [Setup.productDualNorm, Setup.meanOracle, Setup.M] using
    (SOptLib.twoBlockSignedMeanOracle_dualNorm_le_of_secondMoment_bounds
      (μ := setup.P) setup.normX setup.normY setup.DX setup.DY setup.MX setup.MY
      (fun ξ : setup.SamplePoint => setup.Gx (setup.xPoint z) (setup.yPoint z) ξ)
      (fun ξ : setup.SamplePoint => setup.Gy (setup.xPoint z) (setup.yPoint z) ξ)
      (setup.gx (setup.xPoint z) (setup.yPoint z))
      (setup.gy (setup.xPoint z) (setup.yPoint z))
      (fun ξ => canonicalDualNorm_supportSet_bddAbove_of_separating
        setup.normX setup.hnormX_separating
        (setup.Gx (setup.xPoint z) (setup.yPoint z) ξ))
      (fun ξ => canonicalDualNorm_supportSet_bddAbove_of_separating
        setup.normY setup.hnormY_separating
        (setup.Gy (setup.xPoint z) (setup.yPoint z) ξ))
      (setup.Gx_integrable (setup.xPoint z) (setup.yPoint z))
      (setup.Gy_integrable (setup.xPoint z) (setup.yPoint z))
      (setup.hgx_eq_expectation (setup.xPoint z) (setup.yPoint z))
      (setup.hgy_eq_expectation (setup.xPoint z) (setup.yPoint z))
      (setup.Gx_second_moment_integrable (setup.xPoint z) (setup.yPoint z))
      (setup.Gy_second_moment_integrable (setup.xPoint z) (setup.yPoint z))
      (setup.Gx_second_moment_bound (setup.xPoint z) (setup.yPoint z))
      (setup.Gy_second_moment_bound (setup.xPoint z) (setup.yPoint z)))

/-- A compact deterministic product-norm diameter bound on pairs of feasible points. -/
private theorem productNorm_pair_uniform_bound :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ z z' : setup.Point, setup.productNorm (z.1 - z'.1) ≤ D := by
  letI : CompactSpace setup.Point := isCompact_univ_iff.mp setup.point_univ_isCompact
  have hcompact_pair : IsCompact (Set.univ : Set (setup.Point × setup.Point)) := by
    simpa using (isCompact_univ : IsCompact (Set.univ : Set (setup.Point × setup.Point)))
  have hcont : ContinuousOn
      (fun p : setup.Point × setup.Point =>
        setup.productNorm (p.1.1 - p.2.1)) Set.univ := by
    have hfst : Continuous (fun p : setup.Point × setup.Point => (p.1 : Ambient EX EY)) := by
      exact continuous_subtype_val.comp continuous_fst
    have hsnd : Continuous (fun p : setup.Point × setup.Point => (p.2 : Ambient EX EY)) := by
      exact continuous_subtype_val.comp continuous_snd
    exact ((productNorm_continuous (setup := setup)).comp (hfst.sub hsnd)).continuousOn
  rcases exists_nonneg_norm_bound_of_isCompact_of_continuousOn
      (fun p : setup.Point × setup.Point => setup.productNorm (p.1.1 - p.2.1))
      hcompact_pair hcont with ⟨D, hD_nonneg, hD_bound⟩
  refine ⟨D, hD_nonneg, ?_⟩
  intro z z'
  have h := hD_bound (z, z')
    (by simp : (z, z') ∈ (Set.univ : Set (setup.Point × setup.Point)))
  have hpn_nonneg : 0 ≤ setup.productNorm (z.1 - z'.1) := by
    simp [Setup.productNorm_def]
  calc
    setup.productNorm (z.1 - z'.1)
        = ‖setup.productNorm (z.1 - z'.1)‖ := (Real.norm_of_nonneg hpn_nonneg).symm
    _ ≤ D := h

/-- Uniform deterministic domination of the compact maximum value. -/
private theorem maxRegretSum_uniform_bound (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ω, ‖setup.maxRegretSum j ω‖ ≤ C := by
  classical
  rcases setup.productNorm_pair_uniform_bound with ⟨D, hD_nonneg, hD_bound⟩
  let C : ℝ := Finset.sum (outputTimes j) (fun t => setup.gamma t * setup.M * D)
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    refine Finset.sum_nonneg ?_
    intro t ht
    exact mul_nonneg (mul_nonneg (le_of_lt (setup.hgamma_pos t))
      (le_of_lt setup.M_pos)) hD_nonneg
  refine ⟨C, hC_nonneg, ?_⟩
  intro ω
  let zstar : setup.Point := setup.maxRegretPoint j ω
  have hsum_abs :
      |Finset.sum (outputTimes j) (fun t =>
          setup.gamma t *
            ⟪setup.meanOracle (setup.iterate t ω), (setup.iterate t ω).1 - zstar.1⟫_ℝ)| ≤
        Finset.sum (outputTimes j) (fun t =>
          |setup.gamma t *
            ⟪setup.meanOracle (setup.iterate t ω), (setup.iterate t ω).1 - zstar.1⟫_ℝ|) := by
    simpa using
      (Finset.abs_sum_le_sum_abs
        (fun t =>
          setup.gamma t *
            ⟪setup.meanOracle (setup.iterate t ω), (setup.iterate t ω).1 - zstar.1⟫_ℝ)
        (outputTimes j))
  have hterm :
      ∀ t ∈ outputTimes j,
        |setup.gamma t *
            ⟪setup.meanOracle (setup.iterate t ω), (setup.iterate t ω).1 - zstar.1⟫_ℝ| ≤
          setup.gamma t * setup.M * D := by
    intro t ht
    have hgamma_nonneg : 0 ≤ setup.gamma t := le_of_lt (setup.hgamma_pos t)
    have hinner :
        |⟪setup.meanOracle (setup.iterate t ω), (setup.iterate t ω).1 - zstar.1⟫_ℝ| ≤
          setup.productDualNorm (setup.meanOracle (setup.iterate t ω)) *
            setup.productNorm ((setup.iterate t ω).1 - zstar.1) :=
      abs_inner_le_productDualNorm_mul_productNorm (setup := setup)
        (setup.meanOracle (setup.iterate t ω)) ((setup.iterate t ω).1 - zstar.1)
    have hdual :
        setup.productDualNorm (setup.meanOracle (setup.iterate t ω)) ≤ setup.M :=
      setup.meanOracle_productDualNorm_le_M (setup.iterate t ω)
    have hpn :
        setup.productNorm ((setup.iterate t ω).1 - zstar.1) ≤ D :=
      hD_bound (setup.iterate t ω) zstar
    have hprod :
        setup.productDualNorm (setup.meanOracle (setup.iterate t ω)) *
            setup.productNorm ((setup.iterate t ω).1 - zstar.1) ≤
          setup.M * D := by
      exact mul_le_mul hdual hpn
        (by simp [Setup.productNorm_def])
        (le_of_lt setup.M_pos)
    calc
      |setup.gamma t *
          ⟪setup.meanOracle (setup.iterate t ω), (setup.iterate t ω).1 - zstar.1⟫_ℝ|
          = setup.gamma t *
              |⟪setup.meanOracle (setup.iterate t ω),
                (setup.iterate t ω).1 - zstar.1⟫_ℝ| := by
              rw [abs_mul, abs_of_nonneg hgamma_nonneg]
      _ ≤ setup.gamma t *
            (setup.productDualNorm (setup.meanOracle (setup.iterate t ω)) *
              setup.productNorm ((setup.iterate t ω).1 - zstar.1)) :=
            mul_le_mul_of_nonneg_left hinner hgamma_nonneg
      _ ≤ setup.gamma t * (setup.M * D) :=
            mul_le_mul_of_nonneg_left hprod hgamma_nonneg
      _ = setup.gamma t * setup.M * D := by ring
  have habs :
      |setup.maxRegretSum j ω| ≤ C := by
    rw [Setup.maxRegretSum, setup.regretSum_def j ω zstar]
    dsimp [C]
    exact hsum_abs.trans (Finset.sum_le_sum hterm)
  simpa [Real.norm_eq_abs] using habs

/-- Well-definedness of the expectation appearing in Lemma 4.6. -/
theorem maxRegretSum_integrable (j : ℕ) (hj : 1 ≤ j) :
    Integrable (fun ω => setup.maxRegretSum j ω) setup.pathMeasure := by
  have _hj : 1 ≤ j := hj
  letI : IsProbabilityMeasure setup.pathMeasure := setup.pathMeasure_isProbabilityMeasure
  rcases setup.maxRegretSum_uniform_bound j with ⟨C, _hC_nonneg, hC_bound⟩
  exact integrable_of_measurable_bounded_real
    (setup.maxRegretSum_measurable j) hC_bound

private theorem productDGF_proxFunction_le_one (z : setup.InteriorPoint) (u : setup.Point) :
    setup.proxFunction z u ≤ 1 := by
  classical
  let d2 : ℝ :=
    sourceDGFDiameterSq setup.productNorm setup.productPotential setup.jointCarrier_nonempty
      setup.jointCarrier_bounded setup.jointCarrier_closed setup.productDGF_modulus_one
  rcases sourceDGFDiameterSq_eq_attained setup.jointCarrier_nonempty
      setup.jointCarrier_bounded setup.jointCarrier_closed setup.productDGF_modulus_one with
    ⟨zmax, umax, hdiamSq_eq, hdiamSq_bound⟩
  have hprox_le_d2 : setup.proxFunction z u ≤ d2 := by
    simpa [d2, Setup.proxFunction] using hdiamSq_bound z u
  have hzero :
      sourceDGFProx setup.productPotential zmax (setup.interiorPointToPoint zmax) = 0 := by
    simp [sourceDGFProx, Setup.interiorPointToPoint, sourceDGFCoreToCarrier]
  have hd2_nonneg : 0 ≤ d2 := by
    have h0le :
        0 ≤
          sourceDGFDiameterSq setup.productNorm setup.productPotential setup.jointCarrier_nonempty
            setup.jointCarrier_bounded setup.jointCarrier_closed setup.productDGF_modulus_one := by
      calc
        0 = sourceDGFProx setup.productPotential zmax (setup.interiorPointToPoint zmax) := hzero.symm
        _ ≤
            sourceDGFDiameterSq setup.productNorm setup.productPotential setup.jointCarrier_nonempty
              setup.jointCarrier_bounded setup.jointCarrier_closed setup.productDGF_modulus_one :=
              hdiamSq_bound zmax (setup.interiorPointToPoint zmax)
    simpa [d2] using h0le
  have hd2_eq_one : d2 = 1 := by
    have hsqrt :
        Real.sqrt d2 = 1 := by
      simpa [d2, sourceDGFDiameter] using setup.productDGF_diameter_eq_one
    have hsquare : (Real.sqrt d2) ^ 2 = (1 : ℝ) ^ 2 := by
      rw [hsqrt]
    simpa [Real.sq_sqrt hd2_nonneg] using hsquare
  simpa [hd2_eq_one] using hprox_le_d2

private theorem initial_proxFunction_le_one (u : setup.Point) :
    setup.proxFunction (Classical.choose setup.initialPoint_exists) u ≤ 1 :=
  setup.productDGF_proxFunction_le_one (Classical.choose setup.initialPoint_exists) u

private theorem mixed_prox_gamma_step_bound_of_three_point_and_dual_support
    (z y : setup.InteriorPoint) (x : setup.Point) (g : Ambient EX EY) (γ : ℝ)
    (hγ_nonneg : 0 ≤ γ)
    (hthree :
      γ * ⟪g, y.1 - x.1⟫_ℝ +
          setup.proxFunction z (setup.interiorPointToPoint y) ≤
        setup.proxFunction z x - setup.proxFunction y x)
    (hsupport :
      ⟪g, z.1 - y.1⟫_ℝ ≤
        setup.productDualNorm g * setup.productNorm (z.1 - y.1))
    (hlower :
      (1 / 2 : ℝ) * setup.productNorm (z.1 - y.1) ^ 2 ≤
        setup.proxFunction z (setup.interiorPointToPoint y)) :
    γ * ⟪g, z.1 - x.1⟫_ℝ ≤
      setup.proxFunction z x - setup.proxFunction y x +
        (1 / 2 : ℝ) * γ ^ 2 * setup.productDualNorm g ^ 2 := by
  have hscaled_support :
      γ * ⟪g, z.1 - y.1⟫_ℝ ≤
        γ * (setup.productDualNorm g * setup.productNorm (z.1 - y.1)) := by
    exact mul_le_mul_of_nonneg_left hsupport hγ_nonneg
  have hyoung :
      γ * (setup.productDualNorm g * setup.productNorm (z.1 - y.1)) -
          (1 / 2 : ℝ) * setup.productNorm (z.1 - y.1) ^ 2 ≤
        (1 / 2 : ℝ) * γ ^ 2 * setup.productDualNorm g ^ 2 := by
    nlinarith [sq_nonneg (γ * setup.productDualNorm g - setup.productNorm (z.1 - y.1))]
  have hscaled_young :
      γ * ⟪g, z.1 - y.1⟫_ℝ -
          setup.proxFunction z (setup.interiorPointToPoint y) ≤
        (1 / 2 : ℝ) * γ ^ 2 * setup.productDualNorm g ^ 2 := by
    nlinarith
  have hsplit :
      γ * ⟪g, z.1 - x.1⟫_ℝ =
        γ * ⟪g, z.1 - y.1⟫_ℝ + γ * ⟪g, y.1 - x.1⟫_ℝ := by
    have hvec : z.1 - x.1 = (z.1 - y.1) + (y.1 - x.1) := by
      abel
    rw [hvec, inner_add_right]
    ring
  rw [hsplit]
  nlinarith

private theorem mixed_prox_three_point_of_variational
    (z y : setup.InteriorPoint) (u : setup.Point) (g : Ambient EX EY) (γ : ℝ)
    (hvar :
      0 ≤
        ⟪γ • g + setup.productDGFGradient y - setup.productDGFGradient z,
          u.1 - y.1⟫_ℝ) :
    γ * ⟪g, y.1 - u.1⟫_ℝ +
        setup.proxFunction z (setup.interiorPointToPoint y) ≤
      setup.proxFunction z u - setup.proxFunction y u := by
  have hvar_exp :
      0 ≤
        γ * ⟪g, u.1 - y.1⟫_ℝ +
          (⟪setup.productDGFGradient y, u.1 - y.1⟫_ℝ -
            ⟪setup.productDGFGradient z, u.1 - y.1⟫_ℝ) := by
    have hinner :
        ⟪γ • g + setup.productDGFGradient y - setup.productDGFGradient z,
          u.1 - y.1⟫_ℝ =
          γ * ⟪g, u.1 - y.1⟫_ℝ +
            (⟪setup.productDGFGradient y, u.1 - y.1⟫_ℝ -
              ⟪setup.productDGFGradient z, u.1 - y.1⟫_ℝ) := by
      rw [inner_sub_left, inner_add_left, real_inner_smul_left]
      ring
    simpa [hinner] using hvar
  have hgamma_le :
      γ * ⟪g, y.1 - u.1⟫_ℝ ≤
        ⟪setup.productDGFGradient y, u.1 - y.1⟫_ℝ -
          ⟪setup.productDGFGradient z, u.1 - y.1⟫_ℝ := by
    have hneg : ⟪g, y.1 - u.1⟫_ℝ = -⟪g, u.1 - y.1⟫_ℝ := by
      have hvec : y.1 - u.1 = -(u.1 - y.1) := by
        abel
      rw [hvec, inner_neg_right]
    rw [hneg]
    nlinarith
  rw [setup.proxFunction_def z (setup.interiorPointToPoint y),
    setup.proxFunction_def z u, setup.proxFunction_def y u]
  have hy : (setup.interiorPointToPoint y).1 = y.1 := rfl
  rw [hy]
  have hgz_split :
      ⟪setup.productDGFGradient z, u.1 - z.1⟫_ℝ =
        ⟪setup.productDGFGradient z, u.1 - y.1⟫_ℝ +
          ⟪setup.productDGFGradient z, y.1 - z.1⟫_ℝ := by
    have hvec : u.1 - z.1 = (u.1 - y.1) + (y.1 - z.1) := by
      abel
    rw [hvec, inner_add_right]
  rw [hgz_split]
  nlinarith

private theorem sourceDGFCore_of_mem_carrierSubdifferential
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X : Set E} {nu : {x : E // x ∈ X} → ℝ}
    {z : {x : E // x ∈ X}} {g : E}
    (hg : g ∈ SOptLib.carrierSubdifferential (X := X) nu z) :
    z.1 ∈ sourceDGFCore X nu := by
  refine ⟨z.2, -g, ?_⟩
  intro u
  have hsupport : nu z + ⟪g, u.1 - z.1⟫_ℝ ≤ nu u := by
    simpa using (SOptLib.mem_carrierSubdifferential_iff.mp hg u)
  have hsupport' : nu z + (⟪g, u.1⟫_ℝ - ⟪g, z.1⟫_ℝ) ≤ nu u := by
    simpa [inner_sub_right] using hsupport
  calc
    ⟪-g, z.1⟫_ℝ + nu z = nu z - ⟪g, z.1⟫_ℝ := by
      rw [inner_neg_left]
      ring
    _ ≤ nu u - ⟪g, u.1⟫_ℝ := by
      linarith
    _ = ⟪-g, u.1⟫_ℝ + nu u := by
      rw [inner_neg_left]
      ring

private theorem exists_carrierSubdifferential_of_sourceDGFCore
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X : Set E} {nu : {x : E // x ∈ X} → ℝ}
    {x : E} (hx : x ∈ sourceDGFCore X nu) :
    ∃ hxX : x ∈ X, ∃ g : E,
      g ∈ SOptLib.carrierSubdifferential (X := X) nu ⟨x, hxX⟩ := by
  rcases hx with ⟨hxX, p, hmin⟩
  refine ⟨hxX, -p, ?_⟩
  rw [SOptLib.mem_carrierSubdifferential_iff]
  intro y
  have hymin := hmin y
  have hymin' : nu ⟨x, hxX⟩ - nu y ≤ ⟪p, y.1⟫_ℝ - ⟪p, x⟫_ℝ := by
    linarith
  have hinner : ⟪-p, y.1 - x⟫_ℝ = ⟪p, x⟫_ℝ - ⟪p, y.1⟫_ℝ := by
    rw [inner_neg_left, inner_sub_right]
    ring
  rw [hinner]
  linarith

private theorem productDGF_totalize_segment_hasDerivWithinAt_zero
    (y : setup.InteriorPoint) (u : setup.Point) :
    HasDerivWithinAt
      (fun t : ℝ =>
        SOptLib.totalizeOn setup.jointCarrier setup.productPotential
          (AffineMap.lineMap y.1 u.1 t))
      ⟪setup.productDGFGradient y, u.1 - y.1⟫_ℝ
      (Set.Icc (0 : ℝ) 1) 0 := by
  let s : Set ℝ := Set.Icc (0 : ℝ) 1
  let line : ℝ → Ambient EX EY := fun t => AffineMap.lineMap y.1 u.1 t
  let d : Ambient EX EY := u.1 - y.1
  have hgrad_core :
      HasGradientWithinAt
        (SOptLib.totalizeOn setup.jointCarrier setup.productPotential)
        (sourceDGFGradient setup.jointCarrier setup.productPotential y.1)
        setup.jointCarrier y.1 :=
    setup.productDGF_modulus_one.gradient_hasGradientWithinAt y.2
  have hline_deriv_s : HasDerivWithinAt line d s 0 := by
    simpa [line, d] using
      (AffineMap.hasDerivWithinAt_lineMap (a := y.1) (b := u.1)
        (s := s) (x := (0 : ℝ)))
  have hmaps :
      Set.MapsTo line s setup.jointCarrier := by
    intro t ht
    exact setup.jointCarrier_convex.lineMap_mem (Classical.choose y.2) u.2 ht
  have hbase : y.1 = line 0 := by
    simp [line, AffineMap.lineMap_apply_module']
  have hν_s :
      HasDerivWithinAt
        (fun t : ℝ =>
          SOptLib.totalizeOn setup.jointCarrier setup.productPotential (line t))
        ⟪setup.productDGFGradient y, d⟫_ℝ s 0 := by
    have hcomp := hgrad_core.hasFDerivWithinAt.comp_hasDerivWithinAt_of_eq
      0 hline_deriv_s hmaps hbase
    simpa [Function.comp_def, d, Setup.productDGFGradient] using hcomp
  simpa [line, d, s] using hν_s

private theorem mirror_step_objective_first_variation_nonneg
    (z : setup.InteriorPoint) (g : Ambient EX EY) (γ : ℝ) (u : setup.Point) :
    0 ≤
      γ * ⟪g, u.1 - (setup.mirrorStep z g γ).1⟫_ℝ +
        (⟪setup.productDGFGradient (setup.mirrorStep z g γ),
            u.1 - (setup.mirrorStep z g γ).1⟫_ℝ -
          ⟪setup.productDGFGradient z,
            u.1 - (setup.mirrorStep z g γ).1⟫_ℝ) := by
  classical
  let y : setup.InteriorPoint := setup.mirrorStep z g γ
  have hmin :
      IsMinOn
        (fun v : setup.Point =>
          γ * ⟪g, v.1⟫_ℝ +
            (setup.productPotential v -
              setup.productPotential (setup.interiorPointToPoint z) -
              ⟪setup.productDGFGradient z, v.1 - z.1⟫_ℝ))
        Set.univ (setup.interiorPointToPoint y) := by
    simpa [y, Setup.mirrorStepObjective, SOptLib.literalMirrorObjective,
      setup.proxFunction_def, setup.mirrorStep_toPoint z g γ] using
      setup.mirrorStepPoint_isMinOn z g γ
  have hfirst :=
    SOptLib.sourceDGFProx_first_variation_nonneg_of_isMinOn_linear
      (X := setup.jointCarrier)
      (Xcore := sourceDGFCore setup.jointCarrier setup.productPotential)
      (hX_convex := setup.jointCarrier_convex)
      (hcore_subset := by
        intro x hx
        exact Classical.choose hx)
      (nu := setup.productPotential)
      (grad := sourceDGFGradient setup.jointCarrier setup.productPotential)
      (z := z) (y := y) (g := g) (γ := γ) (x := u)
      (hgrad_y := setup.productDGF_modulus_one.gradient_hasGradientWithinAt y.2)
      (hmin := hmin)
  simpa [y, Setup.productDGFGradient] using hfirst

private theorem mirror_step_variational_inequality
    (z : setup.InteriorPoint) (g : Ambient EX EY) (γ : ℝ) (u : setup.Point) :
    0 ≤
      ⟪γ • g + setup.productDGFGradient (setup.mirrorStep z g γ) -
          setup.productDGFGradient z,
        u.1 - (setup.mirrorStep z g γ).1⟫_ℝ := by
  classical
  let y : setup.InteriorPoint := setup.mirrorStep z g γ
  have hmin :
      IsMinOn
        (fun v : setup.Point =>
          γ * ⟪g, v.1⟫_ℝ +
            (setup.productPotential v -
              setup.productPotential (setup.interiorPointToPoint z) -
              ⟪setup.productDGFGradient z, v.1 - z.1⟫_ℝ))
        Set.univ (setup.interiorPointToPoint y) := by
    simpa [y, Setup.mirrorStepObjective, SOptLib.literalMirrorObjective,
      setup.proxFunction_def, setup.mirrorStep_toPoint z g γ] using
      setup.mirrorStepPoint_isMinOn z g γ
  simpa [y, Setup.productDGFGradient, Setup.interiorPointToPoint,
    sourceDGFCoreToCarrier] using
    (SOptLib.sourceDGF_mirrorStep_variational_inequality
      (X := setup.jointCarrier)
      (Xcore := sourceDGFCore setup.jointCarrier setup.productPotential)
      (hX_convex := setup.jointCarrier_convex)
      (hcore_subset := by
        intro x hx
        exact Classical.choose hx)
      (nu := setup.productPotential)
      (grad := sourceDGFGradient setup.jointCarrier setup.productPotential)
      (z := z) (step := y) (g := g) (γ := γ) (u := u)
      (hgrad_step := setup.productDGF_modulus_one.gradient_hasGradientWithinAt y.2)
      (hmin := hmin))

private theorem bregman_lower_bound_of_strongConvexOnWithSeminorm_hasGradientWithinAt
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {X : Set E} {ν : E → ℝ} {p : Seminorm ℝ E} {z x grad : E}
    (hX : Convex ℝ X) (hνgrad : HasGradientWithinAt ν grad X z)
    (hstrong :
      ∀ ⦃y⦄, y ∈ X → ∀ ⦃w⦄, w ∈ X → ∀ ⦃a b : ℝ⦄,
        0 ≤ a → 0 ≤ b → a + b = 1 →
          ν (a • y + b • w) ≤
            a * ν y + b * ν w - (1 : ℝ) / 2 * a * b * p (y - w) ^ 2)
    (hz : z ∈ X) (hx : x ∈ X) :
    (1 / 2 : ℝ) * p (x - z) ^ 2 ≤
      ν x - (ν z + ⟪grad, x - z⟫_ℝ) := by
  let d : E := x - z
  let s : Set ℝ := Set.Icc (0 : ℝ) 1
  let line : ℝ → E := fun t => AffineMap.lineMap z x t
  let q : ℝ := p (x - z) ^ 2
  let A : ℝ := ν x - ν z - (1 / 2 : ℝ) * q
  let r : ℝ → ℝ := fun t =>
    t * A + (1 / 2 : ℝ) * t ^ 2 * q - (ν (line t) - ν z)
  have hline_mem : ∀ t ∈ s, line t ∈ X := by
    intro t ht
    exact hX.lineMap_mem hz hx ht
  have hmaps : Set.MapsTo line s X := by
    intro t ht
    exact hline_mem t ht
  have hmin : ∀ t ∈ s, r 0 ≤ r t := by
    intro t ht
    have ht0 : 0 ≤ t := ht.1
    have ht1 : t ≤ 1 := ht.2
    have h1t : 0 ≤ 1 - t := sub_nonneg.mpr ht1
    have hsum : 1 - t + t = 1 := by ring
    have hsc := hstrong hz hx h1t ht0 hsum
    have hpnorm : p (z - x) = p (x - z) := by
      have hsub : z - x = -(x - z) := by abel
      rw [hsub, map_neg_eq_map]
    have hsc_line :
        ν (line t) ≤
          (1 - t) * ν z + t * ν x - (1 : ℝ) / 2 * (1 - t) * t * q := by
      simpa [line, q, hpnorm, AffineMap.lineMap_apply_module] using hsc
    have hr0 : r 0 = 0 := by simp [r, line]
    rw [hr0]
    dsimp [r, A]
    nlinarith [hsc_line]
  have hline_deriv : HasDerivWithinAt line d s 0 := by
    simpa [line, d] using
      (AffineMap.hasDerivWithinAt_lineMap (a := z) (b := x)
        (s := s) (x := (0 : ℝ)))
  have hνline : HasDerivWithinAt (fun t => ν (line t))
      ⟪grad, d⟫_ℝ s 0 := by
    simpa [Function.comp_def] using
      hνgrad.hasFDerivWithinAt.comp_hasDerivWithinAt_of_eq 0 hline_deriv hmaps
        (by simp [line])
  have hAderiv : HasDerivWithinAt (fun t : ℝ => t * A) A s 0 := by
    simpa using (hasDerivWithinAt_id (x := (0 : ℝ)) (s := s)).mul_const A
  have hquad : HasDerivWithinAt (fun t : ℝ => (1 / 2 : ℝ) * t ^ 2 * q) 0 s 0 := by
    have hp : HasDerivWithinAt (fun t : ℝ => t ^ 2)
        (2 * (0 : ℝ) ^ (2 - 1)) s 0 := by
      simpa using (hasDerivWithinAt_pow (2 : ℕ) (x := (0 : ℝ)) (s := s))
    have h := (hp.const_mul (1 / 2 : ℝ)).mul_const q
    convert h using 1
    ring
  have hνsub : HasDerivWithinAt (fun t : ℝ => ν (line t) - ν z)
      ⟪grad, d⟫_ℝ s 0 := by
    simpa using hνline.sub_const (ν z)
  have hrderiv : HasDerivWithinAt r
      (A - ⟪grad, d⟫_ℝ) s 0 := by
    have hsum := hAderiv.add hquad
    have h := hsum.sub hνsub
    convert h using 1
    ring
  have hnonneg : 0 ≤ A - ⟪grad, d⟫_ℝ :=
    right_derivative_nonneg_of_min_on_Icc (φ := r) hrderiv hmin
  dsimp [A, q, d] at hnonneg
  linarith

private theorem bregman_lower_bound_of_monotoneGradient_hasGradientWithinAt_on_convex_set
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {C : Set E} {ν : E → ℝ} {p : Seminorm ℝ E} {grad : E → E}
    (hC : Convex ℝ C)
    (hgrad : ∀ x, x ∈ C → HasGradientWithinAt ν (grad x) C x)
    (hgrad_cont : Continuous fun x : {x // x ∈ C} => grad x.1)
    (hmono : ∀ x, x ∈ C → ∀ y, y ∈ C →
      p (y - x) ^ 2 ≤ ⟪grad y - grad x, y - x⟫_ℝ)
    {z x : E} (hz : z ∈ C) (hx : x ∈ C) :
    (1 / 2 : ℝ) * p (x - z) ^ 2 ≤
      ν x - (ν z + ⟪grad z, x - z⟫_ℝ) := by
  /-
  Monotone-gradient-to-Bregman bridge on the source core.  This is the
  Section 3.2 route needed by the saddle-point prox coercivity proof; the
  existing reusable lower-bound API currently consumes Jensen strong convexity,
  while the source DGF contract records the equivalent differentiable
  monotone-gradient inequality.
  -/
  let d : E := x - z
  let s : Set ℝ := Set.Icc (0 : ℝ) 1
  let line : ℝ → E := fun t => AffineMap.lineMap z x t
  let Fseg : ℝ → ℝ := fun t => -ν (line t)
  let phi : ℝ → ℝ := fun t => -⟪grad (line t), d⟫_ℝ
  let A : ℝ := -⟪grad z, d⟫_ℝ
  let B : ℝ := -(p d ^ 2)
  have hline_mem : ∀ t ∈ s, line t ∈ C := by
    intro t ht
    exact hC.lineMap_mem hz hx ht
  have hmaps : Set.MapsTo line s C := by
    intro t ht
    exact hline_mem t ht
  have hderiv : ∀ (t : ℝ) (ht : t ∈ s),
      HasDerivWithinAt Fseg (phi t) s t := by
    intro t ht
    have hline_deriv : HasDerivWithinAt line d s t := by
      simpa [line, d] using
        (AffineMap.hasDerivWithinAt_lineMap (a := z) (b := x)
          (s := s) (x := t))
    have hnu : HasDerivWithinAt (fun u : ℝ => ν (line u))
        ⟪grad (line t), d⟫_ℝ s t := by
      have hfseg : HasDerivWithinAt (fun u : ℝ => ν (line u))
          ((InnerProductSpace.toDual ℝ E (grad (line t))) d) s t := by
        simpa [Function.comp_def] using
          (hgrad (line t) (hline_mem t ht)).hasFDerivWithinAt
            |>.comp_hasDerivWithinAt_of_eq t hline_deriv hmaps (by simp [line])
      simpa using hfseg
    simpa [Fseg, phi] using hnu.neg
  have hbound : ∀ (t : ℝ) (ht : t ∈ s),
      phi t ≤ A + B * t := by
    intro t ht
    by_cases htzero : t = 0
    · subst t
      simp [phi, A, B, line]
    · have ht_nonneg : 0 ≤ t := ht.1
      have htpos : 0 < t := lt_of_le_of_ne ht_nonneg (Ne.symm htzero)
      have hseg_sub : line t - z = t • d := by
        simp [line, d, AffineMap.lineMap_apply_module']
      have hprimal_line : p (line t - z) = t * p d := by
        rw [hseg_sub]
        simp [map_smul_eq_mul, Real.norm_of_nonneg ht_nonneg]
      have hinner_line :
          ⟪grad (line t) - grad z, line t - z⟫_ℝ =
            t * ⟪grad (line t) - grad z, d⟫_ℝ := by
        rw [hseg_sub]
        simp [inner_smul_right]
      have hm := hmono z hz (line t) (hline_mem t ht)
      have hm' : (t * p d) ^ 2 ≤
          t * ⟪grad (line t) - grad z, d⟫_ℝ := by
        calc
          (t * p d) ^ 2 = p (line t - z) ^ 2 := by rw [hprimal_line]
          _ ≤ ⟪grad (line t) - grad z, line t - z⟫_ℝ := hm
          _ = t * ⟪grad (line t) - grad z, d⟫_ℝ := hinner_line
      have hpd_nonneg : 0 ≤ p d := apply_nonneg p d
      have hdiff_lower : p d ^ 2 * t ≤
          ⟪grad (line t) - grad z, d⟫_ℝ := by
        nlinarith [hm', htpos, hpd_nonneg]
      have hinner_diff :
          ⟪grad (line t) - grad z, d⟫_ℝ =
            ⟪grad (line t), d⟫_ℝ - ⟪grad z, d⟫_ℝ := by
        simp [inner_sub_left]
      dsimp [phi, A, B]
      nlinarith
  have hscalar : Fseg 1 ≤ Fseg 0 + A + B / 2 := by
    exact le_value_add_of_hasDerivWithinAt_le_affine_on_Icc Fseg phi A B hderiv hbound
  dsimp [Fseg, A, B, d] at hscalar ⊢
  simp [line] at hscalar
  nlinarith

private theorem sourceDGFModulusOne.monotone
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {X : Set E} {p : E → ℝ} {nu : {x : E // x ∈ X} → ℝ}
    [SourceDGFGradientSelector X nu]
    (hdgf : sourceDGFModulusOne X p nu) :
    ∀ x, x ∈ sourceDGFCore X nu → ∀ x', x' ∈ sourceDGFCore X nu →
      p (x' - x) ^ 2 ≤
        ⟪sourceDGFGradient X nu x' - sourceDGFGradient X nu x, x' - x⟫_ℝ := by
  exact hdgf.monotone

private theorem _root_.StochasticConvexConcaveSaddlePoint.sourceDGFModulusOne.bregman_lower_bound_core
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {X : Set E} {p : Seminorm ℝ E} {nu : {x : E // x ∈ X} → ℝ}
    [SourceDGFGradientSelector X nu]
    (hdgf : sourceDGFModulusOne X p nu)
    (z y : SourceDGFCorePoint X nu) :
    (1 / 2 : ℝ) * p (y.1 - z.1) ^ 2 ≤
      SOptLib.totalizeOn X nu y.1 -
        (SOptLib.totalizeOn X nu z.1 +
          ⟪sourceDGFGradient X nu z.1, y.1 - z.1⟫_ℝ) := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact bregman_lower_bound_of_monotoneGradient_hasGradientWithinAt_on_convex_set
    (C := sourceDGFCore X nu) (ν := SOptLib.totalizeOn X nu) (p := p)
    (grad := fun x => sourceDGFGradient X nu x)
    hdgf.core_convex
    (by
      intro x hx
      exact (hdgf.gradient_hasGradientWithinAt hx).congr_mono
        (by intro y hy; rfl) rfl
        (by intro y hy; exact Classical.choose hy))
    hdgf.selectedGradient_continuous
    (by intro x hx y hy; exact hdgf.monotone x hx y hy) z.2 y.2

private theorem sourceDGFProx_lower_bound_between_core_points_of_seminorm
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {X : Set E} {p : Seminorm ℝ E} {nu : {x : E // x ∈ X} → ℝ}
    [SourceDGFGradientSelector X nu]
    (hdgf : sourceDGFModulusOne X p nu)
    (z y : SourceDGFCorePoint X nu) :
    (1 / 2 : ℝ) * p (y.1 - z.1) ^ 2 ≤
      sourceDGFProx nu z (sourceDGFCoreToCarrier y) := by
  have hcore :
      (1 / 2 : ℝ) * p (y.1 - z.1) ^ 2 ≤
        SOptLib.totalizeOn X nu y.1 -
          (SOptLib.totalizeOn X nu z.1 +
            ⟪sourceDGFGradient X nu z.1, y.1 - z.1⟫_ℝ) := by
    exact sourceDGFModulusOne.bregman_lower_bound_core hdgf z y
  have hy_total :
      SOptLib.totalizeOn X nu y.1 = nu (sourceDGFCoreToCarrier y) := by
    rw [SOptLib.totalizeOn_of_mem X nu (Classical.choose y.2)]
    congr
  have hz_total :
      SOptLib.totalizeOn X nu z.1 = nu (sourceDGFCoreToCarrier z) := by
    rw [SOptLib.totalizeOn_of_mem X nu (Classical.choose z.2)]
    congr
  calc
    (1 / 2 : ℝ) * p (y.1 - z.1) ^ 2 ≤
        SOptLib.totalizeOn X nu y.1 -
          (SOptLib.totalizeOn X nu z.1 +
            ⟪sourceDGFGradient X nu z.1, y.1 - z.1⟫_ℝ) := hcore
    _ = sourceDGFProx nu z (sourceDGFCoreToCarrier y) := by
      simp [sourceDGFProx, hy_total, hz_total, sourceDGFCoreToCarrier]
      ring

private theorem productNorm_neg (v : Ambient EX EY) :
    setup.productNorm (-v) = setup.productNorm v := by
  rw [Setup.productNorm_def, Setup.productNorm_def]
  simp

private theorem productDualNorm_neg (v : Ambient EX EY) :
    setup.productDualNorm (-v) = setup.productDualNorm v := by
  rw [Setup.productDualNorm_def, Setup.productDualNorm_def]
  simp

private theorem proxFunction_nonneg
    (z : setup.InteriorPoint) (u : setup.Point) :
    0 ≤ setup.proxFunction z u := by
  simpa [Setup.proxFunction, sourceDGFProx, Setup.interiorPointToPoint,
    sourceDGFCoreToCarrier, Setup.productDGFGradient] using
    (SOptLib.sourceDGFProx_nonneg
      (X := setup.jointCarrier)
      (Xcore := sourceDGFCore setup.jointCarrier setup.productPotential)
      (nu := setup.productPotential)
      (grad := fun x => sourceDGFGradient setup.jointCarrier setup.productPotential x)
      (hcore_subset := by
        intro x hx
        exact Classical.choose hx)
      setup.productDGF_convexOn
      (z := z) (u := u)
      (setup.productDGF_modulus_one.gradient_hasGradientWithinAt z.2))

private theorem product_prox_lower_bound_between_core_points
    (z y : setup.InteriorPoint) :
    (1 / 2 : ℝ) * setup.productNorm (z.1 - y.1) ^ 2 ≤
      setup.proxFunction z (setup.interiorPointToPoint y) := by
  classical
  have hzxy :
      z.1.fst ∈ sourceDGFCore setup.X setup.nuX ∧
        z.1.snd ∈ sourceDGFCore setup.Y setup.nuY := by
    simpa [setup.productDGF_core_eq] using z.2
  have hyxy :
      y.1.fst ∈ sourceDGFCore setup.X setup.nuX ∧
        y.1.snd ∈ sourceDGFCore setup.Y setup.nuY := by
    simpa [setup.productDGF_core_eq] using y.2
  let zX : SourceDGFCorePoint setup.X setup.nuX := ⟨z.1.fst, hzxy.1⟩
  let yX : SourceDGFCorePoint setup.X setup.nuX := ⟨y.1.fst, hyxy.1⟩
  let zY : SourceDGFCorePoint setup.Y setup.nuY := ⟨z.1.snd, hzxy.2⟩
  let yY : SourceDGFCorePoint setup.Y setup.nuY := ⟨y.1.snd, hyxy.2⟩
  have hXlower :
      (1 / 2 : ℝ) * setup.normX (y.1.fst - z.1.fst) ^ 2 ≤
        sourceDGFProx setup.nuX zX (sourceDGFCoreToCarrier yX) := by
    simpa [zX, yX] using
      sourceDGFProx_lower_bound_between_core_points_of_seminorm
        (hdgf := setup.hnuX_dgf_mod_one) zX yX
  have hYlower :
      (1 / 2 : ℝ) * setup.normY (y.1.snd - z.1.snd) ^ 2 ≤
        sourceDGFProx setup.nuY zY (sourceDGFCoreToCarrier yY) := by
    simpa [zY, yY] using
      sourceDGFProx_lower_bound_between_core_points_of_seminorm
        (hdgf := setup.hnuY_dgf_mod_one) zY yY
  have hxPoint_eq :
      setup.xPoint (setup.interiorPointToPoint y) = sourceDGFCoreToCarrier yX := by
    ext
    simp [Setup.xPoint, Setup.interiorPointToPoint, sourceDGFCoreToCarrier, yX]
  have hyPoint_eq :
      setup.yPoint (setup.interiorPointToPoint y) = sourceDGFCoreToCarrier yY := by
    ext
    simp [Setup.yPoint, Setup.interiorPointToPoint, sourceDGFCoreToCarrier, yY]
  have hprox_eq :
      setup.proxFunction z (setup.interiorPointToPoint y) =
        sourceDGFProx setup.nuX zX (sourceDGFCoreToCarrier yX) / (2 * setup.DX ^ 2) +
          sourceDGFProx setup.nuY zY (sourceDGFCoreToCarrier yY) /
            (2 * setup.DY ^ 2) := by
    rw [Setup.proxFunction, setup.productDGF_prox_eq_scaled_sum]
    simp [zX, zY, hxPoint_eq, hyPoint_eq]
  have hDXden_nonneg : 0 ≤ 2 * setup.DX ^ 2 := by positivity
  have hDYden_nonneg : 0 ≤ 2 * setup.DY ^ 2 := by positivity
  have hscaled :
      ((1 / 2 : ℝ) * setup.normX (y.1.fst - z.1.fst) ^ 2) /
            (2 * setup.DX ^ 2) +
          ((1 / 2 : ℝ) * setup.normY (y.1.snd - z.1.snd) ^ 2) /
            (2 * setup.DY ^ 2) ≤
        setup.proxFunction z (setup.interiorPointToPoint y) := by
    rw [hprox_eq]
    exact add_le_add
      (div_le_div_of_nonneg_right hXlower hDXden_nonneg)
      (div_le_div_of_nonneg_right hYlower hDYden_nonneg)
  have hnorm :
      setup.productNorm (z.1 - y.1) = setup.productNorm (y.1 - z.1) := by
    have hsub : z.1 - y.1 = -(y.1 - z.1) := by
      abel
    rw [hsub, setup.productNorm_neg]
  rw [hnorm]
  rw [Setup.productNorm_def, Real.sq_sqrt]
  · calc
      (1 / 2 : ℝ) *
          (setup.normX ((y.1 - z.1).fst) ^ 2 / (2 * setup.DX ^ 2) +
            setup.normY ((y.1 - z.1).snd) ^ 2 / (2 * setup.DY ^ 2)) =
        ((1 / 2 : ℝ) * setup.normX (y.1.fst - z.1.fst) ^ 2) /
            (2 * setup.DX ^ 2) +
          ((1 / 2 : ℝ) * setup.normY (y.1.snd - z.1.snd) ^ 2) /
            (2 * setup.DY ^ 2) := by
          simp
          ring
      _ ≤ setup.proxFunction z (setup.interiorPointToPoint y) := hscaled
  · positivity

private theorem mirrorStep_one_step_bound
    (z : setup.InteriorPoint) (g : Ambient EX EY) (γ : ℝ)
    (hγ_nonneg : 0 ≤ γ) (u : setup.Point) :
    γ * ⟪g, z.1 - u.1⟫_ℝ ≤
      setup.proxFunction z u -
          setup.proxFunction (setup.mirrorStep z g γ) u +
        (1 / 2 : ℝ) * γ ^ 2 * setup.productDualNorm g ^ 2 := by
  classical
  let y : setup.InteriorPoint := setup.mirrorStep z g γ
  simpa [y] using
    (SOptLib.sourceDGF_mirrorStep_one_step_bound
      (V := setup.proxFunction)
      (evalBase := fun v : setup.InteriorPoint => v.1)
      (evalCompare := fun v : setup.Point => v.1)
      (grad := setup.productDGFGradient)
      (toCompare := setup.interiorPointToPoint)
      (primalNorm := setup.productNorm)
      (dualNorm := setup.productDualNorm)
      (step := fun z g γ => setup.mirrorStep z g γ)
      (z := z) (x := u) (g := g) (γ := γ)
      hγ_nonneg
      (by
        simpa [y] using mirror_step_variational_inequality (setup := setup) z g γ u)
      (by
        change setup.proxFunction z u =
          setup.proxFunction z (setup.interiorPointToPoint y) +
            ⟪setup.productDGFGradient y - setup.productDGFGradient z, u.1 - y.1⟫_ℝ +
              setup.proxFunction y u
        rw [setup.proxFunction_def z u,
          setup.proxFunction_def z (setup.interiorPointToPoint y),
          setup.proxFunction_def y u]
        have hy : (setup.interiorPointToPoint y).1 = y.1 := rfl
        rw [hy]
        have hsplit :
            ⟪setup.productDGFGradient z, u.1 - z.1⟫_ℝ =
              ⟪setup.productDGFGradient z, u.1 - y.1⟫_ℝ +
                ⟪setup.productDGFGradient z, y.1 - z.1⟫_ℝ := by
          have hvec : u.1 - z.1 = (u.1 - y.1) + (y.1 - z.1) := by
            abel
          rw [hvec, inner_add_right]
        rw [hsplit]
        rw [inner_sub_left]
        ring)
      (by
        have habs :=
          abs_inner_le_productDualNorm_mul_productNorm (setup := setup) g
            (z.1 - y.1)
        exact (le_abs_self _).trans habs)
      (by
        exact product_prox_lower_bound_between_core_points (setup := setup) z y))

private theorem paper_time_stochastic_one_step_bound
    (t : Time) (ω : setup.SamplePath) (u : setup.Point) :
    setup.gamma t *
        ⟪setup.stochasticOracle (setup.iterate t ω) (setup.sampleAt t ω),
          (setup.iterate t ω).1 - u.1⟫_ℝ ≤
      setup.proxFunction (setup.iterateCoreProcess (t.1 - 1) ω) u -
          setup.proxFunction (setup.iterateCoreProcess t.1 ω) u +
        (1 / 2 : ℝ) * setup.gamma t ^ 2 *
          setup.productDualNorm
            (setup.stochasticOracle (setup.iterate t ω) (setup.sampleAt t ω)) ^ 2 := by
  classical
  have ht_nat : t.1 - 1 + 1 = t.1 := Nat.sub_add_cancel t.2
  have ht_time : SOptLib.natSuccPositiveTime (t.1 - 1) = t := by
    apply Subtype.ext
    simpa [SOptLib.natSuccPositiveTime] using ht_nat
  have hnext :
      setup.mirrorStep (setup.iterateCoreProcess (t.1 - 1) ω)
          (setup.stochasticOracle (setup.iterate t ω) (setup.sampleAt t ω))
          (setup.gamma t) =
        setup.iterateCoreProcess t.1 ω := by
    calc
      setup.mirrorStep (setup.iterateCoreProcess (t.1 - 1) ω)
          (setup.stochasticOracle (setup.iterate t ω) (setup.sampleAt t ω))
          (setup.gamma t) =
          setup.iterateCoreProcess (t.1 - 1 + 1) ω := by
            rw [setup.iterateCoreProcess_succ (t.1 - 1) ω]
            simp [Setup.iterate, Setup.iterateProcess, ht_time]
      _ = setup.iterateCoreProcess t.1 ω := by rw [ht_nat]
  have h :=
    setup.mirrorStep_one_step_bound
      (setup.iterateCoreProcess (t.1 - 1) ω)
      (setup.stochasticOracle (setup.iterate t ω) (setup.sampleAt t ω))
      (setup.gamma t) (le_of_lt (setup.hgamma_pos t)) u
  rw [hnext] at h
  simpa [Setup.iterate, Setup.iterateProcess] using h

private theorem paper_time_auxiliary_delta_one_step_bound
    (t : Time) (ω : setup.SamplePath) (u : setup.Point) :
    setup.gamma t *
        ⟪setup.oracleNoise t ω, u.1 - (setup.auxiliaryIterate t ω).1⟫_ℝ ≤
      setup.proxFunction (setup.auxiliaryCoreProcess (t.1 - 1) ω) u -
          setup.proxFunction (setup.auxiliaryCoreProcess t.1 ω) u +
        (1 / 2 : ℝ) * setup.gamma t ^ 2 *
          setup.productDualNorm (setup.oracleNoise t ω) ^ 2 := by
  classical
  have ht_nat : t.1 - 1 + 1 = t.1 := Nat.sub_add_cancel t.2
  have ht_time : SOptLib.natSuccPositiveTime (t.1 - 1) = t := by
    apply Subtype.ext
    simpa [SOptLib.natSuccPositiveTime] using ht_nat
  have hnext :
      setup.mirrorStep (setup.auxiliaryCoreProcess (t.1 - 1) ω)
          (-(setup.oracleNoise t ω)) (setup.gamma t) =
        setup.auxiliaryCoreProcess t.1 ω := by
    calc
      setup.mirrorStep (setup.auxiliaryCoreProcess (t.1 - 1) ω)
          (-(setup.oracleNoise t ω)) (setup.gamma t) =
          setup.auxiliaryCoreProcess (t.1 - 1 + 1) ω := by
            rw [setup.auxiliaryCoreProcess_succ (t.1 - 1) ω]
            simp [ht_time]
      _ = setup.auxiliaryCoreProcess t.1 ω := by rw [ht_nat]
  have h :=
    setup.mirrorStep_one_step_bound
      (setup.auxiliaryCoreProcess (t.1 - 1) ω)
      (-(setup.oracleNoise t ω)) (setup.gamma t)
      (le_of_lt (setup.hgamma_pos t)) u
  rw [hnext] at h
  have hleft_eq :
      setup.gamma t *
          ⟪-(setup.oracleNoise t ω),
            (setup.auxiliaryCoreProcess (t.1 - 1) ω).1 - u.1⟫_ℝ =
        setup.gamma t *
          ⟪setup.oracleNoise t ω,
            u.1 - (setup.auxiliaryCoreProcess (t.1 - 1) ω).1⟫_ℝ := by
    have hsub :
        (setup.auxiliaryCoreProcess (t.1 - 1) ω).1 - u.1 =
          -(u.1 - (setup.auxiliaryCoreProcess (t.1 - 1) ω).1) := by
      abel
    have hinner :
        ⟪-(setup.oracleNoise t ω),
          (setup.auxiliaryCoreProcess (t.1 - 1) ω).1 - u.1⟫_ℝ =
          ⟪setup.oracleNoise t ω,
            u.1 - (setup.auxiliaryCoreProcess (t.1 - 1) ω).1⟫_ℝ := by
      rw [hsub]
      rw [inner_neg_left, inner_neg_right]
      ring
    exact congrArg (fun r : ℝ => setup.gamma t * r) hinner
  have hdual_eq :
      setup.productDualNorm (-(setup.oracleNoise t ω)) ^ 2 =
        setup.productDualNorm (setup.oracleNoise t ω) ^ 2 := by
    rw [productDualNorm_neg]
  rw [hleft_eq, hdual_eq] at h
  simpa [Setup.auxiliaryIterate, Setup.auxiliaryProcess,
    Setup.interiorPointToPoint, sourceDGFCoreToCarrier] using h

private theorem outputTimes_sum_sub_succ_le_first_of_terminal_nonneg
    (j : ℕ) (hj : 1 ≤ j) (a : Time → ℝ)
    (hterm : 0 ≤ a ⟨j + 1, Nat.succ_le_succ (Nat.zero_le j)⟩) :
    Finset.sum (outputTimes j) (fun t =>
        a t - a (SOptLib.positiveTimeSucc t)) ≤
      a SOptLib.positiveTimeOne := by
  classical
  exact outputWindow_sum_sub_succ_le_first_of_last_nonneg
    (times := outputTimes j) (a := a) (hstart := by norm_num) (hle := hj)
    (by
      intro φ
      simpa [outputTimes] using
        (SOptLib.sum_positiveTimeOutputWindowTimes_eq_Icc (α := ℝ) 1 j
          (by norm_num) hj φ))
    hterm

private theorem paper_time_combined_one_step_budget
    (t : Time) (ω : setup.SamplePath) (u : setup.Point) :
    setup.gamma t *
        ⟪setup.meanOracle (setup.iterate t ω),
          (setup.iterate t ω).1 - u.1⟫_ℝ ≤
      (setup.proxFunction (setup.iterateCoreProcess (t.1 - 1) ω) u -
          setup.proxFunction (setup.iterateCoreProcess t.1 ω) u) +
        (setup.proxFunction (setup.auxiliaryCoreProcess (t.1 - 1) ω) u -
          setup.proxFunction (setup.auxiliaryCoreProcess t.1 ω) u) +
        (1 / 2 : ℝ) * setup.gamma t ^ 2 *
          setup.productDualNorm
            (setup.stochasticOracle (setup.iterate t ω) (setup.sampleAt t ω)) ^ 2 +
        (1 / 2 : ℝ) * setup.gamma t ^ 2 *
          setup.productDualNorm (setup.oracleNoise t ω) ^ 2 -
        setup.gamma t *
          ⟪(setup.iterate t ω).1 - (setup.auxiliaryIterate t ω).1,
            setup.oracleNoise t ω⟫_ℝ := by
  classical
  exact
    combined_mean_oracle_one_step_budget_of_residual_auxiliary_bound
      (dualNorm := setup.productDualNorm) (γ := setup.gamma t)
      (zt := (setup.iterate t ω).1) (vt := (setup.auxiliaryIterate t ω).1)
      (u := u.1)
      (gt := setup.stochasticOracle (setup.iterate t ω) (setup.sampleAt t ω))
      (dt := setup.oracleNoise t ω)
      (mean := setup.meanOracle (setup.iterate t ω))
      (zDrop :=
        setup.proxFunction (setup.iterateCoreProcess (t.1 - 1) ω) u -
          setup.proxFunction (setup.iterateCoreProcess t.1 ω) u)
      (vDrop :=
        setup.proxFunction (setup.auxiliaryCoreProcess (t.1 - 1) ω) u -
          setup.proxFunction (setup.auxiliaryCoreProcess t.1 ω) u)
      (by
        rw [setup.oracleNoise_def t ω]
        abel)
      (by
        simpa using setup.paper_time_stochastic_one_step_bound t ω u)
      (by
        simpa using setup.paper_time_auxiliary_delta_one_step_bound t ω u)

private theorem maxRegretSum_pathwise_budget (j : ℕ) (ω : setup.SamplePath) :
    setup.maxRegretSum j ω ≤
      2 +
        (1 / 2 : ℝ) *
          Finset.sum (outputTimes j) (fun t =>
            setup.gamma t ^ 2 *
              (setup.productDualNorm
                (setup.stochasticOracle (setup.iterate t ω) (setup.sampleAt t ω))) ^ 2) +
        (1 / 2 : ℝ) *
          Finset.sum (outputTimes j) (fun t =>
            setup.gamma t ^ 2 *
              (setup.productDualNorm (setup.oracleNoise t ω)) ^ 2) -
        Finset.sum (outputTimes j) (fun t =>
          setup.gamma t *
            ⟪(setup.iterate t ω).1 - (setup.auxiliaryIterate t ω).1,
              setup.oracleNoise t ω⟫_ℝ) := by
  classical
  let u : setup.Point := setup.maxRegretPoint j ω
  let gap : Time → ℝ := fun t =>
    setup.gamma t *
      ⟪setup.meanOracle (setup.iterate t ω), (setup.iterate t ω).1 - u.1⟫_ℝ
  let dz : Time → ℝ := fun t =>
    setup.proxFunction (setup.iterateCoreProcess (t.1 - 1) ω) u -
      setup.proxFunction (setup.iterateCoreProcess t.1 ω) u
  let dv : Time → ℝ := fun t =>
    setup.proxFunction (setup.auxiliaryCoreProcess (t.1 - 1) ω) u -
      setup.proxFunction (setup.auxiliaryCoreProcess t.1 ω) u
  let q1 : Time → ℝ := fun t =>
    (1 / 2 : ℝ) *
      (setup.gamma t ^ 2 *
        setup.productDualNorm
          (setup.stochasticOracle (setup.iterate t ω) (setup.sampleAt t ω)) ^ 2)
  let q2 : Time → ℝ := fun t =>
    (1 / 2 : ℝ) *
      (setup.gamma t ^ 2 * setup.productDualNorm (setup.oracleNoise t ω) ^ 2)
  let correction : Time → ℝ := fun t =>
    setup.gamma t *
      ⟪(setup.iterate t ω).1 - (setup.auxiliaryIterate t ω).1,
        setup.oracleNoise t ω⟫_ℝ
  have htel :
      ∀ a : Time → ℝ,
        0 ≤ a ⟨j + 1, Nat.succ_le_succ (Nat.zero_le j)⟩ →
        a SOptLib.positiveTimeOne ≤ 1 →
        Finset.sum (outputTimes j) (fun t => a t - a (SOptLib.positiveTimeSucc t)) ≤
          1 := by
    intro a hterm hinit
    by_cases hj : 1 ≤ j
    · exact (outputTimes_sum_sub_succ_le_first_of_terminal_nonneg j hj a hterm).trans hinit
    · have hj0 : j = 0 := by omega
      subst j
      have hOutput : outputTimes 0 = ∅ := by
        ext t
        simp [outputTimes, SOptLib.positiveTimeOutputWindowTimes]
      simp [hOutput]
  have hbudgetZ : Finset.sum (outputTimes j) dz ≤ 1 := by
    let aZ : Time → ℝ := fun τ =>
      setup.proxFunction (setup.iterateCoreProcess (τ.1 - 1) ω) u
    have hterm : 0 ≤ aZ ⟨j + 1, Nat.succ_le_succ (Nat.zero_le j)⟩ := by
      dsimp [aZ]
      exact setup.proxFunction_nonneg _ u
    have hinit : aZ SOptLib.positiveTimeOne ≤ 1 := by
      dsimp [aZ]
      simpa [SOptLib.positiveTimeOne] using setup.initial_proxFunction_le_one u
    simpa [dz, aZ, SOptLib.positiveTimeSucc] using htel aZ hterm hinit
  have hbudgetV : Finset.sum (outputTimes j) dv ≤ 1 := by
    let aV : Time → ℝ := fun τ =>
      setup.proxFunction (setup.auxiliaryCoreProcess (τ.1 - 1) ω) u
    have hterm : 0 ≤ aV ⟨j + 1, Nat.succ_le_succ (Nat.zero_le j)⟩ := by
      dsimp [aV]
      exact setup.proxFunction_nonneg _ u
    have hinit : aV SOptLib.positiveTimeOne ≤ 1 := by
      dsimp [aV]
      simpa [SOptLib.positiveTimeOne] using setup.initial_proxFunction_le_one u
    simpa [dv, aV, SOptLib.positiveTimeSucc] using htel aV hterm hinit
  have hbudget :=
    two_telescope_pathwise_budget_of_pointwise_combined_bounds
      (times := outputTimes j) (gap := gap) (dz := dz) (dv := dv)
      (q1 := q1) (q2 := q2) (correction := correction)
      (budgetZ := 1) (budgetV := 1) (total := setup.maxRegretSum j ω)
      (by
        rw [Setup.maxRegretSum, setup.regretSum_def j ω u])
      (fun t _ht => by
        simpa [gap, dz, dv, q1, q2, correction, mul_assoc] using
          setup.paper_time_combined_one_step_budget t ω u)
      hbudgetZ hbudgetV
  have hbudget' :
      setup.maxRegretSum j ω ≤
        1 + 1 +
          (1 / 2 : ℝ) *
            Finset.sum (outputTimes j) (fun t =>
              setup.gamma t ^ 2 *
                setup.productDualNorm
                  (setup.stochasticOracle (setup.iterate t ω) (setup.sampleAt t ω)) ^ 2) +
          (1 / 2 : ℝ) *
            Finset.sum (outputTimes j) (fun t =>
              setup.gamma t ^ 2 *
                setup.productDualNorm (setup.oracleNoise t ω) ^ 2) -
          Finset.sum (outputTimes j) (fun t =>
            setup.gamma t *
              ⟪(setup.iterate t ω).1 - (setup.auxiliaryIterate t ω).1,
                setup.oracleNoise t ω⟫_ℝ) := by
    simpa [q1, q2, correction, Finset.mul_sum, mul_assoc, add_assoc] using hbudget
  nlinarith

/-- Lemma 4.6: expected maximized regret bound, including expectation well-definedness. -/
theorem lemma_4_6_gap_sum_bound (j : ℕ) (hj : 1 ≤ j) :
    Integrable (fun ω => setup.maxRegretSum j ω) setup.pathMeasure ∧
      setup.pathExpectation (fun ω => setup.maxRegretSum j ω) ≤
        2 + (5 / 2 : ℝ) * setup.M ^ 2 * setup.sumGammaSq j := by
  refine ⟨setup.maxRegretSum_integrable j hj, ?_⟩
  classical
  letI : IsProbabilityMeasure setup.pathMeasure := setup.pathMeasure_isProbabilityMeasure
  let Gsq : Time → setup.SamplePath → ℝ := fun t ω =>
    (setup.productDualNorm
      (setup.stochasticOracle (setup.iterate t ω) (setup.sampleAt t ω))) ^ 2
  let Dsq : Time → setup.SamplePath → ℝ := fun t ω =>
    (setup.productDualNorm (setup.oracleNoise t ω)) ^ 2
  let Cterm : Time → setup.SamplePath → ℝ := fun t ω =>
    setup.gamma t *
      ⟪(setup.iterate t ω).1 - (setup.auxiliaryIterate t ω).1,
        setup.oracleNoise t ω⟫_ℝ
  let SG : setup.SamplePath → ℝ := fun ω =>
    Finset.sum (outputTimes j) (fun t => setup.gamma t ^ 2 * Gsq t ω)
  let SD : setup.SamplePath → ℝ := fun ω =>
    Finset.sum (outputTimes j) (fun t => setup.gamma t ^ 2 * Dsq t ω)
  let SC : setup.SamplePath → ℝ := fun ω =>
    Finset.sum (outputTimes j) (fun t => Cterm t ω)
  let budget : setup.SamplePath → ℝ := fun ω =>
    2 + (1 / 2 : ℝ) * SG ω + (1 / 2 : ℝ) * SD ω - SC ω
  have hG_int : ∀ t ∈ outputTimes j, Integrable (Gsq t) setup.pathMeasure := by
    intro t _ht
    exact (setup.stochasticOracle_productDualNorm_sq_integrable_and_integral_bound t).1
  have hD_int : ∀ t ∈ outputTimes j, Integrable (Dsq t) setup.pathMeasure := by
    intro t _ht
    exact setup.oracleNoise_productDualNorm_sq_integrable t
  have hC_int : ∀ t ∈ outputTimes j, Integrable (Cterm t) setup.pathMeasure := by
    intro t _ht
    exact (setup.oracleNoise_cross_term_zero t).1
  have hSG_int : Integrable SG setup.pathMeasure := by
    dsimp [SG]
    exact MeasureTheory.integrable_finset_sum (μ := setup.pathMeasure) (s := outputTimes j)
      (f := fun t ω => setup.gamma t ^ 2 * Gsq t ω)
      (fun t ht => (hG_int t ht).const_mul (setup.gamma t ^ 2))
  have hSD_int : Integrable SD setup.pathMeasure := by
    dsimp [SD]
    exact MeasureTheory.integrable_finset_sum (μ := setup.pathMeasure) (s := outputTimes j)
      (f := fun t ω => setup.gamma t ^ 2 * Dsq t ω)
      (fun t ht => (hD_int t ht).const_mul (setup.gamma t ^ 2))
  have hSC_int : Integrable SC setup.pathMeasure := by
    dsimp [SC]
    exact MeasureTheory.integrable_finset_sum (μ := setup.pathMeasure) (s := outputTimes j)
      (f := fun t ω => Cterm t ω) hC_int
  have hBudgetInt : Integrable budget setup.pathMeasure := by
    dsimp [budget]
    exact (((integrable_const (2 : ℝ)).add (hSG_int.const_mul (1 / 2 : ℝ))).add
      (hSD_int.const_mul (1 / 2 : ℝ))).sub hSC_int
  have hmono :
      ∫ ω, setup.maxRegretSum j ω ∂setup.pathMeasure ≤
        ∫ ω, budget ω ∂setup.pathMeasure := by
    refine MeasureTheory.integral_mono_ae (setup.maxRegretSum_integrable j hj) hBudgetInt ?_
    refine Filter.Eventually.of_forall ?_
    intro ω
    simpa [budget, SG, SD, SC, Gsq, Dsq, Cterm] using
      setup.maxRegretSum_pathwise_budget j ω
  have hSG_bound :
      ∫ ω, SG ω ∂setup.pathMeasure ≤ setup.M ^ 2 * setup.sumGammaSq j := by
    dsimp [SG]
    rw [MeasureTheory.integral_finset_sum (s := outputTimes j)
      (μ := setup.pathMeasure)
      (f := fun t ω => setup.gamma t ^ 2 * Gsq t ω)
      (fun t ht => (hG_int t ht).const_mul (setup.gamma t ^ 2))]
    calc
      Finset.sum (outputTimes j)
          (fun t => ∫ ω, setup.gamma t ^ 2 * Gsq t ω ∂setup.pathMeasure)
          ≤ Finset.sum (outputTimes j) (fun t => setup.gamma t ^ 2 * setup.M ^ 2) := by
            refine Finset.sum_le_sum ?_
            intro t ht
            rw [MeasureTheory.integral_const_mul]
            exact mul_le_mul_of_nonneg_left
              (setup.stochasticOracle_productDualNorm_sq_integrable_and_integral_bound t).2
              (sq_nonneg (setup.gamma t))
      _ = setup.M ^ 2 * setup.sumGammaSq j := by
            rw [Setup.sumGammaSq, Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro t _ht
            ring
  have hSD_bound :
      ∫ ω, SD ω ∂setup.pathMeasure ≤ 4 * setup.M ^ 2 * setup.sumGammaSq j := by
    dsimp [SD]
    rw [MeasureTheory.integral_finset_sum (s := outputTimes j)
      (μ := setup.pathMeasure)
      (f := fun t ω => setup.gamma t ^ 2 * Dsq t ω)
      (fun t ht => (hD_int t ht).const_mul (setup.gamma t ^ 2))]
    calc
      Finset.sum (outputTimes j)
          (fun t => ∫ ω, setup.gamma t ^ 2 * Dsq t ω ∂setup.pathMeasure)
          ≤ Finset.sum (outputTimes j) (fun t => setup.gamma t ^ 2 * (4 * setup.M ^ 2)) := by
            refine Finset.sum_le_sum ?_
            intro t ht
            rw [MeasureTheory.integral_const_mul]
            exact mul_le_mul_of_nonneg_left
              (setup.oracleNoise_productDualNorm_sq_integral_bound t)
              (sq_nonneg (setup.gamma t))
      _ = 4 * setup.M ^ 2 * setup.sumGammaSq j := by
            rw [Setup.sumGammaSq, Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro t _ht
            ring
  have hSC_zero : ∫ ω, SC ω ∂setup.pathMeasure = 0 := by
    dsimp [SC]
    rw [MeasureTheory.integral_finset_sum (s := outputTimes j)
      (μ := setup.pathMeasure)
      (f := fun t ω => Cterm t ω) hC_int]
    refine Finset.sum_eq_zero ?_
    intro t ht
    have hzero := (setup.oracleNoise_cross_term_zero t).2
    simpa [Cterm, Setup.pathExpectation] using hzero
  have hbudget_eval :
      ∫ ω, budget ω ∂setup.pathMeasure =
        2 + (1 / 2 : ℝ) * ∫ ω, SG ω ∂setup.pathMeasure +
          (1 / 2 : ℝ) * ∫ ω, SD ω ∂setup.pathMeasure -
          ∫ ω, SC ω ∂setup.pathMeasure := by
    have hbudget_fun :
        budget =
          ((fun _ : setup.SamplePath => (2 : ℝ)) +
              (fun ω => (1 / 2 : ℝ) * SG ω) +
              (fun ω => (1 / 2 : ℝ) * SD ω) -
              SC) := by
      funext ω
      simp [budget]
    rw [hbudget_fun]
    change
      ∫ ω,
          ((((fun _ : setup.SamplePath => (2 : ℝ)) +
              (fun ω => (1 / 2 : ℝ) * SG ω) +
              (fun ω => (1 / 2 : ℝ) * SD ω)) ω) - SC ω) ∂setup.pathMeasure =
        2 + (1 / 2 : ℝ) * ∫ ω, SG ω ∂setup.pathMeasure +
          (1 / 2 : ℝ) * ∫ ω, SD ω ∂setup.pathMeasure -
          ∫ ω, SC ω ∂setup.pathMeasure
    rw [MeasureTheory.integral_sub
      (((integrable_const (2 : ℝ)).add (hSG_int.const_mul (1 / 2 : ℝ))).add
        (hSD_int.const_mul (1 / 2 : ℝ))) hSC_int]
    change
      (∫ ω,
          (((fun _ : setup.SamplePath => (2 : ℝ)) +
              (fun ω => (1 / 2 : ℝ) * SG ω)) ω +
              (1 / 2 : ℝ) * SD ω) ∂setup.pathMeasure) -
          ∫ ω, SC ω ∂setup.pathMeasure =
        2 + (1 / 2 : ℝ) * ∫ ω, SG ω ∂setup.pathMeasure +
          (1 / 2 : ℝ) * ∫ ω, SD ω ∂setup.pathMeasure -
          ∫ ω, SC ω ∂setup.pathMeasure
    rw [MeasureTheory.integral_add
      ((integrable_const (2 : ℝ)).add (hSG_int.const_mul (1 / 2 : ℝ)))
      (hSD_int.const_mul (1 / 2 : ℝ))]
    change
      (∫ ω,
          ((fun _ : setup.SamplePath => (2 : ℝ)) ω +
            (1 / 2 : ℝ) * SG ω) ∂setup.pathMeasure +
          ∫ ω, (1 / 2 : ℝ) * SD ω ∂setup.pathMeasure) -
          ∫ ω, SC ω ∂setup.pathMeasure =
        2 + (1 / 2 : ℝ) * ∫ ω, SG ω ∂setup.pathMeasure +
          (1 / 2 : ℝ) * ∫ ω, SD ω ∂setup.pathMeasure -
          ∫ ω, SC ω ∂setup.pathMeasure
    rw [MeasureTheory.integral_add (integrable_const (2 : ℝ))
      (hSG_int.const_mul (1 / 2 : ℝ))]
    simp [MeasureTheory.integral_const_mul]
  have hbudget_bound :
      ∫ ω, budget ω ∂setup.pathMeasure ≤
        2 + (5 / 2 : ℝ) * setup.M ^ 2 * setup.sumGammaSq j := by
    rw [hbudget_eval, hSC_zero]
    calc
      2 + (1 / 2 : ℝ) * ∫ ω, SG ω ∂setup.pathMeasure +
          (1 / 2 : ℝ) * ∫ ω, SD ω ∂setup.pathMeasure - 0
          ≤ 2 + (1 / 2 : ℝ) * (setup.M ^ 2 * setup.sumGammaSq j) +
              (1 / 2 : ℝ) * (4 * setup.M ^ 2 * setup.sumGammaSq j) - 0 := by
              nlinarith [hSG_bound, hSD_bound]
      _ = 2 + (5 / 2 : ℝ) * setup.M ^ 2 * setup.sumGammaSq j := by
              ring
  unfold Setup.pathExpectation
  exact hmono.trans hbudget_bound

/-- The paper reduction `(4.3.8)` from the output saddle gap to the regret maximum. -/
theorem epsilonPhi_weightedAverage_le_regret (j : ℕ) (hj : 1 ≤ j) (ω : setup.SamplePath) :
    setup.epsilonPhi (setup.weightedAverageOutput j hj ω) ≤
      (setup.outputWeightSum j)⁻¹ * setup.maxRegretSum j ω := by
  classical
  let zbar : setup.Point := setup.weightedAverageOutput j hj ω
  let xStar : {x : EX // x ∈ setup.X} := setup.minPhiXPoint (setup.yPoint zbar)
  let yStar : {y : EY // y ∈ setup.Y} := setup.maxPhiYPoint (setup.xPoint zbar)
  let u : setup.Point :=
    ⟨WithLp.toLp 2 (xStar.1, yStar.1),
      (setup.jointCarrier_def _).2 ⟨xStar.2, yStar.2⟩⟩
  let L : {x : EX // x ∈ setup.X} → {y : EY // y ∈ setup.Y} → ℝ :=
    fun x y => SOptLib.objectiveExpectation setup.P
      (fun xy ξ => setup.Phi xy.1 xy.2 ξ) id (x, y)
  have hmain :
      SOptLib.saddleGap L (setup.xPoint zbar, setup.yPoint zbar) (xStar, yStar) ≤
        (setup.outputWeightSum j)⁻¹ * setup.maxRegretSum j ω := by
    refine
      SOptLib.saddleGap_weightedAverage_le_inv_max_regret_of_convex_concave
        (s := outputTimes j) (γ := setup.gamma) (W := setup.outputWeightSum j)
        (regret := setup.maxRegretSum j ω) (X := setup.X) (Y := setup.Y)
        (L := L)
        (x := fun t => setup.xPoint (setup.iterate t ω))
        (y := fun t => setup.yPoint (setup.iterate t ω))
        (xbar := setup.xPoint zbar) (xStar := xStar)
        (ybar := setup.yPoint zbar) (yStar := yStar)
        (hL_convex_x := ?_) (hL_concave_y := ?_) (hγ_nonneg := ?_)
        (hW_pos := ?_) (hW_eq := ?_) (hxbar := ?_) (hybar := ?_)
        (hregret := ?_)
    · simpa [L] using setup.phi_convex_in_x yStar
    · simpa [L] using setup.phi_concave_in_y xStar
    · intro t _ht
      exact le_of_lt (setup.hgamma_pos t)
    · exact setup.outputWeightSum_pos hj
    · rfl
    · have hz := setup.weightedAverageOutput_def j hj ω
      have hfst := congrArg (fun z : Ambient EX EY => WithLp.fst z) hz
      have hsumfst :
          WithLp.fst
              (Finset.sum (outputTimes j) (fun t =>
                setup.gamma t • (setup.iterate t ω).1)) =
            Finset.sum (outputTimes j) (fun t =>
              setup.gamma t • WithLp.fst (setup.iterate t ω).1) := by
        change
          (WithLp.fstₗ (p := 2) (𝕜 := ℝ) (α := EX) (β := EY))
              (Finset.sum (outputTimes j) (fun t =>
                setup.gamma t • (setup.iterate t ω).1)) =
            Finset.sum (outputTimes j) (fun t =>
              setup.gamma t • WithLp.fst (setup.iterate t ω).1)
        simp
      simp only [WithLp.smul_fst] at hfst
      rw [hsumfst] at hfst
      simpa [zbar, Setup.xPoint, WithLp.smul_fst] using hfst
    · have hz := setup.weightedAverageOutput_def j hj ω
      have hsnd := congrArg (fun z : Ambient EX EY => WithLp.snd z) hz
      have hsumsnd :
          WithLp.snd
              (Finset.sum (outputTimes j) (fun t =>
                setup.gamma t • (setup.iterate t ω).1)) =
            Finset.sum (outputTimes j) (fun t =>
              setup.gamma t • WithLp.snd (setup.iterate t ω).1) := by
        change
          (WithLp.sndₗ (p := 2) (𝕜 := ℝ) (α := EX) (β := EY))
              (Finset.sum (outputTimes j) (fun t =>
                setup.gamma t • (setup.iterate t ω).1)) =
            Finset.sum (outputTimes j) (fun t =>
              setup.gamma t • WithLp.snd (setup.iterate t ω).1)
        simp
      simp only [WithLp.smul_snd] at hsnd
      rw [hsumsnd] at hsnd
      simpa [zbar, Setup.yPoint, WithLp.smul_snd] using hsnd
    · have hRegret := setup.weighted_phi_gap_le_inv_maxRegret j hj ω u
      simpa [SOptLib.saddleGap, L, u, Setup.xPoint, Setup.yPoint] using hRegret
  calc
    setup.epsilonPhi (setup.weightedAverageOutput j hj ω) =
        SOptLib.saddleGap L (setup.xPoint zbar, setup.yPoint zbar) (xStar, yStar) := by
      simp [SOptLib.saddleGap, Setup.epsilonPhi_def, Setup.maxPhiY, Setup.minPhiX,
        zbar, xStar, yStar, L]
    _ ≤ (setup.outputWeightSum j)⁻¹ * setup.maxRegretSum j ω := hmain

private theorem xPoint_continuous :
    Continuous (fun z : setup.Point => setup.xPoint z) := by
  change Continuous
    (fun z : setup.Point => (⟨(z : Ambient EX EY).fst, z.2.1⟩ :
      {x : EX // x ∈ setup.X}))
  exact Continuous.subtype_mk
    ((WithLp.continuous_fst 2 EX EY).comp continuous_subtype_val)
    (fun z => z.2.1)

private theorem yPoint_continuous :
    Continuous (fun z : setup.Point => setup.yPoint z) := by
  change Continuous
    (fun z : setup.Point => (⟨(z : Ambient EX EY).snd, z.2.2⟩ :
      {y : EY // y ∈ setup.Y}))
  exact Continuous.subtype_mk
    ((WithLp.continuous_snd 2 EX EY).comp continuous_subtype_val)
    (fun z => z.2.2)

private theorem phi_fixed_y_continuous (y : {y : EY // y ∈ setup.Y}) :
    Continuous (fun x : {x : EX // x ∈ setup.X} => (fun x y => SOptLib.objectiveExpectation setup.P (fun xy ξ => setup.Phi xy.1 xy.2 ξ) id (x, y)) x y) := by
  rcases setup.phi_lipschitz with ⟨_K, hLip⟩
  let payoff : Ambient EX EY → ℝ := fun z => by
    classical
    exact if hz : z ∈ setup.jointCarrier then
      expectedPayoff setup.P setup.Phi ⟨z.fst, hz.1⟩ ⟨z.snd, hz.2⟩
    else
      0
  have hsliceContOn :
      ContinuousOn
        (fun x : EX => payoff (WithLp.toLp 2 (x, y.1)))
        setup.X := by
    have hmap : Continuous
        (fun x : EX => (WithLp.toLp 2 (x, y.1) : Ambient EX EY)) := by
      exact (WithLp.prod_continuous_toLp 2 EX EY).comp (Continuous.prodMk_left y.1)
    exact hLip.continuousOn.comp hmap.continuousOn (by
      intro x hx
      exact (setup.jointCarrier_def _).2 ⟨hx, y.2⟩)
  refine continuous_subtype_of_continuousOn_ambient
    (X := setup.X)
    (fun x : {x : EX // x ∈ setup.X} => (fun x y => SOptLib.objectiveExpectation setup.P (fun xy ξ => setup.Phi xy.1 xy.2 ξ) id (x, y)) x y)
    (fun x : EX => payoff (WithLp.toLp 2 (x, y.1)))
    hsliceContOn ?_
  intro x
  have hz : WithLp.toLp 2 (x.1, y.1) ∈ setup.jointCarrier := by
    exact (setup.jointCarrier_def _).2 ⟨x.2, y.2⟩
  simp [payoff, SOptLib.objectiveExpectation_def, expectedPayoff, hz]

private theorem phi_fixed_x_continuous (x : {x : EX // x ∈ setup.X}) :
    Continuous (fun y : {y : EY // y ∈ setup.Y} => (fun x y => SOptLib.objectiveExpectation setup.P (fun xy ξ => setup.Phi xy.1 xy.2 ξ) id (x, y)) x y) := by
  rcases setup.phi_lipschitz with ⟨_K, hLip⟩
  let payoff : Ambient EX EY → ℝ := fun z => by
    classical
    exact if hz : z ∈ setup.jointCarrier then
      expectedPayoff setup.P setup.Phi ⟨z.fst, hz.1⟩ ⟨z.snd, hz.2⟩
    else
      0
  have hsliceContOn :
      ContinuousOn
        (fun y : EY => payoff (WithLp.toLp 2 (x.1, y)))
        setup.Y := by
    have hmap : Continuous
        (fun y : EY => (WithLp.toLp 2 (x.1, y) : Ambient EX EY)) := by
      exact (WithLp.prod_continuous_toLp 2 EX EY).comp (Continuous.prodMk_right x.1)
    exact hLip.continuousOn.comp hmap.continuousOn (by
      intro y hy
      exact (setup.jointCarrier_def _).2 ⟨x.2, hy⟩)
  refine continuous_subtype_of_continuousOn_ambient
    (X := setup.Y)
    (fun y : {y : EY // y ∈ setup.Y} => (fun x y => SOptLib.objectiveExpectation setup.P (fun xy ξ => setup.Phi xy.1 xy.2 ξ) id (x, y)) x y)
    (fun y : EY => payoff (WithLp.toLp 2 (x.1, y)))
    hsliceContOn ?_
  intro y
  have hz : WithLp.toLp 2 (x.1, y.1) ∈ setup.jointCarrier := by
    exact (setup.jointCarrier_def _).2 ⟨x.2, y.2⟩
  simp [payoff, SOptLib.objectiveExpectation_def, expectedPayoff, hz]

private theorem weightedAverageOutput_measurable_local (j : ℕ) (hj : 1 ≤ j) :
    Measurable (setup.weightedAverageOutput j hj) := by
  simpa [Setup.weightedAverageOutput] using
    (SOptLib.weightedAverageOutput_measurable
      (Ω := setup.SamplePath) (T := Time) (W := Unit) (E := Ambient EX EY)
      setup.jointCarrier
      (fun _ : Unit => outputTimes j)
      setup.gamma
      (fun t ω => (setup.iterate t ω).1)
      (fun _ : Unit => setup.outputWeightSum j)
      setup.jointCarrier_convex
      (by
        intro _ t _ht
        exact le_of_lt (setup.hgamma_pos t))
      (by
        intro _ t _ht ω
        exact (setup.iterate t ω).2)
      (by
        intro _
        exact setup.outputWeightSum_pos hj)
      (by
        intro _
        rfl)
      (by
        intro t
        exact measurable_subtype_coe.comp (setup.iterate_measurable t))
      ())

private theorem phi_x_weightedAverage_measurable
    (j : ℕ) (hj : 1 ≤ j) (y : {y : EY // y ∈ setup.Y}) :
    Measurable
      (fun ω => (fun x y => SOptLib.objectiveExpectation setup.P (fun xy ξ => setup.Phi xy.1 xy.2 ξ) id (x, y)) (setup.xPoint (setup.weightedAverageOutput j hj ω)) y) := by
  exact (setup.phi_fixed_y_continuous y).measurable.comp
    ((setup.xPoint_continuous.measurable).comp
      (setup.weightedAverageOutput_measurable_local j hj))

private theorem phi_y_weightedAverage_measurable
    (j : ℕ) (hj : 1 ≤ j) (x : {x : EX // x ∈ setup.X}) :
    Measurable
      (fun ω => (fun x y => SOptLib.objectiveExpectation setup.P (fun xy ξ => setup.Phi xy.1 xy.2 ξ) id (x, y)) x (setup.yPoint (setup.weightedAverageOutput j hj ω))) := by
  exact (setup.phi_fixed_x_continuous x).measurable.comp
    ((setup.yPoint_continuous.measurable).comp
      (setup.weightedAverageOutput_measurable_local j hj))

private theorem maxPhiY_weightedAverage_measurable (j : ℕ) (hj : 1 ≤ j) :
    Measurable
      (fun ω => setup.maxPhiY (setup.xPoint (setup.weightedAverageOutput j hj ω))) := by
  classical
  have hne : Nonempty {y : EY // y ∈ setup.Y} := by
    rcases setup.hY_nonempty with ⟨y, hy⟩
    exact ⟨⟨y, hy⟩⟩
  letI : Inhabited {y : EY // y ∈ setup.Y} := Classical.inhabited_of_nonempty hne
  have hcompact : IsCompact (Set.univ : Set {y : EY // y ∈ setup.Y}) := by
    simpa using isCompact_univ_subtype_of_isClosed_isBounded setup.hY_closed
      setup.hY_bounded
  letI : CompactSpace {y : EY // y ∈ setup.Y} := isCompact_univ_iff.mp hcompact
  haveI : TopologicalSpace.SeparableSpace {y : EY // y ∈ setup.Y} := by infer_instance
  let u : ℕ → {y : EY // y ∈ setup.Y} := TopologicalSpace.denseSeq _
  let F : setup.SamplePath → ℝ := fun ω =>
    ⨆ n : ℕ, (fun x y => SOptLib.objectiveExpectation setup.P (fun xy ξ => setup.Phi xy.1 xy.2 ξ) id (x, y)) (setup.xPoint (setup.weightedAverageOutput j hj ω)) (u n)
  have hDenseRange : DenseRange u := by
    exact TopologicalSpace.denseRange_denseSeq (α := {y : EY // y ∈ setup.Y})
  have hDense : Dense (Set.range u) := hDenseRange
  have hF_meas : Measurable F := by
    dsimp [F]
    exact Measurable.iSup (fun n => setup.phi_x_weightedAverage_measurable j hj (u n))
  have hEq :
      (fun ω : setup.SamplePath =>
        setup.maxPhiY (setup.xPoint (setup.weightedAverageOutput j hj ω))) = F := by
    funext ω
    apply le_antisymm
    · have hbounded : BddAbove
          (Set.range (fun n : ℕ =>
            (fun x y => SOptLib.objectiveExpectation setup.P (fun xy ξ => setup.Phi xy.1 xy.2 ξ) id (x, y)) (setup.xPoint (setup.weightedAverageOutput j hj ω)) (u n))) := by
        exact ⟨setup.maxPhiY (setup.xPoint (setup.weightedAverageOutput j hj ω)), by
          rintro y ⟨n, rfl⟩
          exact setup.maxPhiY_isMax
            (setup.xPoint (setup.weightedAverageOutput j hj ω)) (u n)⟩
      have hall : ∀ y : {y : EY // y ∈ setup.Y},
          (fun x y => SOptLib.objectiveExpectation setup.P (fun xy ξ => setup.Phi xy.1 xy.2 ξ) id (x, y)) (setup.xPoint (setup.weightedAverageOutput j hj ω)) y ≤ F ω := by
        intro y
        refine le_of_continuousOn_of_dense_le
          (f := fun _ : {y : EY // y ∈ setup.Y} => F ω)
          (g := fun y : {y : EY // y ∈ setup.Y} =>
            (fun x y => SOptLib.objectiveExpectation setup.P (fun xy ξ => setup.Phi xy.1 xy.2 ξ) id (x, y)) (setup.xPoint (setup.weightedAverageOutput j hj ω)) y)
          (s := Set.range u) ?_ hDense ?_ y
        · exact (continuous_const.sub
            (setup.phi_fixed_x_continuous
              (setup.xPoint (setup.weightedAverageOutput j hj ω)))).continuousOn
        · intro y hy
          rcases hy with ⟨n, rfl⟩
          dsimp [F]
          exact le_ciSup hbounded n
      simpa [Setup.maxPhiY] using
        hall (setup.maxPhiYPoint (setup.xPoint (setup.weightedAverageOutput j hj ω)))
    · dsimp [F]
      exact ciSup_le fun n =>
        setup.maxPhiY_isMax (setup.xPoint (setup.weightedAverageOutput j hj ω)) (u n)
  rw [hEq]
  exact hF_meas

private theorem minPhiX_weightedAverage_measurable (j : ℕ) (hj : 1 ≤ j) :
    Measurable
      (fun ω => setup.minPhiX (setup.yPoint (setup.weightedAverageOutput j hj ω))) := by
  classical
  have hne : Nonempty {x : EX // x ∈ setup.X} := by
    rcases setup.hX_nonempty with ⟨x, hx⟩
    exact ⟨⟨x, hx⟩⟩
  letI : Inhabited {x : EX // x ∈ setup.X} := Classical.inhabited_of_nonempty hne
  have hcompact : IsCompact (Set.univ : Set {x : EX // x ∈ setup.X}) := by
    simpa using isCompact_univ_subtype_of_isClosed_isBounded setup.hX_closed
      setup.hX_bounded
  letI : CompactSpace {x : EX // x ∈ setup.X} := isCompact_univ_iff.mp hcompact
  haveI : TopologicalSpace.SeparableSpace {x : EX // x ∈ setup.X} := by infer_instance
  let u : ℕ → {x : EX // x ∈ setup.X} := TopologicalSpace.denseSeq _
  let F : setup.SamplePath → ℝ := fun ω =>
    ⨆ n : ℕ, -(fun x y => SOptLib.objectiveExpectation setup.P (fun xy ξ => setup.Phi xy.1 xy.2 ξ) id (x, y)) (u n) (setup.yPoint (setup.weightedAverageOutput j hj ω))
  have hDenseRange : DenseRange u := by
    exact TopologicalSpace.denseRange_denseSeq (α := {x : EX // x ∈ setup.X})
  have hDense : Dense (Set.range u) := hDenseRange
  have hF_meas : Measurable F := by
    dsimp [F]
    exact Measurable.iSup (fun n => (setup.phi_y_weightedAverage_measurable j hj (u n)).neg)
  have hNegEq :
      (fun ω : setup.SamplePath =>
        -setup.minPhiX (setup.yPoint (setup.weightedAverageOutput j hj ω))) = F := by
    funext ω
    apply le_antisymm
    · have hbounded : BddAbove
          (Set.range (fun n : ℕ =>
            -(fun x y => SOptLib.objectiveExpectation setup.P (fun xy ξ => setup.Phi xy.1 xy.2 ξ) id (x, y)) (u n) (setup.yPoint (setup.weightedAverageOutput j hj ω)))) := by
        exact ⟨-setup.minPhiX (setup.yPoint (setup.weightedAverageOutput j hj ω)), by
          rintro x ⟨n, rfl⟩
          exact neg_le_neg
            (setup.minPhiX_isMin
              (setup.yPoint (setup.weightedAverageOutput j hj ω)) (u n))⟩
      have hpoint :
          -(fun x y => SOptLib.objectiveExpectation setup.P (fun xy ξ => setup.Phi xy.1 xy.2 ξ) id (x, y))
              (setup.minPhiXPoint (setup.yPoint (setup.weightedAverageOutput j hj ω)))
              (setup.yPoint (setup.weightedAverageOutput j hj ω)) ≤ F ω := by
        refine le_of_continuousOn_of_dense_le
          (f := fun _ : {x : EX // x ∈ setup.X} => F ω)
          (g := fun x : {x : EX // x ∈ setup.X} =>
            -(fun x y => SOptLib.objectiveExpectation setup.P (fun xy ξ => setup.Phi xy.1 xy.2 ξ) id (x, y)) x (setup.yPoint (setup.weightedAverageOutput j hj ω)))
          (s := Set.range u) ?_ hDense ?_
          (setup.minPhiXPoint (setup.yPoint (setup.weightedAverageOutput j hj ω)))
        · exact (continuous_const.sub
            ((setup.phi_fixed_y_continuous
              (setup.yPoint (setup.weightedAverageOutput j hj ω))).neg)).continuousOn
        · intro x hx
          rcases hx with ⟨n, rfl⟩
          dsimp [F]
          exact le_ciSup hbounded n
      simpa [Setup.minPhiX] using hpoint
    · dsimp [F]
      exact ciSup_le fun n =>
        neg_le_neg
          (setup.minPhiX_isMin (setup.yPoint (setup.weightedAverageOutput j hj ω)) (u n))
  have hNegMeas :
      Measurable
        (fun ω : setup.SamplePath =>
          -setup.minPhiX (setup.yPoint (setup.weightedAverageOutput j hj ω))) := by
    rw [hNegEq]
    exact hF_meas
  simpa using hNegMeas.neg

private theorem epsilonPhi_weightedAverage_measurable (j : ℕ) (hj : 1 ≤ j) :
    Measurable (fun ω => setup.epsilonPhi (setup.weightedAverageOutput j hj ω)) := by
  simpa [Setup.epsilonPhi_def] using
    (setup.maxPhiY_weightedAverage_measurable j hj).sub
      (setup.minPhiX_weightedAverage_measurable j hj)

private theorem epsilonPhi_nonneg (z : setup.Point) :
    0 ≤ setup.epsilonPhi z := by
  have hmin := setup.minPhiX_isMin (setup.yPoint z) (setup.xPoint z)
  have hmax := setup.maxPhiY_isMax (setup.xPoint z) (setup.yPoint z)
  rw [Setup.epsilonPhi_def]
  linarith

/-- Well-definedness of the expectation in the main saddle-gap theorem. -/
theorem epsilonPhi_weightedAverage_integrable (j : ℕ) (hj : 1 ≤ j) :
    Integrable
      (fun ω => setup.epsilonPhi (setup.weightedAverageOutput j hj ω)) setup.pathMeasure := by
  let c : ℝ := (setup.outputWeightSum j)⁻¹
  have hScaledInt :
      Integrable (fun ω => c * setup.maxRegretSum j ω) setup.pathMeasure := by
    exact (setup.maxRegretSum_integrable j hj).const_mul c
  refine hScaledInt.mono'
    (setup.epsilonPhi_weightedAverage_measurable j hj).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall (fun ω => by
    have hnonneg :
        0 ≤ setup.epsilonPhi (setup.weightedAverageOutput j hj ω) :=
      setup.epsilonPhi_nonneg (setup.weightedAverageOutput j hj ω)
    have hle := setup.epsilonPhi_weightedAverage_le_regret j hj ω
    rw [Real.norm_of_nonneg hnonneg]
    simpa [c] using hle)

/-- Main expected saddle-gap theorem following `(4.3.9)`, including expectation
well-definedness for the displayed expectation. -/
theorem main_expected_gap_bound (j : ℕ) (hj : 1 ≤ j) :
    Integrable
      (fun ω => setup.epsilonPhi (setup.weightedAverageOutput j hj ω)) setup.pathMeasure ∧
      setup.pathExpectation (fun ω => setup.epsilonPhi (setup.weightedAverageOutput j hj ω)) ≤
        (setup.outputWeightSum j)⁻¹ *
          (2 + (5 / 2 : ℝ) * setup.M ^ 2 * setup.sumGammaSq j) := by
  refine ⟨setup.epsilonPhi_weightedAverage_integrable j hj, ?_⟩
  let c : ℝ := (setup.outputWeightSum j)⁻¹
  have hReg := setup.lemma_4_6_gap_sum_bound j hj
  have hc : 0 ≤ c := by
    exact inv_nonneg.mpr (le_of_lt (setup.outputWeightSum_pos hj))
  have hScaledInt :
      Integrable (fun ω => c * setup.maxRegretSum j ω) setup.pathMeasure := by
    exact hReg.1.const_mul c
  have hIntLe :
      (∫ ω, setup.epsilonPhi (setup.weightedAverageOutput j hj ω) ∂setup.pathMeasure) ≤
        ∫ ω, c * setup.maxRegretSum j ω ∂setup.pathMeasure := by
    exact MeasureTheory.integral_mono_ae
      (setup.epsilonPhi_weightedAverage_integrable j hj)
      hScaledInt
      (Filter.Eventually.of_forall (fun ω => by
        simpa [c] using setup.epsilonPhi_weightedAverage_le_regret j hj ω))
  calc
    setup.pathExpectation (fun ω => setup.epsilonPhi (setup.weightedAverageOutput j hj ω))
        = ∫ ω, setup.epsilonPhi (setup.weightedAverageOutput j hj ω) ∂setup.pathMeasure := by
          rfl
    _ ≤ ∫ ω, c * setup.maxRegretSum j ω ∂setup.pathMeasure := hIntLe
    _ = c * setup.pathExpectation (fun ω => setup.maxRegretSum j ω) := by
          simp [Setup.pathExpectation, MeasureTheory.integral_const_mul]
    _ ≤ c * (2 + (5 / 2 : ℝ) * setup.M ^ 2 * setup.sumGammaSq j) := by
          exact mul_le_mul_of_nonneg_left hReg.2 hc
    _ = (setup.outputWeightSum j)⁻¹ *
          (2 + (5 / 2 : ℝ) * setup.M ^ 2 * setup.sumGammaSq j) := by
          rfl

/-- Constant stepsize policy `(4.3.15)` over the fixed horizon `N`. -/
def constantStepsizePolicy (N : ℕ) : Prop :=
  ∀ t : Time, t.1 ≤ N →
    setup.gamma t = 2 / (setup.M * Real.sqrt (5 * (N : ℝ)))

/-- The fixed-horizon threshold printed immediately before `(4.3.16)`. -/
noncomputable def fixedHorizonExpectedThreshold (N : ℕ) : ℝ :=
  2 * setup.M * Real.sqrt (5 / (N : ℝ))

private theorem fixed_horizon_constant_step_sums
    (N : ℕ) (hN : 1 ≤ N)
    (hsteps : setup.constantStepsizePolicy N) :
    let γ0 : ℝ := 2 / (setup.M * Real.sqrt (5 * (N : ℝ)))
    setup.outputWeightSum N = (N : ℝ) * γ0 ∧
      setup.sumGammaSq N = (N : ℝ) * γ0 ^ 2 := by
  let γ0 : ℝ := 2 / (setup.M * Real.sqrt (5 * (N : ℝ)))
  have hsum : setup.outputWeightSum N = (N : ℝ) * γ0 := by
    rw [Setup.outputWeightSum, Setup.outputTimes]
    rw [SOptLib.sum_positiveTimeOutputWindowTimes_eq_Icc (α := ℝ) 1 N
      (by norm_num) hN setup.gamma]
    calc
      Finset.sum (Finset.Icc 1 N) (fun n =>
          if hn : n ∈ Finset.Icc 1 N then
            setup.gamma
              ⟨n, le_trans (by norm_num : 1 ≤ 1) (Finset.mem_Icc.mp hn).1⟩
          else 0)
          = Finset.sum (Finset.Icc 1 N) (fun _n => γ0) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            have hnle : n ≤ N := (Finset.mem_Icc.mp hn).2
            simp [hn, γ0,
              hsteps
                ⟨n, le_trans (by norm_num : 1 ≤ 1) (Finset.mem_Icc.mp hn).1⟩
                hnle]
      _ = (N : ℝ) * γ0 := by
            simp
  have hsumsq : setup.sumGammaSq N = (N : ℝ) * γ0 ^ 2 := by
    rw [Setup.sumGammaSq, Setup.outputTimes]
    rw [SOptLib.sum_positiveTimeOutputWindowTimes_eq_Icc (α := ℝ) 1 N
      (by norm_num) hN (fun t => setup.gamma t ^ 2)]
    calc
      Finset.sum (Finset.Icc 1 N) (fun n =>
          if hn : n ∈ Finset.Icc 1 N then
            setup.gamma
              ⟨n, le_trans (by norm_num : 1 ≤ 1) (Finset.mem_Icc.mp hn).1⟩ ^ 2
          else 0)
          = Finset.sum (Finset.Icc 1 N) (fun _n => γ0 ^ 2) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            have hnle : n ≤ N := (Finset.mem_Icc.mp hn).2
            simp [hn, γ0,
              hsteps
                ⟨n, le_trans (by norm_num : 1 ≤ 1) (Finset.mem_Icc.mp hn).1⟩
                hnle]
      _ = (N : ℝ) * γ0 ^ 2 := by
            simp
  exact ⟨hsum, hsumsq⟩

/-- Fixed-horizon expected error consequence corresponding to the displayed bound
preceding `(4.3.16)`.  The source print around `(4.3.16)` is not used as a
pathwise hypothesis in Proposition 4.10, and the Lean statement packages the
expectation well-definedness with the displayed upper bound. -/
theorem fixed_horizon_expected_error_bound
    (N : ℕ) (hN : 1 ≤ N)
    (_hsteps : setup.constantStepsizePolicy N) :
    SOptLib.expectationLe setup.pathMeasure
      (fun ω => setup.epsilonPhi (setup.weightedAverageOutput N hN ω))
      (setup.fixedHorizonExpectedThreshold N) := by
  let γ0 : ℝ := 2 / (setup.M * Real.sqrt (5 * (N : ℝ)))
  have hsum : setup.outputWeightSum N = (N : ℝ) * γ0 := by
    rw [Setup.outputWeightSum, Setup.outputTimes]
    rw [SOptLib.sum_positiveTimeOutputWindowTimes_eq_Icc (α := ℝ) 1 N
      (by norm_num) hN setup.gamma]
    calc
      Finset.sum (Finset.Icc 1 N) (fun n =>
          if hn : n ∈ Finset.Icc 1 N then
            setup.gamma
              ⟨n, le_trans (by norm_num : 1 ≤ 1) (Finset.mem_Icc.mp hn).1⟩
          else 0)
          = Finset.sum (Finset.Icc 1 N) (fun _n => γ0) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            have hnle : n ≤ N := (Finset.mem_Icc.mp hn).2
            simp [hn, γ0,
              _hsteps
                ⟨n, le_trans (by norm_num : 1 ≤ 1) (Finset.mem_Icc.mp hn).1⟩
                hnle]
      _ = (N : ℝ) * γ0 := by
            simp
  have hsumsq : setup.sumGammaSq N = (N : ℝ) * γ0 ^ 2 := by
    rw [Setup.sumGammaSq, Setup.outputTimes]
    rw [SOptLib.sum_positiveTimeOutputWindowTimes_eq_Icc (α := ℝ) 1 N
      (by norm_num) hN (fun t => setup.gamma t ^ 2)]
    calc
      Finset.sum (Finset.Icc 1 N) (fun n =>
          if hn : n ∈ Finset.Icc 1 N then
            setup.gamma
              ⟨n, le_trans (by norm_num : 1 ≤ 1) (Finset.mem_Icc.mp hn).1⟩ ^ 2
          else 0)
          = Finset.sum (Finset.Icc 1 N) (fun _n => γ0 ^ 2) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            have hnle : n ≤ N := (Finset.mem_Icc.mp hn).2
            simp [hn, γ0,
              _hsteps
                ⟨n, le_trans (by norm_num : 1 ≤ 1) (Finset.mem_Icc.mp hn).1⟩
                hnle]
      _ = (N : ℝ) * γ0 ^ 2 := by
            simp
  have hscalar :
      (setup.outputWeightSum N)⁻¹ *
          (2 + (5 / 2 : ℝ) * setup.M ^ 2 * setup.sumGammaSq N) ≤
        setup.fixedHorizonExpectedThreshold N := by
    rw [hsum, hsumsq]
    dsimp [γ0]
    unfold Setup.fixedHorizonExpectedThreshold
    have hMpos : 0 < setup.M := setup.M_pos
    have hNposNat : 0 < N := lt_of_lt_of_le (Nat.zero_lt_one) hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNposNat
    have hsqrtpos : 0 < Real.sqrt (5 * (N : ℝ)) := by
      exact Real.sqrt_pos_of_pos (by positivity)
    have hMne : setup.M ≠ 0 := ne_of_gt hMpos
    have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
    have hsqrtne : Real.sqrt (5 * (N : ℝ)) ≠ 0 := ne_of_gt hsqrtpos
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 5) (N : ℝ)]
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 5)]
    field_simp [hMne, hNne, hsqrtne,
      Real.sq_sqrt (by positivity : 0 ≤ 5 * (N : ℝ))]
    nlinarith [hMpos, hNpos, Real.sqrt_nonneg (N : ℝ),
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5), Real.sq_sqrt (le_of_lt hNpos)]
  have hmain := setup.main_expected_gap_bound N hN
  refine SOptLib.expectationLe_of_integrable_integral_le hmain.1 ?_
  rw [← Setup.pathExpectation]
  exact le_trans hmain.2 hscalar

/-- Componentwise fixed-horizon threshold printed in `(4.3.16)`.

The parameters `alphaX` and `alphaY` name the source display's `α_x` and `α_y`.
They are kept at the `(4.3.16)` boundary instead of being replaced by the
product-space expected threshold preceding the display. -/
noncomputable def fixedHorizonComponentThreshold
    (N : ℕ) (alphaX alphaY : ℝ) : ℝ :=
  2 * Real.sqrt
    (10 * (alphaY * setup.DX ^ 2 * setup.MX ^ 2 +
        alphaX * setup.DY ^ 2 * setup.MY ^ 2) /
      (alphaX * alphaY * (N : ℝ)))

/-- Exponential moment assumption `(4.3.18)` for Proposition 4.10. -/
def exponentialMomentOracleBound : Prop :=
  (∀ x : {x : EX // x ∈ setup.X}, ∀ y : {y : EY // y ∈ setup.Y},
    Integrable
      (fun ξ => Real.exp (((SOptLib.canonicalDualNorm setup.normX (setup.Gx x y ξ)) ^ 2) /
        setup.MX ^ 2)) setup.P ∧
      ∫ ξ, Real.exp (((SOptLib.canonicalDualNorm setup.normX (setup.Gx x y ξ)) ^ 2) /
        setup.MX ^ 2) ∂setup.P ≤ Real.exp 1) ∧
  (∀ x : {x : EX // x ∈ setup.X}, ∀ y : {y : EY // y ∈ setup.Y},
    Integrable
      (fun ξ => Real.exp (((SOptLib.canonicalDualNorm setup.normY (setup.Gy x y ξ)) ^ 2) /
        setup.MY ^ 2)) setup.P ∧
      ∫ ξ, Real.exp (((SOptLib.canonicalDualNorm setup.normY (setup.Gy x y ξ)) ^ 2) /
        setup.MY ^ 2) ∂setup.P ≤ Real.exp 1)

private theorem exp_add_div_le_weighted_exp
    {a b x y : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Real.exp ((x + y) / (a + b)) ≤
      a / (a + b) * Real.exp (x / a) +
        b / (a + b) * Real.exp (y / b) := by
  have hab : 0 < a + b := add_pos ha hb
  have hwa : 0 ≤ a / (a + b) := div_nonneg ha.le hab.le
  have hwb : 0 ≤ b / (a + b) := div_nonneg hb.le hab.le
  have hsum : a / (a + b) + b / (a + b) = 1 := by
    field_simp [ne_of_gt hab]
  have harg :
      a / (a + b) * (x / a) + b / (a + b) * (y / b) =
        (x + y) / (a + b) := by
    field_simp [ne_of_gt ha, ne_of_gt hb, ne_of_gt hab]
  have hJ :=
    convexOn_exp.2 (Set.mem_univ (x / a)) (Set.mem_univ (y / b))
      hwa hwb hsum
  simpa [smul_eq_mul, harg] using hJ

private theorem product_stochastic_oracle_exp_moment_bound
    (z : setup.Point) (hexp : setup.exponentialMomentOracleBound) :
    Integrable
      (fun ξ =>
        Real.exp (((setup.productDualNorm (setup.stochasticOracle z ξ)) ^ 2) /
          setup.M ^ 2)) setup.P ∧
      ∫ ξ,
        Real.exp (((setup.productDualNorm (setup.stochasticOracle z ξ)) ^ 2) /
          setup.M ^ 2) ∂setup.P ≤ Real.exp 1 := by
  exact
    productOracle_expMoment_bound_of_component_bounds
      (P := setup.P)
      (G := fun ξ => setup.stochasticOracle z ξ)
      (GX := fun ξ => setup.Gx (setup.xPoint z) (setup.yPoint z) ξ)
      (GY := fun ξ => setup.Gy (setup.xPoint z) (setup.yPoint z) ξ)
      (dualProd := setup.productDualNorm)
      (dualX := fun ζ => SOptLib.canonicalDualNorm setup.normX ζ)
      (dualY := fun η => SOptLib.canonicalDualNorm setup.normY η)
      (A := 2 * setup.DX ^ 2 * setup.MX ^ 2)
      (B := 2 * setup.DY ^ 2 * setup.MY ^ 2)
      (M2 := setup.M ^ 2) (MX := setup.MX) (MY := setup.MY)
      (by nlinarith [sq_pos_of_pos setup.DX_pos, sq_pos_of_pos setup.hMX_pos])
      (by nlinarith [sq_pos_of_pos setup.DY_pos, sq_pos_of_pos setup.hMY_pos])
      (by rw [setup.M_sq_eq_M2, Setup.M2])
      (by
        intro ξ
        let Xsq : ℝ :=
          (SOptLib.canonicalDualNorm setup.normX
            (setup.Gx (setup.xPoint z) (setup.yPoint z) ξ)) ^ 2
        let Ysq : ℝ :=
          (SOptLib.canonicalDualNorm setup.normY
            (setup.Gy (setup.xPoint z) (setup.yPoint z) ξ)) ^ 2
        have hMx_ne : setup.MX ≠ 0 := ne_of_gt setup.hMX_pos
        have hMy_ne : setup.MY ≠ 0 := ne_of_gt setup.hMY_pos
        calc
          (setup.productDualNorm (setup.stochasticOracle z ξ)) ^ 2 =
              2 * setup.DX ^ 2 * Xsq + 2 * setup.DY ^ 2 * Ysq := by
                simpa [Xsq, Ysq] using
                  productDualNorm_sq_stochasticOracle_eq (setup := setup) z ξ
          _ =
              (2 * setup.DX ^ 2 * setup.MX ^ 2) * (Xsq / setup.MX ^ 2) +
                (2 * setup.DY ^ 2 * setup.MY ^ 2) * (Ysq / setup.MY ^ 2) := by
                field_simp [hMx_ne, hMy_ne])
      (by
        have hpair :
            Measurable (fun ξ : setup.SamplePoint => (z, ξ)) :=
          (measurable_const : Measurable (fun _ξ : setup.SamplePoint => z)).prodMk
            measurable_id
        have horacle :
            Measurable (fun ξ : setup.SamplePoint => setup.stochasticOracle z ξ) := by
          simpa using setup.stochasticOracle_measurable.comp hpair
        have hdual :
            Measurable
              (fun ξ : setup.SamplePoint =>
                setup.productDualNorm (setup.stochasticOracle z ξ)) :=
          productDualNorm_continuous (setup := setup).measurable.comp horacle
        have hscalar :
            Measurable
              (fun ξ : setup.SamplePoint =>
                Real.exp (((setup.productDualNorm (setup.stochasticOracle z ξ)) ^ 2) /
                  setup.M ^ 2)) :=
          (Real.continuous_exp.comp
            (((continuous_id : Continuous (fun r : ℝ => r)).pow 2).div_const
              (setup.M ^ 2))).measurable.comp hdual
        exact hscalar.aestronglyMeasurable)
      (by simpa using (hexp.1 (setup.xPoint z) (setup.yPoint z)).1)
      (by simpa using (hexp.1 (setup.xPoint z) (setup.yPoint z)).2)
      (by simpa using (hexp.2 (setup.xPoint z) (setup.yPoint z)).1)
      (by simpa using (hexp.2 (setup.xPoint z) (setup.yPoint z)).2)

private theorem exp_finset_weighted_sum_le_sum_weighted_exp
    {ι : Type*} (s : Finset ι) (w x : ι → ℝ)
    (hw_nonneg : ∀ i ∈ s, 0 ≤ w i)
    (hw_sum : Finset.sum s w = 1) :
    Real.exp (Finset.sum s (fun i => w i * x i)) ≤
      Finset.sum s (fun i => w i * Real.exp (x i)) := by
  exact Real.exp_finset_weighted_sum_le_sum_weighted_exp s w x hw_nonneg hw_sum

private theorem random_iterate_product_oracle_exp_moment_bound
    (t : Time) (hexp : setup.exponentialMomentOracleBound) :
    Integrable
      (fun ω =>
        Real.exp (((setup.productDualNorm
          (setup.stochasticOracle (setup.iterate t ω) (setup.sampleAt t ω))) ^ 2) /
          setup.M ^ 2)) setup.pathMeasure ∧
      ∫ ω,
        Real.exp (((setup.productDualNorm
          (setup.stochasticOracle (setup.iterate t ω) (setup.sampleAt t ω))) ^ 2) /
          setup.M ^ 2) ∂setup.pathMeasure ≤ Real.exp 1 := by
  letI : IsProbabilityMeasure setup.pathMeasure := setup.pathMeasure_isProbabilityMeasure
  letI : IsProbabilityMeasure setup.P := setup.hP_prob
  let moment : setup.Point × Ambient EX EY → setup.SamplePoint → ℝ := fun q ξ =>
    Real.exp (((setup.productDualNorm (setup.stochasticOracle q.1 ξ)) ^ 2) /
      setup.M ^ 2)
  have hmoment :
      Measurable (Function.uncurry moment) := by
    have hquery_sample :
        Measurable
          (fun p : (setup.Point × Ambient EX EY) × setup.SamplePoint =>
            (p.1.1, p.2)) :=
      (measurable_fst.comp measurable_fst).prodMk measurable_snd
    have horacle :
        Measurable
          (fun p : (setup.Point × Ambient EX EY) × setup.SamplePoint =>
            setup.stochasticOracle p.1.1 p.2) :=
      setup.stochasticOracle_measurable.comp hquery_sample
    have hdual :
        Measurable
          (fun p : (setup.Point × Ambient EX EY) × setup.SamplePoint =>
            setup.productDualNorm (setup.stochasticOracle p.1.1 p.2)) :=
      productDualNorm_continuous (setup := setup).measurable.comp horacle
    have hscalar :
        Measurable
          (fun p : (setup.Point × Ambient EX EY) × setup.SamplePoint =>
            Real.exp (((setup.productDualNorm (setup.stochasticOracle p.1.1 p.2)) ^ 2) /
              setup.M ^ 2)) :=
      (Real.continuous_exp.comp
        (((continuous_id : Continuous (fun r : ℝ => r)).pow 2).div_const
          (setup.M ^ 2))).measurable.comp hdual
    simpa [moment, Function.uncurry] using hscalar
  have hfixed_int :
      ∀ q : setup.Point × Ambient EX EY,
        Integrable (fun ξ => moment q ξ) setup.P := by
    intro q
    simpa [moment] using
      (product_stochastic_oracle_exp_moment_bound (setup := setup) q.1 hexp).1
  have hfixed_bound :
      ∀ q : setup.Point × Ambient EX EY,
        ∫ ξ, moment q ξ ∂setup.P ≤ Real.exp 1 := by
    intro q
    simpa [moment] using
      (product_stochastic_oracle_exp_moment_bound (setup := setup) q.1 hexp).2
  have htransfer :=
    random_iterate_uncentered_oracle_moment_bound_of_fixed
      (P := setup.pathMeasure) (ν := setup.P)
      (X := setup.crossTermQuery t) (Y := setup.sampleAt t)
      (moment := moment) (C := Real.exp 1)
      hmoment (setup.crossTermQuery_measurable t) (setup.sampleAt_measurable t)
      (setup.crossTermQuery_indep_sampleAt t) (setup.sampleAt_law t)
      (fun _q _ξ => le_of_lt (Real.exp_pos _))
      (le_of_lt (Real.exp_pos _)) hfixed_int hfixed_bound
  simpa [moment] using htransfer

/-- Tail threshold from Proposition 4.10. -/
noncomputable def largeDeviationThreshold (N : ℕ) (lambda : ℝ) : ℝ :=
  ((8 + 2 * lambda) * Real.sqrt 5 * setup.M) / Real.sqrt (N : ℝ)

private theorem productDualNorm_add_sq_le_two_mul_sq_add_two_mul_sq
    (a b : Ambient EX EY) :
    setup.productDualNorm (a + b) ^ 2 ≤
      2 * setup.productDualNorm a ^ 2 + 2 * setup.productDualNorm b ^ 2 := by
  let cX : Ambient EX EY → ℝ := fun zeta =>
    SOptLib.canonicalDualNorm setup.normX zeta.fst
  let cY : Ambient EX EY → ℝ := fun zeta =>
    SOptLib.canonicalDualNorm setup.normY zeta.snd
  have hxadd :
      cX (a + b) ≤ cX a + cX b := by
    dsimp [cX]
    simpa using
      SOptLib.canonicalDualNorm_add_le setup.normX a.fst b.fst
        (canonicalDualNorm_supportSet_bddAbove_of_separating
          setup.normX setup.hnormX_separating a.fst)
        (canonicalDualNorm_supportSet_bddAbove_of_separating
          setup.normX setup.hnormX_separating b.fst)
  have hyadd :
      cY (a + b) ≤ cY a + cY b := by
    dsimp [cY]
    simpa using
      SOptLib.canonicalDualNorm_add_le setup.normY a.snd b.snd
        (canonicalDualNorm_supportSet_bddAbove_of_separating
          setup.normY setup.hnormY_separating a.snd)
        (canonicalDualNorm_supportSet_bddAbove_of_separating
          setup.normY setup.hnormY_separating b.snd)
  have hx_nonneg : 0 ≤ cX (a + b) := by
    dsimp [cX]
    exact SOptLib.canonicalDualNorm_nonneg setup.normX (a + b).fst
  have hxa_nonneg : 0 ≤ cX a := by
    dsimp [cX]
    exact SOptLib.canonicalDualNorm_nonneg setup.normX a.fst
  have hxb_nonneg : 0 ≤ cX b := by
    dsimp [cX]
    exact SOptLib.canonicalDualNorm_nonneg setup.normX b.fst
  have hy_nonneg : 0 ≤ cY (a + b) := by
    dsimp [cY]
    exact SOptLib.canonicalDualNorm_nonneg setup.normY (a + b).snd
  have hya_nonneg : 0 ≤ cY a := by
    dsimp [cY]
    exact SOptLib.canonicalDualNorm_nonneg setup.normY a.snd
  have hyb_nonneg : 0 ≤ cY b := by
    dsimp [cY]
    exact SOptLib.canonicalDualNorm_nonneg setup.normY b.snd
  have hx_sq :
      cX (a + b) ^ 2 ≤ 2 * cX a ^ 2 + 2 * cX b ^ 2 := by
    nlinarith [hxadd, hx_nonneg, hxa_nonneg, hxb_nonneg,
      sq_nonneg (cX a - cX b)]
  have hy_sq :
      cY (a + b) ^ 2 ≤ 2 * cY a ^ 2 + 2 * cY b ^ 2 := by
    nlinarith [hyadd, hy_nonneg, hya_nonneg, hyb_nonneg,
      sq_nonneg (cY a - cY b)]
  have hDXcoeff : 0 ≤ 2 * setup.DX ^ 2 := by positivity
  have hDYcoeff : 0 ≤ 2 * setup.DY ^ 2 := by positivity
  rw [Setup.productDualNorm_def, Setup.productDualNorm_def,
    Setup.productDualNorm_def]
  repeat rw [Real.sq_sqrt (by positivity)]
  change
    2 * setup.DX ^ 2 * cX (a + b) ^ 2 +
        2 * setup.DY ^ 2 * cY (a + b) ^ 2 ≤
      2 * (2 * setup.DX ^ 2 * cX a ^ 2 +
        2 * setup.DY ^ 2 * cY a ^ 2) +
      2 * (2 * setup.DX ^ 2 * cX b ^ 2 +
        2 * setup.DY ^ 2 * cY b ^ 2)
  nlinarith [mul_le_mul_of_nonneg_left hx_sq hDXcoeff,
    mul_le_mul_of_nonneg_left hy_sq hDYcoeff]

private theorem oracle_noise_square_absorbed_by_oracle_square
    (t : Time) (ω : setup.SamplePath) :
    setup.productDualNorm (setup.oracleNoise t ω) ^ 2 ≤
      2 *
          setup.productDualNorm
            (setup.stochasticOracle (setup.iterate t ω) (setup.sampleAt t ω)) ^ 2 +
        2 * setup.M ^ 2 := by
  exact
    oracleResidual_dual_sq_le_two_oracle_sq_add_two_mean_bound_sq
      (dual := setup.productDualNorm) (noise := setup.oracleNoise t ω)
      (G := setup.stochasticOracle (setup.iterate t ω) (setup.sampleAt t ω))
      (g := setup.meanOracle (setup.iterate t ω)) (M := setup.M)
      (by
        rw [setup.oracleNoise_def t ω])
      (by intro v; simp [Setup.productDualNorm_def])
      (by
        intro a b
        exact setup.productDualNorm_add_sq_le_two_mul_sq_add_two_mul_sq a b)
      (by intro v; exact setup.productDualNorm_neg v)
      (le_of_lt setup.M_pos)
      (setup.meanOracle_productDualNorm_le_M (setup.iterate t ω))

private theorem exp_markov_tail_of_integral_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (f : Ω → ℝ) (lambda : ℝ) (hlambda : 1 ≤ lambda)
    (hf_int : Integrable f μ) (hf_nonneg : ∀ ω, 0 ≤ f ω)
    (h_int_le : ∫ ω, f ω ∂μ ≤ Real.exp 1) :
    μ {ω | f ω > Real.exp (1 + lambda)} ≤
      ENNReal.ofReal (Real.exp (-lambda)) := by
  refine measure_gt_le_of_integral_le_of_nonneg
    (μ := μ) f (Real.exp (1 + lambda)) (Real.exp 1)
    (Real.exp (-lambda)) hf_int hf_nonneg h_int_le
    (le_of_lt (Real.exp_pos _)) ?_ ?_
  · intro _ht
    have hratio :
        Real.exp 1 / Real.exp (1 + lambda) = Real.exp (-lambda) := by
      rw [Real.exp_add]
      calc
        Real.exp 1 / (Real.exp 1 * Real.exp lambda)
            = (Real.exp lambda)⁻¹ := by
              field_simp [Real.exp_ne_zero 1]
        _ = Real.exp (-lambda) := by
              rw [Real.exp_neg]
    exact le_of_eq hratio
  · intro hzero
    exact (Real.exp_pos (1 + lambda)).ne' hzero |>.elim

private theorem productNorm_auxiliary_iterate_sub_le_sqrt_two
    (t : Time) (ω : setup.SamplePath) :
    setup.productNorm ((setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1) ≤
      Real.sqrt 2 := by
  let z : setup.InteriorPoint := setup.auxiliaryCoreProcess (t.1 - 1) ω
  let y : setup.InteriorPoint := setup.iterateCoreProcess (t.1 - 1) ω
  have hlower :
      (1 / 2 : ℝ) * setup.productNorm (z.1 - y.1) ^ 2 ≤
        setup.proxFunction z (setup.interiorPointToPoint y) :=
    product_prox_lower_bound_between_core_points (setup := setup) z y
  have hupper :
      setup.proxFunction z (setup.interiorPointToPoint y) ≤ 1 :=
    setup.productDGF_proxFunction_le_one z (setup.interiorPointToPoint y)
  have hsq : setup.productNorm (z.1 - y.1) ^ 2 ≤ 2 := by
    nlinarith [hlower, hupper]
  have hnorm_nonneg : 0 ≤ setup.productNorm (z.1 - y.1) := by
    simp [Setup.productNorm_def]
  have hsqrt_sq : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by
    rw [Real.sq_sqrt]
    norm_num
  have hsq' : setup.productNorm (z.1 - y.1) ^ 2 ≤ (Real.sqrt 2) ^ 2 := by
    simpa [hsqrt_sq] using hsq
  have hbound :
      setup.productNorm (z.1 - y.1) ≤ Real.sqrt 2 :=
    (sq_le_sq₀ hnorm_nonneg (Real.sqrt_nonneg 2)).mp hsq'
  simpa [z, y, Setup.auxiliaryIterate, Setup.auxiliaryProcess,
    Setup.iterate, Setup.iterateProcess] using hbound

private theorem productNorm_smul_sq_of_nonneg
    {a : ℝ} (ha : 0 ≤ a) (z : Ambient EX EY) :
    setup.productNorm (a • z) ^ 2 =
      a ^ 2 * setup.productNorm z ^ 2 := by
  rw [Setup.productNorm_def, Setup.productNorm_def]
  repeat rw [Real.sq_sqrt (by positivity)]
  simp [map_smul_eq_mul, abs_of_nonneg ha]
  ring

private theorem crossTermQuery_direction_productNorm_le_gamma_sqrt_two
    (t : Time) (ω : setup.SamplePath) :
    setup.productNorm ((setup.crossTermQuery t ω).2) ≤
      setup.gamma t * Real.sqrt 2 := by
  have hgamma_nonneg : 0 ≤ setup.gamma t := le_of_lt (setup.hgamma_pos t)
  have hdir :=
    productNorm_auxiliary_iterate_sub_le_sqrt_two (setup := setup) t ω
  have hleft_nonneg : 0 ≤ setup.productNorm ((setup.crossTermQuery t ω).2) := by
    simp [Setup.productNorm_def]
  have hright_nonneg : 0 ≤ setup.gamma t * Real.sqrt 2 :=
    mul_nonneg hgamma_nonneg (Real.sqrt_nonneg 2)
  rw [← sq_le_sq₀ hleft_nonneg hright_nonneg]
  have hleft_sq :
      setup.productNorm ((setup.crossTermQuery t ω).2) ^ 2 =
        setup.gamma t ^ 2 *
          setup.productNorm
            ((setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1) ^ 2 := by
    rw [Setup.crossTermQuery_snd]
    have hvec :
        setup.gamma t • ((setup.iterate t ω).1 - (setup.auxiliaryIterate t ω).1) =
          -(setup.gamma t •
              ((setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1)) := by
      rw [← smul_neg, neg_sub]
    rw [hvec]
    rw [setup.productNorm_neg]
    exact productNorm_smul_sq_of_nonneg (setup := setup) hgamma_nonneg
      ((setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1)
  have hdir_sq :
      setup.productNorm
            ((setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1) ^ 2 ≤
        (Real.sqrt 2) ^ 2 := by
    exact pow_le_pow_left₀ (by simp [Setup.productNorm_def]) hdir 2
  calc
    setup.productNorm ((setup.crossTermQuery t ω).2) ^ 2
        = setup.gamma t ^ 2 *
          setup.productNorm
            ((setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1) ^ 2 :=
          hleft_sq
    _ ≤ setup.gamma t ^ 2 * (Real.sqrt 2) ^ 2 :=
          mul_le_mul_of_nonneg_left hdir_sq (sq_nonneg (setup.gamma t))
    _ = (setup.gamma t * Real.sqrt 2) ^ 2 := by ring

private theorem abs_auxiliary_cross_term_le_gamma_dual_sqrt_two
    (t : Time) (ω : setup.SamplePath) :
    |setup.gamma t *
        ⟪(setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1,
          setup.oracleNoise t ω⟫_ℝ| ≤
      setup.gamma t *
        (setup.productDualNorm (setup.oracleNoise t ω) * Real.sqrt 2) := by
  have hinner0 :=
    abs_inner_le_productDualNorm_mul_productNorm (setup := setup)
      (setup.oracleNoise t ω)
      ((setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1)
  have hinner :
      |⟪(setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1,
          setup.oracleNoise t ω⟫_ℝ| ≤
        setup.productDualNorm (setup.oracleNoise t ω) *
          setup.productNorm
            ((setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1) := by
    simpa [real_inner_comm] using hinner0
  have hdir :=
    productNorm_auxiliary_iterate_sub_le_sqrt_two (setup := setup) t ω
  have hdual_nonneg :
      0 ≤ setup.productDualNorm (setup.oracleNoise t ω) := by
    simp [Setup.productDualNorm_def]
  have hinner_bound :
      |⟪(setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1,
          setup.oracleNoise t ω⟫_ℝ| ≤
        setup.productDualNorm (setup.oracleNoise t ω) * Real.sqrt 2 :=
    hinner.trans (mul_le_mul_of_nonneg_left hdir hdual_nonneg)
  have hgamma_nonneg : 0 ≤ setup.gamma t := le_of_lt (setup.hgamma_pos t)
  calc
    |setup.gamma t *
        ⟪(setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1,
          setup.oracleNoise t ω⟫_ℝ| =
      setup.gamma t *
        |⟪(setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1,
          setup.oracleNoise t ω⟫_ℝ| := by
        rw [abs_mul, abs_of_nonneg hgamma_nonneg]
    _ ≤ setup.gamma t *
        (setup.productDualNorm (setup.oracleNoise t ω) * Real.sqrt 2) :=
      mul_le_mul_of_nonneg_left hinner_bound hgamma_nonneg

private theorem auxiliary_cross_term_sq_le_two_gamma_sq_dual_sq
    (t : Time) (ω : setup.SamplePath) :
    (setup.gamma t *
        ⟪(setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1,
          setup.oracleNoise t ω⟫_ℝ) ^ 2 ≤
      2 * setup.gamma t ^ 2 *
        setup.productDualNorm (setup.oracleNoise t ω) ^ 2 := by
  let x : ℝ :=
    setup.gamma t *
      ⟪(setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1,
        setup.oracleNoise t ω⟫_ℝ
  let y : ℝ :=
    setup.gamma t *
      (setup.productDualNorm (setup.oracleNoise t ω) * Real.sqrt 2)
  have hxy : |x| ≤ y := by
    simpa [x, y] using
      abs_auxiliary_cross_term_le_gamma_dual_sqrt_two (setup := setup) t ω
  have hsq_abs : |x| ^ 2 ≤ y ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg x) hxy 2
  have hx_sq : x ^ 2 = |x| ^ 2 := by
    rw [sq_abs]
  have hy_sq :
      y ^ 2 =
        2 * setup.gamma t ^ 2 *
          setup.productDualNorm (setup.oracleNoise t ω) ^ 2 := by
    dsimp [y]
    rw [mul_pow, mul_pow, Real.sq_sqrt]
    · ring
    · norm_num
  calc
    (setup.gamma t *
        ⟪(setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1,
          setup.oracleNoise t ω⟫_ℝ) ^ 2 = x ^ 2 := by rfl
    _ = |x| ^ 2 := hx_sq
    _ ≤ y ^ 2 := hsq_abs
    _ = 2 * setup.gamma t ^ 2 *
        setup.productDualNorm (setup.oracleNoise t ω) ^ 2 := hy_sq

private theorem auxiliary_cross_term_scaled_sq_le_oracle_scaled_sq_add_half
    (t : Time) (ω : setup.SamplePath) :
    (setup.gamma t *
        ⟪(setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1,
          setup.oracleNoise t ω⟫_ℝ) ^ 2 /
        (8 * setup.gamma t ^ 2 * setup.M ^ 2) ≤
      setup.productDualNorm
          (setup.stochasticOracle (setup.iterate t ω) (setup.sampleAt t ω)) ^ 2 /
          (2 * setup.M ^ 2) +
        (1 / 2 : ℝ) := by
  let cross : ℝ :=
    setup.gamma t *
      ⟪(setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1,
        setup.oracleNoise t ω⟫_ℝ
  let noiseSq : ℝ := setup.productDualNorm (setup.oracleNoise t ω) ^ 2
  let oracleSq : ℝ :=
    setup.productDualNorm
      (setup.stochasticOracle (setup.iterate t ω) (setup.sampleAt t ω)) ^ 2
  have hcross_sq :
      cross ^ 2 ≤ 2 * setup.gamma t ^ 2 * noiseSq := by
    simpa [cross, noiseSq] using
      auxiliary_cross_term_sq_le_two_gamma_sq_dual_sq (setup := setup) t ω
  have hnoise_absorb : noiseSq ≤ 2 * oracleSq + 2 * setup.M ^ 2 := by
    simpa [noiseSq, oracleSq] using
      oracle_noise_square_absorbed_by_oracle_square (setup := setup) t ω
  have hgamma_sq_pos : 0 < setup.gamma t ^ 2 := sq_pos_of_pos (setup.hgamma_pos t)
  have hM_sq_pos : 0 < setup.M ^ 2 := sq_pos_of_pos setup.M_pos
  have hden_pos : 0 < 8 * setup.gamma t ^ 2 * setup.M ^ 2 := by
    positivity
  have hden4_pos : 0 < 4 * setup.M ^ 2 := by
    positivity
  have hstep1 :
      cross ^ 2 / (8 * setup.gamma t ^ 2 * setup.M ^ 2) ≤
        (2 * setup.gamma t ^ 2 * noiseSq) /
          (8 * setup.gamma t ^ 2 * setup.M ^ 2) :=
    div_le_div_of_nonneg_right hcross_sq (le_of_lt hden_pos)
  have hstep1_eq :
      (2 * setup.gamma t ^ 2 * noiseSq) /
          (8 * setup.gamma t ^ 2 * setup.M ^ 2) =
        noiseSq / (4 * setup.M ^ 2) := by
    field_simp [ne_of_gt (setup.hgamma_pos t), ne_of_gt setup.M_pos,
      ne_of_gt hgamma_sq_pos, ne_of_gt hM_sq_pos]
    ring_nf
  have hstep2 :
      noiseSq / (4 * setup.M ^ 2) ≤
        (2 * oracleSq + 2 * setup.M ^ 2) / (4 * setup.M ^ 2) :=
    div_le_div_of_nonneg_right hnoise_absorb (le_of_lt hden4_pos)
  have hstep2_eq :
      (2 * oracleSq + 2 * setup.M ^ 2) / (4 * setup.M ^ 2) =
        oracleSq / (2 * setup.M ^ 2) + (1 / 2 : ℝ) := by
    field_simp [ne_of_gt setup.M_pos, ne_of_gt hM_sq_pos]
    ring_nf
  calc
    (setup.gamma t *
        ⟪(setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1,
          setup.oracleNoise t ω⟫_ℝ) ^ 2 /
        (8 * setup.gamma t ^ 2 * setup.M ^ 2) =
      cross ^ 2 / (8 * setup.gamma t ^ 2 * setup.M ^ 2) := by rfl
    _ ≤ (2 * setup.gamma t ^ 2 * noiseSq) /
          (8 * setup.gamma t ^ 2 * setup.M ^ 2) := hstep1
    _ = noiseSq / (4 * setup.M ^ 2) := hstep1_eq
    _ ≤ (2 * oracleSq + 2 * setup.M ^ 2) / (4 * setup.M ^ 2) := hstep2
    _ = oracleSq / (2 * setup.M ^ 2) + (1 / 2 : ℝ) := hstep2_eq
    _ =
      setup.productDualNorm
          (setup.stochasticOracle (setup.iterate t ω) (setup.sampleAt t ω)) ^ 2 /
          (2 * setup.M ^ 2) +
        (1 / 2 : ℝ) := by rfl

set_option maxHeartbeats 1200000

private theorem fixed_fiber_cross_term_scaled_sq_le_oracle_scaled_sq_add_half
    (t : Time) (q : setup.Point × Ambient EX EY)
    (hq : setup.productNorm q.2 ≤ setup.gamma t * Real.sqrt 2)
    (ξ : setup.SamplePoint) :
    (-⟪q.2, setup.stochasticOracle q.1 ξ - setup.meanOracle q.1⟫_ℝ) ^ 2 /
        (8 * setup.gamma t ^ 2 * setup.M ^ 2) ≤
      setup.productDualNorm (setup.stochasticOracle q.1 ξ) ^ 2 /
          (2 * setup.M ^ 2) +
        (1 / 2 : ℝ) := by
  refine
    boundedDirection_oracleResidual_inner_scaled_sq_le_oracle_sq_add_half
      (primalNorm := setup.productNorm) (dualNorm := setup.productDualNorm)
      (G := setup.stochasticOracle) (g := setup.meanOracle)
      (x := q.1) (ξ := ξ) (d := q.2)
      (γ := setup.gamma t) (M := setup.M) (R := Real.sqrt 2)
      (hγ_pos := setup.hgamma_pos t) (hM_pos := setup.M_pos)
      (hR_sq_le_two := ?_) (hdir := hq) (hsupport := ?_)
      (hdual_nonneg := ?_) (hdual_add_sq := ?_) (hdual_neg := ?_)
      (hmean_le := setup.meanOracle_productDualNorm_le_M q.1)
  · rw [Real.sq_sqrt]
    norm_num
  · intro z w
    have hinner0 :=
      abs_inner_le_productDualNorm_mul_productNorm (setup := setup) z w
    simpa [real_inner_comm, mul_comm] using hinner0
  · intro z
    simp [Setup.productDualNorm_def]
  · intro a b
    exact setup.productDualNorm_add_sq_le_two_mul_sq_add_two_mul_sq a b
  · intro z
    simp [Setup.productDualNorm_def]

private theorem fixed_fiber_cross_term_exp_square_mgf_bound
    (t : Time) (q : setup.Point × Ambient EX EY)
    (hq : setup.productNorm q.2 ≤ setup.gamma t * Real.sqrt 2)
    (hexp : setup.exponentialMomentOracleBound) :
    Integrable
        (fun ξ =>
          Real.exp
            (((-⟪q.2,
              setup.stochasticOracle q.1 ξ - setup.meanOracle q.1⟫_ℝ) ^ 2) /
              (8 * setup.gamma t ^ 2 * setup.M ^ 2)))
        setup.P ∧
      ∫ ξ,
          Real.exp
            (((-⟪q.2,
              setup.stochasticOracle q.1 ξ - setup.meanOracle q.1⟫_ℝ) ^ 2) /
              (8 * setup.gamma t ^ 2 * setup.M ^ 2)) ∂setup.P ≤
        Real.exp 1 := by
  letI : IsProbabilityMeasure setup.P := setup.hP_prob
  refine
    boundedDirection_oracleResidual_exp_square_mgf_bound_of_oracle_exp_moment
      (P := setup.P) (G := setup.stochasticOracle) (g := setup.meanOracle)
      (primalNorm := setup.productNorm) (dualNorm := setup.productDualNorm)
      (x := q.1) (d := q.2) (γ := setup.gamma t) (M := setup.M)
      (R := Real.sqrt 2) (hGx_meas := ?_)
      (horacle_exp_int :=
        (product_stochastic_oracle_exp_moment_bound (setup := setup) q.1 hexp).1)
      (horacle_exp_bound :=
        (product_stochastic_oracle_exp_moment_bound (setup := setup) q.1 hexp).2)
      (hγ_pos := setup.hgamma_pos t) (hM_pos := setup.M_pos)
      (hR_sq_le_two := ?_) (hdir := hq) (hsupport := ?_)
      (hdual_nonneg := ?_) (hdual_add_sq := ?_) (hdual_neg := ?_)
      (hmean_le := setup.meanOracle_productDualNorm_le_M q.1)
  · have hpair :
        Measurable (fun ξ : setup.SamplePoint => (q.1, ξ)) :=
      (measurable_const : Measurable (fun _ξ : setup.SamplePoint => q.1)).prodMk
        measurable_id
    exact setup.stochasticOracle_measurable.comp hpair
  · rw [Real.sq_sqrt]
    norm_num
  · intro z w
    have hinner0 :=
      abs_inner_le_productDualNorm_mul_productNorm (setup := setup) z w
    simpa [real_inner_comm, mul_comm] using hinner0
  · intro z
    simp [Setup.productDualNorm_def]
  · intro a b
    exact setup.productDualNorm_add_sq_le_two_mul_sq_add_two_mul_sq a b
  · intro z
    simp [Setup.productDualNorm_def]

/-- Finite exponential recurrence obtained from the one-step weighted mgf bound
in Lemma 4.1.  This helper is deliberately probability-interface neutral: the
hard source-specific work is proving `hone` from strict-past measurability and
fresh-sample independence. -/
private theorem finite_iid_stream_cross_term_mgf_le_of_one_step
    (N : ℕ) (ν : ℝ) (_hν : 0 ≤ ν)
    (hone :
      ∀ t ∈ outputTimes N,
        ∀ H : setup.SamplePath → ℝ,
          (∀ ω, 0 ≤ H ω) →
          Integrable H setup.pathMeasure →
          Integrable
              (fun ω =>
                H ω *
                  Real.exp
                    (ν *
                      (setup.gamma t *
                        ⟪(setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1,
                          setup.oracleNoise t ω⟫_ℝ)))
              setup.pathMeasure ∧
            ∫ ω,
                H ω *
                  Real.exp
                    (ν *
                      (setup.gamma t *
                        ⟪(setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1,
                          setup.oracleNoise t ω⟫_ℝ)) ∂setup.pathMeasure ≤
              Real.exp
                (3 * ν ^ 2 * (8 * setup.gamma t ^ 2 * setup.M ^ 2) / 4) *
                ∫ ω, H ω ∂setup.pathMeasure) :
    Integrable
        (fun ω =>
          Real.exp
            (ν *
              (∑ t ∈ outputTimes N,
                setup.gamma t *
                  ⟪(setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1,
                    setup.oracleNoise t ω⟫_ℝ)))
        setup.pathMeasure ∧
      ∫ ω,
          Real.exp
            (ν *
              (∑ t ∈ outputTimes N,
                setup.gamma t *
                  ⟪(setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1,
                    setup.oracleNoise t ω⟫_ℝ)) ∂setup.pathMeasure ≤
        Real.exp
          (∑ t ∈ outputTimes N,
            3 * ν ^ 2 * (8 * setup.gamma t ^ 2 * setup.M ^ 2) / 4) := by
  classical
  letI : IsProbabilityMeasure setup.pathMeasure := setup.pathMeasure_isProbabilityMeasure
  let ζ : Time → setup.SamplePath → ℝ := fun t ω =>
    setup.gamma t *
      ⟪(setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1,
        setup.oracleNoise t ω⟫_ℝ
  let c : Time → ℝ := fun t =>
    3 * ν ^ 2 * (8 * setup.gamma t ^ 2 * setup.M ^ 2) / 4
  exact integrable_exp_weighted_sum_le_exp_sum_of_weighted_one_step_mgf
    (P := setup.pathMeasure) (s := outputTimes N) (ζ := ζ) (c := c) (ν := ν)
    (by
      intro t ht H hH_nonneg hH_int
      simpa [ζ, c] using hone t ht H hH_nonneg hH_int)

/-- Product-law integrability transfer when the fixed-fiber bound is a
measurable integrable function of the independent prefix state.

This is the integrability companion to
`integral_comp_le_integral_comp_bound_of_indep_fixed_integral_bound`; it is the
shape needed for Lemma 4.1 prefix weights, where the fixed-fiber bound is
`B(W) = const * H`. -/
private theorem integrable_comp_of_indep_fixed_integral_comp_bound
    {Ω W S : Type*} [MeasurableSpace Ω] [MeasurableSpace W] [MeasurableSpace S]
    {P : Measure Ω} {ν : Measure S} [IsFiniteMeasure P]
    {φ : W → S → ℝ} {B : W → ℝ} {X : Ω → W} {Y : Ω → S}
    (hφ_prod :
      AEStronglyMeasurable
        (fun p : W × S => φ p.1 p.2) ((Measure.map X P).prod ν))
    (hB_aesm : AEStronglyMeasurable B (Measure.map X P))
    (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    (h_indep : IndepFun X Y P)
    (h_dist : Measure.map Y P = ν)
    (hφ_nonneg : ∀ w s, 0 ≤ φ w s)
    (hfixed_int : ∀ w, Integrable (fun s => φ w s) ν)
    (hB_int : Integrable (fun ω => B (X ω)) P)
    (hfixed_bound : ∀ w, ∫ s, φ w s ∂ν ≤ B w) :
    Integrable (fun ω => φ (X ω) (Y ω)) P := by
  exact _root_.integrable_comp_of_indep_fixed_integral_comp_bound_aestronglyMeasurable
    (hφ_prod := hφ_prod) (hB_aesm := hB_aesm) (hX := hX) (hY := hY)
    (h_indep := h_indep) (h_dist := h_dist) (hφ_nonneg := hφ_nonneg)
    (hfixed_int := hfixed_int) (hB_int := hB_int) (hfixed_bound := hfixed_bound)

/-- A law-scoped variable-bound version of the independent product-law integral
transfer.  This pairs with
`integrable_comp_of_indep_fixed_integral_comp_bound` above when the product
kernel is only a.e.-strongly measurable under the generated product law. -/
private theorem integral_comp_le_integral_comp_bound_of_indep_fixed_integral_bound_aestronglyMeasurable
    {Ω W S : Type*} [MeasurableSpace Ω] [MeasurableSpace W] [MeasurableSpace S]
    {P : Measure Ω} {ν : Measure S} [IsFiniteMeasure P]
    {φ : W → S → ℝ} {B : W → ℝ} {X : Ω → W} {Y : Ω → S}
    (hφ_prod :
      AEStronglyMeasurable
        (fun p : W × S => φ p.1 p.2) ((Measure.map X P).prod ν))
    (hB_aesm : AEStronglyMeasurable B (Measure.map X P))
    (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    (h_indep : IndepFun X Y P)
    (h_dist : Measure.map Y P = ν)
    (h_int : Integrable (fun ω => φ (X ω) (Y ω)) P)
    (hB_int : Integrable (fun ω => B (X ω)) P)
    (hfixed_bound : ∀ w, ∫ s, φ w s ∂ν ≤ B w) :
    ∫ ω, φ (X ω) (Y ω) ∂P ≤ ∫ ω, B (X ω) ∂P := by
  exact _root_.integral_comp_le_integral_comp_bound_of_indep_fixed_integral_bound_aestronglyMeasurable
    (hφ_prod := hφ_prod) (hB_aesm := hB_aesm) (hX := hX) (hY := hY)
    (h_indep := h_indep) (h_dist := h_dist) (h_int := h_int) (hB_int := hB_int)
    (hfixed_bound := hfixed_bound)

set_option maxHeartbeats 1200000

/-- The strict-past sample sigma-algebra is independent of the current iid
sample coordinate. -/
private theorem strictPast_indep_sampleAt (t : Time) :
    Indep
      (⨆ j < t.1 - 1,
        MeasurableSpace.comap (fun ω : setup.SamplePath => ω j)
          (by infer_instance : MeasurableSpace setup.SamplePoint))
      (MeasurableSpace.comap (setup.sampleAt t)
        (by infer_instance : MeasurableSpace setup.SamplePoint))
      setup.pathMeasure := by
  letI : IsProbabilityMeasure setup.P := setup.hP_prob
  simpa [Setup.pathMeasure, Setup.sampleAt] using
    (ProbabilityTheory.iIndepFun.indep_prefixFiltration_future
      (ξ := fun n (ω : setup.SamplePath) => ω n)
      (hξ_measurable := fun n => (measurable_pi_apply n :
        Measurable (fun ω : setup.SamplePath => ω n)))
      (hξ_iIndep := SOptLib.iidStreamLaw_iIndepFun_eval setup.P)
      (n := t.1 - 1)
      (i := t.1 - 1)
      le_rfl)

/-- Product-law core for one Lemma 4.1 weighted step.

This isolates the Fubini/product-law part from the strict-past freshness
bookkeeping: once the nonnegative prefix weight paired with the cross-term
query is independent of the current iid sample, a fixed-fiber exponential MGF
bound transfers to the weighted path-space inequality. -/
private theorem weighted_one_step_mgf_transfer_of_indep_state
    (t : Time) (ν c : ℝ) (H : setup.SamplePath → ℝ)
    (hH_nonneg : ∀ ω, 0 ≤ H ω)
    (hH_int : Integrable H setup.pathMeasure)
    (hstate_aemeas :
      AEMeasurable
        (fun ω : setup.SamplePath =>
          ((⟨H ω, hH_nonneg ω⟩ : {r : ℝ // 0 ≤ r}), setup.crossTermQuery t ω))
        setup.pathMeasure)
    (hstate_indep :
      IndepFun
        (fun ω : setup.SamplePath =>
          ((⟨H ω, hH_nonneg ω⟩ : {r : ℝ // 0 ≤ r}), setup.crossTermQuery t ω))
        (setup.sampleAt t) setup.pathMeasure)
    (hfixed_int :
      ∀ q : setup.Point × Ambient EX EY,
        Integrable
          (fun ξ =>
            Real.exp
              (ν *
                (-⟪q.2, setup.stochasticOracle q.1 ξ - setup.meanOracle q.1⟫_ℝ)))
          setup.P)
    (hfixed_bound :
      ∀ q : setup.Point × Ambient EX EY,
        ∫ ξ,
            Real.exp
              (ν *
                (-⟪q.2, setup.stochasticOracle q.1 ξ - setup.meanOracle q.1⟫_ℝ))
            ∂setup.P ≤ Real.exp c) :
    Integrable
        (fun ω =>
          H ω *
            Real.exp
              (ν *
                (setup.gamma t *
                  ⟪(setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1,
                    setup.oracleNoise t ω⟫_ℝ)))
        setup.pathMeasure ∧
      ∫ ω,
          H ω *
            Real.exp
              (ν *
                (setup.gamma t *
                  ⟪(setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1,
                    setup.oracleNoise t ω⟫_ℝ)) ∂setup.pathMeasure ≤
        Real.exp c * ∫ ω, H ω ∂setup.pathMeasure := by
/-
  letI : IsProbabilityMeasure setup.pathMeasure := setup.pathMeasure_isProbabilityMeasure
  let score : setup.Point × Ambient EX EY → setup.SamplePoint → ℝ := fun q ξ =>
    -⟪q.2, setup.stochasticOracle q.1 ξ - setup.meanOracle q.1⟫_ℝ
  let Z : setup.SamplePath → ℝ := fun ω =>
    setup.gamma t *
      ⟪(setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1,
        setup.oracleNoise t ω⟫_ℝ
  let past : MeasurableSpace setup.SamplePath :=
    (⨆ j < t.1 - 1,
      MeasurableSpace.comap (fun ω : setup.SamplePath => ω j)
        (by infer_instance : MeasurableSpace setup.SamplePoint))
  have hH_past : Measurable[past] H := by
    simpa [past] using hH_strict
  have hquery_past : Measurable[past] (setup.crossTermQuery t) := by
    simpa [past] using hquery_strict
  let past : MeasurableSpace setup.SamplePath :=
    (⨆ j < t.1 - 1,
      MeasurableSpace.comap (fun ω : setup.SamplePath => ω j)
        (by infer_instance : MeasurableSpace setup.SamplePoint))
  have hH_past : Measurable[past] H := by
    simpa [past] using hH_strict
  have hquery_past : Measurable[past] (setup.crossTermQuery t) := by
    simpa [past] using hquery_strict
  have hscore_meas :
      Measurable (fun p : (setup.Point × Ambient EX EY) × setup.SamplePoint =>
        score p.1 p.2) := by
    have hdir :
        Measurable (fun p : (setup.Point × Ambient EX EY) × setup.SamplePoint => p.1.2) :=
      measurable_snd.comp measurable_fst
    have hquery_sample :
        Measurable (fun p : (setup.Point × Ambient EX EY) × setup.SamplePoint =>
          (p.1, p.2)) :=
      measurable_fst.prodMk measurable_snd
    have hres :
        Measurable (fun p : (setup.Point × Ambient EX EY) × setup.SamplePoint =>
          setup.stochasticOracle p.1.1 p.2 - setup.meanOracle p.1.1) :=
      (oracle_residual_product_measurable (setup := setup)).comp hquery_sample
    have hinner :
        Measurable (fun p : (setup.Point × Ambient EX EY) × setup.SamplePoint =>
          ⟪p.1.2, setup.stochasticOracle p.1.1 p.2 - setup.meanOracle p.1.1⟫_ℝ) :=
      continuous_inner.measurable.comp (hdir.prodMk hres)
    simpa [score] using hinner.neg
  have hscore_eq :
      ∀ ω, score (setup.crossTermQuery t ω) (setup.sampleAt t ω) = Z ω := by
    intro ω
    have hvec :
        -((setup.iterate t ω).1 - (setup.auxiliaryIterate t ω).1) =
          (setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1 := by
      abel
    have hsign :
        -⟪setup.gamma t • ((setup.iterate t ω).1 - (setup.auxiliaryIterate t ω).1),
            setup.oracleNoise t ω⟫_ℝ =
          setup.gamma t *
            ⟪(setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1,
              setup.oracleNoise t ω⟫_ℝ := by
      calc
        -⟪setup.gamma t • ((setup.iterate t ω).1 - (setup.auxiliaryIterate t ω).1),
            setup.oracleNoise t ω⟫_ℝ
            = -(setup.gamma t *
                ⟪(setup.iterate t ω).1 - (setup.auxiliaryIterate t ω).1,
                  setup.oracleNoise t ω⟫_ℝ) := by
                rw [real_inner_smul_left]
        _ = setup.gamma t *
              (-⟪(setup.iterate t ω).1 - (setup.auxiliaryIterate t ω).1,
                setup.oracleNoise t ω⟫_ℝ) := by ring
        _ = setup.gamma t *
              ⟪(setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1,
                setup.oracleNoise t ω⟫_ℝ := by
              rw [← inner_neg_left, hvec]
    have harg :
        -⟪(setup.crossTermQuery t ω).2,
          setup.stochasticOracle (setup.crossTermQuery t ω).1 (setup.sampleAt t ω) -
            setup.meanOracle (setup.crossTermQuery t ω).1⟫_ℝ =
          setup.gamma t *
            ⟪(setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1,
              setup.oracleNoise t ω⟫_ℝ := by
      rw [Setup.crossTermQuery, Setup.oracleNoise]
      exact hsign
    simpa [score, Z] using harg
  exact bounded_strictPast_weighted_exp_mgf_transfer_of_fixed_fiber_bound
    (Ω := setup.SamplePath) (S := setup.SamplePoint)
    (Q := setup.Point × Ambient EX EY)
    (mΩ := (MeasurableSpace.pi : MeasurableSpace setup.SamplePath))
    (mS := (by infer_instance : MeasurableSpace setup.SamplePoint))
    (mQ := (by infer_instance : MeasurableSpace (setup.Point × Ambient EX EY)))
    (P := setup.pathMeasure) (νS := setup.P)
    (past := past)
    (sample := setup.sampleAt t) (query := setup.crossTermQuery t)
    (H := H) (R := R) (ν := ν) (c := c)
    (gauge := fun q : setup.Point × Ambient EX EY => setup.productNorm q.2)
    (score := score) (Z := Z)
    hscore_meas hH_past hquery_past (setup.crossTermQuery_aemeasurable t)
    (setup.sampleAt_aemeasurable t) (strictPast_indep_sampleAt (setup := setup) t)
    (by simpa using setup.sampleAt_law t)
    hH_nonneg hH_int hquery_bound hscore_eq
    (by
      intro q
      simpa [score] using hfixed_int q)
    (by
      intro q
      simpa [score] using hfixed_bound q)
-/
  letI : IsProbabilityMeasure setup.pathMeasure := setup.pathMeasure_isProbabilityMeasure
  letI : IsProbabilityMeasure setup.P := setup.hP_prob
  let Weight := {r : ℝ // 0 ≤ r}
  let W := Weight × (setup.Point × Ambient EX EY)
  let X : setup.SamplePath → W :=
    fun ω => ((⟨H ω, hH_nonneg ω⟩ : Weight), setup.crossTermQuery t ω)
  let Y : setup.SamplePath → setup.SamplePoint := setup.sampleAt t
  let φ : W → setup.SamplePoint → ℝ :=
    fun w ξ =>
      (w.1 : ℝ) *
        Real.exp
          (ν *
            (-⟪w.2.2, setup.stochasticOracle w.2.1 ξ - setup.meanOracle w.2.1⟫_ℝ))
  let B : W → ℝ := fun w => Real.exp c * (w.1 : ℝ)
  have hφ_meas :
      Measurable (fun p : W × setup.SamplePoint => φ p.1 p.2) := by
    have hweight :
        Measurable (fun p : W × setup.SamplePoint => ((p.1.1 : Weight) : ℝ)) :=
      measurable_subtype_coe.comp (measurable_fst.comp measurable_fst)
    have hdir :
        Measurable (fun p : W × setup.SamplePoint => p.1.2.2) :=
      measurable_snd.comp (measurable_snd.comp measurable_fst)
    have hquery_sample :
        Measurable
          (fun p : W × setup.SamplePoint =>
            ((p.1.2 : setup.Point × Ambient EX EY), p.2)) :=
      (measurable_snd.comp measurable_fst).prod measurable_snd
    have hres :
        Measurable
          (fun p : W × setup.SamplePoint =>
            setup.stochasticOracle p.1.2.1 p.2 - setup.meanOracle p.1.2.1) :=
      (oracle_residual_product_measurable (setup := setup)).comp hquery_sample
    have hinner :
        Measurable
          (fun p : W × setup.SamplePoint =>
            ⟪p.1.2.2,
              setup.stochasticOracle p.1.2.1 p.2 - setup.meanOracle p.1.2.1⟫_ℝ) :=
      continuous_inner.measurable.comp (hdir.prodMk hres)
    have hexp :
        Measurable
          (fun p : W × setup.SamplePoint =>
            Real.exp
              (ν *
                (-⟪p.1.2.2,
                  setup.stochasticOracle p.1.2.1 p.2 -
                    setup.meanOracle p.1.2.1⟫_ℝ))) :=
      (Real.continuous_exp.comp
        (continuous_const.mul continuous_id.neg)).measurable.comp hinner
    simpa [φ] using hweight.mul hexp
  have hφ_prod :
      AEStronglyMeasurable
        (fun p : W × setup.SamplePoint => φ p.1 p.2)
        ((Measure.map X setup.pathMeasure).prod setup.P) :=
    hφ_meas.aestronglyMeasurable
  have hB_meas : Measurable B := by
    have hweight : Measurable (fun w : W => (w.1 : ℝ)) :=
      measurable_subtype_coe.comp measurable_fst
    simpa [B] using measurable_const.mul hweight
  have hB_aesm : AEStronglyMeasurable B (Measure.map X setup.pathMeasure) :=
    hB_meas.aestronglyMeasurable
  have hX_aemeas : AEMeasurable X setup.pathMeasure := by
    simpa [X, Weight] using hstate_aemeas
  have hY_aemeas : AEMeasurable Y setup.pathMeasure := by
    simpa [Y] using setup.sampleAt_aemeasurable t
  have h_indep : IndepFun X Y setup.pathMeasure := by
    simpa [X, Y, Weight] using hstate_indep
  have hY_law : Measure.map Y setup.pathMeasure = setup.P := by
    simpa [Y] using setup.sampleAt_law t
  have hφ_nonneg : ∀ w ξ, 0 ≤ φ w ξ := by
    intro w ξ
    exact mul_nonneg w.1.2 (le_of_lt (Real.exp_pos _))
  have hfixed_int' : ∀ w : W, Integrable (fun ξ => φ w ξ) setup.P := by
    intro w
    simpa [φ] using (hfixed_int w.2).const_mul (w.1 : ℝ)
  have hB_int : Integrable (fun ω => B (X ω)) setup.pathMeasure := by
    simpa [B, X, Weight] using hH_int.const_mul (Real.exp c)
  have hfixed_bound' : ∀ w : W, ∫ ξ, φ w ξ ∂setup.P ≤ B w := by
    intro w
    have hw_nonneg : 0 ≤ (w.1 : ℝ) := w.1.2
    calc
      ∫ ξ, φ w ξ ∂setup.P
          = (w.1 : ℝ) *
              ∫ ξ,
                Real.exp
                  (ν *
                    (-⟪w.2.2,
                      setup.stochasticOracle w.2.1 ξ -
                        setup.meanOracle w.2.1⟫_ℝ)) ∂setup.P := by
            simp [φ, MeasureTheory.integral_const_mul]
      _ ≤ (w.1 : ℝ) * Real.exp c :=
            mul_le_mul_of_nonneg_left (hfixed_bound w.2) hw_nonneg
      _ = B w := by simp [B, mul_comm, mul_left_comm, mul_assoc]
  have hcomp_int :
      Integrable (fun ω => φ (X ω) (Y ω)) setup.pathMeasure :=
    integrable_comp_of_indep_fixed_integral_comp_bound
      (P := setup.pathMeasure) (ν := setup.P)
      (φ := φ) (B := B) (X := X) (Y := Y)
      hφ_prod hB_aesm hX_aemeas hY_aemeas h_indep hY_law
      hφ_nonneg hfixed_int' hB_int hfixed_bound'
  have hcomp_le :
      ∫ ω, φ (X ω) (Y ω) ∂setup.pathMeasure ≤
        ∫ ω, B (X ω) ∂setup.pathMeasure :=
    integral_comp_le_integral_comp_bound_of_indep_fixed_integral_bound_aestronglyMeasurable
      (P := setup.pathMeasure) (ν := setup.P)
      (φ := φ) (B := B) (X := X) (Y := Y)
      hφ_prod hB_aesm hX_aemeas hY_aemeas h_indep hY_law
      hcomp_int hB_int hfixed_bound'
  have hφ_comp_eq :
      (fun ω => φ (X ω) (Y ω)) =
        (fun ω =>
          H ω *
            Real.exp
              (ν *
                (setup.gamma t *
                  ⟪(setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1,
                    setup.oracleNoise t ω⟫_ℝ))) := by
    funext ω
    have hvec :
        -((setup.iterate t ω).1 - (setup.auxiliaryIterate t ω).1) =
          (setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1 := by
      abel
    have hsign :
        -⟪setup.gamma t • ((setup.iterate t ω).1 - (setup.auxiliaryIterate t ω).1),
            setup.oracleNoise t ω⟫_ℝ =
          setup.gamma t *
            ⟪(setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1,
              setup.oracleNoise t ω⟫_ℝ := by
      calc
        -⟪setup.gamma t • ((setup.iterate t ω).1 - (setup.auxiliaryIterate t ω).1),
            setup.oracleNoise t ω⟫_ℝ
            = -(setup.gamma t *
                ⟪(setup.iterate t ω).1 - (setup.auxiliaryIterate t ω).1,
                  setup.oracleNoise t ω⟫_ℝ) := by
                rw [real_inner_smul_left]
        _ = setup.gamma t *
              (-⟪(setup.iterate t ω).1 - (setup.auxiliaryIterate t ω).1,
                setup.oracleNoise t ω⟫_ℝ) := by ring
        _ = setup.gamma t *
              ⟪(setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1,
                setup.oracleNoise t ω⟫_ℝ := by
              rw [← inner_neg_left, hvec]
    have harg :
        ν *
            (-⟪(setup.crossTermQuery t ω).2,
              setup.stochasticOracle (setup.crossTermQuery t ω).1 (setup.sampleAt t ω) -
                setup.meanOracle (setup.crossTermQuery t ω).1⟫_ℝ) =
          ν *
            (setup.gamma t *
              ⟪(setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1,
                setup.oracleNoise t ω⟫_ℝ) := by
      rw [Setup.crossTermQuery, Setup.oracleNoise]
      exact congrArg (fun r : ℝ => ν * r) hsign
    change
      H ω *
          Real.exp
            (ν *
              (-⟪(setup.crossTermQuery t ω).2,
                setup.stochasticOracle (setup.crossTermQuery t ω).1 (setup.sampleAt t ω) -
                  setup.meanOracle (setup.crossTermQuery t ω).1⟫_ℝ)) =
        H ω *
          Real.exp
            (ν *
              (setup.gamma t *
                ⟪(setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1,
                  setup.oracleNoise t ω⟫_ℝ))
    rw [harg]
  have hB_comp_eq :
      (fun ω => B (X ω)) = fun ω => Real.exp c * H ω := by
    funext ω
    simp [B, X, Weight]
  constructor
  · simpa [hφ_comp_eq] using hcomp_int
  · calc
      ∫ ω,
          H ω *
            Real.exp
              (ν *
                (setup.gamma t *
                  ⟪(setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1,
                    setup.oracleNoise t ω⟫_ℝ)) ∂setup.pathMeasure
          = ∫ ω, φ (X ω) (Y ω) ∂setup.pathMeasure := by
              rw [hφ_comp_eq]
      _ ≤ ∫ ω, B (X ω) ∂setup.pathMeasure := hcomp_le
      _ = Real.exp c * ∫ ω, H ω ∂setup.pathMeasure := by
              rw [hB_comp_eq, MeasureTheory.integral_const_mul]

set_option maxHeartbeats 4000000 in
/-- Bounded-query variant of one Lemma 4.1 weighted step.

The state records the cross-term query in the subtype
`{q // productNorm q.2 ≤ R}`, so the fixed-fiber MGF premise is required only
on the range actually produced by the strict-past query. -/
private theorem bounded_prefix_weighted_one_step_mgf_transfer
    (t : Time) (ν c R : ℝ) (H : setup.SamplePath → ℝ)
    (hH_strict :
      Measurable[
        (⨆ j < t.1 - 1,
          MeasurableSpace.comap (fun ω : setup.SamplePath => ω j)
            (by infer_instance : MeasurableSpace setup.SamplePoint))]
        H)
    (hquery_strict :
      Measurable[
        (⨆ j < t.1 - 1,
          MeasurableSpace.comap (fun ω : setup.SamplePath => ω j)
            (by infer_instance : MeasurableSpace setup.SamplePoint))]
        (setup.crossTermQuery t))
    (hH_nonneg : ∀ ω, 0 ≤ H ω)
    (hH_int : Integrable H setup.pathMeasure)
    (hquery_bound :
      ∀ ω, setup.productNorm ((setup.crossTermQuery t ω).2) ≤ R)
    (hfixed_int :
      ∀ q : {q : setup.Point × Ambient EX EY // setup.productNorm q.2 ≤ R},
        Integrable
          (fun ξ =>
            Real.exp
              (ν *
                (-⟪(q : setup.Point × Ambient EX EY).2,
                  setup.stochasticOracle (q : setup.Point × Ambient EX EY).1 ξ -
                    setup.meanOracle (q : setup.Point × Ambient EX EY).1⟫_ℝ)))
          setup.P)
    (hfixed_bound :
      ∀ q : {q : setup.Point × Ambient EX EY // setup.productNorm q.2 ≤ R},
        ∫ ξ,
            Real.exp
              (ν *
                (-⟪(q : setup.Point × Ambient EX EY).2,
                  setup.stochasticOracle (q : setup.Point × Ambient EX EY).1 ξ -
                    setup.meanOracle (q : setup.Point × Ambient EX EY).1⟫_ℝ))
            ∂setup.P ≤ Real.exp c) :
    Integrable
        (fun ω =>
          H ω *
            Real.exp
              (ν *
                (setup.gamma t *
                  ⟪(setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1,
                    setup.oracleNoise t ω⟫_ℝ)))
        setup.pathMeasure ∧
      ∫ ω,
          H ω *
            Real.exp
              (ν *
                (setup.gamma t *
                  ⟪(setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1,
                    setup.oracleNoise t ω⟫_ℝ)) ∂setup.pathMeasure ≤
        Real.exp c * ∫ ω, H ω ∂setup.pathMeasure := by
  letI : IsProbabilityMeasure setup.pathMeasure := setup.pathMeasure_isProbabilityMeasure
  let score : setup.Point × Ambient EX EY → setup.SamplePoint → ℝ := fun q ξ =>
    -⟪q.2, setup.stochasticOracle q.1 ξ - setup.meanOracle q.1⟫_ℝ
  let Z : setup.SamplePath → ℝ := fun ω =>
    setup.gamma t *
      ⟪(setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1,
        setup.oracleNoise t ω⟫_ℝ
  let past : MeasurableSpace setup.SamplePath :=
    (⨆ j < t.1 - 1,
      MeasurableSpace.comap (fun ω : setup.SamplePath => ω j)
        (by infer_instance : MeasurableSpace setup.SamplePoint))
  have hH_past : Measurable[past] H := by
    simpa [past] using hH_strict
  have hquery_past : Measurable[past] (setup.crossTermQuery t) := by
    simpa [past] using hquery_strict
  have hscore_meas :
      Measurable (fun p : (setup.Point × Ambient EX EY) × setup.SamplePoint =>
        score p.1 p.2) := by
    have hdir :
        Measurable (fun p : (setup.Point × Ambient EX EY) × setup.SamplePoint => p.1.2) :=
      measurable_snd.comp measurable_fst
    have hquery_sample :
        Measurable (fun p : (setup.Point × Ambient EX EY) × setup.SamplePoint =>
          (p.1, p.2)) :=
      measurable_fst.prodMk measurable_snd
    have hres :
        Measurable (fun p : (setup.Point × Ambient EX EY) × setup.SamplePoint =>
          setup.stochasticOracle p.1.1 p.2 - setup.meanOracle p.1.1) :=
      (oracle_residual_product_measurable (setup := setup)).comp hquery_sample
    have hinner :
        Measurable (fun p : (setup.Point × Ambient EX EY) × setup.SamplePoint =>
          ⟪p.1.2, setup.stochasticOracle p.1.1 p.2 - setup.meanOracle p.1.1⟫_ℝ) :=
      continuous_inner.measurable.comp (hdir.prodMk hres)
    simpa [score] using hinner.neg
  have hscore_eq :
      ∀ ω, score (setup.crossTermQuery t ω) (setup.sampleAt t ω) = Z ω := by
    intro ω
    have hvec :
        -((setup.iterate t ω).1 - (setup.auxiliaryIterate t ω).1) =
          (setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1 := by
      abel
    have hsign :
        -⟪setup.gamma t • ((setup.iterate t ω).1 - (setup.auxiliaryIterate t ω).1),
            setup.oracleNoise t ω⟫_ℝ =
          setup.gamma t *
            ⟪(setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1,
              setup.oracleNoise t ω⟫_ℝ := by
      calc
        -⟪setup.gamma t • ((setup.iterate t ω).1 - (setup.auxiliaryIterate t ω).1),
            setup.oracleNoise t ω⟫_ℝ
            = -(setup.gamma t *
                ⟪(setup.iterate t ω).1 - (setup.auxiliaryIterate t ω).1,
                  setup.oracleNoise t ω⟫_ℝ) := by
                rw [real_inner_smul_left]
        _ = setup.gamma t *
              (-⟪(setup.iterate t ω).1 - (setup.auxiliaryIterate t ω).1,
                setup.oracleNoise t ω⟫_ℝ) := by ring
        _ = setup.gamma t *
              ⟪(setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1,
                setup.oracleNoise t ω⟫_ℝ := by
              rw [← inner_neg_left, hvec]
    have harg :
        -⟪(setup.crossTermQuery t ω).2,
          setup.stochasticOracle (setup.crossTermQuery t ω).1 (setup.sampleAt t ω) -
            setup.meanOracle (setup.crossTermQuery t ω).1⟫_ℝ =
          setup.gamma t *
            ⟪(setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1,
              setup.oracleNoise t ω⟫_ℝ := by
      rw [Setup.crossTermQuery, Setup.oracleNoise]
      exact hsign
    simpa [score, Z] using harg
  exact bounded_strictPast_weighted_exp_mgf_transfer_of_fixed_fiber_bound
    (Ω := setup.SamplePath) (S := setup.SamplePoint)
    (Q := setup.Point × Ambient EX EY)
    (mΩ := (MeasurableSpace.pi : MeasurableSpace setup.SamplePath))
    (mS := (by infer_instance : MeasurableSpace setup.SamplePoint))
    (mQ := (by infer_instance : MeasurableSpace (setup.Point × Ambient EX EY)))
    (P := setup.pathMeasure) (νS := setup.P)
    (past := past)
    (sample := setup.sampleAt t) (query := setup.crossTermQuery t)
    (H := H) (R := R) (ν := ν) (c := c)
    (gauge := fun q : setup.Point × Ambient EX EY => setup.productNorm q.2)
    (score := score) (Z := Z)
    hscore_meas hH_past hquery_past (setup.crossTermQuery_aemeasurable t)
    (setup.sampleAt_aemeasurable t) (strictPast_indep_sampleAt (setup := setup) t)
    (by simpa using setup.sampleAt_law t)
    hH_nonneg hH_int hquery_bound hscore_eq
    (by
      intro q
      simpa [score] using hfixed_int q)
    (by
      intro q
      simpa [score] using hfixed_bound q)
/-
  letI : IsProbabilityMeasure setup.pathMeasure := setup.pathMeasure_isProbabilityMeasure
  letI : IsProbabilityMeasure setup.P := setup.hP_prob
  let Weight := {r : ℝ // 0 ≤ r}
  let BoundedQuery := {q : setup.Point × Ambient EX EY // setup.productNorm q.2 ≤ R}
  let W := Weight × BoundedQuery
  let X : setup.SamplePath → W := fun ω =>
    ((⟨H ω, hH_nonneg ω⟩ : Weight),
      (⟨setup.crossTermQuery t ω, hquery_bound ω⟩ : BoundedQuery))
  let Y : setup.SamplePath → setup.SamplePoint := setup.sampleAt t
  let φ : W → setup.SamplePoint → ℝ := fun w ξ =>
    (w.1 : ℝ) *
      Real.exp
        (ν *
          (-⟪(w.2 : setup.Point × Ambient EX EY).2,
            setup.stochasticOracle (w.2 : setup.Point × Ambient EX EY).1 ξ -
              setup.meanOracle (w.2 : setup.Point × Ambient EX EY).1⟫_ℝ))
  let B : W → ℝ := fun w => Real.exp c * (w.1 : ℝ)
  have hφ_meas :
      Measurable (fun p : W × setup.SamplePoint => φ p.1 p.2) := by
    have hweight :
        Measurable (fun p : W × setup.SamplePoint => ((p.1.1 : Weight) : ℝ)) :=
      measurable_subtype_coe.comp (measurable_fst.comp measurable_fst)
    have hq :
        Measurable
          (fun p : W × setup.SamplePoint =>
            ((p.1.2 : BoundedQuery) : setup.Point × Ambient EX EY)) :=
      measurable_subtype_coe.comp (measurable_snd.comp measurable_fst)
    have hdir :
        Measurable
          (fun p : W × setup.SamplePoint =>
            ((p.1.2 : BoundedQuery) : setup.Point × Ambient EX EY).2) :=
      measurable_snd.comp hq
    have hquery_sample :
        Measurable
          (fun p : W × setup.SamplePoint =>
            (((p.1.2 : BoundedQuery) : setup.Point × Ambient EX EY), p.2)) :=
      hq.prodMk measurable_snd
    have hres :
        Measurable
          (fun p : W × setup.SamplePoint =>
            setup.stochasticOracle
                ((p.1.2 : BoundedQuery) : setup.Point × Ambient EX EY).1 p.2 -
              setup.meanOracle
                ((p.1.2 : BoundedQuery) : setup.Point × Ambient EX EY).1) :=
      (oracle_residual_product_measurable (setup := setup)).comp hquery_sample
    have hinner :
        Measurable
          (fun p : W × setup.SamplePoint =>
            ⟪((p.1.2 : BoundedQuery) : setup.Point × Ambient EX EY).2,
              setup.stochasticOracle
                  ((p.1.2 : BoundedQuery) : setup.Point × Ambient EX EY).1 p.2 -
                setup.meanOracle
                  ((p.1.2 : BoundedQuery) : setup.Point × Ambient EX EY).1⟫_ℝ) :=
      continuous_inner.measurable.comp (hdir.prodMk hres)
    have hexp :
        Measurable
          (fun p : W × setup.SamplePoint =>
            Real.exp
              (ν *
                (-⟪((p.1.2 : BoundedQuery) : setup.Point × Ambient EX EY).2,
                  setup.stochasticOracle
                      ((p.1.2 : BoundedQuery) : setup.Point × Ambient EX EY).1 p.2 -
                    setup.meanOracle
                      ((p.1.2 : BoundedQuery) : setup.Point × Ambient EX EY).1⟫_ℝ))) :=
      (Real.continuous_exp.comp
        (continuous_const.mul continuous_id.neg)).measurable.comp hinner
    simpa [φ] using hweight.mul hexp
  have hφ_prod :
      AEStronglyMeasurable
        (fun p : W × setup.SamplePoint => φ p.1 p.2)
        ((Measure.map X setup.pathMeasure).prod setup.P) :=
    hφ_meas.aestronglyMeasurable
  have hB_meas : Measurable B := by
    have hweight : Measurable (fun w : W => (w.1 : ℝ)) :=
      measurable_subtype_coe.comp measurable_fst
    simpa [B] using measurable_const.mul hweight
  have hB_aesm : AEStronglyMeasurable B (Measure.map X setup.pathMeasure) :=
    hB_meas.aestronglyMeasurable
  have hstate_aemeas : AEMeasurable X setup.pathMeasure := by
    have hweight_aemeas :
        AEMeasurable
          (fun ω : setup.SamplePath => (⟨H ω, hH_nonneg ω⟩ : Weight))
          setup.pathMeasure := by
      simpa [Set.mem_Ici, Set.codRestrict, Weight] using
        (hH_int.aestronglyMeasurable.aemeasurable).subtype_mk
          (s := Set.Ici (0 : ℝ)) (hfs := fun ω => hH_nonneg ω)
    have hquery_aemeas :
        AEMeasurable
          (fun ω : setup.SamplePath =>
            (⟨setup.crossTermQuery t ω, hquery_bound ω⟩ : BoundedQuery))
          setup.pathMeasure := by
      simpa [BoundedQuery, Set.mem_setOf_eq] using
        (setup.crossTermQuery_aemeasurable t).subtype_mk
          (s := {q : setup.Point × Ambient EX EY | setup.productNorm q.2 ≤ R})
          (hfs := fun ω => hquery_bound ω)
    exact hweight_aemeas.prodMk hquery_aemeas
  have hstate_indep : IndepFun X Y setup.pathMeasure := by
    have hweight_strict :
        Measurable[
          (⨆ j < t.1 - 1,
            MeasurableSpace.comap (fun ω : setup.SamplePath => ω j)
              (by infer_instance : MeasurableSpace setup.SamplePoint))]
          (fun ω : setup.SamplePath => (⟨H ω, hH_nonneg ω⟩ : Weight)) := by
      exact Measurable.subtype_mk hH_strict
    have hquery_strict_subtype :
        Measurable[
          (⨆ j < t.1 - 1,
            MeasurableSpace.comap (fun ω : setup.SamplePath => ω j)
              (by infer_instance : MeasurableSpace setup.SamplePoint))]
          (fun ω : setup.SamplePath =>
            (⟨setup.crossTermQuery t ω, hquery_bound ω⟩ : BoundedQuery)) := by
      exact Measurable.subtype_mk hquery_strict
    have hstate_strict :
        Measurable[
          (⨆ j < t.1 - 1,
            MeasurableSpace.comap (fun ω : setup.SamplePath => ω j)
              (by infer_instance : MeasurableSpace setup.SamplePoint))]
          X := by
      exact hweight_strict.prod hquery_strict_subtype
    exact indepFun_of_measurable_left_of_indep_comap hstate_strict
      (strictPast_indep_sampleAt (setup := setup) t)
  have hX_aemeas : AEMeasurable X setup.pathMeasure := hstate_aemeas
  have hY_aemeas : AEMeasurable Y setup.pathMeasure := by
    simpa [Y] using setup.sampleAt_aemeasurable t
  have hY_law : Measure.map Y setup.pathMeasure = setup.P := by
    simpa [Y] using setup.sampleAt_law t
  have hφ_nonneg : ∀ w ξ, 0 ≤ φ w ξ := by
    intro w ξ
    exact mul_nonneg w.1.2 (le_of_lt (Real.exp_pos _))
  have hfixed_int' : ∀ w : W, Integrable (fun ξ => φ w ξ) setup.P := by
    intro w
    simpa [φ] using (hfixed_int w.2).const_mul (w.1 : ℝ)
  have hB_int : Integrable (fun ω => B (X ω)) setup.pathMeasure := by
    simpa [B, X, Weight] using hH_int.const_mul (Real.exp c)
  have hfixed_bound' : ∀ w : W, ∫ ξ, φ w ξ ∂setup.P ≤ B w := by
    intro w
    have hw_nonneg : 0 ≤ (w.1 : ℝ) := w.1.2
    calc
      ∫ ξ, φ w ξ ∂setup.P
          = (w.1 : ℝ) *
              ∫ ξ,
                Real.exp
                  (ν *
                    (-⟪(w.2 : setup.Point × Ambient EX EY).2,
                      setup.stochasticOracle
                          (w.2 : setup.Point × Ambient EX EY).1 ξ -
                        setup.meanOracle
                          (w.2 : setup.Point × Ambient EX EY).1⟫_ℝ)) ∂setup.P := by
            simp [φ, MeasureTheory.integral_const_mul]
      _ ≤ (w.1 : ℝ) * Real.exp c :=
            mul_le_mul_of_nonneg_left (hfixed_bound w.2) hw_nonneg
      _ = B w := by simp [B, mul_comm, mul_left_comm, mul_assoc]
  have hcomp_int :
      Integrable (fun ω => φ (X ω) (Y ω)) setup.pathMeasure :=
    integrable_comp_of_indep_fixed_integral_comp_bound
      (P := setup.pathMeasure) (ν := setup.P)
      (φ := φ) (B := B) (X := X) (Y := Y)
      hφ_prod hB_aesm hX_aemeas hY_aemeas hstate_indep hY_law
      hφ_nonneg hfixed_int' hB_int hfixed_bound'
  have hcomp_le :
      ∫ ω, φ (X ω) (Y ω) ∂setup.pathMeasure ≤
        ∫ ω, B (X ω) ∂setup.pathMeasure :=
    integral_comp_le_integral_comp_bound_of_indep_fixed_integral_bound_aestronglyMeasurable
      (P := setup.pathMeasure) (ν := setup.P)
      (φ := φ) (B := B) (X := X) (Y := Y)
      hφ_prod hB_aesm hX_aemeas hY_aemeas hstate_indep hY_law
      hcomp_int hB_int hfixed_bound'
  have hφ_comp_eq :
      (fun ω => φ (X ω) (Y ω)) =
        (fun ω =>
          H ω *
            Real.exp
              (ν *
                (setup.gamma t *
                  ⟪(setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1,
                    setup.oracleNoise t ω⟫_ℝ))) := by
    funext ω
    have hvec :
        -((setup.iterate t ω).1 - (setup.auxiliaryIterate t ω).1) =
          (setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1 := by
      abel
    have hsign :
        -⟪setup.gamma t • ((setup.iterate t ω).1 - (setup.auxiliaryIterate t ω).1),
            setup.oracleNoise t ω⟫_ℝ =
          setup.gamma t *
            ⟪(setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1,
              setup.oracleNoise t ω⟫_ℝ := by
      calc
        -⟪setup.gamma t • ((setup.iterate t ω).1 - (setup.auxiliaryIterate t ω).1),
            setup.oracleNoise t ω⟫_ℝ
            = -(setup.gamma t *
                ⟪(setup.iterate t ω).1 - (setup.auxiliaryIterate t ω).1,
                  setup.oracleNoise t ω⟫_ℝ) := by
                rw [real_inner_smul_left]
        _ = setup.gamma t *
              (-⟪(setup.iterate t ω).1 - (setup.auxiliaryIterate t ω).1,
                setup.oracleNoise t ω⟫_ℝ) := by ring
        _ = setup.gamma t *
              ⟪(setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1,
                setup.oracleNoise t ω⟫_ℝ := by
              rw [← inner_neg_left, hvec]
    have harg :
        ν *
            (-⟪(setup.crossTermQuery t ω).2,
              setup.stochasticOracle (setup.crossTermQuery t ω).1 (setup.sampleAt t ω) -
                setup.meanOracle (setup.crossTermQuery t ω).1⟫_ℝ) =
          ν *
            (setup.gamma t *
              ⟪(setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1,
                setup.oracleNoise t ω⟫_ℝ) := by
      rw [Setup.crossTermQuery, Setup.oracleNoise]
      exact congrArg (fun r : ℝ => ν * r) hsign
    change
      H ω *
          Real.exp
            (ν *
              (-⟪(setup.crossTermQuery t ω).2,
                setup.stochasticOracle (setup.crossTermQuery t ω).1 (setup.sampleAt t ω) -
                  setup.meanOracle (setup.crossTermQuery t ω).1⟫_ℝ)) =
        H ω *
          Real.exp
            (ν *
              (setup.gamma t *
                ⟪(setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1,
                  setup.oracleNoise t ω⟫_ℝ))
    rw [harg]
  have hB_comp_eq :
      (fun ω => B (X ω)) = fun ω => Real.exp c * H ω := by
    funext ω
    simp [B, X, Weight]
  constructor
  · simpa [hφ_comp_eq] using hcomp_int
  · calc
      ∫ ω,
          H ω *
            Real.exp
              (ν *
                (setup.gamma t *
                  ⟪(setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1,
                    setup.oracleNoise t ω⟫_ℝ)) ∂setup.pathMeasure
          = ∫ ω, φ (X ω) (Y ω) ∂setup.pathMeasure := by
              rw [hφ_comp_eq]
      _ ≤ ∫ ω, B (X ω) ∂setup.pathMeasure := hcomp_le
      _ = Real.exp c * ∫ ω, H ω ∂setup.pathMeasure := by
              rw [hB_comp_eq, MeasureTheory.integral_const_mul]
-/

/-- One Lemma 4.1 conditional-recurrence step for a strict-past prefix weight.

The random state is `W = (H, crossTermQuery t)`, with `H` stored as a
nonnegative subtype.  Fresh iid sampling then transfers a deterministic
fixed-fiber MGF bound to the weighted prefix inequality. -/
private theorem prefix_weighted_one_step_mgf_transfer
    (t : Time) (ν c : ℝ) (H : setup.SamplePath → ℝ)
    (hH_strict :
      Measurable[
        (⨆ j < t.1 - 1,
          MeasurableSpace.comap (fun ω : setup.SamplePath => ω j)
            (by infer_instance : MeasurableSpace setup.SamplePoint))]
        H)
    (hquery_strict :
      Measurable[
        (⨆ j < t.1 - 1,
          MeasurableSpace.comap (fun ω : setup.SamplePath => ω j)
            (by infer_instance : MeasurableSpace setup.SamplePoint))]
        (setup.crossTermQuery t))
    (hH_nonneg : ∀ ω, 0 ≤ H ω)
    (hH_int : Integrable H setup.pathMeasure)
    (hfixed_int :
      ∀ q : setup.Point × Ambient EX EY,
        Integrable
          (fun ξ =>
            Real.exp
              (ν *
                (-⟪q.2, setup.stochasticOracle q.1 ξ - setup.meanOracle q.1⟫_ℝ)))
          setup.P)
    (hfixed_bound :
      ∀ q : setup.Point × Ambient EX EY,
        ∫ ξ,
            Real.exp
              (ν *
                (-⟪q.2, setup.stochasticOracle q.1 ξ - setup.meanOracle q.1⟫_ℝ))
            ∂setup.P ≤ Real.exp c) :
    Integrable
        (fun ω =>
          H ω *
            Real.exp
              (ν *
                (setup.gamma t *
                  ⟪(setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1,
                    setup.oracleNoise t ω⟫_ℝ)))
        setup.pathMeasure ∧
      ∫ ω,
          H ω *
            Real.exp
              (ν *
                (setup.gamma t *
                  ⟪(setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1,
                    setup.oracleNoise t ω⟫_ℝ)) ∂setup.pathMeasure ≤
        Real.exp c * ∫ ω, H ω ∂setup.pathMeasure := by
  /-
  Direct proof attempt status:
  instantiate the proved variable-bound product-law helpers with
  `W = (⟨H, hH_nonneg⟩, setup.crossTermQuery t)`,
  `φ W ξ = H * exp (ν * -⟪direction, residual ξ⟫)`, and
  `B W = exp c * H`.  The fixed-fiber integral and bound follow from
  `hfixed_int`/`hfixed_bound` by multiplying with the nonnegative subtype
  weight.  The remaining Lean obstruction is ambient measurable-space
  inference for the strict-past independence call and the product-kernel
  measurability term; both direct instantiations were attempted above before
  this proof was collapsed to a single leaf.
  -/
  have hstate_aemeas :
      AEMeasurable
        (fun ω : setup.SamplePath =>
          ((⟨H ω, hH_nonneg ω⟩ : {r : ℝ // 0 ≤ r}), setup.crossTermQuery t ω))
        setup.pathMeasure := by
    have hweight_aemeas :
        AEMeasurable
          (fun ω : setup.SamplePath => (⟨H ω, hH_nonneg ω⟩ : {r : ℝ // 0 ≤ r}))
          setup.pathMeasure := by
      simpa [Set.mem_Ici, Set.codRestrict] using
        (hH_int.aestronglyMeasurable.aemeasurable).subtype_mk
          (s := Set.Ici (0 : ℝ)) (hfs := fun ω => hH_nonneg ω)
    exact hweight_aemeas.prodMk (setup.crossTermQuery_aemeasurable t)
  have hstate_indep :
      IndepFun
        (fun ω : setup.SamplePath =>
          ((⟨H ω, hH_nonneg ω⟩ : {r : ℝ // 0 ≤ r}), setup.crossTermQuery t ω))
        (setup.sampleAt t) setup.pathMeasure := by
    have hweight_strict :
        Measurable[
          (⨆ j < t.1 - 1,
            MeasurableSpace.comap (fun ω : setup.SamplePath => ω j)
              (by infer_instance : MeasurableSpace setup.SamplePoint))]
          (fun ω : setup.SamplePath => (⟨H ω, hH_nonneg ω⟩ : {r : ℝ // 0 ≤ r})) := by
      exact Measurable.subtype_mk hH_strict
    have hstate_strict :
        Measurable[
          (⨆ j < t.1 - 1,
            MeasurableSpace.comap (fun ω : setup.SamplePath => ω j)
              (by infer_instance : MeasurableSpace setup.SamplePoint))]
          (fun ω : setup.SamplePath =>
            ((⟨H ω, hH_nonneg ω⟩ : {r : ℝ // 0 ≤ r}), setup.crossTermQuery t ω)) := by
      exact hweight_strict.prod hquery_strict
    exact indepFun_of_measurable_left_of_indep_comap hstate_strict
      (strictPast_indep_sampleAt (setup := setup) t)
  exact weighted_one_step_mgf_transfer_of_indep_state
    (setup := setup) t ν c H hH_nonneg hH_int hstate_aemeas hstate_indep
    hfixed_int hfixed_bound

/-- Fractional square-exponential moment bound used in the scalar Lemma 4.1
MGF proof.

If `E exp (X^2 / σ2) ≤ exp 1`, then every fractional exponent `p ∈ [0,1]`
has the corresponding integrability and moment bound. -/
private theorem exp_square_fractional_moment_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {σ2 p : ℝ}
    (hσ2_pos : 0 < σ2)
    (hX_int : Integrable X μ)
    (hexp_sq_int : Integrable (fun ω => Real.exp (X ω ^ 2 / σ2)) μ)
    (hexp_sq_bound : ∫ ω, Real.exp (X ω ^ 2 / σ2) ∂μ ≤ Real.exp 1)
    (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    Integrable (fun ω => Real.exp (p * (X ω ^ 2 / σ2))) μ ∧
      ∫ ω, Real.exp (p * (X ω ^ 2 / σ2)) ∂μ ≤ Real.exp p := by
  exact _root_.exp_square_fractional_moment_bound
    (hσ2_pos := hσ2_pos) (hX_aesm := hX_int.aestronglyMeasurable)
    (hexp_sq_int := hexp_sq_int) (hexp_sq_bound := hexp_sq_bound) hp

/-- Nonnegative real exponential dominates its quadratic Taylor truncation. -/
private theorem one_add_self_add_sq_div_two_le_exp {x : ℝ} (hx : 0 ≤ x) :
    1 + x + (1 / 2 : ℝ) * x ^ 2 ≤ Real.exp x := by
  classical
  let f : ℝ → ℝ := fun t => Real.exp t - (1 + t + (1 / 2 : ℝ) * t ^ 2)
  have hmono : MonotoneOn f (Set.Icc (0 : ℝ) x) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) ?_ ?_ ?_
    · exact (by fun_prop : Continuous f).continuousOn
    · exact (by fun_prop : DifferentiableOn ℝ f (interior (Set.Icc (0 : ℝ) x)))
    · intro z hz
      have hz_nonneg : 0 ≤ z := by
        have hz' : z ∈ Set.Ioo (0 : ℝ) x := by simpa using hz
        exact le_of_lt hz'.1
      have hderiv :
          deriv f z = Real.exp z - (1 + z) := by
        have hp :
            HasDerivAt (fun t : ℝ => 1 + t + (1 / 2 : ℝ) * t ^ 2) (1 + z) z := by
          have hsq : HasDerivAt (fun t : ℝ => t ^ 2) (2 * z) z := by
            simpa using (hasDerivAt_pow 2 z)
          have hsq_div :
              HasDerivAt (fun t : ℝ => (1 / 2 : ℝ) * t ^ 2) z z := by
            convert hsq.const_mul ((1 : ℝ) / 2) using 1 <;> ring
          simpa using
            ((hasDerivAt_const (x := z) (c := (1 : ℝ))).add
              (hasDerivAt_id' z)).add hsq_div
        have hf_has : HasDerivAt f (Real.exp z - (1 + z)) z := by
          convert (Real.hasDerivAt_exp z).sub hp using 1 <;> ext t <;> ring
        exact hf_has.deriv
      rw [hderiv]
      linarith [Real.add_one_le_exp z]
  have h0_mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) x := ⟨le_rfl, hx⟩
  have hx_mem : x ∈ Set.Icc (0 : ℝ) x := ⟨hx, le_rfl⟩
  have hle := hmono h0_mem hx_mem hx
  have hf0 : f 0 = 0 := by simp [f]
  have hfx : f x = Real.exp x - (1 + x + (1 / 2 : ℝ) * x ^ 2) := by simp [f]
  rw [hf0, hfx] at hle
  linarith

/-- Nonnegative real exponential dominates its cubic Taylor truncation. -/
private theorem one_add_self_add_sq_div_two_add_cube_div_six_le_exp
    {x : ℝ} (hx : 0 ≤ x) :
    1 + x + (1 / 2 : ℝ) * x ^ 2 + (1 / 6 : ℝ) * x ^ 3 ≤ Real.exp x := by
  classical
  let f : ℝ → ℝ :=
    fun t => Real.exp t - (1 + t + (1 / 2 : ℝ) * t ^ 2 + (1 / 6 : ℝ) * t ^ 3)
  have hmono : MonotoneOn f (Set.Icc (0 : ℝ) x) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) ?_ ?_ ?_
    · exact (by fun_prop : Continuous f).continuousOn
    · exact (by fun_prop : DifferentiableOn ℝ f (interior (Set.Icc (0 : ℝ) x)))
    · intro z hz
      have hz_nonneg : 0 ≤ z := by
        have hz' : z ∈ Set.Ioo (0 : ℝ) x := by simpa using hz
        exact le_of_lt hz'.1
      have hderiv :
          deriv f z = Real.exp z - (1 + z + (1 / 2 : ℝ) * z ^ 2) := by
        have hp :
            HasDerivAt
              (fun t : ℝ =>
                1 + t + (1 / 2 : ℝ) * t ^ 2 + (1 / 6 : ℝ) * t ^ 3)
              (1 + z + (1 / 2 : ℝ) * z ^ 2) z := by
          have hsq : HasDerivAt (fun t : ℝ => t ^ 2) (2 * z) z := by
            simpa using (hasDerivAt_pow 2 z)
          have hsq_div :
              HasDerivAt (fun t : ℝ => (1 / 2 : ℝ) * t ^ 2) z z := by
            convert hsq.const_mul ((1 : ℝ) / 2) using 1 <;> ring
          have hcube : HasDerivAt (fun t : ℝ => t ^ 3) (3 * z ^ 2) z := by
            simpa using (hasDerivAt_pow 3 z)
          have hcube_div :
              HasDerivAt (fun t : ℝ => (1 / 6 : ℝ) * t ^ 3)
                ((1 / 2 : ℝ) * z ^ 2) z := by
            convert hcube.const_mul ((1 : ℝ) / 6) using 1 <;> ring
          simpa using
            (((hasDerivAt_const (x := z) (c := (1 : ℝ))).add
              (hasDerivAt_id' z)).add hsq_div).add hcube_div
        have hf_has :
            HasDerivAt f (Real.exp z - (1 + z + (1 / 2 : ℝ) * z ^ 2)) z := by
          convert (Real.hasDerivAt_exp z).sub hp using 1 <;> ext t <;> ring
        exact hf_has.deriv
      rw [hderiv]
      exact sub_nonneg.mpr (one_add_self_add_sq_div_two_le_exp hz_nonneg)
  have h0_mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) x := ⟨le_rfl, hx⟩
  have hx_mem : x ∈ Set.Icc (0 : ℝ) x := ⟨hx, le_rfl⟩
  have hle := hmono h0_mem hx_mem hx
  have hf0 : f 0 = 0 := by simp [f]
  have hfx :
      f x =
        Real.exp x - (1 + x + (1 / 2 : ℝ) * x ^ 2 + (1 / 6 : ℝ) * x ^ 3) := by
    simp [f]
  rw [hf0, hfx] at hle
  linarith

private theorem quartic_nonneg_for_exp_nine_small {y : ℝ} (hy0 : 0 ≤ y)
    (hy1 : y ≤ 1) :
    0 ≤ 729 * y ^ 4 + 2608 * y ^ 2 - 4096 * y + 1536 := by
  by_cases hyhalf : y ≤ (1 : ℝ) / 2
  · have hquad_nonneg :
        0 ≤ 2608 * (y - 512 / 652) ^ 2 := by positivity
    nlinarith [hquad_nonneg]
  · have hyhalf' : (1 : ℝ) / 2 ≤ y := le_of_not_ge hyhalf
    by_cases hy23 : y ≤ (2 : ℝ) / 3
    · let s : ℝ := (2 : ℝ) / 3 - y
      have hs0 : 0 ≤ s := by dsimp [s]; linarith
      have hs_le : s ≤ (1 : ℝ) / 6 := by dsimp [s]; linarith
      have hs2_le : s ^ 2 ≤ (1 / 6 : ℝ) ^ 2 := by
        simpa [pow_two] using mul_self_le_mul_self hs0 hs_le
      have hs3_le : s ^ 3 ≤ (1 / 6 : ℝ) ^ 3 := by
        have hmul := mul_le_mul hs2_le hs_le hs0 (by positivity : 0 ≤ (1 / 6 : ℝ) ^ 2)
        simpa [pow_succ] using hmul
      have hrewrite :
          729 * y ^ 4 + 2608 * y ^ 2 - 4096 * y + 1536 =
            729 * s ^ 4 - 1944 * s ^ 3 + 4552 * s ^ 2 -
              (736 / 3) * s + 976 / 9 := by
        dsimp [s]
        ring
      rw [hrewrite]
      nlinarith [sq_nonneg s, hs3_le]
    · have hy23' : (2 : ℝ) / 3 ≤ y := le_of_not_ge hy23
      let t : ℝ := y - (2 : ℝ) / 3
      have ht0 : 0 ≤ t := by dsimp [t]; linarith
      have hrewrite :
          729 * y ^ 4 + 2608 * y ^ 2 - 4096 * y + 1536 =
            729 * t ^ 4 + 1944 * t ^ 3 + 4552 * t ^ 2 +
              (736 / 3) * t + 976 / 9 := by
        dsimp [t]
        ring
      rw [hrewrite]
      positivity

private theorem exp_pos_small_branch_le_self_add_exp_nine_mul_sq_div_sixteen
    {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    Real.exp y ≤ y + Real.exp (9 * y ^ 2 / 16) := by
  let a : ℝ := 9 / 16
  have hquad_nonneg : 0 ≤ a * y ^ 2 := by positivity
  have hlower_cubic :
      1 + a * y ^ 2 + (1 / 2 : ℝ) * (a * y ^ 2) ^ 2 +
          (1 / 6 : ℝ) * (a * y ^ 2) ^ 3 ≤
        Real.exp (a * y ^ 2) := by
    exact one_add_self_add_sq_div_two_add_cube_div_six_le_exp hquad_nonneg
  have hupper :=
    Real.exp_bound' (x := y) (n := 4) hy0 hy1 (by norm_num)
  have hpoly :
      (∑ m ∈ Finset.range 4, y ^ m / (m.factorial : ℝ)) +
          y ^ 4 * (4 + 1 : ℝ) / ((Nat.factorial 4 : ℝ) * 4)
        ≤ y + (1 + a * y ^ 2 + (1 / 2 : ℝ) * (a * y ^ 2) ^ 2 +
            (1 / 6 : ℝ) * (a * y ^ 2) ^ 3) := by
    have hq := quartic_nonneg_for_exp_nine_small hy0 hy1
    have hprod :
        0 ≤ y ^ 2 * (729 * y ^ 4 + 2608 * y ^ 2 - 4096 * y + 1536) := by
      exact mul_nonneg (sq_nonneg y) hq
    norm_num [a, Finset.sum_range_succ, pow_succ]
    nlinarith
  calc
    Real.exp y
        ≤ (∑ m ∈ Finset.range 4, y ^ m / (m.factorial : ℝ)) +
            y ^ 4 * (4 + 1 : ℝ) / ((Nat.factorial 4 : ℝ) * 4) := hupper
    _ ≤ y + (1 + a * y ^ 2 + (1 / 2 : ℝ) * (a * y ^ 2) ^ 2 +
            (1 / 6 : ℝ) * (a * y ^ 2) ^ 3) := hpoly
    _ ≤ y + Real.exp (a * y ^ 2) := by linarith
    _ = y + Real.exp (9 * y ^ 2 / 16) := by
          congr 1
          congr 1
          dsimp [a]
          ring

set_option maxHeartbeats 4000000 in
private theorem exp_pos_mid_branch_le_self_add_exp_nine_mul_sq_div_sixteen
    {y : ℝ} (hy1 : 1 ≤ y) (hy_upper : y < (16 : ℝ) / 9) :
    Real.exp y ≤ y + Real.exp (9 * y ^ 2 / 16) := by
  classical
  let a : ℝ := 9 / 16
  let f : ℝ → ℝ := fun z => z + Real.exp (z ^ 2 * a) - Real.exp z
  have hexp_one_le : Real.exp (1 : ℝ) ≤ 11 / 4 := by
    have h :=
      Real.exp_bound' (x := (1 : ℝ)) (n := 4)
        (by norm_num) (by norm_num) (by norm_num)
    norm_num at h ⊢
    linarith
  have hmono : MonotoneOn f (Set.Icc (1 : ℝ) (16 / 9)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) ?_ ?_ ?_
    · exact (by fun_prop : Continuous f).continuousOn
    · exact (by fun_prop : DifferentiableOn ℝ f (interior (Set.Icc (1 : ℝ) (16 / 9))))
    · intro z hz
      have hz' : z ∈ Set.Ioo (1 : ℝ) (16 / 9) := by simpa using hz
      have hz1 : 1 ≤ z := le_of_lt hz'.1
      have hz_upper : z ≤ (16 : ℝ) / 9 := le_of_lt hz'.2
      have hderiv :
          deriv f z =
            1 + z * Real.exp (z ^ 2 * a) * (9 / 8) - Real.exp z := by
        have hf_has :
            HasDerivAt f
              (1 + Real.exp (z ^ 2 * a) * (2 * z * a) - Real.exp z) z := by
          have hsq : HasDerivAt (fun t : ℝ => t ^ 2) (2 * z) z := by
            simpa using (hasDerivAt_pow 2 z)
          have hquad :
              HasDerivAt (fun t : ℝ => t ^ 2 * a) (2 * z * a) z :=
            hsq.mul_const a
          have hexp_quad :
              HasDerivAt (fun t : ℝ => Real.exp (t ^ 2 * a))
                (Real.exp (z ^ 2 * a) * (2 * z * a)) z :=
            hquad.exp
          simpa [f, sub_eq_add_neg] using
            ((hasDerivAt_id' z).add hexp_quad).add ((Real.hasDerivAt_exp z).neg)
        have hf_deriv := hf_has.deriv
        calc
          deriv f z =
              1 + Real.exp (z ^ 2 * a) * (2 * z * a) - Real.exp z := hf_deriv
          _ = 1 + z * Real.exp (z ^ 2 * a) * (9 / 8) - Real.exp z := by
                dsimp [a]
                ring
      rw [hderiv]
      let t : ℝ := z - 1
      have ht0 : 0 ≤ t := by dsimp [t]; linarith
      have ht_le_one : t ≤ 1 := by dsimp [t]; linarith
      have hupper_t :=
        Real.exp_bound' (x := t) (n := 2) ht0 ht_le_one (by norm_num)
      have hlower_quad :
          1 + z ^ 2 * a + (1 / 2 : ℝ) * (z ^ 2 * a) ^ 2 +
              (1 / 6 : ℝ) * (z ^ 2 * a) ^ 3 ≤
            Real.exp (z ^ 2 * a) := by
        have hnonneg : 0 ≤ z ^ 2 * a := by positivity
        exact one_add_self_add_sq_div_two_add_cube_div_six_le_exp hnonneg
      have hpoly :
          (11 / 4 : ℝ) *
              ((∑ m ∈ Finset.range 2, t ^ m / (m.factorial : ℝ)) +
                t ^ 2 * (2 + 1 : ℝ) / ((Nat.factorial 2 : ℝ) * 2))
            ≤ 1 + z * (9 / 8) *
                (1 + z ^ 2 * a + (1 / 2 : ℝ) * (z ^ 2 * a) ^ 2 +
                  (1 / 6 : ℝ) * (z ^ 2 * a) ^ 3) := by
        have hcert :
            0 ≤
              2187 * t ^ 7 + 15309 * t ^ 6 + 57591 * t ^ 5 +
                134865 * t ^ 4 + 234657 * t ^ 3 + 151815 * t ^ 2 +
                  91549 * t + 14363 := by
          positivity
        have hrewrite :
            (1 + z * (9 / 8) *
                (1 + z ^ 2 * a + (1 / 2 : ℝ) * (z ^ 2 * a) ^ 2 +
                  (1 / 6 : ℝ) * (z ^ 2 * a) ^ 3)) -
              ((11 / 4 : ℝ) *
                ((∑ m ∈ Finset.range 2, t ^ m / (m.factorial : ℝ)) +
                  t ^ 2 * (2 + 1 : ℝ) / ((Nat.factorial 2 : ℝ) * 2))) =
              (2187 * t ^ 7 + 15309 * t ^ 6 + 57591 * t ^ 5 +
                134865 * t ^ 4 + 234657 * t ^ 3 + 151815 * t ^ 2 +
                  91549 * t + 14363) / 65536 := by
          dsimp [a, t]
          norm_num [Finset.sum_range_succ, pow_succ]
          ring
        have hdiff_nonneg :
            0 ≤
              (1 + z * (9 / 8) *
                (1 + z ^ 2 * a + (1 / 2 : ℝ) * (z ^ 2 * a) ^ 2 +
                  (1 / 6 : ℝ) * (z ^ 2 * a) ^ 3)) -
              ((11 / 4 : ℝ) *
                ((∑ m ∈ Finset.range 2, t ^ m / (m.factorial : ℝ)) +
                  t ^ 2 * (2 + 1 : ℝ) / ((Nat.factorial 2 : ℝ) * 2))) := by
          rw [hrewrite]
          positivity
        linarith
      have hexp_z_le :
          Real.exp z ≤
            (11 / 4 : ℝ) *
              ((∑ m ∈ Finset.range 2, t ^ m / (m.factorial : ℝ)) +
                t ^ 2 * (2 + 1 : ℝ) / ((Nat.factorial 2 : ℝ) * 2)) := by
        have hz_eq : z = 1 + t := by dsimp [t]; ring
        calc
          Real.exp z = Real.exp (1 : ℝ) * Real.exp t := by
                rw [hz_eq, Real.exp_add]
          _ ≤ (11 / 4 : ℝ) *
              ((∑ m ∈ Finset.range 2, t ^ m / (m.factorial : ℝ)) +
                t ^ 2 * (2 + 1 : ℝ) / ((Nat.factorial 2 : ℝ) * 2)) := by
                exact mul_le_mul hexp_one_le hupper_t (Real.exp_nonneg t) (by norm_num)
      have hscaled :
          z * (9 / 8) *
              (1 + z ^ 2 * a + (1 / 2 : ℝ) * (z ^ 2 * a) ^ 2 +
                (1 / 6 : ℝ) * (z ^ 2 * a) ^ 3)
            ≤ z * (9 / 8) * Real.exp (z ^ 2 * a) := by
        exact mul_le_mul_of_nonneg_left hlower_quad (by positivity)
      nlinarith [hexp_z_le, hpoly, hscaled]
  have hbase : 0 ≤ f 1 := by
    have hnonneg : 0 ≤ (9 / 16 : ℝ) := by norm_num
    have hlow :
        1 + (9 / 16 : ℝ) + (1 / 2 : ℝ) * (9 / 16 : ℝ) ^ 2 +
            (1 / 6 : ℝ) * (9 / 16 : ℝ) ^ 3 ≤
          Real.exp (9 / 16 : ℝ) :=
      one_add_self_add_sq_div_two_add_cube_div_six_le_exp hnonneg
    have hval : f 1 = 1 + Real.exp (9 / 16) - Real.exp 1 := by
      simp [f, a]
    rw [hval]
    norm_num at hlow ⊢
    linarith
  have hy_mem : y ∈ Set.Icc (1 : ℝ) (16 / 9) := ⟨hy1, le_of_lt hy_upper⟩
  have hle := hmono (by norm_num) hy_mem hy1
  have hf_nonneg : 0 ≤ f y := hbase.trans hle
  dsimp [f, a] at hf_nonneg
  have hquad_eq : y ^ 2 * (9 / 16 : ℝ) = 9 * y ^ 2 / 16 := by ring
  rw [hquad_eq] at hf_nonneg
  nlinarith

/-- Scalar exponential domination from Lan Lemma 4.1's small branch. -/
private theorem exp_linear_le_linear_add_exp_nine_sixteenth_sq (x : ℝ) :
    Real.exp x ≤ x + Real.exp (9 * x ^ 2 / 16) := by
  exact Real.exp_le_self_add_exp_nine_mul_sq_div_sixteen x

/-- Source large-parameter square completion from Lemma 4.1. -/
private theorem linear_le_quadratic_scaled
    {σ2 : ℝ} (hσ2_pos : 0 < σ2) (ν x : ℝ) :
    ν * x ≤ 3 * ν ^ 2 * σ2 / 8 + 2 * x ^ 2 / (3 * σ2) := by
  have hnonneg :
      0 ≤
        σ2 *
          (3 * ν ^ 2 * σ2 / 8 + 2 * x ^ 2 / (3 * σ2) - ν * x) := by
    field_simp [hσ2_pos.ne']
    nlinarith [sq_nonneg (4 * x - 3 * ν * σ2)]
  have hdiff :
      0 ≤ 3 * ν ^ 2 * σ2 / 8 + 2 * x ^ 2 / (3 * σ2) - ν * x :=
    (mul_nonneg_iff_of_pos_left hσ2_pos).mp hnonneg
  linarith

/-- Scalar Lemma 4.1 MGF estimate from a centered light-tail square moment.

This is the source analytic step used after fixed-fiber scalarization: if
`X` is centered and `E exp (X^2 / σ2) ≤ exp 1`, then the one-dimensional
linear MGF has the Lemma 4.1 constant. -/
private theorem scalar_centered_exp_square_to_linear_mgf
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {ν σ2 : ℝ}
    (hν : 0 ≤ ν) (hσ2_pos : 0 < σ2)
    (hX_int : Integrable X μ)
    (hX_centered : ∫ ω, X ω ∂μ = 0)
    (hexp_sq_int : Integrable (fun ω => Real.exp (X ω ^ 2 / σ2)) μ)
    (hexp_sq_bound : ∫ ω, Real.exp (X ω ^ 2 / σ2) ∂μ ≤ Real.exp 1) :
    Integrable (fun ω => Real.exp (ν * X ω)) μ ∧
      ∫ ω, Real.exp (ν * X ω) ∂μ ≤ Real.exp (3 * ν ^ 2 * σ2 / 4) := by
  have _ : 0 ≤ ν := hν
  exact centered_exp_square_moment_to_linear_mgf_bound
    (hσ2_pos := hσ2_pos) (hX_int := hX_int) (hX_centered := hX_centered)
    (hexp_sq_int := hexp_sq_int) (hexp_sq_bound := hexp_sq_bound)

/-- Fixed-fiber bounded linear MGF for the cross-term scalarization.

This is the deterministic-fiber premise needed by
`bounded_prefix_weighted_one_step_mgf_transfer`; the bounded query hypothesis is
used only to obtain the square-exponential moment bound already proved from
the oracle light-tail assumption. -/
private theorem fixed_fiber_bounded_cross_term_linear_mgf
    (t : Time) (ν : ℝ) (hν : 0 ≤ ν)
    (hexp : setup.exponentialMomentOracleBound)
    (q : {q : setup.Point × Ambient EX EY //
      setup.productNorm q.2 ≤ setup.gamma t * Real.sqrt 2}) :
    Integrable
        (fun ξ =>
          Real.exp
            (ν *
              (-⟪(q : setup.Point × Ambient EX EY).2,
                setup.stochasticOracle (q : setup.Point × Ambient EX EY).1 ξ -
                  setup.meanOracle (q : setup.Point × Ambient EX EY).1⟫_ℝ)))
        setup.P ∧
      ∫ ξ,
          Real.exp
            (ν *
              (-⟪(q : setup.Point × Ambient EX EY).2,
                setup.stochasticOracle (q : setup.Point × Ambient EX EY).1 ξ -
                  setup.meanOracle (q : setup.Point × Ambient EX EY).1⟫_ℝ))
          ∂setup.P ≤
        Real.exp
          (3 * ν ^ 2 * (8 * setup.gamma t ^ 2 * setup.M ^ 2) / 4) := by
  letI : IsProbabilityMeasure setup.P := setup.hP_prob
  have _ : 0 ≤ ν := hν
  let q0 : setup.Point × Ambient EX EY := q
  have hres_int :
      Integrable
        (fun ξ => setup.stochasticOracle q0.1 ξ - setup.meanOracle q0.1) setup.P :=
    fixed_fiber_product_residual_integrable (setup := setup) q0.1
  have hres_zero :
      ∫ ξ, setup.stochasticOracle q0.1 ξ - setup.meanOracle q0.1 ∂setup.P = 0 :=
    fixed_fiber_product_residual_centered (setup := setup) q0.1
  have hsquare :=
    fixed_fiber_cross_term_exp_square_mgf_bound
      (setup := setup) t q0 q.2 hexp
  have hσ2_pos : 0 < 8 * setup.gamma t ^ 2 * setup.M ^ 2 :=
    mul_pos (mul_pos (by norm_num) (sq_pos_of_pos (setup.hgamma_pos t)))
      (sq_pos_of_pos setup.M_pos)
  simpa [q0] using
    fixed_direction_oracle_residual_linear_mgf_of_exp_square_mgf
      (P := setup.P) (G := setup.stochasticOracle) (meanG := setup.meanOracle)
      (q := q0.1) (d := q0.2) (ν := ν)
      (σ2 := 8 * setup.gamma t ^ 2 * setup.M ^ 2)
      (hσ2_pos := hσ2_pos)
      (hres_int := hres_int) (hres_centered := hres_zero)
      (hexp_sq_int := hsquare.1) (hexp_sq_bound := hsquare.2)

/-- One ordered-prefix cross-term MGF step with the bounded fixed-fiber premise.

Unlike the obsolete `hfinite_mgf_route` premise, this only applies to weights
measurable with respect to the current strict past, exactly the situation in the
chronological Lemma 4.1 recurrence. -/
private theorem prefix_cross_term_one_step_mgf_bound
    (t : Time) (ν : ℝ) (hν : 0 ≤ ν)
    (hexp : setup.exponentialMomentOracleBound)
    (H : setup.SamplePath → ℝ)
    (hH_strict :
      Measurable[
        (⨆ j < t.1 - 1,
          MeasurableSpace.comap (fun ω : setup.SamplePath => ω j)
            (by infer_instance : MeasurableSpace setup.SamplePoint))]
        H)
    (hquery_strict :
      Measurable[
        (⨆ j < t.1 - 1,
          MeasurableSpace.comap (fun ω : setup.SamplePath => ω j)
            (by infer_instance : MeasurableSpace setup.SamplePoint))]
        (setup.crossTermQuery t))
    (hH_nonneg : ∀ ω, 0 ≤ H ω)
    (hH_int : Integrable H setup.pathMeasure) :
    Integrable
        (fun ω =>
          H ω *
            Real.exp
              (ν *
                (setup.gamma t *
                  ⟪(setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1,
                    setup.oracleNoise t ω⟫_ℝ)))
        setup.pathMeasure ∧
      ∫ ω,
          H ω *
            Real.exp
              (ν *
                (setup.gamma t *
                  ⟪(setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1,
                    setup.oracleNoise t ω⟫_ℝ)) ∂setup.pathMeasure ≤
        Real.exp (3 * ν ^ 2 * (8 * setup.gamma t ^ 2 * setup.M ^ 2) / 4) *
          ∫ ω, H ω ∂setup.pathMeasure := by
  exact bounded_prefix_weighted_one_step_mgf_transfer
    (setup := setup) t ν
    (3 * ν ^ 2 * (8 * setup.gamma t ^ 2 * setup.M ^ 2) / 4)
    (setup.gamma t * Real.sqrt 2) H
    hH_strict hquery_strict hH_nonneg hH_int
    (crossTermQuery_direction_productNorm_le_gamma_sqrt_two (setup := setup) t)
    (fun q =>
      (fixed_fiber_bounded_cross_term_linear_mgf
        (setup := setup) t ν hν hexp q).1)
    (fun q =>
      (fixed_fiber_bounded_cross_term_linear_mgf
        (setup := setup) t ν hν hexp q).2)

set_option maxHeartbeats 4000000 in
/-- A previous paper-time sample coordinate is measurable in the current strict
past sigma-algebra. -/
private theorem sampleAt_strictPast_measurable_of_lt
    (τ t : Time) (hτt : τ.1 < t.1) :
    Measurable[
      (⨆ j < t.1 - 1,
        MeasurableSpace.comap (fun ω : setup.SamplePath => ω j)
          (by infer_instance : MeasurableSpace setup.SamplePoint))]
      (setup.sampleAt τ) := by
  have hidx : τ.1 - 1 < t.1 - 1 := by
    omega
  change
    Measurable[
      (⨆ j < t.1 - 1,
        MeasurableSpace.comap (fun ω : setup.SamplePath => ω j)
          (by infer_instance : MeasurableSpace setup.SamplePoint))]
      (fun ω : setup.SamplePath => ω (τ.1 - 1))
  refine Measurable.of_comap_le ?_
  change
    MeasurableSpace.comap (fun ω : setup.SamplePath => ω (τ.1 - 1))
        (by infer_instance : MeasurableSpace setup.SamplePoint) ≤
      ⨆ j < t.1 - 1,
        MeasurableSpace.comap (fun ω : setup.SamplePath => ω j)
          (by infer_instance : MeasurableSpace setup.SamplePoint)
  exact le_iSup_of_le (τ.1 - 1) (le_iSup_of_le hidx le_rfl)

/-- Strict-past filtrations are monotone in paper time. -/
private theorem strictPast_mono_of_le (τ t : Time) (hτt : τ.1 ≤ t.1) :
    (⨆ j < τ.1 - 1,
        MeasurableSpace.comap (fun ω : setup.SamplePath => ω j)
          (by infer_instance : MeasurableSpace setup.SamplePoint)) ≤
      (⨆ j < t.1 - 1,
        MeasurableSpace.comap (fun ω : setup.SamplePath => ω j)
          (by infer_instance : MeasurableSpace setup.SamplePoint)) := by
  have hidx : τ.1 - 1 ≤ t.1 - 1 := by
    omega
  refine iSup_le ?_
  intro j
  refine iSup_le ?_
  intro hj
  exact le_iSup_of_le j (le_iSup_of_le (lt_of_lt_of_le hj hidx) le_rfl)

/-- Finite-sum/exponential measurability closure for prefix MGF weights. -/
private theorem prefix_exp_measurable_of_summands
    {m : MeasurableSpace setup.SamplePath} (s : Finset Time) (ν : ℝ)
    (ζ : Time → setup.SamplePath → ℝ)
    (hζ : ∀ t ∈ s, Measurable[m] (ζ t)) :
    Measurable[m] (fun ω => Real.exp (ν * (∑ t ∈ s, ζ t ω))) := by
  have hsum : Measurable[m] (fun ω : setup.SamplePath => ∑ t ∈ s, ζ t ω) :=
    Finset.measurable_sum s hζ
  exact Real.continuous_exp.measurable.comp (measurable_const.mul hsum)

/-- Membership in the one-based output window gives the underlying natural-time
upper bound. -/
private theorem outputTimes_val_le_of_mem (k : ℕ) {τ : Time}
    (hτ : τ ∈ outputTimes k) : τ.1 ≤ k := by
  rcases (by
    simpa [outputTimes, SOptLib.positiveTimeOutputWindowTimes] using hτ :
      ∃ a, ∃ h : 1 ≤ a ∧ a ≤ k,
        (⟨a, le_trans (by norm_num : 1 ≤ 1) h.1⟩ : Time) = τ) with
    ⟨a, ha, h_eq⟩
  have hval : τ.1 = a := by
    simpa using congrArg Subtype.val h_eq.symm
  simpa [hval] using ha.2

set_option maxHeartbeats 4000000 in
/-- The chronological prefix MGF weight is measurable in the next strict past,
written in the residual-kernel form used by the one-step product-law transfer. -/
private theorem prefix_kernel_exp_weight_strictPast_measurable
    (k : ℕ) (ν : ℝ)
    (hstrict : ∀ t : Time,
      Measurable[
        (⨆ j < t.1 - 1,
          MeasurableSpace.comap (fun ω : setup.SamplePath => ω j)
            (by infer_instance : MeasurableSpace setup.SamplePoint))]
        (setup.crossTermQuery t)) :
    Measurable[
      (⨆ j < (SOptLib.natSuccPositiveTime k).1 - 1,
        MeasurableSpace.comap (fun ω : setup.SamplePath => ω j)
          (by infer_instance : MeasurableSpace setup.SamplePoint))]
      (fun ω =>
        Real.exp
          (ν *
            (∑ τ ∈ outputTimes k,
              -⟪(setup.crossTermQuery τ ω).2,
                setup.stochasticOracle (setup.crossTermQuery τ ω).1
                    (setup.sampleAt τ ω) -
                  setup.meanOracle (setup.crossTermQuery τ ω).1⟫_ℝ))) := by
  exact prefix_exp_kernel_sum_measurable_of_strictPast
    (strictPast := fun τ : Time =>
      (⨆ j < τ.1 - 1,
        MeasurableSpace.comap (fun ω : setup.SamplePath => ω j)
          (by infer_instance : MeasurableSpace setup.SamplePoint)))
    (sampleAt := setup.sampleAt)
    (q := setup.crossTermQuery)
    (kernel := fun (_τ : Time) q ξ =>
      -⟪q.2, setup.stochasticOracle q.1 ξ - setup.meanOracle q.1⟫_ℝ)
    (s := outputTimes k) (ν := ν)
    (hstrict_le := by
      intro τ hτ
      have hτ_le : τ.1 ≤ k := outputTimes_val_le_of_mem k hτ
      have hτt : τ.1 < (SOptLib.natSuccPositiveTime k).1 := by
        simpa [SOptLib.natSuccPositiveTime] using Nat.lt_succ_of_le hτ_le
      simpa using
        strictPast_mono_of_le (setup := setup) τ (SOptLib.natSuccPositiveTime k)
          (le_of_lt hτt))
    (hq := by
      intro τ _hτ
      exact hstrict τ)
    (hsample := by
      intro τ hτ
      have hτ_le : τ.1 ≤ k := outputTimes_val_le_of_mem k hτ
      have hτt : τ.1 < (SOptLib.natSuccPositiveTime k).1 := by
        simpa [SOptLib.natSuccPositiveTime] using Nat.lt_succ_of_le hτ_le
      simpa using
        sampleAt_strictPast_measurable_of_lt
          (setup := setup) τ (SOptLib.natSuccPositiveTime k) hτt)
    (hkernel := by
      intro _τ _hτ
      have hdir :
          Measurable
            (fun p : (setup.Point × Ambient EX EY) × setup.SamplePoint => p.1.2) :=
        measurable_snd.comp measurable_fst
      have hres :
          Measurable
            (fun p : (setup.Point × Ambient EX EY) × setup.SamplePoint =>
              setup.stochasticOracle p.1.1 p.2 - setup.meanOracle p.1.1) :=
        oracle_residual_product_measurable (setup := setup)
      have hinner :
          Measurable
            (fun p : (setup.Point × Ambient EX EY) × setup.SamplePoint =>
              ⟪p.1.2, setup.stochasticOracle p.1.1 p.2 -
                setup.meanOracle p.1.1⟫_ℝ) :=
        continuous_inner.measurable.comp (hdir.prodMk hres)
      simpa using hinner.neg)

private theorem crossTerm_kernel_summand_eq_gamma_auxiliary
    (t : Time) (ω : setup.SamplePath) :
    -⟪(setup.crossTermQuery t ω).2,
      setup.stochasticOracle (setup.crossTermQuery t ω).1 (setup.sampleAt t ω) -
        setup.meanOracle (setup.crossTermQuery t ω).1⟫_ℝ =
      setup.gamma t *
        ⟪(setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1,
          setup.oracleNoise t ω⟫_ℝ := by
  have hvec :
      -((setup.iterate t ω).1 - (setup.auxiliaryIterate t ω).1) =
        (setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1 := by
    abel
  rw [Setup.crossTermQuery, Setup.oracleNoise]
  calc
    -⟪setup.gamma t • ((setup.iterate t ω).1 - (setup.auxiliaryIterate t ω).1),
        setup.stochasticOracle (setup.iterate t ω) (setup.sampleAt t ω) -
          setup.meanOracle (setup.iterate t ω)⟫_ℝ
        = -(setup.gamma t *
            ⟪(setup.iterate t ω).1 - (setup.auxiliaryIterate t ω).1,
              setup.stochasticOracle (setup.iterate t ω) (setup.sampleAt t ω) -
                setup.meanOracle (setup.iterate t ω)⟫_ℝ) := by
            rw [real_inner_smul_left]
    _ = setup.gamma t *
          (-⟪(setup.iterate t ω).1 - (setup.auxiliaryIterate t ω).1,
            setup.stochasticOracle (setup.iterate t ω) (setup.sampleAt t ω) -
              setup.meanOracle (setup.iterate t ω)⟫_ℝ) := by
          ring
    _ = setup.gamma t *
          ⟪(setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1,
            setup.stochasticOracle (setup.iterate t ω) (setup.sampleAt t ω) -
              setup.meanOracle (setup.iterate t ω)⟫_ℝ := by
          rw [← inner_neg_left, hvec]

private theorem outputTimes_sum_eq_range_natSucc
    (N : ℕ) (f : Time → ℝ) :
    (∑ t ∈ outputTimes N, f t) =
      ∑ n ∈ Finset.range N, f (SOptLib.natSuccPositiveTime n) := by
  cases N with
  | zero =>
      simp [outputTimes, SOptLib.positiveTimeOutputWindowTimes]
      refine Finset.sum_eq_zero ?_
      intro x _hx
      have hxI : (x : ℕ) ∈ Finset.Icc 1 0 := x.2
      have hbounds := Finset.mem_Icc.mp hxI
      omega
  | succ k =>
      rw [outputTimes]
      rw [SOptLib.sum_positiveTimeOutputWindowTimes_eq_Icc (α := ℝ) 1 (k + 1)
        (by norm_num) (Nat.succ_pos k) f]
      rw [sum_Icc_one_eq_sum_range_succ]
      refine Finset.sum_congr rfl ?_
      intro n hn
      have hmem : n + 1 ∈ Finset.Icc 1 (k + 1) := by
        have hnlt : n < k + 1 := Finset.mem_range.mp hn
        simp only [Finset.mem_Icc]
        omega
      simp [hmem, SOptLib.natSuccPositiveTime]

set_option maxHeartbeats 4000000 in
private theorem prefix_gamma_exp_weight_strictPast_measurable
    (k : ℕ) (ν : ℝ)
    (hstrict : ∀ t : Time,
      Measurable[
        (⨆ j < t.1 - 1,
          MeasurableSpace.comap (fun ω : setup.SamplePath => ω j)
            (by infer_instance : MeasurableSpace setup.SamplePoint))]
        (setup.crossTermQuery t)) :
    Measurable[
      (⨆ j < (SOptLib.natSuccPositiveTime k).1 - 1,
        MeasurableSpace.comap (fun ω : setup.SamplePath => ω j)
          (by infer_instance : MeasurableSpace setup.SamplePoint))]
      (fun ω =>
        Real.exp
          (ν *
            (∑ n ∈ Finset.range k,
              setup.gamma (SOptLib.natSuccPositiveTime n) *
                ⟪(setup.auxiliaryIterate (SOptLib.natSuccPositiveTime n) ω).1 -
                    (setup.iterate (SOptLib.natSuccPositiveTime n) ω).1,
                  setup.oracleNoise (SOptLib.natSuccPositiveTime n) ω⟫_ℝ))) := by
  have hkernel :=
    prefix_kernel_exp_weight_strictPast_measurable (setup := setup) k ν hstrict
  have hfun :
      (fun ω : setup.SamplePath =>
        Real.exp
          (ν *
            (∑ τ ∈ outputTimes k,
              -⟪(setup.crossTermQuery τ ω).2,
                setup.stochasticOracle (setup.crossTermQuery τ ω).1
                    (setup.sampleAt τ ω) -
                  setup.meanOracle (setup.crossTermQuery τ ω).1⟫_ℝ))) =
        (fun ω =>
          Real.exp
            (ν *
              (∑ n ∈ Finset.range k,
                setup.gamma (SOptLib.natSuccPositiveTime n) *
                  ⟪(setup.auxiliaryIterate (SOptLib.natSuccPositiveTime n) ω).1 -
                      (setup.iterate (SOptLib.natSuccPositiveTime n) ω).1,
                    setup.oracleNoise (SOptLib.natSuccPositiveTime n) ω⟫_ℝ))) := by
    funext ω
    have hsum :
        (∑ τ ∈ outputTimes k,
          -⟪(setup.crossTermQuery τ ω).2,
            setup.stochasticOracle (setup.crossTermQuery τ ω).1 (setup.sampleAt τ ω) -
              setup.meanOracle (setup.crossTermQuery τ ω).1⟫_ℝ) =
          ∑ n ∈ Finset.range k,
            setup.gamma (SOptLib.natSuccPositiveTime n) *
              ⟪(setup.auxiliaryIterate (SOptLib.natSuccPositiveTime n) ω).1 -
                  (setup.iterate (SOptLib.natSuccPositiveTime n) ω).1,
                setup.oracleNoise (SOptLib.natSuccPositiveTime n) ω⟫_ℝ := by
      calc
        (∑ τ ∈ outputTimes k,
          -⟪(setup.crossTermQuery τ ω).2,
            setup.stochasticOracle (setup.crossTermQuery τ ω).1 (setup.sampleAt τ ω) -
              setup.meanOracle (setup.crossTermQuery τ ω).1⟫_ℝ)
            = ∑ τ ∈ outputTimes k,
                setup.gamma τ *
                  ⟪(setup.auxiliaryIterate τ ω).1 - (setup.iterate τ ω).1,
                    setup.oracleNoise τ ω⟫_ℝ := by
                refine Finset.sum_congr rfl ?_
                intro τ _hτ
                exact crossTerm_kernel_summand_eq_gamma_auxiliary (setup := setup) τ ω
        _ = ∑ n ∈ Finset.range k,
              setup.gamma (SOptLib.natSuccPositiveTime n) *
                ⟪(setup.auxiliaryIterate (SOptLib.natSuccPositiveTime n) ω).1 -
                    (setup.iterate (SOptLib.natSuccPositiveTime n) ω).1,
                  setup.oracleNoise (SOptLib.natSuccPositiveTime n) ω⟫_ℝ :=
              outputTimes_sum_eq_range_natSucc k
                (fun τ =>
                  setup.gamma τ *
                    ⟪(setup.auxiliaryIterate τ ω).1 - (setup.iterate τ ω).1,
                      setup.oracleNoise τ ω⟫_ℝ)
    rw [hsum]
  rw [← hfun]
  exact hkernel

set_option maxHeartbeats 4000000 in
private theorem ordered_range_cross_term_mgf_bound
    (N : ℕ) (ν : ℝ) (hν : 0 ≤ ν)
    (hexp : setup.exponentialMomentOracleBound)
    (hstrict : ∀ t : Time,
      Measurable[
        (⨆ j < t.1 - 1,
          MeasurableSpace.comap (fun ω : setup.SamplePath => ω j)
            (by infer_instance : MeasurableSpace setup.SamplePoint))]
        (setup.crossTermQuery t)) :
    Integrable
        (fun ω =>
          Real.exp
            (ν *
              (∑ n ∈ Finset.range N,
                setup.gamma (SOptLib.natSuccPositiveTime n) *
                  ⟪(setup.auxiliaryIterate (SOptLib.natSuccPositiveTime n) ω).1 -
                      (setup.iterate (SOptLib.natSuccPositiveTime n) ω).1,
                    setup.oracleNoise (SOptLib.natSuccPositiveTime n) ω⟫_ℝ)))
        setup.pathMeasure ∧
      ∫ ω,
          Real.exp
            (ν *
              (∑ n ∈ Finset.range N,
                setup.gamma (SOptLib.natSuccPositiveTime n) *
                  ⟪(setup.auxiliaryIterate (SOptLib.natSuccPositiveTime n) ω).1 -
                      (setup.iterate (SOptLib.natSuccPositiveTime n) ω).1,
                    setup.oracleNoise (SOptLib.natSuccPositiveTime n) ω⟫_ℝ))
          ∂setup.pathMeasure ≤
        Real.exp
          (∑ n ∈ Finset.range N,
            3 * ν ^ 2 *
              (8 * setup.gamma (SOptLib.natSuccPositiveTime n) ^ 2 * setup.M ^ 2) / 4) := by
  classical
  letI : IsProbabilityMeasure setup.pathMeasure := setup.pathMeasure_isProbabilityMeasure
  let ζ : ℕ → setup.SamplePath → ℝ := fun n ω =>
    setup.gamma (SOptLib.natSuccPositiveTime n) *
      ⟪(setup.auxiliaryIterate (SOptLib.natSuccPositiveTime n) ω).1 -
          (setup.iterate (SOptLib.natSuccPositiveTime n) ω).1,
        setup.oracleNoise (SOptLib.natSuccPositiveTime n) ω⟫_ℝ
  let c : ℕ → ℝ := fun n =>
    3 * ν ^ 2 *
      (8 * setup.gamma (SOptLib.natSuccPositiveTime n) ^ 2 * setup.M ^ 2) / 4
  let F : ℕ → MeasurableSpace setup.SamplePath := fun k =>
    (⨆ j < (SOptLib.natSuccPositiveTime k).1 - 1,
      MeasurableSpace.comap (fun ω : setup.SamplePath => ω j)
        (by infer_instance : MeasurableSpace setup.SamplePoint))
  refine
    integrable_exp_sum_le_exp_sum_of_weighted_one_step_mgf
      (P := setup.pathMeasure) (F := F) (ζ := ζ) (cost := c) (ν := ν) (N := N)
      ?_ ?_
  · intro k
    simpa [F, ζ] using
      prefix_gamma_exp_weight_strictPast_measurable
        (setup := setup) k ν hstrict
  · intro k H hH_strict hH_nonneg hH_int
    simpa [F, ζ, c] using
      prefix_cross_term_one_step_mgf_bound
        (setup := setup) (SOptLib.natSuccPositiveTime k) ν hν hexp H
        hH_strict (hstrict (SOptLib.natSuccPositiveTime k)) hH_nonneg hH_int

/-- Source Lemma 4.1 specialization for the fixed-horizon martingale cross term.

This is the remaining high-probability bridge in Proposition 4.10: the paper-sign
sum uses `γ_t ⟪v_t - z_t, Δ_t⟫`, while the deterministic regret decomposition
stores the same term as `-SC`.  The proof should combine strict-past
adaptedness, fresh-sample independence/law, centered residuals, the exponential
oracle moment, the product-DGF diameter normalization, and the scalar
martingale-difference light-tail recurrence from Lemma 4.1. -/
private theorem finite_iid_stream_cross_term_martingale_tail
    (N : ℕ) (hN : 1 ≤ N) (lambda : ℝ) (hlambda : 1 ≤ lambda)
    (hsteps : setup.constantStepsizePolicy N)
    (hexp : setup.exponentialMomentOracleBound)
    (hstrict : ∀ t : Time,
      Measurable[
        (⨆ j < t.1 - 1,
          MeasurableSpace.comap (fun ω : setup.SamplePath => ω j)
            (by infer_instance : MeasurableSpace setup.SamplePoint))]
        (setup.crossTermQuery t))
    (hindep : ∀ t : Time, IndepFun (setup.crossTermQuery t) (setup.sampleAt t)
      setup.pathMeasure)
    (hlaw : ∀ t : Time, Measure.map (setup.sampleAt t) setup.pathMeasure = setup.P)
    (hzero : ∀ t : Time,
      Integrable
          (fun ω =>
            setup.gamma t *
              ⟪(setup.iterate t ω).1 - (setup.auxiliaryIterate t ω).1,
                setup.oracleNoise t ω⟫_ℝ)
          setup.pathMeasure ∧
        (setup.pathExpectation fun ω =>
            setup.gamma t *
              ⟪(setup.iterate t ω).1 - (setup.auxiliaryIterate t ω).1,
                setup.oracleNoise t ω⟫_ℝ) = 0)
    (horacleMoment : ∀ t : Time,
      Integrable
          (fun ω =>
            Real.exp
              (setup.productDualNorm
                  (setup.stochasticOracle (setup.iterate t ω) (setup.sampleAt t ω)) ^ 2 /
                setup.M ^ 2))
          setup.pathMeasure ∧
        ∫ ω,
            Real.exp
              (setup.productDualNorm
                  (setup.stochasticOracle (setup.iterate t ω) (setup.sampleAt t ω)) ^ 2 /
                setup.M ^ 2) ∂setup.pathMeasure ≤
          Real.exp 1)
    (hcross_int : Integrable
      (fun ω =>
        ∑ t ∈ outputTimes N,
          setup.gamma t *
            ⟪(setup.iterate t ω).1 - (setup.auxiliaryIterate t ω).1,
              setup.oracleNoise t ω⟫_ℝ)
      setup.pathMeasure) :
    setup.pathMeasure
        {ω |
          (∑ t ∈ outputTimes N,
            setup.gamma t *
              ⟪(setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1,
                setup.oracleNoise t ω⟫_ℝ) >
            12 + (14 / 5 : ℝ) * lambda} ≤
      ENNReal.ofReal (Real.exp (-lambda)) := by
  have hcross_pointwise :
      ∀ t : Time, ∀ ω : setup.SamplePath,
        |setup.gamma t *
            ⟪(setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1,
              setup.oracleNoise t ω⟫_ℝ| ≤
          setup.gamma t *
            (setup.productDualNorm (setup.oracleNoise t ω) * Real.sqrt 2) := by
    intro t ω
    exact abs_auxiliary_cross_term_le_gamma_dual_sqrt_two (setup := setup) t ω
  have hcross_sq_pointwise :
      ∀ t : Time, ∀ ω : setup.SamplePath,
        (setup.gamma t *
            ⟪(setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1,
              setup.oracleNoise t ω⟫_ℝ) ^ 2 ≤
          2 * setup.gamma t ^ 2 *
            setup.productDualNorm (setup.oracleNoise t ω) ^ 2 := by
    intro t ω
    exact auxiliary_cross_term_sq_le_two_gamma_sq_dual_sq (setup := setup) t ω
  have hcross_scaled_arg :
      ∀ t : Time, ∀ ω : setup.SamplePath,
        (setup.gamma t *
            ⟪(setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1,
              setup.oracleNoise t ω⟫_ℝ) ^ 2 /
            (8 * setup.gamma t ^ 2 * setup.M ^ 2) ≤
          setup.productDualNorm
              (setup.stochasticOracle (setup.iterate t ω) (setup.sampleAt t ω)) ^ 2 /
              (2 * setup.M ^ 2) +
            (1 / 2 : ℝ) := by
    intro t ω
    exact auxiliary_cross_term_scaled_sq_le_oracle_scaled_sq_add_half
      (setup := setup) t ω
  have hfinite_mgf_route :
      ∀ ν : ℝ, 0 ≤ ν →
        (∀ t ∈ outputTimes N,
          ∀ H : setup.SamplePath → ℝ,
            (∀ ω, 0 ≤ H ω) →
            Integrable H setup.pathMeasure →
            Integrable
                (fun ω =>
                  H ω *
                    Real.exp
                      (ν *
                        (setup.gamma t *
                          ⟪(setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1,
                            setup.oracleNoise t ω⟫_ℝ)))
                setup.pathMeasure ∧
              ∫ ω,
                  H ω *
                    Real.exp
                      (ν *
                        (setup.gamma t *
                          ⟪(setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1,
                            setup.oracleNoise t ω⟫_ℝ)) ∂setup.pathMeasure ≤
                Real.exp
                  (3 * ν ^ 2 * (8 * setup.gamma t ^ 2 * setup.M ^ 2) / 4) *
                  ∫ ω, H ω ∂setup.pathMeasure) →
        Integrable
            (fun ω =>
              Real.exp
                (ν *
                  (∑ t ∈ outputTimes N,
                    setup.gamma t *
                      ⟪(setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1,
                        setup.oracleNoise t ω⟫_ℝ)))
            setup.pathMeasure ∧
          ∫ ω,
              Real.exp
                (ν *
                  (∑ t ∈ outputTimes N,
                    setup.gamma t *
                      ⟪(setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1,
                        setup.oracleNoise t ω⟫_ℝ)) ∂setup.pathMeasure ≤
            Real.exp
              (∑ t ∈ outputTimes N,
                3 * ν ^ 2 * (8 * setup.gamma t ^ 2 * setup.M ^ 2) / 4) := by
    intro ν hν hone
    exact finite_iid_stream_cross_term_mgf_le_of_one_step
      (setup := setup) N ν hν hone
  /-
  Direct proof attempt status:
  the available hypotheses give the random-query centering and exponential
  oracle moment term-by-term.  What is still missing is the finite conditional
  one-step weighted mgf transfer from PDF Lemma 4.1, i.e. a Lean API turning
  the strict-past `crossTermQuery`/fresh `sampleAt` structure into the
  conditional recurrence premise used by `hfinite_mgf_route`.
  The finite induction part of the exponential-tail recurrence is now isolated
  above; the remaining gap is the conditional/product-law weighted transfer.
  -/
  let S : setup.SamplePath → ℝ := fun ω =>
    ∑ t ∈ outputTimes N,
      setup.gamma t *
        ⟪(setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1,
          setup.oracleNoise t ω⟫_ℝ
  have hmgf_at_nu :
      Integrable (fun ω => Real.exp ((5 / 14 : ℝ) * S ω))
          setup.pathMeasure ∧
        ∫ ω, Real.exp ((5 / 14 : ℝ) * S ω) ∂setup.pathMeasure ≤
          Real.exp 1 := by
    have hordered_mgf_at_nu :
        Integrable (fun ω => Real.exp ((5 / 14 : ℝ) * S ω))
            setup.pathMeasure ∧
          ∫ ω, Real.exp ((5 / 14 : ℝ) * S ω) ∂setup.pathMeasure ≤
            Real.exp
              (∑ t ∈ outputTimes N,
                3 * (5 / 14 : ℝ) ^ 2 *
                    (8 * setup.gamma t ^ 2 * setup.M ^ 2) / 4) := by
      have hν : 0 ≤ (5 / 14 : ℝ) := by norm_num
      have hrange :=
        ordered_range_cross_term_mgf_bound
          (setup := setup) N (5 / 14 : ℝ) hν hexp hstrict
      have hS_eq : ∀ ω,
          S ω =
            ∑ n ∈ Finset.range N,
              setup.gamma (SOptLib.natSuccPositiveTime n) *
                ⟪(setup.auxiliaryIterate (SOptLib.natSuccPositiveTime n) ω).1 -
                    (setup.iterate (SOptLib.natSuccPositiveTime n) ω).1,
                  setup.oracleNoise (SOptLib.natSuccPositiveTime n) ω⟫_ℝ := by
        intro ω
        dsimp [S]
        exact outputTimes_sum_eq_range_natSucc N
          (fun t =>
            setup.gamma t *
              ⟪(setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1,
                setup.oracleNoise t ω⟫_ℝ)
      have hfun_eq :
          (fun ω => Real.exp ((5 / 14 : ℝ) * S ω)) =
            (fun ω =>
              Real.exp
                ((5 / 14 : ℝ) *
                  (∑ n ∈ Finset.range N,
                    setup.gamma (SOptLib.natSuccPositiveTime n) *
                      ⟪(setup.auxiliaryIterate (SOptLib.natSuccPositiveTime n) ω).1 -
                          (setup.iterate (SOptLib.natSuccPositiveTime n) ω).1,
                        setup.oracleNoise (SOptLib.natSuccPositiveTime n) ω⟫_ℝ))) := by
        funext ω
        rw [hS_eq ω]
      have hbudget_eq :
          (∑ n ∈ Finset.range N,
            3 * (5 / 14 : ℝ) ^ 2 *
              (8 * setup.gamma (SOptLib.natSuccPositiveTime n) ^ 2 * setup.M ^ 2) / 4) =
            (∑ t ∈ outputTimes N,
              3 * (5 / 14 : ℝ) ^ 2 *
                  (8 * setup.gamma t ^ 2 * setup.M ^ 2) / 4) := by
        exact (outputTimes_sum_eq_range_natSucc N
          (fun t =>
            3 * (5 / 14 : ℝ) ^ 2 *
              (8 * setup.gamma t ^ 2 * setup.M ^ 2) / 4)).symm
      constructor
      · rw [hfun_eq]
        exact hrange.1
      · calc
          ∫ ω, Real.exp ((5 / 14 : ℝ) * S ω) ∂setup.pathMeasure
              ≤ Real.exp
                  (∑ n ∈ Finset.range N,
                    3 * (5 / 14 : ℝ) ^ 2 *
                      (8 * setup.gamma (SOptLib.natSuccPositiveTime n) ^ 2 *
                          setup.M ^ 2) / 4) := by
                  rw [hfun_eq]
                  exact hrange.2
          _ = Real.exp
                (∑ t ∈ outputTimes N,
                  3 * (5 / 14 : ℝ) ^ 2 *
                      (8 * setup.gamma t ^ 2 * setup.M ^ 2) / 4) := by
                  rw [hbudget_eq]
    have hsum_c :
        (∑ t ∈ outputTimes N,
          3 * (5 / 14 : ℝ) ^ 2 *
              (8 * setup.gamma t ^ 2 * setup.M ^ 2) / 4) =
          (75 / 98 : ℝ) * (setup.M ^ 2 * setup.sumGammaSq N) := by
      rw [Setup.sumGammaSq]
      calc
        (∑ t ∈ outputTimes N,
          3 * (5 / 14 : ℝ) ^ 2 *
              (8 * setup.gamma t ^ 2 * setup.M ^ 2) / 4)
            = ∑ t ∈ outputTimes N,
                (75 / 98 : ℝ) * setup.M ^ 2 * setup.gamma t ^ 2 := by
              refine Finset.sum_congr rfl ?_
              intro t ht
              ring
        _ = (75 / 98 : ℝ) * setup.M ^ 2 *
              (∑ t ∈ outputTimes N, setup.gamma t ^ 2) := by
              rw [Finset.mul_sum]
        _ = (75 / 98 : ℝ) *
              (setup.M ^ 2 * (∑ t ∈ outputTimes N, setup.gamma t ^ 2)) := by
              ring
    let γ0 : ℝ := 2 / (setup.M * Real.sqrt (5 * (N : ℝ)))
    have hconstSums := setup.fixed_horizon_constant_step_sums N hN hsteps
    have hsumGammaSq_const : setup.sumGammaSq N = (N : ℝ) * γ0 ^ 2 :=
      hconstSums.2
    have hM2S : setup.M ^ 2 * setup.sumGammaSq N = 4 / 5 := by
      rw [hsumGammaSq_const]
      dsimp [γ0]
      have hMpos : 0 < setup.M := setup.M_pos
      have hNposNat : 0 < N := lt_of_lt_of_le (Nat.zero_lt_one) hN
      have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNposNat
      have hsqrtpos : 0 < Real.sqrt (5 * (N : ℝ)) := by
        exact Real.sqrt_pos_of_pos (by positivity)
      have hMne : setup.M ≠ 0 := ne_of_gt hMpos
      have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
      have hsqrtne : Real.sqrt (5 * (N : ℝ)) ≠ 0 := ne_of_gt hsqrtpos
      field_simp [hMne, hNne, hsqrtne,
        Real.sq_sqrt (by positivity : 0 ≤ 5 * (N : ℝ))]
      rw [Real.sq_sqrt (by positivity : 0 ≤ (N : ℝ) * 5)]
      ring
    have hsum_c_le_one :
        (∑ t ∈ outputTimes N,
          3 * (5 / 14 : ℝ) ^ 2 *
              (8 * setup.gamma t ^ 2 * setup.M ^ 2) / 4) ≤ 1 := by
      rw [hsum_c, hM2S]
      norm_num
    exact ⟨hordered_mgf_at_nu.1,
      le_trans hordered_mgf_at_nu.2 (Real.exp_le_exp.mpr hsum_c_le_one)⟩
  have htail :
      setup.pathMeasure {ω | S ω > 12 + (14 / 5 : ℝ) * lambda} ≤
        ENNReal.ofReal (Real.exp (-lambda)) := by
    refine measure_gt_le_exp_neg_of_mgf_bound_at
      (P := setup.pathMeasure) (S := S) (ν := (5 / 14 : ℝ))
      (lambda := lambda) (a := 12 + (14 / 5 : ℝ) * lambda) (C := 1)
      (by norm_num) ?_ hmgf_at_nu.1 hmgf_at_nu.2
    nlinarith
  simpa [S] using htail

private theorem maxRegretSum_fixed_horizon_large_deviation
    (N : ℕ) (hN : 1 ≤ N) (lambda : ℝ) (hlambda : 1 ≤ lambda)
    (hsteps : setup.constantStepsizePolicy N)
    (hexp : setup.exponentialMomentOracleBound) :
    setup.pathMeasure
        {ω |
          (setup.outputWeightSum N)⁻¹ * setup.maxRegretSum N ω >
            setup.largeDeviationThreshold N lambda} ≤
      ENNReal.ofReal (2 * Real.exp (-lambda)) := by
  letI : IsProbabilityMeasure setup.pathMeasure := setup.pathMeasure_isProbabilityMeasure
  let t0 : Time := ⟨1, by norm_num⟩
  have ht0le : t0.1 ≤ N := by
    simpa [t0] using hN
  have hgamma_t0 :
      setup.gamma t0 = 2 / (setup.M * Real.sqrt (5 * (N : ℝ))) :=
    hsteps t0 ht0le
  have hlambda_nonneg : 0 ≤ lambda := by
    exact le_trans (by norm_num : (0 : ℝ) ≤ 1) hlambda
  have hWpos : 0 < setup.outputWeightSum N :=
    setup.outputWeightSum_pos hN
  let γ0 : ℝ := 2 / (setup.M * Real.sqrt (5 * (N : ℝ)))
  have hconstSums := setup.fixed_horizon_constant_step_sums N hN hsteps
  have houtputWeight_const : setup.outputWeightSum N = (N : ℝ) * γ0 :=
    hconstSums.1
  have hsumGammaSq_const : setup.sumGammaSq N = (N : ℝ) * γ0 ^ 2 :=
    hconstSums.2
  have hbudget : ∀ ω, setup.maxRegretSum N ω ≤
      2 +
        (1 / 2 : ℝ) *
          Finset.sum (outputTimes N) (fun t =>
            setup.gamma t ^ 2 *
              (setup.productDualNorm
                (setup.stochasticOracle (setup.iterate t ω) (setup.sampleAt t ω))) ^ 2) +
        (1 / 2 : ℝ) *
          Finset.sum (outputTimes N) (fun t =>
            setup.gamma t ^ 2 *
              (setup.productDualNorm (setup.oracleNoise t ω)) ^ 2) -
        Finset.sum (outputTimes N) (fun t =>
          setup.gamma t *
            ⟪(setup.iterate t ω).1 - (setup.auxiliaryIterate t ω).1,
              setup.oracleNoise t ω⟫_ℝ) := by
    intro ω
    exact setup.maxRegretSum_pathwise_budget N ω
  have horacle_exp_t0 :
      ∫ ω,
        Real.exp (((setup.productDualNorm
          (setup.stochasticOracle (setup.iterate t0 ω) (setup.sampleAt t0 ω))) ^ 2) /
          setup.M ^ 2) ∂setup.pathMeasure ≤ Real.exp 1 :=
    (setup.random_iterate_product_oracle_exp_moment_bound t0 hexp).2
  let Gsq : Time → setup.SamplePath → ℝ := fun t ω =>
    (setup.productDualNorm
      (setup.stochasticOracle (setup.iterate t ω) (setup.sampleAt t ω))) ^ 2
  let SD : setup.SamplePath → ℝ := fun ω =>
    Finset.sum (outputTimes N) (fun t =>
      setup.gamma t ^ 2 * (setup.productDualNorm (setup.oracleNoise t ω)) ^ 2)
  let SG : setup.SamplePath → ℝ := fun ω =>
    Finset.sum (outputTimes N) (fun t => setup.gamma t ^ 2 * Gsq t ω)
  let SC : setup.SamplePath → ℝ := fun ω =>
    Finset.sum (outputTimes N) (fun t =>
      setup.gamma t *
        ⟪(setup.iterate t ω).1 - (setup.auxiliaryIterate t ω).1,
          setup.oracleNoise t ω⟫_ℝ)
  have hSD_absorb :
      ∀ ω, SD ω ≤ 2 * SG ω + 2 * setup.M ^ 2 * setup.sumGammaSq N := by
    intro ω
    dsimp [SD, SG, Gsq]
    calc
      Finset.sum (outputTimes N) (fun t =>
          setup.gamma t ^ 2 * (setup.productDualNorm (setup.oracleNoise t ω)) ^ 2)
          ≤ Finset.sum (outputTimes N) (fun t =>
              setup.gamma t ^ 2 *
                (2 * Gsq t ω + 2 * setup.M ^ 2)) := by
            refine Finset.sum_le_sum ?_
            intro t _ht
            exact mul_le_mul_of_nonneg_left
              (setup.oracle_noise_square_absorbed_by_oracle_square t ω)
              (sq_nonneg (setup.gamma t))
      _ = Finset.sum (outputTimes N) (fun t => 2 * (setup.gamma t ^ 2 * Gsq t ω)) +
            Finset.sum (outputTimes N) (fun t => (2 * setup.M ^ 2) * setup.gamma t ^ 2) := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl ?_
            intro t _ht
            ring
      _ = 2 * Finset.sum (outputTimes N) (fun t => setup.gamma t ^ 2 * Gsq t ω) +
            2 * setup.M ^ 2 * setup.sumGammaSq N := by
            rw [← Finset.mul_sum, Setup.sumGammaSq, ← Finset.mul_sum]
  have hbudget_absorbed :
      ∀ ω, setup.maxRegretSum N ω ≤
        2 + (3 / 2 : ℝ) * SG ω + setup.M ^ 2 * setup.sumGammaSq N - SC ω := by
    intro ω
    have hb :
        setup.maxRegretSum N ω ≤
          2 + (1 / 2 : ℝ) * SG ω + (1 / 2 : ℝ) * SD ω - SC ω := by
      simpa [SG, SD, SC, Gsq] using hbudget ω
    have hsd := hSD_absorb ω
    nlinarith
  have hNposNat : 0 < N := lt_of_lt_of_le (Nat.zero_lt_one) hN
  have hNposReal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNposNat
  have hgamma0_pos : 0 < γ0 := by
    dsimp [γ0]
    exact div_pos (by norm_num : (0 : ℝ) < 2)
      (mul_pos setup.M_pos (Real.sqrt_pos_of_pos (by positivity)))
  have hsumGammaSq_pos : 0 < setup.sumGammaSq N := by
    rw [hsumGammaSq_const]
    exact mul_pos hNposReal (sq_pos_of_pos hgamma0_pos)
  have hM_sq_pos : 0 < setup.M ^ 2 := sq_pos_of_pos setup.M_pos
  let θ : Time → ℝ := fun t => setup.gamma t ^ 2 / setup.sumGammaSq N
  have htheta_nonneg : ∀ t ∈ outputTimes N, 0 ≤ θ t := by
    intro t _ht
    dsimp [θ]
    exact div_nonneg (sq_nonneg (setup.gamma t)) hsumGammaSq_pos.le
  have htheta_sum : Finset.sum (outputTimes N) θ = 1 := by
    dsimp [θ]
    calc
      Finset.sum (outputTimes N) (fun t => setup.gamma t ^ 2 / setup.sumGammaSq N)
          = (setup.sumGammaSq N)⁻¹ *
              Finset.sum (outputTimes N) (fun t => setup.gamma t ^ 2) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro t _ht
            ring
      _ = (setup.sumGammaSq N)⁻¹ * setup.sumGammaSq N := by
            rw [Setup.sumGammaSq]
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hsumGammaSq_pos)
  let Fexp : setup.SamplePath → ℝ := fun ω =>
    Real.exp (SG ω / (setup.M ^ 2 * setup.sumGammaSq N))
  have hGsq_int : ∀ t ∈ outputTimes N, Integrable (Gsq t) setup.pathMeasure := by
    intro t _ht
    simpa [Gsq] using
      (setup.stochasticOracle_productDualNorm_sq_integrable_and_integral_bound t).1
  have hweighted_arg : ∀ ω,
      Finset.sum (outputTimes N) (fun t => θ t * (Gsq t ω / setup.M ^ 2)) =
        SG ω / (setup.M ^ 2 * setup.sumGammaSq N) := by
    intro ω
    dsimp [θ, SG]
    calc
      Finset.sum (outputTimes N) (fun t =>
          (setup.gamma t ^ 2 / setup.sumGammaSq N) *
            (Gsq t ω / setup.M ^ 2))
          = Finset.sum (outputTimes N) (fun t =>
              (1 / (setup.sumGammaSq N * setup.M ^ 2)) *
                (setup.gamma t ^ 2 * Gsq t ω)) := by
            refine Finset.sum_congr rfl ?_
            intro t _ht
            field_simp [ne_of_gt hsumGammaSq_pos, ne_of_gt hM_sq_pos]
      _ = (1 / (setup.sumGammaSq N * setup.M ^ 2)) *
            Finset.sum (outputTimes N) (fun t => setup.gamma t ^ 2 * Gsq t ω) := by
            rw [Finset.mul_sum]
      _ = SG ω / (setup.M ^ 2 * setup.sumGammaSq N) := by
            dsimp [SG]
            field_simp [ne_of_gt hsumGammaSq_pos, ne_of_gt hM_sq_pos]
  have horacle_exp_weighted :=
    integrable_exp_weighted_sum_le_of_exp_integral_bounds
      (μ := setup.pathMeasure) (s := outputTimes N) (theta := θ)
      (U := fun t ω => Gsq t ω / setup.M ^ 2) (B := Real.exp 1)
      (hU_aesm := fun t ht => by
        have hscaled :
            AEStronglyMeasurable
              (fun ω => (setup.M ^ 2)⁻¹ * Gsq t ω) setup.pathMeasure :=
          (hGsq_int t ht).aestronglyMeasurable.const_mul ((setup.M ^ 2)⁻¹)
        simpa [div_eq_mul_inv, mul_comm] using hscaled)
      (htheta_nonneg := htheta_nonneg) (htheta_sum := htheta_sum)
      (hU_exp_int := fun t _ht => by
        simpa [Gsq] using (setup.random_iterate_product_oracle_exp_moment_bound t hexp).1)
      (hU_exp_bound := fun t _ht => by
        simpa [Gsq] using (setup.random_iterate_product_oracle_exp_moment_bound t hexp).2)
  have hFexp_int : Integrable Fexp setup.pathMeasure := by
    simpa [Fexp, hweighted_arg] using horacle_exp_weighted.1
  have horacle_exp_integral_le :
      ∫ ω, Fexp ω ∂setup.pathMeasure ≤ Real.exp 1 := by
    simpa [Fexp, hweighted_arg] using horacle_exp_weighted.2
  have horacleTail :
      setup.pathMeasure
          {ω | SG ω > (1 + lambda) * setup.M ^ 2 * setup.sumGammaSq N} ≤
        ENNReal.ofReal (Real.exp (-lambda)) := by
    have htailF :=
      exp_markov_tail_of_integral_le
        (μ := setup.pathMeasure) Fexp lambda hlambda
        hFexp_int (fun _ => le_of_lt (Real.exp_pos _)) horacle_exp_integral_le
    have hden_pos : 0 < setup.M ^ 2 * setup.sumGammaSq N :=
      mul_pos hM_sq_pos hsumGammaSq_pos
    have hsubset :
        {ω | SG ω > (1 + lambda) * setup.M ^ 2 * setup.sumGammaSq N} ⊆
          {ω | Fexp ω > Real.exp (1 + lambda)} := by
      intro ω hω
      dsimp [Fexp]
      apply Real.exp_lt_exp.mpr
      have hω0 : SG ω > (1 + lambda) * setup.M ^ 2 * setup.sumGammaSq N := by
        simpa using hω
      have hω' : (1 + lambda) * (setup.M ^ 2 * setup.sumGammaSq N) < SG ω := by
        nlinarith
      exact (lt_div_iff₀ hden_pos).mpr hω'
    exact (measure_mono hsubset).trans htailF
  let A : Set setup.SamplePath :=
    {ω | SG ω > (1 + lambda) * setup.M ^ 2 * setup.sumGammaSq N}
  let B : Set setup.SamplePath :=
    {ω | -SC ω > 12 + (14 / 5 : ℝ) * lambda}
  have hcrossTail :
      setup.pathMeasure B ≤ ENNReal.ofReal (Real.exp (-lambda)) := by
    have hstrict :=
      fun t : Time => setup.crossTermQuery_strictPast_source_bridge t
    have hindep :=
      fun t : Time => setup.crossTermQuery_indep_sampleAt t
    have hlaw :=
      fun t : Time => setup.sampleAt_law t
    have hzero :=
      fun t : Time => setup.oracleNoise_cross_term_zero t
    have horacleMoment :=
      fun t : Time => setup.random_iterate_product_oracle_exp_moment_bound t hexp
    have hSC_int : Integrable SC setup.pathMeasure := by
      dsimp [SC]
      exact MeasureTheory.integrable_finset_sum (μ := setup.pathMeasure)
        (s := outputTimes N)
        (f := fun t ω =>
          setup.gamma t *
            ⟪(setup.iterate t ω).1 - (setup.auxiliaryIterate t ω).1,
              setup.oracleNoise t ω⟫_ℝ)
        (fun t _ht => (hzero t).1)
    have htail :=
      finite_iid_stream_cross_term_martingale_tail
        (setup := setup) N hN lambda hlambda hsteps hexp
        hstrict hindep hlaw hzero horacleMoment hSC_int
    refine (measure_mono ?_).trans htail
    intro ω hω
    have hsign :
        -SC ω =
          ∑ t ∈ outputTimes N,
            setup.gamma t *
              ⟪(setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1,
                setup.oracleNoise t ω⟫_ℝ := by
      dsimp [SC]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl ?_
      intro t _ht
      have hinner :
          -⟪(setup.iterate t ω).1 - (setup.auxiliaryIterate t ω).1,
              setup.oracleNoise t ω⟫_ℝ =
            ⟪(setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1,
              setup.oracleNoise t ω⟫_ℝ := by
        have hvec :
            -((setup.iterate t ω).1 - (setup.auxiliaryIterate t ω).1) =
              (setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1 := by
          abel
        calc
          -⟪(setup.iterate t ω).1 - (setup.auxiliaryIterate t ω).1,
              setup.oracleNoise t ω⟫_ℝ =
            ⟪-((setup.iterate t ω).1 - (setup.auxiliaryIterate t ω).1),
              setup.oracleNoise t ω⟫_ℝ := by
                rw [inner_neg_left]
          _ =
            ⟪(setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1,
              setup.oracleNoise t ω⟫_ℝ := by rw [hvec]
      calc
        -(setup.gamma t *
            ⟪(setup.iterate t ω).1 - (setup.auxiliaryIterate t ω).1,
              setup.oracleNoise t ω⟫_ℝ)
            =
          setup.gamma t *
            (-⟪(setup.iterate t ω).1 - (setup.auxiliaryIterate t ω).1,
              setup.oracleNoise t ω⟫_ℝ) := by ring
        _ =
          setup.gamma t *
            ⟪(setup.auxiliaryIterate t ω).1 - (setup.iterate t ω).1,
              setup.oracleNoise t ω⟫_ℝ := by rw [hinner]
    dsimp [B] at hω
    simpa [hsign] using hω
  have hM2S : setup.M ^ 2 * setup.sumGammaSq N = 4 / 5 := by
    rw [hsumGammaSq_const]
    dsimp [γ0]
    have hMne : setup.M ≠ 0 := ne_of_gt setup.M_pos
    have hsqrtpos : 0 < Real.sqrt (5 * (N : ℝ)) :=
      Real.sqrt_pos_of_pos (by positivity)
    have hsqrtne : Real.sqrt (5 * (N : ℝ)) ≠ 0 := ne_of_gt hsqrtpos
    field_simp [hMne, hsqrtne,
      Real.sq_sqrt (by positivity : 0 ≤ 5 * (N : ℝ))]
    rw [Real.sq_sqrt (by positivity : 0 ≤ (N : ℝ) * 5)]
    ring
  have hWT :
      setup.outputWeightSum N * setup.largeDeviationThreshold N lambda =
        16 + 4 * lambda := by
    rw [houtputWeight_const]
    unfold Setup.largeDeviationThreshold
    dsimp [γ0]
    have hMne : setup.M ≠ 0 := ne_of_gt setup.M_pos
    have hsqrt5pos : 0 < Real.sqrt (5 : ℝ) :=
      Real.sqrt_pos_of_pos (by norm_num)
    have hsqrtNpos : 0 < Real.sqrt (N : ℝ) :=
      Real.sqrt_pos_of_pos hNposReal
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 5) (N : ℝ)]
    field_simp [hMne, ne_of_gt hsqrt5pos, ne_of_gt hsqrtNpos]
    rw [Real.sq_sqrt (le_of_lt hNposReal)]
    ring
  have htarget_subset :
      {ω |
          (setup.outputWeightSum N)⁻¹ * setup.maxRegretSum N ω >
            setup.largeDeviationThreshold N lambda} ⊆ A ∪ B := by
    intro ω hω
    by_cases hAω : ω ∈ A
    · exact Or.inl hAω
    · refine Or.inr ?_
      by_contra hBω
      have hSG_le :
          SG ω ≤ (1 + lambda) * setup.M ^ 2 * setup.sumGammaSq N := by
        exact le_of_not_gt (by simpa [A] using hAω)
      have hSC_le : -SC ω ≤ 12 + (14 / 5 : ℝ) * lambda := by
        exact le_of_not_gt (by simpa [B] using hBω)
      have hR_gt :
          setup.outputWeightSum N * setup.largeDeviationThreshold N lambda <
            setup.maxRegretSum N ω := by
        have hmul :=
          mul_lt_mul_of_pos_left hω hWpos
        calc
          setup.outputWeightSum N * setup.largeDeviationThreshold N lambda
              < setup.outputWeightSum N *
                  ((setup.outputWeightSum N)⁻¹ * setup.maxRegretSum N ω) := hmul
          _ = setup.maxRegretSum N ω := by
                field_simp [ne_of_gt hWpos]
      have hR_le :
          setup.maxRegretSum N ω ≤
            setup.outputWeightSum N * setup.largeDeviationThreshold N lambda := by
        have hbudgetω := hbudget_absorbed ω
        rw [hWT]
        nlinarith [hbudgetω, hSG_le, hSC_le, hM2S]
      exact (not_lt_of_ge hR_le) hR_gt
  calc
    setup.pathMeasure
        {ω |
          (setup.outputWeightSum N)⁻¹ * setup.maxRegretSum N ω >
            setup.largeDeviationThreshold N lambda}
        ≤ setup.pathMeasure (A ∪ B) := measure_mono htarget_subset
    _ ≤ setup.pathMeasure A + setup.pathMeasure B :=
        MeasureTheory.measure_union_le A B
    _ ≤ ENNReal.ofReal (Real.exp (-lambda)) +
          ENNReal.ofReal (Real.exp (-lambda)) := by
        exact add_le_add (by simpa [A] using horacleTail) hcrossTail
    _ = ENNReal.ofReal (2 * Real.exp (-lambda)) := by
        rw [← ENNReal.ofReal_add (le_of_lt (Real.exp_pos _))
          (le_of_lt (Real.exp_pos _))]
        congr 1
        ring

/-- Large-deviation event in Proposition 4.10. -/
def largeDeviationEvent (N : ℕ) (hN : 1 ≤ N) (lambda : ℝ) : Set setup.SamplePath :=
  {ω | setup.epsilonPhi (setup.weightedAverageOutput N hN ω) >
    setup.largeDeviationThreshold N lambda}

/-- Proposition 4.10, B-track repaired specialization.

This public endpoint proves the source high-probability saddle-gap tail from
the generated stochastic mirror-descent process, the fixed-horizon constant
stepsizes `(4.3.15)`, exponential oracle moments `(4.3.18)`, the normalized
max-regret large-deviation theorem, and the weighted-output regret comparison.
It deliberately exposes that direct specialization rather than routing through
an opaque formalization of the source phrase "conditions of `(4.3.16)`". -/
theorem proposition_4_10_large_deviation_bound (N : ℕ) (hN : 1 ≤ N) (lambda : ℝ)
    (hlambda : 1 ≤ lambda)
    (hsteps : setup.constantStepsizePolicy N)
    (hexp : setup.exponentialMomentOracleBound) :
    setup.pathMeasure (setup.largeDeviationEvent N hN lambda) ≤
      ENNReal.ofReal (2 * Real.exp (-lambda)) := by
  have htail :=
    setup.maxRegretSum_fixed_horizon_large_deviation N hN lambda hlambda hsteps hexp
  have hsubset :
      setup.largeDeviationEvent N hN lambda ⊆
        {ω |
          (setup.outputWeightSum N)⁻¹ * setup.maxRegretSum N ω >
            setup.largeDeviationThreshold N lambda} := by
    intro ω hω
    exact lt_of_lt_of_le hω
      (setup.epsilonPhi_weightedAverage_le_regret N hN ω)
  exact (measure_mono hsubset).trans htail

end Setup

end StochasticConvexConcaveSaddlePoint
