import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import SOptLib.Model.Norms

/-!
# Baillon-Haddad Axioms

This module isolates co-coercivity-style facts whose printed source proofs use
domain-sensitive analytic arguments.  In Lan's text, the relevant Lemma 5.8 proof
uses the point `x - L^{-1} * grad phi x`; for a merely closed convex carrier this
point is not automatically feasible.  Algorithm formalizations may consume this
as a named source boundary instead of reproving the full constrained
Baillon-Haddad theorem inside each algorithm file.
-/

open scoped InnerProductSpace

namespace SOptLib

/-- Gâteaux-gradient predicate for a total representative of a function on an
open domain.

For `x ∈ U`, this states that every directional scalar trace
`t ↦ Φ (x + t • d)` has derivative `⟪g, d⟫` at `0`.  On an open domain the trace
is eventually evaluated inside `U`, so this is the Lean interface matching the
Gâteaux differentiability phrase in Pérez-Aros--Vilches Theorem 3.1. -/
def HasGateauxGradientAt
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (Φ : E → ℝ) (g : E) (x : E) : Prop :=
  ∀ d : E, HasDerivAt (fun t : ℝ => Φ (x + t • d)) ⟪g, d⟫_ℝ 0

/-- Pérez-Aros--Vilches 2019, Theorem 3.1, direction `(a) -> (c)`, in the
paper's Gâteaux-gradient interface.

Paper statement: on a nonempty open convex subset of a Hilbert space, a convex
Gâteaux differentiable function whose gradient is `β`-Lipschitz has
`1 / β`-cocoercive gradient.  Here `B` is the selected gradient field and
`HasGateauxGradientAt Φ (B u) u` is the directional-derivative statement
corresponding to the paper's `∇f(u)`.

This is the paper-exact Baillon-Haddad axiom.  Carrier or Bregman-gap variants
must be treated as corollaries/boundaries derived from this theorem plus the
appropriate chart and boundary transport, not as the literal PAV statement. -/
axiom perez_aros_vilches_open_convex_inner_cocoercivity
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (Φ : E → ℝ) (B : E → E) (U : Set E) (β : ℝ)
    (hβ_pos : 0 < β)
    (hU_open : IsOpen U)
    (hU_convex : Convex ℝ U)
    (hΦ_convex : ConvexOn ℝ U Φ)
    (hgrad : ∀ u ∈ U, HasGateauxGradientAt Φ (B u) u)
    (hB_lipschitz :
      ∀ u ∈ U, ∀ v ∈ U, ‖B u - B v‖ ≤ β * ‖u - v‖) :
    ∀ u ∈ U, ∀ v ∈ U,
      ‖B u - B v‖ ^ 2 ≤ β * ⟪B u - B v, u - v⟫_ℝ

/-- Carrier-level Baillon-Haddad/co-coercivity boundary from support, smooth
upper model, within-gradient semantics, and selected-gradient Lipschitzness.

This is intentionally a downstream carrier boundary, not the literal
Pérez-Aros--Vilches theorem.  It packages the constrained Baillon-Haddad route
already developed in the VRMD formalization: finite-dimensional carrier
reduction, selected `HasGradientWithinAt` semantics, affine-span gradient
representatives, first-order support/nonnegative Bregman gaps, a quadratic
smooth upper model, and an `L`-Lipschitz selected gradient.

The finite-dimensional and affine-span-direction hypotheses are part of the
boundary.  They rule out using an arbitrary normal component of a within-gradient
on lower-dimensional carriers, and they match the constrained carrier route
rather than Lan's unrestricted inverse-gradient-point proof sketch.  A future
proof of this boundary should derive it from
`perez_aros_vilches_open_convex_inner_cocoercivity` by affine-chart transport,
zero-base shifting, and boundary extension.

Use this only as an explicit source/analysis boundary; do not extract it as a
proved SOptLib theorem unless the constrained-domain proof is supplied. -/
axiom carrier_baillon_haddad_of_support_upper_gradient_semantics_lipschitz
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    {X : Set E} (v : {x : E // x ∈ X} → ℝ) (F : E → ℝ)
    (grad : {x : E // x ∈ X} → E)
    (L : ℝ)
    (hX_convex : Convex ℝ X)
    (hL_pos : 0 < L)
    (hF_eval : ∀ (z : E) (hz : z ∈ X), F z = v ⟨z, hz⟩)
    (hgrad : ∀ z : {x : E // x ∈ X}, HasGradientWithinAt F (grad z) X z.1)
    (hgrad_mem_direction :
      ∀ x : {x : E // x ∈ X}, grad x ∈ (affineSpan ℝ X).direction)
    (hBreg_nonneg :
      ∀ x y : {x : E // x ∈ X},
        0 ≤ v x - v y - ⟪grad y, x.1 - y.1⟫_ℝ)
    (hBreg_upper :
      ∀ x y : {x : E // x ∈ X},
        v x - v y - ⟪grad y, x.1 - y.1⟫_ℝ ≤
          L / 2 * ‖x.1 - y.1‖ ^ 2)
    (hgrad_lipschitz :
      ∀ x y : {x : E // x ∈ X}, ‖grad x - grad y‖ ≤ L * ‖x.1 - y.1‖)
    (x y : {x : E // x ∈ X}) :
    (1 / (2 * L)) * ‖grad x - grad y‖ ^ 2 ≤
      v x - v y - ⟪grad y, x.1 - y.1⟫_ℝ

/-- Carrier Baillon-Haddad boundary for an arbitrary separating primal
seminorm and its canonical support dual on the carrier's affine directions.

This is the norm-general counterpart of
`carrier_baillon_haddad_of_support_upper_gradient_semantics_lipschitz`.
It is isolated here because the usual proof first passes to an open affine
chart (or to convex conjugacy) and then transports the result back to a closed
carrier. Lan's inverse-gradient-step proof does not supply that transport: the
shifted point need not remain feasible. Algorithm files may consume this
approved analysis boundary instead of reconstructing the open-domain theorem.

The declaration was manually approved as a SOptLib analysis boundary on
2026-07-29. It must not be copied into an algorithm file as a local axiom. -/
axiom carrier_baillon_haddad_of_separating_seminorm_affine_support
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    {X : Set E} (v : {x : E // x ∈ X} → ℝ) (F : E → ℝ)
    (grad : {x : E // x ∈ X} → E)
    (p : Seminorm ℝ E) (L : ℝ)
    (hp : p.IsSeparating)
    (hX_closed : IsClosed X)
    (hX_convex : Convex ℝ X)
    (hL_pos : 0 < L)
    (hF_eval : ∀ (z : E) (hz : z ∈ X), F z = v ⟨z, hz⟩)
    (hgrad : ∀ z : {x : E // x ∈ X}, HasGradientWithinAt F (grad z) X z.1)
    (hgrad_mem_direction :
      ∀ z : {x : E // x ∈ X}, grad z ∈ (affineSpan ℝ X).direction)
    (hBreg_nonneg :
      ∀ x y : {x : E // x ∈ X},
        0 ≤ v x - v y - ⟪grad y, x.1 - y.1⟫_ℝ)
    (hBreg_upper :
      ∀ x y : {x : E // x ∈ X},
        v x - v y - ⟪grad y, x.1 - y.1⟫_ℝ ≤
          L / 2 * p (x.1 - y.1) ^ 2)
    (hgrad_lipschitz :
      ∀ x y : {x : E // x ∈ X},
        sSup {r : ℝ |
          ∃ d : E, d ∈ (affineSpan ℝ X).direction ∧
            p d ≤ 1 ∧ r = |⟪grad x - grad y, d⟫_ℝ|} ≤
          L * p (x.1 - y.1))
    (x y : {x : E // x ∈ X}) :
    (1 / (2 * L)) *
        (sSup {r : ℝ |
          ∃ d : E, d ∈ (affineSpan ℝ X).direction ∧
            p d ≤ 1 ∧ r = |⟪grad x - grad y, d⟫_ℝ|}) ^ 2 ≤
      v x - v y - ⟪grad y, x.1 - y.1⟫_ℝ

/-- Compatibility name for existing algorithm files.

The old name is retained as a wrapper, but the actual axiom is the more explicit
support/upper/within-gradient carrier boundary above. -/
theorem carrier_baillon_haddad_of_convex_lipschitz_gradient
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    {X : Set E} (v : {x : E // x ∈ X} → ℝ) (F : E → ℝ)
    (grad : {x : E // x ∈ X} → E)
    (L : ℝ)
    (hX_convex : Convex ℝ X)
    (hL_pos : 0 < L)
    (hF_eval : ∀ (z : E) (hz : z ∈ X), F z = v ⟨z, hz⟩)
    (hgrad : ∀ z : {x : E // x ∈ X}, HasGradientWithinAt F (grad z) X z.1)
    (hgrad_mem_direction :
      ∀ x : {x : E // x ∈ X}, grad x ∈ (affineSpan ℝ X).direction)
    (hBreg_nonneg :
      ∀ x y : {x : E // x ∈ X},
        0 ≤ v x - v y - ⟪grad y, x.1 - y.1⟫_ℝ)
    (hBreg_upper :
      ∀ x y : {x : E // x ∈ X},
        v x - v y - ⟪grad y, x.1 - y.1⟫_ℝ ≤
          L / 2 * ‖x.1 - y.1‖ ^ 2)
    (hgrad_lipschitz :
      ∀ x y : {x : E // x ∈ X}, ‖grad x - grad y‖ ≤ L * ‖x.1 - y.1‖)
    (x y : {x : E // x ∈ X}) :
    (1 / (2 * L)) * ‖grad x - grad y‖ ^ 2 ≤
      v x - v y - ⟪grad y, x.1 - y.1⟫_ℝ :=
  carrier_baillon_haddad_of_support_upper_gradient_semantics_lipschitz
    v F grad L hX_convex hL_pos hF_eval hgrad hgrad_mem_direction
    hBreg_nonneg hBreg_upper hgrad_lipschitz x y

end SOptLib
