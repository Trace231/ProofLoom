import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Order.Filter.Extr
import SOptLib.Model.BlockSampling
import SOptLib.Model.Iterates
import SOptLib.Model.Norms
import SOptLib.Model.Objective
import SOptLib.Model.Prox
import SOptLib.Model.Selection
import SOptLib.Model.StochasticOracle
import SOptLib.Glue.Algebra
import SOptLib.Glue.Analysis
import SOptLib.Glue.Probability
import SOptLib.Layer0.ConvexFOC
import SOptLib.Layer0.Objective
import SOptLib.Layer1.Descent
import SOptLib.Layer1.Telescope

/-!
# Nonconvex stochastic block mirror descent: object layer

This file records the paper-facing mathematical objects for Lan's nonconvex
stochastic block mirror descent method from Section 6.3.  The algorithmic spine
is definition-centric: block prox points are selected from the paper argmin,
projected-gradient mappings are scaled prox displacements, sampled block oracle
values come from the primitive stochastic gradient kernel, and iterates are
generated recursively from the one-step update.
-/

open scoped BigOperators
open scoped Gradient
open scoped InnerProductSpace
open MeasureTheory

namespace SGD.NonconvexStochasticBlockMirrorDescent

variable {Ξ ι E : Type*} {Block : ι → Type*}

/-- Coordinate replacement used by the sampled-block update in Eq. (6.3.13). -/
def replaceBlock [DecidableEq ι] (i : ι) (x : ∀ j, Block j) (u : Block i) :
    ∀ j, Block j :=
  Function.update x i u

@[simp]
theorem replaceBlock_selected [DecidableEq ι]
    (i : ι) (x : ∀ j, Block j) (u : Block i) :
    replaceBlock i x u i = u := by
  simp [replaceBlock]

@[simp]
theorem replaceBlock_other [DecidableEq ι]
    {i j : ι} (x : ∀ j, Block j) (u : Block i) (hji : j ≠ i) :
    replaceBlock i x u j = x j := by
  simp [replaceBlock, Function.update_of_ne hji]

/-- Replacing one feasible block in a product-feasible state preserves feasibility. -/
theorem replaceBlock_mem_pi_univ [DecidableEq ι]
    (X : ∀ i, Set (Block i)) (i : ι) (x : ∀ j, Block j) (u : Block i)
    (hx : x ∈ Set.pi Set.univ X) (hu : u ∈ X i) :
    replaceBlock i x u ∈ Set.pi Set.univ X := by
  rw [Set.mem_univ_pi] at hx ⊢
  intro j
  by_cases hji : j = i
  · subst j
    simpa using hu
  · simpa [replaceBlock, Function.update_of_ne hji] using hx j

/-- Product-state coordinates are feasible block points. -/
theorem coord_mem_pi_univ
    (X : ∀ i, Set (Block i)) (i : ι) (x : ∀ j, Block j)
    (hx : x ∈ Set.pi Set.univ X) :
    x i ∈ X i :=
  (Set.mem_univ_pi.mp hx) i

/-- Canonical finite-product Hilbert gradient, returned in block coordinates.

The paper writes `g(x)`/`∇f(x)` for the exact gradient.  Since the raw dependent
product carries the paper's block notation while Mathlib's Hilbert structure
lives on `PiLp 2`, this definition computes the Mathlib gradient after
assembling the block state as a `PiLp` point and then projects it back to raw
coordinates.
-/
noncomputable def exactBlockGradient
    [Fintype ι]
    [∀ i, NormedAddCommGroup (Block i)] [∀ i, InnerProductSpace ℝ (Block i)]
    [∀ i, CompleteSpace (Block i)]
    (f : (∀ i, Block i) → ℝ) (x : ∀ i, Block i) : ∀ i, Block i :=
  SOptLib.piLpBlockGradient f x

@[simp]
theorem exactBlockGradient_apply
    [Fintype ι]
    [∀ i, NormedAddCommGroup (Block i)] [∀ i, InnerProductSpace ℝ (Block i)]
    [∀ i, CompleteSpace (Block i)]
    (f : (∀ i, Block i) → ℝ) (x : ∀ i, Block i) (i : ι) :
    exactBlockGradient f x i =
      WithLp.ofLp
        (gradient (fun y : PiLp 2 Block => f (WithLp.ofLp y)) (WithLp.toLp 2 x)) i := by
  simpa [exactBlockGradient] using SOptLib.piLpBlockGradient_apply (f := f) (x := x) (i := i)

/-- Convexity for a real-valued block term on its feasible carrier. -/
def IsConvexBlockTerm
    [∀ i, NormedAddCommGroup (Block i)] [∀ i, InnerProductSpace ℝ (Block i)]
    (X : ∀ i, Set (Block i))
    (chi : ∀ i, {z : Block i // z ∈ X i} → ℝ) (i : ι) : Prop :=
  ∀ (x : Block i) (hx : x ∈ X i) (y : Block i) (hy : y ∈ X i)
    (a b : ℝ), 0 ≤ a → 0 ≤ b → a + b = 1 →
        (hxy : a • x + b • y ∈ X i) →
        chi i ⟨a • x + b • y, hxy⟩ ≤ a * chi i ⟨x, hx⟩ + b * chi i ⟨y, hy⟩

private theorem convexOn_totalize_of_isConvexBlockTerm
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {X : Set H} {chi : {z : H // z ∈ X} → ℝ}
    (hX_convex : Convex ℝ X)
    (hchi_convex :
      ∀ (x : H) (hx : x ∈ X) (y : H) (hy : y ∈ X)
        (a b : ℝ), 0 ≤ a → 0 ≤ b → a + b = 1 →
          (hxy : a • x + b • y ∈ X) →
          chi ⟨a • x + b • y, hxy⟩ ≤
            a * chi ⟨x, hx⟩ + b * chi ⟨y, hy⟩) :
    ConvexOn ℝ X (SOptLib.totalizeOn X chi) := by
  refine ⟨hX_convex, ?_⟩
  intro x hx y hy a b ha hb hab
  have hxy : a • x + b • y ∈ X := hX_convex hx hy ha hb hab
  simpa [SOptLib.totalizeOn_of_mem X chi hx,
    SOptLib.totalizeOn_of_mem X chi hy,
    SOptLib.totalizeOn_of_mem X chi hxy] using
      hchi_convex x hx y hy a b ha hb hab hxy

private theorem lowerSemicontinuousOn_totalize_of_closed_subtype_epigraph
    {H : Type*} [TopologicalSpace H] {X : Set H} {chi : {z : H // z ∈ X} → ℝ}
    (hchi_closed : IsClosed {p : ({z : H // z ∈ X} × ℝ) | chi p.1 ≤ p.2}) :
    LowerSemicontinuousOn (SOptLib.totalizeOn X chi) X := by
  exact SOptLib.lowerSemicontinuousOn_totalizeOn_of_closed_carrier_epigraph hchi_closed

private theorem closed_convex_block_term_affine_lower_bound
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {X : Set H} {chi : {z : H // z ∈ X} → ℝ}
    (hX_closed : IsClosed X) (hX_convex : Convex ℝ X)
    (hchi_closed : IsClosed {p : ({z : H // z ∈ X} × ℝ) | chi p.1 ≤ p.2})
    (hchi_convex :
      ∀ (x : H) (hx : x ∈ X) (y : H) (hy : y ∈ X)
        (a b : ℝ), 0 ≤ a → 0 ≤ b → a + b = 1 →
          (hxy : a • x + b • y ∈ X) →
          chi ⟨a • x + b • y, hxy⟩ ≤
            a * chi ⟨x, hx⟩ + b * chi ⟨y, hy⟩)
    (z : {x : H // x ∈ X}) :
    ∃ (l : H →L[ℝ] ℝ) (c : ℝ),
      ∀ y : {x : H // x ∈ X}, l y.1 + c ≤ chi y := by
  simpa [SOptLib.totalizeOn_of_mem X chi] using
    exists_continuousLinearMap_add_const_le_of_closed_convex_lscOn
      hX_closed
      (convexOn_totalize_of_isConvexBlockTerm hX_convex hchi_convex)
      (lowerSemicontinuousOn_totalize_of_closed_subtype_epigraph hchi_closed)
      z

private theorem coercive_tail_of_pos_quadratic_add_clm_add_const_add_nonneg
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {X : Set H} (x0 z g : H) {a : ℝ} (ell : H →L[ℝ] ℝ)
    (c : ℝ) (Rterm F : H → ℝ)
    (ha : 0 < a)
    (hF_lower :
      ∀ x : H, x ∈ X →
        a * ‖x - z‖ ^ 2 + ell x + c + Rterm x ≤ F x)
    (hRterm_nonneg : ∀ x : H, x ∈ X → 0 ≤ Rterm x) :
    ∀ B : ℝ, ∃ R : ℝ, ‖x0 - z‖ ≤ R ∧
      ∀ x : H, x ∈ X → R ≤ ‖x - z‖ → B ≤ F x := by
  exact
    coercive_lower_tail_of_pos_quadratic_add_clm_add_const_add_nonneg
      (X := X) x0 z (a := a) ell c Rterm F ha hF_lower hRterm_nonneg

private theorem exists_isMinOn_of_lsc_closed_coercive_closedBall
    {E : Type*} [PseudoMetricSpace E] [ProperSpace E]
    {X : Set E} (hX_closed : IsClosed X) (x0 z : E) (hx0 : x0 ∈ X)
    (F : E → ℝ) (hlsc : LowerSemicontinuousOn F X)
    (htail : ∃ R : ℝ, dist x0 z ≤ R ∧
      ∀ x : E, x ∈ X → R ≤ dist x z → F x0 ≤ F x) :
    ∃ x : E, x ∈ X ∧ IsMinOn F X x := by
  exact _root_.exists_isMinOn_of_lsc_closed_coercive_closedBall
    hX_closed x0 z hx0 F hlsc htail

/-- Block-facing alias for the SOptLib distance-generating-function predicate.

It records the source statement that `ν_i` is a modulus-1 DGF and that `V_i` is
the associated Bregman prox-function, while reusing the canonical model-level
DGF object from `SOptLib.Model.Bregman`.
-/
abbrev IsBlockDistanceGeneratingFunction
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (X : Set E) (nu : E → ℝ) (nuGrad : E → E) : Prop :=
  _root_.IsDistanceGeneratingFunctionOn X nu nuGrad

/-- Squared block norm from Section 6.3:
`‖x‖² = ∑ᵢ ‖x⁽ⁱ⁾‖ᵢ²`. -/
noncomputable def blockNormSq
    [Fintype ι] [∀ i, NormedAddCommGroup (Block i)]
    (x : ∀ i, Block i) : ℝ :=
  SOptLib.dependentProductNormSq x

/-- Source-facing problem data for Section 6.3.

The fields are stated problem data and primitive assumptions: block carriers,
the nonconvex smooth part `f`, separable simple terms `χᵢ`, distance-generating
functions `νᵢ`, the primitive stochastic gradient kernel `G`, stepsizes, block
probabilities, smoothness constants, variance budgets, and the initial feasible
point.  Algorithmic objects such as exact gradients, the source mean-gradient
symbol `g`, Bregman prox functions, sampled gradients, prox points, updates, and
iterates are canonical definitions below, not fields.
-/
structure Setup (Ξ ι : Type*) (Block : ι → Type*) [MeasurableSpace Ξ]
    [Fintype ι] [DecidableEq ι]
    [∀ i, NormedAddCommGroup (Block i)] [∀ i, InnerProductSpace ℝ (Block i)]
    [∀ i, FiniteDimensional ℝ (Block i)]
    [∀ i, CompleteSpace (Block i)] where
  /-- Block feasible carriers `X_i`; source: Eq. (6.3.5), closed convex blocks. -/
  X : ∀ i, Set (Block i)
  /-- Smooth part `f`; source: Eq. (6.3.1), `φ(x) = f(x) + χ(x)`. -/
  f : (∀ i, Block i) → ℝ
  /-- Smoothness of `f`; source: Section 6.3, "`f` is smooth". -/
  f_smooth : ContDiff ℝ 1 (fun y : PiLp 2 Block => f (WithLp.ofLp y))
  /-- Separable simple terms `χ_i`; source: Eq. (6.3.4). -/
  chi : ∀ i, {z : Block i // z ∈ X i} → ℝ
  /-- Distance-generating functions `ν_i`; source: Section 6.3 before Eq. (6.3.6). -/
  nu : ∀ i, Block i → ℝ
  /-- Selected gradients of the DGF potentials, used to define the associated `V_i`. -/
  nuGrad : ∀ i, Block i → Block i
  /-- Primitive stochastic gradient kernel `G(x, ξ)`; source: Algorithm 6.1 step 2. -/
  G : (∀ i, Block i) → Ξ → ∀ i, Block i
  /-- One-step oracle sample law for the random variable `ξ_k` in Algorithm 6.1. -/
  sampleLaw : Measure Ξ
  /-- The oracle sample law is a probability law for the random variable `ξ_k`. -/
  sampleLaw_prob : IsProbabilityMeasure sampleLaw
  /-- Initial feasible point `x₁ ∈ X`; source: Algorithm 6.1 input. -/
  x₁ : ∀ i, Block i
  /-- Stepsizes `γ_k`; source: Algorithm 6.1 input. -/
  γ : ℕ → ℝ
  /-- Block sampling probabilities `p_i`; source: Eq. (6.3.11). -/
  p : ι → ℝ
  /-- Block smoothness constants `L_i`; source: Eqs. (6.3.2)-(6.3.3). -/
  L : ι → ℝ
  /-- Stochastic-gradient variance budgets `\bar σ_k`; source: Eq. (6.3.12). -/
  sigmaBar : ℕ → ℝ
  /-- Prox quadratic-growth constant `Q`; source: Eq. (6.3.7). -/
  Q : ℝ
  /-- Closedness of each block carrier; source: Eq. (6.3.5). -/
  block_closed : ∀ i, IsClosed (X i)
  /-- Convexity of each block carrier; source: Eq. (6.3.5). -/
  block_convex : ∀ i, Convex ℝ (X i)
  /-- Closedness of each simple block term; source: Eq. (6.3.4). -/
  chi_closed : ∀ i, IsClosed {p : ({z : Block i // z ∈ X i} × ℝ) | chi i p.1 ≤ p.2}
  /-- Convexity of each simple block term; source: Eq. (6.3.4). -/
  chi_convex : ∀ i, IsConvexBlockTerm X chi i
  /-- DGF structure with modulus one; source: Section 6.3 before Eq. (6.3.6). -/
  nu_dgf : ∀ i, IsBlockDistanceGeneratingFunction (X i) (nu i) (nuGrad i)
  /-- Block Lipschitz-gradient condition; source: Eq. (6.3.2). -/
  block_lipschitz_gradients :
    ∀ (x : ∀ i, Block i) (i : ι) (ρ : Block i),
      ‖exactBlockGradient f (replaceBlock i x (x i + ρ)) i -
          exactBlockGradient f x i‖ ≤ L i * ‖ρ‖
  /-- Initial point feasibility; source: Algorithm 6.1 input. -/
  x₁_mem : x₁ ∈ Set.pi Set.univ X
  /-- Existence of a minimizer realizing `φ* := min_{x∈X} φ(x)`;
  source: Eq. (6.3.1).

  The book states the problem value as a minimum, so attainment is a
  source-facing boundary fact rather than a theorem to derive from arbitrary
  closed convex block data.
  -/
  problem_minimizer_exists :
    ∃ x : {x : ∀ i, Block i // x ∈ Set.pi Set.univ X},
      ∀ y : {x : ∀ i, Block i // x ∈ Set.pi Set.univ X},
        f x.1 + ∑ i, chi i ⟨x.1 i, (Set.mem_univ_pi.mp x.2) i⟩ ≤
          f y.1 + ∑ i, chi i ⟨y.1 i, (Set.mem_univ_pi.mp y.2) i⟩
  /-- Positive stepsize domain for the prox mapping; source: Eq. (6.3.8) defines
  `P_X(x,y,γ)` for a constant `γ > 0`, and Algorithm 6.1 uses `γ_k` in that
  mapping. -/
  γ_pos : ∀ k, 1 ≤ k → 0 < γ k
  /-- Source upper stepsize restriction `γ_k < 2/L_i`; source: Algorithm 6.1 input. -/
  γ_lt_two_div_L : ∀ k, 1 ≤ k → ∀ i, γ k < 2 / L i
  /-- Nonnegative block probabilities; source: Algorithm 6.1 input. -/
  p_nonneg : ∀ i, 0 ≤ p i
  /-- Sum-one block sampling law; source: Algorithm 6.1 input and Eq. (6.3.11). -/
  p_sum : ∑ i, p i = 1
  /-- Positive quadratic-growth constant; source: Eq. (6.3.7). -/
  Q_pos : 0 < Q
  /-- Prox-function quadratic growth; source: Eq. (6.3.7). -/
  prox_quadratic_growth :
    ∀ (i : ι) (x z : {z : Block i // z ∈ X i}),
      carrierBregmanFormula (nu i) id (nuGrad i) x.1 z.1 ≤
        (Q / 2) * ‖z.1 - x.1‖ ^ 2

namespace Setup

variable [MeasurableSpace Ξ]
variable [Fintype ι] [DecidableEq ι]
variable [∀ i, NormedAddCommGroup (Block i)] [∀ i, InnerProductSpace ℝ (Block i)]
variable [∀ i, FiniteDimensional ℝ (Block i)]
variable [∀ i, CompleteSpace (Block i)]

/-- Feasible product carrier for the paper problem. -/
abbrev Carrier (S : Setup Ξ ι Block) : Type _ :=
  {x : ∀ i, Block i // x ∈ Set.pi Set.univ S.X}

/-- Initial feasible point as a carrier element. -/
def x₁Carrier (S : Setup Ξ ι Block) : S.Carrier :=
  ⟨S.x₁, S.x₁_mem⟩

/-- Exact block gradient `∇f(x)` in the paper's block coordinates. -/
noncomputable def grad (S : Setup Ξ ι Block) (x : ∀ i, Block i) : ∀ i, Block i :=
  exactBlockGradient S.f x

@[simp]
theorem grad_eq_exactBlockGradient (S : Setup Ξ ι Block) (x : ∀ i, Block i) :
    S.grad x = exactBlockGradient S.f x := by
  rfl

/-- Source mean-gradient symbol `g(x)` from Eq. (6.3.12).

The paper centers the stochastic-gradient condition at `g(x_k)` but the proof
of Theorem 6.9 later works with `∇f(x_k)`.  This definition keeps the source
symbol as the canonical mean-oracle object induced by the primitive stochastic
kernel, rather than definitionally identifying it with Mathlib's exact gradient.
-/
noncomputable def sourceGradient (S : Setup Ξ ι Block) (x : ∀ i, Block i) :
    ∀ i, Block i :=
  SOptLib.paperMeanOracle S.sampleLaw S.G id x

@[simp]
theorem sourceGradient_eq_paperMeanOracle (S : Setup Ξ ι Block) (x : ∀ i, Block i) :
    S.sourceGradient x = SOptLib.paperMeanOracle S.sampleLaw S.G id x := by
  rfl

/-- The one-block affine line has derivative given by the corresponding
single-coordinate insertion in the finite `PiLp` product. -/
private theorem replaceBlock_line_hasDerivAt_piLp (x : ∀ i, Block i)
    (i : ι) (ρ : Block i) :
    HasDerivAt (fun t : ℝ => WithLp.toLp 2 (replaceBlock i x (x i + t • ρ)))
      (PiLp.single 2 i ρ) 0 := by
  have hraw :
      HasDerivAt (fun t : ℝ => replaceBlock i x (x i + t • ρ))
        (Pi.single i ρ) 0 := by
    refine hasDerivAt_pi.2 ?_
    intro j
    by_cases hji : j = i
    · subst j
      simpa [replaceBlock, Pi.single_eq_same] using
        (((hasDerivAt_id' (x := (0 : ℝ))).smul_const ρ).const_add (x i))
    · simpa [replaceBlock, Function.update_of_ne hji, Pi.single_eq_of_ne hji] using
        (hasDerivAt_const (x := (0 : ℝ)) (c := x j))
  have hcomp :=
    (((PiLp.continuousLinearEquiv 2 ℝ Block).symm :
        (∀ j, Block j) →L[ℝ] PiLp 2 Block).hasFDerivAt.comp_hasDerivAt 0 hraw)
  simpa [PiLp.coe_symm_continuousLinearEquiv, PiLp.toLp_single] using hcomp

/-- The ambient Mathlib gradient induces the expected gradient for one
coordinate slice of the objective. -/
private theorem block_coordinate_hasGradientAt (S : Setup Ξ ι Block)
    (x : ∀ i, Block i) (i : ι) (u : Block i) :
    HasGradientAt (fun z : Block i => S.f (replaceBlock i x z))
      (S.grad (replaceBlock i x u) i) u := by
  simpa [Setup.grad, exactBlockGradient, replaceBlock] using
    SOptLib.hasGradientAt_coordinate_slice_of_piLp_hasGradientAt
      (f := S.f) (x := x) (i := i) (u := u)
      (g := gradient (fun y : PiLp 2 Block => S.f (WithLp.ofLp y))
        (WithLp.toLp 2 (replaceBlock i x u)))
      (by
        simpa [replaceBlock] using
          (S.f_smooth.differentiable_one.differentiableAt
            (x := WithLp.toLp 2 (replaceBlock i x u))).hasGradientAt)

/-- The source block-Lipschitz gradient condition specialized to a fixed
coordinate slice. -/
private theorem block_coordinate_gradient_lipschitz (S : Setup Ξ ι Block)
    (x : ∀ i, Block i) (i : ι) :
    ∀ u v : Block i,
      ‖S.grad (replaceBlock i x u) i - S.grad (replaceBlock i x v) i‖ ≤
        S.L i * ‖u - v‖ := by
  intro u v
  have h := S.block_lipschitz_gradients (replaceBlock i x v) i (u - v)
  have huv : v + (u - v) = u := by
    abel
  simpa [Setup.grad, replaceBlock, huv] using h

/-- Coordinate form of the smooth quadratic upper model. -/
private theorem block_coordinate_smooth_upper_model (S : Setup Ξ ι Block)
    (x : ∀ i, Block i) (i : ι) (u v : Block i) :
    S.f (replaceBlock i x u) ≤
      S.f (replaceBlock i x v) +
        ⟪S.grad (replaceBlock i x v) i, u - v⟫_ℝ +
          (S.L i / 2) * ‖u - v‖ ^ 2 := by
  exact smooth_quadratic_upper_bound_of_hasGradientAt_lipschitzOn_convex
    (X := Set.univ) (f := fun z : Block i => S.f (replaceBlock i x z))
    (grad := fun z : Block i => S.grad (replaceBlock i x z) i)
    (L := S.L i) convex_univ (by
      intro z _hz
      exact block_coordinate_hasGradientAt (S := S) (x := x) (i := i) (u := z))
    (by
      intro z _hz w _hw
      exact block_coordinate_gradient_lipschitz (S := S) (x := x) (i := i) z w)
    (x := v) (y := u) (by simp) (by simp)

/-- The exact block gradient realizes the block directional derivative of `f`.

The gradient is now a canonical Mathlib object on the finite `PiLp` product,
projected back to block coordinates by `exactBlockGradient`.  The remaining
proof obligation is the calculus bridge from that finite-product gradient to
the paper's single-block directional derivative notation.
-/
theorem grad_block_directional_derivative_obligation (S : Setup Ξ ι Block)
    (x : ∀ i, Block i) (_hx : x ∈ Set.pi Set.univ S.X) (i : ι) (ρ : Block i) :
    HasDerivAt (fun t : ℝ => S.f (replaceBlock i x (x i + t • ρ)))
      ⟪S.grad x i, ρ⟫_ℝ 0 := by
  let F : PiLp 2 Block → ℝ := fun y => S.f (WithLp.ofLp y)
  have hFgrad :
      HasGradientAt F (gradient F (WithLp.toLp 2 x)) (WithLp.toLp 2 x) := by
    simpa [F] using
      (S.f_smooth.differentiable_one.differentiableAt
        (x := WithLp.toLp 2 x)).hasGradientAt
  have hline := replaceBlock_line_hasDerivAt_piLp (x := x) (i := i) (ρ := ρ)
  have hcomp := hFgrad.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by
    ext j
    by_cases hji : j = i
    · subst j
      simp [replaceBlock]
    · simp [replaceBlock, Function.update_of_ne hji])
  have hval :
      (InnerProductSpace.toDual ℝ (PiLp 2 Block) (gradient F (WithLp.toLp 2 x)))
          (PiLp.single 2 i ρ) = ⟪S.grad x i, ρ⟫_ℝ := by
    change ⟪gradient F (WithLp.toLp 2 x), PiLp.single 2 i ρ⟫_ℝ =
      ⟪S.grad x i, ρ⟫_ℝ
    rw [← SOptLib.piLp_inner_coord_single
      (i := i) (v := gradient F (WithLp.toLp 2 x)) (u := ρ)]
    simp [Setup.grad, exactBlockGradient, F]
  rw [← hval]
  simpa [F] using hcomp

/-- Associated Bregman prox-function `V_i` generated by `ν_i`. -/
noncomputable def V (S : Setup Ξ ι Block) (i : ι) :
    {z : Block i // z ∈ S.X i} → {z : Block i // z ∈ S.X i} → ℝ :=
  fun x z => carrierBregmanFormula (S.nu i) id (S.nuGrad i) x.1 z.1

@[simp]
theorem V_apply (S : Setup Ξ ι Block) (i : ι)
    (x z : {z : Block i // z ∈ S.X i}) :
    S.V i x z =
      carrierBregmanFormula (S.nu i) id (S.nuGrad i) x.1 z.1 := by
  rfl

/-- The associated prox-function inherits the modulus-one DGF lower bound. -/
theorem V_lower_bound (S : Setup Ξ ι Block) (i : ι)
    (x z : {z : Block i // z ∈ S.X i}) :
    (1 / 2 : ℝ) * ‖z.1 - x.1‖ ^ 2 ≤ S.V i x z := by
  simpa [Setup.V, norm_sub_rev] using (S.nu_dgf i).2.2 x.1 x.2 z.1 z.2

/-- Source block norm squared on product vectors. -/
noncomputable def blockNormSq (_S : Setup Ξ ι Block) (x : ∀ i, Block i) : ℝ :=
  SGD.NonconvexStochasticBlockMirrorDescent.blockNormSq x

@[simp]
theorem blockNormSq_eq_sum (S : Setup Ξ ι Block) (x : ∀ i, Block i) :
    S.blockNormSq x = ∑ i, ‖x i‖ ^ 2 := by
  rfl

/-- Derived block descent model from the block Lipschitz-gradient condition.

The PDF introduces Eq. (6.3.3) with "It then follows that" after Eq. (6.3.2),
so this is a theorem obligation, not primitive setup data.
-/
theorem block_descent_model (S : Setup Ξ ι Block) :
    ∀ (x : ∀ i, Block i), x ∈ Set.pi Set.univ S.X → ∀ (i : ι) (ρ : Block i),
      S.f (replaceBlock i x (x i + ρ)) ≤
        S.f x + ⟪S.grad x i, ρ⟫_ℝ + (S.L i / 2) * ‖ρ‖ ^ 2 := by
  intro x _hx i ρ
  simpa [replaceBlock] using
    SOptLib.block_smooth_upper_bound_of_coordinate_gradient_lipschitz
      (f := S.f) (grad := S.grad) (x := x) (i := i) (L := S.L i)
      (hgrad := fun u =>
        block_coordinate_hasGradientAt (S := S) (x := x) (i := i) (u := u))
      (hgrad_lipschitz := fun u v =>
        block_coordinate_gradient_lipschitz (S := S) (x := x) (i := i) u v)
      (rho := ρ)

/-- Positive stepsize obligation for the prox mapping used by Algorithm 6.1.

Eq. (6.3.8) defines the projected-gradient mapping for a constant `γ > 0`;
Algorithm 6.1 supplies the stepsize sequence used in that mapping.  This theorem
projects the source-facing positivity field from `Setup`.
-/
theorem gamma_pos_obligation (S : Setup Ξ ι Block) (k : ℕ) (_hk : 1 ≤ k) :
    0 < S.γ k :=
  S.γ_pos k _hk

end Setup

/-- Block prox objective from Eq. (6.3.6):
`⟪y, z - x⟫ + γ⁻¹ V_i(x,z) + χ_i(z)`. -/
noncomputable def blockProxObjective
    [∀ i, NormedAddCommGroup (Block i)] [∀ i, InnerProductSpace ℝ (Block i)]
    (X : ∀ i, Set (Block i))
    (V : ∀ i, {z : Block i // z ∈ X i} → {z : Block i // z ∈ X i} → ℝ)
    (chi : ∀ i, {z : Block i // z ∈ X i} → ℝ)
    (i : ι) (x : {z : Block i // z ∈ X i}) (y : Block i) (γ : ℝ)
    (z : {z : Block i // z ∈ X i}) : ℝ :=
  ⟪y, z.1 - x.1⟫_ℝ + γ⁻¹ * V i x z + chi i z

/-- Argmin predicate for the paper block prox point in Eq. (6.3.6). -/
def IsBlockProxPoint
    [∀ i, NormedAddCommGroup (Block i)] [∀ i, InnerProductSpace ℝ (Block i)]
    (X : ∀ i, Set (Block i))
    (V : ∀ i, {z : Block i // z ∈ X i} → {z : Block i // z ∈ X i} → ℝ)
    (chi : ∀ i, {z : Block i // z ∈ X i} → ℝ)
    (i : ι) (x : {z : Block i // z ∈ X i}) (y : Block i) (γ : ℝ)
    (xplus : {z : Block i // z ∈ X i}) : Prop :=
  IsMinOn (blockProxObjective X V chi i x y γ) Set.univ xplus

/-- Sampled block oracle value `G_{i_k}(x_k, ξ_k)` from Algorithm 6.1 step 2. -/
def sampledBlockGradient
    (G : (∀ i, Block i) → Ξ → ∀ i, Block i)
    (x : ∀ i, Block i) (ξ : Ξ) (i : ι) : Block i :=
  G x ξ i

@[simp]
theorem sampledBlockGradient_eq
    (G : (∀ i, Block i) → Ξ → ∀ i, Block i)
    (x : ∀ i, Block i) (ξ : Ξ) (i : ι) :
    sampledBlockGradient G x ξ i = G x ξ i := by
  rfl

namespace Setup

variable [MeasurableSpace Ξ]
variable [Fintype ι] [DecidableEq ι]
variable [∀ i, NormedAddCommGroup (Block i)] [∀ i, InnerProductSpace ℝ (Block i)]
variable [∀ i, FiniteDimensional ℝ (Block i)]
variable [∀ i, CompleteSpace (Block i)]

/-- Sampled block oracle derived from the primitive kernel stored in `Setup`. -/
def sampledGradient (S : Setup Ξ ι Block) (x : S.Carrier) (ξ : Ξ) (i : ι) : Block i :=
  sampledBlockGradient S.G x.1 ξ i

/-- Named prox solvability/well-definedness obligation for Eq. (6.3.6).

The source defines the prox mapping by an argmin over `X_i`.  Existence is kept
as a proof obligation from the paper setup, not as a free setup field and not as
a theorem-head hypothesis in Theorem 6.9.
-/
theorem blockProxPoint_exists_obligation (S : Setup Ξ ι Block)
    (i : ι) (x : S.Carrier) (y : Block i) (γ : ℝ) (_hγ : 0 < γ) :
    ∃ xplus : {z : Block i // z ∈ S.X i},
      IsBlockProxPoint S.X S.V S.chi i ⟨x.1 i, (Set.mem_univ_pi.mp x.2) i⟩ y γ xplus := by
  have _hlsc_blockProxObjective :
      LowerSemicontinuousOn
        (fun z : Block i =>
          (⟪y, z - x.1 i⟫_ℝ +
            γ⁻¹ * carrierBregmanFormula (S.nu i) id (S.nuGrad i) (x.1 i) z) +
            SOptLib.totalizeOn (S.X i) (S.chi i) z)
        (S.X i) := by
    refine
      lowerSemicontinuousOn_add_totalized_subtype_of_continuousOn
        (X := S.X i)
        (smoothPart := fun z : Block i =>
          ⟪y, z - x.1 i⟫_ℝ +
            γ⁻¹ * carrierBregmanFormula (S.nu i) id (S.nuGrad i) (x.1 i) z)
        (chi := S.chi i) ?_ (S.chi_closed i)
    have hnu_cont : ContinuousOn (S.nu i) (S.X i) := by
      intro z hz
      exact ((S.nu_dgf i).2.1 z hz).continuousAt.continuousWithinAt
    have hV_cont :
        ContinuousOn
          (fun z : Block i =>
            carrierBregmanFormula (S.nu i) id (S.nuGrad i) (x.1 i) z)
          (S.X i) := by
      have hdiff : ContinuousOn (fun z : Block i => z - x.1 i) (S.X i) :=
        continuousOn_id.sub continuousOn_const
      have hinner :
          ContinuousOn
            (fun z : Block i => ⟪S.nuGrad i (x.1 i), z - x.1 i⟫_ℝ)
            (S.X i) :=
        continuousOn_const.inner hdiff
      simpa [carrierBregmanFormula] using
        (hnu_cont.sub continuousOn_const).sub hinner
    have hdiff : ContinuousOn (fun z : Block i => z - x.1 i) (S.X i) :=
      continuousOn_id.sub continuousOn_const
    have hlin : ContinuousOn (fun z : Block i => ⟪y, z - x.1 i⟫_ℝ) (S.X i) :=
      continuousOn_const.inner hdiff
    exact hlin.add (continuousOn_const.mul hV_cont)
  simpa [IsBlockProxPoint, blockProxObjective, Setup.V] using
    exists_compositeProxObjective_isMinOn_of_closed_convex_lsc_dgf
      (X := S.X i) (chi := S.chi i) (nu := S.nu i) (grad := S.nuGrad i)
      (hX_closed := S.block_closed i) (hchi_closed := S.chi_closed i)
      (hchi_convex :=
        convexOn_totalize_of_isConvexBlockTerm (S.block_convex i) (S.chi_convex i))
      (hdgf := S.nu_dgf i)
      (x := ⟨x.1 i, (Set.mem_univ_pi.mp x.2) i⟩) (g := y) (γ := γ) _hγ

/-- Setup-level selected block prox point from Eq. (6.3.6), with positive stepsize. -/
noncomputable def blockProxPoint (S : Setup Ξ ι Block)
    (i : ι) (x : S.Carrier) (y : Block i) (γ : ℝ) (_hγ : 0 < γ) :
    {z : Block i // z ∈ S.X i} :=
  Classical.choose (S.blockProxPoint_exists_obligation i x y γ _hγ)

/-- The selected prox point used by `Setup.step` satisfies the source argmin
property.  The non-trivial source proof of prox solvability remains the named
obligation above. -/
theorem blockProxPoint_isProx (S : Setup Ξ ι Block)
    (i : ι) (x : S.Carrier) (y : Block i) (γ : ℝ) (hγ : 0 < γ) :
    IsBlockProxPoint S.X S.V S.chi i ⟨x.1 i, (Set.mem_univ_pi.mp x.2) i⟩ y γ
      (S.blockProxPoint i x y γ hγ) := by
  simpa [Setup.blockProxPoint] using
    Classical.choose_spec (S.blockProxPoint_exists_obligation i x y γ hγ)

/-- The local block prox certificate also minimizes the canonical SOptLib
prox objective.  The local objective uses `⟪g,z-x⟫`, whereas
`SOptLib.proxObjective` uses `⟪g,z⟫`; the difference is a constant in `z`. -/
private theorem blockProxPoint_isSOptLibProx (S : Setup Ξ ι Block)
    (i : ι) (x : S.Carrier) (y : Block i) (γ : ℝ) (hγ : 0 < γ) :
    IsMinOn
      (SOptLib.proxObjective
        (fun a b : {z : Block i // z ∈ S.X i} => S.V i a b)
        (S.chi i) (fun z : {z : Block i // z ∈ S.X i} => z.1)
        ⟨x.1 i, (Set.mem_univ_pi.mp x.2) i⟩ y γ)
      Set.univ
      (S.blockProxPoint i x y γ hγ) := by
  let xblock : {z : Block i // z ∈ S.X i} := ⟨x.1 i, (Set.mem_univ_pi.mp x.2) i⟩
  let xp := S.blockProxPoint i x y γ hγ
  have hmin : IsBlockProxPoint S.X S.V S.chi i xblock y γ xp := by
    simpa [xblock, xp] using S.blockProxPoint_isProx i x y γ hγ
  rw [IsBlockProxPoint, isMinOn_iff] at hmin
  rw [isMinOn_iff]
  intro z hz
  have h := hmin z (Set.mem_univ z)
  change
    SOptLib.proxObjective
        (fun a b : {z : Block i // z ∈ S.X i} => S.V i a b)
        (S.chi i) (fun z : {z : Block i // z ∈ S.X i} => z.1)
        xblock y γ xp ≤
      SOptLib.proxObjective
        (fun a b : {z : Block i // z ∈ S.X i} => S.V i a b)
        (S.chi i) (fun z : {z : Block i // z ∈ S.X i} => z.1)
        xblock y γ z
  unfold SOptLib.proxObjective at *
  unfold blockProxObjective at h
  dsimp [xblock, xp] at h ⊢
  rw [inner_sub_right, inner_sub_right] at h
  nlinarith

/-- The local block prox certificate in the ambient-totalized simple-term shape
required by SOptLib's composite variational inequality. -/
private theorem blockProxPoint_isSOptLibAmbientProx (S : Setup Ξ ι Block)
    (i : ι) (x : S.Carrier) (y : Block i) (γ : ℝ) (hγ : 0 < γ) :
    IsMinOn
      (SOptLib.proxObjective
        (fun a b : {z : Block i // z ∈ S.X i} =>
          carrierBregmanFormula (S.nu i) id (S.nuGrad i) a.1 b.1)
        (fun z : {z : Block i // z ∈ S.X i} =>
          SOptLib.totalizeOn (S.X i) (S.chi i) z.1)
        (fun z : {z : Block i // z ∈ S.X i} => z.1)
        ⟨x.1 i, (Set.mem_univ_pi.mp x.2) i⟩ y γ)
      Set.univ
      (S.blockProxPoint i x y γ hγ) := by
  let xblock : {z : Block i // z ∈ S.X i} := ⟨x.1 i, (Set.mem_univ_pi.mp x.2) i⟩
  let xp := S.blockProxPoint i x y γ hγ
  have hmin : IsBlockProxPoint S.X S.V S.chi i xblock y γ xp := by
    simpa [xblock, xp] using S.blockProxPoint_isProx i x y γ hγ
  rw [IsBlockProxPoint, isMinOn_iff] at hmin
  rw [isMinOn_iff]
  intro z hz
  have h := hmin z (Set.mem_univ z)
  change
    SOptLib.proxObjective
        (fun a b : {z : Block i // z ∈ S.X i} =>
          carrierBregmanFormula (S.nu i) id (S.nuGrad i) a.1 b.1)
        (fun z : {z : Block i // z ∈ S.X i} =>
          SOptLib.totalizeOn (S.X i) (S.chi i) z.1)
        (fun z : {z : Block i // z ∈ S.X i} => z.1)
        xblock y γ xp ≤
      SOptLib.proxObjective
        (fun a b : {z : Block i // z ∈ S.X i} =>
          carrierBregmanFormula (S.nu i) id (S.nuGrad i) a.1 b.1)
        (fun z : {z : Block i // z ∈ S.X i} =>
          SOptLib.totalizeOn (S.X i) (S.chi i) z.1)
        (fun z : {z : Block i // z ∈ S.X i} => z.1)
        xblock y γ z
  unfold SOptLib.proxObjective at *
  unfold blockProxObjective Setup.V at h
  dsimp [xblock, xp] at h ⊢
  rw [SOptLib.totalizeOn_of_mem (S.X i) (S.chi i) xp.2,
    SOptLib.totalizeOn_of_mem (S.X i) (S.chi i) z.2]
  rw [inner_sub_right, inner_sub_right] at h
  nlinarith

/-- Scaled variational inequality for the selected block prox point. -/
private theorem blockProxPoint_scaled_variational_inequality
    (S : Setup Ξ ι Block)
    (i : ι) (x : S.Carrier) (y : Block i) (γ : ℝ) (hγ : 0 < γ)
    (u : {z : Block i // z ∈ S.X i}) :
    let xblock : {z : Block i // z ∈ S.X i} := ⟨x.1 i, (Set.mem_univ_pi.mp x.2) i⟩
    let xp := S.blockProxPoint i x y γ hγ
    0 ≤
      γ * ⟪y, u.1 - xp.1⟫_ℝ +
        ⟪S.nuGrad i xp.1 - S.nuGrad i xblock.1, u.1 - xp.1⟫_ℝ +
        γ * (S.chi i u - S.chi i xp) := by
  classical
  let xblock : {z : Block i // z ∈ S.X i} := ⟨x.1 i, (Set.mem_univ_pi.mp x.2) i⟩
  let xp := S.blockProxPoint i x y γ hγ
  have hconv :
      ConvexOn ℝ (S.X i) (SOptLib.totalizeOn (S.X i) (S.chi i)) :=
    convexOn_totalize_of_isConvexBlockTerm (S.block_convex i) (S.chi_convex i)
  have hgrad_xp : HasGradientAt (S.nu i) (S.nuGrad i xp.1) xp.1 :=
    (S.nu_dgf i).2.1 xp.1 xp.2
  have hmin :
      IsMinOn
        (SOptLib.proxObjective
          (fun a b : {z : Block i // z ∈ S.X i} =>
            carrierBregmanFormula (S.nu i) id (S.nuGrad i) a.1 b.1)
          (fun z : {z : Block i // z ∈ S.X i} =>
            SOptLib.totalizeOn (S.X i) (S.chi i) z.1)
          (fun z : {z : Block i // z ∈ S.X i} => z.1)
          xblock y γ)
        Set.univ xp := by
    simpa [xblock, xp] using S.blockProxPoint_isSOptLibAmbientProx i x y γ hγ
  have hscaled :=
    composite_prox_scaled_variational_inequality_of_isMinOn
      (X := S.X i) (nu := S.nu i)
      (h := SOptLib.totalizeOn (S.X i) (S.chi i))
      (grad := S.nuGrad i)
      hconv xblock xp u y γ hγ hgrad_xp hmin
  simpa [xblock, xp, SOptLib.totalizeOn_of_mem (S.X i) (S.chi i) u.2,
    SOptLib.totalizeOn_of_mem (S.X i) (S.chi i) xp.2] using hscaled

/-- Setup-level block composite projected-gradient mapping from Eq. (6.3.8). -/
noncomputable def blockProjectedGradient (S : Setup Ξ ι Block)
    (i : ι) (x : S.Carrier) (y : Block i) (γ : ℝ) (_hγ : 0 < γ) : Block i :=
  γ⁻¹ • (x.1 i - (S.blockProxPoint i x y γ _hγ).1)

@[simp]
theorem blockProjectedGradient_eq (S : Setup Ξ ι Block)
    (i : ι) (x : S.Carrier) (y : Block i) (γ : ℝ) (hγ : 0 < γ) :
    S.blockProjectedGradient i x y γ hγ =
      γ⁻¹ • (x.1 i - (S.blockProxPoint i x y γ hγ).1) := by
  rfl

/-- The selected block projected-gradient inner product dominates its squared
norm plus the simple-term difference.  This is the local Lean form of
Lemma 6.7 / Eq. (6.3.15). -/
private theorem blockProjectedGradient_inner_ge_norm_sq_add_chi_diff
    (S : Setup Ξ ι Block)
    (i : ι) (x : S.Carrier) (y : Block i) (γ : ℝ) (hγ : 0 < γ) :
    let xblock : {z : Block i // z ∈ S.X i} := ⟨x.1 i, (Set.mem_univ_pi.mp x.2) i⟩
    let xp := S.blockProxPoint i x y γ hγ
    let pg := S.blockProjectedGradient i x y γ hγ
    ⟪y, pg⟫_ℝ ≥ ‖pg‖ ^ 2 + γ⁻¹ * (S.chi i xp - S.chi i xblock) := by
  classical
  let xblock : {z : Block i // z ∈ S.X i} := ⟨x.1 i, (Set.mem_univ_pi.mp x.2) i⟩
  let xp := S.blockProxPoint i x y γ hγ
  have hmin :
      IsMinOn
        (SOptLib.proxObjective
          (fun a b : {z : Block i // z ∈ S.X i} =>
            carrierBregmanFormula (S.nu i) id (S.nuGrad i) a.1 b.1)
          (fun z : {z : Block i // z ∈ S.X i} =>
            SOptLib.totalizeOn (S.X i) (S.chi i) z.1)
          (fun z : {z : Block i // z ∈ S.X i} => z.1)
          xblock y γ)
        Set.univ xp := by
    simpa [xblock, xp] using S.blockProxPoint_isSOptLibAmbientProx i x y γ hγ
  have hpg :=
    composite_prox_projectedGradient_inner_ge_norm_sq_add_hdiff_of_isMinOn
      (X := S.X i) (nu := S.nu i)
      (h := SOptLib.totalizeOn (S.X i) (S.chi i)) (grad := S.nuGrad i)
      (convexOn_totalize_of_isConvexBlockTerm (S.block_convex i) (S.chi_convex i))
      (S.nu_dgf i) xblock xp y γ hγ hmin
  simpa [SOptLib.projectedGradient, Setup.blockProjectedGradient, xblock, xp,
    SOptLib.totalizeOn_of_mem (S.X i) (S.chi i) xblock.2,
    SOptLib.totalizeOn_of_mem (S.X i) (S.chi i) xp.2] using hpg

/-- Same-state stochastic and exact block projected-gradient mappings differ by
at most the sampled-gradient residual.  This is the block specialization of
Lemma 6.7 / Eq. (6.3.16). -/
private theorem theorem69_block_projected_gradient_lipschitz_residual
    (S : Setup Ξ ι Block)
    (i : ι) (x : S.Carrier) (G : Block i) (γ : ℝ) (hγ : 0 < γ) :
    ‖S.blockProjectedGradient i x G γ hγ -
        S.blockProjectedGradient i x (S.grad x.1 i) γ hγ‖ ≤
      ‖G - S.grad x.1 i‖ := by
  classical
  let xblock : {z : Block i // z ∈ S.X i} := ⟨x.1 i, (Set.mem_univ_pi.mp x.2) i⟩
  let pExact := S.blockProxPoint i x (S.grad x.1 i) γ hγ
  let pStoch := S.blockProxPoint i x G γ hγ
  let eval : {z : Block i // z ∈ S.X i} → Block i := fun z => z.1
  let gradMap : {z : Block i // z ∈ S.X i} → Block i := fun z => S.nuGrad i z.1
  let hsimple : {z : Block i // z ∈ S.X i} → ℝ := S.chi i
  let gExact : Block i := S.grad x.1 i
  have hviExact :
      0 ≤
        ⟪gExact, eval pStoch - eval pExact⟫_ℝ +
          γ⁻¹ * ⟪gradMap pExact - gradMap xblock, eval pStoch - eval pExact⟫_ℝ +
          (hsimple pStoch - hsimple pExact) := by
    have hscaled :=
      S.blockProxPoint_scaled_variational_inequality i x gExact γ hγ pStoch
    let A : ℝ := ⟪gExact, eval pStoch - eval pExact⟫_ℝ
    let B : ℝ := ⟪gradMap pExact - gradMap xblock, eval pStoch - eval pExact⟫_ℝ
    let C : ℝ := hsimple pStoch - hsimple pExact
    have hscaledABC : 0 ≤ γ * A + B + γ * C := by
      simpa [A, B, C, xblock, pExact, pStoch, eval, gradMap, hsimple, gExact]
        using hscaled
    have hmul : 0 ≤ γ * (A + γ⁻¹ * B + C) := by
      convert hscaledABC using 1
      field_simp [hγ.ne']
    have hdiv := (mul_nonneg_iff_of_pos_left hγ).1 hmul
    simpa [A, B, C] using hdiv
  have hviStoch :
      0 ≤
        ⟪G, eval pExact - eval pStoch⟫_ℝ +
          γ⁻¹ * ⟪gradMap pStoch - gradMap xblock, eval pExact - eval pStoch⟫_ℝ +
          (hsimple pExact - hsimple pStoch) := by
    have hscaled :=
      S.blockProxPoint_scaled_variational_inequality i x G γ hγ pExact
    let A : ℝ := ⟪G, eval pExact - eval pStoch⟫_ℝ
    let B : ℝ := ⟪gradMap pStoch - gradMap xblock, eval pExact - eval pStoch⟫_ℝ
    let C : ℝ := hsimple pExact - hsimple pStoch
    have hscaledABC : 0 ≤ γ * A + B + γ * C := by
      simpa [A, B, C, xblock, pExact, pStoch, eval, gradMap, hsimple]
        using hscaled
    have hmul : 0 ≤ γ * (A + γ⁻¹ * B + C) := by
      convert hscaledABC using 1
      field_simp [hγ.ne']
    have hdiv := (mul_nonneg_iff_of_pos_left hγ).1 hmul
    simpa [A, B, C] using hdiv
  have hstrong :
      ‖eval pExact - eval pStoch‖ ^ 2 ≤
        ⟪eval pExact - eval pStoch, gradMap pExact - gradMap pStoch⟫_ℝ := by
    simpa [eval, gradMap, pExact, pStoch] using
      SOptLib.sq_norm_le_inner_gradient_sub_of_dgf_half_sq_bregman
        (S.nu_dgf i) pExact.2 pStoch.2
  have hprox :
      γ⁻¹ * ‖eval (pExact) - eval (pStoch)‖ ≤ ‖gExact - G‖ := by
    simpa [eval, gradMap, hsimple, xblock, pExact, pStoch, gExact] using
      prox_points_scaled_dist_le_oracle_dist_of_variational
        eval gradMap hsimple xblock pExact pStoch gExact G γ hγ
        hviExact hviStoch hstrong
  let prox : {z : Block i // z ∈ S.X i} → Block i → ℝ → {z : Block i // z ∈ S.X i} :=
    fun _ y _ => S.blockProxPoint i x y γ hγ
  let gradConst : {z : Block i // z ∈ S.X i} → Block i := fun _ => gExact
  have hdist :=
    exact_projectedGradient_dist_le_oracle_projectedGradient_dist_add_residual
      eval prox gradConst xblock G γ hγ (by
        simpa [eval, prox, gradConst, xblock, pExact, pStoch, gExact] using hprox)
  simpa [SOptLib.projectedGradient, Setup.blockProjectedGradient, eval, prox,
    gradConst, xblock, pExact, pStoch, gExact, norm_sub_rev] using hdist


/-- Literal printed selected-block update from Eq. (6.3.13).

The PDF prints the selected coordinate as the projected-gradient mapping value.
Because Eq. (6.3.8) defines that mapping as a scaled displacement, this raw
display is kept separate from the feasible prox-point update used by `step`.
-/
private noncomputable def printedStep (S : Setup Ξ ι Block) (k : ℕ) (hk : 1 ≤ k)
    (x : S.Carrier) (i : ι) (ξ : Ξ) :
    ∀ j, Block j :=
  replaceBlock i x.1
    (S.blockProjectedGradient i x (S.sampledGradient x ξ i) (S.γ k)
      (S.gamma_pos_obligation k hk))

@[simp]
private theorem printedStep_selected (S : Setup Ξ ι Block)
    (k : ℕ) (hk : 1 ≤ k) (x : S.Carrier) (i : ι) (ξ : Ξ) :
    S.printedStep k hk x i ξ i =
      S.blockProjectedGradient i x (S.sampledGradient x ξ i) (S.γ k)
        (S.gamma_pos_obligation k hk) := by
  simp [Setup.printedStep, replaceBlock]

@[simp]
private theorem printedStep_other (S : Setup Ξ ι Block)
    (k : ℕ) (hk : 1 ≤ k) (x : S.Carrier) {i j : ι} (ξ : Ξ) (hji : j ≠ i) :
    S.printedStep k hk x i ξ j = x.1 j := by
  simp [Setup.printedStep, replaceBlock, hji]

/-- One SBMD step generated by the sampled block, sample, and canonical prox update. -/
noncomputable def step (S : Setup Ξ ι Block) (k : ℕ) (hk : 1 ≤ k)
    (x : S.Carrier) (i : ι) (ξ : Ξ) :
    S.Carrier :=
  let hγ := S.gamma_pos_obligation k hk
  let xplus := S.blockProxPoint i x (S.sampledGradient x ξ i) (S.γ k) hγ
  ⟨replaceBlock i x.1 xplus.1, replaceBlock_mem_pi_univ S.X i x.1 xplus.1 x.2 xplus.2⟩

/-- Generated SBMD iterate sequence from Algorithm 6.1. -/
noncomputable def iterates (S : Setup Ξ ι Block) (blockSample : ℕ → ι) (sample : ℕ → Ξ) :
    ℕ → S.Carrier
  | 0 => S.x₁Carrier
  | k + 1 => S.step (k + 1) (Nat.succ_pos k) (S.iterates blockSample sample k)
      (blockSample (k + 1)) (sample (k + 1))

@[simp]
theorem iterates_zero (S : Setup Ξ ι Block) (blockSample : ℕ → ι) (sample : ℕ → Ξ) :
    S.iterates blockSample sample 0 = S.x₁Carrier := by
  rfl

@[simp]
theorem iterates_succ (S : Setup Ξ ι Block) (blockSample : ℕ → ι) (sample : ℕ → Ξ)
    (k : ℕ) :
    S.iterates blockSample sample (k + 1) =
      S.step (k + 1) (Nat.succ_pos k) (S.iterates blockSample sample k) (blockSample (k + 1))
        (sample (k + 1)) := by
  rfl

/-- Paper-time iterate `x_k`, with `x_1` equal to the initial feasible point.

The recursive process stores the initial point at raw index `0`; this wrapper is
the one-based object used in Algorithm 6.1 and Theorem 6.9.
-/
noncomputable def paperIterate (S : Setup Ξ ι Block)
    (blockSample : ℕ → ι) (sample : ℕ → Ξ) (k : ℕ) (_hk : 1 ≤ k) : S.Carrier :=
  S.iterates blockSample sample (k - 1)

@[simp]
theorem paperIterate_one (S : Setup Ξ ι Block) (blockSample : ℕ → ι) (sample : ℕ → Ξ)
    (h1 : 1 ≤ 1) :
    S.paperIterate blockSample sample 1 h1 = S.x₁Carrier := by
  rfl

/-- Updating a future block sample does not change a zero-based iterate before
that sample is read. -/
private theorem iterates_update_blockSample_eq_of_lt (S : Setup Ξ ι Block)
    (blockSample : ℕ → ι) (sample : ℕ → Ξ) (k : ℕ) (i : ι) :
    ∀ (m : ℕ), m < k →
      S.iterates (Function.update blockSample k i) sample m =
        S.iterates blockSample sample m
  | 0, _hm => rfl
  | m + 1, hm => by
      have hm_prev : m < k := Nat.lt_trans (Nat.lt_succ_self m) hm
      have hidx : m + 1 ≠ k := ne_of_lt hm
      simp [Setup.iterates_succ,
        iterates_update_blockSample_eq_of_lt S blockSample sample k i m hm_prev,
        Function.update_of_ne hidx]

/-- Updating a future oracle sample does not change a zero-based iterate before
that sample is read. -/
private theorem iterates_update_sample_eq_of_lt (S : Setup Ξ ι Block)
    (blockSample : ℕ → ι) (sample : ℕ → Ξ) (k : ℕ) (ξ : Ξ) :
    ∀ (m : ℕ), m < k →
      S.iterates blockSample (Function.update sample k ξ) m =
        S.iterates blockSample sample m
  | 0, _hm => rfl
  | m + 1, hm => by
      have hm_prev : m < k := Nat.lt_trans (Nat.lt_succ_self m) hm
      have hidx : m + 1 ≠ k := ne_of_lt hm
      simp [Setup.iterates_succ,
        iterates_update_sample_eq_of_lt S blockSample sample k ξ m hm_prev,
        Function.update_of_ne hidx]

/-- A zero-based iterate is determined by the block samples read up to that
time. -/
private theorem iterates_eq_of_blockSample_eq_on_prefix (S : Setup Ξ ι Block)
    (blockSample₁ blockSample₂ : ℕ → ι) (sample : ℕ → Ξ) :
    ∀ (m : ℕ),
      (∀ t, 1 ≤ t → t ≤ m → blockSample₁ t = blockSample₂ t) →
        S.iterates blockSample₁ sample m = S.iterates blockSample₂ sample m
  | 0, _hprefix => rfl
  | m + 1, hprefix => by
      have hprev :
          S.iterates blockSample₁ sample m = S.iterates blockSample₂ sample m :=
        iterates_eq_of_blockSample_eq_on_prefix S blockSample₁ blockSample₂ sample m
          (fun t ht_pos ht_le =>
            hprefix t ht_pos (Nat.le_trans ht_le (Nat.le_succ m)))
      have hcur : blockSample₁ (m + 1) = blockSample₂ (m + 1) :=
        hprefix (m + 1) (Nat.succ_pos m) le_rfl
      simp [Setup.iterates_succ, hprev, hcur]

/-- The paper-time iterate `x_k` is computed before the current block draw
`i_k`, so changing only that draw leaves `x_k` unchanged. -/
private theorem paperIterate_update_current_blockSample_eq (S : Setup Ξ ι Block)
    (blockSample : ℕ → ι) (sample : ℕ → Ξ)
    (k : ℕ) (hk : 1 ≤ k) (i : ι) :
    S.paperIterate (Function.update blockSample k i) sample k hk =
      S.paperIterate blockSample sample k hk := by
  unfold paperIterate
  exact S.iterates_update_blockSample_eq_of_lt blockSample sample k i (k - 1)
    (Nat.sub_lt (Nat.lt_of_lt_of_le Nat.zero_lt_one hk) Nat.zero_lt_one)

/-- The paper-time iterate `x_k` is computed before the current oracle draw
`ξ_k`, so changing only that draw leaves `x_k` unchanged. -/
private theorem paperIterate_update_current_sample_eq (S : Setup Ξ ι Block)
    (blockSample : ℕ → ι) (sample : ℕ → Ξ)
    (k : ℕ) (hk : 1 ≤ k) (ξ : Ξ) :
    S.paperIterate blockSample (Function.update sample k ξ) k hk =
      S.paperIterate blockSample sample k hk := by
  unfold paperIterate
  exact S.iterates_update_sample_eq_of_lt blockSample sample k ξ (k - 1)
    (Nat.sub_lt (Nat.lt_of_lt_of_le Nat.zero_lt_one hk) Nat.zero_lt_one)

/-- One-based paper iterates advance by the current sampled block/oracle step. -/
private theorem paperIterate_succ_eq_step_current (S : Setup Ξ ι Block)
    (blockSample : ℕ → ι) (sample : ℕ → Ξ) (k : ℕ) (hk : 1 ≤ k) :
    S.paperIterate blockSample sample (k + 1)
        (Nat.succ_le_succ (Nat.zero_le k)) =
      S.step k hk (S.paperIterate blockSample sample k hk)
        (blockSample k) (sample k) := by
  cases k with
  | zero =>
      exact False.elim (Nat.not_succ_le_zero 0 hk)
  | succ m =>
      simp [Setup.paperIterate, Setup.iterates_succ]

/-- Fresh sampled block-gradient process at a generated history, before the
current oracle sample `ξ_k` is integrated out.

Book JSON: `algorithm_spec/steps/1-2` states that `i_k` is sampled with law
`p_i` and then the `i_k`-th block stochastic gradient is computed at `x_k`
satisfying Eq. (6.3.12).
-/
noncomputable def stochasticBlockGradientAtHistory (S : Setup Ξ ι Block)
    (k : ℕ) (hk : 1 ≤ k) (blockSample : ℕ → ι) (sample : ℕ → Ξ)
    (ξ : Ξ) : Block (blockSample k) :=
  S.G (S.paperIterate blockSample sample k hk).1 ξ (blockSample k)

/-- Exact queried block gradient `U_{i_k}ᵀ∇f(x_k)` in the same history/process
coordinates as `stochasticBlockGradientAtHistory`. -/
noncomputable def exactBlockGradientAtHistory (S : Setup Ξ ι Block)
    (k : ℕ) (hk : 1 ≤ k) (blockSample : ℕ → ι) (sample : ℕ → Ξ) :
    Block (blockSample k) :=
  S.grad (S.paperIterate blockSample sample k hk).1 (blockSample k)

/-- Source gradient symbol `U_{i_k}ᵀ g(x_k)` from Eq. (6.3.12).

The proof of Theorem 6.9 later rewrites the residual around
`U_{i_k}ᵀ∇f(x_k)`.  This named object keeps the source `g(x_k)` center visible
in the stochastic-gradient assumption before that proof-side bridge is invoked.
-/
noncomputable def sourceBlockGradientAtHistory (S : Setup Ξ ι Block)
    (k : ℕ) (hk : 1 ≤ k) (blockSample : ℕ → ι) (sample : ℕ → Ξ) :
    Block (blockSample k) :=
  S.sourceGradient (S.paperIterate blockSample sample k hk).1 (blockSample k)

@[simp]
theorem sourceBlockGradientAtHistory_eq_sourceGradient (S : Setup Ξ ι Block)
    (k : ℕ) (hk : 1 ≤ k) (blockSample : ℕ → ι) (sample : ℕ → Ξ) :
    S.sourceBlockGradientAtHistory k hk blockSample sample =
      S.sourceGradient (S.paperIterate blockSample sample k hk).1 (blockSample k) := by
  rfl

/-- Residual `δ_k = G_{i_k}-U_{i_k}ᵀ∇f(x_k)` from Theorem 6.9, expressed as a
generated-process object rather than a theorem-local abbreviation. -/
noncomputable def stochasticGradientResidualAtHistory (S : Setup Ξ ι Block)
    (k : ℕ) (hk : 1 ≤ k) (blockSample : ℕ → ι) (sample : ℕ → Ξ)
    (ξ : Ξ) : Block (blockSample k) :=
  S.stochasticBlockGradientAtHistory k hk blockSample sample ξ -
    S.exactBlockGradientAtHistory k hk blockSample sample

@[simp]
theorem stochasticGradientResidualAtHistory_eq (S : Setup Ξ ι Block)
    (k : ℕ) (hk : 1 ≤ k) (blockSample : ℕ → ι) (sample : ℕ → Ξ)
    (ξ : Ξ) :
    S.stochasticGradientResidualAtHistory k hk blockSample sample ξ =
      S.G (S.paperIterate blockSample sample k hk).1 ξ (blockSample k) -
        S.grad (S.paperIterate blockSample sample k hk).1 (blockSample k) := by
  rfl

/-- Source-centered residual `G_{i_k}-U_{i_k}ᵀg(x_k)` from Eq. (6.3.12). -/
noncomputable def stochasticGradientSourceResidualAtHistory (S : Setup Ξ ι Block)
    (k : ℕ) (hk : 1 ≤ k) (blockSample : ℕ → ι) (sample : ℕ → Ξ)
    (ξ : Ξ) : Block (blockSample k) :=
  S.stochasticBlockGradientAtHistory k hk blockSample sample ξ -
    S.sourceBlockGradientAtHistory k hk blockSample sample

/-- Vector expectation clause from Algorithm 6.1 step 2 / Eq. (6.3.12).

This uses `SOptLib.expectationEq`, so the source notation `E[G_{i_k}] = ...`
is represented by a nonfallback Bochner expectation, not by Lean's totalized
integral value outside its domain.
-/
def StochasticGradientMeanConditionAtHistory (S : Setup Ξ ι Block)
    (k : ℕ) (hk : 1 ≤ k) (blockSample : ℕ → ι) (sample : ℕ → Ξ) : Prop :=
  SOptLib.expectationEq S.sampleLaw
    (fun ξ => S.stochasticBlockGradientAtHistory k hk blockSample sample ξ)
    (S.sourceBlockGradientAtHistory k hk blockSample sample)

/-- Second-moment clause from Algorithm 6.1 step 2 / Eq. (6.3.12).

This uses `SOptLib.expectationLe`, pairing integrability with the displayed
expectation bound so the theorem layer cannot rely on a totalized integral
fallback.
-/
def StochasticGradientSecondMomentConditionAtHistory (S : Setup Ξ ι Block)
    (k : ℕ) (hk : 1 ≤ k) (blockSample : ℕ → ι) (sample : ℕ → Ξ) : Prop :=
  SOptLib.expectationLe S.sampleLaw
    (fun ξ => ‖S.stochasticGradientSourceResidualAtHistory k hk blockSample sample ξ‖ ^ 2)
    (S.sigmaBar k ^ 2)

/-- Scalar residual-centering consequence used by the proof of Theorem 6.9.

The PDF states the vector expectation clause in Eq. (6.3.12) and later centers
`δ_k = G_{i_k}-U_{i_k}ᵀ∇f(x_k)` in the proof.  Turning the vector expectation
into this scalar residual integral is a Lean proof obligation, not part of the
primitive source contract.
-/
def StochasticGradientResidualScalarMeanConditionAtHistory (S : Setup Ξ ι Block)
    (k : ℕ) (hk : 1 ≤ k) (blockSample : ℕ → ι) (sample : ℕ → Ξ) : Prop :=
  ∀ v : Block (blockSample k),
    SOptLib.expectationEq S.sampleLaw
      (fun ξ => ⟪S.stochasticGradientResidualAtHistory k hk blockSample sample ξ, v⟫_ℝ)
      0

/-- Exact-gradient residual-square condition used in the proof of Theorem 6.9.

Eq. (6.3.12) bounds the source-centered residual around `g(x_k)`.  The proof
uses `δ_k = G_{i_k}-U_{i_k}ᵀ∇f(x_k)`, so this is a proof-side condition that must
come through the residual-centering source boundary, not directly from the
source stochastic-gradient condition.
-/
def ExactGradientResidualSecondMomentConditionAtHistory (S : Setup Ξ ι Block)
    (k : ℕ) (hk : 1 ≤ k) (blockSample : ℕ → ι) (sample : ℕ → Ξ) : Prop :=
  SOptLib.expectationLe S.sampleLaw
    (fun ξ => ‖S.stochasticGradientResidualAtHistory k hk blockSample sample ξ‖ ^ 2)
    (S.sigmaBar k ^ 2)

/-- Fixed-history residual cancellation and variance budget used in Theorem 6.9.

This is the nonfallback expectation content of proof steps 16-19: after the
source-boundary bridge has centered the residual at the exact gradient, the
fresh oracle sample contributes no scalar cross term and its squared residual is
bounded by `sigmaBar k ^ 2`. -/
private theorem theorem69_fixed_history_residual_expectation
    (S : Setup Ξ ι Block)
    (hResidualMean :
      ∀ (k : ℕ) (hk : 1 ≤ k) (blockSample : ℕ → ι) (sample : ℕ → Ξ),
        S.StochasticGradientResidualScalarMeanConditionAtHistory
          k hk blockSample sample)
    (hResidualSecond :
      ∀ (k : ℕ) (hk : 1 ≤ k) (blockSample : ℕ → ι) (sample : ℕ → Ξ),
        S.ExactGradientResidualSecondMomentConditionAtHistory
          k hk blockSample sample)
    (k : ℕ) (hk : 1 ≤ k) (blockSample : ℕ → ι) (sample : ℕ → Ξ)
    (v : Block (blockSample k)) :
    Integrable
        (fun ξ =>
          ⟪S.stochasticGradientResidualAtHistory k hk blockSample sample ξ, v⟫_ℝ)
        S.sampleLaw ∧
      (∫ ξ,
          ⟪S.stochasticGradientResidualAtHistory k hk blockSample sample ξ, v⟫_ℝ
        ∂S.sampleLaw) = 0 ∧
      Integrable
        (fun ξ =>
          ‖S.stochasticGradientResidualAtHistory k hk blockSample sample ξ‖ ^ 2)
        S.sampleLaw ∧
      (∫ ξ,
          ‖S.stochasticGradientResidualAtHistory k hk blockSample sample ξ‖ ^ 2
        ∂S.sampleLaw) ≤ S.sigmaBar k ^ 2 := by
  have hMean :=
    hResidualMean k hk blockSample sample v
  have hSecond :=
    hResidualSecond k hk blockSample sample
  rcases (SOptLib.expectationLe_def S.sampleLaw
      (fun ξ =>
        ‖S.stochasticGradientResidualAtHistory k hk blockSample sample ξ‖ ^ 2)
      (S.sigmaBar k ^ 2)).1 hSecond with ⟨hSecond_int, hSecond_le⟩
  exact ⟨SOptLib.expectationEq.integrable hMean,
    SOptLib.expectationEq.integral_eq hMean, hSecond_int, hSecond_le⟩

/-- Fixed-history residual budget after multiplying by the current stepsize.

This is the exact scalar noise term that remains after applying the pathwise
one-step descent and integrating only the fresh oracle sample. -/
private theorem theorem69_fixed_history_residual_budget_integral
    (S : Setup Ξ ι Block)
    (hResidualMean :
      ∀ (k : ℕ) (hk : 1 ≤ k) (blockSample : ℕ → ι) (sample : ℕ → Ξ),
        S.StochasticGradientResidualScalarMeanConditionAtHistory
          k hk blockSample sample)
    (hResidualSecond :
      ∀ (k : ℕ) (hk : 1 ≤ k) (blockSample : ℕ → ι) (sample : ℕ → Ξ),
        S.ExactGradientResidualSecondMomentConditionAtHistory
          k hk blockSample sample)
    (k : ℕ) (hk : 1 ≤ k) (blockSample : ℕ → ι) (sample : ℕ → Ξ)
    (v : Block (blockSample k)) :
    Integrable
        (fun ξ =>
          S.γ k *
              ⟪S.stochasticGradientResidualAtHistory k hk blockSample sample ξ, v⟫_ℝ +
            2 * S.γ k *
              ‖S.stochasticGradientResidualAtHistory k hk blockSample sample ξ‖ ^ 2)
        S.sampleLaw ∧
      (∫ ξ,
          S.γ k *
              ⟪S.stochasticGradientResidualAtHistory k hk blockSample sample ξ, v⟫_ℝ +
            2 * S.γ k *
              ‖S.stochasticGradientResidualAtHistory k hk blockSample sample ξ‖ ^ 2
        ∂S.sampleLaw) ≤ 2 * S.γ k * S.sigmaBar k ^ 2 := by
  rcases theorem69_fixed_history_residual_expectation
      S hResidualMean hResidualSecond k hk blockSample sample v with
    ⟨hcross_int, hcross_zero, hsq_int, hsq_le⟩
  have hγ_nonneg : 0 ≤ S.γ k := le_of_lt (S.γ_pos k hk)
  have hbudget_int :
      Integrable
        (fun ξ =>
          S.γ k *
              ⟪S.stochasticGradientResidualAtHistory k hk blockSample sample ξ, v⟫_ℝ +
            2 * S.γ k *
              ‖S.stochasticGradientResidualAtHistory k hk blockSample sample ξ‖ ^ 2)
        S.sampleLaw :=
    (hcross_int.const_mul (S.γ k)).add (hsq_int.const_mul (2 * S.γ k))
  refine ⟨hbudget_int, ?_⟩
  rw [integral_add (hcross_int.const_mul (S.γ k)) (hsq_int.const_mul (2 * S.γ k))]
  rw [integral_const_mul, integral_const_mul, hcross_zero]
  have hsq_scaled :
      2 * S.γ k *
          (∫ ξ,
            ‖S.stochasticGradientResidualAtHistory k hk blockSample sample ξ‖ ^ 2
          ∂S.sampleLaw) ≤
        2 * S.γ k * S.sigmaBar k ^ 2 :=
    mul_le_mul_of_nonneg_left hsq_le (by nlinarith)
  nlinarith

/-- Residual algebra converting a stochastic block descent into exact-block form.

The hypotheses isolate the part of Theorem 6.9 proof steps 9-12 that is pure
Hilbert-space algebra: a stochastic projected-gradient descent, a Lipschitz
comparison between stochastic and exact projected gradients, and the nonnegative
stepsize factor imply the exact projected-gradient bound with the centered
residual cross term and two residual-square budget. -/
private theorem theorem69_residualized_exact_block_from_stochastic_descent
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (γ L D : ℝ) (spg epg δ : E)
    (hγ : 0 ≤ γ)
    (hfactor_nonneg : 0 ≤ 1 - L / 2 * γ)
    (hfactor_le_one : 1 - L / 2 * γ ≤ 1)
    (hdesc :
      γ * (1 - L / 2 * γ) * ‖spg‖ ^ 2 ≤
        D + γ * ⟪δ, spg⟫_ℝ)
    (hlip : ‖spg - epg‖ ≤ ‖δ‖) :
    (γ / 2) * (1 - L / 2 * γ) * ‖epg‖ ^ 2 ≤
      D + γ * ⟪δ, epg⟫_ℝ + 2 * γ * ‖δ‖ ^ 2 := by
  exact _root_.half_weight_norm_sq_le_of_weight_norm_sq_le_add_inner_of_norm_sub_le
    γ (1 - L / 2 * γ) D spg epg δ hγ hfactor_nonneg hfactor_le_one hdesc hlip

/-- Source condition Eq. (6.3.12), stated on the generated stochastic-gradient
process with fixed-history/nonfallback expectation semantics.

Book JSON: `#/assumptions/13` quotes
`E[G_{i_k}]=U_{i_k}^T g(x_k)` and
`E[||G_{i_k}-U_{i_k}^T g(x_k)||^2] <= \bar\sigma_k^2`.  Each history is fixed
and the fresh oracle sample is integrated against `S.sampleLaw`, modeling the
conditional-on-the-past reading used later in the proof without exposing Lean's
totalized integral fallback as the paper meaning.
-/
def StochasticGradientCondition (S : Setup Ξ ι Block) : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (blockSample : ℕ → ι) (sample : ℕ → Ξ),
    S.StochasticGradientMeanConditionAtHistory k hk blockSample sample ∧
      S.StochasticGradientSecondMomentConditionAtHistory k hk blockSample sample

/-- Eq. (6.3.12) mean condition projected from the source process condition. -/
theorem sampledGradient_unbiased_at_iterate_of_source_condition (S : Setup Ξ ι Block)
    (hG : S.StochasticGradientCondition)
    (k : ℕ) (hk : 1 ≤ k) (blockSample : ℕ → ι) (sample : ℕ → Ξ) :
    S.StochasticGradientMeanConditionAtHistory k hk blockSample sample := by
  exact (hG k hk blockSample sample).1

/-- Eq. (6.3.12) second-moment budget projected from the source process
condition. -/
theorem sampledGradient_variance_at_iterate_of_source_condition (S : Setup Ξ ι Block)
    (hG : S.StochasticGradientCondition)
    (k : ℕ) (hk : 1 ≤ k) (blockSample : ℕ → ι) (sample : ℕ → Ξ) :
    S.StochasticGradientSecondMomentConditionAtHistory k hk blockSample sample := by
  exact (hG k hk blockSample sample).2

/-- Source-boundary record for the update/prox-point mismatch in Theorem 6.9.

Eq. (6.3.13) prints the selected coordinate as the projected-gradient mapping
`P_{X_i}`, while the proof immediately uses the prox-point displacement identity
`x_{k+1}-x_k=-γ_k U_{i_k}\tilde g_k`.  The generated Lean algorithm uses the
prox-point update; this predicate names the proof-side displacement boundary
instead of treating the literal printed `printedStep` display as definitionally
identical to the proof update.
-/
def theorem69UpdateProxSourceBoundary (S : Setup Ξ ι Block) : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (x : S.Carrier) (i : ι) (ξ : Ξ),
    (S.step k hk x i ξ).1 i =
      x.1 i - S.γ k •
        S.blockProjectedGradient i x (S.sampledGradient x ξ i) (S.γ k)
          (S.gamma_pos_obligation k hk)

/-- Source-boundary record for the `g(x_k)` versus `∇f(x_k)` centering bridge.

Eq. (6.3.12) states the vector expectation for `G_{i_k}` centered at the paper
gradient notation `g(x_k)`.  The proof of Theorem 6.9 then centers
`δ_k = G_{i_k}-U_{i_k}ᵀ∇f(x_k)` inside scalar conditional expectations.  This
predicate is the corrected-boundary record for that source gap.  There is no
unconditional theorem identifying the source mean-gradient object with the exact
Mathlib gradient; downstream proofs must pass through this explicit boundary
and therefore cannot treat Eq. (6.3.12) as an exact-gradient residual condition.
-/
def theorem69ResidualCenteringSourceBoundary (S : Setup Ξ ι Block) : Prop :=
  ∀ (k : ℕ) (hk : 1 ≤ k) (blockSample : ℕ → ι) (sample : ℕ → Ξ),
    S.StochasticGradientMeanConditionAtHistory k hk blockSample sample →
      S.StochasticGradientSecondMomentConditionAtHistory k hk blockSample sample →
        S.StochasticGradientResidualScalarMeanConditionAtHistory k hk blockSample sample ∧
          S.ExactGradientResidualSecondMomentConditionAtHistory k hk blockSample sample

/-- Residual scalar-centering bridge from the source condition plus the explicit
Theorem 6.9 g-to-∇f boundary. -/
theorem residual_scalar_mean_at_iterate_of_source_condition (S : Setup Ξ ι Block)
    (hG : S.StochasticGradientCondition)
    (hBoundary : S.theorem69ResidualCenteringSourceBoundary)
    (k : ℕ) (hk : 1 ≤ k) (blockSample : ℕ → ι) (sample : ℕ → Ξ) :
    S.StochasticGradientResidualScalarMeanConditionAtHistory k hk blockSample sample := by
  exact (hBoundary k hk blockSample sample (hG k hk blockSample sample).1
    (hG k hk blockSample sample).2).1

/-- Exact-gradient residual-square bridge from the source condition plus the
explicit Theorem 6.9 g-to-∇f boundary. -/
theorem exact_gradient_residual_second_moment_at_iterate_of_source_condition
    (S : Setup Ξ ι Block)
    (hG : S.StochasticGradientCondition)
    (hBoundary : S.theorem69ResidualCenteringSourceBoundary)
    (k : ℕ) (hk : 1 ≤ k) (blockSample : ℕ → ι) (sample : ℕ → Ξ) :
    S.ExactGradientResidualSecondMomentConditionAtHistory k hk blockSample sample := by
  exact (hBoundary k hk blockSample sample (hG k hk blockSample sample).1
    (hG k hk blockSample sample).2).2

/-- At a fixed generated history, source mean centering and exact-gradient
scalar residual centering identify the selected source block gradient with the
selected exact block gradient. -/
private theorem sourceBlockGradientAtHistory_eq_exactBlockGradientAtHistory
    (S : Setup Ξ ι Block)
    (hG : S.StochasticGradientCondition)
    (hResidualMean :
      ∀ (k : ℕ) (hk : 1 ≤ k) (blockSample : ℕ → ι) (sample : ℕ → Ξ),
        S.StochasticGradientResidualScalarMeanConditionAtHistory
          k hk blockSample sample)
    (k : ℕ) (hk : 1 ≤ k) (blockSample : ℕ → ι) (sample : ℕ → Ξ) :
    S.sourceBlockGradientAtHistory k hk blockSample sample =
      S.exactBlockGradientAtHistory k hk blockSample sample := by
  classical
  let F : Ξ → Block (blockSample k) :=
    fun ξ => S.stochasticBlockGradientAtHistory k hk blockSample sample ξ
  let source : Block (blockSample k) :=
    S.sourceBlockGradientAtHistory k hk blockSample sample
  let exact : Block (blockSample k) :=
    S.exactBlockGradientAtHistory k hk blockSample sample
  haveI : IsProbabilityMeasure S.sampleLaw := S.sampleLaw_prob
  have hMean : SOptLib.expectationEq S.sampleLaw F source := by
    simpa [F, source, StochasticGradientMeanConditionAtHistory] using
      (hG k hk blockSample sample).1
  have hF_int : Integrable F S.sampleLaw :=
    SOptLib.expectationEq.integrable hMean
  have hF_integral : (∫ ξ, F ξ ∂S.sampleLaw) = source :=
    SOptLib.expectationEq.integral_eq hMean
  have hResidualCentered :
      SOptLib.expectationEq S.sampleLaw
        (fun ξ => ⟪F ξ - exact, source - exact⟫_ℝ) 0 := by
    simpa [F, source, exact, StochasticGradientResidualScalarMeanConditionAtHistory,
      stochasticGradientResidualAtHistory, exactBlockGradientAtHistory] using
        hResidualMean k hk blockSample sample (source - exact)
  have hResidualIntegral :
      (∫ ξ, ⟪F ξ - exact, source - exact⟫_ℝ ∂S.sampleLaw) = 0 :=
    SOptLib.expectationEq.integral_eq hResidualCentered
  have hdev_int : Integrable (fun ξ => F ξ - exact) S.sampleLaw :=
    hF_int.sub (integrable_const (c := exact))
  have hdev_integral :
      (∫ ξ, F ξ - exact ∂S.sampleLaw) = source - exact := by
    rw [integral_sub hF_int (integrable_const (c := exact)), hF_integral]
    simp
  have hscalar_integral :
      (∫ ξ, ⟪F ξ - exact, source - exact⟫_ℝ ∂S.sampleLaw) =
        ⟪source - exact, source - exact⟫_ℝ := by
    have hlin :=
      ContinuousLinearMap.integral_comp_comm
        (L := innerSLFlip ℝ (source - exact)) hdev_int
    calc
      (∫ ξ, ⟪F ξ - exact, source - exact⟫_ℝ ∂S.sampleLaw) =
          ∫ ξ, (innerSLFlip ℝ (source - exact)) (F ξ - exact) ∂S.sampleLaw := by
            rfl
      _ = (innerSLFlip ℝ (source - exact)) (∫ ξ, F ξ - exact ∂S.sampleLaw) := hlin
      _ = ⟪source - exact, source - exact⟫_ℝ := by
            rw [hdev_integral]
            rfl
  have hinner_zero : ⟪source - exact, source - exact⟫_ℝ = 0 :=
    hscalar_integral.symm.trans hResidualIntegral
  have hnorm_sq_zero : ‖source - exact‖ ^ 2 = 0 := by
    simpa [inner_self_eq_norm_sq] using hinner_zero
  have hnorm_zero : ‖source - exact‖ = 0 := by
    nlinarith [norm_nonneg (source - exact), hnorm_sq_zero]
  have hsub_zero : source - exact = 0 := norm_eq_zero.mp hnorm_zero
  have hsource_exact : source = exact := sub_eq_zero.mp hsub_zero
  simpa [source, exact] using hsource_exact

/-- At a generated paper-time iterate, the source mean-gradient vector agrees
coordinatewise with the exact gradient.  The proof updates the current block
draw to the queried coordinate; `x_k` is unchanged because it only depends on
strictly earlier draws. -/
private theorem sourceGradient_paperIterate_eq_grad
    (S : Setup Ξ ι Block)
    (hG : S.StochasticGradientCondition)
    (hResidualMean :
      ∀ (k : ℕ) (hk : 1 ≤ k) (blockSample : ℕ → ι) (sample : ℕ → Ξ),
        S.StochasticGradientResidualScalarMeanConditionAtHistory
          k hk blockSample sample)
    (k : ℕ) (hk : 1 ≤ k) (blockSample : ℕ → ι) (sample : ℕ → Ξ) :
    S.sourceGradient (S.paperIterate blockSample sample k hk).1 =
      S.grad (S.paperIterate blockSample sample k hk).1 := by
  classical
  ext i
  let blockSample' : ℕ → ι := fun t => if t = k then i else blockSample t
  have hpaper :
      S.paperIterate blockSample' sample k hk =
        S.paperIterate blockSample sample k hk :=
    by
      unfold paperIterate
      refine S.iterates_eq_of_blockSample_eq_on_prefix blockSample' blockSample sample
        (k - 1) ?_
      intro t ht_pos ht_le
      have htk : t ≠ k := by
        intro h
        have hk_pos : 0 < k := by
          simpa [h] using ht_pos
        have hlt : k - 1 < k := Nat.sub_lt hk_pos Nat.zero_lt_one
        exact (not_le_of_gt hlt) (by simpa [h] using ht_le)
      simp [blockSample', htk]
  have hselected :=
    sourceBlockGradientAtHistory_eq_exactBlockGradientAtHistory
      S hG hResidualMean k hk blockSample' sample
  have hsel' :
      S.sourceGradient (S.paperIterate blockSample sample k hk).1 (blockSample' k) =
        S.grad (S.paperIterate blockSample sample k hk).1 (blockSample' k) := by
    simpa [sourceBlockGradientAtHistory, exactBlockGradientAtHistory, hpaper]
      using hselected
  have hbk : blockSample' k = i := by
    simp [blockSample']
  exact hbk ▸ hsel'

/-- Selected-coordinate equation for the generated one-step update. -/
theorem step_selected (S : Setup Ξ ι Block)
    (k : ℕ) (hk : 1 ≤ k) (x : S.Carrier) (i : ι) (ξ : Ξ) :
    (S.step k hk x i ξ).1 i =
      (S.blockProxPoint i x (S.sampledGradient x ξ i) (S.γ k) (S.gamma_pos_obligation k hk)).1 := by
  simp [Setup.step, replaceBlock]

/-- Selected-coordinate displacement identity derived from the generated step
and the projected-gradient definition. -/
theorem step_selected_displacement (S : Setup Ξ ι Block)
    (k : ℕ) (hk : 1 ≤ k) (x : S.Carrier) (i : ι) (ξ : Ξ) :
    (S.step k hk x i ξ).1 i =
      x.1 i - S.γ k •
        S.blockProjectedGradient i x (S.sampledGradient x ξ i) (S.γ k)
          (S.gamma_pos_obligation k hk) := by
  let γ : ℝ := S.γ k
  let hγ : 0 < γ := S.gamma_pos_obligation k hk
  let y : Block i := S.sampledGradient x ξ i
  let xp : {z : Block i // z ∈ S.X i} := S.blockProxPoint i x y γ hγ
  let pg : Block i := S.blockProjectedGradient i x y γ hγ
  have hγpg : γ • pg = x.1 i - xp.1 := by
    simp [pg, xp, γ, hγ.ne', smul_smul]
  calc
    (S.step k hk x i ξ).1 i = xp.1 := by
      simpa [xp, y, γ, hγ] using S.step_selected k hk x i ξ
    _ = x.1 i - γ • pg := by
      rw [hγpg]
      abel

/-- Non-selected coordinates are unchanged by the generated one-step update. -/
theorem step_other (S : Setup Ξ ι Block)
    (k : ℕ) (hk : 1 ≤ k) (x : S.Carrier) {i j : ι} (ξ : Ξ) (hji : j ≠ i) :
    (S.step k hk x i ξ).1 j = x.1 j := by
  simp [Setup.step, replaceBlock, hji]

/-! ## Randomized output and Theorem 6.9 boundary -/

/-- Composite objective `φ(x)=f(x)+∑ᵢχᵢ(xᵢ)` from Eq. (6.3.1) and Eq. (6.3.4). -/
noncomputable def compositeObjective (S : Setup Ξ ι Block) (x : S.Carrier) : ℝ :=
  S.f x.1 + ∑ i, S.chi i ⟨x.1 i, (Set.mem_univ_pi.mp x.2) i⟩

/-- Pathwise selected-block stochastic descent, Eq. (6.3.21), in the concrete
`Setup.step` model. -/
private theorem theorem69_selected_block_pathwise_stochastic_descent
    (S : Setup Ξ ι Block)
    (k : ℕ) (hk : 1 ≤ k) (x : S.Carrier) (i : ι) (ξ : Ξ) :
    let hγ := S.gamma_pos_obligation k hk
    let spg := S.blockProjectedGradient i x (S.sampledGradient x ξ i) (S.γ k) hγ
    let δ := S.sampledGradient x ξ i - S.grad x.1 i
    S.γ k * (1 - S.L i / 2 * S.γ k) * ‖spg‖ ^ 2 ≤
      S.compositeObjective x - S.compositeObjective (S.step k hk x i ξ) +
        S.γ k * ⟪δ, spg⟫_ℝ := by
  classical
  let γ : ℝ := S.γ k
  let hγ : 0 < γ := S.gamma_pos_obligation k hk
  let y : Block i := S.sampledGradient x ξ i
  let spg : Block i := S.blockProjectedGradient i x y γ hγ
  let δ : Block i := y - S.grad x.1 i
  let xnext : S.Carrier := S.step k hk x i ξ
  have hxnext_replace :
      xnext.1 = replaceBlock i x.1 (x.1 i + (-γ) • spg) := by
    ext j
    by_cases hji : j = i
    · subst j
      have hsel := S.step_selected_displacement k hk x i ξ
      have hsel' : xnext.1 i = x.1 i - γ • spg := by
        simpa only [xnext, γ, hγ, y, spg] using hsel
      rw [hsel']
      simp [replaceBlock, sub_eq_add_neg]
    · have hother := S.step_other k hk x (i := i) (j := j) ξ hji
      simpa [xnext, replaceBlock, hji] using hother
  have hsmooth :
      S.f xnext.1 ≤
        S.f x.1 - γ * ⟪S.grad x.1 i, spg⟫_ℝ +
          (S.L i / 2) * γ ^ 2 * ‖spg‖ ^ 2 := by
    have hf_model :=
      S.block_descent_model x.1 x.2 i ((-γ) • spg)
    rw [hxnext_replace]
    have hinner :
        ⟪S.grad x.1 i, (-γ) • spg⟫_ℝ =
          -γ * ⟪S.grad x.1 i, spg⟫_ℝ := by
      simp [inner_smul_right]
    have hnorm :
        ‖(-γ) • spg‖ ^ 2 = γ ^ 2 * ‖spg‖ ^ 2 := by
      rw [norm_smul]
      have hnorm_neg : ‖(-γ : ℝ)‖ = γ := by
        rw [Real.norm_of_nonpos (neg_nonpos.mpr hγ.le)]
        ring
      rw [hnorm_neg]
      ring
    rw [hinner, hnorm] at hf_model
    nlinarith [hf_model]
  dsimp only
  simpa [Setup.compositeObjective, γ, hγ, y, spg, δ, xnext] using
    SOptLib.selected_block_composite_pathwise_descent_of_update_prox
      (smoothPart := fun z : S.Carrier => S.f z.1)
      (simple := fun j z => S.chi j ⟨z.1 j, (Set.mem_univ_pi.mp z.2) j⟩)
      (x := x) (xNext := xnext) (i := i) (gamma := γ) (L := S.L i)
      (gradBlock := S.grad x.1 i) (y := y) (spg := spg) (delta := δ)
      hγ hsmooth
      (by
        intro j hji
        have hcoord := S.step_other k hk x (i := i) (j := j) ξ hji
        exact congrArg (S.chi j) (Subtype.ext hcoord))
      (by
        let xblock : {z : Block i // z ∈ S.X i} :=
          ⟨x.1 i, (Set.mem_univ_pi.mp x.2) i⟩
        let xp : {z : Block i // z ∈ S.X i} := S.blockProxPoint i x y γ hγ
        have hxnext_selected :
            (⟨xnext.1 i, (Set.mem_univ_pi.mp xnext.2) i⟩ :
                {z : Block i // z ∈ S.X i}) = xp := by
          apply Subtype.ext
          simpa [xnext, xp, y, γ, hγ] using S.step_selected k hk x i ξ
        have hpg_raw :=
          blockProjectedGradient_inner_ge_norm_sq_add_chi_diff S i x y γ hγ
        simpa [xblock, xp, spg, y, hxnext_selected] using hpg_raw)
      (by rfl)

/-- Pathwise exact-block descent after residualizing the selected stochastic
projected-gradient step. -/
private theorem theorem69_selected_block_pathwise_exact_descent
    (S : Setup Ξ ι Block)
    (k : ℕ) (hk : 1 ≤ k) (x : S.Carrier) (i : ι) (ξ : Ξ) :
    let hγ := S.gamma_pos_obligation k hk
    let spg := S.blockProjectedGradient i x (S.sampledGradient x ξ i) (S.γ k) hγ
    let epg := S.blockProjectedGradient i x (S.grad x.1 i) (S.γ k) hγ
    let δ := S.sampledGradient x ξ i - S.grad x.1 i
    (S.γ k / 2) * (1 - S.L i / 2 * S.γ k) * ‖epg‖ ^ 2 ≤
      S.compositeObjective x - S.compositeObjective (S.step k hk x i ξ) +
        S.γ k * ⟪δ, epg⟫_ℝ + 2 * S.γ k * ‖δ‖ ^ 2 := by
  classical
  let γ : ℝ := S.γ k
  let hγ : 0 < γ := S.gamma_pos_obligation k hk
  let y : Block i := S.sampledGradient x ξ i
  let spg : Block i := S.blockProjectedGradient i x y γ hγ
  let epg : Block i := S.blockProjectedGradient i x (S.grad x.1 i) γ hγ
  let δ : Block i := y - S.grad x.1 i
  let D : ℝ := S.compositeObjective x - S.compositeObjective (S.step k hk x i ξ)
  have hdesc :
      γ * (1 - S.L i / 2 * γ) * ‖spg‖ ^ 2 ≤
        D + γ * ⟪δ, spg⟫_ℝ := by
    simpa [γ, hγ, y, spg, δ, D] using
      theorem69_selected_block_pathwise_stochastic_descent
        S k hk x i ξ
  have hlip : ‖spg - epg‖ ≤ ‖δ‖ := by
    simpa [γ, hγ, y, spg, epg, δ] using
      theorem69_block_projected_gradient_lipschitz_residual
        S i x y γ hγ
  have hL_pos : 0 < S.L i := by
    by_contra hnot
    have hL_nonpos : S.L i ≤ 0 := le_of_not_gt hnot
    have hdiv_nonpos : 2 / S.L i ≤ 0 :=
      div_nonpos_of_nonneg_of_nonpos (by norm_num) hL_nonpos
    have hlt := S.γ_lt_two_div_L k hk i
    nlinarith [hγ, hlt, hdiv_nonpos]
  have hLγ_lt_two : S.L i * γ < 2 := by
    have hlt := S.γ_lt_two_div_L k hk i
    have hmul := mul_lt_mul_of_pos_left hlt hL_pos
    have hright : S.L i * (2 / S.L i) = 2 := by
      field_simp [ne_of_gt hL_pos]
    nlinarith [hmul, hright]
  have hfactor_nonneg : 0 ≤ 1 - S.L i / 2 * γ := by
    nlinarith
  have hfactor_le_one : 1 - S.L i / 2 * γ ≤ 1 := by
    have hprod_nonneg : 0 ≤ S.L i / 2 * γ := by positivity
    nlinarith
  have h :=
    theorem69_residualized_exact_block_from_stochastic_descent
      γ (S.L i) D spg epg δ hγ.le hfactor_nonneg hfactor_le_one hdesc hlip
  simpa [γ, hγ, y, spg, epg, δ, D] using h

/-- Predicate for a source problem minimizer attaining `min_{x∈X} φ(x)`. -/
def IsProblemMinimizer (S : Setup Ξ ι Block) (x : S.Carrier) : Prop :=
  ∀ y : S.Carrier, S.compositeObjective x ≤ S.compositeObjective y

/-- Named existence obligation for the source value `φ* := min_{x∈X} φ(x)`.

This is the paper's minimum boundary from Eq. (6.3.1), exposed as a proof
obligation rather than replacing the minimum by an infimum surrogate or adding
minimum-attainment as setup data.
-/
theorem problem_minimizer_exists_obligation (S : Setup Ξ ι Block) :
    ∃ x : S.Carrier, S.IsProblemMinimizer x := by
  rcases S.problem_minimizer_exists with ⟨x, hx⟩
  exact ⟨x, hx⟩

/-- Selected minimizer attaining the source value `φ*`. -/
noncomputable def phiMinimizer (S : Setup Ξ ι Block) : S.Carrier :=
  Classical.choose (problem_minimizer_exists_obligation S)

/-- Canonical optimal value `φ* = min_{x∈X} φ(x)` from Eq. (6.3.1). -/
noncomputable def phiStar (S : Setup Ξ ι Block) : ℝ :=
  S.compositeObjective S.phiMinimizer

/-- The selected value `φ*` is attained by the selected source minimizer. -/
theorem phiMinimizer_isProblemMinimizer (S : Setup Ξ ι Block) :
    S.IsProblemMinimizer S.phiMinimizer :=
  Classical.choose_spec (problem_minimizer_exists_obligation S)

/-- Every feasible objective value is bounded below by `φ*`. -/
theorem phiStar_le (S : Setup Ξ ι Block) (x : S.Carrier) :
    S.phiStar ≤ S.compositeObjective x :=
  S.phiMinimizer_isProblemMinimizer x

section Output

variable [Nonempty ι]
variable [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- The minimum block factor `min_i p_i (1 - L_i γ_k / 2)` in Eq. (6.3.14). -/
noncomputable def outputBlockFactor (S : Setup Ξ ι Block) (k : ℕ) : ℝ :=
  SOptLib.min_block_descent_factor S.p S.L (S.γ k)

/-- One-based output window `{1, ..., N}` from Eq. (6.3.14). -/
def outputWindow (_S : Setup Ξ ι Block) (N : ℕ) : Finset ℕ :=
  Finset.Icc 1 N

/-- Raw randomized-output weight in Eq. (6.3.14). -/
noncomputable def outputWeight (S : Setup Ξ ι Block) (k : ℕ) : ℝ :=
  SOptLib.min_block_descent_output_weight S.p S.L S.γ k

/-- Denominator in the randomized-output probability formula Eq. (6.3.14). -/
noncomputable def outputDenominator (S : Setup Ξ ι Block) (N : ℕ) : ℝ :=
  SOptLib.outputWeightDenominator (S.outputWindow N) S.outputWeight

/-- Internal well-definedness predicate for turning the displayed output weights
in Eq. (6.3.14) into a genuine normalized PMF. -/
def outputWeightsAdmissible (S : Setup Ξ ι Block) (N : ℕ) : Prop :=
  SOptLib.FiniteWindowWeightsAdmissible (S.outputWindow N) S.outputWeight

/-- Formal output mass printed in Eq. (6.3.14).  This is only a PMF atom when
the finite output weights are admissible. -/
noncomputable def outputMass (S : Setup Ξ ι Block) (N : ℕ)
    (R : {k : ℕ // k ∈ S.outputWindow N}) : ℝ :=
  S.outputWeight R.1 / S.outputDenominator N

@[simp]
theorem outputMass_eq (S : Setup Ξ ι Block) (N : ℕ)
    (R : {k : ℕ // k ∈ S.outputWindow N}) :
    S.outputMass N R = S.outputWeight R.1 / S.outputDenominator N := by
  rfl

/-- External-law atom specification for Eq. (6.3.14).

Book JSON: `book/FOML/NonconvexStochasticBlockMirrorDescent.json#/assumptions/15`
records the normalized formula for `Prob(R=k)`.

This is an extension-level predicate for comparison with an arbitrary supplied
PMF.  The paper source prints the displayed Eq. (6.3.14) weights, but this file
does not build an unconditional paper-facing PMF from them.
-/
def OutputLawSpec (S : Setup Ξ ι Block) (N : ℕ)
    (Rlaw : PMF {k : ℕ // k ∈ S.outputWindow N}) : Prop :=
  SOptLib.FiniteWindowPMFSpec (S.outputWindow N) S.outputWeight Rlaw

/-- Lean well-definedness predicate for the randomized-output law.

The PDF prints the atom formula but does not separately state the finite-weight
admissibility facts needed to realize that formula as a PMF.  Therefore this
predicate is a source-boundary question, not a source-facing assumption and not
an obligation consumed by the paper theorem. -/
def outputLawWellDefined (S : Setup Ξ ι Block) (N : ℕ) : Prop :=
  ∃ Rlaw : PMF {k : ℕ // k ∈ S.outputWindow N}, S.OutputLawSpec N Rlaw

/-- Source-boundary record for Eq. (6.3.14)'s displayed law.

This proposition intentionally has no theorem asserting it from the paper
setup: Algorithm 6.1 states the formula for `Prob(R = k)`, but the source does
not state the denominator/admissibility facts needed by Lean's PMF constructor.
-/
def outputLawSourceBoundary (S : Setup Ξ ι Block) (N : ℕ) : Prop :=
  S.outputLawWellDefined N

/-- Conditional randomized-output law for `R ∈ {1, ..., N}` when the displayed
weights are known to be admissible.  This is an internal/extension object, not
an unconditional paper-facing law. -/
noncomputable def randomOutputLawOfAdmissible (S : Setup Ξ ι Block) (N : ℕ)
    (hweights : S.outputWeightsAdmissible N) :
    PMF {k : ℕ // k ∈ S.outputWindow N} :=
  SOptLib.normalizedFiniteWindowPMF (S.outputWindow N) S.outputWeight
    (SOptLib.FiniteWindowWeightsAdmissible.nonneg hweights)
    (SOptLib.FiniteWindowWeightsAdmissible.sum_pos hweights)

/-- The conditional output law has the paper's normalized mass formula. -/
theorem randomOutputLawOfAdmissible_apply (S : Setup Ξ ι Block) (N : ℕ)
    (hweights : S.outputWeightsAdmissible N)
    (R : {k : ℕ // k ∈ S.outputWindow N}) :
    S.randomOutputLawOfAdmissible N hweights R =
      ENNReal.ofReal (S.outputMass N R) := by
  rfl

/-- The conditionally constructed output law satisfies the source atom formula. -/
theorem randomOutputLawOfAdmissible_spec (S : Setup Ξ ι Block) (N : ℕ)
    (hweights : S.outputWeightsAdmissible N) :
    S.OutputLawSpec N (S.randomOutputLawOfAdmissible N hweights) := by
  intro R
  simpa [outputMass] using S.randomOutputLawOfAdmissible_apply N hweights R

/-- Denominator positivity projected from an explicit finite-weight admissibility
certificate.  This is not an unconditional paper assumption. -/
theorem outputDenominator_pos_of_admissible (S : Setup Ξ ι Block) (N : ℕ)
    (hweights : S.outputWeightsAdmissible N) :
    0 < S.outputDenominator N := by
  simpa [outputWeightsAdmissible, outputDenominator] using
    SOptLib.FiniteWindowWeightsAdmissible.sum_pos hweights

/-- The block factor in the Theorem 6.9 output law is nonnegative on positive
paper times. -/
private theorem outputBlockFactor_nonneg (S : Setup Ξ ι Block)
    (k : ℕ) (hk : 1 ≤ k) :
    0 ≤ S.outputBlockFactor k := by
  simpa [outputBlockFactor] using
    SOptLib.min_block_descent_factor_nonneg_of_pos_of_lt_two_div
      S.p S.L (S.γ k) S.p_nonneg (S.γ_pos k hk) (S.γ_lt_two_div_L k hk)

/-- The minimum block factor lower-bounds the block-sampled weighted norm sum
after summing over all coordinates. -/
private theorem outputBlockFactor_mul_blockNormSq_le_weighted_block_sum
    (S : Setup Ξ ι Block) (k : ℕ) (z : ∀ i, Block i) :
    S.outputBlockFactor k * S.blockNormSq z ≤
      ∑ i, S.p i * (1 - (S.L i / 2) * S.γ k) * ‖z i‖ ^ 2 := by
  classical
  rw [S.blockNormSq_eq_sum z]
  unfold outputBlockFactor
  rw [SOptLib.min_block_descent_factor_def]
  rw [Finset.min'_eq_inf', Finset.inf'_image]
  exact SOptLib.finset_inf_mul_sum_le_sum_mul_of_nonneg
    (I := ι) (R := ℝ)
    (fun i => S.p i * (1 - (S.L i / 2) * S.γ k))
    (fun i => ‖z i‖ ^ 2) (by
      intro i
      exact sq_nonneg ‖z i‖)

/-- Output weights convert the minimum-factor block-norm bound into the
`γ_k`-scaled sampled-block weighted sum used before taking block-index
expectations. -/
private theorem outputWeight_mul_blockNormSq_le_gamma_weighted_block_sum
    (S : Setup Ξ ι Block) (k : ℕ) (hk : 1 ≤ k) (z : ∀ i, Block i) :
    S.outputWeight k * S.blockNormSq z ≤
      S.γ k * ∑ i, S.p i * (1 - (S.L i / 2) * S.γ k) * ‖z i‖ ^ 2 := by
  have hfactor := S.outputBlockFactor_mul_blockNormSq_le_weighted_block_sum k z
  have hγ_nonneg : 0 ≤ S.γ k := le_of_lt (S.γ_pos k hk)
  calc
    S.outputWeight k * S.blockNormSq z =
        S.γ k * (S.outputBlockFactor k * S.blockNormSq z) := by
          rw [outputWeight, SOptLib.min_block_descent_output_weight_def,
            outputBlockFactor]
          ring
    _ ≤ S.γ k *
        (∑ i, S.p i * (1 - (S.L i / 2) * S.γ k) * ‖z i‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hfactor hγ_nonneg

/-- Raw Theorem 6.9 output weights are nonnegative on the output window. -/
private theorem outputWeight_nonneg_on_window (S : Setup Ξ ι Block)
    (N k : ℕ) (hk : k ∈ S.outputWindow N) :
    0 ≤ S.outputWeight k := by
  have hk_pos : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  exact mul_nonneg (le_of_lt (S.γ_pos k hk_pos))
    (S.outputBlockFactor_nonneg k hk_pos)

/-- If an external PMF satisfies the displayed output-law atom formula, then
the printed denominator cannot be zero. -/
private theorem outputDenominator_ne_zero_of_outputLawSpec
    (S : Setup Ξ ι Block) (N : ℕ)
    (Rlaw : PMF {k : ℕ // k ∈ S.outputWindow N})
    (hRlaw : S.OutputLawSpec N Rlaw) :
    S.outputDenominator N ≠ 0 := by
  simpa [outputDenominator, SOptLib.outputWeightDenominator, OutputLawSpec] using
    SOptLib.FiniteWindowPMFSpec.denominator_ne_zero
      (S.outputWindow N) S.outputWeight Rlaw hRlaw

/-- The displayed output-law denominator is positive whenever it is realized by
an actual PMF satisfying `OutputLawSpec`. -/
private theorem outputDenominator_pos_of_outputLawSpec
    (S : Setup Ξ ι Block) (N : ℕ)
    (Rlaw : PMF {k : ℕ // k ∈ S.outputWindow N})
    (hRlaw : S.OutputLawSpec N Rlaw) :
    0 < S.outputDenominator N := by
  simpa [outputDenominator, SOptLib.outputWeightDenominator, OutputLawSpec] using
    SOptLib.FiniteWindowPMFSpec.denominator_pos_of_nonneg
      (S.outputWindow N) S.outputWeight Rlaw
      (fun k hk => S.outputWeight_nonneg_on_window N k hk) hRlaw

/-- Convert `OutputLawSpec` from ENNReal PMF atoms to real singleton masses. -/
private theorem outputLawSpec_real_singleton
    (S : Setup Ξ ι Block) (N : ℕ)
    (Rlaw : PMF {k : ℕ // k ∈ S.outputWindow N})
    (hRlaw : S.OutputLawSpec N Rlaw) :
    ∀ R : {k : ℕ // k ∈ S.outputWindow N},
      Rlaw.toMeasure.real ({R} : Set {k : ℕ // k ∈ S.outputWindow N}) =
        S.outputMass N R := by
  simpa [outputMass, outputDenominator, SOptLib.outputWeightDenominator, OutputLawSpec] using
    SOptLib.FiniteWindowPMFSpec.toMeasure_real_singleton
      (S.outputWindow N) S.outputWeight Rlaw
      (fun k hk => S.outputWeight_nonneg_on_window N k hk) hRlaw

/-- Natural-time stochastic run: a block-index stream and an oracle-sample stream. -/
abbrev RunSample (_S : Setup Ξ ι Block) : Type _ :=
  SOptLib.split_block_oracle_run_sample ι Ξ

/-- Block-index process `i_k` on the canonical run space. -/
def blockIndexProcess (_S : Setup Ξ ι Block) (ω : (ℕ → ι) × (ℕ → Ξ)) (k : ℕ) : ι :=
  ω.1 k

/-- Oracle-sample process `ξ_k` on the canonical run space. -/
def oracleSampleProcess (_S : Setup Ξ ι Block) (ω : (ℕ → ι) × (ℕ → Ξ)) (k : ℕ) : Ξ :=
  ω.2 k

/-- Canonical block-index law with atoms `Prob{i_k=i}=p_i` from Eq. (6.3.11). -/
noncomputable def blockIndexLaw (S : Setup Ξ ι Block) : Measure ι :=
  SOptLib.finiteBlockIndexLaw S.p S.p_nonneg S.p_sum

/-- The canonical block-index law has the source atom formula `Prob{i_k=i}=p_i`. -/
@[simp]
theorem blockIndexLaw_singleton (S : Setup Ξ ι Block) (i : ι) :
    S.blockIndexLaw ({i} : Set ι) = ENNReal.ofReal (S.p i) := by
  simpa [blockIndexLaw] using
    SOptLib.finiteBlockIndexLaw_singleton S.p S.p_nonneg S.p_sum i

/-- The canonical block-index law is a probability measure. -/
theorem blockIndexLaw_isProbabilityMeasure (S : Setup Ξ ι Block) :
    IsProbabilityMeasure S.blockIndexLaw := by
  simpa [blockIndexLaw] using
    SOptLib.finiteBlockIndexLaw_isProbabilityMeasure S.p S.p_nonneg S.p_sum

/-- Canonical stochastic-run law: iid block-index stream and iid oracle-sample stream. -/
noncomputable def runLaw (S : Setup Ξ ι Block) : Measure S.RunSample :=
  (SOptLib.iidStreamLaw S.blockIndexLaw).prod (SOptLib.iidStreamLaw S.sampleLaw)

/-- The canonical stochastic-run law is a probability measure. -/
private theorem runLaw_isProbabilityMeasure (S : Setup Ξ ι Block) :
    IsProbabilityMeasure S.runLaw := by
  unfold runLaw
  haveI : IsProbabilityMeasure S.blockIndexLaw := S.blockIndexLaw_isProbabilityMeasure
  haveI : IsProbabilityMeasure S.sampleLaw := S.sampleLaw_prob
  infer_instance

/-- Generated iterate process `x_k` on the canonical run law. -/
noncomputable def iterateProcess (S : Setup Ξ ι Block)
    (k : ℕ) (hk : 1 ≤ k) (ω : S.RunSample) : S.Carrier :=
  S.paperIterate ω.1 ω.2 k hk

/-- Sampled stochastic block-gradient process `G_{i_k}` from Algorithm 6.1. -/
noncomputable def stochasticBlockGradientProcess (S : Setup Ξ ι Block)
    (k : ℕ) (hk : 1 ≤ k) (ω : S.RunSample) :
    Block (S.blockIndexProcess ω k) :=
  S.sampledGradient (S.iterateProcess k hk ω) (S.oracleSampleProcess ω k)
    (S.blockIndexProcess ω k)

/-- Exact queried block-gradient process `U_{i_k}ᵀg(x_k)`. -/
noncomputable def exactBlockGradientProcess (S : Setup Ξ ι Block)
    (k : ℕ) (hk : 1 ≤ k) (ω : S.RunSample) :
    Block (S.blockIndexProcess ω k) :=
  S.grad (S.iterateProcess k hk ω).1 (S.blockIndexProcess ω k)

/-- Residual process `δ_k = G_{i_k}-U_{i_k}ᵀ∇f(x_k)` from Theorem 6.9. -/
noncomputable def stochasticGradientResidualProcess (S : Setup Ξ ι Block)
    (k : ℕ) (hk : 1 ≤ k) (ω : S.RunSample) :
    Block (S.blockIndexProcess ω k) :=
  S.stochasticBlockGradientProcess k hk ω - S.exactBlockGradientProcess k hk ω

@[simp]
theorem stochasticGradientResidualProcess_eq (S : Setup Ξ ι Block)
    (k : ℕ) (hk : 1 ≤ k) (ω : S.RunSample) :
    S.stochasticGradientResidualProcess k hk ω =
      S.G (S.iterateProcess k hk ω).1 (S.oracleSampleProcess ω k)
          (S.blockIndexProcess ω k) -
        S.grad (S.iterateProcess k hk ω).1 (S.blockIndexProcess ω k) := by
  rfl

/-- Exact block projected-gradient process `U_{i_k}ᵀg_k` used in the proof of
Theorem 6.9. -/
noncomputable def exactProjectedGradientProcess (S : Setup Ξ ι Block)
    (k : ℕ) (hk : 1 ≤ k) (ω : S.RunSample) :
    Block (S.blockIndexProcess ω k) :=
  S.blockProjectedGradient (S.blockIndexProcess ω k) (S.iterateProcess k hk ω)
    (S.exactBlockGradientProcess k hk ω) (S.γ k) (S.gamma_pos_obligation k hk)

/-- Stochastic sampled-block projected-gradient process `g̃_k` used in the proof
of Theorem 6.9. -/
noncomputable def stochasticProjectedGradientProcess (S : Setup Ξ ι Block)
    (k : ℕ) (hk : 1 ≤ k) (ω : S.RunSample) :
    Block (S.blockIndexProcess ω k) :=
  S.blockProjectedGradient (S.blockIndexProcess ω k) (S.iterateProcess k hk ω)
    (S.stochasticBlockGradientProcess k hk ω) (S.γ k) (S.gamma_pos_obligation k hk)

/-- Eq. (6.3.12)'s mean condition, specialized to histories from the canonical
run process and projected from the source process condition. -/
theorem run_stochasticGradientMeanCondition_of_source_condition (S : Setup Ξ ι Block)
    (hG : S.StochasticGradientCondition)
    (k : ℕ) (hk : 1 ≤ k) (ω : S.RunSample) :
    S.StochasticGradientMeanConditionAtHistory k hk ω.1 ω.2 :=
  S.sampledGradient_unbiased_at_iterate_of_source_condition hG k hk ω.1 ω.2

/-- Eq. (6.3.12)'s second-moment condition, specialized to histories from the
canonical run process and projected from the source process condition. -/
theorem run_stochasticGradientSecondMomentCondition_of_source_condition
    (S : Setup Ξ ι Block) (hG : S.StochasticGradientCondition)
    (k : ℕ) (hk : 1 ≤ k) (ω : S.RunSample) :
    S.StochasticGradientSecondMomentConditionAtHistory k hk ω.1 ω.2 :=
  S.sampledGradient_variance_at_iterate_of_source_condition hG k hk ω.1 ω.2

/-- Random output `x̄_N = x_R` from Eq. (6.3.14), evaluated on a stochastic run. -/
noncomputable def randomOutput (S : Setup Ξ ι Block)
    (N : ℕ) (_hN : 1 ≤ N) (R : {k : ℕ // k ∈ S.outputWindow N})
    (ω : S.RunSample) : S.Carrier :=
  S.paperIterate ω.1 ω.2 R.1 (Finset.mem_Icc.mp R.2).1

@[simp]
theorem randomOutput_eq_iterate (S : Setup Ξ ι Block)
    (N : ℕ) (hN : 1 ≤ N) (R : {k : ℕ // k ∈ S.outputWindow N})
    (ω : S.RunSample) :
    S.randomOutput N hN R ω =
      S.paperIterate ω.1 ω.2 R.1 (Finset.mem_Icc.mp R.2).1 := by
  rfl

/-- Run expectation of the squared source composite projected gradient
`P_X(x_k,g(x_k),γ_k)` at a fixed paper-time iterate. -/
noncomputable def runExpectedSquaredProjectedGradientAt (S : Setup Ξ ι Block)
    (k : ℕ) (hk : 1 ≤ k) : ℝ :=
  ∫ ω : S.RunSample,
      let xk := S.paperIterate ω.1 ω.2 k hk
      S.blockNormSq
        (Pi.map
          (fun i yi => S.blockProjectedGradient i xk yi (S.γ k)
            (S.gamma_pos_obligation k hk))
          (S.sourceGradient xk.1))
    ∂S.runLaw

/-- The run expectation using the source mean-gradient can be rewritten with
the exact gradient once the source/exact bridge is available at `x_k`. -/
private theorem runExpectedSquaredProjectedGradientAt_eq_exactGradient
    (S : Setup Ξ ι Block)
    (hG : S.StochasticGradientCondition)
    (hResidualMean :
      ∀ (k : ℕ) (hk : 1 ≤ k) (blockSample : ℕ → ι) (sample : ℕ → Ξ),
        S.StochasticGradientResidualScalarMeanConditionAtHistory
          k hk blockSample sample)
    (k : ℕ) (hk : 1 ≤ k) :
    S.runExpectedSquaredProjectedGradientAt k hk =
      ∫ ω : S.RunSample,
          let xk := S.paperIterate ω.1 ω.2 k hk
          S.blockNormSq
            (Pi.map
              (fun i yi => S.blockProjectedGradient i xk yi (S.γ k)
                (S.gamma_pos_obligation k hk))
              (S.grad xk.1))
        ∂S.runLaw := by
  unfold runExpectedSquaredProjectedGradientAt
  refine integral_congr_ae ?_
  filter_upwards [] with ω
  have hgrad :
      S.sourceGradient (S.paperIterate ω.1 ω.2 k hk).1 =
        S.grad (S.paperIterate ω.1 ω.2 k hk).1 :=
    sourceGradient_paperIterate_eq_grad S hG hResidualMean k hk ω.1 ω.2
  dsimp
  rw [hgrad]

/-- Pointwise telescope of the objective drops over the one-based output window.

This is the deterministic part of Theorem 6.9 proof steps 13-14.  The
expectation-level telescope additionally needs objective-drop integrability in
order to commute the finite sum with `S.runLaw`.
-/
private theorem theorem69_objective_drop_pointwise_telescope
    (S : Setup Ξ ι Block) (N : ℕ) (hN : 1 ≤ N) (ω : S.RunSample) :
    Finset.sum (S.outputWindow N) (fun k =>
        if hk : k ∈ S.outputWindow N then
          S.compositeObjective
              (S.paperIterate ω.1 ω.2 k (Finset.mem_Icc.mp hk).1) -
            S.compositeObjective
              (S.paperIterate ω.1 ω.2 (k + 1)
                (Nat.succ_le_succ (Nat.zero_le k)))
        else 0) =
      S.compositeObjective S.x₁Carrier -
        S.compositeObjective
          (S.paperIterate ω.1 ω.2 (N + 1) (Nat.succ_le_succ (Nat.zero_le N))) := by
  classical
  let a : ℕ → ℝ := fun n =>
    if hn : 1 ≤ n then
      S.compositeObjective (S.paperIterate ω.1 ω.2 n hn)
    else 0
  have hsum_eq :
      Finset.sum (S.outputWindow N) (fun k =>
          if hk : k ∈ S.outputWindow N then
            S.compositeObjective
                (S.paperIterate ω.1 ω.2 k (Finset.mem_Icc.mp hk).1) -
              S.compositeObjective
                (S.paperIterate ω.1 ω.2 (k + 1)
                  (Nat.succ_le_succ (Nat.zero_le k)))
          else 0) =
        Finset.sum (Finset.Icc 1 N) (fun n => a n - a (n + 1)) := by
    unfold outputWindow
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hk_pos : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hk_succ : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
    simp [a, hk, hk_pos, hk_succ]
  have htelescope :
      Finset.sum (Finset.Icc 1 N) (fun n => a n - a (n + 1)) =
        a 1 - a (N + 1) :=
    sum_Icc_sub_succ a 1 N hN
  calc
    Finset.sum (S.outputWindow N) (fun k =>
        if hk : k ∈ S.outputWindow N then
          S.compositeObjective
              (S.paperIterate ω.1 ω.2 k (Finset.mem_Icc.mp hk).1) -
            S.compositeObjective
              (S.paperIterate ω.1 ω.2 (k + 1)
                (Nat.succ_le_succ (Nat.zero_le k)))
        else 0)
        = Finset.sum (Finset.Icc 1 N) (fun n => a n - a (n + 1)) := hsum_eq
    _ = a 1 - a (N + 1) := htelescope
    _ = S.compositeObjective S.x₁Carrier -
        S.compositeObjective
          (S.paperIterate ω.1 ω.2 (N + 1) (Nat.succ_le_succ (Nat.zero_le N))) := by
          simp [a]

/-- Integrand for the selected-output expectation in Theorem 6.9. -/
noncomputable def theorem69IntegrandWithLaw (S : Setup Ξ ι Block)
    (N : ℕ) (hN : 1 ≤ N)
    (q : {k : ℕ // k ∈ S.outputWindow N} × S.RunSample) : ℝ :=
  let xR := S.randomOutput N hN q.1 q.2
  S.blockNormSq
    (Pi.map
      (fun i yi => S.blockProjectedGradient i xR yi (S.γ q.1.1)
        (S.gamma_pos_obligation q.1.1 (Finset.mem_Icc.mp q.1.2).1))
      (S.sourceGradient xR.1))

/-- Squared exact composite projected-gradient integrand at a fixed paper time. -/
noncomputable def theorem69ExactProjectedGradientNormSqAt (S : Setup Ξ ι Block)
    (k : ℕ) (hk : 1 ≤ k) (ω : S.RunSample) : ℝ :=
  let xk := S.paperIterate ω.1 ω.2 k hk
  S.blockNormSq
    (Pi.map
      (fun i yi => S.blockProjectedGradient i xk yi (S.γ k)
        (S.gamma_pos_obligation k hk))
      (S.grad xk.1))

/-- Consecutive objective-drop integrand used by the expected telescope. -/
noncomputable def theorem69ObjectiveDropIntegrandAt (S : Setup Ξ ι Block)
    (k : ℕ) (hk : 1 ≤ k) (ω : S.RunSample) : ℝ :=
  S.compositeObjective (S.paperIterate ω.1 ω.2 k hk) -
    S.compositeObjective
      (S.paperIterate ω.1 ω.2 (k + 1)
        (Nat.succ_le_succ (Nat.zero_le k)))

/-- Sampled-block left side in the fixed-time current-coordinate descent step. -/
noncomputable def theorem69SelectedBlockDescentLhsAt (S : Setup Ξ ι Block)
    (k : ℕ) (hk : 1 ≤ k) (ω : S.RunSample) : ℝ :=
  let iω := S.blockIndexProcess ω k
  let epg := S.exactProjectedGradientProcess k hk ω
  (S.γ k / 2) * (1 - S.L iω / 2 * S.γ k) * ‖epg‖ ^ 2

/-- Sampled-block right side after substituting the current-step recursion. -/
noncomputable def theorem69SelectedBlockDescentRhsAt (S : Setup Ξ ι Block)
    (k : ℕ) (hk : 1 ≤ k) (ω : S.RunSample) : ℝ :=
  let epg := S.exactProjectedGradientProcess k hk ω
  let δ := S.stochasticGradientResidualProcess k hk ω
  S.theorem69ObjectiveDropIntegrandAt k hk ω +
    S.γ k * ⟪δ, epg⟫_ℝ + 2 * S.γ k * ‖δ‖ ^ 2

/-- Residual/noise budget term in the fixed-time Theorem 6.9 descent step. -/
noncomputable def theorem69ResidualBudgetIntegrandAt (S : Setup Ξ ι Block)
    (k : ℕ) (hk : 1 ≤ k) (ω : S.RunSample) : ℝ :=
  let epg := S.exactProjectedGradientProcess k hk ω
  let δ := S.stochasticGradientResidualProcess k hk ω
  S.γ k * ⟪δ, epg⟫_ℝ + 2 * S.γ k * ‖δ‖ ^ 2

/-- Low-level current-coordinate transport certificate for Theorem 6.9 proof
steps 20-22.

The certificate is deliberately stated at the product-law equality boundary: it
names a measurable strict-history key, the current block variable, and the
finite fiber observable whose sampled expectation equals the weighted all-block
fiber sum.  It does not contain the pathwise descent inequality or the fixed-time
expected-descent conclusion.
-/
structure Theorem69CurrentCoordinateTransportRegularity (S : Setup Ξ ι Block)
    (k : ℕ) (hk : 1 ≤ k) where
  History : Type
  historyMeasurable : MeasurableSpace History
  historyKey : S.RunSample → History
  currentBlock : S.RunSample → ι
  blockFiberLhs : History → ι → ℝ
  currentBlock_eq :
    currentBlock = fun ω : S.RunSample => S.blockIndexProcess ω k
  history_aemeasurable :
    letI := historyMeasurable
    AEMeasurable historyKey S.runLaw
  currentBlock_aemeasurable :
    AEMeasurable currentBlock S.runLaw
  currentBlock_independent :
    letI := historyMeasurable
    ProbabilityTheory.IndepFun historyKey currentBlock S.runLaw
  currentBlock_law :
    Measure.map currentBlock S.runLaw = S.blockIndexLaw
  blockIndexLaw_real_singleton :
    ∀ i : ι, S.blockIndexLaw.real ({i} : Set ι) = S.p i
  blockFiber_integrable :
    letI := historyMeasurable
    Integrable (fun z : History × ι => blockFiberLhs z.1 z.2)
      ((Measure.map historyKey S.runLaw).prod S.blockIndexLaw)
  weightedFiber_aestronglyMeasurable :
    letI := historyMeasurable
    AEStronglyMeasurable
      (fun a : History => Finset.univ.sum (fun i : ι => S.p i • blockFiberLhs a i))
      (Measure.map historyKey S.runLaw)
  weightedFiber_integrable :
    Integrable
      (fun ω : S.RunSample =>
        Finset.univ.sum (fun i : ι => S.p i • blockFiberLhs (historyKey ω) i))
      S.runLaw
  selectedLhs_integrable :
    Integrable (S.theorem69SelectedBlockDescentLhsAt k hk) S.runLaw
  fullGradientLhs_integrable :
    Integrable
      (fun ω : S.RunSample =>
        (1 / 2 : ℝ) * S.outputWeight k *
          S.theorem69ExactProjectedGradientNormSqAt k hk ω)
      S.runLaw
  weightedFiber_fullGradient_eq :
    ∀ᵐ ω ∂S.runLaw,
      Finset.univ.sum (fun i : ι => S.p i • blockFiberLhs (historyKey ω) i) =
        (S.γ k / 2) *
          ∑ i, S.p i * (1 - (S.L i / 2) * S.γ k) *
            ‖(Pi.map
                (fun j yj => S.blockProjectedGradient j
                  (S.paperIterate ω.1 ω.2 k hk)
                  yj (S.γ k) (S.gamma_pos_obligation k hk))
                (S.grad (S.paperIterate ω.1 ω.2 k hk).1) i)‖ ^ 2
  sampled_lhs_eq :
    ∀ᵐ ω ∂S.runLaw,
      blockFiberLhs (historyKey ω) (currentBlock ω) =
        S.theorem69SelectedBlockDescentLhsAt k hk ω

/-- Low-level current-sample transport certificate for the residual budget in
Theorem 6.9 proof steps 16-19.

The fixed-history residual lemma integrates only a fresh oracle draw against
`S.sampleLaw`.  This certificate supplies the Lean process semantics needed to
lift that fixed-fiber budget through the canonical run law: a measurable history
key, a current sample with law `S.sampleLaw`, independence, a measurable scalar
fiber, and the a.e. identification with the generated residual budget process.
-/
structure Theorem69ResidualBudgetTransportRegularity (S : Setup Ξ ι Block)
    (k : ℕ) (hk : 1 ≤ k) where
  History : Type
  historyMeasurable : MeasurableSpace History
  historyKey : S.RunSample → History
  currentSample : S.RunSample → Ξ
  fiberBudget : History → Ξ → ℝ
  historyBlockSample : History → ℕ → ι
  historySample : History → ℕ → Ξ
  historyDirection : (a : History) → Block (historyBlockSample a k)
  currentSample_eq :
    currentSample = fun ω : S.RunSample => S.oracleSampleProcess ω k
  fiberBudget_measurable :
    letI := historyMeasurable
    Measurable (Function.uncurry fiberBudget)
  history_measurable :
    letI := historyMeasurable
    Measurable historyKey
  currentSample_measurable :
    Measurable currentSample
  currentSample_independent :
    letI := historyMeasurable
    ProbabilityTheory.IndepFun historyKey currentSample S.runLaw
  currentSample_law :
    Measure.map currentSample S.runLaw = S.sampleLaw
  composed_integrable :
    Integrable (fun ω : S.RunSample => fiberBudget (historyKey ω) (currentSample ω))
      S.runLaw
  residualBudget_integrable :
    Integrable (S.theorem69ResidualBudgetIntegrandAt k hk) S.runLaw
  fixedFiber_eq :
    ∀ (a : History) (ξ : Ξ),
      fiberBudget a ξ =
        S.γ k *
            ⟪S.stochasticGradientResidualAtHistory k hk
                (historyBlockSample a) (historySample a) ξ,
              historyDirection a⟫_ℝ +
          2 * S.γ k *
            ‖S.stochasticGradientResidualAtHistory k hk
                (historyBlockSample a) (historySample a) ξ‖ ^ 2
  residualBudget_eq :
    ∀ᵐ ω ∂S.runLaw,
      fiberBudget (historyKey ω) (currentSample ω) =
        S.theorem69ResidualBudgetIntegrandAt k hk ω

/-- Run-process regularity boundary for the current-coordinate expectation
transport in Theorem 6.9 proof steps 20-22.

This is a regularity/adaptedness interface only: each fixed output-window time
must provide a strict-history/current-block transport certificate.  The
fixed-time expected-descent inequality is derived in a separate theorem from
this certificate and the already-proved pathwise descent facts.
-/
def theorem69RunProcessRegularity (S : Setup Ξ ι Block)
    (N : ℕ) (_hN : 1 ≤ N) : Prop :=
  ∀ (k : ℕ) (hk : k ∈ S.outputWindow N) (hk_pos : 1 ≤ k),
    Nonempty
        (S.Theorem69CurrentCoordinateTransportRegularity k hk_pos) ∧
      Nonempty
        (S.Theorem69ResidualBudgetTransportRegularity k hk_pos)

/-- The current-coordinate certificate discharges the generic product-law
transport API for the sampled block observable, yielding the weighted all-block
fiber expectation. -/
private theorem theorem69_selected_block_lhs_eq_weighted_fiber_of_process_regularity
    (S : Setup Ξ ι Block) (k : ℕ) (hk : 1 ≤ k)
    (hreg : S.Theorem69CurrentCoordinateTransportRegularity k hk) :
    (∫ ω : S.RunSample,
        S.theorem69SelectedBlockDescentLhsAt k hk ω ∂S.runLaw) =
      ∫ ω : S.RunSample,
        Finset.univ.sum (fun i : ι => S.p i • hreg.blockFiberLhs (hreg.historyKey ω) i)
      ∂S.runLaw := by
  classical
  letI := hreg.historyMeasurable
  haveI : IsProbabilityMeasure S.runLaw := S.runLaw_isProbabilityMeasure
  haveI : IsFiniteMeasure S.runLaw := inferInstance
  have htransport :
      (∫ ω : S.RunSample,
          hreg.blockFiberLhs (hreg.historyKey ω) (hreg.currentBlock ω)
        ∂S.runLaw) =
        ∫ ω : S.RunSample,
          Finset.univ.sum (fun i : ι => S.p i • hreg.blockFiberLhs (hreg.historyKey ω) i)
        ∂S.runLaw :=
    expectation_sample_eq_expectation_weighted_fiber_sum_of_indepFun
      (P := S.runLaw) (W := hreg.historyKey) (Y := hreg.currentBlock)
      (nu := S.blockIndexLaw) (w := S.p)
      (F := hreg.blockFiberLhs)
      hreg.history_aemeasurable hreg.currentBlock_aemeasurable
      hreg.currentBlock_independent hreg.currentBlock_law
      hreg.blockIndexLaw_real_singleton hreg.blockFiber_integrable
  have hleft :
      (∫ ω : S.RunSample,
          S.theorem69SelectedBlockDescentLhsAt k hk ω ∂S.runLaw) =
        ∫ ω : S.RunSample,
          hreg.blockFiberLhs (hreg.historyKey ω) (hreg.currentBlock ω)
        ∂S.runLaw := by
    exact integral_congr_ae
      (hreg.sampled_lhs_eq.mono fun _ h => h.symm)
  calc
    (∫ ω : S.RunSample,
        S.theorem69SelectedBlockDescentLhsAt k hk ω ∂S.runLaw)
        = ∫ ω : S.RunSample,
            hreg.blockFiberLhs (hreg.historyKey ω) (hreg.currentBlock ω)
          ∂S.runLaw := hleft
    _ = ∫ ω : S.RunSample,
          Finset.univ.sum (fun i : ι => S.p i • hreg.blockFiberLhs (hreg.historyKey ω) i)
        ∂S.runLaw := htransport

/-- The block-factor pointwise estimate and current-coordinate product-law
transport compare the full projected-gradient stationarity measure with the
sampled-block left side. -/
private theorem theorem69_full_gradient_lhs_le_selected_block_lhs
    (S : Setup Ξ ι Block) (k : ℕ) (hk : 1 ≤ k)
    (hreg : S.Theorem69CurrentCoordinateTransportRegularity k hk)
    (hblockFactorPointwise :
      ∀ ω : S.RunSample,
        S.outputWeight k *
            S.blockNormSq
              (Pi.map
                (fun i yi => S.blockProjectedGradient i
                  (S.paperIterate ω.1 ω.2 k hk)
                  yi (S.γ k) (S.gamma_pos_obligation k hk))
                (S.grad (S.paperIterate ω.1 ω.2 k hk).1)) ≤
          S.γ k *
            ∑ i, S.p i * (1 - (S.L i / 2) * S.γ k) *
              ‖(Pi.map
                  (fun j yj => S.blockProjectedGradient j
                    (S.paperIterate ω.1 ω.2 k hk)
                    yj (S.γ k) (S.gamma_pos_obligation k hk))
                  (S.grad (S.paperIterate ω.1 ω.2 k hk).1) i)‖ ^ 2) :
    (1 / 2 : ℝ) * S.outputWeight k *
        (∫ ω : S.RunSample,
          S.theorem69ExactProjectedGradientNormSqAt k hk ω ∂S.runLaw) ≤
      ∫ ω : S.RunSample,
        S.theorem69SelectedBlockDescentLhsAt k hk ω ∂S.runLaw := by
  classical
  let weightedFiber : S.RunSample → ℝ := fun ω =>
    Finset.univ.sum (fun i : ι => S.p i • hreg.blockFiberLhs (hreg.historyKey ω) i)
  have hweighted_eq_selected :
      (∫ ω : S.RunSample, weightedFiber ω ∂S.runLaw) =
        ∫ ω : S.RunSample,
          S.theorem69SelectedBlockDescentLhsAt k hk ω ∂S.runLaw := by
    exact (theorem69_selected_block_lhs_eq_weighted_fiber_of_process_regularity
      S k hk hreg).symm
  have hpoint :
      (fun ω : S.RunSample =>
        (1 / 2 : ℝ) * S.outputWeight k *
          S.theorem69ExactProjectedGradientNormSqAt k hk ω) ≤ᵐ[S.runLaw]
        weightedFiber := by
    filter_upwards [hreg.weightedFiber_fullGradient_eq] with ω hω
    have hbf := hblockFactorPointwise ω
    have hhalf :=
      mul_le_mul_of_nonneg_left hbf (by norm_num : (0 : ℝ) ≤ 1 / 2)
    calc
      (1 / 2 : ℝ) * S.outputWeight k *
          S.theorem69ExactProjectedGradientNormSqAt k hk ω
          ≤ (1 / 2 : ℝ) *
              (S.γ k *
                ∑ i, S.p i * (1 - (S.L i / 2) * S.γ k) *
                  ‖(Pi.map
                      (fun j yj => S.blockProjectedGradient j
                        (S.paperIterate ω.1 ω.2 k hk)
                        yj (S.γ k) (S.gamma_pos_obligation k hk))
                      (S.grad (S.paperIterate ω.1 ω.2 k hk).1) i)‖ ^ 2) := by
            simpa [theorem69ExactProjectedGradientNormSqAt, mul_assoc]
              using hhalf
      _ = weightedFiber ω := by
            calc
              (1 / 2 : ℝ) *
                  (S.γ k *
                    ∑ i, S.p i * (1 - (S.L i / 2) * S.γ k) *
                      ‖(Pi.map
                          (fun j yj => S.blockProjectedGradient j
                            (S.paperIterate ω.1 ω.2 k hk)
                            yj (S.γ k) (S.gamma_pos_obligation k hk))
                          (S.grad (S.paperIterate ω.1 ω.2 k hk).1) i)‖ ^ 2)
                  =
                (S.γ k / 2) *
                  ∑ i, S.p i * (1 - (S.L i / 2) * S.γ k) *
                    ‖(Pi.map
                        (fun j yj => S.blockProjectedGradient j
                          (S.paperIterate ω.1 ω.2 k hk)
                          yj (S.γ k) (S.gamma_pos_obligation k hk))
                        (S.grad (S.paperIterate ω.1 ω.2 k hk).1) i)‖ ^ 2 := by
                    ring
              _ = weightedFiber ω := hω.symm
  have hmono :
      ∫ ω : S.RunSample,
          (1 / 2 : ℝ) * S.outputWeight k *
            S.theorem69ExactProjectedGradientNormSqAt k hk ω ∂S.runLaw ≤
        ∫ ω : S.RunSample, weightedFiber ω ∂S.runLaw :=
    integral_mono_ae hreg.fullGradientLhs_integrable hreg.weightedFiber_integrable hpoint
  have hleft :
      (∫ ω : S.RunSample,
          (1 / 2 : ℝ) * S.outputWeight k *
            S.theorem69ExactProjectedGradientNormSqAt k hk ω ∂S.runLaw) =
        (1 / 2 : ℝ) * S.outputWeight k *
          (∫ ω : S.RunSample,
            S.theorem69ExactProjectedGradientNormSqAt k hk ω ∂S.runLaw) := by
    simpa [mul_assoc] using
      (integral_const_mul
        (μ := S.runLaw) (r := (1 / 2 : ℝ) * S.outputWeight k)
        (f := fun ω : S.RunSample =>
          S.theorem69ExactProjectedGradientNormSqAt k hk ω))
  calc
    (1 / 2 : ℝ) * S.outputWeight k *
        (∫ ω : S.RunSample,
          S.theorem69ExactProjectedGradientNormSqAt k hk ω ∂S.runLaw)
        = ∫ ω : S.RunSample,
            (1 / 2 : ℝ) * S.outputWeight k *
              S.theorem69ExactProjectedGradientNormSqAt k hk ω ∂S.runLaw := hleft.symm
    _ ≤ ∫ ω : S.RunSample, weightedFiber ω ∂S.runLaw := hmono
    _ = ∫ ω : S.RunSample,
          S.theorem69SelectedBlockDescentLhsAt k hk ω ∂S.runLaw := hweighted_eq_selected

/-- Lift the fixed-history residual budget through the canonical run law using
the supplied current-sample product-law regularity. -/
private theorem theorem69_run_law_residual_budget_of_process_regularity
    (S : Setup Ξ ι Block) (k : ℕ) (hk : 1 ≤ k)
    (hreg : S.Theorem69ResidualBudgetTransportRegularity k hk)
    (hResidualMean :
      ∀ (t : ℕ) (ht : 1 ≤ t) (blockSample : ℕ → ι) (sample : ℕ → Ξ),
        S.StochasticGradientResidualScalarMeanConditionAtHistory
          t ht blockSample sample)
    (hResidualSecond :
      ∀ (t : ℕ) (ht : 1 ≤ t) (blockSample : ℕ → ι) (sample : ℕ → Ξ),
        S.ExactGradientResidualSecondMomentConditionAtHistory
          t ht blockSample sample) :
    Integrable (S.theorem69ResidualBudgetIntegrandAt k hk) S.runLaw ∧
      (∫ ω : S.RunSample,
        S.theorem69ResidualBudgetIntegrandAt k hk ω ∂S.runLaw) ≤
        2 * S.γ k * S.sigmaBar k ^ 2 := by
  classical
  letI := hreg.historyMeasurable
  haveI : IsProbabilityMeasure S.runLaw := S.runLaw_isProbabilityMeasure
  haveI : IsProbabilityMeasure S.sampleLaw := S.sampleLaw_prob
  have hfixed :
      ∀ a : hreg.History,
        (∫ ξ, hreg.fiberBudget a ξ ∂S.sampleLaw) ≤
          2 * S.γ k * S.sigmaBar k ^ 2 := by
    intro a
    have hbudget :=
      (theorem69_fixed_history_residual_budget_integral
        S hResidualMean hResidualSecond k hk
        (hreg.historyBlockSample a) (hreg.historySample a)
        (hreg.historyDirection a)).2
    simpa [hreg.fixedFiber_eq a] using hbudget
  have hcomp :
      (∫ ω : S.RunSample,
          hreg.fiberBudget (hreg.historyKey ω) (hreg.currentSample ω)
        ∂S.runLaw) ≤
        2 * S.γ k * S.sigmaBar k ^ 2 :=
    integral_comp_le_of_indep_fixed_integral_bound
      (P := S.runLaw) (ν := S.sampleLaw)
      (φ := hreg.fiberBudget) (X := hreg.historyKey) (Y := hreg.currentSample)
      (C := 2 * S.γ k * S.sigmaBar k ^ 2)
      hreg.fiberBudget_measurable hreg.history_measurable
      hreg.currentSample_measurable hreg.currentSample_independent
      hreg.currentSample_law hreg.composed_integrable hfixed
  refine ⟨hreg.residualBudget_integrable, ?_⟩
  calc
    (∫ ω : S.RunSample,
        S.theorem69ResidualBudgetIntegrandAt k hk ω ∂S.runLaw)
        = ∫ ω : S.RunSample,
            hreg.fiberBudget (hreg.historyKey ω) (hreg.currentSample ω)
          ∂S.runLaw := by
            exact integral_congr_ae
              (hreg.residualBudget_eq.mono fun _ h => h.symm)
    _ ≤ 2 * S.γ k * S.sigmaBar k ^ 2 := hcomp

/-- Fixed-time expected descent obtained from current-coordinate process
regularity and the already-proved pathwise/residual/block-factor facts.

The remaining proof leaf is now the source-derived algebraic assembly of:
the product-law transport certificate above, the pathwise one-step descent,
fixed-history residual budget, and the pointwise block-factor lower bound.
Unlike the previous boundary, this theorem's conclusion is not a premise of
`theorem69ExpectationSemanticsWellDefined`.
-/
private theorem theorem69_fixed_time_expected_descent_of_process_regularity
    (S : Setup Ξ ι Block) (N : ℕ) (_hN : 1 ≤ N)
    (k : ℕ) (hk : k ∈ S.outputWindow N)
    (hcurrentReg :
      Nonempty
        (S.Theorem69CurrentCoordinateTransportRegularity k (Finset.mem_Icc.mp hk).1))
    (hresidualReg :
      Nonempty
        (S.Theorem69ResidualBudgetTransportRegularity k (Finset.mem_Icc.mp hk).1))
    (hdrop_int :
      Integrable
        (S.theorem69ObjectiveDropIntegrandAt k (Finset.mem_Icc.mp hk).1)
        S.runLaw)
    (hResidualMean :
      ∀ (t : ℕ) (ht : 1 ≤ t) (blockSample : ℕ → ι) (sample : ℕ → Ξ),
        S.StochasticGradientResidualScalarMeanConditionAtHistory
          t ht blockSample sample)
    (hResidualSecond :
      ∀ (t : ℕ) (ht : 1 ≤ t) (blockSample : ℕ → ι) (sample : ℕ → Ξ),
        S.ExactGradientResidualSecondMomentConditionAtHistory
          t ht blockSample sample)
    (hpathwise_exact :
      ∀ ω : S.RunSample,
        let iω := S.blockIndexProcess ω k
        let xk := S.iterateProcess k (Finset.mem_Icc.mp hk).1 ω
        let epg := S.exactProjectedGradientProcess k (Finset.mem_Icc.mp hk).1 ω
        let δ := S.stochasticGradientResidualProcess k (Finset.mem_Icc.mp hk).1 ω
        (S.γ k / 2) * (1 - S.L iω / 2 * S.γ k) * ‖epg‖ ^ 2 ≤
          S.compositeObjective xk -
            S.compositeObjective
              (S.step k (Finset.mem_Icc.mp hk).1 xk iω (S.oracleSampleProcess ω k)) +
            S.γ k * ⟪δ, epg⟫_ℝ + 2 * S.γ k * ‖δ‖ ^ 2)
    (hcurrent_step_eq :
      ∀ ω : S.RunSample,
        S.step k (Finset.mem_Icc.mp hk).1
            (S.iterateProcess k (Finset.mem_Icc.mp hk).1 ω)
            (S.blockIndexProcess ω k) (S.oracleSampleProcess ω k) =
          S.paperIterate ω.1 ω.2 (k + 1)
            (Nat.succ_le_succ (Nat.zero_le k)))
    (hblockFactorPointwise :
      ∀ ω : S.RunSample,
        S.outputWeight k *
            S.blockNormSq
              (Pi.map
                (fun i yi => S.blockProjectedGradient i
                  (S.paperIterate ω.1 ω.2 k (Finset.mem_Icc.mp hk).1)
                  yi (S.γ k) (S.gamma_pos_obligation k (Finset.mem_Icc.mp hk).1))
                (S.grad (S.paperIterate ω.1 ω.2 k (Finset.mem_Icc.mp hk).1).1)) ≤
          S.γ k *
            ∑ i, S.p i * (1 - (S.L i / 2) * S.γ k) *
              ‖(Pi.map
                  (fun j yj => S.blockProjectedGradient j
                    (S.paperIterate ω.1 ω.2 k (Finset.mem_Icc.mp hk).1)
                    yj (S.γ k) (S.gamma_pos_obligation k (Finset.mem_Icc.mp hk).1))
                  (S.grad (S.paperIterate ω.1 ω.2 k (Finset.mem_Icc.mp hk).1).1) i)‖ ^ 2) :
    (1 / 2 : ℝ) * S.outputWeight k *
        (∫ ω : S.RunSample,
          S.theorem69ExactProjectedGradientNormSqAt k (Finset.mem_Icc.mp hk).1 ω
        ∂S.runLaw) ≤
      (∫ ω : S.RunSample,
        S.theorem69ObjectiveDropIntegrandAt k (Finset.mem_Icc.mp hk).1 ω
      ∂S.runLaw) +
        2 * S.γ k * S.sigmaBar k ^ 2 := by
  classical
  let hk_pos : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  rcases hcurrentReg with ⟨hcurrentReg⟩
  rcases hresidualReg with ⟨hresidualReg⟩
  have hfull_to_selected :
      (1 / 2 : ℝ) * S.outputWeight k *
          (∫ ω : S.RunSample,
            S.theorem69ExactProjectedGradientNormSqAt k hk_pos ω
          ∂S.runLaw) ≤
        ∫ ω : S.RunSample,
          S.theorem69SelectedBlockDescentLhsAt k hk_pos ω ∂S.runLaw :=
    theorem69_full_gradient_lhs_le_selected_block_lhs
      S k hk_pos hcurrentReg hblockFactorPointwise
  have hresidual_budget :=
    theorem69_run_law_residual_budget_of_process_regularity
      S k hk_pos hresidualReg hResidualMean hResidualSecond
  have hselected_point :
      (fun ω : S.RunSample => S.theorem69SelectedBlockDescentLhsAt k hk_pos ω) ≤
        fun ω : S.RunSample =>
          S.theorem69ObjectiveDropIntegrandAt k hk_pos ω +
            S.theorem69ResidualBudgetIntegrandAt k hk_pos ω := by
    intro ω
    have hpath := hpathwise_exact ω
    have hstep := hcurrent_step_eq ω
    dsimp only at hpath
    rw [hstep] at hpath
    simpa [theorem69SelectedBlockDescentLhsAt,
      theorem69ObjectiveDropIntegrandAt, theorem69ResidualBudgetIntegrandAt,
      Setup.iterateProcess, add_assoc] using hpath
  have hselected_rhs_int :
      Integrable
        (fun ω : S.RunSample =>
          S.theorem69ObjectiveDropIntegrandAt k hk_pos ω +
            S.theorem69ResidualBudgetIntegrandAt k hk_pos ω)
        S.runLaw :=
    hdrop_int.add hresidual_budget.1
  have hselected_to_rhs :
      (∫ ω : S.RunSample,
          S.theorem69SelectedBlockDescentLhsAt k hk_pos ω ∂S.runLaw) ≤
        ∫ ω : S.RunSample,
          S.theorem69ObjectiveDropIntegrandAt k hk_pos ω +
            S.theorem69ResidualBudgetIntegrandAt k hk_pos ω ∂S.runLaw :=
    integral_mono hcurrentReg.selectedLhs_integrable hselected_rhs_int hselected_point
  have hsplit :
      (∫ ω : S.RunSample,
          S.theorem69ObjectiveDropIntegrandAt k hk_pos ω +
            S.theorem69ResidualBudgetIntegrandAt k hk_pos ω ∂S.runLaw) =
        (∫ ω : S.RunSample,
          S.theorem69ObjectiveDropIntegrandAt k hk_pos ω ∂S.runLaw) +
          ∫ ω : S.RunSample,
            S.theorem69ResidualBudgetIntegrandAt k hk_pos ω ∂S.runLaw := by
    rw [integral_add hdrop_int hresidual_budget.1]
  calc
    (1 / 2 : ℝ) * S.outputWeight k *
        (∫ ω : S.RunSample,
          S.theorem69ExactProjectedGradientNormSqAt k hk_pos ω
        ∂S.runLaw)
        ≤ ∫ ω : S.RunSample,
            S.theorem69SelectedBlockDescentLhsAt k hk_pos ω ∂S.runLaw :=
          hfull_to_selected
    _ ≤ ∫ ω : S.RunSample,
          S.theorem69ObjectiveDropIntegrandAt k hk_pos ω +
            S.theorem69ResidualBudgetIntegrandAt k hk_pos ω ∂S.runLaw :=
          hselected_to_rhs
    _ = (∫ ω : S.RunSample,
          S.theorem69ObjectiveDropIntegrandAt k hk_pos ω ∂S.runLaw) +
          ∫ ω : S.RunSample,
            S.theorem69ResidualBudgetIntegrandAt k hk_pos ω ∂S.runLaw := hsplit
    _ ≤ (∫ ω : S.RunSample,
          S.theorem69ObjectiveDropIntegrandAt k hk_pos ω ∂S.runLaw) +
          2 * S.γ k * S.sigmaBar k ^ 2 :=
          by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_left hresidual_budget.2
                (∫ ω : S.RunSample,
                  S.theorem69ObjectiveDropIntegrandAt k hk_pos ω ∂S.runLaw)

/-- Canonical current-coordinate process facts for the B-track endpoint.

This interface is the public expectation-semantics boundary used by the
canonical theorem route.  It records only raw process facts and a.e.
identifications: history/current-block measurability, independence, current
block law, product-fiber integrability, and the pointwise identification of the
fiber observable with the generated full-gradient and selected-block terms.
It deliberately does not assume any integrated fixed-time descent or
full-to-selected transport inequality. -/
structure Theorem69CurrentCoordinateProcessSemantics (S : Setup Ξ ι Block)
    (k : ℕ) (hk : 1 ≤ k) where
  History : Type
  historyMeasurable : MeasurableSpace History
  historyKey : S.RunSample → History
  currentBlock : S.RunSample → ι
  blockFiberLhs : History → ι → ℝ
  currentBlock_eq :
    currentBlock = fun ω : S.RunSample => S.blockIndexProcess ω k
  history_aemeasurable :
    letI := historyMeasurable
    AEMeasurable historyKey S.runLaw
  currentBlock_aemeasurable :
    AEMeasurable currentBlock S.runLaw
  currentBlock_independent :
    letI := historyMeasurable
    ProbabilityTheory.IndepFun historyKey currentBlock S.runLaw
  currentBlock_law :
    Measure.map currentBlock S.runLaw = S.blockIndexLaw
  blockIndexLaw_real_singleton :
    ∀ i : ι, S.blockIndexLaw.real ({i} : Set ι) = S.p i
  blockFiber_integrable :
    letI := historyMeasurable
    Integrable (fun z : History × ι => blockFiberLhs z.1 z.2)
      ((Measure.map historyKey S.runLaw).prod S.blockIndexLaw)
  weightedFiber_aestronglyMeasurable :
    letI := historyMeasurable
    AEStronglyMeasurable
      (fun a : History => Finset.univ.sum (fun i : ι => S.p i • blockFiberLhs a i))
      (Measure.map historyKey S.runLaw)
  weightedFiber_integrable :
    Integrable
      (fun ω : S.RunSample =>
        Finset.univ.sum (fun i : ι => S.p i • blockFiberLhs (historyKey ω) i))
      S.runLaw
  selectedLhs_integrable :
    Integrable (S.theorem69SelectedBlockDescentLhsAt k hk) S.runLaw
  fullGradientLhs_integrable :
    Integrable
      (fun ω : S.RunSample =>
        (1 / 2 : ℝ) * S.outputWeight k *
          S.theorem69ExactProjectedGradientNormSqAt k hk ω)
      S.runLaw
  weightedFiber_fullGradient_eq :
    ∀ᵐ ω ∂S.runLaw,
      Finset.univ.sum (fun i : ι => S.p i • blockFiberLhs (historyKey ω) i) =
        (S.γ k / 2) *
          ∑ i, S.p i * (1 - (S.L i / 2) * S.γ k) *
            ‖(Pi.map
                (fun j yj => S.blockProjectedGradient j
                  (S.paperIterate ω.1 ω.2 k hk)
                  yj (S.γ k) (S.gamma_pos_obligation k hk))
                (S.grad (S.paperIterate ω.1 ω.2 k hk).1) i)‖ ^ 2
  sampled_lhs_eq :
    ∀ᵐ ω ∂S.runLaw,
      blockFiberLhs (historyKey ω) (currentBlock ω) =
        S.theorem69SelectedBlockDescentLhsAt k hk ω

/-- Canonical current-sample process facts for the B-track residual-budget
bridge.

The fields expose the generated-current-sample law, independence/adaptedness,
fiber integrability, and a.e. identification with the generated residual-budget
integrand.  The residual moment inequality is proved separately from these
facts and the exact-gradient residual assumptions. -/
structure Theorem69ResidualBudgetProcessSemantics (S : Setup Ξ ι Block)
    (k : ℕ) (hk : 1 ≤ k) where
  History : Type
  historyMeasurable : MeasurableSpace History
  historyKey : S.RunSample → History
  currentSample : S.RunSample → Ξ
  fiberBudget : History → Ξ → ℝ
  historyBlockSample : History → ℕ → ι
  historySample : History → ℕ → Ξ
  historyDirection : (a : History) → Block (historyBlockSample a k)
  currentSample_eq :
    currentSample = fun ω : S.RunSample => S.oracleSampleProcess ω k
  fiberBudget_measurable :
    letI := historyMeasurable
    Measurable (Function.uncurry fiberBudget)
  history_measurable :
    letI := historyMeasurable
    Measurable historyKey
  currentSample_measurable :
    Measurable currentSample
  currentSample_independent :
    letI := historyMeasurable
    ProbabilityTheory.IndepFun historyKey currentSample S.runLaw
  currentSample_law :
    Measure.map currentSample S.runLaw = S.sampleLaw
  composed_integrable :
    Integrable (fun ω : S.RunSample => fiberBudget (historyKey ω) (currentSample ω))
      S.runLaw
  residualBudget_integrable :
    Integrable (S.theorem69ResidualBudgetIntegrandAt k hk) S.runLaw
  fixedFiber_eq :
    ∀ (a : History) (ξ : Ξ),
      fiberBudget a ξ =
        S.γ k *
            ⟪S.stochasticGradientResidualAtHistory k hk
                (historyBlockSample a) (historySample a) ξ,
              historyDirection a⟫_ℝ +
          2 * S.γ k *
            ‖S.stochasticGradientResidualAtHistory k hk
                (historyBlockSample a) (historySample a) ξ‖ ^ 2
  residualBudget_eq :
    ∀ᵐ ω ∂S.runLaw,
      fiberBudget (historyKey ω) (currentSample ω) =
        S.theorem69ResidualBudgetIntegrandAt k hk ω

private theorem theorem69_selected_block_lhs_eq_weighted_fiber_of_process_semantics
    (S : Setup Ξ ι Block) (k : ℕ) (hk : 1 ≤ k)
    (hreg : S.Theorem69CurrentCoordinateProcessSemantics k hk) :
    (∫ ω : S.RunSample,
        S.theorem69SelectedBlockDescentLhsAt k hk ω ∂S.runLaw) =
      ∫ ω : S.RunSample,
        Finset.univ.sum (fun i : ι => S.p i • hreg.blockFiberLhs (hreg.historyKey ω) i)
      ∂S.runLaw := by
  classical
  letI := hreg.historyMeasurable
  haveI : IsProbabilityMeasure S.runLaw := S.runLaw_isProbabilityMeasure
  haveI : IsFiniteMeasure S.runLaw := inferInstance
  have htransport :
      (∫ ω : S.RunSample,
          hreg.blockFiberLhs (hreg.historyKey ω) (hreg.currentBlock ω)
        ∂S.runLaw) =
        ∫ ω : S.RunSample,
          Finset.univ.sum (fun i : ι => S.p i • hreg.blockFiberLhs (hreg.historyKey ω) i)
        ∂S.runLaw :=
    expectation_sample_eq_expectation_weighted_fiber_sum_of_indepFun
      (P := S.runLaw) (W := hreg.historyKey) (Y := hreg.currentBlock)
      (nu := S.blockIndexLaw) (w := S.p)
      (F := hreg.blockFiberLhs)
      hreg.history_aemeasurable hreg.currentBlock_aemeasurable
      hreg.currentBlock_independent hreg.currentBlock_law
      hreg.blockIndexLaw_real_singleton hreg.blockFiber_integrable
  have hleft :
      (∫ ω : S.RunSample,
          S.theorem69SelectedBlockDescentLhsAt k hk ω ∂S.runLaw) =
        ∫ ω : S.RunSample,
          hreg.blockFiberLhs (hreg.historyKey ω) (hreg.currentBlock ω)
        ∂S.runLaw := by
    exact integral_congr_ae
      (hreg.sampled_lhs_eq.mono fun _ h => h.symm)
  calc
    (∫ ω : S.RunSample,
        S.theorem69SelectedBlockDescentLhsAt k hk ω ∂S.runLaw)
        = ∫ ω : S.RunSample,
            hreg.blockFiberLhs (hreg.historyKey ω) (hreg.currentBlock ω)
          ∂S.runLaw := hleft
    _ = ∫ ω : S.RunSample,
          Finset.univ.sum (fun i : ι => S.p i • hreg.blockFiberLhs (hreg.historyKey ω) i)
        ∂S.runLaw := htransport

private theorem theorem69_full_gradient_lhs_le_selected_block_lhs_of_process_semantics
    (S : Setup Ξ ι Block) (k : ℕ) (hk : 1 ≤ k)
    (hreg : S.Theorem69CurrentCoordinateProcessSemantics k hk)
    (hblockFactorPointwise :
      ∀ ω : S.RunSample,
        S.outputWeight k *
            S.blockNormSq
              (Pi.map
                (fun i yi => S.blockProjectedGradient i
                  (S.paperIterate ω.1 ω.2 k hk)
                  yi (S.γ k) (S.gamma_pos_obligation k hk))
                (S.grad (S.paperIterate ω.1 ω.2 k hk).1)) ≤
          S.γ k *
            ∑ i, S.p i * (1 - (S.L i / 2) * S.γ k) *
              ‖(Pi.map
                  (fun j yj => S.blockProjectedGradient j
                    (S.paperIterate ω.1 ω.2 k hk)
                    yj (S.γ k) (S.gamma_pos_obligation k hk))
                  (S.grad (S.paperIterate ω.1 ω.2 k hk).1) i)‖ ^ 2) :
    (1 / 2 : ℝ) * S.outputWeight k *
        (∫ ω : S.RunSample,
          S.theorem69ExactProjectedGradientNormSqAt k hk ω ∂S.runLaw) ≤
      ∫ ω : S.RunSample,
        S.theorem69SelectedBlockDescentLhsAt k hk ω ∂S.runLaw := by
  classical
  let weightedFiber : S.RunSample → ℝ := fun ω =>
    Finset.univ.sum (fun i : ι => S.p i • hreg.blockFiberLhs (hreg.historyKey ω) i)
  have hweighted_eq_selected :
      (∫ ω : S.RunSample, weightedFiber ω ∂S.runLaw) =
        ∫ ω : S.RunSample,
          S.theorem69SelectedBlockDescentLhsAt k hk ω ∂S.runLaw := by
    exact (theorem69_selected_block_lhs_eq_weighted_fiber_of_process_semantics
      S k hk hreg).symm
  have hpoint :
      (fun ω : S.RunSample =>
        (1 / 2 : ℝ) * S.outputWeight k *
          S.theorem69ExactProjectedGradientNormSqAt k hk ω) ≤ᵐ[S.runLaw]
        weightedFiber := by
    filter_upwards [hreg.weightedFiber_fullGradient_eq] with ω hω
    have hbf := hblockFactorPointwise ω
    have hhalf :=
      mul_le_mul_of_nonneg_left hbf (by norm_num : (0 : ℝ) ≤ 1 / 2)
    calc
      (1 / 2 : ℝ) * S.outputWeight k *
          S.theorem69ExactProjectedGradientNormSqAt k hk ω
          ≤ (1 / 2 : ℝ) *
              (S.γ k *
                ∑ i, S.p i * (1 - (S.L i / 2) * S.γ k) *
                  ‖(Pi.map
                      (fun j yj => S.blockProjectedGradient j
                        (S.paperIterate ω.1 ω.2 k hk)
                        yj (S.γ k) (S.gamma_pos_obligation k hk))
                      (S.grad (S.paperIterate ω.1 ω.2 k hk).1) i)‖ ^ 2) := by
            simpa [theorem69ExactProjectedGradientNormSqAt, mul_assoc]
              using hhalf
      _ = weightedFiber ω := by
            calc
              (1 / 2 : ℝ) *
                  (S.γ k *
                    ∑ i, S.p i * (1 - (S.L i / 2) * S.γ k) *
                      ‖(Pi.map
                          (fun j yj => S.blockProjectedGradient j
                            (S.paperIterate ω.1 ω.2 k hk)
                            yj (S.γ k) (S.gamma_pos_obligation k hk))
                          (S.grad (S.paperIterate ω.1 ω.2 k hk).1) i)‖ ^ 2)
                  =
                (S.γ k / 2) *
                  ∑ i, S.p i * (1 - (S.L i / 2) * S.γ k) *
                    ‖(Pi.map
                        (fun j yj => S.blockProjectedGradient j
                          (S.paperIterate ω.1 ω.2 k hk)
                          yj (S.γ k) (S.gamma_pos_obligation k hk))
                        (S.grad (S.paperIterate ω.1 ω.2 k hk).1) i)‖ ^ 2 := by
                    ring
              _ = weightedFiber ω := hω.symm
  have hmono :
      ∫ ω : S.RunSample,
          (1 / 2 : ℝ) * S.outputWeight k *
            S.theorem69ExactProjectedGradientNormSqAt k hk ω ∂S.runLaw ≤
        ∫ ω : S.RunSample, weightedFiber ω ∂S.runLaw :=
    integral_mono_ae hreg.fullGradientLhs_integrable hreg.weightedFiber_integrable hpoint
  have hleft :
      (∫ ω : S.RunSample,
          (1 / 2 : ℝ) * S.outputWeight k *
            S.theorem69ExactProjectedGradientNormSqAt k hk ω ∂S.runLaw) =
        (1 / 2 : ℝ) * S.outputWeight k *
          (∫ ω : S.RunSample,
            S.theorem69ExactProjectedGradientNormSqAt k hk ω ∂S.runLaw) := by
    simpa [mul_assoc] using
      (integral_const_mul
        (μ := S.runLaw) (r := (1 / 2 : ℝ) * S.outputWeight k)
        (f := fun ω : S.RunSample =>
          S.theorem69ExactProjectedGradientNormSqAt k hk ω))
  calc
    (1 / 2 : ℝ) * S.outputWeight k *
        (∫ ω : S.RunSample,
          S.theorem69ExactProjectedGradientNormSqAt k hk ω ∂S.runLaw)
        = ∫ ω : S.RunSample,
            (1 / 2 : ℝ) * S.outputWeight k *
              S.theorem69ExactProjectedGradientNormSqAt k hk ω ∂S.runLaw := hleft.symm
    _ ≤ ∫ ω : S.RunSample, weightedFiber ω ∂S.runLaw := hmono
    _ = ∫ ω : S.RunSample,
          S.theorem69SelectedBlockDescentLhsAt k hk ω ∂S.runLaw := hweighted_eq_selected

private theorem theorem69_run_law_residual_budget_of_process_semantics
    (S : Setup Ξ ι Block) (k : ℕ) (hk : 1 ≤ k)
    (hreg : S.Theorem69ResidualBudgetProcessSemantics k hk)
    (hResidualMean :
      ∀ (t : ℕ) (ht : 1 ≤ t) (blockSample : ℕ → ι) (sample : ℕ → Ξ),
        S.StochasticGradientResidualScalarMeanConditionAtHistory
          t ht blockSample sample)
    (hResidualSecond :
      ∀ (t : ℕ) (ht : 1 ≤ t) (blockSample : ℕ → ι) (sample : ℕ → Ξ),
        S.ExactGradientResidualSecondMomentConditionAtHistory
          t ht blockSample sample) :
    Integrable (S.theorem69ResidualBudgetIntegrandAt k hk) S.runLaw ∧
      (∫ ω : S.RunSample,
        S.theorem69ResidualBudgetIntegrandAt k hk ω ∂S.runLaw) ≤
        2 * S.γ k * S.sigmaBar k ^ 2 := by
  classical
  letI := hreg.historyMeasurable
  haveI : IsProbabilityMeasure S.runLaw := S.runLaw_isProbabilityMeasure
  haveI : IsProbabilityMeasure S.sampleLaw := S.sampleLaw_prob
  have hfixed :
      ∀ a : hreg.History,
        (∫ ξ, hreg.fiberBudget a ξ ∂S.sampleLaw) ≤
          2 * S.γ k * S.sigmaBar k ^ 2 := by
    intro a
    have hbudget :=
      (theorem69_fixed_history_residual_budget_integral
        S hResidualMean hResidualSecond k hk
        (hreg.historyBlockSample a) (hreg.historySample a)
        (hreg.historyDirection a)).2
    simpa [hreg.fixedFiber_eq a] using hbudget
  have hcomp :
      (∫ ω : S.RunSample,
          hreg.fiberBudget (hreg.historyKey ω) (hreg.currentSample ω)
        ∂S.runLaw) ≤
        2 * S.γ k * S.sigmaBar k ^ 2 :=
    integral_comp_le_of_indep_fixed_integral_bound
      (P := S.runLaw) (ν := S.sampleLaw)
      (φ := hreg.fiberBudget) (X := hreg.historyKey) (Y := hreg.currentSample)
      (C := 2 * S.γ k * S.sigmaBar k ^ 2)
      hreg.fiberBudget_measurable hreg.history_measurable
      hreg.currentSample_measurable hreg.currentSample_independent
      hreg.currentSample_law hreg.composed_integrable hfixed
  refine ⟨hreg.residualBudget_integrable, ?_⟩
  calc
    (∫ ω : S.RunSample,
        S.theorem69ResidualBudgetIntegrandAt k hk ω ∂S.runLaw)
        = ∫ ω : S.RunSample,
            hreg.fiberBudget (hreg.historyKey ω) (hreg.currentSample ω)
          ∂S.runLaw := by
            exact integral_congr_ae
              (hreg.residualBudget_eq.mono fun _ h => h.symm)
    _ ≤ 2 * S.γ k * S.sigmaBar k ^ 2 := hcomp

private theorem theorem69_fixed_time_expected_descent_of_process_semantics
    (S : Setup Ξ ι Block) (N : ℕ) (_hN : 1 ≤ N)
    (k : ℕ) (hk : k ∈ S.outputWindow N)
    (hcurrentReg :
      Nonempty
        (S.Theorem69CurrentCoordinateProcessSemantics k (Finset.mem_Icc.mp hk).1))
    (hresidualReg :
      Nonempty
        (S.Theorem69ResidualBudgetProcessSemantics k (Finset.mem_Icc.mp hk).1))
    (hdrop_int :
      Integrable
        (S.theorem69ObjectiveDropIntegrandAt k (Finset.mem_Icc.mp hk).1)
        S.runLaw)
    (hResidualMean :
      ∀ (t : ℕ) (ht : 1 ≤ t) (blockSample : ℕ → ι) (sample : ℕ → Ξ),
        S.StochasticGradientResidualScalarMeanConditionAtHistory
          t ht blockSample sample)
    (hResidualSecond :
      ∀ (t : ℕ) (ht : 1 ≤ t) (blockSample : ℕ → ι) (sample : ℕ → Ξ),
        S.ExactGradientResidualSecondMomentConditionAtHistory
          t ht blockSample sample)
    (hpathwise_exact :
      ∀ ω : S.RunSample,
        let iω := S.blockIndexProcess ω k
        let xk := S.iterateProcess k (Finset.mem_Icc.mp hk).1 ω
        let epg := S.exactProjectedGradientProcess k (Finset.mem_Icc.mp hk).1 ω
        let δ := S.stochasticGradientResidualProcess k (Finset.mem_Icc.mp hk).1 ω
        (S.γ k / 2) * (1 - S.L iω / 2 * S.γ k) * ‖epg‖ ^ 2 ≤
          S.compositeObjective xk -
            S.compositeObjective
              (S.step k (Finset.mem_Icc.mp hk).1 xk iω (S.oracleSampleProcess ω k)) +
            S.γ k * ⟪δ, epg⟫_ℝ + 2 * S.γ k * ‖δ‖ ^ 2)
    (hcurrent_step_eq :
      ∀ ω : S.RunSample,
        S.step k (Finset.mem_Icc.mp hk).1
            (S.iterateProcess k (Finset.mem_Icc.mp hk).1 ω)
            (S.blockIndexProcess ω k) (S.oracleSampleProcess ω k) =
          S.paperIterate ω.1 ω.2 (k + 1)
            (Nat.succ_le_succ (Nat.zero_le k)))
    (hblockFactorPointwise :
      ∀ ω : S.RunSample,
        S.outputWeight k *
            S.blockNormSq
              (Pi.map
                (fun i yi => S.blockProjectedGradient i
                  (S.paperIterate ω.1 ω.2 k (Finset.mem_Icc.mp hk).1)
                  yi (S.γ k) (S.gamma_pos_obligation k (Finset.mem_Icc.mp hk).1))
                (S.grad (S.paperIterate ω.1 ω.2 k (Finset.mem_Icc.mp hk).1).1)) ≤
          S.γ k *
            ∑ i, S.p i * (1 - (S.L i / 2) * S.γ k) *
              ‖(Pi.map
                  (fun j yj => S.blockProjectedGradient j
                    (S.paperIterate ω.1 ω.2 k (Finset.mem_Icc.mp hk).1)
                    yj (S.γ k) (S.gamma_pos_obligation k (Finset.mem_Icc.mp hk).1))
                  (S.grad (S.paperIterate ω.1 ω.2 k (Finset.mem_Icc.mp hk).1).1) i)‖ ^ 2) :
    (1 / 2 : ℝ) * S.outputWeight k *
        (∫ ω : S.RunSample,
          S.theorem69ExactProjectedGradientNormSqAt k (Finset.mem_Icc.mp hk).1 ω
        ∂S.runLaw) ≤
      (∫ ω : S.RunSample,
        S.theorem69ObjectiveDropIntegrandAt k (Finset.mem_Icc.mp hk).1 ω
      ∂S.runLaw) +
        2 * S.γ k * S.sigmaBar k ^ 2 := by
  classical
  let hk_pos : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  rcases hcurrentReg with ⟨hcurrentReg⟩
  rcases hresidualReg with ⟨hresidualReg⟩
  have hfull_to_selected :
      (1 / 2 : ℝ) * S.outputWeight k *
          (∫ ω : S.RunSample,
            S.theorem69ExactProjectedGradientNormSqAt k hk_pos ω
          ∂S.runLaw) ≤
        ∫ ω : S.RunSample,
          S.theorem69SelectedBlockDescentLhsAt k hk_pos ω ∂S.runLaw :=
    theorem69_full_gradient_lhs_le_selected_block_lhs_of_process_semantics
      S k hk_pos hcurrentReg hblockFactorPointwise
  have hresidual_budget :=
    theorem69_run_law_residual_budget_of_process_semantics
      S k hk_pos hresidualReg hResidualMean hResidualSecond
  have hselected_point :
      (fun ω : S.RunSample => S.theorem69SelectedBlockDescentLhsAt k hk_pos ω) ≤
        fun ω : S.RunSample =>
          S.theorem69ObjectiveDropIntegrandAt k hk_pos ω +
            S.theorem69ResidualBudgetIntegrandAt k hk_pos ω := by
    intro ω
    have hpath := hpathwise_exact ω
    have hstep := hcurrent_step_eq ω
    dsimp only at hpath
    rw [hstep] at hpath
    simpa [theorem69SelectedBlockDescentLhsAt,
      theorem69ObjectiveDropIntegrandAt, theorem69ResidualBudgetIntegrandAt,
      Setup.iterateProcess, add_assoc] using hpath
  have hselected_rhs_int :
      Integrable
        (fun ω : S.RunSample =>
          S.theorem69ObjectiveDropIntegrandAt k hk_pos ω +
            S.theorem69ResidualBudgetIntegrandAt k hk_pos ω)
        S.runLaw :=
    hdrop_int.add hresidual_budget.1
  have hselected_to_rhs :
      (∫ ω : S.RunSample,
          S.theorem69SelectedBlockDescentLhsAt k hk_pos ω ∂S.runLaw) ≤
        ∫ ω : S.RunSample,
          S.theorem69ObjectiveDropIntegrandAt k hk_pos ω +
            S.theorem69ResidualBudgetIntegrandAt k hk_pos ω ∂S.runLaw :=
    integral_mono hcurrentReg.selectedLhs_integrable hselected_rhs_int hselected_point
  have hsplit :
      (∫ ω : S.RunSample,
          S.theorem69ObjectiveDropIntegrandAt k hk_pos ω +
            S.theorem69ResidualBudgetIntegrandAt k hk_pos ω ∂S.runLaw) =
        (∫ ω : S.RunSample,
          S.theorem69ObjectiveDropIntegrandAt k hk_pos ω ∂S.runLaw) +
          ∫ ω : S.RunSample,
            S.theorem69ResidualBudgetIntegrandAt k hk_pos ω ∂S.runLaw := by
    rw [integral_add hdrop_int hresidual_budget.1]
  calc
    (1 / 2 : ℝ) * S.outputWeight k *
        (∫ ω : S.RunSample,
          S.theorem69ExactProjectedGradientNormSqAt k hk_pos ω
        ∂S.runLaw)
        ≤ ∫ ω : S.RunSample,
            S.theorem69SelectedBlockDescentLhsAt k hk_pos ω ∂S.runLaw :=
          hfull_to_selected
    _ ≤ ∫ ω : S.RunSample,
          S.theorem69ObjectiveDropIntegrandAt k hk_pos ω +
            S.theorem69ResidualBudgetIntegrandAt k hk_pos ω ∂S.runLaw :=
          hselected_to_rhs
    _ = (∫ ω : S.RunSample,
          S.theorem69ObjectiveDropIntegrandAt k hk_pos ω ∂S.runLaw) +
          ∫ ω : S.RunSample,
            S.theorem69ResidualBudgetIntegrandAt k hk_pos ω ∂S.runLaw := hsplit
    _ ≤ (∫ ω : S.RunSample,
          S.theorem69ObjectiveDropIntegrandAt k hk_pos ω ∂S.runLaw) +
          2 * S.γ k * S.sigmaBar k ^ 2 :=
          by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_left hresidual_budget.2
                (∫ ω : S.RunSample,
                  S.theorem69ObjectiveDropIntegrandAt k hk_pos ω ∂S.runLaw)

/-- Objective-drop integrability needed for the expected telescope in
Theorem 6.9 proof steps 13-14 and 22. -/
def theorem69ObjectiveDropIntegrable (S : Setup Ξ ι Block)
    (N : ℕ) (_hN : 1 ≤ N) : Prop :=
  ∀ (k : ℕ) (hk : k ∈ S.outputWindow N),
    Integrable
      (S.theorem69ObjectiveDropIntegrandAt k (Finset.mem_Icc.mp hk).1)
      S.runLaw

/-- Minimal fixed-time process semantics needed by the B-track Theorem 6.9
route.

This interface exposes only raw stochastic-process facts for each output-window
time: current-coordinate process semantics and current-sample residual process
semantics.  The integrated full-to-selected transport inequality and the
residual-budget moment bound are private derived consequences, not fields of
this public predicate. -/
def theorem69FixedTimeProcessSemantics (S : Setup Ξ ι Block)
    (N : ℕ) (_hN : 1 ≤ N) : Prop :=
  ∀ (k : ℕ) (hk : k ∈ S.outputWindow N) (hk_pos : 1 ≤ k),
    Nonempty (S.Theorem69CurrentCoordinateProcessSemantics k hk_pos) ∧
      Nonempty (S.Theorem69ResidualBudgetProcessSemantics k hk_pos)

/-- Nonfallback expectation semantics for Theorem 6.9 with a supplied output
law.  The PDF states that expectation is taken with respect to `i_k`, `G_{i_k}`,
and `R`, but does not separately state the Lean measurability/integrability
facts needed for Bochner expectation semantics.  Besides the selected-output
integrand, the proof also needs fixed-time process semantics and objective-drop
integrability for the expected telescope. -/
def theorem69ExpectationSemanticsWellDefined (S : Setup Ξ ι Block)
    (N : ℕ) (hN : 1 ≤ N) (Rlaw : PMF {k : ℕ // k ∈ S.outputWindow N}) : Prop :=
  SOptLib.expectationWellDefined (Rlaw.toMeasure.prod S.runLaw)
    (S.theorem69IntegrandWithLaw N hN) ∧
  S.theorem69FixedTimeProcessSemantics N hN ∧
  S.theorem69ObjectiveDropIntegrable N hN

/-- Source-boundary record for the expectation in Theorem 6.9.

This is the Lean realization question for the phrase "expectation is taken
with respect to `i_k`, `G_{i_k}`, and `R`".  The paper does not state the
measurability/integrability facts needed to prove it for the generated process,
so no source-facing theorem in this file assumes or asserts it unconditionally.
-/
def theorem69ExpectationSourceBoundary (S : Setup Ξ ι Block)
    (N : ℕ) (hN : 1 ≤ N) : Prop :=
  ∃ Rlaw : PMF {k : ℕ // k ∈ S.outputWindow N},
    S.OutputLawSpec N Rlaw ∧
      S.theorem69ExpectationSemanticsWellDefined N hN Rlaw

/-- Conditional PMF-realized left-hand expression for extension lemmas that
start from an explicit finite-weight admissibility certificate. -/
noncomputable def outputExpectedSquaredProjectedGradientOfAdmissible
    (S : Setup Ξ ι Block) (N : ℕ) (hN : 1 ≤ N)
    (hweights : S.outputWeightsAdmissible N) : ℝ :=
  ∫ q, S.theorem69IntegrandWithLaw N hN q
    ∂((S.randomOutputLawOfAdmissible N hweights).toMeasure.prod S.runLaw)

/-- Extension-level Theorem 6.9 left-hand expression:
`E[‖P_X(x_R,g(x_R),γ_R)‖²]`, with expectation over block sampling, oracle
randomness, and an externally supplied output PMF.
-/
noncomputable def theorem69LHSWithLaw (S : Setup Ξ ι Block)
    (N : ℕ) (hN : 1 ≤ N) (Rlaw : PMF {k : ℕ // k ∈ S.outputWindow N}) : ℝ :=
  ∫ q, S.theorem69IntegrandWithLaw N hN q
    ∂(Rlaw.toMeasure.prod S.runLaw)

/-- Formal finite-weight expression corresponding to the Eq. (6.3.14) output
mass formula.  This quotient is not used to masquerade as a PMF expectation
when output-law well-definedness has not been established. -/
noncomputable def theorem69FormalWeightedLHS (S : Setup Ξ ι Block)
    (N : ℕ) (_hN : 1 ≤ N) : ℝ :=
  Finset.sum (S.outputWindow N).attach (fun R =>
      S.outputMass N R *
        S.runExpectedSquaredProjectedGradientAt R.1 (Finset.mem_Icc.mp R.2).1)

/-- Zero-atom-safe selector-first product integral expansion over a finite
selector space.  Unlike the older fiberwise expansion API, this only requires
integrability of the selected product integrand; fibers at zero-mass selector
atoms may be nonintegrable because their Bochner integrals are multiplied by
zero in the finite outer integral. -/
private theorem finite_selector_first_product_integral_eq_weighted_sum_of_integrable
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [Fintype α] [MeasurableSingletonClass α]
    (ν : Measure α) (μ : Measure Ω) [SFinite μ] [IsFiniteMeasure ν]
    (F : α → Ω → ℝ)
    (hF : Integrable (fun q : α × Ω => F q.1 q.2) (ν.prod μ)) :
    ∫ q : α × Ω, F q.1 q.2 ∂(ν.prod μ) =
      ∑ a : α, ν.real ({a} : Set α) * ∫ ω, F a ω ∂μ := by
  simpa [smul_eq_mul] using
    (integral_finite_selector_first_prod_eq_sum_of_integrable
      (ν := ν) (μ := μ) (F := F) hF)

/-- The selected-output expectation in Theorem 6.9 expands to the formal
finite weighted expression determined by the displayed output law. -/
private theorem theorem69_lhsWithLaw_eq_formalWeightedLHS
    (S : Setup Ξ ι Block) (N : ℕ) (hN : 1 ≤ N)
    (Rlaw : PMF {k : ℕ // k ∈ S.outputWindow N})
    (hRlaw : S.OutputLawSpec N Rlaw)
    (hExpectation : S.theorem69ExpectationSemanticsWellDefined N hN Rlaw) :
    S.theorem69LHSWithLaw N hN Rlaw =
      S.theorem69FormalWeightedLHS N hN := by
  classical
  let F : {k : ℕ // k ∈ S.outputWindow N} → S.RunSample → ℝ :=
    fun R ω => S.theorem69IntegrandWithLaw N hN (R, ω)
  have hInt :
      Integrable (fun q : {k : ℕ // k ∈ S.outputWindow N} × S.RunSample =>
        F q.1 q.2) (Rlaw.toMeasure.prod S.runLaw) := by
    have hInt0 :
        Integrable (S.theorem69IntegrandWithLaw N hN)
          (Rlaw.toMeasure.prod S.runLaw) :=
      (SOptLib.expectationWellDefined_iff_integrable
        (Rlaw.toMeasure.prod S.runLaw)
        (S.theorem69IntegrandWithLaw N hN)).mp hExpectation.1
    simpa [F] using hInt0
  have hExpand :
      ∫ q : {k : ℕ // k ∈ S.outputWindow N} × S.RunSample,
          F q.1 q.2 ∂(Rlaw.toMeasure.prod S.runLaw) =
        ∑ R : {k : ℕ // k ∈ S.outputWindow N},
          Rlaw.toMeasure.real ({R} : Set {k : ℕ // k ∈ S.outputWindow N}) *
            ∫ ω : S.RunSample, F R ω ∂S.runLaw :=
    haveI : IsProbabilityMeasure S.runLaw := S.runLaw_isProbabilityMeasure
    haveI : SFinite S.runLaw := inferInstance
    finite_selector_first_product_integral_eq_weighted_sum_of_integrable
      (ν := Rlaw.toMeasure) (μ := S.runLaw) (F := F) hInt
  have hAtom := S.outputLawSpec_real_singleton N Rlaw hRlaw
  calc
    S.theorem69LHSWithLaw N hN Rlaw
        = ∫ q : {k : ℕ // k ∈ S.outputWindow N} × S.RunSample,
            F q.1 q.2 ∂(Rlaw.toMeasure.prod S.runLaw) := by
            rfl
    _ = ∑ R : {k : ℕ // k ∈ S.outputWindow N},
          Rlaw.toMeasure.real ({R} : Set {k : ℕ // k ∈ S.outputWindow N}) *
            ∫ ω : S.RunSample, F R ω ∂S.runLaw := hExpand
    _ = S.theorem69FormalWeightedLHS N hN := by
      simp [theorem69FormalWeightedLHS, runExpectedSquaredProjectedGradientAt,
        theorem69IntegrandWithLaw, randomOutput, F, hAtom]

/-- Right-hand quotient from Theorem 6.9 / Eq. (6.3.20).

The denominator is the same normalizing denominator as Eq. (6.3.14).  Positivity
is not asserted here; the quotient is the source expression, and PMF realization
is handled only by conditional declarations requiring admissible weights.
-/
noncomputable def theorem69RHS (S : Setup Ξ ι Block) (N : ℕ) : ℝ :=
  (S.compositeObjective S.x₁Carrier - S.phiStar +
      2 * Finset.sum (S.outputWindow N) (fun k => S.γ k * S.sigmaBar k ^ 2)) /
    S.outputDenominator N

/-- Aggregate fixed-time expected half-bounds and an objective-drop telescope
into the unnormalized half-weighted estimate used in Theorem 6.9. -/
private theorem theorem69_weighted_descent_telescope_bound_of_fixed_step
    (S : Setup Ξ ι Block) (N : ℕ) (_hN : 1 ≤ N)
    (drop : ℕ → ℝ)
    (hstep :
      ∀ (k : ℕ) (hk : k ∈ S.outputWindow N),
        (1 / 2 : ℝ) * S.outputWeight k *
            S.runExpectedSquaredProjectedGradientAt k (Finset.mem_Icc.mp hk).1 ≤
          drop k + 2 * S.γ k * S.sigmaBar k ^ 2)
    (htelescope :
      Finset.sum (S.outputWindow N) drop ≤
        S.compositeObjective S.x₁Carrier - S.phiStar) :
    (1 / 2 : ℝ) *
        Finset.sum (S.outputWindow N).attach (fun R =>
          S.outputWeight R.1 *
            S.runExpectedSquaredProjectedGradientAt R.1
              (Finset.mem_Icc.mp R.2).1) ≤
      S.compositeObjective S.x₁Carrier - S.phiStar +
        2 * Finset.sum (S.outputWindow N) (fun k =>
          S.γ k * S.sigmaBar k ^ 2) := by
  classical
  have hbound :
      (1 / 2 : ℝ) *
          Finset.sum (S.outputWindow N).attach (fun R =>
            S.outputWeight R.1 *
              S.runExpectedSquaredProjectedGradientAt R.1
                (Finset.mem_Icc.mp R.2).1) ≤
        S.compositeObjective S.x₁Carrier - S.phiStar +
          Finset.sum (S.outputWindow N).attach (fun R =>
            2 * (S.γ R.1 * S.sigmaBar R.1 ^ 2)) := by
    simpa [Finset.mul_sum, mul_assoc] using
      (SOptLib.finset_const_mul_sum_le_telescope_add_sum_of_pointwise_le
        (s := (S.outputWindow N).attach)
        (c := (1 / 2 : ℝ))
        (budget := S.compositeObjective S.x₁Carrier - S.phiStar)
        (gap := fun R : {k : ℕ // k ∈ S.outputWindow N} =>
          S.outputWeight R.1 *
            S.runExpectedSquaredProjectedGradientAt R.1
              (Finset.mem_Icc.mp R.2).1)
        (drop := fun R : {k : ℕ // k ∈ S.outputWindow N} => drop R.1)
        (noise := fun R : {k : ℕ // k ∈ S.outputWindow N} =>
          2 * (S.γ R.1 * S.sigmaBar R.1 ^ 2))
        (hpoint := by
          intro R _hR
          simpa [mul_assoc] using hstep R.1 R.2)
        (hdrop := by
          simpa [Finset.sum_attach] using htelescope))
  have hnoise :
      Finset.sum (S.outputWindow N).attach (fun R =>
          2 * (S.γ R.1 * S.sigmaBar R.1 ^ 2)) =
        2 * Finset.sum (S.outputWindow N) (fun k =>
          S.γ k * S.sigmaBar k ^ 2) := by
    calc
      Finset.sum (S.outputWindow N).attach (fun R =>
          2 * (S.γ R.1 * S.sigmaBar R.1 ^ 2))
          =
        Finset.sum (S.outputWindow N) (fun k =>
          2 * (S.γ k * S.sigmaBar k ^ 2)) := by
            simpa using
              (Finset.sum_attach (s := S.outputWindow N)
                (f := fun k => 2 * (S.γ k * S.sigmaBar k ^ 2)))
      _ = 2 * Finset.sum (S.outputWindow N) (fun k =>
            S.γ k * S.sigmaBar k ^ 2) := by
            rw [Finset.mul_sum]
  simpa [hnoise] using hbound

/-- Corrected exact-gradient residual assumptions used by the B-track Theorem
6.9 route.  These disclose the two proof-side residual facts that the source
does not derive from its `g(x_k)`-centered stochastic-gradient condition. -/
def theorem69ExactGradientResidualAssumptions (S : Setup Ξ ι Block) : Prop :=
  (∀ (k : ℕ) (hk : 1 ≤ k) (blockSample : ℕ → ι) (sample : ℕ → Ξ),
    S.StochasticGradientResidualScalarMeanConditionAtHistory
      k hk blockSample sample) ∧
  (∀ (k : ℕ) (hk : 1 ≤ k) (blockSample : ℕ → ι) (sample : ℕ → Ξ),
    S.ExactGradientResidualSecondMomentConditionAtHistory
      k hk blockSample sample)

/-- Proof-source boundary for the Theorem 6.9 argument before output-law and
final-expectation realization.  It records only the source stochastic condition
and explicit corrected exact-gradient residual facts; the generated step
supplies the prox displacement identity directly, and the disputed no-half
factor-two jump is intentionally not part of this boundary. -/
def theorem69ProofSourceBoundary (S : Setup Ξ ι Block)
    (_N : ℕ) (_hN : 1 ≤ _N) : Prop :=
  S.StochasticGradientCondition ∧
    S.theorem69ExactGradientResidualAssumptions

/-- Corrected source-boundary contract for Theorem 6.9 / Eq. (6.3.20).

This is the B-track boundary for the paper theorem.  It preserves the source
stochastic-gradient condition Eq. (6.3.12), records the proof-side corrected
exact-gradient residual assumptions, and carries a single output-law witness
used for the displayed Eq. (6.3.14) masses and the nonfallback Bochner
expectation.
-/
def theorem69CorrectedSourceBoundary (S : Setup Ξ ι Block)
    (N : ℕ) (hN : 1 ≤ N) : Prop :=
  S.StochasticGradientCondition ∧
    S.theorem69ExactGradientResidualAssumptions ∧
      ∃ Rlaw : PMF {k : ℕ // k ∈ S.outputWindow N},
        S.OutputLawSpec N Rlaw ∧
          S.theorem69ExpectationSemanticsWellDefined N hN Rlaw

/-- Extension-level arbitrary-output-law version of the corrected Theorem 6.9
bound.

This is not the paper-facing theorem: it keeps the external PMF/spec and
expectation-realization interface separate from the paper source boundary.
-/
private theorem theorem69Bound_with_output_law_extension (S : Setup Ξ ι Block)
    (N : ℕ) (hN : 1 ≤ N)
    (hG : S.StochasticGradientCondition)
    (hResidual : S.theorem69ExactGradientResidualAssumptions)
    (Rlaw : PMF {k : ℕ // k ∈ S.outputWindow N})
    (_hRlaw : S.OutputLawSpec N Rlaw)
    (_hExpectation : S.theorem69ExpectationSemanticsWellDefined N hN Rlaw) :
    (1 / 2 : ℝ) * S.theorem69LHSWithLaw N hN Rlaw ≤ S.theorem69RHS N := by
  have hLHS :
      S.theorem69LHSWithLaw N hN Rlaw =
        S.theorem69FormalWeightedLHS N hN :=
    theorem69_lhsWithLaw_eq_formalWeightedLHS S N hN Rlaw _hRlaw _hExpectation
  have hhalf :
      (1 / 2 : ℝ) * S.theorem69FormalWeightedLHS N hN ≤
        S.theorem69RHS N := by
    rcases hResidual with ⟨hResidualMean, hResidualSecond⟩
    have hden_pos : 0 < S.outputDenominator N :=
      S.outputDenominator_pos_of_outputLawSpec N Rlaw _hRlaw
    have hweighted :
        (1 / 2 : ℝ) *
            Finset.sum (S.outputWindow N).attach (fun R =>
              S.outputWeight R.1 *
                S.runExpectedSquaredProjectedGradientAt R.1
                  (Finset.mem_Icc.mp R.2).1) ≤
          S.compositeObjective S.x₁Carrier - S.phiStar +
            2 * Finset.sum (S.outputWindow N) (fun k =>
              S.γ k * S.sigmaBar k ^ 2) := by
      classical
      let dropIntegrand : ℕ → S.RunSample → ℝ := fun k ω =>
        if hk : k ∈ S.outputWindow N then
          S.compositeObjective
              (S.paperIterate ω.1 ω.2 k (Finset.mem_Icc.mp hk).1) -
            S.compositeObjective
              (S.paperIterate ω.1 ω.2 (k + 1)
                (Nat.succ_le_succ (Nat.zero_le k)))
        else 0
      let drop : ℕ → ℝ := fun k => ∫ ω : S.RunSample, dropIntegrand k ω ∂S.runLaw
      have hstep :
          ∀ (k : ℕ) (hk : k ∈ S.outputWindow N),
            (1 / 2 : ℝ) * S.outputWeight k *
                S.runExpectedSquaredProjectedGradientAt k (Finset.mem_Icc.mp hk).1 ≤
              drop k + 2 * S.γ k * S.sigmaBar k ^ 2 := by
        intro k hk
        have hk_pos : 1 ≤ k := (Finset.mem_Icc.mp hk).1
        rw [runExpectedSquaredProjectedGradientAt_eq_exactGradient
          S hG hResidualMean k hk_pos]
        have hblockFactorPointwise :
            ∀ ω : S.RunSample,
              S.outputWeight k *
                  S.blockNormSq
                    (Pi.map
                      (fun i yi => S.blockProjectedGradient i
                        (S.paperIterate ω.1 ω.2 k hk_pos)
                        yi (S.γ k) (S.gamma_pos_obligation k hk_pos))
                      (S.grad (S.paperIterate ω.1 ω.2 k hk_pos).1)) ≤
                S.γ k *
                  ∑ i, S.p i * (1 - (S.L i / 2) * S.γ k) *
                    ‖(Pi.map
                        (fun j yj => S.blockProjectedGradient j
                          (S.paperIterate ω.1 ω.2 k hk_pos)
                          yj (S.γ k) (S.gamma_pos_obligation k hk_pos))
                        (S.grad (S.paperIterate ω.1 ω.2 k hk_pos).1) i)‖ ^ 2 := by
          intro ω
          exact
            outputWeight_mul_blockNormSq_le_gamma_weighted_block_sum
              S k hk_pos
                (Pi.map
                  (fun i yi => S.blockProjectedGradient i
                    (S.paperIterate ω.1 ω.2 k hk_pos)
                    yi (S.γ k) (S.gamma_pos_obligation k hk_pos))
                  (S.grad (S.paperIterate ω.1 ω.2 k hk_pos).1))
        have hfixed_time_expected_descent :
            (1 / 2 : ℝ) * S.outputWeight k *
                (∫ ω : S.RunSample,
                  let xk := S.paperIterate ω.1 ω.2 k hk_pos
                  S.blockNormSq
                    (Pi.map
                      (fun i yi => S.blockProjectedGradient i xk yi (S.γ k)
                        (S.gamma_pos_obligation k hk_pos))
                      (S.grad xk.1)) ∂S.runLaw) ≤
              drop k + 2 * S.γ k * S.sigmaBar k ^ 2 := by
          have hpathwise_exact :
              ∀ ω : S.RunSample,
                let iω := S.blockIndexProcess ω k
                let xk := S.iterateProcess k hk_pos ω
                let epg := S.exactProjectedGradientProcess k hk_pos ω
                let δ := S.stochasticGradientResidualProcess k hk_pos ω
                (S.γ k / 2) * (1 - S.L iω / 2 * S.γ k) * ‖epg‖ ^ 2 ≤
                  S.compositeObjective xk -
                    S.compositeObjective
                      (S.step k hk_pos xk iω (S.oracleSampleProcess ω k)) +
                    S.γ k * ⟪δ, epg⟫_ℝ + 2 * S.γ k * ‖δ‖ ^ 2 := by
            intro ω
            simpa [Setup.blockIndexProcess, Setup.oracleSampleProcess,
              Setup.iterateProcess, Setup.exactProjectedGradientProcess,
              Setup.stochasticGradientResidualProcess,
              Setup.stochasticBlockGradientProcess, Setup.exactBlockGradientProcess]
              using
                theorem69_selected_block_pathwise_exact_descent
                  S k hk_pos (S.iterateProcess k hk_pos ω)
                  (S.blockIndexProcess ω k) (S.oracleSampleProcess ω k)
          have hcurrent_step_eq :
              ∀ ω : S.RunSample,
                S.step k hk_pos (S.iterateProcess k hk_pos ω)
                    (S.blockIndexProcess ω k) (S.oracleSampleProcess ω k) =
                  S.paperIterate ω.1 ω.2 (k + 1)
                    (Nat.succ_le_succ (Nat.zero_le k)) := by
            intro ω
            simpa [Setup.iterateProcess, Setup.blockIndexProcess,
              Setup.oracleSampleProcess] using
                (paperIterate_succ_eq_step_current S ω.1 ω.2 k hk_pos).symm
          have hProcess := _hExpectation.2.1 k hk hk_pos
          have hderived :
              (1 / 2 : ℝ) * S.outputWeight k *
                  (∫ ω : S.RunSample,
                    S.theorem69ExactProjectedGradientNormSqAt k hk_pos ω
                  ∂S.runLaw) ≤
                (∫ ω : S.RunSample,
                  S.theorem69ObjectiveDropIntegrandAt k hk_pos ω
                ∂S.runLaw) +
                  2 * S.γ k * S.sigmaBar k ^ 2 :=
            theorem69_fixed_time_expected_descent_of_process_semantics
              S N hN k hk hProcess.1 hProcess.2
              (_hExpectation.2.2 k hk)
              hResidualMean hResidualSecond hpathwise_exact
              hcurrent_step_eq hblockFactorPointwise
          simpa [drop, dropIntegrand, theorem69ExactProjectedGradientNormSqAt,
            theorem69ObjectiveDropIntegrandAt, hk] using hderived
        simpa [drop, dropIntegrand, hk] using hfixed_time_expected_descent
      have htelescope :
          Finset.sum (S.outputWindow N) drop ≤
            S.compositeObjective S.x₁Carrier - S.phiStar := by
        haveI : IsProbabilityMeasure S.runLaw := S.runLaw_isProbabilityMeasure
        have hdrop_int :
            ∀ k ∈ S.outputWindow N, Integrable (dropIntegrand k) S.runLaw := by
          -- Remaining objective regularity blocker: integrability of the
          -- consecutive composite-objective drops along `paperIterate`.
          -- The source theorem uses these expectations, but the current setup
          -- has no objective-process integrability field analogous to the
          -- RSMD route-local `hprocess_int` interface.
          intro k hk
          simpa [dropIntegrand, theorem69ObjectiveDropIntegrandAt, hk] using
            _hExpectation.2.2 k hk
        have hsum_int :
            Integrable
              (fun ω : S.RunSample =>
                Finset.sum (S.outputWindow N) (fun k => dropIntegrand k ω))
              S.runLaw :=
          integrable_finset_sum (S.outputWindow N) hdrop_int
        have hsum_eq :
            Finset.sum (S.outputWindow N) drop =
              ∫ ω : S.RunSample,
                Finset.sum (S.outputWindow N) (fun k => dropIntegrand k ω)
              ∂S.runLaw := by
          dsimp [drop]
          rw [integral_finset_sum (S.outputWindow N) hdrop_int]
        have hpoint :
            ∀ ω : S.RunSample,
              Finset.sum (S.outputWindow N) (fun k => dropIntegrand k ω) =
                S.compositeObjective S.x₁Carrier -
                  S.compositeObjective
                    (S.paperIterate ω.1 ω.2 (N + 1)
                      (Nat.succ_le_succ (Nat.zero_le N))) := by
          intro ω
          simpa [dropIntegrand] using
            theorem69_objective_drop_pointwise_telescope S N hN ω
        have hmono :
            (∫ ω : S.RunSample,
                Finset.sum (S.outputWindow N) (fun k => dropIntegrand k ω)
              ∂S.runLaw) ≤
              ∫ _ω : S.RunSample,
                S.compositeObjective S.x₁Carrier - S.phiStar ∂S.runLaw := by
          refine integral_mono hsum_int
            (integrable_const
              (c := S.compositeObjective S.x₁Carrier - S.phiStar)) ?_
          intro ω
          calc
            Finset.sum (S.outputWindow N) (fun k => dropIntegrand k ω) =
                S.compositeObjective S.x₁Carrier -
                  S.compositeObjective
                    (S.paperIterate ω.1 ω.2 (N + 1)
                      (Nat.succ_le_succ (Nat.zero_le N))) := hpoint ω
            _ ≤ S.compositeObjective S.x₁Carrier - S.phiStar :=
                sub_le_sub_left
                  (S.phiStar_le
                    (S.paperIterate ω.1 ω.2 (N + 1)
                      (Nat.succ_le_succ (Nat.zero_le N))))
                  (S.compositeObjective S.x₁Carrier)
        calc
          Finset.sum (S.outputWindow N) drop =
              ∫ ω : S.RunSample,
                Finset.sum (S.outputWindow N) (fun k => dropIntegrand k ω)
              ∂S.runLaw := hsum_eq
          _ ≤ ∫ _ω : S.RunSample,
              S.compositeObjective S.x₁Carrier - S.phiStar ∂S.runLaw := hmono
          _ = S.compositeObjective S.x₁Carrier - S.phiStar := by
              simp [integral_const, probReal_univ]
      exact
        theorem69_weighted_descent_telescope_bound_of_fixed_step
          S N hN drop hstep htelescope
    have hsum_mass :
        Finset.sum (S.outputWindow N).attach (fun R =>
            S.outputMass N R *
              S.runExpectedSquaredProjectedGradientAt R.1
                (Finset.mem_Icc.mp R.2).1) =
          (Finset.sum (S.outputWindow N).attach (fun R =>
            S.outputWeight R.1 *
              S.runExpectedSquaredProjectedGradientAt R.1
                (Finset.mem_Icc.mp R.2).1)) /
            S.outputDenominator N := by
      rw [div_eq_mul_inv]
      rw [show
          Finset.sum (S.outputWindow N).attach (fun R =>
              S.outputMass N R *
                S.runExpectedSquaredProjectedGradientAt R.1
                  (Finset.mem_Icc.mp R.2).1) =
            (S.outputDenominator N)⁻¹ *
              Finset.sum (S.outputWindow N).attach (fun R =>
                S.outputWeight R.1 *
                  S.runExpectedSquaredProjectedGradientAt R.1
                    (Finset.mem_Icc.mp R.2).1) by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro R _hR
        simp [outputMass, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]]
      ring
    dsimp [theorem69FormalWeightedLHS, theorem69RHS]
    rw [hsum_mass]
    rw [show (1 / 2 : ℝ) *
        ((Finset.sum (S.outputWindow N).attach (fun R =>
            S.outputWeight R.1 *
              S.runExpectedSquaredProjectedGradientAt R.1
                (Finset.mem_Icc.mp R.2).1)) /
          S.outputDenominator N) =
        ((1 / 2 : ℝ) *
          Finset.sum (S.outputWindow N).attach (fun R =>
            S.outputWeight R.1 *
              S.runExpectedSquaredProjectedGradientAt R.1
                (Finset.mem_Icc.mp R.2).1)) /
          S.outputDenominator N by ring]
    exact div_le_div_of_nonneg_right hweighted (le_of_lt hden_pos)
  rw [hLHS]
  exact hhalf

/-- Conditional PMF realization of the Theorem 6.9 bound from an explicit
finite-weight admissibility certificate. -/
theorem theorem69Bound_of_admissible_output_weights_extension (S : Setup Ξ ι Block)
    (N : ℕ) (hN : 1 ≤ N)
    (hG : S.StochasticGradientCondition)
    (hResidual : S.theorem69ExactGradientResidualAssumptions)
    (hweights : S.outputWeightsAdmissible N)
    (hExpectation :
      S.theorem69ExpectationSemanticsWellDefined N hN
        (S.randomOutputLawOfAdmissible N hweights)) :
    (1 / 2 : ℝ) *
        S.outputExpectedSquaredProjectedGradientOfAdmissible N hN hweights ≤
      S.theorem69RHS N := by
  exact S.theorem69Bound_with_output_law_extension N hN
    hG hResidual
    (S.randomOutputLawOfAdmissible N hweights)
    (S.randomOutputLawOfAdmissible_spec N hweights)
    hExpectation

/-- Corrected source-boundary version of Theorem 6.9.

This is not the original paper theorem: the hypothesis is the explicit
source-boundary record above.  It states that, once a PMF realizing Eq. (6.3.14)
and the nonfallback final expectation semantics are available, the extension
bound applies to that realized output law.
-/
theorem theorem69Bound_corrected_source_boundary (S : Setup Ξ ι Block)
    (N : ℕ) (hN : 1 ≤ N)
    (hBoundary : S.theorem69CorrectedSourceBoundary N hN) :
    ∃ Rlaw : PMF {k : ℕ // k ∈ S.outputWindow N},
      S.OutputLawSpec N Rlaw ∧
        S.theorem69ExpectationSemanticsWellDefined N hN Rlaw ∧
          (1 / 2 : ℝ) * S.theorem69LHSWithLaw N hN Rlaw ≤
            S.theorem69RHS N := by
  rcases hBoundary with ⟨hG, hResidual, Rlaw, hRlaw, hSemantics⟩
  exact ⟨Rlaw, hRlaw, hSemantics,
    S.theorem69Bound_with_output_law_extension N hN hG hResidual
      Rlaw hRlaw hSemantics⟩

end Output

end Setup

end SGD.NonconvexStochasticBlockMirrorDescent
