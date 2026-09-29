import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Independence.Basic
import SOptLib.Glue.Analysis
import SOptLib.Glue.Calculus
import SOptLib.Glue.Probability
import SOptLib.Glue.Algebra
import SOptLib.Model.Carrier
import SOptLib.Model.ConditionalGradient
import SOptLib.Model.Diameter
import SOptLib.Model.Filtration
import SOptLib.Model.Iterates
import SOptLib.Model.Objective
import SOptLib.Model.ParameterChoices
import SOptLib.Model.StochasticOracle
import SOptLib.Layer0.Objective
import SOptLib.Layer0.Oracle
import SOptLib.Layer1.Telescope

/-!
Object-layer reconstruction for Lan, Algorithm 7.8 and Theorem 7.11.

This file intentionally contains source-facing definitions and theorem
obligations only.  Nontrivial mathematical proofs remain as `sorry` for later
proof phases.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators
open scoped InnerProductSpace

namespace Algorithms.Unverified.StochasticConditionalGradientSliding

/-- Paper positive-time index subtype. -/
abbrev PositiveTime : Type := {k : ℕ // 1 ≤ k}

/-- Source-facing data for the stochastic conditional-gradient sliding problem.

Only stated setup data and stated assumptions from
`book/FOML/StochasticConditionalGradientSliding.json` are fields: compact convex
`X`, convex objective `f`, the displayed schedules, initial point, stochastic
oracle kernel, and sample array.  Algorithmic objects such as `z_k`, `g_k`,
`x_k`, `y_k`, CndG gaps, and `Γ_k` are definitions below, not witness fields.
-/
structure Setup
    (Ω Ξ E : Type*) [MeasurableSpace Ω] [MeasurableSpace Ξ]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] where
  /-- Feasible compact convex set `X`, Section 7.1 after Eq. (7.1.1). -/
  X : Set E
  /-- Objective function `f : X -> R`, Eq. (7.1.1), stored on the feasible carrier. -/
  fX : {x : E // x ∈ X} → ℝ
  /-- Source derivative `f'` on `X`, used in Eqs. (7.1.4), (7.1.7), (7.2.43), and (7.2.44). -/
  fPrime : {x : E // x ∈ X} → E
  /-- Smoothness constant in Eq. (7.1.4). -/
  L : ℝ
  /-- SFO variance bound parameter in Eq. (7.2.44). -/
  σ : ℝ
  /-- Stochastic first-order oracle kernel `G(z, ξ)`, Eq. (7.2.43). -/
  G : E → Ξ → E
  /-- Quote class: definitional regularity of the stochastic oracle datum.
  Source: PDF Section 4.1 SFO model, Assumption 2, quote `for every given
  x ∈ X and ξ ∈ Ξ returns a stochastic subgradient -- a vector G(x, ξ) such
  that g(x) := E[G(x, ξ)] is well defined`; nearby text: `we can employ a
  measurable selection G(x, ξ)`.  This records only measurability of the oracle
  kernel itself, needed to interpret the same SFO notation at random Algorithm
  7.8 queries; it does not assert centered-residual measurability, zero mean,
  variance, freshness, or any Theorem 7.11 proof-step consequence. -/
  hSFO_kernel_joint_measurable :
    Measurable
      (fun p : {z : E // z ∈ X} × Ξ =>
        G p.1.1 p.2)
  /-- Mini-batch sample array `ξ_{k,j}`, Eq. (7.2.46). -/
  ξ : ℕ → ℕ → Ω → Ξ
  /-- Probability law for the SFO sample space. -/
  P : ProbabilityMeasure Ω
  /-- Outer iteration limit `N`, Algorithm 7.8. -/
  N : ℕ
  /-- Initial point `x_0 ∈ X`; Algorithm 7.6 initialization inherited by Algorithm 7.8. -/
  x0 : E
  /-- Projection curvature schedule `β_k ∈ R_{++}`. -/
  β : ℕ → ℝ
  /-- Averaging schedule `γ_k ∈ [0,1]`. -/
  γ : ℕ → ℝ
  /-- CndG tolerance schedule `η_k ∈ R_+`, modeled as `η_k ≥ 0`
  following Eq. (7.2.8). -/
  η : ℕ → ℝ
  /-- Positive mini-batch sizes `B_k` in Eq. (7.2.46), indexed only by paper
  times `k ≥ 1`.
  Source: `book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec/steps/1`,
  quote `g_k:=1/B_k sum_{j=1}^{B_k} G(z_k, ξ_{k,j})`; PDF Algorithm 7.8
  says these `B_k` are batch sizes and the oracle calls are indexed
  `j = 1, ..., B_k`. -/
  B : PositiveTime → {n : ℕ // 0 < n}
  /-- Quote class: stated setup datum/definitional property.
  Source: `book/FOML/StochasticConditionalGradientSliding.json#/setup/variable_space`
  and `#/assumptions/0`, quote `X ⊆ R^n is a convex compact set`. -/
  hX_convex : Convex ℝ X
  /-- Quote class: stated setup datum/definitional property.
  Source: `book/FOML/StochasticConditionalGradientSliding.json#/setup/variable_space`
  and `#/assumptions/0`, quote `X ⊆ R^n is a convex compact set`. -/
  hX_compact : IsCompact X
  /-- Quote class: stated algorithm input datum.
  Source: `book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec/initialization`,
  quote `x_0 ∈ X and iteration limit N`. -/
  hx0_mem : x0 ∈ X
  /-- Quote class: stated setup datum/definitional property.
  Source: `book/FOML/StochasticConditionalGradientSliding.json#/setup/variable_space`
  and `#/assumptions/0`, quote `f : X → R is a closed convex function`. -/
  hf_convex : ConvexOn ℝ X (SOptLib.carrierTotalizeOn X fX)
  /-- Quote class: stated setup datum/definitional property, realized by the
  epigraph-closed encoding of closedness for the carrier objective.
  Source: `book/FOML/StochasticConditionalGradientSliding.json#/setup/variable_space`
  and `#/assumptions/0`, quote `f : X → R is a closed convex function`. -/
  hf_closed_epigraph : IsClosed {p : E × ℝ | ∃ hx : p.1 ∈ X, fX ⟨p.1, hx⟩ ≤ p.2}
  /-- Quote class: definitional property of the stated source derivative `f'`.
  Source: `book/FOML/StochasticConditionalGradientSliding.json#/assumptions/1`,
  quote `‖f'(x)-f'(y)‖_* ≤ L‖x-y‖, ∀ x,y ∈ X`; also
  `#/algorithm_spec/parameters/2`, quote `l_f(x;y):=f(x)+<f'(x),y-x>`. -/
  hfPrime_derivative :
    ∀ x : {x : E // x ∈ X},
      HasGradientWithinAt (SOptLib.carrierTotalizeOn X fX) (fPrime x) X x.1
  /-- Quote class: stated algorithm parameter domain.
  Source: `book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec/initialization`,
  quote `β_k ∈ R_{++}, γ_k ∈ [0,1], and η_k ∈ R_+, k=1,2,..., be given`. -/
  hβ_pos : ∀ k, 1 ≤ k → 0 < β k
  /-- Quote class: stated algorithm parameter domain.
  Source: `book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec/initialization`,
  quote `β_k ∈ R_{++}, γ_k ∈ [0,1], and η_k ∈ R_+, k=1,2,..., be given`. -/
  hγ_mem : ∀ k, 1 ≤ k → γ k ∈ Set.Icc (0 : ℝ) 1
  /-- Quote class: stated algorithm parameter domain.
  Source: `book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec/initialization`,
  quote `β_k ∈ R_{++}, γ_k ∈ [0,1], and η_k ∈ R_+, k=1,2,..., be given`. -/
  hη_nonneg : ∀ k, 1 ≤ k → 0 ≤ η k
  /-- Quote class: stated assumption.
  Source: `book/FOML/StochasticConditionalGradientSliding.json#/assumptions/5`,
  quote `γ_1=1 and L γ_k ≤ β_k, k≥1`. -/
  hγ_one : γ 1 = 1
  /-- Quote class: stated assumption.
  Source: `book/FOML/StochasticConditionalGradientSliding.json#/assumptions/1`,
  quote `‖f'(x)-f'(y)‖_* ≤ L‖x-y‖, ∀ x,y ∈ X`. -/
  hSmoothness : ∀ x : {x : E // x ∈ X}, ∀ y : {x : E // x ∈ X},
    ‖fPrime x - fPrime y‖ ≤ L * ‖x.1 - y.1‖
  /-- Quote class: stated assumption.
  Source: `book/FOML/StochasticConditionalGradientSliding.json#/assumptions/5`,
  quote `γ_1=1 and L γ_k ≤ β_k, k≥1`. -/
  hparam_lower : ∀ k, 1 ≤ k → L * γ k ≤ β k

namespace Setup

variable {Ω Ξ E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]

/-- Ambient realization of the carrier objective `f : X -> R`.

This uses SOptLib's `carrierTotalizeOn` only as the Lean realization of the
paper's carrier function.  Source-facing derivative and smoothness statements
below remain restricted to `X`; values outside `X` are not part of the paper
semantics.
-/
def f (S : Setup Ω Ξ E) : E → ℝ :=
  SOptLib.carrierTotalizeOn S.X S.fX

theorem f_of_mem (S : Setup Ω Ξ E) (x : E) (hx : x ∈ S.X) :
    S.f x = S.fX ⟨x, hx⟩ := by
  simp [f, SOptLib.carrierTotalizeOn, hx]

/-- Canonical probability law underlying the SFO expectations in
Eqs. (7.2.43), (7.2.44), and Theorem 7.11.

This is a `ProbabilityMeasure`, not an arbitrary `Measure`; the coercion to a
Mathlib measure is used only to realize integrals.
-/
def probabilityLaw (S : Setup Ω Ξ E) : ProbabilityMeasure Ω :=
  S.P

/-- The SFO law is a probability measure by construction. -/
theorem probabilityLaw_isProbabilityMeasure (S : Setup Ω Ξ E) :
    IsProbabilityMeasure (S.probabilityLaw : Measure Ω) := by
  infer_instance

/-- Closed convex objective assumption from Section 7.1 after Eq. (7.1.1).

The source states that `f : X -> R` is closed convex; convexity is the Setup
field `hf_convex`, while this theorem exposes the closed-epigraph component.
-/
theorem closedFunction_7_1_1 (S : Setup Ω Ξ E) :
    IsClosed {p : E × ℝ | ∃ hx : p.1 ∈ S.X, S.fX ⟨p.1, hx⟩ ≤ p.2} :=
  S.hf_closed_epigraph

/-- Canonical source gradient `f'` on the feasible carrier.

The paper uses `f'` directly in Eqs. (7.1.4), (7.1.7), (7.2.43), and
(7.2.44).  This definition exposes that source derivative object rather than a
totalized Lean gradient selector; `grad_is_gradient` records its derivative
semantics on `X`.
-/
def grad (S : Setup Ω Ξ E) (x : {x : E // x ∈ S.X}) : E :=
  S.fPrime x

/-- Linear approximation `l_f(x;y) := f(x) + <f'(x), y - x>`, Eq. (7.1.7).

Considered SOptLib candidates:
`lowerModel_le_compositeObjective_of_curvature_lower` and related model-bound
theorems are proof bridges, not the paper's literal two-argument linear model,
so the local definition records Eq. (7.1.7) directly.
-/
def linearModel (S : Setup Ω Ξ E) (x y : {x : E // x ∈ S.X}) : ℝ :=
  S.f x.1 + ⟪S.grad x, y.1 - x.1⟫_ℝ

/-- Source smoothness assumption, Eq. (7.1.4), specialized to the ambient
Hilbert norm used in this file. -/
theorem smoothness_7_1_4 (S : Setup Ω Ξ E) :
    ∀ x : {x : E // x ∈ S.X}, ∀ y : {x : E // x ∈ S.X},
      ‖S.grad x - S.grad y‖ ≤ S.L * ‖x.1 - y.1‖ :=
  by
    intro x y
    simpa [grad] using S.hSmoothness x y

/-- Differentiability of the carrier objective at feasible points, derived from
the source's use of the derivative notation `f'` together with smoothness
Eq. (7.1.4), rather than stored as a primitive Setup field. -/
theorem differentiableWithinAt_obligation (S : Setup Ω Ξ E) :
    ∀ x ∈ S.X, DifferentiableWithinAt ℝ S.f S.X x := by
  intro x hx
  exact (S.hfPrime_derivative ⟨x, hx⟩).differentiableWithinAt

/-- The source gradient is the derivative `f'` from the source smoothness,
linear-model, and SFO equations. -/
theorem grad_is_gradient (S : Setup Ω Ξ E) :
    ∀ x : {x : E // x ∈ S.X}, HasGradientWithinAt S.f (S.grad x) S.X x.1 := by
  intro x
  simpa [f, grad] using S.hfPrime_derivative x

/-- The source gradient is measurable on the feasible carrier.

This is derived from the stated Lipschitz-gradient assumption (7.1.4), not
assumed as part of the stochastic oracle datum.
-/
theorem grad_measurable (S : Setup Ω Ξ E) :
    Measurable S.grad := by
  simpa [grad] using
    (measurable_of_norm_sub_le_mul_on_subtype (s := S.X) S.fPrime S.L
      (by
        intro x y
        simpa using S.hSmoothness x y))

/-- Smooth upper model, Eq. (7.1.8), derived from the stated smoothness
assumption rather than accepted as a Setup field.

This specializes the SOptLib carrier bridge
`Convex.carrier_smooth_quadratic_upper_bound_of_hasGradientWithinAt_lipschitz`,
aligning its carrier smoothness form with Lan Eq. (7.1.8) from Eq. (7.1.4).
-/
theorem SmoothUpperModel_7_1_8 (S : Setup Ω Ξ E) (x : E) (hx : x ∈ S.X)
    (y : E) (hy : y ∈ S.X) :
    S.f y ≤ S.linearModel ⟨x, hx⟩ ⟨y, hy⟩ + S.L / 2 * ‖y - x‖ ^ 2 := by
  have hcarrier :
      S.fX ⟨y, hy⟩ - S.fX ⟨x, hx⟩ -
          ⟪S.grad ⟨x, hx⟩, y - x⟫_ℝ ≤
        (S.L / 2) * ‖y - x‖ ^ 2 := by
    simpa using
      (Convex.carrier_smooth_quadratic_upper_bound_of_hasGradientWithinAt_lipschitz
        (f := S.fX) (F := S.f) (grad := S.grad) (L := S.L)
        S.hX_convex
        (by
          intro z hz
          exact S.f_of_mem z hz)
        (by
          intro z
          exact S.grad_is_gradient z)
        (by
          intro a b
          simpa [grad, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
            S.hSmoothness b a)
        ⟨y, hy⟩ ⟨x, hx⟩)
  unfold linearModel
  rw [S.f_of_mem y hy, S.f_of_mem x hx]
  linarith

/-- Convexity gives the first-order lower model `l_f(z,x) ≤ f(x)` used in
Eq. (7.2.49).

This specializes the source convexity and within-gradient semantics to the
paper's literal linear model.  Considered `bregmanDivergence_nonneg_of_convexOn`,
`Convex.first_order_condition_of_isMinOn_hasFDerivWithinAt`, and SOptLib
lower-model/composite helpers; the Bregman lemma needs an ambient `HasGradientAt`
for Mathlib's selected `∇`, the FOC lemma is for minimizers, and the composite
helpers assume an already supplied support inequality, so this route-local
bridge proves the carrier support form directly from `ConvexOn` and
`HasGradientWithinAt`.
-/
private theorem linearModel_le_f_of_mem
    (S : Setup Ω Ξ E) {z x : E} (hz : z ∈ S.X) (hx : x ∈ S.X) :
    S.linearModel ⟨z, hz⟩ ⟨x, hx⟩ ≤ S.f x := by
  let I : Set ℝ := Set.Icc (0 : ℝ) 1
  let line : ℝ → E := fun t => AffineMap.lineMap z x t
  have hline_mem : I ⊆ line ⁻¹' S.X := by
    intro t ht
    have ht0 : 0 ≤ t := ht.1
    have ht1 : t ≤ 1 := ht.2
    have h1t : 0 ≤ 1 - t := sub_nonneg.mpr ht1
    have hsum : 1 - t + t = 1 := by ring
    have hmem : (1 - t) • z + t • x ∈ S.X := S.hX_convex hz hx h1t ht0 hsum
    change line t ∈ S.X
    simpa [line, AffineMap.lineMap_apply_module] using hmem
  have hconv_line : ConvexOn ℝ I (fun t => S.f (line t)) := by
    simpa [f, line, I] using
      (S.hf_convex.comp_affineMap (AffineMap.lineMap z x)).subset hline_mem
        (convex_Icc 0 1)
  have hmaps : Set.MapsTo line I S.X := by
    intro t ht
    exact hline_mem ht
  have hline_deriv :
      HasDerivWithinAt line (x - z) I 0 := by
    simpa [line, I] using
      (AffineMap.hasDerivWithinAt_lineMap (a := z) (b := x)
        (s := I) (x := (0 : ℝ)))
  have hz_grad : HasGradientWithinAt S.f (S.grad ⟨z, hz⟩) S.X z :=
    S.grad_is_gradient ⟨z, hz⟩
  have hfline :
      HasDerivWithinAt (fun t => S.f (line t))
        (⟪S.grad ⟨z, hz⟩, x - z⟫_ℝ) I 0 := by
    have hcomp :=
      hz_grad.hasFDerivWithinAt.comp_hasDerivWithinAt_of_eq 0 hline_deriv hmaps
        (by simp [line])
    simpa [line] using hcomp
  have hslope :
      ⟪S.grad ⟨z, hz⟩, x - z⟫_ℝ ≤
        slope (fun t => S.f (line t)) 0 1 := by
    exact hconv_line.le_slope_of_hasDerivWithinAt
      (x := (0 : ℝ)) (y := (1 : ℝ))
      (by norm_num [I]) (by norm_num [I]) (by norm_num) hfline
  have hslope_eval :
      slope (fun t => S.f (line t)) 0 1 = S.f x - S.f z := by
    simp [slope, line]
  unfold linearModel
  rw [hslope_eval] at hslope
  linarith

/-- Gamma weights `Γ_k`, Eq. (7.2.9), aligned with
`SOptLib.acceleratedGammaSchedule`.

The SOptLib candidate `acceleratedGammaSchedule` has exactly the one-based
recurrence `Γ_1 = 1`, `Γ_{k+1} = (1-γ_{k+1})Γ_k`, so this paper-facing name is
a specialization rather than a local redefinition.
-/
def Gamma (S : Setup Ω Ξ E) (k : PositiveTime) : ℝ :=
  SOptLib.acceleratedGammaSchedule S.γ k

/-- Totalized natural-number view of `Γ_k` for finite sums over `Icc 1 k`.
On positive indices this is definitionally the paper Gamma; the zero branch is
only a Lean helper and is not used in source-facing theorem statements. -/
def GammaNat (S : Setup Ω Ξ E) (k : ℕ) : ℝ :=
  if hk : 1 ≤ k then S.Gamma ⟨k, hk⟩ else 1

theorem GammaNat_of_pos (S : Setup Ω Ξ E) (k : ℕ) (hk : 1 ≤ k) :
    S.GammaNat k = S.Gamma ⟨k, hk⟩ := by
  simp [GammaNat, hk]

/-- Natural-number value of the positive mini-batch size `B_k`, Eq. (7.2.46).

This is a paper-facing specialization of the positive batch-size datum rather
than a totalized natural-number fallback.  The SOptLib candidate
`miniBatchOracleAverage` is used below for the finite average itself; this local
accessor records Algorithm 7.8's one-based, positive-time batch schedule. -/
def batchSize (S : Setup Ω Ξ E) (k : PositiveTime) : ℕ :=
  (S.B k).1

/-- Batch sizes in Algorithm 7.8 are nonempty by construction, so the
`1 / B_k` factor in Eq. (7.2.46) never denotes Lean's zero-inverse fallback. -/
theorem batchSize_pos (S : Setup Ω Ξ E) (k : PositiveTime) :
    0 < S.batchSize k :=
  (S.B k).2

theorem batchSize_ne_zero (S : Setup Ω Ξ E) (k : PositiveTime) :
    (S.batchSize k : ℝ) ≠ 0 := by
  exact_mod_cast Nat.ne_of_gt (S.batchSize_pos k)

@[simp]
theorem Gamma_one (S : Setup Ω Ξ E) :
    S.Gamma ⟨1, le_rfl⟩ = 1 := by
  simp [Gamma, SOptLib.acceleratedGammaSchedule_one]

theorem Gamma_succ (S : Setup Ω Ξ E) (k : ℕ) (hk : 1 ≤ k) :
    S.Gamma ⟨k + 1, Nat.succ_le_succ (Nat.zero_le k)⟩ =
      (1 - S.γ (k + 1)) * S.Gamma ⟨k, hk⟩ := by
  simpa [Gamma] using SOptLib.acceleratedGammaSchedule_succ S.γ k hk

/-- Partial real quotient relation for source formulas.

No SOptLib match: searched `Budget.lean` denominator helpers and
`ParameterChoices.lean` checked quotient helpers.  Those helpers certify total
real divisions after separate denominator proofs, while Theorems 7.9 and 7.11
print partial mathematical quotients whose denominator admissibility is not
stated as a theorem-head assumption.  This relation records the quotient by its
domain condition and cross-multiplied value, avoiding Lean's division-by-zero
fallback.
-/
def sourceQuotient (_S : Setup Ω Ξ E) (num den q : ℝ) : Prop :=
  den ≠ 0 ∧ q * den = num

/-- Mathematical quotient `β_k γ_k / Γ_k` from Eqs. (7.2.11) and (7.2.13),
represented as a partial source quotient.

No SOptLib match: searched checked quotient helpers in `ParameterChoices.lean`
and budget quotient candidates.  Those helpers model other schedules or require
separate positivity assumptions; this local relation records the literal
displayed quotient domain and value in the paper.
-/
def parameterRatioQuotient (S : Setup Ω Ξ E) (k : PositiveTime) (q : ℝ) : Prop :=
  S.sourceQuotient (S.β k.1 * S.γ k.1) (S.Gamma k) q

/-- Domain/value bridge for the ratio in Eqs. (7.2.11) and (7.2.13). -/
theorem parameterRatioQuotient_spec (S : Setup Ω Ξ E) (k : PositiveTime) (q : ℝ) :
    S.parameterRatioQuotient k q ↔
      S.Gamma k ≠ 0 ∧ q * S.Gamma k = S.β k.1 * S.γ k.1 := by
  rfl

/-- Lean totalized helper for the displayed scalar `β_k γ_k / Γ_k`.

This is retained only as an internal arithmetic abbreviation; the paper-facing
monotonicity predicates below use `parameterRatioQuotient` so their meaning is
not Lean's total division fallback at `Γ_k = 0`.
-/
def parameterRatio (S : Setup Ω Ξ E) (k : PositiveTime) : ℝ :=
  S.β k.1 * S.γ k.1 / S.Gamma k

theorem parameterRatio_def (S : Setup Ω Ξ E) (k : PositiveTime) :
    S.parameterRatio k = S.β k.1 * S.γ k.1 / S.Gamma k := rfl

/-- Parameter monotonicity (7.2.11), kept as a theorem-facing predicate rather
than a Setup field because Theorem 7.11 selects either (7.2.11) or (7.2.13).

Considered SOptLib checked-quotient helpers such as the `ParameterChoices.lean`
quotient bridges.  Those helpers add realization side-conditions, while the
paper states the literal quotient inequality in Eq. (7.2.11).  The predicate
therefore relates quotient witnesses through `parameterRatioQuotient` rather
than using Lean's total `/` or adding separate theorem-head `Γ_k ≠ 0`
assumptions.
-/
def ParameterMonotonicityA_7_2_11 (S : Setup Ω Ξ E) : Prop :=
  ∀ k : {n : ℕ // 2 ≤ n},
    let prev : PositiveTime := ⟨k.1 - 1, Nat.sub_pos_of_lt (Nat.lt_of_succ_le k.2)⟩
    let cur : PositiveTime := ⟨k.1, le_trans (by decide) k.2⟩
    ∃ qPrev qCur : ℝ,
      S.parameterRatioQuotient prev qPrev ∧
        S.parameterRatioQuotient cur qCur ∧ qPrev ≤ qCur

/-- Parameter monotonicity (7.2.13), the alternative part-(b) hypothesis.
As in (7.2.11), this is the printed quotient inequality represented through
partial quotient witnesses rather than totalized division. -/
def ParameterMonotonicityB_7_2_13 (S : Setup Ω Ξ E) : Prop :=
  ∀ k : {n : ℕ // 2 ≤ n},
    let prev : PositiveTime := ⟨k.1 - 1, Nat.sub_pos_of_lt (Nat.lt_of_succ_le k.2)⟩
    let cur : PositiveTime := ⟨k.1, le_trans (by decide) k.2⟩
    ∃ qPrev qCur : ℝ,
      S.parameterRatioQuotient prev qPrev ∧
        S.parameterRatioQuotient cur qCur ∧ qCur ≤ qPrev

/-- Nonnegativity of the tolerance schedule, Algorithm 7.6 and Eq. (7.2.8). -/
theorem eta_nonneg (S : Setup Ω Ξ E) :
    ∀ k, 1 ≤ k → 0 ≤ S.η k :=
  S.hη_nonneg

/-- Existence obligation for the diameter maximum in Eq. (7.1.18). -/
theorem diameter_exists (S : Setup Ω Ξ E) :
    ∃ D : ℝ, ∃ x ∈ S.X, ∃ y ∈ S.X,
      D = ‖x - y‖ ∧ ∀ a ∈ S.X, ∀ b ∈ S.X, ‖a - b‖ ≤ D := by
  obtain ⟨p, hpmax⟩ := SOptLib.diameterPair_exists ⟨S.x0, S.hx0_mem⟩ S.hX_compact
  refine ⟨‖(p.1 : E) - (p.2 : E)‖, p.1, p.1.property, p.2, p.2.property, rfl, ?_⟩
  intro a ha b hb
  exact SOptLib.le_euclideanDiameterOfPair_of_mem p hpmax ha hb

/-- Feasible-set diameter `D̄_X := max_{x,y∈X} ||x-y||`, Eq. (7.1.18).

This specializes the SOptLib compact diameter-pair theorem to the literal paper
scalar `D̄_X` in Eq. (7.1.18); the local `def` chooses the maximizing value tied
to the current setup.
-/
def diameter (S : Setup Ω Ξ E) : ℝ :=
  Classical.choose S.diameter_exists

theorem diameter_spec (S : Setup Ω Ξ E) :
    ∃ x ∈ S.X, ∃ y ∈ S.X,
      S.diameter = ‖x - y‖ ∧ ∀ a ∈ S.X, ∀ b ∈ S.X, ‖a - b‖ ≤ S.diameter := by
  exact Classical.choose_spec S.diameter_exists

/-- Squared SFO residual integrand from Eq. (7.2.44). -/
def oracleVarianceIntegrand (S : Setup Ω Ξ E) (z : E) (hz : z ∈ S.X)
    (k j : ℕ) : Ω → ℝ :=
  fun ω => ‖S.G z (S.ξ k j ω) - S.grad ⟨z, hz⟩‖ ^ 2

/-- Source expectation equality as a well-defined mathematical expectation.

Considered SOptLib candidates `expectation` and `expectationWellDefined`.
`expectation` alone is Mathlib's total Bochner integral and can be satisfied by
fallback values outside the paper's domain; this relation pairs the paper's
displayed expectation value with the well-definedness intrinsic to writing
`E[.]` in Eqs. (7.2.43), (7.2.44), and Theorem 7.11.
-/
def sourceExpectationEq (S : Setup Ω Ξ E)
    {R : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R]
    (Z : Ω → R) (target : R) : Prop :=
  SOptLib.expectationWellDefined S.P Z ∧ SOptLib.expectation S.P Z = target

/-- Source scalar expectation upper bound as a well-defined mathematical
expectation inequality.

Considered SOptLib candidates `expectation` and `expectationWellDefined`; the
source-facing relation uses both so Theorem 7.11 does not rely on Lean's
totalized integral value when the printed expectation is not well-defined.
-/
def sourceExpectationLe (S : Setup Ω Ξ E) (Z : Ω → ℝ) (bound : ℝ) : Prop :=
  SOptLib.expectationWellDefined S.P Z ∧ SOptLib.expectation S.P Z ≤ bound

/-- Source-level joint measurability of the centered SFO residual kernel.

This is the Lean regularity component of the paper's stochastic-oracle datum:
`G(z, ξ)` is an oracle kernel that can be evaluated at random Algorithm 7.8
queries.  It is kept separate from the displayed moment assumptions
(7.2.43)/(7.2.44), which state only the mean and variance values.
-/
def sourceOracleResidualJointMeasurable (S : Setup Ω Ξ E) : Prop :=
  Measurable
    (fun p : {z : E // z ∈ S.X} × Ξ =>
      S.G p.1.1 p.2 - S.grad p.1)

/-- Source expectation equality for Eq. (7.2.43).

The PDF states only `E[G(z_k, ξ_k)] = f'(z_k)` and does not list oracle
well-definedness as a separate theorem assumption.  This predicate records the
displayed mathematical expectation, including its well-definedness, rather than
Lean's totalized integral fallback.  Oracle-kernel measurability is a separate
property of the SFO datum, exposed by `sourceOracleResidualJointMeasurable`.

Considered `SOptLib.BoundedVarianceUnbiasedOracleOn`; it carries extra
variance and law fields beyond this displayed mean equality.  The local
predicate keeps only the displayed mean value and its well-definedness.
-/
def sourceOracleMeanEq (S : Setup Ω Ξ E) (z : E) (k j : ℕ) (target : E) : Prop :=
  S.sourceExpectationEq (fun ω => S.G z (S.ξ k j ω)) target

/-- Source variance bound for Eq. (7.2.44).

The PDF states the squared-residual expectation inequality and does not list
expectation well-definedness as a separate primitive assumption.  This predicate
records the displayed mathematical expectation inequality, including its
well-definedness, while oracle-kernel measurability remains a separate SFO datum.
-/
def sourceOracleVarianceLe (S : Setup Ω Ξ E) (z : E) (hz : z ∈ S.X)
    (k j : ℕ) (bound : ℝ) : Prop :=
  S.sourceExpectationLe (S.oracleVarianceIntegrand z hz k j) bound

/-- Source-level unbiased SFO condition, Eq. (7.2.43), stated for feasible
queries and the mini-batch sample coordinates used by Algorithm 7.8.

The reusable `BoundedVarianceUnbiasedOracleOn` bundle was considered and
rejected here because it also carries joint-measurability fields not stated in
Theorem 7.11.  This predicate is the displayed mathematical expectation
equality, with expectation well-definedness included as part of the source
meaning of `E[...]` rather than left to Lean's total integral fallback.
-/
def SFO_Unbiased_7_2_43 (S : Setup Ω Ξ E) : Prop :=
  ∀ (z : E) (hz : z ∈ S.X), ∀ (k : PositiveTime) (j : ℕ),
    j ∈ Finset.Icc 1 (S.batchSize k) →
      S.sourceOracleMeanEq z k.1 j (S.grad ⟨z, hz⟩)

/-- Source-level SFO variance condition, Eq. (7.2.44), stated for feasible
queries and the mini-batch sample coordinates used by Algorithm 7.8.

This is the displayed squared-residual mathematical expectation inequality from
the source, with expectation well-definedness included as part of the source
meaning of `E[...]` rather than left to Lean's total integral fallback.
-/
def SFO_Variance_7_2_44 (S : Setup Ω Ξ E) : Prop :=
  ∀ (z : E) (hz : z ∈ S.X), ∀ (k : PositiveTime) (j : ℕ),
    j ∈ Finset.Icc 1 (S.batchSize k) →
      S.sourceOracleVarianceLe z hz k.1 j (S.σ ^ 2)

/-- Stochastic-basis condition for the sample array used by Algorithm 7.8.

The Theorem 7.11 statement names the displayed moment assumptions (7.2.43) and
(7.2.44), while its proof additionally uses that the SFO samples are fresh
relative to the generated search point.  This predicate records the sample
process needed to derive that proof-step sentence from the paper's SFO model
rather than silently proving Theorem 7.11 from marginal moment assumptions
alone.

Considered SOptLib candidates `SOptLib.filtration`,
`SOptLib.strictPastMiniBatchSampleBlock`, and
`ProbabilityTheory.iIndepFun.indep_prefixFiltration_future`; those provide
sample-prefix objects and proof bridges, while this predicate names the
Algorithm 7.8 two-index sample stream itself.
-/
def SFOSampleBasis_Algorithm7_8 (S : Setup Ω Ξ E) : Prop :=
  (∀ k j : ℕ, Measurable (S.ξ k j)) ∧
    ProbabilityTheory.iIndepFun
      (fun (n : ℕ) (ω : Ω) => S.ξ ((Nat.unpair n).1 + 1) ((Nat.unpair n).2 + 1) ω)
      (S.P : Measure Ω)

/-- Source SFO assumptions for Algorithm 7.8 and Theorem 7.11.

This is exactly the pair of displayed assumptions named in Theorem 7.11(a):
unbiasedness (7.2.43) and bounded variance (7.2.44).  The proof's SFO
freshness sentence after Eq. (7.2.50) is represented by a derived theorem
obligation, not folded into this displayed moment-assumption predicate.
-/
def SFOAssumptions_7_2_43_44 (S : Setup Ω Ξ E) : Prop :=
  S.SFO_Unbiased_7_2_43 ∧ S.SFO_Variance_7_2_44

theorem SFOAssumptions_unbiased (S : Setup Ω Ξ E)
    (hSFO : S.SFOAssumptions_7_2_43_44) :
    S.SFO_Unbiased_7_2_43 :=
  hSFO.1

theorem SFOAssumptions_variance (S : Setup Ω Ξ E)
    (hSFO : S.SFOAssumptions_7_2_43_44) :
    S.SFO_Variance_7_2_44 :=
  hSFO.2

/-- Definitional bridge exposing the displayed oracle mean in Eq. (7.2.43). -/
theorem SFO_Unbiased_7_2_43_mean (S : Setup Ω Ξ E)
    (hUnbiased : S.SFO_Unbiased_7_2_43) (z : E) (hz : z ∈ S.X)
    (k : PositiveTime) (j : ℕ) (hj : j ∈ Finset.Icc 1 (S.batchSize k)) :
    S.sourceOracleMeanEq z k.1 j (S.grad ⟨z, hz⟩) := by
  exact hUnbiased z hz k j hj

/-- The stochastic-oracle datum carries the centered-residual kernel regularity
needed to specialize the oracle at random Algorithm 7.8 search points. -/
theorem SFO_Unbiased_7_2_43_residual_joint_measurable (S : Setup Ω Ξ E)
    (hUnbiased : S.SFO_Unbiased_7_2_43) (z : E) (hz : z ∈ S.X)
    (k : PositiveTime) (j : ℕ) (hj : j ∈ Finset.Icc 1 (S.batchSize k)) :
    S.sourceOracleResidualJointMeasurable := by
  have hG :
      Measurable (fun p : {z : E // z ∈ S.X} × Ξ => S.G p.1.1 p.2) :=
    S.hSFO_kernel_joint_measurable
  have hgrad :
      Measurable (fun p : {z : E // z ∈ S.X} × Ξ => S.grad p.1) :=
    S.grad_measurable.comp measurable_fst
  simpa [sourceOracleResidualJointMeasurable] using hG.sub hgrad

/-- The displayed SFO expectation in Eq. (7.2.43) is well-defined as part of
the source expectation relation, not by Lean's total integral fallback. -/
theorem SFO_Unbiased_7_2_43_expectationWellDefined (S : Setup Ω Ξ E)
    (hUnbiased : S.SFO_Unbiased_7_2_43) (z : E) (hz : z ∈ S.X)
    (k : PositiveTime) (j : ℕ) (hj : j ∈ Finset.Icc 1 (S.batchSize k)) :
    SOptLib.expectationWellDefined S.P (fun ω => S.G z (S.ξ k.1 j ω)) := by
  exact (S.SFO_Unbiased_7_2_43_mean hUnbiased z hz k j hj).1

/-- Lean regularity obligation for the SFO expectation in Eq. (7.2.43).

The source expectation relation already records integrability of the displayed
random vector.  This stronger oracle-specific well-definedness bridge remains a
later proof obligation because it is not a separate paper assumption.
-/
theorem SFO_Unbiased_7_2_43_wellDefined_obligation (S : Setup Ω Ξ E)
    (hUnbiased : S.SFO_Unbiased_7_2_43) (z : E) (hz : z ∈ S.X)
    (k : PositiveTime) (j : ℕ) (hj : j ∈ Finset.Icc 1 (S.batchSize k)) :
    SOptLib.oracleWellDefined S.P S.G (S.ξ k.1 j) z := by
  have hwd :=
    S.SFO_Unbiased_7_2_43_expectationWellDefined hUnbiased z hz k j hj
  have hint : Integrable (fun ω => S.G z (S.ξ k.1 j ω)) (S.P : Measure Ω) :=
    (SOptLib.expectationWellDefined_iff_integrable (S.P : Measure Ω) _).mp hwd
  exact SOptLib.paperMeanOracle_wellDefined (S.P : Measure Ω) S.G (S.ξ k.1 j) z hint

/-- Raw integral bridge for later proof phases; this is the displayed equality in
Eq. (7.2.43). -/
theorem SFO_Unbiased_7_2_43_integral (S : Setup Ω Ξ E)
    (hUnbiased : S.SFO_Unbiased_7_2_43) (z : E) (hz : z ∈ S.X)
    (k : PositiveTime) (j : ℕ) (hj : j ∈ Finset.Icc 1 (S.batchSize k)) :
    ∫ ω, S.G z (S.ξ k.1 j ω) ∂S.P = S.grad ⟨z, hz⟩ := by
  exact (S.SFO_Unbiased_7_2_43_mean hUnbiased z hz k j hj).2

/-- The stochastic-oracle datum carries the centered-residual kernel regularity
used with the variance display. -/
theorem SFO_Variance_7_2_44_residual_joint_measurable (S : Setup Ω Ξ E)
    (hVariance : S.SFO_Variance_7_2_44) (z : E) (hz : z ∈ S.X)
    (k : PositiveTime) (j : ℕ) (hj : j ∈ Finset.Icc 1 (S.batchSize k)) :
    S.sourceOracleResidualJointMeasurable := by
  have hG :
      Measurable (fun p : {z : E // z ∈ S.X} × Ξ => S.G p.1.1 p.2) :=
    S.hSFO_kernel_joint_measurable
  have hgrad :
      Measurable (fun p : {z : E // z ∈ S.X} × Ξ => S.grad p.1) :=
    S.grad_measurable.comp measurable_fst
  simpa [sourceOracleResidualJointMeasurable] using hG.sub hgrad

/-- Lean regularity obligation for the SFO second-moment expectation in
Eq. (7.2.44), kept out of the source-facing variance assumption. -/
theorem SFO_Variance_7_2_44_wellDefined_obligation (S : Setup Ω Ξ E)
    (hVariance : S.SFO_Variance_7_2_44) (z : E) (hz : z ∈ S.X)
    (k : PositiveTime) (j : ℕ) (hj : j ∈ Finset.Icc 1 (S.batchSize k)) :
    SOptLib.expectationWellDefined S.P (S.oracleVarianceIntegrand z hz k.1 j) := by
  exact (hVariance z hz k j hj).1

theorem SFO_Variance_7_2_44_expectation (S : Setup Ω Ξ E)
    (hVariance : S.SFO_Variance_7_2_44) (z : E) (hz : z ∈ S.X)
    (k : PositiveTime) (j : ℕ) (hj : j ∈ Finset.Icc 1 (S.batchSize k)) :
    SOptLib.expectation S.P (S.oracleVarianceIntegrand z hz k.1 j) ≤ S.σ ^ 2 := by
  exact (hVariance z hz k j hj).2

/-- Raw integral bridge for the variance display, kept out of the source-facing
assumption predicate. -/
theorem SFO_Variance_7_2_44_integral (S : Setup Ω Ξ E)
    (hVariance : S.SFO_Variance_7_2_44) (z : E) (hz : z ∈ S.X)
    (k : PositiveTime) (j : ℕ) (hj : j ∈ Finset.Icc 1 (S.batchSize k)) :
    ∫ ω, ‖S.G z (S.ξ k.1 j ω) - S.grad ⟨z, hz⟩‖ ^ 2 ∂S.P ≤ S.σ ^ 2 := by
  simpa [oracleVarianceIntegrand, SOptLib.expectation] using
    S.SFO_Variance_7_2_44_expectation hVariance z hz k j hj

/-- Flattened mini-batch sample stream used only to reuse SOptLib's natural
sample-prefix filtration primitive.

This aligns with `SOptLib.filtration`; the flattening is paper-local because
Algorithm 7.8 indexes samples by the two coordinates `(k,j)`.
-/
def flatSample (S : Setup Ω Ξ E) : ℕ → Ω → Ξ
  | n, ω => S.ξ (n.unpair.1 + 1) (n.unpair.2 + 1) ω

/-- Measurability of the flattened sample stream, derived from the explicit
sample-basis regularity for the two-index SFO sample array. -/
theorem flatSample_measurable (S : Setup Ω Ξ E) (hBasis : S.SFOSampleBasis_Algorithm7_8) :
    ∀ n, Measurable (S.flatSample n) := by
  intro n
  simpa [flatSample] using hBasis.1 (n.unpair.1 + 1) (n.unpair.2 + 1)

/-- Natural filtration generated by the mini-batch sample prefixes.

This reuses `SOptLib.filtration`; the local definition only translates the
paper's `(k,j)` sample array to a single prefix stream.
-/
def sampleFiltration (S : Setup Ω Ξ E) (hBasis : S.SFOSampleBasis_Algorithm7_8) :
    Filtration ℕ (by infer_instance : MeasurableSpace Ω) :=
  SOptLib.filtration S.flatSample (S.flatSample_measurable hBasis)

/-- CndG linear-oracle maximizer existence for Eq. (7.2.4). -/
theorem cndGLinearOracle_exists (S : Setup Ω Ξ E) (g u ut : E) (β : ℝ) :
    ∃ v ∈ S.X, ∀ x ∈ S.X,
      ⟪g + β • (ut - u), ut - x⟫_ℝ ≤
        ⟪g + β • (ut - u), ut - v⟫_ℝ := by
  let G : E := g + β • (ut - u)
  obtain ⟨v, hvmax⟩ :=
    SOptLib.exists_linearModelMaximizer_on_compact S.hX_compact
      ⟨S.x0, S.hx0_mem⟩ ut G
  refine ⟨v.1, v.2, ?_⟩
  intro x hx
  simpa [G] using hvmax ⟨x, hx⟩

/-- Linear-oracle point `v_t` for the CndG subproblem, Eq. (7.2.4).

Considered `SOptLib.LinearMinimizationOracle` and
`SOptLib.ConditionalGradient.wolfeGap`.  They are
reusable LMO/gap abstractions, but Algorithm 7.6 needs the literal shifted
maximizer `max_{x∈X}<g+β(u_t-u),u_t-x>`; this definition chooses that paper
maximizer directly from compactness.
-/
def cndGLinearOracle (S : Setup Ω Ξ E) (g u : E) (β : ℝ) (ut : E) : E :=
  Classical.choose (S.cndGLinearOracle_exists g u ut β)

theorem cndGLinearOracle_mem (S : Setup Ω Ξ E) (g u : E) (β : ℝ) (ut : E) :
    S.cndGLinearOracle g u β ut ∈ S.X :=
  (Classical.choose_spec (S.cndGLinearOracle_exists g u ut β)).1

theorem cndGLinearOracle_isMax (S : Setup Ω Ξ E) (g u : E) (β : ℝ) (ut x : E)
    (hx : x ∈ S.X) :
    ⟪g + β • (ut - u), ut - x⟫_ℝ ≤
      ⟪g + β • (ut - u), ut - S.cndGLinearOracle g u β ut⟫_ℝ :=
  (Classical.choose_spec (S.cndGLinearOracle_exists g u ut β)).2 x hx

/-- CndG Wolfe gap `V_{g,u,β}(u_t)`, Eq. (7.2.4).

No SOptLib match: `SOptLib.ConditionalGradient.wolfeGap` models a selected
Frank-Wolfe gap for a gradient field, while Eq. (7.2.4) is the shifted CndG
subproblem gap with parameters `(g,u,β,u_t)`.
-/
def cndGGap (S : Setup Ω Ξ E) (g u : E) (β : ℝ) (ut : E) : ℝ :=
  ⟪g + β • (ut - u), ut - S.cndGLinearOracle g u β ut⟫_ℝ

/-- Quadratic objective minimized by the CndG line search, Eq. (7.2.6).

No SOptLib match: searched checked quotient and conditional-gradient line-search
candidates; `SOptLib.ConditionalGradient.wolfeGap` names the gap, not this
one-dimensional quadratic objective along the selected CndG segment. -/
def cndGLineSearchObjective (_S : Setup Ω Ξ E) (g u : E) (β : ℝ) (_ut α : E) : ℝ :=
  ⟪g, α⟫_ℝ + β / 2 * ‖α - u‖ ^ 2

/-- Existence of the interval minimizer in the CndG line search, Eq. (7.2.6). -/
theorem cndGStepsize_exists (S : Setup Ω Ξ E) (g u : E) (β : ℝ) (ut : E) :
    ∃ α ∈ Set.Icc (0 : ℝ) 1,
      ∀ a ∈ Set.Icc (0 : ℝ) 1,
        let v := S.cndGLinearOracle g u β ut
        S.cndGLineSearchObjective g u β ut ((1 - α) • ut + α • v) ≤
          S.cndGLineSearchObjective g u β ut ((1 - a) • ut + a • v) := by
  classical
  let v := S.cndGLinearOracle g u β ut
  let F : ℝ → ℝ := fun a =>
    S.cndGLineSearchObjective g u β ut ((1 - a) • ut + a • v)
  have hseg : Continuous (fun a : ℝ => (1 - a) • ut + a • v) := by
    exact ((continuous_const.sub continuous_id).smul continuous_const).add
      (continuous_id.smul continuous_const)
  have hinner : Continuous (fun a : ℝ => ⟪g, (1 - a) • ut + a • v⟫_ℝ) := by
    exact continuous_const.inner hseg
  have hquad : Continuous (fun a : ℝ => β / 2 * ‖(1 - a) • ut + a • v - u‖ ^ 2) := by
    exact continuous_const.mul (((hseg.sub continuous_const).norm).pow 2)
  have hcont : ContinuousOn F (Set.Icc (0 : ℝ) 1) := by
    have hcont_global : Continuous F := by
      dsimp [F]
      unfold cndGLineSearchObjective
      exact hinner.add hquad
    exact hcont_global.continuousOn
  have hne : (Set.Icc (0 : ℝ) 1).Nonempty := ⟨0, by norm_num⟩
  obtain ⟨α, hα, hmin⟩ := (isCompact_Icc).exists_isMinOn hne hcont
  refine ⟨α, hα, ?_⟩
  intro a ha
  simpa [F, v] using hmin ha

/-- CndG line-search stepsize `α_t`, canonically selected as the interval
minimizer in Eq. (7.2.6).

No SOptLib match: searched checked quotient and conditional-gradient line-search
candidates.  Existing quotient/recurrence helpers are proof-level arithmetic, while
Algorithm 7.6 states that the displayed scalar is the minimizer of the one-dimensional
problem in Eq. (7.2.6); this definition uses that source-domain minimizer and avoids
Lean's total division fallback for Eq. (7.2.5).
-/
def cndGStepsize (S : Setup Ω Ξ E) (g u : E) (β : ℝ) (ut : E) : ℝ :=
  Classical.choose (S.cndGStepsize_exists g u β ut)

theorem cndGStepsize_mem (S : Setup Ω Ξ E) (g u : E) (β : ℝ) (ut : E) :
    S.cndGStepsize g u β ut ∈ Set.Icc (0 : ℝ) 1 :=
  (Classical.choose_spec (S.cndGStepsize_exists g u β ut)).1

theorem cndGStepsize_minimizes (S : Setup Ω Ξ E) (g u : E) (β : ℝ) (ut : E)
    (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    let v := S.cndGLinearOracle g u β ut
    S.cndGLineSearchObjective g u β ut
        ((1 - S.cndGStepsize g u β ut) • ut + S.cndGStepsize g u β ut • v) ≤
      S.cndGLineSearchObjective g u β ut ((1 - a) • ut + a • v) :=
  (Classical.choose_spec (S.cndGStepsize_exists g u β ut)).2 a ha

/-- Feasibility of the current CndG iterate makes the displayed quotient in
Eq. (7.2.5) nonnegative, so the lower endpoint of the interval line search is
inactive.  This is derived from the linear oracle comparison with `x = u_t`. -/
theorem cndGStepsize_quotient_nonneg_of_current_mem (S : Setup Ω Ξ E)
    (g u : E) (β : ℝ) (ut : E) (hut : ut ∈ S.X)
    (hβ : 0 < β)
    (hden : let v := S.cndGLinearOracle g u β ut; β * ‖v - ut‖ ^ 2 ≠ 0) :
    let v := S.cndGLinearOracle g u β ut
    0 ≤ ⟪β • (u - ut) - g, v - ut⟫_ℝ / (β * ‖v - ut‖ ^ 2) := by
  let v := S.cndGLinearOracle g u β ut
  have hopt := S.cndGLinearOracle_isMax g u β ut ut hut
  have hgap_nonneg : 0 ≤ ⟪g + β • (ut - u), ut - v⟫_ℝ := by
    simpa [v] using hopt
  have hnum_nonneg : 0 ≤ ⟪β • (u - ut) - g, v - ut⟫_ℝ := by
    simpa [v, sub_eq_add_neg, inner_add_left, inner_add_right, inner_neg_left,
      inner_neg_right, inner_smul_left, inner_smul_right, add_comm, add_left_comm,
      add_assoc] using hgap_nonneg
  have hnorm_ne : ‖v - ut‖ ^ 2 ≠ 0 := by
    intro hnorm
    exact hden (by simpa [v, hnorm])
  have hnorm_pos : 0 < ‖v - ut‖ ^ 2 :=
    lt_of_le_of_ne (sq_nonneg ‖v - ut‖) (Ne.symm hnorm_ne)
  have hden_pos : 0 < β * ‖v - ut‖ ^ 2 := mul_pos hβ hnorm_pos
  exact div_nonneg hnum_nonneg (le_of_lt hden_pos)

/-- Scalar uniqueness bridge for the clamped CndG line-search quotient.

No SOptLib match: searched target/SOptLib/Mathlib for "quadratic minimizer
interval min one", "line search quadratic argmin", and "quadratic square
minimizer"; hits covered compact argmin existence and unrelated quadratic
bounds, not uniqueness of the one-dimensional Eq. (7.2.5) clamp. -/
private theorem scalar_quadratic_interval_argmin_eq_min_one
    {α den q : ℝ} (hden : 0 < den) (hq0 : 0 ≤ q)
    (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hmin : ∀ a ∈ Set.Icc (0 : ℝ) 1,
      (den / 2) * α ^ 2 - den * q * α ≤
        (den / 2) * a ^ 2 - den * q * a) :
    α = min 1 q := by
  rcases hα with ⟨hα0, hα1⟩
  by_cases hq1 : q ≤ 1
  · have hqmem : q ∈ Set.Icc (0 : ℝ) 1 := ⟨hq0, hq1⟩
    have hle := hmin q hqmem
    have hdiff :
        ((den / 2) * α ^ 2 - den * q * α) -
            ((den / 2) * q ^ 2 - den * q * q) =
          (den / 2) * (α - q) ^ 2 := by
      ring
    have hle0 :
        ((den / 2) * α ^ 2 - den * q * α) -
            ((den / 2) * q ^ 2 - den * q * q) ≤ 0 :=
      sub_nonpos.mpr hle
    have hnonneg : 0 ≤ (den / 2) * (α - q) ^ 2 :=
      mul_nonneg (le_of_lt (half_pos hden)) (sq_nonneg _)
    have hprod_le : (den / 2) * (α - q) ^ 2 ≤ 0 := by
      nlinarith
    have hprod_eq : (den / 2) * (α - q) ^ 2 = 0 :=
      le_antisymm hprod_le hnonneg
    have hden_half_ne : den / 2 ≠ 0 := ne_of_gt (half_pos hden)
    have hsq : (α - q) ^ 2 = 0 := by
      rcases mul_eq_zero.mp hprod_eq with hzero | hzero
      · exact False.elim (hden_half_ne hzero)
      · exact hzero
    have hαq : α = q := by
      have hsub : α - q = 0 := sq_eq_zero_iff.mp hsq
      linarith
    simp [hq1, hαq]
  · have hqgt : 1 < q := lt_of_not_ge hq1
    have h1mem : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
    have hle := hmin 1 h1mem
    have hdiff :
        ((den / 2) * α ^ 2 - den * q * α) -
            ((den / 2) * 1 ^ 2 - den * q * 1) =
          (den / 2) * (α - 1) * (α + 1 - 2 * q) := by
      ring
    have hle0 :
        ((den / 2) * α ^ 2 - den * q * α) -
            ((den / 2) * 1 ^ 2 - den * q * 1) ≤ 0 :=
      sub_nonpos.mpr hle
    by_contra hαne
    have hmin_eq : min (1 : ℝ) q = 1 := by
      exact min_eq_left (le_of_lt hqgt)
    have hαne_one : α ≠ 1 := by
      intro hαone
      exact hαne (by simpa [hmin_eq] using hαone)
    have hαlt : α < 1 := lt_of_le_of_ne hα1 hαne_one
    have hleft_neg : α - 1 < 0 := by linarith
    have hright_neg : α + 1 - 2 * q < 0 := by linarith
    have hmul_pos : 0 < (α - 1) * (α + 1 - 2 * q) :=
      mul_pos_of_neg_of_neg hleft_neg hright_neg
    have hprod_pos : 0 < (den / 2) * ((α - 1) * (α + 1 - 2 * q)) :=
      mul_pos (half_pos hden) hmul_pos
    have hprod_le : (den / 2) * ((α - 1) * (α + 1 - 2 * q)) ≤ 0 := by
      nlinarith
    nlinarith

/-- Scalar expansion of the CndG line-search objective along the selected
segment, matching the quadratic in Eq. (7.2.5).

No SOptLib match: searched target/SOptLib/Mathlib for "inner product norm
square expansion" and "line search quadratic argmin"; existing hits are generic
norm-square or stochastic variance identities, not this paper-local shifted
CndG segment expansion. -/
private theorem cndG_line_search_objective_scalar_quadratic
    (S : Setup Ω Ξ E) (g u : E) (β : ℝ) (ut : E) (a : ℝ) :
    let v := S.cndGLinearOracle g u β ut
    let d := v - ut
    let den := β * ‖d‖ ^ 2
    let num := ⟪β • (u - ut) - g, d⟫_ℝ
    S.cndGLineSearchObjective g u β ut ((1 - a) • ut + a • v) =
      S.cndGLineSearchObjective g u β ut ut + (den / 2) * a ^ 2 - num * a := by
  classical
  let v := S.cndGLinearOracle g u β ut
  let d := v - ut
  have hseg : (1 - a) • ut + a • v = ut + a • d := by
    simp [d, sub_eq_add_neg, add_smul]
    module
  simp only
  rw [hseg]
  unfold cndGLineSearchObjective
  have hseg_sub : ut + a • d - u = (ut - u) + a • d := by
    abel
  rw [hseg_sub]
  simp [d, norm_add_sq_real, real_inner_self_eq_norm_sq,
    inner_add_left, inner_add_right, inner_sub_left, inner_sub_right, inner_smul_left,
    inner_smul_right, norm_smul, sq_abs]
  have habs_mul_sq : (|a| * ‖v - ut‖) ^ 2 = (a * ‖v - ut‖) ^ 2 := by
    rw [mul_pow, mul_pow, sq_abs]
  rw [habs_mul_sq]
  ring

/-- Quotient form of the CndG line search, Eq. (7.2.5), recorded as a derived
property of the interval minimizer when the displayed denominator is admissible.
The formula is for an algorithmic current iterate `u_t ∈ X`; feasibility is what
lets the linear oracle compare against `x = u_t` and proves that the lower clamp
is inactive.  The PDF displays the quotient but does not state the denominator
fact as a theorem hypothesis, so generated iterates do not use this quotient as
their definition. -/
theorem cndGStepsize_eq_quotient_7_2_5 (S : Setup Ω Ξ E)
    (g u : E) (β : ℝ) (ut : E) (hut : ut ∈ S.X)
    (hβ : 0 < β)
    (hden : let v := S.cndGLinearOracle g u β ut; β * ‖v - ut‖ ^ 2 ≠ 0) :
    let v := S.cndGLinearOracle g u β ut
    S.cndGStepsize g u β ut =
      min 1 (⟪β • (u - ut) - g, v - ut⟫_ℝ / (β * ‖v - ut‖ ^ 2)) := by
  classical
  have hquot_nonneg :=
    S.cndGStepsize_quotient_nonneg_of_current_mem g u β ut hut hβ hden
  let v := S.cndGLinearOracle g u β ut
  let d := v - ut
  let den := β * ‖d‖ ^ 2
  let num := ⟪β • (u - ut) - g, d⟫_ℝ
  let q := num / den
  let α := S.cndGStepsize g u β ut
  have hnorm_ne : ‖d‖ ^ 2 ≠ 0 := by
    intro hnorm
    exact hden (by simpa [v, d, den, hnorm])
  have hnorm_pos : 0 < ‖d‖ ^ 2 :=
    lt_of_le_of_ne (sq_nonneg ‖d‖) (Ne.symm hnorm_ne)
  have hden_pos : 0 < den := by
    simpa [den] using mul_pos hβ hnorm_pos
  have hden_ne : den ≠ 0 := ne_of_gt hden_pos
  have hq0 : 0 ≤ q := by
    simpa [q, num, den, d, v] using hquot_nonneg
  have hαmem : α ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [α] using S.cndGStepsize_mem g u β ut
  have hdenq : den * q = num := by
    dsimp [q]
    field_simp [hden_ne]
  have hmin_scalar : ∀ a ∈ Set.Icc (0 : ℝ) 1,
      (den / 2) * α ^ 2 - den * q * α ≤
        (den / 2) * a ^ 2 - den * q * a := by
    intro a ha
    have hobj :
        S.cndGLineSearchObjective g u β ut ((1 - α) • ut + α • v) ≤
          S.cndGLineSearchObjective g u β ut ((1 - a) • ut + a • v) := by
      simpa [α, v] using S.cndGStepsize_minimizes g u β ut a ha
    have hαexp :
        S.cndGLineSearchObjective g u β ut ((1 - α) • ut + α • v) =
          S.cndGLineSearchObjective g u β ut ut + (den / 2) * α ^ 2 - num * α := by
      simpa [α, v, d, den, num] using
        cndG_line_search_objective_scalar_quadratic S g u β ut α
    have haexp :
        S.cndGLineSearchObjective g u β ut ((1 - a) • ut + a • v) =
          S.cndGLineSearchObjective g u β ut ut + (den / 2) * a ^ 2 - num * a := by
      simpa [v, d, den, num] using
        cndG_line_search_objective_scalar_quadratic S g u β ut a
    have hdenqα : den * q * α = num * α := by rw [hdenq]
    have hdenqa : den * q * a = num * a := by rw [hdenq]
    nlinarith [hobj, hαexp, haexp, hdenqα, hdenqa]
  have hαeq := scalar_quadratic_interval_argmin_eq_min_one hden_pos hq0 hαmem hmin_scalar
  simpa [α, q, num, den, d, v] using hαeq

/-- A concrete singleton feasible-region model used only to certify that the
old arbitrary-current-point quotient theorem was false without `ut ∈ X`. -/
private noncomputable def cndGStepsizeEqQuotientCounterexampleSetup :
    Setup Unit Unit ℝ where
  X := ({0} : Set ℝ)
  fX := fun _ => 0
  fPrime := fun _ => 0
  L := 0
  σ := 0
  G := fun _ _ => 0
  hSFO_kernel_joint_measurable := by
    simpa using
      (measurable_const :
        Measurable
          (fun _ : {z : ℝ // z ∈ ({0} : Set ℝ)} × Unit => (0 : ℝ)))
  ξ := fun _ _ _ => ()
  P := default
  N := 1
  x0 := 0
  β := fun _ => 1
  γ := fun k => if k = 1 then 1 else 0
  η := fun _ => 1
  B := fun _ => ⟨1, by norm_num⟩
  hX_convex := by simp
  hX_compact := by simp
  hx0_mem := by simp
  hf_convex := by
    exact (convexOn_const (𝕜 := ℝ) (s := ({0} : Set ℝ)) (0 : ℝ) (by simp)).congr
      (by
        intro x hx
        change (0 : ℝ) =
          SOptLib.carrierTotalizeOn ({0} : Set ℝ) (fun _ => (0 : ℝ)) x
        simp [SOptLib.carrierTotalizeOn, hx])
  hf_closed_epigraph := by
    have hclosed : IsClosed ({p : ℝ × ℝ | p.1 = 0 ∧ 0 ≤ p.2} : Set (ℝ × ℝ)) := by
      exact (isClosed_singleton.preimage continuous_fst).inter
        (isClosed_Ici.preimage continuous_snd)
    convert hclosed using 1
    ext p
    constructor
    · intro hp
      rcases hp with ⟨hx, hle⟩
      exact ⟨by simpa using hx, by simpa using hle⟩
    · intro hp
      rcases hp with ⟨hfst, hsnd⟩
      exact ⟨by simpa using hfst, by simpa using hsnd⟩
  hfPrime_derivative := by
    intro x
    exact (hasGradientWithinAt_const (s := ({0} : Set ℝ)) (x := x.1)
      (c := (0 : ℝ))).congr_of_mem
        (by
          intro y hy
          change SOptLib.carrierTotalizeOn ({0} : Set ℝ) (fun _ => (0 : ℝ)) y = 0
          simp [SOptLib.carrierTotalizeOn, hy]) x.2
  hβ_pos := by
    intro _ _
    norm_num
  hγ_mem := by
    intro k _
    by_cases h : k = 1
    · simp [h]
    · simp [h]
  hη_nonneg := by
    intro _ _
    norm_num
  hγ_one := by simp
  hSmoothness := by
    intro _ _
    simp
  hparam_lower := by
    intro _ _
    norm_num

private theorem cndGStepsizeEqQuotientCounterexample_ut_not_mem :
    (1 : ℝ) ∉ cndGStepsizeEqQuotientCounterexampleSetup.X := by
  simp [cndGStepsizeEqQuotientCounterexampleSetup]

private theorem cndGStepsizeEqQuotientCounterexample_oracle :
    cndGStepsizeEqQuotientCounterexampleSetup.cndGLinearOracle (-1) 1 1 1 = 0 := by
  have hmem := cndGStepsizeEqQuotientCounterexampleSetup.cndGLinearOracle_mem (-1) 1 1 1
  simpa [cndGStepsizeEqQuotientCounterexampleSetup] using hmem

private theorem cndGStepsizeEqQuotientCounterexample_stepsize :
    cndGStepsizeEqQuotientCounterexampleSetup.cndGStepsize (-1) 1 1 1 = 0 := by
  let α := cndGStepsizeEqQuotientCounterexampleSetup.cndGStepsize (-1) 1 1 1
  have hαmem : α ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [α] using
      cndGStepsizeEqQuotientCounterexampleSetup.cndGStepsize_mem (-1) 1 1 1
  have hmin :=
    cndGStepsizeEqQuotientCounterexampleSetup.cndGStepsize_minimizes
      (-1) 1 1 1 0 (by norm_num)
  have hle : (2 : ℝ)⁻¹ * (α * α) + 1 ≤ inner ℝ (1 : ℝ) (1 - α) := by
    simpa [α, cndGLineSearchObjective, cndGStepsizeEqQuotientCounterexample_oracle,
      pow_two] using hmin
  have hinner : inner ℝ (1 : ℝ) (1 - α) = 1 - α := by
    convert RCLike.inner_apply (𝕜 := ℝ) (1 : ℝ) (1 - α) using 1
    simp
  rw [hinner] at hle
  have hnonneg : 0 ≤ α := hαmem.1
  have hsq_nonneg : 0 ≤ α ^ 2 := sq_nonneg α
  have : α = 0 := by nlinarith
  simpa [α] using this

/-- Formal falsity witness for the retired unguarded version of
`cndGStepsize_eq_quotient_7_2_5`.

The concrete model has `X = {0}` and current point `u_t = 1 ∉ X`.  The selected
line-search minimizer is `0`, while the unclamped quotient displayed by the old
arbitrary-`ut` statement is `-1`. -/
theorem cndGStepsize_eq_quotient_7_2_5_false_without_current_mem :
    ¬ (∀ (S : Setup Unit Unit ℝ) (g u : ℝ) (β : ℝ) (ut : ℝ),
      0 < β →
      (let v := S.cndGLinearOracle g u β ut; β * ‖v - ut‖ ^ 2 ≠ 0) →
      (let v := S.cndGLinearOracle g u β ut;
        S.cndGStepsize g u β ut =
          min 1 (inner ℝ (β • (u - ut) - g) (v - ut) / (β * ‖v - ut‖ ^ 2)))) := by
  intro hold
  have hden :
      (let v := cndGStepsizeEqQuotientCounterexampleSetup.cndGLinearOracle (-1) 1 1 1;
        (1 : ℝ) * ‖v - 1‖ ^ 2 ≠ 0) := by
    simp [cndGStepsizeEqQuotientCounterexample_oracle]
  have hformula :=
    hold cndGStepsizeEqQuotientCounterexampleSetup (-1) 1 1 1 (by norm_num) hden
  rw [cndGStepsizeEqQuotientCounterexample_stepsize] at hformula
  have hright :
      (let v := cndGStepsizeEqQuotientCounterexampleSetup.cndGLinearOracle (-1) 1 1 1;
        min 1 (inner ℝ ((1 : ℝ) • ((1 : ℝ) - 1) - (-1)) (v - 1) /
          ((1 : ℝ) * ‖v - 1‖ ^ 2))) = -1 := by
    simp [cndGStepsizeEqQuotientCounterexample_oracle]
  have hzero : (0 : ℝ) = -1 := Eq.trans hformula hright
  norm_num at hzero

/-- One inner CndG update, Algorithm 7.6 step 4.  The recursion uses the
division-free interval minimizer from Eq. (7.2.6); the quotient form in Eq. (7.2.5)
is a derived theorem under its denominator domain. -/
def cndGInnerUpdate (S : Setup Ω Ξ E) (g u : E) (β : ℝ) (ut : E) : E :=
  let α := S.cndGStepsize g u β ut
  let v := S.cndGLinearOracle g u β ut
  (1 - α) • ut + α • v

/-- Inner CndG trajectory with the paper indexing `u_1 = u`, Algorithm 7.6 step 1.

No SOptLib match: searched conditional-gradient update/iterate candidates.
`BlockIterateState` and `blockMirrorUpdate` are block-state abstractions, while
Algorithm 7.6 has a scalar CndG loop with a source-specific Wolfe stopping test.
The zero branch is only a Lean totalization helper; source-facing statements use
positive CndG indices.
-/
def cndGInnerIterate (S : Setup Ω Ξ E) (g u : E) (β : ℝ) : ℕ → E
  | 0 => u
  | 1 => u
  | t + 2 => S.cndGInnerUpdate g u β (S.cndGInnerIterate g u β (t + 1))

@[simp]
theorem cndGInnerIterate_one (S : Setup Ω Ξ E) (g u : E) (β : ℝ) :
    S.cndGInnerIterate g u β 1 = u := rfl

/-- Early feasibility bridge for generated CndG inner iterates.

This is placed before the termination obligation so the inner-loop proof can use
feasible-current facts without depending on the later selected-output API.
Search note: SOptLib's `conditionalGradientIterUpdate` helpers describe the
same affine pattern for finite-horizon Frank-Wolfe iterates, but Algorithm 7.6
uses this file's recursively generated `cndGInnerIterate`.
-/
private theorem cndGInnerIterate_mem_before_termination
    (S : Setup Ω Ξ E) (g u : E) (β : ℝ) (hu : u ∈ S.X) :
    ∀ t : ℕ, 1 ≤ t → S.cndGInnerIterate g u β t ∈ S.X := by
  have hupdate : ∀ ut : E, ut ∈ S.X → S.cndGInnerUpdate g u β ut ∈ S.X := by
    intro ut hut
    dsimp [cndGInnerUpdate]
    exact SOptLib.acceleratedSearchPoint_mem (X := S.X) S.hX_convex
      (S.cndGStepsize_mem g u β ut) hut (S.cndGLinearOracle_mem g u β ut)
  intro t ht
  induction t with
  | zero =>
      omega
  | succ t ih =>
      cases t with
      | zero =>
          simpa using hu
      | succ t =>
          dsimp [cndGInnerIterate]
          exact hupdate _ (ih (by omega))

/-- One-based successor normalization for Algorithm 7.6 inner iterates. -/
private theorem cndGInnerIterate_succ_of_one_le
    (S : Setup Ω Ξ E) (g u : E) (β : ℝ) {t : ℕ} (ht : 1 ≤ t) :
    S.cndGInnerIterate g u β (t + 1) =
      S.cndGInnerUpdate g u β (S.cndGInnerIterate g u β t) := by
  cases t with
  | zero =>
      omega
  | succ t =>
      cases t with
      | zero =>
          rfl
      | succ t =>
          rfl

/-- The paper step `λ_t = 2/(t+1)` lies in the line-search interval for `t ≥ 1`. -/
private theorem two_div_nat_succ_mem_Icc (t : ℕ) (ht : 1 ≤ t) :
    (2 : ℝ) / ((t + 1 : ℕ) : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  have hden_pos : 0 < ((t + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_pos t
  have htwo_le : (2 : ℝ) ≤ ((t + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ ht
  constructor
  · exact div_nonneg (by norm_num) (le_of_lt hden_pos)
  · have hdiv :
        (2 : ℝ) / ((t + 1 : ℕ) : ℝ) ≤
          ((t + 1 : ℕ) : ℝ) / ((t + 1 : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right htwo_le (le_of_lt hden_pos)
    calc
      (2 : ℝ) / ((t + 1 : ℕ) : ℝ) ≤
          ((t + 1 : ℕ) : ℝ) / ((t + 1 : ℕ) : ℝ) := hdiv
      _ = 1 := div_self (ne_of_gt hden_pos)

/-- Line-search comparison against any admissible point on the CndG segment.

This is the local Algorithm 7.6 specialization of the minimizer property in
Eq. (7.2.6). SOptLib one-step conditional-gradient descent lemmas were checked,
but they assume an already packaged smooth descent premise rather than this
paper-local shifted quadratic line-search objective.
-/
private theorem cndGLineSearchObjective_update_le_candidate
    (S : Setup Ω Ξ E) (g u : E) (β : ℝ) (ut : E) {a : ℝ}
    (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    let v := S.cndGLinearOracle g u β ut
    S.cndGLineSearchObjective g u β ut (S.cndGInnerUpdate g u β ut) ≤
      S.cndGLineSearchObjective g u β ut ((1 - a) • ut + a • v) := by
  simpa [cndGInnerUpdate] using S.cndGStepsize_minimizes g u β ut a ha

/-- Line-search comparison at the source proof's trial step `λ_t = 2/(t+1)`. -/
private theorem cndGLineSearchObjective_iterate_succ_le_two_div_candidate
    (S : Setup Ω Ξ E) (g u : E) (β : ℝ) {t : ℕ} (ht : 1 ≤ t) :
    let ut := S.cndGInnerIterate g u β t
    let v := S.cndGLinearOracle g u β ut
    let lam := (2 : ℝ) / ((t + 1 : ℕ) : ℝ)
    S.cndGLineSearchObjective g u β ut (S.cndGInnerIterate g u β (t + 1)) ≤
      S.cndGLineSearchObjective g u β ut ((1 - lam) • ut + lam • v) := by
  let ut := S.cndGInnerIterate g u β t
  let v := S.cndGLinearOracle g u β ut
  let lam := (2 : ℝ) / ((t + 1 : ℕ) : ℝ)
  change
    S.cndGLineSearchObjective g u β ut (S.cndGInnerIterate g u β (t + 1)) ≤
      S.cndGLineSearchObjective g u β ut ((1 - lam) • ut + lam • v)
  rw [cndGInnerIterate_succ_of_one_le S g u β ht]
  exact cndGLineSearchObjective_update_le_candidate S g u β ut
    (by simpa [lam] using two_div_nat_succ_mem_Icc t ht)

/-- Expansion of the CndG trial point in terms of the Wolfe gap.

This is the Eq. (7.2.5)/(7.2.26) algebraic bridge: the scalar quadratic
line-search expansion is rewritten from the quotient numerator into the
shifted Wolfe gap `V_{g,u,β}(u_t)`.
-/
private theorem cndGLineSearchObjective_candidate_eq_gap_quadratic
    (S : Setup Ω Ξ E) (g u : E) (β : ℝ) (ut : E) (a : ℝ) :
    let v := S.cndGLinearOracle g u β ut
    S.cndGLineSearchObjective g u β ut ((1 - a) • ut + a • v) =
      S.cndGLineSearchObjective g u β ut ut +
        (β * ‖v - ut‖ ^ 2 / 2) * a ^ 2 - S.cndGGap g u β ut * a := by
  classical
  let v := S.cndGLinearOracle g u β ut
  have hnum :
      ⟪β • (u - ut) - g, v - ut⟫_ℝ = S.cndGGap g u β ut := by
    have hvec : β • (u - ut) - g = -(g + β • (ut - u)) := by
      module
    have hdiff : -(v - ut) = ut - v := by
      abel
    calc
      ⟪β • (u - ut) - g, v - ut⟫_ℝ
          = ⟪-(g + β • (ut - u)), v - ut⟫_ℝ := by rw [hvec]
      _ = -⟪g + β • (ut - u), v - ut⟫_ℝ := by rw [inner_neg_left]
      _ = ⟪g + β • (ut - u), ut - v⟫_ℝ := by
        rw [← hdiff, inner_neg_right]
      _ = S.cndGGap g u β ut := by
        rfl
  have hquad := cndG_line_search_objective_scalar_quadratic S g u β ut a
  simpa [v, hnum, mul_comm, mul_left_comm, mul_assoc] using hquad

/-- The selected next CndG iterate is no worse than the source trial step,
after rewriting the trial objective through the Wolfe gap. -/
private theorem cndGLineSearchObjective_iterate_succ_le_gap_quadratic
    (S : Setup Ω Ξ E) (g u : E) (β : ℝ) {t : ℕ} (ht : 1 ≤ t) :
    let ut := S.cndGInnerIterate g u β t
    let v := S.cndGLinearOracle g u β ut
    let lam := (2 : ℝ) / ((t + 1 : ℕ) : ℝ)
    S.cndGLineSearchObjective g u β ut (S.cndGInnerIterate g u β (t + 1)) ≤
      S.cndGLineSearchObjective g u β ut ut +
        (β * ‖v - ut‖ ^ 2 / 2) * lam ^ 2 - S.cndGGap g u β ut * lam := by
  let ut := S.cndGInnerIterate g u β t
  let v := S.cndGLinearOracle g u β ut
  let lam := (2 : ℝ) / ((t + 1 : ℕ) : ℝ)
  calc
    S.cndGLineSearchObjective g u β ut (S.cndGInnerIterate g u β (t + 1))
        ≤ S.cndGLineSearchObjective g u β ut ((1 - lam) • ut + lam • v) := by
          simpa [ut, v, lam] using
            cndGLineSearchObjective_iterate_succ_le_two_div_candidate S g u β ht
    _ = S.cndGLineSearchObjective g u β ut ut +
        (β * ‖v - ut‖ ^ 2 / 2) * lam ^ 2 - S.cndGGap g u β ut * lam := by
          simpa [ut, v, lam] using
            cndGLineSearchObjective_candidate_eq_gap_quadratic S g u β ut lam

/-- The shifted CndG Wolfe gap is nonnegative at feasible current points. -/
private theorem cndGGap_nonneg_of_mem
    (S : Setup Ω Ξ E) (g u : E) (β : ℝ) {ut : E} (hut : ut ∈ S.X) :
    0 ≤ S.cndGGap g u β ut := by
  have hmax := S.cndGLinearOracle_isMax g u β ut ut hut
  simpa [cndGGap] using hmax

/-- The linear-oracle displacement is bounded by the feasible-set diameter. -/
private theorem cndGLinearOracle_displacement_norm_le_diameter
    (S : Setup Ω Ξ E) (g u : E) (β : ℝ) {ut : E} (hut : ut ∈ S.X) :
    ‖S.cndGLinearOracle g u β ut - ut‖ ≤ S.diameter := by
  rcases S.diameter_spec with ⟨_, _, _, _, _, hbound⟩
  exact hbound (S.cndGLinearOracle g u β ut) (S.cndGLinearOracle_mem g u β ut) ut hut

/-- Squared version of the CndG oracle displacement diameter bound. -/
private theorem cndGLinearOracle_displacement_sq_le_diameter_sq
    (S : Setup Ω Ξ E) (g u : E) (β : ℝ) {ut : E} (hut : ut ∈ S.X) :
    ‖S.cndGLinearOracle g u β ut - ut‖ ^ 2 ≤ S.diameter ^ 2 := by
  have hnorm := cndGLinearOracle_displacement_norm_le_diameter S g u β hut
  have hdiam_nonneg : 0 ≤ S.diameter :=
    le_trans (norm_nonneg _) hnorm
  have hnorm_nonneg : 0 ≤ ‖S.cndGLinearOracle g u β ut - ut‖ :=
    norm_nonneg _
  nlinarith

/-- CndG Wolfe gap controls the shifted quadratic objective residual.

This is Lan's local comparison `φ(u_t)-φ(x) ≤ V_{g,u,β}(u_t)`: the linear
oracle supplies the first-order term, and the nonnegative quadratic remainder is
dropped.  Considered SOptLib convex first-order-condition helpers and the local
line-search quadratic expansion; those concern minimizers or segment expansions,
while this proof needs the paper's literal Eq. (7.2.4) oracle comparison. -/
private theorem cndG_gap_controls_phi_suboptimality
    (S : Setup Ω Ξ E) (g u : E) (β : ℝ) {ut x : E}
    (hβ_nonneg : 0 ≤ β) (hx : x ∈ S.X) :
    S.cndGLineSearchObjective g u β ut ut -
        S.cndGLineSearchObjective g u β ut x ≤
      S.cndGGap g u β ut := by
  have hlin := S.cndGLinearOracle_isMax g u β ut x hx
  have hlin_gap :
      ⟪g + β • (ut - u), ut - x⟫_ℝ ≤ S.cndGGap g u β ut := by
    simpa [cndGGap] using hlin
  have hidentity :
      S.cndGLineSearchObjective g u β ut ut -
          S.cndGLineSearchObjective g u β ut x =
        ⟪g + β • (ut - u), ut - x⟫_ℝ -
          β / 2 * ‖ut - x‖ ^ 2 := by
    unfold cndGLineSearchObjective
    have hx_sub : x - u = (ut - u) - (ut - x) := by
      abel
    rw [hx_sub]
    simp [norm_sub_sq_real, real_inner_self_eq_norm_sq, inner_add_left,
      inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      real_inner_comm]
    ring
  have hquad_nonneg : 0 ≤ β / 2 * ‖ut - x‖ ^ 2 := by
    exact mul_nonneg (by positivity) (sq_nonneg _)
  nlinarith [hidentity, hlin_gap, hquad_nonneg]

/-- One-step residual recursion behind Lan Eq. (7.2.25).

This aligns with the source recurrence before Eq. (7.2.25): combine the exact
CndG line-search comparison, the Eq. (7.2.4) Wolfe-gap control of
`φ(u_t)-φ(x)`, and the feasible-set diameter bound on `‖v_t-u_t‖`.  SOptLib's
weighted recurrence telescope was considered, but it starts after this local
paper-specific CndG recurrence has already been assembled. -/
private theorem cndG_phi_one_step_residual_recursion
    (S : Setup Ω Ξ E) (g u : E) (β : ℝ)
    (hu : u ∈ S.X) (hβ : 0 < β) {t : ℕ} (ht : 1 ≤ t) {x : E}
    (hx : x ∈ S.X) :
    let ut := S.cndGInnerIterate g u β t
    let lam := (2 : ℝ) / (((t + 1 : ℕ) : ℝ))
    S.cndGLineSearchObjective g u β ut (S.cndGInnerIterate g u β (t + 1)) -
        S.cndGLineSearchObjective g u β ut x ≤
      (1 - lam) *
          (S.cndGLineSearchObjective g u β ut ut -
            S.cndGLineSearchObjective g u β ut x) +
        (β * S.diameter ^ 2 / 2) * lam ^ 2 := by
  let ut := S.cndGInnerIterate g u β t
  let v := S.cndGLinearOracle g u β ut
  let lam := (2 : ℝ) / (((t + 1 : ℕ) : ℝ))
  have hstep := cndGLineSearchObjective_iterate_succ_le_gap_quadratic S g u β ht
  have hgap :=
    cndG_gap_controls_phi_suboptimality S g u β (le_of_lt hβ) (ut := ut) (x := x) hx
  have hut_mem : ut ∈ S.X :=
    cndGInnerIterate_mem_before_termination S g u β hu t ht
  have hdiam := cndGLinearOracle_displacement_sq_le_diameter_sq S g u β hut_mem
  have hlam_nonneg : 0 ≤ lam := by
    dsimp [lam]
    positivity
  have hquad_le :
      (β * ‖v - ut‖ ^ 2 / 2) * lam ^ 2 ≤
        (β * S.diameter ^ 2 / 2) * lam ^ 2 := by
    have hcoef : β / 2 * ‖v - ut‖ ^ 2 ≤ β / 2 * S.diameter ^ 2 := by
      exact mul_le_mul_of_nonneg_left hdiam (by positivity)
    nlinarith [sq_nonneg lam]
  change
    S.cndGLineSearchObjective g u β ut (S.cndGInnerIterate g u β (t + 1)) -
        S.cndGLineSearchObjective g u β ut x ≤
      (1 - lam) *
          (S.cndGLineSearchObjective g u β ut ut -
            S.cndGLineSearchObjective g u β ut x) +
        (β * S.diameter ^ 2 / 2) * lam ^ 2
  change S.cndGLineSearchObjective g u β ut (S.cndGInnerIterate g u β (t + 1)) ≤
      S.cndGLineSearchObjective g u β ut ut +
        (β * ‖v - ut‖ ^ 2 / 2) * lam ^ 2 - S.cndGGap g u β ut * lam at hstep
  nlinarith [hstep, hgap, hquad_le, hlam_nonneg]

/-- Lan Eq. (7.2.25) residual estimate for the CndG quadratic objective.

This is the first-class source bridge requested for the shifted telescope:
starting from the one-step residual recursion, the source weights
`λ_{t+1}=2/(t+1)` give `φ(u_{t+1})-φ(x) ≤ 2βD²/(t+1)`.  The SOptLib weighted
recurrence telescope was checked, but its `Γ`-weighted interface is heavier than
this one-dimensional post-specialization induction. -/
private theorem cndG_phi_residual_bound_7_2_25
    (S : Setup Ω Ξ E) (g u : E) (β : ℝ)
    (hu : u ∈ S.X) (hβ : 0 < β) {t : ℕ} (ht : 1 ≤ t) {x : E}
    (hx : x ∈ S.X) :
    S.cndGLineSearchObjective g u β
        (S.cndGInnerIterate g u β (t + 1))
        (S.cndGInnerIterate g u β (t + 1)) -
      S.cndGLineSearchObjective g u β x x ≤
        2 * β * S.diameter ^ 2 / (((t + 1 : ℕ) : ℝ)) := by
  let A : ℝ := β * S.diameter ^ 2
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    nlinarith [le_of_lt hβ, sq_nonneg S.diameter]
  refine Nat.le_induction ?base ?step t ht
  · have hrec :=
      cndG_phi_one_step_residual_recursion
        S g u β hu hβ (t := 1) le_rfl (x := x) hx
    have hrec' :
        S.cndGLineSearchObjective g u β
            (S.cndGInnerIterate g u β 2)
            (S.cndGInnerIterate g u β 2) -
          S.cndGLineSearchObjective g u β x x ≤ A / 2 := by
      simpa [A, cndGLineSearchObjective] using hrec
    have htarget : A / 2 ≤ 2 * β * S.diameter ^ 2 / (((1 + 1 : ℕ) : ℝ)) := by
      dsimp [A]
      norm_num
      nlinarith [hA_nonneg]
    exact le_trans hrec' htarget
  · intro n hn ih
    have hn1 : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
    let lam : ℝ := (2 : ℝ) / (((n + 1 + 1 : ℕ) : ℝ))
    have hrec :=
      cndG_phi_one_step_residual_recursion
        S g u β hu hβ (t := n + 1) hn1 (x := x) hx
    have hcoef_nonneg : 0 ≤ 1 - lam := by
      have htwo_le : (2 : ℝ) ≤ (((n + 1 + 1 : ℕ) : ℝ)) := by
        exact_mod_cast (show 2 ≤ n + 1 + 1 by omega)
      have hden_pos : 0 < (((n + 1 + 1 : ℕ) : ℝ)) := by
        exact_mod_cast Nat.succ_pos (n + 1)
      have hle_one : lam ≤ 1 := by
        dsimp [lam]
        have hdiv :
            (2 : ℝ) / (((n + 1 + 1 : ℕ) : ℝ)) ≤
              (((n + 1 + 1 : ℕ) : ℝ)) / (((n + 1 + 1 : ℕ) : ℝ)) :=
          div_le_div_of_nonneg_right htwo_le (le_of_lt hden_pos)
        calc
          (2 : ℝ) / (((n + 1 + 1 : ℕ) : ℝ)) ≤
              (((n + 1 + 1 : ℕ) : ℝ)) / (((n + 1 + 1 : ℕ) : ℝ)) := hdiv
          _ = 1 := div_self (ne_of_gt hden_pos)
      exact sub_nonneg.mpr hle_one
    have ih_ut :
        S.cndGLineSearchObjective g u β
            (S.cndGInnerIterate g u β (n + 1))
            (S.cndGInnerIterate g u β (n + 1)) -
          S.cndGLineSearchObjective g u β
            (S.cndGInnerIterate g u β (n + 1)) x ≤
          2 * β * S.diameter ^ 2 / (((n + 1 : ℕ) : ℝ)) := by
      simpa [cndGLineSearchObjective] using ih
    have hmul_ih :
        (1 - lam) *
            (S.cndGLineSearchObjective g u β
              (S.cndGInnerIterate g u β (n + 1))
              (S.cndGInnerIterate g u β (n + 1)) -
                S.cndGLineSearchObjective g u β
                  (S.cndGInnerIterate g u β (n + 1)) x) ≤
          (1 - lam) * (2 * β * S.diameter ^ 2 /
            (((n + 1 : ℕ) : ℝ))) := by
      exact mul_le_mul_of_nonneg_left ih_ut hcoef_nonneg
    have hrec_norm :
        S.cndGLineSearchObjective g u β
            (S.cndGInnerIterate g u β (n + 1 + 1))
            (S.cndGInnerIterate g u β (n + 1 + 1)) -
          S.cndGLineSearchObjective g u β x x ≤
            (1 - lam) *
              (S.cndGLineSearchObjective g u β
                (S.cndGInnerIterate g u β (n + 1))
                (S.cndGInnerIterate g u β (n + 1)) -
                  S.cndGLineSearchObjective g u β
                    (S.cndGInnerIterate g u β (n + 1)) x) +
              (A / 2) * lam ^ 2 := by
      simpa [lam, A, cndGLineSearchObjective] using hrec
    have hbound :
        S.cndGLineSearchObjective g u β
            (S.cndGInnerIterate g u β (n + 1 + 1))
            (S.cndGInnerIterate g u β (n + 1 + 1)) -
          S.cndGLineSearchObjective g u β x x ≤
            (1 - lam) * (2 * β * S.diameter ^ 2 /
              (((n + 1 : ℕ) : ℝ))) +
              (A / 2) * lam ^ 2 := by
      nlinarith [hrec_norm, hmul_ih]
    have hscalar :
        (1 - lam) * (2 * β * S.diameter ^ 2 /
            (((n + 1 : ℕ) : ℝ))) +
            (A / 2) * lam ^ 2 ≤
          2 * β * S.diameter ^ 2 / (((n + 1 + 1 : ℕ) : ℝ)) := by
      have hden1_pos : 0 < (((n + 1 : ℕ) : ℝ)) := by
        exact_mod_cast Nat.succ_pos n
      have hden2_pos : 0 < (((n + 1 + 1 : ℕ) : ℝ)) := by
        exact_mod_cast Nat.succ_pos (n + 1)
      dsimp [lam, A]
      field_simp [ne_of_gt hden1_pos, ne_of_gt hden2_pos]
      ring_nf
      have hsq_nonneg : 0 ≤ S.diameter ^ 2 := sq_nonneg S.diameter
      have hdiff :
          -(S.diameter ^ 2 * ((2 + n : ℕ) : ℝ) * 2) +
              S.diameter ^ 2 * ((2 + n : ℕ) : ℝ) ^ 2 +
              S.diameter ^ 2 * ((1 + n : ℕ) : ℝ) -
              S.diameter ^ 2 * ((2 + n : ℕ) : ℝ) *
                ((1 + n : ℕ) : ℝ) =
            -S.diameter ^ 2 := by
        norm_num
        ring_nf
      nlinarith [hsq_nonneg, hdiff]
    exact le_trans hbound hscalar

/-- Positive ceiling choice turns a gap bound `A/(T+1)` into a stop bound.

This isolates the scalar part of Theorem 7.9(c)'s final termination step, using
the SOptLib positive-ceiling lower bound rather than Lean's total division
fallback.
-/
private theorem positive_ceiling_turns_gap_bound_into_stop
    (A η : ℝ) (hA : 0 ≤ A) (hη : 0 < η) :
    let T : ℕ := max 1 (Nat.ceil (A / η))
    A / (((T + 1 : ℕ) : ℝ)) ≤ η := by
  let T : ℕ := max 1 (Nat.ceil (A / η))
  have hceil : A / η ≤ (T : ℝ) := by
    simpa [T] using le_positive_ceil_max_one (A / η)
  have hη_nonneg : 0 ≤ η := le_of_lt hη
  have hη_ne : η ≠ 0 := ne_of_gt hη
  have hA_le_ηT : A ≤ η * (T : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hceil hη_nonneg
    have hleft : η * (A / η) = A := by
      field_simp [hη_ne]
    nlinarith
  have hT_le_succ : (T : ℝ) ≤ (((T + 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.le_succ T
  have hA_le_η_succ : A ≤ η * (((T + 1 : ℕ) : ℝ)) := by
    have hmul := mul_le_mul_of_nonneg_left hT_le_succ hη_nonneg
    nlinarith
  have hden_pos : 0 < (((T + 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.succ_pos T
  rw [div_le_iff₀ hden_pos]
  exact hA_le_η_succ

/-- Sum of the one-based real weights used in Eq. (7.2.26).

The pre-searched CndG/SOptLib candidates were considered before adding this
local scalar helper: `finset_weighted_residual_sum_eq_zero` and variance
helpers are Hilbert centering facts, while `finite_window_weighted_recurrence_`
telescopes recurrences rather than the final triangular-weight arithmetic. -/
private theorem sum_Icc_one_to_nat_cast (T : ℕ) :
    Finset.sum (Finset.Icc 1 T) (fun j => (j : ℝ)) =
      (T : ℝ) * (((T + 1 : ℕ) : ℝ)) / 2 := by
  induction T with
  | zero =>
      simp
  | succ T ih =>
      have htop : 1 ≤ T + 1 := Nat.succ_pos T
      rw [Finset.sum_Icc_succ_top htop, ih]
      norm_num
      ring

/-- Finite weighted-average extraction for Lan Eq. (7.2.26).

This is the purely scalar last step after the weighted Wolfe-gap telescope:
if the weighted sum of nonnegative gaps is at most `3*T*A`, then some
one-based inner iterate has gap at most `6*A/(T+1)`.  Considered
`Finset.exists_le_of_sum_le`, but its direct sum-comparison form does not
package the positive natural weights and triangular identity required here. -/
private theorem finite_weighted_gap_sum_yields_exists_small_gap
    (T : ℕ) (A : ℝ) (gap : ℕ → ℝ)
    (hT_pos : 1 ≤ T) (_hA_nonneg : 0 ≤ A)
    (_hgap_nonneg : ∀ j, j ∈ Finset.Icc 1 T → 0 ≤ gap j)
    (hsum : Finset.sum (Finset.Icc 1 T) (fun j => (j : ℝ) * gap j) ≤
      3 * (T : ℝ) * A) :
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ T ∧ gap j ≤
      6 * A / (((T + 1 : ℕ) : ℝ)) := by
  classical
  let B : ℝ := 6 * A / (((T + 1 : ℕ) : ℝ))
  have hden_pos : 0 < (((T + 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.succ_pos T
  have hden_ne : (((T + 1 : ℕ) : ℝ)) ≠ 0 := ne_of_gt hden_pos
  have hs_nonempty : (Finset.Icc 1 T).Nonempty := by
    exact ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hT_pos⟩⟩
  have hsumB :
      Finset.sum (Finset.Icc 1 T) (fun j => (j : ℝ) * B) =
        3 * (T : ℝ) * A := by
    calc
      Finset.sum (Finset.Icc 1 T) (fun j => (j : ℝ) * B)
          = Finset.sum (Finset.Icc 1 T) (fun j => (j : ℝ)) * B := by
            rw [Finset.sum_mul]
      _ = ((T : ℝ) * (((T + 1 : ℕ) : ℝ)) / 2) * B := by
            rw [sum_Icc_one_to_nat_cast]
      _ = 3 * (T : ℝ) * A := by
            dsimp [B]
            field_simp [hden_ne]
            ring
  have hle_sum :
      Finset.sum (Finset.Icc 1 T)
          (fun j => (j : ℝ) * gap j) ≤
        Finset.sum (Finset.Icc 1 T) (fun j => (j : ℝ) * B) := by
    rw [hsumB]
    exact hsum
  rcases Finset.exists_le_of_sum_le hs_nonempty hle_sum with ⟨j, hjmem, hjmul⟩
  have hj_bounds := Finset.mem_Icc.mp hjmem
  have hj_pos_real : 0 < (j : ℝ) := by
    exact_mod_cast hj_bounds.1
  have hgap_le_B : gap j ≤ B := by
    exact le_of_mul_le_mul_left hjmul hj_pos_real
  refine ⟨j, hj_bounds.1, hj_bounds.2, ?_⟩
  simpa [B] using hgap_le_B

/-- One-step Wolfe-gap inequality used in the weighted Eq. (7.2.26) telescope.

This specializes the already proved line-search gap-quadratic comparison and
the CndG diameter displacement bound; SOptLib's general nonconvex conditional
gradient one-step wrappers were considered but target a different smooth-model
interface rather than this paper-local shifted quadratic `φ`. -/
private theorem cndG_wolfe_gap_one_step_le_phi_drop_add_diameter
    (S : Setup Ω Ξ E) (g u : E) (β : ℝ)
    (hu : u ∈ S.X) (hβ : 0 < β) {j : ℕ} (hj : 1 ≤ j) :
    let ut := S.cndGInnerIterate g u β j
    let lam := (2 : ℝ) / (((j + 1 : ℕ) : ℝ))
    lam * S.cndGGap g u β ut ≤
      S.cndGLineSearchObjective g u β ut ut -
        S.cndGLineSearchObjective g u β ut (S.cndGInnerIterate g u β (j + 1)) +
          (β * S.diameter ^ 2 / 2) * lam ^ 2 := by
  let ut := S.cndGInnerIterate g u β j
  let v := S.cndGLinearOracle g u β ut
  let lam := (2 : ℝ) / (((j + 1 : ℕ) : ℝ))
  have hstep := cndGLineSearchObjective_iterate_succ_le_gap_quadratic S g u β hj
  have hut_mem : ut ∈ S.X := by
    exact cndGInnerIterate_mem_before_termination S g u β hu j hj
  have hdiam := cndGLinearOracle_displacement_sq_le_diameter_sq S g u β hut_mem
  have hquad_le :
      (β * ‖v - ut‖ ^ 2 / 2) * lam ^ 2 ≤
        (β * S.diameter ^ 2 / 2) * lam ^ 2 := by
    have hcoef : β / 2 * ‖v - ut‖ ^ 2 ≤ β / 2 * S.diameter ^ 2 := by
      exact mul_le_mul_of_nonneg_left hdiam (by positivity)
    nlinarith [sq_nonneg lam]
  change lam * S.cndGGap g u β ut ≤
    S.cndGLineSearchObjective g u β ut ut -
      S.cndGLineSearchObjective g u β ut (S.cndGInnerIterate g u β (j + 1)) +
        (β * S.diameter ^ 2 / 2) * lam ^ 2
  change S.cndGLineSearchObjective g u β ut (S.cndGInnerIterate g u β (j + 1)) ≤
      S.cndGLineSearchObjective g u β ut ut +
        (β * ‖v - ut‖ ^ 2 / 2) * lam ^ 2 - S.cndGGap g u β ut * lam at hstep
  nlinarith [hstep, hquad_le]

/-- Pure scalar increasing-coefficient Delta-drop bound for Eq. (7.2.26).

This is the narrow finite-sum arithmetic still missing after Eq. (7.2.25):
the increasing coefficients `j*(j+2)/2` telescope against the shifted residuals,
with the terminal negative term dropped by nonnegativity.  SOptLib's existing
two-coefficient telescope has the wrong monotonicity direction for these source
weights, so this local scalar bridge records the exact remaining shape. -/
private theorem shifted_delta_drop_sum_le_two_mul
    (T : ℕ) (A : ℝ) (Delta : ℕ → ℝ)
    (hT_pos : 1 ≤ T) (hA_nonneg : 0 ≤ A)
    (hDelta_nonneg : ∀ n, 2 ≤ n → 0 ≤ Delta n)
    (hDelta_bound : ∀ t, 1 ≤ t →
      Delta (t + 1) ≤ 2 * A / (((t + 1 : ℕ) : ℝ))) :
    Finset.sum (Finset.Icc 1 T)
        (fun j => ((j : ℝ) * (((j + 2 : ℕ) : ℝ)) / 2) *
          (Delta (j + 1) - Delta (j + 2))) ≤
      2 * (T : ℝ) * A := by
  classical
  let c : ℕ → ℝ := fun j => ((j : ℝ) * (((j + 2 : ℕ) : ℝ)) / 2)
  have htelescope_all : ∀ N : ℕ,
      Finset.sum (Finset.Icc 1 N)
          (fun j => c j * (Delta (j + 1) - Delta (j + 2))) =
        Finset.sum (Finset.Icc 1 N)
          (fun j => (c j - c (j - 1)) * Delta (j + 1)) -
          c N * Delta (N + 2) := by
    intro N
    induction N with
    | zero =>
        simp [c]
    | succ n ih =>
        have htop : 1 ≤ n + 1 := by omega
        rw [Finset.sum_Icc_succ_top htop, Finset.sum_Icc_succ_top htop, ih]
        simp [c]
        ring
  have htelescope := htelescope_all T
  have htail_nonneg : 0 ≤ c T * Delta (T + 2) := by
    have hc_nonneg : 0 ≤ c T := by
      dsimp [c]
      positivity
    have hD_nonneg : 0 ≤ Delta (T + 2) := hDelta_nonneg (T + 2) (by omega)
    exact mul_nonneg hc_nonneg hD_nonneg
  have hdrop_le :
      Finset.sum (Finset.Icc 1 T)
          (fun j => c j * (Delta (j + 1) - Delta (j + 2))) ≤
        Finset.sum (Finset.Icc 1 T)
          (fun j => (c j - c (j - 1)) * Delta (j + 1)) := by
    rw [htelescope]
    linarith
  have hterm : ∀ j, j ∈ Finset.Icc 1 T →
      (c j - c (j - 1)) * Delta (j + 1) ≤ 2 * A := by
    intro j hj
    have hj_bounds := Finset.mem_Icc.mp hj
    have hcoef_eq : c j - c (j - 1) = (2 * (j : ℝ) + 1) / 2 := by
      dsimp [c]
      have hj_sub : j - 1 + 2 = j + 1 := by omega
      rw [hj_sub]
      rw [Nat.cast_sub hj_bounds.1]
      norm_num
      ring
    have hcoef_nonneg : 0 ≤ c j - c (j - 1) := by
      rw [hcoef_eq]
      nlinarith [show (0 : ℝ) ≤ j by exact_mod_cast Nat.zero_le j]
    have hD_bound := hDelta_bound j hj_bounds.1
    have hmul := mul_le_mul_of_nonneg_left hD_bound hcoef_nonneg
    have hscalar : (c j - c (j - 1)) *
        (2 * A / (((j + 1 : ℕ) : ℝ))) ≤ 2 * A := by
      rw [hcoef_eq]
      have hden_pos : 0 < (((j + 1 : ℕ) : ℝ)) := by
        exact_mod_cast Nat.succ_pos j
      have hnum_le :
          (2 * (j : ℝ) + 1) * A ≤
            (2 * (((j + 1 : ℕ) : ℝ))) * A := by
        have hbase : 2 * (j : ℝ) + 1 ≤
            2 * (((j + 1 : ℕ) : ℝ)) := by
          norm_num
          nlinarith
        exact mul_le_mul_of_nonneg_right hbase hA_nonneg
      field_simp [ne_of_gt hden_pos]
      nlinarith
    exact le_trans hmul hscalar
  calc
    Finset.sum (Finset.Icc 1 T)
        (fun j => ((j : ℝ) * (((j + 2 : ℕ) : ℝ)) / 2) *
          (Delta (j + 1) - Delta (j + 2)))
        = Finset.sum (Finset.Icc 1 T)
          (fun j => c j * (Delta (j + 1) - Delta (j + 2))) := by simp [c]
    _ ≤ Finset.sum (Finset.Icc 1 T)
          (fun j => (c j - c (j - 1)) * Delta (j + 1)) := hdrop_le
    _ ≤ Finset.sum (Finset.Icc 1 T) (fun _j => 2 * A) := by
          exact Finset.sum_le_sum hterm
    _ = 2 * (T : ℝ) * A := by
          rw [Finset.sum_const]
          have hcard : (Finset.Icc 1 T).card = T := by
            rw [Nat.card_Icc]
            omega
          simp [hcard]
          ring

/-- Pure scalar shifted Delta telescope for Lan Eq. (7.2.26).

This is the remaining arithmetic after the CndG proof has produced Eq.
(7.2.25) and the shifted one-step Wolfe inequality.  Considered
`finite_window_weighted_recurrence_telescope_with_tail_sums` and
`SOptLib.sum_Icc_two_coeff_telescope_le`; the former is a Γ-recurrence theorem
for a different normal form, while the latter handles decreasing adjacent
coefficients and does not cover the increasing `j*(j+2)/2` weights here. -/
private theorem shifted_weighted_delta_telescope_sum_bound
    (T : ℕ) (A : ℝ) (Delta gap : ℕ → ℝ)
    (hT_pos : 1 ≤ T) (hA_nonneg : 0 ≤ A)
    (hDelta_nonneg : ∀ n, 2 ≤ n → 0 ≤ Delta n)
    (hDelta_bound : ∀ t, 1 ≤ t →
      Delta (t + 1) ≤ 2 * A / (((t + 1 : ℕ) : ℝ)))
    (hstep : ∀ j, j ∈ Finset.Icc 1 T →
      (j : ℝ) * gap j ≤
        ((j : ℝ) * (((j + 2 : ℕ) : ℝ)) / 2) *
            (Delta (j + 1) - Delta (j + 2)) +
          A * (j : ℝ) / (((j + 2 : ℕ) : ℝ))) :
    Finset.sum (Finset.Icc 1 T) (fun j => (j : ℝ) * gap j) ≤
      3 * (T : ℝ) * A := by
  classical
  let drop : ℕ → ℝ := fun j =>
    ((j : ℝ) * (((j + 2 : ℕ) : ℝ)) / 2) *
      (Delta (j + 1) - Delta (j + 2))
  let tail : ℕ → ℝ := fun j => A * (j : ℝ) / (((j + 2 : ℕ) : ℝ))
  have hsum_step :
      Finset.sum (Finset.Icc 1 T) (fun j => (j : ℝ) * gap j) ≤
        Finset.sum (Finset.Icc 1 T) (fun j => drop j + tail j) := by
    exact Finset.sum_le_sum (fun j hj => by
      simpa [drop, tail] using hstep j hj)
  have hdrop :
      Finset.sum (Finset.Icc 1 T) drop ≤ 2 * (T : ℝ) * A := by
    simpa [drop] using
      shifted_delta_drop_sum_le_two_mul
        T A Delta hT_pos hA_nonneg hDelta_nonneg hDelta_bound
  have htail_point : ∀ j, j ∈ Finset.Icc 1 T → tail j ≤ A := by
    intro j hj
    have hden_pos : 0 < (((j + 2 : ℕ) : ℝ)) := by
      exact_mod_cast Nat.succ_pos (j + 1)
    have hj_le : (j : ℝ) ≤ (((j + 2 : ℕ) : ℝ)) := by
      exact_mod_cast (show j ≤ j + 2 by omega)
    have hfrac_le : (j : ℝ) / (((j + 2 : ℕ) : ℝ)) ≤ 1 := by
      have hdiv :
          (j : ℝ) / (((j + 2 : ℕ) : ℝ)) ≤
            (((j + 2 : ℕ) : ℝ)) / (((j + 2 : ℕ) : ℝ)) :=
        div_le_div_of_nonneg_right hj_le (le_of_lt hden_pos)
      calc
        (j : ℝ) / (((j + 2 : ℕ) : ℝ)) ≤
            (((j + 2 : ℕ) : ℝ)) / (((j + 2 : ℕ) : ℝ)) := hdiv
        _ = 1 := div_self (ne_of_gt hden_pos)
    have hmul := mul_le_mul_of_nonneg_left hfrac_le hA_nonneg
    simpa [tail, div_eq_mul_inv, mul_assoc] using hmul
  have htail :
      Finset.sum (Finset.Icc 1 T) tail ≤ (T : ℝ) * A := by
    calc
      Finset.sum (Finset.Icc 1 T) tail
          ≤ Finset.sum (Finset.Icc 1 T) (fun _ => A) := by
            exact Finset.sum_le_sum htail_point
      _ = (T : ℝ) * A := by
            rw [Finset.sum_const]
            simp [hT_pos]
  calc
    Finset.sum (Finset.Icc 1 T) (fun j => (j : ℝ) * gap j)
        ≤ Finset.sum (Finset.Icc 1 T) (fun j => drop j + tail j) := hsum_step
    _ = Finset.sum (Finset.Icc 1 T) drop +
          Finset.sum (Finset.Icc 1 T) tail := by
          rw [Finset.sum_add_distrib]
    _ ≤ 3 * (T : ℝ) * A := by
          nlinarith [hdrop, htail]

/-- Shifted weighted Wolfe-gap sum for the CndG inner loop.

This is the corrected performed-update form of Lan Eq. (7.2.26)'s telescope:
the stopping index is one-based, so the finite window controls gaps at
`u_{j+1}` after `j` inner updates.  Candidates considered before adding this
local bridge: `weighted_gap_sum_bound_of_active_one_step_and_budget` is an
active-window aggregation wrapper, `sum_Icc_le_gap_add_sum_of_lagged_step`
telescopes a different lagged recurrence, and the pre-searched Bregman/oracle
variance candidates are unrelated to this deterministic CndG φ-telescope.
-/
private theorem cndG_shifted_weighted_gap_sum_bound
    (S : Setup Ω Ξ E) (g u : E) (β : ℝ)
    (hu : u ∈ S.X) (hβ : 0 < β) (T : ℕ) (_hT_pos : 1 ≤ T) :
    Finset.sum (Finset.Icc 1 T)
        (fun j => (j : ℝ) *
          S.cndGGap g u β (S.cndGInnerIterate g u β (j + 1))) ≤
      3 * (T : ℝ) * (β * S.diameter ^ 2) := by
  classical
  let phi : E → ℝ := fun y => S.cndGLineSearchObjective g u β y y
  let A : ℝ := β * S.diameter ^ 2
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    nlinarith [le_of_lt hβ, sq_nonneg S.diameter]
  have hphi_cont : ContinuousOn phi S.X := by
    have hcont_global : Continuous phi := by
      dsimp [phi]
      unfold cndGLineSearchObjective
      exact (continuous_const.inner continuous_id).add
        (continuous_const.mul (((continuous_id.sub continuous_const).norm).pow 2))
    exact hcont_global.continuousOn
  obtain ⟨xMinSub, hxMinSub_min⟩ :=
    SOptLib.objectiveMinimum_exists_of_isCompact_continuousOn
      phi S.hX_compact ⟨S.x0, S.hx0_mem⟩ hphi_cont
  let xMin : E := xMinSub
  have hxMin : xMin ∈ S.X := xMinSub.property
  have hxMin_min : ∀ y : E, y ∈ S.X → phi xMin ≤ phi y := by
    intro y hy
    exact hxMinSub_min ⟨y, hy⟩
  let Delta : ℕ → ℝ := fun n => phi (S.cndGInnerIterate g u β n) - phi xMin
  let gap : ℕ → ℝ := fun j =>
    S.cndGGap g u β (S.cndGInnerIterate g u β (j + 1))
  have hDelta_nonneg : ∀ n, 2 ≤ n → 0 ≤ Delta n := by
    intro n hn
    have hmem : S.cndGInnerIterate g u β n ∈ S.X := by
      exact cndGInnerIterate_mem_before_termination S g u β hu n (by omega)
    exact sub_nonneg.mpr (hxMin_min _ hmem)
  have hDelta_bound : ∀ t, 1 ≤ t →
      Delta (t + 1) ≤ 2 * A / (((t + 1 : ℕ) : ℝ)) := by
    intro t ht
    have hres :=
      cndG_phi_residual_bound_7_2_25
        S g u β hu hβ (t := t) ht (x := xMin) hxMin
    have hres' :
        Delta (t + 1) ≤
          2 * β * S.diameter ^ 2 / (((t + 1 : ℕ) : ℝ)) := by
      simpa [Delta, phi, cndGLineSearchObjective] using hres
    have hrhs :
        2 * β * S.diameter ^ 2 / (((t + 1 : ℕ) : ℝ)) =
          2 * A / (((t + 1 : ℕ) : ℝ)) := by
      dsimp [A]
      ring
    rwa [hrhs] at hres'
  have hstep : ∀ j, j ∈ Finset.Icc 1 T →
      (j : ℝ) * gap j ≤
        ((j : ℝ) * (((j + 2 : ℕ) : ℝ)) / 2) *
            (Delta (j + 1) - Delta (j + 2)) +
          A * (j : ℝ) / (((j + 2 : ℕ) : ℝ)) := by
    intro j hj
    have hj_bounds := Finset.mem_Icc.mp hj
    have hw :=
      cndG_wolfe_gap_one_step_le_phi_drop_add_diameter
        S g u β hu hβ (j := j + 1) (by omega)
    let den : ℝ := (((j + 2 : ℕ) : ℝ))
    let c : ℝ := (j : ℝ) * den / 2
    have hden_pos : 0 < den := by
      dsimp [den]
      exact_mod_cast Nat.succ_pos (j + 1)
    have hc_nonneg : 0 ≤ c := by
      dsimp [c, den]
      positivity
    have hw_norm :
        (2 / den) * gap j ≤
          Delta (j + 1) - Delta (j + 2) +
            (A / 2) * (2 / den) ^ 2 := by
      simpa [Delta, gap, phi, A, den, cndGLineSearchObjective, Nat.add_assoc,
        add_comm, add_left_comm, add_assoc] using hw
    have hmul := mul_le_mul_of_nonneg_left hw_norm hc_nonneg
    have hleft :
        c * ((2 / den) * gap j) = (j : ℝ) * gap j := by
      dsimp [c]
      field_simp [ne_of_gt hden_pos]
    have hright :
        c * (Delta (j + 1) - Delta (j + 2) +
            (A / 2) * (2 / den) ^ 2) =
          ((j : ℝ) * (((j + 2 : ℕ) : ℝ)) / 2) *
              (Delta (j + 1) - Delta (j + 2)) +
            A * (j : ℝ) / (((j + 2 : ℕ) : ℝ)) := by
      dsimp [c, den]
      field_simp [ne_of_gt hden_pos]
    nlinarith [hmul, hleft, hright]
  simpa [A, gap] using
    shifted_weighted_delta_telescope_sum_bound
      T A Delta gap _hT_pos hA_nonneg hDelta_nonneg hDelta_bound hstep

/-- Shifted minimum Wolfe-gap bound for performed CndG inner updates.

This consumes the corrected shifted weighted telescope and the scalar
weighted-average extraction for Lan Eq. (7.2.26).  The unshifted statement over
`u_j` was rejected because, under this file's `u_1 = u` indexing, it would bound
the initial Wolfe gap and is false in the one-dimensional counterexample noted in
the planner context.
-/
private theorem cndG_shifted_min_wolfe_gap_bound
    (S : Setup Ω Ξ E) (g u : E) (β : ℝ)
    (hu : u ∈ S.X) (hβ : 0 < β) (T : ℕ) (hT_pos : 1 ≤ T) :
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ T ∧
      S.cndGGap g u β (S.cndGInnerIterate g u β (j + 1)) ≤
        6 * β * S.diameter ^ 2 / (((T + 1 : ℕ) : ℝ)) := by
  have hA_nonneg : 0 ≤ β * S.diameter ^ 2 := by
    nlinarith [le_of_lt hβ, sq_nonneg S.diameter]
  have hgap_nonneg :
      ∀ j, j ∈ Finset.Icc 1 T →
        0 ≤ S.cndGGap g u β (S.cndGInnerIterate g u β (j + 1)) := by
    intro j _hj
    have hmem :
        S.cndGInnerIterate g u β (j + 1) ∈ S.X := by
      exact cndGInnerIterate_mem_before_termination S g u β hu (j + 1) (by omega)
    exact cndGGap_nonneg_of_mem S g u β hmem
  have hsum :=
    cndG_shifted_weighted_gap_sum_bound S g u β hu hβ T hT_pos
  have hsmall :=
    finite_weighted_gap_sum_yields_exists_small_gap
      T (β * S.diameter ^ 2)
      (fun j => S.cndGGap g u β (S.cndGInnerIterate g u β (j + 1)))
      hT_pos hA_nonneg hgap_nonneg hsum
  simpa [mul_assoc] using hsmall

/-- CndG stopping predicate, Algorithm 7.6 step 3. -/
def cndGStopsAt (S : Setup Ω Ξ E) (g u : E) (β η : ℝ) (t : ℕ) : Prop :=
  1 ≤ t ∧ S.cndGGap g u β (S.cndGInnerIterate g u β t) ≤ η

/-- Termination proposition for the CndG procedure on the source domain.

Algorithm 7.6 states the stopping test but does not separately assert finite
termination for every `η ∈ R_+`.  This is only the proposition that some
stopping index exists; the paper-facing output is the relational
`cndGOutput` below.
-/
def cndGTerminates (S : Setup Ω Ξ E) (g u : E) (β η : ℝ) : Prop :=
  ∃ t : ℕ, S.cndGStopsAt g u β η t

/-- Relational CndG output `u⁺`, Algorithm 7.6 step 3 and Eq. (7.2.45).

Algorithm 7.6 does not state a fallback value or a global finite-stopping
theorem.  The paper-facing object is therefore this output relation: `u⁺` is the
inner iterate at a stopping index.  No SOptLib match: searched
conditional-gradient process and realization-contract candidates; those encode
finite-horizon Frank-Wolfe recursions, while Algorithm 7.6 is an unbounded while
loop with the displayed Wolfe stopping test.
-/
def cndGOutput (S : Setup Ω Ξ E) (g u : E) (β η : ℝ) (uplus : E) : Prop :=
  ∃ t : ℕ,
    S.cndGStopsAt g u β η t ∧
      (∀ s : ℕ, 1 ≤ s → s < t → ¬ S.cndGStopsAt g u β η s) ∧
        uplus = S.cndGInnerIterate g u β t

theorem cndGOutput_terminates (S : Setup Ω Ξ E) (g u : E) (β η : ℝ) (uplus : E)
    (hout : S.cndGOutput g u β η uplus) :
    S.cndGTerminates g u β η := by
  rcases hout with ⟨t, ht, _, _⟩
  exact ⟨t, ht⟩

theorem cndGOutput_stopping (S : Setup Ω Ξ E) (g u : E) (β η : ℝ) (uplus : E)
    (hout : S.cndGOutput g u β η uplus) :
    ∃ t : ℕ, S.cndGStopsAt g u β η t ∧
      S.cndGGap g u β uplus ≤ η := by
  rcases hout with ⟨t, ht, _, rfl⟩
  exact ⟨t, ht, ht.2⟩

/-- Termination obligation for Algorithm 7.6's CndG while-loop on the stated
source domain.

The paper proves finite CndG stopping through the inner-loop bound
`6 β D_X^2 / (t+1) ≤ η`, so this source-derived obligation is stated only for
positive tolerance.  The algorithm-level boundary below remains relational when
the source only supplies `η ≥ 0`; in particular, the `Nat.find` selector
spine below is not available from `S.hη_nonneg`.
-/
theorem cndGTerminates_obligation (S : Setup Ω Ξ E) (g u : E) (β η : ℝ)
    (hu : u ∈ S.X) (hβ : 0 < β) (hη : 0 < η) :
    S.cndGTerminates g u β η := by
  let T : ℕ := max 1 (Nat.ceil ((6 * β * S.diameter ^ 2) / η))
  have hT_pos : 1 ≤ T := by
    exact Nat.le_max_left 1 (Nat.ceil ((6 * β * S.diameter ^ 2) / η))
  have hA_nonneg : 0 ≤ 6 * β * S.diameter ^ 2 := by
    nlinarith [le_of_lt hβ, sq_nonneg S.diameter]
  have hstop_scalar :
      6 * β * S.diameter ^ 2 / (((T + 1 : ℕ) : ℝ)) ≤ η := by
    simpa [T] using
      positive_ceiling_turns_gap_bound_into_stop
        (6 * β * S.diameter ^ 2) η hA_nonneg hη
  have hmin_gap :
      ∃ j : ℕ, 1 ≤ j ∧ j ≤ T ∧
        S.cndGGap g u β (S.cndGInnerIterate g u β (j + 1)) ≤
          6 * β * S.diameter ^ 2 / (((T + 1 : ℕ) : ℝ)) := by
    exact cndG_shifted_min_wolfe_gap_bound S g u β hu hβ T hT_pos
  rcases hmin_gap with ⟨j, hj_pos, _hj_le, hgap⟩
  unfold cndGTerminates cndGStopsAt
  exact ⟨j + 1, by omega, le_trans hgap hstop_scalar⟩

/-- Selected stopping index for the source CndG procedure.

No SOptLib match: searched conditional-gradient output/stopping/iterate
candidates and checked `ConditionalGradientState`,
`conditionalGradientIterUpdate`, and related finite-horizon Frank-Wolfe process
helpers.  Those encode single affine LMO updates or other algorithms, while
Algorithm 7.6 is the paper's Wolfe-gap while-loop ending at an acceptable CndG
inner iterate.
-/
def cndGStopIndex (S : Setup Ω Ξ E) (g u : E) (β η : ℝ)
    (hu : u ∈ S.X) (hβ : 0 < β) (hη : 0 < η) : ℕ :=
  by
    classical
    exact Nat.find (S.cndGTerminates_obligation g u β η hu hβ hη)

/-- The selected CndG stopping index satisfies the Algorithm 7.6 stopping test. -/
theorem cndGStopIndex_stops (S : Setup Ω Ξ E) (g u : E) (β η : ℝ)
    (hu : u ∈ S.X) (hβ : 0 < β) (hη : 0 < η) :
    S.cndGStopsAt g u β η (S.cndGStopIndex g u β η hu hβ hη) := by
  classical
  simpa [cndGStopIndex] using
    Nat.find_spec (S.cndGTerminates_obligation g u β η hu hβ hη)

/-- The selected CndG stopping index is the first index satisfying Algorithm
7.6's Wolfe-gap stopping test. -/
theorem cndGStopIndex_min (S : Setup Ω Ξ E) (g u : E) (β η : ℝ)
    (hu : u ∈ S.X) (hβ : 0 < β) (hη : 0 < η) (s : ℕ)
    (hs : s < S.cndGStopIndex g u β η hu hβ hη) :
    ¬ S.cndGStopsAt g u β η s := by
  classical
  simpa [cndGStopIndex] using
    Nat.find_min (S.cndGTerminates_obligation g u β η hu hβ hη) hs

/-- Feasibility obligation for every CndG inner iterate generated from a feasible
starting point. -/
theorem cndGInnerIterate_mem (S : Setup Ω Ξ E) (g u : E) (β : ℝ)
    (hu : u ∈ S.X) :
    ∀ t : ℕ, 1 ≤ t → S.cndGInnerIterate g u β t ∈ S.X := by
  have hupdate : ∀ ut : E, ut ∈ S.X → S.cndGInnerUpdate g u β ut ∈ S.X := by
    intro ut hut
    dsimp [cndGInnerUpdate]
    exact SOptLib.acceleratedSearchPoint_mem (X := S.X) S.hX_convex
      (S.cndGStepsize_mem g u β ut) hut (S.cndGLinearOracle_mem g u β ut)
  intro t ht
  induction t with
  | zero =>
      omega
  | succ t ih =>
      cases t with
      | zero =>
          simpa using hu
      | succ t =>
          dsimp [cndGInnerIterate]
          exact hupdate _ (ih (by omega))

/-- Canonical CndG output `CndG(g,u,β,η)` used by Algorithm 7.8, Eq. (7.2.45).

This selected object is available only on the positive-tolerance domain where
the paper's Theorem 7.9(c) termination proof applies.  Algorithm 7.8's public
state boundary uses `cndGOutput` relationally, so it does not smuggle an exact
finite-termination theorem at `η = 0`.
-/
def cndG (S : Setup Ω Ξ E) (g u : E) (β η : ℝ)
    (hu : u ∈ S.X) (hβ : 0 < β) (hη : 0 < η) : E :=
  S.cndGInnerIterate g u β (S.cndGStopIndex g u β η hu hβ hη)

/-- The selected CndG output is feasible. -/
theorem cndG_mem (S : Setup Ω Ξ E) (g u : E) (β η : ℝ)
    (hu : u ∈ S.X) (hβ : 0 < β) (hη : 0 < η) :
    S.cndG g u β η hu hβ hη ∈ S.X := by
  have hstop := S.cndGStopIndex_stops g u β η hu hβ hη
  exact S.cndGInnerIterate_mem g u β hu
    (S.cndGStopIndex g u β η hu hβ hη) hstop.1

/-- The canonical CndG output realizes the relational CndG output predicate. -/
theorem cndGOutput_cndG (S : Setup Ω Ξ E) (g u : E) (β η : ℝ)
    (hu : u ∈ S.X) (hβ : 0 < β) (hη : 0 < η) :
    S.cndGOutput g u β η (S.cndG g u β η hu hβ hη) := by
  refine ⟨S.cndGStopIndex g u β η hu hβ hη,
    S.cndGStopIndex_stops g u β η hu hβ hη, ?_, rfl⟩
  intro s _hspos hslt
  exact S.cndGStopIndex_min g u β η hu hβ hη s hslt

/-- Mini-batch gradient estimator at a supplied search point, Eq. (7.2.46).

This specializes SOptLib's `miniBatchOracleAverage` to Algorithm 7.8 by using
random sample-coordinate functions `Ω → Ξ` as the finite-average indices.  The
batch schedule is `batchSize : PositiveTime -> ℕ`, so the displayed
`B_k^{-1}` never relies on Lean's inverse at zero. -/
def miniBatchGradientAt (S : Setup Ω Ξ E) (ω : Ω) (k : PositiveTime) (z : E) : E :=
  SOptLib.miniBatchOracleAverage S.batchSize
    (fun sample z ω => S.G z (sample ω))
    (fun (_ : Unit) k j => S.ξ k.1 j)
    () k z ω

/-- Two-coordinate SCGS state `(x_k,y_k)` over the feasible carrier. -/
abbrev OuterStatePoint (S : Setup Ω Ξ E) : Type _ :=
  {x : E // x ∈ S.X} × {x : E // x ∈ S.X}

/-- Initial SCGS state `(x_0,y_0)`, Algorithm 7.8 inherited from Algorithm 7.6. -/
def initialOuterState (S : Setup Ω Ξ E) : S.OuterStatePoint :=
  (⟨S.x0, S.hx0_mem⟩, ⟨S.x0, S.hx0_mem⟩)

/-- Search-point sequence `x_k`. -/
def x (S : Setup Ω Ξ E)
    (state : ℕ → Ω → {x : E // x ∈ S.X} × {x : E // x ∈ S.X}) (k : ℕ)
    (ω : Ω) : E :=
  (state k ω).1.1

/-- Averaged output sequence `y_k`. -/
def y (S : Setup Ω Ξ E)
    (state : ℕ → Ω → {x : E // x ∈ S.X} × {x : E // x ∈ S.X}) (k : ℕ)
    (ω : Ω) : E :=
  (state k ω).2.1

/-- Strict-past sample history for Algorithm 7.8 at outer time `k`.

This sigma-algebra is generated by mini-batch samples from completed outer
iterations `1, ..., k`.  The search point used at time `k+1` must be measurable
with respect to this history, so later samples cannot be used to select among
relational CndG outputs.

Considered SOptLib candidates `SOptLib.filtration` and
`SOptLib.strictPastMiniBatchSampleBlock`.  The former is a one-dimensional
prefix filtration for a stream, and the latter is a finite block index set; the
paper object needed here is the actual two-index strict-past sigma-algebra for
Algorithm 7.8's mini-batches.
-/
@[reducible]
def strictPastSampleHistory (S : Setup Ω Ξ E) (k : ℕ) : MeasurableSpace Ω :=
  ⨆ t : {t : ℕ // 1 ≤ t ∧ t ≤ k},
    ⨆ j : {j : ℕ // j ∈ Finset.Icc 1 (S.batchSize ⟨t.1, t.2.1⟩)},
      MeasurableSpace.comap (fun ω => S.ξ t.1 j.1 ω)
        (by infer_instance : MeasurableSpace Ξ)

/-- Nonanticipativity/adaptedness of the generated outer SCGS state.

For Algorithm 7.8, `(x_k,y_k)` is generated after the first `k` mini-batch
sample blocks and before the next block is queried.  This predicate is part of
the generated-state object, not an additional theorem hypothesis.  It records
both ambient measurability, needed for Bochner expectations, and measurability
with respect to the strict-past sample history used for nonanticipativity.
-/
def OuterStateAdapted (S : Setup Ω Ξ E)
    (state : ℕ → Ω → {x : E // x ∈ S.X} × {x : E // x ∈ S.X}) : Prop :=
  ∀ k : ℕ,
    Measurable (fun ω => S.x state k ω) ∧
      Measurable (fun ω => S.y state k ω) ∧
        Measurable[S.strictPastSampleHistory k] (fun ω => S.x state k ω) ∧
      Measurable[S.strictPastSampleHistory k] (fun ω => S.y state k ω)

/-- Feasibility obligation for the extrapolated point `z_k`, Eq. (7.2.1). -/
theorem outerExtrapolation_mem (S : Setup Ω Ξ E) (k : PositiveTime)
    (prev : S.OuterStatePoint) :
    (1 - S.γ k.1) • prev.2.1 + S.γ k.1 • prev.1.1 ∈ S.X := by
  have hγ : S.γ k.1 ∈ Set.Icc (0 : ℝ) 1 := S.hγ_mem k.1 k.2
  simpa using
    (SOptLib.acceleratedSearchPoint_mem (X := S.X) S.hX_convex hγ prev.2.2
      prev.1.2)

/-- Feasibility obligation for the averaged output `y_k`, Eq. (7.2.3). -/
theorem outerAverage_mem (S : Setup Ω Ξ E) (k : PositiveTime)
    (prevY xplus : {x : E // x ∈ S.X}) :
    (1 - S.γ k.1) • prevY.1 + S.γ k.1 • xplus.1 ∈ S.X := by
  have hγ : S.γ k.1 ∈ Set.Icc (0 : ℝ) 1 := S.hγ_mem k.1 k.2
  simpa using
    (SOptLib.acceleratedSearchPoint_mem (X := S.X) S.hX_convex hγ prevY.2
      xplus.2)

/-- One outer SCGS transition relation, Algorithm 7.8.

This is the algorithmic spine without a hidden CndG termination theorem: compute
`z_k`, form `g_k` from the oracle kernel, require `x_k` to satisfy the CndG
output relation, then average to obtain `y_k`.
-/
def outerStepRel (S : Setup Ω Ξ E) (k : PositiveTime)
    (prev next : {x : E // x ∈ S.X} × {x : E // x ∈ S.X}) (ω : Ω) : Prop :=
  let zVal : E := (1 - S.γ k.1) • prev.2.1 + S.γ k.1 • prev.1.1
  zVal ∈ S.X ∧
    let g := S.miniBatchGradientAt ω k zVal
    S.cndGOutput g prev.1.1 (S.β k.1) (S.η k.1) next.1.1 ∧
      next.2.1 = (1 - S.γ k.1) • prev.2.1 + S.γ k.1 • next.1.1

/-- Positive-tolerance one-step outer SCGS transition, Algorithm 7.8.

This function-valued specialization computes `z_k`, forms the mini-batch
gradient `g_k`, takes the selected CndG output from Eq. (7.2.45), and averages
to obtain `y_k` as in Eq. (7.2.3).  It is intentionally restricted to the
positive-tolerance domain where the selected CndG output is justified.
-/
def outerStep (S : Setup Ω Ξ E) (k : PositiveTime)
    (hη : 0 < S.η k.1) (prev : S.OuterStatePoint) (ω : Ω) : S.OuterStatePoint :=
  let zVal : E := (1 - S.γ k.1) • prev.2.1 + S.γ k.1 • prev.1.1
  let g : E := S.miniBatchGradientAt ω k zVal
  let xPlus : E :=
    S.cndG g prev.1.1 (S.β k.1) (S.η k.1) prev.1.2 (S.hβ_pos k.1 k.2)
      hη
  let hxPlus : xPlus ∈ S.X :=
    S.cndG_mem g prev.1.1 (S.β k.1) (S.η k.1) prev.1.2 (S.hβ_pos k.1 k.2)
      hη
  let yPlus : E := (1 - S.γ k.1) • prev.2.1 + S.γ k.1 • xPlus
  let hyPlus : yPlus ∈ S.X := S.outerAverage_mem k prev.2 ⟨xPlus, hxPlus⟩
  (⟨xPlus, hxPlus⟩, ⟨yPlus, hyPlus⟩)

/-- The positive-tolerance outer step realizes the relational Algorithm 7.8 transition. -/
theorem outerStep_rel (S : Setup Ω Ξ E) (k : PositiveTime)
    (hη : 0 < S.η k.1) (prev : S.OuterStatePoint) (ω : Ω) :
    S.outerStepRel k prev (S.outerStep k hη prev ω) ω := by
  dsimp [outerStepRel, outerStep]
  refine ⟨S.outerExtrapolation_mem k prev, ?_⟩
  refine ⟨?_, rfl⟩
  simpa using
    (S.cndGOutput_cndG
      (S.miniBatchGradientAt ω k
        ((1 - S.γ k.1) • prev.2.1 + S.γ k.1 • prev.1.1))
      prev.1.1 (S.β k.1) (S.η k.1) prev.1.2 (S.hβ_pos k.1 k.2)
      hη)

/-- Source-domain predicate for using the selected CndG output at every outer step.

The algorithm initialization records `η_k ∈ R_+`, but the source proof of the
CndG inner-iteration bound and the printed quotient in Eq. (7.2.15) require the
positive subdomain.  Theorem 7.11's corrected source-boundary contracts carry
this predicate explicitly instead of hiding it inside the generated state.
-/
def HasPositiveEtaSchedule (S : Setup Ω Ξ E) : Prop :=
  ∀ k, 1 ≤ k → 0 < S.η k

/-- Positive-tolerance generated Algorithm 7.8 state process.

This reuses `SOptLib.recursiveIterateProcess`, whose signature was checked for
the zero-based stochastic recursion.  It is intentionally parameterized by the
extra positive-tolerance proof; when the source boundary only provides
`η_k ≥ 0`, downstream theorems use the relational `IsOuterState` predicate
instead of this function-valued specialization.
-/
def canonicalOuterStatePositive (S : Setup Ω Ξ E)
    (hη : S.HasPositiveEtaSchedule) :
    ℕ → Ω → S.OuterStatePoint :=
  SOptLib.recursiveIterateProcess S.initialOuterState
    (fun k prev ω =>
      S.outerStep ⟨k + 1, Nat.succ_pos k⟩ (hη (k + 1) (Nat.succ_pos k)) prev ω)

/-- Corrected public Algorithm 7.8 generated-state name.

The paper's CndG call has no source-stated fallback when `η_k = 0`, while the
inner-iteration bound (7.2.15) divides by `η_k`.  The generated function-valued
state is therefore exposed only on the positive-tolerance correction domain.
The relational `IsOuterState` predicate remains available for arbitrary
source-level CndG outputs.
-/
def canonicalOuterState (S : Setup Ω Ξ E)
    (hη : S.HasPositiveEtaSchedule) : ℕ → Ω → S.OuterStatePoint :=
  S.canonicalOuterStatePositive hη

theorem canonicalOuterState_eq_positive (S : Setup Ω Ξ E)
    (hη : S.HasPositiveEtaSchedule) :
    S.canonicalOuterState hη = S.canonicalOuterStatePositive hη := rfl

@[simp]
theorem canonicalOuterState_zero (S : Setup Ω Ξ E)
    (hη : S.HasPositiveEtaSchedule) (ω : Ω) :
    S.canonicalOuterState hη 0 ω = S.initialOuterState := by
  simpa [canonicalOuterState, canonicalOuterStatePositive] using
    (SOptLib.recursiveIterateProcess_zero
      (S.canonicalOuterStatePositive hη)
      S.initialOuterState
      (fun k prev ω =>
        S.outerStep ⟨k + 1, Nat.succ_pos k⟩ (hη (k + 1) (Nat.succ_pos k)) prev ω)
      rfl ω)

theorem canonicalOuterStatePositive_succ (S : Setup Ω Ξ E)
    (hη : S.HasPositiveEtaSchedule) (k : ℕ) (ω : Ω) :
    S.canonicalOuterStatePositive hη (k + 1) ω =
      S.outerStep ⟨k + 1, Nat.succ_pos k⟩ (hη (k + 1) (Nat.succ_pos k))
        (S.canonicalOuterStatePositive hη k ω) ω := by
  simpa [canonicalOuterStatePositive] using
    (SOptLib.recursiveIterateProcess_succ
      (S.canonicalOuterStatePositive hη)
      S.initialOuterState
      (fun k prev ω =>
        S.outerStep ⟨k + 1, Nat.succ_pos k⟩ (hη (k + 1) (Nat.succ_pos k)) prev ω)
      rfl k ω)

theorem canonicalOuterState_succ (S : Setup Ω Ξ E)
    (hη : S.HasPositiveEtaSchedule) (k : ℕ) (ω : Ω) :
    S.canonicalOuterState hη (k + 1) ω =
      S.outerStep ⟨k + 1, Nat.succ_pos k⟩ (hη (k + 1) (Nat.succ_pos k))
        (S.canonicalOuterState hη k ω) ω := by
  simpa [canonicalOuterState] using S.canonicalOuterStatePositive_succ hη k ω

/-- A stochastic SCGS state process generated by Algorithm 7.8.

The process is relational because Algorithm 7.6 defines CndG output only at a
stopping index and does not provide a nontermination fallback.  This predicate
records only the algorithmic initial condition and transition equations; stochastic
nonanticipativity is the separate `OuterStateAdapted` regularity obligation below.
Keeping these separate avoids proving measurability of the selected CndG
while-loop output just to establish the deterministic Algorithm 7.8 recursion.
-/
def IsOuterState (S : Setup Ω Ξ E)
    (state : ℕ → Ω → {x : E // x ∈ S.X} × {x : E // x ∈ S.X}) : Prop :=
  (∀ ω, state 0 ω = (⟨S.x0, S.hx0_mem⟩, ⟨S.x0, S.hx0_mem⟩)) ∧
    ∀ k ω, S.outerStepRel ⟨k + 1, Nat.succ_pos k⟩ (state k ω) (state (k + 1) ω) ω

/-- The canonical recursive state satisfies the relational generated-state
predicate used by downstream proof obligations. -/
theorem canonicalOuterState_isOuterState (S : Setup Ω Ξ E)
    (hη : S.HasPositiveEtaSchedule) :
    S.IsOuterState (S.canonicalOuterState hη) := by
  refine ⟨?_, ?_⟩
  · intro ω
    exact S.canonicalOuterState_zero hη ω
  · intro k ω
    simpa [S.canonicalOuterState_succ hη k ω] using
      S.outerStep_rel ⟨k + 1, Nat.succ_pos k⟩ (hη (k + 1) (Nat.succ_pos k))
        (S.canonicalOuterState hη k ω) ω

/-- Explicit generated-state adaptedness regularity.  This theorem is only a
projection from the separate regularity hypothesis; it is not derived from the
relational CndG transition alone. -/
theorem outerState_adapted (S : Setup Ω Ξ E)
    (state : ℕ → Ω → {x : E // x ∈ S.X} × {x : E // x ∈ S.X})
    (hAdapted : S.OuterStateAdapted state) :
    S.OuterStateAdapted state :=
  hAdapted

theorem outerStateAdapted_x_measurable (S : Setup Ω Ξ E)
    (state : ℕ → Ω → {x : E // x ∈ S.X} × {x : E // x ∈ S.X})
    (hAdapted : S.OuterStateAdapted state) (k : ℕ) :
    Measurable (fun ω => S.x state k ω) :=
  (hAdapted k).1

theorem outerStateAdapted_y_measurable (S : Setup Ω Ξ E)
    (state : ℕ → Ω → {x : E // x ∈ S.X} × {x : E // x ∈ S.X})
    (hAdapted : S.OuterStateAdapted state) (k : ℕ) :
    Measurable (fun ω => S.y state k ω) :=
  (hAdapted k).2.1

theorem outerStateAdapted_x_strictPast_measurable (S : Setup Ω Ξ E)
    (state : ℕ → Ω → {x : E // x ∈ S.X} × {x : E // x ∈ S.X})
    (hAdapted : S.OuterStateAdapted state) (k : ℕ) :
    Measurable[S.strictPastSampleHistory k] (fun ω => S.x state k ω) :=
  (hAdapted k).2.2.1

theorem outerStateAdapted_y_strictPast_measurable (S : Setup Ω Ξ E)
    (state : ℕ → Ω → {x : E // x ∈ S.X} × {x : E // x ∈ S.X})
    (hAdapted : S.OuterStateAdapted state) (k : ℕ) :
    Measurable[S.strictPastSampleHistory k] (fun ω => S.y state k ω) :=
  (hAdapted k).2.2.2

/-- Extrapolated point `z_k=(1-γ_k)y_{k-1}+γ_k x_{k-1}`, Eq. (7.2.1). -/
def z (S : Setup Ω Ξ E)
    (state : ℕ → Ω → {x : E // x ∈ S.X} × {x : E // x ∈ S.X}) (k : ℕ)
    (ω : Ω) : E :=
  (1 - S.γ k) • S.y state (k - 1) ω + S.γ k • S.x state (k - 1) ω

/-- Batch stochastic gradient `g_k`, Eq. (7.2.46), derived from `G` and `ξ`. -/
def batchGradient (S : Setup Ω Ξ E)
    (state : ℕ → Ω → {x : E // x ∈ S.X} × {x : E // x ∈ S.X}) (k : PositiveTime)
    (ω : Ω) : E :=
  S.miniBatchGradientAt ω k (S.z state k.1 ω)

@[simp]
theorem x_zero (S : Setup Ω Ξ E)
    (state : ℕ → Ω → {x : E // x ∈ S.X} × {x : E // x ∈ S.X})
    (hstate : S.IsOuterState state) (ω : Ω) : S.x state 0 ω = S.x0 := by
  simpa [x] using congrArg (fun p => p.1.1) (hstate.1 ω)

@[simp]
theorem y_zero (S : Setup Ω Ξ E)
    (state : ℕ → Ω → {x : E // x ∈ S.X} × {x : E // x ∈ S.X})
    (hstate : S.IsOuterState state) (ω : Ω) : S.y state 0 ω = S.x0 := by
  simpa [y] using congrArg (fun p => p.2.1) (hstate.1 ω)

theorem z_eq_extrapolation (S : Setup Ω Ξ E)
    (state : ℕ → Ω → {x : E // x ∈ S.X} × {x : E // x ∈ S.X})
    (k : ℕ) (ω : Ω) :
    S.z state k ω =
      (1 - S.γ k) • S.y state (k - 1) ω + S.γ k • S.x state (k - 1) ω := rfl

theorem batchGradient_eq_formula (S : Setup Ω Ξ E)
    (state : ℕ → Ω → {x : E // x ∈ S.X} × {x : E // x ∈ S.X})
    (k : PositiveTime) (ω : Ω) :
    S.batchGradient state k ω =
      ((S.batchSize k : ℝ)⁻¹) •
        Finset.sum (Finset.Icc 1 (S.batchSize k)) (fun j =>
          S.G (S.z state k.1 ω) (S.ξ k.1 j ω)) := rfl

theorem outerStep_x_is_cndGOutput (S : Setup Ω Ξ E)
    (state : ℕ → Ω → {x : E // x ∈ S.X} × {x : E // x ∈ S.X})
    (hstate : S.IsOuterState state) (k : ℕ) (ω : Ω) :
    S.cndGOutput (S.batchGradient state ⟨k.succ, Nat.succ_pos k⟩ ω) (S.x state k ω)
      (S.β k.succ) (S.η k.succ) (S.x state k.succ ω) := by
  have hrel := hstate.2 k ω
  dsimp [outerStepRel, batchGradient, z, x, y] at hrel ⊢
  simpa using hrel.2.1

theorem outerStep_y_eq_average (S : Setup Ω Ξ E)
    (state : ℕ → Ω → {x : E // x ∈ S.X} × {x : E // x ∈ S.X})
    (hstate : S.IsOuterState state) (k : ℕ) (ω : Ω) :
    S.y state k.succ ω =
      (1 - S.γ k.succ) • S.y state k ω + S.γ k.succ • S.x state k.succ ω := by
  have hrel := hstate.2 k ω
  dsimp [outerStepRel, x, y] at hrel ⊢
  simpa using hrel.2.2

/-- Algorithm 7.8's stochastic CndG call gives the approximate projection
inequality used before Eq. (7.2.49), for the successor-indexed outer step.

This aligns the local relational outer-step semantics with Lan's
`x_k = CndG(g_k,x_{k-1},β_k,η_k)` stopping condition.  SOptLib Wolfe-gap
candidates (`wolfeGap`, `le_wolfeGap`, and descent wrappers) were considered
but rejected because they model a generic Frank-Wolfe gap, while this proof
uses this file's shifted CndG gap and relational `cndGOutput` object directly.
-/
private theorem outer_step_cndg_projection_inequality_succ
    (S : Setup Ω Ξ E)
    (state : ℕ → Ω → {x : E // x ∈ S.X} × {x : E // x ∈ S.X})
    (hstate : S.IsOuterState state) (k : ℕ) (ω : Ω) {x : E} (hx : x ∈ S.X) :
    ⟪S.batchGradient state ⟨k.succ, Nat.succ_pos k⟩ ω +
        S.β k.succ • (S.x state k.succ ω - S.x state k ω),
      S.x state k.succ ω - x⟫_ℝ ≤ S.η k.succ := by
  have hout := S.outerStep_x_is_cndGOutput state hstate k ω
  obtain ⟨_t, _ht, hstop⟩ := S.cndGOutput_stopping
    (S.batchGradient state ⟨k.succ, Nat.succ_pos k⟩ ω)
    (S.x state k ω) (S.β k.succ) (S.η k.succ)
    (S.x state k.succ ω) hout
  have hmax := S.cndGLinearOracle_isMax
    (S.batchGradient state ⟨k.succ, Nat.succ_pos k⟩ ω)
    (S.x state k ω) (S.β k.succ) (S.x state k.succ ω) x hx
  have hle_gap :
      ⟪S.batchGradient state ⟨k.succ, Nat.succ_pos k⟩ ω +
          S.β k.succ • (S.x state k.succ ω - S.x state k ω),
        S.x state k.succ ω - x⟫_ℝ ≤
        S.cndGGap
          (S.batchGradient state ⟨k.succ, Nat.succ_pos k⟩ ω)
          (S.x state k ω) (S.β k.succ) (S.x state k.succ ω) := by
    simpa [cndGGap] using hmax
  exact le_trans hle_gap hstop

/-- Positive-time form of Algorithm 7.8's stochastic CndG approximate
projection inequality, matching the indexing of Eq. (7.2.49).

This is only the one-based restatement of
`outer_step_cndg_projection_inequality_succ`; the same SOptLib Wolfe-gap
candidates were rejected for the reason recorded there.
-/
private theorem outer_step_cndg_projection_inequality
    (S : Setup Ω Ξ E)
    (state : ℕ → Ω → {x : E // x ∈ S.X} × {x : E // x ∈ S.X})
    (hstate : S.IsOuterState state) (i : PositiveTime) (ω : Ω) {x : E}
    (hx : x ∈ S.X) :
    ⟪S.batchGradient state i ω +
        S.β i.1 • (S.x state i.1 ω - S.x state (i.1 - 1) ω),
      S.x state i.1 ω - x⟫_ℝ ≤ S.η i.1 := by
  rcases i with ⟨n, hn⟩
  cases n with
  | zero =>
      exact False.elim ((Nat.not_succ_le_zero 0) hn)
  | succ k =>
      simpa using
        (outer_step_cndg_projection_inequality_succ S state hstate k ω hx)

/-- Euclidean three-point algebra converting an approximate projection
inequality into the distance-difference form used in Eq. (7.2.17)/(7.2.49).

Considered SOptLib Bregman three-point identities and prox wrappers; they are
more general than needed and use Bregman kernels, while this source step is the
literal squared-Hilbert-norm identity printed in Eq. (7.2.17).
-/
private theorem cndg_projection_inner_le_distance_difference
    {g u up x : E} {β η : ℝ}
    (hproj : ⟪g + β • (up - u), up - x⟫_ℝ ≤ η) :
    ⟪g, up - x⟫_ℝ ≤
      η + β / 2 * (‖u - x‖ ^ 2 - ‖up - x‖ ^ 2 - ‖up - u‖ ^ 2) := by
  have hsplit :
      ⟪g + β • (up - u), up - x⟫_ℝ =
        ⟪g, up - x⟫_ℝ + β * ⟪up - u, up - x⟫_ℝ := by
    simp [inner_add_left, inner_smul_left]
  have hthree :
      ⟪up - u, up - x⟫_ℝ =
        (‖up - x‖ ^ 2 + ‖up - u‖ ^ 2 - ‖u - x‖ ^ 2) / 2 := by
    have hnorm := norm_sub_sq_real (up - x) (up - u)
    have hsub : (up - x) - (up - u) = u - x := by
      abel
    rw [hsub] at hnorm
    have hcomm : ⟪up - x, up - u⟫_ℝ = ⟪up - u, up - x⟫_ℝ := by
      rw [real_inner_comm]
    nlinarith
  rw [hsplit, hthree] at hproj
  nlinarith

/-- Algorithm 7.8's stochastic CndG projection identity in the
distance-difference form consumed by the one-step recursion Eq. (7.2.49). -/
private theorem outer_step_cndg_projection_distance_difference
    (S : Setup Ω Ξ E)
    (state : ℕ → Ω → {x : E // x ∈ S.X} × {x : E // x ∈ S.X})
    (hstate : S.IsOuterState state) (i : PositiveTime) (ω : Ω) {x : E}
    (hx : x ∈ S.X) :
    ⟪S.batchGradient state i ω, S.x state i.1 ω - x⟫_ℝ ≤
      S.η i.1 + S.β i.1 / 2 *
        (‖S.x state (i.1 - 1) ω - x‖ ^ 2 -
          ‖S.x state i.1 ω - x‖ ^ 2 -
            ‖S.x state i.1 ω - S.x state (i.1 - 1) ω‖ ^ 2) := by
  exact
    cndg_projection_inner_le_distance_difference
      (outer_step_cndg_projection_inequality S state hstate i ω hx)

/-- Relation between the averaged output and extrapolated search point in
Algorithm 7.8, used to turn the smoothness quadratic into
`γ_i^2 ‖x_i-x_{i-1}‖^2` in Eq. (7.2.49). -/
private theorem outerStep_y_sub_z_eq_gamma_xdiff
    (S : Setup Ω Ξ E)
    (state : ℕ → Ω → {x : E // x ∈ S.X} × {x : E // x ∈ S.X})
    (hstate : S.IsOuterState state) (i : PositiveTime) (ω : Ω) :
    S.y state i.1 ω - S.z state i.1 ω =
      S.γ i.1 • (S.x state i.1 ω - S.x state (i.1 - 1) ω) := by
  rcases i with ⟨n, hn⟩
  cases n with
  | zero =>
      exact False.elim ((Nat.not_succ_le_zero 0) hn)
  | succ k =>
      rw [S.outerStep_y_eq_average state hstate k ω]
      simp [z, sub_eq_add_neg]
      abel

/-- Young/completion-square estimate used in the proof of Eq. (7.2.49).

This is the exact source display after expanding
`<δ_i, x-x_i> - (β_i-Lγ_i)/2 ||x_i-x_{i-1}||^2`.  Considered
`young_absorb_inner_of_norm_sq_budget`, which is a reusable SOptLib absorption
lemma, but it packages an additional budget variable; this local helper keeps
the literal source quotient form `||δ||^2/(2a)`. -/
private theorem young_delta_cross_term_bound
    {a : ℝ} (ha : 0 < a) (δ d : E) :
    ⟪δ, -d⟫_ℝ - a / 2 * ‖d‖ ^ 2 ≤ ‖δ‖ ^ 2 / (2 * a) := by
  have hinner_abs : ⟪δ, -d⟫_ℝ ≤ ‖δ‖ * ‖d‖ := by
    calc
      ⟪δ, -d⟫_ℝ ≤ |⟪δ, -d⟫_ℝ| := le_abs_self _
      _ ≤ ‖δ‖ * ‖-d‖ := abs_real_inner_le_norm δ (-d)
      _ = ‖δ‖ * ‖d‖ := by simp
  have hscalar :
      ‖δ‖ * ‖d‖ - a / 2 * ‖d‖ ^ 2 ≤ ‖δ‖ ^ 2 / (2 * a) := by
    have hsq : 0 ≤ (‖δ‖ - a * ‖d‖) ^ 2 := sq_nonneg _
    have hapos : 0 < 2 * a := by positivity
    rw [le_div_iff₀ hapos]
    nlinarith
  linarith

/-- Feasibility of relational `x_k`, to be proved from compact convexity and CndG
linear-oracle feasibility rather than assumed in theorem heads. -/
theorem x_mem (S : Setup Ω Ξ E)
    (state : ℕ → Ω → {x : E // x ∈ S.X} × {x : E // x ∈ S.X})
    (k : ℕ) (ω : Ω) : S.x state k ω ∈ S.X := by
  exact (state k ω).1.2

/-- Feasibility of relational averaged outputs `y_k`. -/
theorem y_mem (S : Setup Ω Ξ E)
    (state : ℕ → Ω → {x : E // x ∈ S.X} × {x : E // x ∈ S.X})
    (k : ℕ) (ω : Ω) : S.y state k ω ∈ S.X := by
  exact (state k ω).2.2

/-- Feasibility of relational extrapolated points `z_k`. -/
theorem z_mem (S : Setup Ω Ξ E)
    (state : ℕ → Ω → {x : E // x ∈ S.X} × {x : E // x ∈ S.X})
    (k : ℕ) (ω : Ω) (hk : 1 ≤ k) : S.z state k ω ∈ S.X := by
  simpa [z, x, y] using (S.outerExtrapolation_mem ⟨k, hk⟩ (state (k - 1) ω))

/-- Linearity of the paper model `l_f(z;.)` along the Algorithm 7.8 averaged
output, aligning the first equality in Lan Eq. (7.2.16).

Considered `composite_upper_model_at_convex_average`, which packages the same
affine-model algebra for a composite objective.  This theorem keeps the
paper's literal `linearModel` and the relational `outerStep_y_eq_average`
objects, so it can be consumed directly in Eq. (7.2.49). -/
private theorem linearModel_outerStep_y_eq_weighted
    (S : Setup Ω Ξ E)
    (state : ℕ → Ω → {x : E // x ∈ S.X} × {x : E // x ∈ S.X})
    (hstate : S.IsOuterState state) (i : PositiveTime) (ω : Ω) :
    let hz : S.z state i.1 ω ∈ S.X := S.z_mem state i.1 ω i.2
    S.linearModel ⟨S.z state i.1 ω, hz⟩
        ⟨S.y state i.1 ω, S.y_mem state i.1 ω⟩ =
      (1 - S.γ i.1) *
          S.linearModel ⟨S.z state i.1 ω, hz⟩
            ⟨S.y state (i.1 - 1) ω, S.y_mem state (i.1 - 1) ω⟩ +
        S.γ i.1 *
          S.linearModel ⟨S.z state i.1 ω, hz⟩
            ⟨S.x state i.1 ω, S.x_mem state i.1 ω⟩ := by
  rcases i with ⟨n, hn⟩
  cases n with
  | zero =>
      exact False.elim ((Nat.not_succ_le_zero 0) hn)
  | succ k =>
      dsimp
      unfold linearModel
      change
        S.f (S.z state (k + 1) ω) +
            ⟪S.grad ⟨S.z state (k + 1) ω, S.z_mem state (k + 1) ω hn⟩,
              S.y state (k + 1) ω - S.z state (k + 1) ω⟫_ℝ =
          (1 - S.γ (k + 1)) *
              (S.f (S.z state (k + 1) ω) +
                ⟪S.grad ⟨S.z state (k + 1) ω, S.z_mem state (k + 1) ω hn⟩,
                  S.y state k ω - S.z state (k + 1) ω⟫_ℝ) +
            S.γ (k + 1) *
              (S.f (S.z state (k + 1) ω) +
                ⟪S.grad ⟨S.z state (k + 1) ω, S.z_mem state (k + 1) ω hn⟩,
                  S.x state (k + 1) ω - S.z state (k + 1) ω⟫_ℝ)
      rw [S.outerStep_y_eq_average state hstate k ω]
      simp [inner_add_right, inner_smul_right, sub_eq_add_neg]
      ring

/-- Noise atom `δ_{k,j}=G(z_k,ξ_{k,j})-f'(z_k)`, Theorem 7.11 proof. -/
def deltaAtom (S : Setup Ω Ξ E)
    (state : ℕ → Ω → {x : E // x ∈ S.X} × {x : E // x ∈ S.X})
    (k : PositiveTime) (j : ℕ) (ω : Ω) : E :=
  S.G (S.z state k.1 ω) (S.ξ k.1 j ω) -
    S.grad ⟨S.z state k.1 ω, S.z_mem state k.1 ω k.2⟩

/-- Mini-batch noise `δ_k=g_k-f'(z_k)`, Theorem 7.11 proof. -/
def deltaBatch (S : Setup Ω Ξ E)
    (state : ℕ → Ω → {x : E // x ∈ S.X} × {x : E // x ∈ S.X})
    (k : PositiveTime) (ω : Ω) : E :=
  S.batchGradient state k ω -
    S.grad ⟨S.z state k.1 ω, S.z_mem state k.1 ω k.2⟩

/-- Decomposition of `l_f(z_i;x_i)` into the feasible comparison model,
stochastic projection term, and mini-batch residual term, matching the equality
before Lan Eq. (7.2.49).

No SOptLib match: searched `linear model affine convex combination inner
product` and checked the available conditional-gradient model candidates; they
cover Wolfe/max-linear comparisons rather than this file's literal
`linearModel` plus `deltaBatch = g_i - f'(z_i)` identity. -/
private theorem linearModel_x_eq_linearModel_compare_add_batch_delta
    (S : Setup Ω Ξ E)
    (state : ℕ → Ω → {x : E // x ∈ S.X} × {x : E // x ∈ S.X})
    (i : PositiveTime) (ω : Ω) {x : E} (hx : x ∈ S.X) :
    let hz : S.z state i.1 ω ∈ S.X := S.z_mem state i.1 ω i.2
    S.linearModel ⟨S.z state i.1 ω, hz⟩
        ⟨S.x state i.1 ω, S.x_mem state i.1 ω⟩ =
      S.linearModel ⟨S.z state i.1 ω, hz⟩ ⟨x, hx⟩ +
        ⟪S.batchGradient state i ω, S.x state i.1 ω - x⟫_ℝ +
          ⟪S.deltaBatch state i ω, x - S.x state i.1 ω⟫_ℝ := by
  dsimp
  unfold linearModel deltaBatch
  change
    S.f (S.z state i.1 ω) +
        ⟪S.grad ⟨S.z state i.1 ω, S.z_mem state i.1 ω i.2⟩,
          S.x state i.1 ω - S.z state i.1 ω⟫_ℝ =
      S.f (S.z state i.1 ω) +
          ⟪S.grad ⟨S.z state i.1 ω, S.z_mem state i.1 ω i.2⟩,
            x - S.z state i.1 ω⟫_ℝ +
        ⟪S.batchGradient state i ω, S.x state i.1 ω - x⟫_ℝ +
          ⟪S.batchGradient state i ω -
              S.grad ⟨S.z state i.1 ω, S.z_mem state i.1 ω i.2⟩,
            x - S.x state i.1 ω⟫_ℝ
  simp [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
    inner_neg_left, inner_neg_right, sub_eq_add_neg]
  ring

set_option maxHeartbeats 800000 in
/-- One-step stochastic CGS recursion, Eq. (7.2.49), before Gamma
telescoping.

This helper aligns with Lan Theorem 7.11 proof steps 2-6.  It consumes the
source smooth upper model `SmoothUpperModel_7_1_8`, the convex lower-model
bridge `linearModel_le_f_of_mem`, the stochastic CndG projection distance
identity `outer_step_cndg_projection_distance_difference`, the averaged-output
identity `outerStep_y_sub_z_eq_gamma_xdiff`, and the strict denominator gap
supplied at call sites by `theorem711VarianceDenominatorDomain_gap_pos`. -/
private theorem stochastic_one_step_recursion_7_2_49
    (S : Setup Ω Ξ E)
    (state : ℕ → Ω → {x : E // x ∈ S.X} × {x : E // x ∈ S.X})
    (hstate : S.IsOuterState state) (i : PositiveTime) (ω : Ω) {x : E}
    (hx : x ∈ S.X)
    (hgap : 0 < S.β i.1 - S.L * S.γ i.1) :
    S.f (S.y state i.1 ω) ≤
      (1 - S.γ i.1) * S.f (S.y state (i.1 - 1) ω) +
        S.γ i.1 * S.f x +
          S.β i.1 * S.γ i.1 / 2 *
            (‖S.x state (i.1 - 1) ω - x‖ ^ 2 -
              ‖S.x state i.1 ω - x‖ ^ 2) +
          S.η i.1 * S.γ i.1 +
          S.γ i.1 *
            ⟪S.deltaBatch state i ω, x - S.x state (i.1 - 1) ω⟫_ℝ +
          S.γ i.1 * ‖S.deltaBatch state i ω‖ ^ 2 /
            (2 * (S.β i.1 - S.L * S.γ i.1)) := by
  classical
  have hγ_mem := S.hγ_mem i.1 i.2
  have hγ_nonneg : 0 ≤ S.γ i.1 := (Set.mem_Icc.mp hγ_mem).1
  have hγ_le_one : S.γ i.1 ≤ 1 := (Set.mem_Icc.mp hγ_mem).2
  have h_one_sub_nonneg : 0 ≤ 1 - S.γ i.1 := sub_nonneg.mpr hγ_le_one
  let zi : E := S.z state i.1 ω
  let yi : E := S.y state i.1 ω
  let yprev : E := S.y state (i.1 - 1) ω
  let xi : E := S.x state i.1 ω
  let xprev : E := S.x state (i.1 - 1) ω
  let δ : E := S.deltaBatch state i ω
  let d : E := xi - xprev
  let gap : ℝ := S.β i.1 - S.L * S.γ i.1
  have hgap' : 0 < gap := by simpa [gap] using hgap
  have hzmem : zi ∈ S.X := by simpa [zi] using S.z_mem state i.1 ω i.2
  have hymem : yi ∈ S.X := by simpa [yi] using S.y_mem state i.1 ω
  have hypmem : yprev ∈ S.X := by simpa [yprev] using S.y_mem state (i.1 - 1) ω
  have hximem : xi ∈ S.X := by simpa [xi] using S.x_mem state i.1 ω
  have hsmooth :
      S.f yi ≤
        S.linearModel ⟨zi, hzmem⟩ ⟨yi, hymem⟩ +
          S.L / 2 * ‖yi - zi‖ ^ 2 := by
    simpa [zi, yi] using
      S.SmoothUpperModel_7_1_8 (S.z state i.1 ω)
        (S.z_mem state i.1 ω i.2) (S.y state i.1 ω)
        (S.y_mem state i.1 ω)
  have hmodel_y :
      S.linearModel ⟨zi, hzmem⟩ ⟨yi, hymem⟩ =
        (1 - S.γ i.1) *
            S.linearModel ⟨zi, hzmem⟩ ⟨yprev, hypmem⟩ +
          S.γ i.1 * S.linearModel ⟨zi, hzmem⟩ ⟨xi, hximem⟩ := by
    simpa [zi, yi, yprev, xi] using
      linearModel_outerStep_y_eq_weighted S state hstate i ω
  have hyz :
      yi - zi = S.γ i.1 • d := by
    simpa [zi, yi, xi, xprev, d] using
      outerStep_y_sub_z_eq_gamma_xdiff S state hstate i ω
  have hnorm_yz :
      ‖yi - zi‖ ^ 2 = S.γ i.1 ^ 2 * ‖d‖ ^ 2 := by
    rw [hyz, norm_smul, Real.norm_eq_abs, abs_of_nonneg hγ_nonneg]
    ring
  have hlower_prev :
      S.linearModel ⟨zi, hzmem⟩ ⟨yprev, hypmem⟩ ≤ S.f yprev := by
    simpa [zi, yprev] using
      linearModel_le_f_of_mem S (S.z_mem state i.1 ω i.2)
        (S.y_mem state (i.1 - 1) ω)
  have hproj :
      ⟪S.batchGradient state i ω, xi - x⟫_ℝ ≤
        S.η i.1 + S.β i.1 / 2 *
          (‖xprev - x‖ ^ 2 - ‖xi - x‖ ^ 2 - ‖d‖ ^ 2) := by
    simpa [xi, xprev, d] using
      outer_step_cndg_projection_distance_difference S state hstate i ω hx
  have hmodel_decomp :
      S.linearModel ⟨zi, hzmem⟩ ⟨xi, hximem⟩ =
        S.linearModel ⟨zi, hzmem⟩ ⟨x, hx⟩ +
          ⟪S.batchGradient state i ω, xi - x⟫_ℝ +
            ⟪δ, x - xi⟫_ℝ := by
    simpa [zi, xi, δ] using
      linearModel_x_eq_linearModel_compare_add_batch_delta S state i ω hx
  have hlower_x :
      S.linearModel ⟨zi, hzmem⟩ ⟨x, hx⟩ ≤ S.f x := by
    simpa [zi] using linearModel_le_f_of_mem S (S.z_mem state i.1 ω i.2) hx
  have hyoung :
      ⟪δ, x - xi⟫_ℝ - gap / 2 * ‖d‖ ^ 2 ≤
        ⟪δ, x - xprev⟫_ℝ + ‖δ‖ ^ 2 / (2 * gap) := by
    have hsplit : x - xi = (x - xprev) + -d := by
      simp [d, xi, xprev]
    have hbase := young_delta_cross_term_bound hgap' δ d
    rw [hsplit, inner_add_right]
    linarith
  dsimp [zi, yi, yprev, xi, xprev, δ, d, gap] at *
  have hprev_scaled :
      (1 - S.γ i.1) *
          S.linearModel ⟨S.z state i.1 ω, hzmem⟩
            ⟨S.y state (i.1 - 1) ω, hypmem⟩ ≤
        (1 - S.γ i.1) * S.f (S.y state (i.1 - 1) ω) :=
    mul_le_mul_of_nonneg_left hlower_prev h_one_sub_nonneg
  have hmodel_xi_le :
      S.linearModel ⟨S.z state i.1 ω, hzmem⟩
          ⟨S.x state i.1 ω, hximem⟩ ≤
        S.f x + S.η i.1 +
          S.β i.1 / 2 *
            (‖S.x state (i.1 - 1) ω - x‖ ^ 2 -
              ‖S.x state i.1 ω - x‖ ^ 2 -
                ‖S.x state i.1 ω - S.x state (i.1 - 1) ω‖ ^ 2) +
          ⟪S.deltaBatch state i ω, x - S.x state i.1 ω⟫_ℝ := by
    nlinarith [hmodel_decomp, hproj, hlower_x]
  have hmodel_xi_scaled :
      S.γ i.1 *
          S.linearModel ⟨S.z state i.1 ω, hzmem⟩
            ⟨S.x state i.1 ω, hximem⟩ ≤
        S.γ i.1 *
          (S.f x + S.η i.1 +
            S.β i.1 / 2 *
              (‖S.x state (i.1 - 1) ω - x‖ ^ 2 -
                ‖S.x state i.1 ω - x‖ ^ 2 -
                  ‖S.x state i.1 ω - S.x state (i.1 - 1) ω‖ ^ 2) +
            ⟪S.deltaBatch state i ω, x - S.x state i.1 ω⟫_ℝ) :=
    mul_le_mul_of_nonneg_left hmodel_xi_le hγ_nonneg
  have hyoung_scaled :
      S.γ i.1 *
          (⟪S.deltaBatch state i ω, x - S.x state i.1 ω⟫_ℝ -
            (S.β i.1 - S.L * S.γ i.1) / 2 *
              ‖S.x state i.1 ω - S.x state (i.1 - 1) ω‖ ^ 2) ≤
        S.γ i.1 *
          (⟪S.deltaBatch state i ω, x - S.x state (i.1 - 1) ω⟫_ℝ +
            ‖S.deltaBatch state i ω‖ ^ 2 /
              (2 * (S.β i.1 - S.L * S.γ i.1))) :=
    mul_le_mul_of_nonneg_left hyoung hγ_nonneg
  have hdescent_model :
      S.f (S.y state i.1 ω) ≤
        (1 - S.γ i.1) * S.f (S.y state (i.1 - 1) ω) +
          S.γ i.1 *
            (S.f x + S.η i.1 +
              S.β i.1 / 2 *
                (‖S.x state (i.1 - 1) ω - x‖ ^ 2 -
                  ‖S.x state i.1 ω - x‖ ^ 2 -
                    ‖S.x state i.1 ω - S.x state (i.1 - 1) ω‖ ^ 2) +
              ⟪S.deltaBatch state i ω, x - S.x state i.1 ω⟫_ℝ) +
          S.L / 2 *
            (S.γ i.1 ^ 2 *
              ‖S.x state i.1 ω - S.x state (i.1 - 1) ω‖ ^ 2) := by
    calc
      S.f (S.y state i.1 ω)
          ≤ S.linearModel ⟨S.z state i.1 ω, hzmem⟩
              ⟨S.y state i.1 ω, hymem⟩ +
            S.L / 2 * ‖S.y state i.1 ω - S.z state i.1 ω‖ ^ 2 := hsmooth
      _ =
          ((1 - S.γ i.1) *
              S.linearModel ⟨S.z state i.1 ω, hzmem⟩
                ⟨S.y state (i.1 - 1) ω, hypmem⟩ +
            S.γ i.1 *
              S.linearModel ⟨S.z state i.1 ω, hzmem⟩
                ⟨S.x state i.1 ω, hximem⟩) +
            S.L / 2 *
              (S.γ i.1 ^ 2 *
                ‖S.x state i.1 ω - S.x state (i.1 - 1) ω‖ ^ 2) := by
              rw [hmodel_y, hnorm_yz]
      _ ≤
          (1 - S.γ i.1) * S.f (S.y state (i.1 - 1) ω) +
            S.γ i.1 *
              (S.f x + S.η i.1 +
                S.β i.1 / 2 *
                  (‖S.x state (i.1 - 1) ω - x‖ ^ 2 -
                    ‖S.x state i.1 ω - x‖ ^ 2 -
                      ‖S.x state i.1 ω - S.x state (i.1 - 1) ω‖ ^ 2) +
                ⟪S.deltaBatch state i ω, x - S.x state i.1 ω⟫_ℝ) +
            S.L / 2 *
              (S.γ i.1 ^ 2 *
                ‖S.x state i.1 ω - S.x state (i.1 - 1) ω‖ ^ 2) := by
              nlinarith [hprev_scaled, hmodel_xi_scaled]
  have hpre_young :
      S.f (S.y state i.1 ω) ≤
        (1 - S.γ i.1) * S.f (S.y state (i.1 - 1) ω) +
          S.γ i.1 * S.f x +
          S.β i.1 * S.γ i.1 / 2 *
            (‖S.x state (i.1 - 1) ω - x‖ ^ 2 -
              ‖S.x state i.1 ω - x‖ ^ 2) +
          S.η i.1 * S.γ i.1 +
          S.γ i.1 *
            (⟪S.deltaBatch state i ω, x - S.x state i.1 ω⟫_ℝ -
              (S.β i.1 - S.L * S.γ i.1) / 2 *
                ‖S.x state i.1 ω - S.x state (i.1 - 1) ω‖ ^ 2) := by
    nlinarith [hdescent_model]
  calc
    S.f (S.y state i.1 ω) ≤
        (1 - S.γ i.1) * S.f (S.y state (i.1 - 1) ω) +
          S.γ i.1 * S.f x +
          S.β i.1 * S.γ i.1 / 2 *
            (‖S.x state (i.1 - 1) ω - x‖ ^ 2 -
              ‖S.x state i.1 ω - x‖ ^ 2) +
          S.η i.1 * S.γ i.1 +
          S.γ i.1 *
            (⟪S.deltaBatch state i ω, x - S.x state i.1 ω⟫_ℝ -
              (S.β i.1 - S.L * S.γ i.1) / 2 *
                ‖S.x state i.1 ω - S.x state (i.1 - 1) ω‖ ^ 2) := hpre_young
    _ ≤
        (1 - S.γ i.1) * S.f (S.y state (i.1 - 1) ω) +
          S.γ i.1 * S.f x +
          S.β i.1 * S.γ i.1 / 2 *
            (‖S.x state (i.1 - 1) ω - x‖ ^ 2 -
              ‖S.x state i.1 ω - x‖ ^ 2) +
          S.η i.1 * S.γ i.1 +
          S.γ i.1 *
            (⟪S.deltaBatch state i ω, x - S.x state (i.1 - 1) ω⟫_ℝ +
              ‖S.deltaBatch state i ω‖ ^ 2 /
                (2 * (S.β i.1 - S.L * S.γ i.1))) := by
          nlinarith [hyoung_scaled]
    _ =
        (1 - S.γ i.1) * S.f (S.y state (i.1 - 1) ω) +
          S.γ i.1 * S.f x +
            S.β i.1 * S.γ i.1 / 2 *
              (‖S.x state (i.1 - 1) ω - x‖ ^ 2 -
                ‖S.x state i.1 ω - x‖ ^ 2) +
            S.η i.1 * S.γ i.1 +
            S.γ i.1 *
              ⟪S.deltaBatch state i ω, x - S.x state (i.1 - 1) ω⟫_ℝ +
            S.γ i.1 * ‖S.deltaBatch state i ω‖ ^ 2 /
              (2 * (S.β i.1 - S.L * S.γ i.1)) := by
          ring

/-- Martingale cancellation used in Theorem 7.11 after Eq. (7.2.50).

The proof first keeps Eq. (7.2.50) for an arbitrary feasible comparison point
`x`, and only then specializes to `x = x*`.  This predicate records the
source-level consequence of SFO freshness and unbiasedness as a well-defined
expectation identity rather than as a raw total integral.
-/
def theorem711MartingaleCancellation (S : Setup Ω Ξ E)
    (state : ℕ → Ω → {x : E // x ∈ S.X} × {x : E // x ∈ S.X}) : Prop :=
  ∀ (i : PositiveTime) (j : ℕ), j ∈ Finset.Icc 1 (S.batchSize i) →
    ∀ x : E, x ∈ S.X →
      S.sourceExpectationEq
        (fun ω => ⟪S.deltaAtom state i j ω, x - S.x state (i.1 - 1) ω⟫_ℝ) 0

/-- Mini-batch variance relation (7.2.47) in the form consumed by Theorem 7.11.

The source proves this from the SFO moment assumptions plus fresh mini-batch
samples.  For relational Algorithm 7.8 states, the batch estimator is represented
by `deltaBatch`, so the source-boundary interface exposes the resulting
well-defined second-moment inequality directly.
-/
def theorem711MiniBatchVarianceBound (S : Setup Ω Ξ E)
    (state : ℕ → Ω → {x : E // x ∈ S.X} × {x : E // x ∈ S.X}) : Prop :=
  ∀ i : PositiveTime,
    S.sourceExpectationLe
      (fun ω => ‖S.deltaBatch state i ω‖ ^ 2)
      (S.σ ^ 2 / (S.batchSize i : ℝ))

/-- SFO freshness interface used in Theorem 7.11 after Eq. (7.2.50).

The PDF sentence immediately after Eq. (7.2.50) states that the residuals
`δ_{i,j}` are independent of the search point `x_{i-1}`.  The martingale
cancellation and mini-batch variance estimates consumed by parts (a)/(b) are
kept as derived bridge theorems below, rather than hidden as extra conjuncts of
this source-facing freshness assumption.
-/
def SFO_Independence_Theorem7_11 (S : Setup Ω Ξ E)
    (state : ℕ → Ω → {x : E // x ∈ S.X} × {x : E // x ∈ S.X}) : Prop :=
  ∀ (i : PositiveTime) (j : ℕ), j ∈ Finset.Icc 1 (S.batchSize i) →
    ProbabilityTheory.IndepFun
      (fun ω => S.deltaAtom state i j ω)
      (fun ω => S.x state (i.1 - 1) ω) S.P

theorem SFO_Independence_Theorem7_11_raw (S : Setup Ω Ξ E)
    {state : ℕ → Ω → {x : E // x ∈ S.X} × {x : E // x ∈ S.X}}
    (hFresh : S.SFO_Independence_Theorem7_11 state) :
    ∀ (i : PositiveTime) (j : ℕ), j ∈ Finset.Icc 1 (S.batchSize i) →
      ProbabilityTheory.IndepFun
        (fun ω => S.deltaAtom state i j ω)
        (fun ω => S.x state (i.1 - 1) ω) S.P :=
  hFresh

/-- Source-derived martingale bridge for Theorem 7.11, proof step after Eq.
(7.2.50).

This is the proof obligation represented in the PDF by "by our assumptions on
the SFO ... hence E[<δ_{i,j}, x* - x_{i-1}>] = 0".  Its hypotheses are exactly
the displayed SFO moment assumptions, relational generated-state semantics,
adaptedness, and the raw residual freshness clause above.  It is not a
projection from a strengthened freshness predicate.
-/
theorem theorem711MartingaleCancellation_of_sfo_freshness (S : Setup Ω Ξ E)
    {state : ℕ → Ω → {x : E // x ∈ S.X} × {x : E // x ∈ S.X}}
    (hstate : S.IsOuterState state)
    (hAdapted : S.OuterStateAdapted state)
    (hBasis : S.SFOSampleBasis_Algorithm7_8)
    (hSFO : S.SFOAssumptions_7_2_43_44)
    (hFresh : S.SFO_Independence_Theorem7_11 state) :
    S.theorem711MartingaleCancellation state := by
  classical
  intro i j hj x hx
  have hUnbiased : S.SFO_Unbiased_7_2_43 := S.SFOAssumptions_unbiased hSFO
  have hFreshAtom :
      ProbabilityTheory.IndepFun
        (fun ω => S.deltaAtom state i j ω)
        (fun ω => S.x state (i.1 - 1) ω) S.P :=
    hFresh i j hj
  have hxPastMeas :
      Measurable[S.strictPastSampleHistory (i.1 - 1)]
        (fun ω => S.x state (i.1 - 1) ω) :=
    S.outerStateAdapted_x_strictPast_measurable state hAdapted (i.1 - 1)
  have hFlatSampleIndep :
      ProbabilityTheory.iIndepFun S.flatSample (S.P : Measure Ω) := by
    simpa [flatSample] using hBasis.2
  have hzMem : ∀ ω, S.z state i.1 ω ∈ S.X := fun ω => S.z_mem state i.1 ω i.2
  let Q : Type _ := {z : E // z ∈ S.X} × E
  let query : Ω → Q := fun ω => (⟨S.z state i.1 ω, hzMem ω⟩, S.x state (i.1 - 1) ω)
  let sample : Ω → Ξ := fun ω => S.ξ i.1 j ω
  let residual : Q → Ξ → E := fun q ξ => S.G q.1.1 ξ - S.grad q.1
  let direction : Q → E := fun q => x - q.2
  have hquery_meas : Measurable query := by
    have hy : Measurable (fun ω => S.y state (i.1 - 1) ω) :=
      S.outerStateAdapted_y_measurable state hAdapted (i.1 - 1)
    have hxMeas : Measurable (fun ω => S.x state (i.1 - 1) ω) :=
      S.outerStateAdapted_x_measurable state hAdapted (i.1 - 1)
    have hzMeas : Measurable (fun ω => S.z state i.1 ω) := by
      simpa [z] using ((hy.const_smul (1 - S.γ i.1)).add (hxMeas.const_smul (S.γ i.1)))
    have hzSubtype :
        Measurable (fun ω => (⟨S.z state i.1 ω, hzMem ω⟩ : {z : E // z ∈ S.X})) := by
      exact hzMeas.subtype_mk
    simpa [query, Q] using hzSubtype.prodMk hxMeas
  have hsample_meas : Measurable sample := by
    simpa [sample] using hBasis.1 i.1 j
  have hres_meas :
      Measurable (fun p : Q × Ξ => residual p.1 p.2) := by
    have hresGlobal :
        S.sourceOracleResidualJointMeasurable :=
      S.SFO_Unbiased_7_2_43_residual_joint_measurable hUnbiased x hx i j hj
    have hproj :
        Measurable
          ((fun p : Q × Ξ => (p.1.1, p.2)) :
            Q × Ξ → {z : E // z ∈ S.X} × Ξ) :=
      measurable_fst.fst.prodMk measurable_snd
    simpa [sourceOracleResidualJointMeasurable, residual, Q] using hresGlobal.comp hproj
  have hdirection_meas : Measurable direction := by
    simpa [direction] using (measurable_const.sub measurable_snd)
  have hsample_law_int :
      ∀ q : Q, Integrable (fun ξ => residual q ξ) (Measure.map sample S.P) := by
    intro q
    have hφ_meas : Measurable (fun ξ : Ξ => residual q ξ) := by
      have hpair : Measurable (fun ξ : Ξ => ((q, ξ) : Q × Ξ)) := by
        exact (measurable_const : Measurable (fun _ : Ξ => q)).prodMk measurable_id
      simpa using hres_meas.comp hpair
    have hG_int : Integrable (fun ω => S.G q.1.1 (S.ξ i.1 j ω)) (S.P : Measure Ω) := by
      have hwd :=
        S.SFO_Unbiased_7_2_43_expectationWellDefined hUnbiased q.1.1 q.1.2 i j hj
      simpa using
        (SOptLib.expectationWellDefined_iff_integrable (S.P : Measure Ω) _).mp hwd
    have hres_base_int : Integrable (fun ω => residual q (sample ω)) (S.P : Measure Ω) := by
      have hconst_int : Integrable (fun _ : Ω => S.grad q.1) (S.P : Measure Ω) :=
        integrable_const (c := S.grad q.1)
      simpa [residual, sample] using hG_int.sub hconst_int
    exact
      (integrable_map_measure hφ_meas.aestronglyMeasurable hsample_meas.aemeasurable).mpr
        (by simpa [Function.comp_def] using hres_base_int)
  have hsample_law_zero :
      ∀ q : Q, ∫ ξ, residual q ξ ∂Measure.map sample S.P = 0 := by
    intro q
    have hmean :=
      S.SFO_Unbiased_7_2_43_integral hUnbiased q.1.1 q.1.2 i j hj
    have hφ_meas : Measurable (fun ξ : Ξ => residual q ξ) := by
      have hpair : Measurable (fun ξ : Ξ => ((q, ξ) : Q × Ξ)) := by
        exact (measurable_const : Measurable (fun _ : Ξ => q)).prodMk measurable_id
      simpa using hres_meas.comp hpair
    have hG_int : Integrable (fun ω => S.G q.1.1 (S.ξ i.1 j ω)) (S.P : Measure Ω) := by
      have hwd :=
        S.SFO_Unbiased_7_2_43_expectationWellDefined hUnbiased q.1.1 q.1.2 i j hj
      simpa using
        (SOptLib.expectationWellDefined_iff_integrable (S.P : Measure Ω) _).mp hwd
    have hconst_int : Integrable (fun _ : Ω => S.grad q.1) (S.P : Measure Ω) :=
      integrable_const (c := S.grad q.1)
    have hunb : ∫ ω, residual q (sample ω) ∂(S.P : Measure Ω) = 0 := by
      rw [show (∫ ω, residual q (sample ω) ∂(S.P : Measure Ω)) =
          ∫ ω, S.G q.1.1 (S.ξ i.1 j ω) - S.grad q.1 ∂(S.P : Measure Ω) by
        rfl]
      rw [integral_sub hG_int hconst_int]
      simp [hmean]
    exact (integral_map hsample_meas.aemeasurable hφ_meas.aestronglyMeasurable).trans hunb
  have hquery_sample_indep :
      ProbabilityTheory.IndepFun query sample S.P := by
    have hyPast : Measurable[S.strictPastSampleHistory (i.1 - 1)]
        (fun ω => S.y state (i.1 - 1) ω) :=
      S.outerStateAdapted_y_strictPast_measurable state hAdapted (i.1 - 1)
    have hxPast : Measurable[S.strictPastSampleHistory (i.1 - 1)]
        (fun ω => S.x state (i.1 - 1) ω) :=
      S.outerStateAdapted_x_strictPast_measurable state hAdapted (i.1 - 1)
    have hzPast : Measurable[S.strictPastSampleHistory (i.1 - 1)]
        (fun ω => S.z state i.1 ω) := by
      simpa [z] using
        ((hyPast.const_smul (1 - S.γ i.1)).add (hxPast.const_smul (S.γ i.1)))
    have hzSubtypePast :
        Measurable[S.strictPastSampleHistory (i.1 - 1)]
          (fun ω => (⟨S.z state i.1 ω, hzMem ω⟩ : {z : E // z ∈ S.X})) := by
      exact hzPast.subtype_mk
    have hqueryPast : Measurable[S.strictPastSampleHistory (i.1 - 1)] query := by
      simpa [query, Q] using hzSubtypePast.prodMk hxPast
    let ξpos : ℕ × ℕ → Ω → Ξ := fun q ω => S.ξ (q.1 + 1) (q.2 + 1) ω
    have hξpos_meas : ∀ q, Measurable (ξpos q) := by
      intro q
      exact hBasis.1 (q.1 + 1) (q.2 + 1)
    have hpair_inj : Function.Injective (fun q : ℕ × ℕ => Nat.pair q.1 q.2) := by
      intro a b hab
      have h := congrArg Nat.unpair hab
      simpa [Nat.unpair_pair] using h
    have hξpos_iIndep : ProbabilityTheory.iIndepFun ξpos (S.P : Measure Ω) := by
      have hpre := hFlatSampleIndep.precomp hpair_inj
      have hfun : (fun q : ℕ × ℕ => S.flatSample (Nat.pair q.1 q.2)) = ξpos := by
        funext q ω
        simp [ξpos, flatSample, Nat.unpair_pair]
      simpa [hfun] using hpre
    let pastSet : Set (ℕ × ℕ) := {q | q.1 + 1 ≤ i.1 - 1}
    let current : ℕ × ℕ := (i.1 - 1, j - 1)
    have hj_one : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hcurrent_eq : ξpos current = sample := by
      funext ω
      simp [ξpos, current, sample, Nat.sub_add_cancel i.2, Nat.sub_add_cancel hj_one]
    have hpast_disj : Disjoint pastSet ({current} : Set (ℕ × ℕ)) := by
      rw [Set.disjoint_singleton_right]
      intro hmem
      dsimp [pastSet, current] at hmem
      omega
    have hpast_iSup_indep_current_iSup :
        ProbabilityTheory.Indep
          (⨆ q ∈ pastSet, MeasurableSpace.comap (ξpos q)
            (by infer_instance : MeasurableSpace Ξ))
          (⨆ q ∈ ({current} : Set (ℕ × ℕ)), MeasurableSpace.comap (ξpos q)
            (by infer_instance : MeasurableSpace Ξ))
          (S.P : Measure Ω) := by
      classical
      let mPair : ℕ × ℕ → MeasurableSpace Ω := fun q =>
        MeasurableSpace.comap (ξpos q) (by infer_instance : MeasurableSpace Ξ)
      have hiPair : ProbabilityTheory.iIndep mPair (S.P : Measure Ω) := by
        simpa [mPair] using hξpos_iIndep.iIndep
      have h_le : ∀ q, mPair q ≤ (by infer_instance : MeasurableSpace Ω) := by
        intro q
        simpa [mPair] using (hξpos_meas q).comap_le
      simpa [mPair] using
        ProbabilityTheory.indep_iSup_of_disjoint (m := mPair) h_le hiPair
          (S := pastSet) (T := ({current} : Set (ℕ × ℕ))) hpast_disj
    have hpast_indep_current :
        ProbabilityTheory.Indep
          (⨆ q ∈ pastSet, MeasurableSpace.comap (ξpos q)
            (by infer_instance : MeasurableSpace Ξ))
          (MeasurableSpace.comap (ξpos current)
            (by infer_instance : MeasurableSpace Ξ))
          (S.P : Measure Ω) := by
      simpa [current] using hpast_iSup_indep_current_iSup
    have hstrict_le :
        S.strictPastSampleHistory (i.1 - 1) ≤
          (⨆ q ∈ pastSet, MeasurableSpace.comap (ξpos q)
            (by infer_instance : MeasurableSpace Ξ)) := by
      rw [strictPastSampleHistory]
      refine iSup_le ?_
      intro t
      refine iSup_le ?_
      intro r
      let q : ℕ × ℕ := (t.1 - 1, r.1 - 1)
      have hr_one : 1 ≤ r.1 := (Finset.mem_Icc.mp r.2).1
      have hqmem : q ∈ pastSet := by
        dsimp [pastSet, q]
        simpa [Nat.sub_add_cancel t.2.1] using t.2.2
      calc
        MeasurableSpace.comap (fun ω => S.ξ t.1 r.1 ω)
            (by infer_instance : MeasurableSpace Ξ)
            = MeasurableSpace.comap (ξpos q) (by infer_instance : MeasurableSpace Ξ) := by
              congr 1
              funext ω
              simp [ξpos, q, Nat.sub_add_cancel t.2.1, Nat.sub_add_cancel hr_one]
        _ ≤ (⨆ q ∈ pastSet, MeasurableSpace.comap (ξpos q)
            (by infer_instance : MeasurableSpace Ξ)) := by
              exact le_iSup_of_le q (le_iSup_of_le hqmem le_rfl)
    have hstrict_indep_current :
        ProbabilityTheory.Indep
          (S.strictPastSampleHistory (i.1 - 1))
          (MeasurableSpace.comap sample (by infer_instance : MeasurableSpace Ξ))
          (S.P : Measure Ω) := by
      have hshrunk := ProbabilityTheory.indep_of_indep_of_le_left hpast_indep_current hstrict_le
      simpa [hcurrent_eq] using hshrunk
    exact indepFun_of_measurable_left_of_indep_comap hqueryPast hstrict_indep_current
  have hzero :
      ∫ ω, ⟪direction (query ω), residual (query ω) (sample ω)⟫_ℝ ∂S.P = 0 := by
    exact
      randomQuery_inner_oracleResidual_integral_eq_zero_of_fixed_zero
        (P := (S.P : Measure Ω)) (ν := Measure.map sample S.P)
        (query := query) (sample := sample) (residual := residual)
        (d := direction) hres_meas hdirection_meas hquery_meas hsample_meas
        hquery_sample_indep rfl hsample_law_int hsample_law_zero
  have hscalar_int :
      Integrable
        (fun ω => ⟪S.deltaAtom state i j ω, x - S.x state (i.1 - 1) ω⟫_ℝ)
        (S.P : Measure Ω) := by
    have hVariance : S.SFO_Variance_7_2_44 := S.SFOAssumptions_variance hSFO
    let ν : Measure Ξ := Measure.map sample (S.P : Measure Ω)
    have hfixed_int :
        ∀ q : Q, Integrable (fun ξ => ‖residual q ξ‖ ^ 2) ν := by
      intro q
      have hφ_meas : Measurable (fun ξ : Ξ => ‖residual q ξ‖ ^ 2) := by
        have hpair : Measurable (fun ξ : Ξ => ((q, ξ) : Q × Ξ)) := by
          exact (measurable_const : Measurable (fun _ : Ξ => q)).prodMk measurable_id
        simpa using (hres_meas.comp hpair).norm.pow_const 2
      have hbase :
          Integrable (fun ω => ‖residual q (sample ω)‖ ^ 2) (S.P : Measure Ω) := by
        have hwd :=
          S.SFO_Variance_7_2_44_wellDefined_obligation
            hVariance q.1.1 q.1.2 i j hj
        simpa [oracleVarianceIntegrand, residual, sample] using
          (SOptLib.expectationWellDefined_iff_integrable (S.P : Measure Ω) _).mp hwd
      exact
        (integrable_map_measure hφ_meas.aestronglyMeasurable hsample_meas.aemeasurable).mpr
          (by simpa [Function.comp_def] using hbase)
    have hfixed_bound :
        ∀ q : Q, ∫ ξ, ‖residual q ξ‖ ^ 2 ∂ν ≤ S.σ ^ 2 := by
      intro q
      have hφ_meas : Measurable (fun ξ : Ξ => ‖residual q ξ‖ ^ 2) := by
        have hpair : Measurable (fun ξ : Ξ => ((q, ξ) : Q × Ξ)) := by
          exact (measurable_const : Measurable (fun _ : Ξ => q)).prodMk measurable_id
        simpa using (hres_meas.comp hpair).norm.pow_const 2
      have hmap :
          (∫ ξ, ‖residual q ξ‖ ^ 2 ∂ν) =
            ∫ ω, ‖residual q (sample ω)‖ ^ 2 ∂(S.P : Measure Ω) := by
        dsimp [ν]
        exact integral_map hsample_meas.aemeasurable hφ_meas.aestronglyMeasurable
      rw [hmap]
      simpa [oracleVarianceIntegrand, residual, sample] using
        S.SFO_Variance_7_2_44_integral hVariance q.1.1 q.1.2 i j hj
    have hres_sq :
        Integrable (fun ω => ‖residual (query ω) (sample ω)‖ ^ 2)
          (S.P : Measure Ω) := by
      simpa [residual] using
        integrable_sq_oracleResidual_of_indep_fixed_variance_bound
          (P := (S.P : Measure Ω)) (ν := ν)
          (query := query) (sample := sample)
          (G := fun q : Q => fun ξ : Ξ => S.G q.1.1 ξ)
          (target := fun q : Q => S.grad q.1) (σ2 := S.σ ^ 2)
          (by simpa [residual] using hres_meas)
          hquery_meas hsample_meas hquery_sample_indep rfl (sq_nonneg S.σ)
          (by intro q; simpa [residual] using hfixed_int q)
          (by intro q; simpa [residual] using hfixed_bound q)
    have hmult_sq :
        Integrable (fun ω => ‖direction (query ω)‖ ^ 2) (S.P : Measure Ω) := by
      have hx_meas :
          AEStronglyMeasurable (fun _ : Ω => x) (S.P : Measure Ω) :=
        (measurable_const : Measurable (fun _ : Ω => x)).aestronglyMeasurable_measure
      have hy_meas :
          AEStronglyMeasurable (fun ω => S.x state (i.1 - 1) ω) (S.P : Measure Ω) :=
        (S.outerStateAdapted_x_measurable state hAdapted (i.1 - 1)).aestronglyMeasurable_measure
      have hx_mem : ∀ᵐ ω ∂(S.P : Measure Ω), (fun _ : Ω => x) ω ∈ S.X :=
        Filter.Eventually.of_forall (fun _ => hx)
      have hy_mem : ∀ᵐ ω ∂(S.P : Measure Ω), S.x state (i.1 - 1) ω ∈ S.X :=
        Filter.Eventually.of_forall (fun ω => S.x_mem state (i.1 - 1) ω)
      have hdiam : ∀ ⦃a b : E⦄, a ∈ S.X → b ∈ S.X → ‖a - b‖ ≤ S.diameter := by
        rcases S.diameter_spec with ⟨_, _, _, _, _, hbound⟩
        intro a b ha hb
        exact hbound a ha b hb
      have h :=
        integrable_sq_norm_sub_of_measurable_mem_diameter_bound
          (μ := (S.P : Measure Ω)) (X := S.X) (D := S.diameter)
          (x := fun _ : Ω => x) (y := fun ω => S.x state (i.1 - 1) ω)
          hx_meas hy_meas hx_mem hy_mem (by intro a b ha hb; exact hdiam ha hb)
      simpa [direction, query] using h
    have hmult_meas :
        AEStronglyMeasurable (fun ω => direction (query ω)) (S.P : Measure Ω) :=
      (hdirection_meas.comp hquery_meas).aestronglyMeasurable_measure
    have hinner :
        Integrable
          (fun ω => ⟪residual (query ω) (sample ω), direction (query ω)⟫_ℝ)
          (S.P : Measure Ω) := by
      simpa [residual] using
        integrable_oracle_residual_inner_of_l2_multiplier
          (P := (S.P : Measure Ω))
          (query := query) (sample := sample)
          (G := fun q : Q => fun ξ : Ξ => S.G q.1.1 ξ)
          (target := fun q : Q => S.grad q.1)
          (multiplier := fun ω => direction (query ω))
          hquery_meas hsample_meas (by simpa [residual] using hres_meas)
          hmult_meas
          (by simpa [residual] using hres_sq)
          hmult_sq
    simpa [deltaAtom, query, sample, residual, direction] using hinner
  refine ⟨?_, ?_⟩
  · exact (SOptLib.expectationWellDefined_iff_integrable (S.P : Measure Ω) _).mpr hscalar_int
  · change ∫ ω, ⟪S.deltaAtom state i j ω, x - S.x state (i.1 - 1) ω⟫_ℝ ∂S.P = 0
    simpa [deltaAtom, query, sample, residual, direction, real_inner_comm] using hzero

/-- Mini-batch decomposition `δ_k = B_k^{-1} sum_j δ_{k,j}`, source proof first
sentence. -/
theorem deltaBatch_eq_average_deltaAtom (S : Setup Ω Ξ E)
    (state : ℕ → Ω → {x : E // x ∈ S.X} × {x : E // x ∈ S.X})
    (k : PositiveTime) (ω : Ω) :
    S.deltaBatch state k ω =
      ((S.batchSize k : ℝ)⁻¹) •
        Finset.sum (Finset.Icc 1 (S.batchSize k)) (fun j => S.deltaAtom state k j ω) := by
  let I : Finset ℕ := Finset.Icc 1 (S.batchSize k)
  let c : E := S.grad ⟨S.z state k.1 ω, S.z_mem state k.1 ω k.2⟩
  let a : ℕ → E := fun j => S.G (S.z state k.1 ω) (S.ξ k.1 j ω)
  have hcard : I.card = S.batchSize k := by
    dsimp [I]
    rw [Nat.card_Icc]
    omega
  have hIpos : 0 < I.card := by
    rw [hcard]
    exact S.batchSize_pos k
  have hcenter :
      ((S.batchSize k : ℝ)⁻¹) • Finset.sum I a - c =
        ((S.batchSize k : ℝ)⁻¹) • Finset.sum I (fun j => a j - c) := by
    simpa [hcard] using
      (inv_card_smul_sum_sub_const_eq I a c hIpos).symm
  simpa [deltaBatch, batchGradient, miniBatchGradientAt, SOptLib.miniBatchOracleAverage,
    deltaAtom, I, a, c] using hcenter

/-- Source-derived mini-batch variance bridge for Theorem 7.11, relation
(7.2.47) specialized to the relational Algorithm 7.8 state.

The source proof treats this as the standard mini-batch estimator consequence
of the SFO variance bound and fresh samples.  The statement keeps that
consequence as a theorem from `SFOAssumptions_7_2_43_44` plus raw freshness,
instead of adding it to the source-facing independence predicate.
-/
theorem theorem711MiniBatchVarianceBound_of_sfo_assumptions (S : Setup Ω Ξ E)
    {state : ℕ → Ω → {x : E // x ∈ S.X} × {x : E // x ∈ S.X}}
    (hstate : S.IsOuterState state)
    (hAdapted : S.OuterStateAdapted state)
    (hBasis : S.SFOSampleBasis_Algorithm7_8)
    (hSFO : S.SFOAssumptions_7_2_43_44)
    (hFresh : S.SFO_Independence_Theorem7_11 state) :
    S.theorem711MiniBatchVarianceBound state := by
  classical
  intro i
  have hUnbiased : S.SFO_Unbiased_7_2_43 := S.SFOAssumptions_unbiased hSFO
  have hVariance : S.SFO_Variance_7_2_44 := S.SFOAssumptions_variance hSFO
  let I : Finset ℕ := Finset.Icc 1 (S.batchSize i)
  let Xq : Type _ := {z : E // z ∈ S.X}
  let xq : Ω → Xq := fun ω => ⟨S.z state i.1 ω, S.z_mem state i.1 ω i.2⟩
  let Y : ℕ → Ω → Ξ := fun j ω => S.ξ i.1 j ω
  let Gq : Xq → Ξ → E := fun z ξ => S.G z.1 ξ
  let target : Xq → E := fun z => S.grad z
  have hmpos : 0 < S.batchSize i := S.batchSize_pos i
  have hcard : I.card = S.batchSize i := by
    dsimp [I]
    rw [Nat.card_Icc]
    omega
  have hres_meas :
      Measurable (fun p : Xq × Ξ => Gq p.1 p.2 - target p.1) := by
    have hOne : (1 : ℕ) ∈ I := by
      dsimp [I]
      exact Finset.mem_Icc.mpr ⟨le_rfl, Nat.succ_le_of_lt hmpos⟩
    have hresGlobal :
        S.sourceOracleResidualJointMeasurable :=
      S.SFO_Unbiased_7_2_43_residual_joint_measurable hUnbiased
        S.x0 S.hx0_mem i 1 (by simpa [I] using hOne)
    simpa [sourceOracleResidualJointMeasurable, Xq, Gq, target] using hresGlobal
  have hxq_meas : Measurable xq := by
    have hy : Measurable (fun ω => S.y state (i.1 - 1) ω) :=
      S.outerStateAdapted_y_measurable state hAdapted (i.1 - 1)
    have hx : Measurable (fun ω => S.x state (i.1 - 1) ω) :=
      S.outerStateAdapted_x_measurable state hAdapted (i.1 - 1)
    have hz : Measurable (fun ω => S.z state i.1 ω) := by
      simpa [z] using ((hy.const_smul (1 - S.γ i.1)).add (hx.const_smul (S.γ i.1)))
    simpa [xq, Xq] using hz.subtype_mk
  have hY_meas : ∀ j ∈ I, Measurable (Y j) := by
    intro j hj
    simpa [Y] using hBasis.1 i.1 j
  have hindep_query : ∀ j ∈ I, ProbabilityTheory.IndepFun xq (Y j) S.P := by
    intro j hj
    have hyPast : Measurable[S.strictPastSampleHistory (i.1 - 1)]
        (fun ω => S.y state (i.1 - 1) ω) :=
      S.outerStateAdapted_y_strictPast_measurable state hAdapted (i.1 - 1)
    have hxPast : Measurable[S.strictPastSampleHistory (i.1 - 1)]
        (fun ω => S.x state (i.1 - 1) ω) :=
      S.outerStateAdapted_x_strictPast_measurable state hAdapted (i.1 - 1)
    have hzPast : Measurable[S.strictPastSampleHistory (i.1 - 1)]
        (fun ω => S.z state i.1 ω) := by
      simpa [z] using
        ((hyPast.const_smul (1 - S.γ i.1)).add (hxPast.const_smul (S.γ i.1)))
    have hxqPast : Measurable[S.strictPastSampleHistory (i.1 - 1)] xq := by
      simpa [xq, Xq] using hzPast.subtype_mk
    let ξpos : ℕ × ℕ → Ω → Ξ := fun q ω => S.ξ (q.1 + 1) (q.2 + 1) ω
    have hξpos_meas : ∀ q, Measurable (ξpos q) := by
      intro q
      exact hBasis.1 (q.1 + 1) (q.2 + 1)
    have hpair_inj : Function.Injective (fun q : ℕ × ℕ => Nat.pair q.1 q.2) := by
      intro a b hab
      have h := congrArg Nat.unpair hab
      simpa [Nat.unpair_pair] using h
    have hFlatSampleIndep : ProbabilityTheory.iIndepFun S.flatSample (S.P : Measure Ω) := by
      simpa [flatSample] using hBasis.2
    have hξpos_iIndep : ProbabilityTheory.iIndepFun ξpos (S.P : Measure Ω) := by
      have hpre := hFlatSampleIndep.precomp hpair_inj
      have hfun : (fun q : ℕ × ℕ => S.flatSample (Nat.pair q.1 q.2)) = ξpos := by
        funext q ω
        simp [ξpos, flatSample, Nat.unpair_pair]
      simpa [hfun] using hpre
    let pastSet : Set (ℕ × ℕ) := {q | q.1 + 1 ≤ i.1 - 1}
    let current : ℕ × ℕ := (i.1 - 1, j - 1)
    have hj_one : 1 ≤ j := (Finset.mem_Icc.mp (by simpa [I] using hj)).1
    have hcurrent_eq : ξpos current = Y j := by
      funext ω
      simp [ξpos, current, Y, Nat.sub_add_cancel i.2, Nat.sub_add_cancel hj_one]
    have hpast_disj : Disjoint pastSet ({current} : Set (ℕ × ℕ)) := by
      rw [Set.disjoint_singleton_right]
      intro hmem
      dsimp [pastSet, current] at hmem
      omega
    have hpast_iSup_indep_current_iSup :
        ProbabilityTheory.Indep
          (⨆ q ∈ pastSet, MeasurableSpace.comap (ξpos q)
            (by infer_instance : MeasurableSpace Ξ))
          (⨆ q ∈ ({current} : Set (ℕ × ℕ)), MeasurableSpace.comap (ξpos q)
            (by infer_instance : MeasurableSpace Ξ))
          (S.P : Measure Ω) := by
      classical
      let mPair : ℕ × ℕ → MeasurableSpace Ω := fun q =>
        MeasurableSpace.comap (ξpos q) (by infer_instance : MeasurableSpace Ξ)
      have hiPair : ProbabilityTheory.iIndep mPair (S.P : Measure Ω) := by
        simpa [mPair] using hξpos_iIndep.iIndep
      have h_le : ∀ q, mPair q ≤ (by infer_instance : MeasurableSpace Ω) := by
        intro q
        simpa [mPair] using (hξpos_meas q).comap_le
      simpa [mPair] using
        ProbabilityTheory.indep_iSup_of_disjoint (m := mPair) h_le hiPair
          (S := pastSet) (T := ({current} : Set (ℕ × ℕ))) hpast_disj
    have hpast_indep_current :
        ProbabilityTheory.Indep
          (⨆ q ∈ pastSet, MeasurableSpace.comap (ξpos q)
            (by infer_instance : MeasurableSpace Ξ))
          (MeasurableSpace.comap (ξpos current)
            (by infer_instance : MeasurableSpace Ξ))
          (S.P : Measure Ω) := by
      simpa [current] using hpast_iSup_indep_current_iSup
    have hstrict_le :
        S.strictPastSampleHistory (i.1 - 1) ≤
          (⨆ q ∈ pastSet, MeasurableSpace.comap (ξpos q)
            (by infer_instance : MeasurableSpace Ξ)) := by
      rw [strictPastSampleHistory]
      refine iSup_le ?_
      intro t
      refine iSup_le ?_
      intro r
      let q : ℕ × ℕ := (t.1 - 1, r.1 - 1)
      have hr_one : 1 ≤ r.1 := (Finset.mem_Icc.mp r.2).1
      have hqmem : q ∈ pastSet := by
        dsimp [pastSet, q]
        simpa [Nat.sub_add_cancel t.2.1] using t.2.2
      calc
        MeasurableSpace.comap (fun ω => S.ξ t.1 r.1 ω)
            (by infer_instance : MeasurableSpace Ξ)
            = MeasurableSpace.comap (ξpos q) (by infer_instance : MeasurableSpace Ξ) := by
              congr 1
              funext ω
              simp [ξpos, q, Nat.sub_add_cancel t.2.1, Nat.sub_add_cancel hr_one]
        _ ≤ (⨆ q ∈ pastSet, MeasurableSpace.comap (ξpos q)
            (by infer_instance : MeasurableSpace Ξ)) := by
              exact le_iSup_of_le q (le_iSup_of_le hqmem le_rfl)
    have hstrict_indep_current :
        ProbabilityTheory.Indep
          (S.strictPastSampleHistory (i.1 - 1))
          (MeasurableSpace.comap (Y j) (by infer_instance : MeasurableSpace Ξ))
          (S.P : Measure Ω) := by
      have hshrunk := ProbabilityTheory.indep_of_indep_of_le_left hpast_indep_current hstrict_le
      simpa [hcurrent_eq] using hshrunk
    exact indepFun_of_measurable_left_of_indep_comap hxqPast hstrict_indep_current
  have hindep_query_peer :
      ∀ j ∈ I, ∀ l ∈ I, j ≠ l →
        ProbabilityTheory.IndepFun (fun ω => (xq ω, Y l ω)) (Y j) S.P := by
    intro j hj l hl hne
    have hyPast : Measurable[S.strictPastSampleHistory (i.1 - 1)]
        (fun ω => S.y state (i.1 - 1) ω) :=
      S.outerStateAdapted_y_strictPast_measurable state hAdapted (i.1 - 1)
    have hxPast : Measurable[S.strictPastSampleHistory (i.1 - 1)]
        (fun ω => S.x state (i.1 - 1) ω) :=
      S.outerStateAdapted_x_strictPast_measurable state hAdapted (i.1 - 1)
    have hzPast : Measurable[S.strictPastSampleHistory (i.1 - 1)]
        (fun ω => S.z state i.1 ω) := by
      simpa [z] using
        ((hyPast.const_smul (1 - S.γ i.1)).add (hxPast.const_smul (S.γ i.1)))
    have hxqPast : Measurable[S.strictPastSampleHistory (i.1 - 1)] xq := by
      simpa [xq, Xq] using hzPast.subtype_mk
    let ξpos : ℕ × ℕ → Ω → Ξ := fun q ω => S.ξ (q.1 + 1) (q.2 + 1) ω
    have hξpos_meas : ∀ q, Measurable (ξpos q) := by
      intro q
      exact hBasis.1 (q.1 + 1) (q.2 + 1)
    have hpair_inj : Function.Injective (fun q : ℕ × ℕ => Nat.pair q.1 q.2) := by
      intro a b hab
      have h := congrArg Nat.unpair hab
      simpa [Nat.unpair_pair] using h
    have hFlatSampleIndep : ProbabilityTheory.iIndepFun S.flatSample (S.P : Measure Ω) := by
      simpa [flatSample] using hBasis.2
    have hξpos_iIndep : ProbabilityTheory.iIndepFun ξpos (S.P : Measure Ω) := by
      have hpre := hFlatSampleIndep.precomp hpair_inj
      have hfun : (fun q : ℕ × ℕ => S.flatSample (Nat.pair q.1 q.2)) = ξpos := by
        funext q ω
        simp [ξpos, flatSample, Nat.unpair_pair]
      simpa [hfun] using hpre
    let pastSet : Set (ℕ × ℕ) := {q | q.1 + 1 ≤ i.1 - 1}
    let current : ℕ × ℕ := (i.1 - 1, j - 1)
    let peer : ℕ × ℕ := (i.1 - 1, l - 1)
    let leftSet : Set (ℕ × ℕ) := pastSet ∪ ({peer} : Set (ℕ × ℕ))
    have hj_one : 1 ≤ j := (Finset.mem_Icc.mp (by simpa [I] using hj)).1
    have hl_one : 1 ≤ l := (Finset.mem_Icc.mp (by simpa [I] using hl)).1
    have hcurrent_eq : ξpos current = Y j := by
      funext ω
      simp [ξpos, current, Y, Nat.sub_add_cancel i.2, Nat.sub_add_cancel hj_one]
    have hpeer_eq : ξpos peer = Y l := by
      funext ω
      simp [ξpos, peer, Y, Nat.sub_add_cancel i.2, Nat.sub_add_cancel hl_one]
    have hleft_disj : Disjoint leftSet ({current} : Set (ℕ × ℕ)) := by
      rw [Set.disjoint_singleton_right]
      intro hmem
      dsimp [leftSet] at hmem
      rcases hmem with hpast | hpeer_mem
      · dsimp [pastSet, current] at hpast
        omega
      · have hcurpeer : current = peer := by simpa using hpeer_mem
        have hsecond : j - 1 = l - 1 := congrArg Prod.snd hcurpeer
        have hjl : j = l := by omega
        exact hne hjl
    have hleft_iSup_indep_current_iSup :
        ProbabilityTheory.Indep
          (⨆ q ∈ leftSet, MeasurableSpace.comap (ξpos q)
            (by infer_instance : MeasurableSpace Ξ))
          (⨆ q ∈ ({current} : Set (ℕ × ℕ)), MeasurableSpace.comap (ξpos q)
            (by infer_instance : MeasurableSpace Ξ))
          (S.P : Measure Ω) := by
      classical
      let mPair : ℕ × ℕ → MeasurableSpace Ω := fun q =>
        MeasurableSpace.comap (ξpos q) (by infer_instance : MeasurableSpace Ξ)
      have hiPair : ProbabilityTheory.iIndep mPair (S.P : Measure Ω) := by
        simpa [mPair] using hξpos_iIndep.iIndep
      have h_le : ∀ q, mPair q ≤ (by infer_instance : MeasurableSpace Ω) := by
        intro q
        simpa [mPair] using (hξpos_meas q).comap_le
      simpa [mPair] using
        ProbabilityTheory.indep_iSup_of_disjoint (m := mPair) h_le hiPair
          (S := leftSet) (T := ({current} : Set (ℕ × ℕ))) hleft_disj
    have hleft_indep_current :
        ProbabilityTheory.Indep
          (⨆ q ∈ leftSet, MeasurableSpace.comap (ξpos q)
            (by infer_instance : MeasurableSpace Ξ))
          (MeasurableSpace.comap (ξpos current)
            (by infer_instance : MeasurableSpace Ξ))
          (S.P : Measure Ω) := by
      simpa [current] using hleft_iSup_indep_current_iSup
    have hstrict_le_left :
        S.strictPastSampleHistory (i.1 - 1) ≤
          (⨆ q ∈ leftSet, MeasurableSpace.comap (ξpos q)
            (by infer_instance : MeasurableSpace Ξ)) := by
      rw [strictPastSampleHistory]
      refine iSup_le ?_
      intro t
      refine iSup_le ?_
      intro r
      let q : ℕ × ℕ := (t.1 - 1, r.1 - 1)
      have hr_one : 1 ≤ r.1 := (Finset.mem_Icc.mp r.2).1
      have hqmem_past : q ∈ pastSet := by
        dsimp [pastSet, q]
        simpa [Nat.sub_add_cancel t.2.1] using t.2.2
      have hqmem_left : q ∈ leftSet := by
        exact Or.inl hqmem_past
      calc
        MeasurableSpace.comap (fun ω => S.ξ t.1 r.1 ω)
            (by infer_instance : MeasurableSpace Ξ)
            = MeasurableSpace.comap (ξpos q) (by infer_instance : MeasurableSpace Ξ) := by
              congr 1
              funext ω
              simp [ξpos, q, Nat.sub_add_cancel t.2.1, Nat.sub_add_cancel hr_one]
        _ ≤ (⨆ q ∈ leftSet, MeasurableSpace.comap (ξpos q)
            (by infer_instance : MeasurableSpace Ξ)) := by
              exact le_iSup_of_le q (le_iSup_of_le hqmem_left le_rfl)
    have hpeer_le_left :
        MeasurableSpace.comap (Y l) (by infer_instance : MeasurableSpace Ξ) ≤
          (⨆ q ∈ leftSet, MeasurableSpace.comap (ξpos q)
            (by infer_instance : MeasurableSpace Ξ)) := by
      calc
        MeasurableSpace.comap (Y l) (by infer_instance : MeasurableSpace Ξ)
            = MeasurableSpace.comap (ξpos peer) (by infer_instance : MeasurableSpace Ξ) := by
              rw [hpeer_eq]
        _ ≤ (⨆ q ∈ leftSet, MeasurableSpace.comap (ξpos q)
            (by infer_instance : MeasurableSpace Ξ)) := by
              have hpeer_left : peer ∈ leftSet := by
                exact Or.inr (by simp [peer])
              exact le_iSup_of_le peer (le_iSup_of_le hpeer_left le_rfl)
    have hsup_le_left :
        S.strictPastSampleHistory (i.1 - 1) ⊔
            MeasurableSpace.comap (Y l) (by infer_instance : MeasurableSpace Ξ) ≤
          (⨆ q ∈ leftSet, MeasurableSpace.comap (ξpos q)
            (by infer_instance : MeasurableSpace Ξ)) := by
      exact sup_le hstrict_le_left hpeer_le_left
    have hstrict_peer_indep_current :
        ProbabilityTheory.Indep
          (S.strictPastSampleHistory (i.1 - 1) ⊔
            MeasurableSpace.comap (Y l) (by infer_instance : MeasurableSpace Ξ))
          (MeasurableSpace.comap (Y j) (by infer_instance : MeasurableSpace Ξ))
          (S.P : Measure Ω) := by
      have hshrunk := ProbabilityTheory.indep_of_indep_of_le_left hleft_indep_current hsup_le_left
      simpa [hcurrent_eq] using hshrunk
    have hYl_sup :
        Measurable[S.strictPastSampleHistory (i.1 - 1) ⊔
            MeasurableSpace.comap (Y l) (by infer_instance : MeasurableSpace Ξ)] (Y l) :=
      measurable_iff_comap_le.mpr le_sup_right
    exact
      indepFun_prod_of_measurable_le_of_indep_comap
        hxqPast le_sup_left hYl_sup hstrict_peer_indep_current
  have hfixed_int :
      ∀ j ∈ I, ∀ z : Xq,
        Integrable (fun ω => ‖Gq z (Y j ω) - target z‖ ^ 2) S.P := by
    intro j hj z
    have hwd :=
      S.SFO_Variance_7_2_44_wellDefined_obligation hVariance z.1 z.2 i j (by simpa [I] using hj)
    simpa [oracleVarianceIntegrand, Gq, target, Y] using
      (SOptLib.expectationWellDefined_iff_integrable (S.P : Measure Ω) _).mp hwd
  have hfixed_bound :
      ∀ j ∈ I, ∀ z : Xq,
        ∫ ω, ‖Gq z (Y j ω) - target z‖ ^ 2 ∂S.P ≤ S.σ ^ 2 := by
    intro j hj z
    simpa [oracleVarianceIntegrand, Gq, target, Y] using
      S.SFO_Variance_7_2_44_integral hVariance z.1 z.2 i j (by simpa [I] using hj)
  have hfixed_zero :
      ∀ j ∈ I, ∀ z : Xq,
        ∫ ξ, Gq z ξ - target z ∂Measure.map (Y j) S.P = 0 := by
    intro j hj z
    have hmean :=
      S.SFO_Unbiased_7_2_43_integral hUnbiased z.1 z.2 i j (by simpa [I] using hj)
    have hφ_meas : Measurable (fun ξ : Ξ => Gq z ξ - target z) := by
      have hpair : Measurable (fun ξ : Ξ => ((z, ξ) : Xq × Ξ)) := by
        exact (measurable_const : Measurable (fun _ : Ξ => z)).prodMk measurable_id
      simpa using hres_meas.comp hpair
    have hG_int : Integrable (fun ω => Gq z (Y j ω)) (S.P : Measure Ω) := by
      have hwd :=
        S.SFO_Unbiased_7_2_43_expectationWellDefined hUnbiased z.1 z.2 i j
          (by simpa [I] using hj)
      simpa [Gq, Y] using
        (SOptLib.expectationWellDefined_iff_integrable (S.P : Measure Ω) _).mp hwd
    have hconst_int : Integrable (fun _ : Ω => target z) (S.P : Measure Ω) :=
      integrable_const (c := target z)
    have hunb : ∫ ω, Gq z (Y j ω) - target z ∂(S.P : Measure Ω) = 0 := by
      rw [integral_sub hG_int hconst_int]
      simp [hmean, Gq, target, Y]
    exact (integral_map (hY_meas j hj).aemeasurable hφ_meas.aestronglyMeasurable).trans hunb
  have havg_int :
      Integrable
        (fun ω =>
          ‖((S.batchSize i : ℝ)⁻¹) •
            Finset.sum I (fun j => Gq (xq ω) (Y j ω) - target (xq ω))‖ ^ 2)
        S.P := by
    exact
      integrable_sq_norm_randomQuery_centeredMiniBatchAverage_of_fixed_variance
        (P := (S.P : Measure Ω)) I (S.batchSize i) Gq target xq Y (S.σ ^ 2)
        hres_meas hxq_meas hY_meas hindep_query (sq_nonneg S.σ)
        hfixed_int hfixed_bound
  have havg_le :
      ∫ ω,
          ‖((S.batchSize i : ℝ)⁻¹) •
            Finset.sum I (fun j => Gq (xq ω) (Y j ω) - target (xq ω))‖ ^ 2 ∂S.P ≤
        S.σ ^ 2 / (S.batchSize i : ℝ) := by
    exact
      randomQuery_centeredMiniBatchAverage_secondMoment_le_variance_div_card
        (P := (S.P : Measure Ω)) I (S.batchSize i) Gq target xq Y (S.σ ^ 2)
        hmpos hcard hres_meas hxq_meas hY_meas hindep_query hindep_query_peer
        (sq_nonneg S.σ) hfixed_int hfixed_bound hfixed_zero
  have hdelta_avg :
      (fun ω => ‖S.deltaBatch state i ω‖ ^ 2) =
        fun ω =>
          ‖((S.batchSize i : ℝ)⁻¹) •
            Finset.sum I (fun j => Gq (xq ω) (Y j ω) - target (xq ω))‖ ^ 2 := by
    funext ω
    rw [S.deltaBatch_eq_average_deltaAtom state i ω]
    simp [deltaAtom, I, Xq, xq, Y, Gq, target]
  refine ⟨?_, ?_⟩
  · rw [hdelta_avg]
    exact (SOptLib.expectationWellDefined_iff_integrable (S.P : Measure Ω) _).mpr havg_int
  · change ∫ ω, ‖S.deltaBatch state i ω‖ ^ 2 ∂S.P ≤
      S.σ ^ 2 / (S.batchSize i : ℝ)
    rw [hdelta_avg]
    exact havg_le

/-- Batch martingale cancellation used in Theorem 7.11(a), proof step after
Eq. (7.2.50).

This aligns with Lan Theorem 7.11 proof step 9: the batch residual is the
literal mini-batch average from `deltaBatch_eq_average_deltaAtom`, so atomwise
martingale cancellation sums to zero.  Considered SOptLib candidates
`integral_finset_sum_const_mul_eq_zero` and
`finite_window_zero_mean_plus_quadratic_noise_integral_bound`; the former is
the exact finite-sum integral bridge used here, while the latter is a larger
window budget lemma not imported in this file and not needed for the atom-to-batch
bridge.
-/
private theorem theorem711_deltaBatch_inner_expectation_zero
    (S : Setup Ω Ξ E)
    (state : ℕ → Ω → {x : E // x ∈ S.X} × {x : E // x ∈ S.X})
    (hMartingale : S.theorem711MartingaleCancellation state)
    (i : PositiveTime) {xStar : E} (hxStar : xStar ∈ S.X) :
    S.sourceExpectationEq
      (fun ω => ⟪S.deltaBatch state i ω, xStar - S.x state (i.1 - 1) ω⟫_ℝ) 0 := by
  classical
  let I : Finset ℕ := Finset.Icc 1 (S.batchSize i)
  let c : ℝ := (S.batchSize i : ℝ)⁻¹
  let Z : ℕ → Ω → ℝ := fun j ω =>
    ⟪S.deltaAtom state i j ω, xStar - S.x state (i.1 - 1) ω⟫_ℝ
  have hZ_src : ∀ j ∈ I, S.sourceExpectationEq (Z j) 0 := by
    intro j hj
    exact hMartingale i j (by simpa [I] using hj) xStar hxStar
  have hZ_int : ∀ j ∈ I, Integrable (Z j) (S.P : Measure Ω) := by
    intro j hj
    exact
      (SOptLib.expectationWellDefined_iff_integrable (S.P : Measure Ω) (Z j)).mp
        (hZ_src j hj).1
  have hZ_zero : ∀ j ∈ I, ∫ ω, Z j ω ∂(S.P : Measure Ω) = 0 := by
    intro j hj
    simpa [SOptLib.expectation, Z] using (hZ_src j hj).2
  have hbatch_eq :
      (fun ω => ⟪S.deltaBatch state i ω, xStar - S.x state (i.1 - 1) ω⟫_ℝ) =
        fun ω => Finset.sum I (fun j => c * Z j ω) := by
    funext ω
    rw [S.deltaBatch_eq_average_deltaAtom state i ω]
    rw [inner_smul_left, sum_inner, Finset.mul_sum]
    rfl
  have hbatch_int :
      Integrable
        (fun ω => ⟪S.deltaBatch state i ω, xStar - S.x state (i.1 - 1) ω⟫_ℝ)
        (S.P : Measure Ω) := by
    rw [hbatch_eq]
    exact integrable_finset_sum I (fun j hj => (hZ_int j hj).const_mul c)
  refine ⟨?_, ?_⟩
  · exact
      (SOptLib.expectationWellDefined_iff_integrable (S.P : Measure Ω)
        (fun ω => ⟪S.deltaBatch state i ω, xStar - S.x state (i.1 - 1) ω⟫_ℝ)).mpr
        hbatch_int
  · change ∫ ω, ⟪S.deltaBatch state i ω, xStar - S.x state (i.1 - 1) ω⟫_ℝ ∂S.P = 0
    rw [hbatch_eq]
    exact integral_finset_sum_const_mul_eq_zero I (fun _ => c) Z hZ_int hZ_zero

/-- Per-index expectation budget for the stochastic terms in Theorem 7.11(a),
proof step after Eq. (7.2.50).

This aligns with Lan Theorem 7.11 proof steps 9-10: the linear residual term
has zero expectation and the mini-batch quadratic term is bounded by
`σ^2 / B_i`.  Considered SOptLib candidates
`finite_window_zero_mean_plus_quadratic_noise_integral_bound` and
`integral_scaled_finset_sum_le_scaled_sum_of_integral_bounds`; they package
larger finite-window shapes, while this route-local helper isolates the single
time-index quotient normalization needed before summing over the theorem
window.
-/
private theorem theorem711_part_a_per_index_noise_budget
    (S : Setup Ω Ξ E)
    (state : ℕ → Ω → {x : E // x ∈ S.X} × {x : E // x ∈ S.X})
    (i : PositiveTime) {xStar : E} (etaTerm varianceTerm : ℝ)
    (hBatchZero :
      S.sourceExpectationEq
        (fun ω => ⟪S.deltaBatch state i ω, xStar - S.x state (i.1 - 1) ω⟫_ℝ) 0)
    (hBatchVariance :
      S.sourceExpectationLe
        (fun ω => ‖S.deltaBatch state i ω‖ ^ 2)
        (S.σ ^ 2 / (S.batchSize i : ℝ)))
    (hGammaNat : S.GammaNat i.1 = S.Gamma i)
    (hGamma_pos : 0 < S.GammaNat i.1)
    (hγ_nonneg : 0 ≤ S.γ i.1)
    (hgap : 0 < S.β i.1 - S.L * S.γ i.1)
    (hetaTerm : etaTerm = (S.η i.1 * S.γ i.1) / S.Gamma i)
    (hvarianceTerm : varianceTerm =
      (S.γ i.1 * S.σ ^ 2) /
        (2 * S.Gamma i * (S.batchSize i : ℝ) *
          (S.β i.1 - S.L * S.γ i.1))) :
    (∫ ω,
        (S.γ i.1 / S.GammaNat i.1) *
          (S.η i.1 +
            ⟪S.deltaBatch state i ω, xStar - S.x state (i.1 - 1) ω⟫_ℝ +
            ‖S.deltaBatch state i ω‖ ^ 2 /
              (2 * (S.β i.1 - S.L * S.γ i.1))) ∂(S.P : Measure Ω) ≤
      etaTerm + varianceTerm) ∧
      Integrable
        (fun ω =>
          (S.γ i.1 / S.GammaNat i.1) *
            (S.η i.1 +
              ⟪S.deltaBatch state i ω, xStar - S.x state (i.1 - 1) ω⟫_ℝ +
              ‖S.deltaBatch state i ω‖ ^ 2 /
                (2 * (S.β i.1 - S.L * S.γ i.1))))
        (S.P : Measure Ω) := by
  classical
  let innerTerm : Ω → ℝ := fun ω =>
    ⟪S.deltaBatch state i ω, xStar - S.x state (i.1 - 1) ω⟫_ℝ
  let quadTerm : Ω → ℝ := fun ω => ‖S.deltaBatch state i ω‖ ^ 2
  let a : ℝ := S.γ i.1 / S.GammaNat i.1
  let gap : ℝ := S.β i.1 - S.L * S.γ i.1
  let quadScaled : Ω → ℝ := fun ω => quadTerm ω / (2 * gap)
  have hinner_int : Integrable innerTerm (S.P : Measure Ω) := by
    exact
      (SOptLib.expectationWellDefined_iff_integrable (S.P : Measure Ω) innerTerm).mp
        hBatchZero.1
  have hinner_zero : ∫ ω, innerTerm ω ∂(S.P : Measure Ω) = 0 := by
    simpa [SOptLib.expectation, innerTerm] using hBatchZero.2
  have hquad_int : Integrable quadTerm (S.P : Measure Ω) := by
    exact
      (SOptLib.expectationWellDefined_iff_integrable (S.P : Measure Ω) quadTerm).mp
        hBatchVariance.1
  have hquad_bound :
      ∫ ω, quadTerm ω ∂(S.P : Measure Ω) ≤
        S.σ ^ 2 / (S.batchSize i : ℝ) := by
    simpa [SOptLib.expectation, quadTerm] using hBatchVariance.2
  have hgap_pos' : 0 < gap := by simpa [gap] using hgap
  have hden_pos : 0 < 2 * gap := by positivity
  have hGamma_ne : S.Gamma i ≠ 0 := by
    rw [← hGammaNat]
    exact ne_of_gt hGamma_pos
  have hGammaNat_ne : S.GammaNat i.1 ≠ 0 := ne_of_gt hGamma_pos
  have hbatch_ne : (S.batchSize i : ℝ) ≠ 0 := S.batchSize_ne_zero i
  have hden_ne : 2 * gap ≠ 0 := ne_of_gt hden_pos
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    exact div_nonneg hγ_nonneg (le_of_lt hGamma_pos)
  have hquad_coeff_nonneg : 0 ≤ a * (2 * gap)⁻¹ := by
    exact mul_nonneg ha_nonneg (inv_nonneg.mpr (le_of_lt hden_pos))
  have hsum_int :
      Integrable
        (fun ω => S.η i.1 + innerTerm ω + quadTerm ω / (2 * gap))
        (S.P : Measure Ω) := by
    have hconst : Integrable (fun _ : Ω => S.η i.1) (S.P : Measure Ω) :=
      integrable_const (c := S.η i.1)
    have hquad_scaled :
        Integrable (fun ω => quadTerm ω / (2 * gap)) (S.P : Measure Ω) := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        hquad_int.const_mul ((2 * gap)⁻¹)
    exact (hconst.add hinner_int).add hquad_scaled
  have hquad_scaled_int : Integrable quadScaled (S.P : Measure Ω) := by
    simpa [quadScaled, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      hquad_int.const_mul ((2 * gap)⁻¹)
  have hquad_scaled_integral :
      ∫ ω, quadScaled ω ∂(S.P : Measure Ω) =
        (2 * gap)⁻¹ * ∫ ω, quadTerm ω ∂(S.P : Measure Ω) := by
    have hfun : quadScaled = fun ω => (2 * gap)⁻¹ * quadTerm ω := by
      funext ω
      simp [quadScaled, div_eq_mul_inv, mul_comm]
    rw [hfun]
    exact integral_const_mul ((2 * gap)⁻¹) quadTerm
  have hconst_inner_integral :
      ∫ ω, ((fun _ : Ω => S.η i.1) + innerTerm) ω ∂(S.P : Measure Ω) =
        S.η i.1 := by
    have hconst : Integrable (fun _ : Ω => S.η i.1) (S.P : Measure Ω) :=
      integrable_const (c := S.η i.1)
    change ∫ ω, (fun _ : Ω => S.η i.1) ω + innerTerm ω ∂(S.P : Measure Ω) =
      S.η i.1
    rw [integral_add hconst hinner_int]
    rw [hinner_zero]
    simp [integral_const]
  have hintegral_eval :
      ∫ ω,
          a * (S.η i.1 + innerTerm ω + quadTerm ω / (2 * gap))
          ∂(S.P : Measure Ω) =
        a * S.η i.1 + a * ((2 * gap)⁻¹ * ∫ ω, quadTerm ω ∂(S.P : Measure Ω)) := by
    rw [integral_const_mul]
    · have hconst : Integrable (fun _ : Ω => S.η i.1) (S.P : Measure Ω) :=
        integrable_const (c := S.η i.1)
      change
        a * ∫ ω, ((fun _ : Ω => S.η i.1) + innerTerm) ω + quadScaled ω
            ∂(S.P : Measure Ω) =
          a * S.η i.1 + a * ((2 * gap)⁻¹ * ∫ ω, quadTerm ω ∂(S.P : Measure Ω))
      rw [integral_add (hconst.add hinner_int) hquad_scaled_int]
      rw [hconst_inner_integral]
      rw [hquad_scaled_integral]
      simp [integral_const, mul_add, add_assoc, mul_comm, mul_left_comm, mul_assoc]
  have hquad_scaled_bound :
      a * ((2 * gap)⁻¹ * ∫ ω, quadTerm ω ∂(S.P : Measure Ω)) ≤
        a * ((2 * gap)⁻¹ * (S.σ ^ 2 / (S.batchSize i : ℝ))) := by
    have hmul := mul_le_mul_of_nonneg_left hquad_bound hquad_coeff_nonneg
    simpa [mul_assoc] using hmul
  have hraw_bound :
      ∫ ω,
          a * (S.η i.1 + innerTerm ω + quadTerm ω / (2 * gap))
          ∂(S.P : Measure Ω) ≤
        a * S.η i.1 +
          a * ((2 * gap)⁻¹ * (S.σ ^ 2 / (S.batchSize i : ℝ))) := by
    rw [hintegral_eval]
    simpa [add_comm, add_left_comm, add_assoc] using
      add_le_add_left hquad_scaled_bound (a * S.η i.1)
  have htarget_eq :
      a * S.η i.1 +
          a * ((2 * gap)⁻¹ * (S.σ ^ 2 / (S.batchSize i : ℝ))) =
        etaTerm + varianceTerm := by
    rw [hetaTerm, hvarianceTerm]
    dsimp [a, gap]
    rw [hGammaNat]
    field_simp [hGamma_ne, hbatch_ne, ne_of_gt hgap]
  have hrewrite :
      (fun ω =>
        (S.γ i.1 / S.GammaNat i.1) *
          (S.η i.1 +
            ⟪S.deltaBatch state i ω, xStar - S.x state (i.1 - 1) ω⟫_ℝ +
            ‖S.deltaBatch state i ω‖ ^ 2 /
              (2 * (S.β i.1 - S.L * S.γ i.1)))) =
        fun ω => a * (S.η i.1 + innerTerm ω + quadTerm ω / (2 * gap)) := by
    funext ω
    rfl
  rw [hrewrite]
  constructor
  · exact le_trans hraw_bound (le_of_eq htarget_eq)
  · rw [hrewrite]
    exact hsum_int.const_mul a

/-- Bridge from the explicit stochastic sample basis and generated-state
semantics to the filtration data it actually provides.

The PDF says the residual independence sentence after Eq. (7.2.50) follows
"by our assumptions on the SFO".  That residual statement is represented by
`SFO_Independence_Theorem7_11` at the theorem boundary below.  The raw
mini-batch sample basis by itself proves only sample measurability, sample
freshness for the flattened stream.  Adaptedness of a relational CndG state is
kept as an explicit regularity input because the relation alone does not prevent
future-dependent choices among valid CndG outputs.
-/
theorem theorem711_sampleBasis_generated_filtration_data (S : Setup Ω Ξ E)
    (state : ℕ → Ω → {x : E // x ∈ S.X} × {x : E // x ∈ S.X})
    (_hstate : S.IsOuterState state)
    (hAdapted : S.OuterStateAdapted state)
    (hBasis : S.SFOSampleBasis_Algorithm7_8) :
    S.OuterStateAdapted state ∧
      (∀ n, Measurable (S.flatSample n)) ∧
        ProbabilityTheory.iIndepFun S.flatSample (S.P : Measure Ω) := by
  refine ⟨S.outerState_adapted state hAdapted, S.flatSample_measurable hBasis, ?_⟩
  simpa [flatSample] using hBasis.2

/-- Optimal solution predicate for Eq. (7.1.1). -/
def IsOptimalSolution (S : Setup Ω Ξ E) (xStar : E) : Prop :=
  xStar ∈ S.X ∧ ∀ x ∈ S.X, S.f xStar ≤ S.f x

/-- Lean well-definedness obligation for the expectation in Theorem 7.11.

The PDF states the expected gap but does not list this as a primitive theorem
hypothesis; later proof phases must derive it from the generated stochastic
process and oracle assumptions instead of adding it to the theorem head.
-/
def expectedGapWellDefined (S : Setup Ω Ξ E)
    (state : ℕ → Ω → {x : E // x ∈ S.X} × {x : E // x ∈ S.X})
    (k : ℕ) (xStar : E) : Prop :=
  SOptLib.expectationWellDefined S.P (fun ω => S.f (S.y state k ω) - S.f xStar)

/-- Bochner-integral realization of the printed expected suboptimality
`E[f(y_k)-f(x*)]`.

The separate theorem `theorem711_expectedGap_wellDefined` records the Lean
regularity obligation for this expectation; the public Theorem 7.11 statements
below use the printed scalar inequality directly.
-/
def expectedGapRaw (S : Setup Ω Ξ E)
    (state : ℕ → Ω → {x : E // x ∈ S.X} × {x : E // x ∈ S.X})
    (k : ℕ) (xStar : E) : ℝ :=
  SOptLib.expectation S.P (fun ω => S.f (S.y state k ω) - S.f xStar)

/-- Lean well-definedness obligation for a relational SCGS state. -/
def expectedGapSeqWellDefined (S : Setup Ω Ξ E)
    (state : ℕ → Ω → {x : E // x ∈ S.X} × {x : E // x ∈ S.X})
    (k : ℕ) (xStar : E) : Prop :=
  S.expectedGapWellDefined state k xStar

/-- Internal helper pairing expectation well-definedness with a bound.  The
source-facing Theorem 7.11 declarations below use the printed inequality
directly; this helper remains available for proof phases that need regularity. -/
def expectedGapSeqBound (S : Setup Ω Ξ E)
    (state : ℕ → Ω → {x : E // x ∈ S.X} × {x : E // x ∈ S.X})
    (k : ℕ) (xStar : E) (bound : ℝ) : Prop :=
  S.expectedGapSeqWellDefined state k xStar ∧
    S.expectedGapRaw state k xStar ≤ bound

/-- The carrier objective is continuous on the feasible set.

This is a Lean regularity bridge derived from the source derivative semantics
`hfPrime_derivative`; it is not a new paper assumption.
-/
theorem objective_continuousOn (S : Setup Ω Ξ E) :
    ContinuousOn S.f S.X := by
  intro x hx
  exact (S.differentiableWithinAt_obligation x hx).continuousWithinAt

/-- Compactness of `X` gives a uniform finite bound on the source objective. -/
theorem objective_norm_bound_on_X (S : Setup Ω Ξ E) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E, x ∈ S.X → ‖S.f x‖ ≤ C := by
  exact exists_nonneg_norm_bound_of_isCompact_of_continuousOn S.f S.hX_compact
    S.objective_continuousOn

/-- Measurability of the objective gap along an adapted relational state. -/
theorem objectiveGap_measurable_of_outerStateAdapted (S : Setup Ω Ξ E)
    (state : ℕ → Ω → {x : E // x ∈ S.X} × {x : E // x ∈ S.X})
    (hAdapted : S.OuterStateAdapted state) (k : ℕ) (xStar : E) :
    Measurable (fun ω => S.f (S.y state k ω) - S.f xStar) := by
  have hyMeas : Measurable (fun ω => S.y state k ω) :=
    S.outerStateAdapted_y_measurable state hAdapted k
  have hyMem : ∀ ω, S.y state k ω ∈ S.X := fun ω => S.y_mem state k ω
  have hfCarrier : Continuous S.fX :=
    continuous_subtype_of_continuousOn_ambient S.fX S.f S.objective_continuousOn
      (by
        intro x
        exact S.f_of_mem x.1 x.2)
  have hySubtype :
      Measurable (fun ω => (⟨S.y state k ω, hyMem ω⟩ : {x : E // x ∈ S.X})) :=
    Measurable.subtype_mk hyMeas
  have hyObjCarrier :
      Measurable (fun ω => S.fX (⟨S.y state k ω, hyMem ω⟩ : {x : E // x ∈ S.X})) :=
    hfCarrier.measurable.comp hySubtype
  have hyObj : Measurable (fun ω => S.f (S.y state k ω)) := by
    convert hyObjCarrier using 1
    ext ω
    exact S.f_of_mem (S.y state k ω) (hyMem ω)
  exact hyObj.sub measurable_const

/-- Integrability of the objective gap along an adapted relational state.

The proof uses the compact feasible range and the continuous objective bridge,
so this is the compiled objective-regularity route needed by Theorem 7.11(a/b).
-/
theorem expectedGap_integrable_of_outerStateAdapted (S : Setup Ω Ξ E)
    (state : ℕ → Ω → {x : E // x ∈ S.X} × {x : E // x ∈ S.X})
    (hAdapted : S.OuterStateAdapted state) (k : ℕ) (xStar : E) :
    Integrable (fun ω => S.f (S.y state k ω) - S.f xStar) (S.P : Measure Ω) := by
  have hgapMeas :=
    S.objectiveGap_measurable_of_outerStateAdapted state hAdapted k xStar
  obtain ⟨C, _hC_nonneg, hC⟩ := S.objective_norm_bound_on_X
  refine integrable_of_measurable_bounded_real hgapMeas (C := C + ‖S.f xStar‖) ?_
  intro ω
  calc
    ‖S.f (S.y state k ω) - S.f xStar‖
        ≤ ‖S.f (S.y state k ω)‖ + ‖S.f xStar‖ := norm_sub_le _ _
    _ ≤ C + ‖S.f xStar‖ :=
        add_le_add_left (hC (S.y state k ω) (S.y_mem state k ω)) _

/-- Expected-gap well-definedness derived from adaptedness and compact feasible
objective regularity. -/
theorem expectedGapSeqWellDefined_of_outerStateAdapted (S : Setup Ω Ξ E)
    (state : ℕ → Ω → {x : E // x ∈ S.X} × {x : E // x ∈ S.X})
    (hAdapted : S.OuterStateAdapted state) (k : ℕ) (xStar : E) :
    S.expectedGapSeqWellDefined state k xStar := by
  exact (SOptLib.expectationWellDefined_iff_integrable (S.P : Measure Ω)
    (fun ω => S.f (S.y state k ω) - S.f xStar)).mpr
      (S.expectedGap_integrable_of_outerStateAdapted state hAdapted k xStar)

/-- Source expectation inequality for Theorem 7.11.

The theorem prints `E[f(y_k)-f(x*)] ≤ ...`; this source-facing relation treats
that as a well-defined mathematical expectation inequality rather than a raw
total Bochner-integral inequality.
-/
def expectedGapSourceLe (S : Setup Ω Ξ E)
    (state : ℕ → Ω → {x : E // x ∈ S.X} × {x : E // x ∈ S.X})
    (k : ℕ) (xStar : E) (bound : ℝ) : Prop :=
  S.sourceExpectationLe (fun ω => S.f (S.y state k ω) - S.f xStar) bound

/-- Denominator of the stochastic-variance term in Theorem 7.11(a)/(b),
`2 Γ_i B_i (β_i - L γ_i)`.

The source statement displays this as a denominator while Eq. (7.2.10) only
states `L γ_i ≤ β_i`.  It is therefore named separately so the corrected
source-boundary contract can expose the partial-domain requirement instead of
using Lean's total division fallback.
-/
def theorem711VarianceDenominator (S : Setup Ω Ξ E) (i : PositiveTime) : ℝ :=
  2 * S.Gamma i * (S.batchSize i : ℝ) * (S.β i.1 - S.L * S.γ i.1)

/-- Source quotient for the Theorem 7.11(a)/(b) stochastic-variance term. -/
def theorem711VarianceQuotient_sourceBoundary (S : Setup Ω Ξ E)
    (i : PositiveTime) (q : ℝ) : Prop :=
  S.sourceQuotient (S.γ i.1 * S.σ ^ 2) (S.theorem711VarianceDenominator i) q

/-- Domain/value bridge for the variance quotient in Theorem 7.11(a)/(b). -/
theorem theorem711VarianceQuotient_sourceBoundary_spec (S : Setup Ω Ξ E)
    (i : PositiveTime) (q : ℝ) :
    S.theorem711VarianceQuotient_sourceBoundary i q ↔
      S.theorem711VarianceDenominator i ≠ 0 ∧
        q * S.theorem711VarianceDenominator i = S.γ i.1 * S.σ ^ 2 := by
  rfl

/-- Domain predicate for all displayed stochastic-variance quotients up to `k`
in Theorem 7.11(a)/(b). -/
def theorem711VarianceDenominatorDomain (S : Setup Ω Ξ E) (k : PositiveTime) :
    Prop :=
  ∀ i : {i : ℕ // i ∈ Finset.Icc 1 k.1},
    let ip : PositiveTime := ⟨i.1, (Finset.mem_Icc.mp i.2).1⟩
    S.theorem711VarianceDenominator ip ≠ 0

/-- The corrected variance-domain predicate and Eq. (7.2.10)'s non-strict lower
bound imply the strict denominator gap needed in the proof of Eq. (7.2.49). -/
theorem theorem711VarianceDenominatorDomain_gap_pos (S : Setup Ω Ξ E)
    (k : PositiveTime) (hDomain : S.theorem711VarianceDenominatorDomain k)
    (i : {i : ℕ // i ∈ Finset.Icc 1 k.1}) :
    let ip : PositiveTime := ⟨i.1, (Finset.mem_Icc.mp i.2).1⟩
    0 < S.β ip.1 - S.L * S.γ ip.1 := by
  classical
  let ip : PositiveTime := ⟨i.1, (Finset.mem_Icc.mp i.2).1⟩
  have hden : S.theorem711VarianceDenominator ip ≠ 0 := hDomain i
  have hgap_ne : S.β ip.1 - S.L * S.γ ip.1 ≠ 0 := by
    intro hzero
    apply hden
    simp [theorem711VarianceDenominator, hzero]
  have hgap_nonneg : 0 ≤ S.β ip.1 - S.L * S.γ ip.1 := by
    exact sub_nonneg.mpr (S.hparam_lower ip.1 ip.2)
  exact lt_of_le_of_ne' hgap_nonneg hgap_ne

/-- The variance-denominator domain in Theorem 7.11 also supplies the
nonzero `Γ_i` side condition needed by the Gamma-weighted telescope.

This is a denominator projection from the source-boundary variance quotient,
not a new parameter assumption; it aligns the displayed denominator
`2 Γ_i B_i (β_i-Lγ_i)` with the telescope API's `Γ_i ≠ 0` requirement. -/
private theorem theorem711VarianceDenominatorDomain_Gamma_ne (S : Setup Ω Ξ E)
    (k : PositiveTime) (hDomain : S.theorem711VarianceDenominatorDomain k)
    (i : {i : ℕ // i ∈ Finset.Icc 1 k.1}) :
    let ip : PositiveTime := ⟨i.1, (Finset.mem_Icc.mp i.2).1⟩
    S.Gamma ip ≠ 0 := by
  classical
  let ip : PositiveTime := ⟨i.1, (Finset.mem_Icc.mp i.2).1⟩
  have hden : S.theorem711VarianceDenominator ip ≠ 0 := hDomain i
  dsimp
  intro hGamma
  have hGamma_ip : S.Gamma ip = 0 := by
    simpa [ip] using hGamma
  apply hden
  simp [theorem711VarianceDenominator, hGamma_ip]

/-- Gamma-unrolled first inequality in Lan Eq. (7.2.50), before the
distance-budget and expectation steps.

This is the paper's step from Eq. (7.2.49) to the weighted finite-window
recursion.  It directly uses the SOptLib candidate
`finite_window_weighted_recurrence_telescope_with_tail_sums`; the pre-searched
state/oracle candidates such as `BlockIterateState` and the update-realization
lemmas were checked and rejected because they concern algorithm-state
realization rather than this scalar Gamma recurrence.
-/
private theorem weighted_recursion_part_a_7_2_50_first (S : Setup Ω Ξ E)
    (state : ℕ → Ω → S.OuterStatePoint) (k : PositiveTime) (xStar : E)
    (hstep_7_2_49 :
      ∀ (iwin : {i : ℕ // i ∈ Finset.Icc 1 k.1}) (ω : Ω),
        let ip : PositiveTime := ⟨iwin.1, (Finset.mem_Icc.mp iwin.2).1⟩
        S.f (S.y state ip.1 ω) ≤
          (1 - S.γ ip.1) * S.f (S.y state (ip.1 - 1) ω) +
            S.γ ip.1 * S.f xStar +
              S.β ip.1 * S.γ ip.1 / 2 *
                (‖S.x state (ip.1 - 1) ω - xStar‖ ^ 2 -
                  ‖S.x state ip.1 ω - xStar‖ ^ 2) +
              S.η ip.1 * S.γ ip.1 +
              S.γ ip.1 *
                ⟪S.deltaBatch state ip ω, xStar - S.x state (ip.1 - 1) ω⟫_ℝ +
              S.γ ip.1 * ‖S.deltaBatch state ip ω‖ ^ 2 /
                (2 * (S.β ip.1 - S.L * S.γ ip.1)))
    (hGamma_ne_window :
      ∀ iwin : {i : ℕ // i ∈ Finset.Icc 1 k.1},
        let ip : PositiveTime := ⟨iwin.1, (Finset.mem_Icc.mp iwin.2).1⟩
        S.Gamma ip ≠ 0) :
    ∀ ω : Ω,
      S.f (S.y state k.1 ω) - S.f xStar ≤
        S.GammaNat k.1 * (1 - S.γ 1) *
            (S.f (S.y state 0 ω) - S.f xStar) +
          S.GammaNat k.1 *
            Finset.sum (Finset.Icc 1 k.1) (fun t =>
              S.γ t / S.GammaNat t *
                (S.β t / 2 *
                  (‖S.x state (t - 1) ω - xStar‖ ^ 2 -
                    ‖S.x state t ω - xStar‖ ^ 2))) +
          S.GammaNat k.1 *
            Finset.sum (Finset.Icc 1 k.1) (fun t =>
              if ht : 1 ≤ t then
                S.γ t / S.GammaNat t *
                  (S.η t +
                    ⟪S.deltaBatch state ⟨t, ht⟩ ω,
                      xStar - S.x state (t - 1) ω⟫_ℝ +
                    ‖S.deltaBatch state ⟨t, ht⟩ ω‖ ^ 2 /
                      (2 * (S.β t - S.L * S.γ t)))
              else 0) := by
  classical
  intro ω
  let alpha : ℕ → ℝ := fun t => if t ≤ k.1 then S.γ t else 0
  let gamma : ℕ → ℝ := fun _t => (1 : ℝ)
  let GammaExt : ℕ → ℝ := fun t => if t ≤ k.1 then S.GammaNat t else S.GammaNat k.1
  let A : ℕ → ℝ := fun t => S.f (S.y state t ω) - S.f xStar
  let Lterm : ℕ → ℝ := fun t =>
    S.β t / 2 *
      (‖S.x state (t - 1) ω - xStar‖ ^ 2 -
        ‖S.x state t ω - xStar‖ ^ 2)
  let Bterm : ℕ → ℝ := fun t =>
    if ht : 1 ≤ t then
      S.η t +
        ⟪S.deltaBatch state ⟨t, ht⟩ ω, xStar - S.x state (t - 1) ω⟫_ℝ +
        ‖S.deltaBatch state ⟨t, ht⟩ ω‖ ^ 2 /
          (2 * (S.β t - S.L * S.γ t))
    else 0
  let Dterm : ℕ → ℝ := fun t =>
    if t ≤ k.1 then 0
    else A t -
      ((1 - alpha t) * A (t - 1) + alpha t * Lterm t +
        alpha t / gamma t * Bterm t)
  have hgamma_ne : ∀ t, 1 ≤ t → gamma t ≠ 0 := by
    intro t ht
    simp [gamma]
  have hGamma_ne_ext : ∀ t, 1 ≤ t → GammaExt t ≠ 0 := by
    intro t ht
    by_cases htk : t ≤ k.1
    · have hmem : t ∈ Finset.Icc 1 k.1 := by
        exact Finset.mem_Icc.mpr ⟨ht, htk⟩
      have hne := hGamma_ne_window ⟨t, hmem⟩
      have hpos : S.GammaNat t = S.Gamma ⟨t, ht⟩ := S.GammaNat_of_pos t ht
      simpa [GammaExt, htk, hpos] using hne
    · have hmemk : k.1 ∈ Finset.Icc 1 k.1 := by
        exact Finset.mem_Icc.mpr ⟨k.2, le_rfl⟩
      have hne := hGamma_ne_window ⟨k.1, hmemk⟩
      have hposk : S.GammaNat k.1 = S.Gamma k := S.GammaNat_of_pos k.1 k.2
      simpa [GammaExt, htk, hposk] using hne
  have hGamma_one_ext : GammaExt 1 = 1 := by
    have h1k : 1 ≤ k.1 := k.2
    simp [GammaExt, h1k, S.GammaNat_of_pos, S.Gamma_one]
  have halpha_one_ext : alpha 1 = 1 := by
    have h1k : 1 ≤ k.1 := k.2
    simp [alpha, h1k, S.hγ_one]
  have halpha_le_one_ext : ∀ t, 1 ≤ t → alpha t ≤ 1 := by
    intro t ht
    by_cases htk : t ≤ k.1
    · have hγmem := S.hγ_mem t ht
      have hle : S.γ t ≤ 1 := (Set.mem_Icc.mp hγmem).2
      simpa [alpha, htk] using hle
    · simp [alpha, htk]
  have hGamma_succ_ext :
      ∀ t, 1 ≤ t → GammaExt (t + 1) = (1 - alpha (t + 1)) * GammaExt t := by
    intro t ht
    by_cases hsucc : t + 1 ≤ k.1
    · have htk : t ≤ k.1 := le_trans (Nat.le_succ t) hsucc
      have htpos_succ : 1 ≤ t + 1 := Nat.succ_le_succ (Nat.zero_le t)
      have hpos_t : S.GammaNat t = S.Gamma ⟨t, ht⟩ := S.GammaNat_of_pos t ht
      have hpos_succ :
          S.GammaNat (t + 1) =
            S.Gamma ⟨t + 1, Nat.succ_le_succ (Nat.zero_le t)⟩ :=
        S.GammaNat_of_pos (t + 1) htpos_succ
      simp [GammaExt, alpha, hsucc, htk, hpos_t, hpos_succ, S.Gamma_succ t ht]
    · have hnot_succ : ¬ t + 1 ≤ k.1 := hsucc
      have halpha_zero : alpha (t + 1) = 0 := by
        simp [alpha, hnot_succ]
      by_cases htk : t ≤ k.1
      · have hkt : k.1 ≤ t := Nat.le_of_lt_succ (Nat.lt_of_not_ge hnot_succ)
        have htk_eq : t = k.1 := le_antisymm htk hkt
        simp [GammaExt, alpha, hnot_succ, htk, halpha_zero, htk_eq]
      · simp [GammaExt, alpha, hnot_succ, htk, halpha_zero]
  have hstep_ext : ∀ t, 1 ≤ t →
      A t ≤ (1 - alpha t) * A (t - 1) + alpha t * Lterm t +
        alpha t / gamma t * Bterm t + Dterm t := by
    intro t ht
    by_cases htk : t ≤ k.1
    · have hmem : t ∈ Finset.Icc 1 k.1 := Finset.mem_Icc.mpr ⟨ht, htk⟩
      let ip : PositiveTime := ⟨t, ht⟩
      have hraw := hstep_7_2_49 ⟨t, hmem⟩ ω
      have hstep' :
          A t ≤ (1 - S.γ t) * A (t - 1) +
            S.γ t * Lterm t + S.γ t * Bterm t := by
        dsimp [A, Lterm, Bterm, ip] at hraw ⊢
        simp [ht] at hraw ⊢
        have hcalc :
            S.f (S.y state t ω) - S.f xStar ≤
              (1 - S.γ t) * (S.f (S.y state (t - 1) ω) - S.f xStar) +
                S.γ t *
                  (S.β t / 2 *
                    (‖S.x state (t - 1) ω - xStar‖ ^ 2 -
                      ‖S.x state t ω - xStar‖ ^ 2)) +
                S.γ t *
                  (S.η t +
                    ⟪S.deltaBatch state ⟨t, ht⟩ ω,
                      xStar - S.x state (t - 1) ω⟫_ℝ +
                    ‖S.deltaBatch state ⟨t, ht⟩ ω‖ ^ 2 /
                      (2 * (S.β t - S.L * S.γ t))) := by
          calc
            S.f (S.y state t ω) - S.f xStar
                ≤ ((1 - S.γ t) * S.f (S.y state (t - 1) ω) +
                      S.γ t * S.f xStar +
                      S.β t * S.γ t / 2 *
                        (‖S.x state (t - 1) ω - xStar‖ ^ 2 -
                          ‖S.x state t ω - xStar‖ ^ 2) +
                      S.η t * S.γ t +
                      S.γ t *
                        ⟪S.deltaBatch state ⟨t, ht⟩ ω,
                          xStar - S.x state (t - 1) ω⟫_ℝ +
                      S.γ t * ‖S.deltaBatch state ⟨t, ht⟩ ω‖ ^ 2 /
                        (2 * (S.β t - S.L * S.γ t))) - S.f xStar := by
                    exact sub_le_sub_right hraw (S.f xStar)
            _ = (1 - S.γ t) * (S.f (S.y state (t - 1) ω) - S.f xStar) +
                  S.γ t *
                    (S.β t / 2 *
                      (‖S.x state (t - 1) ω - xStar‖ ^ 2 -
                        ‖S.x state t ω - xStar‖ ^ 2)) +
                  S.γ t *
                    (S.η t +
                      ⟪S.deltaBatch state ⟨t, ht⟩ ω,
                        xStar - S.x state (t - 1) ω⟫_ℝ +
                      ‖S.deltaBatch state ⟨t, ht⟩ ω‖ ^ 2 /
                        (2 * (S.β t - S.L * S.γ t))) := by
                    ring
        nlinarith [hcalc]
      have hD : Dterm t = 0 := by simp [Dterm, htk]
      have hα : alpha t = S.γ t := by simp [alpha, htk]
      have hγ : gamma t = 1 := by simp [gamma]
      simpa [hD, hα, hγ] using hstep'
    · have hD : Dterm t =
          A t -
            ((1 - alpha t) * A (t - 1) + alpha t * Lterm t +
              alpha t / gamma t * Bterm t) := by
        simp [Dterm, htk]
      rw [hD]
      ring_nf
      exact le_rfl
  have htel := finite_window_weighted_recurrence_telescope_with_tail_sums
    alpha gamma GammaExt A Lterm Bterm Dterm k.1 k.2 hgamma_ne hGamma_ne_ext
    hGamma_one_ext halpha_one_ext halpha_le_one_ext hGamma_succ_ext hstep_ext
  have hDsum :
      Finset.sum (Finset.Icc 1 k.1) (fun t => Dterm t / GammaExt t) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro t ht
    have htk : t ≤ k.1 := (Finset.mem_Icc.mp ht).2
    simp [Dterm, htk]
  have hLsum :
      Finset.sum (Finset.Icc 1 k.1) (fun t => alpha t / GammaExt t * Lterm t) =
        Finset.sum (Finset.Icc 1 k.1) (fun t =>
          S.γ t / S.GammaNat t *
            (S.β t / 2 *
              (‖S.x state (t - 1) ω - xStar‖ ^ 2 -
                ‖S.x state t ω - xStar‖ ^ 2))) := by
    refine Finset.sum_congr rfl ?_
    intro t ht
    have htk : t ≤ k.1 := (Finset.mem_Icc.mp ht).2
    simp [alpha, GammaExt, Lterm, htk]
  have hBsum :
      Finset.sum (Finset.Icc 1 k.1)
          (fun t => alpha t / (gamma t * GammaExt t) * Bterm t) =
        Finset.sum (Finset.Icc 1 k.1) (fun t =>
          if ht : 1 ≤ t then
            S.γ t / S.GammaNat t *
              (S.η t +
                ⟪S.deltaBatch state ⟨t, ht⟩ ω,
                  xStar - S.x state (t - 1) ω⟫_ℝ +
                ‖S.deltaBatch state ⟨t, ht⟩ ω‖ ^ 2 /
                  (2 * (S.β t - S.L * S.γ t)))
          else 0) := by
    refine Finset.sum_congr rfl ?_
    intro t htmem
    have htk : t ≤ k.1 := (Finset.mem_Icc.mp htmem).2
    simp [alpha, gamma, GammaExt, Bterm, htk]
  have htop : GammaExt k.1 = S.GammaNat k.1 := by
    simp [GammaExt, le_rfl]
  have hmain :
      A k.1 ≤
        GammaExt k.1 * (1 - alpha 1) * A 0 +
          GammaExt k.1 *
            Finset.sum (Finset.Icc 1 k.1) (fun t => alpha t / GammaExt t * Lterm t) +
          GammaExt k.1 *
            Finset.sum (Finset.Icc 1 k.1)
              (fun t => alpha t / (gamma t * GammaExt t) * Bterm t) := by
    have htel' : A k.1 - GammaExt k.1 *
        Finset.sum (Finset.Icc 1 k.1) (fun t => alpha t / GammaExt t * Lterm t) ≤
      GammaExt k.1 * (1 - alpha 1) * A 0 +
        GammaExt k.1 *
          Finset.sum (Finset.Icc 1 k.1)
            (fun t => alpha t / (gamma t * GammaExt t) * Bterm t) := by
      simpa [hDsum] using htel
    linarith
  have halpha_one_source : alpha 1 = S.γ 1 := by
    have h1k : 1 ≤ k.1 := k.2
    simp [alpha, h1k]
  simpa [A, htop, halpha_one_source, hLsum, hBsum] using hmain

/-- Convert the source quotient monotonicity in Eq. (7.2.11) to the total
ratio inequality needed by the finite-window distance telescope.

This is a route-local bridge for Lan Eq. (7.2.20).  The relevant candidate is
`sum_Icc_two_coeff_telescope_le`, which expects ordinary scalar coefficients;
the pre-searched update/state candidates were rejected because they do not
convert the paper's `sourceQuotient` witnesses into usable real ratios.
-/
private theorem parameterRatio_monoA_total_window (S : Setup Ω Ξ E)
    (k : PositiveTime) (hMono : S.ParameterMonotonicityA_7_2_11)
    (hGamma_ne_window :
      ∀ iwin : {i : ℕ // i ∈ Finset.Icc 1 k.1},
        let ip : PositiveTime := ⟨iwin.1, (Finset.mem_Icc.mp iwin.2).1⟩
        S.Gamma ip ≠ 0) :
    ∀ n, 1 ≤ n → n < k.1 →
      S.β n * S.γ n / S.GammaNat n ≤
        S.β (n + 1) * S.γ (n + 1) / S.GammaNat (n + 1) := by
  classical
  intro n hn hnlt
  have hn_succ_two : 2 ≤ n + 1 := Nat.succ_le_succ hn
  rcases hMono ⟨n + 1, hn_succ_two⟩ with
    ⟨qPrev, qCur, hqPrev, hqCur, hle⟩
  have hn_succ_pos : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
  have hprev :
      S.parameterRatioQuotient ⟨n, hn⟩ qPrev := by
    simpa [Nat.succ_sub_one] using hqPrev
  have hcur :
      S.parameterRatioQuotient ⟨n + 1, hn_succ_pos⟩ qCur := by
    simpa using hqCur
  have hprev_spec :=
    (S.parameterRatioQuotient_spec ⟨n, hn⟩ qPrev).mp hprev
  have hcur_spec :=
    (S.parameterRatioQuotient_spec ⟨n + 1, hn_succ_pos⟩ qCur).mp hcur
  have hprev_nat : S.GammaNat n = S.Gamma ⟨n, hn⟩ :=
    S.GammaNat_of_pos n hn
  have hcur_nat : S.GammaNat (n + 1) = S.Gamma ⟨n + 1, hn_succ_pos⟩ :=
    S.GammaNat_of_pos (n + 1) hn_succ_pos
  have hqPrev_eq : qPrev = S.β n * S.γ n / S.GammaNat n := by
    rw [hprev_nat]
    field_simp [hprev_spec.1]
    exact hprev_spec.2
  have hqCur_eq : qCur = S.β (n + 1) * S.γ (n + 1) / S.GammaNat (n + 1) := by
    rw [hcur_nat]
    field_simp [hcur_spec.1]
    exact hcur_spec.2
  simpa [hqPrev_eq, hqCur_eq] using hle

/-- Convert the source quotient monotonicity in Eq. (7.2.13) to the total
ratio inequality needed by the finite-window distance telescope.

This is the part-(b) analogue of `parameterRatio_monoA_total_window`, aligning
with Lan Eq. (7.2.13).  Considered the pre-searched update/state candidates and
`SOptLib.sum_Icc_two_coeff_telescope_le`; the latter consumes ordinary scalar
coefficients but does not convert the paper's `sourceQuotient` witnesses, while
the update/state candidates concern algorithm realization rather than quotient
values. -/
private theorem parameterRatio_monoB_total_window (S : Setup Ω Ξ E)
    (k : PositiveTime) (hMono : S.ParameterMonotonicityB_7_2_13)
    (hGamma_ne_window :
      ∀ iwin : {i : ℕ // i ∈ Finset.Icc 1 k.1},
        let ip : PositiveTime := ⟨iwin.1, (Finset.mem_Icc.mp iwin.2).1⟩
        S.Gamma ip ≠ 0) :
    ∀ n, 1 ≤ n → n < k.1 →
      S.β (n + 1) * S.γ (n + 1) / S.GammaNat (n + 1) ≤
        S.β n * S.γ n / S.GammaNat n := by
  classical
  intro n hn hnlt
  have hn_succ_two : 2 ≤ n + 1 := Nat.succ_le_succ hn
  rcases hMono ⟨n + 1, hn_succ_two⟩ with
    ⟨qPrev, qCur, hqPrev, hqCur, hle⟩
  have hn_succ_pos : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
  have hprev :
      S.parameterRatioQuotient ⟨n, hn⟩ qPrev := by
    simpa [Nat.succ_sub_one] using hqPrev
  have hcur :
      S.parameterRatioQuotient ⟨n + 1, hn_succ_pos⟩ qCur := by
    simpa using hqCur
  have hprev_spec :=
    (S.parameterRatioQuotient_spec ⟨n, hn⟩ qPrev).mp hprev
  have hcur_spec :=
    (S.parameterRatioQuotient_spec ⟨n + 1, hn_succ_pos⟩ qCur).mp hcur
  have hprev_nat : S.GammaNat n = S.Gamma ⟨n, hn⟩ :=
    S.GammaNat_of_pos n hn
  have hcur_nat : S.GammaNat (n + 1) = S.Gamma ⟨n + 1, hn_succ_pos⟩ :=
    S.GammaNat_of_pos (n + 1) hn_succ_pos
  have hqPrev_eq : qPrev = S.β n * S.γ n / S.GammaNat n := by
    rw [hprev_nat]
    field_simp [hprev_spec.1]
    exact hprev_spec.2
  have hqCur_eq : qCur = S.β (n + 1) * S.γ (n + 1) / S.GammaNat (n + 1) := by
    rw [hcur_nat]
    field_simp [hcur_spec.1]
    exact hcur_spec.2
  simpa [hqPrev_eq, hqCur_eq] using hle

/-- Finite-window positivity of the Gamma weights used in Theorem 7.11(a).

This aligns with `SOptLib.acceleratedGamma_pos_of_mem_Icc_and_ne_zero`; that
candidate requires a global nonzero Gamma hypothesis, while Theorem 7.11's
source-boundary denominator domain only gives nonzero Gamma on the displayed
finite window. -/
private theorem gammaNat_pos_on_theorem711_window (S : Setup Ω Ξ E)
    (k : PositiveTime)
    (hGamma_ne_window :
      ∀ iwin : {i : ℕ // i ∈ Finset.Icc 1 k.1},
        let ip : PositiveTime := ⟨iwin.1, (Finset.mem_Icc.mp iwin.2).1⟩
        S.Gamma ip ≠ 0) :
    ∀ n, 1 ≤ n → n ≤ k.1 → 0 < S.GammaNat n := by
  classical
  have hGamma_nonneg_all : ∀ n, 1 ≤ n → 0 ≤ S.GammaNat n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
        simp [S.GammaNat_of_pos, S.Gamma_one]
    | succ m hm ih =>
        have hm_succ_pos : 1 ≤ m + 1 := Nat.succ_le_succ (Nat.zero_le m)
        have hγmem := S.hγ_mem (m + 1) hm_succ_pos
        have hfactor : 0 ≤ 1 - S.γ (m + 1) := by
          exact sub_nonneg.mpr (Set.mem_Icc.mp hγmem).2
        rw [S.GammaNat_of_pos (m + 1) hm_succ_pos, S.Gamma_succ m hm,
          ← S.GammaNat_of_pos m hm]
        exact mul_nonneg hfactor ih
  intro n hn hnk
  have hmem : n ∈ Finset.Icc 1 k.1 := Finset.mem_Icc.mpr ⟨hn, hnk⟩
  have hne_gamma : S.Gamma ⟨n, hn⟩ ≠ 0 := by
    simpa using hGamma_ne_window ⟨n, hmem⟩
  have hne_nat : S.GammaNat n ≠ 0 := by
    simpa [S.GammaNat_of_pos n hn] using hne_gamma
  exact lt_of_le_of_ne (hGamma_nonneg_all n hn) hne_nat.symm

/-- Increasing-coefficient scalar distance telescope with a retained terminal
tail, matching the arithmetic core of Lan Eq. (7.2.20).

Considered `SOptLib.sum_Icc_two_coeff_telescope_le` and
`SOptLib.sum_weighted_sub_mul_le_first_sub_tail`; both package decreasing or
bridged outgoing coefficients, while Eq. (7.2.20) needs nondecreasing
coefficients and a diameter cap on every potential value. -/
private theorem sum_Icc_increasing_coeff_distance_drop_le_terminal_with_tail
    (a V : ℕ → ℝ) (D : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (ha_mono : ∀ n, 1 ≤ n → n < k → a n ≤ a (n + 1))
    (ha_nonneg : ∀ n, 1 ≤ n → n ≤ k → 0 ≤ a n)
    (hV_nonneg : ∀ n, n ≤ k → 0 ≤ V n)
    (hV_le : ∀ n, n ≤ k → V n ≤ D) :
    Finset.sum (Finset.Icc 1 k) (fun t => a t * (V (t - 1) - V t)) ≤
      a k * D - a k * V k := by
  classical
  have hstrong : ∀ m, (hm : 1 ≤ m) → m ≤ k →
      Finset.sum (Finset.Icc 1 m) (fun t => a t * (V (t - 1) - V t)) ≤
        a m * D - a m * V m := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base =>
        intro hbase_le
        have ha1 : 0 ≤ a 1 := ha_nonneg 1 le_rfl hbase_le
        have hV0 : V 0 ≤ D := hV_le 0 (Nat.zero_le k)
        have hmul : a 1 * V 0 ≤ a 1 * D :=
          mul_le_mul_of_nonneg_left hV0 ha1
        calc
          Finset.sum (Finset.Icc 1 1) (fun t => a t * (V (t - 1) - V t)) =
              a 1 * (V (1 - 1) - V 1) := by simp
          _ = a 1 * V 0 - a 1 * V 1 := by ring
          _ ≤ a 1 * D - a 1 * V 1 := sub_le_sub_right hmul (a 1 * V 1)
    | succ n hn ih =>
        intro hsucc_le
        have hn_succ_pos : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
        rw [Finset.sum_Icc_succ_top hn_succ_pos, Nat.succ_sub_one]
        have hn_le_k : n ≤ k := Nat.le_trans (Nat.le_succ n) hsucc_le
        have hn_lt_k : n < k := Nat.lt_of_succ_le hsucc_le
        have hprev := ih hn_le_k
        have hcoef_nonneg : 0 ≤ a (n + 1) - a n := by
          exact sub_nonneg.mpr (ha_mono n hn hn_lt_k)
        have hVn_le : V n ≤ D := hV_le n hn_le_k
        have hmiddle :
            (a (n + 1) - a n) * V n ≤ (a (n + 1) - a n) * D :=
          mul_le_mul_of_nonneg_left hVn_le hcoef_nonneg
        nlinarith
  exact hstrong k hk le_rfl

/-- Increasing-coefficient scalar distance telescope without the terminal tail,
the inequality form used after dropping the nonnegative final term in Lan
Eq. (7.2.20). -/
private theorem sum_Icc_increasing_coeff_distance_drop_le_terminal
    (a V : ℕ → ℝ) (D : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (ha_mono : ∀ n, 1 ≤ n → n < k → a n ≤ a (n + 1))
    (ha_nonneg : ∀ n, 1 ≤ n → n ≤ k → 0 ≤ a n)
    (hV_nonneg : ∀ n, n ≤ k → 0 ≤ V n)
    (hV_le : ∀ n, n ≤ k → V n ≤ D) :
    Finset.sum (Finset.Icc 1 k) (fun t => a t * (V (t - 1) - V t)) ≤
      a k * D := by
  have htail :=
    sum_Icc_increasing_coeff_distance_drop_le_terminal_with_tail
      a V D k hk ha_mono ha_nonneg hV_nonneg hV_le
  have htail_nonneg : 0 ≤ a k * V k :=
    mul_nonneg (ha_nonneg k hk le_rfl) (hV_nonneg k le_rfl)
  nlinarith

/-- Decreasing-coefficient scalar distance telescope with the terminal tail
retained, matching the arithmetic core of Lan Eq. (7.2.21).

This aligns directly with `SOptLib.sum_Icc_two_coeff_telescope_le`; the local
wrapper only rewrites the paper's drop form `a_t (V_{t-1}-V_t)` into that
library theorem's two-coefficient form. -/
private theorem sum_Icc_decreasing_coeff_distance_drop_le_initial_with_tail
    (a V : ℕ → ℝ) (k : ℕ) (hk : 1 ≤ k)
    (ha_mono : ∀ n, 1 ≤ n → n < k → a (n + 1) ≤ a n)
    (hV_nonneg : ∀ n, 1 ≤ n → n < k → 0 ≤ V n) :
    Finset.sum (Finset.Icc 1 k) (fun t => a t * (V (t - 1) - V t)) ≤
      a 1 * V 0 - a k * V k := by
  classical
  have htel :=
    SOptLib.sum_Icc_two_coeff_telescope_le a a V k hk hV_nonneg ha_mono
  have hsum_eq :
      Finset.sum (Finset.Icc 1 k) (fun t => a t * (V (t - 1) - V t)) =
        Finset.sum (Finset.Icc 1 k) (fun t => a t * V (t - 1) - a t * V t) := by
    refine Finset.sum_congr rfl ?_
    intro t _ht
    ring
  simpa [hsum_eq] using htel

/-- Distance-sum bound in Lan Eq. (7.2.20), specialized to Theorem 7.11(a)'s
finite window.

This consumes the source monotonicity bridge `parameterRatio_monoA_total_window`,
Gamma positivity on the displayed denominator window, and the feasible-set
diameter definition for `x_t` and `x*`. -/
private theorem theorem711_part_a_distance_telescope_7_2_20 (S : Setup Ω Ξ E)
    (state : ℕ → Ω → S.OuterStatePoint) (k : PositiveTime) {xStar : E}
    (hxStar : S.IsOptimalSolution xStar)
    (hGamma_pos_window : ∀ n, 1 ≤ n → n ≤ k.1 → 0 < S.GammaNat n)
    (hratio_mono_window :
      ∀ n, 1 ≤ n → n < k.1 →
        S.β n * S.γ n / S.GammaNat n ≤
          S.β (n + 1) * S.γ (n + 1) / S.GammaNat (n + 1)) :
    ∀ ω : Ω,
      Finset.sum (Finset.Icc 1 k.1) (fun t =>
        S.γ t / S.GammaNat t *
          (S.β t / 2 *
            (‖S.x state (t - 1) ω - xStar‖ ^ 2 -
              ‖S.x state t ω - xStar‖ ^ 2))) ≤
        (S.β k.1 * S.γ k.1 / (2 * S.GammaNat k.1)) * S.diameter ^ 2 := by
  classical
  intro ω
  let a : ℕ → ℝ := fun t => S.β t * S.γ t / (2 * S.GammaNat t)
  let V : ℕ → ℝ := fun t => ‖S.x state t ω - xStar‖ ^ 2
  have ha_mono : ∀ n, 1 ≤ n → n < k.1 → a n ≤ a (n + 1) := by
    intro n hn hnlt
    have hr := hratio_mono_window n hn hnlt
    have hleft :
        a n = (S.β n * S.γ n / S.GammaNat n) / 2 := by
      simp [a]
      ring
    have hright :
        a (n + 1) =
          (S.β (n + 1) * S.γ (n + 1) / S.GammaNat (n + 1)) / 2 := by
      simp [a]
      ring
    rw [hleft, hright]
    exact div_le_div_of_nonneg_right hr (by norm_num : (0 : ℝ) ≤ 2)
  have ha_nonneg : ∀ n, 1 ≤ n → n ≤ k.1 → 0 ≤ a n := by
    intro n hn hnk
    have hβpos : 0 < S.β n := S.hβ_pos n hn
    have hγnonneg : 0 ≤ S.γ n := (Set.mem_Icc.mp (S.hγ_mem n hn)).1
    have hΓpos : 0 < S.GammaNat n := hGamma_pos_window n hn hnk
    have hdenpos : 0 < 2 * S.GammaNat n := by positivity
    exact div_nonneg (mul_nonneg (le_of_lt hβpos) hγnonneg) (le_of_lt hdenpos)
  have hV_nonneg : ∀ n, n ≤ k.1 → 0 ≤ V n := by
    intro n _hnk
    exact sq_nonneg _
  have hV_le : ∀ n, n ≤ k.1 → V n ≤ S.diameter ^ 2 := by
    intro n _hnk
    rcases S.diameter_spec with ⟨_, _, _, _, _, hbound⟩
    have hnorm : ‖S.x state n ω - xStar‖ ≤ S.diameter :=
      hbound (S.x state n ω) (S.x_mem state n ω) xStar hxStar.1
    have hdiam_nonneg : 0 ≤ S.diameter := le_trans (norm_nonneg _) hnorm
    have hnorm_nonneg : 0 ≤ ‖S.x state n ω - xStar‖ := norm_nonneg _
    dsimp [V]
    nlinarith
  have hscalar :
      Finset.sum (Finset.Icc 1 k.1) (fun t => a t * (V (t - 1) - V t)) ≤
        a k.1 * S.diameter ^ 2 :=
    sum_Icc_increasing_coeff_distance_drop_le_terminal
      a V (S.diameter ^ 2) k.1 k.2 ha_mono ha_nonneg hV_nonneg hV_le
  have hsum_eq :
      Finset.sum (Finset.Icc 1 k.1) (fun t =>
        S.γ t / S.GammaNat t *
          (S.β t / 2 *
            (‖S.x state (t - 1) ω - xStar‖ ^ 2 -
              ‖S.x state t ω - xStar‖ ^ 2))) =
        Finset.sum (Finset.Icc 1 k.1) (fun t => a t * (V (t - 1) - V t)) := by
    refine Finset.sum_congr rfl ?_
    intro t _ht
    dsimp [a, V]
    ring
  simpa [hsum_eq, a] using hscalar

/-- Distance-sum bound in Lan Eq. (7.2.21), specialized to Theorem 7.11(b)'s
finite window.

This consumes the source monotonicity bridge `parameterRatio_monoB_total_window`,
Gamma positivity on the displayed denominator window, `x_zero`, and the source
normalizations `γ₁ = Γ₁ = 1`. -/
private theorem theorem711_part_b_distance_telescope_7_2_21 (S : Setup Ω Ξ E)
    (state : ℕ → Ω → S.OuterStatePoint) (k : PositiveTime) {xStar : E}
    (hstate : S.IsOuterState state)
    (hGamma_pos_window : ∀ n, 1 ≤ n → n ≤ k.1 → 0 < S.GammaNat n)
    (hratio_mono_window :
      ∀ n, 1 ≤ n → n < k.1 →
        S.β (n + 1) * S.γ (n + 1) / S.GammaNat (n + 1) ≤
          S.β n * S.γ n / S.GammaNat n) :
    ∀ ω : Ω,
      Finset.sum (Finset.Icc 1 k.1) (fun t =>
        S.γ t / S.GammaNat t *
          (S.β t / 2 *
            (‖S.x state (t - 1) ω - xStar‖ ^ 2 -
              ‖S.x state t ω - xStar‖ ^ 2))) ≤
        (S.β 1 / 2) * ‖S.x0 - xStar‖ ^ 2 := by
  classical
  intro ω
  let a : ℕ → ℝ := fun t => S.β t * S.γ t / (2 * S.GammaNat t)
  let V : ℕ → ℝ := fun t => ‖S.x state t ω - xStar‖ ^ 2
  have ha_mono : ∀ n, 1 ≤ n → n < k.1 → a (n + 1) ≤ a n := by
    intro n hn hnlt
    have hr := hratio_mono_window n hn hnlt
    have hn_succ_pos : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
    have hleft :
        a (n + 1) =
          (S.β (n + 1) * S.γ (n + 1) / S.GammaNat (n + 1)) / 2 := by
      simp [a]
      ring
    have hright :
        a n = (S.β n * S.γ n / S.GammaNat n) / 2 := by
      simp [a]
      ring
    rw [hleft, hright]
    exact div_le_div_of_nonneg_right hr (by norm_num : (0 : ℝ) ≤ 2)
  have hV_nonneg : ∀ n, 1 ≤ n → n < k.1 → 0 ≤ V n := by
    intro n _hn _hnlt
    exact sq_nonneg _
  have hscalar_tail :
      Finset.sum (Finset.Icc 1 k.1) (fun t => a t * (V (t - 1) - V t)) ≤
        a 1 * V 0 - a k.1 * V k.1 :=
    sum_Icc_decreasing_coeff_distance_drop_le_initial_with_tail
      a V k.1 k.2 ha_mono hV_nonneg
  have ha_k_nonneg : 0 ≤ a k.1 := by
    have hβpos : 0 < S.β k.1 := S.hβ_pos k.1 k.2
    have hγnonneg : 0 ≤ S.γ k.1 := (Set.mem_Icc.mp (S.hγ_mem k.1 k.2)).1
    have hΓpos : 0 < S.GammaNat k.1 := hGamma_pos_window k.1 k.2 le_rfl
    have hdenpos : 0 < 2 * S.GammaNat k.1 := by positivity
    exact div_nonneg (mul_nonneg (le_of_lt hβpos) hγnonneg) (le_of_lt hdenpos)
  have hV_k_nonneg : 0 ≤ V k.1 := sq_nonneg _
  have hscalar :
      Finset.sum (Finset.Icc 1 k.1) (fun t => a t * (V (t - 1) - V t)) ≤
        a 1 * V 0 := by
    have htail_nonneg : 0 ≤ a k.1 * V k.1 :=
      mul_nonneg ha_k_nonneg hV_k_nonneg
    nlinarith
  have hsum_eq :
      Finset.sum (Finset.Icc 1 k.1) (fun t =>
        S.γ t / S.GammaNat t *
          (S.β t / 2 *
            (‖S.x state (t - 1) ω - xStar‖ ^ 2 -
              ‖S.x state t ω - xStar‖ ^ 2))) =
        Finset.sum (Finset.Icc 1 k.1) (fun t => a t * (V (t - 1) - V t)) := by
    refine Finset.sum_congr rfl ?_
    intro t _ht
    dsimp [a, V]
    ring
  have hinit :
      a 1 * V 0 = (S.β 1 / 2) * ‖S.x0 - xStar‖ ^ 2 := by
    dsimp [a, V]
    rw [S.x_zero state hstate ω]
    simp [S.GammaNat_of_pos, S.Gamma_one, S.hγ_one]
  calc
    Finset.sum (Finset.Icc 1 k.1) (fun t =>
        S.γ t / S.GammaNat t *
          (S.β t / 2 *
            (‖S.x state (t - 1) ω - xStar‖ ^ 2 -
              ‖S.x state t ω - xStar‖ ^ 2)))
        = Finset.sum (Finset.Icc 1 k.1) (fun t => a t * (V (t - 1) - V t)) := hsum_eq
    _ ≤ a 1 * V 0 := hscalar
    _ = (S.β 1 / 2) * ‖S.x0 - xStar‖ ^ 2 := hinit

/-- Source formula relation for the bound `C_e` in Theorem 7.11(a), Eq.
(7.2.48).

This is the displayed scalar formula from the theorem statement, with every
source-sensitive quotient represented by `sourceQuotient` witnesses inside the
formula relation.  The PDF does not add nonzero-denominator hypotheses to the
theorem boundary, so denominator admissibility is exposed as part of the partial
mathematical expression rather than as Lean's total `/` fallback.  The SOptLib
candidate `acceleratedExpectedGapBudget` was checked and rejected because it
models the AC-SA budget with different coefficients and denominators.
-/
def theorem711BoundA_sourceBoundary (S : Setup Ω Ξ E) (k : PositiveTime) (Ce : ℝ) :
    Prop :=
  ∃ etaTerm varianceTerm : {i : ℕ // i ∈ Finset.Icc 1 k.1} → ℝ,
    (∀ i : {i : ℕ // i ∈ Finset.Icc 1 k.1},
      let ip : PositiveTime := ⟨i.1, (Finset.mem_Icc.mp i.2).1⟩
      S.sourceQuotient (S.η i.1 * S.γ i.1) (S.Gamma ip) (etaTerm i) ∧
        S.theorem711VarianceQuotient_sourceBoundary ip (varianceTerm i)) ∧
      Ce =
        (S.β k.1 * S.γ k.1 / 2) * S.diameter ^ 2 +
          S.Gamma k * Finset.sum (Finset.Icc 1 k.1).attach (fun i =>
            etaTerm i + varianceTerm i)

/-- Source formula relation for the part-(b) replacement bound in Theorem 7.11.

As in part (a), quotients involving `Γ_i`, `B_i`, and `β_i - Lγ_i` are modeled
with `sourceQuotient` witnesses inside the relation, not by raw Lean division at
the source boundary.
-/
def theorem711BoundB_sourceBoundary (S : Setup Ω Ξ E) (k : PositiveTime) (xStar : E)
    (Ce : ℝ) : Prop :=
  ∃ etaTerm varianceTerm : {i : ℕ // i ∈ Finset.Icc 1 k.1} → ℝ,
    (∀ i : {i : ℕ // i ∈ Finset.Icc 1 k.1},
      let ip : PositiveTime := ⟨i.1, (Finset.mem_Icc.mp i.2).1⟩
      S.sourceQuotient (S.η i.1 * S.γ i.1) (S.Gamma ip) (etaTerm i) ∧
        S.theorem711VarianceQuotient_sourceBoundary ip (varianceTerm i)) ∧
      Ce =
        (S.β 1 * S.Gamma k / 2) * ‖S.x0 - xStar‖ ^ 2 +
          S.Gamma k * Finset.sum (Finset.Icc 1 k.1).attach (fun i =>
            etaTerm i + varianceTerm i)

/-- If a displayed variance denominator in Theorem 7.11(a) is zero, the partial
source formula for `C_e` is not defined. -/
theorem theorem711BoundA_sourceBoundary_false_of_variance_denominator_zero
    (S : Setup Ω Ξ E) (k : PositiveTime) (Ce : ℝ)
    (i : {i : ℕ // i ∈ Finset.Icc 1 k.1})
    (hzero :
      let ip : PositiveTime := ⟨i.1, (Finset.mem_Icc.mp i.2).1⟩
      S.theorem711VarianceDenominator ip = 0) :
    ¬ S.theorem711BoundA_sourceBoundary k Ce := by
  classical
  rintro ⟨etaTerm, varianceTerm, hterms, _hCe⟩
  let ip : PositiveTime := ⟨i.1, (Finset.mem_Icc.mp i.2).1⟩
  have hq : S.theorem711VarianceQuotient_sourceBoundary ip (varianceTerm i) :=
    (hterms i).2
  have hne : S.theorem711VarianceDenominator ip ≠ 0 :=
    ((S.theorem711VarianceQuotient_sourceBoundary_spec ip (varianceTerm i)).mp hq).1
  exact hne hzero

/-- If a displayed variance denominator in Theorem 7.11(b) is zero, the partial
source formula for `C_e` is not defined. -/
theorem theorem711BoundB_sourceBoundary_false_of_variance_denominator_zero
    (S : Setup Ω Ξ E) (k : PositiveTime) (xStar : E) (Ce : ℝ)
    (i : {i : ℕ // i ∈ Finset.Icc 1 k.1})
    (hzero :
      let ip : PositiveTime := ⟨i.1, (Finset.mem_Icc.mp i.2).1⟩
      S.theorem711VarianceDenominator ip = 0) :
    ¬ S.theorem711BoundB_sourceBoundary k xStar Ce := by
  classical
  rintro ⟨etaTerm, varianceTerm, hterms, _hCe⟩
  let ip : PositiveTime := ⟨i.1, (Finset.mem_Icc.mp i.2).1⟩
  have hq : S.theorem711VarianceQuotient_sourceBoundary ip (varianceTerm i) :=
    (hterms i).2
  have hne : S.theorem711VarianceDenominator ip ≠ 0 :=
    ((S.theorem711VarianceQuotient_sourceBoundary_spec ip (varianceTerm i)).mp hq).1
  exact hne hzero

/-- Conclusion shape for the printed Theorem 7.11(a) bound:
`E[f(y_k)-f(x*)] ≤ C_e`, Eq. (7.2.48). -/
def theorem711PartAConclusion_sourceBoundary (S : Setup Ω Ξ E)
    (state : ℕ → Ω → {x : E // x ∈ S.X} × {x : E // x ∈ S.X})
    (k : PositiveTime) (xStar : E) :
    Prop :=
  ∃ Ce : ℝ, S.theorem711BoundA_sourceBoundary k Ce ∧
    S.expectedGapSourceLe state k.1 xStar Ce

/-- Conclusion shape for the printed Theorem 7.11(b) replacement bound. -/
def theorem711PartBConclusion_sourceBoundary (S : Setup Ω Ξ E)
    (state : ℕ → Ω → {x : E // x ∈ S.X} × {x : E // x ∈ S.X})
    (k : PositiveTime) (xStar : E) :
    Prop :=
  ∃ Ce : ℝ, S.theorem711BoundB_sourceBoundary k xStar Ce ∧
    S.expectedGapSourceLe state k.1 xStar Ce

/-- Active relational signature contract for Theorem 7.11(a).

This names the source theorem interface: the displayed assumptions are
(7.2.43), (7.2.44), and (7.2.11), and the optimal-solution clause realizes
Eq. (7.1.1).  The proof sentence after Eq. (7.2.50) about SFO freshness is
included as the source-backed SFO freshness clause rather than derived from
marginal moment assumptions alone.  The generated Algorithm 7.8 state is kept
relational here, so part (a) does not inherit the positive-eta correction needed
only for selected CndG outputs and the part-(c) budget.  The separate
adaptedness clause is the Lean regularity needed to interpret the printed
expectation for a relational state; it is not derivable from `IsOuterState`,
which permits nonmeasurable choices among valid CndG outputs.

No SOptLib match: searched `source boundary contract theorem signature
Theorem 7.11 stochastic conditional gradient sliding`, checked the returned boundary/run
contract bridge candidates, and scanned `SOptLib/Model/Iterates.lean` and
`SOptLib/Layer1/Descent.lean`; those are realization bridges for other
algorithms, not the Theorem 7.11 signature for Algorithm 7.8.
-/
def theorem711PartA_activeSignatureContract_sourceBoundary (S : Setup Ω Ξ E)
    (state : ℕ → Ω → S.OuterStatePoint) (_k : PositiveTime) (xStar : E) : Prop :=
  S.IsOuterState state ∧
    S.OuterStateAdapted state ∧
      S.SFOAssumptions_7_2_43_44 ∧
        S.SFOSampleBasis_Algorithm7_8 ∧
          S.SFO_Independence_Theorem7_11 state ∧
            S.ParameterMonotonicityA_7_2_11 ∧
              S.theorem711VarianceDenominatorDomain _k ∧
                S.IsOptimalSolution xStar

/-- Active relational signature contract for Theorem 7.11(b).

This mirrors the part-(a) contract but uses the alternative quotient
monotonicity condition (7.2.13), matching the source theorem's replacement
case.  The stochastic-freshness sentence used in the proof is included as the
source-backed SFO freshness clause rather than derived from the displayed moment
assumptions alone.  As in part (a), this contract uses a relational generated
state and does not require `HasPositiveEtaSchedule`; it does require the same
adaptedness regularity needed to make the printed expected gap a genuine
expectation for relational states.

No SOptLib match: searched `source boundary contract theorem signature
Theorem 7.11 stochastic conditional gradient sliding`, checked the returned boundary/run
contract bridge candidates, and scanned `SOptLib/Model/Iterates.lean` and
`SOptLib/Layer1/Descent.lean`; none specialize to this paper's corrected
Theorem 7.11(b) signature.
-/
def theorem711PartB_activeSignatureContract_sourceBoundary (S : Setup Ω Ξ E)
    (state : ℕ → Ω → S.OuterStatePoint) (_k : PositiveTime) (xStar : E) : Prop :=
  S.IsOuterState state ∧
    S.OuterStateAdapted state ∧
      S.SFOAssumptions_7_2_43_44 ∧
        S.SFOSampleBasis_Algorithm7_8 ∧
          S.SFO_Independence_Theorem7_11 state ∧
            S.ParameterMonotonicityB_7_2_13 ∧
              S.theorem711VarianceDenominatorDomain _k ∧
                S.IsOptimalSolution xStar

/-- Active corrected signature contract for Theorem 7.11(c).

The source says part (c) holds under the assumptions in part (a) or part (b),
so the contract carries the displayed SFO moment assumptions and either
monotonicity regime together with the source-backed SFO freshness clause used in
the proof after Eq. (7.2.50).  It does not add an `η_k ≠ 0` condition that is
absent from the theorem statement.

No SOptLib match: searched `source boundary contract theorem signature
Theorem 7.11 stochastic conditional gradient sliding`, checked the returned boundary/run
contract bridge candidates, and scanned `SOptLib/Model/Iterates.lean` and
`SOptLib/Layer1/Descent.lean`; available contracts concern generic realization
side conditions, not the Algorithm 7.8 Theorem 7.11(c) corrected signature.
-/
def theorem711PartC_activeSignatureContract_sourceBoundary (S : Setup Ω Ξ E)
    (hη : S.HasPositiveEtaSchedule) : Prop :=
  (S.ParameterMonotonicityA_7_2_11 ∨ S.ParameterMonotonicityB_7_2_13) ∧
    S.SFOAssumptions_7_2_43_44 ∧
      S.SFO_Independence_Theorem7_11 (S.canonicalOuterState hη)

/-- Derived Lean regularity obligation for the expected gap in Theorem 7.11.
It is intentionally separate from the source-facing theorem conclusion. -/
theorem theorem711_expectedGap_wellDefined (S : Setup Ω Ξ E)
    (state : ℕ → Ω → {x : E // x ∈ S.X} × {x : E // x ∈ S.X})
    (hstate : S.IsOuterState state)
    (hAdapted : S.OuterStateAdapted state)
    (hSFO : S.SFOAssumptions_7_2_43_44)
    (k : PositiveTime) {xStar : E} (hxStar : S.IsOptimalSolution xStar) :
    S.expectedGapSeqWellDefined state k.1 xStar := by
  exact S.expectedGapSeqWellDefined_of_outerStateAdapted state hAdapted k.1 xStar

/-- Source-boundary version of Theorem 7.11(a), Eq. (7.2.48), for the generated
Algorithm 7.8 output sequence.

The PDF prints quotients whose denominator admissibility is not fully stated in
the theorem assumptions.  The active contract therefore carries the variance
denominator domain explicitly, while the bound relation still records quotient
values through internal `sourceQuotient` witnesses rather than Lean's total `/`
fallback.  The proof sentence after Eq. (7.2.50) that `δ_{i,j}` is independent
of `x_{i-1}` is carried by the source-backed SFO freshness clause.
-/
theorem theorem711_part_a_sourceBoundary (S : Setup Ω Ξ E)
    (state : ℕ → Ω → S.OuterStatePoint) (k : PositiveTime)
    {xStar : E}
    (hContract : S.theorem711PartA_activeSignatureContract_sourceBoundary state k xStar) :
    S.theorem711PartAConclusion_sourceBoundary state k xStar := by
  rcases hContract with ⟨hstate, hAdapted, hSFO, hBasis, hIndep, hMono, hVarDen, hxStar⟩
  have hwd := S.theorem711_expectedGap_wellDefined
    state hstate hAdapted hSFO k hxStar
  have hUnbiased : S.SFO_Unbiased_7_2_43 := S.SFOAssumptions_unbiased hSFO
  have hVariance : S.SFO_Variance_7_2_44 := S.SFOAssumptions_variance hSFO
  have hFreshRaw := S.SFO_Independence_Theorem7_11_raw hIndep
  have hMartingale :=
    S.theorem711MartingaleCancellation_of_sfo_freshness hstate hAdapted hBasis hSFO hIndep
  have hBatchVariance :=
    S.theorem711MiniBatchVarianceBound_of_sfo_assumptions hstate hAdapted hBasis hSFO hIndep
  have hstep_7_2_49 :
      ∀ (iwin : {i : ℕ // i ∈ Finset.Icc 1 k.1}) (ω : Ω),
        let ip : PositiveTime := ⟨iwin.1, (Finset.mem_Icc.mp iwin.2).1⟩
        S.f (S.y state ip.1 ω) ≤
          (1 - S.γ ip.1) * S.f (S.y state (ip.1 - 1) ω) +
            S.γ ip.1 * S.f xStar +
              S.β ip.1 * S.γ ip.1 / 2 *
                (‖S.x state (ip.1 - 1) ω - xStar‖ ^ 2 -
                  ‖S.x state ip.1 ω - xStar‖ ^ 2) +
              S.η ip.1 * S.γ ip.1 +
              S.γ ip.1 *
                ⟪S.deltaBatch state ip ω, xStar - S.x state (ip.1 - 1) ω⟫_ℝ +
              S.γ ip.1 * ‖S.deltaBatch state ip ω‖ ^ 2 /
                (2 * (S.β ip.1 - S.L * S.γ ip.1)) := by
    intro iwin ω
    let ip : PositiveTime := ⟨iwin.1, (Finset.mem_Icc.mp iwin.2).1⟩
    have hgap_ip : 0 < S.β ip.1 - S.L * S.γ ip.1 := by
      simpa [ip] using S.theorem711VarianceDenominatorDomain_gap_pos k hVarDen iwin
    simpa [ip] using
      stochastic_one_step_recursion_7_2_49 S state hstate ip ω hxStar.1 hgap_ip
  have hGamma_ne_window :
      ∀ iwin : {i : ℕ // i ∈ Finset.Icc 1 k.1},
        let ip : PositiveTime := ⟨iwin.1, (Finset.mem_Icc.mp iwin.2).1⟩
        S.Gamma ip ≠ 0 := by
    intro iwin
    simpa using S.theorem711VarianceDenominatorDomain_Gamma_ne k hVarDen iwin
  have hpath_7_2_50_first :
      ∀ ω : Ω,
        S.f (S.y state k.1 ω) - S.f xStar ≤
          S.GammaNat k.1 * (1 - S.γ 1) *
              (S.f (S.y state 0 ω) - S.f xStar) +
            S.GammaNat k.1 *
              Finset.sum (Finset.Icc 1 k.1) (fun t =>
                S.γ t / S.GammaNat t *
                  (S.β t / 2 *
                    (‖S.x state (t - 1) ω - xStar‖ ^ 2 -
                      ‖S.x state t ω - xStar‖ ^ 2))) +
            S.GammaNat k.1 *
              Finset.sum (Finset.Icc 1 k.1) (fun t =>
                if ht : 1 ≤ t then
                  S.γ t / S.GammaNat t *
                    (S.η t +
                      ⟪S.deltaBatch state ⟨t, ht⟩ ω,
                        xStar - S.x state (t - 1) ω⟫_ℝ +
                      ‖S.deltaBatch state ⟨t, ht⟩ ω‖ ^ 2 /
                        (2 * (S.β t - S.L * S.γ t)))
                else 0) :=
    weighted_recursion_part_a_7_2_50_first S state k xStar
      hstep_7_2_49 hGamma_ne_window
  have hratio_mono_window :
      ∀ n, 1 ≤ n → n < k.1 →
        S.β n * S.γ n / S.GammaNat n ≤
          S.β (n + 1) * S.γ (n + 1) / S.GammaNat (n + 1) :=
    parameterRatio_monoA_total_window S k hMono hGamma_ne_window
  have hGamma_pos_window :
      ∀ n, 1 ≤ n → n ≤ k.1 → 0 < S.GammaNat n :=
    gammaNat_pos_on_theorem711_window S k hGamma_ne_window
  have hdist_7_2_20 :
      ∀ ω : Ω,
        Finset.sum (Finset.Icc 1 k.1) (fun t =>
          S.γ t / S.GammaNat t *
            (S.β t / 2 *
              (‖S.x state (t - 1) ω - xStar‖ ^ 2 -
                ‖S.x state t ω - xStar‖ ^ 2))) ≤
          (S.β k.1 * S.γ k.1 / (2 * S.GammaNat k.1)) * S.diameter ^ 2 :=
    theorem711_part_a_distance_telescope_7_2_20 S state k hxStar
      hGamma_pos_window hratio_mono_window
  have hdist_7_2_20_scaled :
      ∀ ω : Ω,
        S.GammaNat k.1 *
          Finset.sum (Finset.Icc 1 k.1) (fun t =>
            S.γ t / S.GammaNat t *
              (S.β t / 2 *
                (‖S.x state (t - 1) ω - xStar‖ ^ 2 -
                  ‖S.x state t ω - xStar‖ ^ 2))) ≤
          (S.β k.1 * S.γ k.1 / 2) * S.diameter ^ 2 := by
    intro ω
    have hGamma_pos_k : 0 < S.GammaNat k.1 :=
      hGamma_pos_window k.1 k.2 le_rfl
    have hmul :=
      mul_le_mul_of_nonneg_left (hdist_7_2_20 ω) (le_of_lt hGamma_pos_k)
    have hrewrite :
        S.GammaNat k.1 *
            ((S.β k.1 * S.γ k.1 / (2 * S.GammaNat k.1)) *
              S.diameter ^ 2) =
          (S.β k.1 * S.γ k.1 / 2) * S.diameter ^ 2 := by
      field_simp [ne_of_gt hGamma_pos_k]
    simpa [hrewrite] using hmul
  have hpath_7_2_50_second :
      ∀ ω : Ω,
        S.f (S.y state k.1 ω) - S.f xStar ≤
          (S.β k.1 * S.γ k.1 / 2) * S.diameter ^ 2 +
            S.GammaNat k.1 *
              Finset.sum (Finset.Icc 1 k.1) (fun t =>
                if ht : 1 ≤ t then
                  S.γ t / S.GammaNat t *
                    (S.η t +
                      ⟪S.deltaBatch state ⟨t, ht⟩ ω,
                        xStar - S.x state (t - 1) ω⟫_ℝ +
                      ‖S.deltaBatch state ⟨t, ht⟩ ω‖ ^ 2 /
                        (2 * (S.β t - S.L * S.γ t)))
                else 0) := by
    intro ω
    have hfirst := hpath_7_2_50_first ω
    have hinit_zero :
        S.GammaNat k.1 * (1 - S.γ 1) *
            (S.f (S.y state 0 ω) - S.f xStar) = 0 := by
      simp [S.hγ_one]
    have hdist := hdist_7_2_20_scaled ω
    nlinarith
  let etaTerm : {i : ℕ // i ∈ Finset.Icc 1 k.1} → ℝ := fun i =>
    let ip : PositiveTime := ⟨i.1, (Finset.mem_Icc.mp i.2).1⟩
    (S.η i.1 * S.γ i.1) / S.Gamma ip
  let varianceTerm : {i : ℕ // i ∈ Finset.Icc 1 k.1} → ℝ := fun i =>
    let ip : PositiveTime := ⟨i.1, (Finset.mem_Icc.mp i.2).1⟩
    (S.γ i.1 * S.σ ^ 2) / S.theorem711VarianceDenominator ip
  let Ce : ℝ :=
    (S.β k.1 * S.γ k.1 / 2) * S.diameter ^ 2 +
      S.Gamma k * Finset.sum (Finset.Icc 1 k.1).attach (fun i =>
        etaTerm i + varianceTerm i)
  have hBatchZero_window :
      ∀ iwin : {i : ℕ // i ∈ Finset.Icc 1 k.1},
        let ip : PositiveTime := ⟨iwin.1, (Finset.mem_Icc.mp iwin.2).1⟩
        S.sourceExpectationEq
          (fun ω =>
            ⟪S.deltaBatch state ip ω, xStar - S.x state (ip.1 - 1) ω⟫_ℝ) 0 := by
    intro iwin
    let ip : PositiveTime := ⟨iwin.1, (Finset.mem_Icc.mp iwin.2).1⟩
    simpa [ip] using
      theorem711_deltaBatch_inner_expectation_zero S state hMartingale ip hxStar.1
  have hPerIndex_noise_budget :
      ∀ iwin : {i : ℕ // i ∈ Finset.Icc 1 k.1},
        let ip : PositiveTime := ⟨iwin.1, (Finset.mem_Icc.mp iwin.2).1⟩
        (∫ ω,
              (S.γ iwin.1 / S.GammaNat iwin.1) *
                (S.η iwin.1 +
                  ⟪S.deltaBatch state ip ω, xStar - S.x state (iwin.1 - 1) ω⟫_ℝ +
                  ‖S.deltaBatch state ip ω‖ ^ 2 /
                    (2 * (S.β iwin.1 - S.L * S.γ iwin.1))) ∂(S.P : Measure Ω) ≤
            etaTerm iwin + varianceTerm iwin) ∧
          Integrable
            (fun ω =>
              (S.γ iwin.1 / S.GammaNat iwin.1) *
                (S.η iwin.1 +
                  ⟪S.deltaBatch state ip ω, xStar - S.x state (iwin.1 - 1) ω⟫_ℝ +
                  ‖S.deltaBatch state ip ω‖ ^ 2 /
                    (2 * (S.β iwin.1 - S.L * S.γ iwin.1))))
            (S.P : Measure Ω) := by
    intro iwin
    let ip : PositiveTime := ⟨iwin.1, (Finset.mem_Icc.mp iwin.2).1⟩
    have hGammaNat_ip : S.GammaNat ip.1 = S.Gamma ip := by
      simpa [ip] using S.GammaNat_of_pos iwin.1 (Finset.mem_Icc.mp iwin.2).1
    have hGamma_pos_ip : 0 < S.GammaNat ip.1 := by
      exact hGamma_pos_window iwin.1 (Finset.mem_Icc.mp iwin.2).1
        (Finset.mem_Icc.mp iwin.2).2
    have hγ_nonneg_ip : 0 ≤ S.γ ip.1 := by
      exact (Set.mem_Icc.mp (S.hγ_mem ip.1 ip.2)).1
    have hgap_ip : 0 < S.β ip.1 - S.L * S.γ ip.1 := by
      simpa [ip] using S.theorem711VarianceDenominatorDomain_gap_pos k hVarDen iwin
    have heta_ip : etaTerm iwin = (S.η ip.1 * S.γ ip.1) / S.Gamma ip := by
      dsimp [etaTerm, ip]
    have hvar_ip :
        varianceTerm iwin =
          (S.γ ip.1 * S.σ ^ 2) /
            (2 * S.Gamma ip * (S.batchSize ip : ℝ) *
              (S.β ip.1 - S.L * S.γ ip.1)) := by
      dsimp [varianceTerm, theorem711VarianceDenominator, ip]
    simpa [ip] using
      theorem711_part_a_per_index_noise_budget S state ip (etaTerm iwin)
        (varianceTerm iwin)
        (by simpa [ip] using hBatchZero_window iwin)
        (hBatchVariance ip) hGammaNat_ip hGamma_pos_ip hγ_nonneg_ip hgap_ip
        heta_ip hvar_ip
  let noiseSummand :
      {i : ℕ // i ∈ Finset.Icc 1 k.1} → Ω → ℝ := fun iwin ω =>
    if ht : 1 ≤ iwin.1 then
      (S.γ iwin.1 / S.GammaNat iwin.1) *
        (S.η iwin.1 +
          ⟪S.deltaBatch state ⟨iwin.1, ht⟩ ω,
            xStar - S.x state (iwin.1 - 1) ω⟫_ℝ +
          ‖S.deltaBatch state ⟨iwin.1, ht⟩ ω‖ ^ 2 /
            (2 * (S.β iwin.1 - S.L * S.γ iwin.1)))
    else 0
  have hNoiseWindow_attach :
      ∫ ω,
          S.GammaNat k.1 *
            Finset.sum (Finset.Icc 1 k.1).attach (fun iwin => noiseSummand iwin ω)
          ∂(S.P : Measure Ω) ≤
        S.GammaNat k.1 *
          Finset.sum (Finset.Icc 1 k.1).attach (fun iwin =>
            etaTerm iwin + varianceTerm iwin) := by
    refine
      integral_scaled_finset_sum_le_scaled_sum_of_integral_bounds
        (mu := (S.P : Measure Ω)) (Finset.Icc 1 k.1).attach noiseSummand
        (fun iwin => etaTerm iwin + varianceTerm iwin) (S.GammaNat k.1)
        ?_ ?_ (le_of_lt (hGamma_pos_window k.1 k.2 le_rfl))
    · intro iwin _hi
      have hi1 : 1 ≤ iwin.1 := (Finset.mem_Icc.mp iwin.2).1
      simpa [noiseSummand, hi1] using (hPerIndex_noise_budget iwin).2
    · intro iwin _hi
      have hi1 : 1 ≤ iwin.1 := (Finset.mem_Icc.mp iwin.2).1
      simpa [noiseSummand, hi1] using (hPerIndex_noise_budget iwin).1
  have hNoiseGuarded_eq_attach :
      ∀ ω : Ω,
        Finset.sum (Finset.Icc 1 k.1) (fun t =>
          if ht : 1 ≤ t then
            S.γ t / S.GammaNat t *
              (S.η t +
                ⟪S.deltaBatch state ⟨t, ht⟩ ω,
                  xStar - S.x state (t - 1) ω⟫_ℝ +
                ‖S.deltaBatch state ⟨t, ht⟩ ω‖ ^ 2 /
                  (2 * (S.β t - S.L * S.γ t)))
          else 0) =
          Finset.sum (Finset.Icc 1 k.1).attach (fun iwin => noiseSummand iwin ω) := by
    intro ω
    simpa [noiseSummand] using
      (Finset.sum_attach (s := Finset.Icc 1 k.1)
        (f := fun t : ℕ =>
          if ht : 1 ≤ t then
            S.γ t / S.GammaNat t *
              (S.η t +
                ⟪S.deltaBatch state ⟨t, ht⟩ ω,
                  xStar - S.x state (t - 1) ω⟫_ℝ +
                ‖S.deltaBatch state ⟨t, ht⟩ ω‖ ^ 2 /
                  (2 * (S.β t - S.L * S.γ t)))
          else 0)).symm
  have hNoiseWindow_guarded :
      ∫ ω,
          S.GammaNat k.1 *
            Finset.sum (Finset.Icc 1 k.1) (fun t =>
              if ht : 1 ≤ t then
                S.γ t / S.GammaNat t *
                  (S.η t +
                    ⟪S.deltaBatch state ⟨t, ht⟩ ω,
                      xStar - S.x state (t - 1) ω⟫_ℝ +
                    ‖S.deltaBatch state ⟨t, ht⟩ ω‖ ^ 2 /
                      (2 * (S.β t - S.L * S.γ t)))
              else 0) ∂(S.P : Measure Ω) ≤
        S.GammaNat k.1 *
          Finset.sum (Finset.Icc 1 k.1).attach (fun iwin =>
            etaTerm iwin + varianceTerm iwin) := by
    have hfun :
        (fun ω =>
          S.GammaNat k.1 *
            Finset.sum (Finset.Icc 1 k.1) (fun t =>
              if ht : 1 ≤ t then
                S.γ t / S.GammaNat t *
                  (S.η t +
                    ⟪S.deltaBatch state ⟨t, ht⟩ ω,
                      xStar - S.x state (t - 1) ω⟫_ℝ +
                    ‖S.deltaBatch state ⟨t, ht⟩ ω‖ ^ 2 /
                      (2 * (S.β t - S.L * S.γ t)))
              else 0)) =
          fun ω =>
            S.GammaNat k.1 *
              Finset.sum (Finset.Icc 1 k.1).attach (fun iwin => noiseSummand iwin ω) := by
      funext ω
      rw [hNoiseGuarded_eq_attach ω]
    rw [hfun]
    exact hNoiseWindow_attach
  have hNoiseWindow_guarded_int :
      Integrable
        (fun ω =>
          S.GammaNat k.1 *
            Finset.sum (Finset.Icc 1 k.1) (fun t =>
              if ht : 1 ≤ t then
                S.γ t / S.GammaNat t *
                  (S.η t +
                    ⟪S.deltaBatch state ⟨t, ht⟩ ω,
                      xStar - S.x state (t - 1) ω⟫_ℝ +
                    ‖S.deltaBatch state ⟨t, ht⟩ ω‖ ^ 2 /
                      (2 * (S.β t - S.L * S.γ t)))
              else 0))
        (S.P : Measure Ω) := by
    have hattach_int :
        Integrable
          (fun ω =>
            S.GammaNat k.1 *
              Finset.sum (Finset.Icc 1 k.1).attach (fun iwin => noiseSummand iwin ω))
          (S.P : Measure Ω) := by
      have hsum_int :
          Integrable
            (fun ω =>
              Finset.sum (Finset.Icc 1 k.1).attach (fun iwin => noiseSummand iwin ω))
            (S.P : Measure Ω) := by
        exact integrable_finset_sum (Finset.Icc 1 k.1).attach (fun iwin _hi => by
          have hi1 : 1 ≤ iwin.1 := (Finset.mem_Icc.mp iwin.2).1
          simpa [noiseSummand, hi1] using (hPerIndex_noise_budget iwin).2)
      exact hsum_int.const_mul (S.GammaNat k.1)
    have hfun :
        (fun ω =>
          S.GammaNat k.1 *
            Finset.sum (Finset.Icc 1 k.1) (fun t =>
              if ht : 1 ≤ t then
                S.γ t / S.GammaNat t *
                  (S.η t +
                    ⟪S.deltaBatch state ⟨t, ht⟩ ω,
                      xStar - S.x state (t - 1) ω⟫_ℝ +
                    ‖S.deltaBatch state ⟨t, ht⟩ ω‖ ^ 2 /
                      (2 * (S.β t - S.L * S.γ t)))
              else 0)) =
          fun ω =>
            S.GammaNat k.1 *
              Finset.sum (Finset.Icc 1 k.1).attach (fun iwin => noiseSummand iwin ω) := by
      funext ω
      rw [hNoiseGuarded_eq_attach ω]
    rw [hfun]
    exact hattach_int
  refine ⟨Ce, ?hCe, ?hExp⟩
  · unfold theorem711BoundA_sourceBoundary
    refine ⟨etaTerm, varianceTerm, ?_, rfl⟩
    intro i
    let ip : PositiveTime := ⟨i.1, (Finset.mem_Icc.mp i.2).1⟩
    have hGamma_ne : S.Gamma ip ≠ 0 := by
      simpa [ip] using hGamma_ne_window i
    have hVar_ne : S.theorem711VarianceDenominator ip ≠ 0 := by
      simpa [ip] using hVarDen i
    constructor
    · exact ⟨hGamma_ne, by
        dsimp [etaTerm, ip]
        field_simp [hGamma_ne]
        have hGamma_ne' :
            S.Gamma ⟨i.1, (Finset.mem_Icc.mp i.2).1⟩ ≠ 0 := by
          simpa [ip] using hGamma_ne
        field_simp [hGamma_ne']⟩
    · rw [S.theorem711VarianceQuotient_sourceBoundary_spec ip (varianceTerm i)]
      refine ⟨hVar_ne, ?_⟩
      dsimp [varianceTerm, ip]
      field_simp [hVar_ne]
      have hVar_ne' :
          S.theorem711VarianceDenominator ⟨i.1, (Finset.mem_Icc.mp i.2).1⟩ ≠ 0 := by
        simpa [ip] using hVar_ne
      field_simp [hVar_ne']
  · unfold expectedGapSourceLe sourceExpectationLe
    refine ⟨hwd, ?_⟩
    change ∫ ω, S.f (S.y state k.1 ω) - S.f xStar ∂(S.P : Measure Ω) ≤ Ce
    let firstTerm : ℝ := (S.β k.1 * S.γ k.1 / 2) * S.diameter ^ 2
    let noiseWindow : Ω → ℝ := fun ω =>
      S.GammaNat k.1 *
        Finset.sum (Finset.Icc 1 k.1) (fun t =>
          if ht : 1 ≤ t then
            S.γ t / S.GammaNat t *
              (S.η t +
                ⟪S.deltaBatch state ⟨t, ht⟩ ω,
                  xStar - S.x state (t - 1) ω⟫_ℝ +
                ‖S.deltaBatch state ⟨t, ht⟩ ω‖ ^ 2 /
                  (2 * (S.β t - S.L * S.γ t)))
          else 0)
    have hleft_int :
        Integrable (fun ω => S.f (S.y state k.1 ω) - S.f xStar)
          (S.P : Measure Ω) := by
      exact
        (SOptLib.expectationWellDefined_iff_integrable (S.P : Measure Ω)
          (fun ω => S.f (S.y state k.1 ω) - S.f xStar)).mp
          (by simpa [expectedGapSeqWellDefined, expectedGapWellDefined] using hwd)
    have hnoise_int : Integrable noiseWindow (S.P : Measure Ω) := by
      simpa [noiseWindow] using hNoiseWindow_guarded_int
    have hrhs_int :
        Integrable (fun ω => firstTerm + noiseWindow ω) (S.P : Measure Ω) := by
      exact (integrable_const (c := firstTerm)).add hnoise_int
    have hmono :
        ∫ ω, S.f (S.y state k.1 ω) - S.f xStar ∂(S.P : Measure Ω) ≤
          ∫ ω, firstTerm + noiseWindow ω ∂(S.P : Measure Ω) := by
      refine integral_mono hleft_int hrhs_int ?_
      intro ω
      simpa [firstTerm, noiseWindow] using hpath_7_2_50_second ω
    have hrhs_bound :
        ∫ ω, firstTerm + noiseWindow ω ∂(S.P : Measure Ω) ≤
          firstTerm +
            S.GammaNat k.1 *
              Finset.sum (Finset.Icc 1 k.1).attach (fun iwin =>
                etaTerm iwin + varianceTerm iwin) := by
      have hconst_int : Integrable (fun _ : Ω => firstTerm) (S.P : Measure Ω) :=
        integrable_const (c := firstTerm)
      rw [integral_add hconst_int hnoise_int]
      simp [integral_const]
      simpa [noiseWindow] using hNoiseWindow_guarded
    have hCe_eq :
        firstTerm +
            S.GammaNat k.1 *
              Finset.sum (Finset.Icc 1 k.1).attach (fun iwin =>
                etaTerm iwin + varianceTerm iwin) = Ce := by
      dsimp [Ce, firstTerm]
      rw [S.GammaNat_of_pos k.1 k.2]
    exact le_trans hmono (le_trans hrhs_bound (le_of_eq hCe_eq))

/-- Source-boundary version of Theorem 7.11(b), with the part-(b) replacement
bound, for the generated Algorithm 7.8 output sequence.

As in part (a), the displayed variance quotient carries a denominator domain not
listed as a paper assumption; the corrected active contract exposes that domain
and the source formula relation records the quotient value without totalized
division.  The same SFO-freshness proof step used in part (a) is carried by the
source-backed SFO freshness clause.
-/
theorem theorem711_part_b_sourceBoundary (S : Setup Ω Ξ E)
    (state : ℕ → Ω → S.OuterStatePoint) (k : PositiveTime)
    {xStar : E}
    (hContract : S.theorem711PartB_activeSignatureContract_sourceBoundary state k xStar) :
    S.theorem711PartBConclusion_sourceBoundary state k xStar := by
  rcases hContract with ⟨hstate, hAdapted, hSFO, hBasis, hIndep, hMono, hVarDen, hxStar⟩
  have hwd := S.theorem711_expectedGap_wellDefined
    state hstate hAdapted hSFO k hxStar
  have hUnbiased : S.SFO_Unbiased_7_2_43 := S.SFOAssumptions_unbiased hSFO
  have hVariance : S.SFO_Variance_7_2_44 := S.SFOAssumptions_variance hSFO
  have hFreshRaw := S.SFO_Independence_Theorem7_11_raw hIndep
  have hMartingale :=
    S.theorem711MartingaleCancellation_of_sfo_freshness hstate hAdapted hBasis hSFO hIndep
  have hBatchVariance :=
    S.theorem711MiniBatchVarianceBound_of_sfo_assumptions hstate hAdapted hBasis hSFO hIndep
  have hstep_7_2_49 :
      ∀ (iwin : {i : ℕ // i ∈ Finset.Icc 1 k.1}) (ω : Ω),
        let ip : PositiveTime := ⟨iwin.1, (Finset.mem_Icc.mp iwin.2).1⟩
        S.f (S.y state ip.1 ω) ≤
          (1 - S.γ ip.1) * S.f (S.y state (ip.1 - 1) ω) +
            S.γ ip.1 * S.f xStar +
              S.β ip.1 * S.γ ip.1 / 2 *
                (‖S.x state (ip.1 - 1) ω - xStar‖ ^ 2 -
                  ‖S.x state ip.1 ω - xStar‖ ^ 2) +
              S.η ip.1 * S.γ ip.1 +
              S.γ ip.1 *
                ⟪S.deltaBatch state ip ω, xStar - S.x state (ip.1 - 1) ω⟫_ℝ +
              S.γ ip.1 * ‖S.deltaBatch state ip ω‖ ^ 2 /
                (2 * (S.β ip.1 - S.L * S.γ ip.1)) := by
    intro iwin ω
    let ip : PositiveTime := ⟨iwin.1, (Finset.mem_Icc.mp iwin.2).1⟩
    have hgap_ip : 0 < S.β ip.1 - S.L * S.γ ip.1 := by
      simpa [ip] using S.theorem711VarianceDenominatorDomain_gap_pos k hVarDen iwin
    simpa [ip] using
      stochastic_one_step_recursion_7_2_49 S state hstate ip ω hxStar.1 hgap_ip
  have hGamma_ne_window :
      ∀ iwin : {i : ℕ // i ∈ Finset.Icc 1 k.1},
        let ip : PositiveTime := ⟨iwin.1, (Finset.mem_Icc.mp iwin.2).1⟩
        S.Gamma ip ≠ 0 := by
    intro iwin
    simpa using S.theorem711VarianceDenominatorDomain_Gamma_ne k hVarDen iwin
  have hpath_7_2_50_first :
      ∀ ω : Ω,
        S.f (S.y state k.1 ω) - S.f xStar ≤
          S.GammaNat k.1 * (1 - S.γ 1) *
              (S.f (S.y state 0 ω) - S.f xStar) +
            S.GammaNat k.1 *
              Finset.sum (Finset.Icc 1 k.1) (fun t =>
                S.γ t / S.GammaNat t *
                  (S.β t / 2 *
                    (‖S.x state (t - 1) ω - xStar‖ ^ 2 -
                      ‖S.x state t ω - xStar‖ ^ 2))) +
            S.GammaNat k.1 *
              Finset.sum (Finset.Icc 1 k.1) (fun t =>
                if ht : 1 ≤ t then
                  S.γ t / S.GammaNat t *
                    (S.η t +
                      ⟪S.deltaBatch state ⟨t, ht⟩ ω,
                        xStar - S.x state (t - 1) ω⟫_ℝ +
                      ‖S.deltaBatch state ⟨t, ht⟩ ω‖ ^ 2 /
                        (2 * (S.β t - S.L * S.γ t)))
                else 0) :=
    weighted_recursion_part_a_7_2_50_first S state k xStar
      hstep_7_2_49 hGamma_ne_window
  have hratio_mono_window :
      ∀ n, 1 ≤ n → n < k.1 →
        S.β (n + 1) * S.γ (n + 1) / S.GammaNat (n + 1) ≤
          S.β n * S.γ n / S.GammaNat n :=
    parameterRatio_monoB_total_window S k hMono hGamma_ne_window
  have hGamma_pos_window :
      ∀ n, 1 ≤ n → n ≤ k.1 → 0 < S.GammaNat n :=
    gammaNat_pos_on_theorem711_window S k hGamma_ne_window
  have hdist_7_2_21 :
      ∀ ω : Ω,
        Finset.sum (Finset.Icc 1 k.1) (fun t =>
          S.γ t / S.GammaNat t *
            (S.β t / 2 *
              (‖S.x state (t - 1) ω - xStar‖ ^ 2 -
                ‖S.x state t ω - xStar‖ ^ 2))) ≤
          (S.β 1 / 2) * ‖S.x0 - xStar‖ ^ 2 :=
    theorem711_part_b_distance_telescope_7_2_21 S state k hstate
      hGamma_pos_window hratio_mono_window
  have hdist_7_2_21_scaled :
      ∀ ω : Ω,
        S.GammaNat k.1 *
          Finset.sum (Finset.Icc 1 k.1) (fun t =>
            S.γ t / S.GammaNat t *
              (S.β t / 2 *
                (‖S.x state (t - 1) ω - xStar‖ ^ 2 -
                  ‖S.x state t ω - xStar‖ ^ 2))) ≤
          (S.β 1 * S.Gamma k / 2) * ‖S.x0 - xStar‖ ^ 2 := by
    intro ω
    have hGamma_pos_k : 0 < S.GammaNat k.1 :=
      hGamma_pos_window k.1 k.2 le_rfl
    have hmul :=
      mul_le_mul_of_nonneg_left (hdist_7_2_21 ω) (le_of_lt hGamma_pos_k)
    have hrewrite :
        S.GammaNat k.1 * ((S.β 1 / 2) * ‖S.x0 - xStar‖ ^ 2) =
          (S.β 1 * S.Gamma k / 2) * ‖S.x0 - xStar‖ ^ 2 := by
      rw [S.GammaNat_of_pos k.1 k.2]
      ring
    simpa [hrewrite] using hmul
  have hpath_7_2_50_second :
      ∀ ω : Ω,
        S.f (S.y state k.1 ω) - S.f xStar ≤
          (S.β 1 * S.Gamma k / 2) * ‖S.x0 - xStar‖ ^ 2 +
            S.GammaNat k.1 *
              Finset.sum (Finset.Icc 1 k.1) (fun t =>
                if ht : 1 ≤ t then
                  S.γ t / S.GammaNat t *
                    (S.η t +
                      ⟪S.deltaBatch state ⟨t, ht⟩ ω,
                        xStar - S.x state (t - 1) ω⟫_ℝ +
                      ‖S.deltaBatch state ⟨t, ht⟩ ω‖ ^ 2 /
                        (2 * (S.β t - S.L * S.γ t)))
                else 0) := by
    intro ω
    have hfirst := hpath_7_2_50_first ω
    have hinit_zero :
        S.GammaNat k.1 * (1 - S.γ 1) *
            (S.f (S.y state 0 ω) - S.f xStar) = 0 := by
      simp [S.hγ_one]
    have hdist := hdist_7_2_21_scaled ω
    nlinarith
  let etaTerm : {i : ℕ // i ∈ Finset.Icc 1 k.1} → ℝ := fun i =>
    let ip : PositiveTime := ⟨i.1, (Finset.mem_Icc.mp i.2).1⟩
    (S.η i.1 * S.γ i.1) / S.Gamma ip
  let varianceTerm : {i : ℕ // i ∈ Finset.Icc 1 k.1} → ℝ := fun i =>
    let ip : PositiveTime := ⟨i.1, (Finset.mem_Icc.mp i.2).1⟩
    (S.γ i.1 * S.σ ^ 2) / S.theorem711VarianceDenominator ip
  let Ce : ℝ :=
    (S.β 1 * S.Gamma k / 2) * ‖S.x0 - xStar‖ ^ 2 +
      S.Gamma k * Finset.sum (Finset.Icc 1 k.1).attach (fun i =>
        etaTerm i + varianceTerm i)
  have hBatchZero_window :
      ∀ iwin : {i : ℕ // i ∈ Finset.Icc 1 k.1},
        let ip : PositiveTime := ⟨iwin.1, (Finset.mem_Icc.mp iwin.2).1⟩
        S.sourceExpectationEq
          (fun ω =>
            ⟪S.deltaBatch state ip ω, xStar - S.x state (ip.1 - 1) ω⟫_ℝ) 0 := by
    intro iwin
    let ip : PositiveTime := ⟨iwin.1, (Finset.mem_Icc.mp iwin.2).1⟩
    simpa [ip] using
      theorem711_deltaBatch_inner_expectation_zero S state hMartingale ip hxStar.1
  have hPerIndex_noise_budget :
      ∀ iwin : {i : ℕ // i ∈ Finset.Icc 1 k.1},
        let ip : PositiveTime := ⟨iwin.1, (Finset.mem_Icc.mp iwin.2).1⟩
        (∫ ω,
              (S.γ iwin.1 / S.GammaNat iwin.1) *
                (S.η iwin.1 +
                  ⟪S.deltaBatch state ip ω, xStar - S.x state (iwin.1 - 1) ω⟫_ℝ +
                  ‖S.deltaBatch state ip ω‖ ^ 2 /
                    (2 * (S.β iwin.1 - S.L * S.γ iwin.1))) ∂(S.P : Measure Ω) ≤
            etaTerm iwin + varianceTerm iwin) ∧
          Integrable
            (fun ω =>
              (S.γ iwin.1 / S.GammaNat iwin.1) *
                (S.η iwin.1 +
                  ⟪S.deltaBatch state ip ω, xStar - S.x state (iwin.1 - 1) ω⟫_ℝ +
                  ‖S.deltaBatch state ip ω‖ ^ 2 /
                    (2 * (S.β iwin.1 - S.L * S.γ iwin.1))))
            (S.P : Measure Ω) := by
    intro iwin
    let ip : PositiveTime := ⟨iwin.1, (Finset.mem_Icc.mp iwin.2).1⟩
    have hGammaNat_ip : S.GammaNat ip.1 = S.Gamma ip := by
      simpa [ip] using S.GammaNat_of_pos iwin.1 (Finset.mem_Icc.mp iwin.2).1
    have hGamma_pos_ip : 0 < S.GammaNat ip.1 := by
      exact hGamma_pos_window iwin.1 (Finset.mem_Icc.mp iwin.2).1
        (Finset.mem_Icc.mp iwin.2).2
    have hγ_nonneg_ip : 0 ≤ S.γ ip.1 := by
      exact (Set.mem_Icc.mp (S.hγ_mem ip.1 ip.2)).1
    have hgap_ip : 0 < S.β ip.1 - S.L * S.γ ip.1 := by
      simpa [ip] using S.theorem711VarianceDenominatorDomain_gap_pos k hVarDen iwin
    have heta_ip : etaTerm iwin = (S.η ip.1 * S.γ ip.1) / S.Gamma ip := by
      dsimp [etaTerm, ip]
    have hvar_ip :
        varianceTerm iwin =
          (S.γ ip.1 * S.σ ^ 2) /
            (2 * S.Gamma ip * (S.batchSize ip : ℝ) *
              (S.β ip.1 - S.L * S.γ ip.1)) := by
      dsimp [varianceTerm, theorem711VarianceDenominator, ip]
    simpa [ip] using
      theorem711_part_a_per_index_noise_budget S state ip (etaTerm iwin)
        (varianceTerm iwin)
        (by simpa [ip] using hBatchZero_window iwin)
        (hBatchVariance ip) hGammaNat_ip hGamma_pos_ip hγ_nonneg_ip hgap_ip
        heta_ip hvar_ip
  let noiseSummand :
      {i : ℕ // i ∈ Finset.Icc 1 k.1} → Ω → ℝ := fun iwin ω =>
    if ht : 1 ≤ iwin.1 then
      (S.γ iwin.1 / S.GammaNat iwin.1) *
        (S.η iwin.1 +
          ⟪S.deltaBatch state ⟨iwin.1, ht⟩ ω,
            xStar - S.x state (iwin.1 - 1) ω⟫_ℝ +
          ‖S.deltaBatch state ⟨iwin.1, ht⟩ ω‖ ^ 2 /
            (2 * (S.β iwin.1 - S.L * S.γ iwin.1)))
    else 0
  have hNoiseWindow_attach :
      ∫ ω,
          S.GammaNat k.1 *
            Finset.sum (Finset.Icc 1 k.1).attach (fun iwin => noiseSummand iwin ω)
          ∂(S.P : Measure Ω) ≤
        S.GammaNat k.1 *
          Finset.sum (Finset.Icc 1 k.1).attach (fun iwin =>
            etaTerm iwin + varianceTerm iwin) := by
    refine
      integral_scaled_finset_sum_le_scaled_sum_of_integral_bounds
        (mu := (S.P : Measure Ω)) (Finset.Icc 1 k.1).attach noiseSummand
        (fun iwin => etaTerm iwin + varianceTerm iwin) (S.GammaNat k.1)
        ?_ ?_ (le_of_lt (hGamma_pos_window k.1 k.2 le_rfl))
    · intro iwin _hi
      have hi1 : 1 ≤ iwin.1 := (Finset.mem_Icc.mp iwin.2).1
      simpa [noiseSummand, hi1] using (hPerIndex_noise_budget iwin).2
    · intro iwin _hi
      have hi1 : 1 ≤ iwin.1 := (Finset.mem_Icc.mp iwin.2).1
      simpa [noiseSummand, hi1] using (hPerIndex_noise_budget iwin).1
  have hNoiseGuarded_eq_attach :
      ∀ ω : Ω,
        Finset.sum (Finset.Icc 1 k.1) (fun t =>
          if ht : 1 ≤ t then
            S.γ t / S.GammaNat t *
              (S.η t +
                ⟪S.deltaBatch state ⟨t, ht⟩ ω,
                  xStar - S.x state (t - 1) ω⟫_ℝ +
                ‖S.deltaBatch state ⟨t, ht⟩ ω‖ ^ 2 /
                  (2 * (S.β t - S.L * S.γ t)))
          else 0) =
          Finset.sum (Finset.Icc 1 k.1).attach (fun iwin => noiseSummand iwin ω) := by
    intro ω
    simpa [noiseSummand] using
      (Finset.sum_attach (s := Finset.Icc 1 k.1)
        (f := fun t : ℕ =>
          if ht : 1 ≤ t then
            S.γ t / S.GammaNat t *
              (S.η t +
                ⟪S.deltaBatch state ⟨t, ht⟩ ω,
                  xStar - S.x state (t - 1) ω⟫_ℝ +
                ‖S.deltaBatch state ⟨t, ht⟩ ω‖ ^ 2 /
                  (2 * (S.β t - S.L * S.γ t)))
          else 0)).symm
  have hNoiseWindow_guarded :
      ∫ ω,
          S.GammaNat k.1 *
            Finset.sum (Finset.Icc 1 k.1) (fun t =>
              if ht : 1 ≤ t then
                S.γ t / S.GammaNat t *
                  (S.η t +
                    ⟪S.deltaBatch state ⟨t, ht⟩ ω,
                      xStar - S.x state (t - 1) ω⟫_ℝ +
                    ‖S.deltaBatch state ⟨t, ht⟩ ω‖ ^ 2 /
                      (2 * (S.β t - S.L * S.γ t)))
              else 0) ∂(S.P : Measure Ω) ≤
        S.GammaNat k.1 *
          Finset.sum (Finset.Icc 1 k.1).attach (fun iwin =>
            etaTerm iwin + varianceTerm iwin) := by
    have hfun :
        (fun ω =>
          S.GammaNat k.1 *
            Finset.sum (Finset.Icc 1 k.1) (fun t =>
              if ht : 1 ≤ t then
                S.γ t / S.GammaNat t *
                  (S.η t +
                    ⟪S.deltaBatch state ⟨t, ht⟩ ω,
                      xStar - S.x state (t - 1) ω⟫_ℝ +
                    ‖S.deltaBatch state ⟨t, ht⟩ ω‖ ^ 2 /
                      (2 * (S.β t - S.L * S.γ t)))
              else 0)) =
          fun ω =>
            S.GammaNat k.1 *
              Finset.sum (Finset.Icc 1 k.1).attach (fun iwin => noiseSummand iwin ω) := by
      funext ω
      rw [hNoiseGuarded_eq_attach ω]
    rw [hfun]
    exact hNoiseWindow_attach
  have hNoiseWindow_guarded_int :
      Integrable
        (fun ω =>
          S.GammaNat k.1 *
            Finset.sum (Finset.Icc 1 k.1) (fun t =>
              if ht : 1 ≤ t then
                S.γ t / S.GammaNat t *
                  (S.η t +
                    ⟪S.deltaBatch state ⟨t, ht⟩ ω,
                      xStar - S.x state (t - 1) ω⟫_ℝ +
                    ‖S.deltaBatch state ⟨t, ht⟩ ω‖ ^ 2 /
                      (2 * (S.β t - S.L * S.γ t)))
              else 0))
        (S.P : Measure Ω) := by
    have hattach_int :
        Integrable
          (fun ω =>
            S.GammaNat k.1 *
              Finset.sum (Finset.Icc 1 k.1).attach (fun iwin => noiseSummand iwin ω))
          (S.P : Measure Ω) := by
      have hsum_int :
          Integrable
            (fun ω =>
              Finset.sum (Finset.Icc 1 k.1).attach (fun iwin => noiseSummand iwin ω))
            (S.P : Measure Ω) := by
        exact integrable_finset_sum (Finset.Icc 1 k.1).attach (fun iwin _hi => by
          have hi1 : 1 ≤ iwin.1 := (Finset.mem_Icc.mp iwin.2).1
          simpa [noiseSummand, hi1] using (hPerIndex_noise_budget iwin).2)
      exact hsum_int.const_mul (S.GammaNat k.1)
    have hfun :
        (fun ω =>
          S.GammaNat k.1 *
            Finset.sum (Finset.Icc 1 k.1) (fun t =>
              if ht : 1 ≤ t then
                S.γ t / S.GammaNat t *
                  (S.η t +
                    ⟪S.deltaBatch state ⟨t, ht⟩ ω,
                      xStar - S.x state (t - 1) ω⟫_ℝ +
                    ‖S.deltaBatch state ⟨t, ht⟩ ω‖ ^ 2 /
                      (2 * (S.β t - S.L * S.γ t)))
              else 0)) =
          fun ω =>
            S.GammaNat k.1 *
              Finset.sum (Finset.Icc 1 k.1).attach (fun iwin => noiseSummand iwin ω) := by
      funext ω
      rw [hNoiseGuarded_eq_attach ω]
    rw [hfun]
    exact hattach_int
  refine ⟨Ce, ?hCe, ?hExp⟩
  · unfold theorem711BoundB_sourceBoundary
    refine ⟨etaTerm, varianceTerm, ?_, rfl⟩
    intro i
    let ip : PositiveTime := ⟨i.1, (Finset.mem_Icc.mp i.2).1⟩
    have hGamma_ne : S.Gamma ip ≠ 0 := by
      simpa [ip] using hGamma_ne_window i
    have hVar_ne : S.theorem711VarianceDenominator ip ≠ 0 := by
      simpa [ip] using hVarDen i
    constructor
    · exact ⟨hGamma_ne, by
        dsimp [etaTerm, ip]
        field_simp [hGamma_ne]
        have hGamma_ne' :
            S.Gamma ⟨i.1, (Finset.mem_Icc.mp i.2).1⟩ ≠ 0 := by
          simpa [ip] using hGamma_ne
        field_simp [hGamma_ne']⟩
    · rw [S.theorem711VarianceQuotient_sourceBoundary_spec ip (varianceTerm i)]
      refine ⟨hVar_ne, ?_⟩
      dsimp [varianceTerm, ip]
      field_simp [hVar_ne]
      have hVar_ne' :
          S.theorem711VarianceDenominator ⟨i.1, (Finset.mem_Icc.mp i.2).1⟩ ≠ 0 := by
        simpa [ip] using hVar_ne
      field_simp [hVar_ne']
  · unfold expectedGapSourceLe sourceExpectationLe
    refine ⟨hwd, ?_⟩
    change ∫ ω, S.f (S.y state k.1 ω) - S.f xStar ∂(S.P : Measure Ω) ≤ Ce
    let firstTerm : ℝ := (S.β 1 * S.Gamma k / 2) * ‖S.x0 - xStar‖ ^ 2
    let noiseWindow : Ω → ℝ := fun ω =>
      S.GammaNat k.1 *
        Finset.sum (Finset.Icc 1 k.1) (fun t =>
          if ht : 1 ≤ t then
            S.γ t / S.GammaNat t *
              (S.η t +
                ⟪S.deltaBatch state ⟨t, ht⟩ ω,
                  xStar - S.x state (t - 1) ω⟫_ℝ +
                ‖S.deltaBatch state ⟨t, ht⟩ ω‖ ^ 2 /
                  (2 * (S.β t - S.L * S.γ t)))
          else 0)
    have hleft_int :
        Integrable (fun ω => S.f (S.y state k.1 ω) - S.f xStar)
          (S.P : Measure Ω) := by
      exact
        (SOptLib.expectationWellDefined_iff_integrable (S.P : Measure Ω)
          (fun ω => S.f (S.y state k.1 ω) - S.f xStar)).mp
          (by simpa [expectedGapSeqWellDefined, expectedGapWellDefined] using hwd)
    have hnoise_int : Integrable noiseWindow (S.P : Measure Ω) := by
      simpa [noiseWindow] using hNoiseWindow_guarded_int
    have hrhs_int :
        Integrable (fun ω => firstTerm + noiseWindow ω) (S.P : Measure Ω) := by
      exact (integrable_const (c := firstTerm)).add hnoise_int
    have hmono :
        ∫ ω, S.f (S.y state k.1 ω) - S.f xStar ∂(S.P : Measure Ω) ≤
          ∫ ω, firstTerm + noiseWindow ω ∂(S.P : Measure Ω) := by
      refine integral_mono hleft_int hrhs_int ?_
      intro ω
      simpa [firstTerm, noiseWindow] using hpath_7_2_50_second ω
    have hrhs_bound :
        ∫ ω, firstTerm + noiseWindow ω ∂(S.P : Measure Ω) ≤
          firstTerm +
            S.GammaNat k.1 *
              Finset.sum (Finset.Icc 1 k.1).attach (fun iwin =>
                etaTerm iwin + varianceTerm iwin) := by
      have hconst_int : Integrable (fun _ : Ω => firstTerm) (S.P : Measure Ω) :=
        integrable_const (c := firstTerm)
      rw [integral_add hconst_int hnoise_int]
      simp [integral_const]
      simpa [noiseWindow] using hNoiseWindow_guarded
    have hCe_eq :
        firstTerm +
            S.GammaNat k.1 *
              Finset.sum (Finset.Icc 1 k.1).attach (fun iwin =>
                etaTerm iwin + varianceTerm iwin) = Ce := by
      dsimp [Ce, firstTerm]
      rw [S.GammaNat_of_pos k.1 k.2]
    exact le_trans hmono (le_trans hrhs_bound (le_of_eq hCe_eq))

/-- Printed scalar inside the CndG inner-iteration ceiling, Eq. (7.2.15), as a
partial source quotient.

The source states `η_k ∈ R_+` / `η_k ≥ 0`, while Eq. (7.2.15) divides by
`η_k`.  This definition therefore records the displayed expression through
`sourceQuotient`; the corrected Theorem 7.11(c) contract supplies
`HasPositiveEtaSchedule` rather than using Lean's total division fallback.
-/
def cndGIterationBudgetScalar_sourceBoundary (S : Setup Ω Ξ E) (k : PositiveTime)
    (q : ℝ) : Prop :=
  S.sourceQuotient (6 * S.β k.1 * S.diameter ^ 2) (S.η k.1) q

/-- Domain/value bridge for the CndG inner-iteration scalar in Eq. (7.2.15). -/
theorem cndGIterationBudgetScalar_sourceBoundary_spec (S : Setup Ω Ξ E)
    (k : PositiveTime) (q : ℝ) :
    S.cndGIterationBudgetScalar_sourceBoundary k q ↔
      S.η k.1 ≠ 0 ∧ q * S.η k.1 = 6 * S.β k.1 * S.diameter ^ 2 := by
  rfl

/-- The CndG inner-iteration ceiling `T_k := ceil(6 β_k Dbar_X^2 / η_k)`, Eq.
(7.2.15), as a source formula relation.

No SOptLib match: searched the pre-candidates and ceiling helpers such as
`le_positive_ceil_max_one`; those are generic budget facts, while Eq. (7.2.15)
is the paper-specific CndG ceiling with `β_k`, `D̄_X`, and `η_k`.  The
definition stays a source formula relation; positivity is carried by the
corrected theorem contract that consumes it.
-/
def cndGIterationBudget_7_2_15 (S : Setup Ω Ξ E) (k : PositiveTime) (T : ℕ) :
    Prop :=
  ∃ q : ℝ, S.cndGIterationBudgetScalar_sourceBoundary k q ∧ T = Nat.ceil q

/-- Inner-iteration bound using the printed Eq. (7.2.15) ceiling.

Algorithm 7.6 starts the CndG index at `t = 1`; the source text counts an inner
iteration when that index increments.  Thus stopping at source index `t` performs
`t - 1` inner iterations, and Theorem 7.11(c)'s bound is on this count rather than
on the one-based stopping index itself.
-/
def InnerIterationBound_7_2_15 (S : Setup Ω Ξ E)
    (state : ℕ → Ω → {x : E // x ∈ S.X} × {x : E // x ∈ S.X}) : Prop :=
  ∀ (k : PositiveTime) (ω : Ω),
    ∃ t T : ℕ,
      S.cndGStopsAt (S.batchGradient state k ω) (S.x state (k.1 - 1) ω)
          (S.β k.1) (S.η k.1) t ∧
        S.x state k.1 ω =
            S.cndGInnerIterate (S.batchGradient state k ω) (S.x state (k.1 - 1) ω)
            (S.β k.1) t ∧
          S.cndGIterationBudget_7_2_15 k T ∧
            t - 1 ≤ T

/-- Retired audit-only version of `InnerIterationBound_7_2_15`.

This records the old, incorrect interpretation that bounded the one-based CndG
stopping index `t` itself by the Eq. (7.2.15) budget.  It is intentionally not
used by the source-facing Theorem 7.11(c) boundary; the theorem below is the
formal falsity witness for this retired shape in the zero-budget case.
-/
def retiredInnerIterationBound_7_2_15_indexBound (S : Setup Ω Ξ E)
    (state : ℕ → Ω → {x : E // x ∈ S.X} × {x : E // x ∈ S.X}) : Prop :=
  ∀ (k : PositiveTime) (ω : Ω),
    ∃ t T : ℕ,
      S.cndGStopsAt (S.batchGradient state k ω) (S.x state (k.1 - 1) ω)
          (S.β k.1) (S.η k.1) t ∧
        S.x state k.1 ω =
            S.cndGInnerIterate (S.batchGradient state k ω) (S.x state (k.1 - 1) ω)
            (S.β k.1) t ∧
          S.cndGIterationBudget_7_2_15 k T ∧
            t ≤ T

/-- If the numerator in Eq. (7.2.15) is zero and `η_k > 0`, its ceiling budget
is forced to be zero. -/
theorem cndGIterationBudget_7_2_15_eq_zero_of_numerator_zero (S : Setup Ω Ξ E)
    (k : PositiveTime) {T : ℕ} (hηpos : 0 < S.η k.1)
    (hnum : 6 * S.β k.1 * S.diameter ^ 2 = 0)
    (hbudget : S.cndGIterationBudget_7_2_15 k T) :
    T = 0 := by
  rcases hbudget with ⟨q, hq, rfl⟩
  have hqspec := (S.cndGIterationBudgetScalar_sourceBoundary_spec k q).mp hq
  have hqη0 : q * S.η k.1 = 0 := by
    simpa [hnum] using hqspec.2
  have hηne : S.η k.1 ≠ 0 := ne_of_gt hηpos
  have hq0 : q = 0 := (mul_eq_zero.mp hqη0).resolve_right hηne
  simpa [hq0]

/-- Zero feasible-set diameter is a concrete source-compatible case where the
printed Eq. (7.2.15) budget is zero under positive tolerance. -/
theorem cndGIterationBudget_7_2_15_eq_zero_of_diameter_zero (S : Setup Ω Ξ E)
    (k : PositiveTime) {T : ℕ} (hηpos : 0 < S.η k.1)
    (hD0 : S.diameter = 0)
    (hbudget : S.cndGIterationBudget_7_2_15 k T) :
    T = 0 := by
  exact S.cndGIterationBudget_7_2_15_eq_zero_of_numerator_zero k hηpos
    (by simp [hD0]) hbudget

/-- Formal falsity witness for the retired `t <= T` interpretation.

When Eq. (7.2.15) forces `T = 0`, the retired statement would require a CndG
stopping index `t` with both `1 <= t` from `cndGStopsAt` and `t <= 0`.
-/
theorem retiredInnerIterationBound_7_2_15_indexBound_false_of_zero_budget
    (S : Setup Ω Ξ E)
    (state : ℕ → Ω → {x : E // x ∈ S.X} × {x : E // x ∈ S.X})
    (k : PositiveTime) (ω : Ω)
    (hBudgetZero : ∀ T : ℕ, S.cndGIterationBudget_7_2_15 k T → T = 0) :
    ¬ S.retiredInnerIterationBound_7_2_15_indexBound state := by
  intro hbound
  rcases hbound k ω with ⟨t, T, hstop, _hx, hbudget, ht_le_T⟩
  have hT0 : T = 0 := hBudgetZero T hbudget
  have ht_le_zero : t ≤ 0 := by
    simpa [hT0] using ht_le_T
  have ht_pos : 1 ≤ t := hstop.1
  omega

/-- Formal zero-diameter falsity witness for the retired `t <= T` shape.

This is the contradiction that motivated replacing the live bound with
`t - 1 <= T`: with `Dbar_X = 0`, positive `η_k` makes the Eq. (7.2.15) budget
zero, while every valid CndG stopping index is one-based.
-/
theorem retiredInnerIterationBound_7_2_15_indexBound_false_of_diameter_zero
    (S : Setup Ω Ξ E)
    (state : ℕ → Ω → {x : E // x ∈ S.X} × {x : E // x ∈ S.X})
    (k : PositiveTime) (ω : Ω) (hηpos : 0 < S.η k.1)
    (hD0 : S.diameter = 0) :
    ¬ S.retiredInnerIterationBound_7_2_15_indexBound state := by
  exact S.retiredInnerIterationBound_7_2_15_indexBound_false_of_zero_budget
    state k ω (fun T hbudget =>
      S.cndGIterationBudget_7_2_15_eq_zero_of_diameter_zero k hηpos hD0 hbudget)

/-- Formal eta-zero obstruction for the printed CndG budget (7.2.15).

The source formula is represented by `sourceQuotient`, whose denominator must be
nonzero.  Thus at any outer index with `η_k = 0`, the old unguarded part-(c)
conclusion is false before any stochastic proof obligations are considered.
-/
theorem cndGIterationBudget_7_2_15_false_of_eta_zero (S : Setup Ω Ξ E)
    (k : PositiveTime) (hη0 : S.η k.1 = 0) (T : ℕ) :
    ¬ S.cndGIterationBudget_7_2_15 k T := by
  rintro ⟨q, hq, _hT⟩
  exact ((S.cndGIterationBudgetScalar_sourceBoundary_spec k q).mp hq).1 hη0

/-- Formal statement-correction witness for Theorem 7.11(c).

If the original unguarded conclusion were used at an index with `η_k = 0`, the
required source quotient in (7.2.15) would be impossible.  The corrected
Theorem 7.11(c) boundary below therefore carries `HasPositiveEtaSchedule`.
-/
theorem InnerIterationBound_7_2_15_false_of_eta_zero (S : Setup Ω Ξ E)
    (state : ℕ → Ω → {x : E // x ∈ S.X} × {x : E // x ∈ S.X})
    (k : PositiveTime) (ω : Ω) (hη0 : S.η k.1 = 0) :
    ¬ S.InnerIterationBound_7_2_15 state := by
  intro hbound
  rcases hbound k ω with ⟨_t, T, _hstop, _hx, hbudget, _hle⟩
  exact S.cndGIterationBudget_7_2_15_false_of_eta_zero k hη0 T hbudget

/-- Positive eta supplies the denominator side condition required by (7.2.15). -/
theorem theorem711PartC_positiveEta_denominator (S : Setup Ω Ξ E)
    (hη : S.HasPositiveEtaSchedule) (k : PositiveTime) :
    S.η k.1 ≠ 0 :=
  ne_of_gt (hη k.1 k.2)

/-- Source-boundary bridge from Theorem 7.9(c)'s shifted CndG Wolfe-gap bound
to the performed-update count in Eq. (7.2.15).

This is the same source step as Lan Theorem 7.9(c), proof step 18: the CndG
procedure stops once the shifted minimum Wolfe gap is below `η`.  Candidates
considered before adding this bridge were `cndG_shifted_min_wolfe_gap_bound`,
`cndGStopIndex_stops`, `cndGTerminates_obligation`, and SOptLib's
`le_positive_ceil_max_one`; they either provide the min-gap/termination input or
bound `max 1 (ceil q)`, while this theorem needs the paper's exact performed
count `stopIndex - 1 ≤ ceil q`.
-/
private theorem cndGStopIndex_sub_one_le_budget (S : Setup Ω Ξ E)
    (g u : E) (β η q : ℝ) (hu : u ∈ S.X) (hβ : 0 < β) (hη : 0 < η)
    (hq : S.sourceQuotient (6 * β * S.diameter ^ 2) η q) :
    S.cndGStopIndex g u β η hu hβ hη - 1 ≤ Nat.ceil q := by
  classical
  let A : ℝ := 6 * β * S.diameter ^ 2
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    nlinarith [le_of_lt hβ, sq_nonneg S.diameter]
  rcases hq with ⟨hηne, hq_mul_raw⟩
  have hq_mul : q * η = A := by
    simpa [A] using hq_mul_raw
  have hq_eq : q = A / η := by
    rw [← hq_mul]
    field_simp [ne_of_gt hη]
  have hq_nonneg : 0 ≤ q := by
    rw [hq_eq]
    exact div_nonneg hA_nonneg (le_of_lt hη)
  by_cases hceil0 : Nat.ceil q = 0
  · have hq_le_zero : q ≤ 0 := by
      simpa [hceil0] using (Nat.le_ceil q)
    have hq0 : q = 0 := le_antisymm hq_le_zero hq_nonneg
    have hA0 : A = 0 := by
      have htmp : (0 : ℝ) = A := by simpa [hq0] using hq_mul
      exact htmp.symm
    have hDsq0 : S.diameter ^ 2 = 0 := by
      dsimp [A] at hA0
      nlinarith [hA0, hβ]
    have hD0 : S.diameter = 0 := by
      nlinarith [hDsq0, sq_nonneg S.diameter]
    have hlin_eq : S.cndGLinearOracle g u β u = u := by
      have hnorm_le := cndGLinearOracle_displacement_norm_le_diameter S g u β hu
      have hnorm_nonneg : 0 ≤ ‖S.cndGLinearOracle g u β u - u‖ := norm_nonneg _
      have hnorm0 : ‖S.cndGLinearOracle g u β u - u‖ = 0 := by
        nlinarith [hD0, hnorm_le, hnorm_nonneg]
      have hsub : S.cndGLinearOracle g u β u - u = 0 := norm_eq_zero.mp hnorm0
      exact sub_eq_zero.mp hsub
    have hgap0 : S.cndGGap g u β (S.cndGInnerIterate g u β 1) = 0 := by
      simp [cndGGap, hlin_eq]
    have hstop1 : S.cndGStopsAt g u β η 1 := by
      refine ⟨le_rfl, ?_⟩
      rw [hgap0]
      exact le_of_lt hη
    have hfind : S.cndGStopIndex g u β η hu hβ hη ≤ 1 := by
      unfold cndGStopIndex
      exact Nat.find_le hstop1
    have htarget : S.cndGStopIndex g u β η hu hβ hη - 1 ≤ 0 := by
      omega
    simpa [hceil0] using htarget
  · have hTpos : 1 ≤ Nat.ceil q := by omega
    obtain ⟨j, hj1, hjT, hgap⟩ :=
      cndG_shifted_min_wolfe_gap_bound S g u β hu hβ (Nat.ceil q) hTpos
    let d : ℝ := ((Nat.ceil q + 1 : ℕ) : ℝ)
    have hdpos : 0 < d := by
      dsimp [d]
      exact_mod_cast Nat.succ_pos (Nat.ceil q)
    have hq_le_T : q ≤ (Nat.ceil q : ℝ) := Nat.le_ceil q
    have hT_le_d : (Nat.ceil q : ℝ) ≤ d := by
      dsimp [d]
      exact_mod_cast Nat.le_succ (Nat.ceil q)
    have hq_le_d : q ≤ d := le_trans hq_le_T hT_le_d
    have hq_div_le_one : q / d ≤ 1 := by
      field_simp [ne_of_gt hdpos]
      exact hq_le_d
    have hscalar :
        6 * β * S.diameter ^ 2 / (((Nat.ceil q + 1 : ℕ) : ℝ)) ≤ η := by
      have hrewrite : 6 * β * S.diameter ^ 2 = q * η := by
        simpa [A] using hq_mul.symm
      rw [hrewrite]
      change q * η / d ≤ η
      have hcalc : q / d * η ≤ 1 * η := by
        exact mul_le_mul_of_nonneg_right hq_div_le_one (le_of_lt hη)
      have heq : q * η / d = q / d * η := by field_simp [ne_of_gt hdpos]
      linarith
    have hstop : S.cndGStopsAt g u β η (j + 1) := by
      refine ⟨by omega, ?_⟩
      exact le_trans hgap hscalar
    have hfind : S.cndGStopIndex g u β η hu hβ hη ≤ j + 1 := by
      unfold cndGStopIndex
      exact Nat.find_le hstop
    omega

/-- Source-boundary version of Theorem 7.11(c), the CndG inner-iteration bound,
for the generated Algorithm 7.8 output sequence.

The printed ceiling (7.2.15) contains division by `η_k`, while the algorithm only
states `η_k ∈ R_+`; the active contract therefore carries the positive-domain
correction needed by Theorem 7.9(c)'s proof and by `sourceQuotient`.
-/
theorem theorem711_part_c_sourceBoundary (S : Setup Ω Ξ E)
    (hη : S.HasPositiveEtaSchedule)
    (hContract : S.theorem711PartC_activeSignatureContract_sourceBoundary hη) :
    S.InnerIterationBound_7_2_15 (S.canonicalOuterState hη) := by
  rcases hContract with ⟨hMono, hSFO, hIndep⟩
  have hstate : S.IsOuterState (S.canonicalOuterState hη) :=
    S.canonicalOuterState_isOuterState hη
  have hUnbiased : S.SFO_Unbiased_7_2_43 := S.SFOAssumptions_unbiased hSFO
  have hVariance : S.SFO_Variance_7_2_44 := S.SFOAssumptions_variance hSFO
  intro k ω
  rcases k with ⟨m, hm⟩
  cases m with
  | zero => omega
  | succ n =>
      let kp : PositiveTime := ⟨n + 1, Nat.succ_pos n⟩
      have hkp_eq : (⟨n + 1, hm⟩ : PositiveTime) = kp := by
        ext
        rfl
      let state := S.canonicalOuterState hη
      let q : ℝ := (6 * S.β (n + 1) * S.diameter ^ 2) / S.η (n + 1)
      let T : ℕ := Nat.ceil q
      let gk : E := S.batchGradient state kp ω
      let uk : E := S.x state n ω
      have hηk : 0 < S.η (n + 1) := hη (n + 1) (Nat.succ_pos n)
      have hβk : 0 < S.β (n + 1) := S.hβ_pos (n + 1) (Nat.succ_pos n)
      have huk : uk ∈ S.X := by
        dsimp [uk, state, x]
        exact (S.canonicalOuterState hη n ω).1.2
      let t : ℕ :=
        S.cndGStopIndex gk uk (S.β (n + 1)) (S.η (n + 1)) huk hβk hηk
      refine ⟨t, T, ?_, ?_, ?_, ?_⟩
      · dsimp [t]
        simpa [gk, uk, state, hkp_eq] using
          (S.cndGStopIndex_stops gk uk (S.β (n + 1)) (S.η (n + 1)) huk hβk
            hηk)
      · dsimp [t, gk, uk, state]
        simp [x, cndG, canonicalOuterState_succ, outerStep, batchGradient, z, y,
          hkp_eq, kp]
      · refine ⟨q, ?_, rfl⟩
        constructor
        · exact ne_of_gt hηk
        · dsimp [q]
          field_simp [ne_of_gt hηk]
      · dsimp [t, T]
        apply cndGStopIndex_sub_one_le_budget S gk uk (S.β (n + 1))
          (S.η (n + 1)) q huk hβk hηk
        constructor
        · exact ne_of_gt hηk
        · dsimp [q]
          field_simp [ne_of_gt hηk]

/-- Private audit table naming the live split source-boundary contract.

This is not a mathematical hypothesis and is not consumed by Theorem 7.11.
It is a compact metadata hook for Phase 0 signature-contract mode: the active
contract is `theorem711_sourceBoundary_activeSignatureContract`, and the table
records that parts (a)/(b) use the relational generated-state route while part
(c) uses the corrected positive-eta source-boundary route. -/
def theorem711_sourceBoundary_signatureTable_iteration41 : List
    (String × String × String × String × String × String × String) :=
  [
    ("Algorithms.Unverified.StochasticConditionalGradientSliding.Setup.theorem711_sourceBoundary_activeSignatureContract",
      "live B-track contract packages Theorem 7.11(a), (b), (c), and the sample-basis filtration bridge",
      "Theorem 7.11(a)/(b) use relational Algorithm 7.8 states; part (c) uses S.canonicalOuterState hEta on the explicit HasPositiveEtaSchedule correction domain",
      "SFOAssumptions_7_2_43_44 is exactly the displayed mean/variance pair, while SFOSampleBasis_Algorithm7_8 supplies the fresh mini-batch sample stream used in Eq. (7.2.47)",
      "SFO_Independence_Theorem7_11 is the proof-step residual-freshness boundary after Eq. (7.2.50)",
      "theorem711BoundA/B and cndGIterationBudget_7_2_15 keep sourceQuotient partial-domain formulas; A/B contracts carry the displayed variance denominator domain",
      "corrected_not_original: JSON main_theorem prints quotients and SFO moments, while PDF proof uses residual freshness and omits nonzero denominator assumptions")
  ]

/-- Active type-level contract for the split Theorem 7.11 source-boundary
surface.

This is an audit target rather than a new mathematical assumption.  It names the
live part-(a), part-(b), and part-(c) declarations, and it also names the
sample-basis bridge that derives only generated filtration data.  Parts (a) and
(b) remain relational generated-state theorems; part (c) is the corrected
positive-eta budget theorem.  The residual-freshness sentence used after
Eq. (7.2.50) remains the explicit boundary `SFO_Independence_Theorem7_11`.
If a future edit reintroduces raw total quotients, drops the active
SFO-freshness boundary, or replaces the relational Algorithm 7.8 state in parts
(a)/(b) by an unconditional CndG selector, this contract stops typechecking.

No SOptLib match: searched source-boundary/run-contract bridge candidates and
checked sibling active-signature patterns in
`Algorithms/Unverified/StochasticGradientSliding/Part007.lean`; available
SOptLib bridge theorems are generic realization tools, not this paper's Theorem
7.11 public surface.
-/
def theorem711_sourceBoundary_activeSignatureContractStatement (S : Setup Ω Ξ E) :
    Prop :=
  (∀ (state : ℕ → Ω → S.OuterStatePoint) (k : PositiveTime) (xStar : E),
      S.theorem711PartA_activeSignatureContract_sourceBoundary state k xStar →
        S.theorem711PartAConclusion_sourceBoundary state k xStar) ∧
    (∀ (state : ℕ → Ω → S.OuterStatePoint) (k : PositiveTime) (xStar : E),
      S.theorem711PartB_activeSignatureContract_sourceBoundary state k xStar →
        S.theorem711PartBConclusion_sourceBoundary state k xStar) ∧
      (∀ hη : S.HasPositiveEtaSchedule,
        S.theorem711PartC_activeSignatureContract_sourceBoundary hη →
          S.InnerIterationBound_7_2_15 (S.canonicalOuterState hη)) ∧
        (∀ state :
          ℕ → Ω → {x : E // x ∈ S.X} × {x : E // x ∈ S.X},
          S.IsOuterState state →
            S.OuterStateAdapted state →
            S.SFOSampleBasis_Algorithm7_8 →
              S.OuterStateAdapted state ∧
                (∀ n, Measurable (S.flatSample n)) ∧
                  ProbabilityTheory.iIndepFun S.flatSample (S.P : Measure Ω))

/-- Active signature contract for the corrected Theorem 7.11 source-boundary
surface. -/
theorem theorem711_sourceBoundary_activeSignatureContract (S : Setup Ω Ξ E) :
    S.theorem711_sourceBoundary_activeSignatureContractStatement := by
  dsimp [theorem711_sourceBoundary_activeSignatureContractStatement]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro state k xStar hContract
    exact S.theorem711_part_a_sourceBoundary state k hContract
  · intro state k xStar hContract
    exact S.theorem711_part_b_sourceBoundary state k hContract
  · intro hη hContract
    exact S.theorem711_part_c_sourceBoundary hη hContract
  · intro state hstate hAdapted hBasis
    exact S.theorem711_sampleBasis_generated_filtration_data state hstate hAdapted hBasis

end Setup

end Algorithms.Unverified.StochasticConditionalGradientSliding
