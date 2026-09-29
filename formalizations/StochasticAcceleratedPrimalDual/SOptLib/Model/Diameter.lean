import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Order.Compact

namespace SOptLib

/-- Any feasible pair is bounded by the norm diameter of a selected maximizing feasible pair.

The selected pair lives in the subtype carrier `X × X`, while callers often
reason about ambient points with membership proofs. This theorem bridges those
forms without exposing the subtype packaging at every bound site.

Layer: Model | Gap: Level 0 (selected feasible-set diameter pair bound)
Proof: build the carrier pair from the two ambient membership proofs and apply
  the supplied maximality certificate for the selected pair.
Source: Mathlib subtype, product, normed additive group, and ordered real APIs
Used in: stochastic and finite-sum nonconvex conditional-gradient feasible-set
  diameter bounds for Wolfe-gap perturbation and smoothness estimates
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/parameters
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem le_euclideanDiameterOfPair_of_mem
    {E : Type*} [NormedAddCommGroup E] {X : Set E}
    (p : {x : E // x ∈ X} × {x : E // x ∈ X})
    (hmax : ∀ q : {x : E // x ∈ X} × {x : E // x ∈ X},
      ‖(q.1 : E) - (q.2 : E)‖ ≤ ‖(p.1 : E) - (p.2 : E)‖)
    {x y : E} (hx : x ∈ X) (hy : y ∈ X) :
    ‖x - y‖ ≤ ‖(p.1 : E) - (p.2 : E)‖ := by
  exact hmax (⟨⟨x, hx⟩, ⟨y, hy⟩⟩ : {x : E // x ∈ X} × {x : E // x ∈ X})

/-- A nonempty compact set in a normed additive group has a pair attaining its norm diameter.

The witness is returned in the subtype carrier `X × X`, so downstream
algorithm code can use the maximizing pair directly as feasible points.

Layer: Model | Gap: Level 1 (compact feasible-set norm diameter maximizer)
Proof: apply `IsCompact.exists_isMaxOn` to the continuous kernel
  `p ↦ ‖p.1 - p.2‖` on the compact product `X × X`, then rebuild the
  maximizing point as a pair of subtype elements.
Source: Mathlib compactness, product compactness, norm continuity, and
  extreme-value APIs
Used in: stochastic and finite-sum nonconvex conditional-gradient feasible-set
  diameter constants for Wolfe-gap perturbation estimates
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/parameters
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem diameterPair_exists_of_isCompact
    {E : Type*} [NormedAddCommGroup E] {X : Set E}
    (hX_ne : X.Nonempty) (hX_compact : IsCompact X) :
    ∃ p : {x : E // x ∈ X} × {x : E // x ∈ X},
      ∀ q : {x : E // x ∈ X} × {x : E // x ∈ X},
        ‖(q.1 : E) - (q.2 : E)‖ ≤ ‖(p.1 : E) - (p.2 : E)‖ := by
  classical
  let S : Set (E × E) := X.prod X
  have hSne : S.Nonempty := by
    rcases hX_ne with ⟨x, hx⟩
    exact ⟨(x, x), ⟨hx, hx⟩⟩
  have hScompact : IsCompact S := hX_compact.prod hX_compact
  have hcont : ContinuousOn (fun p : E × E => ‖p.1 - p.2‖) S := by
    exact ((continuous_fst.sub continuous_snd).norm).continuousOn
  obtain ⟨p, hpS, hpmax⟩ := hScompact.exists_isMaxOn hSne hcont
  refine ⟨(⟨p.1, hpS.1⟩, ⟨p.2, hpS.2⟩), ?_⟩
  intro q
  exact hpmax (show ((q.1 : E), (q.2 : E)) ∈ S from
    ⟨q.1.property, q.2.property⟩)

/-- Compatibility spelling for compact feasible-set diameter maximizers. -/
theorem diameterPair_exists
    {E : Type*} [NormedAddCommGroup E] {X : Set E}
    (hX_ne : X.Nonempty) (hX_compact : IsCompact X) :
    ∃ p : {x : E // x ∈ X} × {x : E // x ∈ X},
      ∀ q : {x : E // x ∈ X} × {x : E // x ∈ X},
        ‖(q.1 : E) - (q.2 : E)‖ ≤ ‖(p.1 : E) - (p.2 : E)‖ :=
  diameterPair_exists_of_isCompact hX_ne hX_compact

-- Promoted from SAPD Phase 3 staging (batch 1): Bregman compactness bridge.

-- Generalization plan (G0):
-- G0.1 naming: isCompact_of_closed_of_bregman_half_sq_le_bounded_at_base
--   (orig was: isCompact_of_closed_of_bregman_half_sq_le_bounded_at_base).
-- G0.2 typeclass level used:
--   E: [NormedAddCommGroup E] [ProperSpace E]; the proof uses only subtraction,
--     norm, the triangle inequality, compactness of closed balls in a proper
--     metric space, and real square-root arithmetic. No inner product,
--     completeness, convexity, differentiability, or finite-dimensionality is
--     used.
--   measure: none.
--   convexity: none.
-- G0.3 reusability — could instantiate:
--   1. stochastic accelerated primal-dual primal and dual carrier compactness
--      from bounded DGF/Bregman diameter assumptions.
--   2. stochastic mirror descent or mirror-prox compact prox-subproblem
--      existence after a Bregman diameter assumption supplies a base-point
--      metric radius.
-- G0.4 search trace:
--   queries: ["closed bregman bounded compact",
--     "IsCompact closed subset closedBall ProperSpace"]
--   top hits: ["isCompact_univ_subtype_of_isClosed_isBounded",
--     "ProperSpace.isCompact_closedBall",
--     "Metric.isCompact_of_isClosed_isBounded",
--     "sq_norm_le_two_mul_of_half_sq_norm_le",
--     "IsDistanceGeneratingFunctionOn.half_sq_norm_le_bregman"]
--   coverage: partial — Mathlib and SOptLib cover closed-and-bounded
--     compactness and the pointwise half-squared-distance normalization, but
--     no hit packages the Bregman-at-base inequalities into the boundedness
--     proof for the feasible carrier.
-- G0.4 not-a-thin-wrapper rationale: the theorem adds the reusable invariant
--   that a closed carrier with a base-point Bregman lower bound and a
--   base-point Bregman radius bound is metrically bounded, then compact in any
--   proper normed additive commutative group.
-- G0.5 structural-content rationale: the statement exposes the optimization
--   proof boundary between Bregman coercivity at a base point, a squared
--   Bregman radius, and compactness of the carrier without paper-local setup
--   fields.
-- G0.5c thin-wrapper self-detect: clean — the body constructs a global norm
--   radius from two pointwise Bregman inequalities before invoking compactness
--   of closed balls.
-- G0.5d minimal-hypothesis check: the Bregman lower and upper bounds are
--   pointwise at the selected base point for each feasible `x`; no unused
--   global two-point diameter, convexity, continuity, or differentiability
--   hypothesis is retained.

/-- A closed carrier is compact when Bregman control at one base point bounds
its metric radius.

If every feasible point has half-squared distance to `x0` controlled by a
two-point Bregman kernel and that same Bregman value is bounded by `D ^ 2`,
then the carrier lies in a closed ball around the origin. In a proper normed
space, closedness turns this boundedness into compactness.

Layer: Model | Gap: Level 1 (Bregman base-point radius compactness)
Proof: derive a uniform bound on `‖x - x0‖` by combining the half-squared
  lower bound, the Bregman upper bound, and `Real.le_sqrt_of_sq_le`; the
  triangle inequality bounds `‖x‖`, so the closed carrier is a closed subset of
  a compact closed ball.
Source: Mathlib proper metric spaces, normed additive groups, and real
  square-root/order arithmetic
Used in: stochastic accelerated primal-dual feasible-carrier compactness before
  prox-subproblem and diameter arguments
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/assumptions
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
theorem isCompact_of_closed_of_bregman_half_sq_le_bounded_at_base
    {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    (X : Set E) (x0 : E) (V : E → E → ℝ) (D : ℝ)
    (hX_closed : IsClosed X)
    (hlower : ∀ x, x ∈ X → (1 / 2 : ℝ) * ‖x - x0‖ ^ 2 ≤ V x x0)
    (hupper : ∀ x, x ∈ X → V x x0 ≤ D ^ 2) :
    IsCompact X := by
  let R : ℝ := ‖x0‖ + Real.sqrt (2 * D ^ 2)
  have hX_bound : ∀ x, x ∈ X → ‖x‖ ≤ R := by
    intro x hx
    have hsq : ‖x - x0‖ ^ 2 ≤ 2 * D ^ 2 := by
      have hlower_x := hlower x hx
      have hupper_x := hupper x hx
      nlinarith
    have hdist : ‖x - x0‖ ≤ Real.sqrt (2 * D ^ 2) :=
      Real.le_sqrt_of_sq_le hsq
    have htri : ‖x‖ ≤ ‖x - x0‖ + ‖x0‖ := by
      have h := norm_add_le (x - x0) x0
      have hEq : x - x0 + x0 = x := by
        abel
      simpa [hEq] using h
    nlinarith
  refine (ProperSpace.isCompact_closedBall (0 : E) R).of_isClosed_subset hX_closed ?_
  intro x hx
  have hxR := hX_bound x hx
  simpa [Metric.mem_closedBall, dist_eq_norm] using hxR

end SOptLib
