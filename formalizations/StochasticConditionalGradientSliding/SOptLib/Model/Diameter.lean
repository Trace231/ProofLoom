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

end SOptLib
