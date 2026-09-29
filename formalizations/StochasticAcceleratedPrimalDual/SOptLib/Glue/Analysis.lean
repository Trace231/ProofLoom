-- SOptLib/Glue/Analysis.lean
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Seminorm
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic
import SOptLib.Model.Bregman
import SOptLib.Model.Norms
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Topology.Semicontinuity.Basic


open Topology
open scoped BigOperators ENNReal InnerProductSpace

/-- A selector cluster point lifts to a graph cluster point under parameter convergence.

If the parameter filter tends to `p` and `z` is a cluster point of `sel` along
that filter, then `(p, z)` is a cluster point of the graph map
`q ↦ (q, sel q)`.

Layer: Glue | Gap: Level 1 (graph cluster-point lifting under parameter convergence)
Proof: rewrite `MapClusterPt` using the product-neighborhood basis, then combine
  eventual membership of parameter neighborhoods from `Tendsto` with frequent
  membership of selector neighborhoods from the cluster-point hypothesis.
Source: Mathlib filter cluster-point and product topology APIs
Used in: compact unique-argmin continuity via graph cluster-point extraction
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic mirror descent -/
private theorem mapClusterPt_graph_of_tendsto_of_mapClusterPt
    {P K : Type*} [TopologicalSpace P] [TopologicalSpace K]
    {l : Filter P} {p : P} {sel : P → K} {z : K}
    (hp : Filter.Tendsto id l (𝓝 p)) (hz : MapClusterPt z l sel) :
    MapClusterPt (p, z) l (fun q => (q, sel q)) := by
  rw [((𝓝 p).basis_sets.prod_nhds (𝓝 z).basis_sets).mapClusterPt_iff_frequently]
  rintro ⟨s, t⟩ ⟨hs, ht⟩
  have hs_eventually : ∀ᶠ q in l, q ∈ s := hp hs
  have ht_frequently : ∃ᶠ q in l, sel q ∈ t := by
    rw [mapClusterPt_iff_frequently] at hz
    exact hz t ht
  exact (ht_frequently.and_eventually hs_eventually).mono fun q hq => ⟨hq.2, hq.1⟩

/-- A compact unique argmin selector is continuous under joint continuity.

If `F` is continuous jointly in a parameter and a compact candidate, `sel p`
minimizes `F p ·` for every `p`, and minimizers are unique, then `sel` is
continuous.

Layer: Glue | Gap: Level 2 (compact unique-argmin selection continuity)
Proof: every cluster point of `sel` along parameters tending to `p₀` is a
  minimizer of the limiting objective by closedness of `≤` in `ℝ`; uniqueness
  identifies the cluster point with `sel p₀`, and compactness turns unique
  cluster points into convergence.
Source: Mathlib compactness and closed-order topology APIs
Used in: stochastic mirror descent prox-step continuity
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan stochastic mirror descent -/
theorem continuous_argmin_of_compact_unique
    {P K : Type*} [TopologicalSpace P] [TopologicalSpace K] [CompactSpace K]
    (F : P → K → ℝ) (sel : P → K)
    (hF : Continuous (fun q : P × K => F q.1 q.2))
    (hsel_min : ∀ p y, F p (sel p) ≤ F p y)
    (hunique : ∀ p z z',
      (∀ y, F p z ≤ F p y) →
      (∀ y, F p z' ≤ F p y) →
      z = z') :
    Continuous sel := by
  refine continuous_iff_continuousAt.2 ?_
  intro p0
  change Filter.Tendsto sel (𝓝 p0) (𝓝 (sel p0))
  refine (isCompact_univ : IsCompact (Set.univ : Set K)).tendsto_nhds_of_unique_mapClusterPt
    (l := 𝓝 p0) (y := sel p0) (f := sel)
    (Filter.Eventually.of_forall fun p => Set.mem_univ (sel p)) ?_
  intro z _hzuniv hzcluster
  have hzmin : ∀ y : K, F p0 z ≤ F p0 y := by
    intro y
    let graph : P → P × K := fun p => (p, sel p)
    let C : Set (P × K) := {q | F q.1 q.2 ≤ F q.1 y}
    have hCclosed : IsClosed C := by
      have hleft : Continuous (fun q : P × K => F q.1 q.2) := hF
      have hright : Continuous (fun q : P × K => F q.1 y) :=
        hF.comp (continuous_fst.prodMk continuous_const)
      simpa [C] using isClosed_le hleft hright
    have hgraph_cluster : MapClusterPt (p0, z) (𝓝 p0) graph := by
      exact mapClusterPt_graph_of_tendsto_of_mapClusterPt
        (sel := sel) (p := p0) (z := z)
        (continuous_id.continuousAt : Filter.Tendsto id (𝓝 p0) (𝓝 p0))
        (by simpa using hzcluster)
    have hevent : ∀ᶠ p in 𝓝 p0, graph p ∈ C := by
      exact Filter.Eventually.of_forall fun p => by
        dsimp [graph, C]
        exact hsel_min p y
    have hmem : (p0, z) ∈ C :=
      hCclosed.mem_of_mapClusterPt hgraph_cluster hevent
    simpa [C] using hmem
  have hselmin : ∀ y : K, F p0 (sel p0) ≤ F p0 y := by
    intro y
    exact hsel_min p0 y
  exact hunique p0 z (sel p0) hzmin hselmin

/-- A compact unique argmin prox selector is measurable under joint continuity.

If the mirror-step objective is jointly continuous in the state, gradient,
stepsize, and compact candidate, and the minimizing candidate is unique, then
the selected prox point is measurable as a function of the step parameters.

Layer: Model | Gap: Level 2 (measurability of compact unique-argmin prox selector)
Proof: first apply compact unique-argmin continuity to the parameterized
  objective, then use continuity-to-measurability for Borel spaces.
Source: Mathlib compactness, continuity, and Borel measurability APIs
Used in: stochastic mirror descent prox-step measurability for compact argmin selection
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic mirror descent -/
theorem proxStep_measurable_of_joint_continuous_unique
    {P E : Type*} [TopologicalSpace P] [MeasurableSpace P] [BorelSpace P]
    [CompactSpace P] [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    [OpensMeasurableSpace (P × E × ℝ)]
    (F : P → E → ℝ → P → ℝ) (sel : P → E → ℝ → P)
    (hF : Continuous (fun q : (P × E × ℝ) × P =>
      F q.1.1 q.1.2.1 q.1.2.2 q.2))
    (hsel_min : ∀ x g γ y, F x g γ (sel x g γ) ≤ F x g γ y)
    (hunique : ∀ x g γ z z',
      (∀ y, F x g γ z ≤ F x g γ y) →
      (∀ y, F x g γ z' ≤ F x g γ y) →
      z = z') :
    Measurable (fun p : P × E × ℝ => sel p.1 p.2.1 p.2.2) := by
  classical
  have hcont : Continuous (fun p : P × E × ℝ => sel p.1 p.2.1 p.2.2) := by
    refine continuous_argmin_of_compact_unique
      (P := P × E × ℝ) (K := P)
      (F := fun p z => F p.1 p.2.1 p.2.2 z)
      (sel := fun p => sel p.1 p.2.1 p.2.2) ?_ ?_ ?_
    · simpa using hF
    · intro p y
      exact hsel_min p.1 p.2.1 p.2.2 y
    · intro p z z' hz hz'
      exact hunique p.1 p.2.1 p.2.2 z z' hz hz'
  exact hcont.measurable



/-- A continuous real-valued function that is nonnegative on a dense subset is
nonnegative everywhere.

Layer: Glue | Gap: Level 1 (extend a closed-order inequality from a dense set)
Proof: close the image of the dense set under continuity and use that `Set.Ici 0`
  is closed in `ℝ`.
Source: Mathlib topology and closed-order APIs
Used in: stochastic mirror descent Bregman lower-bound boundary extension
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan stochastic mirror descent -/
theorem nonneg_of_continuousOn_of_dense_nonneg
    {α : Type*} [TopologicalSpace α]
    (D : α → ℝ) (s : Set α)
    (hcont : ContinuousOn D Set.univ)
    (hdense : Dense s)
    (hnonneg : Set.MapsTo D s (Set.Ici (0 : ℝ)))
    (a : α) :
    0 ≤ D a := by
  have hall :
      Set.MapsTo D (closure s) (closure (Set.Ici (0 : ℝ))) :=
    hnonneg.closure_of_continuousOn (by
      exact hcont.mono (by intro y hy; simp))
  have ha : a ∈ closure s := by
    rw [Dense.closure_eq hdense]
    simp
  have h := hall ha
  have hIci_closed : closure (Set.Ici (0 : ℝ)) = Set.Ici 0 := isClosed_Ici.closure_eq
  rw [hIci_closed] at h
  exact h

/-- Extend an order inequality from a dense set to all points using a continuous residual.

If the residual `f - g` is continuous on the whole space and `g x ≤ f x`
holds on a dense set, then `g a ≤ f a` holds at every point `a`.

Layer: Glue | Gap: Level 1 (dense-set closed-order inequality extension)
Proof: apply dense nonnegativity propagation to the continuous residual `f - g`,
  then convert nonnegativity of the residual back to `g a ≤ f a` using
  `sub_nonneg`.
Source: Mathlib dense-set topology and closed-order topology on `ℝ`
Used in: stochastic mirror descent residual lower-bound transfer from intrinsic
  closure to the full carrier
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem le_of_continuousOn_of_dense_le
    {α : Type*} [TopologicalSpace α]
    (f g : α → ℝ) (s : Set α)
    (hcont : ContinuousOn (fun x => f x - g x) Set.univ)
    (hdense : Dense s)
    (hle : ∀ x ∈ s, g x ≤ f x)
    (a : α) :
    g a ≤ f a := by
  exact sub_nonneg.mp (nonneg_of_continuousOn_of_dense_nonneg
    (D := fun x => f x - g x)
    (s := s)
    hcont
    hdense
    (by
      intro x hx
      exact sub_nonneg.mpr (hle x hx))
    a)

/-- A pointwise norm-difference estimate packages as a `LipschitzWith` bound.

If `f` satisfies `‖f x - f y‖ ≤ M * dist x y` for all points, then `f` is
`LipschitzWith (Real.toNNReal M)`.

Layer: Glue | Gap: Level 0 (pointwise Lipschitz packaging)
Proof: apply `LipschitzWith.of_dist_le'` and rewrite the codomain distance with
  `dist_eq_norm`.
Source: Mathlib metric Lipschitz maps and normed-group distance APIs
Used in: stochastic mirror descent conversion of pointwise prox stability into a
  reusable Lipschitz estimate
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem lipschitzWith_of_norm_sub_le_mul
    {P E : Type*} [PseudoMetricSpace P] [SeminormedAddCommGroup E]
    (f : P → E) (M : ℝ)
    (h : ∀ x y : P, ‖f x - f y‖ ≤ M * dist x y) :
    LipschitzWith (Real.toNNReal M) f := by
  refine LipschitzWith.of_dist_le' ?_
  intro x y
  simpa [dist_eq_norm] using h x y

/-- A continuous real-valued product map has measurable left sections.

For a jointly continuous observable `V` on `P × P`, fixing the right argument
`z` yields a measurable map `x ↦ V x z`.

Layer: Glue | Gap: Level 0 (continuous product left-section measurability)
Proof: Convert `ContinuousOn ... Set.univ` to global continuity, compose with
  the continuous section map `x ↦ (x, z)`, then use the Borel measurability API
  for continuous real-valued maps.
Source: Mathlib topology continuity and BorelSpace measurability APIs
Used in: stochastic mirror descent measurable objective sections for fixed prox
  centers
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem measurable_left_section_of_continuousOn_univ
    {P : Type*} [TopologicalSpace P] [MeasurableSpace P] [BorelSpace P]
    (V : P → P → ℝ)
    (hcont : ContinuousOn (fun p : P × P => V p.1 p.2) Set.univ)
    (z : P) :
    Measurable (fun x : P => V x z) := by
  have hV : Continuous (fun p : P × P => V p.1 p.2) :=
    continuousOn_univ.mp hcont
  exact (hV.comp (continuous_id.prodMk continuous_const)).measurable

/-- A real-valued observable is measurable after composition with a measurable random variable.

If `f : P → ℝ` is measurable and `X : Ω → P` is measurable, then the random
observable `fun ω => f (X ω)` is measurable.

Layer: Glue | Gap: Level 0 (measurable composition for real observables)
Proof: Direct application of Mathlib's measurable-function composition API via
  `hf.comp hX`.
Source: Mathlib measurable spaces and measurable function composition APIs
Used in: stochastic mirror descent measurability of the output objective
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem measurable_comp_real
    {Ω P : Type*} [MeasurableSpace Ω] [MeasurableSpace P]
    (f : P → ℝ) (X : Ω → P)
    (hf : Measurable f) (hX : Measurable X) :
    Measurable (fun ω => f (X ω)) := by
  exact hf.comp hX

/-- The start-point Bregman observable is measurable from a measurable iterate.

If the paired Bregman map is continuous on the full carrier product and the
iterate random variable is measurable, then `ω ↦ V (X ω) z` is measurable for
each fixed start point `z`.

Layer: Glue | Gap: Level 1 (Bregman start observable measurability)
Proof: specialize the continuous paired map to the left section at `z` using
  `measurable_left_section_of_continuousOn_univ`, then compose with the
  measurable iterate `X`.
Source: Mathlib Borel measurability of continuous maps and measurable
  composition APIs
Used in: stochastic mirror descent Bregman start random variable measurability
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem measurable_bregman_start_of_measurable_iterate
    {Ω P : Type*} [MeasurableSpace Ω]
    [TopologicalSpace P] [MeasurableSpace P] [BorelSpace P]
    (V : P → P → ℝ) (X : Ω → P) (z : P)
    (hV : ContinuousOn (fun p : P × P => V p.1 p.2) Set.univ)
    (hX : Measurable X) :
    Measurable (fun ω => V (X ω) z) := by
  exact (measurable_left_section_of_continuousOn_univ V hV z).comp hX

/-- A normalized positive finite weighted sum of feasible points stays feasible in a convex set.

Layer: Model | Gap: Level 0 (convex feasibility of averaged output)
Proof: rewrite the normalized sum as a finite convex combination with weights
  `W⁻¹ * w i`; use nonnegativity, normalization to one, and `Convex.sum_mem`.
Source: Mathlib convex sets and Finset weighted-sum APIs
Used in: stochastic mirror descent weighted averaged output feasibility
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem Convex.normalized_weighted_sum_mem
    {ι E : Type*} [AddCommGroup E] [Module ℝ E]
    {X : Set E} (hX : Convex ℝ X)
    (s : Finset ι) (w : ι → ℝ) (x : ι → E)
    (hW_pos : 0 < Finset.sum s w)
    (hw_nonneg : ∀ i ∈ s, 0 ≤ w i)
    (hx_mem : ∀ i ∈ s, x i ∈ X) :
    (Finset.sum s w)⁻¹ • Finset.sum s (fun i => w i • x i) ∈ X := by
  classical
  let W := Finset.sum s w
  have hWpos : 0 < W := by
    simpa [W] using hW_pos
  have hWne : W ≠ 0 := ne_of_gt hWpos
  have hsum_one : Finset.sum s (fun i => W⁻¹ * w i) = 1 := by
    calc
      Finset.sum s (fun i => W⁻¹ * w i) =
          W⁻¹ * Finset.sum s (fun i => w i) := by
        rw [Finset.mul_sum]
      _ = W⁻¹ * W := by
        simp [W]
      _ = 1 := by
        exact inv_mul_cancel₀ hWne
  have hweights_nonneg : ∀ i ∈ s, 0 ≤ W⁻¹ * w i := by
    intro i hi
    exact mul_nonneg (inv_nonneg.mpr (le_of_lt hWpos)) (hw_nonneg i hi)
  have hconv : Finset.sum s (fun i => (W⁻¹ * w i) • x i) ∈ X := by
    exact hX.sum_mem hweights_nonneg hsum_one hx_mem
  convert hconv using 1
  simp [W, Finset.smul_sum, smul_smul]

/-- A real-valued Lipschitz map on a measurable metric domain is measurable.

Layer: Glue | Gap: Level 0 (Lipschitz real map measurability)
Proof: `LipschitzWith.continuous` turns the Lipschitz bound into continuity,
  and `Continuous.measurable` gives measurability from the Borel structure.
Source: Mathlib Lipschitz continuity and Borel measurability APIs
Used in: stochastic mirror descent measurability of Lipschitz real-valued update maps
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem LipschitzWith.measurable
    {P : Type*} [PseudoMetricSpace P] [MeasurableSpace P] [OpensMeasurableSpace P]
    {K : NNReal} {f : P → ℝ}
    (hf : LipschitzWith K f) :
    Measurable f := by
  exact hf.continuous.measurable

/-- A subtype carrier function is continuous when it is induced by an ambient function continuous on the carrier.

If an ambient totalization `F : E → R` is continuous on `X` and agrees with
`f : {x // x ∈ X} → R` on subtype points, then `f` is continuous in the subtype
topology.

Layer: Glue | Gap: Level 0 (subtype continuity from ambient continuousOn)
Proof: compose `hF` with the continuous subtype projection using `Set.MapsTo`,
  convert continuity on `Set.univ` to continuity, and rewrite by pointwise
  agreement.
Source: Mathlib topology `ContinuousOn.comp`, subtype topology, and
  `continuousOn_univ` APIs
Used in: stochastic mirror descent carrier-restricted objective and prox
  continuity from ambient totalizations over the feasible set
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem continuous_subtype_of_continuousOn_ambient
    {E R : Type*} [TopologicalSpace E] [TopologicalSpace R]
    {X : Set E} (f : {x : E // x ∈ X} → R) (F : E → R)
    (hF : ContinuousOn F X)
    (h_eq : ∀ x : {x : E // x ∈ X}, F x.1 = f x) :
    Continuous f := by
  have hmaps :
      Set.MapsTo (fun x : {x : E // x ∈ X} => x.1) Set.univ X := by
    intro x _hx
    exact x.2
  have hcomp :
      ContinuousOn (fun x : {x : E // x ∈ X} => F x.1) Set.univ :=
    hF.comp continuous_subtype_val.continuousOn hmaps
  have hcomp' : Continuous (fun x : {x : E // x ∈ X} => F x.1) :=
    continuousOn_univ.mp hcomp
  rw [show f = fun x : {x : E // x ∈ X} => F x.1 by
    funext x
    exact (h_eq x).symm]
  exact hcomp'

/-- A subset is dense in the carrier subtype when the carrier lies in its closure.

If `U ⊆ X` and every point of `X` lies in `closure U`, then the subtype of
points of `X` whose underlying value lies in `U` is dense in the subtype carrier
over `X`.

Layer: Glue | Gap: Level 1 (dense subtype from ambient closure inclusion)
Proof: rewrite density in a subtype with `Subtype.dense_iff`; identify the
  subtype image of the restricted set with `U`, then apply the ambient closure
  hypothesis.
Source: Mathlib topology dense sets, closures, and subtype image APIs
Used in: stochastic mirror descent interior feasible-point approximation inside
  the constraint carrier
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic mirror descent -/
theorem dense_subtype_of_subset_closure
    {E : Type*} [TopologicalSpace E] {X U : Set E}
    (hUX : U ⊆ X) (hXdense : X ⊆ closure U) :
    Dense {x : {x : E // x ∈ X} | (x : E) ∈ U} := by
  rw [Subtype.dense_iff]
  intro x hx
  change (x : E) ∈ closure (((↑) : {x : E // x ∈ X} → E) ''
    {x : {x : E // x ∈ X} | (x : E) ∈ U})
  have hsubset : (x : E) ∈ closure U :=
    hXdense hx
  have himage :
      ((↑) : {x : E // x ∈ X} → E) ''
          {x : {x : E // x ∈ X} | (x : E) ∈ U} =
        U := by
    ext y
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact hu
    · intro hy
      exact ⟨⟨y, hUX hy⟩, hy, rfl⟩
  simpa [himage] using hsubset

/-- The closure of the intrinsic interior of a nonempty finite-dimensional convex set is
its intrinsic closure.

Layer: Glue | Gap: Level 1 (finite-dimensional relative-interior closure)
Proof: pass to the affine span as a chart, transport the set by
  `AffineIsometryEquiv.constVSub`, use the finite-dimensional convex theorem
  `closure_interior_eq_closure_of_nonempty_interior`, then return through the
  closed embedding of the affine span subtype.
Source: Mathlib convex geometry and finite-dimensional affine-subspace topology APIs
Used in: stochastic mirror descent feasible-region closure and relative-interior arguments
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic mirror descent -/
theorem closure_intrinsicInterior_eq_intrinsicClosure_of_nonempty_convex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {X : Set E} (hX_convex : Convex ℝ X) (hX_nonempty : X.Nonempty) :
    closure (intrinsicInterior ℝ X) = intrinsicClosure ℝ X := by
  rcases hX_nonempty with ⟨x0, hx0⟩
  let A : AffineSubspace ℝ E := affineSpan ℝ X
  haveI : Nonempty A := ⟨⟨x0, subset_affineSpan ℝ X hx0⟩⟩
  let p : A := ⟨x0, subset_affineSpan ℝ X hx0⟩
  let H : A.direction ≃ₜ A := (AffineIsometryEquiv.constVSub ℝ p).symm.toHomeomorph
  let T : Set A := ((↑) : A → E) ⁻¹' X
  let U : Set A.direction := H ⁻¹' T
  have hUconv : Convex ℝ U := by
    simpa [A, T, U, H, p] using
      hX_convex.affine_preimage
        ((A.subtype).comp
          (AffineIsometryEquiv.constVSub ℝ p).symm.toAffineEquiv.toAffineMap)
  have himageU : H '' U = T := by
    ext a
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact hu
    · intro ha
      refine ⟨H.symm a, ?_, ?_⟩
      · simpa [U]
      · exact H.apply_symm_apply a
  have hT_int_nonempty : (interior T).Nonempty := by
    have hIi : (intrinsicInterior ℝ X).Nonempty :=
      Set.Nonempty.intrinsicInterior hX_convex ⟨x0, hx0⟩
    simpa [intrinsicInterior, A, T, Set.image_nonempty] using hIi
  have hT_int_eq : interior T = H '' interior U := by
    rw [← himageU, ← H.image_interior U]
  have hU_int_nonempty : (interior U).Nonempty := by
    rw [hT_int_eq] at hT_int_nonempty
    simpa [Set.image_nonempty] using hT_int_nonempty
  have hTclosure : closure (interior T) = closure T := by
    calc
      closure (interior T) = closure (H '' interior U) := by rw [hT_int_eq]
      _ = H '' closure (interior U) := by
            exact (H.image_closure (interior U)).symm
      _ = H '' closure U := by
            rw [hUconv.closure_interior_eq_closure_of_nonempty_interior hU_int_nonempty]
      _ = closure (H '' U) := by
            exact H.image_closure U
      _ = closure T := by
            rw [himageU]
  have hclosedEmbedding :
      IsClosedEmbedding ((↑) : A → E) :=
    (affineSpan ℝ X).closed_of_finiteDimensional.isClosedEmbedding_subtypeVal
  calc
    closure (intrinsicInterior ℝ X)
        = closure (((↑) : A → E) '' interior T) := by
          simp [intrinsicInterior, A, T]
    _ = ((↑) : A → E) '' closure (interior T) := by
          exact hclosedEmbedding.closure_image_eq (interior T)
    _ = ((↑) : A → E) '' closure T := by rw [hTclosure]
    _ = intrinsicClosure ℝ X := by
          simp [intrinsicClosure, A, T]

/-- A nonempty finite-dimensional convex feasible set lies in the closure of its intrinsic interior.

For a convex set `X` in a finite-dimensional real normed space, every point of
`X` belongs to `closure (intrinsicInterior ℝ X)` when `X` is nonempty.

Layer: Glue | Gap: Level 1 (convex intrinsic-interior closure containment)
Proof: rewrite the closure of the intrinsic interior as the intrinsic closure
  using `closure_intrinsicInterior_eq_intrinsicClosure_of_nonempty_convex`, then
  apply the canonical inclusion `subset_intrinsicClosure`.
Source: Mathlib convex analysis APIs for intrinsic interior and intrinsic closure
Used in: stochastic mirror descent feasible-set closure argument for prox-step existence
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic mirror descent -/
theorem subset_closure_intrinsicInterior_of_nonempty_convex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {X : Set E} (hX_convex : Convex ℝ X) (hX_nonempty : X.Nonempty) :
    X ⊆ closure (intrinsicInterior ℝ X) := by
  intro x hx
  rw [closure_intrinsicInterior_eq_intrinsicClosure_of_nonempty_convex
    hX_convex hX_nonempty]
  exact subset_intrinsicClosure (𝕜 := ℝ) (s := X) hx

/-- A closed convex set with nonempty interior lies in the closure of its interior.

If a convex feasible region `X` is closed and has nonempty topological interior,
then every feasible point is approximable by interior feasible points.

Layer: Glue | Gap: Level 1 (closed convex full-dimensional interior closure)
Proof: Mathlib's convex-analysis lemma identifies `closure (interior X)` with
  `closure X` under nonempty interior; closedness rewrites `closure X` to `X`,
  and `subset_closure` supplies membership in the closure.
Source: Mathlib convex analysis and topological closure APIs
Used in: stochastic mirror descent feasibility arguments moving from boundary
  points to interior approximations
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem subset_closure_interior_of_closed_convex_nonempty_interior
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {X : Set E} (hX_closed : IsClosed X) (hX_convex : Convex ℝ X)
    (hXint : (interior X).Nonempty) :
    X ⊆ closure (interior X) := by
  intro x hx
  have hclosure :
      closure (interior X) = closure X :=
    hX_convex.closure_interior_eq_closure_of_nonempty_interior hXint
  have hxclosure : x ∈ closure X := subset_closure hx
  simpa [hclosure, hX_closed.closure_eq] using hxclosure

/-- A continuous real-valued function on a compact product carrier has a finite
uniform absolute bound.

For a jointly continuous Bregman-type kernel `D` on the full product carrier,
compactness gives a maximum of `‖D x z‖`, yielding a global nonnegative bound.

Layer: Model | Gap: Level 1 (compact absolute bound for Bregman kernels)
Proof: apply continuity of the norm to the jointly continuous kernel, then use
  `IsCompact.exists_isMaxOn` on the compact product carrier; the empty-carrier
  case is discharged vacuously.
Source: Mathlib compactness, continuous-on norm, and extrema APIs
Used in: stochastic mirror descent Bregman prox-step boundedness audit
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem exists_abs_bound_on_compact_product_of_continuousOn
    {P : Type*} [TopologicalSpace P] (D : P → P → ℝ)
    (hcompact : IsCompact (Set.univ : Set (P × P)))
    (hcont : ContinuousOn (fun p : P × P => D p.1 p.2) Set.univ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x z : P, ‖D x z‖ ≤ C := by
  by_cases hP : Nonempty P
  · have hne : (Set.univ : Set (P × P)).Nonempty :=
      ⟨(Classical.choice hP, Classical.choice hP), by simp⟩
    have hnorm :
        ContinuousOn (fun p : P × P => ‖D p.1 p.2‖) Set.univ :=
      hcont.norm
    rcases hcompact.exists_isMaxOn hne hnorm with ⟨p, _hp, hpmax⟩
    refine ⟨‖D p.1 p.2‖, norm_nonneg _, ?_⟩
    intro x z
    exact (isMaxOn_iff.mp hpmax) (x, z) (by simp)
  · refine ⟨0, le_rfl, ?_⟩
    intro x _z
    exact (hP ⟨x⟩).elim

/-- A Lipschitz real function over a bounded evaluated carrier has a uniform absolute
bound.

If the image of `eval` is bounded and `f` is Lipschitz with respect to `eval`
with nonnegative constant `M`, then `‖f x‖` is bounded uniformly over all `x`.

Layer: Glue | Gap: Level 1 (bounded Lipschitz image estimate)
Proof: choose a closed ball around `eval x0` from `Metric.isBounded_iff_subset_closedBall`,
  then combine the Lipschitz estimate with the triangle inequality for `f x =
  (f x - f x0) + f x0` and linear arithmetic.
Source: Mathlib metric bounded sets and normed-group triangle inequalities
Used in: stochastic mirror descent bounded-domain Lipschitz objective estimates
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem exists_bound_of_bounded_lipschitzOn_real
    {P E : Type*} [NormedAddCommGroup E]
    (f : P → ℝ) (eval : P → E) (x0 : P) (M : ℝ)
    (hM_nonneg : 0 ≤ M)
    (hbounded : Bornology.IsBounded (Set.range eval))
    (hLip : ∀ x y : P, ‖f x - f y‖ ≤ M * ‖eval x - eval y‖) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : P, ‖f x‖ ≤ C := by
  rcases (Metric.isBounded_iff_subset_closedBall (eval x0)).1 hbounded with
    ⟨R, hR⟩
  refine ⟨M * |R| + ‖f x0‖, ?_, ?_⟩
  · exact add_nonneg (mul_nonneg hM_nonneg (abs_nonneg R)) (norm_nonneg _)
  · intro x
    have hxR : dist (eval x) (eval x0) ≤ R := hR ⟨x, rfl⟩
    have hxR_abs : ‖eval x - eval x0‖ ≤ |R| := by
      have hdist_abs : dist (eval x) (eval x0) ≤ |R| :=
        hxR.trans (le_abs_self R)
      simpa [dist_eq_norm] using hdist_abs
    have hfxy : ‖f x - f x0‖ ≤ M * ‖eval x - eval x0‖ :=
      hLip x x0
    have hMdist : M * ‖eval x - eval x0‖ ≤ M * |R| :=
      mul_le_mul_of_nonneg_left hxR_abs hM_nonneg
    have hsplit : ‖f x‖ ≤ ‖f x - f x0‖ + ‖f x0‖ := by
      have hdecomp : f x = (f x - f x0) + f x0 := by
        ring
      calc
        ‖f x‖ = ‖(f x - f x0) + f x0‖ := by
          exact congrArg norm hdecomp
        _ ≤ ‖f x - f x0‖ + ‖f x0‖ :=
          norm_add_le (f x - f x0) (f x0)
    linarith

/-- A declared pair maximizing a real-valued pair function yields an attained maximum witness.

Given a candidate `pmax` whose value dominates every pair, this lemma packages
`pmax` as the existential attaining maximizer.

Layer: Model | Gap: Level 0 (declared pair maximizer witness packaging)
Proof: direct existential introduction with the declared maximizer and its
  universal dominance certificate.
Source: Mathlib logic, product type, and existential quantifier APIs
Used in: stochastic mirror descent Bregman diameter maximum over carrier pairs
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem exists_max_pair_of_declared_maximizer
    {P : Type*} (V : P → P → ℝ) (pmax : P × P)
    (hmax : ∀ q : P × P, V q.1 q.2 ≤ V pmax.1 pmax.2) :
    ∃ p : P × P, ∀ q : P × P, V q.1 q.2 ≤ V p.1 p.2 := by
  exact ⟨pmax, hmax⟩

/-- A continuous real-valued function on a compact set has a finite nonnegative
uniform bound on its norm.

Layer: Glue | Gap: Level 1 (compact continuous norm bound)
Proof: apply the extreme-value theorem to `fun x => ‖f x‖` on the nonempty
  compact set using `ContinuousOn.norm`; the empty-set case is vacuous.
Source: Mathlib compactness, continuous-on norm, and extreme-value APIs
Used in: stochastic mirror descent compact prox-step absolute-bound estimates
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic mirror descent -/
theorem exists_nonneg_norm_bound_of_isCompact_of_continuousOn
    {α : Type*} [TopologicalSpace α] {s : Set α} (f : α → ℝ)
    (hcompact : IsCompact s) (hcont : ContinuousOn f s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : α, x ∈ s → ‖f x‖ ≤ C := by
  by_cases hne : s.Nonempty
  · have hnorm : ContinuousOn (fun x : α => ‖f x‖) s := hcont.norm
    rcases hcompact.exists_isMaxOn hne hnorm with ⟨p, _hp, hpmax⟩
    refine ⟨‖f p‖, norm_nonneg _, ?_⟩
    intro x hx
    exact (isMaxOn_iff.mp hpmax) x hx
  · refine ⟨0, le_rfl, ?_⟩
    intro x hx
    exact (hne ⟨x, hx⟩).elim

/-- Agreement on feasible displacement inner products at an interior point extends to every direction.

If `x` is in the interior of a feasible set `X` and two vectors `a` and `b`
have equal inner products against every feasible displacement `z - x`, then
their inner products agree against any direction `y`.

Layer: Glue | Gap: Level 1 (interior small-step displacement cancellation)
Proof: choose a positive scalar `t` small enough that `x + t • y` stays in `X`
  using the metric-neighborhood characterization of interior, apply the
  displacement hypothesis to `t • y`, rewrite by inner-product scalar
  linearity, and cancel `t`.
Source: Mathlib metric neighborhoods, interior of sets, and inner product
  scalar-linearity APIs
Used in: stochastic mirror descent first-order optimality reduction from
  feasible displacements to arbitrary search directions
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem inner_eq_of_eq_on_displacements_of_mem_interior
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X : Set E} {x a b : E} (hx : x ∈ interior X)
    (hdisplacement : ∀ z : E, z ∈ X → ⟪a, z - x⟫_ℝ = ⟪b, z - x⟫_ℝ)
    (y : E) :
    ⟪a, y⟫_ℝ = ⟪b, y⟫_ℝ := by
  have hx_mem : interior X ∈ 𝓝 x := IsOpen.mem_nhds isOpen_interior hx
  rcases Metric.mem_nhds_iff.1 hx_mem with ⟨ε, hεpos, hεsub⟩
  let t : ℝ := ε / (2 * (‖y‖ + 1))
  have htpos : 0 < t := by
    unfold t
    positivity
  have hmul_lt : t * ‖y‖ < ε := by
    have hden_pos : 0 < 2 * (‖y‖ + 1) := by
      positivity
    have hnorm_lt : ‖y‖ < 2 * (‖y‖ + 1) := by
      nlinarith [norm_nonneg y]
    unfold t
    rw [div_mul_eq_mul_div]
    rw [div_lt_iff₀ hden_pos]
    nlinarith [hεpos, hnorm_lt]
  have hzmem : x + t • y ∈ X := by
    have hball : x + t • y ∈ interior X := by
      apply hεsub
      rw [Metric.mem_ball, dist_eq_norm]
      have hdist_eq : ‖x + t • y - x‖ = t * ‖y‖ := by
        calc
          ‖x + t • y - x‖ = ‖t • y‖ := by abel
          _ = ‖t‖ * ‖y‖ := by rw [norm_smul]
          _ = |t| * ‖y‖ := by simp [Real.norm_eq_abs]
          _ = t * ‖y‖ := by rw [abs_of_pos htpos]
      rw [hdist_eq]
      exact hmul_lt
    exact interior_subset hball
  have hinner : ⟪a, (x + t • y) - x⟫_ℝ = ⟪b, (x + t • y) - x⟫_ℝ :=
    hdisplacement (x + t • y) hzmem
  have hscaled : t * ⟪a, y⟫_ℝ = t * ⟪b, y⟫_ℝ := by
    have hdisp : x + t • y - x = t • y := by
      abel
    simpa [hdisp, inner_smul_right, mul_comm, mul_left_comm, mul_assoc] using hinner
  exact mul_left_cancel₀ (ne_of_gt htpos) hscaled

/-- The positive natural ceiling of a three-way maximum is at most the sum plus two.

For nonnegative real requirements `a`, `b`, and `c`, the natural selector
`max 1 (Nat.ceil (max (max a b) c))` is bounded above by the additive budget
`a + b + c + 2` after coercion back to `ℝ`.

Layer: Glue | Gap: Level 0 (three-way ceiling maximum upper bound)
Proof: bound the `max 1` totalization by one successor above `Nat.ceil`, use the standard `Nat.ceil_lt_add_one` estimate on a nonnegative maximum, and compare the maximum with the sum using nonnegativity.
Source: Mathlib real Archimedean ceiling and lattice-order APIs
Used in: two-phase randomized stochastic mirror descent per-run SFO budget asymptotic upper bound
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/parameters
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, nonconvex stochastic mirror descent -/
theorem natCast_max_one_ceil_max3_le_sum_add_two
    (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    ((max 1 (Nat.ceil (max (max a b) c)) : ℕ) : ℝ) ≤ a + b + c + 2 := by
  let m : ℝ := max (max a b) c
  have hm_nonneg : 0 ≤ m := by
    dsimp [m]
    exact le_trans ha (le_trans (le_max_left a b) (le_max_left (max a b) c))
  have hceil : (Nat.ceil m : ℝ) ≤ m + 1 :=
    le_of_lt (Nat.ceil_lt_add_one hm_nonneg)
  have hchoice :
      ((max 1 (Nat.ceil m) : ℕ) : ℝ) ≤ (Nat.ceil m : ℝ) + 1 := by
    exact_mod_cast
      (max_le (Nat.succ_le_succ (Nat.zero_le (Nat.ceil m)))
        (Nat.le_succ (Nat.ceil m)))
  have hm_le_sum : m ≤ a + b + c := by
    dsimp [m]
    exact max_le
      (max_le (by nlinarith [hb, hc])
        (by nlinarith [ha, hc]))
      (by nlinarith [ha, hb])
  calc
    ((max 1 (Nat.ceil m) : ℕ) : ℝ) ≤ (Nat.ceil m : ℝ) + 1 := hchoice
    _ ≤ m + 2 := by linarith
    _ ≤ a + b + c + 2 := by linarith

open MeasureTheory

namespace ConvexOn

/-- Convex sublevel sets are null-measurable for finite-dimensional Haar volume.

For a real-valued function convex on `X`, the restricted sublevel
`{x | x ∈ X ∧ f x ≤ r}` is a convex subset of the ambient finite-dimensional
real normed space, hence null-measurable for additive Haar volume.

Layer: Glue | Gap: Level 1 (convex sublevel Haar null-measurability)
Proof: `ConvexOn.convex_le` turns the restricted sublevel into a convex set;
  Mathlib's finite-dimensional convex-measure API supplies null-measurability
  for convex subsets with respect to Haar volume.
Source: Mathlib convex analysis and additive Haar measure APIs for finite-dimensional real normed spaces
Used in: nonconvex stochastic mirror descent simple convex term sublevel regularity
Book citation: book/FOML/StochasticMirrorDescent.json#/setup/variable_space/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, randomized stochastic mirror descent -/
theorem sublevel_nullMeasurableSet_volume
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [MeasureTheory.Measure.IsAddHaarMeasure μ]
    {X : Set E} {f : E → ℝ} (hf : ConvexOn ℝ X f) (r : ℝ) :
    NullMeasurableSet {x : E | x ∈ X ∧ f x ≤ r} μ := by
  simpa using (hf.convex_le r).nullMeasurableSet μ

end ConvexOn

/-- A base-two logarithmic confidence ceiling is bounded by three log factors.

If `Λ` is a positive failure probability at most one half, then the ceiling of
`log₂ (2 / Λ)` is controlled by three times `log₂ (1 / Λ)`.

Layer: Glue | Gap: Level 0 (base-two logarithmic ceiling bound)
Proof: compare `log₂ (2 / Λ)` with `1 + log₂ (1 / Λ)` using `Real.log_mul`,
  bound `Nat.ceil x` by `x + 1`, and use `1 ≤ log₂ (1 / Λ)`.
Source: Mathlib real logarithm, natural ceiling, and ordered-field arithmetic APIs
Used in: two-phase randomized stochastic mirror descent independent run-count
  bound inside the Theorem 6.7 SFO-call rate calculation
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec/parameters
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, two-phase randomized stochastic mirror descent -/
theorem ceil_log_two_div_le_three_log_one_div_over_log_two
    (Λ : ℝ) (hΛ_pos : 0 < Λ) (hΛ_half : Λ ≤ 1 / 2) :
    (Nat.ceil (Real.log (2 / Λ) / Real.log 2) : ℝ) ≤
      3 * (Real.log (1 / Λ) / Real.log 2) := by
  let l : ℝ := Real.log (1 / Λ) / Real.log 2
  let x : ℝ := Real.log (2 / Λ) / Real.log 2
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog2_ne : Real.log 2 ≠ 0 := ne_of_gt hlog2_pos
  have hΛ_ne : Λ ≠ 0 := ne_of_gt hΛ_pos
  have hl_ge_one : 1 ≤ l := by
    have harg_ge : (2 : ℝ) ≤ 1 / Λ := by
      field_simp [hΛ_ne]
      nlinarith
    have hlog_le : Real.log 2 ≤ Real.log (1 / Λ) := by
      exact Real.log_le_log (by norm_num) harg_ge
    rw [le_div_iff₀ hlog2_pos]
    simpa [l] using hlog_le
  have hx_nonneg : 0 ≤ x := by
    have hx_arg : 1 ≤ 2 / Λ := by
      field_simp [hΛ_ne]
      nlinarith
    have hx_log_nonneg : 0 ≤ Real.log (2 / Λ) := by
      simpa using Real.log_nonneg hx_arg
    exact div_nonneg hx_log_nonneg (le_of_lt hlog2_pos)
  have hceil : (Nat.ceil x : ℝ) ≤ x + 1 :=
    le_of_lt (Nat.ceil_lt_add_one hx_nonneg)
  have hx_eq : x = 1 + l := by
    dsimp [x, l]
    have htwo_div : 2 / Λ = (2 : ℝ) * (1 / Λ) := by ring
    rw [htwo_div]
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (one_div_ne_zero hΛ_ne)]
    field_simp [hlog2_ne]
  calc
    (Nat.ceil (Real.log (2 / Λ) / Real.log 2) : ℝ) = (Nat.ceil x : ℝ) := by rfl
    _ ≤ x + 1 := hceil
    _ = l + 2 := by rw [hx_eq]; ring
    _ ≤ 3 * l := by nlinarith

/-- A nonnegative real quantity is bounded by a positive multiple of any positive rate.

This packages the elementary domination step used when a pointwise finite cost
must be compared with a strictly positive asymptotic rate at fixed parameters.

Layer: Glue | Gap: Level 0 (positive scalar domination of nonnegative quantities)
Proof: choose `(M + 1) / R` as the constant; positivity follows from `M ≥ 0`
  and `R > 0`, and cancellation reduces the bound to `M ≤ M + 1`.
Source: Mathlib ordered-field arithmetic over the real numbers
Used in: nonconvex stochastic mirror descent Theorem 6.7 SFO call bound pointwise rate packaging
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/convergence_results
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
theorem exists_pos_const_mul_ge_of_nonneg_of_pos
    (M R : ℝ) (hM_nonneg : 0 ≤ M) (hR_pos : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ M ≤ C * R := by
  refine ⟨(M + 1) / R, ?_, ?_⟩
  · exact div_pos (by linarith) hR_pos
  · rw [div_mul_cancel₀ _ (ne_of_gt hR_pos)]
    linarith

/-- A positive number at most one half has base-two reciprocal logarithm at least one.

If `Λ` is a positive failure probability bounded by `1 / 2`, then
`log₂ (1 / Λ)` is at least `1`.

Layer: Glue | Gap: Level 0 (base-two reciprocal logarithm lower bound)
Proof: convert `Λ ≤ 1 / 2` into `2 ≤ 1 / Λ`, apply monotonicity of the real
  logarithm, and divide by the positive constant `log 2`.
Source: Mathlib real logarithm monotonicity and ordered-field arithmetic APIs
Used in: two-phase randomized stochastic mirror descent SFO-call rate
  calculation for lower-bounding the confidence logarithm
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec/parameters
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, two-phase randomized stochastic mirror descent -/
theorem one_le_log_one_div_over_log_two_of_pos_le_half
    (Λ : ℝ) (hΛ_pos : 0 < Λ) (hΛ_half : Λ ≤ 1 / 2) :
    1 ≤ Real.log (1 / Λ) / Real.log 2 := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have harg_ge : (2 : ℝ) ≤ 1 / Λ := by
    field_simp [ne_of_gt hΛ_pos]
    nlinarith
  have hlog_le : Real.log 2 ≤ Real.log (1 / Λ) := by
    exact Real.log_le_log (by norm_num) harg_ge
  rw [le_div_iff₀ hlog2_pos]
  simpa using hlog_le

/-- The positive natural ceiling of a nonnegative real is at most that real plus two.

For a nonnegative real requirement `y`, the totalized natural selector
`max 1 (Nat.ceil y)` overshoots `y` by at most two after coercion back to `ℝ`.

Layer: Glue | Gap: Level 0 (positive ceiling upper bound)
Proof: bound the `max 1` totalization by one successor above `Nat.ceil`, then
  apply `Nat.ceil_lt_add_one` for nonnegative reals and combine the two one-unit
  overshoot estimates.
Source: Mathlib real Archimedean ceiling and natural-number lattice-order APIs
Used in: two-phase randomized stochastic mirror descent validation sample count
  asymptotic upper bound
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/parameters
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
theorem natCast_max_one_ceil_le_add_two (y : ℝ) (hy : 0 ≤ y) :
    ((max 1 (Nat.ceil y) : ℕ) : ℝ) ≤ y + 2 := by
  have hceil : (Nat.ceil y : ℝ) ≤ y + 1 :=
    le_of_lt (Nat.ceil_lt_add_one hy)
  have hchoice :
      ((max 1 (Nat.ceil y) : ℕ) : ℝ) ≤ (Nat.ceil y : ℝ) + 1 := by
    exact_mod_cast
      (max_le (Nat.succ_le_succ (Nat.zero_le (Nat.ceil y)))
        (Nat.le_succ (Nat.ceil y)))
  linarith

namespace PiLp

/-- Coordinatewise closed carriers define a closed subset of a dependent `PiLp` product.

If every coordinate carrier `X i` is closed, then the set of `PiLp` points whose
`i`th coordinate lies in `X i` for every `i` is closed.

Layer: Glue | Gap: Level 0 (PiLp coordinatewise closed carrier)
Proof: identify the coordinatewise carrier with an indexed intersection of
  closed preimages under the continuous coordinate-evaluation maps.
Source: Mathlib product topology, `PiLp` coordinate continuity, and closed
  indexed-intersection APIs
Used in: stochastic block mirror descent closedness of the product feasible
  set from closed block feasible carriers
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem isClosed_set_pi
    {ι : Type*} {p : ℝ≥0∞} {E : ι → Type*} [∀ i, TopologicalSpace (E i)]
    (X : ∀ i, Set (E i)) (hX : ∀ i, IsClosed (X i)) :
    IsClosed {x : PiLp p E | ∀ i, x i ∈ X i} := by
  rw [show {x : PiLp p E | ∀ i, x i ∈ X i} =
      ⋂ i, {x : PiLp p E | x i ∈ X i} by
    ext x
    simp]
  exact isClosed_iInter fun i =>
    (hX i).preimage (PiLp.continuous_apply (p := p) (β := E) i)

/-- Coordinatewise convex carriers define a convex subset of a dependent `PiLp` product.

If every coordinate carrier `X i` is convex, then the set of `PiLp` points whose
`i`th coordinate lies in `X i` for every `i` is convex.

Layer: Glue | Gap: Level 0 (PiLp coordinatewise convex carrier)
Proof: unpack the convexity goal, rewrite coordinate evaluation of addition
  and scalar multiplication in `PiLp`, and apply the coordinate convexity
  hypothesis.
Source: Mathlib convex sets and `PiLp` coordinate operation APIs
Used in: stochastic block mirror descent convexity of the product feasible
  set from convex block feasible carriers
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem convex_set_pi
    {𝕜 : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
    {ι : Type*} {p : ℝ≥0∞} {E : ι → Type*}
    [∀ i, SeminormedAddCommGroup (E i)] [∀ i, SMul 𝕜 (E i)]
    (X : ∀ i, Set (E i)) (hX : ∀ i, Convex 𝕜 (X i)) :
    Convex 𝕜 {x : PiLp p E | ∀ i, x i ∈ X i} := by
  intro x hx y hy a b ha hb hab i
  simpa using hX i (hx i) (hy i) ha hb hab

end PiLp

/-- A gauge-strongly-convex function transfers to its carrier restriction.

If a carrier-local function agrees with an enclosing-space function on every
point of a convex carrier, then the enclosing function's gauge-relative Jensen
strong-convexity inequality gives the same inequality for subtype endpoints.

Layer: Glue | Gap: Level 1 (subtype transport for gauge strong convexity)
Proof: specialize the gauge strong-convexity inequality at the subtype
  endpoints, construct the convex-combination subtype point by convexity, and
  rewrite the three carrier-local function values using the equality bridge.
Source: Mathlib convex analysis APIs for convex sets and Jensen-style strong
  convexity
Used in: stochastic block mirror descent restricted block distance-generator
  strong convexity from an enclosing-space realization
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/assumptions/3/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem strongConvexOnWithGauge_subtype_restrict_of_eqOn
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {X : Set E} {mu : ℝ} {rho : E → ℝ} {f : E → ℝ}
    {fc : {x : E // x ∈ X} → ℝ}
    (hX : Convex ℝ X)
    (hf : StrongConvexOnWithGauge X mu rho f)
    (hfc : ∀ x : {x : E // x ∈ X}, fc x = f x.1) :
    ∀ ⦃x : {u : E // u ∈ X}⦄,
      ∀ ⦃y : {u : E // u ∈ X}⦄,
      ∀ ⦃a b : ℝ⦄, (ha : 0 ≤ a) → (hb : 0 ≤ b) → (hab : a + b = 1) →
        fc ⟨a • x.1 + b • y.1, hX x.2 y.2 ha hb hab⟩ ≤
          a * fc x + b * fc y - mu / 2 * a * b * (rho (x.1 - y.1)) ^ 2 := by
  intro x y a b ha hb hab
  have h :=
    hf x.2 y.2 ha hb hab
  rw [hfc ⟨a • x.1 + b • y.1, hX x.2 y.2 ha hb hab⟩,
    hfc x, hfc y]
  exact h

/-- A closed bounded subset of a proper metric space has compact subtype universe.

This repackages ambient compactness of a closed bounded carrier as compactness
of the subtype used for constrained optimization over that carrier.

Layer: Glue | Gap: Level 0 (closed bounded carrier subtype compactness)
Proof: use Mathlib's closed-and-bounded compactness theorem in a proper metric
  space, then transfer compactness through the subtype coercion image.
Source: Mathlib proper metric spaces and subtype compactness APIs
Used in: stochastic block mirror descent compact block feasible carrier for
  block mirror-prox argmin selection
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem isCompact_univ_subtype_of_isClosed_isBounded
    {E : Type*} [PseudoMetricSpace E] [ProperSpace E] {X : Set E}
    (hclosed : IsClosed X) (hbounded : Bornology.IsBounded X) :
    IsCompact (Set.univ : Set X) := by
  rw [Subtype.isCompact_iff]
  simpa using (Metric.isCompact_of_isClosed_isBounded hclosed hbounded)

namespace Module.Basis

/-- A coordinate functional of a basis on a finite-dimensional normed space is
bounded by the ambient norm.

For any basis `b` and index `i`, there is a positive constant `C` such that
the norm of the `i`th coordinate of every vector is at most
`C * ‖x‖`.

Layer: Glue | Gap: Level 1 (finite-dimensional basis-coordinate norm control)
Proof: finite-dimensionality makes the coordinate linear map continuous; the
  continuous linear-map boundedness API gives an operator bound.
Source: Mathlib finite-dimensional normed-space and continuous linear-map APIs
Used in: stochastic block mirror descent finite block coordinate estimates inside seminorm control
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic block mirror descent -/
theorem exists_norm_coord_le_mul_norm_of_finiteDimensional
    {𝕜 ι E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace 𝕜]
    [FiniteDimensional 𝕜 E] (b : Basis ι 𝕜 E) (i : ι) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : E, ‖b.coord i x‖ ≤ C * ‖x‖ := by
  have hcont : Continuous (b.coord i : E → 𝕜) :=
    LinearMap.continuous_of_finiteDimensional (b.coord i)
  rcases SemilinearMapClass.bound_of_continuous (b.coord i) hcont with
    ⟨C, hCpos, hC⟩
  refine ⟨C, hCpos, ?_⟩
  intro x
  simpa using hC x

end Module.Basis

namespace Seminorm

/-- On a finite-dimensional normed vector space, every seminorm is bounded by
the ambient norm.

For a seminorm `p`, there is a nonnegative constant `K` such that
`p x ≤ K * ‖x‖` for every vector `x`.

Layer: Glue | Gap: Level 1 (finite-dimensional seminorm norm control)
Proof: expand each vector in a finite basis, bound each coordinate functional
  by finite-dimensional linear-map continuity, then sum the seminorm triangle
  inequalities and homogeneous coordinate bounds.
Source: Mathlib seminorm API and finite-dimensional continuous linear-map theory
Used in: stochastic block mirror descent finite block seminorm continuity and dual unit-ball support bounds
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic block mirror descent -/
theorem exists_bound_by_norm_of_finiteDimensional
    {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace 𝕜]
    [FiniteDimensional 𝕜 E]
    (p : Seminorm 𝕜 E) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : E, p x ≤ K * ‖x‖ := by
  classical
  let b := Module.finBasis 𝕜 E
  have hcoord :
      ∀ i, ∃ C : ℝ, 0 < C ∧ ∀ x : E, ‖b.equivFun x i‖ ≤ C * ‖x‖ := by
    intro i
    have hcont : Continuous (b.coord i : E → 𝕜) :=
      LinearMap.continuous_of_finiteDimensional (b.coord i)
    rcases SemilinearMapClass.bound_of_continuous (b.coord i) hcont with
      ⟨C, hCpos, hC⟩
    refine ⟨C, hCpos, ?_⟩
    intro x
    change ‖b.coord i x‖ ≤ C * ‖x‖
    simpa using hC x
  choose C hCpos hCbound using hcoord
  refine ⟨∑ i, C i * p (b i), ?_, ?_⟩
  · exact Finset.sum_nonneg (fun i _ =>
      mul_nonneg (le_of_lt (hCpos i)) (apply_nonneg p (b i)))
  · intro x
    have hsum :
        p (∑ i, b.equivFun x i • b i) ≤
          ∑ i, p (b.equivFun x i • b i) := by
      refine Finset.induction_on Finset.univ ?_ ?_
      · simp
      · intro a s ha ih
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        exact (map_add_le_add p _ _).trans (add_le_add le_rfl ih)
    have hterms :
        (∑ i, p (b.equivFun x i • b i)) ≤
          ∑ i, (C i * ‖x‖) * p (b i) := by
      refine Finset.sum_le_sum ?_
      intro i _
      have hi := hCbound i x
      have hmul := mul_le_mul_of_nonneg_right hi (apply_nonneg p (b i))
      simpa [map_smul_eq_mul, mul_assoc] using hmul
    calc
      p x = p (∑ i, b.equivFun x i • b i) := by rw [b.sum_equivFun x]
      _ ≤ ∑ i, p (b.equivFun x i • b i) := hsum
      _ ≤ ∑ i, (C i * ‖x‖) * p (b i) := hterms
      _ = (∑ i, C i * p (b i)) * ‖x‖ := by
        simp_rw [mul_assoc, mul_comm ‖x‖, ← mul_assoc]
        rw [Finset.sum_mul]

/-- A continuous separating seminorm has a positive lower bound on the ambient unit sphere.

On a proper real normed vector space, the ambient unit sphere is compact and
nonempty when the space is nontrivial. If a seminorm has trivial kernel and is
continuous on that sphere, its compact minimum is strictly positive.

Layer: Glue | Gap: Level 1 (positive compact-sphere lower bound for separating seminorms)
Proof: choose a normalized nonzero vector to witness nonemptiness of the unit
  sphere, minimize the seminorm on the compact sphere, and use separation to
  rule out a zero minimum.
Source: Mathlib seminorm API, proper metric compact-sphere API, and compact
  extreme-value theorem
Used in: stochastic block mirror descent derivation of ambient norm control from
  block primal seminorm separation
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic block mirror descent -/
theorem exists_pos_le_on_unit_sphere_of_separating
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E] [Nontrivial E]
    (p : Seminorm ℝ E) (hp : p.IsSeparating)
    (hcont : ContinuousOn p (Metric.sphere (0 : E) 1)) :
    ∃ c : ℝ, 0 < c ∧ ∀ y : E, ‖y‖ = 1 → c ≤ p y := by
  classical
  let s : Set E := Metric.sphere (0 : E) 1
  have hscompact : IsCompact s := isCompact_sphere (0 : E) 1
  rcases exists_ne (0 : E) with ⟨z, hz⟩
  let y : E := (‖z‖)⁻¹ • z
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hys : y ∈ s := by
    simp [s, y, norm_smul, hzpos.ne']
  rcases hscompact.exists_isMinOn ⟨y, hys⟩ hcont with
    ⟨ymin, hymin_s, hymin⟩
  refine ⟨p ymin, ?_, ?_⟩
  · have hymin_norm : ‖ymin‖ = 1 := by
      simpa [s, Metric.mem_sphere, dist_eq_norm] using hymin_s
    have hymin_ne : ymin ≠ 0 := by
      intro hzero
      simp [hzero] at hymin_norm
    have hp_ne : p ymin ≠ 0 := by
      intro hp_zero
      exact hymin_ne ((hp ymin).mp hp_zero)
    exact lt_of_le_of_ne (apply_nonneg p ymin) (Ne.symm hp_ne)
  · intro y hy
    exact hymin (by simpa [s, Metric.mem_sphere, dist_eq_norm] using hy)

/-- A separating seminorm on a finite-dimensional real normed space controls the
ambient norm.

Equivalently, the identity map from the seminorm gauge to the ambient norm is
bounded whenever the seminorm has trivial kernel.

Layer: Glue | Gap: Level 1 (finite-dimensional separating seminorm coercivity)
Proof: first obtain continuity of the seminorm from finite-dimensional upper
  control by the ambient norm, then minimize it on the compact ambient unit
  sphere and rescale arbitrary nonzero vectors.
Source: Mathlib finite-dimensional normed-space topology, seminorm API, and
  compact unit-sphere extreme-value arguments
Used in: stochastic block mirror descent block primal seminorm unit-ball
  boundedness before support-dual norm estimates
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic block mirror descent -/
theorem exists_norm_le_mul_self_of_finiteDimensional_separating
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (p : Seminorm ℝ E) (hp : p.IsSeparating) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E, ‖x‖ ≤ C * p x := by
  classical
  by_cases htriv : Subsingleton E
  · refine ⟨0, le_rfl, ?_⟩
    intro x
    have hx : x = 0 := Subsingleton.elim x 0
    simp [hx]
  · haveI : Nontrivial E := not_subsingleton_iff_nontrivial.mp htriv
    haveI : ProperSpace E := FiniteDimensional.proper ℝ E
    rcases Seminorm.exists_bound_by_norm_of_finiteDimensional p with
      ⟨K, hKnonneg, hK⟩
    have hcont : Continuous p := by
      let q : Seminorm ℝ E := (Real.toNNReal K) • normSeminorm ℝ E
      have hqcont : Continuous q := by
        change Continuous (fun x : E => ((Real.toNNReal K : ℝ) * ‖x‖))
        exact continuous_const.mul continuous_norm
      refine Seminorm.continuous_of_le hqcont ?_
      intro x
      change p x ≤ ((Real.toNNReal K : ℝ) * ‖x‖)
      simpa [Real.toNNReal_of_nonneg hKnonneg] using hK x
    rcases Seminorm.exists_pos_le_on_unit_sphere_of_separating
        p hp hcont.continuousOn with
      ⟨c, hcpos, hc⟩
    refine ⟨c⁻¹, inv_nonneg.mpr (le_of_lt hcpos), ?_⟩
    intro x
    by_cases hx : x = 0
    · simp [hx]
    · let y : E := (‖x‖)⁻¹ • x
      have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
      have hy_norm : ‖y‖ = 1 := by
        simp [y, norm_smul, inv_mul_cancel₀ hxpos.ne']
      have hcy : c ≤ p y := hc y hy_norm
      have hpy : p y = (‖x‖)⁻¹ * p x := by
        simp [y, map_smul_eq_mul]
      have hineq : c ≤ (‖x‖)⁻¹ * p x := by simpa [hpy] using hcy
      have hmul : c * ‖x‖ ≤ p x := by
        have hmul' := mul_le_mul_of_nonneg_right hineq (le_of_lt hxpos)
        have hright : ((‖x‖)⁻¹ * p x) * ‖x‖ = p x := by
          rw [mul_assoc, mul_comm (p x) ‖x‖, ← mul_assoc,
            inv_mul_cancel₀ hxpos.ne', one_mul]
        simpa [hright] using hmul'
      have hmul_comm : ‖x‖ * c ≤ p x := by simpa [mul_comm] using hmul
      have hdiv : ‖x‖ ≤ p x / c := (le_div_iff₀ hcpos).2 hmul_comm
      simpa [div_eq_inv_mul, mul_comm] using hdiv

end Seminorm

/-- Bounded finite-dimensional carriers admit uniform seminorm displacement
bounds from a fixed point.

For each block carrier `X i`, any fixed ambient point `x i` has a finite
seminorm radius controlling `p i (x i - y i)` uniformly over all feasible
`y i ∈ X i`.

Layer: Glue | Gap: Level 1 (dependent-family seminorm displacement bound)
Proof: bound each seminorm by the ambient norm using finite dimensionality,
  bound each carrier in ambient norm, and combine those bounds with the
  triangle inequality.
Source: Mathlib bounded-set norm APIs and finite-dimensional seminorm control
Used in: stochastic block mirror descent blockwise oracle-noise integrability
  through bounded feasible displacements
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem exists_uniform_seminorm_sub_bound_of_bounded_sets
    {𝕜 I Y : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    {B : I → Type*} [∀ i, NormedAddCommGroup (B i)] [∀ i, NormedSpace 𝕜 (B i)]
    [∀ i, FiniteDimensional 𝕜 (B i)]
    (X : ∀ i, Set (B i)) (p : ∀ i, Seminorm 𝕜 (B i)) (x : ∀ i, B i)
    (coord : Y → ∀ i, B i)
    (hcoord : ∀ y i, coord y i ∈ X i)
    (hX : ∀ i, Bornology.IsBounded (X i)) :
    ∃ R : I → ℝ, (∀ i, 0 ≤ R i) ∧
      ∀ y : Y, ∀ i, p i (x i - coord y i) ≤ R i := by
  classical
  have hK :
      ∀ i, ∃ K : ℝ, 0 ≤ K ∧
        ∀ d : B i, p i d ≤ K * ‖d‖ := by
    intro i
    exact Seminorm.exists_bound_by_norm_of_finiteDimensional (p i)
  choose K hK_nonneg hK_bound using hK
  have hB : ∀ i, ∃ C : ℝ, ∀ y ∈ X i, ‖y‖ ≤ C := by
    intro i
    exact (hX i).exists_norm_le
  choose C hC_bound using hB
  refine ⟨fun i => K i * (‖x i‖ + |C i|), ?_, ?_⟩
  · intro i
    exact mul_nonneg (hK_nonneg i) (add_nonneg (norm_nonneg _) (abs_nonneg _))
  · intro y i
    have hyC : ‖coord y i‖ ≤ |C i| :=
      (hC_bound i (coord y i) (hcoord y i)).trans (le_abs_self (C i))
    have hnorm : ‖x i - coord y i‖ ≤ ‖x i‖ + |C i| :=
      (norm_sub_le (x i) (coord y i)).trans (add_le_add (le_refl _) hyC)
    exact (hK_bound i (x i - coord y i)).trans
      (mul_le_mul_of_nonneg_left hnorm (hK_nonneg i))

/-- A finite measurable selector dispatches among measurable branch maps measurably.

If `idx : α → δ` is measurable and `δ` is a finite measurable-singleton space,
then choosing the branch `f (idx a)` at each point `a` preserves measurability
whenever every branch `f i` is measurable.

Layer: Glue | Gap: Level 1 (finite selector dispatch measurability)
Proof: view the branches as a measurable function on `α × δ` using Mathlib's
  countable-product measurability theorem, then compose with the measurable
  graph map `a ↦ (a, idx a)`.
Source: Mathlib measurable-space constructions for countable products and finite singleton fibers
Used in: stochastic block mirror descent sampled block update and selected oracle-kernel measurability
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic block mirror descent -/
theorem measurable_fintype_dispatch
    {α β δ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace δ]
    [Fintype δ] [MeasurableSingletonClass δ]
    {idx : α → δ} {f : δ → α → β}
    (hidx : Measurable idx) (hf : ∀ i, Measurable (f i)) :
    Measurable (fun a => f (idx a) a) := by
  classical
  have hjoint : Measurable (fun p : α × δ => f p.2 p.1) := by
    exact measurable_from_prod_countable_left (fun i => hf i)
  exact hjoint.comp (measurable_id.prodMk hidx)

/-- Backward-compatible finite dispatch name used by staged block-coordinate proofs.

Layer: Glue | Gap: Level 1 (finite selector dispatch measurability)
Proof: direct alias of `measurable_fintype_dispatch`.
Source: Mathlib measurable-space constructions for countable products and finite singleton fibers
Used in: stochastic block mirror descent sampled block update and selected oracle-kernel measurability
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic block mirror descent -/
theorem measurable_countable_dispatch
    {α β δ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace δ]
    [Fintype δ] [MeasurableSingletonClass δ]
    {idx : α → δ} {f : δ → α → β}
    (hidx : Measurable idx) (hf : ∀ i, Measurable (f i)) :
    Measurable (fun a => f (idx a) a) := by
  exact measurable_fintype_dispatch hidx hf

open MeasureTheory

/-- Two feasible-valued random points have integrable squared distance under a
uniform feasible-set diameter bound.

On a finite measure space, if `x` and `y` are a.e. strongly measurable
normed-space-valued maps, belong to a set `X` almost everywhere, and every pair
of points in `X` is at norm distance at most `D`, then the squared norm of
`x - y` is integrable.

Layer: Glue | Gap: Level 1 (feasible-pair diameter domination for L2 integrability)
Proof: form the measurable difference process, derive its a.e. squared-norm
  domination from the two a.e. membership facts and the pairwise diameter
  hypothesis, then apply integrability by domination against a constant.
Source: Mathlib measurable normed-group operations and measure-theory
  integrability by domination APIs
Used in: stochastic nonconvex conditional-gradient iterate-difference
  square-integrability from compact feasible-set diameter control
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem integrable_sq_norm_sub_of_measurable_mem_diameter_bound
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : Set E} {D : ℝ} {x y : Ω → E}
    (hx_meas : AEStronglyMeasurable x μ)
    (hy_meas : AEStronglyMeasurable y μ)
    (hx_mem : ∀ᵐ ω ∂μ, x ω ∈ X)
    (hy_mem : ∀ᵐ ω ∂μ, y ω ∈ X)
    (hdiam : ∀ ⦃a b : E⦄, a ∈ X → b ∈ X → ‖a - b‖ ≤ D) :
    Integrable (fun ω => ‖x ω - y ω‖ ^ 2) μ := by
  have hdiff_meas : AEStronglyMeasurable (fun ω => x ω - y ω) μ :=
    hx_meas.sub hy_meas
  have hbound : ∀ᵐ ω ∂μ, ‖‖x ω - y ω‖ ^ 2‖ ≤ ‖D ^ 2‖ := by
    refine (hx_mem.and hy_mem).mono ?_
    intro ω hω
    rw [Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg (sq_nonneg D)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hdiam hω.1 hω.2) 2
  exact Integrable.mono (integrable_const (D ^ 2)) (hdiff_meas.norm.pow 2) hbound

/-- A state-valued map is measurable when its coordinate map is measurable and
the state sigma-algebra is bounded by the coordinate comap.

This is useful for state records whose measurable structure intentionally
forgets proof fields: once the visible coordinates of `f` are represented by a
measurable process `g`, measurability of `f` follows from the comap bound.

Layer: Glue | Gap: Level 0 (codomain coordinate-comap measurability closure)
Proof: rewrite `coord ∘ f` to the measurable coordinate process, use its comap
  bound, then transport that bound through monotonicity of codomain comap and
  apply `Measurable.of_comap_le`.
Source: Mathlib measure-theory measurable-space comap and product-coordinate APIs
Used in: stochastic accelerated gradient descent sample-kernel state transition
  after prox and averaged-output coordinate measurability
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec/steps
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
theorem measurable_to_comap_state_of_measurable_coordinates
    {Ω A B : Type*} [MeasurableSpace Ω] [mA : MeasurableSpace A]
    [MeasurableSpace B]
    (coord : A → B) (f : Ω → A) (g : Ω → B)
    (hg : Measurable g)
    (hcoord : ∀ ω, coord (f ω) = g ω)
    (hA_le_coord :
      mA ≤ MeasurableSpace.comap coord (inferInstance : MeasurableSpace B)) :
    Measurable f := by
  have hcoord_f : Measurable (fun ω : Ω => coord (f ω)) := by
    simpa [hcoord] using hg
  refine Measurable.of_comap_le ?_
  exact le_trans (MeasurableSpace.comap_mono hA_le_coord) (by
    simpa [Function.comp_def] using hcoord_f.comap_le)

namespace SOptLib

open MeasureTheory

/-- A two-argument map is continuous when a joint distance bound is controlled
by the sum of the coordinate distances.

The product metric uses the maximum of the coordinate distances, so the
coordinate-sum estimate yields a `2 * K` Lipschitz bound for `Function.uncurry f`.

Layer: Glue | Gap: Level 1 (product-coordinate Lipschitz continuity)
Proof: package the coordinate-sum estimate as a `LipschitzWith` bound on the
  product using `Prod.dist_eq`, then apply Mathlib's Lipschitz-continuity API.
Source: Mathlib metric Lipschitz maps and product pseudometric-space APIs
Used in: stochastic block mirror descent prox-step continuity from state-oracle
  stability estimates
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem continuous_uncurry_of_dist_le_mul_add_dist
    {P E F : Type*} [PseudoMetricSpace P] [PseudoMetricSpace E] [PseudoMetricSpace F]
    (f : P → E → F) {K : ℝ} (hK : 0 ≤ K)
    (hbound :
      ∀ (x₁ x₂ : P) (g₁ g₂ : E),
        dist (f x₁ g₁) (f x₂ g₂) ≤ K * (dist x₁ x₂ + dist g₁ g₂)) :
    Continuous (Function.uncurry f) := by
  have hLip : LipschitzWith (Real.toNNReal (2 * K)) (Function.uncurry f) := by
    refine LipschitzWith.of_dist_le' ?_
    intro p q
    have hmain :
        dist (f p.1 p.2) (f q.1 q.2) ≤
          K * (dist p.1 q.1 + dist p.2 q.2) :=
      hbound p.1 q.1 p.2 q.2
    have hsum :
        dist p.1 q.1 + dist p.2 q.2 ≤
          2 * max (dist p.1 q.1) (dist p.2 q.2) := by
      calc
        dist p.1 q.1 + dist p.2 q.2
            ≤ max (dist p.1 q.1) (dist p.2 q.2) +
                max (dist p.1 q.1) (dist p.2 q.2) :=
              add_le_add (le_max_left _ _) (le_max_right _ _)
        _ = 2 * max (dist p.1 q.1) (dist p.2 q.2) := by ring
    calc
      dist (Function.uncurry f p) (Function.uncurry f q)
          ≤ K * (dist p.1 q.1 + dist p.2 q.2) := by
            simpa [Function.uncurry] using hmain
      _ ≤ K * (2 * max (dist p.1 q.1) (dist p.2 q.2)) :=
            mul_le_mul_of_nonneg_left hsum hK
      _ = (2 * K) * dist p q := by
            rw [Prod.dist_eq]
            ring
  exact hLip.continuous

/-- A nonnegative real function bounded above a.e. has its norm bounded by the
same envelope a.e.

This packages the scalar step from a nonnegative gap estimate to a norm
domination estimate under an arbitrary measure.

Layer: Glue | Gap: Level 0 (a.e. real gap norm domination)
Proof: combine the two a.e. hypotheses with `filter_upwards`, rewrite the real
  norm as absolute value, and use `abs_of_nonneg` at each point.
Source: Mathlib real norm/order identities and almost-everywhere filter APIs
Used in: stochastic block mirror descent expected suboptimality gap domination
  by a finite-window envelope
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/main_theorem
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem norm_le_of_ae_nonneg_of_ae_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (gap envelope : Ω → ℝ)
    (hnonneg : ∀ᵐ ω ∂μ, 0 ≤ gap ω)
    (hle : ∀ᵐ ω ∂μ, gap ω ≤ envelope ω) :
    ∀ᵐ ω ∂μ, ‖gap ω‖ ≤ envelope ω := by
  filter_upwards [hnonneg, hle] with ω hnonnegω hleω
  simpa [Real.norm_eq_abs, abs_of_nonneg hnonnegω] using hleω

/-- A function is continuous at a point when its displacement is eventually
bounded by a real envelope that is continuous there and vanishes there.

Layer: Glue | Gap: Level 1 (metric continuity from a vanishing envelope)
Proof: use the metric characterization of continuity at a point; continuity of
  the envelope makes it eventually smaller than any positive radius, and the
  eventual distance bound transfers that estimate to the function.
Source: Mathlib metric-space continuity and closed-order topology APIs
Used in: stochastic block mirror descent prox-step continuity from a vanishing
  state-oracle displacement envelope
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem continuousAt_of_dist_le_continuousAt_zero_envelope
    {α β : Type*} [TopologicalSpace α] [PseudoMetricSpace β]
    {f : α → β} {a : α} {envelope : α → ℝ}
    (henvelope_cont : ContinuousAt envelope a)
    (henvelope_zero : envelope a = 0)
    (hbound : ∀ᶠ x in 𝓝 a, dist (f x) (f a) ≤ envelope x) :
    ContinuousAt f a := by
  rw [Metric.continuousAt_iff']
  intro ε hε
  have hevent :
      ∀ᶠ x in 𝓝 a, envelope x < (fun _ => ε) x := by
    exact henvelope_cont.eventually_lt continuousAt_const
      (by simpa [henvelope_zero] using hε)
  filter_upwards [hbound, hevent] with x hx henv
  exact lt_of_le_of_lt hx henv

end SOptLib

-- Promoted from Staging/measurable_finset_sum_const_mul_seminorm_subtype_radius.lean
open scoped BigOperators

-- Generalization plan (G0):
-- concept/name: finite-sum weighted seminorm radius measurability on a subtype;
--   orig was scalarDelta_radiusBudget_measurable, renamed away from scalar-noise
--   and algorithm-local delta terminology.
-- generality used: finite dependent product of finite-dimensional normed real
--   modules with Borel measurable coordinate spaces; no probability measure,
--   independence, integrability, convexity, smoothness, or oracle assumptions.
-- portable call pattern: randomized block mirror descent, block proximal-gradient,
--   and coordinate stochastic-gradient proofs call this when a deterministic
--   finite radius budget on feasible queries must be measurable; the weights,
--   seminorms, reference point, and feasible carrier change while the conclusion
--   keeps the same shape.
-- counterargument checked: Mathlib has `Finset.measurable_fun_sum` and scalar
--   multiplication closure, but it does not package coordinate projection from a
--   feasible subtype together with finite-dimensional seminorm continuity.
--   SOptLib has `integrable_finset_sum_const_mul`, which covers integrability
--   from already-integrable summands rather than this subtype-radius
--   measurability pattern.
-- coverage search: LeanSearch query "measurable finite sum constant times
--   seminorm of coordinate difference subtype" returned `Finset.measurable_fun_sum`
--   and related finite-sum APIs; project search for "seminorm radius measurable"
--   found only paper-local proofs and finite-dimensional seminorm control lemmas.
--   Coverage is partial, not duplicate.
-- minimal hypotheses: finite dimensionality is used only to derive continuity of
--   each seminorm; all measure/probability and algorithm hypotheses from the
--   source declaration are removed.

/-- A finite weighted sum of coordinate seminorm radii is measurable on any subtype.

For a finite dependent product of finite-dimensional real normed spaces, the map
sending a subtype point `x` to `sum_i c_i * p_i (xRef_i - x_i)` is measurable.

Layer: Glue | Gap: Level 1 (finite-dimensional seminorm subtype-radius measurability)
Proof: coordinate projections from the subtype are measurable; finite-dimensional
  seminorms are continuous by ambient-norm domination, and finite sums of
  measurable real functions are measurable.
Source: Mathlib dependent-product measurable-space APIs, finite sums, and
  SOptLib finite-dimensional seminorm norm control
Used in: stochastic block mirror descent deterministic radius-budget
  measurability before random-radius integrability transfer
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/main_theorem/proof
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem measurable_finset_sum_const_mul_seminorm_subtype_radius
    {ι : Type*} [Fintype ι]
    {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace ℝ (E i)] [∀ i, MeasurableSpace (E i)]
    [∀ i, BorelSpace (E i)] [∀ i, FiniteDimensional ℝ (E i)]
    (pNorm : ∀ i, Seminorm ℝ (E i)) (c : ι → ℝ)
    (xRef : ∀ i, E i) (A : Set (∀ i, E i)) :
    Measurable
      (fun x : {y : ∀ i, E i // y ∈ A} =>
        Finset.sum Finset.univ (fun i => c i * pNorm i (xRef i - x.1 i))) := by
  classical
  refine Finset.measurable_sum Finset.univ ?_
  intro i _
  have hcoord :
      Measurable (fun x : {y : ∀ i, E i // y ∈ A} => x.1 i) :=
    (measurable_pi_apply i).comp measurable_subtype_coe
  have hdiff :
      Measurable (fun x : {y : ∀ i, E i // y ∈ A} => xRef i - x.1 i) :=
    measurable_const.sub hcoord
  have hseminorm_cont : Continuous (fun u : E i => pNorm i u) := by
    rcases Seminorm.exists_bound_by_norm_of_finiteDimensional (pNorm i) with
      ⟨K, hKnonneg, hK⟩
    let q : Seminorm ℝ (E i) := (Real.toNNReal K) • normSeminorm ℝ (E i)
    have hqcont : Continuous q := by
      change Continuous (fun u : E i => ((Real.toNNReal K : ℝ) * ‖u‖))
      exact continuous_const.mul continuous_norm
    refine Seminorm.continuous_of_le hqcont ?_
    intro u
    change pNorm i u ≤ ((Real.toNNReal K : ℝ) * ‖u‖)
    simpa [Real.toNNReal_of_nonneg hKnonneg] using hK u
  exact (hseminorm_cont.measurable.comp hdiff).const_mul (c i)

-- Generalization plan (G0):
-- concept/name: compact upper boundedness of a convex function on an interior subset;
--   orig was `bounded_on_compact_subset_of_interior_for_convexOn`, renamed to
--   `ConvexOn.exists_upper_bound_on_compact_subset_interior`.
-- generality used: real-valued `ConvexOn ℝ K f` on a finite-dimensional real
--   normed vector space, compact `C`, and the pointwise inclusion
--   `C ⊆ interior K`; no measure, smoothness, oracle, or algorithm state is used.
-- portable call pattern: stochastic mirror descent, accelerated primal-dual,
--   and composite prox proofs that need a finite upper bound for a convex
--   penalty or gap component after restricting a compact feasible subset to
--   the ordinary interior; `E`, `K`, `C`, and `f` vary while the conclusion stays.
-- counterargument checked: not paper-local traceability and not a one-line
--   rename of Mathlib; it packages `ConvexOn.continuousOn_interior` with compact
--   image boundedness into the reusable convex-analysis shape callers need.
-- coverage search: queried `ConvexOn continuousOn_interior bounded compact upper
--   bound`, `convex function bounded above on compact subset of interior`, and
--   catalog tokens `ConvexOn interior compact bddAbove`; top hits were
--   `ConvexOn.continuousOn_interior`, `IsCompact.bddAbove_image`, and SOptLib's
--   `exists_nonneg_norm_bound_of_isCompact_of_continuousOn`, all partial only.
-- minimal hypotheses: all already minimal relative to Mathlib's interior
--   continuity theorem; finite dimensionality is required by that theorem.

/-- A convex real-valued function is bounded above on compact subsets of the
ordinary interior of its carrier.

Layer: Glue | Gap: Level 1 (convex interior compact upper bound)
Proof: use `ConvexOn.continuousOn_interior`, restrict continuity to the compact
  subset, then apply compact image boundedness for real-valued continuous
  functions.
Source: Mathlib convex-analysis continuity and compact ordered-image APIs
Used in: stochastic accelerated primal-dual convex penalty upper-bound step on
  compact feasible subsets inside the carrier interior
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/assumptions/0/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem ConvexOn.exists_upper_bound_on_compact_subset_interior
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {C K : Set E} {f : E → ℝ}
    (hfconv : ConvexOn ℝ K f) (hCcompact : IsCompact C) (hCsub : C ⊆ interior K) :
    ∃ B : ℝ, ∀ x, x ∈ C → f x ≤ B := by
  have hcontInterior : ContinuousOn f (interior K) :=
    ConvexOn.continuousOn_interior hfconv
  have hcontC : ContinuousOn f C :=
    hcontInterior.mono hCsub
  obtain ⟨B, hB⟩ := bddAbove_def.mp (hCcompact.bddAbove_image hcontC)
  refine ⟨B, ?_⟩
  intro x hx
  exact hB (f x) ⟨x, hx, rfl⟩

-- Generalization plan (G0):
-- concept/name: norm radius bound from a squared displacement budget; orig was bregman_bounded_domain_norm_radius_bound_pattern.
-- generality used: carrier E only needs [SeminormedAddGroup E]; no measure, convexity, smoothness, oracle, topology beyond the normed metric, inner product, completeness, or finite-dimensional hypotheses are used.
-- portable call pattern: stochastic accelerated primal-dual and mirror-descent compactness/boundedness steps where a Bregman or telescope estimate first gives ‖x - x0‖ ^ 2 ≤ R, while the conclusion remains the ambient norm bound ‖x‖ ≤ ‖x0‖ + sqrt R.
-- counterargument checked: this is close to Mathlib's norm_le_norm_add_const_of_dist_le, but that lemma requires a distance bound; this statement packages the recurring squared-budget-to-radius conversion used at algorithm call-sites rather than renaming a single theorem.
-- coverage search: searched CATALOG/SOptLib/Staging for norm/sqrt/sq_norm_sub and LeanSearch for the squared-distance-to-norm-radius statement; top full hit was Mathlib norm_le_norm_add_const_of_dist_le, partial only because it lacks the Real.le_sqrt_of_sq_le step.
-- minimal hypotheses: all already minimal; the hypothesis is pointwise and no global feasible set, Bregman formula, probability frame, convexity, or finite-dimensional structure is retained.

/-- A squared displacement budget gives an ambient norm radius around the base
point.

If the squared norm of `x - x0` is bounded by a real budget `R`, then `x` lies
within the corresponding square-root radius in the norm estimate centered at
`x0`.

Layer: Glue | Gap: Level 0 (squared displacement budget to norm radius)
Proof: convert the squared norm estimate to a distance estimate with
  `Real.le_sqrt_of_sq_le`, then apply the norm triangle estimate around the
  base point.
Source: Mathlib seminormed additive groups and real square-root order APIs
Used in: stochastic accelerated primal-dual feasible-radius bounds derived from
  Bregman-domain diameter estimates
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/assumptions
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
theorem norm_le_norm_base_add_sqrt_of_sq_norm_sub_le
    {E : Type*} [SeminormedAddGroup E]
    (x x0 : E) {R : ℝ}
    (hsq : ‖x - x0‖ ^ 2 ≤ R) :
    ‖x‖ ≤ ‖x0‖ + Real.sqrt R := by
  have hdist_norm : ‖x - x0‖ ≤ Real.sqrt R :=
    Real.le_sqrt_of_sq_le hsq
  exact (norm_le_norm_add_norm_sub' x x0).trans (add_le_add_right hdist_norm ‖x0‖)

namespace ConvexOn

-- Generalization plan (G0):
-- concept/name: scaled two-point convex average bound for `ConvexOn`; orig was
--   `convex_beta_average_scaled_bound`.
-- generality used: real module over an additive commutative group, a set carrier,
--   a real-valued `ConvexOn ℝ X f`, two feasible endpoints, and one scale
--   hypothesis `1 ≤ β`.
-- portable call pattern: accelerated primal-dual, accelerated composite gradient,
--   and estimate-sequence proofs can call this when an output average is updated
--   by `(1 - β⁻¹) • previous + β⁻¹ • next`; the objective, carrier, endpoints,
--   and schedule scale vary while the scaled conclusion stays the same.
-- counterargument checked: not paper-local traceability because the statement is
--   exactly the reusable two-point Jensen bound after multiplying by the
--   acceleration scale; not a pure wrapper around the caller expression because it
--   packages feasibility, convex weights, and post-scaling arithmetic.
-- coverage search: queried `ConvexOn map_sum_le convex combination smul average le`
--   and LeanSearch `ConvexOn two point convex combination beta smul average
--   inequality`; top hits were Mathlib `ConvexOn.map_sum_le`,
--   `convexOn_iff_div`, and SOptLib `convexOn_weighted_average_le_weighted_sum`.
--   Those cover finite Jensen but not this scaled two-point beta conclusion.
-- minimal hypotheses: pointwise endpoint membership and the defining average
--   equality replace all algorithm setup fields; no topology, norm, measure, or
--   finite-dimensional assumptions are used.

/-- A convex function at an inverse-beta two-point average gives the scaled
accelerated average bound.

If `c = (1 - β⁻¹) • a + β⁻¹ • b` with `1 ≤ β`, then convexity bounds
`β * f c` by `(β - 1) * f a + f b`.

Layer: Glue | Gap: Level 1 (scaled two-point Jensen bridge)
Proof: apply the two-point form of `ConvexOn` with weights `1 - β⁻¹` and
  `β⁻¹`, then multiply the resulting inequality by the nonnegative scale `β`
  and simplify the scalar coefficients.
Source: Mathlib convex-analysis API for `ConvexOn` and ordered-field arithmetic
Used in: accelerated primal-dual dual aggregate bound from inverse-beta averaged
  output recurrence
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem beta_smul_average_le
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {X : Set E} {f : E → ℝ} (hf : ConvexOn ℝ X f)
    {β : ℝ} {a b c : E}
    (hβ : 1 ≤ β) (ha : a ∈ X) (hb : b ∈ X)
    (hc : c = (1 - β⁻¹) • a + β⁻¹ • b) :
    β * f c ≤ (β - 1) * f a + f b := by
  have hβpos : 0 < β := lt_of_lt_of_le zero_lt_one hβ
  have hβnonneg : 0 ≤ β := le_of_lt hβpos
  have hβne : β ≠ 0 := ne_of_gt hβpos
  have hcoef_left : β * (1 - β⁻¹) = β - 1 := by
    field_simp [hβne]
  have hcoef_right : β * β⁻¹ = 1 := by
    field_simp [hβne]
  have hleft : 0 ≤ 1 - β⁻¹ := by
    have hmul : 0 ≤ β * (1 - β⁻¹) := by
      rw [hcoef_left]
      linarith
    exact (mul_nonneg_iff_of_pos_left hβpos).mp hmul
  have hright : 0 ≤ β⁻¹ := inv_nonneg.mpr hβnonneg
  have hsum : 1 - β⁻¹ + β⁻¹ = 1 := by
    ring
  have hconv :
      f c ≤ (1 - β⁻¹) * f a + β⁻¹ * f b := by
    have hraw := hf.2 ha hb hleft hright hsum
    simpa [hc] using hraw
  have hmul := mul_le_mul_of_nonneg_left hconv hβnonneg
  have hrhs :
      β * ((1 - β⁻¹) * f a + β⁻¹ * f b) =
        (β - 1) * f a + f b := by
    calc
      β * ((1 - β⁻¹) * f a + β⁻¹ * f b)
          = (β * (1 - β⁻¹)) * f a + (β * β⁻¹) * f b := by
            ring
      _ = (β - 1) * f a + f b := by
            rw [hcoef_left, hcoef_right, one_mul]
  nlinarith [hmul, hrhs]

-- Generalization plan (G0):
-- concept/name: supporting hyperplane inequality for a convex function from a selected
--   ambient gradient; orig was convex_hasGradientAt_supporting_hyperplane_on_carrier.
-- generality used: real Hilbert-space carrier with `ConvexOn ℝ X f`, feasible base and
--   endpoint, and one pointwise `HasGradientAt f g x`; no measure, filtration, oracle, or
--   algorithm data.
-- portable call pattern: accelerated primal-dual, mirror descent, and proximal-gradient
--   one-step descent proofs use this to replace convex objective values by tangent
--   hyperplanes; the carrier, objective, selected gradient, and endpoints vary.
-- counterargument checked: this is not paper-local traceability because the statement is
--   exactly the textbook first-order convex support inequality; it is not a one-line
--   wrapper around the existing Bregman API because callers may have a selected gradient
--   `g` rather than Mathlib's canonical `∇ f x`, and may need the raw inequality directly.
-- coverage search: queried `ConvexOn supporting hyperplane HasGradientAt inner` and
--   LeanSearch `convex function supporting hyperplane has gradient at inner product`;
--   top hits were `HasGradientAt.fderiv_apply`, `HasGradientAt.hasFDerivAt`,
--   `smooth_quadratic_upper_bound_of_hasGradientAt_lipschitzOn_convex`, and
--   `bregmanDivergence_nonneg_of_convexOn`; coverage is partial but no hit states this
--   selected-gradient carrier support inequality.
-- minimal hypotheses: convexity is required on the full segment between `x` and `u`;
--   differentiability is pointwise at `x`; `CompleteSpace E` is required by Mathlib's
--   `HasGradientAt` API, and finite-dimensionality is not used.

/-- A convex function lies above the supporting hyperplane from a selected gradient.

If `f` is convex on a carrier `X`, `x` and `u` are feasible, and `g` is an
ambient gradient of `f` at `x`, then the value at `u` dominates the affine
first-order model based at `x`.

Layer: Glue | Gap: Level 1 (selected-gradient convex support inequality)
Proof: restrict `f` to the affine segment from `x` to `u`, use the
  one-dimensional convex slope inequality at `0`, and identify the segment
  derivative from `HasGradientAt` by the Hilbert-space dual pairing.
Source: Mathlib convex one-dimensional derivative/slope API and `HasGradientAt`
  calculus in real Hilbert spaces
Used in: stochastic accelerated primal-dual and mirror-style one-step descent
  proofs when a convex objective is replaced by its tangent lower model
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec/steps
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem supporting_hyperplane_of_hasGradientAt
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {X : Set E} {f : E → ℝ} {g x u : E}
    (hf : ConvexOn ℝ X f) (hx : x ∈ X) (hu : u ∈ X)
    (hgrad : HasGradientAt f g x) :
    f x + ⟪g, u - x⟫_ℝ ≤ f u := by
  let φ : ℝ → ℝ := fun s => f (AffineMap.lineMap x u s)
  have hline_mem : Set.Icc (0 : ℝ) 1 ⊆ (AffineMap.lineMap x u) ⁻¹' X := by
    intro s hs
    have hs0 : 0 ≤ s := hs.1
    have hs1 : s ≤ 1 := hs.2
    have h1s : 0 ≤ 1 - s := sub_nonneg.mpr hs1
    have hsum : 1 - s + s = 1 := by ring
    have hmem : (1 - s) • x + s • u ∈ X := hf.1 hx hu h1s hs0 hsum
    change AffineMap.lineMap x u s ∈ X
    rw [AffineMap.lineMap_apply_module']
    convert hmem using 1
    module
  have hφ_conv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) φ := by
    simpa [φ] using
      (hf.comp_affineMap (AffineMap.lineMap x u)).subset hline_mem (convex_Icc 0 1)
  have hφ_deriv : HasDerivAt φ (⟪g, u - x⟫_ℝ) 0 := by
    have hφ_eq : φ = fun s : ℝ => f (x + s • (u - x)) := by
      ext s
      simp only [φ, AffineMap.lineMap_apply_module']
      congr 1
      module
    rw [hφ_eq]
    have hfderiv : HasFDerivAt f (InnerProductSpace.toDual ℝ E g)
        (x + (0 : ℝ) • (u - x)) := by
      simpa using hgrad.hasFDerivAt
    have hline : HasDerivAt (fun s : ℝ => x + s • (u - x)) ((1 : ℝ) • (u - x)) 0 := by
      exact (hasDerivAt_id 0).smul_const (u - x) |>.const_add x
    have hcomp := hfderiv.comp_hasDerivAt 0 (hline.congr_deriv (one_smul ℝ (u - x)))
    simpa [Function.comp_def, InnerProductSpace.toDual_apply_apply] using hcomp
  have hslope := hφ_conv.le_slope_of_hasDerivAt (by norm_num) (by norm_num) zero_lt_one hφ_deriv
  simp [φ, slope_def_field, AffineMap.lineMap_apply_module'] at hslope
  linarith

end ConvexOn

-- Generalization plan (G0):
-- concept/name: three-term lower-semicontinuity closure; orig was lowerSemicontinuousOn_saddle_gap_left_section_block
-- generality used: arbitrary topological domain and carrier set; real-valued functions; no measure, convexity, smoothness, or oracle assumptions
-- portable call pattern: saddle-gap and prox-objective section proofs where two lower-semicontinuous objective pieces are separated by a continuous affine or bilinear coupling term
-- counterargument checked: Mathlib has `LowerSemicontinuousOn.add` and `ContinuousOn.lowerSemicontinuousOn`, but no single theorem packages the recurring lsc + continuous + lsc three-term shape used in product-carrier objective sections
-- coverage search: queried `LowerSemicontinuousOn add continuousOn add`, `lower semicontinuous on sum of two lower semicontinuous functions and one continuous function`; hits were `LowerSemicontinuousOn.add`, `LowerSemicontinuousOn.add'`, and finite-sum variants; partial coverage only
-- minimal hypotheses: all already minimal for this real-valued three-term closure; no finite-dimensional, vector-space, compactness, or product-space assumptions are used

/-- Adding a continuous middle term between two lower-semicontinuous terms
preserves lower-semicontinuity on a carrier.

Layer: Glue | Gap: Level 0 (three-term lower-semicontinuity closure)
Proof: convert the continuous middle term to lower-semicontinuity and apply
  Mathlib's binary `LowerSemicontinuousOn.add` twice.
Source: Mathlib semicontinuity APIs for continuous real-valued functions and
  sums on topological spaces
Used in: stochastic saddle-gap and prox-objective section lower-semicontinuity
  with continuous affine coupling terms
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/setup/problem/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem LowerSemicontinuousOn.add_continuousOn_add
    {α : Type*} [TopologicalSpace α] {s : Set α} {f g h : α → ℝ}
    (hf : LowerSemicontinuousOn f s) (hg : ContinuousOn g s)
    (hh : LowerSemicontinuousOn h s) :
    LowerSemicontinuousOn (fun x => f x + g x + h x) s := by
  exact (hf.add hg.lowerSemicontinuousOn).add hh

-- Generalization plan (G0):
-- concept/name: carrier lower-semicontinuity closure for an affine inner-product
--   term plus an lsc simple term plus a scalar multiple of a continuous term;
--   orig was dual_lsc_affine_simple_bregman_objective.
-- generality used: arbitrary real inner-product normed additive group `E` and
--   carrier set `s`; no measure, compactness, convexity, differentiability,
--   oracle, or algorithm-update assumptions.
-- portable call pattern: composite prox and saddle-subproblem existence proofs
--   where the linear oracle/coupling vector and stepsize change, while the
--   lower-semicontinuity conclusion for `⟪a, y⟫ + h y + c * Vsec y` is reused.
-- counterargument checked: this is a short wrapper over Mathlib continuity and
--   `LowerSemicontinuousOn.add`, but it fixes a recurring prox-objective
--   proof boundary and is not paper traceability or a formula-definition alias.
-- coverage search: queried `LowerSemicontinuousOn add continuousOn const_mul
--   inner` and LeanSearch for lower-semicontinuous sums; hits were
--   `LowerSemicontinuousOn.add`, finite-sum lsc lemmas,
--   `LowerSemicontinuousOn.add_continuousOn_add`, and
--   `SOptLib.proxObjective_lowerSemicontinuous`; coverage is partial because
--   none states this ambient carrier-level affine/lsc/scaled-continuous form.
-- minimal hypotheses: `hh` is lsc only on `s`, `hV` is continuity only on `s`,
--   and the affine coefficient `a` and scalar `c` are point parameters; no
--   finite-dimensional hypothesis is used.

/-- Adding an affine inner-product term, an lsc term, and a scaled continuous
term preserves lower-semicontinuity on a carrier.

Layer: Glue | Gap: Level 0 (affine-plus-scaled lower-semicontinuity closure)
Proof: the inner-product term is continuous, the scaled section is continuous,
  and Mathlib's binary `LowerSemicontinuousOn.add` combines their induced lsc
  facts with the supplied lsc term.
Source: Mathlib lower-semicontinuity closure and real inner-product continuity
  APIs
Used in: accelerated primal-dual composite Bregman prox objective
  lower-semicontinuity before compact argmin extraction
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem LowerSemicontinuousOn.inner_add_lsc_add_const_mul_continuousOn
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {s : Set E} {h Vsec : E → ℝ} (a : E) (c : ℝ)
    (hh : LowerSemicontinuousOn h s) (hV : ContinuousOn Vsec s) :
    LowerSemicontinuousOn (fun y : E => ⟪a, y⟫_ℝ + h y + c * Vsec y) s := by
  have hinner : ContinuousOn (fun y : E => ⟪a, y⟫_ℝ) s :=
    (continuous_const.inner continuous_id).continuousOn
  have hscaled : ContinuousOn (fun y : E => c * Vsec y) s :=
    hV.const_mul c
  exact (hinner.lowerSemicontinuousOn.add hh).add hscaled.lowerSemicontinuousOn

-- Generalization plan (G0):
-- concept/name: positive momentum extrapolation can leave a closed convex set; orig was
--   extrapolateXValue_convexity_coverage_counterexample.
-- generality used: concrete one-dimensional real carrier, closedness and convexity of a set,
--   and two feasible endpoints; no measure, smoothness, oracle, norm, or finite-dimensional
--   hypothesis is used beyond the real line witness.
-- portable call pattern: accelerated primal-dual, accelerated gradient, and mirror-prox
--   source-boundary checks where an extrapolated query is formed from two feasible iterates;
--   the set and iterates change while the conclusion warns that convexity alone cannot prove
--   feasibility of a positive momentum extrapolate.
-- counterargument checked: not a paper traceability wrapper because it records a genuine
--   geometric obstruction; not a formula def; the concrete witness is stronger for reuse than
--   a parameterized hypothesis-equality statement.
-- coverage search: queried "convex closed extrapolate not mem" in project/SOptLib and
--   "closed convex set two points extrapolation outside not in set" in LeanSearch. Relevant
--   hits were Convex.add_smul_sub_mem for true convex combinations and separation theorems;
--   no hit states this positive-momentum counterexample.
-- minimal hypotheses: all already minimal for a counterexample; closedness and convexity are
--   included because they are the assumptions the obstruction refutes.


/-- A positive momentum extrapolate of two points in a closed convex set can
fall outside the set.

The witness is the interval `[0, 1]` with endpoints `0` and `1` and momentum
parameter `1`, whose extrapolate is `2`. This separates positive extrapolation
from the convex-combination API.

Layer: Glue | Gap: Level 0 (closed convex set extrapolation counterexample)
Proof: instantiate the real interval `[0, 1]`; Mathlib supplies closedness and
  convexity of intervals, and `norm_num` discharges the endpoint and
  nonmembership arithmetic.
Source: Mathlib convex interval and real order topology APIs
Used in: accelerated stochastic optimization extrapolated-query feasibility
  boundary checks
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec/steps/3/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem exists_convex_closed_extrapolate_not_mem :
    ∃ (X : Set ℝ) (xPrev xNext θ : ℝ),
      IsClosed X ∧ Convex ℝ X ∧ xPrev ∈ X ∧ xNext ∈ X ∧ 0 < θ ∧
        θ • (xNext - xPrev) + xNext ∉ X := by
  refine ⟨Set.Icc (0 : ℝ) 1, 0, 1, 1, ?_⟩
  constructor
  · exact isClosed_Icc
  constructor
  · exact convex_Icc (0 : ℝ) 1
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  · norm_num


-- Generalization plan (G0):
-- concept/name: squared norm of a Lipschitz map difference controlled by a
--   squared input-distance budget; orig was generatedHatfGradientMismatch_sq_le_bounded_domain.
-- generality used: seminormed additive groups for domain and codomain; no
--   measure, convexity, smoothness structure, or inner product is used.
-- portable call pattern: deterministic gradient-mismatch bounds in stochastic
--   gradient, mirror-descent, variance-reduced, and primal-dual proofs; the map,
--   Lipschitz constant, endpoints, and squared-distance budget vary while the
--   conclusion has the same L^2 times distance-budget form.
-- counterargument checked: not paper-local traceability because the SAPD query
--   and midpoint disappear completely; not a pure wrapper because it combines a
--   pointwise Lipschitz estimate with scalar square monotonicity and budget
--   multiplication into one reusable proof step.
-- coverage search: queried "norm sub le square Lipschitz dist squared" and
--   LeanSearch natural-language Lipschitz squared-distance bound; top hits were
--   LipschitzWith.norm_sub_le, LipschitzWith.norm_sub_le_of_le,
--   LipschitzOnWith.norm_sub_le_of_le, and SOptLib.lipschitzWith_of_norm_sub_le_mul.
--   Coverage is partial: these produce first-power Lipschitz bounds, not the
--   squared codomain norm bound under a squared input-distance budget.
-- minimal hypotheses: global Lipschitz and domain-boundedness assumptions are
--   weakened to the two pointwise inequalities used by the proof.

open scoped BigOperators

/-- A pointwise Lipschitz estimate and a squared-distance budget give a squared
norm-difference budget.

If `grad` is `L`-Lipschitz for the queried pair `x, y`, and the squared input
distance is at most `R`, then the squared codomain difference is at most
`L ^ 2 * R`.

Layer: Glue | Gap: Level 0 (squared Lipschitz distance-budget estimate)
Proof: square the nonnegative norm inequality with `pow_le_pow_left₀`, rewrite
  `(L * d) ^ 2` as `L ^ 2 * d ^ 2`, and multiply the squared-distance budget by
  the nonnegative scalar `L ^ 2`.
Source: Mathlib normed-group inequalities and ordered-ring power algebra
Used in: stochastic accelerated primal-dual deterministic gradient-mismatch
  control from a Lipschitz gradient and bounded primal diameter
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
theorem sq_norm_sub_le_sq_mul_of_lipschitz_sqdist_le
    {E F : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    (grad : E → F) (x y : E) (L R : ℝ)
    (h_lipschitz : ‖grad x - grad y‖ ≤ L * ‖x - y‖)
    (h_sqdist : ‖x - y‖ ^ 2 ≤ R) :
    ‖grad x - grad y‖ ^ 2 ≤ L ^ 2 * R := by
  have hpow :
      ‖grad x - grad y‖ ^ 2 ≤ (L * ‖x - y‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h_lipschitz 2
  have hmul :
      L ^ 2 * ‖x - y‖ ^ 2 ≤ L ^ 2 * R :=
    mul_le_mul_of_nonneg_left h_sqdist (sq_nonneg L)
  calc
    ‖grad x - grad y‖ ^ 2 ≤ (L * ‖x - y‖) ^ 2 := hpow
    _ = L ^ 2 * ‖x - y‖ ^ 2 := by ring
    _ ≤ L ^ 2 * R := hmul


-- Generalization plan (G0):
-- concept/name: positive-scale quadratic exponential domination of absolute value; orig was lemma_4_1_abs_le_sigma_mul_exp_sq_div_sq
-- generality used: pointwise scalar real inequality only; no measure, topology, convexity, smoothness, filtration, oracle, or finite-dimensional assumptions
-- portable call pattern: light-tail integrability steps in stochastic accelerated primal-dual, stochastic mirror-prox, stochastic saddle-point, SGD, and martingale MGF proofs; the random increment and positive scale change while the scalar domination conclusion stays fixed
-- counterargument checked: not paper-local traceability because the statement is a standalone real-analysis envelope turning square-exponential control into L1 domination; not a caller-side expression because it packages the normalization by a positive scale and the exact square-exponential integrability majorant used before expectation transport
-- coverage search: rg over SOptLib/Staging/Algorithms found only the SAPD private helper and adjacent exponential-tilt lemmas; lean_search_symbols query "abs exp square sigma" found no public duplicate; LeanSearch found Mathlib Real.abs_mulExpNegMulSq_le for |x * exp (-eps*x^2)|, which is adjacent but not the direct positive-scale domination call shape
-- minimal hypotheses: only 0 < sigma is required so division by sigma is normalized and the left multiplication preserves order; x is an arbitrary real scalar

/-- Absolute value is dominated by a positive scale times a quadratic exponential envelope.

For `0 < sigma`, normalizing by `sigma` reduces the estimate to
`r <= exp (r^2)` for `r = |x| / sigma`, then rescales back to `x`.

Layer: Glue | Gap: Level 1 (absolute-value domination by square-exponential envelope)
Proof: normalize by the positive scale, prove `r <= r^2 + 1 <= exp (r^2)`,
  and multiply by the positive scale before rewriting the normalized square.
Source: Mathlib real exponential lower bounds and ordered-field square arithmetic
Used in: stochastic optimization light-tail integrability bridges from
  square-exponential control to scalar increment integrability
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/assumptions/8
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic accelerated primal-dual -/
theorem abs_le_pos_mul_exp_sq_div_sq
    (x sigma : ℝ) (hsigma : 0 < sigma) :
    |x| ≤ sigma * Real.exp (x ^ 2 / sigma ^ 2) := by
  let r : ℝ := |x| / sigma
  have hr_nonneg : 0 ≤ r := div_nonneg (abs_nonneg x) (le_of_lt hsigma)
  have hr_quad : r ≤ r ^ 2 + 1 := by
    nlinarith [sq_nonneg (r - 1), hr_nonneg]
  have hr_exp : r ≤ Real.exp (r ^ 2) :=
    le_trans hr_quad (Real.add_one_le_exp (r ^ 2))
  have hmul := mul_le_mul_of_nonneg_left hr_exp (le_of_lt hsigma)
  have hleft : sigma * r = |x| := by
    dsimp [r]
    field_simp [ne_of_gt hsigma]
  have hright : sigma * Real.exp (r ^ 2) =
      sigma * Real.exp (x ^ 2 / sigma ^ 2) := by
    congr 1
    dsimp [r]
    field_simp [ne_of_gt hsigma]
    rw [sq_abs]
  calc
    |x| = sigma * r := hleft.symm
    _ ≤ sigma * Real.exp (r ^ 2) := hmul
    _ = sigma * Real.exp (x ^ 2 / sigma ^ 2) := hright


open scoped BigOperators

-- Generalization plan (G0):
-- concept/name: real exponential quadratic envelope; orig was lemma_4_1_exp_le_id_add_exp_sq_all_real
-- generality used: pointwise scalar real inequality only; no measure, topology, convexity, smoothness, or oracle assumptions
-- portable call pattern: exponential-supermartingale MGF estimates in stochastic accelerated primal-dual, stochastic mirror-prox, and stochastic saddle-point high-probability bounds; the martingale differences and variance scales change while this scalar envelope stays fixed
-- counterargument checked: not paper-local traceability because the theorem is a standalone real-analysis estimate used by multiple light-tail/MGF arguments; not a pure wrapper around a named Mathlib lemma because the sharp 9/16 quadratic envelope is assembled from Taylor and tail branches
-- coverage search: lean_search_symbols query "Real exp y <= y + exp 9 16 y^2" found only SAPD private helpers and planner sandboxes; LeanSearch query "for all real y exp y less than y plus exp nine sixteenths times y squared" returned generic exp monotonicity/Taylor lemmas such as Real.exp_le_exp, Real.add_one_le_exp, Real.exp_bound', and Real.sum_le_exp_of_nonneg, with no full statement
-- minimal hypotheses: all already minimal; the theorem quantifies only y : ℝ

namespace Real

/-- The real exponential is bounded by its linear term plus a `9/16` quadratic
exponential envelope.

This pointwise scalar estimate is the reusable Taylor/tail bridge behind
light-tail martingale moment-generating-function bounds.

Layer: Glue | Gap: Level 1 (real exponential quadratic envelope)
Proof: split into nonpositive, compact nonnegative, and positive-tail branches.
  The branches use Mathlib Taylor bounds for `exp`, monotonicity of `exp`, and
  polynomial certificates discharged by ordered-ring arithmetic.
Source: Mathlib real exponential Taylor bounds and ordered semiring arithmetic
Used in: high-probability stochastic optimization exponential-supermartingale moment bounds
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/key_lemmas/5
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic accelerated primal-dual -/
theorem exp_le_self_add_exp_nine_sixteen_mul_sq (y : ℝ) :
    exp y ≤ y + exp ((9 / 16 : ℝ) * y ^ 2) := by
  have h_compact_branch_quartic_nonneg :
      ∀ y : ℝ, 0 ≤ 729 * y ^ 4 + 2608 * y ^ 2 - 4096 * y + 1536 := by
    intro y
    have htangent : (32 / 27 : ℝ) * y - 16 / 27 ≤ y ^ 4 := by
      have hfact : y ^ 4 - ((32 / 27 : ℝ) * y - 16 / 27) =
          ((3 * y - 2) ^ 2 * (3 * y ^ 2 + 4 * y + 4)) / 27 := by
        ring
      have hsq : 0 ≤ (3 * y - 2) ^ 2 := sq_nonneg _
      have hquad : 0 ≤ 3 * y ^ 2 + 4 * y + 4 := by
        nlinarith [sq_nonneg (3 * y + 2)]
      have hprod : 0 ≤ ((3 * y - 2) ^ 2 * (3 * y ^ 2 + 4 * y + 4)) / 27 := by
        positivity
      nlinarith
    have hmul : 729 * ((32 / 27 : ℝ) * y - 16 / 27) ≤ 729 * y ^ 4 := by
      nlinarith
    have hquadpos : 0 ≤ 2608 * y ^ 2 - 3232 * y + 1104 := by
      nlinarith [sq_nonneg (163 * y - 101)]
    nlinarith
  have hcompact :
      ∀ {y : ℝ}, 0 ≤ y → y ≤ 1 →
        exp y ≤ y + exp ((9 / 16 : ℝ) * y ^ 2) := by
    intro y hy0 hy1
    have hupper := exp_bound' hy0 hy1 (n := 4) (by norm_num)
    have hq_nonneg : 0 ≤ (9 / 16 : ℝ) * y ^ 2 := by
      positivity
    have hlower := sum_le_exp_of_nonneg hq_nonneg 5
    have hpoly :
        (∑ m ∈ Finset.range 4, y ^ m / (m.factorial : ℝ)) +
            y ^ 4 * ((4 : ℕ) + 1 : ℝ) / (((4 : ℕ).factorial : ℝ) * (4 : ℝ)) ≤
          y + (∑ m ∈ Finset.range 5,
            (((9 / 16 : ℝ) * y ^ 2) ^ m / (m.factorial : ℝ))) := by
      norm_num [Finset.sum_range_succ]
      have hquartic := h_compact_branch_quartic_nonneg y
      have hy2_nonneg : 0 ≤ y ^ 2 := sq_nonneg y
      nlinarith [mul_nonneg hy2_nonneg hquartic]
    calc
      exp y
          ≤ (∑ m ∈ Finset.range 4, y ^ m / (m.factorial : ℝ)) +
              y ^ 4 * ((4 : ℕ) + 1 : ℝ) /
                (((4 : ℕ).factorial : ℝ) * (4 : ℝ)) := hupper
      _ ≤ y + (∑ m ∈ Finset.range 5,
            (((9 / 16 : ℝ) * y ^ 2) ^ m / (m.factorial : ℝ))) := hpoly
      _ ≤ y + exp ((9 / 16 : ℝ) * y ^ 2) := by
        linarith
  have h_exp_neg_le_quadratic_upper :
      ∀ {t : ℝ}, 0 ≤ t → exp (-t) ≤ 1 - t + t ^ 2 / 2 := by
    intro t ht
    let q : ℝ := 1 + t + t ^ 2 / 2
    let p : ℝ := 1 - t + t ^ 2 / 2
    have hsum := sum_le_exp_of_nonneg ht 3
    have hq_le_exp : q ≤ exp t := by
      dsimp [q]
      norm_num [Finset.sum_range_succ] at hsum ⊢
      linarith
    have hq_pos : 0 < q := by
      dsimp [q]
      nlinarith [sq_nonneg t]
    have hp_nonneg : 0 ≤ p := by
      dsimp [p]
      nlinarith [sq_nonneg (t - 1)]
    have hpq : 1 ≤ p * q := by
      dsimp [p, q]
      nlinarith [sq_nonneg (t ^ 2)]
    have hmul : 1 ≤ p * exp t := by
      have hmul_le : p * q ≤ p * exp t :=
        mul_le_mul_of_nonneg_left hq_le_exp hp_nonneg
      exact hpq.trans hmul_le
    have hexp_pos : 0 < exp t := exp_pos t
    have hdiv : (exp t)⁻¹ ≤ p := by
      rw [inv_le_iff_one_le_mul₀ hexp_pos]
      simpa [mul_comm] using hmul
    simpa [exp_neg, p] using hdiv
  have hnonpos :
      ∀ {y : ℝ}, y ≤ 0 → exp y ≤ y + exp ((9 / 16 : ℝ) * y ^ 2) := by
    intro y hy
    let t : ℝ := -y
    have ht : 0 ≤ t := by
      dsimp [t]
      linarith
    have hy_eq : y = -t := by
      dsimp [t]
      ring
    have hneg := h_exp_neg_le_quadratic_upper (t := t) ht
    have hsq_nonneg : 0 ≤ t ^ 2 := sq_nonneg t
    have hcoef : t ^ 2 / 2 ≤ (9 / 16 : ℝ) * t ^ 2 := by
      nlinarith
    have hadd :
        1 + t ^ 2 / 2 ≤ exp ((9 / 16 : ℝ) * t ^ 2) := by
      have harg_nonneg : 0 ≤ (9 / 16 : ℝ) * t ^ 2 := by
        positivity
      have hbase := add_one_le_exp ((9 / 16 : ℝ) * t ^ 2)
      nlinarith
    calc
      exp y
          = exp (-t) := by simp [hy_eq]
      _ ≤ 1 - t + t ^ 2 / 2 := hneg
      _ ≤ -t + exp ((9 / 16 : ℝ) * t ^ 2) := by
            nlinarith
      _ = y + exp ((9 / 16 : ℝ) * y ^ 2) := by
            rw [hy_eq]
            ring
  have htail_far :
      ∀ {y : ℝ}, (16 / 9 : ℝ) ≤ y →
        exp y ≤ y + exp ((9 / 16 : ℝ) * y ^ 2) := by
    intro y hy
    have hy0 : 0 ≤ y := by nlinarith
    have hquad : y ≤ (9 / 16 : ℝ) * y ^ 2 := by
      have hmul : (16 / 9 : ℝ) * y ≤ y * y :=
        mul_le_mul_of_nonneg_right hy hy0
      nlinarith
    calc
      exp y
          ≤ exp ((9 / 16 : ℝ) * y ^ 2) :=
            exp_le_exp.mpr hquad
      _ ≤ y + exp ((9 / 16 : ℝ) * y ^ 2) :=
            le_add_of_nonneg_left hy0
  have htail_mid :
      ∀ {y : ℝ}, 1 ≤ y → y ≤ (16 / 9 : ℝ) →
        exp y ≤ y + exp ((9 / 16 : ℝ) * y ^ 2) := by
    intro y hy1 hyub
    let u : ℝ := y - 1
    have hy_eq : y = 1 + u := by
      dsimp [u]
      ring
    have hu0 : 0 ≤ u := by
      dsimp [u]
      linarith
    have hu1 : u ≤ 1 := by
      dsimp [u]
      nlinarith
    have hexp_one_le : exp (1 : ℝ) ≤ 11 / 4 := by
      have h := exp_bound' (x := (1 : ℝ)) (by norm_num) (by norm_num)
        (n := 3) (by norm_num)
      norm_num [Finset.sum_range_succ] at h ⊢
      linarith
    have hu_upper := exp_bound' (x := u) hu0 hu1 (n := 3) (by norm_num)
    let U : ℝ :=
      (∑ m ∈ Finset.range 3, u ^ m / (m.factorial : ℝ)) +
        u ^ 3 * ((3 : ℕ) + 1 : ℝ) / (((3 : ℕ).factorial : ℝ) * (3 : ℝ))
    have hU_nonneg : 0 ≤ U := by
      dsimp [U]
      norm_num [Finset.sum_range_succ]
      positivity
    have h_exp_u_le : exp u ≤ U := by
      simpa [U] using hu_upper
    let z : ℝ := (9 / 16 : ℝ) * (1 + u) ^ 2
    have hz_nonneg : 0 ≤ z := by
      dsimp [z]
      positivity
    have hz_lower := sum_le_exp_of_nonneg hz_nonneg 4
    let L : ℝ := ∑ m ∈ Finset.range 4, z ^ m / (m.factorial : ℝ)
    have hL_le_exp : L ≤ exp z := by
      simpa [L] using hz_lower
    have hpoly :
        (11 / 4 : ℝ) * U ≤ (1 + u) + L := by
      have hcert :
          0 ≤ 2187 * u ^ 6 + 13122 * u ^ 5 + 44469 * u ^ 4 +
            45340 * u ^ 3 + 42885 * u ^ 2 + 13698 * u + 27 := by
        positivity
      dsimp [U, L, z]
      norm_num [Finset.sum_range_succ]
      nlinarith
    calc
      exp y
          = exp ((1 : ℝ) + u) := by rw [hy_eq]
      _ = exp (1 : ℝ) * exp u := by rw [exp_add]
      _ ≤ (11 / 4 : ℝ) * U := by
            exact mul_le_mul hexp_one_le h_exp_u_le
              (le_of_lt (exp_pos u)) (by norm_num)
      _ ≤ (1 + u) + L := hpoly
      _ ≤ y + exp ((9 / 16 : ℝ) * y ^ 2) := by
            have hz_eq : z = (9 / 16 : ℝ) * y ^ 2 := by
              rw [hy_eq]
            have hL_le_exp_y : L ≤ exp ((9 / 16 : ℝ) * y ^ 2) := by
              simpa [hz_eq] using hL_le_exp
            rw [hy_eq]
            linarith
  have htail_nonneg :
      ∀ {y : ℝ}, 1 ≤ y → exp y ≤ y + exp ((9 / 16 : ℝ) * y ^ 2) := by
    intro y hy
    by_cases hfar : (16 / 9 : ℝ) ≤ y
    · exact htail_far hfar
    · have hyub : y ≤ (16 / 9 : ℝ) := le_of_lt (lt_of_not_ge hfar)
      exact htail_mid hy hyub
  by_cases hy_nonpos : y ≤ 0
  · exact hnonpos hy_nonpos
  · have hy0 : 0 ≤ y := le_of_lt (lt_of_not_ge hy_nonpos)
    by_cases hy_le_one : y ≤ 1
    · exact hcompact hy0 hy_le_one
    · have hy1 : 1 ≤ y := le_of_lt (lt_of_not_ge hy_le_one)
      exact htail_nonneg hy1

end Real


-- Generalization plan (G0):
-- concept/name: fixed-coefficient weighted Young exponential envelope; orig was lemma_4_1_exp_linear_le_exp_large_branch
-- generality used: pointwise scalar real inequality only; no measure, topology, convexity, smoothness, filtration, oracle, or finite-dimensional assumptions
-- portable call pattern: large-tilt MGF branches in stochastic accelerated primal-dual, stochastic mirror-prox, saddle-point, and light-tail martingale proofs; the random increment and tilt scale change while the fixed scalar envelope is reused
-- counterargument checked: not paper-local traceability because the statement is the paper-free weighted Young bound `r*x <= 3*r^2/8 + 2*x^2/3` after exponentiation; not a pure wrapper because it gives the exact no-sqrt call shape needed before conditional square-exponential transport
-- coverage search: rg/lean_search found the SAPD private helper, adjacent staged `exp_mul_le_exp_sq_div_mul_const`, and generic Mathlib `Real.exp_le_exp`; LeanSearch returned exponential monotonicity and hyperbolic-cosine bounds but no exact fixed-coefficient product envelope; this differs from the scale-parameter lemma by exposing the conjugate coefficients directly
-- minimal hypotheses: all already minimal; the theorem quantifies only r x : ℝ

/-- A linear exponential tilt is bounded by a fixed weighted-quadratic product envelope.

This is the exponentiated weighted Young inequality
`r * x <= 3 * r^2 / 8 + (2 / 3) * x^2`, with the exponential of the sum
split into a product.

Layer: Glue | Gap: Level 1 (fixed-coefficient exponential Young envelope)
Proof: certify the weighted Young inequality by nonnegativity of
  `(3 * r - 4 * x)^2`, then apply monotonicity and additivity of the real
  exponential.
Source: Mathlib real exponential monotonicity and ordered-field square arithmetic
Used in: high-probability stochastic optimization large-tilt moment-generating-function bounds
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/key_lemmas/4/proof/large_tilt
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic accelerated primal-dual -/
theorem exp_mul_le_exp_three_eighth_sq_mul_exp_two_thirds_sq
    (r x : ℝ) :
    Real.exp (r * x) ≤
      Real.exp ((3 * r ^ 2) / 8) * Real.exp ((2 / 3) * x ^ 2) := by
  have hquad : r * x ≤ (3 * r ^ 2) / 8 + (2 / 3) * x ^ 2 := by
    nlinarith [sq_nonneg (3 * r - 4 * x)]
  calc
    Real.exp (r * x)
        ≤ Real.exp ((3 * r ^ 2) / 8 + (2 / 3) * x ^ 2) :=
          Real.exp_le_exp.mpr hquad
    _ = Real.exp ((3 * r ^ 2) / 8) * Real.exp ((2 / 3) * x ^ 2) := by
          rw [Real.exp_add]


-- Generalization plan (G0):
-- concept/name: real exponential quadratic envelope under scalar multiplication; orig was lemma_4_1_exp_linear_le_linear_add_exp_small_branch
-- generality used: pointwise scalar real inequality only; no measure, topology, convexity, smoothness, filtration, or oracle assumptions
-- portable call pattern: exponential-supermartingale MGF small-tilt estimates in stochastic accelerated primal-dual, stochastic mirror-prox, stochastic saddle-point, and light-tail SGD proofs; the martingale increment and scale parameters change while the scaled scalar envelope stays fixed
-- counterargument checked: this is a specialization of Real.exp_le_self_add_exp_nine_sixteen_mul_sq, but not a pure rename or paper traceability wrapper; the named product form is the reusable caller-facing inequality needed before conditional-expectation transport
-- coverage search: rg over Mathlib/SOptLib/Staging found only Staging.Real.exp_le_self_add_exp_nine_sixteen_mul_sq and SAPD private helpers; LeanSearch for "for real y exp y less than y plus exp c y squared" returned generic Real.add_one_le_exp, Real.exp_le_exp, Real.exp_bound', and Real.sum_le_exp_of_nonneg, with no scaled product statement
-- minimal hypotheses: all already minimal; the theorem quantifies only r x : ℝ

namespace Real

/-- The real exponential of a product is bounded by the product plus a `9/16`
quadratic exponential envelope.

This is the scaled form of the all-real envelope
`exp y <= y + exp ((9/16) * y^2)`, stated so MGF proofs can rewrite a
linear tilt directly into a variance-scale square term.

Layer: Glue | Gap: Level 1 (scaled real exponential quadratic envelope)
Proof: specialize the all-real `9/16` exponential envelope at `r * x`, then
  normalize the square of the product by ordered-ring algebra.
Source: Mathlib real exponential Taylor bounds and ordered semiring arithmetic
Used in: high-probability stochastic optimization small-tilt moment-generating-function bounds
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/key_lemmas/5
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic accelerated primal-dual -/
theorem exp_mul_le_mul_add_exp_nine_sixteen_mul_sq_mul_sq (r x : ℝ) :
    exp (r * x) ≤ r * x + exp (((9 * r ^ 2) / 16) * x ^ 2) := by
  have h := exp_le_self_add_exp_nine_sixteen_mul_sq (r * x)
  have hcoef :
      (9 / 16 : ℝ) * (r * x) ^ 2 = ((9 * r ^ 2) / 16) * x ^ 2 := by
    ring
  simpa [hcoef] using h

end Real


open scoped BigOperators

-- Generalization plan (G0):
-- concept/name: real negative-exponential quadratic upper envelope; orig was lemma_4_1_exp_neg_le_quadratic_upper
-- generality used: pointwise scalar real inequality only; no measure, topology, convexity, smoothness, finite-dimensional, or oracle assumptions
-- portable call pattern: exponential-supermartingale MGF estimates in stochastic accelerated primal-dual, stochastic mirror-prox, and stochastic saddle-point high-probability bounds; the martingale differences and variance scales change while this half-line scalar envelope stays fixed
-- counterargument checked: not paper-local traceability because the theorem is a standalone real-analysis estimate used inside light-tail/MGF scalar envelopes; not a pure wrapper because Mathlib exposes adjacent lower bounds such as Real.one_sub_le_exp_neg and Taylor estimates, but not this quadratic upper bound
-- coverage search: rg over SOptLib/Staging/Algorithms found only SAPD private helpers and a local helper inside Staging.Real_exp_le_self_add_exp_nine_sixteen_mul_sq; LeanSearch query "for all real t exp negative t less than one minus t plus t squared over two" returned Real.one_sub_le_exp_neg, Real.exp_bound', Real.sum_le_exp_of_nonneg, and norm_exp_sub_one_sub_id_le, with no full half-line statement
-- minimal hypotheses: the nonnegativity hypothesis 0 ≤ t is necessary for the one-sided alternating-style bound; all other assumptions are absent

namespace Real

/-- For nonnegative `t`, the negative exponential is bounded by the quadratic
Taylor truncation `1 - t + t^2 / 2`.

This half-line scalar estimate is the reusable negative-branch ingredient in
light-tail moment-generating-function envelopes.

Layer: Glue | Gap: Level 1 (negative exponential quadratic upper envelope)
Proof: compare `1 + t + t^2 / 2` with `exp t` using Mathlib's lower Taylor
  bound, then multiply by the nonnegative quadratic conjugate and invert the
  positive exponential.
Source: Mathlib real exponential Taylor lower bounds and ordered field arithmetic
Used in: high-probability stochastic optimization exponential-supermartingale moment bounds
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/key_lemmas/5
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic accelerated primal-dual -/
theorem exp_neg_le_one_sub_add_sq_half {t : ℝ} (ht : 0 ≤ t) :
    exp (-t) ≤ 1 - t + t ^ 2 / 2 := by
  let q : ℝ := 1 + t + t ^ 2 / 2
  let p : ℝ := 1 - t + t ^ 2 / 2
  have hsum := sum_le_exp_of_nonneg ht 3
  have hq_le_exp : q ≤ exp t := by
    dsimp [q]
    norm_num [Finset.sum_range_succ] at hsum ⊢
    linarith
  have hp_nonneg : 0 ≤ p := by
    dsimp [p]
    nlinarith [sq_nonneg (t - 1)]
  have hpq : 1 ≤ p * q := by
    dsimp [p, q]
    nlinarith [sq_nonneg (t ^ 2)]
  have hmul : 1 ≤ p * exp t := by
    have hmul_le : p * q ≤ p * exp t :=
      mul_le_mul_of_nonneg_left hq_le_exp hp_nonneg
    exact hpq.trans hmul_le
  have hexp_pos : 0 < exp t := exp_pos t
  have hdiv : (exp t)⁻¹ ≤ p := by
    rw [inv_le_iff_one_le_mul₀ hexp_pos]
    simpa [mul_comm] using hmul
  simpa [exp_neg, p] using hdiv

end Real


-- Generalization plan (G0):
-- concept/name: completed-square exponential domination; orig was lemma_4_1_exp_tilt_le_const_mul_exp_sq_div_sq
-- generality used: pointwise scalar real inequality only; no measure, topology, convexity, smoothness, filtration, oracle, or finite-dimensional assumptions
-- portable call pattern: light-tail and sub-Gaussian MGF integrability steps in stochastic accelerated primal-dual, stochastic mirror-prox, stochastic saddle-point, and SGD martingale proofs; the random increment and variance scale change while the scalar completed-square bound stays fixed
-- counterargument checked: not paper-local traceability because the statement is a standalone real-analysis Young/completing-square inequality used before expectation transport; not a caller-side expression because it packages the nontrivial normalization by a positive scale into the exact exponential product needed by MGF proofs
-- coverage search: rg over SOptLib/Staging/Algorithms found only SAPD private helpers and adjacent exponential-envelope lemmas; LeanSearch query "real exponential theta x less equal exp theta squared sigma squared over 4 times exp x squared over sigma squared" returned Real.exp monotonicity and generic exponential lemmas, with no full completed-square product statement
-- minimal hypotheses: only 0 < sigma is required to divide by sigma and normalize the square; x and theta are arbitrary real scalars

/-- A linear exponential tilt is dominated by a completed-square quadratic
envelope at any positive scale.

For `0 < sigma`, Young's inequality in the normalized form
`theta * x <= x^2 / sigma^2 + theta^2 * sigma^2 / 4` exponentiates to the
displayed product bound.

Layer: Glue | Gap: Level 1 (completed-square exponential domination)
Proof: expand the nonnegative square `(x / sigma - theta * sigma / 2)^2`,
  derive the normalized Young inequality, then use monotonicity and additivity
  of the real exponential.
Source: Mathlib real exponential monotonicity and ordered-field square arithmetic
Used in: high-probability stochastic optimization light-tail MGF integrability bounds
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/key_lemmas/3/proof/0
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic accelerated primal-dual -/
theorem exp_mul_le_exp_sq_div_mul_const
    (x sigma theta : ℝ) (hsigma : 0 < sigma) :
    Real.exp (theta * x) ≤
      Real.exp ((theta ^ 2 * sigma ^ 2) / 4) *
        Real.exp (x ^ 2 / sigma ^ 2) := by
  have hsigma_ne : sigma ≠ 0 := ne_of_gt hsigma
  have hsq : 0 ≤ (x / sigma - theta * sigma / 2) ^ 2 :=
    sq_nonneg (x / sigma - theta * sigma / 2)
  have hiden :
      (x / sigma - theta * sigma / 2) ^ 2 =
        x ^ 2 / sigma ^ 2 - theta * x + (theta ^ 2 * sigma ^ 2) / 4 := by
    field_simp [hsigma_ne]
    ring
  have hineq : theta * x ≤ x ^ 2 / sigma ^ 2 + (theta ^ 2 * sigma ^ 2) / 4 := by
    nlinarith [hiden ▸ hsq]
  calc
    Real.exp (theta * x)
        ≤ Real.exp (x ^ 2 / sigma ^ 2 + (theta ^ 2 * sigma ^ 2) / 4) :=
          Real.exp_le_exp.mpr hineq
    _ = Real.exp ((theta ^ 2 * sigma ^ 2) / 4) *
          Real.exp (x ^ 2 / sigma ^ 2) := by
        rw [Real.exp_add, mul_comm]


open Topology

-- Generalization plan (G0):
-- concept/name: compact absolute boundedness of a convex function on an interior
--   subset; orig was `norm_bounded_on_compact_subset_of_interior_for_convexOn`,
--   renamed to `ConvexOn.exists_norm_bound_on_compact_subset_interior`.
-- generality used: real-valued `ConvexOn ℝ K f` on a finite-dimensional real
--   normed vector space, compact `C`, and pointwise inclusion
--   `C ⊆ interior K`; no measure, smoothness, oracle, or algorithm state is used.
-- portable call pattern: stochastic mirror descent, accelerated primal-dual,
--   and composite prox proofs that need a finite absolute bound for a convex
--   penalty, gap component, or value term after restricting a compact feasible
--   subset to the ordinary carrier interior; `E`, `K`, `C`, and `f` vary while
--   the conclusion stays the same.
-- counterargument checked: not paper-local traceability and not a pure wrapper;
--   it packages the recurring composition of convex interior continuity with
--   compact continuous absolute boundedness in the exact statement callers use.
-- coverage search: queried `ConvexOn continuousOn_interior compact norm bound`,
--   `convex function bounded on compact subset of interior norm absolute value`,
--   and catalog tokens `ConvexOn interior compact norm bound`; top hits were
--   Mathlib `ConvexOn.continuousOn_interior`, Mathlib local
--   `ConvexOn.isBoundedUnder_abs`, and SOptLib
--   `exists_nonneg_norm_bound_of_isCompact_of_continuousOn`, all partial only.
-- minimal hypotheses: all already minimal relative to Mathlib's finite-dimensional
--   interior continuity theorem; compactness and subset inclusion are used
--   directly, and no nonemptiness assumption is needed.

/-- A convex real-valued function has a finite absolute bound on compact subsets
of the ordinary interior of its carrier.

Layer: Glue | Gap: Level 1 (convex interior compact absolute bound)
Proof: use `ConvexOn.continuousOn_interior`, restrict continuity to the compact
  subset, then apply the compact continuous norm-bound theorem for real-valued
  functions.
Source: Mathlib convex-analysis continuity and SOptLib compact norm-bound APIs
Used in: stochastic accelerated primal-dual convex penalty absolute-bound step on
  compact feasible subsets inside the carrier interior
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/assumptions/0/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem ConvexOn.exists_norm_bound_on_compact_subset_interior
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {C K : Set E} {f : E → ℝ}
    (hfconv : ConvexOn ℝ K f) (hCcompact : IsCompact C) (hCsub : C ⊆ interior K) :
    ∃ B : ℝ, ∀ x, x ∈ C → ‖f x‖ ≤ B := by
  have hcontInterior : ContinuousOn f (interior K) :=
    ConvexOn.continuousOn_interior hfconv
  have hcontC : ContinuousOn f C :=
    hcontInterior.mono hCsub
  obtain ⟨B, _hB_nonneg, hB⟩ :=
    exists_nonneg_norm_bound_of_isCompact_of_continuousOn f hCcompact hcontC
  exact ⟨B, hB⟩


open scoped InnerProductSpace

-- Generalization plan (G0):
-- concept/name: upper-semicontinuity of an affine inner-product section minus
--   a lower-semicontinuous term; orig was local `husc` inside
--   `saddle_argmax_upperSemicontinuousOn`.
-- generality used: arbitrary real inner-product normed additive group `E`,
--   carrier set `s`, scalar offset `c`, vector coefficient `a`, and lsc real
--   function `g`; no measure, compactness, convexity, smoothness, oracle, or
--   finite-dimensional assumptions.
-- portable call pattern: saddle-section maximization and dual value
--   attainment proofs where the affine coupling vector and nonsmooth penalty
--   change, while compact maximum extraction needs the same
--   `c + ⟪a, y⟫ - g y` upper-semicontinuity certificate.
-- counterargument checked: the proof is a short composition of Mathlib
--   semicontinuity APIs, but it is not a pure rename because no single
--   Mathlib/SOptLib theorem states the recurring affine-minus-lsc objective
--   section needed before maximizer extraction.
-- coverage search: queried `UpperSemicontinuousOn add LowerSemicontinuousOn
--   neg continuous inner`, LeanSearch for continuous affine plus negative lsc,
--   and scanned staged saddle-gap/prox lsc entries; hits were
--   `Continuous.comp_lowerSemicontinuousOn_antitone`,
--   `UpperSemicontinuousOn.add`, and
--   `saddle_gap_comparison_right_upperSemicontinuousOn`, giving partial but
--   not full coverage.
-- minimal hypotheses: lsc is assumed only on `s`; the affine part is
--   continuous without additional hypotheses; no finite-dimensional,
--   compactness, convexity, or closed-carrier assumptions are used.

/-- An affine inner-product section minus an lsc term is upper-semicontinuous
on a carrier.

For a real Hilbert-space carrier, the continuous affine term
`y ↦ c + ⟪a, y⟫` is upper-semicontinuous, and negating a
lower-semicontinuous real function produces an upper-semicontinuous term.

Layer: Glue | Gap: Level 0 (affine-minus-lsc upper-semicontinuity closure)
Proof: convert the affine inner-product term to upper-semicontinuity, turn the
  lsc term into an upper-semicontinuous negative by the antitone continuous
  negation map, then use Mathlib's binary `UpperSemicontinuousOn.add`.
Source: Mathlib semicontinuity closure APIs and real inner-product continuity
Used in: stochastic accelerated primal-dual saddle-section maximizer
  extraction over a feasible dual carrier
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/setup/problem/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem upperSemicontinuousOn_const_add_inner_sub_lsc
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {s : Set E} (c : ℝ) (a : E) {g : E → ℝ}
    (hg : LowerSemicontinuousOn g s) :
    UpperSemicontinuousOn (fun y : E => c + ⟪a, y⟫_ℝ - g y) s := by
  have hcont_affine : ContinuousOn (fun y : E => c + ⟪a, y⟫_ℝ) s := by
    exact (continuous_const.add (continuous_const.inner continuous_id)).continuousOn
  have husc_affine :
      UpperSemicontinuousOn (fun y : E => c + ⟪a, y⟫_ℝ) s :=
    hcont_affine.upperSemicontinuousOn
  have hneg_antitone : Antitone (fun r : ℝ => -r) := by
    intro x y hxy
    exact neg_le_neg hxy
  have husc_neg : UpperSemicontinuousOn (fun y : E => -g y) s := by
    simpa [Function.comp_def] using
      (continuous_neg.comp_lowerSemicontinuousOn_antitone hg hneg_antitone)
  have hsum := husc_affine.add husc_neg
  simpa [sub_eq_add_neg, add_assoc] using hsum
