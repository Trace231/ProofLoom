-- SOptLib/Glue/Analysis.lean
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Topology
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

/-- A lower bound by a negative-log schedule for a contraction gives an inverse scale bound.

If `0 < alpha < 1` and `s` is at least `-log B / log alpha`, then the
contraction power `alpha ^ s` is at most `B⁻¹`.

Layer: Glue | Gap: Level 0 (contraction power bound from logarithmic ceiling)
Proof: use `Nat.le_ceil`, multiply by the negative logarithm of the contraction
  with reversed order, exponentiate, and convert between natural powers and
  real exponentials.
Source: Mathlib real logarithm, natural ceiling, exponential monotonicity, and ordered-field APIs
Used in: randomized accelerated proximal-point inner-loop contraction length selection
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec/parameters
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, randomized accelerated proximal-point method -/
theorem pow_nat_le_inv_of_neg_log_div_log_le
    {alpha B : ℝ} {s : ℕ}
    (halpha_pos : 0 < alpha) (halpha_lt_one : alpha < 1) (hB_pos : 0 < B)
    (hs_le : -Real.log B / Real.log alpha ≤ (s : ℝ)) :
    alpha ^ s ≤ B⁻¹ := by
  have hlog_alpha_neg : Real.log alpha < 0 := (Real.log_neg_iff halpha_pos).mpr halpha_lt_one
  have hlog_alpha_ne : Real.log alpha ≠ 0 := ne_of_lt hlog_alpha_neg
  have hmul :
      (s : ℝ) * Real.log alpha ≤
        (-Real.log B / Real.log alpha) * Real.log alpha := by
    simpa [mul_comm] using
      (mul_le_mul_of_nonpos_right hs_le (le_of_lt hlog_alpha_neg))
  have hmul' : (s : ℝ) * Real.log alpha ≤ -Real.log B := by
    calc
      (s : ℝ) * Real.log alpha ≤
          (-Real.log B / Real.log alpha) * Real.log alpha := hmul
      _ = -Real.log B := by
        simp [hlog_alpha_ne]
  have hexp : Real.exp ((s : ℝ) * Real.log alpha) ≤ Real.exp (-Real.log B) :=
    Real.exp_le_exp.mpr hmul'
  calc
    alpha ^ s = alpha ^ ((s : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]
    _ = Real.exp (Real.log alpha * (s : ℝ)) := by
      rw [Real.rpow_def_of_pos halpha_pos]
    _ = Real.exp ((s : ℝ) * Real.log alpha) := by
      ring_nf
    _ ≤ Real.exp (-Real.log B) := hexp
    _ = B⁻¹ := by
      rw [Real.exp_neg, Real.exp_log hB_pos]

/-- A continuous objective on a nonempty closed set attains a constrained minimum
from a closed-ball coercive tail bound.

The theorem truncates the feasible set to `X ∩ closedBall z R`, minimizes on the
compact truncation, and uses the tail lower bound outside the ball to extend the
minimum certificate back to all of `X`.

Layer: Glue | Gap: Level 1 (closed-ball coercive constrained minimum existence)
Proof: choose the tail radius at the base value, minimize on the compact
  intersection of the closed carrier with the closed ball, then split an
  arbitrary feasible point by membership in that ball.
Source: Mathlib proper metric compact-ball API and compact extreme-value theorem
Used in: finite-dimensional stochastic proximal subproblem existence from a
  closed-domain coercive lower tail
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
theorem exists_isMinOn_of_closed_coercive_closedBall
    {E : Type*} [PseudoMetricSpace E] [ProperSpace E]
    {X : Set E} (hX_closed : IsClosed X) (x0 z : E) (hx0 : x0 ∈ X)
    (F : E → ℝ) (hcont : ContinuousOn F X)
    (htail : ∃ R : ℝ, dist x0 z ≤ R ∧
      ∀ x : E, x ∈ X → R ≤ dist x z → F x0 ≤ F x) :
    ∃ x : E, x ∈ X ∧ IsMinOn F X x := by
  classical
  obtain ⟨R, hx0_le_R, htail⟩ := htail
  let K : Set E := X ∩ Metric.closedBall z R
  have hK_compact : IsCompact K := by
    have hcompact_ball : IsCompact (Metric.closedBall z R) := isCompact_closedBall z R
    have hcompact_ball_inter_X : IsCompact (Metric.closedBall z R ∩ X) :=
      hcompact_ball.inter_right hX_closed
    simpa [K, Set.inter_comm, Set.inter_assoc] using hcompact_ball_inter_X
  have hx0_ball : x0 ∈ Metric.closedBall z R := by
    simpa [Metric.mem_closedBall] using hx0_le_R
  have hK_nonempty : K.Nonempty := ⟨x0, hx0, hx0_ball⟩
  have hcontK : ContinuousOn F K := hcont.mono (by
    intro x hx
    exact hx.1)
  obtain ⟨xmin, hxminK, hxmin_min⟩ := hK_compact.exists_isMinOn hK_nonempty hcontK
  refine ⟨xmin, hxminK.1, ?_⟩
  intro y hy
  by_cases hyball : y ∈ Metric.closedBall z R
  · exact hxmin_min ⟨hy, hyball⟩
  · have hxmin_le_x0 : F xmin ≤ F x0 := hxmin_min ⟨hx0, hx0_ball⟩
    have hnot_dist : ¬ dist y z ≤ R := by
      simpa [Metric.mem_closedBall] using hyball
    have hR_le_dist : R ≤ dist y z := le_of_lt (lt_of_not_ge hnot_dist)
    exact le_trans hxmin_le_x0 (htail y hy hR_le_dist)

/-- A function constant on fibers of a finite-range measurable observable is measurable.

If `Y` is measurable, has finite range, and `Z` depends only on the value of
`Y`, then `Z` is measurable. The proof factors `Z` through the finite subtype
`Set.range Y`, where every map out is measurable.

Layer: Glue | Gap: Level 1 (finite-observable fiber-factor measurability)
Proof: replace the observable by its range subtype, prove that subtype-valued
  map measurable by checking singleton fibers, and compose with an arbitrary
  map out of the finite range.
Source: Mathlib measurable singleton classes, finite-domain measurability, and
  subtype range APIs
Used in: randomized accelerated proximal point finite-prefix observables for
  fixed inner-loop scalar integrability
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal point -/
theorem measurable_of_finite_range_fiber_const
    {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace β]
    {Y : Ω → α} {Z : Ω → β}
    (hY : Measurable Y)
    (hfin : (Set.range Y).Finite)
    (hconst : ∀ ⦃ω ω' : Ω⦄, Y ω = Y ω' → Z ω = Z ω') :
    Measurable Z := by
  classical
  haveI : Fintype {y : α // y ∈ Set.range Y} := hfin.fintype
  let Yrange : Ω → {y : α // y ∈ Set.range Y} := fun ω => ⟨Y ω, ⟨ω, rfl⟩⟩
  let G : {y : α // y ∈ Set.range Y} → β := fun y =>
    Z (Classical.choose y.2)
  have hYrange : Measurable Yrange := by
    refine measurable_to_countable ?_
    intro ω
    have hset : MeasurableSet (Y ⁻¹' {Y ω}) :=
      hY (measurableSet_singleton (Y ω))
    convert hset using 1
    ext ω'
    simp [Yrange]
  have hG : Measurable G := measurable_of_finite G
  have hZG : Z = G ∘ Yrange := by
    funext ω
    dsimp [Function.comp, G, Yrange]
    exact hconst (Classical.choose_spec (show Y ω ∈ Set.range Y from ⟨ω, rfl⟩)).symm
  rw [hZG]
  exact hG.comp hYrange

/-- A representative chosen from the range of a key evaluates a fiber-constant kernel like the original point.

If an indexed kernel `raw` is constant on the fibers of `Z`, then replacing a
point by the `Classical.choose` representative of the same value in `Set.range Z`
does not change any indexed evaluation.  The `else` branch is unreachable for
actual keys, so only a zero element in the codomain is needed to type the if.

Layer: Glue | Gap: Level 1 (range representative evaluation for fiber-constant kernels)
Proof: split on the range-membership decidable proposition; the positive branch
  applies fiber constancy to `Classical.choose_spec`, and the negative branch
  contradicts membership witnessed by the original point.
Source: Mathlib set range and classical choice APIs
Used in: randomized proximal-point representative scalar kernels over finite sample-prefix states
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, randomized accelerated proximal-point method -/
theorem rangeRepresentative_eval_of_const_on_fibers
    {Ω W ι β : Type*} [Zero β]
    (Z : Ω → W) (raw : Ω → ι → β)
    [DecidablePred (fun q => q ∈ Set.range Z)]
    (hconst :
      ∀ ⦃ω ω' : Ω⦄, Z ω = Z ω' → ∀ j : ι, raw ω j = raw ω' j) :
    ∀ (ω : Ω) (j : ι),
      (if hq : Z ω ∈ Set.range Z then raw (Classical.choose hq) j else 0) =
        raw ω j := by
  intro ω j
  by_cases hq : Z ω ∈ Set.range Z
  · rw [dif_pos hq]
    exact hconst (Classical.choose_spec hq) j
  · exact False.elim (hq ⟨ω, rfl⟩)

/-- The negative-log natural-ceiling schedule is monotone in the target scale.

For a contraction base `alpha ∈ (0, 1)`, increasing the positive target scale
from `A` to `B` can only increase the schedule
`Nat.ceil (-log target / log alpha)`.

Layer: Glue | Gap: Level 0 (negative-log ceiling schedule monotonicity)
Proof: apply monotonicity of `log`, reverse order by negation, reverse again by
  multiplying by the nonpositive inverse of `log alpha`, and finish with
  `Nat.ceil_mono`.
Source: Mathlib real logarithm, ordered-field arithmetic, and natural ceiling APIs
Used in: randomized accelerated proximal-point inner-loop contraction length comparison
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec/parameters
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, randomized accelerated proximal-point method -/
theorem natCeil_neg_log_div_log_mono_of_base_lt_one
    {alpha A B : ℝ}
    (halpha_pos : 0 < alpha) (halpha_lt_one : alpha < 1)
    (hA_pos : 0 < A) (hAB : A ≤ B) :
    Nat.ceil (-Real.log A / Real.log alpha) ≤
      Nat.ceil (-Real.log B / Real.log alpha) := by
  have hlog_alpha_neg : Real.log alpha < 0 :=
    (Real.log_neg_iff halpha_pos).mpr halpha_lt_one
  have hlog_le : Real.log A ≤ Real.log B :=
    Real.log_le_log hA_pos hAB
  have hneg : -Real.log B ≤ -Real.log A := by
    linarith
  have hinv_nonpos : (Real.log alpha)⁻¹ ≤ 0 :=
    le_of_lt (inv_lt_zero'.mpr hlog_alpha_neg)
  have hreal :
      -Real.log A / Real.log alpha ≤ -Real.log B / Real.log alpha := by
    simpa [div_eq_mul_inv] using
      (mul_le_mul_of_nonpos_right hneg hinv_nonpos)
  exact Nat.ceil_mono hreal
