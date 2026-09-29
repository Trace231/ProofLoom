import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Convex.Approximation
import SOptLib.Model.Carrier
-- SOptLib/Glue/Analysis.lean
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Seminorm
import Mathlib.Analysis.SpecialFunctions.Log.Base
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
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Range
import SOptLib.Glue.Algebra
import SOptLib.Glue.Calculus


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

/-- The scalar bound `(1 + x)^a ≤ exp (a * x)` for nonnegative `x` and `a`.

Layer: Glue | Gap: Level 2 (packaged `log`-linearization bound for `rpow`)
Proof: Rewrite the left-hand side as an exponential via `Real.rpow_def_of_pos`,
bound `log (1 + x)` by `x` using `log t ≤ t - 1`, then multiply by the
nonnegative exponent `a`.
Source: elementary inequality `log (1 + x) ≤ x`
Used in: Gaussian moment upper bounds -/
theorem one_add_rpow_le_exp_mul
    (x a : ℝ) (hx : 0 ≤ x) (ha : 0 ≤ a) :
    (1 + x) ^ a ≤ Real.exp (a * x) := by
  have hbase_pos : 0 < 1 + x := by linarith
  rw [Real.rpow_def_of_pos hbase_pos]
  apply Real.exp_le_exp.mpr
  have hlog : Real.log (1 + x) ≤ x := by
    linarith [Real.log_le_sub_one_of_pos hbase_pos]
  simpa [mul_comm] using mul_le_mul_of_nonneg_right hlog ha

/-- The scalar appendix bound
`t^p * exp (-(τ/2) * t^2) ≤ (p / (τ * e))^(p/2)` for nonnegative `t`,
positive exponent `p`, and positive damping `τ`.

Layer: Glue | Gap: Level 2 (scalar exponential-envelope inequality)
Proof: Introduce `u = τ * t^2 / p`, use `u * exp (-u) ≤ exp (-1)`, rewrite
both factors in terms of `u`, and combine them with `Real.mul_rpow`.
Source: Nesterov-Spokoiny Gaussian moment appendix bound
Used in: Gaussian moment upper bounds -/
theorem rpow_mul_exp_neg_mul_sq_le
    (t p τ : ℝ) (ht : 0 ≤ t) (hp : 0 < p) (hτ0 : 0 < τ) :
    t ^ p * Real.exp (-(τ / 2) * t ^ 2) ≤ (p / (τ * Real.exp 1)) ^ (p / 2) := by
  rcases eq_or_lt_of_le ht with rfl | ht_pos
  · simp [Real.zero_rpow hp.ne']
    positivity
  · set u := τ * t ^ 2 / p with hu_def
    have hu_pos : 0 < u := by positivity
    have h_key : u * Real.exp (-u) ≤ Real.exp (-1) := by
      have h_ule : u ≤ Real.exp (u - 1) := by
        linarith [Real.add_one_le_exp (u - 1)]
      calc
        u * Real.exp (-u)
            ≤ Real.exp (u - 1) * Real.exp (-u) :=
              mul_le_mul_of_nonneg_right h_ule (Real.exp_pos _).le
        _ = Real.exp (-1) := by
              rw [← Real.exp_add]
              ring_nf
    have ht2_eq : t ^ 2 = u * p / τ := by
      rw [hu_def]
      field_simp
    have htp_eq : t ^ p = u ^ (p / 2) * (p / τ) ^ (p / 2) := by
      have : t ^ p = (t ^ 2 : ℝ) ^ (p / 2) := by
        rw [← Real.rpow_natCast t 2, ← Real.rpow_mul ht]
        congr 1
        ring
      rw [this, ht2_eq, show u * p / τ = u * (p / τ) by ring]
      exact Real.mul_rpow hu_pos.le (div_nonneg hp.le hτ0.le)
    have hexp_val : -(τ / 2) * (t ^ 2 : ℝ) = -(u * (p / 2)) := by
      rw [hu_def]
      field_simp
    rw [show (-(τ / 2) * t ^ 2 : ℝ) = -(τ / 2) * (t ^ 2 : ℝ) from rfl, hexp_val, htp_eq]
    rw [show -(u * (p / 2)) = Real.log (Real.exp (-u)) * (p / 2) by
      rw [Real.log_exp]
      ring]
    rw [← Real.rpow_def_of_pos (Real.exp_pos _)]
    have hmul_rpow :
        u ^ (p / 2) * Real.exp (-u) ^ (p / 2) = (u * Real.exp (-u)) ^ (p / 2) :=
      (Real.mul_rpow hu_pos.le (Real.exp_pos (-u)).le).symm
    calc
      u ^ (p / 2) * (p / τ) ^ (p / 2) * Real.exp (-u) ^ (p / 2)
          = (p / τ) ^ (p / 2) * (u ^ (p / 2) * Real.exp (-u) ^ (p / 2)) := by
              ring
      _ = (p / τ) ^ (p / 2) * (u * Real.exp (-u)) ^ (p / 2) := by
            rw [hmul_rpow]
      _ ≤ (p / τ) ^ (p / 2) * Real.exp (-1) ^ (p / 2) := by
            exact mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow (by positivity) h_key (by linarith))
              (by positivity)
      _ = (p / τ * Real.exp (-1)) ^ (p / 2) := by
            exact (Real.mul_rpow (by positivity) (by positivity)).symm
      _ = (p / (τ * Real.exp 1)) ^ (p / 2) := by
            congr 1
            rw [Real.exp_neg]
            field_simp

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

-- Batch 2 promoted from .sgd_phase3_staging/SOptLib/Glue/measurable_sub_const_of_continuousOn_comp_measurable_mem.lean
-- Generalization plan (G0):
-- concept/name: measurability of a constant-shifted carrier observable; orig was `objectiveGap_measurable_of_outerStateAdapted`
-- generality used: arbitrary measurable source space and Borel topological target; no measure, convexity, smoothness, oracle, filtration, or finite-dimensional assumptions
-- portable call pattern: objective-gap or residual measurability for any stochastic optimization algorithm whose feasible-valued output process is measurable while the continuous objective and baseline constant vary
-- counterargument checked: not paper-local traceability because the statement removes all SCGS notation and packages the recurring carrier-membership composition plus constant shift; not a pure duplicate of `continuous_subtype_of_continuousOn_ambient`, which proves continuity on the subtype but not measurability along a process
-- coverage search: checked `continuousOn measurable comp mem sub const`, SOptLib `measurable_left_section_of_continuousOn_univ`, `measurable_comp_real`, and `continuous_subtype_of_continuousOn_ambient`; Mathlib semantic search was unavailable (HTTP 502), and no existing hit covered the restricted-carrier composition with subtract-constant conclusion
-- minimal hypotheses: all already minimal; the proof uses only `Measurable y`, `ContinuousOn f X`, and pointwise membership `∀ ω, y ω ∈ X`

/-- A constant shift of a continuous-on carrier observable is measurable along a feasible-valued process.

If `f` is continuous on a carrier `X`, `y` is measurable, and every `y ω` lies
in `X`, then `ω ↦ f (y ω) - c` is measurable.

Layer: Glue | Gap: Level 1 (restricted continuous observable measurability)
Proof: restrict the continuous-on ambient map to the carrier subtype, make the
  process subtype-valued using its pointwise membership proof, compose, and
  subtract the measurable constant.
Source: Mathlib subtype topology, Borel measurability of continuous maps, and
  measurable-function algebra APIs
Used in: stochastic conditional-gradient sliding objective-gap measurability for
  feasible output processes
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
theorem measurable_sub_const_of_continuousOn_comp_measurable_mem
    {Ω E : Type*} [MeasurableSpace Ω]
    [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    (X : Set E) (f : E → ℝ) (y : Ω → E) (c : ℝ)
    (hf : ContinuousOn f X) (hy : Measurable y) (hy_mem : ∀ ω, y ω ∈ X) :
    Measurable (fun ω => f (y ω) - c) := by
  have hfCarrier : Continuous (fun x : {x : E // x ∈ X} => f x.1) :=
    continuous_subtype_of_continuousOn_ambient
      (X := X) (fun x : {x : E // x ∈ X} => f x.1) f hf (by
        intro x
        rfl)
  have hySubtype :
      Measurable (fun ω => (⟨y ω, hy_mem ω⟩ : {x : E // x ∈ X})) :=
    Measurable.subtype_mk hy
  exact (hfCarrier.measurable.comp hySubtype).sub measurable_const
-- Batch 5 promoted from Staging/Set_Finite_range_of_finite_range_fiber_const.lean
/-- A fiber-constant function has finite range when its key has finite range.

If `Y` has finite range and `Z` is constant on every fiber of `Y`, then the
range of `Z` is finite. The proof factors `Z` through the finite subtype
`Set.range Y` by choosing one representative from each key value.

Layer: Glue | Gap: Level 1 (finite-observable fiber-factor range finiteness)
Proof: choose a representative from each value in the finite range of `Y`, map
  the finite subtype `Set.range Y` through `Z`, and show every value of `Z`
  lies in that image using fiber constancy.
Source: Mathlib finite set range APIs and subtype representative selection
Used in: generated variance-reduced accelerated state finite-range propagation
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem Set.Finite.range_of_finite_range_fiber_const
    {Omega alpha beta : Type*} {Y : Omega -> alpha} {Z : Omega -> beta}
    (hfin : (Set.range Y).Finite)
    (hconst : forall ⦃omega omega' : Omega⦄, Y omega = Y omega' -> Z omega = Z omega') :
    (Set.range Z).Finite := by
  classical
  haveI : Fintype {y : alpha // y ∈ Set.range Y} := Set.Finite.fintype hfin
  let G : {y : alpha // y ∈ Set.range Y} -> beta := fun y =>
    Z (Classical.choose y.2)
  have hsubset : Set.range Z <= Set.range G := by
    rintro z ⟨omega, rfl⟩
    refine ⟨⟨Y omega, ⟨omega, rfl⟩⟩, ?_⟩
    dsimp [G]
    exact hconst (Classical.choose_spec
      (show Y omega ∈ Set.range Y from ⟨omega, rfl⟩))
  exact Set.Finite.subset (Set.finite_range G) hsubset

-- Batch 5 promoted from Staging/four_lt_sqrt_twelve_mul_div_of_lt_three_mul_div_four_mul.lean
/-- A small `3/4` threshold forces the normalized `sqrt(12)` ratio to exceed four.

If a positive scale `m` is below `3*L/(4*mu)` with `mu > 0`, then the
square-root normalization `sqrt (12*L/(m*mu))` is strictly larger than `4`.

Layer: Glue | Gap: Level 0 (scalar square-root threshold normalization)
Proof: clear the positive denominator `4*mu`, transform the goal with
  `Real.lt_sqrt_of_sq_lt`, and finish the resulting ordered-ring arithmetic.
Source: Mathlib real square-root inequalities and ordered-field arithmetic
Used in: variance-reduced accelerated-gradient small-regime tail cutoff
  normalization
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/key_lemmas/18
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem four_lt_sqrt_twelve_mul_div_of_lt_three_mul_div_four_mul
    {m L mu : Real}
    (hm : 0 < m) (hmu : 0 < mu)
    (hsmall : m < 3 * L / (4 * mu)) :
    (4 : Real) < Real.sqrt (12 * L / (m * mu)) := by
  have hden_pos : 0 < m * mu := mul_pos hm hmu
  have hfour_mu_pos : 0 < 4 * mu := by positivity
  have hsmall_clear : m * (4 * mu) < 3 * L :=
    (lt_div_iff₀ hfour_mu_pos).1 hsmall
  have hsquare : (4 : Real) ^ 2 < 12 * L / (m * mu) := by
    rw [lt_div_iff₀ hden_pos]
    nlinarith
  exact Real.lt_sqrt_of_sq_lt hsquare

-- Batch 5 promoted from Staging/Real_exp_le_one_add_two_mul_of_mem_Icc_zero_one.lean
namespace Real

/-- On the real unit interval, `exp x` is bounded by the line `1 + 2 * x`.

This packages the common scalar step turning an exponential estimate with a
unit-sized nonnegative argument into a linear estimate with constant `2`.

Layer: Glue | Gap: Level 0 (real exponential unit-interval linearization)
Proof: apply Mathlib's Taylor upper bound `Real.exp_bound'` with three terms,
  then use `x ^ 2 ≤ x` and `x ^ 3 ≤ x` on `0 ≤ x ≤ 1` to close by arithmetic.
Source: Mathlib real exponential Taylor bounds in `Analysis.Complex.Exponential`
Used in: accelerated finite-sum linear-tail power bounds via `exp (Tδ)`
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/key_lemmas/18/proof/6
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, variance-reduced accelerated gradient descent -/
theorem exp_le_one_add_two_mul_of_mem_Icc_zero_one
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    exp x ≤ 1 + 2 * x := by
  rcases hx with ⟨hx0, hx1⟩
  have hbound :=
    Real.exp_bound' (x := x) hx0 hx1 (n := 3) (by norm_num)
  have hx_sq_le : x ^ 2 ≤ x := by
    have hmul := mul_le_mul_of_nonneg_left hx1 hx0
    simpa [pow_two] using hmul
  have hx_cube_le : x ^ 3 ≤ x := by
    have hsq_nonneg : 0 ≤ x ^ 2 := sq_nonneg x
    have hmul := mul_le_mul_of_nonneg_left hx1 hsq_nonneg
    have hx3_le_x2 : x ^ 3 ≤ x ^ 2 := by
      simpa [pow_succ, pow_two, mul_assoc, mul_comm, mul_left_comm] using hmul
    exact hx3_le_x2.trans hx_sq_le
  calc
    exp x ≤
        (∑ m ∈ Finset.range 3, x ^ m / (m.factorial : ℕ)) +
          x ^ 3 * (3 + 1) / ((Nat.factorial 3 : ℕ) * 3) := hbound
    _ = 1 + x + x ^ 2 / 2 + (2 / 9) * x ^ 3 := by
      norm_num [Finset.sum_range_succ, pow_succ, Nat.factorial]
      ring
    _ ≤ 1 + 2 * x := by
      nlinarith

end Real

-- Batch 5 promoted from Staging/one_add_nonneg_pow_le_one_add_two_mul_of_mul_le_one.lean
/-- A small nonnegative increment has at most linear natural-power growth.

If `0 <= delta` and the accumulated budget `T * delta` is at most one, then
`(1 + delta)^T` is bounded by `1 + 2 * T * delta`.

Layer: Glue | Gap: Level 0 (small-budget real natural-power upper bound)
Proof: compare `(1 + delta)^T` to `exp (T * delta)` using
  `log (1 + delta) <= delta`, then apply the unit-interval linear bound
  `exp x <= 1 + 2 * x`.
Source: Mathlib real logarithm and exponential order bounds
Used in: accelerated finite-sum linear-tail geometric growth control
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/key_lemmas/18/proof/6
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, variance-reduced accelerated gradient descent -/
theorem one_add_nonneg_pow_le_one_add_two_mul_of_mul_le_one
    (T : Nat) {delta : ℝ} (hdelta : 0 <= delta)
    (hbudget : (T : ℝ) * delta <= 1) :
    (1 + delta) ^ T <= 1 + 2 * (T : ℝ) * delta := by
  have hT_nonneg : 0 <= (T : ℝ) := by positivity
  have hx0 : 0 <= (T : ℝ) * delta :=
    mul_nonneg hT_nonneg hdelta
  have hbase_pos : 0 < 1 + delta := by linarith
  have hlog_le_delta : Real.log (1 + delta) <= delta := by
    have h := Real.log_le_sub_one_of_pos hbase_pos
    linarith
  have hlog_mul_le : Real.log (1 + delta) * (T : ℝ) <= (T : ℝ) * delta := by
    calc
      Real.log (1 + delta) * (T : ℝ) <= delta * (T : ℝ) :=
        mul_le_mul_of_nonneg_right hlog_le_delta hT_nonneg
      _ = (T : ℝ) * delta := by ring
  have hpow_le_exp :
      (1 + delta) ^ T <= Real.exp ((T : ℝ) * delta) := by
    rw [← Real.rpow_natCast]
    rw [Real.rpow_def_of_pos hbase_pos]
    rw [Real.exp_le_exp]
    nlinarith
  have hexp_le :
      Real.exp ((T : ℝ) * delta) <= 1 + 2 * ((T : ℝ) * delta) :=
    Real.exp_le_one_add_two_mul_of_mem_Icc_zero_one
      (x := (T : ℝ) * delta) ⟨hx0, hbudget⟩
  calc
    (1 + delta) ^ T <= Real.exp ((T : ℝ) * delta) := hpow_le_exp
    _ <= 1 + 2 * ((T : ℝ) * delta) := hexp_le
    _ = 1 + 2 * (T : ℝ) * delta := by ring

-- Batch 5 promoted from Staging/inv_nat_pow_eq_rpow_neg_mul.lean
/-- The inverse of a nested natural power is the corresponding negative real
power with product exponent.

For a real base, `((base^T)^N)⁻¹` can be displayed as
`base^(-(T * N))` using real powers. This packages the standard bridge from
natural-power contraction factors to real-exponent rate notation.

Layer: Glue | Gap: Level 0 (natural-power contraction to negative real power)
Proof: collapse the nested natural powers with `pow_mul`, rewrite the natural
  power as `Real.rpow` at a natural exponent, cast the product exponent, and
  apply `Real.rpow_neg`.
Source: Mathlib real-power and natural-power APIs
Used in: variance-reduced accelerated finite-sum tail analysis converting
  epoch-count contractions into printed negative-real-exponent rates
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem inv_nat_pow_eq_rpow_neg_mul
    (base : Real) (T N : Nat) :
    ((base ^ T) ^ N)⁻¹ = Real.rpow base (-((T : Real) * (N : Real))) := by
  calc
    ((base ^ T) ^ N)⁻¹ = (base ^ (T * N))⁻¹ := by
      rw [pow_mul]
    _ = base ^ (-(T * N : ℤ)) := by
      rw [zpow_neg, ← Nat.cast_mul, zpow_natCast]
    _ = Real.rpow base (-((T * N : Nat) : Real)) := by
      exact (Real.rpow_neg_natCast base (T * N)).symm
    _ = Real.rpow base (-((T : Real) * (N : Real))) := by
      norm_num [Nat.cast_mul]


-- Batch 6 promoted from Staging/real_rpow_le_inv_of_log_div_log_selector.lean
-- Generalization plan (G0):
-- concept/name: logarithmic selector inversion for an increasing real-power base; orig was `real_rpow_log_selector_le_inv_ratio`
-- generality used: Glue-layer real scalar parameters only; no carrier type, measure, convexity, smoothness, oracle, filtration, or finite-dimensional assumptions
-- portable call pattern: restarted and accelerated tail analyses choose an epoch after a tail anchor from a logarithmic scale ratio; the base, target ratio, multiplier, and tail anchor vary while the `rpow <= inverse ratio` conclusion stays the same
-- counterargument checked: not paper-local traceability because the statement is a reusable scalar real-analysis step; not a pure wrapper because it composes selector algebra, monotonicity of `rpow` for bases above one, and log/exponential inversion
-- coverage search: searched project/catalog tokens `rpow`, `log_div_log`, `inv_ratio`, `selector`; SOptLib hits `pow_nat_le_inv_of_neg_log_div_log_le` and `natCeil_neg_log_div_log_mono_of_base_lt_one` cover natural powers or contraction bases below one, while Mathlib hits `Real.le_logb_iff_rpow_le`, `Real.rpow_le_rpow_left_iff`, and `Real.rpow_def_of_pos` provide primitives but not this selector theorem
-- minimal hypotheses: all already minimal; the proof uses `1 < base` for positive logarithm and monotone real powers, `0 < R` for `exp_log`, `0 < m` to normalize the selector inequality, and the pointwise selector lower bound

/-- A logarithmic selector for an increasing real-power base gives an inverse-ratio
tail bound.

If `base > 1`, `R > 0`, and the selected point `s` is at least
`tail + (2 / m) * (log R / log base)`, then the tail factor
`base ^ (-(m * (s - tail) / 2))` is at most `R⁻¹`.

Layer: Glue | Gap: Level 0 (logarithmic real-power selector inversion)
Proof: normalize the selector inequality to compare the exponent with
  `-log R / log base`, use monotonicity of `Real.rpow` for bases above one,
  and evaluate the boundary case with `Real.rpow_def_of_pos`.
Source: Mathlib real logarithm-base, real-power monotonicity, and exponential APIs
Used in: variance-reduced accelerated finite-sum tail analysis converting a
  logarithmic epoch choice into an inverse target-ratio contraction bound
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem real_rpow_le_inv_of_log_div_log_selector
    {base R m tail s : ℝ}
    (hbase_gt_one : 1 < base) (hR_pos : 0 < R) (hm_pos : 0 < m)
    (hselector :
      tail + (2 / m) * (Real.log R / Real.log base) ≤ s) :
    Real.rpow base (-(m * (s - tail) / 2)) ≤ R⁻¹ := by
  have hbase_pos : 0 < base := lt_trans zero_lt_one hbase_gt_one
  have hbase_ge_one : 1 ≤ base := le_of_lt hbase_gt_one
  have hlog_base_pos : 0 < Real.log base := Real.log_pos hbase_gt_one
  have hlog_base_ne : Real.log base ≠ 0 := ne_of_gt hlog_base_pos
  let K : ℝ := Real.log R / Real.log base
  have hinc_le : (2 / m) * K ≤ s - tail := by
    have hselector' : tail + (2 / m) * K ≤ s := by
      simpa [K] using hselector
    linarith
  have hK_le : K ≤ m * (s - tail) / 2 := by
    have hmul :=
      mul_le_mul_of_nonneg_left hinc_le (le_of_lt (half_pos hm_pos))
    have hleft : (m / 2) * ((2 / m) * K) = K := by
      field_simp [ne_of_gt hm_pos]
    have hright : (m / 2) * (s - tail) = m * (s - tail) / 2 := by
      ring
    simpa [hleft, hright] using hmul
  have hexp_order : -(m * (s - tail) / 2) ≤ -K := by
    linarith
  have hrpow_cmp :
      Real.rpow base (-(m * (s - tail) / 2)) ≤ Real.rpow base (-K) :=
    Real.rpow_le_rpow_of_exponent_le hbase_ge_one hexp_order
  have hrpow_log : Real.rpow base (-K) = R⁻¹ := by
    calc
      Real.rpow base (-K) = Real.exp (Real.log base * (-K)) := by
        simpa using Real.rpow_def_of_pos hbase_pos (-K)
      _ = Real.exp (-Real.log R) := by
        dsimp [K]
        field_simp [hlog_base_ne]
      _ = R⁻¹ := by
        rw [Real.exp_neg, Real.exp_log hR_pos]
  exact hrpow_cmp.trans_eq hrpow_log


-- Batch 6 promoted from Staging/isMinOn_subtype_univ_congr_iff.lean
-- Generalization plan (G0):
-- concept/name: objective congruence for `IsMinOn`; orig was `theorem59PrintedFeasibleProxUpdateRelOn_iff_canonical_of_core_centers`, and this supersedes the overly prox-specific generic wrapper `isProxPoint_iff_isPaperProxPoint`
-- generality used: arbitrary domain, arbitrary set, and arbitrary preorder-valued objectives; no measure, convexity, smoothness, oracle, topology, subtype, or inner-product assumptions are used
-- portable call pattern: future proximal, mirror-descent, and constrained stochastic-optimization proofs can transport an argmin certificate from one objective name to another once the objectives agree on the carrier and at the selected point
-- counterargument checked: not just paper-local traceability because the proof step is objective congruence for `IsMinOn`; Mathlib exposes `isMinOn_iff` and `isMinOn_univ_iff` but no named congruence theorem
-- coverage search: LeanSearch for "IsMinOn subtype univ congruent objective functions iff" returned `IsMinOn`, `isMinOn_iff`, and `isMinOn_univ_iff`; project search found `SOptLib.Model.Prox.isProxPoint_iff_isPaperProxPoint`, which covers a broader raw type but is named for prox/paper normalization rather than the order-theoretic concept
-- minimal hypotheses: all already minimal; equality is required only at the endpoint and pointwise on the set, and the codomain needs only `[Preorder β]` because `IsMinOn` only compares objective values

/-- Pointwise equal objectives on a set have equivalent `IsMinOn` predicates.

This is objective congruence for constrained minimizers: if two objective names
agree at the selected point and on the feasible carrier, then the selected point
minimizes one objective on that carrier exactly when it minimizes the other.

Layer: Glue | Gap: Level 0 (subtype global-minimum objective congruence)
Proof: expand minimization with Mathlib's `isMinOn_iff`, then rewrite the
  endpoint and comparison objective values using the supplied equalities.
Source: Mathlib order argmin predicates in `Mathlib.Order.Filter.Extr`
Used in: feasible-subtype prox-step normalization from a printed objective to a
  canonical ambient/core objective
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem isMinOn_congr_iff
    {α β : Type*} [Preorder β] {f g : α → β} {s : Set α} {a : α}
    (ha : f a = g a) (hs : ∀ x ∈ s, f x = g x) :
    IsMinOn f s a ↔ IsMinOn g s a := by
  rw [isMinOn_iff, isMinOn_iff]
  constructor
  · intro ha_min x hx
    simpa [ha, hs x hx] using ha_min x hx
  · intro ha_min x hx
    simpa [← ha, ← hs x hx] using ha_min x hx


-- Batch 6 promoted from Staging/rpow_tail_prefactor_le_of_ratio_le.lean
-- Generalization plan (G0):
-- concept/name: real-power tail prefactor suppression by a ratio bound; orig was
--   `theorem59_case4_tail_prefactor_le_epsilon`, renamed away from theorem
--   numbering and case labels.
-- generality used: Glue-layer real scalar parameters only; no carrier type,
--   measure, convexity, smoothness, oracle, filtration, or finite-dimensional
--   assumptions are used.
-- portable call pattern: restarted, accelerated, and variance-reduced tail-rate
--   proofs with a base at least one and a post-tail epoch discard a nonpositive
--   real-power contraction factor; the base, tail scale, epoch, budget, and
--   accuracy vary while the prefactor conclusion stays the same.
-- counterargument checked: not paper-local traceability because the theorem
--   packages a reusable scalar rate-finalization step; not a pure wrapper
--   because Mathlib supplies only the `rpow <= 1` primitive and not the
--   combined ratio-to-accuracy prefactor bound.
-- coverage search: searched project/catalog tokens `rpow_tail`, `tail_prefactor`,
--   `ratio_le`, `prefactor`, and `Real.rpow`; existing SOptLib/Staging hits
--   cover logarithmic selector inversion and unrelated rate denominators.
--   LeanSearch returned Mathlib `Real.rpow_le_one_of_one_le_of_nonpos` and
--   `Real.rpow_le_rpow_of_exponent_le`, which are primitives but not this
--   packaged prefactor theorem.
-- minimal hypotheses: weakened the source proof from `0 < m` and `tail < s`
--   to `0 <= m` and `tail <= s`, and from `0 < D` to `0 <= D`; all other
--   positivity hypotheses are used to clear divisions.

/-- A nonpositive real-power tail factor does not enlarge a ratio-bounded
prefactor.

If `base >= 1`, the epoch is at or after the tail anchor, and `D / epsilon <= A`,
then the tail contraction `base ^ (-(m * (s - tail) / 2))` can be discarded
from the prefactor `D / A`.

Layer: Glue | Gap: Level 0 (real-power tail prefactor suppression)
Proof: use `Real.rpow_le_one_of_one_le_of_nonpos` for the post-tail exponent,
  multiply by the nonnegative ratio `D / A`, and clear the denominator in the
  ratio hypothesis to obtain `D / A <= epsilon`.
Source: Mathlib real-power monotonicity and ordered-field division APIs
Used in: variance-reduced accelerated finite-sum tail analysis reducing a
  post-tail contraction prefactor to the target accuracy ratio
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem rpow_tail_prefactor_le_of_ratio_le
    {base m D A epsilon tail s : ℝ}
    (hbase_ge_one : 1 <= base) (hm_nonneg : 0 <= m) (hD_nonneg : 0 <= D)
    (hA_pos : 0 < A) (heps_pos : 0 < epsilon)
    (htail_le : tail <= s) (hratio_le : D / epsilon <= A) :
    Real.rpow base (-(m * (s - tail) / 2)) * (D / A) <= epsilon := by
  have hD_le_Aeps : D <= A * epsilon := (div_le_iff₀ heps_pos).1 hratio_le
  have hpref_le : D / A <= epsilon := by
    exact (div_le_iff₀ hA_pos).2 (by simpa [mul_comm] using hD_le_Aeps)
  have hexp_le_zero : -(m * (s - tail) / 2) <= 0 := by
    have hdiff_nonneg : 0 <= s - tail := by linarith
    nlinarith
  have hrpow_le_one :
      Real.rpow base (-(m * (s - tail) / 2)) <= 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hbase_ge_one hexp_le_zero
  have hpref_nonneg : 0 <= D / A :=
    div_nonneg hD_nonneg (le_of_lt hA_pos)
  calc
    Real.rpow base (-(m * (s - tail) / 2)) * (D / A) <=
        1 * (D / A) :=
      mul_le_mul_of_nonneg_right hrpow_le_one hpref_nonneg
    _ = D / A := by ring
    _ <= epsilon := hpref_le


-- Batch 6 promoted from Staging/exists_closedBall_forall_inner_le_of_dual_simplex.lean
open scoped BigOperators InnerProductSpace

-- Generalization plan (G0):
-- concept/name: finite halfspace feasibility over a closed ball from simplex-dual
--   support inequalities; orig was theorem59_finite_closedBall_halfspace_feasible_of_dual.
-- generality used: arbitrary real inner product normed additive group with compact
--   closed balls via [ProperSpace E]; finite index set; no measure,
--   convexity/smoothness, or oracle assumptions.
-- portable call pattern: finite-dimensional separation/KKT leaves in stochastic
--   proximal, mirror, or conditional-gradient proofs can instantiate `d`, `rhs`,
--   and `R` after deriving the same simplex-weighted support inequality.
-- counterargument checked: not paper-local traceability, because the statement is
--   a Farkas-style alternative for finitely many halfspaces intersected with a
--   compact ball; not a pure wrapper around a single Mathlib lemma.
-- coverage search: queries "closedBall halfspace dual simplex inner" and
--   "exist point closed ball satisfying finite halfspace inequalities from simplex
--   dual inequality Hilbert space"; Mathlib hits were Hahn-Banach separation and
--   stdSimplex support lemmas, SOptLib hits were unrelated norm/argmin APIs;
--   coverage is partial and this theorem composes those primitives.
-- minimal hypotheses: [ProperSpace E] replaces the original Euclidean finite
--   dimension exactly where compactness of closed balls is used; all dual and
--   halfspace assumptions are pointwise and already minimal.

/-- A finite family of halfspaces meets a closed ball when all simplex dual
support inequalities hold.

For vectors `d i`, right sides `rhs i`, and radius `R ≥ 0`, it suffices to
check every nonnegative weight vector of total mass one.  The dual condition is
the support-function inequality for the closed ball in the aggregate direction.

Layer: Glue | Gap: Level 2 (finite halfspace feasibility from simplex duality)
Proof: separate the compact image of the closed ball from the closed lower
  orthant of right-side bounds; normalize the separating functional into
  simplex weights and contradict the assumed dual support inequality.
Source: Mathlib Hahn-Banach separation, compact closed balls, and finite-sum
  inner-product APIs
Used in: stochastic accelerated proximal support-vector feasibility from finite
  comparison families
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem exists_closedBall_forall_inner_le_of_dual_simplex
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E] [ProperSpace E]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : Real) (hR : 0 <= R)
    (d : ι -> E) (rhs : ι -> Real)
    (hdual :
      ∀ w : ι -> Real,
        (∀ i : ι, 0 <= w i) ->
        Finset.univ.sum w = 1 ->
          -R * ‖Finset.univ.sum (fun i : ι => w i • d i)‖ <=
            Finset.univ.sum (fun i : ι => w i * rhs i)) :
    ∃ p : E, ‖p‖ <= R ∧ ∀ i : ι, ⟪p, d i⟫_Real <= rhs i := by
  classical
  let T : E →L[Real] (ι -> Real) :=
    ContinuousLinearMap.pi fun i => innerSL Real (d i)
  let C : Set (ι -> Real) := T '' Metric.closedBall (0 : E) R
  let D : Set (ι -> Real) := {r | ∀ i : ι, r i <= rhs i}
  by_contra hnot
  have hdisj : Disjoint C D := by
    rw [Set.disjoint_left]
    rintro r ⟨p, hpball, rfl⟩ hrD
    have hp_norm : ‖p‖ <= R := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hpball
    exact hnot ⟨p, hp_norm, fun i => by
      have hi := hrD i
      simpa [T, ContinuousLinearMap.pi_apply, real_inner_comm] using hi⟩
  have hC_convex : Convex Real C := by
    simpa [C] using
      (convex_closedBall (0 : E) R).linear_image T.toLinearMap
  have hC_compact : IsCompact C := by
    simpa [C] using
      (isCompact_closedBall (0 : E) R).image T.continuous
  have hD_convex : Convex Real D := by
    intro x hx y hy a b ha hb hab i
    have hxi := hx i
    have hyi := hy i
    calc
      (a • x + b • y) i = a * x i + b * y i := by simp
      _ <= a * rhs i + b * rhs i := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hxi ha)
          (mul_le_mul_of_nonneg_left hyi hb)
      _ = rhs i := by
        rw [← add_mul, hab, one_mul]
  have hD_closed : IsClosed D := by
    rw [show D =
        ⋂ i : ι, {r : ι -> Real | r i <= rhs i} by
      ext r
      simp [D]]
    exact isClosed_iInter fun i =>
      isClosed_le (by fun_prop) continuous_const
  obtain ⟨f, u, v, hfC, huv, hfD⟩ :=
    geometric_hahn_banach_compact_closed hC_convex hC_compact
      hD_convex hD_closed hdisj
  let coeff : ι -> Real := fun i => f ((Pi.single i (1 : Real) : ι -> Real))
  have hf_eq_sum : ∀ r : ι -> Real,
      f r = Finset.univ.sum (fun i : ι => r i * coeff i) := by
    intro r
    have hdecomp :
        (Finset.univ.sum fun i : ι =>
          r i • (Pi.single i (1 : Real) : ι -> Real)) = r := by
      ext j
      simp [Pi.single_apply]
    calc
      f r =
          f (Finset.univ.sum fun i : ι =>
            r i • (Pi.single i (1 : Real) : ι -> Real)) := by
            rw [hdecomp]
      _ = Finset.univ.sum
            (fun i : ι => f (r i • (Pi.single i (1 : Real) : ι -> Real))) := by
            simp
      _ = Finset.univ.sum (fun i : ι => r i * coeff i) := by
            apply Finset.sum_congr rfl
            intro i _hi
            simp [coeff]
  let bvec : ι -> Real := fun i => rhs i
  have hbvec_mem : bvec ∈ D := by
    intro i
    simp [bvec]
  have hbvec_sep : v < f bvec := hfD bvec hbvec_mem
  have hcoeff_nonpos : ∀ i : ι, coeff i <= 0 := by
    intro i
    by_contra hnot_nonpos
    have hpos : 0 < coeff i := lt_of_not_ge hnot_nonpos
    let M : Real := (f bvec - v + 1) / coeff i
    have hM_nonneg : 0 <= M := by
      have hnum_pos : 0 < f bvec - v + 1 := by linarith
      exact div_nonneg (le_of_lt hnum_pos) (le_of_lt hpos)
    let rM : ι -> Real := bvec - M • (Pi.single i (1 : Real) : ι -> Real)
    have hrM_mem : rM ∈ D := by
      intro j
      by_cases hji : j = i
      · subst j
        dsimp [rM, bvec, D]
        simp [Pi.single_eq_same, hM_nonneg]
      · dsimp [rM, bvec, D]
        simp [Pi.single_eq_of_ne hji]
    have hrM_sep : v < f rM := hfD rM hrM_mem
    have hf_rM : f rM = f bvec - M * coeff i := by
      dsimp [rM, coeff]
      simp
    have hM_mul : M * coeff i = f bvec - v + 1 := by
      dsimp [M]
      field_simp [ne_of_gt hpos]
    linarith
  let lam : ι -> Real := fun i => -coeff i
  have hlam_nonneg : ∀ i : ι, 0 <= lam i := by
    intro i
    dsimp [lam]
    linarith [hcoeff_nonpos i]
  let W : Real := Finset.univ.sum lam
  have hW_nonneg : 0 <= W := by
    dsimp [W]
    exact Finset.sum_nonneg fun i _hi => hlam_nonneg i
  have hW_pos : 0 < W := by
    by_contra hW_not_pos
    have hW_le : W <= 0 := le_of_not_gt hW_not_pos
    have hW_eq : W = 0 := le_antisymm hW_le hW_nonneg
    have hlam_zero : ∀ i : ι, lam i = 0 := by
      intro i
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _hj => hlam_nonneg j)).mp hW_eq i (Finset.mem_univ i)
    have hcoeff_zero : ∀ i : ι, coeff i = 0 := by
      intro i
      have hi := hlam_zero i
      dsimp [lam] at hi
      linarith
    have hf_zero : ∀ r : ι -> Real, f r = 0 := by
      intro r
      rw [hf_eq_sum r]
      simp [hcoeff_zero]
    have hC0 : T 0 ∈ C := by
      refine ⟨0, ?_, rfl⟩
      simpa [Metric.mem_closedBall, dist_eq_norm] using hR
    have h0u : 0 < u := by
      simpa [hf_zero] using hfC (T 0) hC0
    have hv0 : v < 0 := by
      simpa [hf_zero] using hfD bvec hbvec_mem
    linarith
  let Dsum : E := Finset.univ.sum (fun i : ι => lam i • d i)
  have hfT : ∀ p : E, f (T p) = -⟪Dsum, p⟫_Real := by
    intro p
    have hinner_sum :
        ⟪Dsum, p⟫_Real =
          Finset.univ.sum (fun i : ι => lam i * ⟪d i, p⟫_Real) := by
      dsimp [Dsum]
      rw [sum_inner]
      apply Finset.sum_congr rfl
      intro i _hi
      simp [inner_smul_left]
    calc
      f (T p) =
          Finset.univ.sum (fun i : ι => (T p) i * coeff i) := hf_eq_sum (T p)
      _ = Finset.univ.sum (fun i : ι => ⟪d i, p⟫_Real * coeff i) := by
            apply Finset.sum_congr rfl
            intro i _hi
            simp [T, ContinuousLinearMap.pi_apply]
      _ = -⟪Dsum, p⟫_Real := by
            rw [hinner_sum]
            simp [lam, mul_comm, Finset.sum_neg_distrib]
  have hRnormD_lt_u : R * ‖Dsum‖ < u := by
    by_cases hDzero : Dsum = 0
    · have hC0 : T 0 ∈ C := by
        refine ⟨0, ?_, rfl⟩
        simpa [Metric.mem_closedBall, dist_eq_norm] using hR
      have h0u : 0 < u := by
        simpa [hfT, hDzero] using hfC (T 0) hC0
      simpa [hDzero] using h0u
    · have hnorm_pos : 0 < ‖Dsum‖ := norm_pos_iff.mpr hDzero
      let pstar : E := -(R / ‖Dsum‖) • Dsum
      have hpstar_norm : ‖pstar‖ = R := by
        dsimp [pstar]
        have hscalar_nonneg : 0 <= R / ‖Dsum‖ :=
          div_nonneg hR (le_of_lt hnorm_pos)
        rw [norm_smul, norm_neg, Real.norm_eq_abs, abs_of_nonneg hscalar_nonneg]
        field_simp [ne_of_gt hnorm_pos]
      have hpstar_ball : pstar ∈ Metric.closedBall (0 : E) R := by
        simp [Metric.mem_closedBall, dist_eq_norm, hpstar_norm]
      have hCstar : T pstar ∈ C := ⟨pstar, hpstar_ball, rfl⟩
      have hsep_star := hfC (T pstar) hCstar
      have hfstar : f (T pstar) = R * ‖Dsum‖ := by
        have hinner :
            ⟪Dsum, pstar⟫_Real = -(R / ‖Dsum‖) * ‖Dsum‖ ^ 2 := by
          dsimp [pstar]
          rw [inner_smul_right, real_inner_self_eq_norm_sq]
        rw [hfT, hinner]
        field_simp [ne_of_gt hnorm_pos]
      simpa [hfstar] using hsep_star
  have hfbvec : f bvec = -Finset.univ.sum (fun i : ι => lam i * rhs i) := by
    rw [hf_eq_sum bvec]
    simp [bvec, lam, mul_comm, Finset.sum_neg_distrib]
  have hdual_contra :
      Finset.univ.sum (fun i : ι => lam i * rhs i) + R * ‖Dsum‖ < 0 := by
    rw [hfbvec] at hbvec_sep
    linarith
  let w : ι -> Real := fun i => lam i / W
  have hw_nonneg : ∀ i : ι, 0 <= w i := by
    intro i
    dsimp [w]
    exact div_nonneg (hlam_nonneg i) (le_of_lt hW_pos)
  have hw_sum : Finset.univ.sum w = 1 := by
    dsimp [w, W]
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt hW_pos)
  have hD_w :
      Finset.univ.sum (fun i : ι => w i • d i) = (1 / W) • Dsum := by
    dsimp [w, Dsum]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    simp [div_eq_inv_mul, smul_smul, mul_comm]
  have hnorm_w :
      ‖Finset.univ.sum (fun i : ι => w i • d i)‖ =
        (1 / W) * ‖Dsum‖ := by
    rw [hD_w, norm_smul]
    have hinv_nonneg : 0 <= (1 / W : Real) := by
      exact div_nonneg zero_le_one (le_of_lt hW_pos)
    rw [Real.norm_eq_abs, abs_of_nonneg hinv_nonneg]
  have hrhs_w :
      Finset.univ.sum (fun i : ι => w i * rhs i) =
        (1 / W) * Finset.univ.sum (fun i : ι => lam i * rhs i) := by
    calc
      Finset.univ.sum (fun i : ι => w i * rhs i) =
          Finset.univ.sum (fun i : ι => (1 / W) * (lam i * rhs i)) := by
            dsimp [w]
            apply Finset.sum_congr rfl
            intro i _hi
            field_simp [ne_of_gt hW_pos]
      _ = (1 / W) * Finset.univ.sum (fun i : ι => lam i * rhs i) := by
            rw [Finset.mul_sum]
  have hdual_w := hdual w hw_nonneg hw_sum
  have hdual_nonneg :
      0 <= Finset.univ.sum (fun i : ι => w i * rhs i) +
        R * ‖Finset.univ.sum (fun i : ι => w i • d i)‖ := by
    linarith
  have hdual_neg :
      Finset.univ.sum (fun i : ι => w i * rhs i) +
        R * ‖Finset.univ.sum (fun i : ι => w i • d i)‖ < 0 := by
    rw [hrhs_w, hnorm_w]
    have hinv_pos : 0 < (1 / W : Real) := one_div_pos.mpr hW_pos
    have hscaled :
        (1 / W) *
          (Finset.univ.sum (fun i : ι => lam i * rhs i) + R * ‖Dsum‖) < 0 :=
      mul_neg_of_pos_of_neg hinv_pos hdual_contra
    nlinarith
  linarith


-- Batch 6 promoted from Staging/max_one_ceil_log_div_log_le_floor_log_add_one_of_le.lean
-- Generalization plan (G0):
-- concept/name: logarithmic ceiling selector bounded by a floor-log cutoff; orig was `theorem59_first_log_selector_le_cutoff`
-- generality used: Glue-layer real scalar parameters only; no carrier type, measure, convexity, smoothness, oracle, or filtration assumptions
-- portable call pattern: finite-sum and epoch-doubling complexity proofs choose a logarithmic epoch before a cutoff scale; the positive selector argument, cutoff cap, and logarithm base change while the conclusion shape stays fixed
-- counterargument checked: not paper-local traceability because the same scalar rounding bridge applies to any base-greater-than-one logarithmic epoch selector; not a pure wrapper because it composes log monotonicity, division by a positive log, natural ceiling monotonicity, `max 1`, and floor/ceiling rounding
-- coverage search: searched project/catalog tokens `ceil log floor selector`, `max_one_ceil_log`, `Nat.ceil_le_floor_add_one`, and LeanSearch query for ceiling logarithm bounded by floor logarithm; Mathlib provides `Nat.ceil_le_floor_add_one` and natural-log analogues, while staged `max_one_ceil_log_div_le_floor_log_of_div_le` is the base-two ratio-specialized corollary, so this statement strengthens it
-- minimal hypotheses: positivity of `x`, a base strictly greater than one, and the pointwise cap `x ≤ M` are exactly what the proof uses

/-- A logarithmic ceiling selector is bounded by the matching floor-log cutoff
whenever its positive argument is bounded by the cutoff scale.

For any real base greater than one, this packages the common complexity step
that turns `x ≤ M` into a natural-number selector bound after applying
`log x / log base`, natural ceiling, and the positive `max 1` totalization.

Layer: Glue | Gap: Level 0 (logarithmic selector cutoff rounding)
Proof: use monotonicity of `Real.log`, divide by the positive `log base`, apply
  `Nat.ceil_mono`, and finish with `Nat.ceil_le_floor_add_one`.
Source: Mathlib real logarithm monotonicity and natural ceiling/floor APIs
Used in: variance-reduced accelerated finite-sum complexity proof selecting a
  pre-cutoff logarithmic epoch from an accuracy-to-component ratio
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem max_one_ceil_log_div_log_le_floor_log_add_one_of_le
    {x M base : ℝ} (hx : 0 < x) (hbase : 1 < base) (hx_le_M : x ≤ M) :
    max 1 (Nat.ceil (Real.log x / Real.log base)) ≤
      Nat.floor (Real.log M / Real.log base) + 1 := by
  have hlog_arg_le :
      Real.log x / Real.log base ≤ Real.log M / Real.log base := by
    have hlog_le : Real.log x ≤ Real.log M :=
      Real.log_le_log hx hx_le_M
    exact div_le_div_of_nonneg_right hlog_le
      (le_of_lt (Real.log_pos hbase))
  have hceil_le :
      Nat.ceil (Real.log x / Real.log base) ≤
        Nat.floor (Real.log M / Real.log base) + 1 :=
    (Nat.ceil_mono hlog_arg_le).trans
      (Nat.ceil_le_floor_add_one (Real.log M / Real.log base))
  exact max_le (Nat.succ_le_succ (Nat.zero_le _)) hceil_le


-- Batch 6 promoted from Staging/log_contraction_selector_overshoot_le_const_mul_log.lean
-- Generalization plan (G0):
-- concept/name: contraction-base logarithmic selector overshoot absorption; orig was `theorem59_large_m_log45_selector_absorption`
-- generality used: Glue-layer real scalar parameters only; no carrier type, measure, convexity, smoothness, oracle, filtration, or finite-dimensional assumptions
-- portable call pattern: finite-sum and restarted methods choose a logarithmic epoch from a contraction base below one; the base, ratio lower bound, and final constant vary while the additive selector overshoot is absorbed into `m * log ratio`
-- counterargument checked: not paper-local traceability because the statement removes the `4/5` base and theorem-numbered constant, and captures a reusable scalar complexity step; not a pure wrapper because it combines contraction-base log normalization, threshold monotonicity, and constant absorption
-- coverage search: searched project/catalog tokens `log_contraction`, `selector`, `overshoot`, `Real.log`, `large_m_log45`, and LeanSearch query for contraction-base logarithmic selector overshoot; SOptLib `pow_nat_le_inv_of_neg_log_div_log_le` covers natural contraction powers, and staged `real_rpow_le_inv_of_log_div_log_selector` covers increasing-base tail inversion, but neither states this real scalar additive-overshoot absorption bound
-- minimal hypotheses: all already minimal except the paper-specific `2 < D0 / epsilon` is generalized to `alpha⁻¹ ≤ ratio`, which is exactly what proves `1 ≤ log ratio / (-log alpha)`

/-- A contraction-base logarithmic selector with additive overshoot is absorbed
by a constant multiple of `m * log ratio`.

If `0 < alpha < 1`, `ratio` dominates `alpha⁻¹`, and the final constant
dominates `6 / (-log alpha)`, then the common selector estimate
`2 * m * (-log ratio / log alpha + 2)` is bounded by `C * (m * log ratio)`.

Layer: Glue | Gap: Level 0 (contraction logarithmic selector overshoot absorption)
Proof: normalize the logarithmic selector by `den = -log alpha`; the lower
  bound `alpha⁻¹ ≤ ratio` gives `1 ≤ log ratio / den`, so the additive
  overshoot satisfies `y + 2 ≤ 3y`, and the remaining step is constant
  monotonicity.
Source: Mathlib real logarithm monotonicity and ordered-field arithmetic APIs
Used in: variance-reduced accelerated finite-sum complexity proof absorbing a
  logarithmic epoch-selector overshoot into a first-branch call-rate constant
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem log_contraction_selector_overshoot_le_const_mul_log
    {alpha ratio m C : ℝ}
    (hm_nonneg : 0 ≤ m)
    (halpha_pos : 0 < alpha) (halpha_lt_one : alpha < 1)
    (hinv_alpha_le_ratio : alpha⁻¹ ≤ ratio)
    (hC_ge : 6 / (-Real.log alpha) ≤ C) :
    2 * m * (-Real.log ratio / Real.log alpha + 2) ≤
      C * (m * Real.log ratio) := by
  let den : ℝ := -Real.log alpha
  let y : ℝ := Real.log ratio / den
  have hlog_alpha_neg : Real.log alpha < 0 := Real.log_neg halpha_pos halpha_lt_one
  have hden_pos : 0 < den := by
    dsimp [den]
    linarith only [hlog_alpha_neg]
  have hinv_alpha_pos : 0 < alpha⁻¹ := inv_pos.mpr halpha_pos
  have hone_lt_inv_alpha : 1 < alpha⁻¹ := (one_lt_inv₀ halpha_pos).2 halpha_lt_one
  have hone_lt_ratio : 1 < ratio := hone_lt_inv_alpha.trans_le hinv_alpha_le_ratio
  have hy_expr : -Real.log ratio / Real.log alpha = y := by
    dsimp [y, den]
    field_simp [ne_of_lt hlog_alpha_neg]
  have hden_le_log_ratio : den ≤ Real.log ratio := by
    have hlog_inv_le : Real.log alpha⁻¹ ≤ Real.log ratio := by
      exact Real.log_le_log hinv_alpha_pos hinv_alpha_le_ratio
    have hlog_inv_eq : Real.log alpha⁻¹ = -Real.log alpha := by
      rw [Real.log_inv]
    dsimp [den]
    simpa [hlog_inv_eq] using hlog_inv_le
  have hy_one : 1 ≤ y := by
    dsimp [y]
    rw [le_div_iff₀ hden_pos]
    simpa [den] using hden_le_log_ratio
  have hy_add_le : y + 2 ≤ 3 * y := by
    linarith only [hy_one]
  have htwo_m_nonneg : 0 ≤ 2 * m := by nlinarith only [hm_nonneg]
  have hleft_le :
      2 * m * (-Real.log ratio / Real.log alpha + 2) ≤
        2 * m * (3 * y) := by
    rw [hy_expr]
    exact mul_le_mul_of_nonneg_left hy_add_le htwo_m_nonneg
  have hrewrite :
      2 * m * (3 * y) =
        (6 / den) * (m * Real.log ratio) := by
    dsimp [y]
    field_simp [ne_of_gt hden_pos]
    ring
  have hleft_le_rate :
      2 * m * (-Real.log ratio / Real.log alpha + 2) ≤
        (6 / den) * (m * Real.log ratio) :=
    hleft_le.trans_eq hrewrite
  have hlog_ratio_pos : 0 < Real.log ratio := Real.log_pos hone_lt_ratio
  have hrate_nonneg : 0 ≤ m * Real.log ratio :=
    mul_nonneg hm_nonneg (le_of_lt hlog_ratio_pos)
  exact hleft_le_rate.trans
    (mul_le_mul_of_nonneg_right (by simpa [den] using hC_ge) hrate_nonneg)

namespace SOptLib

/-- A dependent Pi of subtype-valued coordinates is measurable when every
ambient coordinate value is measurable.

This packages the common reconstruction step from coordinate-value
measurability to measurability of a support-valued finite or infinite product.

Layer: Glue | Gap: Level 1 (dependent product subtype measurability reconstruction)
Proof: use `measurable_pi_lambda` to reduce to coordinates, then rebuild each
  subtype-valued coordinate with `Measurable.subtype_mk` from the measurable
  ambient value.
Source: Mathlib measurable-space APIs for dependent products and subtypes
Used in: nonconvex variance-reduced mirror descent strict-past mini-batch
  measurability from erased sample-coordinate histories
Book citation: book/FOML/NonconvexVarianceReducedMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex variance-reduced mirror descent -/
theorem measurable_pi_subtype_mk_of_val_measurable
    {Ω κ : Type*} [MeasurableSpace Ω]
    {α : κ → Type*} [(r : κ) → MeasurableSpace (α r)]
    {p : (r : κ) → α r → Prop}
    (sample : Ω → (r : κ) → {a : α r // p r a})
    (hcoord : ∀ r : κ, Measurable fun ω : Ω => (sample ω r : α r)) :
    Measurable sample := by
  refine measurable_pi_lambda sample ?_
  intro r
  exact Measurable.subtype_mk (hcoord r)

end SOptLib


-- Promoted from Staging/sum_convexOn_weighted_average_le_weighted_sum.lean
open scoped BigOperators

-- Generalization plan (G0):
-- concept/name: finite coordinate-family weighted Jensen aggregation; orig was
--   theorem51_weighted_dual_conjugate_sum_le.
-- generality used: finite coordinate type, arbitrary finite time window,
--   real nonnegative weights with positive normalizer, coordinate carriers,
--   coordinatewise Mathlib `ConvexOn`, and a real module; no measure,
--   smoothness, oracle, filtration, topology, norm, completeness, or
--   finite-dimensional assumptions are used.
-- portable call pattern: weighted-output proofs for randomized primal-dual,
--   stochastic mirror descent, block-coordinate mirror descent, and
--   variance-reduced finite-sum methods call this after identifying each
--   coordinate of an output as the same normalized weighted average; the time
--   window, weights, coordinate carriers, convex functions, and iterates vary
--   while the summed Jensen conclusion has the same shape.
-- counterargument checked: not paper-local traceability and not a pure wrapper;
--   Mathlib `ConvexOn.map_sum_le` and SOptLib
--   `convexOn_weighted_average_le_weighted_sum` cover one function, but this
--   theorem packages the recurring coordinate-family aggregation and the
--   finite-sum interchange needed by product-coordinate proofs.
-- coverage search: searched CATALOG.md/SOptLib for convexOn weighted average,
--   coordinate weighted average, finite Jensen, and sum convex; read
--   `SOptLib.Layer1.Telescope.convexOn_weighted_average_le_weighted_sum` as a
--   partial single-function hit. LeanSearch for "finite sum Jensen convex
--   functions weighted average" returned Mathlib `ConvexOn.map_sum_le` and
--   `ConvexOn.map_centerMass_le` as partial Jensen APIs, not this summed
--   coordinate-family statement.
-- minimal hypotheses: all already minimal for this shape; `NormedAddCommGroup`,
--   `InnerProductSpace`, completeness, finite dimensionality, measure,
--   filtration, and algorithm setup assumptions from the source proof are
--   dropped.

/-- A finite sum of coordinatewise convex functions at common weighted averages
is bounded by the normalized weighted sum of coordinatewise values.

Each coordinate has its own carrier and convex function, but all coordinates
share the same finite time window, weights, and normalizer. This combines
coordinatewise finite Jensen inequalities with finite-sum commutation.

Layer: Glue | Gap: Level 1 (finite coordinate-family weighted Jensen aggregation)
Proof: normalize the weights by `W`, apply `ConvexOn.map_sum_le` in each
  coordinate, sum the resulting inequalities over coordinates, commute the two
  finite sums, and factor out the common scalar `W⁻¹`.
Source: Mathlib finite Jensen inequality `ConvexOn.map_sum_le` and finite-sum
  algebra over real modules
Used in: randomized primal-dual gradient weighted dual-output Jensen bound,
  and future block-coordinate weighted-output convexity estimates
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec/steps/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized primal-dual gradient -/
theorem sum_convexOn_weighted_average_le_weighted_sum
    {I T E : Type*} [Fintype I] [AddCommGroup E] [Module ℝ E]
    (s : Finset T) (γ : T → ℝ) (X : I → Set E) (f : I → E → ℝ)
    (p : T → I → E) (xbar : I → E) (W : ℝ)
    (hf : ∀ i, ConvexOn ℝ (X i) (f i))
    (hγ_nonneg : ∀ t ∈ s, 0 ≤ γ t)
    (hp_mem : ∀ t ∈ s, ∀ i, p t i ∈ X i)
    (hW_pos : 0 < W)
    (hW_eq : W = ∑ t ∈ s, γ t)
    (hxbar : ∀ i, xbar i = W⁻¹ • ∑ t ∈ s, γ t • p t i) :
    (∑ i : I, f i (xbar i)) ≤
      W⁻¹ * ∑ t ∈ s, γ t * (∑ i : I, f i (p t i)) := by
  classical
  let q : T → ℝ := fun t => W⁻¹ * γ t
  have hW_ne : W ≠ 0 := ne_of_gt hW_pos
  have hqsum : ∑ t ∈ s, q t = 1 := by
    calc
      ∑ t ∈ s, q t = W⁻¹ * ∑ t ∈ s, γ t := by
        simp [q, Finset.mul_sum]
      _ = W⁻¹ * W := by
        rw [← hW_eq]
      _ = 1 := inv_mul_cancel₀ hW_ne
  have hq_nonneg : ∀ t ∈ s, 0 ≤ q t := by
    intro t ht
    exact mul_nonneg (inv_nonneg.mpr hW_pos.le) (hγ_nonneg t ht)
  have hcoord : ∀ i : I,
      f i (xbar i) ≤ W⁻¹ * ∑ t ∈ s, γ t * f i (p t i) := by
    intro i
    have haverage :
        xbar i = ∑ t ∈ s, q t • p t i := by
      calc
        xbar i = W⁻¹ • ∑ t ∈ s, γ t • p t i := hxbar i
        _ = ∑ t ∈ s, W⁻¹ • (γ t • p t i) := by
          rw [Finset.smul_sum]
        _ = ∑ t ∈ s, q t • p t i := by
          refine Finset.sum_congr rfl ?_
          intro t _ht
          simp [q, smul_smul]
    have hJ :=
      (hf i).map_sum_le
        (t := s) (w := q) (p := fun t => p t i)
        hq_nonneg hqsum (fun t ht => hp_mem t ht i)
    rw [← haverage] at hJ
    have hright :
        (∑ t ∈ s, q t • f i (p t i)) =
          W⁻¹ * ∑ t ∈ s, γ t * f i (p t i) := by
      calc
        (∑ t ∈ s, q t • f i (p t i)) =
            ∑ t ∈ s, W⁻¹ * (γ t * f i (p t i)) := by
          refine Finset.sum_congr rfl ?_
          intro t _ht
          simp [q, smul_eq_mul, mul_assoc]
        _ = W⁻¹ * ∑ t ∈ s, γ t * f i (p t i) := by
          rw [Finset.mul_sum]
    rw [hright] at hJ
    exact hJ
  calc
    (∑ i : I, f i (xbar i))
        ≤ ∑ i : I, W⁻¹ * ∑ t ∈ s, γ t * f i (p t i) := by
          exact Finset.sum_le_sum fun i _hi => hcoord i
    _ = W⁻¹ * ∑ t ∈ s, γ t * (∑ i : I, f i (p t i)) := by
      calc
        ∑ i : I, W⁻¹ * ∑ t ∈ s, γ t * f i (p t i) =
            W⁻¹ * ∑ i : I, ∑ t ∈ s, γ t * f i (p t i) := by
          rw [Finset.mul_sum]
        _ = W⁻¹ * ∑ t ∈ s, ∑ i : I, γ t * f i (p t i) := by
          rw [Finset.sum_comm]
        _ = W⁻¹ * ∑ t ∈ s, γ t * (∑ i : I, f i (p t i)) := by
          refine congrArg (fun r => W⁻¹ * r) ?_
          refine Finset.sum_congr rfl ?_
          intro t _ht
          rw [Finset.mul_sum]


-- Merged from Staging/ConvexOn_of_firstOrder_lowerSupport.lean
/-!
-- Generalization plan (G0):
-- concept/name: `ConvexOn.of_first_order_lower_support` exposes the standard
--   convex-analysis principle that global first-order affine lower supports
--   imply convexity; orig was `nu_convexOn_from_strong`, renamed away from the
--   RGEM distance-generating function and setup field names.
-- generality used: real module decision space with `[AddCommGroup E]` and
--   `[Module ℝ E]`; a carrier `X : Set E`, scalar potential `phi : E → ℝ`,
--   and pointwise linear support functionals `support : E → E →ₗ[ℝ] ℝ`. No
--   norm, inner product, measure, filtration, smoothness, oracle, compactness,
--   completeness, or finite-dimensional assumption is used.
-- portable call pattern: stochastic mirror descent, proximal-gradient,
--   accelerated, and variance-reduced proofs that store a differentiable
--   strong-convexity or subgradient lower-model inequality can derive
--   `ConvexOn` for Jensen and convex-combination steps while changing `X`,
--   `phi`, `support`, and the caller-side proof of the lower-support
--   hypothesis.
-- counterargument checked: not paper-local traceability because the theorem is
--   a paper-free converse direction to first-order convex support; not a pure
--   wrapper because Mathlib and SOptLib expose `ConvexOn` consequences that
--   produce support inequalities, while this packages the reverse derivation
--   from stored pointwise support data.
-- coverage search: searched `CATALOG.md`, `SOptLib`, `Staging`, and the
--   algorithm file for `firstOrder`, `lowerSupport`, `ConvexOn`, and
--   `strongConvex`; relevant SOptLib hits were
--   `ConvexOn.firstOrderLinearModel_le_of_hasGradientWithinAt`, Bregman lower
--   bounds from `StrongConvexOn`, and finite Jensen APIs, none of which derive
--   `ConvexOn` from lower support. LeanSearch for "first order lower support
--   inequality implies convex on set" returned Mathlib `ConvexOn` definitions,
--   `convexOn_iff_forall_pos`, and `UniformConvexOn.convexOn`, but no matching
--   first-order-support-to-ConvexOn theorem.
-- minimal hypotheses: the paper's strong-convexity residual is reduced at the
--   call site to the exact pointwise lower-support inequality consumed here;
--   all remaining hypotheses are used directly in the Jensen proof.
-/

/-- Pointwise first-order lower supports imply convexity on a carrier.

If every feasible base point `z` supplies an affine lower model
`phi z + support z (x - z)` for all feasible `x`, then `phi` is convex on the
carrier.

Layer: Glue | Gap: Level 1 (first-order lower support implies convexity)
Proof: evaluate the lower supports at the convex-combination point, multiply
  by nonnegative weights, and use linearity of the support functional to cancel
  the weighted displacement from the base point.
Source: convex analysis supporting-hyperplane criterion and Mathlib `ConvexOn`
  / `LinearMap` APIs
Used in: random gradient extrapolation Jensen step for the regularized gap
  after converting strong convexity of the distance-generating function into
  affine lower supports
Book citation: book/FOML/RandomGradientExtrapolation.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random gradient extrapolation -/
theorem ConvexOn.of_first_order_lower_support
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {X : Set E} {phi : E → ℝ} {support : E → E →ₗ[ℝ] ℝ}
    (hX : Convex ℝ X)
    (hsupport : ∀ x z, x ∈ X → z ∈ X → phi z + support z (x - z) ≤ phi x) :
    ConvexOn ℝ X phi := by
  classical
  refine ⟨hX, ?_⟩
  intro x hx y hy a b ha hb hab
  let z : E := a • x + b • y
  have hz : z ∈ X := hX hx hy ha hb hab
  have hxlin : phi z + support z (x - z) ≤ phi x :=
    hsupport x z hx hz
  have hylin : phi z + support z (y - z) ≤ phi y :=
    hsupport y z hy hz
  have hxscaled :
      a * (phi z + support z (x - z)) ≤ a * phi x :=
    mul_le_mul_of_nonneg_left hxlin ha
  have hyscaled :
      b * (phi z + support z (y - z)) ≤ b * phi y :=
    mul_le_mul_of_nonneg_left hylin hb
  have hvec : a • (x - z) + b • (y - z) = 0 := by
    have hb_eq : b = 1 - a := by linarith
    subst b
    subst z
    module
  have hsupport_zero :
      a * support z (x - z) + b * support z (y - z) = 0 := by
    calc
      a * support z (x - z) + b * support z (y - z)
          = support z (a • (x - z)) + support z (b • (y - z)) := by simp
      _ = support z (a • (x - z) + b • (y - z)) := by
        rw [map_add]
      _ = support z 0 := by
        rw [hvec]
      _ = 0 := by simp
  have hlower :
      phi z ≤
        a * (phi z + support z (x - z)) +
          b * (phi z + support z (y - z)) := by
    have hsum :
        a * (phi z + support z (x - z)) +
            b * (phi z + support z (y - z)) =
          phi z := by
      calc
        a * (phi z + support z (x - z)) +
            b * (phi z + support z (y - z))
            = (a + b) * phi z +
                (a * support z (x - z) +
                  b * support z (y - z)) := by ring
        _ = phi z := by rw [hab, hsupport_zero]; ring
    exact le_of_eq hsum.symm
  have hupper :
      a * (phi z + support z (x - z)) +
          b * (phi z + support z (y - z)) ≤
        a * phi x + b * phi y := by
    nlinarith [hxscaled, hyscaled]
  calc
    phi z ≤
        a * (phi z + support z (x - z)) +
          b * (phi z + support z (y - z)) := hlower
    _ ≤ a * phi x + b * phi y := hupper


-- Merged from Staging/ConvexOn_expectation_inner_sub_le_expectation_sub_of_hasGradientWithinAt.lean
open MeasureTheory
open scoped InnerProductSpace

-- Generalization plan (G0):
-- concept/name: expectation lift of the convex first-order support inequality;
--   orig was `terminal_component_inner_expectation_le_value_gap`, renamed away
--   from terminal/component algorithm vocabulary.
-- generality used: arbitrary measurable source, probability measure, complete
--   real Hilbert decision space, convex carrier, convex real objective, fixed
--   feasible support point, random a.e. feasible endpoint, and pointwise
--   `HasGradientWithinAt` at the support point; no filtration, independence,
--   finite-dimensional, smoothness, oracle, update, or block-index assumptions
--   are used.
-- portable call pattern: stochastic gradient, mirror-descent, conditional
--   gradient, and variance-reduced proofs replace an expected linearized
--   endpoint term by an expected objective value gap; the measure, carrier,
--   objective, support point, endpoint random variable, and integrability
--   witnesses change while the conclusion keeps the same shape.
-- counterargument checked: not paper-local traceability because the statement
--   is paper-free convex analysis plus probability; not a pure wrapper because
--   Mathlib/SOptLib expose the pointwise support inequality and integral
--   monotonicity separately, but no theorem packages the expected linear-model
--   gap for random feasible endpoints.
-- coverage search: searched project/catalog for `expectation inner`,
--   `inner_sub`, `HasGradientWithinAt`, `ConvexOn expectation`, and
--   `value_gap`; closest SOptLib hit was
--   `ConvexOn.firstOrderLinearModel_le_of_hasGradientWithinAt`, which is only
--   pointwise. LeanSearch for convex differentiable first-order expectation
--   integral inner-product bounds returned `HasGradientWithinAt`,
--   `ConvexOn.slope_le_derivWithin`, and mean-value inequalities, none covering
--   the expectation lift.
-- minimal hypotheses: weakened the local proof's pointwise endpoint membership
--   to a.e. membership and kept only the two scalar integrability hypotheses
--   required for the Bochner integral comparison.

/-- A random feasible endpoint satisfies the expected convex first-order value gap.

If `f` is convex on `C`, has within-gradient `grad` at a feasible support point
`x`, and `Y` lands in `C` almost surely, then the expected linearized endpoint
term `⟪Y - x, grad⟫` is bounded by the expected objective gap.

Layer: Glue | Gap: Level 1 (expected convex first-order support inequality)
Proof: apply the pointwise convex first-order support theorem a.e., commute the
  real inner product, and lift the resulting scalar inequality with Bochner
  integral monotonicity and probability normalization of constant integrals.
Source: Mathlib convex first-order support, within-gradient calculus, and
  Bochner integral monotonicity APIs
Used in: random gradient extrapolation terminal component value-gap replacement
Book citation: book/FOML/RandomGradientExtrapolation.json#/algorithm_spec/steps/6
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random gradient extrapolation method -/
theorem ConvexOn.expectation_inner_sub_le_expectation_sub_of_hasGradientWithinAt
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {C : Set E} {f : E → ℝ} {grad x : E} {Y : Ω → E}
    (hf : ConvexOn ℝ C f) (hx : x ∈ C) (hY : ∀ᵐ ω ∂μ, Y ω ∈ C)
    (hgrad : HasGradientWithinAt f grad C x)
    (hinner_int : Integrable (fun ω => ⟪Y ω - x, grad⟫_ℝ) μ)
    (hfY_int : Integrable (fun ω => f (Y ω)) μ) :
    (∫ ω, ⟪Y ω - x, grad⟫_ℝ ∂μ) ≤
      (∫ ω, f (Y ω) ∂μ) - f x := by
  have hpoint :
      ∀ᵐ ω ∂μ, ⟪Y ω - x, grad⟫_ℝ ≤ f (Y ω) - f x := by
    filter_upwards [hY] with ω hYω
    have hsupport :
        f x + ⟪grad, Y ω - x⟫_ℝ ≤ f (Y ω) :=
      ConvexOn.first_order_linear_model_le_of_hasGradientWithinAt
        hf hx hYω hgrad
    have hsupport' :
        ⟪grad, Y ω - x⟫_ℝ ≤ f (Y ω) - f x := by
      linarith
    simpa [real_inner_comm] using hsupport'
  have hmono :
      (∫ ω, ⟪Y ω - x, grad⟫_ℝ ∂μ) ≤
        ∫ ω, (f (Y ω) - f x) ∂μ := by
    exact integral_mono_ae hinner_int
      (hfY_int.sub (integrable_const (f x))) hpoint
  have hsub :
      (∫ ω, (f (Y ω) - f x) ∂μ) =
        (∫ ω, f (Y ω) ∂μ) - f x := by
    rw [integral_sub]
    · simp [integral_const, probReal_univ]
    · exact hfY_int
    · exact integrable_const (f x)
  exact hmono.trans_eq hsub

/-- A nonnegative increment divided by its updated positive base is at most
the corresponding increment of the natural logarithm.

Layer: Glue | Gap: Level 0 (normalized-increment logarithmic lower bound)
Proof: apply `Real.log_le_sub_one_of_pos` to the ratio of the old and updated bases, rewrite the logarithm of the quotient, and normalize the resulting ordered-field inequality.
Source: Mathlib real logarithm upper bounds and ordered-field quotient algebra
Used in: adaptive-gradient and self-normalized potential proofs that telescope one-step cumulative-denominator increments into a logarithmic bound
Book citation: book/STORM/StochasticRecursiveMomentum.json#/key_lemmas/2
Origin algorithm: Cutkosky and Orabona, Momentum-Based Variance Reduction in Non-Convex SGD, STOchastic Recursive Momentum -/
theorem div_add_le_log_add_sub_log_of_pos_of_nonneg
    {p q : ℝ} (hp : 0 < p) (hq : 0 ≤ q) :
    q / (p + q) ≤ Real.log (p + q) - Real.log p := by
  have hpq : 0 < p + q := by linarith
  have hratio_pos : 0 < p / (p + q) := div_pos hp hpq
  have hlog := Real.log_le_sub_one_of_pos hratio_pos
  have hlog' : Real.log p - Real.log (p + q) ≤ -q / (p + q) := by
    rw [Real.log_div hp.ne' hpq.ne'] at hlog
    convert hlog using 1
    field_simp [hpq.ne']
    ring
  have hstep := neg_le_neg hlog'
  rw [neg_div, neg_neg, neg_sub] at hstep
  exact hstep

/-- The sum of nonnegative increments divided by a positive offset plus their
prefix sums is at most the logarithm of one plus the total-to-offset ratio.

Layer: Glue | Gap: Level 1 (cumulative-denominator logarithmic sum bound)
Proof: bound each normalized increment by the corresponding logarithmic increment using `Real.log_le_sub_one_of_pos`, then induct over the one-based horizon so those logarithmic increments telescope.
Source: Mathlib real logarithm inequalities and finite sums over natural closed intervals
Used in: adaptive-gradient, online-learning, and self-normalized convergence estimates that replace a cumulative squared-gradient denominator sum by a logarithmic factor
Book citation: book/STORM/StochasticRecursiveMomentum.json#/key_lemmas/2
Origin algorithm: Cutkosky and Orabona, Momentum-Based Variance Reduction in Non-Convex SGD, STOchastic Recursive Momentum -/
theorem sum_div_add_prefix_sum_le_log_one_add_sum_div_of_pos_of_nonneg
    (a₀ : ℝ) (a : ℕ → ℝ) (T : ℕ)
    (ha₀ : 0 < a₀) (ha_nonneg : ∀ t, t ∈ Finset.Icc 1 T → 0 ≤ a t) :
    (Finset.sum (Finset.Icc 1 T)
      (fun t => a t / (a₀ + Finset.sum (Finset.Icc 1 t) a))) ≤
        Real.log (1 + Finset.sum (Finset.Icc 1 T) a / a₀) := by
  have log_increment_ratio_bound :
      ∀ {p q : ℝ}, 0 < p → 0 ≤ q →
        q / (p + q) ≤ Real.log (p + q) - Real.log p := by
    intro p q hp hq
    exact div_add_le_log_add_sub_log_of_pos_of_nonneg hp hq
  have prefix_sum_nonneg :
      ∀ {U t : ℕ}, t ≤ U →
        (∀ i, i ∈ Finset.Icc 1 U → 0 ≤ a i) →
          0 ≤ (Finset.Icc 1 t).sum a := by
    intro U t ht hnonneg
    refine Finset.sum_nonneg ?_
    intro i hi
    exact hnonneg i (by
      rw [Finset.mem_Icc] at hi ⊢
      exact ⟨hi.1, le_trans hi.2 ht⟩)
  have log_one_add_div_eq_log_sub_log :
      ∀ {s : ℝ}, 0 ≤ s →
        Real.log (1 + s / a₀) = Real.log (a₀ + s) - Real.log a₀ := by
    intro s hs
    have hnum : a₀ + s ≠ 0 := by positivity
    have hratio : 1 + s / a₀ = (a₀ + s) / a₀ := by
      field_simp [ha₀.ne']
    rw [hratio, Real.log_div hnum ha₀.ne']
  revert ha_nonneg
  induction T with
  | zero =>
      intro ha_nonneg
      simp
  | succ T ih =>
      intro ha_nonneg
      have ha_nonneg_T : ∀ t, t ∈ Finset.Icc 1 T → 0 ≤ a t := by
        intro t ht
        exact ha_nonneg t (by
          rw [Finset.mem_Icc] at ht ⊢
          exact ⟨ht.1, Nat.le_succ_of_le ht.2⟩)
      have hlast_nonneg : 0 ≤ a (T + 1) := by
        exact ha_nonneg (T + 1) (by
          rw [Finset.mem_Icc]
          exact ⟨by omega, le_rfl⟩)
      have hsum_split :
          (Finset.Icc 1 (T + 1)).sum a =
            (Finset.Icc 1 T).sum a + a (T + 1) := by
        rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ T + 1)]
      have hleft_split :
          (Finset.Icc 1 (T + 1)).sum
              (fun t => a t / (a₀ + (Finset.Icc 1 t).sum a)) =
            (Finset.Icc 1 T).sum
                (fun t => a t / (a₀ + (Finset.Icc 1 t).sum a)) +
              a (T + 1) / (a₀ + (Finset.Icc 1 (T + 1)).sum a) := by
        rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ T + 1)]
      have hprefix_nonneg : 0 ≤ (Finset.Icc 1 T).sum a :=
        prefix_sum_nonneg (le_rfl : T ≤ T) ha_nonneg_T
      have hsucc_nonneg : 0 ≤ (Finset.Icc 1 (T + 1)).sum a := by
        rw [hsum_split]
        exact add_nonneg hprefix_nonneg hlast_nonneg
      have hprefix_pos : 0 < a₀ + (Finset.Icc 1 T).sum a :=
        add_pos_of_pos_of_nonneg ha₀ hprefix_nonneg
      have hstep :
          a (T + 1) / (a₀ + (Finset.Icc 1 (T + 1)).sum a) ≤
            Real.log (a₀ + (Finset.Icc 1 (T + 1)).sum a) -
              Real.log (a₀ + (Finset.Icc 1 T).sum a) := by
        have hraw := log_increment_ratio_bound hprefix_pos hlast_nonneg
        rw [hsum_split]
        simpa [add_assoc] using hraw
      have hlog_T :
          Real.log (1 + (Finset.Icc 1 T).sum a / a₀) =
            Real.log (a₀ + (Finset.Icc 1 T).sum a) - Real.log a₀ :=
        log_one_add_div_eq_log_sub_log hprefix_nonneg
      have hlog_succ :
          Real.log (1 + (Finset.Icc 1 (T + 1)).sum a / a₀) =
            Real.log (a₀ + (Finset.Icc 1 (T + 1)).sum a) - Real.log a₀ :=
        log_one_add_div_eq_log_sub_log hsucc_nonneg
      calc
        (Finset.Icc 1 (T + 1)).sum
            (fun t => a t / (a₀ + (Finset.Icc 1 t).sum a)) =
          (Finset.Icc 1 T).sum
              (fun t => a t / (a₀ + (Finset.Icc 1 t).sum a)) +
            a (T + 1) / (a₀ + (Finset.Icc 1 (T + 1)).sum a) := hleft_split
        _ ≤ Real.log (1 + (Finset.Icc 1 T).sum a / a₀) +
            a (T + 1) / (a₀ + (Finset.Icc 1 (T + 1)).sum a) := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_right (ih ha_nonneg_T)
              (a (T + 1) / (a₀ + (Finset.Icc 1 (T + 1)).sum a))
        _ ≤ Real.log (1 + (Finset.Icc 1 (T + 1)).sum a / a₀) := by
          rw [hlog_T, hlog_succ]
          linarith

/-- Uniformly capped nonnegative increments divided by their cap plus prefix sum
have total sum at most the logarithm of the horizon plus two.

Layer: Glue | Gap: Level 1 (uniform-cap cumulative-denominator horizon bound)
Proof: apply the data-dependent cumulative-denominator logarithmic bound, estimate the total increment by `T * cap`, divide by the positive cap, and use monotonicity of the logarithm.
Source: Mathlib finite sums on natural closed intervals, ordered-field division, and real logarithm monotonicity
Used in: adaptive-gradient and self-normalized convergence proofs that turn uniformly bounded squared-gradient prefix ratios into a logarithmic iteration budget
Book citation: book/STORM/StochasticRecursiveMomentum.json#/main_theorem/proof/12
Origin algorithm: Cutkosky and Orabona, Momentum-Based Variance Reduction in Non-Convex SGD, STOchastic Recursive Momentum -/
theorem sum_div_add_prefix_sum_le_log_nat_add_two_of_le
    (a : ℕ → ℝ) (cap : ℝ) (T : ℕ)
    (hcap : 0 < cap)
    (ha_nonneg : ∀ t, t ∈ Finset.Icc 1 T → 0 ≤ a t)
    (ha_le : ∀ t, t ∈ Finset.Icc 1 T → a t ≤ cap) :
    (Finset.sum (Finset.Icc 1 T)
      (fun t => a t / (cap + Finset.sum (Finset.Icc 1 t) a))) ≤
        Real.log (T + 2 : ℝ) := by
  have hdata :=
    sum_div_add_prefix_sum_le_log_one_add_sum_div_of_pos_of_nonneg
      cap a T hcap ha_nonneg
  have hsum_le :
      (Finset.Icc 1 T).sum a ≤ (T : ℝ) * cap := by
    calc
      (Finset.Icc 1 T).sum a ≤
          (Finset.Icc 1 T).sum (fun _t => cap) := by
            exact Finset.sum_le_sum (fun t ht => ha_le t ht)
      _ = (T : ℝ) * cap := by
            rw [sum_Icc_one_eq_sum_range_succ]
            simp
  have hsum_nonneg : 0 ≤ (Finset.Icc 1 T).sum a :=
    Finset.sum_nonneg (fun t ht => ha_nonneg t ht)
  have hdiv_le : (Finset.Icc 1 T).sum a / cap ≤ (T : ℝ) := by
    rw [div_le_iff₀ hcap]
    simpa [mul_comm] using hsum_le
  have harg_pos : 0 < 1 + (Finset.Icc 1 T).sum a / cap :=
    add_pos_of_pos_of_nonneg zero_lt_one (div_nonneg hsum_nonneg hcap.le)
  have harg_le :
      1 + (Finset.Icc 1 T).sum a / cap ≤ (T + 2 : ℝ) := by
    norm_num at hdiv_le ⊢
    linarith
  exact hdata.trans (Real.log_le_log harg_pos harg_le)

/-- A continuous observable composed with an almost-everywhere compact-valued input
has a uniform nonnegative almost-everywhere norm bound.

Layer: Glue | Gap: Level 1 (almost-everywhere transport of a compact continuous norm bound)
Proof: obtain a uniform norm bound on the compact set from `exists_nonneg_norm_bound_of_isCompact_of_continuousOn`, then transport it pointwise along the almost-everywhere membership hypothesis.
Source: Mathlib compact extreme-value and almost-everywhere filter APIs, via SOptLib's compact continuous norm-bound theorem
Used in: recursive-momentum and adaptive stochastic-gradient proofs bounding continuous coefficient observables of almost-everywhere compact-valued accumulated histories
Book citation: book/STORM/StochasticRecursiveMomentum.json#/algorithm_spec
Origin algorithm: Cutkosky and Orabona, Momentum-Based Variance Reduction in Non-Convex SGD, STOchastic Recursive Momentum -/
theorem exists_nonneg_ae_norm_bound_comp_of_eventually_mem_compact_of_continuousOn
    {Ω α β : Type*} [MeasurableSpace Ω] [TopologicalSpace α]
    [SeminormedAddGroup β]
    (μ : Measure Ω) (K : Set α) (X : Ω → α) (f : α → β)
    (hX : ∀ᵐ ω ∂μ, X ω ∈ K) (hcompact : IsCompact K)
    (hcont : ContinuousOn f K) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᵐ ω ∂μ, ‖f (X ω)‖ ≤ A := by
  rcases exists_nonneg_norm_bound_of_isCompact_of_continuousOn
      (fun x => ‖f x‖) hcompact hcont.norm with ⟨A, hA_nonneg, hA⟩
  refine ⟨A, hA_nonneg, hX.mono ?_⟩
  intro ω hω
  simpa using hA (X ω) hω

/-- For positive ordered endpoints, the cube-root increment is at most the
tangent slope at the lower endpoint times the endpoint increment.

Layer: Glue | Gap: Level 1 (cube-root secant bound at a positive endpoint)
Proof: normalize the one-third powers by cubing, factor their difference of
  cubes, and lower-bound the positive factor by three times the lower square.
Source: Mathlib `Real.rpow_mul`, `Real.rpow_le_rpow`, and ordered-field division
  from `Analysis.SpecialFunctions.Pow.Real`
Used in: adaptive recursive-momentum analysis bounding reciprocal stepsize
  increments when the accumulated squared-gradient denominator increases
Book citation: book/STORM/StochasticRecursiveMomentum.json#/main_theorem/proof/6
Origin algorithm: Cutkosky and Orabona, Momentum-Based Variance Reduction in
  Non-Convex SGD, STOchastic Recursive Momentum -/
theorem real_rpow_one_third_sub_le_div_three_rpow_two_thirds
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    b ^ ((1 : ℝ) / 3) - a ^ ((1 : ℝ) / 3) ≤
      (b - a) / (3 * a ^ ((2 : ℝ) / 3)) := by
  have hb_pos : 0 < b := lt_of_lt_of_le ha hab
  have ha_nonneg : 0 ≤ a := le_of_lt ha
  have hb_nonneg : 0 ≤ b := le_of_lt hb_pos
  let rb : ℝ := b ^ ((1 : ℝ) / 3)
  let ra : ℝ := a ^ ((1 : ℝ) / 3)
  have hra_pos : 0 < ra := by
    dsimp [ra]
    exact Real.rpow_pos_of_pos ha ((1 : ℝ) / 3)
  have hrb_ge_ra : ra ≤ rb := by
    dsimp [ra, rb]
    exact Real.rpow_le_rpow ha_nonneg hab (by norm_num)
  have hcube_b : rb ^ 3 = b := by
    dsimp [rb]
    have hpow := Real.rpow_mul hb_nonneg ((1 : ℝ) / 3) (3 : ℝ)
    simpa [show ((1 : ℝ) / 3) * 3 = 1 by norm_num] using hpow.symm
  have hcube_a : ra ^ 3 = a := by
    dsimp [ra]
    have hpow := Real.rpow_mul ha_nonneg ((1 : ℝ) / 3) (3 : ℝ)
    simpa [show ((1 : ℝ) / 3) * 3 = 1 by norm_num] using hpow.symm
  let D : ℝ := rb ^ 2 + rb * ra + ra ^ 2
  have hfactor : (rb - ra) * D = b - a := by
    dsimp [D]
    calc
      (rb - ra) * (rb ^ 2 + rb * ra + ra ^ 2) = rb ^ 3 - ra ^ 3 := by ring
      _ = b - a := by rw [hcube_b, hcube_a]
  have hD_ge : 3 * ra ^ 2 ≤ D := by
    have hprod_nonneg : 0 ≤ (rb - ra) * (rb + 2 * ra) := by
      exact mul_nonneg (sub_nonneg.mpr hrb_ge_ra) (by positivity)
    dsimp [D]
    nlinarith
  have hD_pos : 0 < D := lt_of_lt_of_le (by positivity : 0 < 3 * ra ^ 2) hD_ge
  have hD_ne : D ≠ 0 := ne_of_gt hD_pos
  have hnum_nonneg : 0 ≤ b - a := sub_nonneg.mpr hab
  have hdiff_eq : rb - ra = (b - a) / D := by
    rw [eq_div_iff hD_ne]
    exact hfactor
  have hdiv_le : (b - a) / D ≤ (b - a) / (3 * ra ^ 2) := by
    exact div_le_div_of_nonneg_left hnum_nonneg (by positivity : 0 < 3 * ra ^ 2) hD_ge
  have hra_sq : ra ^ 2 = a ^ ((2 : ℝ) / 3) := by
    dsimp [ra]
    have hpow := Real.rpow_mul ha_nonneg ((1 : ℝ) / 3) (2 : ℝ)
    simpa [one_div, show (3 : ℝ)⁻¹ * 2 = (2 : ℝ) / 3 by norm_num,
      Real.rpow_two] using hpow.symm
  calc
    b ^ ((1 : ℝ) / 3) - a ^ ((1 : ℝ) / 3) = rb - ra := by rfl
    _ = (b - a) / D := hdiff_eq
    _ ≤ (b - a) / (3 * ra ^ 2) := hdiv_le
    _ = (b - a) / (3 * a ^ ((2 : ℝ) / 3)) := by rw [hra_sq]

/-- Cubing the two-thirds real power of a nonnegative real recovers its square.

Layer: Glue | Gap: Level 0 (fractional real-power cube normalization)
Proof: apply `Real.rpow_mul` to the nonnegative base, normalize the product of
  exponents to two, and rewrite the resulting real square with `Real.rpow_two`.
Source: Mathlib real-power composition and integer-exponent normalization in
  `Analysis.SpecialFunctions.Pow.Real`
Used in: adaptive recursive-momentum parameter calculations that cube a
  two-thirds-power scale while simplifying stepsize and momentum coefficients
Book citation: book/STORM/StochasticRecursiveMomentum.json#/main_theorem/proof/9
Origin algorithm: Cutkosky and Orabona, Momentum-Based Variance Reduction in
  Non-Convex SGD, STOchastic Recursive Momentum -/
theorem real_rpow_two_thirds_pow_three {x : ℝ} (hx : 0 ≤ x) :
    (Real.rpow x ((2 : ℝ) / 3)) ^ 3 = x ^ 2 := by
  have hmul := (Real.rpow_mul hx ((2 : ℝ) / 3) (3 : ℝ)).symm
  simpa [show ((2 : ℝ) / 3) * 3 = 2 by norm_num, Real.rpow_two] using hmul

/-- A nonnegative real raised to an exponent in the unit interval is at most the
affine majorant given by the base plus one.

Layer: Glue | Gap: Level 0 (sublinear real-power affine majorant)
Proof: split according to whether the base is at most one; use
  `Real.rpow_le_one` on the small branch and `Real.rpow_le_self_of_one_le` on
  the large branch, then compare with `x + 1`.
Source: Mathlib real-power order lemmas in `Analysis.SpecialFunctions.Pow.Real`
Used in: fractional-moment integrability and Jensen steps that dominate a
  nonnegative random quantity raised to an exponent in `[0, 1]` by an
  integrable affine function
Book citation: book/STORM/StochasticRecursiveMomentum.json#/main_theorem/proof/24
Origin algorithm: Cutkosky and Orabona, Momentum-Based Variance Reduction in
  Non-Convex SGD, STOchastic Recursive Momentum -/
theorem rpow_le_self_add_one_of_nonneg_of_mem_Icc
    {x p : ℝ} (hx : 0 ≤ x) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    Real.rpow x p ≤ x + 1 := by
  by_cases hx_le_one : x ≤ 1
  · have hpow_le_one : Real.rpow x p ≤ 1 :=
      Real.rpow_le_one hx hx_le_one hp.1
    linarith
  · have hone_le : 1 ≤ x := le_of_not_ge hx_le_one
    have hpow_le_self : Real.rpow x p ≤ x :=
      Real.rpow_le_self_of_one_le hone_le hp.2
    linarith

/-- A nonnegative scalar whose square is bounded by a coefficient times its
two-thirds power is bounded by the coefficient's three-fourths power.

Layer: Glue | Gap: Level 1 (fractional-power scalar inequality solving)
Proof: split off the zero case, divide by the positive two-thirds power, rewrite
  the quotient as the four-thirds power, and invert that positive exponent.
Source: Mathlib `Real.rpow_sub`, `Real.le_rpow_inv_iff_of_pos`, and ordered-field
  division APIs for real powers
Used in: fractional-rate convergence proofs that solve a self-referential scalar
  bound after a root-sum or moment estimate has produced a two-thirds-power term
Book citation: book/STORM/StochasticRecursiveMomentum.json#/main_theorem/proof/29
Origin algorithm: Cutkosky and Orabona, Momentum-Based Variance Reduction in
  Non-Convex SGD, STOchastic Recursive Momentum -/
theorem le_rpow_three_fourths_of_sq_le_mul_rpow_two_thirds
    {A X : ℝ} (hA_nonneg : 0 ≤ A) (hX_nonneg : 0 ≤ X)
    (hbound : X ^ 2 ≤ A * Real.rpow X ((2 : ℝ) / 3)) :
    X ≤ Real.rpow A ((3 : ℝ) / 4) := by
  by_cases hXzero : X = 0
  · subst X
    exact Real.rpow_nonneg hA_nonneg _
  · have hXpos : 0 < X := lt_of_le_of_ne hX_nonneg (Ne.symm hXzero)
    have hX23_pos : 0 < Real.rpow X ((2 : ℝ) / 3) :=
      Real.rpow_pos_of_pos hXpos _
    have hdiv0 := div_le_div_of_nonneg_right hbound (le_of_lt hX23_pos)
    have hdiv :
        X ^ 2 / Real.rpow X ((2 : ℝ) / 3) ≤ A := by
      calc
        X ^ 2 / Real.rpow X ((2 : ℝ) / 3)
            ≤ (A * Real.rpow X ((2 : ℝ) / 3)) /
                Real.rpow X ((2 : ℝ) / 3) := hdiv0
        _ = A := by field_simp [ne_of_gt hX23_pos]
    have hX43_le : Real.rpow X ((4 : ℝ) / 3) ≤ A := by
      have hsub := Real.rpow_sub hXpos (2 : ℝ) ((2 : ℝ) / 3)
      norm_num at hsub
      have hleft_eq :
          X ^ 2 / Real.rpow X ((2 : ℝ) / 3) =
            Real.rpow X ((4 : ℝ) / 3) := by
        simpa [Real.rpow_natCast] using hsub.symm
      rw [← hleft_eq]
      exact hdiv
    rw [show (3 : ℝ) / 4 = ((4 : ℝ) / 3)⁻¹ by norm_num]
    exact (Real.le_rpow_inv_iff_of_pos hX_nonneg hA_nonneg (by norm_num)).2 hX43_le

/-- The reciprocal increment between adjacent inverse-cube-root step sizes is
bounded by the current step when the accumulator increment is bounded.

If the current positive base is the previous base plus a nonnegative increment,
the increment is at most `bound` and at most half the previous base, and the
current step is at most `1 / (4 * L)`, then the reciprocal-step increment has
the displayed `bound / (7 * L * scale ^ 3)` control.

Layer: Glue | Gap: Level 1 (reciprocal inverse-cube-root adjacent-step bound)
Proof: apply the cube-root secant bound, compare adjacent two-thirds powers using
  the relative-increment hypothesis, and use the current step cap to absorb the
  remaining denominator factors.
Source: Mathlib real-power monotonicity and ordered-field division APIs,
  together with the cube-root secant estimate from concavity of the one-third power
Used in: recursive-momentum, AdaGrad-style, and adaptive stochastic-gradient
  drift estimates that absorb a reciprocal adaptive-step increment into a
  current-step error budget
Book citation: book/STORM/StochasticRecursiveMomentum.json#/main_theorem/proof/6
Origin algorithm: Cutkosky and Orabona, Momentum-Based Variance Reduction in
  Non-Convex SGD, STOchastic Recursive Momentum -/
theorem reciprocal_inverse_cube_root_step_increment_le
    (prevBase currBase inc scale L bound : ℝ)
    (hprev_pos : 0 < prevBase)
    (hcurr_eq : currBase = prevBase + inc)
    (hinc_nonneg : 0 ≤ inc)
    (hinc_le : inc ≤ bound)
    (hinc_relative : 2 * inc ≤ prevBase)
    (hscale_pos : 0 < scale)
    (hL_pos : 0 < L)
    (hstep_le :
      scale / Real.rpow currBase ((1 : ℝ) / 3) ≤ (1 : ℝ) / (4 * L)) :
    1 / (scale / Real.rpow currBase ((1 : ℝ) / 3)) -
        1 / (scale / Real.rpow prevBase ((1 : ℝ) / 3)) ≤
      (bound / (7 * L * scale ^ 3)) *
        (scale / Real.rpow currBase ((1 : ℝ) / 3)) := by
  let currRoot : ℝ := Real.rpow currBase ((1 : ℝ) / 3)
  let prevRoot : ℝ := Real.rpow prevBase ((1 : ℝ) / 3)
  let prevPow : ℝ := Real.rpow prevBase ((2 : ℝ) / 3)
  let currPow : ℝ := Real.rpow currBase ((2 : ℝ) / 3)
  have hcurr_pos : 0 < currBase := by
    rw [hcurr_eq]
    positivity
  have hcurr_nonneg : 0 ≤ currBase := hcurr_pos.le
  have hprev_nonneg : 0 ≤ prevBase := hprev_pos.le
  have hcurrRoot_pos : 0 < currRoot := by
    exact Real.rpow_pos_of_pos hcurr_pos ((1 : ℝ) / 3)
  have hprevRoot_pos : 0 < prevRoot := by
    exact Real.rpow_pos_of_pos hprev_pos ((1 : ℝ) / 3)
  have hprevPow_pos : 0 < prevPow := by
    exact Real.rpow_pos_of_pos hprev_pos ((2 : ℝ) / 3)
  have hprev_le_curr : prevBase ≤ currBase := by
    rw [hcurr_eq]
    exact le_add_of_nonneg_right hinc_nonneg
  have hcurr_le_three_halves_prev :
      currBase ≤ ((3 : ℝ) / 2) * prevBase := by
    rw [hcurr_eq]
    nlinarith
  have hcurrPow_le_scaled_prevPow :
      currPow ≤ ((3 : ℝ) / 2) * prevPow := by
    have hpow_mono :
        currPow ≤
          Real.rpow (((3 : ℝ) / 2) * prevBase) ((2 : ℝ) / 3) := by
      exact Real.rpow_le_rpow hcurr_nonneg hcurr_le_three_halves_prev (by norm_num)
    have hscaled_pow :
        Real.rpow (((3 : ℝ) / 2) * prevBase) ((2 : ℝ) / 3) =
          Real.rpow ((3 : ℝ) / 2) ((2 : ℝ) / 3) * prevPow := by
      dsimp [prevPow]
      exact Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3 / 2) hprev_nonneg
    have hconst_le :
        Real.rpow ((3 : ℝ) / 2) ((2 : ℝ) / 3) ≤ (3 : ℝ) / 2 :=
      Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)
    calc
      currPow ≤ Real.rpow (((3 : ℝ) / 2) * prevBase) ((2 : ℝ) / 3) :=
        hpow_mono
      _ = Real.rpow ((3 : ℝ) / 2) ((2 : ℝ) / 3) * prevPow := hscaled_pow
      _ ≤ ((3 : ℝ) / 2) * prevPow :=
        mul_le_mul_of_nonneg_right hconst_le hprevPow_pos.le
  have hprevPow_lower : 2 * currPow ≤ 3 * prevPow := by
    nlinarith
  have hcurrPow_eq_root_sq : currPow = currRoot ^ 2 := by
    have hpow := Real.rpow_mul hcurr_nonneg ((1 : ℝ) / 3) (2 : ℝ)
    simpa [currPow, currRoot, one_div,
      show (3 : ℝ)⁻¹ * 2 = (2 : ℝ) / 3 by norm_num,
      Real.rpow_two] using hpow
  have hroot_ge_fourLscale : 4 * L * scale ≤ currRoot := by
    have hfourL_pos : 0 < 4 * L := by positivity
    have htmp : scale * (4 * L) / currRoot ≤ 1 := by
      calc
        scale * (4 * L) / currRoot =
            (4 * L) * (scale / currRoot) := by ring
        _ ≤ (4 * L) * ((1 : ℝ) / (4 * L)) :=
          mul_le_mul_of_nonneg_left (by simpa [currRoot] using hstep_le) hfourL_pos.le
        _ = 1 := by field_simp [ne_of_gt hfourL_pos]
    have hmul : scale * (4 * L) ≤ currRoot := by
      simpa using (div_le_iff₀ hcurrRoot_pos).1 htmp
    nlinarith
  have hroot_sub :
      currRoot - prevRoot ≤ inc / (3 * prevPow) := by
    simpa [currRoot, prevRoot, prevPow, hcurr_eq] using
      (real_rpow_one_third_sub_le_div_three_rpow_two_thirds
        hprev_pos hprev_le_curr)
  have hrecip_eq :
      1 / (scale / currRoot) - 1 / (scale / prevRoot) =
        (currRoot - prevRoot) / scale := by
    field_simp [ne_of_gt hscale_pos, ne_of_gt hcurrRoot_pos,
      ne_of_gt hprevRoot_pos]
  have hscaled_root :
      (currRoot - prevRoot) / scale ≤ (inc / (3 * prevPow)) / scale :=
    div_le_div_of_nonneg_right hroot_sub hscale_pos.le
  have hinc_to_bound :
      (inc / (3 * prevPow)) / scale ≤
        (bound / (3 * prevPow)) / scale := by
    exact div_le_div_of_nonneg_right
      (div_le_div_of_nonneg_right hinc_le (by positivity)) hscale_pos.le
  have hbound_nonneg : 0 ≤ bound := le_trans hinc_nonneg hinc_le
  have hbound_scaled_final :
      (bound / (3 * prevPow)) / scale ≤
        (bound / (7 * L * scale ^ 3)) * (scale / currRoot) := by
    have hcurr_sq_lower : 7 * L * scale * currRoot ≤ 3 * prevPow := by
      have htwo_curr_sq_le : 2 * currRoot ^ 2 ≤ 3 * prevPow := by
        nlinarith [hprevPow_lower, hcurrPow_eq_root_sq]
      have hseven_le_two :
          7 * L * scale * currRoot ≤ 2 * currRoot ^ 2 := by
        nlinarith [hroot_ge_fourLscale, hcurrRoot_pos]
      exact le_trans hseven_le_two htwo_curr_sq_le
    have hunit_le :
        (1 / (3 * prevPow)) / scale ≤
          (1 / (7 * L * scale ^ 3)) * (scale / currRoot) := by
      field_simp [ne_of_gt hscale_pos, ne_of_gt hL_pos,
        ne_of_gt hprevPow_pos, ne_of_gt hcurrRoot_pos]
      nlinarith [hcurr_sq_lower]
    calc
      (bound / (3 * prevPow)) / scale =
          bound * ((1 / (3 * prevPow)) / scale) := by ring
      _ ≤ bound * ((1 / (7 * L * scale ^ 3)) * (scale / currRoot)) :=
        mul_le_mul_of_nonneg_left hunit_le hbound_nonneg
      _ = (bound / (7 * L * scale ^ 3)) * (scale / currRoot) := by ring
  change 1 / (scale / currRoot) - 1 / (scale / prevRoot) ≤
    (bound / (7 * L * scale ^ 3)) * (scale / currRoot)
  rw [hrecip_eq]
  exact le_trans (le_trans hscaled_root hinc_to_bound) hbound_scaled_final

-- Promoted from Staging/rpow_add_split_of_le_weighted_add.lean
-- Generalization plan (G0):
-- concept/name: fractional real-power split under weighted additive domination;
--   orig was `theorem1_terminal_rpow_pointwise_noise_grad_split`
-- generality used: seven real scalars, nonnegativity of the two power bases
--   and both factors in the extracted product, and an exponent in `[0, 1]`;
--   no measure, vector-space, convexity, smoothness, oracle, or
--   finite-dimensional data
-- portable call pattern: adaptive stochastic methods split a dominated terminal
--   statistic into two nonnegative error windows while varying the offset,
--   component weights, and fractional exponent
-- counterargument checked: the source theorem is not merely paper traceability or
--   a pure rename; it composes domination monotonicity, fractional-power
--   subadditivity, and extraction of the second weight into one reusable contract
-- coverage search: searches for `rpow weighted product split of upper bound` and
--   `real power of dominated weighted addition` found Mathlib's
--   `Real.rpow_le_rpow`, `Real.rpow_add_le_add_rpow`, and `Real.mul_rpow` as
--   separate components, but no Mathlib, SOptLib, or staged declaration with the
--   complete dominated weighted-split conclusion
-- minimal hypotheses: nonnegativity is imposed directly on the two bases used by
--   monotonicity and subadditivity; the second weight and component remain separate
--   because the product-power identity requires both; exponent membership supplies
--   exactly the lower and upper bounds used by those inequalities

/-- A fractional power of an offset dominated total splits into weighted component powers.

For nonnegative power bases and an exponent in `[0, 1]`, domination of `total`
by `a * left + b * right` bounds the power of `offset + total` by the power
of `offset + a * left` plus the factored power of the second weighted component.

Layer: Glue | Gap: Level 1 (fractional-power split under weighted additive domination)
Proof: use `Real.rpow_le_rpow` to transfer the domination, apply
  `Real.rpow_add_le_add_rpow` to the two nonnegative summands, and factor the
  second weighted power with `Real.mul_rpow`.
Source: Mathlib real-power monotonicity, subadditivity, and product identities in `Analysis.MeanInequalitiesPow` and `Analysis.SpecialFunctions.Pow.Real`
Used in: adaptive stochastic-gradient terminal bounds that separate a sampled-gradient aggregate into offset-noise and objective-gradient contributions
Book citation: book/STORM/StochasticRecursiveMomentum.json#/main_theorem/proof/24
Origin algorithm: Cutkosky and Orabona, Momentum-Based Variance Reduction in Non-Convex SGD, STOchastic Recursive Momentum -/
theorem rpow_add_split_of_le_weighted_add
    {offset total left right a b p : ℝ}
    (hbase_nonneg : 0 ≤ offset + total)
    (hleft_nonneg : 0 ≤ offset + a * left)
    (hright : 0 ≤ right) (hb : 0 ≤ b)
    (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (htotal_le : total ≤ a * left + b * right) :
    Real.rpow (offset + total) p ≤
      Real.rpow (offset + a * left) p +
        Real.rpow b p * Real.rpow right p := by
  have hbase_le :
      offset + total ≤ (offset + a * left) + b * right := by
    linarith
  have hright_nonneg : 0 ≤ b * right := mul_nonneg hb hright
  calc
    Real.rpow (offset + total) p ≤
        Real.rpow ((offset + a * left) + b * right) p :=
      Real.rpow_le_rpow hbase_nonneg hbase_le hp.1
    _ ≤ Real.rpow (offset + a * left) p + Real.rpow (b * right) p :=
      Real.rpow_add_le_add_rpow hleft_nonneg hright_nonneg hp.1 hp.2
    _ = Real.rpow (offset + a * left) p +
        Real.rpow b p * Real.rpow right p := by
      congr 1
      simpa using
        (Real.mul_rpow (x := b) (y := right) (z := p) hb hright)

-- Phase 4 batch 1 merge from Staging/lowerSemicontinuousOn_totalizeOn_of_closed_carrier_epigraph.lean
namespace SOptLib

-- Generalization plan (G0):
-- concept/name: carrier-subtype closed epigraph implies lower semicontinuity
--   on the carrier for the ambient `totalizeOn`; orig was
--   `lowerSemicontinuousOn_totalize_of_closed_subtype_epigraph`.
-- generality used: an arbitrary topological ambient type, carrier set, and
--   ordered topological codomain with closed upper rays are enough. No
--   vector-space, norm, convexity, measure, independence, integrability,
--   oracle, smoothness, or finite-dimensional hypothesis is used; the only
--   hypothesis is closedness of the subtype epigraph.
-- portable call pattern: prox-solvability and composite-objective proofs
--   define a regularizer or objective term on a feasible carrier subtype,
--   prove its subtype epigraph is closed, and then need lower
--   semicontinuity of the ambient carrier totalization on the carrier; the
--   carrier and subtype function vary while the conclusion shape stays fixed.
-- counterargument checked: not paper-local traceability and not a pure
--   rename, because Mathlib supplies the epigraph and restriction equivalences
--   separately but not the SOptLib `totalizeOn` carrier bridge. Existing
--   SOptLib carrier API covers value agreement, not lower semicontinuity.
-- coverage search: project queries `lower semicontinuous totalizeOn closed
--   epigraph carrier subtype` and `LowerSemicontinuousOn totalizeOn closed
--   epigraph subtype` found only the local private theorem plus carrier value
--   lemmas; LeanSearch query `closed epigraph lower semicontinuous function
--   subtype restrict` returned Mathlib
--   `lowerSemicontinuous_iff_isClosed_epigraph` and
--   `lowerSemicontinuous_restrict_iff`, which are proof ingredients rather
--   than this carrier-totalization statement.
-- minimal hypotheses: all already minimal; the proof only needs the subtype
--   closed epigraph and the definitional agreement of `totalizeOn` on carrier
--   points.

/-- A carrier-subtype function with closed epigraph totalizes to a lower
semicontinuous function on the carrier.

If the epigraph of a function on `{x // x in X}` is closed, then the ambient
zero-extension `SOptLib.totalizeOn X h` is lower semicontinuous when restricted
back to `X`.

Layer: Model | Gap: Level 0 (carrier totalization lower semicontinuity from closed epigraph)
Proof: convert the closed subtype epigraph to `LowerSemicontinuous h`, rewrite
  `LowerSemicontinuousOn` through `Set.restrict`, and identify the restriction
  of `SOptLib.totalizeOn X h` with `h` using `SOptLib.totalizeOn_of_mem`.
Source: Mathlib semicontinuity epigraph and restriction APIs, combined with
  SOptLib carrier totalization value agreement
Used in: nonconvex stochastic block mirror descent block-prox solvability,
  where each closed convex block regularizer is totalized from its feasible
  block carrier before adding the continuous Bregman-prox terms
Book citation: book/FOML/NonconvexStochasticBlockMirrorDescent.json#/assumptions/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic block mirror descent -/
theorem lowerSemicontinuousOn_totalizeOn_of_closed_carrier_epigraph
    {E γ : Type*} [TopologicalSpace E] [LinearOrder γ] [TopologicalSpace γ]
    [ClosedIciTopology γ] [Zero γ] {X : Set E} {h : {x : E // x ∈ X} → γ}
    (hh_closed : IsClosed {p : ({x : E // x ∈ X} × γ) | h p.1 ≤ p.2}) :
    LowerSemicontinuousOn (totalizeOn X h) X := by
  have hsub : LowerSemicontinuous h :=
    (lowerSemicontinuous_iff_isClosed_epigraph).2 hh_closed
  rw [← lowerSemicontinuous_restrict_iff]
  have heq : X.restrict (totalizeOn X h) = h := by
    ext x
    exact totalizeOn_of_mem X h x.2
  simpa [heq] using hsub

end SOptLib

-- Phase 4 batch 1 merge from Staging/lowerSemicontinuousOn_add_totalized_subtype_of_continuousOn.lean
-- Generalization plan (G0):
-- concept/name: lower semicontinuity of a continuous smooth part plus a
--   carrier-totalized subtype term; orig was
--   `blockProxObjective_lsc_closure_block`, renamed away from the block prox
--   objective and setup-local fields.
-- generality used: an arbitrary topological carrier type, a carrier set, a
--   codomain carrying the ordered-topological additive structure needed by
--   semicontinuity addition, an ambient continuous part, and a subtype term
--   with closed epigraph. No norm, inner-product, finite-dimensional,
--   convexity, measure, filtration, independence, integrability, oracle, or
--   DGF hypothesis is used by this lower-semicontinuity composition step.
-- portable call pattern: composite prox and nonsmooth objective existence
--   proofs first prove continuity of all smooth/Bregman/linear terms and
--   closed-epigraph lower semicontinuity of the carrier simple term, then call
--   this statement to obtain lower semicontinuity of the full ambient
--   totalized objective on the carrier; the carrier, smooth expression, and
--   subtype term vary while the conclusion shape stays fixed.
-- counterargument checked: not paper-local traceability because this packages
--   a reusable composition boundary; not a pure wrapper around Mathlib because
--   it includes the SOptLib `totalizeOn` subtype bridge before applying the
--   standard `LowerSemicontinuousOn.add` rule.
-- coverage search: searched `LowerSemicontinuousOn add totalize subtype
--   continuousOn closed epigraph`, `LowerSemicontinuousOn add continuousOn
--   lowerSemicontinuousOn`, and LeanSearch query `lower semicontinuous on sum
--   of continuous function and lower semicontinuous function`. Mathlib has
--   `LowerSemicontinuousOn.add` and `ContinuousOn.lowerSemicontinuousOn`; the
--   project has `SOptLib.lowerSemicontinuousOn_totalizeOn_of_closed_carrier_epigraph`.
--   No existing declaration combines the carrier-totalized subtype term with a
--   continuous ambient summand.
-- minimal hypotheses: all already minimal for the composed statement; the
--   smooth part needs only `ContinuousOn`, and the subtype term needs only the
--   closed epigraph consumed by the existing totalization lemma.

/-- A continuous ambient summand plus a carrier-totalized closed-epigraph
subtype term is lower semicontinuous on the carrier.

This is the carrier-totalized version of the standard rule that a continuous
function added to a lower semicontinuous function is lower semicontinuous.

Layer: Glue | Gap: Level 0 (continuous plus totalized subtype lsc composition)
Proof: turn the closed subtype epigraph into lower semicontinuity of
  `SOptLib.totalizeOn X chi` on `X`, turn the continuous summand into lower
  semicontinuity, and combine them with `LowerSemicontinuousOn.add`.
Source: Mathlib semicontinuity addition and continuous-to-lower-semicontinuous
  APIs, plus SOptLib carrier totalization lower-semicontinuity bridge
Used in: nonconvex stochastic block mirror descent block-prox solvability,
  where the linear-plus-Bregman smooth objective section is added to a
  closed-epigraph block regularizer totalized from the feasible carrier
Book citation: book/FOML/NonconvexStochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic block mirror descent -/
theorem lowerSemicontinuousOn_add_totalized_subtype_of_continuousOn
    {E γ : Type*} [TopologicalSpace E] [LinearOrder γ] [TopologicalSpace γ]
    [OrderTopology γ] [ClosedIciTopology γ] [AddCommMonoid γ]
    [IsOrderedAddMonoid γ] [ContinuousAdd γ]
    {X : Set E} (smoothPart : E → γ) (chi : {z : E // z ∈ X} → γ)
    (hsmooth : ContinuousOn smoothPart X)
    (hchi_closed : IsClosed {p : ({z : E // z ∈ X} × γ) | chi p.1 ≤ p.2}) :
    LowerSemicontinuousOn
      (fun z : E => smoothPart z + SOptLib.totalizeOn X chi z) X := by
  exact hsmooth.lowerSemicontinuousOn.add
    (SOptLib.lowerSemicontinuousOn_totalizeOn_of_closed_carrier_epigraph
      (X := X) (h := chi) hchi_closed)

-- Phase 4 batch 1 merge from Staging/exists_continuousLinearMap_add_const_le_of_closed_convex_lscOn.lean
-- Generalization plan (G0):
-- concept/name: affine lower minorant for a closed-carrier convex lower-
--   semicontinuous real function; orig was
--   closed_convex_block_term_affine_lower_bound, renamed away from block and
--   algorithm-local terminology.
-- generality used: real locally convex topological vector-space carrier `{E}`;
--   no norm, inner product, measure,
--   independence, integrability, oracle, smoothness, or finite-dimensional
--   hypothesis is used. The mathematical assumptions are `IsClosed X`,
--   `ConvexOn ℝ X f`, `LowerSemicontinuousOn f X`, and one carrier point.
-- portable call pattern: prox-existence and nonsmooth-composite coercivity
--   proofs supply a closed convex carrier and a closed convex penalty term,
--   then need a carrier-wide affine lower model; the Hilbert space, carrier,
--   function, and carrier point vary while the conclusion stays fixed.
-- counterargument checked: not paper-local traceability because the statement
--   is the standard closed-convex lsc affine-minorant step used before
--   coercivity; it is a corollary of Mathlib rather than duplicate local
--   Hahn-Banach algebra, and its weaker conclusion is the reusable call shape.
-- coverage search: searched `continuous linear map add constant lower bound
--   closed convex lower semicontinuous`, `affine minorant closed convex lower
--   semicontinuous epigraph`, and `ConvexOn exists affine le of lt lower
--   semicontinuous closed`. Mathlib has the stronger
--   `ConvexOn.exists_affine_le_of_lt`; SOptLib has
--   `IsSimpleConvexTermOn.exists_strict_affine_minorant` for a different
--   simple-term predicate. This staging specializes the Mathlib theorem to the
--   no-touch carrier-minorant shape used by prox proofs.
-- minimal hypotheses: all already minimal for this corollary; closedness is
--   required by the Mathlib separation theorem, and `z : X` supplies
--   nonemptiness.

/-- A closed-carrier convex lower-semicontinuous function has an affine lower
minorant on the carrier.

Given a closed carrier `X`, a function `f` that is convex and lower
semicontinuous on `X`, and one feasible point, there are a continuous linear
functional and a real constant whose sum is bounded above by `f` at every
carrier point.

Layer: Glue | Gap: Level 0 (closed convex lsc affine minorant)
Proof: apply Mathlib's `ConvexOn.exists_affine_le_of_lt` at the strict subvalue
  `f z - 1`, then forget the touching equality and rewrite the restricted
  affine map on carrier subtype points.
Source: Mathlib convex approximation by continuous affine functions
Used in: nonconvex stochastic block mirror descent prox-solvability, where a
  closed convex block penalty supplies an affine lower model before the
  quadratic prox term proves coercivity
Book citation: book/FOML/NonconvexStochasticBlockMirrorDescent.json#/assumptions/7
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic block mirror descent -/
theorem exists_continuousLinearMap_add_const_le_of_closed_convex_lscOn
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
    {X : Set E} {f : E → ℝ}
    (hX_closed : IsClosed X) (hf_convex : ConvexOn ℝ X f)
    (hf_lsc : LowerSemicontinuousOn f X) (z : {x : E // x ∈ X}) :
    ∃ (l : E →L[ℝ] ℝ) (c : ℝ),
      ∀ y : {x : E // x ∈ X}, l y.1 + c ≤ f y.1 := by
  obtain ⟨l, c, hle, _htouch⟩ :=
    hf_convex.exists_affine_le_of_lt (𝕜 := ℝ) z.2
      (a := f z.1 - 1)
      (sub_lt_self (f z.1) zero_lt_one)
      hX_closed hf_lsc
  exact ⟨l, c, fun y => by simpa using hle y⟩

-- Phase 4 batch 1 merge from Staging/exists_isMinOn_of_lsc_closed_coercive_closedBall.lean
-- Generalization plan (G0):
-- concept/name: constrained minimizer existence from lower semicontinuity,
--   closed feasible set, and a closed-ball coercive tail; orig was already
--   named `exists_isMinOn_of_lsc_closed_coercive_closedBall`.
-- generality used: a proper pseudo-metric space is enough to make closed balls
--   compact; no vector-space, norm, convexity, measure, independence,
--   integrability, oracle, smoothness, or finite-dimensional hypothesis is
--   used. The objective hypothesis is `LowerSemicontinuousOn F X`.
-- portable call pattern: noncompact proximal, mirror, and composite
--   subproblem proofs supply a closed carrier, one feasible base point, an lsc
--   objective, and a closed-ball lower tail, then need an `IsMinOn` witness;
--   the carrier, center, objective, and tail proof vary while the conclusion
--   stays fixed.
-- counterargument checked: not paper-local traceability and not a pure wrapper;
--   Mathlib gives compact lsc minimizer existence and SOptLib has the
--   continuous closed-ball coercive version, but neither exposes this lsc
--   noncompact truncation contract directly.
-- coverage search: project query `lower semicontinuous closed set coercive
--   closed ball IsMinOn minimizer existence` found SOptLib
--   `exists_isMinOn_of_closed_coercive_closedBall` with `ContinuousOn F X` and
--   Mathlib `LowerSemicontinuousOn.exists_isMinOn` only for compact sets;
--   LeanSearch for `lower semicontinuous function on closed set coercive
--   closed ball attains constrained minimum` returned the compact lsc theorem
--   and continuous cocompact variants, with no lsc closed-tail constrained
--   theorem.
-- minimal hypotheses: all already minimal for the proof shape; `ProperSpace`
--   supplies compact closed balls, closedness of `X` makes the truncation
--   compact, and the tail is only needed at the selected base value.

/-- A lower-semicontinuous objective on a nonempty closed set attains a
constrained minimum from a closed-ball coercive tail bound.

The theorem truncates the feasible set to `X ∩ closedBall z R`, applies compact
lower-semicontinuous minimizer existence on the truncation, and uses the tail
bound outside the ball to extend the minimum certificate back to all of `X`.

Layer: Glue | Gap: Level 1 (lsc closed-ball coercive constrained minimum existence)
Proof: choose the tail radius at the base value, minimize on the compact
  intersection of the closed carrier with the closed ball using
  `LowerSemicontinuousOn.exists_isMinOn`, then split each feasible comparison
  point by membership in that ball.
Source: Mathlib proper metric compact-ball API and lower-semicontinuous compact extreme-value theorem
Used in: nonconvex stochastic block mirror descent block-prox solvability, where
  a lower-semicontinuous composite block objective has a quadratic closed-ball
  tail over a closed block carrier
Book citation: book/FOML/NonconvexStochasticBlockMirrorDescent.json#/assumptions/7
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic block mirror descent -/
theorem exists_isMinOn_of_lsc_closed_coercive_closedBall
    {E : Type*} [PseudoMetricSpace E] [ProperSpace E]
    {X : Set E} (hX_closed : IsClosed X) (x0 z : E) (hx0 : x0 ∈ X)
    (F : E → ℝ) (hlsc : LowerSemicontinuousOn F X)
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
  have hlscK : LowerSemicontinuousOn F K := hlsc.mono (by
    intro x hx
    exact hx.1)
  obtain ⟨xmin, hxminK, hxmin_min⟩ :=
    LowerSemicontinuousOn.exists_isMinOn hK_nonempty hK_compact hlscK
  refine ⟨xmin, hxminK.1, ?_⟩
  intro y hy
  by_cases hyball : y ∈ Metric.closedBall z R
  · exact hxmin_min ⟨hy, hyball⟩
  · have hxmin_le_x0 : F xmin ≤ F x0 := hxmin_min ⟨hx0, hx0_ball⟩
    have hnot_dist : ¬ dist y z ≤ R := by
      simpa [Metric.mem_closedBall] using hyball
    have hR_le_dist : R ≤ dist y z := le_of_lt (lt_of_not_ge hnot_dist)
    exact le_trans hxmin_le_x0 (htail y hy hR_le_dist)

namespace Real

-- Generalization plan (G0):
-- concept/name: finite Jensen inequality for the real exponential; orig was exp_finset_weighted_sum_le_sum_weighted_exp and the staged name exposes the Mathlib-style `Real.exp` weighted finite-sum inequality.
-- generality used: arbitrary finite index type with real weights and real scalars; no measure, probability, convexity, smoothness, oracle, normed-space, or finite-dimensional hypotheses are used beyond Mathlib's convexity theorem for `Real.exp`.
-- portable call pattern: concentration and light-tail MGF proofs can apply the same finite convex-mixture step after proving nonnegative normalized weights, while changing the finite index set, weights, and scalar summands.
-- counterargument checked: not paper-local traceability because the statement is paper-free real analysis and packages the recurring scalar exponential Jensen boundary; not a duplicate of SOptLib weighted-output Jensen lemmas, which include explicit normalizers or vector-valued convex functions rather than the direct normalized `Real.exp` inequality.
-- coverage search: searched "Real exp finite weighted sum Jensen nonnegative weights sum one", "convexOn_exp map_sum_le weighted real exp Finset", and LeanSearch for the natural-language exponential Jensen statement; top hits were Mathlib `ConvexOn.map_sum_le` and `convexOn_exp`, plus SOptLib normalized weighted-average Jensen variants, giving partial generic coverage but no direct scalar exponential specialization.
-- minimal hypotheses: all already minimal; the proof uses only nonnegativity of weights on the finset and normalization of their finite sum to one.

/-- Jensen's inequality for the real exponential over a normalized finite weighted sum.

If the real weights on a finite set are nonnegative and sum to one, then the
exponential of the weighted scalar average is bounded by the weighted average
of the exponentials.

Layer: Glue | Gap: Level 0 (finite scalar exponential Jensen specialization)
Proof: apply Mathlib's finite Jensen theorem `ConvexOn.map_sum_le` to `convexOn_exp`, then rewrite real scalar multiplication as multiplication.
Source: Mathlib convex analysis APIs `convexOn_exp` and `ConvexOn.map_sum_le`
Used in: stochastic convex-concave saddle-point light-tail proof when bounding the exponential of a normalized weighted oracle-square sum by the weighted sum of single-step exponential moments
Book citation: book/FOML/StochasticConvexConcaveSaddlePoint.json#/assumptions/14
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic mirror descent for stochastic convex-concave saddle point problems -/
theorem exp_finset_weighted_sum_le_sum_weighted_exp
    {ι : Type*} (s : Finset ι) (w x : ι → ℝ)
    (hw_nonneg : ∀ i ∈ s, 0 ≤ w i)
    (hw_sum : Finset.sum s w = 1) :
    Real.exp (Finset.sum s (fun i => w i * x i)) ≤
      Finset.sum s (fun i => w i * Real.exp (x i)) := by
  have hJ :=
    convexOn_exp.map_sum_le
      (t := s) (w := w) (p := x)
      hw_nonneg hw_sum (fun _ _ => Set.mem_univ _)
  simpa [smul_eq_mul] using hJ

set_option maxHeartbeats 4000000

-- Generalization plan (G0):
-- concept/name: scalar exponential-square domination; orig was exp_linear_le_linear_add_exp_nine_sixteenth_sq and the staged name exposes the Mathlib-style real exponential inequality.
-- generality used: one real variable only; no measure, probability, convexity, smoothness, oracle, normed-space, or finite-dimensional hypotheses are used.
-- portable call pattern: scalar MGF and light-tail proofs in stochastic mirror-descent variants can apply the same pointwise inequality to a changing real scalar such as a weighted oracle-noise inner product.
-- counterargument checked: not paper-local traceability because the statement is a pure real-analysis inequality reused by multiple scalar MGF adapters; not a pure wrapper because Mathlib has only generic Taylor bounds and weaker/simple exponential inequalities, not this sharp square-exponential domination.
-- coverage search: searched "Real.exp x ≤ x + Real.exp (9 * x ^ 2 / 16) exponential upper bound", "exp_le_self_add_exp nine sixteenth square", and LeanSearch for the same natural-language statement; top hits were the local private theorem, local duplicated algorithm theorem, SOptLib.Real.exp_le_one_add_two_mul_of_mem_Icc_zero_one, and Mathlib Real.add_one_le_exp / Real.exp_bound', giving partial coverage only.
-- minimal hypotheses: all already minimal; the result is pointwise over x : ℝ and needs no assumptions.

/-- Nonnegative real exponential dominates its quadratic Taylor truncation.

Layer: Glue | Gap: Level 0 (real exponential Taylor lower bound)
Proof: apply monotonicity of the residual on `[0, x]`; the derivative is
  nonnegative by `Real.add_one_le_exp`.
Source: Mathlib real exponential Taylor and derivative APIs in `Analysis.Complex.Exponential`
Used in: scalar MGF light-tail proofs that lower-bound a square-exponential term by a polynomial truncation
Book citation: book/FOML/StochasticConvexConcaveSaddlePoint.json#/key_lemmas
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic mirror descent for stochastic convex-concave saddle point problems -/
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
            convert hsq.const_mul ((1 : ℝ) / 2) using 1
            ring
          simpa using
            ((hasDerivAt_const (x := z) (c := (1 : ℝ))).add
              (hasDerivAt_id' z)).add hsq_div
        have hf_has : HasDerivAt f (Real.exp z - (1 + z)) z := by
          convert (Real.hasDerivAt_exp z).sub hp using 1
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

/-- Nonnegative real exponential dominates its cubic Taylor truncation.

Layer: Glue | Gap: Level 0 (real exponential cubic Taylor lower bound)
Proof: apply monotonicity of the cubic residual on `[0, x]`; the derivative
  reduces to the quadratic Taylor lower bound above.
Source: Mathlib real exponential Taylor and derivative APIs in `Analysis.Complex.Exponential`
Used in: scalar MGF light-tail proofs that compare `exp ((9/16) x^2)` with cubic polynomial certificates
Book citation: book/FOML/StochasticConvexConcaveSaddlePoint.json#/key_lemmas
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic mirror descent for stochastic convex-concave saddle point problems -/
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
            convert hsq.const_mul ((1 : ℝ) / 2) using 1
            ring
          have hcube : HasDerivAt (fun t : ℝ => t ^ 3) (3 * z ^ 2) z := by
            simpa using (hasDerivAt_pow 3 z)
          have hcube_div :
              HasDerivAt (fun t : ℝ => (1 / 6 : ℝ) * t ^ 3)
                ((1 / 2 : ℝ) * z ^ 2) z := by
            convert hcube.const_mul ((1 : ℝ) / 6) using 1
            ring
          simpa using
            (((hasDerivAt_const (x := z) (c := (1 : ℝ))).add
              (hasDerivAt_id' z)).add hsq_div).add hcube_div
        have hf_has :
            HasDerivAt f (Real.exp z - (1 + z + (1 / 2 : ℝ) * z ^ 2)) z := by
          convert (Real.hasDerivAt_exp z).sub hp using 1
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

/-- Quartic certificate for the small positive branch of the `9/16` exponential-square bound.

Layer: Glue | Gap: Level 0 (polynomial certificate on the unit interval)
Proof: split the unit interval at `1/2` and `2/3`, then rewrite the quartic
  around a nonnegative local coordinate with positive or bounded terms.
Source: ordered-field polynomial arithmetic with `ring`, `nlinarith`, and positivity
Used in: scalar MGF light-tail proofs that need the sharp `9/16` Taylor comparison for `0 ≤ x ≤ 1`
Book citation: book/FOML/StochasticConvexConcaveSaddlePoint.json#/key_lemmas
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic mirror descent for stochastic convex-concave saddle point problems -/
private theorem quartic_nonneg_for_exp_nine_small {y : ℝ} (_hy0 : 0 ≤ y)
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

/-- Small positive branch of the `9/16` exponential-square bound.

Layer: Glue | Gap: Level 1 (small-interval exponential-square comparison)
Proof: upper-bound `exp y` by Mathlib's Taylor remainder bound at order four,
  lower-bound `exp ((9/16) y^2)` by the cubic Taylor truncation, and close the
  remaining comparison with the quartic certificate.
Source: Mathlib real exponential Taylor upper bound `Real.exp_bound'` and polynomial arithmetic
Used in: scalar MGF light-tail proofs on the bounded positive interval `0 ≤ x ≤ 1`
Book citation: book/FOML/StochasticConvexConcaveSaddlePoint.json#/key_lemmas
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic mirror descent for stochastic convex-concave saddle point problems -/
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

/-- Mid positive branch of the `9/16` exponential-square bound.

Layer: Glue | Gap: Level 1 (middle-interval exponential-square comparison)
Proof: prove monotonicity of `z + exp ((9/16)z^2) - exp z` on `[1, 16/9]`
  by derivative comparison, then check the endpoint with a Taylor lower bound.
Source: Mathlib derivative monotonicity, real exponential Taylor bounds, and polynomial arithmetic
Used in: scalar MGF light-tail proofs on the bounded positive interval `1 ≤ x < 16/9`
Book citation: book/FOML/StochasticConvexConcaveSaddlePoint.json#/key_lemmas
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic mirror descent for stochastic convex-concave saddle point problems -/
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

/-- The real exponential is dominated by a linear term plus a `9/16` square-exponential term.

For every real `x`, `exp x ≤ x + exp (9 * x^2 / 16)`.  This scalar bound is
the pointwise real-analysis leaf used before integrating light-tail
exponential-square moment assumptions into linear MGF bounds.

Layer: Glue | Gap: Level 1 (scalar exponential-square domination)
Proof: split by the sign and by the large-tail threshold `16/9`; the bounded
  positive interval uses Taylor upper/lower bounds and polynomial certificates,
  while both tails reduce to monotonicity of `exp` and `Real.add_one_le_exp`.
Source: Mathlib real exponential Taylor bounds `Real.exp_bound` and `Real.exp_bound'`
Used in: stochastic convex-concave saddle-point mirror descent when converting fixed-fiber scalar oracle-noise light-tail control into the one-step linear MGF estimate
Book citation: book/FOML/StochasticConvexConcaveSaddlePoint.json#/key_lemmas
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic mirror descent for stochastic convex-concave saddle point problems -/
theorem exp_le_self_add_exp_nine_mul_sq_div_sixteen (x : ℝ) :
    Real.exp x ≤ x + Real.exp (9 * x ^ 2 / 16) := by
  have hbounded :
      ∀ y : ℝ, 0 ≤ y → y < (16 : ℝ) / 9 →
        Real.exp y ≤ y + Real.exp (9 * y ^ 2 / 16) ∧
          Real.exp (-y) + y ≤ Real.exp (9 * y ^ 2 / 16) := by
    intro y hy0 hy_upper
    let a : ℝ := 9 / 16
    have hquad_nonneg : 0 ≤ a * y ^ 2 := by positivity
    have hlower_quad :
        1 + a * y ^ 2 + (1 / 2 : ℝ) * (a * y ^ 2) ^ 2 ≤
          Real.exp (a * y ^ 2) := by
      exact one_add_self_add_sq_div_two_le_exp hquad_nonneg
    constructor
    · by_cases hy1 : y ≤ 1
      · exact exp_pos_small_branch_le_self_add_exp_nine_mul_sq_div_sixteen hy0 hy1
      · have hy1' : 1 ≤ y := le_of_not_ge hy1
        exact exp_pos_mid_branch_le_self_add_exp_nine_mul_sq_div_sixteen hy1' hy_upper
    · by_cases hy1 : y ≤ 1
      · have hy_abs : |(-y : ℝ)| ≤ 1 := by
          rw [abs_neg, abs_of_nonneg hy0]
          exact hy1
        have hupper :=
          Real.exp_bound (x := -y) (n := 4) hy_abs (by norm_num)
        have hupper_exp :
            Real.exp (-y) ≤
              (∑ m ∈ Finset.range 4, (-y) ^ m / (m.factorial : ℝ)) +
                y ^ 4 * ((5 : ℝ) / ((Nat.factorial 4 : ℝ) * 4)) := by
          have habs_pow : |(-y : ℝ)| ^ 4 = y ^ 4 := by
            rw [abs_neg, abs_of_nonneg hy0]
          have hleft := (abs_sub_le_iff.mp hupper).1
          rw [habs_pow] at hleft
          simpa [Nat.succ_eq_add_one] using sub_le_iff_le_add'.mp hleft
        have hpoly :
            (∑ m ∈ Finset.range 4, (-y) ^ m / (m.factorial : ℝ)) +
                y ^ 4 * ((5 : ℝ) / ((Nat.factorial 4 : ℝ) * 4)) + y
              ≤ 1 + a * y ^ 2 + (1 / 2 : ℝ) * (a * y ^ 2) ^ 2 := by
          have hy_sq_nonneg : 0 ≤ y ^ 2 := sq_nonneg y
          have hy3_nonneg : 0 ≤ y ^ 3 := by positivity
          norm_num [a, Finset.sum_range_succ, pow_succ]
          nlinarith [hy_sq_nonneg, hy3_nonneg]
        calc
          Real.exp (-y) + y
              ≤ (∑ m ∈ Finset.range 4, (-y) ^ m / (m.factorial : ℝ)) +
                  y ^ 4 * ((5 : ℝ) / ((Nat.factorial 4 : ℝ) * 4)) + y := by
                linarith
          _ ≤ 1 + a * y ^ 2 + (1 / 2 : ℝ) * (a * y ^ 2) ^ 2 := hpoly
          _ ≤ Real.exp (a * y ^ 2) := hlower_quad
          _ = Real.exp (9 * y ^ 2 / 16) := by
                congr 1
                dsimp [a]
                ring
      · have hy1' : 1 ≤ y := le_of_not_ge hy1
        have hexp_neg_le_half : Real.exp (-y) ≤ 1 / 2 := by
          have hle : -y ≤ -(1 : ℝ) := by linarith
          have h_exp_le : Real.exp (-y) ≤ Real.exp (-(1 : ℝ)) :=
            Real.exp_le_exp.mpr hle
          have htwo : (2 : ℝ) ≤ Real.exp 1 := by
            linarith [Real.add_one_le_exp (1 : ℝ)]
          have hhalf : Real.exp (-(1 : ℝ)) ≤ 1 / 2 := by
            have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) htwo
            simpa [Real.exp_neg] using h
          exact h_exp_le.trans hhalf
        have hpoly :
            y + 1 / 2 ≤ 1 + a * y ^ 2 := by
          dsimp [a]
          nlinarith [sq_nonneg (3 * y - 8 / 3)]
        calc
          Real.exp (-y) + y ≤ 1 / 2 + y := by linarith
          _ = y + 1 / 2 := by ring
          _ ≤ 1 + a * y ^ 2 := hpoly
          _ ≤ Real.exp (a * y ^ 2) := by
                have hbase :
                    1 + a * y ^ 2 ≤
                      1 + a * y ^ 2 + (1 / 2 : ℝ) * (a * y ^ 2) ^ 2 := by
                  have hs : 0 ≤ (1 / 2 : ℝ) * (a * y ^ 2) ^ 2 := by positivity
                  linarith
                exact hbase.trans hlower_quad
          _ = Real.exp (9 * y ^ 2 / 16) := by
                congr 1
                dsimp [a]
                ring
  by_cases hx0 : 0 ≤ x
  · by_cases hxlarge : (16 : ℝ) / 9 ≤ x
    · have hx_le_quad : x ≤ 9 * x ^ 2 / 16 := by nlinarith
      calc
        Real.exp x ≤ Real.exp (9 * x ^ 2 / 16) :=
          Real.exp_le_exp.mpr hx_le_quad
        _ ≤ x + Real.exp (9 * x ^ 2 / 16) :=
          le_add_of_nonneg_left hx0
    · have hx_upper : x < (16 : ℝ) / 9 := lt_of_not_ge hxlarge
      exact (hbounded x hx0 hx_upper).1
  · let y : ℝ := -x
    have hy0 : 0 ≤ y := by dsimp [y]; linarith
    have hx_eq : x = -y := by dsimp [y]; ring
    by_cases hylarge : (16 : ℝ) / 9 ≤ y
    · have hy_le_quad : y ≤ 9 * y ^ 2 / 16 := by nlinarith
      have htail : y + 1 ≤ Real.exp (9 * y ^ 2 / 16) := by
        have hadd := Real.add_one_le_exp (9 * y ^ 2 / 16)
        nlinarith
      have hexp_neg_le_one : Real.exp (-y) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        linarith
      rw [hx_eq]
      have hsquare : (-y) ^ 2 = y ^ 2 := by ring
      rw [hsquare]
      nlinarith
    · have hy_upper : y < (16 : ℝ) / 9 := lt_of_not_ge hylarge
      have h := (hbounded y hy0 hy_upper).2
      rw [hx_eq]
      have hsquare : (-y) ^ 2 = y ^ 2 := by ring
      rw [hsquare]
      nlinarith

end Real

namespace Seminorm

/-- Every seminorm on a finite-dimensional normed vector space is continuous.

The proof uses finite-dimensional domination of the seminorm by the ambient norm,
then applies the Mathlib continuity criterion for a seminorm bounded above by a
continuous seminorm.

Layer: Glue | Gap: Level 1 (finite-dimensional seminorm continuity)
Proof: use `Seminorm.exists_bound_by_norm_of_finiteDimensional` to dominate the seminorm by a scalar multiple of `normSeminorm`, then apply `Seminorm.continuous_of_le`.
Source: Mathlib seminorm continuity API and SOptLib finite-dimensional seminorm norm control
Used in: stochastic convex-concave saddle-point mirror descent continuity of component primal seminorms before forming product seminorm observables
Book citation: book/FOML/StochasticConvexConcaveSaddlePoint.json#/setup/variable_space
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic mirror descent for stochastic convex-concave saddle point problems -/
theorem continuous_of_finiteDimensional
    {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace 𝕜]
    [FiniteDimensional 𝕜 E]
    (p : Seminorm 𝕜 E) :
    Continuous (fun x : E => p x) := by
  rcases Seminorm.exists_bound_by_norm_of_finiteDimensional p with ⟨K, hKnonneg, hK⟩
  let q : Seminorm 𝕜 E := (Real.toNNReal K) • normSeminorm 𝕜 E
  have hqcont : Continuous (fun x : E => q x) := by
    change Continuous (fun x : E => ((Real.toNNReal K : ℝ) * ‖x‖))
    exact continuous_const.mul continuous_norm
  refine Seminorm.continuous_of_le hqcont ?_
  intro x
  change p x ≤ ((Real.toNNReal K : ℝ) * ‖x‖)
  simpa [Real.toNNReal_of_nonneg hKnonneg] using hK x

end Seminorm
