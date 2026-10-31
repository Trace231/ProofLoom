import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Topology.ContinuousMap.Units
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Convex.Approximation
import SOptLib.Model.Carrier
-- SOptLib/Glue/Analysis.lean
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Operator.Mul
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
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Nat.Periodic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Instances.Matrix
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Range
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import SOptLib.Glue.Algebra
import SOptLib.Glue.Calculus
import SOptLib.Model.Norms.FiniteMatrixQuadraticForm


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


open scoped InnerProductSpace

-- Generalization plan (G0):
-- concept/name: convexity of a fixed-center kernel slice from a three-point
--   identity and nonnegative residual; orig was
--   `localProx_convexOn_second_arg_of_distanceGenerating`.
-- generality used: an arbitrary convex subset of a real inner-product space,
--   a two-point real kernel, a vector selector, and a fixed center; no
--   completeness, finite-dimensionality, measure, smoothness, oracle, or
--   algorithm setup assumptions are used.
-- portable call pattern: mirror-descent, Bregman-prox, mirror-prox, and
--   conditional-sliding proofs establish convexity of a kernel's second slice
--   while varying the carrier, kernel, gradient selector, and fixed center.
-- counterargument checked: this is not paper-local traceability or a pure
--   wrapper because it packages the recurring bridge from a three-point
--   decomposition and residual nonnegativity to the affine lower-support
--   contract required for convexity.
-- coverage search: symbol searches for `three point identity nonnegative
--   residual convex second argument`, `convexOn second argument three point
--   identity`, `first order lower support convexOn`, and `Bregman divergence
--   convex second argument` found
--   `carrierBregmanDivergence_three_point_identity` and
--   `ConvexOn.of_first_order_lower_support`; the former provides only the
--   identity and the latter starts from an already-proved lower support.
--   Mathlib LeanSearch for the full implication was unavailable with HTTP 500.
-- minimal hypotheses: the source's distance-generating structure and
--   quadratic strong-convexity bound are reduced to the pointwise three-point
--   identity and nonnegativity facts actually consumed on the carrier.

/-- A three-point kernel with nonnegative residuals has convex fixed-center
second-argument slices on a convex carrier.

For feasible `x` and `z`, the three-point identity expresses `V center x` as
the affine model of `V center ·` at `z` plus the residual `V z x`.
Nonnegativity of that residual therefore supplies the lower supports needed
for convexity.

Layer: Glue | Gap: Level 1 (three-point kernel identity to slice convexity)
Proof: discard the nonnegative residual in the three-point identity to obtain
  an inner-product lower support, then apply
  `ConvexOn.of_first_order_lower_support`.
Source: Bregman three-point identities and the convex-analysis affine
  lower-support criterion implemented by `ConvexOn.of_first_order_lower_support`
Used in: mirror-descent, Bregman-prox, and stochastic conditional-sliding
  subproblems when proving convexity of the candidate variable in a fixed-center
  proximal kernel term
Book citation: book/research/Source.json#/algorithm_spec/steps/6
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic decentralized communication sliding -/
theorem convexOn_second_of_three_point_identity_and_nonneg
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X : Set E) (V : E → E → ℝ) (grad : E → E) (center : E)
    (hX : Convex ℝ X)
    (hThree : ∀ x ∈ X, ∀ z ∈ X,
      V center x = V center z +
        inner ℝ (grad z - grad center) (x - z) + V z x)
    (hnonneg : ∀ x ∈ X, ∀ z ∈ X, 0 ≤ V z x) :
    ConvexOn ℝ X (fun z => V center z) := by
  refine ConvexOn.of_first_order_lower_support
    (support := fun z => (innerSL ℝ (grad z - grad center)).toLinearMap) hX ?_
  intro x z hx hz
  change V center z + inner ℝ (grad z - grad center) (x - z) ≤ V center x
  rw [hThree x hx z hz]
  linarith [hnonneg x hx z hz]


-- Generalization plan (G0):
-- concept/name: absolute objective-difference bound and carrier continuity from
--   a linearly bounded nonnegative first-order remainder; orig was
--   objective_growth_abs_bound_and_continuity_pattern.
-- generality used: an arbitrary subset of a real inner-product space, a
--   real-valued function, a selected support vector at each point, and a
--   nonnegative scalar remainder modulus; no completeness, finite-dimensional,
--   convexity, smoothness, measure, independence, integrability, or oracle
--   assumptions are used.
-- portable call pattern: nonsmooth mirror-descent, proximal, and constrained
--   subgradient proofs can turn a one-sided first-order growth remainder into a
--   base-point objective modulus and continuity; the carrier, objective,
--   selected support vector, and remainder modulus vary while the conclusion
--   retains the same shape.
-- counterargument checked: this is not paper-local traceability or a pure
--   caller-side rewrite because it composes remainder algebra, inner-product
--   Cauchy--Schwarz, an explicit absolute-difference estimate, and the
--   epsilon--delta continuity argument. Existing bounded-subgradient lemmas
--   require uniform bounds at two points and do not consume this remainder
--   contract or return continuity.
-- coverage search: searched SOptLib and Mathlib for `first order remainder
--   absolute difference bound continuous on carrier`, `absolute objective
--   difference bounded by remainder modulus plus subgradient norm`, and
--   `continuousOn of first order lower upper bound norm`; the closest hits were
--   `SOptLib.abs_sub_le_of_subgradient_norm_bound`,
--   `SOptLib.lipschitzOn_of_forall_subgradient_norm_le`, and the unrelated
--   smooth quadratic `SOptLib.AbsTaylorRemainderBound`. Coverage is partial:
--   none has the asymmetric linear-remainder hypothesis and paired conclusions.
-- minimal hypotheses: the source's positive modulus is weakened to
--   nonnegativity, and its global setup growth field is reduced to the exact
--   pointwise remainder inequalities used on the carrier.

/-- A nonnegative linearly bounded first-order remainder controls objective
differences and makes the objective continuous on its carrier.

At a base point `z`, the absolute difference has modulus
`M + ‖g z‖`. Applying this estimate with a fixed base point gives continuity
within `X`, without a uniform bound on `g`.

Layer: Glue | Gap: Level 1 (first-order remainder bound to carrier continuity)
Proof: decompose the objective difference into its nonnegative remainder and
  linear term, bound the latter by Cauchy--Schwarz, then use the resulting
  base-point linear modulus in the metric epsilon--delta criterion.
Source: Mathlib real absolute-value inequalities, Hilbert-space
  Cauchy--Schwarz, and metric `ContinuousOn` APIs
Used in: nonsmooth mirror-descent and proximal objective regularity when a
  feasible first-order growth condition supplies a linear remainder bound
Book citation: book/research/Source.json#/assumptions/6
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic decentralized communication sliding -/
theorem abs_sub_le_and_continuousOn_of_first_order_remainder_le_norm
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X : Set E) (f : E → ℝ) (g : E → E) (M : ℝ)
    (hM : 0 ≤ M)
    (hremainder : ∀ x ∈ X, ∀ z ∈ X,
      0 ≤ f x - f z - inner ℝ (g z) (x - z) ∧
        f x - f z - inner ℝ (g z) (x - z) ≤ M * ‖x - z‖) :
    (∀ x ∈ X, ∀ z ∈ X,
      |f x - f z| ≤ (M + ‖g z‖) * ‖x - z‖) ∧
      ContinuousOn f X := by
  have hbound : ∀ x ∈ X, ∀ z ∈ X,
      |f x - f z| ≤ (M + ‖g z‖) * ‖x - z‖ := by
    intro x hx z hz
    let R : ℝ := f x - f z - inner ℝ (g z) (x - z)
    have hR_nonneg : 0 ≤ R := by
      simpa [R] using (hremainder x hx z hz).1
    have hR_le : R ≤ M * ‖x - z‖ := by
      simpa [R] using (hremainder x hx z hz).2
    have hdiff_eq : f x - f z = R + inner ℝ (g z) (x - z) := by
      dsimp [R]
      ring
    calc
      |f x - f z| = |R + inner ℝ (g z) (x - z)| := by rw [hdiff_eq]
      _ ≤ |R| + |inner ℝ (g z) (x - z)| := abs_add_le _ _
      _ ≤ M * ‖x - z‖ + ‖g z‖ * ‖x - z‖ :=
        add_le_add (by simpa [abs_of_nonneg hR_nonneg] using hR_le)
          (abs_real_inner_le_norm _ _)
      _ = (M + ‖g z‖) * ‖x - z‖ := by ring
  refine ⟨hbound, ?_⟩
  intro z hz
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  let C : ℝ := M + ‖g z‖
  have hC_nonneg : 0 ≤ C := add_nonneg hM (norm_nonneg _)
  refine ⟨ε / (C + 1), by positivity, ?_⟩
  intro x hx hdist
  have hdist_norm : ‖x - z‖ < ε / (C + 1) := by
    simpa [dist_eq_norm] using hdist
  have hscaled : (C + 1) * ‖x - z‖ < ε := by
    have hpos : 0 < C + 1 := by positivity
    calc
      (C + 1) * ‖x - z‖ < (C + 1) * (ε / (C + 1)) :=
        mul_lt_mul_of_pos_left hdist_norm hpos
      _ = ε := by field_simp [ne_of_gt hpos]
  have hC_lt : C * ‖x - z‖ < ε := by
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)) hscaled
  have habs := hbound x hx z hz
  simpa [C, Real.dist_eq] using lt_of_le_of_lt habs hC_lt

/- Phase 4 Shampoo batch 7: reusable finite-matrix analysis bridges. -/

-- Merged from Staging/Matrix_diagonal_cfc_sqrt_le_cfc_sqrt_diagonal.lean

-- Generalization plan (G0):
-- concept/name: diagonal projection commutes sublinearly with the operator square root;
--   orig was `diagonal_of_psd_half_power_le_half_power_diagonal`
-- generality used: an arbitrary finite decidable index type and a real positive-semidefinite
--   square matrix; no optimization, measure, convexity, or finite-dimensional-space assumptions
-- portable call pattern: diagonal AdaGrad and block-diagonal adaptive methods compare the
--   diagonal of a full PSD preconditioner square root with the square root of its diagonal
--   projection; the index type and accumulated PSD matrix vary while the Loewner bound remains
-- counterargument checked: this is not paper-local bookkeeping or a pure wrapper; it combines
--   CFC square-root uniqueness, matrix diagonal extraction, and Loewner order in an inequality
--   absent from the underlying APIs
-- coverage search: queries "diagonal continuous functional calculus square root Loewner
--   inequality positive semidefinite" and "diagonal projection PSD square root less than square
--   root diagonal projection" found only partial Mathlib support (`CFC.sqrt_le_sqrt`,
--   `CFC.sq_sqrt`, and `Matrix.PosSemidef.posSemidef_sqrt`) and no SOptLib theorem
-- minimal hypotheses: the diagonal PSD premise was removed because it follows pointwise from
--   positive semidefiniteness of the original matrix

open scoped MatrixOrder

/-- For a positive-semidefinite real matrix, the diagonal projection of its operator square root
is Loewner-bounded by the operator square root of its diagonal projection.

Layer: Glue | Gap: Level 2 (diagonal Jensen inequality for the matrix square root)
Proof: identify the square root of the diagonal projection coordinatewise using `CFC.sqrt_eq_iff`;
  each diagonal square-root entry is then bounded by the scalar square root of the corresponding
  diagonal entry by expanding the diagonal entry of the squared operator root.
Source: Mathlib continuous functional calculus square-root API and positive-semidefinite matrix order
Used in: diagonal adaptive preconditioner domination, where full Gram accumulators are projected to
  diagonal accumulators before taking one-half powers
Book citation: book/research/Source.json#/algorithm_spec
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization,
  Algorithm 3 (diagonal matrix case) -/
theorem Matrix.diagonal_cfc_sqrt_le_cfc_sqrt_diagonal
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.PosSemidef) :
    (Matrix.diagonal (fun i : ι => CFC.sqrt A i i) : Matrix ι ι ℝ) ≤
      CFC.sqrt (Matrix.diagonal (fun i : ι => A i i) : Matrix ι ι ℝ) := by
  classical
  let B : Matrix ι ι ℝ := CFC.sqrt A
  have hBpsd : B.PosSemidef := by
    exact Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)
  have hBsq : B * B = A := by
    simpa [B, pow_two] using CFC.sq_sqrt A hA.nonneg
  have hdiag_psd :
      (Matrix.diagonal (fun i : ι => A i i) : Matrix ι ι ℝ).PosSemidef := by
    exact Matrix.PosSemidef.diagonal (fun i => hA.diag_nonneg)
  have hsqrt_diag_psd :
      (Matrix.diagonal (fun i : ι => Real.sqrt (A i i)) : Matrix ι ι ℝ).PosSemidef := by
    exact Matrix.PosSemidef.diagonal (fun i => Real.sqrt_nonneg _)
  have hdiag_sqrt :
      CFC.sqrt (Matrix.diagonal (fun i : ι => A i i) : Matrix ι ι ℝ) =
        Matrix.diagonal (fun i : ι => Real.sqrt (A i i)) := by
    apply (CFC.sqrt_eq_iff _ _ hdiag_psd.nonneg hsqrt_diag_psd.nonneg).2
    rw [Matrix.diagonal_mul_diagonal]
    congr
    funext i
    exact Real.mul_self_sqrt (hA.diag_nonneg)
  rw [hdiag_sqrt, Matrix.le_iff]
  have hdiffdiag :
      (Matrix.diagonal (fun i : ι => Real.sqrt (A i i)) -
          Matrix.diagonal (fun i : ι => CFC.sqrt A i i) : Matrix ι ι ℝ) =
        Matrix.diagonal (fun i : ι => Real.sqrt (A i i) - CFC.sqrt A i i) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  rw [hdiffdiag]
  apply Matrix.PosSemidef.diagonal
  intro i
  have hBii_nonneg : 0 ≤ B i i := hBpsd.diag_nonneg
  have hBsym : ∀ j : ι, B j i = B i j := by
    intro j
    have h := Matrix.IsHermitian.apply hBpsd.1 i j
    simpa using h
  have hA_entry_sum : A i i = ∑ j : ι, B i j ^ 2 := by
    have hentry := congr_fun (congr_fun hBsq i) i
    rw [← hentry]
    simp [Matrix.mul_apply, hBsym, pow_two]
  have hsingle : B i i ^ 2 ≤ ∑ j : ι, B i j ^ 2 := by
    exact Finset.single_le_sum
      (by intro j _hj; exact sq_nonneg (B i j))
      (Finset.mem_univ i)
  have hsq_le : B i i ^ 2 ≤ A i i := by
    simpa [hA_entry_sum] using hsingle
  have hle_sqrt : B i i ≤ Real.sqrt (A i i) := Real.le_sqrt_of_sq_le hsq_le
  change 0 ≤ Real.sqrt (A i i) - B i i
  exact sub_nonneg.mpr hle_sqrt

-- Merged from Staging/Matrix_two_mul_trace_le_trace_mul_mul_inv_add_trace_of_posDef.lean

-- Generalization plan (G0):
-- concept/name: matrix trace Young inequality against a positive-definite metric;
--   orig was `genericTrace_trace_young_posDef`
-- generality used: arbitrary finite decidable index type, a Hermitian real matrix `H`, and a
--   positive-definite real matrix `K`; no optimization, measure, convexity, or oracle assumptions
-- portable call pattern: full-matrix AdaGrad, matrix FTRL, and adaptive mirror descent compare
--   twice the trace of a Hermitian target with its inverse-metric square cost plus the metric
--   trace; the index type, target, and positive-definite metric vary while the inequality remains
-- counterargument checked: this is not paper-local traceability or a caller-side rewrite; it
--   packages the noncommutative square completion, positive-definite operator square root, and
--   cyclic trace argument, and no existing Mathlib/SOptLib declaration states the resulting bound
-- coverage search: symbol and semantic queries for "twice matrix trace upper bound trace square
--   times inverse plus trace positive definite" found only partial APIs (`Matrix.PosDef.trace_pos`,
--   `Matrix.PosSemidef.trace_nonneg`, `CFC.sqrt_mul_sqrt_self`, and cyclicity of matrix trace),
--   while SOptLib contains objective rewrites but no matrix trace Young inequality
-- minimal hypotheses: positivity of `H` was weakened to the Hermitian property actually used;
--   positive definiteness of `K` supplies its invertibility and positive-definite square root

open scoped MatrixOrder

set_option maxHeartbeats 800000 in
/-- For a Hermitian real matrix `H` and a positive-definite real matrix `K`, twice the trace of
`H` is at most the trace of `H * H * K⁻¹` plus the trace of `K`.

Layer: Glue | Gap: Level 2 (matrix trace Young inequality with an inverse metric)
Proof: complete the square with `K`'s positive-definite CFC square root, expand its nonnegative
  Frobenius trace, and use cyclicity of trace together with inverse cancellation.
Source: Mathlib positive-definite matrix order, continuous functional calculus square roots,
  nonsingular matrix inverse, and finite-matrix trace cyclicity
Used in: full-matrix adaptive-gradient and matrix-FTRL potential minimization, where a terminal
  square-root preconditioner is compared with an arbitrary positive-definite competitor
Book citation: book/research/Source.json#/key_lemmas/8/proof/11
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization,
  Theorem 7 matrix regret analysis -/
theorem Matrix.two_mul_trace_le_trace_mul_mul_inv_add_trace_of_posDef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H K : Matrix ι ι ℝ) (hH : H.IsHermitian) (hK : K.PosDef) :
    2 * Matrix.trace H ≤ Matrix.trace (H * H * K⁻¹) + Matrix.trace K := by
  classical
  let R : Matrix ι ι ℝ := CFC.sqrt K
  have hR : R.PosDef := by
    simpa [R] using Matrix.isStrictlyPositive_iff_posDef.mp hK.isStrictlyPositive.sqrt
  have hRsqr : R * R = K := by
    simpa [R] using CFC.sqrt_mul_sqrt_self K
  let A : Matrix ι ι ℝ := R⁻¹ * H - R
  have hA_nonneg : 0 ≤ Matrix.trace (A.transpose * A) := by
    unfold Matrix.trace
    change 0 ≤ ∑ i : ι, ∑ j : ι, A j i * A j i
    exact Finset.sum_nonneg (by
      intro i _hi
      exact Finset.sum_nonneg (by
        intro j _hj
        exact mul_self_nonneg (A j i)))
  have hR_sym : R.transpose = R := by
    have hstar : star R = R := hR.1.eq
    ext i j
    have hij := congrFun (congrFun hstar j) i
    simpa [Matrix.star_apply] using hij.symm
  have hH_sym : H.transpose = H := by
    have hstar : star H = H := hH.eq
    ext i j
    have hij := congrFun (congrFun hstar j) i
    simpa [Matrix.star_apply] using hij.symm
  have hRinv_sym : (R⁻¹).transpose = R⁻¹ := by
    ext i j
    have h := (hR.isHermitian.inv).apply j i
    simpa [Matrix.star_apply] using h.symm
  have hRdet_ne : R.det ≠ 0 := ne_of_gt hR.det_pos
  letI : Invertible R.det := invertibleOfNonzero hRdet_ne
  letI : Invertible R := Matrix.invertibleOfDetInvertible R
  have hR_left : R⁻¹ * R = (1 : Matrix ι ι ℝ) := Matrix.inv_mul_of_invertible R
  have hR_right : R * R⁻¹ = (1 : Matrix ι ι ℝ) := Matrix.mul_inv_of_invertible R
  have hKdet_ne : K.det ≠ 0 := ne_of_gt hK.det_pos
  letI : Invertible K.det := invertibleOfNonzero hKdet_ne
  letI : Invertible K := Matrix.invertibleOfDetInvertible K
  have hK_right : K * K⁻¹ = (1 : Matrix ι ι ℝ) := Matrix.mul_inv_of_invertible K
  have hRinv_sq : R⁻¹ * R⁻¹ = K⁻¹ := by
    have hcancel : (R⁻¹ * R⁻¹) * (R * R) = (1 : Matrix ι ι ℝ) := by
      calc
        (R⁻¹ * R⁻¹) * (R * R) = R⁻¹ * (R⁻¹ * R) * R := by simp [mul_assoc]
        _ = 1 := by rw [hR_left]; simp [hR_left]
    calc
      R⁻¹ * R⁻¹ = (R⁻¹ * R⁻¹) * 1 := by simp
      _ = (R⁻¹ * R⁻¹) * (K * K⁻¹) := by rw [hK_right]
      _ = ((R⁻¹ * R⁻¹) * K) * K⁻¹ := by simp [mul_assoc]
      _ = ((R⁻¹ * R⁻¹) * (R * R)) * K⁻¹ := by rw [hRsqr]
      _ = K⁻¹ := by rw [hcancel]; simp
  have htrace_expand :
      Matrix.trace (A.transpose * A) =
        Matrix.trace (H * H * K⁻¹) + Matrix.trace K - 2 * Matrix.trace H := by
    calc
      Matrix.trace (A.transpose * A) =
          Matrix.trace ((H * R⁻¹ - R) * (R⁻¹ * H - R)) := by
            simp [A, Matrix.transpose_sub, Matrix.transpose_mul, hR_sym, hH_sym, hRinv_sym]
      _ = Matrix.trace (H * R⁻¹ * (R⁻¹ * H) - H * R⁻¹ * R -
              R * (R⁻¹ * H) + R * R) := by
            congr 1
            noncomm_ring
      _ = Matrix.trace (H * R⁻¹ * (R⁻¹ * H)) -
              Matrix.trace (H * R⁻¹ * R) -
              Matrix.trace (R * (R⁻¹ * H)) + Matrix.trace (R * R) := by
            simp [Matrix.trace_sub, Matrix.trace_add]
      _ = Matrix.trace (H * H * K⁻¹) - Matrix.trace H -
              Matrix.trace H + Matrix.trace K := by
            have hmain :
                Matrix.trace (H * R⁻¹ * (R⁻¹ * H)) =
                  Matrix.trace (H * H * K⁻¹) := by
              calc
                Matrix.trace (H * R⁻¹ * (R⁻¹ * H)) =
                    Matrix.trace (H * H * (R⁻¹ * R⁻¹)) := by
                      simpa [mul_assoc] using Matrix.trace_mul_cycle (H * R⁻¹) R⁻¹ H
                _ = Matrix.trace (H * H * K⁻¹) := by rw [hRinv_sq]
            have hcross1 : Matrix.trace (H * R⁻¹ * R) = Matrix.trace H := by
              rw [show H * R⁻¹ * R = H by
                calc
                  H * R⁻¹ * R = H * (R⁻¹ * R) := by noncomm_ring
                  _ = H := by rw [hR_left]; simp]
            have hcross2 : Matrix.trace (R * (R⁻¹ * H)) = Matrix.trace H := by
              rw [show R * (R⁻¹ * H) = H by
                calc
                  R * (R⁻¹ * H) = (R * R⁻¹) * H := by noncomm_ring
                  _ = H := by rw [hR_right]; simp]
            have hKtrace : Matrix.trace (R * R) = Matrix.trace K := by rw [hRsqr]
            rw [hmain, hcross1, hcross2, hKtrace]
      _ = Matrix.trace (H * H * K⁻¹) + Matrix.trace K - 2 * Matrix.trace H := by ring
  have hgap_nonneg :
      0 ≤ Matrix.trace (H * H * K⁻¹) + Matrix.trace K - 2 * Matrix.trace H := by
    rw [← htrace_expand]
    exact hA_nonneg
  linarith

-- Merged from Staging/Matrix_trace_cfc_sqrt_add_smul_one_eq_sum_sqrt_eigenvalues_add.lean

open scoped BigOperators

namespace Matrix

-- Generalization plan (G0):
-- concept/name: trace of the CFC square root after scalar spectral regularization; orig was
--   `generic_hhat_delta_trace_spectral`, renamed
--   `Matrix.trace_cfc_sqrt_add_smul_one_eq_sum_sqrt_eigenvalues_add`
-- generality used: arbitrary finite decidable coordinate type, RCLike coefficient field,
--   Hermitian matrix, and arbitrary real scalar identity shift; no horizon, gradient stream,
--   prefix sum, or algorithm state
-- portable call pattern: full-matrix AdaGrad, Shampoo, covariance-adaptive mirror descent, and
--   matrix FTRL vary the PSD accumulator and regularization scalar while using the same terminal
--   trace-of-square-root spectral evaluation
-- counterargument checked: not paper-local bookkeeping or a pure rename; Mathlib exposes the
--   Hermitian CFC spectral representation and trace cyclicity separately, but no declaration
--   combines scalar identity regularization with the resulting shifted-eigenvalue trace formula
-- coverage search: queries "trace continuous functional calculus square root positive
--   semidefinite matrix sum eigenvalues scalar identity shift", "trace cfc rpow equals sum
--   eigenvalues rpow", and Mathlib semantic search for the full formula found
--   `Matrix.IsHermitian.cfc_eq`, `Matrix.IsHermitian.trace_eq_sum_eigenvalues`, and
--   `Matrix.PosSemidef.sqrt`; these are component results and do not cover the shifted formula
-- minimal hypotheses: `Fintype` and `DecidableEq` support finite Hermitian spectral theory;
--   Hermitianity is exactly the spectral contract used by the proof, while no sign condition on
--   the shift is needed because real square root and half-power agree on all reals

/-- The trace of the continuous-functional-calculus square root of a
scalar-shifted Hermitian matrix is the sum of the square roots of its shifted eigenvalues.

Layer: Glue | Gap: Level 1 (trace formula for a scalar-regularized Hermitian matrix square root)
Proof: express the scalar shift as the CFC of an affine function, compose it with the continuous real square root, then evaluate the resulting CFC in the original Hermitian eigenbasis and use cyclicity of trace.
Source: Mathlib finite Hermitian matrix spectral functional calculus, real square-root continuity, and finite-matrix trace cyclicity
Used in: full-matrix adaptive-gradient and matrix-FTRL limit arguments that evaluate a terminal regularized square-root preconditioner trace before removing the scalar regularizer
Book citation: book/research/Source.json#/key_lemmas/8/proof/14
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 1 matrix regret proof -/
theorem trace_cfc_sqrt_add_smul_one_eq_sum_sqrt_eigenvalues_add
    {ι 𝕜 : Type*} [Fintype ι] [DecidableEq ι] [RCLike 𝕜]
    (A : Matrix ι ι 𝕜) (delta : ℝ) (hA : A.IsHermitian) :
    trace
        (cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ (1 / 2 : ℝ))
          (A + delta • (1 : Matrix ι ι 𝕜))) =
      ((∑ i : ι, (hA.eigenvalues i + delta) ^ (1 / 2 : ℝ) : ℝ) : 𝕜) := by
  classical
  simp_rw [← Real.sqrt_eq_rpow]
  have hshift :
      cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x + delta) A =
        A + delta • (1 : Matrix ι ι 𝕜) := by
    calc
      cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x + delta) A =
          cfc (R := ℝ) (p := IsSelfAdjoint) id A +
            algebraMap ℝ (Matrix ι ι 𝕜) delta := by
              simpa [id] using
                (cfc_add_const delta id A (ha := hA.isSelfAdjoint))
      _ = A + delta • (1 : Matrix ι ι 𝕜) := by
            rw [cfc_id ℝ A (ha := hA.isSelfAdjoint),
              Algebra.algebraMap_eq_smul_one]
  have hcomp :
      cfc (R := ℝ) (p := IsSelfAdjoint) Real.sqrt
          (A + delta • (1 : Matrix ι ι 𝕜)) =
        cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => Real.sqrt (x + delta)) A := by
    rw [← hshift]
    symm
    simpa [Function.comp_def] using
      (cfc_comp Real.sqrt (fun x : ℝ => x + delta) A (ha := hA.isSelfAdjoint)
        (hg := Real.continuous_sqrt.continuousOn)
        (hf := (continuous_id.add continuous_const).continuousOn))
  rw [hcomp, hA.cfc_eq]
  unfold Matrix.IsHermitian.cfc
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle]
  simp [Matrix.trace_diagonal, Function.comp_def]

end Matrix

-- Merged from Staging/Matrix_tendsto_trace_cfc_sqrt_add_smul_one_nhdsWithin_zero.lean

open Topology
open scoped BigOperators

namespace Matrix

-- Generalization plan (G0):
-- concept/name: positive-side convergence of the trace of a scalar-regularized CFC square
--   root; orig was `generic_hhat_delta_trace_tendsto`, renamed
--   `Matrix.tendsto_trace_cfc_sqrt_add_smul_one_nhdsWithin_zero`
-- generality used: arbitrary finite decidable coordinate type, RCLike coefficient field, and
--   Hermitian matrix; positivity, a gradient stream, a prefix sum, and an algorithm horizon are
--   unnecessary once the square root is expressed by continuous functional calculus
-- portable call pattern: full-matrix AdaGrad, Shampoo, covariance-adaptive mirror descent, and
--   matrix FTRL vary the finite Hermitian accumulator while using the same positive-side removal
--   of scalar identity regularization from its square-root trace
-- counterargument checked: not paper-local traceability or a caller-side expression; the proof
--   composes a matrix spectral trace identity with a finite family of scalar limit arguments,
--   and neither Mathlib nor SOptLib packages that reusable matrix convergence step
-- coverage search: queries "trace square root matrix plus positive scalar identity tends to trace
--   square root at zero positive side" and "trace of matrix square root A plus delta identity tends
--   to trace square root A" found `Continuous.matrix_trace`, `Filter.Tendsto.sqrt`, and
--   `Matrix.PosSemidef.sqrt`; the project search additionally found the component identity
--   `Matrix.trace_cfc_sqrt_add_smul_one_eq_sum_sqrt_eigenvalues_add`, but no convergence theorem
-- minimal hypotheses: finite decidable coordinates support Hermitian spectral theory and
--   Hermitianity is the exact matrix hypothesis consumed; positive semidefiniteness is not used

/-- The trace of the CFC square root of a scalar-regularized Hermitian matrix converges from
positive regularizers to the trace of the unregularized CFC square root.

Layer: Glue | Gap: Level 1 (positive-side continuity of a scalar-regularized matrix square-root trace)
Proof: rewrite each regularized trace as a finite sum over shifted Hermitian eigenvalues, prove termwise convergence with `Filter.Tendsto.rpow_const`, and identify the limiting sum with the unregularized spectral trace formula.
Source: Mathlib finite Hermitian matrix continuous functional calculus, finite-sum filter convergence, and continuity of real powers
Used in: full-matrix adaptive-gradient, matrix-FTRL, and Shampoo limit arguments that remove a vanishing scalar identity regularizer from a possibly singular accumulator
Book citation: book/research/Source.json#/key_lemmas/8/proof/14
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 1 matrix regret proof -/
theorem tendsto_trace_cfc_sqrt_add_smul_one_nhdsWithin_zero
    {ι 𝕜 : Type*} [Fintype ι] [DecidableEq ι] [RCLike 𝕜]
    (A : Matrix ι ι 𝕜) (hA : A.IsHermitian) :
    Filter.Tendsto
      (fun delta : ℝ =>
        if 0 < delta then
          trace
            (cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ (1 / 2 : ℝ))
              (A + delta • (1 : Matrix ι ι 𝕜)))
        else
          0)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds
        (trace
          (cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ (1 / 2 : ℝ)) A))) := by
  classical
  have hsum :
      Filter.Tendsto
        (fun delta : ℝ =>
          ((∑ i : ι, (hA.eigenvalues i + delta) ^ (1 / 2 : ℝ) : ℝ) : 𝕜))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds ((∑ i : ι, (hA.eigenvalues i) ^ (1 / 2 : ℝ) : ℝ) : 𝕜)) := by
    apply (RCLike.continuous_ofReal.tendsto _).comp
    simpa using
      (tendsto_finset_sum (s := (Finset.univ : Finset ι))
        (f := fun i delta => (hA.eigenvalues i + delta) ^ (1 / 2 : ℝ))
        (a := fun i => (hA.eigenvalues i) ^ (1 / 2 : ℝ))
        (x := nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (fun i _ => by
          have hlin :
              Filter.Tendsto (fun delta : ℝ => hA.eigenvalues i + delta)
                (nhdsWithin (0 : ℝ) (Set.Ioi 0))
                (nhds (hA.eigenvalues i + 0)) := by
            exact tendsto_const_nhds.add
              (tendsto_nhdsWithin_of_tendsto_nhds (f := id) Filter.tendsto_id)
          have hrpow :=
            hlin.rpow_const (p := (1 / 2 : ℝ)) (Or.inr (by norm_num))
          simpa using hrpow))
  have htrace_zero :
      trace
          (cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ (1 / 2 : ℝ)) A) =
        ((∑ i : ι, (hA.eigenvalues i) ^ (1 / 2 : ℝ) : ℝ) : 𝕜) := by
    simpa only [zero_smul, add_zero] using
      trace_cfc_sqrt_add_smul_one_eq_sum_sqrt_eigenvalues_add A 0 hA
  rw [htrace_zero]
  apply hsum.congr'
  filter_upwards
    [show Set.Ioi (0 : ℝ) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) by
      exact self_mem_nhdsWithin]
    with delta hdelta
  change 0 < delta at hdelta
  rw [if_pos hdelta]
  exact (trace_cfc_sqrt_add_smul_one_eq_sum_sqrt_eigenvalues_add A delta hA).symm

end Matrix

-- Merged from Staging/Filter_sum_le_mul_of_tendsto_of_eventually.lean

open Topology
open scoped BigOperators

-- Generalization plan (G0):
-- concept/name: passage of an eventual upper bound through a finite sum of
--   pointwise limits and a scaled terminal limit; orig was
--   `generic_hhat_support_bound_of_regularized_limits`
-- generality used: an arbitrary explicitly selected finite index set, source
--   type and nontrivial source filter, with real-valued summands and terminal
--   function; no matrix, measure, optimization, normed-space, or
--   finite-dimensional assumptions are used
-- portable call pattern: regularization and approximation proofs vary the
--   finite family of scalar functions, their pointwise limits, the terminal
--   comparison function, its limit, and the scalar multiplier while retaining
--   the same limiting finite-sum inequality
-- counterargument checked: although the proof composes standard convergence
--   lemmas, it is not a pure rename or paper-local wrapper; it packages the
--   recurring transition from componentwise convergence plus an eventual
--   aggregate bound to the endpoint inequality
-- coverage search: queried `finite sum upper bound from pointwise limits and
--   eventual inequality`, `le_of_tendsto_of_tendsto eventual inequality`, and
--   `tendsto finite sum pointwise limits` with `lean_search_symbols`, and
--   queried the finite-sum eventual-inequality contract with Mathlib LeanSearch;
--   the hits were the component declarations `tendsto_finset_sum`,
--   `Filter.Tendsto.const_mul`, and `le_of_tendsto_of_tendsto`, but no Mathlib
--   or SOptLib declaration with the combined statement
-- minimal hypotheses: the explicit `Finset` selects exactly the convergent
--   summands, `Filter.NeBot` is required to turn eventual comparison into a
--   limiting order comparison, and every convergence and eventual-bound
--   hypothesis is used

/-- Pointwise limits of a finite family satisfy a scaled terminal bound when
their finite sums satisfy that bound eventually and the terminal function
converges.

Layer: Glue | Gap: Level 1 (finite-sum eventual inequality passage to limits)
Proof: use `tendsto_finset_sum` to combine the pointwise summand limits, use `Filter.Tendsto.const_mul` for the scaled terminal limit, and pass the eventual inequality to the limits with `le_of_tendsto_of_tendsto`.
Source: Mathlib finite-sum convergence, continuous real multiplication, and closed-order topology APIs
Used in: regularized adaptive-preconditioner and approximation arguments that pass an eventual finite-sum energy bound to singular or unregularized endpoint limits
Book citation: book/research/Source.json#/key_lemmas/8/proof/15
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 1 matrix regret proof -/
theorem Filter.sum_le_mul_of_tendsto_of_eventually
    {ι X : Type*} (s : Finset ι) (l : Filter X) [l.NeBot]
    (f : ι → X → ℝ) (g : X → ℝ)
    (a : ι → ℝ) (b c : ℝ)
    (hf : ∀ i ∈ s, Filter.Tendsto (f i) l (nhds (a i)))
    (hg : Filter.Tendsto g l (nhds c))
    (hfg : (fun x ↦ ∑ i ∈ s, f i x) ≤ᶠ[l] (fun x ↦ b * g x)) :
    (∑ i ∈ s, a i) ≤ b * c := by
  exact le_of_tendsto_of_tendsto
    (tendsto_finset_sum s hf)
    (hg.const_mul b)
    hfg

-- Merged from Staging/Matrix_dualQuadraticForm_le_mul_of_cfc_sqrt_le_of_regularized_tendsto.lean

open scoped BigOperators MatrixOrder

namespace Matrix

-- Generalization plan (G0):
-- concept/name: transfer of CFC square-root Loewner domination to a dual
--   quadratic-form bound whose comparison value is specified by a positive
--   regularization limit; orig was
--   `generic_algorithm_dual_pointwise_le_hhat_support`
-- generality used: an arbitrary finite decidable real coordinate type, a PSD
--   reference matrix, a PD metric, one vector dominated by the reference
--   matrix, a nonnegative domination factor, and a chosen regularized limit;
--   no horizon, prefix sum, accumulator, algorithm state, measure, convexity,
--   smoothness, stochastic, or oracle assumptions are used
-- portable call pattern: full-matrix AdaGrad, Shampoo, covariance-adaptive
--   mirror descent, and online Newton proofs change the reference covariance,
--   current metric, vector, domination factor, and selected regularized limit
--   while retaining the same pointwise inverse-metric energy conclusion
-- counterargument checked: this is not a pure rename of the existing spectral
--   support bound; it adds the reusable limit-identification step that lets a
--   caller use any previously chosen regularized limit without exposing
--   eigenvectors or spectral coefficients
-- coverage search: symbol queries for `dual quadratic form upper bound
--   regularized limit CFC square root Loewner domination positive definite`
--   and `tendsto inverse square root dual quadratic form support matrix`, plus
--   Mathlib semantic search for PSD inverse-square-root regularization, found
--   the component theorems
--   `Matrix.dualQuadraticForm_cfc_sqrt_add_smul_one_spectral_support`,
--   `tendsto_sum_sq_mul_add_rpow_neg_half_of_support`, and
--   `Matrix.dualQuadraticForm_le_mul_spectralSupport_of_cfc_sqrt_le`, but no
--   theorem composing a chosen regularized limit with the Loewner bound
-- minimal hypotheses: finite decidable coordinates support matrix spectral
--   theory and total inversion; PSD and rank-one domination provide spectral
--   support, PD supplies the target inverse metric, nonnegative scaling is
--   required by the order bound, and the Tendsto hypothesis alone specifies
--   the chosen comparison value

/-- A CFC square-root Loewner bound controls the dual quadratic form by any
value obtained as the positive-regularization limit of the reference
inverse-square-root dual quadratic form.

Layer: Glue | Gap: Level 2 (regularized spectral-limit to dual-energy order bound)
Proof: obtain the shifted spectral formula and zero-eigenspace support, use the support-aware inverse-square-root finite-sum limit to identify the chosen limit uniquely, then apply the spectral-support Loewner bound.
Source: Mathlib finite Hermitian matrix spectral functional calculus, filter-limit uniqueness, positive-definite inversion, and Loewner order, together with SOptLib regularized spectral-support and dual quadratic-form bounds
Used in: Shampoo, full-matrix AdaGrad, covariance-adaptive mirror descent, and online Newton analyses that replace a singular reference inverse square root by a chosen positive-regularization limit before transferring metric domination
Book citation: book/research/Source.json#/key_lemmas/8/proof/15
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 1 matrix regret proof -/
private theorem batch7_spectral_coeff_eq_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → ℝ) (A : Matrix ι ι ℝ) (hA : A.PosSemidef)
    (hOuter : Matrix.vecMulVec g g ≤ A) (i : ι)
    (hi : hA.1.eigenvalues i = 0) :
    (∑ j : ι, g j * (hA.1.eigenvectorUnitary : Matrix ι ι ℝ) j i) = 0 := by
  classical
  let v : ι → ℝ := ⇑(hA.1.eigenvectorBasis i)
  have hAv : A.mulVec v = 0 := by
    simpa [v, hi] using hA.1.mulVec_eigenvectorBasis i
  have hA_zero : Matrix.toBilin' A v v = 0 := by
    rw [Matrix.toBilin'_apply']
    simp [hAv]
  have hOuter_le :
      Matrix.toBilin' (Matrix.vecMulVec g g) v v ≤ Matrix.toBilin' A v v :=
    Matrix.toBilin_self_mono_of_le v hOuter
  have hsq_le : (∑ j : ι, g j * v j) ^ 2 ≤ 0 := by
    rw [← hA_zero]
    simpa [Matrix.toBilin'_apply', Matrix.mulVec, Matrix.vecMulVec_apply,
      dotProduct, pow_two, Finset.mul_sum, Finset.sum_mul, mul_assoc,
      mul_left_comm, mul_comm] using hOuter_le
  have hcoeff : (∑ j : ι, g j * v j) = 0 := by
    nlinarith [sq_nonneg (∑ j : ι, g j * v j)]
  simpa [v] using hcoeff


private theorem batch7_tendsto_sum_sq_mul_add_rpow_neg_half_of_support
    {ι : Type*} [Fintype ι]
    (lam coeff : ι → ℝ)
    (hlam_nonneg : ∀ i : ι, 0 ≤ lam i)
    (hcoeff_zero : ∀ i : ι, lam i = 0 → coeff i = 0) :
    Filter.Tendsto
      (fun delta : ℝ ↦
        ∑ i : ι, coeff i ^ 2 * (lam i + delta) ^ (-(1 / 2 : ℝ)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (∑ i : ι, coeff i ^ 2 * (lam i) ^ (-(1 / 2 : ℝ)))) := by
  classical
  refine
    tendsto_finset_sum (s := (Finset.univ : Finset ι))
      (f := fun i delta ↦ coeff i ^ 2 * (lam i + delta) ^ (-(1 / 2 : ℝ)))
      (a := fun i ↦ coeff i ^ 2 * (lam i) ^ (-(1 / 2 : ℝ)))
      (x := nhdsWithin (0 : ℝ) (Set.Ioi 0)) ?_
  intro i _hi
  by_cases hzero : lam i = 0
  · have hcoeff : coeff i = 0 := hcoeff_zero i hzero
    simp [hcoeff]
  · have hpos : 0 < lam i := lt_of_le_of_ne (hlam_nonneg i) (Ne.symm hzero)
    have hlin :
        Filter.Tendsto (fun delta : ℝ ↦ lam i + delta)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (lam i + 0)) := by
      exact tendsto_const_nhds.add
        (tendsto_nhdsWithin_of_tendsto_nhds (f := id) Filter.tendsto_id)
    have hrpow :
        Filter.Tendsto
          (fun delta : ℝ ↦ (lam i + delta) ^ (-(1 / 2 : ℝ)))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhds ((lam i + 0) ^ (-(1 / 2 : ℝ)))) := by
      exact hlin.rpow_const (p := (-(1 / 2 : ℝ))) (Or.inl (by positivity))
    have hmul := (tendsto_const_nhds (x := coeff i ^ 2)).mul hrpow
    simpa using hmul

private theorem batch7_dualQuadraticForm_le_mul_spectralSupport
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) (hA : A.PosSemidef) (hB : B.PosDef)
    (alpha : ℝ) (halpha_nonneg : 0 ≤ alpha) (g coeff : ι → ℝ)
    (hroot_le :
      cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ (1 / 2 : ℝ)) A ≤
        alpha • B)
    (hcoeff_def : ∀ i : ι,
      coeff i = ∑ j : ι, g j * (hA.1.eigenvectorUnitary : Matrix ι ι ℝ) j i)
    (hcoeff_zero : ∀ i : ι, hA.1.eigenvalues i = 0 → coeff i = 0) :
    SOptLib.finiteMatrixDualQuadraticForm B (WithLp.toLp 2 g) ≤
      alpha * ∑ i : ι,
        coeff i ^ 2 * (hA.1.eigenvalues i) ^ (-(1 / 2 : ℝ)) := by
  classical
  let U : unitary (Matrix ι ι ℝ) := hA.1.eigenvectorUnitary
  let lam : ι → ℝ := hA.1.eigenvalues
  let y : ι → ℝ := B⁻¹.mulVec g
  let ycoeff : ι → ℝ := fun i =>
    ∑ j : ι, y j * (U : Matrix ι ι ℝ) j i
  let supportValue : ℝ :=
    ∑ i : ι, coeff i ^ 2 * (lam i) ^ (-(1 / 2 : ℝ))
  let rootEnergy : ℝ :=
    ∑ i : ι, ycoeff i ^ 2 * (lam i) ^ (1 / 2 : ℝ)
  let dualValue : ℝ :=
    SOptLib.finiteMatrixDualQuadraticForm B (WithLp.toLp 2 g)
  have hdual_dot : dualValue = ∑ i : ι, g i * y i := by
    simp [dualValue, y, Matrix.mulVec,
      dotProduct, Finset.mul_sum, mul_assoc]
  have hcoeff_def_lam : ∀ i : ι,
      coeff i = ∑ j : ι, g j * (U : Matrix ι ι ℝ) j i := by
    intro i
    simpa [U] using hcoeff_def i
  have hdual_spectral :
      dualValue = ∑ i : ι, coeff i * ycoeff i := by
    calc
      dualValue = ∑ i : ι, g i * y i := hdual_dot
      _ = ∑ i : ι,
          (∑ j : ι, g j * (U : Matrix ι ι ℝ) j i) *
            (∑ j : ι, y j * (U : Matrix ι ι ℝ) j i) := by
          simpa only [mul_comm] using
            (finite_orthonormal_coordinate_bilinear_collapse
              (fun i k => (U : Matrix ι ι ℝ) i k) g y (fun i j => by
                have hunit := congrArg (fun M : Matrix ι ι ℝ => M i j)
                  (Unitary.coe_mul_star_self U)
                simpa [Matrix.mul_apply, Matrix.one_apply] using hunit)).symm
      _ = ∑ i : ι, coeff i * ycoeff i := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          simp [ycoeff, hcoeff_def_lam i]
  have hroot_spec :
      cfc (R := ℝ) (p := IsSelfAdjoint)
          (fun x : ℝ => x ^ (1 / 2 : ℝ)) A =
        (U : Matrix ι ι ℝ) *
          Matrix.diagonal (fun i : ι => (lam i) ^ (1 / 2 : ℝ)) *
            star (U : Matrix ι ι ℝ) := by
    rw [hA.1.cfc_eq]
    rfl
  have hroot_energy_eq :
      Matrix.toBilin'
          (cfc (R := ℝ) (p := IsSelfAdjoint)
            (fun x : ℝ => x ^ (1 / 2 : ℝ)) A) y y = rootEnergy := by
    rw [hroot_spec]
    simpa [rootEnergy, ycoeff, U, lam] using
      (Matrix.toBilin_mul_diagonal_mul_transpose_self_eq_sum_sq_mul
        y (fun i : ι => (lam i) ^ (1 / 2 : ℝ)) (U : Matrix ι ι ℝ))
  have hdet_ne : B.det ≠ 0 := ne_of_gt hB.det_pos
  letI : Invertible B.det := invertibleOfNonzero hdet_ne
  letI : Invertible B := Matrix.invertibleOfDetInvertible B
  have hcancel : B.mulVec y = g := by
    dsimp [y]
    rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible]
    simp
  have hdual_quad : Matrix.toBilin' B y y = dualValue := by
    rw [Matrix.toBilin'_apply]
    calc
      (∑ i, ∑ j, y i * B i j * y j) =
          ∑ i, y i * (B.mulVec y) i := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
      _ = ∑ i, y i * g i := by simp [hcancel]
      _ = ∑ i, g i * y i := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            ring
      _ = dualValue := hdual_dot.symm
  have hroot_bound : rootEnergy ≤ alpha * dualValue := by
    calc
      rootEnergy = Matrix.toBilin'
          (cfc (R := ℝ) (p := IsSelfAdjoint)
            (fun x : ℝ => x ^ (1 / 2 : ℝ)) A) y y := hroot_energy_eq.symm
      _ ≤ Matrix.toBilin' (alpha • B) y y :=
        Matrix.toBilin_self_mono_of_le y hroot_le
      _ = alpha * dualValue := by simp [hdual_quad]
  have hcs : dualValue ^ 2 ≤ supportValue * rootEnergy := by
    have hcs0 :=
      Finset.sum_mul_sq_le_inverse_sqrt_weight_mul_sqrt_weight lam coeff ycoeff
        (fun i => by simpa [lam] using hA.eigenvalues_nonneg i)
        (fun i hi => hcoeff_zero i (by simpa [lam] using hi))
    rw [hdual_spectral]
    simpa [supportValue, rootEnergy, lam] using hcs0
  have hsupport_nonneg : 0 ≤ supportValue := by
    refine Finset.sum_nonneg ?_
    intro i _hi
    exact mul_nonneg (sq_nonneg (coeff i))
      (Real.rpow_nonneg (by simpa [lam] using hA.eigenvalues_nonneg i) _)
  have hdual_nonneg : 0 ≤ dualValue := by
    rw [← hdual_quad, Matrix.toBilin'_apply']
    simpa only [star_trivial] using hB.posSemidef.dotProduct_mulVec_nonneg y
  have hsq_le : dualValue ^ 2 ≤ (alpha * supportValue) * dualValue := by
    calc
      dualValue ^ 2 ≤ supportValue * rootEnergy := hcs
      _ ≤ supportValue * (alpha * dualValue) :=
        mul_le_mul_of_nonneg_left hroot_bound hsupport_nonneg
      _ = (alpha * supportValue) * dualValue := by ring
  have hcoefficient_nonneg : 0 ≤ alpha * supportValue :=
    mul_nonneg halpha_nonneg hsupport_nonneg
  have hle : dualValue ≤ alpha * supportValue := by
    by_cases hdual_zero : dualValue = 0
    · simpa [hdual_zero] using hcoefficient_nonneg
    · have hdual_pos : 0 < dualValue := lt_of_le_of_ne hdual_nonneg (Ne.symm hdual_zero)
      apply le_of_mul_le_mul_right _ hdual_pos
      simpa [pow_two, mul_assoc] using hsq_le
  simpa [dualValue, supportValue, lam, mul_comm, mul_left_comm, mul_assoc] using hle


private theorem batch7_dualQuadraticForm_cfc_sqrt_spectral_support
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (g : ι → ℝ) (hA : A.PosSemidef)
    (hOuter : Matrix.vecMulVec g g ≤ A) :
    ∃ coeff : ι → ℝ,
      (∀ {delta : ℝ}, 0 < delta →
        SOptLib.finiteMatrixDualQuadraticForm
            (cfc (R := ℝ) (p := IsSelfAdjoint)
              (fun x : ℝ => x ^ (1 / 2 : ℝ))
              (A + delta • (1 : Matrix ι ι ℝ)))
            (WithLp.toLp 2 g) =
          ∑ i : ι, coeff i ^ 2 *
            ((hA.1.eigenvalues i + delta) ^ (-(1 / 2 : ℝ)))) ∧
      (∀ i : ι, hA.1.eigenvalues i = 0 → coeff i = 0) ∧
      (∀ i : ι, coeff i =
        ∑ j : ι, g j * (hA.1.eigenvectorUnitary : Matrix ι ι ℝ) j i) := by
  classical
  let U : unitary (Matrix ι ι ℝ) := hA.1.eigenvectorUnitary
  let lam : ι → ℝ := hA.1.eigenvalues
  let coeff : ι → ℝ := fun i =>
    ∑ j : ι, g j * (U : Matrix ι ι ℝ) j i
  have hcfc_diagonal : ∀ (d : ι → ℝ) (s : ℝ),
      (∀ i, 0 ≤ d i) →
      cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ s)
          (Matrix.diagonal d : Matrix ι ι ℝ) =
        Matrix.diagonal (fun i : ι => (d i) ^ s) := by
    intro d s hd
    let D : Matrix ι ι ℝ := Matrix.diagonal d
    let q : Polynomial ℝ :=
      Lagrange.interpolate (Finset.univ : Finset {x : ℝ // x ∈ Set.range d})
        (fun x : {x : ℝ // x ∈ Set.range d} => (x : ℝ))
        (fun x : {x : ℝ // x ∈ Set.range d} => (x : ℝ) ^ s)
    have hDpsd : D.PosSemidef := by
      simpa [D] using Matrix.PosSemidef.diagonal (d := d) hd
    have hinj : Set.InjOn
        (fun x : {x : ℝ // x ∈ Set.range d} => (x : ℝ))
        ((Finset.univ : Finset {x : ℝ // x ∈ Set.range d}) :
          Set {x : ℝ // x ∈ Set.range d}) := by
      intro x _ y _ hxy
      exact Subtype.ext hxy
    have hq_eval : ∀ i : ι, q.eval (d i) = (d i) ^ s := by
      intro i
      have hnode := Lagrange.eval_interpolate_at_node
        (s := (Finset.univ : Finset {x : ℝ // x ∈ Set.range d}))
        (v := fun x : {x : ℝ // x ∈ Set.range d} => (x : ℝ))
        (r := fun x : {x : ℝ // x ∈ Set.range d} => (x : ℝ) ^ s)
        hinj (Finset.mem_univ (⟨d i, ⟨i, rfl⟩⟩ : {x : ℝ // x ∈ Set.range d}))
      simpa [q] using hnode
    have hspec : spectrum ℝ D = Set.range d := by
      simp [D, spectrum_diagonal (R := ℝ) (n := ι) (d := d)]
    have hfg : (spectrum ℝ D).EqOn (fun x : ℝ => x ^ s) q.eval := by
      rw [hspec]
      intro x hx
      rcases hx with ⟨i, rfl⟩
      exact (hq_eval i).symm
    calc
      cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ s)
          (Matrix.diagonal d : Matrix ι ι ℝ) =
          cfc (R := ℝ) (p := IsSelfAdjoint) q.eval D := by
            simpa [D] using
              (cfc_congr (R := ℝ) (A := Matrix ι ι ℝ)
                (p := IsSelfAdjoint) (a := D) hfg)
      _ = Polynomial.aeval D q := by
            simpa using
              (cfc_polynomial (R := ℝ) (A := Matrix ι ι ℝ)
                (p := IsSelfAdjoint) q D (ha := hDpsd.1))
      _ = Matrix.diagonal (fun i : ι => (d i) ^ s) := by
            calc
              Polynomial.aeval D q =
                  (Matrix.diagonalAlgHom ℝ : (ι → ℝ) →ₐ[ℝ] Matrix ι ι ℝ)
                    (Polynomial.aeval d q) := by
                    simpa [D] using
                      (Polynomial.aeval_algHom_apply
                        (f := (Matrix.diagonalAlgHom ℝ :
                          (ι → ℝ) →ₐ[ℝ] Matrix ι ι ℝ))
                        (x := d) (p := q))
              _ = Matrix.diagonal (fun i : ι => (d i) ^ s) := by
                    ext i j
                    by_cases hij : i = j
                    · subst j
                      simp [Polynomial.aeval_pi_apply, hq_eval]
                    · simp [hij]
  have hcfc_unitary : ∀ (f : ℝ → ℝ) (V : unitary (Matrix ι ι ℝ))
      (D : Matrix ι ι ℝ), IsSelfAdjoint D →
      cfc (R := ℝ) (p := IsSelfAdjoint) f
          (((V : Matrix ι ι ℝ) * D) * star (V : Matrix ι ι ℝ)) =
        ((V : Matrix ι ι ℝ) *
          cfc (R := ℝ) (p := IsSelfAdjoint) f D) *
            star (V : Matrix ι ι ℝ) := by
    intro f V D hD
    let φ := Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) V
    have hcontφ : Continuous (φ : Matrix ι ι ℝ → Matrix ι ι ℝ) := by
      simpa [φ, Unitary.conjStarAlgAut_apply] using
        (show Continuous (fun X : Matrix ι ι ℝ =>
          (V : Matrix ι ι ℝ) * X * star (V : Matrix ι ι ℝ)) from by fun_prop)
    have hfD : ContinuousOn f (spectrum ℝ D) := by
      have hfin : (spectrum ℝ D).Finite := by
        rw [(show Matrix.IsHermitian D from hD).spectrum_real_eq_range_eigenvalues]
        exact Set.finite_range _
      exact hfin.continuousOn _
    have hφD : IsSelfAdjoint (φ D) := by
      change IsSelfAdjoint
        (((V : Matrix ι ι ℝ) * D) * star (V : Matrix ι ι ℝ))
      exact (Matrix.isHermitian_mul_mul_conjTranspose
        (V : Matrix ι ι ℝ) (show Matrix.IsHermitian D from hD)).isSelfAdjoint
    have hmap := (φ : Matrix ι ι ℝ →⋆ₐ[ℝ] Matrix ι ι ℝ).map_cfc
      f D (hf := hfD) (hφ := hcontφ) (ha := hD) (hφa := hφD)
    simpa [φ, Unitary.conjStarAlgAut_apply] using hmap.symm
  refine ⟨coeff, ?_, ?_, ?_⟩
  · intro delta hdelta
    let Aδ : Matrix ι ι ℝ := A + delta • (1 : Matrix ι ι ℝ)
    let Droot : Matrix ι ι ℝ :=
      Matrix.diagonal (fun i : ι => (lam i + delta) ^ (1 / 2 : ℝ))
    let Dneg : Matrix ι ι ℝ :=
      Matrix.diagonal (fun i : ι => (lam i + delta) ^ (-(1 / 2 : ℝ)))
    have hAδpd : Aδ.PosDef := by
      dsimp [Aδ]
      simpa [add_comm] using
        (((Matrix.PosDef.one : (1 : Matrix ι ι ℝ).PosDef).smul hdelta).add_posSemidef hA)
    have hdiagA :
        A = (U : Matrix ι ι ℝ) * Matrix.diagonal lam *
          star (U : Matrix ι ι ℝ) := by
      simpa [U, lam, Unitary.conjStarAlgAut_apply, Function.comp_def] using
        hA.1.spectral_theorem
    have hdiag_delta :
        Aδ = (U : Matrix ι ι ℝ) *
          Matrix.diagonal (fun i : ι => lam i + delta) *
            star (U : Matrix ι ι ℝ) := by
      let I : Matrix ι ι ℝ := 1
      let D : Matrix ι ι ℝ := Matrix.diagonal lam
      let Dδ : Matrix ι ι ℝ := Matrix.diagonal (fun i : ι => lam i + delta)
      have hDδ : Dδ = D + delta • I := by
        ext i j
        by_cases hij : i = j
        · subst j
          simp [Dδ, D, I]
        · simp [Dδ, D, I, hij]
      have hconj_I :
          (U : Matrix ι ι ℝ) * I * star (U : Matrix ι ι ℝ) = I := by
        simp [I]
      calc
        Aδ = A + delta • I := by rfl
        _ = (U : Matrix ι ι ℝ) * D * star (U : Matrix ι ι ℝ) +
              delta • I := by rw [hdiagA]
        _ = (U : Matrix ι ι ℝ) * D * star (U : Matrix ι ι ℝ) +
              delta • ((U : Matrix ι ι ℝ) * I *
                star (U : Matrix ι ι ℝ)) := by rw [hconj_I]
        _ = (U : Matrix ι ι ℝ) * (D + delta • I) *
              star (U : Matrix ι ι ℝ) := by
              simp [Matrix.mul_assoc, mul_add, add_mul]
        _ = (U : Matrix ι ι ℝ) * Dδ * star (U : Matrix ι ι ℝ) := by
              rw [hDδ]
    have hshift_nonneg : ∀ i : ι, 0 ≤ lam i + delta := by
      intro i
      exact add_nonneg (by simpa [lam] using hA.eigenvalues_nonneg i)
        (le_of_lt hdelta)
    have hroot :
        cfc (R := ℝ) (p := IsSelfAdjoint)
            (fun x : ℝ => x ^ (1 / 2 : ℝ)) Aδ =
          (U : Matrix ι ι ℝ) * Droot * star (U : Matrix ι ι ℝ) := by
      rw [hdiag_delta]
      calc
        cfc (R := ℝ) (p := IsSelfAdjoint)
            (fun x : ℝ => x ^ (1 / 2 : ℝ))
            (((U : Matrix ι ι ℝ) *
              Matrix.diagonal (fun i : ι => lam i + delta)) *
                star (U : Matrix ι ι ℝ)) =
            ((U : Matrix ι ι ℝ) *
              cfc (R := ℝ) (p := IsSelfAdjoint)
                (fun x : ℝ => x ^ (1 / 2 : ℝ))
                (Matrix.diagonal (fun i : ι => lam i + delta) :
                  Matrix ι ι ℝ)) * star (U : Matrix ι ι ℝ) := by
              exact hcfc_unitary _ U _
                (Matrix.PosSemidef.diagonal hshift_nonneg).1
        _ = (U : Matrix ι ι ℝ) * Droot * star (U : Matrix ι ι ℝ) := by
              rw [hcfc_diagonal (fun i : ι => lam i + delta)
                (1 / 2 : ℝ) hshift_nonneg]
    have hDroot_pd : Droot.PosDef := by
      dsimp [Droot]
      apply Matrix.PosDef.diagonal
      intro i
      exact Real.rpow_pos_of_pos
        (add_pos_of_nonneg_of_pos
          (by simpa [lam] using hA.eigenvalues_nonneg i) hdelta) _
    have hroot_pd :
        (cfc (R := ℝ) (p := IsSelfAdjoint)
          (fun x : ℝ => x ^ (1 / 2 : ℝ)) Aδ).PosDef := by
      rw [hroot]
      have hUunit : IsUnit (U : Matrix ι ι ℝ) := (Unitary.toUnits U).isUnit
      exact (Matrix.IsUnit.posDef_star_right_conjugate_iff hUunit).mpr hDroot_pd
    have hDmul : Dneg * Droot = 1 := by
      ext i j
      by_cases hij : i = j
      · subst j
        have hpos : 0 < lam i + delta :=
          add_pos_of_nonneg_of_pos
            (by simpa [lam] using hA.eigenvalues_nonneg i) hdelta
        have hpow :
            (lam i + delta) ^ (-(1 / 2 : ℝ)) *
                (lam i + delta) ^ (1 / 2 : ℝ) = 1 := by
          calc
            (lam i + delta) ^ (-(1 / 2 : ℝ)) *
                (lam i + delta) ^ (1 / 2 : ℝ) =
                (lam i + delta) ^
                  (-(1 / 2 : ℝ) + (1 / 2 : ℝ)) := by
                    rw [Real.rpow_add hpos]
            _ = 1 := by norm_num [Real.rpow_zero]
        simpa [Dneg, Droot, Matrix.diagonal_mul_diagonal] using hpow
      · simp [Dneg, Droot, hij]
    have hinv :
        (cfc (R := ℝ) (p := IsSelfAdjoint)
          (fun x : ℝ => x ^ (1 / 2 : ℝ)) Aδ)⁻¹ =
            (U : Matrix ι ι ℝ) * Dneg * star (U : Matrix ι ι ℝ) := by
      let Root : Matrix ι ι ℝ :=
        cfc (R := ℝ) (p := IsSelfAdjoint)
          (fun x : ℝ => x ^ (1 / 2 : ℝ)) Aδ
      let Neg : Matrix ι ι ℝ :=
        (U : Matrix ι ι ℝ) * Dneg * star (U : Matrix ι ι ℝ)
      have hmul : Neg * Root = 1 := by
        rw [show Root = (U : Matrix ι ι ℝ) * Droot *
          star (U : Matrix ι ι ℝ) by simpa [Root] using hroot]
        dsimp [Neg]
        calc
          ((U : Matrix ι ι ℝ) * Dneg * star (U : Matrix ι ι ℝ)) *
              ((U : Matrix ι ι ℝ) * Droot * star (U : Matrix ι ι ℝ)) =
              (U : Matrix ι ι ℝ) *
                (Dneg * (star (U : Matrix ι ι ℝ) *
                  (U : Matrix ι ι ℝ)) * Droot) *
                    star (U : Matrix ι ι ℝ) := by noncomm_ring
          _ = (U : Matrix ι ι ℝ) * 1 * star (U : Matrix ι ι ℝ) := by
                simp [hDmul]
          _ = 1 := by simp
      have hdet_ne : Root.det ≠ 0 := by
        exact ne_of_gt (by simpa [Root] using hroot_pd.det_pos)
      letI : Invertible Root.det := invertibleOfNonzero hdet_ne
      letI : Invertible Root := Matrix.invertibleOfDetInvertible Root
      have hNeg : Neg = Root⁻¹ := by
        calc
          Neg = Neg * 1 := by simp
          _ = Neg * (Root * Root⁻¹) := by rw [Matrix.mul_inv_of_invertible]
          _ = (Neg * Root) * Root⁻¹ := by noncomm_ring
          _ = Root⁻¹ := by rw [hmul]; simp
      simpa [Root, Neg] using hNeg.symm
    rw [SOptLib.finiteMatrixDualQuadraticForm_eq_finiteMatrixQuadraticForm]
    unfold SOptLib.finiteMatrixQuadraticForm SOptLib.finiteMatrixVec
    rw [show
      (cfc (R := ℝ) (p := IsSelfAdjoint)
        (fun x : ℝ => x ^ (1 / 2 : ℝ))
        (A + delta • (1 : Matrix ι ι ℝ)))⁻¹ =
          (U : Matrix ι ι ℝ) * Dneg * star (U : Matrix ι ι ℝ) by
      simpa [Aδ] using hinv]
    simp_rw [Finset.mul_sum]
    simpa [coeff, Dneg, lam, Matrix.toBilin'_apply, Matrix.star_apply,
      mul_assoc] using
      (Matrix.toBilin_mul_diagonal_mul_transpose_self_eq_sum_sq_mul
        g (fun i : ι => (lam i + delta) ^ (-(1 / 2 : ℝ)))
        (U : Matrix ι ι ℝ))
  · intro i hi
    simpa [coeff, U] using
      batch7_spectral_coeff_eq_zero
        g A hA hOuter i hi
  · intro i
    rfl

theorem dualQuadraticForm_le_mul_of_cfc_sqrt_le_of_regularized_tendsto
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) (g : ι → ℝ) (alpha support : ℝ)
    (hA : A.PosSemidef) (hB : B.PosDef)
    (hOuter : Matrix.vecMulVec g g ≤ A) (halpha_nonneg : 0 ≤ alpha)
    (hroot_le :
      cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ (1 / 2 : ℝ)) A ≤
        alpha • B)
    (hSupportLimit :
      Filter.Tendsto
        (fun delta : ℝ =>
          if 0 < delta then
            SOptLib.finiteMatrixDualQuadraticForm
              (cfc (R := ℝ) (p := IsSelfAdjoint)
                (fun x : ℝ => x ^ (1 / 2 : ℝ))
                (A + delta • (1 : Matrix ι ι ℝ)))
              (WithLp.toLp 2 g)
          else
            0)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds support)) :
    SOptLib.finiteMatrixDualQuadraticForm B (WithLp.toLp 2 g) ≤
      alpha * support := by
  classical
  obtain ⟨coeff, hcoeff_spec, hcoeff_zero, hcoeff_def⟩ :=
    batch7_dualQuadraticForm_cfc_sqrt_spectral_support A g hA hOuter
  let supportValue : ℝ :=
    ∑ i : ι,
      coeff i ^ 2 * (hA.1.eigenvalues i) ^ (-(1 / 2 : ℝ))
  let lam : ι → ℝ := fun i => hA.1.eigenvalues i
  have hSpectralLimit :
      Filter.Tendsto
        (fun delta : ℝ =>
          if 0 < delta then
            SOptLib.finiteMatrixDualQuadraticForm
              (cfc (R := ℝ) (p := IsSelfAdjoint)
                (fun x : ℝ => x ^ (1 / 2 : ℝ))
                (A + delta • (1 : Matrix ι ι ℝ)))
              (WithLp.toLp 2 g)
          else
            0)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds supportValue) := by
    have hlim :
        Filter.Tendsto
          (fun delta : ℝ =>
            ∑ i : ι, coeff i ^ 2 * (lam i + delta) ^ (-(1 / 2 : ℝ)))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhds
            (∑ i : ι,
              coeff i ^ 2 * (lam i) ^ (-(1 / 2 : ℝ)))) := by
      exact
        batch7_tendsto_sum_sq_mul_add_rpow_neg_half_of_support lam coeff
          (fun i => by simpa [lam] using hA.eigenvalues_nonneg i)
          (fun i hi => hcoeff_zero i (by simpa [lam] using hi))
    have heventual :
        (fun delta : ℝ =>
          if 0 < delta then
            SOptLib.finiteMatrixDualQuadraticForm
              (cfc (R := ℝ) (p := IsSelfAdjoint)
                (fun x : ℝ => x ^ (1 / 2 : ℝ))
                (A + delta • (1 : Matrix ι ι ℝ)))
              (WithLp.toLp 2 g)
          else
            0) =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
          (fun delta : ℝ =>
            ∑ i : ι, coeff i ^ 2 * (lam i + delta) ^ (-(1 / 2 : ℝ))) := by
      filter_upwards
        [show Set.Ioi (0 : ℝ) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) by
          exact self_mem_nhdsWithin]
        with delta hdelta
      have hdelta_pos : 0 < delta := hdelta
      rw [if_pos hdelta_pos]
      simpa [lam] using hcoeff_spec hdelta_pos
    change Filter.Tendsto _ _
      (nhds (∑ i : ι, coeff i ^ 2 * (lam i) ^ (-(1 / 2 : ℝ))))
    exact hlim.congr' heventual.symm
  have hSupportEq : support = supportValue :=
    tendsto_nhds_unique hSupportLimit hSpectralLimit
  have hbound :=
    batch7_dualQuadraticForm_le_mul_spectralSupport
      A B hA hB alpha halpha_nonneg g coeff hroot_le hcoeff_def hcoeff_zero
  simpa [supportValue, hSupportEq] using hbound

end Matrix


namespace Matrix

/-- Public support formula for regularized inverse-square-root dual quadratic forms.
This exposes the already-verified spectral helper used by singular prefix-Gram limits. -/
theorem dualQuadraticForm_cfc_sqrt_add_smul_one_spectral_support
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (g : ι → ℝ) (hA : A.PosSemidef)
    (hOuter : Matrix.vecMulVec g g ≤ A) :
    ∃ coeff : ι → ℝ,
      (∀ {delta : ℝ}, 0 < delta →
        SOptLib.finiteMatrixDualQuadraticForm
            (cfc (R := ℝ) (p := IsSelfAdjoint)
              (fun x : ℝ => x ^ (1 / 2 : ℝ))
              (A + delta • (1 : Matrix ι ι ℝ)))
            (WithLp.toLp 2 g) =
          ∑ i : ι, coeff i ^ 2 *
            ((hA.1.eigenvalues i + delta) ^ (-(1 / 2 : ℝ)))) ∧
      (∀ i : ι, hA.1.eigenvalues i = 0 → coeff i = 0) ∧
      (∀ i : ι, coeff i =
        ∑ j : ι, g j * (hA.1.eigenvectorUnitary : Matrix ι ι ℝ) j i) :=
  batch7_dualQuadraticForm_cfc_sqrt_spectral_support A g hA hOuter

end Matrix

private theorem Matrix.analysis_cfc_rpowIntegrand₀₁_eq_resolvent
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : Matrix ι ι ℝ) (p s : ℝ) (hX : X.PosSemidef) (hs : 0 < s) :
    cfc (R := ℝ) (p := IsSelfAdjoint) (Real.rpowIntegrand₀₁ p s) X =
      (s ^ p) • ((s⁻¹) • (1 : Matrix ι ι ℝ) -
        (s • (1 : Matrix ι ι ℝ) + X)⁻¹) := by
  have hnonzero : ∀ x ∈ spectrum ℝ X, s + x ≠ 0 := by
    intro x hx
    have hx_nonneg : 0 ≤ x := by
      rw [hX.1.spectrum_real_eq_range_eigenvalues] at hx
      obtain ⟨i, rfl⟩ := hx
      exact hX.eigenvalues_nonneg i
    exact ne_of_gt (add_pos_of_pos_of_nonneg hs hx_nonneg)
  change cfc (R := ℝ) (p := IsSelfAdjoint)
      (fun x : ℝ => (s ^ p) * (s⁻¹ - (s + x)⁻¹)) X = _
  have hcont_add :
      ContinuousOn (fun x : ℝ => s + x) (spectrum ℝ X) :=
    continuousOn_const.add continuousOn_id
  have hcont_inv :
      ContinuousOn (fun x : ℝ => (s + x)⁻¹) (spectrum ℝ X) :=
    hcont_add.inv₀ hnonzero
  have hcont_diff :
      ContinuousOn (fun x : ℝ => s⁻¹ - (s + x)⁻¹) (spectrum ℝ X) :=
    continuousOn_const.sub hcont_inv
  have hconst :
      cfc (R := ℝ) (p := IsSelfAdjoint) (fun _ : ℝ => s⁻¹) X =
        (s⁻¹) • (1 : Matrix ι ι ℝ) := by
    rw [cfc_const (R := ℝ) (p := IsSelfAdjoint) s⁻¹ X hX.1]
    simp [Algebra.smul_def]
  have hadd :
      cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => s + x) X =
        s • (1 : Matrix ι ι ℝ) + X := by
    rw [cfc_const_add (R := ℝ) (p := IsSelfAdjoint) s (fun x : ℝ => x) X
      continuousOn_id hX.1]
    rw [cfc_id' (p := IsSelfAdjoint) ℝ X hX.1]
    simp [Algebra.smul_def]
  have hinv :
      cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => (s + x)⁻¹) X =
        (s • (1 : Matrix ι ι ℝ) + X)⁻¹ := by
    rw [cfc_inv (p := IsSelfAdjoint) (f := fun x : ℝ => s + x) (a := X)
      hnonzero hcont_add hX.1]
    rw [hadd]
    exact (Matrix.nonsing_inv_eq_ringInverse
      (A := s • (1 : Matrix ι ι ℝ) + X)).symm
  calc
    cfc (R := ℝ) (p := IsSelfAdjoint)
        (fun x : ℝ => (s ^ p) * (s⁻¹ - (s + x)⁻¹)) X =
        (s ^ p) • cfc (R := ℝ) (p := IsSelfAdjoint)
          (fun x : ℝ => s⁻¹ - (s + x)⁻¹) X :=
      cfc_const_mul (R := ℝ) (p := IsSelfAdjoint) (s ^ p)
        (fun x : ℝ => s⁻¹ - (s + x)⁻¹) X hcont_diff
    _ = (s ^ p) •
        (cfc (R := ℝ) (p := IsSelfAdjoint) (fun _ : ℝ => s⁻¹) X -
          cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => (s + x)⁻¹) X) := by
      rw [cfc_sub (R := ℝ) (p := IsSelfAdjoint)
        (fun _ : ℝ => s⁻¹) (fun x : ℝ => (s + x)⁻¹) X
        continuousOn_const hcont_inv]
    _ = (s ^ p) • ((s⁻¹) • (1 : Matrix ι ι ℝ) -
        (s • (1 : Matrix ι ι ℝ) + X)⁻¹) := by rw [hconst, hinv]

open scoped ComplexOrder

namespace Matrix

universe u

private theorem analysis_starAlgHom_mono_of_le
    {R A B : Type*} [CommRing R]
    [Ring A] [PartialOrder A] [StarRing A] [StarOrderedRing A]
    [Ring B] [PartialOrder B] [StarRing B] [StarOrderedRing B]
    [Algebra R A] [Algebra R B]
    (f : A →⋆ₐ[R] B) {a b : A} (hab : a ≤ b) : f a ≤ f b := by
  exact OrderHomClass.mono f hab

private theorem analysis_realMatrixComplexification_nonneg_iff
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) :
    0 ≤ SOptLib.realMatrixComplexification A ↔ 0 ≤ A := by
  let scalarCast : ℝ →⋆ₐ[ℝ] ℂ :=
    { toFun := fun r => (r : ℂ)
      map_one' := Complex.ofReal_one
      map_mul' := Complex.ofReal_mul
      map_zero' := Complex.ofReal_zero
      map_add' := Complex.ofReal_add
      commutes' := fun _ => rfl
      map_star' := fun r => by simp }
  let matrixCast : Matrix ι ι ℝ →⋆ₐ[ℝ] Matrix ι ι ℂ :=
    StarAlgHom.mk (AlgHom.mapMatrix scalarCast.toAlgHom)
      (by
        intro M
        change Matrix.map (star M) scalarCast = star (Matrix.map M scalarCast)
        ext i j
        simp [scalarCast, Matrix.star_eq_conjTranspose])
  let e : Matrix ι ι ℂ ≃⋆ₐ[ℝ] CStarMatrix ι ι ℂ :=
    (CStarMatrix.ofMatrixStarAlgEquiv (n := ι) (A := ℂ)).restrictScalars ℝ
  let castA : Matrix ι ι ℂ := Matrix.map A scalarCast
  have hcomplexify : SOptLib.realMatrixComplexification A = e castA := by rfl
  rw [hcomplexify]
  change e 0 ≤ e castA ↔ 0 ≤ A
  rw [map_le_map_iff e]
  constructor
  · intro hcast
    have hcast_psd : castA.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hcast
    rw [Matrix.nonneg_iff_posSemidef]
    constructor
    · apply Matrix.IsHermitian.ext
      intro i j
      apply Complex.ofReal_injective
      simpa [castA, scalarCast] using hcast_psd.1.apply i j
    · intro v
      let vc : ι →₀ ℂ :=
        v.mapRange (fun r : ℝ => (r : ℂ)) Complex.ofReal_zero
      have hv := hcast_psd.2 vc
      have heq :
          vc.sum (fun i vi => vc.sum fun j vj => star vi * castA i j * vj) =
            ((v.sum fun i vi => v.sum fun j vj => star vi * A i j * vj : ℝ) : ℂ) := by
        dsimp [vc]
        rw [Finsupp.sum_mapRange_index (by intro; simp)]
        simp only [Finsupp.sum,
          Finsupp.support_mapRange_of_injective Complex.ofReal_zero v
            Complex.ofReal_injective,
          castA, scalarCast, Matrix.map_apply, StarAlgHom.coe_mk]
        push_cast
        simp [Finsupp.mapRange_apply]
      rw [heq] at hv
      exact (Complex.nonneg_iff.mp hv).1
  · intro hA
    exact map_nonneg matrixCast.toNonUnitalStarAlgHom hA

private theorem analysis_nonsing_inv_antitone_of_posDef
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) (hA : A.PosDef) (hAB : A ≤ B) :
    B⁻¹ ≤ A⁻¹ := by
  have hB : B.PosDef := by
    convert hA.add_posSemidef (Matrix.le_iff.mp hAB) using 1
    abel
  let φ := SOptLib.realMatrixComplexification (ι := ι)
  let a : (Matrix ι ι ℝ)ˣ := hA.isUnit.unit
  let b : (Matrix ι ι ℝ)ˣ := hB.isUnit.unit
  let φa : (CStarMatrix ι ι ℂ)ˣ := Units.map φ.toMonoidHom a
  let φb : (CStarMatrix ι ι ℂ)ˣ := Units.map φ.toMonoidHom b
  have hcomplex_order : (φa : CStarMatrix ι ι ℂ) ≤ φb := by
    simpa [φa, φb, φ, a, b, IsUnit.unit_spec] using
      analysis_starAlgHom_mono_of_le φ hAB
  have hcomplex_A_nonneg : 0 ≤ (φa : CStarMatrix ι ι ℂ) := by
    simpa [φa, φ, a, IsUnit.unit_spec] using
      (analysis_realMatrixComplexification_nonneg_iff A).2 hA.posSemidef.nonneg
  have hcomplex_inv :
      (↑φb⁻¹ : CStarMatrix ι ι ℂ) ≤ (↑φa⁻¹ : CStarMatrix ι ι ℂ) :=
    CStarAlgebra.inv_le_inv hcomplex_A_nonneg hcomplex_order
  have himage_inv : φ B⁻¹ ≤ φ A⁻¹ := by
    simpa [φa, φb, φ, a, b, IsUnit.unit_spec, Matrix.coe_units_inv] using hcomplex_inv
  rw [Matrix.le_iff]
  apply Matrix.nonneg_iff_posSemidef.mp
  apply (analysis_realMatrixComplexification_nonneg_iff (A⁻¹ - B⁻¹)).mp
  rw [map_sub]
  exact sub_nonneg.mpr himage_inv

end Matrix

-- Merged from Staging/mul_add_rpow_neg_half_le_two_mul_sub_rpow_half_of_nonneg.lean

-- Generalization plan (G0):
-- concept/name: inverse-square-root charge bound by a square-root potential increment; orig was scalar_sq_rpow_neg_half_le_sqrt_increment.
-- generality used: two real scalars and their pointwise nonnegativity; no measure, filtration, optimization, oracle, norm, inner-product, convexity, smoothness, or finite-dimensional assumptions are used.
-- portable call pattern: AdaGrad, diagonal preconditioner, and self-normalized-sum proofs instantiate `a` with the previous nonnegative mass and `b` with the next nonnegative increment; both values vary while the inverse-square-root charge and square-root potential-increment conclusion stays fixed.
-- counterargument checked: this is not paper-local traceability or a pure rename; it packages the nontrivial endpoint-safe inequality, including the zero updated-mass case, that turns an inverse-square-root charge into a telescoping square-root increment.
-- coverage search: queried `nonnegative increment inverse square root upper bound square root difference` and the precise displayed inequality with `lean_search_symbols`, plus the natural-language contract with Mathlib LeanSearch; Mathlib returned only lower-level real-power and square-root lemmas, and SOptLib had logarithmic and cube-root accumulator bounds but no theorem covering this square-root increment contract.
-- minimal hypotheses: both scalar nonnegativity hypotheses are used; they allow a zero previous mass and a zero updated mass, so no positivity strengthening is needed.

/-- A nonnegative increment charged at the inverse square root of its updated
mass is at most twice the corresponding square-root potential increment.

Layer: Glue | Gap: Level 1 (inverse-square-root charge to square-root potential increment)
Proof: split off the zero updated-mass endpoint, rewrite the negative half power as the reciprocal square root, and clear the positive square-root denominator; the result follows from the square of the difference of the two square roots.
Source: Mathlib real square-root order and square identities together with `Real.rpow_neg` and `Real.sqrt_eq_rpow` from `Analysis.SpecialFunctions.Pow.Real`
Used in: coordinatewise AdaGrad, diagonal Shampoo, and self-normalized accumulator telescopes that sum squared-gradient increments divided by the current accumulator square root
Book citation: book/research/Source.json#/key_lemmas/16/proof/12
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 3 diagonal matrix case -/
theorem mul_add_rpow_neg_half_le_two_mul_sub_rpow_half_of_nonneg
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    b * (a + b) ^ (-(1 / 2 : ℝ)) ≤
      2 * ((a + b) ^ (1 / 2 : ℝ) - a ^ (1 / 2 : ℝ)) := by
  have hab_nonneg : 0 ≤ a + b := add_nonneg ha hb
  by_cases hab_zero : a + b = 0
  · have hb_zero : b = 0 := by linarith
    simp [hb_zero]
  · have hab_pos : 0 < a + b := lt_of_le_of_ne hab_nonneg (Ne.symm hab_zero)
    have hsqrt_pos : 0 < Real.sqrt (a + b) := Real.sqrt_pos.2 hab_pos
    have hsqrt_mono : Real.sqrt a ≤ Real.sqrt (a + b) :=
      Real.sqrt_le_sqrt (by linarith)
    have hsqrt_ab_sq : Real.sqrt (a + b) ^ 2 = a + b :=
      Real.sq_sqrt hab_nonneg
    have hsqrt_a_sq : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
    have hrpow_neg :
        (a + b) ^ (-(1 / 2 : ℝ)) = (Real.sqrt (a + b))⁻¹ := by
      rw [Real.rpow_neg hab_nonneg]
      rw [← Real.sqrt_eq_rpow]
    rw [hrpow_neg, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
    rw [← div_eq_mul_inv]
    apply (div_le_iff₀ hsqrt_pos).2
    nlinarith [sq_nonneg (Real.sqrt (a + b) - Real.sqrt a)]

-- Merged from Staging/sum_sq_mul_prefix_add_rpow_neg_half_le_two_mul_terminal_rpow_half.lean

open scoped BigOperators

-- Generalization plan (G0):
-- concept/name: inclusive-prefix inverse-square-root sum bounded by its terminal square-root potential; orig was scalar_diagonal_square_root_telescope.
-- generality used: a finite real sequence and a nonnegative real initial mass; no measure, filtration, optimization, oracle, norm, inner-product, convexity, smoothness, or finite-dimensional assumptions are used.
-- portable call pattern: coordinatewise AdaGrad, diagonal Shampoo, and singular diagonal-metric proofs vary the finite scalar sequence and nonnegative initial mass while retaining the same inclusive-prefix inverse-square-root charge and terminal square-root bound.
-- counterargument checked: this is not paper-local traceability or a caller-side expression; it composes a nontrivial endpoint-safe scalar estimate with finite prefix bookkeeping and telescoping, a recurring self-normalized-sum proof step.
-- coverage search: `prefix squared increments inverse square root inclusive prefix sum terminal square root nonnegative initial mass`, `sum square prefix rpow negative half terminal rpow half`, and Mathlib LeanSearch for the full contract found only Cauchy--Schwarz primitives, SOptLib logarithmic prefix bounds, `sum_fin_adjacent_sub_eq_sub`, and the already-staged one-step inequality; none covers this finite inclusive-prefix conclusion.
-- minimal hypotheses: `0 ≤ a` is the only explicit hypothesis; each increment is a square, so its nonnegativity is automatic, and zero initial or updated mass remains allowed.

/-- The sum of squared increments weighted by the inverse square root of their
inclusive prefix masses is at most twice the terminal square-root mass.

Layer: Glue | Gap: Level 1 (inclusive-prefix inverse-square-root finite telescope)
Proof: apply the endpoint-safe one-step inverse-square-root charge bound to each squared increment, sum it, telescope the adjacent square-root potential differences, and discard the nonnegative initial potential.
Source: Mathlib finite big operators and real powers, together with SOptLib's `sum_fin_adjacent_sub_eq_sub` and the scalar square-root increment inequality
Used in: coordinatewise AdaGrad and diagonal Shampoo bounds that sum squared-gradient charges against singular inclusive-prefix inverse-square-root metrics
Book citation: book/research/Source.json#/key_lemmas/16/proof/12
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 3 diagonal matrix case -/
theorem sum_sq_mul_prefix_add_rpow_neg_half_le_two_mul_terminal_rpow_half
    {T : Nat} (g : Fin T → ℝ) (a : ℝ) (ha : 0 ≤ a) :
    (∑ t : Fin T,
      g t ^ 2 *
        (a + ∑ s : Fin T, if s.1 < t.1 + 1 then g s ^ 2 else 0) ^
          (-(1 / 2 : ℝ))) ≤
      2 *
        (a + ∑ s : Fin T, if s.1 < T then g s ^ 2 else 0) ^
          (1 / 2 : ℝ) := by
  classical
  let p : ℕ → ℝ := fun k =>
    a + ∑ s : Fin T, if s.1 < k then g s ^ 2 else 0
  have hp_nonneg : ∀ k : ℕ, 0 ≤ p k := by
    intro k
    exact add_nonneg ha (Finset.sum_nonneg (fun s _ => by
      split_ifs
      · exact sq_nonneg (g s)
      · exact le_rfl))
  have hp_succ : ∀ t : Fin T, p (t.1 + 1) = p t.1 + g t ^ 2 := by
    intro t
    let current : Fin T := ⟨t.1, t.2⟩
    have hfilter :
        (Finset.univ.filter (fun s : Fin T => s.1 < t.1 + 1)) =
          insert current (Finset.univ.filter (fun s : Fin T => s.1 < t.1)) := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · intro hs
        have hle : s.1 ≤ t.1 := Nat.lt_succ_iff.mp hs
        rcases Nat.lt_or_eq_of_le hle with hlt | heq
        · exact Or.inr hlt
        · left
          ext
          exact heq
      · intro hs
        rcases hs with hs | hs
        · rw [hs]
          exact Nat.lt_succ_self t.1
        · exact Nat.lt_trans hs (Nat.lt_succ_self t.1)
    have hsum :
        (∑ s : Fin T, if s.1 < t.1 + 1 then g s ^ 2 else 0) =
          (∑ s : Fin T, if s.1 < t.1 then g s ^ 2 else 0) + g t ^ 2 := by
      calc
        (∑ s : Fin T, if s.1 < t.1 + 1 then g s ^ 2 else 0) =
            Finset.sum (Finset.univ.filter (fun s : Fin T => s.1 < t.1 + 1))
              (fun s => g s ^ 2) := by
                simp [Finset.sum_filter]
        _ = Finset.sum
              (insert current (Finset.univ.filter (fun s : Fin T => s.1 < t.1)))
              (fun s => g s ^ 2) := by rw [hfilter]
        _ = g current ^ 2 +
              Finset.sum (Finset.univ.filter (fun s : Fin T => s.1 < t.1))
                (fun s => g s ^ 2) := by
                  rw [Finset.sum_insert]
                  simp [current]
        _ = (∑ s : Fin T, if s.1 < t.1 then g s ^ 2 else 0) + g t ^ 2 := by
              simp [Finset.sum_filter, current, add_comm]
    simp only [p]
    rw [hsum]
    ring
  have hpoint : ∀ t : Fin T,
      g t ^ 2 * (p (t.1 + 1)) ^ (-(1 / 2 : ℝ)) ≤
        2 * ((p (t.1 + 1)) ^ (1 / 2 : ℝ) -
          (p t.1) ^ (1 / 2 : ℝ)) := by
    intro t
    rw [hp_succ t]
    exact mul_add_rpow_neg_half_le_two_mul_sub_rpow_half_of_nonneg
      (p t.1) (g t ^ 2) (hp_nonneg t.1) (sq_nonneg (g t))
  have hsum_le := Finset.sum_le_sum (fun t (_ht : t ∈ Finset.univ) => hpoint t)
  have htelescope :
      (∑ t : Fin T,
        ((p (t.1 + 1)) ^ (1 / 2 : ℝ) - (p t.1) ^ (1 / 2 : ℝ))) =
        (p T) ^ (1 / 2 : ℝ) - (p 0) ^ (1 / 2 : ℝ) := by
    have hdrop := sum_fin_adjacent_sub_eq_sub T (fun k => (p k) ^ (1 / 2 : ℝ))
    calc
      (∑ t : Fin T,
        ((p (t.1 + 1)) ^ (1 / 2 : ℝ) - (p t.1) ^ (1 / 2 : ℝ))) =
          -(∑ t : Fin T,
            ((p t.1) ^ (1 / 2 : ℝ) - (p (t.1 + 1)) ^ (1 / 2 : ℝ))) := by
              rw [← Finset.sum_neg_distrib]
              apply Finset.sum_congr rfl
              intro t _ht
              ring
      _ = -((p 0) ^ (1 / 2 : ℝ) - (p T) ^ (1 / 2 : ℝ)) := by rw [hdrop]
      _ = (p T) ^ (1 / 2 : ℝ) - (p 0) ^ (1 / 2 : ℝ) := by ring
  have hp0_nonneg : 0 ≤ (p 0) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (hp_nonneg 0) _
  calc
    (∑ t : Fin T,
      g t ^ 2 *
        (a + ∑ s : Fin T, if s.1 < t.1 + 1 then g s ^ 2 else 0) ^
          (-(1 / 2 : ℝ))) =
        ∑ t : Fin T, g t ^ 2 * (p (t.1 + 1)) ^ (-(1 / 2 : ℝ)) := by
          rfl
    _ ≤ ∑ t : Fin T,
          2 * ((p (t.1 + 1)) ^ (1 / 2 : ℝ) -
            (p t.1) ^ (1 / 2 : ℝ)) := hsum_le
    _ = 2 * ((p T) ^ (1 / 2 : ℝ) - (p 0) ^ (1 / 2 : ℝ)) := by
          rw [← Finset.mul_sum, htelescope]
    _ ≤ 2 * (p T) ^ (1 / 2 : ℝ) := by linarith
    _ = 2 *
        (a + ∑ s : Fin T, if s.1 < T then g s ^ 2 else 0) ^
          (1 / 2 : ℝ) := by rfl

-- Merged from Staging/Matrix_spectral_coeff_eq_zero_of_sq_le_diagonal_of_eigenvalue_eq_zero.lean

open scoped BigOperators

namespace Matrix

-- Generalization plan (G0):
-- concept/name: vanishing spectral coefficient under coordinate-square
--   domination by a diagonal matrix; orig was
--   `spectral_coeff_zero_of_diagonal_current_sq_le`
-- generality used: an arbitrary finite index type with decidable equality,
--   two real coordinate families, a pointwise square bound, and one
--   zero-eigenvalue hypothesis; no algorithm, measure, PSD, convexity,
--   smoothness, or oracle assumptions
-- portable call pattern: diagonal AdaGrad, diagonal Shampoo, and diagonal
--   covariance proofs vary the coordinate type, accumulated diagonal weights,
--   and current vector while proving that negative spectral powers never see
--   a nonzero coefficient at a zero eigenvalue
-- counterargument checked: the result is not paper-local or a pure wrapper;
--   unlike rank-one Loewner domination, coordinate-square domination does not
--   imply `vecMulVec g g ≤ diagonal d`, so the diagonal support argument is a
--   distinct reusable bridge
-- coverage search: symbol searches for `spectral coefficient equals zero
--   square bounded by diagonal eigenvalue zero` and `diagonal kernel support
--   coordinate square domination`, plus Mathlib semantic search for the full
--   statement, found `Matrix.ker_diagonal_toLin'`,
--   `Matrix.IsHermitian.mulVec_eigenvectorBasis`, and
--   `Matrix.PosSemidef.dotProduct_mulVec_zero_iff`; these describe proof
--   components but do not combine the square bound with spectral support
-- minimal hypotheses: `Fintype` is required by the finite Hermitian spectral
--   basis and sum, `DecidableEq` by diagonal matrices, and the source's
--   arbitrary matrix equality and positive-semidefinite proof are eliminated

/-- Coordinate-square domination by diagonal weights forces a vector's
coefficient along every zero-eigenvalue direction of the diagonal matrix to
vanish.

Layer: Glue | Gap: Level 1 (diagonal coordinate domination to spectral kernel support)
Proof: use the diagonal eigenvector equation to show every positive-weight coordinate of the zero-eigenvector vanishes; on a zero-weight coordinate, the square bound forces the dominated vector coordinate to vanish.
Source: Mathlib finite Hermitian matrix spectral theory, diagonal matrix-vector multiplication, and ordered real square arithmetic
Used in: diagonal AdaGrad, Shampoo, and covariance-preconditioner estimates that remove zero-eigenvalue terms before applying negative spectral powers
Book citation: book/research/Source.json#/additional_algorithm_specs/1/steps/2
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 3 diagonal matrix regret proof -/
theorem spectral_coeff_eq_zero_of_sq_le_diagonal_of_eigenvalue_eq_zero
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    (d g : iota → ℝ) (hcurrent : ∀ j, g j ^ 2 ≤ d j) (i : iota)
    (hi : (Matrix.isHermitian_diagonal d).eigenvalues i = 0) :
    (∑ j : iota,
      g j * ((Matrix.isHermitian_diagonal d).eigenvectorUnitary :
        Matrix iota iota ℝ) j i) = 0 := by
  classical
  let hD : (Matrix.diagonal d : Matrix iota iota ℝ).IsHermitian :=
    Matrix.isHermitian_diagonal d
  have heig := hD.mulVec_eigenvectorBasis i
  have hcoord : ∀ j : iota,
      d j * (hD.eigenvectorUnitary : Matrix iota iota ℝ) j i = 0 := by
    intro j
    have hj := congrFun heig j
    rw [hi] at hj
    simpa [Matrix.mulVec, dotProduct, Matrix.diagonal_apply] using hj
  apply Finset.sum_eq_zero
  intro j _hj
  by_cases hdj : d j = 0
  · have hgj_sq : g j ^ 2 = 0 :=
      le_antisymm (by simpa [hdj] using hcurrent j) (sq_nonneg (g j))
    have hgj : g j = 0 := sq_eq_zero_iff.mp hgj_sq
    simp [hgj]
  · have hUji : (hD.eigenvectorUnitary : Matrix iota iota ℝ) j i = 0 := by
      exact (mul_eq_zero.mp (hcoord j)).resolve_left hdj
    exact mul_eq_zero.mpr (Or.inr hUji)

end Matrix

-- Merged from Staging/Matrix_spectral_coeff_eq_zero_of_vecMulVec_le_of_eigenvalue_eq_zero.lean

open scoped BigOperators MatrixOrder

namespace Matrix

-- Generalization plan (G0):
-- concept/name: vanishing spectral coefficient of a vector whose self outer
--   product is dominated by a Hermitian matrix; orig was
--   `spectral_coeff_zero_of_vectorOuter_le_psd_zero_eigen`
-- generality used: an arbitrary finite index type with decidable equality, a
--   real vector, a real Hermitian square matrix, one Loewner-order
--   domination hypothesis, and one zero-eigenvalue hypothesis; no algorithm,
--   measure, convexity, smoothness, oracle, or strict-positivity assumptions
-- portable call pattern: low-rank covariance, Gram-prefix, and pseudoinverse
--   support proofs vary the dominated vector and PSD matrix while concluding
--   that the vector has no component in a zero-eigenvalue direction
-- counterargument checked: this is not paper-local traceability or a pure
--   wrapper; it combines Loewner domination, a rank-one quadratic form, and
--   the chosen spectral basis into the reusable range/kernel support fact
-- coverage search: symbol searches for `spectral coefficient zero vector outer
--   product dominated positive semidefinite matrix zero eigenvalue` and
--   `vecMulVec less equal positive semidefinite eigenvalue zero coefficient`,
--   plus Mathlib semantic search for the kernel-support statement, found only
--   `Matrix.PosSemidef.dotProduct_mulVec_zero_iff`,
--   `Matrix.IsHermitian.mulVec_eigenvectorBasis`, and
--   `Matrix.posSemidef_vecMulVec_self_star`; these cover proof components but
--   not the domination-to-spectral-coefficient conclusion
-- minimal hypotheses: `Fintype` supports the spectral and finite-sum APIs and
--   `DecidableEq` supports the chosen eigenbasis and matrix Loewner order; all
--   data hypotheses are pointwise and already minimal

/-- If a real vector's self outer product is Loewner-bounded by a
Hermitian matrix, then its coefficient along every zero-eigenvalue
direction of that matrix vanishes.

Layer: Glue | Gap: Level 1 (rank-one Loewner domination to spectral kernel support)
Proof: evaluate the Loewner bound on the zero-eigenvalue eigenvector, use the eigenvector equation to make the upper quadratic form zero, and expand the rank-one lower quadratic form as the square of the spectral coefficient.
Source: Mathlib finite Hermitian matrix spectral theory, positive-semidefinite matrix order, and bilinear-form evaluation APIs
Used in: low-rank covariance, Gram-prefix, and pseudoinverse estimates that must remove zero-eigenvalue terms before applying negative spectral powers
Book citation: book/research/Source.json#/key_lemmas/8/proof/15
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 1 matrix regret proof -/
theorem spectral_coeff_eq_zero_of_vecMulVec_le_of_eigenvalue_eq_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → ℝ) (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    (hOuter : Matrix.vecMulVec g g ≤ A) (i : ι)
    (hi : hA.eigenvalues i = 0) :
    (∑ j : ι, g j * (hA.eigenvectorUnitary : Matrix ι ι ℝ) j i) = 0 := by
  classical
  let v : ι → ℝ := ⇑(hA.eigenvectorBasis i)
  have hAv : A.mulVec v = 0 := by
    simpa [v, hi] using hA.mulVec_eigenvectorBasis i
  have hA_zero : Matrix.toBilin' A v v = 0 := by
    rw [Matrix.toBilin'_apply']
    simp [hAv]
  have hOuter_le :
      Matrix.toBilin' (Matrix.vecMulVec g g) v v ≤ Matrix.toBilin' A v v :=
    Matrix.toBilin_self_mono_of_le v hOuter
  have hsq_le : (∑ j : ι, g j * v j) ^ 2 ≤ 0 := by
    rw [← hA_zero]
    simpa [Matrix.toBilin'_apply', Matrix.mulVec, Matrix.vecMulVec_apply,
      dotProduct, pow_two, Finset.mul_sum, Finset.sum_mul, mul_assoc,
      mul_left_comm, mul_comm] using hOuter_le
  have hcoeff : (∑ j : ι, g j * v j) = 0 := by
    nlinarith [sq_nonneg (∑ j : ι, g j * v j)]
  simpa [v] using hcoeff

end Matrix

-- Merged from Staging/tendsto_sum_sq_mul_add_rpow_neg_half_of_support.lean

open Topology
open scoped BigOperators

-- Generalization plan (G0):
-- concept/name: convergence of a finite inverse-square-root spectral sum under positive regularization and a zero-spectrum support condition; orig was spectral_support_inverse_sqrt_tendsto.
-- generality used: an arbitrary finite index type and two real-valued families, with pointwise nonnegativity of the spectral values and pointwise vanishing of coefficients on their zero set; no matrix, measure, optimization, norm, inner-product, or finite-dimensional assumptions are used.
-- portable call pattern: singular Shampoo, AdaGrad, and pseudoinverse preconditioner arguments vary the spectrum and spectral coefficients while using the same support condition to remove a positive scalar regularizer at zero.
-- counterargument checked: this is not paper-local traceability or a one-line rename; it packages the essential zero/nonzero spectral split, real-power continuity away from zero, and finite-sum convergence needed at singular endpoints.
-- coverage search: queried `finite sum convergence real powers under positive regularization coefficients zero on zero support`, `tendsto sum squared coefficients lambda plus delta rpow negative half support`, and `Tendsto rpow add positive right neighborhood zero` with `lean_search_symbols`, and the finite-sum convergence contract with Mathlib LeanSearch; the hits provided only `tendsto_finset_sum` and pointwise real-power continuity, while neither Mathlib nor SOptLib contains the combined support-aware conclusion.
-- minimal hypotheses: finite indexing, pointwise nonnegativity, and coefficient vanishing at zero are all used; `DecidableEq` is supplied locally by classical logic and no nonemptiness or strict positivity assumption is needed.

/-- A finite sum of squared coefficients times inverse square roots converges as a
positive additive regularizer tends to zero, provided the coefficients vanish on
the zero set of the nonnegative base family.

Layer: Glue | Gap: Level 1 (support-aware inverse-square-root regularization limit)
Proof: commute the limit through the finite sum, split each spectral value into zero and positive cases, cancel zero-spectrum summands by the support hypothesis, and use continuity of real powers at each positive spectral value.
Source: Mathlib finite-sum filter convergence and `Filter.Tendsto.rpow_const` from `Analysis.SpecialFunctions.Pow.Real`
Used in: singular Shampoo, AdaGrad, and pseudoinverse preconditioner proofs that remove positive regularization from finite spectral dual-quadratic sums
Book citation: book/research/Source.json#/key_lemmas/8/proof/14
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 1 matrix Shampoo -/
theorem tendsto_sum_sq_mul_add_rpow_neg_half_of_support
    {ι : Type*} [Fintype ι]
    (lam coeff : ι → ℝ)
    (hlam_nonneg : ∀ i : ι, 0 ≤ lam i)
    (hcoeff_zero : ∀ i : ι, lam i = 0 → coeff i = 0) :
    Filter.Tendsto
      (fun delta : ℝ ↦
        ∑ i : ι, coeff i ^ 2 * (lam i + delta) ^ (-(1 / 2 : ℝ)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (∑ i : ι, coeff i ^ 2 * (lam i) ^ (-(1 / 2 : ℝ)))) := by
  classical
  refine
    tendsto_finset_sum (s := (Finset.univ : Finset ι))
      (f := fun i delta ↦ coeff i ^ 2 * (lam i + delta) ^ (-(1 / 2 : ℝ)))
      (a := fun i ↦ coeff i ^ 2 * (lam i) ^ (-(1 / 2 : ℝ)))
      (x := nhdsWithin (0 : ℝ) (Set.Ioi 0)) ?_
  intro i _hi
  by_cases hzero : lam i = 0
  · have hcoeff : coeff i = 0 := hcoeff_zero i hzero
    simp [hcoeff]
  · have hpos : 0 < lam i := lt_of_le_of_ne (hlam_nonneg i) (Ne.symm hzero)
    have hlin :
        Filter.Tendsto (fun delta : ℝ ↦ lam i + delta)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (lam i + 0)) := by
      exact tendsto_const_nhds.add
        (tendsto_nhdsWithin_of_tendsto_nhds (f := id) Filter.tendsto_id)
    have hrpow :
        Filter.Tendsto
          (fun delta : ℝ ↦ (lam i + delta) ^ (-(1 / 2 : ℝ)))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhds ((lam i + 0) ^ (-(1 / 2 : ℝ)))) := by
      exact hlin.rpow_const (p := (-(1 / 2 : ℝ))) (Or.inl (by positivity))
    have hmul := (tendsto_const_nhds (x := coeff i ^ 2)).mul hrpow
    simpa using hmul

-- Merged from Staging/Matrix_weightedHarmonicResolvent_mono.lean

open scoped MatrixOrder

namespace Matrix

universe u

-- Generalization plan (G0):
-- concept/name: joint Loewner monotonicity of the weighted harmonic resolvent;
--   orig was `Shampoo.weightedHarmonicResolvent_mono`
-- generality used: arbitrary finite index type with decidable equality, four real
--   square matrices, positive definiteness of the two smaller matrices, coordinatewise
--   Loewner bounds, and a nonnegative scalar weight; no fixed dimension, probability,
--   optimization, commutativity, or finite-dimensional vector-space assumptions
-- portable call pattern: operator-mean and adaptive-preconditioner proofs vary all four
--   positive-definite metric matrices and the scalar weight while using the same joint
--   monotonicity step before applying a positive map or integrating a resolvent kernel
-- counterargument checked: a private copy occurs inside the staged binary operator-mean
--   proof, but no public Mathlib or SOptLib declaration packages this two-coordinate
--   inverse-order composition; it is not a pure rename of inverse antitonicity
-- coverage search: queries for "weighted harmonic resolvent joint Loewner monotonicity
--   positive definite matrices positive scalar" and "inverse of sum of inverse matrices
--   monotone under Loewner order" found `CStarAlgebra.inv_le_inv`,
--   `Matrix.nonsing_inv_antitone_of_posDef`, and the private operator-mean copy, but no
--   public theorem with this joint conclusion
-- minimal hypotheses: positivity of `C` and `D` follows from `A ≤ C`, `B ≤ D` and
--   positivity of `A` and `B`; the scalar assumption is weakened from `0 < s` to `0 ≤ s`

/-- The weighted harmonic resolvent is jointly monotone in its two
positive-definite matrix arguments for every nonnegative weight.

Layer: Glue | Gap: Level 1 (joint Loewner monotonicity of a weighted harmonic resolvent)
Proof: reverse both coordinate inequalities by positive-definite matrix inversion, preserve their sum under nonnegative scalar multiplication, and reverse the resulting sum inequality by inversion once more.
Source: Kubo--Ando harmonic means; Mathlib matrix positive-definiteness and Loewner-order APIs together with `Matrix.nonsing_inv_antitone_of_posDef`
Used in: operator-geometric-mean monotonicity proofs comparing pointwise harmonic-resolvent kernels before applying a positive linear map and integrating
Book citation: book/research/Source.json#/key_lemmas/7
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Lemma 6 operator-mean monotonicity support -/
theorem weightedHarmonicResolvent_mono
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A B C D : Matrix ι ι ℝ) (s : ℝ)
    (hA : A.PosDef) (hB : B.PosDef)
    (hAC : A ≤ C) (hBD : B ≤ D) (hs : 0 ≤ s) :
    (A⁻¹ + s • B⁻¹)⁻¹ ≤ (C⁻¹ + s • D⁻¹)⁻¹ := by
  have hC : C.PosDef := by
    convert hA.add_posSemidef (Matrix.le_iff.mp hAC) using 1
    abel
  have hD : D.PosDef := by
    convert hB.add_posSemidef (Matrix.le_iff.mp hBD) using 1
    abel
  have hCinv_Ainv : C⁻¹ ≤ A⁻¹ :=
    analysis_nonsing_inv_antitone_of_posDef A C hA hAC
  have hDinv_Binv : D⁻¹ ≤ B⁻¹ :=
    analysis_nonsing_inv_antitone_of_posDef B D hB hBD
  have hsum : C⁻¹ + s • D⁻¹ ≤ A⁻¹ + s • B⁻¹ :=
    add_le_add hCinv_Ainv (smul_le_smul_of_nonneg_left hDinv_Binv hs)
  exact analysis_nonsing_inv_antitone_of_posDef
    (C⁻¹ + s • D⁻¹) (A⁻¹ + s • B⁻¹)
    (hC.inv.add_posSemidef (hD.inv.posSemidef.smul hs)) hsum

end Matrix

-- Merged from Staging/Matrix_rpowPerspectiveKernel_eq_smul_weightedHarmonicResolvent.lean

open scoped ContinuousFunctionalCalculus MatrixOrder

namespace Matrix

-- Generalization plan (G0):
-- concept/name: rational real-power perspective kernel as a scalar multiple of the
--   weighted harmonic resolvent; orig was
--   `Shampoo.weightedHarmonicResolvent_eq_rpow_perspective_integrand`
-- generality used: arbitrary finite index type with decidable equality, two
--   positive-definite real square matrices, and a positive real resolvent parameter;
--   no optimization, probability, commutativity, or fixed-dimension assumptions
-- portable call pattern: Kubo--Ando operator-mean, full-matrix adaptive-gradient, and
--   matrix-concavity proofs vary both positive-definite matrices and the positive
--   integration parameter while rewriting the same perspective kernel as a harmonic
--   resolvent before applying order or integration arguments
-- counterargument checked: the standalone resolvent definition was rejected this round,
--   but this theorem is not a caller-side expression or pure wrapper: it proves a
--   noncommutative conjugation-and-inversion identity linking CFC powers to an explicit
--   inverse sum, and is already needed privately by the staged operator-mean proof
-- coverage search: queries for "positive definite matrix rpow perspective kernel equals
--   scalar multiple weighted harmonic resolvent" and "inverse sum inverse matrices
--   harmonic resolvent rational perspective equality" found Mathlib's `CFC.rpow_add`,
--   matrix nonsingular-inverse laws, and a private copy inside the staged binary
--   weighted-geometric-mean monotonicity proof, but no public Mathlib or SOptLib theorem
-- minimal hypotheses: positive definiteness supplies the inverse and real-power
--   cancellations; `0 < s` is used for invertibility of `s • A + B` and scalar inverse
--   cancellation, and no commutation hypothesis between `A` and `B` is needed

/-- Conjugating the rational real-power perspective kernel of two positive-definite
matrices gives the reciprocal parameter times their weighted harmonic resolvent.

Layer: Glue | Gap: Level 2 (noncommutative real-power perspective to harmonic-resolvent identity)
Proof: cancel the positive square and inverse-square roots, identify the conjugated middle inverse through `s • A + B`, express the inverse sum as `A * (s • A + B)⁻¹ * B`, and finish by scalar cancellation
Source: Kubo--Ando operator means; Mathlib continuous-functional-calculus real-power addition and finite-matrix nonsingular-inverse APIs
Used in: operator-geometric-mean monotonicity and concavity proofs that convert each pointwise rational perspective integrand into a positive scalar multiple of an order-monotone harmonic resolvent before integration
Book citation: book/research/Source.json#/key_lemmas/7
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Lemma 6 operator-mean monotonicity support -/
theorem rpowPerspectiveKernel_eq_smul_weightedHarmonicResolvent
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) (s : ℝ)
    (hA : A.PosDef) (hB : B.PosDef) (hs : 0 < s) :
    CFC.rpow A (1 / 2 : ℝ) *
          ((s⁻¹) • (1 : Matrix ι ι ℝ) -
            (s • (1 : Matrix ι ι ℝ) +
              CFC.rpow A (-(1 / 2 : ℝ)) * B *
                CFC.rpow A (-(1 / 2 : ℝ)))⁻¹) *
        CFC.rpow A (1 / 2 : ℝ) =
      (s⁻¹) • (A⁻¹ + s • B⁻¹)⁻¹ := by
  classical
  let P : Matrix ι ι ℝ := CFC.rpow A (1 / 2 : ℝ)
  let Q : Matrix ι ι ℝ := CFC.rpow A (-(1 / 2 : ℝ))
  let K : Matrix ι ι ℝ := s • A + B
  have hK_pd : K.PosDef := (hA.smul hs).add hB
  have hP_Q : P * Q = (1 : Matrix ι ι ℝ) := by
    dsimp only [P, Q]
    rw [show CFC.rpow A (1 / 2 : ℝ) * CFC.rpow A (-(1 / 2 : ℝ)) =
        CFC.rpow A ((1 / 2 : ℝ) + (-(1 / 2 : ℝ))) by
      simpa only [CFC.rpow_eq_pow] using
        (CFC.rpow_add (a := A) (x := (1 / 2 : ℝ))
          (y := -(1 / 2 : ℝ)) hA.isUnit).symm]
    norm_num
    exact CFC.rpow_zero A
  have hQ_P : Q * P = (1 : Matrix ι ι ℝ) := by
    dsimp only [P, Q]
    rw [show CFC.rpow A (-(1 / 2 : ℝ)) * CFC.rpow A (1 / 2 : ℝ) =
        CFC.rpow A ((-(1 / 2 : ℝ)) + (1 / 2 : ℝ)) by
      simpa only [CFC.rpow_eq_pow] using
        (CFC.rpow_add (a := A) (x := -(1 / 2 : ℝ))
          (y := (1 / 2 : ℝ)) hA.isUnit).symm]
    norm_num
    exact CFC.rpow_zero A
  have hP_P : P * P = A := by
    dsimp only [P]
    rw [show CFC.rpow A (1 / 2 : ℝ) * CFC.rpow A (1 / 2 : ℝ) =
        CFC.rpow A ((1 / 2 : ℝ) + (1 / 2 : ℝ)) by
      simpa only [CFC.rpow_eq_pow] using
        (CFC.rpow_add (a := A) (x := (1 / 2 : ℝ))
          (y := (1 / 2 : ℝ)) hA.isUnit).symm]
    norm_num
    exact CFC.rpow_one A hA.posSemidef.nonneg
  have hKinv_K : K⁻¹ * K = (1 : Matrix ι ι ℝ) := by
    have hdet : K.det ≠ 0 := ne_of_gt hK_pd.det_pos
    letI : Invertible K.det := invertibleOfNonzero hdet
    letI : Invertible K := Matrix.invertibleOfDetInvertible K
    exact Matrix.inv_mul_of_invertible K
  have hB_Binv : B * B⁻¹ = (1 : Matrix ι ι ℝ) := by
    have hdet : B.det ≠ 0 := ne_of_gt hB.det_pos
    letI : Invertible B.det := invertibleOfNonzero hdet
    letI : Invertible B := Matrix.invertibleOfDetInvertible B
    exact Matrix.mul_inv_of_invertible B
  have hA_Ainv : A * A⁻¹ = (1 : Matrix ι ι ℝ) := by
    have hdet : A.det ≠ 0 := ne_of_gt hA.det_pos
    letI : Invertible A.det := invertibleOfNonzero hdet
    letI : Invertible A := Matrix.invertibleOfDetInvertible A
    exact Matrix.mul_inv_of_invertible A
  have hmiddle :
      s • (1 : Matrix ι ι ℝ) + Q * B * Q = Q * K * Q := by
    have hQAQ : Q * A * Q = (1 : Matrix ι ι ℝ) := by
      rw [← hP_P]
      calc
        Q * (P * P) * Q = (Q * P) * (P * Q) := by noncomm_ring
        _ = 1 := by rw [hQ_P, hP_Q, one_mul]
    dsimp [K]
    rw [mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul, hQAQ]
  have hmiddle_inv :
      (s • (1 : Matrix ι ι ℝ) + Q * B * Q)⁻¹ = P * K⁻¹ * P := by
    rw [hmiddle]
    apply Matrix.inv_eq_left_inv
    calc
      (P * K⁻¹ * P) * (Q * K * Q) =
          P * K⁻¹ * (P * Q) * K * Q := by noncomm_ring
      _ = P * (K⁻¹ * K) * Q := by rw [hP_Q]; simp [mul_assoc]
      _ = 1 := by rw [hKinv_K, mul_one, hP_Q]
  have hresolver_inv :
      (A⁻¹ + s • B⁻¹)⁻¹ = A * K⁻¹ * B := by
    apply Matrix.inv_eq_left_inv
    calc
      (A * K⁻¹ * B) * (A⁻¹ + s • B⁻¹) =
          A * K⁻¹ * (B + s • A) * A⁻¹ := by
            noncomm_ring [hA_Ainv, hB_Binv]
      _ = A * (K⁻¹ * K) * A⁻¹ := by
            rw [show B + s • A = K by simp [K, add_comm]]
            simp [mul_assoc]
      _ = 1 := by rw [hKinv_K, mul_one, hA_Ainv]
  change P * ((s⁻¹) • (1 : Matrix ι ι ℝ) -
      (s • (1 : Matrix ι ι ℝ) + Q * B * Q)⁻¹) * P =
    (s⁻¹) • (A⁻¹ + s • B⁻¹)⁻¹
  rw [hmiddle_inv, hresolver_inv]
  rw [mul_sub, sub_mul]
  simp only [Matrix.mul_smul, Matrix.smul_mul, mul_one]
  have hconj : P * (P * K⁻¹ * P) * P = A * K⁻¹ * A := by
    calc
      P * (P * K⁻¹ * P) * P = (P * P) * K⁻¹ * (P * P) := by
        noncomm_ring
      _ = A * K⁻¹ * A := by rw [hP_P]
  rw [hconj]
  have hexpand : A = s • (A * K⁻¹ * A) + A * K⁻¹ * B := by
    calc
      A = A * (K⁻¹ * K) := by rw [hKinv_K, mul_one]
      _ = s • (A * K⁻¹ * A) + A * K⁻¹ * B := by
        dsimp [K]
        simp only [mul_add, mul_assoc, Matrix.mul_smul]
  have hscaled :
      (s⁻¹) • A = A * K⁻¹ * A + (s⁻¹) • (A * K⁻¹ * B) := by
    calc
      (s⁻¹) • A = (s⁻¹) • (s • (A * K⁻¹ * A) + A * K⁻¹ * B) :=
        congrArg ((s⁻¹) • ·) hexpand
      _ = A * K⁻¹ * A + (s⁻¹) • (A * K⁻¹ * B) := by
        rw [smul_add, smul_smul, inv_mul_cancel₀ hs.ne', one_smul]
  rw [hP_P, hscaled]
  module

end Matrix

-- Merged from Staging/Matrix_rpowPerspectiveIntegrand_eq_smul_weightedHarmonicResolvent.lean

open scoped ContinuousFunctionalCalculus MatrixOrder

namespace Matrix

-- Generalization plan (G0):
-- concept/name: full real-power perspective integrand as a scalar multiple of the
--   weighted harmonic resolvent; orig was
--   `Shampoo.rpowPerspectiveIntegrand_eq_smul_weightedHarmonicResolvent`
-- generality used: arbitrary finite index type with decidable equality, two
--   positive-definite real matrices, an unrestricted real exponent, and a positive
--   integration parameter; no optimization, probability, or commutativity assumptions
-- portable call pattern: Kubo--Ando operator-mean and adaptive full-matrix proofs vary
--   the two positive-definite matrices, exponent, integration parameter, and coordinate
--   type while rewriting the same pointwise power-perspective integrand before integration
-- counterargument checked: the nearby kernel theorem is a strict substep rather than a
--   duplicate; this result additionally evaluates `Real.rpowIntegrand₀₁` by CFC and
--   combines its exponent-dependent scalar with the harmonic-resolvent normalization
-- coverage search: queries for "matrix rpow perspective integrand equality scalar multiple
--   weighted harmonic resolvent positive definite" and "positive matrix power sandwich
--   functional calculus power integrand resolvent equality" found the staged kernel theorem
--   and CFC integrand evaluation, but no public declaration for their full perspective
--   composition; Mathlib semantic search returned only positive-definiteness primitives
-- minimal hypotheses: positive definiteness is used for the negative half-power and its
--   congruence with `B`; `0 < s` is exactly what enables both resolvent identities

/-- The full real-power perspective integrand of two positive-definite matrices is the
exponent-dependent scalar multiple of their weighted harmonic resolvent.

Layer: Glue | Gap: Level 1 (full matrix real-power perspective integrand evaluation)
Proof: evaluate `Real.rpowIntegrand₀₁` by the matrix continuous functional calculus, apply
  the noncommutative rational perspective-kernel identity, and combine scalar powers using
  `Real.rpow_sub_one`.
Source: Kubo--Ando operator means; Mathlib real-power continuous functional calculus,
  positive-definite matrix congruence, and real scalar-power identities
Used in: operator-geometric-mean monotonicity proofs that replace each pointwise integral
  representation term by a positive scalar multiple of a jointly monotone resolvent
Book citation: book/research/Source.json#/key_lemmas/7
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor
  Optimization, Lemma 6 operator-mean monotonicity support -/
theorem rpowPerspectiveIntegrand_eq_smul_weightedHarmonicResolvent
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) (p s : ℝ)
    (hA : A.PosDef) (hB : B.PosDef) (hs : 0 < s) :
    let Aneg := CFC.rpow A (-(1 / 2 : ℝ))
    let Ahalf := CFC.rpow A (1 / 2 : ℝ)
    Ahalf * cfc (R := ℝ) (p := IsSelfAdjoint)
          (Real.rpowIntegrand₀₁ p s) (Aneg * B * Aneg) * Ahalf =
      (s ^ (p - 1)) • (A⁻¹ + s • B⁻¹)⁻¹ := by
  classical
  let Aneg := CFC.rpow A (-(1 / 2 : ℝ))
  let Ahalf := CFC.rpow A (1 / 2 : ℝ)
  have hAneg : Aneg.PosDef := by
    exact Matrix.isStrictlyPositive_iff_posDef.mp
      (hA.isStrictlyPositive.rpow A (-(1 / 2 : ℝ)))
  have hAneg_star : Matrix.conjTranspose Aneg = Aneg := hAneg.1
  have hmiddle : (Aneg * B * Aneg).PosDef := by
    simpa only [hAneg_star] using
      hB.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hAneg.isUnit)
  have hcfc := Matrix.analysis_cfc_rpowIntegrand₀₁_eq_resolvent
    (Aneg * B * Aneg) p s hmiddle.posSemidef hs
  have hperspective := Matrix.rpowPerspectiveKernel_eq_smul_weightedHarmonicResolvent
    A B s hA hB hs
  change Ahalf * cfc (R := ℝ) (p := IsSelfAdjoint)
      (Real.rpowIntegrand₀₁ p s) (Aneg * B * Aneg) * Ahalf = _
  rw [hcfc]
  simp only [Matrix.mul_smul, Matrix.smul_mul]
  rw [hperspective, smul_smul]
  congr 1
  rw [Real.rpow_sub_one hs.ne' p]
  exact (div_eq_mul_inv (s ^ p) s).symm

end Matrix

-- Merged from Staging/Matrix_dualQuadraticForm_le_mul_spectralSupport_of_cfc_sqrt_le.lean

open scoped BigOperators MatrixOrder

namespace Matrix

-- Generalization plan (G0):
-- concept/name: a CFC square-root Loewner bound controls the inverse-metric
--   dual quadratic form by inverse-square-root spectral support; orig was
--   `spectral_support_inverse_sqrt_order_dual_bound`
-- generality used: an arbitrary finite decidable real coordinate type, a PSD
--   reference matrix, a PD metric, a nonnegative domination factor, and one
--   supported vector; no horizon, accumulator, algorithm state, measure,
--   convexity, smoothness, stochastic, or oracle assumptions are used
-- portable call pattern: full-matrix AdaGrad, Shampoo, covariance-adaptive
--   mirror descent, and online Newton proofs change the accumulated PSD matrix,
--   current PD metric, domination factor, and gradient while retaining the same
--   inverse-metric energy bound
-- counterargument checked: the result is not paper-local or a caller-side
--   expression; unlike the staged regularized spectral formula, it combines a
--   Loewner comparison, inverse-metric cancellation, singular weighted
--   Cauchy--Schwarz, and zero-eigenspace support into a new inequality
-- coverage search: symbol and semantic searches for `dual quadratic form upper
--   bound spectral support inverse square root positive definite matrix square
--   root Loewner order` found the regularized equality
--   `Matrix.dualQuadraticForm_cfc_sqrt_add_smul_one_spectral_support`,
--   `Matrix.toBilin_self_mono_of_le`, and the support-aware weighted
--   Cauchy--Schwarz theorem; these are ingredients and do not imply the complete
--   transport contract in one call
-- minimal hypotheses: finite decidable coordinates support matrix spectral
--   theory and total inversion; PSD supplies nonnegative eigenvalues, PD gives
--   inverse cancellation and nonnegative dual energy, nonnegative scaling is
--   needed at the final cancellation, and zero-spectrum support is exactly what
--   makes the singular inverse-square-root sum finite

/-- If the CFC square root of a positive-semidefinite matrix is Loewner-bounded
by a nonnegative multiple of a positive-definite metric, then the metric's dual
quadratic form is bounded by the same multiple of the vector's singular
inverse-square-root spectral support value.

Layer: Glue | Gap: Level 2 (Loewner domination to singular spectral dual-energy bound)
Proof: expand the CFC square root in its unitary eigenbasis, apply a support-aware weighted Cauchy--Schwarz inequality, evaluate the Loewner bound at the inverse-metric vector, and cancel the resulting nonnegative dual energy.
Source: Mathlib finite Hermitian matrix spectral functional calculus, positive-definite nonsingular inversion, and Loewner order, together with SOptLib finite-matrix quadratic forms and singular weighted Cauchy--Schwarz
Used in: full-matrix AdaGrad, Shampoo, covariance-adaptive mirror-descent, and online Newton analyses that transfer a square-root accumulator domination into a per-gradient inverse-metric bound
Book citation: book/research/Source.json#/key_lemmas/8/proof/15
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 1 matrix regret proof -/
theorem dualQuadraticForm_le_mul_spectralSupport_of_cfc_sqrt_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) (hA : A.PosSemidef) (hB : B.PosDef)
    (alpha : ℝ) (halpha_nonneg : 0 ≤ alpha) (g coeff : ι → ℝ)
    (hroot_le :
      cfc (R := ℝ) (p := IsSelfAdjoint) (fun x : ℝ => x ^ (1 / 2 : ℝ)) A ≤
        alpha • B)
    (hcoeff_def : ∀ i : ι,
      coeff i = ∑ j : ι, g j * (hA.1.eigenvectorUnitary : Matrix ι ι ℝ) j i)
    (hcoeff_zero : ∀ i : ι, hA.1.eigenvalues i = 0 → coeff i = 0) :
    SOptLib.finiteMatrixDualQuadraticForm B (WithLp.toLp 2 g) ≤
      alpha * ∑ i : ι,
        coeff i ^ 2 * (hA.1.eigenvalues i) ^ (-(1 / 2 : ℝ)) := by
  classical
  let U : unitary (Matrix ι ι ℝ) := hA.1.eigenvectorUnitary
  let lam : ι → ℝ := hA.1.eigenvalues
  let y : ι → ℝ := B⁻¹.mulVec g
  let ycoeff : ι → ℝ := fun i =>
    ∑ j : ι, y j * (U : Matrix ι ι ℝ) j i
  let supportValue : ℝ :=
    ∑ i : ι, coeff i ^ 2 * (lam i) ^ (-(1 / 2 : ℝ))
  let rootEnergy : ℝ :=
    ∑ i : ι, ycoeff i ^ 2 * (lam i) ^ (1 / 2 : ℝ)
  let dualValue : ℝ :=
    SOptLib.finiteMatrixDualQuadraticForm B (WithLp.toLp 2 g)
  have hdual_dot : dualValue = ∑ i : ι, g i * y i := by
    simp [dualValue, y, Matrix.mulVec,
      dotProduct, Finset.mul_sum, mul_assoc]
  have hcoeff_def_lam : ∀ i : ι,
      coeff i = ∑ j : ι, g j * (U : Matrix ι ι ℝ) j i := by
    intro i
    simpa [U] using hcoeff_def i
  have hdual_spectral :
      dualValue = ∑ i : ι, coeff i * ycoeff i := by
    calc
      dualValue = ∑ i : ι, g i * y i := hdual_dot
      _ = ∑ i : ι,
          (∑ j : ι, g j * (U : Matrix ι ι ℝ) j i) *
            (∑ j : ι, y j * (U : Matrix ι ι ℝ) j i) := by
          simpa only [mul_comm] using
            (finite_orthonormal_coordinate_bilinear_collapse
              (fun i k => (U : Matrix ι ι ℝ) i k) g y (fun i j => by
                have hunit := congrArg (fun M : Matrix ι ι ℝ => M i j)
                  (Unitary.coe_mul_star_self U)
                simpa [Matrix.mul_apply, Matrix.one_apply] using hunit)).symm
      _ = ∑ i : ι, coeff i * ycoeff i := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          simp [ycoeff, hcoeff_def_lam i]
  have hroot_spec :
      cfc (R := ℝ) (p := IsSelfAdjoint)
          (fun x : ℝ => x ^ (1 / 2 : ℝ)) A =
        (U : Matrix ι ι ℝ) *
          Matrix.diagonal (fun i : ι => (lam i) ^ (1 / 2 : ℝ)) *
            star (U : Matrix ι ι ℝ) := by
    rw [hA.1.cfc_eq]
    rfl
  have hroot_energy_eq :
      Matrix.toBilin'
          (cfc (R := ℝ) (p := IsSelfAdjoint)
            (fun x : ℝ => x ^ (1 / 2 : ℝ)) A) y y = rootEnergy := by
    rw [hroot_spec]
    simpa [rootEnergy, ycoeff, U, lam] using
      (Matrix.toBilin_mul_diagonal_mul_transpose_self_eq_sum_sq_mul
        y (fun i : ι => (lam i) ^ (1 / 2 : ℝ)) (U : Matrix ι ι ℝ))
  have hdet_ne : B.det ≠ 0 := ne_of_gt hB.det_pos
  letI : Invertible B.det := invertibleOfNonzero hdet_ne
  letI : Invertible B := Matrix.invertibleOfDetInvertible B
  have hcancel : B.mulVec y = g := by
    dsimp [y]
    rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible]
    simp
  have hdual_quad : Matrix.toBilin' B y y = dualValue := by
    rw [Matrix.toBilin'_apply]
    calc
      (∑ i, ∑ j, y i * B i j * y j) =
          ∑ i, y i * (B.mulVec y) i := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
      _ = ∑ i, y i * g i := by simp [hcancel]
      _ = ∑ i, g i * y i := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            ring
      _ = dualValue := hdual_dot.symm
  have hroot_bound : rootEnergy ≤ alpha * dualValue := by
    calc
      rootEnergy = Matrix.toBilin'
          (cfc (R := ℝ) (p := IsSelfAdjoint)
            (fun x : ℝ => x ^ (1 / 2 : ℝ)) A) y y := hroot_energy_eq.symm
      _ ≤ Matrix.toBilin' (alpha • B) y y :=
        Matrix.toBilin_self_mono_of_le y hroot_le
      _ = alpha * dualValue := by simp [hdual_quad]
  have hcs : dualValue ^ 2 ≤ supportValue * rootEnergy := by
    have hcs0 :=
      Finset.sum_mul_sq_le_inverse_sqrt_weight_mul_sqrt_weight lam coeff ycoeff
        (fun i => by simpa [lam] using hA.eigenvalues_nonneg i)
        (fun i hi => hcoeff_zero i (by simpa [lam] using hi))
    rw [hdual_spectral]
    simpa [supportValue, rootEnergy, lam] using hcs0
  have hsupport_nonneg : 0 ≤ supportValue := by
    refine Finset.sum_nonneg ?_
    intro i _hi
    exact mul_nonneg (sq_nonneg (coeff i))
      (Real.rpow_nonneg (by simpa [lam] using hA.eigenvalues_nonneg i) _)
  have hdual_nonneg : 0 ≤ dualValue := by
    rw [← hdual_quad, Matrix.toBilin'_apply']
    simpa only [star_trivial] using hB.posSemidef.dotProduct_mulVec_nonneg y
  have hsq_le : dualValue ^ 2 ≤ (alpha * supportValue) * dualValue := by
    calc
      dualValue ^ 2 ≤ supportValue * rootEnergy := hcs
      _ ≤ supportValue * (alpha * dualValue) :=
        mul_le_mul_of_nonneg_left hroot_bound hsupport_nonneg
      _ = (alpha * supportValue) * dualValue := by ring
  have hcoefficient_nonneg : 0 ≤ alpha * supportValue :=
    mul_nonneg halpha_nonneg hsupport_nonneg
  have hle : dualValue ≤ alpha * supportValue := by
    by_cases hdual_zero : dualValue = 0
    · simpa [hdual_zero] using hcoefficient_nonneg
    · have hdual_pos : 0 < dualValue := lt_of_le_of_ne hdual_nonneg (Ne.symm hdual_zero)
      apply le_of_mul_le_mul_right _ hdual_pos
      simpa [pow_two, mul_assoc] using hsq_le
  simpa [dualValue, supportValue, lam, mul_comm, mul_left_comm, mul_assoc] using hle

end Matrix


/-! Promoted from Staging/analyticAt_sub_linearization_isBigO_sq.lean. -/

open Filter Topology

-- Generalization plan (G1):
-- concept/name: quadratic Big-O remainder after subtracting the first-order
--   linearization of an analytic map; orig was
--   analyticAt_scalar_first_order_remainder_isBigO_sq
-- generality used: maps between normed spaces over an arbitrary nontrivially
--   normed field, an arbitrary base point, value, and Frechet derivative; no
--   completeness or finite-dimensional assumptions
-- portable call pattern: analytic perturbation, response, and local asymptotic
--   proofs vary the analytic map, base point, value, and derivative while
--   retaining a quadratic remainder after linearization
-- counterargument checked: this is not paper-local traceability or a pure
--   rename; Mathlib exposes the formal-power-series remainder, but callers
--   otherwise must identify its constant and linear coefficients and transport
--   the displacement estimate back to the original coordinate
-- coverage search: searched `analytic function first order linearization
--   quadratic big O remainder derivative at point`, `AnalyticAt sub
--   linearization IsBigO square displacement HasDerivAt`, and `isBigO sub
--   partialSum pow analytic formal multilinear series`; Mathlib's
--   `HasFPowerSeriesAt.isBigO_sub_partialSum_pow`, `HasFPowerSeriesAt.coeff_zero`,
--   and `HasFPowerSeriesAt.deriv` are proof components, while neither Mathlib
--   nor SOptLib contains the complete normed-space linearization contract
-- minimal hypotheses: analyticity supplies the second-order remainder, while
--   the value and derivative equalities are exactly the coefficient
--   identifications used by the proof

/-- Subtracting the value-and-derivative linearization of an analytic map leaves
a quadratic Big-O remainder at the base point.

Layer: Glue | Gap: Level 1 (analytic Taylor remainder in linearization form)
Proof: expose a local formal power series, identify its first coefficient from the supplied derivative, specialize `HasFPowerSeriesAt.isBigO_image_sub_norm_mul_norm_sub` at the base point, and use the supplied value equality.
Source: Mathlib analytic formal power series, Frechet derivative identification, and asymptotic filter composition APIs
Used in: analytic perturbation and response expansions where a map is replaced by its first-order model with a quadratic local error
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/13/proof/3
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem analyticAt_sub_linearization_isBigO_sq
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : E → F} {x₀ : E} {c : F} {d : E →L[𝕜] F}
    (hf : AnalyticAt 𝕜 f x₀) (hf_value : f x₀ = c)
    (hf_deriv : HasFDerivAt f d x₀) :
    Asymptotics.IsBigO (nhds x₀)
      (fun x => f x - (c + d (x - x₀)))
      (fun x => ‖x - x₀‖ ^ 2) := by
  rcases hf with ⟨p, hp⟩
  have hp₁ : continuousMultilinearCurryFin1 𝕜 E F (p 1) = d :=
    hp.hasFDerivAt.unique hf_deriv
  have hp₁_apply : ∀ y : E, p 1 (fun _ => y) = d y := by
    intro y
    rw [← hp₁, continuousMultilinearCurryFin1_apply]
    congr 2
  have hbig := hp.isBigO_image_sub_norm_mul_norm_sub.comp_tendsto
    (tendsto_id.prodMk_nhds tendsto_const_nhds)
  refine hbig.congr ?_ ?_
  · intro x
    simp only [Function.comp_apply, id_eq]
    rw [hf_value, hp₁_apply]
    abel
  · intro x
    simp [Prod.norm_def, pow_two]

/-! Promoted from Staging/ContinuousLinearMap_exists_eventually_analytic_normalized_eigenbranch_of_borderedEquiv.lean. -/

open Filter Topology

namespace ContinuousLinearMap

-- Generalization plan (G0):
-- concept/name: local analytic normalized eigenbranch from an invertible bordered derivative; orig was analytic_normalized_right_eigenbranch_eventually_of_bordered
-- generality used: an arbitrary complete real normed space, an analytic continuous-endomorphism family, a base eigenvalue/eigenvector, a continuous normalization functional, and a bordered continuous linear equivalence; no finite-dimensional or inner-product structure
-- portable call pattern: analytic perturbation steps for stochastic transition, mixing, preconditioner, and Hessian operators; the operator family, base eigenpair, normalization functional, neighborhood, and bordered equivalence vary while the local normalized branch conclusion is unchanged
-- counterargument checked: the result is not paper-local bookkeeping or a one-line wrapper; Mathlib supplies analytic inverse-function and bilinear-evaluation pieces but no normalized eigenbranch theorem, and SOptLib has no declaration with this contract
-- coverage search: queries "analytic eigenvalue eigenvector branch from invertible bordered derivative", "analytic inverse function local branch continuous linear equivalence", and "analytic continuous linear map application product" found Mathlib ContinuousLinearMap.analyticAt_bilinear and OpenPartialHomeomorph.analyticAt_symm' as components, but no full Mathlib/SOptLib eigenbranch result
-- minimal hypotheses: AnalyticAt at the base point replaces the paper's interval-wide analyticity; completeness is retained for the inverse function theorem, while finite dimensionality is dropped

/-- An analytic family of continuous endomorphisms admits a local analytic normalized
eigenpair branch when the bordered eigenpair derivative at the base point is a
continuous linear equivalence.

Layer: Glue | Gap: Level 2 (analytic normalized eigenbranch from bordered invertibility)
Proof: apply the analytic inverse-function theorem to the parameter, normalization,
  and eigen-residual map; the supplied bordered equivalence makes its triangular
  derivative invertible.
Source: Mathlib analytic maps, bilinear Fréchet differentiation, and the Banach-space inverse function theorem
Used in: analytic perturbation of stochastic mixing operators around a normalized Perron eigenpair, and analogous local eigenpair constructions for preconditioners and Hessian families
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem exists_eventually_analytic_normalized_eigenbranch_of_borderedEquiv
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (A : ℝ → (V →L[ℝ] V)) (lambda0 : ℝ) (right : V)
    (left : V →L[ℝ] ℝ)
    (hA : AnalyticAt ℝ A 0)
    (hright : A 0 right = lambda0 • right)
    (hnormalized : left right = 1)
    (bordered : (ℝ × V) ≃L[ℝ] (ℝ × V))
    (hbordered : ∀ x : ℝ × V,
      bordered x = (left x.2, A 0 x.2 - lambda0 • x.2 - x.1 • right)) :
    ∃ gamma : ℝ → ℝ, ∃ r : ℝ → V,
      gamma 0 = lambda0 ∧ r 0 = right ∧
        ∀ᶠ alpha : ℝ in 𝓝 0,
          AnalyticAt ℝ gamma alpha ∧ AnalyticAt ℝ r alpha ∧
            A alpha (r alpha) = gamma alpha • r alpha ∧
            left (r alpha) = 1 := by
  obtain ⟨Aderiv, hAderiv⟩ : ∃ Aderiv : V →L[ℝ] V, HasDerivAt A Aderiv 0 :=
    ⟨_, hA.differentiableAt.hasDerivAt⟩
  let vderiv : V := Aderiv right
  let T : (ℝ × (ℝ × V)) →L[ℝ] (ℝ × (ℝ × V)) :=
    { toFun := fun x => (x.1, bordered x.2 + (0, x.1 • vderiv))
      map_add' := by
        intro x y
        ext
        · simp
        · simp [add_smul]
        · simp [add_smul]
          abel
      map_smul' := by
        intro c x
        ext <;> simp [mul_smul]
      cont := by fun_prop }
  have hT_injective : Function.Injective T := by
    intro x y hxy
    have hfirst_raw := congrArg Prod.fst hxy
    have hfirst : x.1 = y.1 := by simpa [T] using hfirst_raw
    have hsecond : bordered x.2 = bordered y.2 := by
      have h := congrArg Prod.snd hxy
      simpa [T, hfirst] using h
    exact Prod.ext hfirst (bordered.injective hsecond)
  have hT_surjective : Function.Surjective T := by
    intro y
    refine ⟨(y.1, bordered.symm (y.2 - (0, y.1 • vderiv))), ?_⟩
    ext <;> simp [T]
  let jacobian : (ℝ × (ℝ × V)) ≃L[ℝ] (ℝ × (ℝ × V)) :=
    ContinuousLinearEquiv.ofBijective T
      (LinearMap.ker_eq_bot.mpr hT_injective)
      (LinearMap.range_eq_top.mpr hT_surjective)
  have hjacobian (x : ℝ × (ℝ × V)) :
      jacobian x = (x.1, bordered x.2 + (0, x.1 • vderiv)) := by
    rfl
  let base : ℝ × (ℝ × V) := (0, (lambda0, right))
  let target : ℝ × (ℝ × V) := (0, (1, 0))
  let Phi : (ℝ × (ℝ × V)) → (ℝ × (ℝ × V)) := fun x =>
    (x.1, (left x.2.2, A x.1 x.2.2 - x.2.1 • x.2.2))
  have hPhi_base : Phi base = target := by
    simp [Phi, base, target, hright, hnormalized]
  have hPhi_analytic : AnalyticAt ℝ Phi base := by
    have hx1 : AnalyticAt ℝ (fun x : ℝ × (ℝ × V) => x.1) base :=
      analyticAt_fst
    have hx2 : AnalyticAt ℝ (fun x : ℝ × (ℝ × V) => x.2) base :=
      analyticAt_snd
    have hx21 : AnalyticAt ℝ (fun x : ℝ × (ℝ × V) => x.2.1) base :=
      analyticAt_fst.comp' hx2
    have hx22 : AnalyticAt ℝ (fun x : ℝ × (ℝ × V) => x.2.2) base :=
      analyticAt_snd.comp' hx2
    have hAcomp : AnalyticAt ℝ (fun x : ℝ × (ℝ × V) => A x.1) base :=
      hA.comp_of_eq' hx1 (by simp [base])
    have hnormal : AnalyticAt ℝ
        (fun x : ℝ × (ℝ × V) => left x.2.2) base :=
      (left.analyticAt _).comp' hx22
    have hoperator : AnalyticAt ℝ
        (fun x : ℝ × (ℝ × V) => A x.1 x.2.2) base := by
      exact (ContinuousLinearMap.flip (ContinuousLinearMap.apply ℝ V)).analyticAt_bilinear _
        |>.comp' (hAcomp.prod hx22)
    have hscalar : AnalyticAt ℝ
        (fun x : ℝ × (ℝ × V) => x.2.1 • x.2.2) base := by
      exact (ContinuousLinearMap.lsmul ℝ ℝ).analyticAt_bilinear _
        |>.comp' (hx21.prod hx22)
    exact hx1.prod (hnormal.prod (hoperator.sub hscalar))
  have hPhi_deriv : HasFDerivAt Phi
      (jacobian : (ℝ × (ℝ × V)) →L[ℝ] (ℝ × (ℝ × V))) base := by
    let rawDeriv : (ℝ × (ℝ × V)) → (ℝ × (ℝ × V)) := fun d =>
      (d.1, (left d.2.2,
        d.1 • vderiv + A 0 d.2.2 - (d.2.1 • right + lambda0 • d.2.2)))
    have hraw_eq (d : ℝ × (ℝ × V)) : rawDeriv d = jacobian d := by
      rw [hjacobian d, hbordered d.2]
      ext <;> simp [rawDeriv]
      abel
    have hline (d : ℝ × (ℝ × V)) :
        HasDerivAt (fun t : ℝ => Phi (base + t • d)) (rawDeriv d) 0 := by
      have hparam : HasDerivAt (fun t : ℝ => (base + t • d).1) d.1 0 := by
        simpa [base] using (hasDerivAt_id (0 : ℝ)).smul_const d.1
      have heigenvalue : HasDerivAt (fun t : ℝ => (base + t • d).2.1) d.2.1 0 := by
        simpa [base, add_comm] using
          ((hasDerivAt_id (0 : ℝ)).smul_const d.2.1).const_add lambda0
      have heigenvector : HasDerivAt (fun t : ℝ => (base + t • d).2.2) d.2.2 0 := by
        simpa [base, add_comm] using
          ((hasDerivAt_id (0 : ℝ)).smul_const d.2.2).const_add right
      have hALine : HasDerivAt (fun t : ℝ => A ((base + t • d).1))
          (d.1 • Aderiv) 0 := by
        simpa [Function.comp_def] using
          hAderiv.scomp_of_eq 0 hparam (by simp [base])
      have hnormalLine : HasDerivAt
          (fun t : ℝ => left (base + t • d).2.2) (left d.2.2) 0 := by
        exact (left.hasFDerivAt : HasFDerivAt left left right).comp_hasDerivAt_of_eq
          0 heigenvector (by simp [base])
      have hoperatorLine : HasDerivAt
          (fun t : ℝ => A ((base + t • d).1) (base + t • d).2.2)
          (d.1 • vderiv + A 0 d.2.2) 0 := by
        have h := (ContinuousLinearMap.flip (ContinuousLinearMap.apply ℝ V)).hasFDerivAt_of_bilinear
          hALine.hasFDerivAt heigenvector.hasFDerivAt
        convert h.hasDerivAt using 1
        simp [base, vderiv, add_comm]
      have hscalarLine : HasDerivAt
          (fun t : ℝ => (base + t • d).2.1 • (base + t • d).2.2)
          (d.2.1 • right + lambda0 • d.2.2) 0 := by
        convert heigenvalue.smul heigenvector using 1
        simp [base, add_comm]
      have hcombined := hparam.prodMk
        (hnormalLine.prodMk (hoperatorLine.sub hscalarLine))
      convert hcombined using 1
    have hcanonical := hPhi_analytic.differentiableAt.hasFDerivAt
    have hderiv_eq : fderiv ℝ Phi base =
        (jacobian : (ℝ × (ℝ × V)) →L[ℝ] (ℝ × (ℝ × V))) := by
      apply ContinuousLinearMap.ext
      intro d
      let line : ℝ → ℝ × (ℝ × V) := fun t => base + t • d
      have hlineDeriv : HasDerivAt line d 0 := by
        simpa [line] using ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add base
      have hcomp := hcanonical.comp_hasDerivAt_of_eq 0 hlineDeriv (by simp [line])
      have hline' := hline d
      rw [hraw_eq d] at hline'
      exact hcomp.unique (by simpa [Function.comp_def, line] using hline')
    rw [← hderiv_eq]
    exact hcanonical
  have hPhi_strict : HasStrictFDerivAt Phi
      (jacobian : (ℝ × (ℝ × V)) →L[ℝ] (ℝ × (ℝ × V))) base := by
    have h := hPhi_analytic.hasStrictFDerivAt
    convert h using 1
    exact hPhi_deriv.fderiv.symm
  let H : OpenPartialHomeomorph (ℝ × (ℝ × V)) (ℝ × (ℝ × V)) :=
    hPhi_strict.toOpenPartialHomeomorph Phi
  have hbase_source : base ∈ H.source :=
    hPhi_strict.mem_toOpenPartialHomeomorph_source
  have htarget_target : target ∈ H.target := by
    rw [← hPhi_base]
    exact H.map_source hbase_source
  let embed : ℝ → ℝ × (ℝ × V) := fun alpha => (alpha, (1, 0))
  have hembed0 : embed 0 = target := rfl
  have hinv_analytic : AnalyticAt ℝ H.symm target := by
    rw [← hPhi_base]
    apply H.analyticAt_symm'
    · exact hbase_source
    · simpa [H] using hPhi_analytic
    · simpa [H] using hPhi_deriv.fderiv
  have hembed_analytic : AnalyticAt ℝ embed 0 := by fun_prop
  have hbranch_analytic : AnalyticAt ℝ (fun alpha => H.symm (embed alpha)) 0 :=
    hinv_analytic.comp_of_eq' hembed_analytic hembed0
  let gamma : ℝ → ℝ := fun alpha => (H.symm (embed alpha)).2.1
  let r : ℝ → V := fun alpha => (H.symm (embed alpha)).2.2
  have hbase_inverse : H.symm target = base := by
    rw [← hPhi_base]
    exact H.left_inv hbase_source
  have hgamma0 : gamma 0 = lambda0 := by
    simp [gamma, hembed0, hbase_inverse, base]
  have hr0 : r 0 = right := by
    simp [r, hembed0, hbase_inverse, base]
  have hgamma_analytic : AnalyticAt ℝ gamma 0 :=
    analyticAt_fst.comp' (analyticAt_snd.comp' hbranch_analytic)
  have hr_analytic : AnalyticAt ℝ r 0 :=
    analyticAt_snd.comp' (analyticAt_snd.comp' hbranch_analytic)
  have hembed_tendsto : Tendsto embed (𝓝 0) (𝓝 (Phi base)) := by
    rw [hPhi_base, ← hembed0]
    exact hembed_analytic.continuousAt
  have hright_inverse : ∀ᶠ alpha : ℝ in 𝓝 0,
      Phi (H.symm (embed alpha)) = embed alpha :=
    hembed_tendsto.eventually hPhi_strict.eventually_right_inverse
  refine ⟨gamma, r, hgamma0, hr0, ?_⟩
  filter_upwards [hgamma_analytic.eventually_analyticAt,
    hr_analytic.eventually_analyticAt, hright_inverse] with alpha hga hra hinv
  have hnormal := congrArg (fun x => x.2.1) hinv
  have heigen := congrArg (fun x => x.2.2) hinv
  have hparameter := congrArg Prod.fst hinv
  have hparameter' : (H.symm (embed alpha)).1 = alpha := by
    simpa [embed] using hparameter
  refine ⟨hga, hra, ?_, ?_⟩
  · have heigen' :
        A (H.symm (embed alpha)).1 (H.symm (embed alpha)).2.2 =
          (H.symm (embed alpha)).2.1 • (H.symm (embed alpha)).2.2 :=
      sub_eq_zero.mp (by simpa [Phi, embed] using heigen)
    rw [hparameter'] at heigen'
    simpa [gamma, r] using heigen'
  · simpa [Phi, embed, r] using hnormal

end ContinuousLinearMap

/-! Promoted from Staging/ContinuousLinearMap_exists_eventually_analytic_normalized_eigenbranch_of_algebraicallySimple.lean. -/

open Filter Topology

namespace ContinuousLinearMap

-- Generalization plan (G0):
-- concept/name: eventual analytic normalized eigenbranch from a normalized simple
--   eigenpair; orig was analytic_normalized_right_eigenbranch_eventually
-- generality used: an arbitrary finite-dimensional real Banach space, an analytic
--   continuous-endomorphism family, a base eigenvalue/eigenvector, and a continuous
--   left eigenfunctional; no coordinates, matrices, or inner-product structure
-- portable call pattern: spectral perturbation steps for stochastic transition,
--   mixing, preconditioner, and Hessian operator families vary the analytic family,
--   simple eigenvalue, and normalized left-right eigenpair while retaining the same
--   local analytic normalized eigenbranch conclusion
-- counterargument checked: this is not paper-local traceability or a pure rename;
--   it composes the reusable bordered-invertibility argument with the analytic
--   inverse-function construction, and neither Mathlib nor SOptLib exposes the
--   resulting one-call eigenbranch theorem
-- coverage search: lean_search_symbols queries “analytic normalized eigenvalue
--   eigenvector branch algebraically simple eigenpair”, “eventually analytic
--   eigenbranch left eigenvector normalized simple eigenspace”, and “bordered
--   eigenpair equivalence normalized simple eigenpair” found only the two component
--   staging theorems; LeanSearch queries for analytic branches at simple eigenvalues
--   found general analytic-map APIs but no eigenpair continuation theorem
-- minimal hypotheses: AnalyticAt at the base point replaces interval-wide
--   analyticity; only spanning of the ordinary eigenspace is used from algebraic
--   simplicity, while finite dimensionality is retained for bordered surjectivity

/-- An analytic finite-dimensional operator family admits a locally analytic normalized
eigenpair branch from a normalized left-right eigenpair whose right vector spans the
base eigenspace.

Layer: Glue | Gap: Level 2 (analytic normalized eigenbranch from a simple eigenpair)
Proof: construct the bordered eigenpair equivalence from the left eigenfunctional and
  one-dimensional eigenspace, then apply the analytic inverse-function eigenbranch theorem.
Source: Mathlib finite-dimensional eigenspaces, continuous linear equivalences, analytic maps, and the Banach-space inverse function theorem
Used in: local spectral perturbation of stochastic mixing and transition operators around a normalized simple Perron mode, with analogous calls for preconditioner and Hessian families
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12/proof/2
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem exists_eventually_analytic_normalized_eigenbranch_of_algebraicallySimple
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (A : ℝ → (V →L[ℝ] V)) (lambda0 : ℝ) (right : V)
    (left : V →L[ℝ] ℝ)
    (hA : AnalyticAt ℝ A 0)
    (hright : A 0 right = lambda0 • right)
    (hleft : ∀ v : V, left (A 0 v) = lambda0 * left v)
    (hnormalized : left right = 1)
    (hspan : ∀ v : V, A 0 v = lambda0 • v → ∃ c : ℝ, v = c • right) :
    ∃ gamma : ℝ → ℝ, ∃ r : ℝ → V,
      gamma 0 = lambda0 ∧ r 0 = right ∧
        ∀ᶠ alpha : ℝ in 𝓝 0,
          AnalyticAt ℝ gamma alpha ∧ AnalyticAt ℝ r alpha ∧
            A alpha (r alpha) = gamma alpha • r alpha ∧
            left (r alpha) = 1 := by
  obtain ⟨bordered, hbordered⟩ :=
    ContinuousLinearMap.exists_borderedEigenpairEquiv_of_simpleEigenpair
      (A 0) lambda0 right left hleft hnormalized hspan
  exact
    ContinuousLinearMap.exists_eventually_analytic_normalized_eigenbranch_of_borderedEquiv
      A lambda0 right left hA hright hnormalized bordered hbordered

end ContinuousLinearMap

/-! Promoted from Staging/eventually_eq_pos_mul_inv_sqrt_rate_package.lean. -/

open Filter Topology

-- Generalization plan (G0):
-- concept/name: asymptotic rate package for a sequence eventually equal to a
--   positive constant times the inverse square root; orig was
--   balancing_inv_sqrt_rate_package_block
-- generality used: an arbitrary real sequence on natural horizons and a
--   positive real scaling constant; no measure, convexity, smoothness, oracle,
--   normed-space, or finite-dimensional assumptions are used
-- portable call pattern: balancing-stepsize and diminishing-stepsize proofs
--   vary the positive constant and stepsize sequence while reusing eventual
--   positivity, decay, horizon-product divergence, and the two-term Big-O rate
-- counterargument checked: this is not paper-local traceability or a one-line
--   wrapper; it packages four jointly recurring consequences and the Big-O
--   conclusion requires nontrivial inverse-square-root algebra
-- coverage search: searched `eventually equal positive constant times inverse
--   square root implies eventually positive tends to zero product tends to
--   infinity and two term big O`, `inverse square root sequence product tends
--   to infinity big O inverse square root`, and the full contract with Mathlib
--   LeanSearch; only generic limit and Big-O primitives were found, with no
--   SOptLib or Mathlib theorem covering the complete package
-- minimal hypotheses: eventual equality and positivity of the scaling constant
--   are exactly what all four conclusions use

/-- A sequence eventually equal to a positive constant times the inverse square
root is eventually positive, tends to zero, has horizon product tending to
positive infinity, and its inverse-product-plus-value scale is
`O(T⁻¹ᐟ²)`.

Layer: Glue | Gap: Level 1 (inverse-square-root diminishing-rate package)
Proof: transfer the standard square-root limits through eventual equality, rewrite the horizon product using `sqrt(T)^2 = T`, and prove the Big-O estimate by an eventual exact constant-multiple identity.
Source: Mathlib real square-root limits, filter convergence at infinity, and asymptotic Big-O bounds
Used in: balancing-stepsize analyses that instantiate a positive multiple of the inverse-square-root horizon rate before applying a small-stepsize long-horizon expansion
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/17/proof/13
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem eventually_eq_pos_mul_inv_sqrt_rate_package
    (c : ℝ) (alpha : ℕ → ℝ) (hc : 0 < c)
    (halpha :
      alpha =ᶠ[atTop] fun T : ℕ => c * (Real.sqrt (T : ℝ))⁻¹) :
    (∀ᶠ T : ℕ in atTop, 0 < alpha T) ∧
      Tendsto alpha atTop (nhds 0) ∧
      Tendsto (fun T : ℕ => alpha T * (T : ℝ)) atTop atTop ∧
      Asymptotics.IsBigO atTop
        (fun T : ℕ => (alpha T * (T : ℝ))⁻¹ + alpha T)
        (fun T : ℕ => (Real.sqrt (T : ℝ))⁻¹) := by
  have hsqrt_atTop :
      Tendsto (fun T : ℕ => Real.sqrt (T : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hinv_sqrt_zero :
      Tendsto (fun T : ℕ => (Real.sqrt (T : ℝ))⁻¹) atTop (nhds 0) :=
    hsqrt_atTop.inv_tendsto_atTop
  have halpha_pos : ∀ᶠ T : ℕ in atTop, 0 < alpha T := by
    have hlarge : ∀ᶠ T : ℕ in atTop, 1 ≤ T :=
      eventually_atTop.2 ⟨1, fun T hT => hT⟩
    filter_upwards [halpha, hlarge] with T halphaT hT
    have hT_pos : 0 < (T : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hT)
    rw [halphaT]
    positivity
  have halpha_tendsto : Tendsto alpha atTop (nhds 0) := by
    have hmodel :
        Tendsto (fun T : ℕ => c * (Real.sqrt (T : ℝ))⁻¹)
          atTop (nhds 0) := by
      simpa using Tendsto.const_mul c hinv_sqrt_zero
    exact hmodel.congr' halpha.symm
  have halpha_prod_tendsto :
      Tendsto (fun T : ℕ => alpha T * (T : ℝ)) atTop atTop := by
    have hmodel :
        Tendsto (fun T : ℕ => c * Real.sqrt (T : ℝ)) atTop atTop :=
      hsqrt_atTop.const_mul_atTop hc
    refine hmodel.congr' ?_
    have hlarge : ∀ᶠ T : ℕ in atTop, 1 ≤ T :=
      eventually_atTop.2 ⟨1, fun T hT => hT⟩
    filter_upwards [halpha, hlarge] with T halphaT hT
    have hT_pos : 0 < (T : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hT)
    have hsqrtT_ne : Real.sqrt (T : ℝ) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 hT_pos)
    have hsqrt_sq : Real.sqrt (T : ℝ) ^ 2 = (T : ℝ) :=
      Real.sq_sqrt hT_pos.le
    rw [halphaT]
    field_simp [hsqrtT_ne]
    rw [hsqrt_sq]
  have halpha_scale_bigO :
      Asymptotics.IsBigO atTop
        (fun T : ℕ => (alpha T * (T : ℝ))⁻¹ + alpha T)
        (fun T : ℕ => (Real.sqrt (T : ℝ))⁻¹) := by
    let C : ℝ := c⁻¹ + c
    have hC_nonneg : 0 ≤ C := by
      dsimp [C]
      exact add_nonneg (inv_nonneg.mpr hc.le) hc.le
    refine Asymptotics.IsBigO.of_bound C ?_
    have hlarge : ∀ᶠ T : ℕ in atTop, 1 ≤ T :=
      eventually_atTop.2 ⟨1, fun T hT => hT⟩
    filter_upwards [halpha, hlarge] with T halphaT hT
    have hT_pos : 0 < (T : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hT)
    have hsqrtT_pos : 0 < Real.sqrt (T : ℝ) :=
      Real.sqrt_pos.2 hT_pos
    have hsqrtT_ne : Real.sqrt (T : ℝ) ≠ 0 := ne_of_gt hsqrtT_pos
    have htarget_nonneg : 0 ≤ (Real.sqrt (T : ℝ))⁻¹ :=
      inv_nonneg.mpr hsqrtT_pos.le
    have hscale_eq :
        (alpha T * (T : ℝ))⁻¹ + alpha T =
          C * (Real.sqrt (T : ℝ))⁻¹ := by
      have hsqrt_sq : Real.sqrt (T : ℝ) ^ 2 = (T : ℝ) :=
        Real.sq_sqrt hT_pos.le
      rw [halphaT]
      dsimp [C]
      field_simp [ne_of_gt hc, hsqrtT_ne]
      ring_nf
      rw [hsqrt_sq]
      ring
    rw [Real.norm_eq_abs, Real.norm_eq_abs, hscale_eq,
      abs_of_nonneg htarget_nonneg,
      abs_of_nonneg (mul_nonneg hC_nonneg htarget_nonneg)]
  exact ⟨halpha_pos, halpha_tendsto, halpha_prod_tendsto,
    halpha_scale_bigO⟩

/-! Promoted from Staging/sum_block_norm_sq_map_average_le_start_add_path_energy_of_lipschitz.lean. -/

open scoped BigOperators

-- Generalization plan (G0):
-- concept/name: finite-block squared output-energy bound for a Lipschitz map of arithmetic averages; orig was block_averageGradient_energy_bound
-- generality used: a nonempty finite index type, a real seminormed space for the averaged path, a seminormed additive group for the map output, and Mathlib's canonical LipschitzWith predicate; no measure, inner product, completeness, commutativity of the codomain, or finite-dimensional assumption
-- portable call pattern: periodic and epoch-based distributed methods compare a Lipschitz observable along within-block arithmetic-average iterates with its block-start value while the finite node family, block length, state path, observable, and Lipschitz constant vary
-- counterargument checked: this is not paper-local traceability or a one-line wrapper because it composes finite-family Jensen, coordinatewise path telescoping, finite-range monotonicity, the Lipschitz estimate, and block aggregation into one reusable energy contract
-- coverage search: searched `finite block sum squared norm Lipschitz map arithmetic average bounded by start value and path increment energy`, `sum range norm squared map average upper bound path displacement energy Lipschitz`, and Mathlib semantic equivalents; `norm_sq_inv_card_smul_sum_le_inv_card_mul_sum_norm_sq`, `sq_sum_le_card_mul_sum_sq`, and `lipschitzWith_iff_norm_sub_le` cover constituents only, not the complete block conclusion
-- minimal hypotheses: the source's Hilbert, complete, and finite-dimensional structures are unused; component-gradient smoothness is reduced to the canonical LipschitzWith bound actually consumed, and the codomain needs no commutativity

/-- Over a finite block, the squared output energy of a Lipschitz map applied to
arithmetic averages is controlled by its block-start output and the nodewise
squared path-increment energy.

Layer: Glue | Gap: Level 1 (finite-block Lipschitz output energy from averaged path increments)
Proof: bound every averaged displacement by finite-family Jensen and a telescoping-path Cauchy--Schwarz estimate, transfer it through the pointwise Lipschitz bound and a two-term norm-square inequality, then sum over the block.
Source: Mathlib finite sums, normed-space triangle inequalities, and Chebyshev finite-sum square inequality; SOptLib finite-average squared-norm Jensen bound
Used in: periodic and epoch-based distributed optimization when all within-block observable energies must be charged to the block-start observable and the distributed state path energy
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/6/proof/17
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem sum_block_norm_sq_map_average_le_start_add_path_energy_of_lipschitz
    {I E F : Type*} [Fintype I] [Nonempty I]
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] [SeminormedAddGroup F]
    (X : ℕ → I → E) (g : E → F) (s p : ℕ) (K : NNReal)
    (hg : LipschitzWith K g) :
    ∑ r ∈ Finset.range p,
        ‖g (((Fintype.card I : ℝ)⁻¹ • ∑ i : I, X (s + r) i))‖ ^ 2 ≤
      2 * (p : ℝ) *
          ‖g (((Fintype.card I : ℝ)⁻¹ • ∑ i : I, X s i))‖ ^ 2 +
        (2 * (K : ℝ) ^ 2 * (p : ℝ) ^ 2 / (Fintype.card I : ℝ)) *
          ∑ j ∈ Finset.range p, ∑ i : I,
            ‖X (s + j + 1) i - X (s + j) i‖ ^ 2 := by
  classical
  let avg : ℕ → E := fun t =>
    ((Fintype.card I : ℝ)⁻¹) • ∑ i : I, X t i
  let D : ℝ := ∑ j ∈ Finset.range p, ∑ i : I,
    ‖X (s + j + 1) i - X (s + j) i‖ ^ 2
  have hn : 0 < (Fintype.card I : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hD : 0 ≤ D := by
    dsimp [D]
    positivity
  have havg (r : ℕ) (hr : r ∈ Finset.range p) :
      ‖avg (s + r) - avg s‖ ^ 2 ≤
        ((p : ℝ) / (Fintype.card I : ℝ)) * D := by
    have hrle : r ≤ p := Nat.le_of_lt (Finset.mem_range.mp hr)
    have hcoord (i : I) :
        X (s + r) i - X s i =
          ∑ j ∈ Finset.range r,
            (X (s + j + 1) i - X (s + j) i) := by
      simpa [Nat.add_assoc] using
        (Finset.sum_range_sub (fun j => X (s + j) i) r).symm
    have hpoint (i : I) :
        ‖X (s + r) i - X s i‖ ^ 2 ≤
          (r : ℝ) * ∑ j ∈ Finset.range r,
            ‖X (s + j + 1) i - X (s + j) i‖ ^ 2 := by
      rw [hcoord]
      have hnorm :
          ‖∑ j ∈ Finset.range r,
              (X (s + j + 1) i - X (s + j) i)‖ ≤
            ∑ j ∈ Finset.range r,
              ‖X (s + j + 1) i - X (s + j) i‖ :=
        norm_sum_le _ _
      have hsquares := sq_sum_le_card_mul_sum_sq
        (s := Finset.range r)
        (f := fun j => ‖X (s + j + 1) i - X (s + j) i‖)
      simp only [Finset.card_range] at hsquares
      nlinarith [norm_nonneg (∑ j ∈ Finset.range r,
        (X (s + j + 1) i - X (s + j) i))]
    have hstate :
        ∑ i : I, ‖X (s + r) i - X s i‖ ^ 2 ≤ (p : ℝ) * D := by
      calc
        ∑ i : I, ‖X (s + r) i - X s i‖ ^ 2 ≤
            ∑ i : I, (r : ℝ) * ∑ j ∈ Finset.range r,
              ‖X (s + j + 1) i - X (s + j) i‖ ^ 2 :=
          Finset.sum_le_sum fun i _hi => hpoint i
        _ = (r : ℝ) * ∑ j ∈ Finset.range r, ∑ i : I,
              ‖X (s + j + 1) i - X (s + j) i‖ ^ 2 := by
          rw [Finset.sum_comm, Finset.mul_sum]
        _ ≤ (r : ℝ) * D := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          dsimp [D]
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hrle)
          intro j _hj _hjr
          positivity
        _ ≤ (p : ℝ) * D :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hrle) hD
    have havgJensen :=
      norm_sq_inv_card_smul_sum_le_inv_card_mul_sum_norm_sq
        (Finset.univ : Finset I)
        (fun i : I => X (s + r) i - X s i)
        (by simp [Fintype.card_pos])
    calc
      ‖avg (s + r) - avg s‖ ^ 2 =
          ‖((Fintype.card I : ℝ)⁻¹ •
            ∑ i : I, (X (s + r) i - X s i))‖ ^ 2 := by
        dsimp [avg]
        rw [← smul_sub, ← Finset.sum_sub_distrib]
      _ ≤ (Fintype.card I : ℝ)⁻¹ *
          ∑ i : I, ‖X (s + r) i - X s i‖ ^ 2 := by
        simpa only [Finset.card_univ] using havgJensen
      _ ≤ (Fintype.card I : ℝ)⁻¹ * ((p : ℝ) * D) :=
        mul_le_mul_of_nonneg_left hstate (inv_nonneg.mpr hn.le)
      _ = ((p : ℝ) / (Fintype.card I : ℝ)) * D := by
        rw [div_eq_mul_inv]
        ring
  have hpoint (r : ℕ) (hr : r ∈ Finset.range p) :
      ‖g (avg (s + r))‖ ^ 2 ≤
        2 * ‖g (avg s)‖ ^ 2 +
          (2 * (K : ℝ) ^ 2 * (p : ℝ) / (Fintype.card I : ℝ)) * D := by
    let gt := g (avg (s + r))
    let gs := g (avg s)
    have hdiff : dist gt gs ^ 2 ≤
        (K : ℝ) ^ 2 * ‖avg (s + r) - avg s‖ ^ 2 := by
      have hlip := hg.dist_le_mul (avg (s + r)) (avg s)
      dsimp [gt, gs]
      simpa only [dist_eq_norm, mul_pow] using
        ((sq_le_sq₀ (dist_nonneg : 0 ≤ dist (g (avg (s + r))) (g (avg s)))
          (mul_nonneg K.coe_nonneg dist_nonneg)).2 hlip)
    have hdiff' : dist gt gs ^ 2 ≤
        (K : ℝ) ^ 2 * (((p : ℝ) / (Fintype.card I : ℝ)) * D) :=
      hdiff.trans (mul_le_mul_of_nonneg_left (havg r hr) (sq_nonneg (K : ℝ)))
    have htri : ‖gt‖ ≤ dist gt gs + ‖gs‖ := by
      simpa only [dist_zero_right] using dist_triangle gt gs 0
    have hsquare : ‖gt‖ ^ 2 ≤ 2 * dist gt gs ^ 2 + 2 * ‖gs‖ ^ 2 := by
      nlinarith [norm_nonneg gt, (dist_nonneg : 0 ≤ dist gt gs), norm_nonneg gs,
        sq_nonneg (dist gt gs - ‖gs‖)]
    calc
      _ ≤ 2 * dist gt gs ^ 2 + 2 * ‖gs‖ ^ 2 := hsquare
      _ ≤ 2 * ((K : ℝ) ^ 2 *
            (((p : ℝ) / (Fintype.card I : ℝ)) * D)) + 2 * ‖gs‖ ^ 2 :=
        add_le_add (mul_le_mul_of_nonneg_left hdiff' (by norm_num)) le_rfl
      _ = _ := by
        dsimp [gt, gs]
        ring
  change ∑ r ∈ Finset.range p, ‖g (avg (s + r))‖ ^ 2 ≤ _
  calc
    ∑ r ∈ Finset.range p, ‖g (avg (s + r))‖ ^ 2 ≤
        ∑ _r ∈ Finset.range p,
          (2 * ‖g (avg s)‖ ^ 2 +
            (2 * (K : ℝ) ^ 2 * (p : ℝ) / (Fintype.card I : ℝ)) * D) :=
      Finset.sum_le_sum fun r hr => hpoint r hr
    _ = 2 * (p : ℝ) * ‖g (avg s)‖ ^ 2 +
        (2 * (K : ℝ) ^ 2 * (p : ℝ) ^ 2 / (Fintype.card I : ℝ)) * D := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring
    _ = _ := by
      rfl

/-! Promoted from Staging/circleIntegral_integral_sub_inv_of_not_mem_closedBall.lean. -/

open MeasureTheory

-- Generalization plan (G0):
-- concept/name: vanishing circle integral of a simple pole outside the closed disk; orig was `circleIntegral_sub_inv_eq_zero_of_not_mem_closedBall`.
-- generality used: arbitrary complex center and pole and arbitrary nonnegative real radius; no algorithm setup, measure assumption, finite-dimensional space, convexity, smoothness, or oracle hypothesis is used.
-- portable call pattern: contour and Riesz-projection proofs vary the center, radius, and exterior pole while discarding resolvent partial-fraction terms whose poles lie outside the contour.
-- counterargument checked: this is not paper-local traceability or a pure rename; Mathlib provides the interior-pole evaluation and the general Cauchy--Goursat theorem, but not the exterior simple-pole specialization that discharges continuity, differentiability, and boundary nonvanishing obligations.
-- coverage search: `lean_search_symbols` query "circle integral inverse difference equals zero pole outside closed ball" found no matching SOptLib or Mathlib declaration; `lean_leansearch` query "circle integral of one over z minus pole is zero if pole is outside the closed ball bounded by the circle" found `Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable` and `circleIntegral.integral_sub_inv_of_mem_ball`, which are respectively a general proof ingredient and the complementary interior-pole formula, not duplicates.
-- minimal hypotheses: nonnegativity of the radius is required by the disk Cauchy--Goursat API, and exclusion of the pole from the closed ball is exactly what supplies nonvanishing on both the closed disk and its interior.

/-- The circle integral of a simple pole vanishes when the pole lies outside the
closed disk bounded by the circle.

Layer: Glue | Gap: Level 1 (exterior simple-pole circle-integral vanishing)
Proof: apply the disk Cauchy--Goursat theorem with no exceptional points; exterior closed-ball membership makes subtraction nonzero and hence inversion differentiable throughout the disk and continuous on its closure.
Source: Mathlib complex Cauchy--Goursat theorem for disks and complex differentiability of inversion away from zero
Used in: contour and Riesz-projection calculations that discard partial-fraction terms associated with spectral poles outside a selected circle
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12/proof/1
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem circleIntegral.integral_sub_inv_of_not_mem_closedBall
    {center pole : ℂ} {radius : ℝ} (hradius_nonneg : 0 ≤ radius)
    (hpole : pole ∉ Metric.closedBall center radius) :
    (∮ z in C(center, radius), (z - pole)⁻¹) = 0 := by
  refine
    Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
      hradius_nonneg (s := (∅ : Set ℂ)) Set.countable_empty ?_ ?_
  · intro z hz
    have hzw : z ≠ pole := by
      intro hzp
      exact hpole (by simpa [hzp] using hz)
    have hsub_ne : z - pole ≠ 0 := sub_ne_zero.mpr hzw
    have hsub_diff :
        DifferentiableAt ℂ (fun y : ℂ ↦ y - pole) z :=
      differentiableAt_id.sub
        (differentiableAt_const (𝕜 := ℂ) (c := pole) (x := z))
    exact
      ((differentiableAt_inv hsub_ne).comp z hsub_diff).continuousAt.continuousWithinAt
  · intro z hz
    have hzclosed : z ∈ Metric.closedBall center radius :=
      Metric.mem_closedBall.2 (le_of_lt (Metric.mem_ball.mp hz.1))
    have hzw : z ≠ pole := by
      intro hzp
      exact hpole (by simpa [hzp] using hzclosed)
    have hsub_ne : z - pole ≠ 0 := sub_ne_zero.mpr hzw
    have hsub_diff :
        DifferentiableAt ℂ (fun y : ℂ ↦ y - pole) z :=
      differentiableAt_id.sub
        (differentiableAt_const (𝕜 := ℂ) (c := pole) (x := z))
    exact (differentiableAt_inv hsub_ne).comp z hsub_diff

/-! Promoted from Staging/Matrix_analyticAt_det_of_entrywise.lean. -/

-- Generalization plan (G0):
-- concept/name: entrywise analyticity implies determinant analyticity; orig was
--   `complexMatrix_det_analyticAt_alpha`, renamed `Matrix.analyticAt_det_of_entrywise`
-- generality used: an arbitrary nontrivially normed scalar field, normed domain,
--   normed commutative target algebra, and finite square-matrix index type
-- portable call pattern: analytic perturbation and contour-resolvent arguments can
--   vary the parameter space, scalar field, coefficient algebra, and finite index type
-- counterargument checked: this is not paper-local or a pure wrapper; Mathlib has
--   `Continuous.matrix_det` but no analytic determinant closure theorem, and the proof
--   substantively combines determinant expansion with finite analytic sums and products
-- coverage search: queries "matrix determinant analytic entrywise analytic",
--   "analytic determinant of matrix-valued function", and "AnalyticAt matrix det
--   entries" found only the paper-local copies; Mathlib semantic search found the
--   partial hits `Continuous.matrix_det` and `Finset.analyticAt_fun_prod`
-- minimal hypotheses: `Fintype` and `DecidableEq` for the determinant, with exactly
--   the normed field, normed space, normed commutative ring, and normed algebra classes
--   required by `AnalyticAt` and its finite sum/product closure lemmas

namespace Matrix

/-- The determinant of a finite square-matrix family is analytic at a point when
every matrix entry is analytic there.

Layer: Glue | Gap: Level 1 (determinant analyticity from entrywise analyticity)
Proof: expand the determinant as its signed permutation sum, then apply Mathlib's finite analytic sum and product closure lemmas to the analytic entries.
Source: Mathlib `Matrix.det_apply'`, `Finset.analyticAt_fun_sum`, and `Finset.analyticAt_fun_prod`
Used in: analytic matrix perturbations and contour-resolvent constructions where determinant nonvanishing controls analytic inverse entries
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12/proof/1
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem analyticAt_det_of_entrywise
    {𝕜 𝕜' X κ : Type*}
    [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedCommRing 𝕜'] [NormedAlgebra 𝕜 𝕜']
    [Fintype κ] [DecidableEq κ]
    (M : X → Matrix κ κ 𝕜') {x₀ : X}
    (hM : ∀ i j : κ, AnalyticAt 𝕜 (fun x : X => M x i j) x₀) :
    AnalyticAt 𝕜 (fun x : X => (M x).det) x₀ := by
  classical
  simpa [Matrix.det_apply'] using
    Finset.analyticAt_fun_sum
      (Finset.univ : Finset (Equiv.Perm κ)) (fun σ _hσ =>
      analyticAt_const.mul
        (Finset.analyticAt_fun_prod Finset.univ (fun i _hi =>
          hM (σ i) i)))

end Matrix

/-! Promoted from Staging/Matrix_analyticAt_adjugate_apply_of_entrywise.lean. -/

-- Generalization plan (G0):
-- concept/name: entrywise analyticity implies analyticity of each adjugate entry;
--   orig was `complexMatrix_adjugate_entry_analyticAt_alpha`, renamed
--   `Matrix.analyticAt_adjugate_apply_of_entrywise`
-- generality used: an arbitrary nontrivially normed scalar field, normed parameter
--   space, normed commutative target algebra, and finite square-matrix index type
-- portable call pattern: analytic inverse, cofactor, and contour-resolvent proofs can
--   vary the parameter space, scalar field, coefficient algebra, matrix family, and
--   requested entry while reusing the same adjugate-entry analyticity conclusion
-- counterargument checked: this is not paper-local or a pure rename; Mathlib exposes
--   the adjugate entry as an updated-row determinant and proves continuous adjugate
--   closure, but has no analytic closure theorem for an adjugate entry
-- coverage search: queries "matrix adjugate entry analytic at from entrywise analytic",
--   "adjugate entry equals determinant updated row", and the Mathlib semantic query
--   "entries of the adjugate of a finite matrix-valued analytic function are analytic"
--   found `Matrix.adjugate_apply`, `Continuous.matrix_adjugate`, and the reusable
--   `Matrix.analyticAt_det_of_entrywise`, but no public theorem with this conclusion;
--   related staged contour proofs contain only private specialized copies
-- minimal hypotheses: `Fintype` and `DecidableEq` support adjugate and row update;
--   all normed field, space, commutative ring, and algebra classes are inherited from
--   the determinant analyticity theorem, with only pointwise entry analyticity assumed

namespace Matrix

/-- Every entry of the adjugate of a finite square-matrix family is analytic at a
point when all entries of the original family are analytic there.

Layer: Glue | Gap: Level 1 (adjugate-entry analyticity from entrywise analyticity)
Proof: rewrite the requested adjugate entry as the determinant of a constant-row update, prove that update entrywise analytic by cases on its row, and apply `Matrix.analyticAt_det_of_entrywise`.
Source: Mathlib `Matrix.adjugate_apply`, `Matrix.updateRow`, and analytic constants, composed with `Matrix.analyticAt_det_of_entrywise`
Used in: analytic inverse, cofactor, and contour-resolvent arguments for finite matrix families, where inverse entries are expressed through an adjugate and a nonvanishing determinant
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12/proof/1
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem analyticAt_adjugate_apply_of_entrywise
    {𝕜 𝕜' X κ : Type*}
    [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedCommRing 𝕜'] [NormedAlgebra 𝕜 𝕜']
    [Fintype κ] [DecidableEq κ]
    (M : X → Matrix κ κ 𝕜') {x₀ : X}
    (hM : ∀ i j : κ, AnalyticAt 𝕜 (fun x : X => M x i j) x₀)
    (i j : κ) :
    AnalyticAt 𝕜 (fun x : X => (M x).adjugate i j) x₀ := by
  classical
  simpa [Matrix.adjugate_apply] using
    (Matrix.analyticAt_det_of_entrywise
      (fun x : X => (M x).updateRow j (Pi.single i (1 : 𝕜')))
      (x₀ := x₀) (by
        intro r c
        by_cases hr : r = j
        · subst r
          simpa [Matrix.updateRow] using
            (analyticAt_const (𝕜 := 𝕜) (E := X) (F := 𝕜')
              (v := ((Pi.single i (1 : 𝕜') : κ → 𝕜') c)) (x := x₀))
        · simpa [Matrix.updateRow, hr] using hM r c))

end Matrix

/-! Promoted from Staging/Matrix_analyticAt_inv_apply_of_entrywise_of_det_ne_zero.lean. -/

-- Generalization plan (G0):
-- concept/name: entrywise analyticity and determinant nonvanishing imply
--   analyticity of each inverse-matrix entry; orig was
--   `complexMatrix_inv_entry_analyticAt_alpha_of_det_ne_zero`, renamed
--   `Matrix.analyticAt_inv_apply_of_entrywise_of_det_ne_zero`
-- generality used: arbitrary nontrivially normed parameter and coefficient
--   fields, a normed parameter space, a normed algebra structure between the
--   fields, and an arbitrary finite square-matrix index type
-- portable call pattern: resolvent, implicit finite linear-system,
--   preconditioner, and matrix-perturbation proofs vary the analytic parameter
--   family, scalar fields, finite index type, base point, and requested entry
--   while retaining determinant nonvanishing and inverse-entry analyticity
-- counterargument checked: this is not paper-local or a pure wrapper; it
--   composes determinant and adjugate analytic closure, scalar inversion away
--   from zero, and Mathlib's adjugate-over-determinant matrix inverse formula
-- coverage search: symbol queries "matrix inverse entry analytic at entrywise
--   analytic determinant nonzero" and "analytic inverse matrix determinant
--   nonzero finite matrix family" found only paper-local and private copies plus
--   the staged determinant/adjugate components; Mathlib semantic search found
--   scalar `AnalyticAt.inv` but no theorem for entries of a finite matrix inverse
-- minimal hypotheses: entrywise analyticity is pointwise at the requested base
--   point and determinant nonvanishing is required only there; `Fintype` and
--   `DecidableEq` support determinant, adjugate, and nonsingular matrix inverse

namespace Matrix

/-- Each entry of the inverse of a finite square-matrix family is analytic at a
point where every original entry is analytic and the determinant is nonzero.

Layer: Glue | Gap: Level 1 (inverse-entry analyticity from entrywise analyticity and local nonsingularity)
Proof: combine determinant and adjugate-entry analyticity, invert the nonvanishing determinant analytically, and rewrite Mathlib's adjugate-over-determinant formula for matrix inversion.
Source: Mathlib `AnalyticAt.inv` and `Matrix.inv_def`, composed with `Matrix.analyticAt_det_of_entrywise` and `Matrix.analyticAt_adjugate_apply_of_entrywise`
Used in: analytic resolvent perturbations, implicit finite linear systems, and variable preconditioners where local nonsingularity must yield coordinatewise analytic dependence
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12/proof/1
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem analyticAt_inv_apply_of_entrywise_of_det_ne_zero
    {𝕜 𝕜' X κ : Type*}
    [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
    [Fintype κ] [DecidableEq κ]
    (M : X → Matrix κ κ 𝕜') {x₀ : X}
    (hM : ∀ i j : κ, AnalyticAt 𝕜 (fun x : X ↦ M x i j) x₀)
    (hdet : (M x₀).det ≠ 0) (i j : κ) :
    AnalyticAt 𝕜 (fun x : X ↦ (M x)⁻¹ i j) x₀ := by
  classical
  have hinv_det : AnalyticAt 𝕜 (fun x : X ↦ ((M x).det)⁻¹) x₀ :=
    (Matrix.analyticAt_det_of_entrywise M hM).inv hdet
  have hentry :
      AnalyticAt 𝕜
        (fun x : X ↦ ((M x).det)⁻¹ * (M x).adjugate i j) x₀ :=
    hinv_det.mul (Matrix.analyticAt_adjugate_apply_of_entrywise M hM i j)
  simpa [Matrix.inv_def, Pi.smul_apply, smul_eq_mul, Ring.inverse_eq_inv'] using
    hentry

end Matrix

/-! Promoted from Staging/Matrix_eventually_spectrum_norm_lt_of_continuousAt.lean. -/

open Filter
open scoped Topology
section
open scoped Matrix.Norms.Operator

-- Generalization plan (G0):
-- concept/name: eventual strict spectral norm enclosure for a continuous finite
-- matrix family; orig was complexNodeMatrix_spectrum_upperSemicontinuity_norm_lt
-- generality used: arbitrary finite matrix index and topological
-- parameter space, with continuity only at an arbitrary distinguished parameter
-- portable call pattern: matrix perturbation, stability, and contour arguments
-- vary the finite state space, parameter space, base point, family, and enclosing
-- radius while retaining eventual strict containment of every spectral value
-- counterargument checked: this is not paper traceability or a pure rename;
-- Mathlib exposes spectrum upper hemicontinuity but not its strict norm-disk
-- specialization, while the staged closed-exclusion theorem has a different
-- closed-set/disjointness interface
-- coverage search: searches for "spectrum contained open ball eventually
-- continuousAt matrix family" and "spectrum upper hemicontinuous contained in
-- open ball norm less than radius nearby" found the lower-level Mathlib theorem
-- `upperHemicontinuous_spectrum` and the distinct staged theorem
-- `eventually_spectrum_disjoint_closed_of_continuousAt`, but no matching strict
-- norm-enclosure declaration
-- minimal hypotheses: the base-spectrum hypothesis is the pointwise strict bound
-- actually consumed; no auxiliary weak radius, metric parameter space, or global
-- continuity assumption is retained

namespace Matrix

/-- If the spectrum of the base matrix lies strictly inside a norm disk, then
the spectra of a continuous finite complex matrix family eventually lie in the
same disk.

Layer: Glue | Gap: Level 1 (strict spectral norm enclosure under matrix perturbation)
Proof: compose Mathlib's upper hemicontinuity of the spectrum with the matrix
family, then specialize its open-neighborhood conclusion to the strict norm disk.
Source: Mathlib normed-algebra spectrum upper hemicontinuity and norm topology APIs
Used in: perturbation-stable eigenspace splittings and fixed-contour resolvent
arguments that require all nearby eigenvalues to remain inside an enclosing disk
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12/proof/1
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem eventually_spectrum_norm_lt_of_continuousAt
    {κ α : Type*} [Fintype κ] [DecidableEq κ]
    [TopologicalSpace α]
    (G : α → Matrix κ κ ℂ) (a₀ : α) (theta : ℝ)
    (hG : ContinuousAt G a₀)
    (hbase : ∀ z : ℂ, z ∈ spectrum ℂ (G a₀) → ‖z‖ < theta) :
    ∀ᶠ a in 𝓝 a₀, ∀ z : ℂ, z ∈ spectrum ℂ (G a) → ‖z‖ < theta := by
  letI : CompleteSpace (Matrix κ κ ℂ) :=
    FiniteDimensional.complete ℂ (Matrix κ κ ℂ)
  have hspectrum :
      UpperHemicontinuousAt (fun a : α => spectrum ℂ (G a)) a₀ := by
    simpa only [Function.comp_apply] using
      (upperHemicontinuous_spectrum ℂ (Matrix κ κ ℂ)).upperHemicontinuousAt
        (G a₀) |>.comp hG
  exact hspectrum.forall_isOpen
    {z : ℂ | ‖z‖ < theta}
    (isOpen_lt continuous_norm continuous_const)
    hbase

end Matrix

/-! Promoted from Staging/Matrix_continuousOn_inv_of_det_ne_zero.lean. -/

-- Generalization plan (G0):
-- concept/name: continuity on a set of pointwise nonsingular matrix inversion;
--   orig was complexResolventInverse_continuousOn_contour
-- generality used: arbitrary topological parameter space, finite matrix index, and
--   topological field with inversion continuous away from zero; no norm, measure,
--   convexity, smoothness, or oracle assumptions
-- portable call pattern: spectral resolvent, control transfer-matrix, and variable-metric
--   optimization proofs whose continuous matrix family and parameter set change while
--   determinant nonvanishing still yields continuity of the inverse family
-- counterargument checked: not paper-local and not a pure rename; Mathlib supplies the
--   pointwise `continuousAt_matrix_inv` engine but no set-level theorem combining it with
--   `ContinuousOn` and pointwise determinant nonvanishing
-- coverage search: "matrix inverse continuousOn determinant nonzero" and "continuous
--   matrix nonsingular inverse determinant" found `continuousAt_matrix_inv` as partial
--   Mathlib coverage and no matching SOptLib declaration
-- minimal hypotheses: continuity and determinant nonvanishing are pointwise on the set;
--   normed-field and finite-dimensional assumptions were weakened to the topology and
--   inversion-continuity classes actually used

/-- A continuous finite square-matrix family with nonzero determinant on a set has a
continuous pointwise nonsingular inverse on that set.

Layer: Glue | Gap: Level 1 (setwise continuity of nonsingular matrix inversion)
Proof: at each point, use determinant nonvanishing and `ContinuousInv₀` to invoke Mathlib's `continuousAt_matrix_inv`, then compose with the matrix family's within-set continuity.
Source: Mathlib `Topology.Instances.Matrix` and the continuity-away-from-zero API for inversion in topological fields
Used in: spectral-resolvent contour arguments, control transfer-matrix families, and variable-metric optimization proofs that invert a continuous nonsingular finite-matrix family
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12/proof/1
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem Matrix.continuousOn_inv_of_det_ne_zero
    {X K i : Type*} [TopologicalSpace X] [TopologicalSpace K]
    [Field K] [IsTopologicalRing K] [ContinuousInv₀ K]
    [Fintype i] [DecidableEq i]
    (G : X → Matrix i i K) (s : Set X)
    (hG : ContinuousOn G s)
    (hdet : ∀ x ∈ s, Matrix.det (G x) ≠ 0) :
    ContinuousOn (fun x ↦ (G x)⁻¹) s := by
  intro x hx
  have hdetInverse : ContinuousAt Ring.inverse (Matrix.det (G x)) := by
    simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ (hdet x hx)
  exact (continuousAt_matrix_inv (G x) hdetInverse).comp_continuousWithinAt (hG x hx)

end

/-! Promoted from Staging/exists_pos_le_norm_of_isCompact_of_continuousOn_of_ne_zero.lean. -/


-- Generalization plan (G0):
-- concept/name: positive uniform norm lower bound for a nonvanishing continuous map on a nonempty compact set; orig was complexResolvent_base_det_pos_lower_bound_on_shifted_circle
-- generality used: arbitrary topological domain, normed additive codomain, compact nonempty set, continuous-on map, and pointwise nonvanishing on that set
-- portable call pattern: perturbation, coercivity, denominator-control, and spectral resolvent proofs can vary the compact domain, codomain, and continuous map while retaining a strictly positive uniform norm lower bound
-- counterargument checked: this is not paper-local determinant traceability or a pure rename; it packages minimum attainment with strict positivity, while Mathlib exposes only the constituent compact-extreme-value and norm facts
-- coverage search: symbol and semantic searches for compact continuous nonvanishing positive norm lower bounds found Mathlib IsCompact.exists_isMinOn, SOptLib exists_nonneg_norm_bound_of_isCompact_of_continuousOn, and the narrower Seminorm.exists_pos_le_on_unit_sphere_of_separating, but no declaration with this general contract
-- minimal hypotheses: nonemptiness is required for a positive bound, compactness and continuity give an attained minimum, and pointwise nonvanishing is used only at the minimizer; no finite-dimensional, metric, completeness, or measure assumptions are used

/-- A continuous map that does not vanish on a nonempty compact set has a
strictly positive uniform lower bound on the norm of its values.

Layer: Glue | Gap: Level 1 (positive compact nonvanishing norm lower bound)
Proof: minimize the continuous norm on the compact set with `IsCompact.exists_isMinOn`; pointwise nonvanishing makes the attained minimum strictly positive.
Source: Mathlib compact extreme-value theorem and norm-continuity APIs
Used in: spectral resolvent persistence by uniformly separating a base determinant from zero on a compact contour, and in perturbation or denominator-control arguments on compact parameter sets
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12/proof/1
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem exists_pos_le_norm_of_isCompact_of_continuousOn_of_ne_zero
    {X E : Type*} [TopologicalSpace X] [NormedAddGroup E]
    (s : Set X) (f : X → E)
    (hcompact : IsCompact s) (hne : s.Nonempty)
    (hcont : ContinuousOn f s)
    (hf_ne : ∀ x ∈ s, f x ≠ 0) :
    ∃ m : ℝ, 0 < m ∧ ∀ x ∈ s, m ≤ ‖f x‖ := by
  have hnorm : ContinuousOn (fun x : X ↦ ‖f x‖) s := hcont.norm
  obtain ⟨xmin, hxmin, hmin⟩ := hcompact.exists_isMinOn hne hnorm
  refine ⟨‖f xmin‖, norm_pos_iff.mpr (hf_ne xmin hxmin), ?_⟩
  intro x hx
  exact hmin hx

/-! Promoted from Staging/Matrix_eventually_spectrum_disjoint_compact_of_continuousAt.lean. -/


open Filter
open scoped Topology

-- Generalization plan (G0):
-- concept/name: eventual spectral disjointness from a closed exclusion set under a
-- continuous family in a complete normed algebra
-- generality used: arbitrary proper normed field, complete normed algebra,
-- topological parameter space, continuous-at algebra-valued family, and closed
-- spectral exclusion set
-- portable call pattern: resolvent-set and spectral-perturbation arguments vary
-- the scalar field, algebra, parameter space, family, and closed exclusion set
-- while retaining eventual disjointness from the spectrum
-- counterargument checked: Mathlib proves upper hemicontinuity of the spectrum,
-- but does not package its composition with a parameterized family and a closed
-- exclusion set into this eventual disjointness contract
-- coverage search: symbol search for "spectrum disjoint closed set eventually
-- continuousAt upper hemicontinuous" found no matching SOptLib or project
-- declaration; `upperHemicontinuous_spectrum` is the lower-level Mathlib input
-- minimal hypotheses: continuity is needed only at the distinguished parameter;
-- closedness is exactly what makes the complement an open spectral neighborhood

/-- A closed set disjoint from the spectrum of an element remains disjoint from
the spectra of a continuous algebra-valued family eventually at the parameter.

Layer: Glue | Gap: Level 1 (closed spectral-exclusion persistence under perturbation)
Proof: compose Mathlib's upper hemicontinuity of the spectrum with the continuous
family, then use the open complement of the closed exclusion set as a spectral
neighborhood.
Source: Mathlib normed-algebra spectrum upper hemicontinuity and closed-set APIs
Used in: fixed-contour Riesz projections, stable spectral splittings, and
operator perturbation arguments where a closed set must stay in the resolvent
set near a distinguished parameter
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12/proof/1
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem eventually_spectrum_disjoint_closed_of_continuousAt
    {𝕜 A α : Type*} [NormedField 𝕜] [ProperSpace 𝕜]
    [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A]
    [TopologicalSpace α]
    (G : α → A) (a₀ : α) (K : Set 𝕜)
    (hG : ContinuousAt G a₀) (hK : IsClosed K)
    (hdisjoint : Disjoint K (spectrum 𝕜 (G a₀))) :
    ∀ᶠ a in 𝓝 a₀, Disjoint K (spectrum 𝕜 (G a)) := by
  have hspectrum :
      UpperHemicontinuousAt (fun a : α => spectrum 𝕜 (G a)) a₀ := by
    simpa only [Function.comp_apply] using
      (upperHemicontinuous_spectrum 𝕜 A).upperHemicontinuousAt (G a₀) |>.comp hG
  have hat : spectrum 𝕜 (G a₀) ⊆ Kᶜ := by
    intro z hz
    exact hdisjoint.symm.notMem_of_mem_left hz
  filter_upwards [hspectrum.forall_isOpen Kᶜ hK.isOpen_compl hat] with a ha
  exact Set.disjoint_left.2 fun z hzK hz => ha hz hzK

/-! Promoted from Staging/Matrix_circleIntegral_resolvent_apply_eq_of_spectrum_disjoint_annulus.lean. -/


noncomputable section

open MeasureTheory

namespace Matrix

-- Generalization plan (G0):
-- concept/name: entrywise matrix-resolvent circle-integral invariance across a spectrum-disjoint annulus; orig was `complex_resolvent_inv_entry_circleIntegral_eq_of_no_eigen_annulus`.
-- generality used: arbitrary finite index type, complex square matrix, complex contour center, positive inner radius, ordered radii, and pointwise determinant nonvanishing on the closed annulus; no real-matrix origin, algorithm setup, measure, convexity, smoothness, oracle, or extra finite-dimensional assumption is used.
-- portable call pattern: finite-dimensional spectral perturbation, Markov-chain, stability, consensus, and distributed-optimization proofs vary the matrix, contour center, radii, and selected entry while replacing one resolvent contour by another without crossing spectrum.
-- counterargument checked: the existing matrix Riesz-projection contour-independence theorem is closely related but does not expose the raw unnormalized entry integral required inside later products and finite sums; cancelling its nonzero normalization factor yields a genuine companion API rather than a paper-local rename.
-- coverage search: `lean_search_symbols` queries "circle integral inverse resolvent entry equal spectrum disjoint annulus", "resolvent apply circle integral equality determinant nonzero annulus", and "Riesz projection contour independence spectrum disjoint annulus" found the matrix-level `Matrix.rieszProjectionOnCircle_eq_of_spectrum_disjoint_annulus` but no public entrywise integral theorem; `lean_leansearch` found only Mathlib's more general `Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable`.
-- minimal hypotheses: `[Fintype ι] [DecidableEq ι]`, positivity of the inner radius, radius ordering, and determinant nonvanishing throughout the closed annulus are exactly the hypotheses inherited from contour independence; no nonempty-carrier assumption is needed.

/-- The circle integrals of a selected entry of a finite matrix resolvent agree
on two concentric circles when the intervening closed annulus is disjoint from
the spectrum.

Layer: Glue | Gap: Level 1 (entrywise finite-matrix resolvent contour independence)
Proof: apply contour independence of the associated circle Riesz projections entrywise, unfold their specification, and cancel the nonzero `(2πi)⁻¹` normalization factor.
Source: Mathlib complex annulus circle-integral theorem, finite-matrix nonsingular inversion, and the circle Riesz-projection entry specification
Used in: finite spectral perturbation and periodic push-pull resolvent calculations that move a selected matrix entry between nested admissible contours before distributing integrals through matrix products and finite sums
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12/proof/1
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem circleIntegral_resolvent_apply_eq_of_spectrum_disjoint_annulus
    {ι : Type*} [Fintype ι] [decEq : DecidableEq ι]
    (A : Matrix ι ι ℂ) (center : ℂ) {innerRadius outerRadius : ℝ}
    (hinner_pos : 0 < innerRadius) (hradii : innerRadius ≤ outerRadius)
    (hspectrum : ∀ z : ℂ, innerRadius ≤ ‖z - center‖ →
      ‖z - center‖ ≤ outerRadius →
        det (z • (1 : Matrix ι ι ℂ) - A) ≠ 0)
    (i j : ι) :
    (∮ z in C(center, outerRadius),
        ((z • (1 : Matrix ι ι ℂ) - A)⁻¹) i j) =
      ∮ z in C(center, innerRadius),
        ((z • (1 : Matrix ι ι ℂ) - A)⁻¹) i j := by
  classical
  have hdec : decEq = Classical.decEq ι := Subsingleton.elim _ _
  cases hdec
  refine
    Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable
      (c := center) hinner_pos hradii (s := (∅ : Set ℂ)) Set.countable_empty ?_ ?_
  · intro z hz
    rcases hz with ⟨hzclosed, hznotball⟩
    have hlower : innerRadius ≤ ‖z - center‖ := by
      have hnotlt : ¬ dist z center < innerRadius := by
        intro hlt
        exact hznotball (Metric.mem_ball.2 hlt)
      simpa [dist_eq_norm] using le_of_not_gt hnotlt
    have hupper : ‖z - center‖ ≤ outerRadius := by
      simpa [dist_eq_norm] using Metric.mem_closedBall.mp hzclosed
    exact
      ((Matrix.analyticAt_inv_apply_of_entrywise_of_det_ne_zero
        (fun w : ℂ ↦ w • (1 : Matrix ι ι ℂ) - A)
        (x₀ := z) (by
          intro r c
          simpa only [Pi.smul_apply, smul_eq_mul, Matrix.sub_apply] using
            ((analyticAt_id (𝕜 := ℂ) (z := z)).mul
              (analyticAt_const (𝕜 := ℂ) (E := ℂ) (F := ℂ)
                (v := (1 : Matrix ι ι ℂ) r c) (x := z))).sub
              (analyticAt_const (𝕜 := ℂ) (E := ℂ) (F := ℂ)
                (v := A r c) (x := z)))
        (hspectrum z hlower hupper) i j).differentiableAt).continuousAt.continuousWithinAt
  · intro z hz
    rcases hz with ⟨⟨hzball, hznotclosed⟩, _⟩
    have hlower : innerRadius ≤ ‖z - center‖ := by
      have hnotle : ¬ dist z center ≤ innerRadius := by
        intro hle
        exact hznotclosed (Metric.mem_closedBall.2 hle)
      exact le_of_lt (by simpa [dist_eq_norm] using lt_of_not_ge hnotle)
    have hupper : ‖z - center‖ ≤ outerRadius := by
      exact le_of_lt (by simpa [dist_eq_norm] using Metric.mem_ball.mp hzball)
    exact
      (Matrix.analyticAt_inv_apply_of_entrywise_of_det_ne_zero
        (fun w : ℂ ↦ w • (1 : Matrix ι ι ℂ) - A)
        (x₀ := z) (by
          intro r c
          simpa only [Pi.smul_apply, smul_eq_mul, Matrix.sub_apply] using
            ((analyticAt_id (𝕜 := ℂ) (z := z)).mul
              (analyticAt_const (𝕜 := ℂ) (E := ℂ) (F := ℂ)
                (v := (1 : Matrix ι ι ℂ) r c) (x := z))).sub
              (analyticAt_const (𝕜 := ℂ) (E := ℂ) (F := ℂ)
                (v := A r c) (x := z)))
        (hspectrum z hlower hupper) i j).differentiableAt

end Matrix

/-! Promoted from Staging/spectrum_resolvent_sub_resolvent.lean. -/


-- Generalization plan (G0):
-- concept/name: first resolvent identity at two points; orig was
--   `complex_resolvent_inverse_identity_two_points`
-- generality used: a commutative scalar ring, a ring algebra, one algebra element,
--   and two scalars in its resolvent set; no topology, norm, measure, or finiteness
-- portable call pattern: spectral-contour and perturbation proofs comparing the
--   resolvent of a fixed algebra element at two admissible scalar points
-- counterargument checked: Mathlib has the named `resolvent` and the lower-level
--   `Ring.inverse_sub_inverse`, but no theorem exposing their two-point resolvent identity
-- coverage search: queries for "first resolvent identity in a unital algebra" and
--   "resolvent difference inverse product" found `resolvent`, `resolventSet`,
--   `Ring.inverse_sub_inverse`, and `Matrix.inv_sub_inv`; coverage is partial
-- minimal hypotheses: `CommRing K`, `Ring A`, `Algebra K A`, and pointwise membership
--   of both scalars in `resolventSet`; a field and finite dimensionality are unnecessary

open scoped Ring

namespace spectrum

/-- The difference of the resolvent at two points is their scalar difference times
the ordered product of the two resolvents.

Layer: Glue | Gap: Level 1 (first resolvent identity for a ring algebra)
Proof: apply `Ring.inverse_sub_inverse` to the two invertible resolvent denominators, simplify their difference through the algebra map, and commute the central scalar across the left inverse.
Source: Mathlib algebra spectrum definitions and total ring-inverse identities
Used in: spectral-contour and perturbation arguments that replace a product of two resolvents by a divided difference along two points of the resolvent set
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12/proof/1
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, periodic spectral decomposition -/
theorem resolvent_sub_resolvent
    {K A : Type*} [CommRing K] [Ring A] [Algebra K A]
    (a : A) (z w : K)
    (hz : z ∈ resolventSet K a) (hw : w ∈ resolventSet K a) :
    resolvent a z - resolvent a w =
      (w - z) • (resolvent a z * resolvent a w) := by
  have hunitz : IsUnit (algebraMap K A z - a) := hz
  have hunitw : IsUnit (algebraMap K A w - a) := hw
  have hdiff :
      (algebraMap K A w - a) - (algebraMap K A z - a) =
        algebraMap K A (w - z) := by
    rw [map_sub]
    noncomm_ring
  calc
    resolvent a z - resolvent a w =
        (algebraMap K A z - a)⁻¹ʳ *
          ((algebraMap K A w - a) - (algebraMap K A z - a)) *
            (algebraMap K A w - a)⁻¹ʳ := by
      exact Ring.inverse_sub_inverse ⟨fun _ => hunitw, fun _ => hunitz⟩
    _ = (algebraMap K A z - a)⁻¹ʳ * algebraMap K A (w - z) *
          (algebraMap K A w - a)⁻¹ʳ := by rw [hdiff]
    _ = algebraMap K A (w - z) * (algebraMap K A z - a)⁻¹ʳ *
          (algebraMap K A w - a)⁻¹ʳ := by
      rw [Algebra.commutes]
    _ = (w - z) • (resolvent a z * resolvent a w) := by
      rw [Algebra.smul_def, mul_assoc]
      rfl

end spectrum

/-! Promoted from Staging/MeasureTheory_setIntegral_Icc_Icc_swap_of_continuousOn.lean. -/


-- Generalization plan (G0):
-- concept/name: Fubini swap for a jointly continuous kernel on a closed real rectangle; orig was complex_setIntegral_Icc_Icc_swap_of_continuousOn
-- generality used: arbitrary real normed additive commutative group codomain; Lebesgue measure on both real coordinates; joint continuity only on the rectangle
-- portable call pattern: contour kernels and finite-horizon integral kernels call the same swap while the four endpoints, codomain, and jointly continuous integrand vary
-- counterargument checked: not paper-local or a pure wrapper because Mathlib's Fubini theorem still requires product integrability, while its compact-support variant requires global continuity and compact support
-- coverage search: queried `setIntegral Icc Icc swap continuousOn` and semantic `continuous function on compact product set iterated integrals swap Fubini`; top hits were Mathlib `integral_integral_swap`, `setIntegral_prod`, and `integral_integral_swap_of_hasCompactSupport`, which provide only the lower-level or globally supported forms
-- minimal hypotheses: endpoint order and finite-dimensional or complete-space assumptions are unnecessary; continuity on the closed rectangle alone supplies restricted-product integrability

/-- Iterated Bochner integrals of a jointly continuous kernel over two closed real
intervals agree after exchanging the order of integration.

Layer: Glue | Gap: Level 1 (compact-rectangle continuity to restricted Fubini swap)
Proof: joint continuity gives integrability on the compact measurable rectangle; rewrite the restricted product measure and apply Mathlib's `integral_integral_swap`.
Source: Mathlib Bochner integration on compact sets and product-measure Fubini theorems
Used in: contour-resolvent and finite-horizon kernel calculations that exchange two compact real parameter integrations without a separate product-integrability proof
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12/proof/1
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem MeasureTheory.setIntegral_Icc_Icc_swap_of_continuousOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a b c d : ℝ) (F : ℝ → ℝ → E)
    (hF :
      ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2)
        (Set.Icc a b ×ˢ Set.Icc c d)) :
    (∫ x in Set.Icc a b, ∫ y in Set.Icc c d, F x y) =
      ∫ y in Set.Icc c d, ∫ x in Set.Icc a b, F x y := by
  let s : Set ℝ := Set.Icc a b
  let t : Set ℝ := Set.Icc c d
  let G : ℝ × ℝ → E := fun p => F p.1 p.2
  have hcompact : IsCompact (s ×ˢ t) := by
    simpa [s, t] using (isCompact_Icc.prod isCompact_Icc)
  have hmeas : MeasurableSet (s ×ˢ t) := hcompact.measurableSet
  have hfinite : volume (s ×ˢ t) < ⊤ := hcompact.measure_lt_top
  have hGintOn : IntegrableOn G (s ×ˢ t) volume :=
    hF.integrableOn_of_subset_isCompact
      (K := s ×ˢ t) hcompact hmeas (fun p hp => hp) (ne_of_lt hfinite)
  have hGint :
      Integrable G ((volume.restrict s).prod (volume.restrict t)) := by
    rw [Measure.prod_restrict]
    simpa [IntegrableOn] using hGintOn
  calc
    (∫ x in Set.Icc a b, ∫ y in Set.Icc c d, F x y) =
        ∫ x, ∫ y, G (x, y) ∂(volume.restrict t) ∂(volume.restrict s) := by
          simp [s, t, G]
    _ = ∫ y, ∫ x, G (x, y) ∂(volume.restrict s) ∂(volume.restrict t) := by
      simpa [G] using
        (MeasureTheory.integral_integral_swap
          (μ := volume.restrict s) (ν := volume.restrict t)
          (f := fun x y => G (x, y)) hGint)
    _ = ∫ y in Set.Icc c d, ∫ x in Set.Icc a b, F x y := by
      simp [s, t, G]

/-! Promoted from Staging/ContinuousMap_integralCLM.lean. -/


open MeasureTheory
open scoped MeasureTheory

-- Generalization plan (G0):
-- concept/name: continuous-map Bochner integration operator; orig was
--   continuousMap_Icc_setIntegral_clm
-- generality used: compact Borel domain, arbitrary finite measure, complete normed
--   codomain over a normed scalar field compatible with its real normed-space structure
-- portable call pattern: analytic-under-integral and contour arguments apply this operator
--   to continuous-map-valued parameter families while changing the compact domain, measure,
--   scalar field, and Banach codomain
-- counterargument checked: this can be expressed by composing ContinuousMap.toLp with the L1
--   integral, but Mathlib has no named continuous-map integration operator; the evaluation API
--   and direct sup-norm continuity boundary make the object reusable rather than paper-local
-- coverage search: "continuous functions Bochner integral continuous linear map finite measure
--   supremum norm" and "ContinuousMap integral CLM" found only ContinuousMap.toLp and
--   MeasureTheory.L1.integralCLM'; no Mathlib or SOptLib declaration has this source and target
-- minimal hypotheses: finite measure replaces the interval-volume estimate; compactness,
--   Borel measurability, and SecondCountableTopologyEither are exactly what makes every
--   continuous map integrable; no finite-dimensional hypothesis is used

namespace ContinuousMap

/-- Bochner integration over a compact finite-measure Borel space is a continuous linear map
from continuous functions with the supremum norm to their codomain.

Layer: Glue | Concept: continuous-map Bochner integration operator
Proof: (definitional construction; compose the continuous embedding into `L1` with the Bochner integral continuous linear map)
Source: Mathlib `ContinuousMap.toLp` and `MeasureTheory.L1.integralCLM'` for Bochner integration of `L1` functions
Used in: analytic contour and parameter-dependent integral proofs, where a Banach-valued analytic family of continuous integrands is sent to its integral
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
noncomputable def integralCLM
    {K E 𝕜 : Type*}
    [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K] [CompactSpace K]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopologyEither K E]
    [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
    [SMulCommClass ℝ 𝕜 E]
    (μ : Measure K) [IsFiniteMeasure μ] :
    ContinuousMap K E →L[𝕜] E :=
  (MeasureTheory.L1.integralCLM' 𝕜).comp
    (ContinuousMap.toLp 1 μ 𝕜)

/-- Evaluating the continuous-map integration operator gives the Bochner integral.

Layer: Glue | Gap: Level 0 (continuous-map integration operator evaluation)
Proof: identify the continuous map with its `L1` class almost everywhere and use the defining evaluation theorem for the `L1` integral continuous linear map.
Source: Mathlib `ContinuousMap.coeFn_toLp`, `MeasureTheory.L1.integral_eq'`, and Bochner integral congruence
Used in: rewriting the continuous-linear image of a parameterized contour integrand to the corresponding subtype or ambient set integral
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
@[simp] theorem integralCLM_apply
    {K E 𝕜 : Type*}
    [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K] [CompactSpace K]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopologyEither K E]
    [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
    [SMulCommClass ℝ 𝕜 E]
    (μ : Measure K) [IsFiniteMeasure μ] (f : ContinuousMap K E) :
    integralCLM (𝕜 := 𝕜) μ f = ∫ x, f x ∂μ := by
  rw [integralCLM, ContinuousLinearMap.comp_apply]
  rw [← MeasureTheory.L1.integral_eq' 𝕜]
  rw [MeasureTheory.L1.integral_eq_integral]
  exact MeasureTheory.integral_congr_ae
    (ContinuousMap.coeFn_toLp (E := E) (p := 1) (𝕜 := 𝕜) μ f)

/-- Bochner integration of continuous maps commutes with postcomposition by a continuous
linear map.

Layer: Glue | Gap: Level 0 (continuous-map integration and continuous-linear postcomposition)
Proof: evaluate both continuous linear maps, identify `ContinuousMap.toLp` with the original
continuous function almost everywhere, and apply the Bochner integral commutation theorem.
Source: Mathlib `ContinuousLinearMap.compLeftContinuous` and
`ContinuousLinearMap.integral_comp_comm`
Used in: transporting vector-valued continuous integrals through coordinate projections,
matrix entries, bounded linear updates, and changes of Banach-valued observables
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous
Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem integralCLM_compLeftContinuous
    {K E F 𝕜 : Type*}
    [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K] [CompactSpace K]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [SecondCountableTopologyEither K E] [SecondCountableTopologyEither K F]
    [RCLike 𝕜] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]
    [SMulCommClass ℝ 𝕜 E] [SMulCommClass ℝ 𝕜 F]
    (μ : Measure K) [IsFiniteMeasure μ] (L : E →L[𝕜] F) :
    (integralCLM (K := K) (E := F) (𝕜 := 𝕜) μ).comp
        (L.compLeftContinuous 𝕜 K) =
      L.comp (integralCLM (K := K) (E := E) (𝕜 := 𝕜) μ) := by
  ext f
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    integralCLM_apply, integralCLM_apply]
  exact L.integral_comp_comm
    ((MeasureTheory.L1.integrable_coeFn
      (ContinuousMap.toLp 1 μ 𝕜 f)).congr
        (ContinuousMap.coeFn_toLp (E := E) (p := 1) (𝕜 := 𝕜) μ f))

end ContinuousMap

/-! Promoted from Staging/analyticAt_setIntegral_of_eventually_eq_continuousMap_integral.lean. -/


open Filter MeasureTheory
open scoped Topology

-- Generalization plan (G0):
-- concept/name: transfer of analyticity from subtype integrals to ambient set integrals
--   under eventual almost-everywhere agreement; orig was
--   `continuousMap_Icc_setIntegral_clm_apply_eventually_eq_ambient_integral`
-- generality used: an arbitrary nontrivially normed analytic scalar field, parameter normed
--   space, measurable integration domain, measurable set and measure, and
--   codomain carrying the real normed-space structure needed by the Bochner integral and the
--   analytic scalar structure; no compactness, finite measure, or completeness is used
-- portable call pattern: analytic-under-integral proofs for contour, compact-domain, and
--   parameterized-expectation arguments change the parameter space, measurable set, measure,
--   codomain, and subtype integrand while retaining eventual almost-everywhere agreement with
--   an ambient integrand
-- counterargument checked: this is not paper-local or a pure rename; it packages the recurring
--   bridge from an integrand on a measurable subtype to the ambient set
--   integral, combining analytic congruence with subtype-comap integral transport
-- coverage search: `lean_search_symbols` queries "analytic at set integral eventually equal
--   continuous map integral subtype comap" and "analytic congruence eventually equal integral
--   compact interval continuous map" found only the source declaration and the separate
--   `ContinuousMap.integralCLM` API; Mathlib semantic search found
--   `AnalyticWithinAt.congr_of_eventuallyEq` and `integral_subtype_comap` as separate ingredients,
--   but no declaration with this combined contract
-- minimal hypotheses: measurability of the set is the only measure-side hypothesis; eventual
--   almost-everywhere agreement is local at the analytic parameter, and finite-dimensionality,
--   compactness, finite measure, integrability, and completeness assumptions are unnecessary

/-- Analyticity of subtype integrals transfers to ambient set integrals when the subtype and
ambient integrands eventually agree almost everywhere on the set.

Layer: Glue | Gap: Level 1 (analytic transfer from subtype integrals to ambient set integrals)
Proof: use analytic congruence on a parameter neighborhood, rewrite each subtype integral by almost-everywhere agreement, and apply `MeasureTheory.integral_subtype_comap`.
Source: Mathlib analytic-function congruence and Bochner subtype-comap integral transport
Used in: analytic contour-integration and parameterized-integral arguments that first construct a locally analytic family of integrands on a measurable subtype
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12/proof/1
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem analyticAt_setIntegral_of_eventually_eq_subtype_integral
    {k P X E : Type*}
    [NontriviallyNormedField k]
    [NormedAddCommGroup P] [NormedSpace k P]
    [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace k E]
    (mu : Measure X) (s : Set X) (hs : MeasurableSet s)
    (a0 : P) (F : P → s → E) (f : P → X → E)
    (hFint :
      AnalyticAt k
        (fun a : P ↦ ∫ x : s, F a x ∂Measure.comap Subtype.val mu)
        a0)
    (hF_eq :
      ∀ᶠ a in 𝓝 a0,
        ∀ᵐ x : s ∂Measure.comap Subtype.val mu, F a x = f a x.1) :
    AnalyticAt k (fun a : P ↦ ∫ x in s, f a x ∂mu) a0 := by
  refine hFint.congr ?_
  filter_upwards [hF_eq] with a ha
  calc
    (∫ x : s, F a x ∂Measure.comap Subtype.val mu) =
        ∫ x : s, f a x.1 ∂Measure.comap Subtype.val mu := by
      exact MeasureTheory.integral_congr_ae ha
    _ = ∫ x in s, f a x ∂mu :=
      MeasureTheory.integral_subtype_comap hs (f a)

/-! Promoted from Staging/continuous_path_stays_in_ball_of_avoids_sphere.lean. -/


-- Generalization plan (G0):
-- concept/name: boundary avoidance keeps a continuous path in an open ball; orig was a local block in eigenbranch_stays_inside_fixed_circle_of_no_boundary
-- generality used: an arbitrary pseudo-metric space, a real-parameter path, a center, a radius containing the initial point, and one endpoint; no measure, vector-space, finite-dimensional, convexity, smoothness, or oracle assumptions
-- portable call pattern: spectral branches, homotopies, continuation methods, and stability paths use the same boundary-crossing exclusion while the metric target, path, endpoint, center, radius, and source of boundary avoidance vary
-- counterargument checked: this is not paper-local traceability or a pure rename; Mathlib supplies the intermediate value theorem and continuous distance separately, but callers otherwise repeat the nontrivial boundary-crossing contradiction
-- coverage search: symbol queries for “continuous path avoids sphere starts center endpoint mem ball”, “continuous distance intermediate value unoriented interval sphere”, and “preconnected image avoids boundary remains component open ball”, plus Mathlib semantic searches, found `intermediate_value_uIcc`, `continuous_dist`, and general connected-image lemmas but no theorem with this complete contract; coverage is partial
-- minimal hypotheses: `PseudoMetricSpace` suffices; the initial point need only lie in the ball, continuity is required only on `Set.uIcc 0 a`, and sphere avoidance is pointwise only on that interval

/-- A continuous path starting in an open ball stays there if it avoids
the boundary sphere throughout the intervening unoriented interval.

Layer: Glue | Gap: Level 1 (continuous-path open-ball invariance under sphere avoidance)
Proof: compose the path with distance to the center and apply `intermediate_value_uIcc`; an endpoint outside the ball would force the distance path to attain the radius, contradicting sphere avoidance.
Source: Mathlib pseudo-metric continuity of distance and the intermediate value theorem on unoriented real intervals
Used in: spectral-branch continuation across a fixed contour, homotopy invariance regions, and stability paths whose admissible component is bounded by a metric sphere
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12/proof/2
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem continuous_path_stays_in_ball_of_avoids_sphere
    {X : Type*} [PseudoMetricSpace X]
    (path : ℝ → X) (center : X) (radius a : ℝ)
    (hpath_start : path 0 ∈ Metric.ball center radius)
    (hpath_cont : ContinuousOn path (Set.uIcc (0 : ℝ) a))
    (havoid : ∀ t ∈ Set.uIcc (0 : ℝ) a,
      path t ∉ Metric.sphere center radius) :
    path a ∈ Metric.ball center radius := by
  rw [Metric.mem_ball]
  by_contra hnot_lt
  let distToCenter : ℝ → ℝ := fun t => dist (path t) center
  have hradius_le : radius ≤ distToCenter a := by
    exact le_of_not_gt hnot_lt
  have hdist_start : distToCenter 0 < radius := by
    simpa [distToCenter, Metric.mem_ball] using hpath_start
  have hdist_cont :
      ContinuousOn distToCenter (Set.uIcc (0 : ℝ) a) := by
    exact continuous_dist.comp_continuousOn
      (hpath_cont.prodMk continuousOn_const)
  have hradius_mem :
      radius ∈ Set.uIcc (distToCenter 0) (distToCenter a) := by
    exact Set.mem_uIcc_of_le (le_of_lt hdist_start) hradius_le
  rcases intermediate_value_uIcc hdist_cont hradius_mem with
    ⟨t, ht, hdist_eq⟩
  exact (havoid t ht) (by
    rw [Metric.mem_sphere]
    simpa [distToCenter] using hdist_eq)

/-! Promoted from Staging/DifferentiableAt_exists_norm_sub_le_mul_dist.lean. -/


open Topology

-- Generalization plan (G0):
-- concept/name: eventual linear displacement bound from differentiability at a
--   point; orig was `differentiableAt_exists_local_norm_sub_le_mul_dist`
-- generality used: arbitrary normed spaces over a nontrivially normed field,
--   with only pointwise Fréchet differentiability; no completeness,
--   finite-dimensionality, measure, convexity, or smoothness assumptions
-- portable call pattern: analytic or differentiable parameter families in
--   perturbation, sensitivity, and stable-response proofs vary their domain,
--   codomain, base point, and map while retaining an eventual linear bound on
--   displacement from the base value
-- counterargument checked: Mathlib exposes the displacement only as
--   `DifferentiableAt.isBigO_sub`; this declaration is not a pure rename because
--   it extracts a directly usable pointwise estimate and normalizes its real
--   constant to be nonnegative
-- coverage search: queried `differentiable at point exists neighborhood norm
--   difference upper bound constant times distance` and `differentiable at
--   exists nonnegative C eventually norm f y minus f x less than C times dist`;
--   Mathlib's `DifferentiableAt.isBigO_sub` is the precise asymptotic ingredient,
--   while no Mathlib, SOptLib, or approved round declaration has this eventual
--   nonnegative-constant distance-bound conclusion
-- minimal hypotheses: all normed-space typeclasses are required by Fréchet
--   differentiability and `DifferentiableAt.isBigO_sub`; the sole pointwise
--   differentiability hypothesis is used directly

/-- A function differentiable at a point has an eventual linear displacement
bound there, with a nonnegative real constant.

Layer: Glue | Gap: Level 1 (pointwise differentiability to an explicit local linear bound)
Proof: convert differentiability to Mathlib's `DifferentiableAt.isBigO_sub`, extract its eventual norm bound, and enlarge the witness to its maximum with zero.
Source: Mathlib Fréchet differentiability and asymptotic comparison APIs
Used in: analytic matrix-family and finite-mode perturbation arguments that need an explicit local displacement estimate before converting ambient norms to algorithm-specific operator or coordinate norms
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/13/proof/8
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem DifferentiableAt.exists_norm_sub_le_mul_dist
    {k E F : Type*} [NontriviallyNormedField k]
    [NormedAddCommGroup E] [NormedSpace k E]
    [NormedAddCommGroup F] [NormedSpace k F]
    {f : E → F} {x₀ : E} (hf : DifferentiableAt k f x₀) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ x in 𝓝 x₀, ‖f x - f x₀‖ ≤ C * Dist.dist x x₀ := by
  obtain ⟨c, hc⟩ := hf.isBigO_sub.bound
  refine ⟨max c 0, le_max_right c 0, ?_⟩
  filter_upwards [hc] with x hx
  calc
    ‖f x - f x₀‖ ≤ c * ‖x - x₀‖ := hx
    _ ≤ max c 0 * ‖x - x₀‖ :=
      mul_le_mul_of_nonneg_right (le_max_left c 0) (norm_nonneg _)
    _ = max c 0 * Dist.dist x x₀ := by rw [dist_eq_norm]

/-! Promoted from Staging/Filter_Eventually_exists_pos_le_and_forall_abs_lt.lean. -/


open Topology

-- Generalization plan (G0):
-- concept/name: capped metric-neighborhood witness
-- generality used: an arbitrary pseudo-metric space, center, predicate, and positive real cap;
--   no separation, measure, convexity, smoothness, or finite-dimensional assumptions
-- portable call pattern: continuity and local-analysis arguments that must shrink an eventual
--   neighborhood to a positive metric radius below a chosen cap
-- counterargument checked: this is not a pure alias; `Metric.eventually_nhds_iff` supplies an
--   arbitrary positive radius, while this theorem additionally enforces a prescribed cap
-- coverage search: precise capped-radius and eventual-neighborhood queries found
--   `Metric.eventually_nhds_iff` only as a partial hit
-- minimal hypotheses: `PseudoMetricSpace` is exactly what the neighborhood-basis theorem uses

/-- An eventual predicate at a point holds on a metric ball of positive radius
that can be chosen below any prescribed positive cap.

Layer: Glue | Gap: Level 1 (capped metric-neighborhood witness)
Proof: extract a positive metric radius with `Metric.eventually_nhds_iff`, then take
  its minimum with the prescribed cap.
Source: Mathlib metric neighborhood bases
Used in: analytic perturbation and local stability arguments that must choose one positive
  parameter radius below an ambient admissible radius while preserving an eventual predicate
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12/proof/2
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem Filter.Eventually.exists_pos_le_and_forall_dist_lt
    {α : Type*} [PseudoMetricSpace α] {x : α} {p : α → Prop}
    (hp : ∀ᶠ y in 𝓝 x, p y)
    (R : ℝ) (hR : 0 < R) :
    ∃ r : ℝ, r ≤ R ∧ 0 < r ∧ ∀ y : α, dist y x < r → p y := by
  rcases Metric.eventually_nhds_iff.mp hp with ⟨δ, hδ, hpδ⟩
  refine ⟨min R δ, min_le_left R δ, lt_min hR hδ, ?_⟩
  intro y hy
  exact hpδ (lt_of_lt_of_le hy (min_le_right R δ))

/-! Promoted from Staging/exists_approximate_minimizer_sequence.lean. -/


-- Generalization plan (G0):
-- concept/name: simultaneous choice from an indexed family of sets with a pointwise sInf-plus-tolerance bound; orig was exists_quadratic_lower_bound_near_sInf_sequence
-- generality used: arbitrary index and carrier types and a conditionally complete linearly ordered codomain with only the additive structure needed to add a positive tolerance
-- portable call pattern: choose one member of each active set whose mapped value is at most the corresponding infimum plus a pointwise positive tolerance
-- counterargument checked: Mathlib supplies the one-set approximation theorem exists_lt_of_csInf_lt, but not the simultaneous total selector; this result packages that theorem with classical choice
-- coverage search: symbol searches for `nonempty set exists member less than or equal to sInf plus positive` and `exists function each index value less than sInf plus epsilon`, plus LeanSearch for the one-set infimum approximation contract, found exists_lt_of_csInf_lt but no Mathlib, SOptLib, staging, or round-registry declaration with this family-level contract
-- minimal hypotheses: set nonemptiness and tolerance positivity are required only at active indices; Nonempty X supplies values at inactive indices, and no bounded-below hypothesis or stronger additive structure is used

/-- A pointwise nonempty family of sets admits a simultaneous choice of members
whose mapped values are at most the corresponding infima plus positive tolerances.

The membership and bound guarantees are imposed only at indices selected by
`active`; the returned function is total on the whole index type.

Layer: Glue | Gap: Level 1 (simultaneous indexed sInf approximation)
Proof: apply `exists_lt_of_csInf_lt` to the nonempty value set at each active index, then assemble the witnesses into a total function by classical choice.
Source: Mathlib conditionally complete linear order and classical choice APIs
Used in: indexed selection arguments requiring simultaneous set membership and pointwise sInf-plus-tolerance bounds
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/16/proof/0
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem exists_fun_mem_and_le_sInf_add
    {ι X R : Type*} [Nonempty X]
    [ConditionallyCompleteLinearOrder R] [AddZeroClass R] [AddLeftStrictMono R]
    (active : ι → Prop) (f : ι → X → R)
    (S : ι → Set X) (eps : ι → R)
    (hS : ∀ i : ι, active i → (S i).Nonempty)
    (heps : ∀ i : ι, active i → 0 < eps i) :
    ∃ x : ι → X,
      (∀ i : ι, active i → x i ∈ S i) ∧
        ∀ i : ι, active i →
          f i (x i) ≤
            sInf {value : R | ∃ y : X, y ∈ S i ∧ value = f i y} + eps i := by
  classical
  have hselect :
      ∀ i : ι, (hi : active i) →
        ∃ y : X, y ∈ S i ∧
          f i y ≤
            sInf {value : R | ∃ z : X, z ∈ S i ∧ value = f i z} + eps i := by
    intro i hi
    rcases hS i hi with ⟨y₀, hy₀⟩
    have hvalues :
        ({value : R | ∃ y : X, y ∈ S i ∧ value = f i y} : Set R).Nonempty :=
      ⟨f i y₀, y₀, hy₀, rfl⟩
    rcases exists_lt_of_csInf_lt hvalues
        (lt_add_of_pos_right _ (heps i hi)) with
      ⟨value, ⟨y, hy, rfl⟩, hlt⟩
    exact ⟨y, hy, hlt.le⟩
  let x : ι → X := fun i ↦
    if hi : active i then Classical.choose (hselect i hi)
    else Classical.choice inferInstance
  refine ⟨x, ?_, ?_⟩
  · intro i hi
    simpa [x, hi] using (Classical.choose_spec (hselect i hi)).1
  · intro i hi
    simpa [x, hi] using (Classical.choose_spec (hselect i hi)).2

/-! Promoted from Staging/ContinuousLinearMap_finrank_range_eq_of_continuous_idempotent_on_preconnected.lean. -/


open Topology
open Filter

-- Generalization plan (G0):
-- concept/name: constancy of the range finrank of a continuous family of idempotent continuous linear endomorphisms on a preconnected space; orig was finrank_range_mulVecLin_eq_on_Icc_of_continuous_idempotent
-- generality used: an arbitrary nontrivially normed field, finite-dimensional normed vector space, and preconnected topological parameter space; no measure, convexity, smoothness, or oracle assumptions
-- portable call pattern: spectral-continuation and invariant-subspace proofs for continuous families of Riesz, consensus, or complementary projections; the parameter space, field, vector space, family, and endpoints may vary while range finrank remains equal
-- counterargument checked: this is not paper-local or a pure wrapper; the nearby-idempotent theorem supplies only local equality, whereas this theorem derives global equality by proving the rank function locally constant and using preconnectedness
-- coverage search: searches for “continuous family idempotent endomorphisms constant rank preconnected” and “locally constant natural valued function constant preconnected space” found Mathlib's local-constancy propagation API and the staged nearby-idempotent theorem, but no declaration with this complete signature
-- minimal hypotheses: global continuity and pointwise idempotence are exactly what the local operator-norm argument uses; finite-dimensionality is required by the nearby-idempotent range-finrank theorem

/-- A continuous family of idempotent continuous linear endomorphisms on a
preconnected parameter space has constant range finrank.

Continuity makes every family member operator-norm close to nearby members, so
the range finrank is locally constant; preconnectedness then makes it globally
constant.

Layer: Glue | Gap: Level 1 (constant rank of a continuous idempotent family)
Proof: apply operator-norm range-rank stability in a unit neighborhood of each parameter to make the finrank function locally constant, then use `IsLocallyConstant.apply_eq_of_preconnectedSpace`.
Source: Mathlib connectedness and continuous-linear-map topology APIs, together with finite-dimensional rank stability for nearby idempotents
Used in: spectral-continuation steps that transport the rank of Riesz, consensus, or invariant-subspace projections between parameters
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12/proof/2
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem ContinuousLinearMap.finrank_range_eq_of_continuous_idempotent_on_preconnected
    {𝕜 V X : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
    [TopologicalSpace X] [PreconnectedSpace X]
    (P : X → V →L[𝕜] V)
    (hP : Continuous P)
    (hidempotent : ∀ x : X, (P x).comp (P x) = P x)
    (x y : X) :
    Module.finrank 𝕜 (LinearMap.range (P x : V →ₗ[𝕜] V)) =
      Module.finrank 𝕜 (LinearMap.range (P y : V →ₗ[𝕜] V)) := by
  let rdim : X → ℕ := fun z =>
    Module.finrank 𝕜 (LinearMap.range (P z : V →ₗ[𝕜] V))
  have hlocal : IsLocallyConstant rdim := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro z
    have hball : {T : V →L[𝕜] V | ‖T - P z‖ < 1} ∈ 𝓝 (P z) := by
      refine mem_of_superset
        (Metric.ball_mem_nhds (P z) (by norm_num : (0 : ℝ) < 1)) ?_
      intro T hT
      simpa [Metric.mem_ball, dist_eq_norm] using hT
    have hclose : ∀ᶠ w in 𝓝 z, ‖P w - P z‖ < 1 :=
      hP.continuousAt hball
    refine hclose.mono ?_
    intro w hw
    exact ContinuousLinearMap.finrank_range_eq_of_idempotent_norm_sub_lt_one
      (P w) (P z) (hidempotent w) (hidempotent z) hw
  exact hlocal.apply_eq_of_preconnectedSpace x y

/-! Promoted from Staging/Matrix_analyticAt_re_of_entrywise.lean. -/


-- Generalization plan (G0):
-- concept/name: analyticity of the entrywise real part of a complex matrix
--   family; orig was `fixedCircleRieszProjection_analyticAt_of_complex_entries`,
--   renamed `Matrix.analyticAt_re_of_entrywise`
-- generality used: an arbitrary real normed parameter space, arbitrary finite
--   row and column index types, and a complex matrix family
-- portable call pattern: real-parameter spectral perturbation, signal-processing,
--   and matrix-optimization proofs can vary the parameter space, finite matrix
--   shape, and complex family while retaining entrywise real-part analyticity
-- counterargument checked: the result is a short composition, but it packages a
--   recurring matrix-level closure step; Mathlib exposes only the separate Pi
--   analyticity and continuous-linear real-part facts
-- coverage search: queries "matrix real part analytic at from entrywise complex
--   analytic" and "analyticAt matrix entries iff" found only the paper-local
--   theorem; Mathlib semantic search found the component `analyticAt_pi_iff` and
--   scalar restriction theorem `AnalyticAt.re_ofReal`, but no matching matrix lemma
-- minimal hypotheses: the parameter only needs a real normed-space structure;
--   `Fintype` on each matrix index is exactly what `AnalyticAt.pi` requires

namespace Matrix

/-- Taking the real part of every entry in an entrywise analytic complex matrix
family yields an analytic real matrix family.

Layer: Glue | Gap: Level 1 (entrywise real-part analyticity for finite matrix families)
Proof: assemble the matrix with `AnalyticAt.pi` twice and compose each entry with the analytic continuous linear map `Complex.reCLM`.
Source: Mathlib `AnalyticAt.pi`, `ContinuousLinearMap.analyticAt`, and `Complex.reCLM`
Used in: fixed-contour spectral projection descent and real matrix reconstruction from analytic complex transfer or resolvent entries
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12/proof/1
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem analyticAt_re_of_entrywise
    {X m n : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [Fintype m] [Fintype n]
    (M : X → Matrix m n ℂ) {x : X}
    (hM : ∀ i j, AnalyticAt ℝ (fun y ↦ M y i j) x) :
    AnalyticAt ℝ (fun y i j ↦ (M y i j).re) x := by
  apply AnalyticAt.pi
  intro i
  apply AnalyticAt.pi
  intro j
  simpa only [Function.comp_apply, Complex.reCLM_apply] using
    (Complex.reCLM.analyticAt (M x i j)).comp_of_eq' (hM i j) rfl

end Matrix

/-! Promoted from Staging/Matrix_analyticAt_intervalIntegral_circle_resolvent_apply_of_spectrum_disjoint.lean. -/


noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Matrix

local instance realMatrixNormedAddCommGroup
    {ι : Type*} [Fintype ι] : NormedAddCommGroup (Matrix ι ι ℝ) :=
  Matrix.normedAddCommGroup

local instance realMatrixNormedSpace
    {ι : Type*} [Fintype ι] : NormedSpace ℝ (Matrix ι ι ℝ) :=
  Matrix.normedSpace

set_option maxHeartbeats 2000000 in

-- Generalization plan (G0):
-- concept/name: analyticity of a fixed-circle inverse-resolvent entry integral under
--   spectral disjointness; orig was
--   `fixed_contour_resolvent_integral_analytic_via_neumann_identity`
-- generality used: an arbitrary nonempty finite index type, a real-parameterized real
--   square-matrix family with its canonical complexification, an arbitrary complex circle
--   center, and a nonnegative real radius; only analyticity and determinant nonvanishing at
--   the distinguished parameter are used
-- portable call pattern: spectral perturbation and stability proofs for consensus, Markov,
--   and distributed-algorithm matrices vary the analytic matrix family, contour, parameter,
--   and selected entry while retaining fixed-contour spectral disjointness
-- counterargument checked: the nearby staged Riesz-projection theorem concludes analyticity
--   only after forming the Riesz projection and taking entrywise real parts; this theorem
--   preserves the complex inverse-resolvent interval integral needed before that descent, so
--   neither it nor Mathlib covers this contract
-- coverage search: `lean_search_symbols` queries "matrix analytic interval integral circle
--   inverse resolvent spectrum disjoint" and "analytic Riesz projection circle spectrum
--   disjoint" found `Matrix.analyticAt_rieszProjectionOnCircle_of_spectrum_disjoint` as a
--   partial hit; Mathlib semantic search found analytic inversion and continuous functional
--   calculus ingredients but no theorem for this parameterized contour integral
-- minimal hypotheses: pointwise analyticity and contour determinant nonvanishing at the base
--   parameter replace the source's stronger analytic interval and uniform spectral-gap
--   hypotheses; nonnegativity of the radius is used to parametrize the circle

/-- The normalized interval integral of an entry of a finite-matrix resolvent is real-analytic
at a parameter where the matrix family is real-analytic and the fixed circle is disjoint from
its spectrum.

Layer: Glue | Gap: Level 2 (analytic fixed-contour inverse-resolvent entry integration)
Proof: lift the resolvent to the Banach algebra of continuous matrix-valued functions on the circle parameter interval, apply analytic inversion at a unit, and compose with bounded entrywise contour integration.
Source: Mathlib `analyticAt_inverse`, `ContinuousMap.isUnit_iff_forall_isUnit`, `Matrix.isUnit_iff_isUnit_det`, and Bochner subtype-comap integration
Used in: fixed-contour spectral perturbation steps for periodic push-pull, consensus, and finite-state stability proofs where one resolvent entry is integrated to form a spectral projection
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12/proof/1
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem analyticAt_integral_Icc_circle_resolvent_apply_of_spectrum_disjoint
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (A : ℝ → Matrix ι ι ℝ) (radius : ℝ) (center : ℂ) (a₀ : ℝ) (p q : ι)
    (hradius_nonneg : 0 ≤ radius)
    (hA : AnalyticAt ℝ A a₀)
    (hspectrum : ∀ z : ℂ, ‖z - center‖ = radius →
      det (z • (1 : Matrix ι ι ℂ) - Matrix.map (A a₀) (algebraMap ℝ ℂ)) ≠ 0) :
    AnalyticAt ℝ
      (fun a : ℝ =>
        ∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi),
          deriv (circleMap center radius) theta *
            ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
              (((circleMap center radius theta) • (1 : Matrix ι ι ℂ) -
                Matrix.map (A a) (algebraMap ℝ ℂ))⁻¹) p q))
      a₀ := by
  classical
  let K : Type := Set.Icc (0 : ℝ) (2 * Real.pi)
  letI : NormedAddCommGroup (Matrix ι ι ℂ) :=
    Matrix.linftyOpNormedAddCommGroup
  letI : NormedSpace ℂ (Matrix ι ι ℂ) := Matrix.linftyOpNormedSpace
  letI : NormedRing (Matrix ι ι ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix ι ι ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedSpace ℝ (Matrix ι ι ℂ) :=
    NormedSpace.restrictScalars ℝ ℂ (Matrix ι ι ℂ)
  letI : IsBoundedSMul ℝ (Matrix ι ι ℂ) :=
    IsBoundedSMul.of_norm_smul_le NormedSpace.norm_smul_le
  letI : ContinuousSMul ℝ (Matrix ι ι ℂ) := IsBoundedSMul.continuousSMul
  letI hMComplete : CompleteSpace (Matrix ι ι ℂ) :=
    FiniteDimensional.complete ℂ (Matrix ι ι ℂ)
  have hCMComplete : CompleteSpace (ContinuousMap K (Matrix ι ι ℂ)) :=
    (ContinuousMap.isometryEquivBoundedOfCompact K (Matrix ι ι ℂ)).completeSpace
  letI := hCMComplete
  letI : HasSummableGeomSeries (ContinuousMap K (Matrix ι ι ℂ)) :=
    @instHasSummableGeomSeriesOfCompleteSpace
      (ContinuousMap K (Matrix ι ι ℂ)) _ hCMComplete
  let C : Matrix ι ι ℝ →ₗ[ℝ] ContinuousMap K (Matrix ι ι ℂ) :=
    { toFun := fun B =>
        ⟨fun _ => Matrix.map B (algebraMap ℝ ℂ), continuous_const⟩
      map_add' := by
        intro B D
        ext theta i j
        change ((B i j + D i j : ℝ) : ℂ) = (B i j : ℂ) + (D i j : ℂ)
        exact Complex.ofReal_add _ _
      map_smul' := by
        intro r B
        ext theta i j
        change ((r * B i j : ℝ) : ℂ) = (r : ℂ) * (B i j : ℂ)
        exact Complex.ofReal_mul _ _ }
  let Cc : Matrix ι ι ℝ →L[ℝ] ContinuousMap K (Matrix ι ι ℂ) :=
    LinearMap.toContinuousLinearMap C
  let Z : ContinuousMap K (Matrix ι ι ℂ) :=
    ⟨fun theta =>
        (circleMap center radius theta.1) • (1 : Matrix ι ι ℂ),
      (continuous_circleMap center radius).comp continuous_subtype_val |>.smul
        continuous_const⟩
  let R : ℝ → ContinuousMap K (Matrix ι ι ℂ) := fun a => Z - Cc (A a)
  have hR_analytic : AnalyticAt ℝ R a₀ := by
    simpa [R] using analyticAt_const.sub ((Cc.analyticAt (A a₀)).comp' hA)
  have hR_unit : IsUnit (R a₀) := by
    rw [ContinuousMap.isUnit_iff_forall_isUnit]
    intro theta
    rw [Matrix.isUnit_iff_isUnit_det]
    simpa [R, Z, Cc, C] using isUnit_iff_ne_zero.mpr (hspectrum
      (circleMap center radius theta.1) (by
        simpa [Metric.mem_sphere, dist_eq_norm] using
          circleMap_mem_sphere center hradius_nonneg theta.1))
  have hR_inv_analytic :
      AnalyticAt ℝ (fun a => Ring.inverse (R a)) a₀ := by
    exact (analyticAt_inverse (𝕜 := ℝ) hR_unit.unit).comp_of_eq'
      hR_analytic hR_unit.unit_spec.symm
  have hR_eventually_unit : ∀ᶠ a in 𝓝 a₀, IsUnit (R a) :=
    hR_analytic.continuousAt (Units.isOpen.mem_nhds hR_unit)
  let muK : Measure K := Measure.comap (Subtype.val : K → ℝ) volume
  have hmuK : muK (Set.univ : Set K) < ⊤ := by
    dsimp [muK, K]
    rw [comap_subtype_coe_apply isCompact_Icc.measurableSet]
    simpa using (isCompact_Icc (a := (0 : ℝ)) (b := 2 * Real.pi)).measure_lt_top
  let c : ℂ := (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹)
  let entryLin : Matrix ι ι ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun B => B p q
      map_add' := by intro B D; rfl
      map_smul' := by intro z B; rfl }
  let entryCLM : Matrix ι ι ℂ →L[ℂ] ℂ :=
    LinearMap.toContinuousLinearMap entryLin
  let T : ContinuousMap K (Matrix ι ι ℂ) →ₗ[ℝ] ContinuousMap K ℂ :=
    { toFun := fun f =>
        ⟨fun theta =>
            deriv (circleMap center radius) theta.1 * (c * f theta p q), by
          have hfpq : Continuous (fun theta : K => f theta p q) :=
            (continuous_apply q).comp ((continuous_apply p).comp f.continuous)
          simpa only [deriv_circleMap] using
            (((continuous_circleMap 0 radius).comp continuous_subtype_val).mul
              continuous_const).mul (continuous_const.mul hfpq)⟩
      map_add' := by
        intro f g
        ext theta
        simp [mul_add]
      map_smul' := by
        intro r f
        ext theta
        change deriv (circleMap center radius) theta.1 *
            (c * ((r : ℂ) * f theta p q)) =
          (r : ℂ) *
            (deriv (circleMap center radius) theta.1 * (c * f theta p q))
        ring }
  let Tc : ContinuousMap K (Matrix ι ι ℂ) →L[ℝ] ContinuousMap K ℂ :=
    LinearMap.mkContinuous T (‖c‖ * |radius| * ‖entryCLM‖) (by
      intro f
      let g : ContinuousMap K ℂ :=
        ⟨fun theta =>
            deriv (circleMap center radius) theta.1 * (c * f theta p q), by
          have hfpq : Continuous (fun theta : K => f theta p q) :=
            (continuous_apply q).comp ((continuous_apply p).comp f.continuous)
          simpa only [deriv_circleMap] using
            (((continuous_circleMap 0 radius).comp continuous_subtype_val).mul
              continuous_const).mul (continuous_const.mul hfpq)⟩
      change ‖g‖ ≤ (‖c‖ * |radius| * ‖entryCLM‖) * ‖f‖
      apply (g.norm_le (mul_nonneg
        (mul_nonneg (mul_nonneg (norm_nonneg c) (abs_nonneg radius))
          (norm_nonneg entryCLM)) (norm_nonneg f))).2
      intro theta
      change ‖deriv (circleMap center radius) theta.1 * (c * f theta p q)‖ ≤
        (‖c‖ * |radius| * ‖entryCLM‖) * ‖f‖
      calc
        ‖deriv (circleMap center radius) theta.1 * (c * f theta p q)‖ =
            (‖c‖ * |radius|) * ‖f theta p q‖ := by
              simp [deriv_circleMap]
              ring
        _ ≤ (‖c‖ * |radius|) * (‖entryCLM‖ * ‖f theta‖) := by
          have hentry : ‖f theta p q‖ ≤ ‖entryCLM‖ * ‖f theta‖ := by
            simpa [entryCLM, entryLin] using
              (ContinuousLinearMap.le_opNorm entryCLM (f theta))
          exact mul_le_mul_of_nonneg_left hentry (by positivity)
        _ ≤ (‖c‖ * |radius|) * (‖entryCLM‖ * ‖f‖) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left
              (ContinuousMap.norm_coe_le_norm f theta) (norm_nonneg entryCLM))
            (by positivity)
        _ = (‖c‖ * |radius| * ‖entryCLM‖) * ‖f‖ := by ring)
  let LI : ContinuousMap K ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun f => ∫ theta in (Set.univ : Set K), f theta ∂muK
      map_add' := by
        intro f g
        have hf : Integrable (fun theta : K => f theta) muK := by
          simpa [IntegrableOn] using
            (f.continuous.continuousOn.integrableOn_of_subset_isCompact
              (μ := muK) (K := Set.univ) isCompact_univ MeasurableSet.univ
              (fun x hx => hx) (ne_of_lt hmuK))
        have hg : Integrable (fun theta : K => g theta) muK := by
          simpa [IntegrableOn] using
            (g.continuous.continuousOn.integrableOn_of_subset_isCompact
              (μ := muK) (K := Set.univ) isCompact_univ MeasurableSet.univ
              (fun x hx => hx) (ne_of_lt hmuK))
        simpa [Pi.add_apply] using integral_add hf hg
      map_smul' := by
        intro r f
        simpa [Pi.smul_apply] using
          (integral_smul (μ := muK) (𝕜 := ℝ) (G := ℂ) r (fun x : K => f x)) }
  let LIc : ContinuousMap K ℂ →L[ℝ] ℂ :=
    LinearMap.mkContinuous LI (muK.real (Set.univ : Set K)) (by
      intro f
      change ‖∫ theta in (Set.univ : Set K), f theta ∂muK‖ ≤
        muK.real (Set.univ : Set K) * ‖f‖
      have hbound := MeasureTheory.norm_setIntegral_le_of_norm_le_const
        (μ := muK) (s := (Set.univ : Set K))
        (f := fun theta : K => f theta) hmuK
        (fun theta _ => ContinuousMap.norm_coe_le_norm f theta)
      simpa only [mul_comm] using hbound)
  have hIntegral_analytic : AnalyticAt ℝ
      (fun a => LIc (Tc (Ring.inverse (R a)))) a₀ :=
    (LIc.analyticAt _).comp' ((Tc.analyticAt _).comp' hR_inv_analytic)
  have hIntegral_eq : ∀ᶠ a in 𝓝 a₀,
      LIc (Tc (Ring.inverse (R a))) =
        ∫ theta in Set.Icc (0 : ℝ) (2 * Real.pi),
          deriv (circleMap center radius) theta *
            (c * (((circleMap center radius theta) • (1 : Matrix ι ι ℂ) -
              Matrix.map (A a) (algebraMap ℝ ℂ))⁻¹) p q) := by
    filter_upwards [hR_eventually_unit] with a ha
    have hinv_apply (theta : K) :
        Ring.inverse (R a) theta =
          ((circleMap center radius theta.1) • (1 : Matrix ι ι ℂ) -
            Matrix.map (A a) (algebraMap ℝ ℂ))⁻¹ := by
      rw [Matrix.nonsing_inv_eq_ringInverse]
      have hu : (ha.unit : ContinuousMap K (Matrix ι ι ℂ)) = R a :=
        ha.unit_spec
      calc
        Ring.inverse (R a) theta =
            Ring.inverse (↑ha.unit : ContinuousMap K (Matrix ι ι ℂ)) theta := by
              rw [hu]
        _ = (↑ha.unit⁻¹ : ContinuousMap K (Matrix ι ι ℂ)) theta := by
              rw [Ring.inverse_unit]
        _ = ↑(ContinuousMap.unitsLift.symm ha.unit theta)⁻¹ := by
              exact (ContinuousMap.unitsLift_symm_apply_apply_inv' ha.unit theta).symm
        _ = Ring.inverse ((R a) theta) := by
              rw [← Ring.inverse_unit (ContinuousMap.unitsLift.symm ha.unit theta)]
              rfl
        _ = Ring.inverse
            ((circleMap center radius theta.1) • (1 : Matrix ι ι ℂ) -
              Matrix.map (A a) (algebraMap ℝ ℂ)) := by
              congr 1
    change
      (∫ theta in (Set.univ : Set K),
        deriv (circleMap center radius) theta.1 *
          (c * (Ring.inverse (R a) theta) p q) ∂muK) = _
    rw [show
      (∫ theta in (Set.univ : Set K),
        deriv (circleMap center radius) theta.1 *
          (c * (Ring.inverse (R a) theta) p q) ∂muK) =
        ∫ theta in (Set.univ : Set K),
          deriv (circleMap center radius) theta.1 *
            (c * (((circleMap center radius theta.1) • (1 : Matrix ι ι ℂ) -
              Matrix.map (A a) (algebraMap ℝ ℂ))⁻¹) p q) ∂muK by
        apply integral_congr_ae
        filter_upwards with theta
        rw [hinv_apply theta]]
    simpa [K, muK] using
      (MeasureTheory.integral_subtype_comap
        (μ := volume) (s := Set.Icc (0 : ℝ) (2 * Real.pi))
        isCompact_Icc.measurableSet
        (fun theta : ℝ =>
          deriv (circleMap center radius) theta *
            (c * (((circleMap center radius theta) • (1 : Matrix ι ι ℂ) -
              Matrix.map (A a) (algebraMap ℝ ℂ))⁻¹) p q)))
  exact hIntegral_analytic.congr hIntegral_eq

end Matrix

/-! Promoted from Staging/summable_and_norm_tsum_le_of_geometric_bound.lean. -/


open scoped BigOperators

-- Generalization plan (G0):
-- concept/name: summability and infinite-sum norm control from a geometric
--   pointwise majorant; orig was `geometric_majorant_summability_and_tsum_norm`
-- generality used: an arbitrary complete normed additive commutative group, a
--   vector-valued sequence, a real majorant constant, and a nonnegative ratio
--   below one; no measure, convexity, smoothness, oracle, or finite-dimensional
--   assumptions
-- portable call pattern: stable-series, mixing-tail, and linear-response proofs
--   instantiate the sequence, majorant constant, and contraction ratio while
--   reusing both absolute convergence and the norm bound on the infinite sum
-- counterargument checked: Mathlib has the comparison test and its quantitative
--   companion separately, but no searched declaration packages both conclusions
--   under the recurring geometric majorant needed by downstream proofs
-- coverage search: searched `summable norm infinite sum bounded by summable norm
--   majorant`, `geometric bound summable series norm tsum upper bound`, and the
--   exact suggested name; the closest full signatures were Mathlib
--   `Summable.of_norm_bounded`, `tsum_of_norm_bounded`, and
--   `summable_geometric_of_lt_one`, which are precisely the three components
-- minimal hypotheses: `0 ≤ r`, `r < 1`, completeness, and the pointwise norm
--   bound are exactly what the proof uses; nonnegativity of `C` follows at index
--   zero from the pointwise bound and is not assumed separately

/-- A sequence dominated in norm by a real geometric majorant is summable, and
the norm of its infinite sum is bounded by the summed majorant.

Layer: Glue | Gap: Level 1 (paired geometric-series convergence and sum-norm bound)
Proof: establish summability of the scalar geometric series, scale it by the
majorant constant, then apply Mathlib's direct comparison test and its
quantitative `tsum` companion.
Source: Mathlib normed-group infinite sums via `Summable.of_norm_bounded` and
`tsum_of_norm_bounded`, and real geometric-series summability
Used in: contractive mixing and corrected-lift series proofs that need both
existence of an infinite response and a geometric bound on its total norm
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/11
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed
Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem summable_and_norm_tsum_le_of_geometric_bound
    {F : Type*} [NormedAddCommGroup F] [CompleteSpace F]
    (f : ℕ → F) (C r : ℝ)
    (hr_nonneg : 0 ≤ r) (hr_lt_one : r < 1)
    (hf : ∀ j, ‖f j‖ ≤ C * r ^ j) :
    Summable f ∧ ‖∑' j, f j‖ ≤ C * ∑' j : ℕ, r ^ j := by
  have hgeom : Summable (fun j : ℕ ↦ r ^ j) :=
    summable_geometric_of_lt_one hr_nonneg hr_lt_one
  have hmajor : Summable (fun j : ℕ ↦ C * r ^ j) :=
    Summable.mul_left C hgeom
  constructor
  · exact Summable.of_norm_bounded hmajor hf
  · rw [← tsum_mul_left]
    exact tsum_of_norm_bounded hmajor.hasSum hf

/-! Promoted from Staging/Asymptotics_isLittleO_of_eventually_between.lean. -/


open Filter

-- Generalization plan (G0):
-- concept/name: the little-o squeeze theorem for an eventual order interval;
--   orig was isLittleO_of_eventually_between
-- generality used: an arbitrary index type and filter, lower, middle, and
--   upper functions valued in a linearly ordered normed additive commutative
--   group with a solid norm, and a comparison function into any type with a
--   norm; no measure, convexity, smoothness, oracle, or finite-dimensional
--   assumptions are used
-- portable call pattern: asymptotic upper/lower-bound proofs for stochastic
--   approximation and distributed optimization vary the indexed functions,
--   filter, and comparison scale while concluding the same little-o estimate
-- counterargument checked: this is not paper-local traceability or a pure
--   rename; it composes two little-o estimates with an eventual order squeeze,
--   a contract not supplied by one existing Mathlib or SOptLib declaration
-- coverage search: searched `little o upper lower eventually between squeeze`
--   and `IsLittleO of eventually bounded between real functions` with project
--   symbol search, and the complete natural-language contract with Mathlib
--   LeanSearch; the closest hits were IsLittleO.of_bound, IsLittleO.add, and
--   IsLittleO.trans_isBigO, which do not accept an eventual order interval
-- minimal hypotheses: all order hypotheses are eventual and both endpoint
--   little-o assumptions are necessary; the scale only requires a norm

/-- A function into a linearly ordered normed additive commutative group with a
solid norm, eventually squeezed between two functions that are little-o of the
same scale, is itself little-o of that scale.

Layer: Glue | Gap: Level 1 (little-o squeeze under eventual two-sided bounds)
Proof: apply `IsLittleO.of_bound` at half the requested constant, combine the two endpoint bounds, and control the absolute value of the squeezed function by the sum of the endpoint absolute values.
Source: Mathlib asymptotic comparison definitions and ordered additive lattice norm inequalities
Used in: matching lower-bound arguments where an optimized stochastic-objective residual is trapped between near-minimizer and balancing-stepsize residuals that are both negligible at the target rate
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/17/proof/12
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem Asymptotics.isLittleO_of_eventually_between
    {I E F : Type*} [Norm E]
    [NormedAddCommGroup F] [LinearOrder F] [IsOrderedAddMonoid F] [HasSolidNorm F]
    {l : Filter I} {f lower upper : I → F} {scale : I → E}
    (hlower : Asymptotics.IsLittleO l lower scale)
    (hupper : Asymptotics.IsLittleO l upper scale)
    (hbetween : ∀ᶠ i in l, lower i ≤ f i ∧ f i ≤ upper i) :
    Asymptotics.IsLittleO l f scale := by
  refine Asymptotics.IsLittleO.of_bound ?_
  intro eps heps
  have hhalf : 0 < eps / 2 := by positivity
  have hlower_bound := hlower.def hhalf
  have hupper_bound := hupper.def hhalf
  filter_upwards [hlower_bound, hupper_bound, hbetween] with
    i hlower_i hupper_i hbetween_i
  rcases hbetween_i with ⟨hlo, hhi⟩
  have hnorm : ‖f i‖ ≤ ‖lower i‖ + ‖upper i‖ := by
    have hsup_nonneg : 0 ≤ |lower i| ⊔ |upper i| :=
      (abs_nonneg (lower i)).trans le_sup_left
    calc
      ‖f i‖ ≤ ‖|lower i| ⊔ |upper i|‖ :=
        norm_le_norm_of_abs_le_abs (by
          simpa only [abs_of_nonneg hsup_nonneg] using abs_le_max_abs_abs hlo hhi)
      _ ≤ ‖|lower i|‖ + ‖|upper i|‖ := norm_sup_le_add _ _
      _ = ‖lower i‖ + ‖upper i‖ := by rw [norm_abs_eq_norm, norm_abs_eq_norm]
  calc
    ‖f i‖ ≤ ‖lower i‖ + ‖upper i‖ := hnorm
    _ ≤ (eps / 2) * ‖scale i‖ + (eps / 2) * ‖scale i‖ :=
      add_le_add hlower_i hupper_i
    _ = eps * ‖scale i‖ := by ring

/-! Promoted from Staging/Metric_mem_cthickening_sphere_of_abs_norm_sub_le.lean. -/


-- Generalization plan (G0):
-- concept/name: radial-error criterion for membership in a closed thickening of a sphere;
--   orig was `mem_cthickening_sphere_of_abs_norm_sub_le`
-- generality used: an arbitrary real seminormed additive commutative group; no completeness,
--   inner-product, finite-dimensional, measure, convexity, smoothness, or oracle assumptions
-- portable call pattern: compact-contour and robust-feasibility arguments that convert a
--   radial norm error into membership in a closed neighborhood while varying the ambient
--   normed space, center, radius, thickness, and point
-- counterargument checked: this is not paper-local traceability or a pure wrapper;
--   Mathlib supplies witness-to-thickening membership but not the radial projection bridge
-- coverage search: queries "closed thickening sphere membership absolute radial norm
--   difference bounded", "cthickening sphere abs dist radius", and the corresponding
--   LeanSearch sentence found `Metric.mem_cthickening_of_dist_le` as a partial result only
-- minimal hypotheses: `0 ≤ delta` and `0 < radius` are derived from the error bound and
--   `delta < radius`; all remaining hypotheses are used

/-- A radial norm error bounded by `delta < radius` puts a point in the closed
`delta`-thickening of the sphere.

Layer: Glue | Gap: Level 1 (radial error to closed sphere-thickening membership)
Proof: radially rescale the displacement from the center onto the sphere, compute
  its distance from the original point, and apply `Metric.mem_cthickening_of_dist_le`.
Source: Mathlib real normed-space scalar norms, metric spheres, and closed thickenings
Used in: compact-contour isolation and robust-feasibility arguments that turn radial error bounds into closed-neighborhood membership
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/algorithm_spec
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem Metric.mem_cthickening_sphere_of_abs_norm_sub_le
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    {center z : E} {radius delta : ℝ}
    (hdelta_lt_radius : delta < radius)
    (hz : |‖z - center‖ - radius| ≤ delta) :
    z ∈ Metric.cthickening delta (Metric.sphere center radius) := by
  let d : ℝ := ‖z - center‖
  have hdelta_nonneg : 0 ≤ delta :=
    (abs_nonneg (d - radius)).trans (by simpa [d] using hz)
  have hradius_pos : 0 < radius := lt_of_le_of_lt hdelta_nonneg hdelta_lt_radius
  have hd_pos : 0 < d := by
    have hleft : -delta ≤ d - radius := (abs_le.mp (by simpa [d] using hz)).1
    nlinarith
  let y : E := center + (radius / d) • (z - center)
  have hy_sphere : y ∈ Metric.sphere center radius := by
    have hy_sub : y - center = (radius / d) • (z - center) := by
      simp [y]
    have hnorm : ‖(radius / d) • (z - center)‖ = radius := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hradius_pos hd_pos)]
      rw [show ‖z - center‖ = d by rfl]
      field_simp [ne_of_gt hd_pos]
    exact Metric.mem_sphere.mpr (by
      simpa [dist_eq_norm, hy_sub] using hnorm)
  have hdist_le : dist z y ≤ delta := by
    have hz_sub : z - y = (1 - radius / d) • (z - center) := by
      dsimp [y]
      module
    have hnorm : ‖(1 - radius / d) • (z - center)‖ = |d - radius| := by
      rw [norm_smul, Real.norm_eq_abs]
      rw [show ‖z - center‖ = d by rfl]
      have hfactor : |(1 : ℝ) - radius / d| * d = |d - radius| := by
        have hd_ne : d ≠ 0 := ne_of_gt hd_pos
        calc
          |(1 : ℝ) - radius / d| * d = |(d - radius) / d| * d := by
            congr 1
            field_simp [hd_ne]
          _ = (|d - radius| / d) * d := by
            rw [abs_div, abs_of_pos hd_pos]
          _ = |d - radius| := by
            field_simp [hd_ne]
      exact hfactor
    have hdist : dist z y = |d - radius| := by
      simpa [dist_eq_norm, hz_sub] using hnorm
    simpa [d, hdist] using hz
  exact Metric.mem_cthickening_of_dist_le z y delta
    (Metric.sphere center radius) hy_sphere hdist_le

/-! Promoted from Staging/Metric_exists_annulus_subset_open_of_sphere_subset.lean. -/


-- Generalization plan (G0):
-- concept/name: existence of a closed concentric annulus inside an open
--   neighborhood of a positive-radius sphere; orig was the local block in
--   `exists_no_eigen_annulus_around_fixed_circle`
-- generality used: a real seminormed space with compactness assumed only for
--   the sphere in question; no properness, inner-product, finite-dimensional,
--   completeness, measure, convexity, smoothness, or oracle assumptions are used
-- portable call pattern: contour isolation, perturbation, robust-feasibility,
--   and level-set proofs vary the ambient space, open set, center, and positive
--   radius while retaining sphere containment and requiring a closed annulus
-- counterargument checked: the result composes compact-neighborhood separation
--   with the radial projection bridge, so it is neither paper-local nor a pure
--   rename of either ingredient
-- coverage search: queries "closed annulus subset open set containing sphere"
--   and "compact sphere thickening subset open" found Mathlib's
--   `IsCompact.exists_cthickening_subset_open` and the staged
--   `Metric.mem_cthickening_sphere_of_abs_norm_sub_le` only as partial results;
--   no Mathlib or SOptLib declaration packages the annulus conclusion
-- minimal hypotheses: compactness is needed only for the sphere in question;
--   positivity of `radius` is needed to choose a positive inner radius

/-- If an open set contains a positive-radius sphere, it contains a closed
concentric annulus with the sphere strictly between its boundary radii.

Layer: Glue | Gap: Level 1 (closed annulus inside an open sphere neighborhood)
Proof: compactness gives a positive closed thickening of the sphere inside the open set; choose a smaller thickness than the radius and use radial projection to place every point of the resulting annulus in that thickening.
Source: Mathlib compact-set closed-thickening neighborhoods, together with the radial sphere-projection bound
Used in: fixed-contour spectral isolation, perturbation neighborhoods, robust-feasibility margins, and level-set arguments that need a whole closed annulus around an admissible sphere
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12/proof/1
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem Metric.exists_annulus_subset_open_of_sphere_subset
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (U : Set E) (center : E) (radius : ℝ)
    (hsphere_compact : IsCompact (Metric.sphere center radius))
    (hradius_pos : 0 < radius) (hUopen : IsOpen U)
    (hsphere_subset : Metric.sphere center radius ⊆ U) :
    ∃ innerRadius outerRadius : ℝ,
      0 < innerRadius ∧ innerRadius < radius ∧ radius < outerRadius ∧
      ∀ z : E, innerRadius ≤ ‖z - center‖ →
        ‖z - center‖ ≤ outerRadius → z ∈ U := by
  rcases hsphere_compact.exists_cthickening_subset_open hUopen hsphere_subset with
    ⟨delta, hdelta_pos, hdelta_subset⟩
  let eta : ℝ := min (delta / 2) (radius / 2)
  have heta_pos : 0 < eta :=
    lt_min (half_pos hdelta_pos) (half_pos hradius_pos)
  have heta_le_delta : eta ≤ delta :=
    le_trans (min_le_left (delta / 2) (radius / 2)) (by linarith)
  have heta_lt_radius : eta < radius :=
    lt_of_le_of_lt (min_le_right (delta / 2) (radius / 2)) (by linarith)
  refine ⟨radius - eta, radius + eta, ?_, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · linarith
  · intro z hzinner hzouter
    have hz_abs : |‖z - center‖ - radius| ≤ eta := by
      rw [abs_sub_le_iff]
      constructor <;> linarith
    have hz_cthick_eta :
        z ∈ Metric.cthickening eta (Metric.sphere center radius) :=
      Metric.mem_cthickening_sphere_of_abs_norm_sub_le heta_lt_radius hz_abs
    exact hdelta_subset
      (Metric.cthickening_mono heta_le_delta (Metric.sphere center radius)
        hz_cthick_eta)

/-! Promoted from Staging/Asymptotics_isLittleO_natCast_inv_inv_sqrt.lean. -/


open Filter Topology

-- Generalization plan (G0):
-- concept/name: reciprocal natural horizons are little-o of reciprocal
--   square-root horizons; orig was nat_inv_isLittleO_inv_sqrt
-- generality used: natural indices, real-valued rates, and the at-top filter;
--   no measure, convexity, smoothness, oracle, vector-space, or
--   finite-dimensional assumptions are used
-- portable call pattern: finite-horizon stochastic-optimization and
--   distributed-optimization rate proofs vary their residual estimates while
--   repeatedly absorb an inverse-horizon term into an inverse-square-root rate
-- counterargument checked: this is not paper-local traceability or a pure
--   rename; it packages the positivity, square-root limit, and reciprocal
--   comparison needed to establish a standard Nat-indexed rate relation that
--   is not available as one Mathlib or SOptLib declaration
-- coverage search: searched `inverse natural number is little o of inverse
--   square root`, `inverse natural cast little o inverse square root`, and
--   `power is little o power atTop exponent inequality`; Mathlib's
--   `Asymptotics.IsLittleO.natCast_atTop`,
--   `Asymptotics.isLittleO_pow_pow_atTop_of_lt`, and
--   `Asymptotics.IsLittleO.sqrt` are partial, while SOptLib and the round
--   registry contain no complete match
-- minimal hypotheses: all already minimal; the theorem is a closed comparison
--   of the two canonical real rate sequences on natural horizons

/-- The reciprocal natural horizon is little-o of the reciprocal square-root
horizon as the horizon tends to infinity.

Layer: Glue | Gap: Level 1 (reciprocal horizon versus reciprocal square-root asymptotics)
Proof: use decay of the reciprocal square root, identify the reciprocal horizon with its square, and bound that square by an arbitrary positive multiple of the reciprocal square root.
Source: Mathlib real square-root limits, natural-cast convergence at infinity, and asymptotic little-o bounds
Used in: finite-horizon rate squeezes that discard an inverse-horizon near-minimizer error against an inverse-square-root leading scale
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/17/proof/12
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem Asymptotics.isLittleO_natCast_inv_inv_sqrt :
    Asymptotics.IsLittleO atTop
      (fun T : ℕ => (T : ℝ)⁻¹)
      (fun T : ℕ => (Real.sqrt (T : ℝ))⁻¹) := by
  classical
  refine Asymptotics.IsLittleO.of_bound ?_
  intro eps heps
  have hsqrt_atTop :
      Tendsto (fun T : ℕ => Real.sqrt (T : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hinv_sqrt_zero :
      Tendsto (fun T : ℕ => (Real.sqrt (T : ℝ))⁻¹) atTop (nhds 0) :=
    hsqrt_atTop.inv_tendsto_atTop
  have hsmall_dist :
      ∀ᶠ T : ℕ in atTop, dist ((Real.sqrt (T : ℝ))⁻¹) 0 < eps :=
    (Metric.tendsto_nhds.mp hinv_sqrt_zero) eps heps
  have hlarge : ∀ᶠ T : ℕ in atTop, 1 ≤ T :=
    eventually_atTop.2 ⟨1, fun T hT => hT⟩
  filter_upwards [hsmall_dist, hlarge] with T hsmallT hT
  let invs : ℝ := (Real.sqrt (T : ℝ))⁻¹
  have hinvs_nonneg : 0 ≤ invs := by
    dsimp [invs]
    exact inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hinvs_le_eps : invs ≤ eps := by
    have habs : |invs| < eps := by
      simpa [Real.dist_eq, invs] using hsmallT
    exact le_of_lt (lt_of_le_of_lt (le_abs_self invs) habs)
  have hTinv_le_invs_sq : (T : ℝ)⁻¹ ≤ invs ^ 2 := by
    have hTreal_pos : 0 < (T : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hT)
    have hsqrt_pos : 0 < Real.sqrt (T : ℝ) :=
      Real.sqrt_pos.2 hTreal_pos
    have hsqrt_ne : Real.sqrt (T : ℝ) ≠ 0 := ne_of_gt hsqrt_pos
    have hsqrt_sq : Real.sqrt (T : ℝ) ^ 2 = (T : ℝ) :=
      Real.sq_sqrt hTreal_pos.le
    have hEq : (T : ℝ)⁻¹ = invs ^ 2 := by
      dsimp [invs]
      calc
        (T : ℝ)⁻¹ = (Real.sqrt (T : ℝ) ^ 2)⁻¹ := by rw [hsqrt_sq]
        _ = (Real.sqrt (T : ℝ))⁻¹ ^ 2 := by
          field_simp [hsqrt_ne]
    exact le_of_eq hEq
  have hsq_le : invs ^ 2 ≤ eps * invs := by
    nlinarith [mul_le_mul_of_nonneg_left hinvs_le_eps hinvs_nonneg]
  have hleft_abs : |(T : ℝ)⁻¹| = (T : ℝ)⁻¹ :=
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg T))
  have hright_abs : |(Real.sqrt (T : ℝ))⁻¹| =
      (Real.sqrt (T : ℝ))⁻¹ :=
    abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))
  rw [Real.norm_eq_abs, Real.norm_eq_abs, hleft_abs, hright_abs]
  exact le_trans hTinv_le_invs_sq hsq_le


/-! Promoted from Staging/eventually_lt_of_vanishing_upper_and_quadratic_floor.lean. -/


open Filter

-- Generalization plan (G0):
-- concept/name: eventual smallness forced by a vanishing objective upper bound
--   and a positive quadratic floor; orig was
--   near_minimizer_eventually_lt_delta_of_upper_and_fresh_floor
-- generality used: an arbitrary index type and filter, a real-valued family,
--   parameter and rate functions, and real scaling and coercivity constants;
--   no measure, convexity, smoothness, oracle, or finite-dimensional assumptions
-- portable call pattern: tuning-parameter and lower-bound arguments for future
--   stochastic algorithms may change the objective family, selected parameters,
--   vanishing rate, and coercivity constant while using the same eventual-smallness
--   conclusion
-- counterargument checked: this is not paper-local traceability or a pure rename;
--   it packages the nonlinear coercivity step from an objective-value sandwich,
--   while Mathlib's squeeze lemmas only propagate already established bounds
--   between functions
-- coverage search: project symbol searches for `eventually below positive threshold
--   vanishing upper bound positive quadratic lower bound`, `tendsto zero nonnegative
--   sequence square upper bound`, and `quadratic lower bound objective vanishing upper
--   bound eventually` found no matching declaration; Mathlib LeanSearch returned
--   `squeeze_zero'` and `squeeze_zero` as partial hits, neither of which derives a
--   parameter bound from an intervening objective and a positive quadratic floor
-- minimal hypotheses: both objective inequalities are eventual; the positivity of the
--   threshold itself supplies the sign information needed to compare squares, the rate
--   need only tend to zero, and no sign condition on its constant scale is used

/-- A parameter is eventually below every positive threshold when its objective values
have a constant-scaled vanishing upper bound and a positive quadratic lower bound.

Layer: Glue | Gap: Level 1 (eventual parameter smallness from a coercive objective sandwich)
Proof: use convergence of the scaled rate to make the objective upper envelope smaller than `kappa * delta ^ 2`; if the parameter were at least `delta`, nonnegativity and the quadratic floor would give the contradictory reverse inequality.
Source: Mathlib filter convergence in metric spaces and ordered real polynomial inequalities
Used in: near-minimizer arguments where a vanishing objective-value estimate and a fresh-noise or coercivity floor force selected nonnegative tuning parameters to approach zero from above
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/17/proof/10
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem eventually_lt_of_vanishing_upper_and_quadratic_floor
    {I : Type*} {l : Filter I}
    (J : I → ℝ → ℝ) (alpha rate : I → ℝ) (C kappa : ℝ)
    (hkappa : 0 < kappa)
    (hrate : Tendsto rate l (nhds 0))
    (hupper : ∀ᶠ i in l, J i (alpha i) ≤ C * rate i)
    (hfloor : ∀ᶠ i in l, kappa * alpha i ^ 2 ≤ J i (alpha i)) :
    ∀ delta : ℝ, 0 < delta → ∀ᶠ i in l, alpha i < delta := by
  have hscaled_zero :
      Tendsto (fun i => C * rate i) l (nhds 0) := by
    simpa using hrate.const_mul C
  intro delta hdelta
  have hthreshold : 0 < kappa * delta ^ 2 := by positivity
  have hdist :
      ∀ᶠ i in l, dist (C * rate i) 0 < kappa * delta ^ 2 :=
    (Metric.tendsto_nhds.mp hscaled_zero) _ hthreshold
  have hsmall :
      ∀ᶠ i in l, C * rate i < kappa * delta ^ 2 := by
    filter_upwards [hdist] with i hi
    have habs : |C * rate i| < kappa * delta ^ 2 := by
      simpa [Real.dist_eq] using hi
    exact lt_of_le_of_lt (le_abs_self _) habs
  filter_upwards [hupper, hfloor, hsmall] with i hupper_i hfloor_i hsmall_i
  by_contra hnot
  have hdelta_le : delta ≤ alpha i := le_of_not_gt hnot
  have hsquare : delta ^ 2 ≤ alpha i ^ 2 := by
    nlinarith [sq_nonneg (alpha i - delta)]
  have hscaled_square : kappa * delta ^ 2 ≤ kappa * alpha i ^ 2 :=
    mul_le_mul_of_nonneg_left hsquare hkappa.le
  linarith

/-! Promoted from Staging/parameter_mul_natCast_tendsto_atTop_of_vanishing_upper_and_bounded_region_floor.lean. -/


open Filter

-- Generalization plan (G0):
-- concept/name: divergence of a parameter-horizon product forced by a vanishing
--   value upper bound and positive floors on bounded product regions; orig was
--   near_minimizer_product_tendsto_atTop_of_upper_and_slow_floor
-- generality used: real-valued parameter, upper-envelope, and value families on
--   natural horizons; no measure, convexity, smoothness, oracle, normed-space, or
--   finite-dimensional assumptions
-- portable call pattern: rate lower-bound and asymptotic-regime proofs may change
--   the value family, parameter sequence, vanishing comparison rate, and bounded-
--   region floor supplier while retaining divergence of parameter times horizon
-- counterargument checked: this is not paper-local traceability or a one-call
--   wrapper; it packages a substantive filter contradiction joining convergence
--   to zero, eventual inequalities, and a family of bounded-region coercive floors
-- coverage search: symbol searches for `parameter times natural cast tends to
--   infinity from vanishing upper bound and positive floor on bounded regions` and
--   `tendsto atTop product bounded region lower bound vanishing value` found only
--   the source theorem and the distinct preceding eventual-smallness lemma;
--   Mathlib LeanSearch returned generic product-limit facts but no matching contract
-- minimal hypotheses: the explicit inverse-square-root envelope is weakened to an
--   arbitrary upper sequence tending to zero, and parameter nonnegativity is needed
--   only eventually; the bounded-region floor hypotheses are already pointwise

/-- A nonnegative parameter sequence whose attained values have a vanishing upper
envelope escapes every bounded parameter-times-horizon region when each such region
has an eventually positive value floor.

Layer: Glue | Gap: Level 1 (escape from bounded parameter-horizon regions under vanishing values)
Proof: test convergence to `atTop` against an arbitrary real bound; for a nonnegative bound, combine eventual smallness of the parameter and upper envelope with its positive bounded-region floor to obtain a contradiction.
Source: Mathlib filter convergence at `atTop`, real order topology, and natural-to-real cast inequalities
Used in: near-minimizer and tuning-parameter arguments that must enter a small-parameter, long-horizon asymptotic regime before applying a uniform expansion
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/16/proof/2
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem parameter_mul_natCast_tendsto_atTop_of_vanishing_upper_and_bounded_region_floor
    (J : ℕ → ℝ → ℝ) (alpha upper : ℕ → ℝ)
    (halpha_nonneg : ∀ᶠ T : ℕ in atTop, 0 ≤ alpha T)
    (halpha_tendsto : Tendsto alpha atTop (nhds 0))
    (hupper_tendsto : Tendsto upper atTop (nhds 0))
    (hvalue_upper : ∀ᶠ T : ℕ in atTop, J T (alpha T) ≤ upper T)
    (hfloor :
      ∀ M : ℝ, 0 ≤ M →
        ∃ c alpha0 : ℝ, ∃ T0 : ℕ, 0 < c ∧ 0 < alpha0 ∧
          ∀ T : ℕ, ∀ a : ℝ, T0 ≤ T → 0 ≤ a →
            a ≤ alpha0 → a * (T : ℝ) ≤ M → c ≤ J T a) :
    Tendsto (fun T : ℕ => alpha T * (T : ℝ)) atTop atTop := by
  rw [Filter.tendsto_atTop]
  intro M
  by_cases hM_neg : M < 0
  · filter_upwards [halpha_nonneg] with T hnonneg
    exact le_trans (le_of_lt hM_neg) (mul_nonneg hnonneg (Nat.cast_nonneg T))
  · have hM_nonneg : 0 ≤ M := le_of_not_gt hM_neg
    rcases hfloor M hM_nonneg with
      ⟨c, alpha0, Tfloor, hc_pos, halpha0_pos, hfloor_bound⟩
    have hsmall_upper : ∀ᶠ T : ℕ in atTop, upper T < c :=
      hupper_tendsto.eventually_lt_const hc_pos
    have hsmall_alpha : ∀ᶠ T : ℕ in atTop, alpha T < alpha0 :=
      halpha_tendsto.eventually_lt_const halpha0_pos
    have hlarge : ∀ᶠ T : ℕ in atTop, Tfloor ≤ T :=
      Filter.eventually_atTop.2 ⟨Tfloor, fun _ hT => hT⟩
    filter_upwards [halpha_nonneg, hvalue_upper, hsmall_upper, hsmall_alpha, hlarge] with
      T halpha_nonneg_T hvalue_upper_T hsmall_upper_T hsmall_alpha_T hlarge_T
    by_contra hnot
    have hprod_le : alpha T * (T : ℝ) ≤ M := le_of_not_ge hnot
    have hfloor_T :=
      hfloor_bound T (alpha T) hlarge_T halpha_nonneg_T
        (le_of_lt hsmall_alpha_T) hprod_le
    exact (not_lt_of_ge hfloor_T) (lt_of_le_of_lt hvalue_upper_T hsmall_upper_T)

/-! Promoted from Staging/exists_const_one_add_natCast_mul_pow_le_pow_of_lt.lean. -/


open scoped BigOperators

-- Generalization plan (G0):
-- concept/name: uniform absorption of a linear natural-index factor into a
--   strictly larger geometric rate; orig was `one_plus_nat_mul_geometric_absorb`.
-- generality used: an arbitrary field with a compatible strict linear order,
--   a nonnegative smaller scalar, a strictly larger scalar, and natural powers;
--   no measure, optimization,
--   convexity, smoothness, oracle, or finite-dimensional assumptions are used.
-- portable call pattern: recurrence, matrix-power perturbation, and convergence-
--   rate proofs vary the two positive geometric rates while reusing one constant
--   that absorbs the linear prefactor uniformly over every natural index.
-- counterargument checked: this is not paper-local traceability or a pure
--   wrapper; it converts a pointwise polynomial-geometric sequence to a uniform
--   larger-rate envelope with an explicit geometric-series constant.
-- coverage search: searches for `positive geometric rate linear polynomial
--   factor upper bound by larger geometric rate exists constant`, `polynomial
--   times geometric sequence uniformly bounded`, and the precise natural-cast
--   statement found Mathlib's eventual `isBigO_pow_pow_of_le_left` and formal-
--   series radius bounds, but no theorem with this uniform finite-index contract;
--   SOptLib geometric-rate hits have different signatures, so coverage is partial.
-- minimal hypotheses: nonnegativity of the smaller rate and its strict
--   inequality with the larger rate imply every sign and denominator condition
--   used by the proof; no upper contraction bound is needed.

/-- A linear natural-index factor times a nonnegative geometric rate is uniformly
bounded by a constant times any strictly larger geometric rate.

Layer: Glue | Gap: Level 1 (uniform polynomial-factor geometric-rate absorption)
Proof: divide the rates to obtain a ratio in `[0, 1)`, bound each linear-weighted
  power by a finite geometric sum, and rescale the resulting inverse-gap bound.
Source: Mathlib ordered-field natural powers and finite geometric-series identity
  `mul_neg_geom_sum`
Used in: stable-recurrence and matrix-power perturbation bounds that enlarge a
  geometric decay rate to absorb a lag-dependent linear prefactor
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/13/proof/7
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed
  Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem exists_const_one_add_natCast_mul_pow_le_pow_of_lt
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {r R : K} (hr_nonneg : 0 ≤ r) (hr_lt_R : r < R) :
    ∃ C : K, 0 ≤ C ∧
      ∀ n : ℕ, ((n : K) + 1) * r ^ n ≤ C * R ^ n := by
  have hR_pos : 0 < R := lt_of_le_of_lt hr_nonneg hr_lt_R
  have hR_ne : R ≠ 0 := ne_of_gt hR_pos
  let q : K := r / R
  have hq_nonneg : 0 ≤ q := div_nonneg hr_nonneg hR_pos.le
  have hq_lt_one : q < 1 := by
    rw [div_lt_one hR_pos]
    exact hr_lt_R
  have hden_pos : 0 < 1 - q := by linarith
  refine ⟨(1 - q)⁻¹, inv_nonneg.mpr hden_pos.le, ?_⟩
  intro n
  have hterm_le_sum :
      ((n : K) + 1) * q ^ n ≤
        ∑ k ∈ Finset.range (n + 1), q ^ k := by
    calc
      ((n : K) + 1) * q ^ n =
          (∑ _k ∈ Finset.range (n + 1), q ^ n) := by
            simp [Finset.sum_const, nsmul_eq_mul, Nat.cast_add]
      _ ≤ ∑ k ∈ Finset.range (n + 1), q ^ k := by
            apply Finset.sum_le_sum
            intro k hk
            have hk_le : k ≤ n :=
              Nat.le_of_lt_succ (Finset.mem_range.mp hk)
            exact pow_le_pow_of_le_one hq_nonneg hq_lt_one.le hk_le
  have hsum_le :
      (∑ k ∈ Finset.range (n + 1), q ^ k) ≤ (1 - q)⁻¹ := by
    have hmul :
        (∑ k ∈ Finset.range (n + 1), q ^ k) * (1 - q) ≤ 1 := by
      calc
        (∑ k ∈ Finset.range (n + 1), q ^ k) * (1 - q) =
            (1 - q) * ∑ k ∈ Finset.range (n + 1), q ^ k := by ring
        _ = 1 - q ^ (n + 1) := by
            simpa using (mul_neg_geom_sum q (n + 1))
        _ ≤ 1 := by
            have hpow_nonneg : 0 ≤ q ^ (n + 1) := pow_nonneg hq_nonneg _
            linarith
    have hdiv :
        (∑ k ∈ Finset.range (n + 1), q ^ k) ≤ 1 / (1 - q) :=
      (le_div_iff₀ hden_pos).2 hmul
    simpa only [one_div] using hdiv
  have hpoly : ((n : K) + 1) * q ^ n ≤ (1 - q)⁻¹ :=
    le_trans hterm_le_sum hsum_le
  have hR_pow_nonneg : 0 ≤ R ^ n := pow_nonneg hR_pos.le n
  have hpow_eq : r ^ n = q ^ n * R ^ n := by
    dsimp [q]
    rw [div_pow]
    field_simp [hR_ne]
  calc
    ((n : K) + 1) * r ^ n =
        (((n : K) + 1) * q ^ n) * R ^ n := by
          rw [hpow_eq]
          ring
    _ ≤ (1 - q)⁻¹ * R ^ n :=
        mul_le_mul_of_nonneg_right hpoly hR_pow_nonneg

/-! Promoted from Staging/eventually_sub_lt_mul_of_tendsto_div_zero_and_isLittleO.lean. -/


open Filter

-- Generalization plan (G0):
-- concept/name: eventual strict comparison for a difference of asymptotically
--   negligible real residuals; orig was
--   originalLinearSpeedupResidual_sub_littleOInvSqrt_eventually_lt_gap
-- generality used: an arbitrary index type and filter, three real-valued
--   functions, eventual positivity of the comparison scale, quotient
--   convergence for one residual, and a little-o hypothesis for the other;
--   no measure, convexity, smoothness, oracle, or finite-dimensional assumptions
-- portable call pattern: lower-bound contradiction and leading-term absorption
--   steps can vary the filter, positive scale, residuals, and coefficient gap
--   while retaining the same eventual strict comparison
-- counterargument checked: this is not paper-local traceability or a pure
--   wrapper; it composes quotient convergence, the little-o conversion and
--   subtraction laws, and an ordered strict estimate under scale positivity
-- coverage search: searched `eventually residual difference less than positive
--   multiple scale tendsto quotient zero little o`, `IsLittleO of tendsto
--   division zero eventually positive denominator`, and the full contract via
--   Mathlib LeanSearch; the closest hits were
--   `Asymptotics.isLittleO_of_tendsto'`, `Asymptotics.IsLittleO.sub`, and
--   `Asymptotics.IsLittleO.forall_isBigOWith`, each covering only one transition
-- minimal hypotheses: scale positivity is only eventual; it both discharges the
--   zero-denominator condition and makes the final multiplication strict

/-- If one residual divided by an eventually positive scale tends to zero and a
second residual is little-o of that scale, their difference is eventually less
than every fixed positive multiple of the scale.

Layer: Glue | Gap: Level 1 (eventual strict comparison of negligible residuals)
Proof: convert quotient convergence to a little-o estimate using eventual scale nonvanishing, subtract the second little-o estimate, and apply the resulting norm bound at half the positive coefficient.
Source: Mathlib asymptotic comparison lemmas `Asymptotics.isLittleO_of_tendsto'`, `Asymptotics.IsLittleO.sub`, and `Asymptotics.IsLittleO.def`
Used in: lower-bound contradictions where a conjectured normalized residual and a matching-expansion residual must be absorbed by a positive leading-coefficient gap
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/9/proof/9
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem eventually_sub_lt_mul_of_tendsto_div_zero_and_isLittleO
    {ι : Type*} {l : Filter ι} {residual residual0 scale : ι → ℝ}
    (hscale : ∀ᶠ i in l, 0 < scale i)
    (hresidual : Tendsto (fun i => residual i / scale i) l (nhds 0))
    (hresidual0 : Asymptotics.IsLittleO l residual0 scale)
    {gap : ℝ} (hgap : 0 < gap) :
    ∀ᶠ i in l, residual i - residual0 i < gap * scale i := by
  have hresidual_little : Asymptotics.IsLittleO l residual scale := by
    exact Asymptotics.isLittleO_of_tendsto'
      (hscale.mono fun _ hi hzero => (ne_of_gt hi hzero).elim) hresidual
  have hdiff :
      Asymptotics.IsLittleO l (fun i => residual i - residual0 i) scale :=
    hresidual_little.sub hresidual0
  have hhalf : 0 < gap / 2 := half_pos hgap
  have hbound := hdiff.def hhalf
  filter_upwards [hbound, hscale] with i hbound_i hscale_i
  have hscale_norm : ‖scale i‖ = scale i := by
    rw [Real.norm_eq_abs, abs_of_pos hscale_i]
  have habs_bound :
      |residual i - residual0 i| ≤ (gap / 2) * scale i := by
    simpa [Real.norm_eq_abs, hscale_norm] using hbound_i
  calc
    residual i - residual0 i ≤ |residual i - residual0 i| := le_abs_self _
    _ ≤ (gap / 2) * scale i := habs_bound
    _ < gap * scale i :=
      mul_lt_mul_of_pos_right (half_lt_self hgap) hscale_i

/-! Promoted from Staging/periodic_continuousLinearMap_apply_le_of_phase_bound.lean. -/


-- Generalization plan (G0):
-- concept/name: arbitrary-time action bound for a periodic family of continuous linear maps; orig was `periodic_continuousLinearMap_apply_le_of_phase_bound`
-- generality used: an arbitrary nontrivially normed scalar field and seminormed modules; no completeness, finite-dimensionality, measure, convexity, smoothness, oracle, or algorithm assumptions
-- portable call pattern: periodic linear-system, consensus, and optimization proofs change the period, normed modules, operator family, phase bound, time, and vector while retaining the same all-time operator-action estimate
-- counterargument checked: the proof is a short composition, but it packages a recurring phase-to-arbitrary-time transition rather than renaming either component theorem; neither `Function.Periodic.map_mod_nat` nor `ContinuousLinearMap.le_opNorm` alone supplies the conclusion
-- coverage search: queried `periodic family continuous linear map arbitrary time action norm bound from phase representative bound`, `continuous linear map apply norm bounded by operator norm`, and the corresponding Mathlib semantic description; the closest hits were Mathlib's `Function.Periodic.map_mod_nat` and `ContinuousLinearMap.le_opNorm`, which cover only the reindexing and pointwise operator estimate separately
-- minimal hypotheses: positivity of the natural period constructs its residue phase, periodicity identifies that phase with the requested time, and only the phasewise operator-norm upper bound is used

/-- A periodic family of continuous linear maps whose phase operator norms are
bounded by `M` acts at every natural time with bound `M`.

Layer: Glue | Gap: Level 1 (uniform action bound from finite periodic phase bounds)
Proof: reduce the time index modulo the positive period with `Function.Periodic.map_mod_nat`, apply `ContinuousLinearMap.le_opNorm` at that phase, and multiply the phase operator-norm bound by the nonnegative vector norm.
Source: Mathlib natural-number periodicity in `Data.Nat.Periodic` and continuous-linear-map operator norms in `Analysis.Normed.Operator.Basic`
Used in: periodic consensus and push--pull deviation estimates that promote one-period operator bounds to arbitrary-time actions on a state or residual vector
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/assumptions/7
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem periodic_continuousLinearMap_apply_le_of_phase_bound
    {𝕜 V W : Type*} [NontriviallyNormedField 𝕜]
    [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
    [SeminormedAddCommGroup W] [NormedSpace 𝕜 W]
    (p : ℕ) (A : ℕ → V →L[𝕜] W) (M : ℝ)
    (hp : 0 < p) (hperiodic : Function.Periodic A p)
    (hphase : ∀ r : Fin p, ‖A r.1‖ ≤ M)
    (t : ℕ) (x : V) :
    ‖A t x‖ ≤ M * ‖x‖ := by
  let r : Fin p := ⟨t % p, Nat.mod_lt t hp⟩
  have hAt : A r.1 = A t := hperiodic.map_mod_nat t
  calc
    ‖A t x‖ = ‖A r.1 x‖ := by rw [hAt]
    _ ≤ ‖A r.1‖ * ‖x‖ := (A r.1).le_opNorm x
    _ ≤ M * ‖x‖ := mul_le_mul_of_nonneg_right (hphase r) (norm_nonneg x)

/-! Promoted from Staging/dependent_product_operator_map_endpoint_sq_le_length_mul_path_energy.lean. -/


open scoped BigOperators

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: dependent-product operator energy of a coordinatewise Lipschitz endpoint map controlled by finite-path increment energy; orig was perronResidual_gradient_block_sq_le
-- generality used: a finite index type, a dependent family of seminormed additive commutative groups for the path and seminormed additive groups for the mapped endpoints, an arbitrary product operator with a nonnegative endpoint root-energy action bound, coordinate maps with pointwise endpoint Lipschitz estimates, and a finite path; no scalar action, inner product, completeness, finite-dimensionality, measure, convexity, differentiability, or optimization assumptions
-- portable call pattern: block and epoch analyses for distributed gradient tracking, coordinate maps, and residual filters change the finite coordinate family, product operator and its energy bound, coordinatewise map, path, block start, and block length while retaining the same endpoint-to-path energy conclusion
-- counterargument checked: this is not paper-local traceability or a one-line wrapper because it composes an operator energy estimate, coordinatewise Lipschitz energy aggregation, coordinatewise path telescoping, finite-sum Cauchy--Schwarz, and product-energy reindexing into one reusable contract
-- coverage search: queried `dependent product operator squared norm endpoint coordinatewise Lipschitz map bounded by path length sum squared increments`, `finite path endpoint squared displacement bounded by length times sum squared increments`, and the Mathlib semantic equivalent; `dependent_product_norm_sq_map_sub_le_of_pointwise_lipschitz`, `sq_sum_le_card_mul_sum_sq`, and `norm_sum_le` cover constituents only, while SOptLib's finite-path integrability and coercive-energy lemmas have materially different conclusions and hypotheses
-- minimal hypotheses: the operator estimate and Lipschitz estimates are required only at the two path endpoints, commutativity is retained only for the path codomain where finite sums are formed, and nonnegativity is needed for the operator and map constants when their estimates are squared

/-- A product operator applied to a coordinatewise Lipschitz endpoint difference
has squared energy at most the path length times the intervening squared
increment energy, scaled by the operator and map bounds.

Layer: Glue | Gap: Level 1 (operator-transformed Lipschitz endpoint energy from finite-path increments)
Proof: apply the supplied operator energy estimate and the coordinatewise Lipschitz dependent-product bound, then telescope each path coordinate and use finite-sum Cauchy--Schwarz before reordering the two finite sums.
Source: Mathlib finite range-sum telescoping, norm-of-sum and finite-sum square inequalities, together with SOptLib dependent-product squared-norm energy aggregation
Used in: block and epoch residual analyses that charge an operator-transformed gradient or coordinate-map endpoint jump to the distributed state displacement energy accumulated inside the block
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/6/proof/8
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem dependent_product_operator_map_endpoint_sq_le_length_mul_path_energy
    {ι : Type*} [Fintype ι]
    {E F : ι → Type*}
    [∀ i, SeminormedAddCommGroup (E i)]
    [∀ i, SeminormedAddGroup (F i)]
    (A : (∀ i, F i) → (∀ i, F i))
    (f : ∀ i, E i → F i) (X : ℕ → ∀ i, E i)
    (s p : ℕ) (c L : ℝ)
    (hc : 0 ≤ c)
    (hA : Real.sqrt (dependentProductNormSq
        (A (fun i => f i (X (s + p) i)) -
          A (fun i => f i (X s i)))) ≤
      c * Real.sqrt (dependentProductNormSq
        ((fun i => f i (X (s + p) i)) -
          (fun i => f i (X s i)))))
    (hL : 0 ≤ L)
    (hf : ∀ i,
      ‖f i (X (s + p) i) - f i (X s i)‖ ≤
        L * ‖X (s + p) i - X s i‖) :
    dependentProductNormSq
        (A (fun i => f i (X (s + p) i)) -
          A (fun i => f i (X s i))) ≤
      (p : ℝ) * c ^ 2 * L ^ 2 *
        ∑ j ∈ Finset.range p,
          dependentProductNormSq
            (fun i => X (s + j + 1) i - X (s + j) i) := by
  classical
  let Y : ∀ i, F i := fun i => f i (X (s + p) i)
  let Z : ∀ i, F i := fun i => f i (X s i)
  have hoperator : dependentProductNormSq (A Y - A Z) ≤
      c ^ 2 * dependentProductNormSq (Y - Z) := by
    have hout : 0 ≤ dependentProductNormSq (A Y - A Z) :=
      dependentProductNormSq_nonneg _
    have hin : 0 ≤ dependentProductNormSq (Y - Z) :=
      dependentProductNormSq_nonneg _
    have hsq := (sq_le_sq₀ (Real.sqrt_nonneg _)
      (mul_nonneg hc (Real.sqrt_nonneg _))).2 hA
    rw [Real.sq_sqrt hout, mul_pow, Real.sq_sqrt hin] at hsq
    exact hsq
  have hmap : dependentProductNormSq (Y - Z) ≤
      L ^ 2 * dependentProductNormSq
        (fun i => X (s + p) i - X s i) := by
    simpa only [Y, Z, Pi.sub_apply] using
      (dependent_product_norm_sq_map_sub_le_of_pointwise_lipschitz
        f L (X (s + p)) (X s) hL hf)
  have hpath : dependentProductNormSq
      (fun i => X (s + p) i - X s i) ≤
      (p : ℝ) * ∑ j ∈ Finset.range p,
        dependentProductNormSq
          (fun i => X (s + j + 1) i - X (s + j) i) := by
    have hcoord (i : ι) :
        X (s + p) i - X s i =
          ∑ j ∈ Finset.range p,
            (X (s + j + 1) i - X (s + j) i) := by
      simpa [Nat.add_assoc] using
        (Finset.sum_range_sub (fun j => X (s + j) i) p).symm
    have hpoint (i : ι) :
        ‖X (s + p) i - X s i‖ ^ 2 ≤
          (p : ℝ) * ∑ j ∈ Finset.range p,
            ‖X (s + j + 1) i - X (s + j) i‖ ^ 2 := by
      rw [hcoord]
      have hnorm :
          ‖∑ j ∈ Finset.range p,
              (X (s + j + 1) i - X (s + j) i)‖ ≤
            ∑ j ∈ Finset.range p,
              ‖X (s + j + 1) i - X (s + j) i‖ :=
        norm_sum_le _ _
      have hsquares := sq_sum_le_card_mul_sum_sq
        (s := Finset.range p)
        (f := fun j => ‖X (s + j + 1) i - X (s + j) i‖)
      simp only [Finset.card_range] at hsquares
      nlinarith [norm_nonneg
        (∑ j ∈ Finset.range p,
          (X (s + j + 1) i - X (s + j) i))]
    simp only [dependentProductNormSq_def]
    calc
      ∑ i : ι, ‖X (s + p) i - X s i‖ ^ 2 ≤
          ∑ i : ι, (p : ℝ) * ∑ j ∈ Finset.range p,
            ‖X (s + j + 1) i - X (s + j) i‖ ^ 2 :=
        Finset.sum_le_sum fun i _hi => hpoint i
      _ = (p : ℝ) * ∑ j ∈ Finset.range p, ∑ i : ι,
          ‖X (s + j + 1) i - X (s + j) i‖ ^ 2 := by
        rw [Finset.sum_comm, Finset.mul_sum]
  calc
    dependentProductNormSq (A Y - A Z) ≤
        c ^ 2 * dependentProductNormSq (Y - Z) := hoperator
    _ ≤ c ^ 2 * (L ^ 2 * dependentProductNormSq
        (fun i => X (s + p) i - X s i)) :=
      mul_le_mul_of_nonneg_left hmap (sq_nonneg c)
    _ ≤ c ^ 2 * (L ^ 2 * ((p : ℝ) *
        ∑ j ∈ Finset.range p,
          dependentProductNormSq
            (fun i => X (s + j + 1) i - X (s + j) i))) := by
      apply mul_le_mul_of_nonneg_left
      apply mul_le_mul_of_nonneg_left hpath
      · exact sq_nonneg L
      · exact sq_nonneg c
    _ = _ := by ring

end SOptLib

/-! Promoted from Staging/List_analyticAt_map_prod.lean. -/


open scoped Matrix.Norms.Elementwise

-- Generalization plan (G0):
-- concept/name: analyticity of an evaluated ordered list product; orig was
--   quadraticRestrictedConsecutiveProduct_analyticAt_start.
-- generality used: an arbitrary nontrivially normed scalar field, normed parameter
--   space, normed coefficient algebra, and finite square-matrix index;
--   no measure, stochasticity, convexity, smoothness, oracle, or finite-dimensional
--   assumption on the parameter space is used.
-- portable call pattern: analytic perturbation, periodic linear-system, transfer-
--   matrix, and matrix-recursion proofs change the algebra, parameter space, finite
--   factor list, and base point while retaining analyticity of the evaluated product.
-- counterargument checked: this is not paper-local or a pure wrapper because matrix
--   factor order matters and Mathlib's finite-product analytic theorem is restricted
--   to commutative rings; matrix multiplication under the product-space norm must be
--   handled entrywise through finite sums rather than by a `NormedRing` instance.
-- coverage search: queries "finite ordered list product analytic at point each factor
--   analytic", "List prod AnalyticAt NormedRing NormedAlgebra", and "ordered
--   noncommutative list product of analytic functions is analytic" found Mathlib's
--   `AnalyticAt.mul` and commutative `Finset.analyticAt_fun_prod`, but no List theorem;
--   SOptLib searches found ordered-list algebra lemmas with different conclusions.
-- minimal hypotheses: `Fintype` and `DecidableEq` support square-matrix multiplication;
--   the coefficient `NormedRing` and `NormedAlgebra` support analytic entry products
--   and sums; completeness and finite dimensionality of the parameter space are unused.

namespace List

/-- Evaluating and multiplying a finite ordered list of analytic square-matrix
functions gives a matrix-valued function analytic at the same point.

Layer: Glue | Gap: Level 1 (noncommutative ordered finite-product analyticity)
Proof: induct on the list, assemble matrix analyticity entrywise, and use Mathlib's finite analytic sums and binary analytic multiplication for each matrix-product entry.
Source: Mathlib `AnalyticAt.pi`, `Finset.analyticAt_fun_sum`, `AnalyticAt.mul`, and noncommutative matrix `List.prod`
Used in: analytic parameter perturbations of finite periodic propagators and ordered transfer-matrix or linear-recursion products
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/14/proof/0
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
@[fun_prop] theorem analyticAt_matrix_map_prod
    {K E R ι : Type*}
    [NontriviallyNormedField K]
    [NormedAddCommGroup E] [NormedSpace K E]
    [NormedRing R] [NormedAlgebra K R]
    [Fintype ι] [DecidableEq ι]
    (fs : List (E → Matrix ι ι R)) (x : E)
    (hfs : ∀ f ∈ fs, AnalyticAt K f x) :
    AnalyticAt K (fun y ↦ (fs.map fun f ↦ f y).prod) x := by
  induction fs with
  | nil =>
      apply AnalyticAt.pi
      intro i
      apply AnalyticAt.pi
      intro j
      simp only [map_nil, prod_nil, Matrix.one_apply]
      fun_prop
  | cons f fs ih =>
      simp only [map_cons, prod_cons]
      apply AnalyticAt.pi
      intro i
      apply AnalyticAt.pi
      intro k
      change AnalyticAt K
        (fun y ↦ ∑ j, f y i j * (fs.map fun g ↦ g y).prod j k) x
      apply Finset.analyticAt_fun_sum
      intro j _hj
      exact
        ((analyticAt_pi_iff.mp
          (analyticAt_pi_iff.mp (hfs f (by simp)) i) j).mul
          (analyticAt_pi_iff.mp
            (analyticAt_pi_iff.mp
              (ih fun g hg ↦ hfs g (by simp [hg])) j) k))

end List

/-! Promoted from Staging/continuous_nat_rec_of_continuous_step.lean. -/


-- Generalization plan (G0):
-- concept/name: continuity of a finite natural-number recursion under
--   continuity-preserving parameterized steps; orig was
--   quadraticRestrictedHomogeneousOrbit_continuous_alpha_of_continuous_initial
-- generality used: arbitrary parameter and state types equipped only with
--   topological spaces; no measure, algebraic, metric, finite-dimensional,
--   convexity, smoothness, or oracle assumptions are used
-- portable call pattern: finite-horizon stochastic, distributed, and
--   deterministic algorithms vary the parameter space, state space,
--   time-dependent transition, initial-state family, and horizon while each
--   transition preserves continuity along the generated state family
-- counterargument checked: this is not paper-local traceability or a pure
--   caller-side expression because it packages induction through an abstract
--   time-varying recursion; Mathlib's `Continuous.iterate` covers only repeated
--   application of one parameter-free self-map
-- coverage search: searched `finite natural recursion continuous parameter
--   initial transition jointly continuous`, `continuous recursion step
--   initial`, and the full natural-language contract in Mathlib LeanSearch;
--   the closest hit was `Continuous.iterate`, whose autonomous iteration
--   signature does not cover time-varying parameterized steps, and no SOptLib
--   declaration had the required recurrence signature
-- minimal hypotheses: the proof uses only continuity of the initial family,
--   the zero recurrence equation, successor equations below the horizon, and
--   preservation of continuity along the orbit below the horizon; joint
--   continuity and all
--   finite-dimensional assumptions from the source context are unnecessary

/-- A finite natural-number recursion is continuous in a parameter when its
initial state is continuous and every step below the horizon preserves
continuity along the recursively generated state family.

Layer: Glue | Gap: Level 1 (continuity of finite parameterized time-varying recursions)
Proof: induct on the horizon, rewrite the zero and successor orbit equations, and apply the corresponding step's continuity-preservation hypothesis to the induction hypothesis.
Source: Mathlib topology APIs for `Continuous` together with natural-number induction
Used in: finite-horizon parameter sensitivity for stochastic and distributed optimization recursions whose initial state and time-varying updates depend continuously on a stepsize or model parameter
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/14/proof/1
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem continuous_nat_rec_of_continuous_step
    {P S : Type*} [TopologicalSpace P] [TopologicalSpace S]
    (step : ℕ → P → S → S) (orbit : ℕ → P → S)
    (initial : P → S) (n : ℕ)
    (horbit_zero : orbit 0 = initial)
    (horbit_succ : ∀ k < n,
      orbit (k + 1) = fun p ↦ step k p (orbit k p))
    (hinitial : Continuous initial)
    (hstep : ∀ k < n, Continuous (orbit k) →
      Continuous (fun p ↦ step k p (orbit k p))) :
    Continuous (orbit n) := by
  induction n with
  | zero =>
      simpa [horbit_zero] using hinitial
  | succ n ih =>
      rw [horbit_succ n (Nat.lt_succ_self n)]
      exact hstep n (Nat.lt_succ_self n)
        (ih
          (fun k hk => horbit_succ k (Nat.lt_succ_of_lt hk))
          (fun k hk => hstep k (Nat.lt_succ_of_lt hk)))

/-! Promoted from Staging/Asymptotics_exists_uniform_bound_of_eq_base_of_isBigO.lean. -/


open Filter Topology

-- Generalization plan (G0):
-- concept/name: uniform local bound for an indexed family equal to a base member whose
--   remainder is Big-O; orig was quadraticScalarBlockInnovationSecondMoment_expansion_uniform
-- generality used: an arbitrary pseudo-metric parameter space, index type, normed output type,
--   seminormed additive comparison group, subtraction on the output, base point, leading term,
--   and comparison gauge;
--   no measure, convexity, smoothness, oracle, scalar-field, or finite-dimensional assumptions
-- portable call pattern: periodic, stationary, or symmetry-invariant families vary the parameter
--   space, index type, indexed observable, leading term, and remainder gauge while reusing one
--   explicit local bound obtained from a base-index Big-O estimate
-- counterargument checked: this is not paper-local traceability or a pure rename; it composes
--   filter-level asymptotic control, an explicit metric radius, and index-invariance transport
--   into the uniform estimate consumed by downstream finite-horizon arguments
-- coverage search: queried `uniform explicit neighborhood norm bound indexed family equal base
--   index IsBigO`, `exists positive radius nonnegative constant bound of IsBigO at zero`, and the
--   corresponding LeanSearch sentence; Mathlib `Asymptotics.IsBigO.bound`,
--   `Asymptotics.IsBigO.exists_pos`, and `Metric.eventually_nhds_iff` are partial ingredients,
--   while SOptLib and the round registry contain no theorem with the complete indexed contract
-- minimal hypotheses: `PseudoMetricSpace` supplies the explicit neighborhood radius, `Norm` and
--   `Sub` supply the output remainder norm, `SeminormedAddGroup` supplies a nonnegative comparison
--   norm so the Big-O constant can be enlarged to a positive one, and eventual equality to one
--   base index is the exact local uniformity assumption used

/-- If every member of an indexed family eventually equals one base member near a point, a Big-O
estimate for the base-member remainder yields one explicit local bound uniform over all indices.

Layer: Glue | Gap: Level 1 (indexed uniformization of a base-point Big-O bound)
Proof: choose a positive Big-O constant, realize its eventual norm bound on a metric ball, and rewrite every indexed value to the base member.
Source: Mathlib asymptotic bounds (`Asymptotics.IsBigO.isBigOWith`, `Asymptotics.isBigOWith_iff`) and metric neighborhood bases (`Metric.eventually_nhds_iff`)
Used in: periodic and stationary moment expansions where index invariance turns one base-period remainder estimate into a uniform bound for every block
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/15/proof/1
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem Asymptotics.exists_uniform_bound_of_eq_base_of_isBigO
    {X ι E G : Type*} [PseudoMetricSpace X]
    [Norm E] [Sub E] [SeminormedAddGroup G]
    (x₀ : X) (i₀ : ι) (F : X → ι → E) (L : X → E) (g : X → G)
    (hbase : Asymptotics.IsBigO (𝓝 x₀) (fun x => F x i₀ - L x) g)
    (h_eq : ∀ᶠ x in 𝓝 x₀, ∀ i, F x i = F x i₀) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 ≤ C ∧
      ∀ x, dist x x₀ < ε → ∀ i, ‖F x i - L x‖ ≤ C * ‖g x‖ := by
  obtain ⟨c, hc⟩ := hbase.isBigOWith
  let C := max c 1
  have hC_pos : 0 < C :=
    lt_of_lt_of_le zero_lt_one (le_max_right c 1)
  have hC :
      Asymptotics.IsBigOWith C (𝓝 x₀) (fun x => F x i₀ - L x) g := by
    apply Asymptotics.isBigOWith_iff.mpr
    filter_upwards [Asymptotics.isBigOWith_iff.mp hc] with x hx
    exact hx.trans (mul_le_mul_of_nonneg_right (le_max_left c 1) (norm_nonneg _))
  have hevent_bound :
      ∀ᶠ x in 𝓝 x₀, ‖F x i₀ - L x‖ ≤ C * ‖g x‖ :=
    Asymptotics.isBigOWith_iff.mp hC
  have hevent :
      ∀ᶠ x in 𝓝 x₀, (∀ i, F x i = F x i₀) ∧ ‖F x i₀ - L x‖ ≤ C * ‖g x‖ :=
    h_eq.and hevent_bound
  obtain ⟨ε, hε_pos, hε⟩ := Metric.eventually_nhds_iff.mp hevent
  refine ⟨ε, C, hε_pos, hC_pos.le, ?_⟩
  intro x hx i
  rw [(hε hx).1 i]
  exact (hε hx).2

/-! Promoted from Staging/two_sided_linear_bounds_near_zero_of_isBigO_sub_linear_sq.lean. -/


open Filter Topology

-- Generalization plan (G0):
-- concept/name: two-sided linear bounds near zero from a positive linear term
--   and a quadratic Big-O remainder; orig was
--   quadraticScalarPeriodDenominator_smallAlpha_linear_bounds
-- generality used: an arbitrary real-valued function, a real linear coefficient,
--   positivity of that coefficient, and a quadratic Big-O remainder at zero; no
--   measure, convexity, smoothness, oracle, normed-space, or finite-dimensional
--   assumptions are used
-- portable call pattern: asymptotic stability, denominator, and quotient proofs
--   vary the real function and its positive first-order coefficient while reusing
--   positive lower and upper linear controls on a small positive interval
-- counterargument checked: this is not paper-local traceability or a pure wrapper;
--   it packages the nontrivial conversion from a filter-level quadratic remainder
--   estimate to uniform ordered two-sided bounds with positive witnesses
-- coverage search: searched `two sided linear bounds near zero positive coefficient
--   big O square remainder`, `function equals positive linear term plus order alpha
--   squared upper lower bounds`, and the corresponding LeanSearch query; Mathlib
--   provides `Asymptotics.IsBigO.exists_pos` and `isBigOWith_iff` as components,
--   while neither Mathlib nor SOptLib provides the combined ordered conclusion
-- minimal hypotheses: the proof uses exactly positivity of the real coefficient
--   and the stated Big-O remainder; analyticity and a derivative hypothesis belong
--   to upstream ways of establishing the remainder and are not required here

/-- A function with a positive linear term and a quadratic Big-O remainder has
positive two-sided linear bounds on a sufficiently small positive interval.

Layer: Glue | Gap: Level 1 (ordered linear bounds from a quadratic asymptotic remainder)
Proof: choose a positive Big-O constant, realize its eventual norm bound on a metric neighborhood of zero, and shrink the interval until the quadratic error is at most half of the positive linear term.
Source: Mathlib asymptotic Big-O bounds, metric neighborhood filters, real absolute values, and ordered-field arithmetic
Used in: small-stepsize stability and quotient estimates that require a first-order denominator or contraction gap to be uniformly comparable to the positive stepsize
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/15/proof/3
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem two_sided_linear_bounds_near_zero_of_isBigO_sub_linear_sq
    (f : ℝ → ℝ) (d : ℝ)
    (hd_pos : 0 < d)
    (hrem : Asymptotics.IsBigO (nhds 0)
      (fun alpha : ℝ => f alpha - alpha * d)
      (fun alpha : ℝ => alpha ^ 2)) :
    ∃ alpha0 dlow dup : ℝ,
      0 < alpha0 ∧ 0 < dlow ∧ 0 < dup ∧
        ∀ alpha : ℝ, 0 < alpha → alpha ≤ alpha0 →
          dlow * alpha ≤ f alpha ∧ f alpha ≤ dup * alpha := by
  obtain ⟨C, hC_pos, hCbig⟩ := hrem.exists_pos
  have hbound_eventually :
      ∀ᶠ alpha : ℝ in nhds 0,
        ‖f alpha - alpha * d‖ ≤ C * ‖alpha ^ 2‖ := by
    exact Asymptotics.isBigOWith_iff.mp hCbig
  obtain ⟨eps, heps_pos, hbound_eps⟩ :=
    Metric.eventually_nhds_iff.mp hbound_eventually
  let dlow : ℝ := d / 2
  let dup : ℝ := 3 * d / 2
  let alpha0 : ℝ := min (eps / 2) (d / (2 * C))
  have hdlow_pos : 0 < dlow := by
    dsimp [dlow]
    positivity
  have hdup_pos : 0 < dup := by
    dsimp [dup]
    positivity
  have hd_div_pos : 0 < d / (2 * C) := by
    positivity
  have halpha0_pos : 0 < alpha0 := by
    dsimp [alpha0]
    exact lt_min (half_pos heps_pos) hd_div_pos
  refine ⟨alpha0, dlow, dup, halpha0_pos, hdlow_pos, hdup_pos, ?_⟩
  intro alpha halpha_pos halpha_le
  have halpha_nonneg : 0 ≤ alpha := le_of_lt halpha_pos
  have halpha_le_eps_half : alpha ≤ eps / 2 := by
    exact le_trans halpha_le (min_le_left _ _)
  have halpha_lt_eps : alpha < eps := by
    nlinarith
  have hdist : dist alpha 0 < eps := by
    simpa [Real.dist_eq, abs_of_pos halpha_pos] using halpha_lt_eps
  have hraw_bound := hbound_eps hdist
  have herror_abs :
      |f alpha - alpha * d| ≤ C * alpha ^ 2 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg alpha)] using hraw_bound
  have halpha_le_d_div : alpha ≤ d / (2 * C) := by
    exact le_trans halpha_le (min_le_right _ _)
  have hC_alpha_le : C * alpha ≤ d / 2 := by
    calc
      C * alpha ≤ C * (d / (2 * C)) :=
        mul_le_mul_of_nonneg_left halpha_le_d_div (le_of_lt hC_pos)
      _ = d / 2 := by
        field_simp [ne_of_gt hC_pos]
  have hrem_le : C * alpha ^ 2 ≤ (d / 2) * alpha := by
    have hmul := mul_le_mul_of_nonneg_right hC_alpha_le halpha_nonneg
    nlinarith
  have herror_le :
      |f alpha - alpha * d| ≤ (d / 2) * alpha :=
    le_trans herror_abs hrem_le
  have htwo := abs_le.mp herror_le
  constructor
  · dsimp [dlow]
    nlinarith
  · dsimp [dup]
    nlinarith

/-! Promoted from Staging/Asymptotics_isLittleO_inv_add_sq_add_exp_div_of_tendsto_zero_mul_atTop.lean. -/


open Filter Topology

-- Generalization plan (G0):
-- concept/name: a little-o estimate for an inverse-horizon, squared-scale, and
--   normalized exponential-tail remainder; orig was
--   quadraticScalarUniformRemainder_isLittleO_scale
-- generality used: a real sequence indexed by natural horizons and a positive
--   real exponential rate; no measure, convexity, smoothness, oracle,
--   normed-space, or finite-dimensional assumptions are used
-- portable call pattern: diminishing-stepsize convergence and rate proofs vary
--   the positive sequence and exponential decay rate while reusing the same
--   three-term remainder estimate under convergence to zero and divergence of
--   the stepsize-horizon product
-- counterargument checked: the source declaration is not merely a paper-facing
--   rename or caller-side expression; it packages the nontrivial simultaneous
--   comparison of an inverse horizon, a squared stepsize, and a normalized
--   exponential tail with a mixed leading scale
-- coverage search: searched `IsLittleO exponential quotient sequence product
--   tends to infinity`, `inverse horizon squared sequence exponential divided
--   product little o inverse product plus sequence tendsto zero`, and the full
--   natural-language contract with Mathlib LeanSearch; Mathlib returned only
--   generic little-o characterizations and SOptLib had no matching compound
--   estimate, so the paper-local source theorem was the sole complete hit
-- minimal hypotheses: eventual positivity was removed because divergence of
--   `alphaSeq T * T` to positive infinity already implies it; positivity of the
--   exponential rate and the two stated limit assumptions are otherwise used

/-- If a real sequence tends to zero while its product with the natural horizon
tends to positive infinity, then the sum of its inverse-horizon, squared-scale,
and normalized exponential-tail errors is little-o of the inverse-product plus
sequence scale.

Layer: Glue | Gap: Level 1 (compound diminishing-scale exponential-tail estimate)
Proof: derive eventual positivity from divergence of the sequence-horizon product, make the exponential tail tend to zero, and bound all three nonnegative remainder terms by vanishing coefficients times the common comparison scale.
Source: Mathlib filter limits at infinity, real exponential decay at negative infinity, and asymptotic little-o bounds
Used in: diminishing-stepsize stochastic approximation and distributed-optimization expansions that discard finite-horizon, quadratic, and geometrically decaying transient errors against their two leading scales
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/15/proof/6
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem Asymptotics.isLittleO_inv_add_sq_add_exp_div_of_tendsto_zero_mul_atTop
    {alphaSeq : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (halpha : Tendsto alphaSeq atTop (nhds 0))
    (hprod : Tendsto (fun T : ℕ => alphaSeq T * (T : ℝ)) atTop atTop) :
    Asymptotics.IsLittleO atTop
      (fun T : ℕ =>
        (T : ℝ)⁻¹ + alphaSeq T ^ 2 +
          Real.exp (-(c * alphaSeq T * (T : ℝ))) /
            (alphaSeq T * (T : ℝ)))
      (fun T : ℕ => (alphaSeq T * (T : ℝ))⁻¹ + alphaSeq T) := by
  classical
  let q : ℕ → ℝ := fun T => alphaSeq T * (T : ℝ)
  let scale : ℕ → ℝ := fun T => (q T)⁻¹ + alphaSeq T
  have hq : Tendsto q atTop atTop := by
    simpa [q] using hprod
  have hpos : ∀ᶠ T in atTop, 0 < alphaSeq T := by
    filter_upwards [hq.eventually_gt_atTop 0] with T hqT
    by_contra hnot
    have halpha_nonpos : alphaSeq T ≤ 0 := le_of_not_gt hnot
    have hq_nonpos : q T ≤ 0 := by
      dsimp [q]
      exact mul_nonpos_of_nonpos_of_nonneg halpha_nonpos (Nat.cast_nonneg T)
    exact (not_lt_of_ge hq_nonpos) hqT
  have hexp_tendsto :
      Tendsto (fun T : ℕ => Real.exp (-(c * q T))) atTop (nhds 0) := by
    have hcq : Tendsto (fun T : ℕ => c * q T) atTop atTop :=
      hq.const_mul_atTop hc
    have hneg : Tendsto (fun T : ℕ => -(c * q T)) atTop atBot :=
      tendsto_neg_atBot_iff.mpr hcq
    exact Real.tendsto_exp_atBot.comp hneg
  refine Asymptotics.IsLittleO.of_bound ?_
  intro eps heps
  have heps4 : 0 < eps / 4 := by positivity
  have hsmall_alpha_abs :
      ∀ᶠ T : ℕ in atTop, dist (alphaSeq T) 0 < eps / 4 :=
    (Metric.tendsto_nhds.mp halpha) (eps / 4) heps4
  have hsmall_alpha : ∀ᶠ T : ℕ in atTop, alphaSeq T ≤ eps / 4 := by
    filter_upwards [hpos, hsmall_alpha_abs] with T hApos hAdist
    have hAabs : |alphaSeq T| < eps / 4 := by
      simpa [Real.dist_eq] using hAdist
    exact le_of_lt (lt_of_le_of_lt (le_abs_self (alphaSeq T)) hAabs)
  have hsmall_exp_abs :
      ∀ᶠ T : ℕ in atTop, dist (Real.exp (-(c * q T))) 0 < eps / 4 :=
    (Metric.tendsto_nhds.mp hexp_tendsto) (eps / 4) heps4
  have hsmall_exp :
      ∀ᶠ T : ℕ in atTop, Real.exp (-(c * q T)) ≤ eps / 4 := by
    filter_upwards [hsmall_exp_abs] with T hdist
    have habs : |Real.exp (-(c * q T))| < eps / 4 := by
      simpa [Real.dist_eq] using hdist
    exact le_of_lt (lt_of_le_of_lt (le_abs_self _) habs)
  have hq_ge_one : ∀ᶠ T : ℕ in atTop, (1 : ℝ) ≤ q T :=
    hq.eventually (eventually_ge_atTop (1 : ℝ))
  filter_upwards [hpos, hsmall_alpha, hsmall_exp, hq_ge_one]
    with T hApos hAle hEle hq1
  have hAnonneg : 0 ≤ alphaSeq T := le_of_lt hApos
  have hq_pos : 0 < q T := lt_of_lt_of_le zero_lt_one hq1
  have hq_nonneg : 0 ≤ q T := le_of_lt hq_pos
  have hqinv_nonneg : 0 ≤ (q T)⁻¹ := inv_nonneg.mpr hq_nonneg
  have hscale_nonneg : 0 ≤ scale T := add_nonneg hqinv_nonneg hAnonneg
  have hT_pos : 0 < (T : ℝ) := by
    by_contra hnot
    have hT_nonpos : (T : ℝ) ≤ 0 := le_of_not_gt hnot
    have hT_zero : (T : ℝ) = 0 :=
      le_antisymm hT_nonpos (Nat.cast_nonneg T)
    have hq_zero : q T = 0 := by simp [q, hT_zero]
    linarith
  have hT_nonneg : 0 ≤ (T : ℝ) := le_of_lt hT_pos
  have hT_ne : (T : ℝ) ≠ 0 := ne_of_gt hT_pos
  have hA_ne : alphaSeq T ≠ 0 := ne_of_gt hApos
  have htermT_eq : (T : ℝ)⁻¹ = alphaSeq T * (q T)⁻¹ := by
    simp [q]
    field_simp [hA_ne, hT_ne]
  have htermT_le : (T : ℝ)⁻¹ ≤ alphaSeq T * scale T := by
    rw [htermT_eq]
    have hmul := mul_le_mul_of_nonneg_left
      (show (q T)⁻¹ ≤ scale T by
        dsimp [scale]
        nlinarith [hAnonneg]) hAnonneg
    simpa using hmul
  have htermA_le : alphaSeq T ^ 2 ≤ alphaSeq T * scale T := by
    have hmul := mul_le_mul_of_nonneg_left
      (show alphaSeq T ≤ scale T by
        dsimp [scale]
        nlinarith [hqinv_nonneg]) hAnonneg
    simpa [pow_two] using hmul
  have htermE_eq :
      Real.exp (-(c * alphaSeq T * (T : ℝ))) /
          (alphaSeq T * (T : ℝ)) =
        Real.exp (-(c * q T)) * (q T)⁻¹ := by
    dsimp [q]
    field_simp [hA_ne, hT_ne]
  have htermE_le :
      Real.exp (-(c * alphaSeq T * (T : ℝ))) /
          (alphaSeq T * (T : ℝ)) ≤
        Real.exp (-(c * q T)) * scale T := by
    rw [htermE_eq]
    exact mul_le_mul_of_nonneg_left
      (show (q T)⁻¹ ≤ scale T by
        dsimp [scale]
        nlinarith [hAnonneg]) (Real.exp_nonneg _)
  have hcoeff_le :
      alphaSeq T + alphaSeq T + Real.exp (-(c * q T)) ≤ eps := by
    nlinarith [hAle, hEle]
  have hsum_le :
      (T : ℝ)⁻¹ + alphaSeq T ^ 2 +
          Real.exp (-(c * alphaSeq T * (T : ℝ))) /
            (alphaSeq T * (T : ℝ)) ≤ eps * scale T := by
    have hsum_aux :
        (T : ℝ)⁻¹ + alphaSeq T ^ 2 +
            Real.exp (-(c * alphaSeq T * (T : ℝ))) /
              (alphaSeq T * (T : ℝ)) ≤
          (alphaSeq T + alphaSeq T + Real.exp (-(c * q T))) * scale T := by
      calc
        (T : ℝ)⁻¹ + alphaSeq T ^ 2 +
            Real.exp (-(c * alphaSeq T * (T : ℝ))) /
              (alphaSeq T * (T : ℝ))
            ≤ alphaSeq T * scale T + alphaSeq T * scale T +
                Real.exp (-(c * q T)) * scale T := by
              nlinarith [htermT_le, htermA_le, htermE_le]
        _ = (alphaSeq T + alphaSeq T + Real.exp (-(c * q T))) * scale T := by
              ring
    exact le_trans hsum_aux
      (mul_le_mul_of_nonneg_right hcoeff_le hscale_nonneg)
  have hrem_nonneg :
      0 ≤ (T : ℝ)⁻¹ + alphaSeq T ^ 2 +
          Real.exp (-(c * alphaSeq T * (T : ℝ))) /
            (alphaSeq T * (T : ℝ)) := by
    exact add_nonneg
      (add_nonneg (inv_nonneg.mpr hT_nonneg) (sq_nonneg _))
      (div_nonneg (Real.exp_nonneg _)
        (mul_nonneg hAnonneg hT_nonneg))
  have hnorm_left :
      ‖(T : ℝ)⁻¹ + alphaSeq T ^ 2 +
          Real.exp (-(c * alphaSeq T * (T : ℝ))) /
            (alphaSeq T * (T : ℝ))‖ =
        (T : ℝ)⁻¹ + alphaSeq T ^ 2 +
          Real.exp (-(c * alphaSeq T * (T : ℝ))) /
            (alphaSeq T * (T : ℝ)) := by
    simpa [Real.norm_eq_abs] using abs_of_nonneg hrem_nonneg
  have hnorm_right :
      ‖(alphaSeq T * (T : ℝ))⁻¹ + alphaSeq T‖ = scale T := by
    have hraw : |(alphaSeq T * (T : ℝ))⁻¹ + alphaSeq T| = scale T := by
      simpa [scale, q] using (abs_of_nonneg hscale_nonneg)
    simpa [Real.norm_eq_abs] using hraw
  rw [hnorm_left, hnorm_right]
  exact hsum_le

/-! Promoted from Staging/finite_family_abs_sub_le_mul_of_differentiableAt.lean. -/


open Topology
open scoped BigOperators

-- Generalization plan (G0):
-- concept/name: common local linear bound for a finite differentiable family;
--   orig was `quadraticScalarWithinPeriodMultiplier_residue_uniform_bound`
-- generality used: an arbitrary finite index type and real-valued functions
--   differentiable at zero, normalized there to arbitrary prescribed constants;
--   no measure, convexity, smoothness, completeness, or finite-dimensional
--   assumptions are needed
-- portable call pattern: periodic, cyclic, and finite-mode algorithm analyses
--   vary the finite phase type, normalized scalar functions, and base values
--   while retaining one positive radius and one nonnegative linear-growth
--   constant for every mode
-- counterargument checked: this is not paper-local traceability or a one-line
--   wrapper; it combines pointwise differentiability, finite aggregation,
--   asymptotic norm control, neighborhood extraction, and summand domination
--   into a common quantitative bound
-- coverage search: queried `finite family absolute difference upper bound
--   linear near zero of differentiableAt and value at zero`, `exists positive
--   radius nonnegative constant all finite indices abs f x sub f zero le
--   constant mul x differentiableAt`, and `DifferentiableAt finite family norm
--   difference common local linear bound`; Mathlib's
--   `DifferentiableWithinAt.isBigO_sub` supplies only the pointwise asymptotic
--   ingredient, and no Mathlib, SOptLib, or approved round entry supplies the
--   finite-family common-radius conclusion
-- minimal hypotheses: `Fintype I` is used to aggregate all members, each
--   pointwise differentiability hypothesis produces its local linear bound,
--   and each normalization equality rewrites the bound to the prescribed
--   constant; all hypotheses are used

/-- A finite family of real functions differentiable at zero and normalized to
prescribed values has a common one-sided local linear bound.

Layer: Glue | Gap: Level 1 (finite-family common local linear bound)
Proof: turn each differentiability hypothesis into a Big-O bound, sum their absolute residues, and extract one metric neighborhood and positive Big-O constant; each nonnegative summand is then bounded by the aggregate.
Source: Mathlib Fréchet differentiability Big-O estimates, finite-sum asymptotics, and metric neighborhood filters
Used in: periodic, cyclic, and finite-mode stochastic-optimization proofs that need one small positive stepsize range controlling every normalized phase function
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/15/proof/5
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem finite_family_abs_sub_le_mul_of_differentiableAt
    {I : Type*} [Fintype I]
    (f : I → ℝ → ℝ) (c : I → ℝ)
    (hf : ∀ i, DifferentiableAt ℝ (f i) 0)
    (hfc : ∀ i, f i 0 = c i) :
    ∃ delta C : ℝ,
      0 < delta ∧ 0 ≤ C ∧
        ∀ x : ℝ, 0 < x → x ≤ delta →
          ∀ i : I, |f i x - c i| ≤ C * x := by
  classical
  let residue : ℝ → ℝ := fun x ↦ ∑ i : I, |f i x - c i|
  have hresidueO :
      Asymptotics.IsBigO (nhds 0) residue (fun x : ℝ ↦ x) := by
    dsimp [residue]
    apply Asymptotics.IsBigO.sum
    intro i _hi
    have hiO :
        (fun x : ℝ ↦ f i x - f i 0) =O[nhds (0 : ℝ)]
          (fun x : ℝ ↦ x - 0) :=
      (hf i).isBigO_sub
    simpa [hfc i, Real.norm_eq_abs] using hiO.norm_left
  obtain ⟨C, hC_pos, hCO⟩ := hresidueO.exists_pos
  have hbound_eventually :
      ∀ᶠ x : ℝ in nhds 0, ‖residue x‖ ≤ C * ‖x‖ := by
    simpa using (Asymptotics.isBigOWith_iff.mp hCO)
  obtain ⟨eps, heps_pos, hbound_eps⟩ :=
    Metric.eventually_nhds_iff.mp hbound_eventually
  let delta : ℝ := eps / 2
  have hdelta_pos : 0 < delta := by
    dsimp [delta]
    positivity
  refine ⟨delta, C, hdelta_pos, le_of_lt hC_pos, ?_⟩
  intro x hx_pos hx_le i
  have hx_lt_eps : x < eps := by
    dsimp [delta] at hx_le
    linarith
  have hdist : dist x 0 < eps := by
    simpa [Real.dist_eq, abs_of_pos hx_pos] using hx_lt_eps
  have hbound := hbound_eps hdist
  have hresidue_nonneg : 0 ≤ residue x := by
    dsimp [residue]
    exact Finset.sum_nonneg fun i _hi ↦ abs_nonneg _
  have hresidue_le : residue x ≤ C * x := by
    rw [Real.norm_eq_abs, abs_of_nonneg hresidue_nonneg] at hbound
    simpa [abs_of_pos hx_pos] using hbound
  have hterm_le : |f i x - c i| ≤ residue x := by
    dsimp [residue]
    exact Finset.single_le_sum
      (fun j _hj ↦ abs_nonneg (f j x - c j))
      (Finset.mem_univ i)
  exact hterm_le.trans hresidue_le

/-! Promoted from Staging/analyticAt_sub_isBigO_sq_of_value_eq_of_deriv_eq.lean. -/


open Filter Topology

-- Generalization plan (G0):
-- concept/name: quadratic-order difference of analytic maps with
--   the same first-order jet; orig was
--   quadratic_restricted_projected_period_input_coeff_row_sub_scalar_isBigO_sq_of_hasDerivAt
-- generality used: analytic maps between normed spaces over an arbitrary
--   nontrivially normed field, with an arbitrary base point, common value, and
--   common Frechet derivative; no completeness or finite-dimensional assumptions
-- portable call pattern: analytic perturbation and response comparisons vary
--   both maps, the expansion point, and their common first-order
--   jet while retaining a quadratic-order bound on their difference
-- counterargument checked: this is not paper-local traceability or a pure
--   wrapper; the existing single-function linearization theorem does not state
--   the two-function equal-jet conclusion and must be composed twice
-- coverage search: searched `analytic functions equal value derivative
--   difference big O squared displacement` and `analytic first order Taylor
--   remainder is big O square`; Mathlib's
--   `HasFPowerSeriesAt.isBigO_image_sub_norm_mul_norm_sub` is a proof component,
--   and the staged `analyticAt_sub_linearization_isBigO_sq` covers one function
--   against its linearization, but neither gives this two-function contract
-- minimal hypotheses: analyticity of both functions and identification of
--   their common value and derivative are exactly the hypotheses used

/-- Two analytic maps with the same value and Frechet derivative at a point
differ by a quadratic-order remainder there.

Layer: Glue | Gap: Level 1 (equal first-order analytic jets imply quadratic difference)
Proof: apply the analytic quadratic-remainder theorem to each function around their common linearization, subtract the two Big-O estimates, and cancel the shared affine term.
Source: Mathlib analytic formal power series and asymptotic arithmetic APIs, via `analyticAt_sub_linearization_isBigO_sq`
Used in: perturbation comparisons between a projected period-input coefficient and its scalar slow-mode approximation after matching their value and derivative
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/14/proof/2
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem analyticAt_sub_isBigO_sq_of_value_eq_of_deriv_eq
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f g : E → F} {x : E} {value : F} {deriv : E →L[𝕜] F}
    (hf : AnalyticAt 𝕜 f x) (hg : AnalyticAt 𝕜 g x)
    (hf_value : f x = value) (hg_value : g x = value)
    (hf_deriv : HasFDerivAt f deriv x) (hg_deriv : HasFDerivAt g deriv x) :
    Asymptotics.IsBigO (nhds x)
      (fun y => f y - g y)
      (fun y => ‖y - x‖ ^ 2) := by
  have hf_remainder :=
    analyticAt_sub_linearization_isBigO_sq hf hf_value hf_deriv
  have hg_remainder :=
    analyticAt_sub_linearization_isBigO_sq hg hg_value hg_deriv
  have hdiff := hf_remainder.sub hg_remainder
  refine hdiff.congr ?_ ?_
  · intro y
    dsimp
    abel
  · intro _
    rfl

/-! Promoted from Staging/Asymptotics_isBigO_const_mul_inv_add_mul_of_nonneg.lean. -/


open Filter

-- Generalization plan (G0):
-- concept/name: Big-O domination of a constant-weighted inverse-plus-linear
--   combination by its nonnegative comparison scale; orig was
--   quadratic_scalar_twoTerm_isBigO_scalar_scale
-- generality used: an arbitrary index type, filter, two real-valued functions,
--   and two real coefficients; only eventual nonnegativity of the inverse
--   input and linear scale is used, with no measure, optimization, convexity,
--   smoothness, oracle, vector-space, or finite-dimensional assumptions
-- portable call pattern: rate expansions for stochastic-gradient, distributed,
--   and variance-reduced algorithms vary both leading coefficients and the
--   positive stepsize/horizon scale while retaining an inverse-plus-linear
--   comparison scale
-- counterargument checked: Mathlib's `IsBigO.add_add` supplies the norm-valued
--   comparison `‖q⁻¹‖ + ‖alpha‖`, but does not expose the recurring raw
--   nonnegative scale `q⁻¹ + alpha`; this theorem is the faithful bridge rather
--   than paper-local traceability or a duplicate declaration
-- coverage search: searched SOptLib, Staging, and Mathlib for `Big O constant
--   times inverse plus constant times nonnegative scale`, `IsBigO add const_mul
--   nonnegative functions`, and `eventually nonnegative weighted sum big O
--   sum`; the closest complete signature is Mathlib's `IsBigO.add_add`, whose
--   right side contains norms, and no SOptLib or staged theorem has this raw
--   nonnegative comparison-scale conclusion
-- minimal hypotheses: eventual nonnegativity of `q` and `alpha` is exactly
--   what removes both norms from the `IsBigO.add_add` comparison function

/-- A constant-weighted inverse term plus a constant-weighted nonnegative term
is Big-O of the corresponding inverse-plus-linear scale.

Layer: Glue | Gap: Level 0 (raw nonnegative comparison scale for a two-term Big-O sum)
Proof: apply Mathlib's `IsBigO.add_add` to the two constant multiples, then use eventual nonnegativity to remove the norms from its comparison function.
Source: Mathlib asymptotic comparison under addition and constant multiplication, with ordered-field inverse and absolute-value identities
Used in: stochastic and distributed optimization rate expansions that compare bias-over-horizon plus stepsize variance against their shared inverse-plus-linear scale
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/16/proof/4
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem Asymptotics.isBigO_const_mul_inv_add_mul_of_nonneg
    {ι : Type*} {l : Filter ι} (A B : ℝ) (q alpha : ι → ℝ)
    (hq : ∀ᶠ x in l, 0 ≤ q x) (halpha : ∀ᶠ x in l, 0 ≤ alpha x) :
    Asymptotics.IsBigO l
      (fun x ↦ A / q x + B * alpha x)
      (fun x ↦ (q x)⁻¹ + alpha x) := by
  have h :=
    (Asymptotics.isBigO_const_mul_self A (fun x ↦ (q x)⁻¹) l).add_add
      (Asymptotics.isBigO_const_mul_self B alpha l)
  refine h.congr' (Filter.Eventually.of_forall fun x ↦ by simp only [div_eq_mul_inv]) ?_
  filter_upwards [hq, halpha] with x hqx halphax
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hqx),
    abs_of_nonneg halphax]

/-! Promoted from Staging/Matrix_continuous_toContinuousLinearMap_mulVecLin.lean. -/


-- Generalization plan (G0):
-- concept/name: continuity of the concrete finite-matrix action as a continuous
--   linear operator; orig was `realMatrixContinuousLinearMap_continuous`, renamed
--   `Matrix.continuous_toContinuousLinearMap_mulVecLin`
-- generality used: an arbitrary complete nontrivially normed field and arbitrary
--   finite row/column index type; no inner product, nonempty-index, or paper setup assumptions
-- portable call pattern: matrix perturbation and spectral-continuation proofs can
--   transport continuity of a parameterized finite matrix family to its induced
--   continuous operator while changing the scalar field and finite row/column types
-- counterargument checked: `Matrix.continuous_toContinuousLinearMapAlgEquiv` covers
--   the same construction through an algebra equivalence but exposes `DecidableEq`;
--   this concrete theorem removes that public assumption and directly matches `mulVecLin`
-- coverage search: queries "matrix mulVec continuous linear map depends continuously
--   on matrix entries" and "toContinuousLinearMap mulVecLin continuity finite matrix"
--   found Mathlib `Continuous.matrix_mulVec` and the staged
--   `Matrix.continuous_toContinuousLinearMapAlgEquiv`; neither states this
--   assumption-minimal operator-valued continuity result
-- minimal hypotheses: `CompleteSpace 𝕜` is required by
--   `LinearMap.toContinuousLinearMap`; `Fintype m` and `Fintype n` supply
--   finite-dimensionality;
--   decidable equality is used only classically inside the proof

namespace Matrix

/-- The continuous linear operator induced by a finite rectangular matrix depends
continuously on the matrix entries.

Layer: Glue | Gap: Level 0 (finite-matrix action continuity in operator norm)
Proof: bundle the construction as a linear map from matrices to continuous endomorphisms, then use finite-dimensional continuity of linear maps.
Source: Mathlib finite matrix actions and finite-dimensional continuity, especially `Matrix.mulVecLin`, `LinearMap.toContinuousLinearMap`, and `LinearMap.continuous_of_finiteDimensional`
Used in: matrix perturbation and spectral-continuation steps that lift a continuous family of finite matrices to a continuous family of bounded coordinate-space operators
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/algorithm_spec
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem continuous_toContinuousLinearMap_mulVecLin
    {𝕜 m n : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [Fintype m] [Fintype n] :
    Continuous
      (fun A : Matrix m n 𝕜 =>
        LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)) := by
  classical
  let L : Matrix m n 𝕜 →ₗ[𝕜] ((n → 𝕜) →L[𝕜] (m → 𝕜)) :=
    { toFun := fun A => LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)
      map_add' := by
        intro A B
        ext x i
        simp
      map_smul' := by
        intro c A
        ext x i
        simp }
  change Continuous L
  exact L.continuous_of_finiteDimensional

end Matrix

/-! Promoted from Staging/real_balancing_remainder_le_inv_sqrt.lean. -/


-- Generalization plan (G0):
-- concept/name: explicit inverse-square-root bound for a square-root-balanced remainder;
--   orig was the local block hTinv_bound/halpha_sq_bound/hexp_bound/hrest_bound
-- generality used: real balance scale and exponential rate, with only positivity of the
--   scale, nonnegativity of the rate, and a natural horizon at least one
-- portable call pattern: finite-time stochastic-optimization rate proofs that choose a
--   positive square-root-balanced stepsize; the scale, decay rate, and horizon vary
-- counterargument checked: not paper-local bookkeeping or a one-line wrapper, because it
--   packages three distinct horizon estimates, including an exponential transient
-- coverage search: queried inverse-square-root balancing remainder and exponential quotient
--   bounds; Mathlib had no complete match, and project hits covered only separate components
-- minimal hypotheses: the source's strict positivity assumption on the exponential rate is
--   weakened to nonnegativity; all remaining hypotheses are used

/-- At a square-root-balanced scale, the reciprocal-horizon, squared-scale, and
exponential-transient remainder is bounded by an explicit inverse-square-root rate.

Layer: Glue | Gap: Level 1 (explicit square-root-balanced remainder aggregation)
Proof: bound the reciprocal horizon and squared balanced scale separately, rewrite the balanced horizon product as `sqrt A * sqrt T`, and use `exp x ≤ 1` for the nonpositive exponent before adding the three estimates.
Source: Mathlib real square-root identities, monotonicity of inversion on positive reals, and `Real.exp_le_one_iff`
Used in: finite-time stochastic-optimization bounds after substituting a square-root-balanced constant stepsize into a scalar expansion with reciprocal, quadratic, and exponentially decaying remainder terms
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/17/proof/10
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem real_balancing_remainder_le_inv_sqrt
    {A c : Real} (hA_pos : 0 < A) (hc_nonneg : 0 ≤ c) {T : Nat}
    (hT : 1 ≤ T) :
    ((T : Real)⁻¹) +
        (Real.sqrt A * (Real.sqrt (T : Real))⁻¹) ^ 2 +
        Real.exp (-(c * (Real.sqrt A * (Real.sqrt (T : Real))⁻¹) *
          (T : Real))) /
          ((Real.sqrt A * (Real.sqrt (T : Real))⁻¹) * (T : Real)) ≤
      (1 + A + (Real.sqrt A)⁻¹) * (Real.sqrt (T : Real))⁻¹ := by
  have hTreal_ge_one : (1 : Real) ≤ (T : Real) := by
    exact_mod_cast hT
  have hTreal_pos : 0 < (T : Real) :=
    lt_of_lt_of_le (by norm_num) hTreal_ge_one
  have hsqrtT_ge_one : (1 : Real) ≤ Real.sqrt (T : Real) := by
    simpa using Real.sqrt_le_sqrt hTreal_ge_one
  have hsqrtT_pos : 0 < Real.sqrt (T : Real) :=
    lt_of_lt_of_le (by norm_num) hsqrtT_ge_one
  have hsqrtA_pos : 0 < Real.sqrt A := Real.sqrt_pos.2 hA_pos
  have hsqrtT_ne : Real.sqrt (T : Real) ≠ 0 := ne_of_gt hsqrtT_pos
  have hinv_nonneg : 0 ≤ (Real.sqrt (T : Real))⁻¹ := by
    positivity
  have hTinv_bound :
      ((T : Real)⁻¹) ≤ (Real.sqrt (T : Real))⁻¹ := by
    have hsqrtT_le_T : Real.sqrt (T : Real) ≤ (T : Real) := by
      nlinarith [Real.sq_sqrt hTreal_pos.le]
    exact (inv_le_inv₀ hTreal_pos hsqrtT_pos).2 hsqrtT_le_T
  have halpha_sq_bound :
      (Real.sqrt A * (Real.sqrt (T : Real))⁻¹) ^ 2 ≤
        A * (Real.sqrt (T : Real))⁻¹ := by
    have hinv_le_one : (Real.sqrt (T : Real))⁻¹ ≤ 1 := by
      simpa using inv_le_one_of_one_le₀ hsqrtT_ge_one
    have hsq_sqrtA : (Real.sqrt A) ^ 2 = A :=
      Real.sq_sqrt hA_pos.le
    calc
      (Real.sqrt A * (Real.sqrt (T : Real))⁻¹) ^ 2 =
          A * ((Real.sqrt (T : Real))⁻¹) ^ 2 := by
        rw [mul_pow, hsq_sqrtA]
      _ ≤ A * (Real.sqrt (T : Real))⁻¹ := by
        have hinv_sq_le : ((Real.sqrt (T : Real))⁻¹) ^ 2 ≤
            (Real.sqrt (T : Real))⁻¹ := by
          nlinarith [sq_nonneg ((Real.sqrt (T : Real))⁻¹)]
        exact mul_le_mul_of_nonneg_left hinv_sq_le hA_pos.le
  have hprod_eq :
      (Real.sqrt A * (Real.sqrt (T : Real))⁻¹) * (T : Real) =
        Real.sqrt A * Real.sqrt (T : Real) := by
    have hsqrtT_sq : Real.sqrt (T : Real) ^ 2 = (T : Real) :=
      Real.sq_sqrt hTreal_pos.le
    field_simp [hsqrtT_ne]
    exact hsqrtT_sq.symm
  have hprod_pos :
      0 < (Real.sqrt A * (Real.sqrt (T : Real))⁻¹) * (T : Real) := by
    rw [hprod_eq]
    positivity
  have hexp_le_one :
      Real.exp (-(c * (Real.sqrt A * (Real.sqrt (T : Real))⁻¹) *
        (T : Real))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have harg_nonneg :
        0 ≤ c * ((Real.sqrt A * (Real.sqrt (T : Real))⁻¹) *
          (T : Real)) := mul_nonneg hc_nonneg hprod_pos.le
    nlinarith
  have hexp_bound :
      Real.exp (-(c * (Real.sqrt A * (Real.sqrt (T : Real))⁻¹) *
          (T : Real))) /
          ((Real.sqrt A * (Real.sqrt (T : Real))⁻¹) * (T : Real)) ≤
        (Real.sqrt A)⁻¹ * (Real.sqrt (T : Real))⁻¹ := by
    calc
      Real.exp (-(c * (Real.sqrt A * (Real.sqrt (T : Real))⁻¹) *
          (T : Real))) /
          ((Real.sqrt A * (Real.sqrt (T : Real))⁻¹) * (T : Real)) ≤
          1 / ((Real.sqrt A * (Real.sqrt (T : Real))⁻¹) *
            (T : Real)) := by
        exact div_le_div_of_nonneg_right hexp_le_one hprod_pos.le
      _ = (Real.sqrt A)⁻¹ * (Real.sqrt (T : Real))⁻¹ := by
        rw [hprod_eq]
        field_simp [ne_of_gt hsqrtA_pos, ne_of_gt hsqrtT_pos]
  calc
    ((T : Real)⁻¹) +
        (Real.sqrt A * (Real.sqrt (T : Real))⁻¹) ^ 2 +
        Real.exp (-(c * (Real.sqrt A * (Real.sqrt (T : Real))⁻¹) *
          (T : Real))) /
          ((Real.sqrt A * (Real.sqrt (T : Real))⁻¹) * (T : Real)) ≤
      (Real.sqrt (T : Real))⁻¹ +
        A * (Real.sqrt (T : Real))⁻¹ +
        (Real.sqrt A)⁻¹ * (Real.sqrt (T : Real))⁻¹ := by
      exact add_le_add (add_le_add hTinv_bound halpha_sq_bound) hexp_bound
    _ = (1 + A + (Real.sqrt A)⁻¹) *
        (Real.sqrt (T : Real))⁻¹ := by ring

/-! Promoted from Staging/Real_exp_neg_two_mul_le_one_sub_pow.lean. -/


-- Generalization plan (G0):
-- concept/name: lower exponential comparison for powers of one minus a small real;
--   orig was real_exp_neg_two_mul_le_one_sub_pow
-- generality used: real scalar x and natural exponent n; only the pointwise interval
--   hypotheses 0 <= x and x <= 1 / 2
-- portable call pattern: contraction and persistence proofs lower-bound a finite power
--   after changing the contraction amount x and horizon n
-- counterargument checked: this is not paper-local bookkeeping or a pure wrapper;
--   it composes logarithm, inverse, and natural-power estimates absent as one theorem
-- coverage search: searched exponential lower bound for one-minus powers and the exact
--   exp(-2*x*n) shape; Mathlib hits Real.exp_bound_div_one_sub_of_interval,
--   Real.one_sub_le_exp_neg, and Real.le_pow_of_log_le are partial, and SOptLib has no match
-- minimal hypotheses: all already minimal for this half-interval comparison

/-- If `x` lies in `[0, 1 / 2]`, then `exp (-2 * x * n)` is at most `(1 - x) ^ n`.

Layer: Glue | Gap: Level 1 (finite-power exponential lower comparison on the half interval)
Proof: bound `log ((1 - x)⁻¹)` by `2 * x` using `Real.log_le_sub_one_of_pos`, then multiply the resulting lower bound for `log (1 - x)` by the nonnegative natural exponent and compare positive arguments through `Real.log_le_log_iff`.
Source: Mathlib real logarithm inverse, power, and ordered logarithm APIs
Used in: contraction and slow-mode persistence arguments that replace a small-loss finite power by a uniform exponential lower envelope
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/16/proof/2
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem Real.exp_neg_two_mul_le_one_sub_pow
    (x : ℝ) (n : ℕ)
    (hx_nonneg : 0 ≤ x) (hx_half : x ≤ 1 / 2) :
    Real.exp (-(2 * x * (n : ℝ))) ≤ (1 - x) ^ n := by
  have hbase_pos : 0 < 1 - x := by nlinarith
  have hinv_pos : 0 < (1 - x)⁻¹ := inv_pos.mpr hbase_pos
  have hlog_inv_le_sub :
      Real.log ((1 - x)⁻¹) ≤ (1 - x)⁻¹ - 1 :=
    Real.log_le_sub_one_of_pos hinv_pos
  have hsub_le : (1 - x)⁻¹ - 1 ≤ 2 * x := by
    have hbase_ne : 1 - x ≠ 0 := ne_of_gt hbase_pos
    field_simp [hbase_ne]
    nlinarith [mul_nonneg hx_nonneg hx_nonneg, hx_half]
  have hlog_inv_le : Real.log ((1 - x)⁻¹) ≤ 2 * x :=
    le_trans hlog_inv_le_sub hsub_le
  have hlog_base_lower : -(2 * x) ≤ Real.log (1 - x) := by
    have hlog_inv_eq : Real.log ((1 - x)⁻¹) = -Real.log (1 - x) := by
      rw [Real.log_inv]
    rw [hlog_inv_eq] at hlog_inv_le
    linarith
  have hn_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hlog_pow_lower :
      -(2 * x * (n : ℝ)) ≤ Real.log ((1 - x) ^ n) := by
    rw [Real.log_pow]
    have hmul := mul_le_mul_of_nonneg_right hlog_base_lower hn_nonneg
    nlinarith
  have hexp_pos : 0 < Real.exp (-(2 * x * (n : ℝ))) := Real.exp_pos _
  have hpow_pos : 0 < (1 - x) ^ n := pow_pos hbase_pos n
  exact (Real.log_le_log_iff hexp_pos hpow_pos).mp
    (by simpa [Real.log_exp] using hlog_pow_lower)

/-! Promoted from Staging/Real_inv_mul_le_fixed_exp_tail_of_le.lean. -/


-- Generalization plan (G0):
-- concept/name: reciprocal-product absorption by a fixed exponential-tail
--   coefficient; orig was real_inv_alpha_time_le_fixed_exp_tail
-- generality used: four real scalars `alpha`, `c`, `T`, and `p`; positivity of
--   the reciprocal product and an upper bound `alpha * T <= p`;
--   no measure, probability, convexity, smoothness, oracle, or vector-space
--   assumptions are used, and the exponential rate `c` is unrestricted
-- portable call pattern: transient, burn-in, and finite-prefix rate proofs vary
--   a positive stepsize, exponential rate, horizon, and fixed horizon cap while
--   absorbing `1 / (alpha * T)` into the normalized exponential tail
-- counterargument checked: this is not paper-local traceability or a pure
--   wrapper; it packages the bounded-horizon exponent comparison, exponential
--   cancellation, and positive-denominator transport, including the negative-rate
--   branch made valid by the fixed coefficient's additive one
-- coverage search: symbol queries for reciprocal-product exponential-tail
--   absorption and bounded-horizon exponential decay found only the source
--   theorem; Mathlib LeanSearch found `Real.exp_neg`, `Real.le_inv_mul_exp`, and
--   reciprocal-order lemmas as partial ingredients, but no matching complete
--   contract in Mathlib or SOptLib
-- minimal hypotheses: positivity of `alpha * T` makes the reciprocal denominator
--   positive, and `alpha * T <= p` is the exact comparison used in the
--   exponential argument; no sign hypothesis on `c` is needed because the
--   negative-rate tail is at least one

/-- On a bounded positive horizon, the reciprocal product is bounded by a fixed
coefficient times its normalized exponential tail.

The additive one in the fixed coefficient also covers nonpositive exponential
rates, so no sign assumption on `c` is required.

Layer: Glue | Gap: Level 1 (bounded-horizon reciprocal exponential-tail absorption)
Proof: Bound `alpha * T` by `p`; for nonnegative `c`, compare positive exponents and cancel `exp (c * alpha * T)` against its negative exponential, while for negative `c` both fixed factors dominate one. Divide the resulting unit bound by the positive product denominator.
Source: Mathlib real exponential monotonicity and cancellation together with linear ordered-field division
Used in: transient, burn-in, and finite-prefix stochastic-optimization bounds that absorb an inverse stepsize-horizon scale into a normalized exponential remainder with a horizon-independent coefficient
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/15/proof/6
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem Real.inv_mul_le_fixed_exp_tail_of_le
    {alpha c T p : ℝ} (hprod_pos : 0 < alpha * T)
    (hprod_le_p : alpha * T ≤ p) :
    (alpha * T)⁻¹ ≤
      (Real.exp (c * p) + 1) *
        (Real.exp (-(c * alpha * T)) / (alpha * T)) := by
  have hunit :
      1 ≤ (Real.exp (c * p) + 1) * Real.exp (-(c * alpha * T)) := by
    by_cases hc : 0 ≤ c
    · have hmono_arg : c * alpha * T ≤ c * p := by
        simpa [mul_assoc] using mul_le_mul_of_nonneg_left hprod_le_p hc
      have hexp_le : Real.exp (c * alpha * T) ≤ Real.exp (c * p) :=
        Real.exp_le_exp.mpr hmono_arg
      have hfactor_le :
          Real.exp (c * alpha * T) ≤ Real.exp (c * p) + 1 := by
        linarith
      have hmul := mul_le_mul_of_nonneg_right hfactor_le
        (Real.exp_pos (-(c * alpha * T))).le
      have hcancel :
          Real.exp (c * alpha * T) * Real.exp (-(c * alpha * T)) = 1 := by
        rw [← Real.exp_add]
        ring_nf
        simp
      simpa [hcancel] using hmul
    · have hc_neg : c < 0 := lt_of_not_ge hc
      have hneg : 0 ≤ -(c * alpha * T) := by
        have hcprod_neg : c * (alpha * T) < 0 :=
          mul_neg_of_neg_of_pos hc_neg hprod_pos
        exact neg_nonneg.mpr (by simpa [mul_assoc] using hcprod_neg.le)
      have hfactor_ge_one : 1 ≤ Real.exp (c * p) + 1 := by
        linarith [Real.exp_pos (c * p)]
      have htail_ge_one : 1 ≤ Real.exp (-(c * alpha * T)) :=
        Real.one_le_exp hneg
      calc
        1 = 1 * 1 := by ring
        _ ≤ (Real.exp (c * p) + 1) * Real.exp (-(c * alpha * T)) :=
          mul_le_mul hfactor_ge_one htail_ge_one (by norm_num)
            (le_trans (by norm_num) hfactor_ge_one)
  calc
    (alpha * T)⁻¹ = 1 / (alpha * T) := by rw [inv_eq_one_div]
    _ ≤ ((Real.exp (c * p) + 1) * Real.exp (-(c * alpha * T))) /
          (alpha * T) :=
      div_le_div_of_nonneg_right hunit hprod_pos.le
    _ = (Real.exp (c * p) + 1) *
        (Real.exp (-(c * alpha * T)) / (alpha * T)) := by ring

/-! Promoted from Staging/real_isBigO_nhds_zero_pow_explicit_pos_bound.lean. -/


open Filter Topology

-- Generalization plan (G0):
-- concept/name: explicit positive one-sided power bound from Big-O at zero;
--   orig was `real_isBigO_nhds_zero_pow_four_explicit_pos_bound`
-- generality used: an arbitrary real-valued function and natural exponent;
--   no measure, convexity, smoothness, oracle, normed-space parameter, or
--   finite-dimensional assumption is used
-- portable call pattern: local asymptotic estimates in perturbation, stability,
--   and stochastic-moment arguments vary the real function and power while
--   reusing a positive constant and positive stepsize radius
-- counterargument checked: this is not paper-local traceability or a pure
--   rename; it packages the conversion from a filter-level norm estimate to an
--   ordered scalar bound on an explicit positive interval
-- coverage search: searched `IsBigO positive constant positive radius upper
--   bound power` and `big O near zero explicit pointwise upper bound one-sided
--   interval`; Mathlib's `Asymptotics.isBigO_iff'`,
--   `Asymptotics.IsBigO.exists_pos`, and `Metric.eventually_nhds_iff` provide
--   components, but neither Mathlib nor SOptLib provides the combined conclusion
-- minimal hypotheses: the Big-O estimate is needed only within the positive
--   half-line; positivity of the argument removes the absolute value from its
--   natural power

/-- A real function that is Big-O of a natural power at zero admits an explicit
upper bound on a sufficiently small positive interval, with positive witnesses.

Layer: Glue | Gap: Level 1 (one-sided explicit bound from filter-level Big-O)
Proof: choose a positive Big-O constant, realize its eventual norm bound on a metric neighborhood of zero, and shrink to a positive radius where real powers are nonnegative.
Source: Mathlib asymptotic Big-O bounds, metric neighborhood filters, natural powers, and real absolute-value order
Used in: small-stepsize perturbation and stochastic-moment estimates that turn a local power-order remainder into a uniform positive-stepsize bound
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/17/proof/5
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem real_isBigO_nhds_zero_pow_explicit_pos_bound
    (f : ℝ → ℝ) (n : ℕ)
    (h : Asymptotics.IsBigO (nhdsWithin 0 (Set.Ioi 0)) f
      (fun alpha : ℝ => alpha ^ n)) :
    ∃ C alpha0 : ℝ,
      0 < C ∧ 0 < alpha0 ∧
        ∀ alpha : ℝ, 0 < alpha → alpha ≤ alpha0 →
          f alpha ≤ C * alpha ^ n := by
  obtain ⟨C, hC_pos, hbound_within⟩ := Asymptotics.isBigO_iff'.mp h
  have hbound_eventually :
      ∀ᶠ alpha : ℝ in nhds 0,
        alpha ∈ Set.Ioi 0 → ‖f alpha‖ ≤ C * ‖alpha ^ n‖ :=
    eventually_nhdsWithin_iff.mp hbound_within
  obtain ⟨eps, heps_pos, hbound_eps⟩ :=
    Metric.eventually_nhds_iff.mp hbound_eventually
  let alpha0 : ℝ := eps / 2
  have halpha0_pos : 0 < alpha0 := by
    dsimp [alpha0]
    positivity
  refine ⟨C, alpha0, hC_pos, halpha0_pos, ?_⟩
  intro alpha halpha_pos halpha_le
  have halpha_nonneg : 0 ≤ alpha := le_of_lt halpha_pos
  have halpha_lt_eps : alpha < eps := by
    dsimp [alpha0] at halpha_le
    linarith
  have hdist : dist alpha 0 < eps := by
    simpa [Real.dist_eq, abs_of_pos halpha_pos] using halpha_lt_eps
  have hbound := hbound_eps hdist halpha_pos
  have hnorm_pow : ‖alpha ^ n‖ = alpha ^ n := by
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg halpha_nonneg n)]
  have hf_le_norm : f alpha ≤ ‖f alpha‖ := by
    simpa [Real.norm_eq_abs] using le_abs_self (f alpha)
  rw [hnorm_pow] at hbound
  exact le_trans hf_le_norm hbound

/-! Promoted from Staging/Real_pow_le_exp_neg_mul_of_nonneg_of_le_one_sub.lean. -/


-- Generalization plan (G0):
-- concept/name: exponential upper bound for a natural power of a nonnegative
--   real contraction; orig was real_nonneg_pow_le_exp_neg_mul_of_le_one_sub
-- generality used: real scalars gamma and x and a natural exponent n; only the
--   pointwise hypotheses 0 <= gamma and gamma <= 1 - x
-- portable call pattern: mixing, stable-recursion, and complexity proofs replace
--   a squeezed nonnegative contraction power by an exponential tail while gamma,
--   x, and the horizon n vary
-- counterargument checked: although the proof composes short Mathlib facts, it is
--   not a pure rename; it packages monotonicity from an arbitrary dominated base,
--   the one-step exponential comparison, and the natural-power/exponential bridge
-- coverage search: semantic and symbol searches found Real.one_sub_le_exp_neg and
--   Real.one_sub_div_pow_le_exp_neg as partial matches, but no Mathlib or SOptLib
--   declaration with the arbitrary nonnegative base and exact conclusion
-- minimal hypotheses: all already pointwise and minimal for monotonicity of powers

/-- A nonnegative real bounded by `1 - x` has its `n`th power bounded by
`exp (-(x * n))`.

Layer: Glue | Gap: Level 1 (finite-power exponential upper comparison for a dominated contraction)
Proof: raise the base comparison and `Real.one_sub_le_exp_neg` to the natural power using nonnegativity, then identify the exponential power with the exponential of the scaled exponent via `Real.exp_nat_mul`.
Source: Mathlib real exponential tangent bound, ordered natural powers, and exponential monoid-homomorphism API
Used in: mixing, stable-recursion, and complexity tail estimates after a nonnegative contraction factor is squeezed above by one minus a decay amount
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/15/proof/3
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem Real.pow_le_exp_neg_mul_of_nonneg_of_le_one_sub
    {gamma x : ℝ} (n : ℕ)
    (hgamma_nonneg : 0 ≤ gamma)
    (hgamma_le : gamma ≤ 1 - x) :
    gamma ^ n ≤ Real.exp (-(x * (n : ℝ))) := by
  calc
    gamma ^ n ≤ (1 - x) ^ n :=
      pow_le_pow_left₀ hgamma_nonneg hgamma_le n
    _ ≤ Real.exp (-x) ^ n :=
      pow_le_pow_left₀ (hgamma_nonneg.trans hgamma_le)
        (Real.one_sub_le_exp_neg x) n
    _ = Real.exp (-(x * (n : ℝ))) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

/-! Promoted from Staging/Asymptotics_isBigO_quadratic_div_linear_sub_linear.lean. -/


open Filter Topology

-- Generalization plan (G0):
-- concept/name: second-order quotient expansion from quadratic-over-linear
--   leading terms; orig was real_quadratic_over_linear_isBigO_sq
-- generality used: arbitrary real-valued numerator and denominator functions,
--   two real leading coefficients, positivity of the linear denominator
--   coefficient, and the two stated Big-O remainders; no measure, convexity,
--   smoothness, oracle, normed-space, or finite-dimensional assumptions are used
-- portable call pattern: perturbation, steady-state, and ratio-asymptotic proofs
--   vary the numerator, denominator, quadratic coefficient, and positive linear
--   coefficient while reusing the same second-order quotient expansion
-- counterargument checked: this is not paper-local traceability or a one-line
--   wrapper; it proves eventual denominator separation and combines both
--   remainder estimates through a nontrivial quotient bound
-- coverage search: searched `Big O quotient expansion numerator quadratic
--   denominator positive linear`, `division of quadratic leading numerator by
--   linear leading denominator remainder`, and semantic Mathlib queries;
--   Mathlib's `isBigO_iff_div_isBoundedUnder` and inverse lemmas are only
--   components, while the staged two-sided linear-bound theorem is a
--   complementary denominator result and no complete SOptLib theorem was found
-- minimal hypotheses: positivity of the real linear coefficient and both Big-O
--   remainder hypotheses are exactly what the proof uses

/-- Dividing a quadratic-leading expansion by a positive linear-leading
expansion gives the expected linear quotient with a quadratic remainder.

Layer: Glue | Gap: Level 1 (second-order quotient expansion with a vanishing denominator)
Proof: extract eventual norm bounds for both remainders, use positivity of the denominator's linear coefficient to prove eventual denominator separation, and bound the cross-multiplied quotient error by a quadratic scale.
Source: Mathlib asymptotic Big-O bounds, neighborhood filters on the reals, absolute-value estimates, and ordered-field division
Used in: perturbation and steady-state variance expansions that divide a quadratic innovation term by a positive first-order stability gap
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/15/proof/4
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem Asymptotics.isBigO_quadratic_div_linear_sub_linear
    {N D : ℝ → ℝ} {B d : ℝ} (hd_pos : 0 < d)
    (hnum :
      Asymptotics.IsBigO (nhds 0)
        (fun alpha : ℝ => N alpha - alpha ^ 2 * B)
        (fun alpha : ℝ => alpha ^ 3))
    (hden :
      Asymptotics.IsBigO (nhds 0)
        (fun alpha : ℝ => D alpha - alpha * d)
        (fun alpha : ℝ => alpha ^ 2)) :
    Asymptotics.IsBigO (nhds 0)
      (fun alpha : ℝ => N alpha / D alpha - alpha * B / d)
      (fun alpha : ℝ => alpha ^ 2) := by
  classical
  obtain ⟨Cn, hCn_pos, hCn_big⟩ := hnum.exists_pos
  obtain ⟨Cd, hCd_pos, hCd_big⟩ := hden.exists_pos
  let C : ℝ := 2 * (d * Cn + |B| * Cd) / d ^ 2
  have hnum_eventually :
      ∀ᶠ alpha : ℝ in nhds 0,
        ‖N alpha - alpha ^ 2 * B‖ ≤ Cn * ‖alpha ^ 3‖ := by
    exact Asymptotics.isBigOWith_iff.mp hCn_big
  have hden_eventually :
      ∀ᶠ alpha : ℝ in nhds 0,
        ‖D alpha - alpha * d‖ ≤ Cd * ‖alpha ^ 2‖ := by
    exact Asymptotics.isBigOWith_iff.mp hCd_big
  have hsmall_eventually :
      ∀ᶠ alpha : ℝ in nhds 0, |alpha| < d / (2 * Cd) := by
    refine Metric.eventually_nhds_iff.mpr ?_
    refine ⟨d / (2 * Cd), by positivity, ?_⟩
    intro alpha halpha
    simpa [Real.dist_eq, abs_sub_comm] using halpha
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [hnum_eventually, hden_eventually, hsmall_eventually]
    with alpha hnum_bound hden_bound hsmall
  by_cases halpha_zero : alpha = 0
  · subst alpha
    have hN0 : N 0 = 0 := by
      have hle : ‖N 0‖ ≤ (0 : ℝ) := by
        simpa using hnum_bound
      exact norm_eq_zero.mp (le_antisymm hle (norm_nonneg _))
    simp [hN0]
  · have halpha_abs_pos : 0 < |alpha| := abs_pos.mpr halpha_zero
    have halpha_abs_nonneg : 0 ≤ |alpha| := abs_nonneg alpha
    have hden_abs_bound :
        |D alpha - alpha * d| ≤ Cd * |alpha| ^ 2 := by
      simpa [Real.norm_eq_abs, abs_pow] using hden_bound
    have hnum_abs_bound :
        |N alpha - alpha ^ 2 * B| ≤ Cn * |alpha| ^ 3 := by
      simpa [Real.norm_eq_abs, abs_pow] using hnum_bound
    have hCd_abs_le : Cd * |alpha| ≤ d / 2 := by
      have hmul := mul_lt_mul_of_pos_left hsmall hCd_pos
      have hcancel : Cd * (d / (2 * Cd)) = d / 2 := by
        field_simp [ne_of_gt hCd_pos]
      nlinarith
    have hden_err_le :
        |D alpha - alpha * d| ≤ (d / 2) * |alpha| := by
      calc
        |D alpha - alpha * d| ≤ Cd * |alpha| ^ 2 := hden_abs_bound
        _ = (Cd * |alpha|) * |alpha| := by ring
        _ ≤ (d / 2) * |alpha| :=
          mul_le_mul_of_nonneg_right hCd_abs_le halpha_abs_nonneg
    have htri :
        |alpha * d| ≤ |D alpha| + |D alpha - alpha * d| := by
      calc
        |alpha * d| = |D alpha - (D alpha - alpha * d)| := by ring_nf
        _ ≤ |D alpha| + |D alpha - alpha * d| := abs_sub _ _
    have hden_abs_lower :
        (d / 2) * |alpha| ≤ |D alpha| := by
      have hdalpha : |alpha * d| = d * |alpha| := by
        rw [abs_mul, abs_of_pos hd_pos, mul_comm]
      rw [hdalpha] at htri
      nlinarith
    have hD_abs_pos : 0 < |D alpha| :=
      lt_of_lt_of_le (mul_pos (half_pos hd_pos) halpha_abs_pos)
        hden_abs_lower
    have hD_ne : D alpha ≠ 0 := abs_pos.mp hD_abs_pos
    have hquot_eq :
        N alpha / D alpha - alpha * B / d =
          (d * (N alpha - alpha ^ 2 * B) -
              alpha * B * (D alpha - alpha * d)) / (d * D alpha) := by
      field_simp [hD_ne, ne_of_gt hd_pos]
      ring
    have hnum_total :
        |d * (N alpha - alpha ^ 2 * B) -
            alpha * B * (D alpha - alpha * d)| ≤
          (d * Cn + |B| * Cd) * |alpha| ^ 3 := by
      calc
        |d * (N alpha - alpha ^ 2 * B) -
            alpha * B * (D alpha - alpha * d)| ≤
            |d * (N alpha - alpha ^ 2 * B)| +
              |alpha * B * (D alpha - alpha * d)| := abs_sub _ _
        _ ≤ d * (Cn * |alpha| ^ 3) +
              (|alpha| * |B|) * (Cd * |alpha| ^ 2) := by
          refine add_le_add ?_ ?_
          · rw [abs_mul, abs_of_pos hd_pos]
            exact mul_le_mul_of_nonneg_left hnum_abs_bound hd_pos.le
          · rw [abs_mul, abs_mul]
            exact mul_le_mul_of_nonneg_left hden_abs_bound
              (mul_nonneg (abs_nonneg alpha) (abs_nonneg B))
        _ = (d * Cn + |B| * Cd) * |alpha| ^ 3 := by ring
    have hden_product_lower :
        (d ^ 2 / 2) * |alpha| ≤ |d * D alpha| := by
      rw [abs_mul, abs_of_pos hd_pos]
      calc
        (d ^ 2 / 2) * |alpha| = d * ((d / 2) * |alpha|) := by ring
        _ ≤ d * |D alpha| :=
          mul_le_mul_of_nonneg_left hden_abs_lower hd_pos.le
    have hden_product_pos : 0 < |d * D alpha| := by
      rw [abs_mul, abs_of_pos hd_pos]
      positivity
    have hscale_bound :
        |(d * (N alpha - alpha ^ 2 * B) -
            alpha * B * (D alpha - alpha * d)) / (d * D alpha)| ≤
          C * |alpha| ^ 2 := by
      have hnum_nonneg :
          0 ≤ |d * (N alpha - alpha ^ 2 * B) -
            alpha * B * (D alpha - alpha * d)| := abs_nonneg _
      have hden_lower_pos :
          0 < (d ^ 2 / 2) * |alpha| := by
        exact mul_pos (by positivity) halpha_abs_pos
      have hdiv_den :
          |d * (N alpha - alpha ^ 2 * B) -
              alpha * B * (D alpha - alpha * d)| / |d * D alpha| ≤
            |d * (N alpha - alpha ^ 2 * B) -
              alpha * B * (D alpha - alpha * d)| /
                ((d ^ 2 / 2) * |alpha|) := by
        exact div_le_div_of_nonneg_left hnum_nonneg hden_lower_pos
          hden_product_lower
      have hdiv_num :
          |d * (N alpha - alpha ^ 2 * B) -
              alpha * B * (D alpha - alpha * d)| /
                ((d ^ 2 / 2) * |alpha|) ≤
            ((d * Cn + |B| * Cd) * |alpha| ^ 3) /
                ((d ^ 2 / 2) * |alpha|) := by
        exact div_le_div_of_nonneg_right hnum_total hden_lower_pos.le
      have hcancel :
          ((d * Cn + |B| * Cd) * |alpha| ^ 3) /
              ((d ^ 2 / 2) * |alpha|) =
            C * |alpha| ^ 2 := by
        dsimp [C]
        field_simp [ne_of_gt hd_pos, ne_of_gt halpha_abs_pos]
      calc
        |(d * (N alpha - alpha ^ 2 * B) -
            alpha * B * (D alpha - alpha * d)) / (d * D alpha)| =
            |d * (N alpha - alpha ^ 2 * B) -
              alpha * B * (D alpha - alpha * d)| / |d * D alpha| := by
          rw [abs_div]
        _ ≤ |d * (N alpha - alpha ^ 2 * B) -
              alpha * B * (D alpha - alpha * d)| /
                ((d ^ 2 / 2) * |alpha|) := hdiv_den
        _ ≤ ((d * Cn + |B| * Cd) * |alpha| ^ 3) /
                ((d ^ 2 / 2) * |alpha|) := hdiv_num
        _ = C * |alpha| ^ 2 := hcancel
    calc
      ‖N alpha / D alpha - alpha * B / d‖ =
          |N alpha / D alpha - alpha * B / d| := Real.norm_eq_abs _
      _ = |(d * (N alpha - alpha ^ 2 * B) -
              alpha * B * (D alpha - alpha * d)) / (d * D alpha)| := by
        rw [hquot_eq]
      _ ≤ C * |alpha| ^ 2 := hscale_bound
      _ = C * ‖alpha ^ 2‖ := by simp [Real.norm_eq_abs]

/-! Promoted from Staging/Real_abs_quadratic_div_linear_sub_linear_le.lean. -/


-- Generalization plan (G0):
-- concept/name: explicit quadratic-over-linear quotient error bound; orig was
--   `real_quadratic_over_linear_uniform_bound`
-- generality used: eight scalars in a strictly ordered field, positivity of
--   the expansion scale and
--   the two linear denominator coefficients, and three pointwise error bounds;
--   no measure, convexity, smoothness, oracle, or finite-dimensional assumptions
-- portable call pattern: finite-horizon perturbation and steady-state variance
--   proofs vary the numerator, denominator, leading coefficients, and error
--   constants while retaining quadratic-over-linear leading orders
-- counterargument checked: this is not paper-local traceability or a pure
--   wrapper; it cross-multiplies and combines two remainder estimates with a
--   vanishing-denominator lower bound to produce an explicit reusable constant
-- coverage search: project and semantic searches for an explicit absolute
--   quadratic-over-linear quotient bound found Mathlib `abs_div` as a primitive,
--   `common_scale_quotient_error_le` with a different normalized-tail contract,
--   and `Asymptotics.isBigO_quadratic_div_linear_sub_linear` with a function-level
--   eventual conclusion, but no declaration covering this pointwise estimate
-- minimal hypotheses: all three positivity hypotheses and all three pointwise
--   bounds are used; separate nonnegativity assumptions on `Cn` and `Cd` are not
--   needed because their signed products occur only through the supplied bounds

/-- A quadratic-leading numerator divided by a linearly bounded denominator
differs from its linear leading quotient by an explicit quadratic error.

Layer: Glue | Gap: Level 1 (pointwise quadratic-over-linear quotient perturbation)
Proof: Cross-multiply the quotient error, bound its two remainder terms by the numerator and denominator estimates, and divide by the positive linear lower bound for the denominator.
Source: Mathlib ordered-field absolute-value, division-monotonicity, polynomial normalization, and nonlinear arithmetic APIs
Used in: finite-horizon perturbation and periodic steady-state variance expansions after obtaining uniform cubic numerator error and quadratic denominator error estimates
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/15/proof/4
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem abs_quadratic_div_linear_sub_linear_le
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {alpha N D B d Cn Cd dlow : K}
    (halpha_pos : 0 < alpha) (hd_pos : 0 < d) (hdlow_pos : 0 < dlow)
    (hnum_bound : |N - alpha ^ 2 * B| ≤ Cn * alpha ^ 3)
    (hD_lower : dlow * alpha ≤ D)
    (hden_close : |D - alpha * d| ≤ Cd * alpha ^ 2) :
    |N / D - alpha * B / d| ≤
      ((d * Cn + |B| * Cd) / (d * dlow)) * alpha ^ 2 := by
  have halpha_nonneg : 0 ≤ alpha := halpha_pos.le
  have hD_pos : 0 < D :=
    lt_of_lt_of_le (mul_pos hdlow_pos halpha_pos) hD_lower
  have hD_ne : D ≠ 0 := ne_of_gt hD_pos
  have hquot_eq :
      N / D - alpha * B / d =
        (d * (N - alpha ^ 2 * B) -
            alpha * B * (D - alpha * d)) / (d * D) := by
    field_simp [hD_ne, ne_of_gt hd_pos]
    ring
  have hnum_total :
      |d * (N - alpha ^ 2 * B) -
          alpha * B * (D - alpha * d)| ≤
        (d * Cn + |B| * Cd) * alpha ^ 3 := by
    calc
      |d * (N - alpha ^ 2 * B) -
          alpha * B * (D - alpha * d)| ≤
          |d * (N - alpha ^ 2 * B)| +
            |alpha * B * (D - alpha * d)| := abs_sub _ _
      _ ≤ d * (Cn * alpha ^ 3) +
            (alpha * |B|) * (Cd * alpha ^ 2) := by
        refine add_le_add ?_ ?_
        · rw [abs_mul, abs_of_pos hd_pos]
          exact mul_le_mul_of_nonneg_left hnum_bound hd_pos.le
        · rw [abs_mul, abs_mul, abs_of_pos halpha_pos]
          exact mul_le_mul_of_nonneg_left hden_close
            (mul_nonneg halpha_nonneg (abs_nonneg B))
      _ = (d * Cn + |B| * Cd) * alpha ^ 3 := by ring
  have hden_product_lower :
      d * dlow * alpha ≤ |d * D| := by
    rw [abs_mul, abs_of_pos hd_pos, abs_of_pos hD_pos]
    nlinarith [mul_le_mul_of_nonneg_left hD_lower hd_pos.le]
  have hden_product_pos : 0 < d * dlow * alpha :=
    mul_pos (mul_pos hd_pos hdlow_pos) halpha_pos
  rw [hquot_eq, abs_div]
  have hdiv_den :
      |d * (N - alpha ^ 2 * B) -
          alpha * B * (D - alpha * d)| / |d * D| ≤
        |d * (N - alpha ^ 2 * B) -
          alpha * B * (D - alpha * d)| / (d * dlow * alpha) :=
    div_le_div_of_nonneg_left (abs_nonneg _) hden_product_pos
      hden_product_lower
  have hdiv_num :
      |d * (N - alpha ^ 2 * B) -
          alpha * B * (D - alpha * d)| / (d * dlow * alpha) ≤
        ((d * Cn + |B| * Cd) * alpha ^ 3) /
          (d * dlow * alpha) :=
    div_le_div_of_nonneg_right hnum_total hden_product_pos.le
  have hcancel :
      ((d * Cn + |B| * Cd) * alpha ^ 3) /
          (d * dlow * alpha) =
        ((d * Cn + |B| * Cd) / (d * dlow)) * alpha ^ 2 := by
    field_simp [ne_of_gt hd_pos, ne_of_gt hdlow_pos, ne_of_gt halpha_pos]
  exact le_trans hdiv_den (le_trans hdiv_num (le_of_eq hcancel))

/-! Promoted from Staging/exists_uniform_power_lower_of_one_sub_linear_lower_and_scaled_horizon.lean. -/


-- Generalization plan (G0):
-- concept/name: uniform positive lower bound for powers from a local one-minus-linear
--   lower envelope and a bounded scaled horizon; orig was
--   restricted_gamma_power_lower_of_bounded_scaled_stepsize
-- generality used: a real-valued function of a real parameter, a nonnegative real
--   scaled-horizon budget, and a pointwise local lower envelope; no measure,
--   optimization, continuity, or finite-dimensional assumptions are used
-- portable call pattern: slow-mode, contraction, and stability proofs obtain a
--   uniform positive floor for finite powers while changing the multiplier, local
--   linear-loss constant, scaled-horizon budget, and exponent
-- counterargument checked: although the source theorem is already abstract, this is
--   not paper-local traceability or a pure wrapper; it composes a local envelope,
--   finite-power monotonicity, exponential comparison, and horizon scaling
-- coverage search: searched SOptLib/project symbols and Mathlib semantic search for
--   uniform power lower bounds from one-minus-linear envelopes under bounded scaled
--   horizons; Real.exp_neg_two_mul_le_one_sub_pow is the closest partial result, and
--   no declaration covers the quantified uniform conclusion
-- minimal hypotheses: dropped the source's unused pointwise nonnegativity of gamma;
--   all remaining hypotheses are used

/-- A local lower envelope `1 - c * alpha <= gamma alpha` gives a uniform positive
lower bound for powers of `gamma alpha` over every bounded scaled horizon.

Layer: Glue | Gap: Level 1 (uniform finite-power persistence from a local linear lower envelope)
Proof: restrict the parameter so the linear loss is at most one half, compare the resulting power with an exponential lower bound, and use the scaled-horizon budget to replace the exponent by a fixed positive constant.
Source: Mathlib ordered real powers and exponentials, together with `Real.exp_neg_two_mul_le_one_sub_pow`
Used in: slow-mode, contraction, and stability estimates that must retain a positive multiplier floor while the stepsize times the iteration horizon stays bounded
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/16/proof/2
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem exists_uniform_power_lower_of_one_sub_linear_lower_and_scaled_horizon
    (gamma : ℝ → ℝ) (M : ℝ) (hM_nonneg : 0 ≤ M)
    (hgamma_lower :
      ∃ alphaGammaLower cGammaLower : ℝ,
        0 < alphaGammaLower ∧ 0 < cGammaLower ∧
          ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaGammaLower →
            1 - cGammaLower * alpha ≤ gamma alpha) :
    ∃ alpha0 cgam : ℝ, 0 < alpha0 ∧ 0 < cgam ∧
      cgam ≤ 1 ∧
      ∀ T : ℕ, ∀ alpha : ℝ, ∀ k : ℕ,
        0 < alpha → alpha ≤ alpha0 → alpha * (T : ℝ) ≤ M →
          k ≤ T → cgam ≤ gamma alpha ^ k := by
  rcases hgamma_lower with
    ⟨alphaGammaLower, cGammaLower, halphaGammaLower_pos,
      hcGammaLower_pos, hgamma_lower_point⟩
  let alpha0 : ℝ := min alphaGammaLower (1 / (2 * cGammaLower))
  let cgam : ℝ := Real.exp (-(2 * cGammaLower * M))
  have halpha0_pos : 0 < alpha0 := by
    dsimp [alpha0]
    exact lt_min halphaGammaLower_pos (by positivity)
  have hcgam_pos : 0 < cgam := by
    dsimp [cgam]
    exact Real.exp_pos _
  have hcgam_le_one : cgam ≤ 1 := by
    dsimp [cgam]
    have hexp_le : Real.exp (-(2 * cGammaLower * M)) ≤ Real.exp 0 := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg hcGammaLower_pos.le hM_nonneg]
    simpa using hexp_le
  refine ⟨alpha0, cgam, halpha0_pos, hcgam_pos, hcgam_le_one, ?_⟩
  intro T alpha k halpha_pos halpha_le hscaled hkT
  have halpha_nonneg : 0 ≤ alpha := le_of_lt halpha_pos
  have halpha_le_gamma : alpha ≤ alphaGammaLower :=
    le_trans halpha_le (min_le_left _ _)
  have halpha_le_half : alpha ≤ 1 / (2 * cGammaLower) :=
    le_trans halpha_le (min_le_right _ _)
  have hx_nonneg : 0 ≤ cGammaLower * alpha :=
    mul_nonneg hcGammaLower_pos.le halpha_nonneg
  have hx_half : cGammaLower * alpha ≤ 1 / 2 := by
    calc
      cGammaLower * alpha ≤
          cGammaLower * (1 / (2 * cGammaLower)) :=
        mul_le_mul_of_nonneg_left halpha_le_half hcGammaLower_pos.le
      _ = 1 / 2 := by
        field_simp [ne_of_gt hcGammaLower_pos]
  have hbase_nonneg : 0 ≤ 1 - cGammaLower * alpha := by
    nlinarith
  have hpow_base_le_gamma :
      (1 - cGammaLower * alpha) ^ k ≤ gamma alpha ^ k :=
    pow_le_pow_left₀ hbase_nonneg
      (hgamma_lower_point alpha halpha_pos halpha_le_gamma) k
  have hbase_exp :
      Real.exp (-(2 * (cGammaLower * alpha) * (k : ℝ))) ≤
        (1 - cGammaLower * alpha) ^ k :=
    Real.exp_neg_two_mul_le_one_sub_pow
      (cGammaLower * alpha) k hx_nonneg hx_half
  have hscaled_k : alpha * (k : ℝ) ≤ M := by
    have hkT_real : (k : ℝ) ≤ (T : ℝ) := by exact_mod_cast hkT
    calc
      alpha * (k : ℝ) ≤ alpha * (T : ℝ) :=
        mul_le_mul_of_nonneg_left hkT_real halpha_nonneg
      _ ≤ M := hscaled
  have hexp_const_le :
      cgam ≤ Real.exp (-(2 * (cGammaLower * alpha) * (k : ℝ))) := by
    dsimp [cgam]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hcGammaLower_pos.le hM_nonneg, hscaled_k]
  exact le_trans hexp_const_le (le_trans hbase_exp hpow_base_le_gamma)

/-! Promoted from Staging/near_zero_contraction_bounds_of_isBigO_sub_sq.lean. -/


open Filter Topology

-- Generalization plan (G0):
-- concept/name: simultaneous near-zero contraction bounds under a quadratic
--   perturbation; orig was
--   `restricted_gamma_smallAlpha_contract_from_scalar_squeeze`
-- generality used: two arbitrary real-valued functions, an existential local
--   linear squeeze for the baseline, and a quadratic Big-O difference at zero;
--   no measure, convexity, smoothness, oracle, normed-space, or
--   finite-dimensional assumptions are used
-- portable call pattern: spectral perturbation, discretization, and local
--   stability proofs vary the baseline and perturbed multipliers, squeeze
--   constants, and small-parameter radius while reusing a common positive
--   contraction envelope and an explicit quadratic error bound
-- counterargument checked: this is not paper-local traceability or a one-line
--   wrapper; it combines a filter-level asymptotic estimate with a baseline
--   squeeze, selects compatible positive constants, and proves six ordered
--   conclusions simultaneously
-- coverage search: searched `near zero contraction bounds quadratic perturbation
--   isBigO square linear squeeze`, `positive radius common contraction upper
--   bound perturbation baseline`, and the corresponding LeanSearch query;
--   Mathlib provides `Asymptotics.IsBigO.exists_pos`, `isBigOWith_iff`, and
--   metric-neighborhood components, while the staged
--   `two_sided_linear_bounds_near_zero_of_isBigO_sub_linear_sq` treats one
--   function with a prescribed linear leading term and does not cover this
--   simultaneous perturbation-transfer contract
-- minimal hypotheses: only positivity of the baseline squeeze witnesses, its
--   two linear bounds, and the quadratic Big-O perturbation are retained; all
--   algorithm-specific spectral and homogeneous-quadratic assumptions are
--   upstream ways to establish these two premises

/-- A linear contraction squeeze persists under a quadratic-order perturbation
on a sufficiently small positive interval.

The conclusion gives one positive linear envelope for both functions while
retaining a pointwise quadratic bound with a positive constant.

Layer: Glue | Gap: Level 1 (simultaneous contraction bounds under quadratic perturbation)
Proof: choose a positive Big-O constant, realize its bound on a metric neighborhood, and shrink the baseline squeeze radius until the quadratic error is dominated by half of the linear contraction margin.
Source: Mathlib asymptotic Big-O bounds, metric neighborhood filters, real absolute values, and linear ordered-field arithmetic
Used in: spectral multiplier and discretization stability arguments that transfer a baseline small-parameter contraction squeeze to a quadratically perturbed multiplier
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/14/proof/5
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem near_zero_contraction_bounds_of_isBigO_sub_sq
    (base perturbed : ℝ → ℝ)
    (hbase :
      ∃ alphaS c1 c2 : ℝ,
        0 < alphaS ∧ 0 < c1 ∧ 0 < c2 ∧
          ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaS →
            1 - c2 * alpha ≤ base alpha ∧
              base alpha ≤ 1 - c1 * alpha)
    (hperturbed :
      Asymptotics.IsBigO (nhds 0)
        (fun alpha : ℝ => perturbed alpha - base alpha)
        (fun alpha : ℝ => alpha ^ 2)) :
    ∃ alpha0 c C : ℝ,
      0 < alpha0 ∧ 0 < c ∧ 0 < C ∧
        ∀ alpha : ℝ, 0 < alpha → alpha ≤ alpha0 →
          0 ≤ base alpha ∧ base alpha ≤ 1 - c * alpha ∧
            |perturbed alpha - base alpha| ≤ C * alpha ^ 2 ∧
              0 ≤ perturbed alpha ∧
                perturbed alpha ≤ 1 - c * alpha ∧
                  0 < 1 - c * alpha := by
  obtain ⟨alphaS, c1, c2, halphaS_pos, hc1_pos, hc2_pos, hbase_bound⟩ := hbase
  obtain ⟨C, hC_pos, hC_big⟩ := hperturbed.exists_pos
  have hbound_eventually :
      ∀ᶠ alpha : ℝ in nhds 0,
        ‖perturbed alpha - base alpha‖ ≤ C * ‖alpha ^ 2‖ := by
    exact Asymptotics.isBigOWith_iff.mp hC_big
  obtain ⟨eps, heps_pos, hbound_eps⟩ :=
    Metric.eventually_nhds_iff.mp hbound_eventually
  let c : ℝ := c1 / 2
  let alpha0 : ℝ :=
    min alphaS
      (min (eps / 2)
        (min (c / C) (1 / (c2 + c))))
  have hc_pos : 0 < c := by
    dsimp [c]
    positivity
  have hsum_pos : 0 < c2 + c := add_pos hc2_pos hc_pos
  have hC_radius_pos : 0 < c / C := by
    positivity
  have hinv_sum_pos : 0 < 1 / (c2 + c) := by
    positivity
  have halpha0_pos : 0 < alpha0 := by
    dsimp [alpha0]
    exact lt_min halphaS_pos
      (lt_min (half_pos heps_pos)
        (lt_min hC_radius_pos hinv_sum_pos))
  refine ⟨alpha0, c, C, halpha0_pos, hc_pos, hC_pos, ?_⟩
  intro alpha halpha_pos halpha_le
  have halpha_nonneg : 0 ≤ alpha := le_of_lt halpha_pos
  have halpha_le_base : alpha ≤ alphaS := by
    exact le_trans halpha_le (min_le_left _ _)
  have hbase_alpha := hbase_bound alpha halpha_pos halpha_le_base
  have halpha_le_eps_half : alpha ≤ eps / 2 := by
    exact le_trans halpha_le
      (le_trans (min_le_right _ _) (min_le_left _ _))
  have halpha_lt_eps : alpha < eps := by
    nlinarith
  have hdist : dist alpha 0 < eps := by
    simpa [Real.dist_eq, abs_of_pos halpha_pos] using halpha_lt_eps
  have hraw_bound := hbound_eps hdist
  have herror_abs :
      |perturbed alpha - base alpha| ≤ C * alpha ^ 2 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg alpha)] using hraw_bound
  have halpha_le_c_div : alpha ≤ c / C := by
    exact le_trans halpha_le
      (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hC_alpha_le : C * alpha ≤ c := by
    calc
      C * alpha ≤ C * (c / C) :=
        mul_le_mul_of_nonneg_left halpha_le_c_div (le_of_lt hC_pos)
      _ = c := by
        field_simp [ne_of_gt hC_pos]
  have herror_linear :
      |perturbed alpha - base alpha| ≤ c * alpha := by
    calc
      |perturbed alpha - base alpha| ≤ C * alpha ^ 2 := herror_abs
      _ ≤ c * alpha := by
        have hmul := mul_le_mul_of_nonneg_right hC_alpha_le halpha_nonneg
        nlinarith
  have hdiff_bounds := abs_le.mp herror_linear
  have halpha_le_inv_sum : alpha ≤ 1 / (c2 + c) := by
    exact le_trans halpha_le
      (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hsum_alpha_le_one : (c2 + c) * alpha ≤ 1 := by
    calc
      (c2 + c) * alpha ≤ (c2 + c) * (1 / (c2 + c)) :=
        mul_le_mul_of_nonneg_left halpha_le_inv_sum (le_of_lt hsum_pos)
      _ = 1 := by
        field_simp [ne_of_gt hsum_pos]
  have hbase_nonneg : 0 ≤ base alpha := by
    nlinarith [hbase_alpha.1, hsum_alpha_le_one]
  have hbase_upper : base alpha ≤ 1 - c * alpha := by
    dsimp [c] at *
    nlinarith [hbase_alpha.2, halpha_nonneg]
  have hperturbed_nonneg : 0 ≤ perturbed alpha := by
    nlinarith [hbase_alpha.1, hdiff_bounds.1, hsum_alpha_le_one]
  have hperturbed_upper : perturbed alpha ≤ 1 - c * alpha := by
    dsimp [c] at *
    nlinarith [hbase_alpha.2, hdiff_bounds.2]
  have henvelope_pos : 0 < 1 - c * alpha := by
    have hc_alpha_pos : 0 < c * alpha := mul_pos hc_pos halpha_pos
    have hc_alpha_lt_one : c * alpha < 1 := by
      have hc2_part_pos : 0 < c2 * alpha := mul_pos hc2_pos halpha_pos
      nlinarith [hsum_alpha_le_one, hc2_part_pos]
    nlinarith
  exact ⟨hbase_nonneg, hbase_upper, herror_abs, hperturbed_nonneg,
    hperturbed_upper, henvelope_pos⟩

/-! Promoted from Staging/near_zero_linear_lower_bound_of_isBigO_sub_sq.lean. -/


open Filter Topology

-- Generalization plan (G0):
-- concept/name: near-zero linear lower-bound transfer under a quadratic
--   perturbation; orig was
--   `restricted_gamma_smallAlpha_lower_from_scalar_squeeze`
-- generality used: two arbitrary real-valued functions, a positive baseline
--   radius, an arbitrary linear-loss coefficient, a pointwise baseline lower
--   bound, and a quadratic Big-O difference from the right at zero; no measure,
--   convexity, smoothness, oracle, normed-space, or finite-dimensional
--   assumptions are used
-- portable call pattern: persistence, product-lower-bound, spectral
--   perturbation, and discretization-stability proofs vary the baseline and
--   perturbed scalar functions and their local loss coefficient while reusing
--   a positive interval on which the perturbation is nonnegative and retains
--   a linear lower bound
-- counterargument checked: this is not paper-local traceability or a one-line
--   wrapper; it converts a filter-level quadratic error estimate and a
--   one-sided baseline squeeze into compatible positive witnesses and two
--   ordered conclusions on a common interval
-- coverage search: searched `near zero linear lower bound quadratic perturbation
--   Big O square baseline lower bound`, `nonnegative lower linear bound of
--   isBigO difference square`, and the corresponding LeanSearch query; Mathlib
--   provides the Big-O and metric-neighborhood components, the staged
--   `near_zero_contraction_bounds_of_isBigO_sub_sq` requires an additional
--   upper squeeze and proves upper contraction bounds, and
--   `two_sided_linear_bounds_near_zero_of_isBigO_sub_linear_sq` concerns one
--   function with a prescribed positive linear leading term
-- minimal hypotheses: positivity is retained only for the baseline interval;
--   the perturbation estimate is restricted to the positive side used by the
--   conclusion, and the baseline slope need not be positive

/-- A near-zero linear lower bound persists under a quadratic-order perturbation.

On a sufficiently small positive interval, the perturbed function is
nonnegative and remains above one minus a positive multiple of the parameter.

Layer: Glue | Gap: Level 1 (one-sided linear lower-bound transfer under quadratic perturbation)
Proof: realize the Big-O estimate on a metric neighborhood, shrink the baseline interval until the quadratic error is at most the parameter, and shrink once more so the resulting linear lower envelope is nonnegative.
Source: Mathlib asymptotic Big-O bounds, metric neighborhood filters, real absolute values, and linear ordered-field arithmetic
Used in: persistence and product-lower-bound arguments that transfer a baseline small-parameter lower squeeze to a quadratically perturbed spectral multiplier
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/16/proof/2
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem near_zero_linear_lower_bound_of_isBigO_sub_sq
    (base perturbed : ℝ → ℝ) (alphaS c2 : ℝ)
    (halphaS_pos : 0 < alphaS)
    (hbase : ∀ alpha : ℝ, 0 < alpha → alpha ≤ alphaS →
      1 - c2 * alpha ≤ base alpha)
    (hperturbed :
      Asymptotics.IsBigO (𝓝[>] 0)
        (fun alpha : ℝ => perturbed alpha - base alpha)
        (fun alpha : ℝ => alpha ^ 2)) :
    ∃ alpha0 cLower : ℝ,
      0 < alpha0 ∧ 0 < cLower ∧
        ∀ alpha : ℝ, 0 < alpha → alpha ≤ alpha0 →
          0 ≤ perturbed alpha ∧
            1 - cLower * alpha ≤ perturbed alpha := by
  obtain ⟨C, hC_pos, hC_big⟩ := hperturbed.exists_pos
  have hbound_eventually :
      ∀ᶠ alpha : ℝ in 𝓝[>] 0,
        ‖perturbed alpha - base alpha‖ ≤ C * ‖alpha ^ 2‖ := by
    exact Asymptotics.isBigOWith_iff.mp hC_big
  have hbound_eventually' :
      ∀ᶠ alpha : ℝ in nhds 0,
        alpha ∈ Set.Ioi 0 →
          ‖perturbed alpha - base alpha‖ ≤ C * ‖alpha ^ 2‖ := by
    exact eventually_nhdsWithin_iff.mp hbound_eventually
  obtain ⟨eps, heps_pos, hbound_eps⟩ :=
    Metric.eventually_nhds_iff.mp hbound_eventually'
  let cLower : ℝ := |c2| + 1
  let alpha0 : ℝ :=
    min alphaS
      (min (eps / 2) (min (1 / C) (1 / (2 * cLower))))
  have hcLower_pos : 0 < cLower := by
    dsimp [cLower]
    positivity
  have halpha0_pos : 0 < alpha0 := by
    dsimp [alpha0]
    exact lt_min halphaS_pos
      (lt_min (half_pos heps_pos)
        (lt_min (by positivity) (by positivity)))
  refine ⟨alpha0, cLower, halpha0_pos, hcLower_pos, ?_⟩
  intro alpha halpha_pos halpha_le
  have halpha_nonneg : 0 ≤ alpha := le_of_lt halpha_pos
  have halpha_le_base : alpha ≤ alphaS := by
    exact le_trans halpha_le (min_le_left _ _)
  have hbase_alpha := hbase alpha halpha_pos halpha_le_base
  have halpha_le_eps_half : alpha ≤ eps / 2 := by
    exact le_trans halpha_le
      (le_trans (min_le_right _ _) (min_le_left _ _))
  have halpha_lt_eps : alpha < eps := by
    linarith
  have hdist : dist alpha 0 < eps := by
    simpa [Real.dist_eq, abs_of_pos halpha_pos] using halpha_lt_eps
  have hraw_bound := hbound_eps hdist halpha_pos
  have herror_abs :
      |perturbed alpha - base alpha| ≤ C * alpha ^ 2 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg alpha)] using hraw_bound
  have halpha_le_inv_C : alpha ≤ 1 / C := by
    exact le_trans halpha_le
      (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hC_alpha_le_one : C * alpha ≤ 1 := by
    calc
      C * alpha ≤ C * (1 / C) :=
        mul_le_mul_of_nonneg_left halpha_le_inv_C hC_pos.le
      _ = 1 := by
        field_simp [ne_of_gt hC_pos]
  have herror_linear : |perturbed alpha - base alpha| ≤ alpha := by
    calc
      |perturbed alpha - base alpha| ≤ C * alpha ^ 2 := herror_abs
      _ ≤ alpha := by
        have hmul := mul_le_mul_of_nonneg_right hC_alpha_le_one halpha_nonneg
        nlinarith
  have hdiff_lower := (abs_le.mp herror_linear).1
  have hperturbed_lower : 1 - cLower * alpha ≤ perturbed alpha := by
    dsimp [cLower] at *
    have hc2_le_abs : c2 ≤ |c2| := le_abs_self c2
    nlinarith
  have halpha_le_half : alpha ≤ 1 / (2 * cLower) := by
    exact le_trans halpha_le
      (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hcLower_alpha_le_half : cLower * alpha ≤ 1 / 2 := by
    calc
      cLower * alpha ≤ cLower * (1 / (2 * cLower)) :=
        mul_le_mul_of_nonneg_left halpha_le_half hcLower_pos.le
      _ = 1 / 2 := by
        field_simp [ne_of_gt hcLower_pos]
  have hperturbed_nonneg : 0 ≤ perturbed alpha := by
    have henvelope_nonneg : 0 ≤ 1 - cLower * alpha := by
      linarith
    exact le_trans henvelope_nonneg hperturbed_lower
  exact ⟨hperturbed_nonneg, hperturbed_lower⟩

/-! Promoted from Staging/finite_sum_sq_isBigO_pow_four_of_forall_isBigO_sq.lean. -/


open scoped BigOperators

namespace Asymptotics

/-- A finite sum of coordinate squares is bounded by the square of a common
asymptotic comparison function when every coordinate has that comparison.

Layer: Glue | Gap: Level 1 (finite-family squared asymptotic aggregation)
Proof: multiply each coordinate estimate by itself and combine the resulting
estimates with finite-sum closure.
Source: Mathlib asymptotic multiplication and finite-sum closure APIs
Used in: finite-dimensional perturbation and squared-error aggregation before
stochastic moment bounds
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/14/proof/5
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem IsBigO.fintype_sum_sq
    {α I R S : Type*} [Fintype I] [SeminormedRing R]
    [NormedRing S] [NormMulClass S]
    {l : Filter α} {w : α → I → R} {g : α → S}
    (h : ∀ i : I, (fun x => w x i) =O[l] g) :
    (fun x => ∑ i : I, (w x i) ^ 2) =O[l] fun x => (g x) ^ 2 := by
  classical
  apply IsBigO.sum
  intro i _hi
  simpa only [pow_two] using (h i).mul (h i)

end Asymptotics

/-! Promoted from Staging/sInf_mem_nonnegative_linear_majorant_set_of_nonempty.lean. -/


-- Generalization plan (G0):
-- concept/name: attainment of the least nonnegative universal linear-majorant
--   constant; orig was the repeated local `admissible` infimum block
-- generality used: an arbitrary index type and value and weight families over
--   any conditionally complete linear order with order topology, zero, and
--   continuous multiplication; no finiteness, nonempty-index, measure,
--   convexity, smoothness, oracle, normed-space, or finite-dimensional
--   assumptions
-- portable call pattern: operator-norm, Lipschitz-modulus, and stability-gain
--   constructions vary the indexed values and weights while defining the sharp
--   nonnegative multiplicative bound as the infimum of all admissible constants
-- counterargument checked: Mathlib already supplies closed-set infimum
--   attainment, but not the structured result that derives closedness and a
--   lower bound automatically from universal linear inequalities; this packages
--   the recurring proof boundary rather than renaming a single declaration
-- coverage search: queried `infimum belongs to nonempty set of nonnegative
--   constants satisfying universal linear majorant inequalities`, `closed
--   nonnegative linear inequality feasible set infimum is attained of
--   nonempty`, and the semantic Mathlib equivalent; `IsClosed.csInf_mem` is the
--   terminal ingredient, while no Mathlib, SOptLib, or approved round entry has
--   the complete structured signature
-- minimal hypotheses: nonemptiness is the only explicit hypothesis; the
--   nonnegative-constant clause itself supplies boundedness below, and each
--   indexed multiplicative inequality defines a closed set

/-- The infimum of a nonempty set of nonnegative universal linear-majorant
constants is itself an admissible majorant.

Layer: Glue | Gap: Level 1 (attainment of least nonnegative linear-majorant constant)
Proof: express the admissible set as the intersection of the nonnegative ray and closed affine-inequality sets, use zero as a lower bound, and apply `IsClosed.csInf_mem`.
Source: Mathlib closed indexed intersections, continuity of multiplication, and conditionally complete order infimum attainment
Used in: operator-norm, Lipschitz-modulus, and stability-gain specifications that define a sharp multiplicative constant as the infimum of all nonnegative bounds
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/algorithm_spec
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem sInf_mem_nonnegative_linear_majorant_set_of_nonempty
    {ι α : Type*} [ConditionallyCompleteLinearOrder α]
    [TopologicalSpace α] [OrderTopology α] [Zero α] [Mul α]
    [ContinuousMul α] (f g : ι → α)
    (h_nonempty : ({c : α | 0 ≤ c ∧ ∀ i, f i ≤ c * g i} : Set α).Nonempty) :
    sInf {c : α | 0 ≤ c ∧ ∀ i, f i ≤ c * g i} ∈
      {c : α | 0 ≤ c ∧ ∀ i, f i ≤ c * g i} := by
  let admissible : Set α := {c : α | 0 ≤ c ∧ ∀ i, f i ≤ c * g i}
  have h_bddBelow : BddBelow admissible := by
    refine ⟨0, ?_⟩
    intro c hc
    exact hc.1
  have h_closed : IsClosed admissible := by
    rw [show admissible = Set.Ici 0 ∩
        ⋂ i : ι, {c : α | f i ≤ c * g i} by
      ext c
      simp [admissible]]
    apply IsClosed.inter isClosed_Ici
    apply isClosed_iInter
    intro i
    exact isClosed_le continuous_const (continuous_id.mul continuous_const)
  exact h_closed.csInf_mem h_nonempty h_bddBelow

/-! Promoted from Staging/le_of_pow_le_const_mul_pow_for_all.lean. -/


open Filter Topology

-- Generalization plan (G0):
-- concept/name: recover an order between nonnegative bases from uniform
--   constant-factor domination of every positive natural power; orig was
--   scalar_pow_le_geometric_for_all_forces_base_le
-- generality used: a nonnegative comparison base and an arbitrary real first
--   base and prefactor; no measure, convexity, finite-dimensionality, or scale
-- portable call pattern: spectral-radius, geometric-recurrence, and asymptotic
--   lower-bound proofs can vary both bases and the fixed prefactor while using
--   all-power domination to recover the base inequality
-- counterargument checked: the source theorem includes a cancellable positive
--   scale and a larger comparison radius, but the extracted endpoint `a ≤ q`
--   is a stronger reusable asymptotic order fact rather than a paper wrapper
-- coverage search: searched "nonnegative real bases inequality all powers
--   constant multiple implies base inequality", "power domination implies
--   base inequality", and LeanSearch for `a^n ≤ C*q^n`; Mathlib hits such as
--   `ENNReal.pow_le_pow_left_iff` concern one common exponent, while SOptLib's
--   geometric contraction lemmas propagate bounds but do not recover the base
-- minimal hypotheses: only the comparison base must be nonnegative; if the
--   first base exceeds it, positivity follows. Domination for every positive
--   exponent is retained, while the common scale and larger radius are removed

/-- Uniform constant-factor domination of all positive powers by powers of a
nonnegative real base forces the first base to be no larger.

Layer: Glue | Gap: Level 1 (base order from uniform all-power geometric domination)
Proof: if the second base were smaller, divide by the positive powers of the first base; the resulting lower bound `1 ≤ M * (q / a)^(N+1)` contradicts convergence of the right side to zero.
Source: Mathlib geometric-power convergence `tendsto_pow_atTop_nhds_zero_of_norm_lt_one` and filter limit comparison
Used in: spectral-radius and stable-recurrence arguments that recover an eigenvalue or contraction-base bound from uniform estimates on every positive power
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem le_of_pow_le_const_mul_pow_for_all
    {a q M : ℝ} (hq_nonneg : 0 ≤ q)
    (hbound : ∀ N : ℕ, a ^ (N + 1) ≤ M * q ^ (N + 1)) :
    a ≤ q := by
  by_contra hnot
  have hq_lt_a : q < a := lt_of_not_ge hnot
  have ha_pos : 0 < a := lt_of_le_of_lt hq_nonneg hq_lt_a
  have hr_nonneg : 0 ≤ q / a := div_nonneg hq_nonneg ha_pos.le
  have hr_lt_one : q / a < 1 := by
    rw [div_lt_one ha_pos]
    exact hq_lt_a
  have hr_norm_lt : ‖q / a‖ < 1 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hq_nonneg,
      abs_of_nonneg ha_pos.le] using hr_lt_one
  have hpow :
      Tendsto (fun N : ℕ => (q / a) ^ (N + 1)) atTop (nhds 0) := by
    have hbase := tendsto_pow_atTop_nhds_zero_of_norm_lt_one hr_norm_lt
    simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using
      hbase.const_mul (q / a)
  have htail :
      Tendsto (fun N : ℕ => M * (q / a) ^ (N + 1)) atTop (nhds 0) := by
    simpa [mul_assoc] using hpow.const_mul M
  have hle : ∀ N : ℕ, (1 : ℝ) ≤ M * (q / a) ^ (N + 1) := by
    intro N
    have hden_pos : 0 < a ^ (N + 1) := pow_pos ha_pos _
    have hbdiv :
        a ^ (N + 1) / a ^ (N + 1) ≤
          (M * q ^ (N + 1)) / a ^ (N + 1) :=
      div_le_div_of_nonneg_right (hbound N) hden_pos.le
    calc
      (1 : ℝ) = a ^ (N + 1) / a ^ (N + 1) := by
        exact (div_self (ne_of_gt hden_pos)).symm
      _ ≤ (M * q ^ (N + 1)) / a ^ (N + 1) := hbdiv
      _ = M * (q / a) ^ (N + 1) := by
        rw [div_pow]
        ring
  have hone_le_zero : (1 : ℝ) ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds htail
      (Filter.Eventually.of_forall hle)
  norm_num at hone_le_zero

/-! Promoted from Staging/Asymptotics_isBigO_of_le_leading_and_value_upper_and_littleO_sub.lean. -/


-- Generalization plan (G0):
-- concept/name: asymptotic absorption of a little-o value-minus-leading residual;
--   orig was scale_isBigO_of_value_upper_and_littleO_transfer
-- generality used: four arbitrary real-valued functions on an arbitrary type and filter,
--   with only eventual order bounds, scale nonnegativity, and a little-o hypothesis;
--   no measure, convexity, smoothness, oracle, or finite-dimensional assumptions
-- portable call pattern: rate proofs for near-minimizers, approximate objective values,
--   or comparison recurrences can change the value, leading approximation, scale, and
--   target while retaining the same residual-absorption conclusion
-- counterargument checked: this is not paper-local traceability or a pure wrapper;
--   it packages the nontrivial choice of a little-o tolerance and absorption of half
--   the scale, and no existing Mathlib or SOptLib declaration has the full contract
-- coverage search: queried scale Big-O from a leading upper bound, value upper bound,
--   and little-o subtraction; Mathlib IsLittleO.isBigO and right_isBigO_sub are partial,
--   while SOptLib.isBigO_principal_and_compl_of_forall_norm_le is structurally different
-- minimal hypotheses: the value upper bound is stated eventually, and neither its
--   coefficient nor the target is required to be nonnegative

/-- A scale bounded by a leading term is big-O of a target when the value is
target-bounded and its difference from the leading term is little-o of the scale.

Layer: Glue | Gap: Level 1 (little-o residual absorption into an eventual Big-O bound)
Proof: choose the little-o tolerance `(2 * Cscale)⁻¹`, bound the leading term by the
  target-controlled value plus the residual, and absorb one half of the scale.
Source: Mathlib asymptotic filters via `Asymptotics.IsLittleO.def` and
  `Asymptotics.IsBigO.of_bound`, with ordered real-field arithmetic
Used in: near-minimizer rate transfer from a two-term quadratic leading expansion to an
  inverse-square-root comparison scale in a stochastic distributed lower-bound proof
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/16/proof/4
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous
  Periodic Directed Networks, matching quadratic lower bound -/
theorem Asymptotics.isBigO_of_le_leading_and_value_upper_and_littleO_sub
    {α : Type*} {l : Filter α} {J leading scale target : α → Real}
    (hscale_leading :
      ∃ Cscale : Real, 0 < Cscale ∧
        ∀ᶠ x in l, scale x ≤ Cscale * leading x)
    (htransfer :
      Asymptotics.IsLittleO l (fun x => J x - leading x) scale)
    (hvalue_upper :
      ∃ Cvalue : Real, ∀ᶠ x in l, J x ≤ Cvalue * target x)
    (hscale_nonneg : ∀ᶠ x in l, 0 ≤ scale x) :
    Asymptotics.IsBigO l scale target := by
  rcases hscale_leading with ⟨Cscale, hCscale_pos, hscale_leading_ev⟩
  rcases hvalue_upper with ⟨Cvalue, hvalue_bound⟩
  let eps : Real := (2 * Cscale)⁻¹
  have heps_pos : 0 < eps := by
    dsimp [eps]
    positivity
  have htransfer_bound := htransfer.def heps_pos
  refine Asymptotics.IsBigO.of_bound (2 * Cscale * |Cvalue|) ?_
  filter_upwards
    [hscale_leading_ev, htransfer_bound, hvalue_bound, hscale_nonneg]
    with x hscale_leading_x htransfer_x hvalue_x hscale_nonneg_x
  have hscale_abs : |scale x| = scale x :=
    abs_of_nonneg hscale_nonneg_x
  have htransfer_abs :
      |J x - leading x| ≤ eps * scale x := by
    simpa [Real.norm_eq_abs, hscale_abs] using htransfer_x
  have hleading_le : leading x ≤ J x + |J x - leading x| := by
    have hneg_le_abs : -(J x - leading x) ≤ |J x - leading x| :=
      neg_le_abs (J x - leading x)
    linarith
  have hmain :
      scale x ≤
        Cscale * (Cvalue * target x + eps * scale x) := by
    have hmul_leading :
        Cscale * leading x ≤
          Cscale * (J x + |J x - leading x|) :=
      mul_le_mul_of_nonneg_left hleading_le hCscale_pos.le
    have hsum_bound :
        J x + |J x - leading x| ≤
          Cvalue * target x + eps * scale x := by
      linarith
    have hmul_sum :
        Cscale * (J x + |J x - leading x|) ≤
          Cscale * (Cvalue * target x + eps * scale x) :=
      mul_le_mul_of_nonneg_left hsum_bound hCscale_pos.le
    exact hscale_leading_x.trans (hmul_leading.trans hmul_sum)
  have hCscale_eps : Cscale * eps = (1 / 2 : Real) := by
    dsimp [eps]
    field_simp [ne_of_gt hCscale_pos]
  have hfinal : scale x ≤ 2 * Cscale * Cvalue * target x := by
    nlinarith [hmain, hCscale_eps]
  have hvalue_abs : Cvalue * target x ≤ |Cvalue| * |target x| := by
    rw [← abs_mul]
    exact le_abs_self (Cvalue * target x)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, hscale_abs]
  calc
    scale x ≤ 2 * Cscale * (Cvalue * target x) := by
      simpa [mul_assoc] using hfinal
    _ ≤ 2 * Cscale * (|Cvalue| * |target x|) :=
      mul_le_mul_of_nonneg_left hvalue_abs (by positivity)
    _ = 2 * Cscale * |Cvalue| * |target x| := by ring

/-! Promoted from Staging/isLittleO_of_abs_le_error_add_sqrt_cross.lean. -/


open Filter

-- Generalization plan (G0):
-- concept/name: little-o transfer through an absolute error-plus-square-root
--   cross-term bound; orig was signed_difference_isLittleO_of_abs_le_l2_budget
-- generality used: arbitrary index type and filter, arbitrary normed
--   codomains for the dominated function and comparison scale, and real-valued
--   error and reference functions; no measure, convexity, smoothness, oracle,
--   or finite-dimensional assumptions are used
-- portable call pattern: perturbation and comparison-process proofs vary the
--   signed moment difference, mean-square error, reference moment, filter, and
--   rate scale after proving the error and square-root cross term are little-o
-- counterargument checked: Mathlib provides the primitive asymptotic
--   transitivity rules and the staged squeeze theorem gives a generic interval,
--   but neither packages the recurring L2 error-plus-cross-term budget
-- coverage search: queried `little o of eventual absolute value bounded by sum
--   of little o functions`, `isLittleO of abs le error add square root cross
--   term`, and the full domination contract; closest hits were
--   `Asymptotics.IsLittleO.of_bound`, `IsBigO.trans_isLittleO`, and
--   `Asymptotics.isLittleO_of_eventually_between`, all partial rather than full
-- minimal hypotheses: Nat/atTop were generalized to an arbitrary type/filter;
--   eventual nonnegativity of the whole budget is unnecessary because the
--   real budget is always bounded above by its norm

/-- An eventual norm bound by an error plus twice a square-root cross term
is little-o of a scale when both budget components are little-o of that scale.

Layer: Glue | Gap: Level 1 (little-o transfer through an L2 perturbation budget)
Proof: add the two little-o component estimates, dominate the function by the resulting budget with Big-O constant one, and compose Big-O with little-o.
Source: Mathlib asymptotic comparison APIs `Asymptotics.IsLittleO.add`, `Asymptotics.IsBigO.of_bound`, and `Asymptotics.IsBigO.trans_isLittleO`
Used in: comparison-process perturbation arguments that transfer a negligible mean-square error and its square-root reference-moment cross term to a signed second-moment difference
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/17/proof/9
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem Asymptotics.isLittleO_of_abs_le_error_add_sqrt_cross
    {α E F : Type*} [Norm E] [Norm F] {l : Filter α}
    {f : α → E} {M U : α → ℝ} {scale : α → F}
    (hbound : ∀ᶠ x in l, ‖f x‖ ≤ M x + 2 * Real.sqrt (M x * U x))
    (hM : Asymptotics.IsLittleO l M scale)
    (hcross :
      Asymptotics.IsLittleO l (fun x => Real.sqrt (M x * U x)) scale) :
    Asymptotics.IsLittleO l f scale := by
  let budget : α → ℝ := fun x => M x + 2 * Real.sqrt (M x * U x)
  have hbudgetLittle : Asymptotics.IsLittleO l budget scale := by
    have hsum := hM.add (hcross.const_mul_left 2)
    simpa [budget, mul_assoc] using hsum
  have hbig : Asymptotics.IsBigO l f budget := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [hbound] with x hx
    calc
      ‖f x‖ ≤ budget x := by simpa [budget] using hx
      _ ≤ 1 * ‖budget x‖ := by
        rw [one_mul, Real.norm_eq_abs]
        exact le_abs_self _
  exact hbig.trans_isLittleO hbudgetLittle

/-! Promoted from Staging/Matrix_exists_uniform_one_sub_mulVec_norm_sq_bound_of_isCompact_of_entry_continuousOn.lean. -/


open scoped BigOperators Matrix.Norms.L2Operator

-- Generalization plan (G0):
-- concept/name: compact-uniform squared Euclidean action bound for the complementary operator of a continuous finite-matrix family; orig was spectralStableComplementVector_uniform_operator_bound_on_Icc
-- generality used: an arbitrary topological parameter type, compact parameter set, finite matrix index type, RCLike scalar field, matrix family, and entrywise continuity on the set; no interval order, nonempty index, measure, convexity, smoothness, oracle, spectral, projection, or finite-dimensional ambient-space assumptions
-- portable call pattern: spectral perturbation, consensus decomposition, and parameterized finite-state recursion proofs can vary the compact parameter set, finite coordinate type, continuous matrix family, and input vector while retaining one nonnegative constant bounding the squared Euclidean action of `I - P a`
-- counterargument checked: this is not paper-local traceability or a caller-side expression because it packages compactness, entrywise-to-matrix continuity, the Euclidean matrix operator norm, and squared action control; existing compact-bound and entrywise operator-norm lemmas each cover only a proper internal step
-- coverage search: queried `compact set entrywise continuous matrix family uniform squared norm action bound identity minus matrix`, `exists nonnegative uniform operator norm bound compact continuous matrix family`, and `matrix mulVec norm squared upper bound operator norm`; closest hits were Mathlib `Matrix.l2_opNorm_mulVec`, SOptLib `exists_nonneg_norm_bound_of_isCompact_of_continuousOn`, and staged `Matrix.euclidean_opNorm_le_of_entrywise_norm_le`, all partial rather than the compact family action contract
-- minimal hypotheses: `TopologicalSpace A`, `Fintype I`, compactness of `s`, and entrywise `ContinuousOn` are sufficient; neither `s.Nonempty`, `Nonempty I`, a positive interval endpoint, nor positivity of the parameter is used

namespace Matrix

/-- An entrywise-continuous finite matrix family over an `RCLike` field has a uniform squared
Euclidean action bound for its complementary operators on a compact set.

Layer: Glue | Gap: Level 1 (compact-uniform complementary matrix action bound)
Proof: lift entrywise continuity to continuity of the matrix family in the Euclidean operator-norm topology, bound the operator norm of `I - P a` on the compact set, apply `Matrix.l2_opNorm_mulVec`, and square the resulting nonnegative inequality.
Source: Mathlib compact continuous-map bounds and the finite-matrix L2 operator norm, especially `IsCompact.exists_bound_of_continuousOn` and `Matrix.l2_opNorm_mulVec`
Used in: spectral and consensus stable-complement estimates that need one squared-energy multiplier for `I - P(a)` across a compact stepsize or perturbation region before summing projected innovations
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/14/proof/3
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem exists_uniform_one_sub_mulVec_norm_sq_bound_of_isCompact_of_entry_continuousOn
    {A I 𝕜 : Type*} [TopologicalSpace A] [Fintype I] [RCLike 𝕜]
    (s : Set A) (P : A → Matrix I I 𝕜)
    (hcompact : IsCompact s)
    (hentry_cont : ∀ i j : I, ContinuousOn (fun a => P a i j) s) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ a : A, a ∈ s → ∀ z : I → 𝕜,
        ‖WithLp.toLp 2 ((1 - Matrix.mulVecLin (P a)) z)‖ ^ 2 ≤
          C ^ 2 * ‖WithLp.toLp 2 z‖ ^ 2 := by
  classical
  let Q : A → Matrix I I 𝕜 := fun a => 1 - P a
  have hP_cont : ContinuousOn P s :=
    continuousOn_pi.mpr fun i => continuousOn_pi.mpr fun j => hentry_cont i j
  have hQ_cont : ContinuousOn Q s := by
    exact continuousOn_const.sub hP_cont
  let T : Matrix I I 𝕜 →L[𝕜]
      (EuclideanSpace 𝕜 I →L[𝕜] EuclideanSpace 𝕜 I) :=
    (Matrix.toEuclideanCLM (n := I) (𝕜 := 𝕜)).toAlgEquiv.toLinearEquiv
      |>.toContinuousLinearEquiv.toContinuousLinearMap
  have hT_cont : ContinuousOn (fun a => T (Q a)) s :=
    T.continuous.comp_continuousOn hQ_cont
  obtain ⟨B, hB⟩ := hcompact.exists_bound_of_continuousOn hT_cont.norm
  let C : ℝ := max B 0
  refine ⟨C, le_max_right B 0, ?_⟩
  intro a ha z
  have hQ_le : ‖Q a‖ ≤ C := by
    rw [Matrix.cstar_norm_def]
    change ‖T (Q a)‖ ≤ C
    exact (le_abs_self ‖T (Q a)‖).trans ((hB a ha).trans (le_max_left B 0))
  have haction :
      ‖WithLp.toLp 2 ((1 - Matrix.mulVecLin (P a)) z)‖ ≤
        C * ‖WithLp.toLp 2 z‖ := by
    have hmul := (Q a).l2_opNorm_mulVec (WithLp.toLp 2 z)
    have hmul' :
        ‖WithLp.toLp 2 ((Q a) *ᵥ z)‖ ≤
          ‖Q a‖ * ‖WithLp.toLp 2 z‖ := by
      simpa using hmul
    calc
      ‖WithLp.toLp 2 ((1 - Matrix.mulVecLin (P a)) z)‖ =
          ‖WithLp.toLp 2 ((Q a) *ᵥ z)‖ := by
            congr 2
            simp [Q, LinearMap.sub_apply, Module.End.one_apply,
              Matrix.sub_mulVec, Matrix.one_mulVec]
      _ ≤ ‖Q a‖ * ‖WithLp.toLp 2 z‖ := hmul'
      _ ≤ C * ‖WithLp.toLp 2 z‖ :=
        mul_le_mul_of_nonneg_right hQ_le (norm_nonneg _)
  have hsquare :=
    (sq_le_sq₀ (norm_nonneg (WithLp.toLp 2 ((1 - Matrix.mulVecLin (P a)) z)))
      (mul_nonneg (le_max_right B 0) (norm_nonneg (WithLp.toLp 2 z)))).2 haction
  simpa [mul_pow] using hsquare

end Matrix

/-! Promoted from Staging/Asymptotics_IsLittleO_sqrt_mul_of_isBigO.lean. -/


-- Generalization plan (G0):
-- concept/name: square-root product preserves little-o when one factor is little-o and the other is big-O; orig was sqrt_mul_isLittleO_of_left_littleO_right_isBigO_nonneg_scale
-- generality used: arbitrary index type and filter; real-valued factors and comparison scale; only eventual nonnegativity of the scale
-- portable call pattern: comparison-error transfers in stochastic approximation and distributed optimization, with the error factor, reference moment, index type, filter, and nonnegative rate scale all varying
-- counterargument checked: not paper-local and not a pure wrapper; it composes product asymptotics, square-root asymptotics, and eventual identification of the square root of the squared scale
-- coverage search: queried square-root product little-o from a little-o factor and a big-O factor under a nonnegative scale; Mathlib IsLittleO.mul_isBigO, IsLittleO.sqrt, and Real.sqrt_mul_self are partial ingredients, while SOptLib and the round registry contain no complete match
-- minimal hypotheses: Nat and atTop were generalized to an arbitrary type and filter; eventual scale nonnegativity is exactly what identifies sqrt (scale * scale) with scale

/-- The square root of a product of a little-o factor and a big-O factor is
little-o of their common eventually nonnegative comparison scale.

Layer: Glue | Gap: Level 1 (square-root cross-term asymptotic composition)
Proof: multiply the little-o and big-O estimates, apply square-root preservation of little-o, then identify the square root of the squared scale using eventual nonnegativity.
Source: Mathlib asymptotics for products and real powers (`Asymptotics.IsLittleO.mul_isBigO`, `Asymptotics.IsLittleO.sqrt`) and real square-root identities (`Real.sqrt_mul_self`)
Used in: transferring a mean-square comparison error into a lower-order square-root cross term against a big-O reference moment
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/17/proof/9
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem Asymptotics.IsLittleO.sqrt_mul_of_isBigO
    {α : Type*} {l : Filter α} {f g scale : α → ℝ}
    (hf : Asymptotics.IsLittleO l f scale)
    (hg : Asymptotics.IsBigO l g scale)
    (hscale_nonneg : ∀ᶠ x in l, 0 ≤ scale x) :
    Asymptotics.IsLittleO l (fun x => Real.sqrt (f x * g x)) scale := by
  have hprod :
      Asymptotics.IsLittleO l
        (fun x => f x * g x)
        (fun x => scale x * scale x) :=
    hf.mul_isBigO hg
  have hscale_sq_nonneg :
      ∀ᶠ x in l, 0 ≤ scale x * scale x := by
    filter_upwards with x
    exact mul_self_nonneg (scale x)
  have hsqrt :
      Asymptotics.IsLittleO l
        (fun x => Real.sqrt (f x * g x))
        (fun x => Real.sqrt (scale x * scale x)) :=
    hprod.sqrt hscale_sq_nonneg
  have hsqrt_scale :
      (fun x => Real.sqrt (scale x * scale x)) =ᶠ[l] scale := by
    filter_upwards [hscale_nonneg] with x hx
    exact Real.sqrt_mul_self hx
  exact hsqrt.trans_eventuallyEq hsqrt_scale

/-! Promoted from Staging/exists_nonneg_uniform_norm_bound_of_finite_of_isCompact_of_continuousOn.lean. -/


-- Generalization plan (G0):
-- concept/name: finite-family compact continuous uniform norm bound; orig was two_step_counterexample_phase_input_channel_bound_on_interval
-- generality used: an arbitrary topological domain, seminormed additive-group codomain, finite index type, compact set, and componentwise continuity; no measure, convexity, smoothness, oracle, completeness, or linear structure
-- portable call pattern: finite-mode stochastic recursions and distributed channel estimates can bound every continuous mode or node map on one compact parameter set; the index type, parameter carrier, compact set, codomain, and maps vary while one common nonnegative norm bound is returned
-- counterargument checked: this is not paper-local traceability or a pure rename because it packages componentwise continuity, the finite product norm, and coordinate domination into one common bound; Mathlib's compact bound handles only one map
-- coverage search: `finite family continuous maps common uniform norm upper bound compact set` and `finite family continuous functions compact common norm bound`; Mathlib `IsCompact.exists_bound_of_continuousOn` and SOptLib `exists_nonneg_norm_bound_of_isCompact_of_continuousOn` cover one map only, so coverage is partial
-- minimal hypotheses: `SeminormedAddGroup E` suffices; no nonemptiness of the compact set or finite index type is needed, and all other hypotheses are already minimal

/-- A finite family of continuous normed-valued maps has one nonnegative norm bound on a compact set.

Layer: Glue | Gap: Level 1 (common compact norm bound for a finite family)
Proof: assemble the family as a map into the finite product with its sup norm, apply Mathlib's compact continuous-map bound, and dominate each coordinate by the product norm; taking a maximum with zero makes the bound nonnegative.
Source: Mathlib `IsCompact.exists_bound_of_continuousOn`, product-topology continuity, and finite-product seminorm APIs
Used in: finite-phase distributed stochastic recursions when all mode and node input channels need one bound over a compact stepsize interval before a stable-impulse estimate
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/13/proof/7
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem exists_nonneg_uniform_norm_bound_of_finite_of_isCompact_of_continuousOn
    {α E ι : Type*} [TopologicalSpace α] [SeminormedAddGroup E] [Fintype ι]
    (s : Set α) (f : ι → α → E)
    (hcompact : IsCompact s) (hcont : ∀ i, ContinuousOn (f i) s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i x, x ∈ s → ‖f i x‖ ≤ C := by
  let F : α → ι → E := fun x i => f i x
  have hF : ContinuousOn F s := continuousOn_pi.mpr hcont
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn hF
  refine ⟨max C 0, le_max_right C 0, ?_⟩
  intro i x hx
  exact (norm_le_pi_norm (F x) i).trans ((hC x hx).trans (le_max_left C 0))

/-! Promoted from Staging/Finite_exists_uniform_local_linear_bound.lean. -/


-- Generalization plan (G0):
-- concept/name: common local linear bound for a finite family; orig was
--   `two_step_counterexample_phase_input_channel_uniform_lipschitz_at_zero`
-- generality used: an arbitrary nonempty finite index type and a linearly
--   ordered type with zero, multiplication, and monotonicity of right
--   multiplication by nonnegative elements; no additive, topological, norm,
--   measure, differentiability, convexity, completeness, or
--   finite-dimensionality assumptions are needed
-- portable call pattern: finite-mode, finite-node, and finite-phase estimates
--   change the index type and scalar family while supplying one local linear
--   bound per index and receiving one radius and constant valid for all indices
-- counterargument checked: this is not paper-local traceability or a pure
--   wrapper because it packages the simultaneous finite minimum-radius and
--   maximum-constant argument needed to preserve every pointwise estimate
-- coverage search: queried `finite family pointwise local linear upper bounds
--   common positive radius nonnegative constant` and `exists uniform local
--   linear bound finite index`; Mathlib `Finite.exists_min` and
--   `Finite.exists_max` provide only the extrema, while the staged
--   `finite_family_abs_sub_le_mul_of_differentiableAt` has stronger analytic
--   premises and derives a specialized absolute-residual conclusion
-- minimal hypotheses: finiteness and nonemptiness select attained extrema;
--   linear order chooses them, while multiplication and monotonicity under
--   right multiplication by a nonnegative argument transfer each estimate to
--   the common constant

namespace Finite

/-- Pointwise local linear bounds for a nonempty finite family admit one
positive radius and one nonnegative constant valid for every family member.

Layer: Glue | Gap: Level 1 (finite-family uniformization of local linear bounds)
Proof: choose each member's radius and constant, attain the finite minimum radius and maximum constant, and enlarge each bound using nonnegativity of the argument.
Source: Mathlib `Finite.exists_min`, `Finite.exists_max`, and right multiplication monotonicity by a nonnegative element
Used in: finite-phase and finite-node distributed estimates that require one small stepsize range and one linear channel-growth constant before a stable-impulse bound
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/13/proof/7
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem exists_uniform_local_linear_bound
    {ι R : Type*} [Finite ι] [Nonempty ι]
    [LinearOrder R] [Zero R] [Mul R] [MulPosMono R]
    (phi : ι → R → R)
    (hlocal :
      ∀ i,
        ∃ delta L : R, 0 < delta ∧ 0 ≤ L ∧
          ∀ x : R, 0 ≤ x → x ≤ delta → phi i x ≤ L * x) :
    ∃ delta L : R, 0 < delta ∧ 0 ≤ L ∧
      ∀ i x, 0 ≤ x → x ≤ delta → phi i x ≤ L * x := by
  choose delta L hdelta hL hbound using hlocal
  obtain ⟨imin, hmin⟩ := Finite.exists_min delta
  obtain ⟨imax, hmax⟩ := Finite.exists_max L
  refine ⟨delta imin, L imax, hdelta imin, hL imax, ?_⟩
  intro i x hx hxi
  exact (hbound i x hx (hxi.trans (hmin i))).trans
    (mul_le_mul_of_nonneg_right (hmax i) hx)

end Finite

/-! Promoted from Staging/Module_End_normalized_circleIntegral_zpow_resolvent_succ.lean. -/


open scoped ComplexConjugate
open MeasureTheory

-- Generalization plan (G0):
-- concept/name: normalized circle integral recurrence for powers times an operator resolvent;
--   orig was zero_center_cauchy_resolvent_power_integral_succ
-- generality used: the canonical theorem uses a finite-dimensional complex normed space and an
--   algebraic endomorphism, with a finite complex-matrix specialization for entrywise callers;
--   neither statement needs an inner product
-- portable call pattern: holomorphic functional-calculus and matrix-power inductions advance
--   the monomial degree while the operator and enclosing zero-centered circle vary
-- counterargument checked: this is not a paper-local wrapper: it combines resolvent algebra,
--   circle integrability, vector-valued integration, and monomial cancellation in one recurrence
-- coverage search: searches for "circle integral zpow resolvent successor" and "resolvent
--   identity multiply operator" found Mathlib's resolvent derivative and circle-integral APIs,
--   but no theorem combining them; SOptLib had no matching declaration
-- minimal hypotheses: the operator form uses nonnegativity and boundary resolvent membership; the
--   coordinate form needs only nonnegative radius, entry integrability, and the contour recurrence

namespace Module.End

/-- Normalized zero-centered contour integrals of successive resolvent moments are related by
right multiplication by the endomorphism.

Layer: Glue | Gap: Level 2 (operator-valued Cauchy resolvent moment recurrence)
Proof: use the Banach-algebra resolvent identity pointwise on the circle, integrate the sum,
  commute right multiplication with the Bochner integral, and cancel the monomial identity term.
Source: Mathlib Banach-algebra spectrum resolvent derivative and vector-valued circle-integral APIs
Used in: the stable-complement matrix-power induction that advances one Cauchy resolvent moment
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12/proof/3
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem normalized_circleIntegral_pow_resolvent_succ
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V]
    (A : Module.End ℂ V) (theta : ℝ) (htheta_nonneg : 0 ≤ theta)
    (hcircle : ∀ z : ℂ, ‖z‖ = theta →
      z ∈ resolventSet ℂ (Module.End.toContinuousLinearMap V A))
    (m : ℕ) :
    let Ac := Module.End.toContinuousLinearMap V A
    ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ •
        (∮ z in C((0 : ℂ), theta), z ^ (m + 1) • resolvent Ac z) =
      (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ •
        (∮ z in C((0 : ℂ), theta), z ^ m • resolvent Ac z)) * Ac := by
  classical
  dsimp only
  let Ac : V →L[ℂ] V := Module.End.toContinuousLinearMap V A
  let R : ℂ → (V →L[ℂ] V) := resolvent Ac
  let c : ℂ := ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹
  have hresolvent_continuous :
      ContinuousOn R (Metric.sphere (0 : ℂ) theta) := by
    intro z hz
    have hz_norm : ‖z‖ = theta := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hz
    exact (spectrum.hasDerivAt_resolvent (hcircle z hz_norm)).continuousAt.continuousWithinAt
  have hmoment_integrable (n : ℕ) :
      CircleIntegrable (fun z : ℂ => z ^ n • R z) (0 : ℂ) theta := by
    exact ((continuousOn_pow n).smul hresolvent_continuous).circleIntegrable htheta_nonneg
  have hone_integrable :
      CircleIntegrable (fun z : ℂ => z ^ m • (1 : V →L[ℂ] V))
        (0 : ℂ) theta := by
    exact ((continuousOn_pow m).smul continuousOn_const).circleIntegrable htheta_nonneg
  have hresolvent_mul : ∀ z : ℂ, ‖z‖ = theta →
      R z * Ac = z • R z - 1 := by
    intro z hz
    have hzmem := hcircle z hz
    have hinv_mul : R z * (algebraMap ℂ (V →L[ℂ] V) z - Ac) = 1 := by
      change resolvent Ac z * (algebraMap ℂ (V →L[ℂ] V) z - Ac) = 1
      rw [spectrum.resolvent_eq hzmem]
      exact hzmem.unit.inv_mul
    have hscalar : R z * algebraMap ℂ (V →L[ℂ] V) z = z • R z := by
      simp [Algebra.algebraMap_eq_smul_one]
    calc
      R z * Ac = R z * algebraMap ℂ (V →L[ℂ] V) z - 1 := by
        rw [eq_sub_iff_add_eq, ← hinv_mul, mul_sub]
        abel
      _ = z • R z - 1 := by rw [hscalar]
  have hpoint :
      Set.EqOn
        (fun z : ℂ => z ^ (m + 1) • R z)
        (fun z : ℂ => (z ^ m • R z) * Ac + z ^ m • (1 : V →L[ℂ] V))
        (Metric.sphere (0 : ℂ) theta) := by
    intro z hz
    have hz_norm : ‖z‖ = theta := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hz
    have hrec := hresolvent_mul z hz_norm
    calc
      z ^ (m + 1) • R z = z ^ m • (z • R z) := by
        rw [pow_succ, smul_smul]
      _ = z ^ m • (R z * Ac + 1) := by rw [hrec]; abel
      _ = (z ^ m • R z) * Ac + z ^ m • (1 : V →L[ℂ] V) := by
        rw [smul_add, smul_mul_assoc]
  have hmul_integrable :
      CircleIntegrable (fun z : ℂ => (z ^ m • R z) * Ac) (0 : ℂ) theta := by
    have hcont : ContinuousOn (fun z : ℂ => (z ^ m • R z) * Ac)
        (Metric.sphere (0 : ℂ) theta) :=
      (((continuousOn_pow m).smul hresolvent_continuous).mul continuousOn_const)
    exact hcont.circleIntegrable htheta_nonneg
  have hcongr :
      (∮ z in C((0 : ℂ), theta), z ^ (m + 1) • R z) =
        ∮ z in C((0 : ℂ), theta),
          (z ^ m • R z) * Ac + z ^ m • (1 : V →L[ℂ] V) :=
    circleIntegral.integral_congr htheta_nonneg hpoint
  have hsplit :
      (∮ z in C((0 : ℂ), theta),
          (z ^ m • R z) * Ac + z ^ m • (1 : V →L[ℂ] V)) =
        (∮ z in C((0 : ℂ), theta), (z ^ m • R z) * Ac) +
          (∮ z in C((0 : ℂ), theta), z ^ m • (1 : V →L[ℂ] V)) :=
    circleIntegral.integral_add hmul_integrable hone_integrable
  have hid_zero :
      (∮ z in C((0 : ℂ), theta), z ^ m • (1 : V →L[ℂ] V)) = 0 := by
    rw [circleIntegral.integral_smul_const]
    have hzpow : (∮ z in C((0 : ℂ), theta), z ^ m) = 0 := by
      exact Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
        htheta_nonneg (s := (∅ : Set ℂ)) Set.countable_empty
        (fun z _ => (continuousAt_pow z m).continuousWithinAt)
        (fun _ _ => differentiableAt_pow (𝕜 := ℂ) m)
    rw [hzpow, zero_smul]
  have hmul_pull :
      (∮ z in C((0 : ℂ), theta), (z ^ m • R z) * Ac) =
        (∮ z in C((0 : ℂ), theta), z ^ m • R z) * Ac := by
    let L : (V →L[ℂ] V) →L[ℂ] (V →L[ℂ] V) :=
      (ContinuousLinearMap.mul ℂ (V →L[ℂ] V)).flip Ac
    change (∮ z in C((0 : ℂ), theta), L (z ^ m • R z)) =
      L (∮ z in C((0 : ℂ), theta), z ^ m • R z)
    simp only [circleIntegral]
    exact L.intervalIntegral_comp_comm (hmoment_integrable m).out
  calc
    c • (∮ z in C((0 : ℂ), theta), z ^ (m + 1) • R z) =
        c • ((∮ z in C((0 : ℂ), theta), (z ^ m • R z) * Ac) + 0) := by
          rw [hcongr, hsplit, hid_zero]
    _ = c • ((∮ z in C((0 : ℂ), theta), z ^ m • R z) * Ac) := by
          rw [add_zero, hmul_pull]
    _ = (c • (∮ z in C((0 : ℂ), theta), z ^ m • R z)) * Ac := by
          rw [smul_mul_assoc]

end Module.End

namespace Matrix

/-- Entrywise normalized circle integrals advance one resolvent moment when the kernel satisfies
the right resolvent recurrence on the contour.

Layer: Glue | Gap: Level 2 (finite-coordinate resolvent moment recurrence under integration)
Proof: expand the pointwise recurrence entrywise, exchange the finite sum with the contour
  integral, pull out constant matrix entries, and cancel the polynomial identity contribution.
Source: Mathlib vector-valued circle-integral linearity and finite matrix multiplication APIs
Used in: the stable-complement Cauchy matrix-power induction after contour resolvent integrability
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12/proof/3
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem normalized_circleIntegral_pow_resolvent_succ_apply
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ ℂ) (R : ℂ → Matrix κ κ ℂ)
    (theta : ℝ) (htheta_nonneg : 0 ≤ theta) (m : ℕ) (i k : κ)
    (hentry_integrable : ∀ l : κ,
      CircleIntegrable (fun z : ℂ => z ^ m * R z i l) (0 : ℂ) theta)
    (hresolventRightMul : ∀ z : ℂ, ‖z‖ = theta →
      R z * A = z • R z - (1 : Matrix κ κ ℂ)) :
    (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
        (∮ z in C((0 : ℂ), theta), z ^ (m + 1) * R z i k) =
      ∑ l : κ,
        ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
          (∮ z in C((0 : ℂ), theta), z ^ m * R z i l)) * A l k := by
  classical
  let c : ℂ := ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹
  have hterm_integrable : ∀ l ∈ (Finset.univ : Finset κ),
      CircleIntegrable (fun z : ℂ => z ^ m * R z i l * A l k) (0 : ℂ) theta := by
    intro l _hl
    have hscaled :
        CircleIntegrable (fun z : ℂ => A l k * (z ^ m * R z i l)) (0 : ℂ) theta := by
      simpa [Pi.smul_apply, smul_eq_mul] using
        (hentry_integrable l).const_smul (a := A l k)
    simpa [mul_assoc, mul_comm, mul_left_comm] using hscaled
  have hsum_integrable :
      CircleIntegrable
        (fun z : ℂ => ∑ l ∈ (Finset.univ : Finset κ), z ^ m * R z i l * A l k)
        (0 : ℂ) theta :=
    CircleIntegrable.fun_sum (Finset.univ : Finset κ) hterm_integrable
  have hid_integrable :
      CircleIntegrable (fun z : ℂ => z ^ m * (1 : Matrix κ κ ℂ) i k)
        (0 : ℂ) theta := by
    exact ((continuousOn_pow m).mul continuousOn_const).circleIntegrable htheta_nonneg
  have hpoint :
      Set.EqOn
        (fun z : ℂ => z ^ (m + 1) * R z i k)
        (fun z : ℂ =>
          (∑ l ∈ (Finset.univ : Finset κ), z ^ m * R z i l * A l k) +
            z ^ m * (1 : Matrix κ κ ℂ) i k)
        (Metric.sphere (0 : ℂ) theta) := by
    intro z hz
    have hz_norm : ‖z‖ = theta := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hz
    have hentry := congrArg (fun M : Matrix κ κ ℂ => M i k)
      (hresolventRightMul z hz_norm)
    have hsum_eq :
        (∑ l : κ, R z i l * A l k) = z * R z i k - (1 : Matrix κ κ ℂ) i k := by
      simpa [Matrix.mul_apply, Pi.smul_apply, smul_eq_mul] using hentry
    have hzR_eq :
        z * R z i k = (∑ l : κ, R z i l * A l k) + (1 : Matrix κ κ ℂ) i k := by
      rw [hsum_eq]
      ring
    calc
      z ^ (m + 1) * R z i k = z ^ m * (z * R z i k) := by
        rw [pow_succ']
        ring
      _ = z ^ m * ((∑ l : κ, R z i l * A l k) + (1 : Matrix κ κ ℂ) i k) := by
        rw [hzR_eq]
      _ = (∑ l ∈ (Finset.univ : Finset κ), z ^ m * R z i l * A l k) +
          z ^ m * (1 : Matrix κ κ ℂ) i k := by
        rw [mul_add, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro l _hl
        ring
  have hcongr :
      (∮ z in C((0 : ℂ), theta), z ^ (m + 1) * R z i k) =
        ∮ z in C((0 : ℂ), theta),
          (∑ l ∈ (Finset.univ : Finset κ), z ^ m * R z i l * A l k) +
            z ^ m * (1 : Matrix κ κ ℂ) i k :=
    circleIntegral.integral_congr htheta_nonneg hpoint
  have hsplit :
      (∮ z in C((0 : ℂ), theta),
          (∑ l ∈ (Finset.univ : Finset κ), z ^ m * R z i l * A l k) +
            z ^ m * (1 : Matrix κ κ ℂ) i k) =
        (∮ z in C((0 : ℂ), theta),
          ∑ l ∈ (Finset.univ : Finset κ), z ^ m * R z i l * A l k) +
          (∮ z in C((0 : ℂ), theta), z ^ m * (1 : Matrix κ κ ℂ) i k) :=
    circleIntegral.integral_add hsum_integrable hid_integrable
  have hsum_exchange :
      (∮ z in C((0 : ℂ), theta),
        ∑ l ∈ (Finset.univ : Finset κ), z ^ m * R z i l * A l k) =
        ∑ l ∈ (Finset.univ : Finset κ),
          ∮ z in C((0 : ℂ), theta), z ^ m * R z i l * A l k :=
    circleIntegral.integral_fun_sum hterm_integrable
  have hid_zero :
      (∮ z in C((0 : ℂ), theta), z ^ m * (1 : Matrix κ κ ℂ) i k) = 0 := by
    rw [show (fun z : ℂ => z ^ m * (1 : Matrix κ κ ℂ) i k) =
        fun z : ℂ => (1 : Matrix κ κ ℂ) i k * z ^ m by
          funext z
          ring]
    rw [circleIntegral.integral_const_mul]
    have hzpow : (∮ z in C((0 : ℂ), theta), z ^ m) = 0 := by
      exact Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
        htheta_nonneg (s := (∅ : Set ℂ)) Set.countable_empty
        (fun z _ => (continuousAt_pow z m).continuousWithinAt)
        (fun _ _ => differentiableAt_pow (𝕜 := ℂ) m)
    rw [hzpow, mul_zero]
  have hconst_pull : ∀ l : κ,
      (∮ z in C((0 : ℂ), theta), z ^ m * R z i l * A l k) =
        A l k * (∮ z in C((0 : ℂ), theta), z ^ m * R z i l) := by
    intro l
    rw [show (fun z : ℂ => z ^ m * R z i l * A l k) =
        fun z : ℂ => A l k * (z ^ m * R z i l) by
          funext z
          ring]
    exact circleIntegral.integral_const_mul
      (A l k) (fun z : ℂ => z ^ m * R z i l) (0 : ℂ) theta
  calc
    c * (∮ z in C((0 : ℂ), theta), z ^ (m + 1) * R z i k) =
        c * ((∑ l ∈ (Finset.univ : Finset κ),
          ∮ z in C((0 : ℂ), theta), z ^ m * R z i l * A l k) + 0) := by
      rw [hcongr, hsplit, hsum_exchange, hid_zero]
    _ = c * (∑ l ∈ (Finset.univ : Finset κ),
        A l k * (∮ z in C((0 : ℂ), theta), z ^ m * R z i l)) := by
      congr 1
      rw [add_zero]
      apply Finset.sum_congr rfl
      intro l _hl
      exact hconst_pull l
    _ = ∑ l ∈ (Finset.univ : Finset κ),
        (c * (∮ z in C((0 : ℂ), theta), z ^ m * R z i l)) * A l k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _hl
      ring

end Matrix

/-! Promoted from Staging/Matrix_norm_normalized_circleIntegral_neumann_resolvent_remainder_le.lean. -/


open scoped Matrix.Norms.Operator

-- Generalization plan (G0):
-- concept/name: norm bound for the normalized circle integral of a finite
--   Neumann resolvent remainder; orig was
--   `zero_center_neumann_remainder_integral_bound`
-- generality used: an arbitrary finite matrix coordinate type over `Complex`,
--   a nonnegative contour radius, a uniform resolvent bound, a truncation
--   index, and selected coordinates; no algorithm setup or real-matrix origin
-- portable call pattern: matrix Cauchy-power, transfer-operator, and stable
--   finite-system proofs can vary the matrix, radius, inverse bound,
--   truncation, and entry while retaining the integrated geometric-tail bound
-- counterargument checked: the generic Mathlib circle-integral estimate alone
--   does not expose the Neumann-resolvent contract, while the staged pointwise
--   companion stops before contour aggregation; their composition is a
--   reusable mathematical step rather than paper-local traceability
-- coverage search: queries for `normalized circle integral finite Neumann
--   resolvent remainder norm bounded by radius uniform resolvent geometric
--   power` and `circle integral norm upper bound pointwise constant on sphere`
--   found `Matrix.neumann_resolvent_remainder_entry_norm_le_on_sphere` and
--   `circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const` as
--   strict component results, but no Mathlib or SOptLib theorem with this
--   complete signature
-- minimal hypotheses: `Fintype`, `DecidableEq`, and `0 ≤ R` suffice; a
--   separate positivity hypothesis for `R` and nonnegativity hypothesis for
--   `M` from the source declaration are not used

namespace Matrix

/-- The normalized circle integral of an entry of a finite Neumann resolvent
remainder is bounded by the contour radius times its geometric tail estimate.

Layer: Glue | Gap: Level 1 (integrated finite-matrix Neumann resolvent tail bound)
Proof: apply the entrywise Neumann remainder estimate on the sphere, then aggregate its uniform pointwise bound with Mathlib's normalized circle-integral norm inequality.
Source: Mathlib circle-integral norm estimates and finite-matrix induced `L∞` operator norms
Used in: matrix Cauchy-power and stable-resolvent arguments that discard a finite Neumann truncation tail after normalized contour integration
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12/proof/3
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem norm_normalized_circleIntegral_neumann_resolvent_remainder_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (R M : ℝ) (hR_nonneg : 0 ≤ R)
    (hM_bound :
      ∀ z : ℂ, ‖z‖ = R →
        ‖(z • (1 : Matrix ι ι ℂ) - A)⁻¹‖ ≤ M)
    (N : ℕ) (i k : ι) :
    ‖(2 * Real.pi * Complex.I : ℂ)⁻¹ •
        (∮ z in C((0 : ℂ), R),
          (((z⁻¹) ^ (N + 1) •
            ((z • (1 : Matrix ι ι ℂ) - A)⁻¹ * A ^ (N + 1))) i k))‖ ≤
      R * (M * (‖A‖ / R) ^ (N + 1)) := by
  apply circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
    hR_nonneg
  exact Matrix.neumann_resolvent_remainder_entry_norm_le_on_sphere
    A R M hM_bound N i k

end Matrix

/-! Promoted from Staging/eq_zero_of_norm_le_of_tendsto_zero.lean. -/


open Filter Topology

-- Generalization plan (G0):
-- concept/name: vanishing of a fixed normed-group element under a convergent
--   scalar majorant; orig was zero_center_norm_le_geometric_tail_for_all_N_forces_eq_zero
-- generality used: an arbitrary normed additive group, an arbitrary
--   nontrivial filter, and an eventual real-valued norm majorant tending to zero
-- portable call pattern: approximation, truncation, and contour-limit proofs can
--   change the element, index type, filter, and majorant while retaining equality to zero
-- counterargument checked: this is not paper-local geometric bookkeeping;
--   Mathlib's squeeze theorem yields convergence of a varying function but does
--   not expose the fixed-element zero conclusion under an eventual bound
-- coverage search: "norm le tendsto zero implies eq zero" and "constant vector
--   norm eventually bounded by real function converging to zero equals zero";
--   Mathlib squeeze_zero_norm' and norm_le_zero_iff are partial, with no full match
-- minimal hypotheses: the pointwise geometric bound is weakened to an eventual
--   bound; NeBot is necessary for limit comparison and Normed is necessary to
--   turn zero norm into equality, so Seminormed alone does not suffice

/-- A fixed element is zero if its norm is eventually bounded by a real
majorant converging to zero along a nontrivial filter.

Layer: Glue | Gap: Level 0 (fixed-element vanishing under a convergent norm majorant)
Proof: pass the eventual norm inequality to the limits with `le_of_tendsto_of_tendsto`, then use `norm_le_zero_iff`.
Source: Mathlib filter limit comparison and normed additive group separation APIs
Used in: geometric truncation and contour-remainder arguments that identify an exact limit after every finite-tail error bound vanishes
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12/proof/3
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem eq_zero_of_norm_le_of_tendsto_zero
    {E ι : Type*} [NormedAddGroup E]
    (l : Filter ι) [NeBot l] (x : E) (u : ι → ℝ)
    (hbound : ∀ᶠ i in l, ‖x‖ ≤ u i)
    (hu : Tendsto u l (nhds 0)) :
    x = 0 := by
  exact norm_le_zero_iff.mp
    (le_of_tendsto_of_tendsto tendsto_const_nhds hu hbound)

/-! Promoted from Staging/eq_zero_of_invariant_along_geometrically_contracting_orbit.lean. -/


open Filter Topology

-- Generalization plan (G0):
-- concept/name: vanishing of a functional invariant along an orbit with a
--   geometric norm bound; orig was quadraticRestrictedTrackerInvariantFunctional_eq_zero
-- generality used: an arbitrary orbit carrier and a normed additive codomain;
--   no linearity, topology, finite dimensionality, measure, or convexity is used
-- portable call pattern: consensus, fixed-point, stable-subspace, and
--   Poisson-equation proofs can change the orbit, functional, geometric
--   constants, and initial point while retaining the zero conclusion
-- counterargument checked: this is not merely paper-local traceability or a
--   pure wrapper; it combines invariance along a varying orbit with geometric
--   decay to identify the invariant value, while the existing vanishing-majorant
--   lemma handles only the final fixed-element limit step
-- coverage search: symbol and semantic searches for "functional equals zero
--   invariant along geometrically contracting orbit norm bound" and "fixed
--   element norm bounded by geometric sequence tends to zero" found Mathlib's
--   tendsto_pow_atTop_nhds_zero_of_norm_lt_one and the staged
--   eq_zero_of_norm_le_of_tendsto_zero, both partial rather than full matches
-- minimal hypotheses: the orbit carrier needs no structure; NormedAddGroup on
--   the codomain is needed to turn zero norm into equality, and `‖q‖ < 1`
--   subsumes separate sign and strict-upper-bound assumptions on the ratio

/-- A functional that is invariant along an orbit and geometrically bounded
there has zero value at the initial point.

Layer: Glue | Gap: Level 1 (invariant functional vanishing along a geometrically bounded orbit)
Proof: rewrite the fixed initial value as each invariant orbit value, then apply `eq_zero_of_norm_le_of_tendsto_zero` to the geometric majorant using convergence of powers with ratio norm below one.
Source: Mathlib geometric-power limits and filter comparison for norms
Used in: identifying zero stable or corrected-lift coordinates after invariance propagates them along a contracting consensus or fixed-point orbit
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/14/proof/3
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem eq_zero_of_invariant_along_geometrically_contracting_orbit
    {V W : Type*} [NormedAddGroup W]
    (orbit : ℕ → V) (Phi : V → W) (C q : ℝ)
    (hinvariant : ∀ n : ℕ, Phi (orbit n) = Phi (orbit 0))
    (hbound : ∀ n : ℕ, ‖Phi (orbit n)‖ ≤ C * q ^ n)
    (hq : ‖q‖ < 1) :
    Phi (orbit 0) = 0 := by
  apply eq_zero_of_norm_le_of_tendsto_zero atTop (Phi (orbit 0))
    (fun n : ℕ ↦ C * q ^ n)
  · filter_upwards with n
    simpa [hinvariant n] using hbound n
  · simpa using (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq).const_mul C

/-! Promoted from Staging/circleIntegral_normalized_zero_center_inv_pow_succ_mul_const.lean. -/


open MeasureTheory

-- Generalization plan (G0):
-- concept/name: normalized zero-centered circle integral as a Laurent coefficient selector; orig was `zero_center_normalized_circleIntegral_inv_pow_succ_mul_const`.
-- generality used: arbitrary nonzero real radius, natural Laurent index, and complex coefficient; no algorithm setup, measure assumption, finite-dimensional space, convexity, smoothness, or oracle hypothesis is used.
-- portable call pattern: Laurent-series, residue, and Cauchy-coefficient proofs vary the contour radius, inverse-power exponent, and coefficient while retaining the same normalized coefficient-selection conclusion.
-- counterargument checked: this is not paper-local traceability or a pure rename; it packages the recurring normalized coefficient-selection step, while Mathlib exposes only the simple-pole and nonexceptional-zpow integral formulas separately.
-- coverage search: `lean_search_symbols` queries "normalized circle integral inverse power times constant equals coefficient zero centered positive radius" and "circle integral zpow equals zero exponent not minus one" found the source theorem and Mathlib's component `circleIntegral.integral_sub_zpow_of_ne`, but no matching SOptLib theorem; `lean_leansearch` found `circleIntegral.integral_sub_inv_of_mem_ball` and the more general Cauchy derivative formula, neither of which directly gives the stated coefficient selector without splitting cases and normalizing.
-- minimal hypotheses: nonzeroness of the radius is necessary for the simple-pole case `n = 0`; the exponent and coefficient assumptions are already minimal.

/-- The normalized zero-centered circle integral of an inverse-power monomial
times a constant selects exactly its `z⁻¹` coefficient.

Layer: Glue | Gap: Level 1 (normalized Laurent-monomial coefficient selection)
Proof: split on the natural exponent; evaluate the simple-pole case with `circleIntegral.integral_sub_center_inv`, and cancel every higher inverse power using `circleIntegral.integral_sub_zpow_of_ne`.
Source: Mathlib circle-integral formulas for a simple pole inside a disk and for nonexceptional integer powers
Used in: finite Neumann--Laurent prefix integration, where all higher inverse-power terms vanish and only the constant matrix coefficient remains
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12/proof/3
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem circleIntegral.normalized_zero_center_inv_pow_succ_mul_const
    {R : ℝ} (hR_ne : R ≠ 0) (n : ℕ) (c : ℂ) :
    (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
        (∮ z in C((0 : ℂ), R), (z⁻¹) ^ (n + 1) * c) =
      if n = 0 then c else 0 := by
  classical
  cases n with
  | zero =>
      have hinv :
          (∮ z in C((0 : ℂ), R), z⁻¹) =
            (2 : ℂ) * (Real.pi : ℂ) * Complex.I := by
        simpa [sub_zero] using
          (circleIntegral.integral_sub_center_inv (0 : ℂ) (R := R) hR_ne)
      have hconst :
          (∮ z in C((0 : ℂ), R), z⁻¹ * c) =
            c * (∮ z in C((0 : ℂ), R), z⁻¹) := by
        rw [show (fun z : ℂ ↦ z⁻¹ * c) = fun z : ℂ ↦ c * z⁻¹ by
          funext z
          ring]
        exact circleIntegral.integral_const_mul c (fun z : ℂ ↦ z⁻¹) (0 : ℂ) R
      simp only [zero_add, pow_one, if_pos]
      rw [hconst, hinv, mul_comm c]
      rw [← mul_assoc, inv_mul_cancel₀ Complex.two_pi_I_ne_zero, one_mul]
  | succ n =>
      let m : ℕ := Nat.succ n + 1
      have hm_pos : 0 < m := by
        dsimp [m]
        omega
      have hne : -((m : ℤ)) ≠ -1 := by
        dsimp [m]
        omega
      have hbase :
          (∮ z in C((0 : ℂ), R), (z - (0 : ℂ)) ^ (-((m : ℤ)))) = 0 := by
        exact circleIntegral.integral_sub_zpow_of_ne
          (n := -((m : ℤ))) hne (0 : ℂ) (0 : ℂ) R
      have hconst :
          (∮ z in C((0 : ℂ), R), (z ^ m)⁻¹ * c) =
            c * (∮ z in C((0 : ℂ), R),
              (z - (0 : ℂ)) ^ (-((m : ℤ)))) := by
        rw [show (fun z : ℂ ↦ (z ^ m)⁻¹ * c) =
            fun z : ℂ ↦ c * (z - (0 : ℂ)) ^ (-((m : ℤ))) by
          funext z
          rw [sub_zero, zpow_neg_coe_of_pos z hm_pos]
          ring]
        exact circleIntegral.integral_const_mul c
          (fun z : ℂ ↦ (z - (0 : ℂ)) ^ (-((m : ℤ)))) (0 : ℂ) R
      have hzero :
          (∮ z in C((0 : ℂ), R),
              (z⁻¹) ^ (Nat.succ n + 1) * c) = 0 := by
        simpa [m] using (by
          rw [hconst, hbase, mul_zero])
      rw [hzero]
      simp

/-! Promoted from Staging/circleIntegral_normalized_sum_inv_pow_succ_smul_eq_zero_coeff.lean. -/


open MeasureTheory
open scoped BigOperators

-- Generalization plan (G0):
-- concept/name: normalized circle integral of a finite inverse-power Laurent sum extracts its zeroth coefficient; orig was `zero_center_neumann_prefix_integral_eq_one_entry`.
-- generality used: arbitrary complete normed complex vector space, coefficient family indexed by naturals, nonzero real contour radius, and finite truncation; no matrix, finite-dimensional, spectral, measure, convexity, smoothness, or oracle assumptions are used.
-- portable call pattern: finite Laurent and resolvent-prefix proofs vary the coefficient family, contour radius, and truncation while using the same normalized contour coefficient-extraction conclusion.
-- counterargument checked: the theorem is not a matrix-entry wrapper or paper-local traceability; it combines vector-valued contour integration, finite-sum exchange, and Laurent coefficient selection into a reusable step beyond the previously staged scalar monomial case.
-- coverage search: `lean_search_symbols` and `lean_leansearch` queries for normalized finite inverse-power sums found the scalar component `circleIntegral.normalized_zero_center_inv_pow_succ_mul_const` and Mathlib linearity lemmas `circleIntegral.integral_fun_sum` and `circleIntegral.integral_smul_const`, but no finite-sum vector-valued coefficient extractor.
-- minimal hypotheses: completeness is required by Mathlib's integral-of-scalar-times-constant theorem, and radius nonzeroness is required by coefficient extraction and keeps every inverse-power term continuous on the contour sphere.

/-- The normalized zero-centered circle integral of a finite inverse-power
Laurent sum extracts its zeroth coefficient.

Layer: Glue | Gap: Level 1 (vector-valued finite Laurent coefficient extraction)
Proof: exchange the finite sum with the circle integral, pull each constant vector coefficient through the integral, and apply normalized scalar Laurent-monomial coefficient selection termwise.
Source: Mathlib vector-valued circle-integral finite-sum and scalar-multiplication APIs together with the zero-centered Laurent monomial integral formula
Used in: finite Neumann and resolvent-prefix contour calculations where the normalized integral discards every higher inverse-power term and retains the identity coefficient
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12/proof/3
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem circleIntegral.normalized_sum_inv_pow_succ_smul_eq_zero_coeff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (coeff : ℕ → E) (R : ℝ) (N : ℕ) (hR_ne : R ≠ 0) :
    ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ •
        (∮ z in C((0 : ℂ), R),
          ∑ n ∈ Finset.range (N + 1), (z⁻¹) ^ (n + 1) • coeff n) =
      coeff 0 := by
  have hterm_integrable :
      ∀ n ∈ Finset.range (N + 1),
        CircleIntegrable (fun z : ℂ => (z⁻¹) ^ (n + 1) • coeff n)
          (0 : ℂ) R := by
    intro n _hn
    have hcont :
        ContinuousOn (fun z : ℂ => (z⁻¹) ^ (n + 1) • coeff n)
          (Metric.sphere (0 : ℂ) |R|) := by
      intro z hz
      have hz_norm : ‖z‖ = |R| := by
        simpa [Metric.mem_sphere, dist_eq_norm] using hz
      have hz_ne : z ≠ 0 := by
        intro hz0
        have hR_abs_zero : |R| = 0 := by
          simpa [hz0] using hz_norm.symm
        exact hR_ne (abs_eq_zero.mp hR_abs_zero)
      exact (((continuousAt_inv₀ hz_ne).pow (n + 1)).smul
        (continuousAt_const : ContinuousAt (fun _ : ℂ => coeff n) z)).continuousWithinAt
    exact hcont.circleIntegrable'
  rw [circleIntegral.integral_fun_sum hterm_integrable, Finset.smul_sum]
  calc
    (∑ n ∈ Finset.range (N + 1),
        ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ •
          (∮ z in C((0 : ℂ), R), (z⁻¹) ^ (n + 1) • coeff n)) =
        ∑ n ∈ Finset.range (N + 1),
          (if n = 0 then coeff n else 0) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [circleIntegral.integral_smul_const]
      rw [← smul_assoc]
      have hscalar :
          ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
              (∮ z in C((0 : ℂ), R), (z⁻¹) ^ (n + 1)) =
            if n = 0 then 1 else 0 := by
        simpa only [mul_one] using
          (circleIntegral.normalized_zero_center_inv_pow_succ_mul_const
            hR_ne n (1 : ℂ))
      rw [show
        ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ •
            (∮ z in C((0 : ℂ), R), (z⁻¹) ^ (n + 1)) =
          if n = 0 then 1 else 0 by
            simpa only [smul_eq_mul] using hscalar]
      split_ifs <;> simp_all
    _ = coeff 0 := by
      have h0mem : 0 ∈ Finset.range (N + 1) := by simp
      rw [Finset.sum_eq_single_of_mem 0 h0mem]
      · simp
      · intro n _hn hn0
        simp [hn0]

/-! Promoted from Staging/Module_End_zero_center_rieszProjection_eq_one_of_spectrum_inside_disk.lean. -/


noncomputable section

open Filter MeasureTheory Topology
open scoped Matrix.Norms.Operator

-- Generalization plan (G0):
-- concept/name: zero-centered Riesz projection equals the identity when the entire spectrum is
--   strictly inside the contour; orig was zero_center_resolvent_projection_eq_one_of_spectrum_inside_disk
-- generality used: an arbitrary finite-dimensional complex normed space and algebraic endomorphism;
--   no basis, matrix coordinates, inner product, or separate contour-boundary hypothesis is used
-- portable call pattern: finite-dimensional spectral proofs for consensus, Markov, transfer, and
--   distributed-optimization operators vary the operator and enclosing radius while reusing the
--   whole-spectrum contour projection identity
-- counterargument checked: this is not paper-local traceability or a one-line wrapper; Mathlib has
--   resolvent holomorphy and circle-integral APIs but no whole-spectrum Riesz-projection theorem,
--   while existing staged results cover only matrix contour deformation or resolvent recurrences
-- coverage search: queries "Riesz projection equals identity entire spectrum inside circle" and
--   "normalized circle integral resolvent equals identity spectrum disk" found Mathlib resolvent
--   differentiability, staged matrix annulus invariance, and the operator moment successor only;
--   none has this conclusion at the basis-free Module.End level
-- minimal hypotheses: strict containment alone implies boundary resolvent membership; finite
--   dimensionality is used only to continuously realize the algebraic endomorphism

namespace Module.End

set_option maxHeartbeats 800000

/-- The normalized resolvent integral on a zero-centered circle is the identity when the whole
spectrum of a finite-dimensional endomorphism lies strictly inside the circle.

Layer: Glue | Gap: Level 2 (whole-spectrum finite-dimensional Riesz projection identity)
Proof: enlarge the contour past the operator norm through a spectrum-free annulus, evaluate the
  large contour by a finite Neumann expansion, and send its geometric remainder to zero.
Source: Mathlib Banach-algebra resolvent holomorphy, complex annulus deformation, and normalized
  vector-valued circle-integral norm estimates
Used in: the base case of a stable-complement Cauchy power formula for periodic push-pull dynamics,
  and in finite-dimensional spectral decompositions whose contour encloses every spectral value
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12/proof/3
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem normalized_circleIntegral_resolvent_eq_one_of_spectrum_inside_disk
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V]
    (A : Module.End ℂ V) (theta : ℝ) (htheta_pos : 0 < theta)
    (hspectrum_inside :
      ∀ z : ℂ,
        z ∈ spectrum ℂ (Module.End.toContinuousLinearMap V A) →
          ‖z‖ < theta) :
    let Ac := Module.End.toContinuousLinearMap V A
    ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ •
        (∮ z in C((0 : ℂ), theta), resolvent Ac z) =
      (1 : V →L[ℂ] V) := by
  classical
  dsimp only
  let Ac : V →L[ℂ] V := Module.End.toContinuousLinearMap V A
  let c : ℂ := ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹
  let outerRadius : ℝ := max theta ‖Ac‖ + 1
  have htheta_le_outer : theta ≤ outerRadius := by
    dsimp [outerRadius]
    linarith [le_max_left theta ‖Ac‖]
  have hAc_lt_outer : ‖Ac‖ < outerRadius := by
    dsimp [outerRadius]
    linarith [le_max_right theta ‖Ac‖]
  have houter_pos : 0 < outerRadius :=
    lt_of_lt_of_le htheta_pos htheta_le_outer
  have houtside : ∀ z : ℂ, theta ≤ ‖z‖ → z ∈ resolventSet ℂ Ac := by
    intro z hz
    have hnot : z ∉ spectrum ℂ Ac := by
      intro hspec
      exact (not_le_of_gt (hspectrum_inside z hspec)) hz
    simpa [spectrum] using hnot
  have hdeform :
      (∮ z in C((0 : ℂ), outerRadius), resolvent Ac z) =
        ∮ z in C((0 : ℂ), theta), resolvent Ac z := by
    refine Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable
      (c := (0 : ℂ)) htheta_pos htheta_le_outer (s := (∅ : Set ℂ))
      Set.countable_empty ?_ ?_
    · intro z hz
      rcases hz with ⟨hzclosed, hznotball⟩
      have hlower : theta ≤ ‖z‖ := by
        have hnotlt : ¬ dist z (0 : ℂ) < theta := by
          intro hlt
          exact hznotball (Metric.mem_ball.2 hlt)
        simpa [dist_eq_norm] using le_of_not_gt hnotlt
      exact (spectrum.hasDerivAt_resolvent (houtside z hlower)).continuousAt.continuousWithinAt
    · intro z hz
      rcases hz with ⟨⟨_hzball, hznotclosed⟩, _hznotempty⟩
      have hlower : theta ≤ ‖z‖ := by
        have hnotle : ¬ dist z (0 : ℂ) ≤ theta := by
          intro hle
          exact hznotclosed (Metric.mem_closedBall.2 hle)
        exact le_of_lt (by simpa [dist_eq_norm] using lt_of_not_ge hnotle)
      exact (spectrum.hasDerivAt_resolvent (houtside z hlower)).differentiableAt
  have houter_resolvent : ∀ z : ℂ, ‖z‖ = outerRadius →
      z ∈ resolventSet ℂ Ac := by
    intro z hz
    apply spectrum.mem_resolventSet_of_norm_lt_mul
    calc
      ‖Ac‖ * ‖(1 : V →L[ℂ] V)‖ ≤ ‖Ac‖ * 1 := by
        gcongr
        change ‖ContinuousLinearMap.id ℂ V‖ ≤ 1
        exact ContinuousLinearMap.norm_id_le
      _ = ‖Ac‖ := mul_one _
      _ < ‖z‖ := by simpa [hz] using hAc_lt_outer
  have hresolvent_continuous :
      ContinuousOn (resolvent Ac) (Metric.sphere (0 : ℂ) outerRadius) := by
    intro z hz
    have hz_norm : ‖z‖ = outerRadius := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hz
    exact (spectrum.hasDerivAt_resolvent
      (houter_resolvent z hz_norm)).continuousAt.continuousWithinAt
  obtain ⟨M, hM_nonneg, hM_bound⟩ :=
    exists_nonneg_norm_bound_of_isCompact_of_continuousOn
      (fun z : ℂ => ‖resolvent Ac z‖)
      (isCompact_sphere (0 : ℂ) outerRadius) hresolvent_continuous.norm
  have hM_bound' : ∀ z : ℂ, ‖z‖ = outerRadius →
      ‖resolvent Ac z‖ ≤ M := by
    intro z hz
    simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (resolvent Ac z))] using
      hM_bound z (by simpa [Metric.mem_sphere, dist_eq_norm] using hz)
  have hfiniteExpansion : ∀ N : ℕ, ∀ z : ℂ, ‖z‖ = outerRadius →
      resolvent Ac z =
        Finset.sum (Finset.range (N + 1))
          (fun n => (z⁻¹) ^ (n + 1) • Ac ^ n) +
        (z⁻¹) ^ (N + 1) •
          (resolvent Ac z * Ac ^ (N + 1)) := by
    intro N z hz
    have hz_ne : z ≠ 0 := by
      intro hz0
      have hzero : (0 : ℝ) = outerRadius := by simpa [hz0] using hz
      linarith
    have hzres : z ∈ resolventSet ℂ Ac := houter_resolvent z hz
    have hinv_mul : resolvent Ac z * (algebraMap ℂ (V →L[ℂ] V) z - Ac) = 1 := by
      rw [spectrum.resolvent_eq hzres]
      exact hzres.unit.inv_mul
    have hrec :
        resolvent Ac z =
          z⁻¹ • (1 : V →L[ℂ] V) + z⁻¹ • (resolvent Ac z * Ac) := by
      have hscalar : resolvent Ac z * algebraMap ℂ (V →L[ℂ] V) z =
          z • resolvent Ac z := by
        simp [Algebra.algebraMap_eq_smul_one]
      have hzres_eq : z • resolvent Ac z = resolvent Ac z * Ac + 1 := by
        rw [mul_sub, hscalar] at hinv_mul
        exact (sub_eq_iff_eq_add.mp hinv_mul).trans (add_comm _ _)
      calc
        resolvent Ac z = z⁻¹ • (z • resolvent Ac z) := by
          rw [smul_smul, inv_mul_cancel₀ hz_ne, one_smul]
        _ = z⁻¹ • (resolvent Ac z * Ac + 1) := by rw [hzres_eq]
        _ = z⁻¹ • (1 : V →L[ℂ] V) + z⁻¹ • (resolvent Ac z * Ac) := by
          rw [smul_add, add_comm]
    exact eq_sum_smul_pow_add_right_remainder_of_affine_recurrence
      (resolvent Ac z) Ac z⁻¹ hrec N
  let q : ℝ := ‖Ac‖ / outerRadius
  have hq_nonneg : 0 ≤ q := by
    exact div_nonneg (norm_nonneg Ac) houter_pos.le
  have hq_lt_one : q < 1 := by
    dsimp [q]
    rwa [div_lt_one houter_pos]
  have hnorm_pow : ∀ n : ℕ, ‖Ac ^ n‖ ≤ ‖Ac‖ ^ n := by
    intro n
    induction n with
    | zero =>
        simpa only [pow_zero] using
          (ContinuousLinearMap.norm_id_le :
            ‖ContinuousLinearMap.id ℂ V‖ ≤ 1)
    | succ n ih =>
        rw [pow_succ, pow_succ]
        exact (norm_mul_le (Ac ^ n) Ac).trans
          (mul_le_mul ih le_rfl (norm_nonneg Ac) (pow_nonneg (norm_nonneg Ac) n))
  have hremainder_pointwise : ∀ N : ℕ, ∀ z ∈ Metric.sphere (0 : ℂ) outerRadius,
      ‖(z⁻¹) ^ (N + 1) •
          (resolvent Ac z * Ac ^ (N + 1))‖ ≤
        M * q ^ (N + 1) := by
    intro N z hz
    have hz_norm : ‖z‖ = outerRadius := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hz
    calc
      ‖(z⁻¹) ^ (N + 1) • (resolvent Ac z * Ac ^ (N + 1))‖ =
          ‖z⁻¹‖ ^ (N + 1) * ‖resolvent Ac z * Ac ^ (N + 1)‖ := by
            rw [norm_smul, norm_pow]
      _ ≤ ‖z⁻¹‖ ^ (N + 1) *
          (‖resolvent Ac z‖ * ‖Ac‖ ^ (N + 1)) := by
            refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (norm_nonneg _) _)
            exact (norm_mul_le (resolvent Ac z) (Ac ^ (N + 1))).trans
              (mul_le_mul_of_nonneg_left (hnorm_pow (N + 1))
                (norm_nonneg (resolvent Ac z)))
      _ ≤ ‖z⁻¹‖ ^ (N + 1) *
          (M * ‖Ac‖ ^ (N + 1)) := by
            gcongr
            exact hM_bound' z hz_norm
      _ = M * q ^ (N + 1) := by
            rw [norm_inv, hz_norm]
            dsimp [q]
            rw [div_pow]
            ring
  have hremainderIntegralBound : ∀ N : ℕ,
      ‖c •
          (∮ z in C((0 : ℂ), outerRadius),
            (z⁻¹) ^ (N + 1) •
              (resolvent Ac z * Ac ^ (N + 1)))‖ ≤
        outerRadius * (M * q ^ (N + 1)) := by
    intro N
    simpa [c] using
      (circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
        houter_pos.le (hremainder_pointwise N))
  have hprefix_integrable : ∀ N : ℕ,
      CircleIntegrable
        (fun z : ℂ => Finset.sum (Finset.range (N + 1))
          (fun n => (z⁻¹) ^ (n + 1) • Ac ^ n))
        (0 : ℂ) outerRadius := by
    intro N
    apply CircleIntegrable.fun_sum
    intro n _hn
    have hcont : ContinuousOn
        (fun z : ℂ => (z⁻¹) ^ (n + 1) • Ac ^ n)
        (Metric.sphere (0 : ℂ) outerRadius) := by
      intro z hz
      have hz_norm : ‖z‖ = outerRadius := by
        simpa [Metric.mem_sphere, dist_eq_norm] using hz
      have hz_ne : z ≠ 0 := by
        intro hz0
        have hzero : (0 : ℝ) = outerRadius := by simpa [hz0] using hz_norm
        linarith
      exact (((continuousAt_inv₀ hz_ne).pow (n + 1)).smul
        continuousAt_const).continuousWithinAt
    exact hcont.circleIntegrable houter_pos.le
  have hprefix_eval : ∀ N : ℕ,
      c •
          (∮ z in C((0 : ℂ), outerRadius),
            Finset.sum (Finset.range (N + 1))
              (fun n => (z⁻¹) ^ (n + 1) • Ac ^ n)) =
        (1 : V →L[ℂ] V) := by
    intro N
    have hterm_integrable : ∀ n ∈ Finset.range (N + 1),
        CircleIntegrable (fun z : ℂ => (z⁻¹) ^ (n + 1) • Ac ^ n)
          (0 : ℂ) outerRadius := by
      intro n _hn
      have hcont : ContinuousOn
          (fun z : ℂ => (z⁻¹) ^ (n + 1) • Ac ^ n)
          (Metric.sphere (0 : ℂ) outerRadius) := by
        intro z hz
        have hz_norm : ‖z‖ = outerRadius := by
          simpa [Metric.mem_sphere, dist_eq_norm] using hz
        have hz_ne : z ≠ 0 := by
          intro hz0
          have hzero : (0 : ℝ) = outerRadius := by simpa [hz0] using hz_norm
          linarith
        exact (((continuousAt_inv₀ hz_ne).pow (n + 1)).smul
          continuousAt_const).continuousWithinAt
      exact hcont.circleIntegrable houter_pos.le
    rw [circleIntegral.integral_fun_sum hterm_integrable, Finset.smul_sum]
    calc
      ∑ n ∈ Finset.range (N + 1),
          c • (∮ z in C((0 : ℂ), outerRadius),
            (z⁻¹) ^ (n + 1) • Ac ^ n) =
          ∑ n ∈ Finset.range (N + 1),
            (if n = 0 then Ac ^ n else 0) := by
              apply Finset.sum_congr rfl
              intro n hn
              rw [circleIntegral.integral_smul_const]
              cases n with
              | zero =>
                  have hmem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) outerRadius := by
                    simpa [Metric.mem_ball] using houter_pos
                  have hscalar :
                      c * (∮ z in C((0 : ℂ), outerRadius), z⁻¹) = 1 := by
                    have hinv :
                        (∮ z in C((0 : ℂ), outerRadius),
                          (z - (0 : ℂ))⁻¹) =
                            (2 : ℂ) * (Real.pi : ℂ) * Complex.I :=
                      circleIntegral.integral_sub_inv_of_mem_ball
                        (c := (0 : ℂ)) (w := (0 : ℂ))
                        (R := outerRadius) hmem
                    rw [show (∮ z in C((0 : ℂ), outerRadius), z⁻¹) =
                        ∮ z in C((0 : ℂ), outerRadius),
                          (z - (0 : ℂ))⁻¹ by simp, hinv]
                    exact inv_mul_cancel₀ Complex.two_pi_I_ne_zero
                  simpa [hscalar, smul_smul]
              | succ n =>
                  let m : ℕ := n + 2
                  have hm_pos : 0 < m := by simp [m]
                  have hne : -((m : ℤ)) ≠ -1 := by
                    dsimp [m]
                    omega
                  have hzero :
                      (∮ z in C((0 : ℂ), outerRadius),
                        (z⁻¹) ^ m) = 0 := by
                    have hbase :
                        (∮ z in C((0 : ℂ), outerRadius),
                          (z - (0 : ℂ)) ^ (-((m : ℤ)))) = 0 :=
                      circleIntegral.integral_sub_zpow_of_ne
                        (n := -((m : ℤ))) hne
                        (0 : ℂ) (0 : ℂ) outerRadius
                    simpa [sub_zero, zpow_neg_coe_of_pos, hm_pos] using hbase
                  rw [hzero, zero_smul, smul_zero]
                  simp
      _ = Ac ^ 0 := by
            have h0mem : 0 ∈ Finset.range (N + 1) := by simp
            rw [Finset.sum_eq_single_of_mem 0 h0mem]
            · simp
            · intro n _hn hn0
              simp [hn0]
      _ = (1 : V →L[ℂ] V) := by simp
  let lhs : V →L[ℂ] V :=
    c • (∮ z in C((0 : ℂ), outerRadius), resolvent Ac z)
  have hresolvent_integrable :
      CircleIntegrable (resolvent Ac) (0 : ℂ) outerRadius :=
    hresolvent_continuous.circleIntegrable houter_pos.le
  have hdiffBound : ∀ N : ℕ,
      ‖lhs - (1 : V →L[ℂ] V)‖ ≤
        outerRadius * (M * q ^ (N + 1)) := by
    intro N
    let pref : ℂ → (V →L[ℂ] V) := fun z =>
      Finset.sum (Finset.range (N + 1))
        (fun n => (z⁻¹) ^ (n + 1) • Ac ^ n)
    let rem : ℂ → (V →L[ℂ] V) := fun z =>
      (z⁻¹) ^ (N + 1) • (resolvent Ac z * Ac ^ (N + 1))
    have hrem_eq_sub :
        (∮ z in C((0 : ℂ), outerRadius), rem z) =
          ∮ z in C((0 : ℂ), outerRadius), resolvent Ac z - pref z := by
      refine circleIntegral.integral_congr houter_pos.le ?_
      intro z hz
      have hz_norm : ‖z‖ = outerRadius := by
        simpa [Metric.mem_sphere, dist_eq_norm] using hz
      have hexpand := hfiniteExpansion N z hz_norm
      change rem z = resolvent Ac z - pref z
      rw [hexpand]
      simp [pref, rem]
    have hsub_split :
        (∮ z in C((0 : ℂ), outerRadius), resolvent Ac z - pref z) =
          (∮ z in C((0 : ℂ), outerRadius), resolvent Ac z) -
            ∮ z in C((0 : ℂ), outerRadius), pref z :=
      circleIntegral.integral_sub hresolvent_integrable (by
        simpa [pref] using hprefix_integrable N)
    have hpref_eval :
        c • (∮ z in C((0 : ℂ), outerRadius), pref z) =
          (1 : V →L[ℂ] V) := by
      simpa [pref] using hprefix_eval N
    have hdiff_eq :
        lhs - (1 : V →L[ℂ] V) =
          c • (∮ z in C((0 : ℂ), outerRadius), rem z) := by
      dsimp [lhs]
      rw [← hpref_eval, hrem_eq_sub, hsub_split, smul_sub]
    rw [hdiff_eq]
    simpa [rem] using hremainderIntegralBound N
  have hdiff_zero : lhs - (1 : V →L[ℂ] V) = 0 := by
    apply eq_zero_of_norm_le_of_tendsto_zero atTop
      (lhs - (1 : V →L[ℂ] V))
      (fun N : ℕ => outerRadius * (M * q ^ (N + 1)))
    · exact Filter.Eventually.of_forall hdiffBound
    · have hq_norm_lt : ‖q‖ < 1 := by
        simpa [Real.norm_eq_abs, abs_of_nonneg hq_nonneg] using hq_lt_one
      have hpow := tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq_norm_lt
      simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using
        (hpow.const_mul q).const_mul (outerRadius * M)
  have hlhs : lhs = (1 : V →L[ℂ] V) := sub_eq_zero.mp hdiff_zero
  rw [← hdeform]
  simpa [lhs, c] using hlhs

end Module.End

namespace Matrix

/-- Entrywise finite-matrix specialization of the whole-spectrum normalized resolvent-integral
identity.

Layer: Glue | Gap: Level 1 (matrix-coordinate specialization of an operator Riesz projection)
Proof: transport the operator-valued identity through the finite matrix/continuous-endomorphism
  algebra equivalence, commute its continuous inverse with the circle integral, and evaluate one
  matrix coordinate.
Source: Mathlib finite-matrix algebra equivalence, nonsingular matrix inverse, and Bochner
  integration under continuous linear maps
Used in: coordinatewise Cauchy power formulas for finite transition and stable-complement matrices
  after a spectral disk bound has enclosed the whole spectrum
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12/proof/3
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem normalized_circleIntegral_resolvent_apply_eq_one_of_spectrum_inside_disk
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (theta : ℝ) (htheta_pos : 0 < theta)
    (hspectrum_inside : ∀ z : ℂ, z ∈ spectrum ℂ A → ‖z‖ < theta)
    (i k : ι) :
    (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
        (∮ z in C((0 : ℂ), theta),
          ((z • (1 : Matrix ι ι ℂ) - A)⁻¹) i k) =
      (1 : Matrix ι ι ℂ) i k := by
  classical
  let e := Matrix.toContinuousLinearMapAlgEquiv (K := ℂ) (ι := ι)
  let Aop : Module.End ℂ (ι → ℂ) := Matrix.toLinAlgEquiv' A
  let Op : (ι → ℂ) →L[ℂ] (ι → ℂ) :=
    Module.End.toContinuousLinearMap (ι → ℂ) Aop
  let fromOp : ((ι → ℂ) →L[ℂ] (ι → ℂ)) →L[ℂ] Matrix ι ι ℂ :=
    LinearMap.toContinuousLinearMap e.symm.toLinearMap
  have hspectrum_op : ∀ z : ℂ, z ∈ spectrum ℂ Op → ‖z‖ < theta := by
    intro z hz
    apply hspectrum_inside z
    simpa [Op, Aop, e, Matrix.toContinuousLinearMapAlgEquiv] using hz
  have hop :=
    Module.End.normalized_circleIntegral_resolvent_eq_one_of_spectrum_inside_disk
      Aop theta htheta_pos hspectrum_op
  have hboundary : ∀ z : ℂ, ‖z‖ = theta → z ∈ resolventSet ℂ Op := by
    intro z hz
    have hnot : z ∉ spectrum ℂ Op := by
      intro hspec
      exact (not_lt_of_ge (by simpa [hz] using le_rfl)) (hspectrum_op z hspec)
    simpa [spectrum] using hnot
  have hresolvent_continuous :
      ContinuousOn (resolvent Op) (Metric.sphere (0 : ℂ) theta) := by
    intro z hz
    have hz_norm : ‖z‖ = theta := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hz
    exact (spectrum.hasDerivAt_resolvent
      (hboundary z hz_norm)).continuousAt.continuousWithinAt
  have hcircleIntegrable : CircleIntegrable (resolvent Op) (0 : ℂ) theta :=
    hresolvent_continuous.circleIntegrable htheta_pos.le
  have hmap_circle :
      fromOp (∮ z in C((0 : ℂ), theta), resolvent Op z) =
        ∮ z in C((0 : ℂ), theta), fromOp (resolvent Op z) := by
    simp only [circleIntegral]
    rw [← fromOp.intervalIntegral_comp_comm hcircleIntegrable.out]
    congr 1
  have hresolvent_matrix : ∀ z : ℂ,
      fromOp (resolvent Op z) = (z • (1 : Matrix ι ι ℂ) - A)⁻¹ := by
    intro z
    apply e.injective
    have hop_sub :
        algebraMap ℂ (((ι → ℂ) →L[ℂ] (ι → ℂ))) z - Op =
          e (algebraMap ℂ (Matrix ι ι ℂ) z - A) := by
      change algebraMap ℂ (((ι → ℂ) →L[ℂ] (ι → ℂ))) z - e A =
        e (algebraMap ℂ (Matrix ι ι ℂ) z - A)
      rw [← e.commutes z]
      exact (map_sub e (algebraMap ℂ (Matrix ι ι ℂ) z) A).symm
    simpa [fromOp, resolvent, Matrix.nonsing_inv_eq_ringInverse,
      Algebra.algebraMap_eq_smul_one, hop_sub] using
      (RingEquiv.map_ringInverse e.toRingEquiv
        (algebraMap ℂ (Matrix ι ι ℂ) z - A)).symm
  have hmatrix :
      (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) •
          (∮ z in C((0 : ℂ), theta), (z • (1 : Matrix ι ι ℂ) - A)⁻¹) =
        (1 : Matrix ι ι ℂ) := by
    have hmapped := congrArg fromOp hop
    rw [map_smul, hmap_circle] at hmapped
    have hfrom_one : fromOp (1 : (ι → ℂ) →L[ℂ] (ι → ℂ)) =
        (1 : Matrix ι ι ℂ) := by
      change e.symm 1 = 1
      simp
    simpa only [hresolvent_matrix, hfrom_one] using hmapped
  have hentry := congrArg (fun M : Matrix ι ι ℂ => M i k) hmatrix
  let entryLin : Matrix ι ι ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun M => M i k
      map_add' := by simp
      map_smul' := by simp }
  let entryMap : Matrix ι ι ℂ →L[ℂ] ℂ :=
    LinearMap.toContinuousLinearMap entryLin
  have hmatrix_continuous :
      ContinuousOn (fun z : ℂ => (z • (1 : Matrix ι ι ℂ) - A)⁻¹)
        (Metric.sphere (0 : ℂ) theta) := by
    have hcomp := fromOp.continuous.comp_continuousOn hresolvent_continuous
    have heq : fromOp ∘ resolvent Op =
        fun z : ℂ => (z • (1 : Matrix ι ι ℂ) - A)⁻¹ := by
      funext z
      exact hresolvent_matrix z
    rw [heq] at hcomp
    exact hcomp
  have hmatrix_integrable :
      CircleIntegrable (fun z : ℂ => (z • (1 : Matrix ι ι ℂ) - A)⁻¹)
        (0 : ℂ) theta :=
    hmatrix_continuous.circleIntegrable htheta_pos.le
  have hentry_circle :
      (∮ z in C((0 : ℂ), theta), (z • (1 : Matrix ι ι ℂ) - A)⁻¹) i k =
        ∮ z in C((0 : ℂ), theta), ((z • (1 : Matrix ι ι ℂ) - A)⁻¹) i k := by
    change entryMap
        (∮ z in C((0 : ℂ), theta), (z • (1 : Matrix ι ι ℂ) - A)⁻¹) = _
    simp only [circleIntegral]
    rw [← entryMap.intervalIntegral_comp_comm hmatrix_integrable.out]
    congr 1
  change
    (((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹) *
        ((∮ z in C((0 : ℂ), theta), (z • (1 : Matrix ι ι ℂ) - A)⁻¹) i k) =
      (1 : Matrix ι ι ℂ) i k at hentry
  rw [hentry_circle] at hentry
  exact hentry

end Matrix

/-! Promoted from Staging/Module_End_pow_eq_normalized_circleIntegral_zpow_resolvent.lean. -/


noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator

-- Generalization plan (G0):
-- concept/name: Cauchy resolvent formula for powers of a finite-dimensional endomorphism;
--   orig was `complex_matrix_power_cauchy_entry_formula_of_spectrum_inside_disk`
-- generality used: an arbitrary finite-dimensional complex normed space and algebraic
--   endomorphism; no basis, matrix coordinates, inner product, or paper setup is needed
-- portable call pattern: spectral power estimates for consensus, Markov, and distributed-
--   optimization operators vary the endomorphism, enclosing radius, and exponent while reusing
--   the same normalized contour representation
-- counterargument checked: this is not paper-local traceability or a caller-side expression;
--   it packages the nontrivial whole-spectrum Riesz base case with the resolvent-moment recurrence
-- coverage search: queries "endomorphism power equals normalized circle integral z power
--   resolvent spectrum inside disk" and "Cauchy integral formula operator power spectrum
--   enclosed circle" found the staged base and successor contracts and Mathlib's scalar Cauchy
--   formula, but no operator-power theorem combining them
-- minimal hypotheses: strict spectral containment supplies boundary resolvent membership;
--   finite dimensionality is needed to continuously realize the algebraic endomorphism

namespace Module.End

/-- A power of a finite-dimensional complex endomorphism is the normalized circle integral of
the matching monomial times its resolvent when the circle encloses the whole spectrum.

Layer: Glue | Gap: Level 2 (finite-dimensional operator Cauchy power formula)
Proof: use the whole-spectrum normalized resolvent integral as the zero-power case, then apply
  the normalized resolvent-moment recurrence and the algebraic power recurrence inductively.
Source: Mathlib finite-dimensional continuous endomorphisms, Banach-algebra resolvents, and
  vector-valued Cauchy circle integrals
Used in: stable-complement power bounds for periodic push-pull dynamics and analogous spectral
  decay estimates where a contour encloses the full spectrum of a finite-dimensional operator
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12/proof/3
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem pow_eq_normalized_circleIntegral_pow_resolvent
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V]
    (A : Module.End ℂ V) (theta : ℝ) (htheta_pos : 0 < theta)
    (hspectrum_inside :
      ∀ z : ℂ,
        z ∈ spectrum ℂ (Module.End.toContinuousLinearMap V A) →
          ‖z‖ < theta)
    (j : ℕ) :
    let Ac := Module.End.toContinuousLinearMap V A
    Ac ^ j =
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ •
        (∮ z in C((0 : ℂ), theta), z ^ j • resolvent Ac z) := by
  classical
  dsimp only
  let Ac : V →L[ℂ] V := Module.End.toContinuousLinearMap V A
  let c : ℂ := ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹
  have hcircle : ∀ z : ℂ, ‖z‖ = theta → z ∈ resolventSet ℂ Ac := by
    intro z hz
    have hnot : z ∉ spectrum ℂ Ac := by
      intro hspec
      have hlt : ‖z‖ < theta := hspectrum_inside z hspec
      exact (lt_irrefl theta) (by simpa [hz] using hlt)
    simpa [spectrum] using hnot
  induction j with
  | zero =>
      simpa [Ac, c] using
        (normalized_circleIntegral_resolvent_eq_one_of_spectrum_inside_disk
          A theta htheta_pos hspectrum_inside).symm
  | succ j ih =>
      calc
        Ac ^ (j + 1) = Ac ^ j * Ac := pow_succ Ac j
        _ = (c • (∮ z in C((0 : ℂ), theta), z ^ j • resolvent Ac z)) * Ac := by
          rw [ih]
        _ = c • (∮ z in C((0 : ℂ), theta), z ^ (j + 1) • resolvent Ac z) := by
          simpa [Ac, c] using
            (normalized_circleIntegral_pow_resolvent_succ
              A theta htheta_pos.le hcircle j).symm

end Module.End

namespace Matrix

/-- Entrywise finite-matrix specialization of the Cauchy resolvent formula for powers.

Layer: Glue | Gap: Level 1 (finite-coordinate specialization of the operator Cauchy power formula)
Proof: transport the operator identity through the finite matrix/continuous-endomorphism algebra
  equivalence, commute its inverse with the circle integral, and evaluate one matrix coordinate.
Source: Mathlib finite-matrix algebra equivalences, nonsingular matrix inversion, continuous
  endomorphism resolvents, and Bochner integration under continuous linear maps
Used in: coordinatewise stable-matrix power bounds after a spectral disk estimate encloses every
  eigenvalue of a finite transition or stable-complement matrix
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12/proof/3
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem pow_apply_eq_normalized_circleIntegral_pow_resolvent
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (theta : ℝ) (htheta_pos : 0 < theta)
    (hspectrum_inside : ∀ z : ℂ, z ∈ spectrum ℂ A → ‖z‖ < theta)
    (j : ℕ) (i k : ι) :
    (A ^ j) i k =
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        (∮ z in C((0 : ℂ), theta),
          z ^ j * ((z • (1 : Matrix ι ι ℂ) - A)⁻¹) i k) := by
  classical
  let e := Matrix.toContinuousLinearMapAlgEquiv (K := ℂ) (ι := ι)
  let Aop : Module.End ℂ (ι → ℂ) := Matrix.toLinAlgEquiv' A
  let Op : (ι → ℂ) →L[ℂ] (ι → ℂ) :=
    Module.End.toContinuousLinearMap (ι → ℂ) Aop
  let fromOp : ((ι → ℂ) →L[ℂ] (ι → ℂ)) →L[ℂ] Matrix ι ι ℂ :=
    LinearMap.toContinuousLinearMap e.symm.toLinearMap
  have hspectrum_op : ∀ z : ℂ, z ∈ spectrum ℂ Op → ‖z‖ < theta := by
    intro z hz
    apply hspectrum_inside z
    simpa [Op, Aop, e, Matrix.toContinuousLinearMapAlgEquiv] using hz
  have hop :=
    Module.End.pow_eq_normalized_circleIntegral_pow_resolvent
      Aop theta htheta_pos hspectrum_op j
  have hboundary : ∀ z : ℂ, ‖z‖ = theta → z ∈ resolventSet ℂ Op := by
    intro z hz
    have hnot : z ∉ spectrum ℂ Op := by
      intro hspec
      have hlt := hspectrum_op z hspec
      exact (lt_irrefl theta) (by simpa [hz] using hlt)
    simpa [spectrum] using hnot
  have hresolvent_continuous :
      ContinuousOn (resolvent Op) (Metric.sphere (0 : ℂ) theta) := by
    intro z hz
    have hz_norm : ‖z‖ = theta := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hz
    exact (spectrum.hasDerivAt_resolvent
      (hboundary z hz_norm)).continuousAt.continuousWithinAt
  have hmoment_integrable :
      CircleIntegrable (fun z : ℂ => z ^ j • resolvent Op z) (0 : ℂ) theta :=
    ((continuousOn_pow j).smul hresolvent_continuous).circleIntegrable htheta_pos.le
  have hmap_circle :
      fromOp (∮ z in C((0 : ℂ), theta), z ^ j • resolvent Op z) =
        ∮ z in C((0 : ℂ), theta), fromOp (z ^ j • resolvent Op z) := by
    simp only [circleIntegral]
    rw [← fromOp.intervalIntegral_comp_comm hmoment_integrable.out]
    congr 1
  have hresolvent_matrix : ∀ z : ℂ,
      fromOp (resolvent Op z) = (z • (1 : Matrix ι ι ℂ) - A)⁻¹ := by
    intro z
    apply e.injective
    have hop_sub :
        algebraMap ℂ (((ι → ℂ) →L[ℂ] (ι → ℂ))) z - Op =
          e (algebraMap ℂ (Matrix ι ι ℂ) z - A) := by
      change algebraMap ℂ (((ι → ℂ) →L[ℂ] (ι → ℂ))) z - e A =
        e (algebraMap ℂ (Matrix ι ι ℂ) z - A)
      rw [← e.commutes z]
      exact (map_sub e (algebraMap ℂ (Matrix ι ι ℂ) z) A).symm
    simpa [fromOp, resolvent, Matrix.nonsing_inv_eq_ringInverse,
      Algebra.algebraMap_eq_smul_one, hop_sub] using
      (RingEquiv.map_ringInverse e.toRingEquiv
        (algebraMap ℂ (Matrix ι ι ℂ) z - A)).symm
  have hmatrix :
      A ^ j =
        ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ •
          (∮ z in C((0 : ℂ), theta),
            z ^ j • (z • (1 : Matrix ι ι ℂ) - A)⁻¹) := by
    have hmapped := congrArg fromOp hop
    rw [map_smul, hmap_circle] at hmapped
    have hfrom_pow : fromOp (Op ^ j) = A ^ j := by
      change e.symm (e A ^ j) = A ^ j
      rw [← map_pow]
      simp
    rw [hfrom_pow] at hmapped
    simpa only [map_smul, hresolvent_matrix] using hmapped
  have hmatrix_moment_integrable :
      CircleIntegrable
        (fun z : ℂ => z ^ j • (z • (1 : Matrix ι ι ℂ) - A)⁻¹)
        (0 : ℂ) theta := by
    have hcont : ContinuousOn
        (fun z : ℂ => fromOp (z ^ j • resolvent Op z))
        (Metric.sphere (0 : ℂ) theta) :=
      fromOp.continuous.comp_continuousOn
        ((continuousOn_pow j).smul hresolvent_continuous)
    simpa only [map_smul, hresolvent_matrix] using
      hcont.circleIntegrable htheta_pos.le
  let evalLin : Matrix ι ι ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun M => M i k
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  let eval : Matrix ι ι ℂ →L[ℂ] ℂ :=
    LinearMap.toContinuousLinearMap evalLin
  have hcoord :
      eval (∮ z in C((0 : ℂ), theta),
          z ^ j • (z • (1 : Matrix ι ι ℂ) - A)⁻¹) =
        ∮ z in C((0 : ℂ), theta),
          eval (z ^ j • (z • (1 : Matrix ι ι ℂ) - A)⁻¹) := by
    simp only [circleIntegral]
    rw [← eval.intervalIntegral_comp_comm hmatrix_moment_integrable.out]
    congr 1
  have hentry := congrArg (fun M : Matrix ι ι ℂ => M i k) hmatrix
  change
    (A ^ j) i k =
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        eval (∮ z in C((0 : ℂ), theta),
          z ^ j • (z • (1 : Matrix ι ι ℂ) - A)⁻¹) at hentry
  rw [hcoord] at hentry
  simpa [smul_eq_mul] using hentry

end Matrix

/-! Promoted from Staging/Module_End_uniform_pow_norm_le_of_spectrum_inside_circle_of_resolvent_bound.lean. -/


noncomputable section

open MeasureTheory

-- Generalization plan (G0):
-- concept/name: uniform geometric operator-power bound from a spectral enclosure and a
--   contour-resolvent bound; orig was `stableRemainder_cauchy_power_bound_from_resolvent`
-- generality used: an arbitrary parameter type and finite-dimensional complex normed space;
--   no matrix basis, compact parameter set, inner product, or algorithm setup is needed
-- portable call pattern: parameterized stable linear systems in consensus, Markov-chain, and
--   distributed-optimization analyses vary the operator family, parameter set, contour radius,
--   and resolvent constant while reusing the same uniform geometric power estimate
-- counterargument checked: this is not paper-local traceability or a pure wrapper; it combines
--   the operator Cauchy power formula with a uniform vector-valued contour estimate and removes
--   the source proof's coordinatewise, dimension-dependent norm conversion
-- coverage search: queries "operator power norm bounded geometric resolvent circle spectrum
--   inside" and "norm circle integral bounded radius supremum integrand" found the staged Cauchy
--   power formula and Mathlib's normalized circle-integral estimate separately, but no theorem
--   with the combined uniform family contract
-- minimal hypotheses: positivity of the radius, pointwise spectral enclosure, and the pointwise
--   boundary resolvent bound are exactly what the proof uses; nonnegativity of the bound follows
--   whenever the parameter family is inhabited and is not needed when it is empty

namespace Module.End

/-- Uniform resolvent bounds on a circle enclosing each spectrum give a uniform geometric bound
on every power of a finite-dimensional complex endomorphism family.

Layer: Glue | Gap: Level 2 (uniform Cauchy-resolvent operator-power estimate)
Proof: identify each power with its operator-valued Cauchy resolvent integral, bound the monomial
  resolvent integrand uniformly on the circle, and apply Mathlib's normalized circle-integral norm
  estimate.
Source: Mathlib finite-dimensional continuous endomorphism spectra, Banach-algebra resolvents,
  and `circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const`
Used in: uniform stable-complement power decay for periodic push-pull dynamics and parameterized
  spectral stability estimates for finite-dimensional linear recurrences
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12/proof/3
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem uniform_pow_norm_le_of_spectrum_inside_circle_of_resolvent_bound
    {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V]
    (F : ι → Module.End ℂ V) (theta M : ℝ)
    (htheta_pos : 0 < theta)
    (hspectrum_inside :
      ∀ (a : ι) (z : ℂ),
        z ∈ spectrum ℂ (Module.End.toContinuousLinearMap V (F a)) →
          ‖z‖ < theta)
    (hresolvent_bound :
      ∀ (a : ι) (z : ℂ), ‖z‖ = theta →
        ‖resolvent (Module.End.toContinuousLinearMap V (F a)) z‖ ≤ M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (a : ι) (j : ℕ),
        ‖(Module.End.toContinuousLinearMap V (F a)) ^ j‖ ≤ K * theta ^ j := by
  refine ⟨theta * max M 0, mul_nonneg htheta_pos.le (le_max_right M 0), ?_⟩
  intro a j
  let A : V →L[ℂ] V := Module.End.toContinuousLinearMap V (F a)
  have hM_nonneg : 0 ≤ M := by
    calc
      0 ≤ ‖resolvent A (theta : ℂ)‖ := norm_nonneg _
      _ ≤ M := hresolvent_bound a (theta : ℂ) (by
        simpa [abs_of_pos htheta_pos] using htheta_pos.le)
  rw [max_eq_left hM_nonneg]
  have hformula :=
    Module.End.pow_eq_normalized_circleIntegral_pow_resolvent
      (F a) theta htheta_pos (hspectrum_inside a) j
  rw [hformula]
  calc
    ‖((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ •
        (∮ z in C((0 : ℂ), theta), z ^ j • resolvent A z)‖ ≤
        theta * (theta ^ j * M) := by
      apply circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
        htheta_pos.le
      intro z hz
      have hz_norm : ‖z‖ = theta := by
        simpa [Metric.mem_sphere, dist_eq_norm] using hz
      calc
        ‖z ^ j • resolvent A z‖ = ‖z‖ ^ j * ‖resolvent A z‖ := by
          rw [norm_smul, norm_pow]
        _ ≤ theta ^ j * M := by
          rw [hz_norm]
          exact mul_le_mul_of_nonneg_left (hresolvent_bound a z hz_norm) (pow_nonneg htheta_pos.le j)
    _ = (theta * M) * theta ^ j := by ring

end Module.End

/-! Promoted from Staging/Module_End_exists_uniform_geometric_power_bound_of_analytic_of_spectrum_inside_disk.lean. -/


noncomputable section

open Topology

-- Generalization plan (G0):
-- concept/name: uniform geometric power bound for a continuous finite-dimensional operator
--   family with spectrum in a fixed disk; orig was `uniform_stable_remainder_power_bound`
-- generality used: an arbitrary finite-dimensional complex normed space and a continuous family
--   of continuous complex-linear endomorphisms; no basis, matrix coordinates, inner product, or
--   algorithm setup is used (algebraic `Module.End` has no canonical topology)
-- portable call pattern: continuous perturbations of stable transition, monodromy, and consensus
--   operators vary the family, compact parameter interval, and disk radius while reusing the
--   same compact-resolvent plus Cauchy power estimate
-- counterargument checked: the theorem is not a paper-local rename or one-line wrapper; it
--   supplies the missing compactness step that turns pointwise spectral enclosure into one
--   resolvent constant before invoking the existing uniform Cauchy power theorem
-- coverage search: symbol queries "analytic family finite dimensional operator spectrum strictly
--   inside circle compact interval uniform geometric power bound" and "continuous operator family
--   compact parameter resolvent norm uniformly bounded" found the lower-level staged theorem
--   `Module.End.uniform_pow_norm_le_of_spectrum_inside_circle_of_resolvent_bound`, while Mathlib
--   LeanSearch returned only pointwise Gelfand-formula results and no uniform-family theorem
-- minimal hypotheses: continuity is required only on the closed parameter interval; positivity
--   of the circle radius and pointwise spectral enclosure are otherwise sufficient

namespace Module.End

/-- A continuous finite-dimensional endomorphism family whose spectra lie in a fixed open disk
has one geometric operator-power bound on a compact real interval.

Layer: Glue | Gap: Level 2 (compact analytic-family uniform geometric power estimate)
Proof: continuity of the family and continuity of inversion at units make the resolvent
  continuous on the compact parameter-circle product; compactness supplies one resolvent norm
  bound, and the uniform Cauchy-resolvent power theorem gives the geometric estimate.
Source: Mathlib analytic-map continuity, Banach-algebra unit inversion, compact extrema, and
  finite-dimensional operator spectra, together with the uniform Cauchy-resolvent power bound
Used in: stable-complement power decay in periodic push-pull spectral splittings and analytic
  perturbation bounds for finite-dimensional monodromy or transition-operator families
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12/proof/3
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem exists_uniform_geometric_power_bound_of_continuousOn_of_spectrum_inside_disk
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V]
    (F : ℝ → (V →L[ℂ] V)) (alpha0 theta : ℝ)
    (hFcontinuousOn : ContinuousOn F (Set.Icc (-alpha0) alpha0))
    (htheta_pos : 0 < theta)
    (hspectrum_inside :
      ∀ alpha : ℝ, |alpha| ≤ alpha0 → ∀ z : ℂ,
        z ∈ spectrum ℂ (F alpha) →
          ‖z‖ < theta) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ alpha : ℝ, |alpha| ≤ alpha0 → ∀ j : ℕ,
        ‖(F alpha) ^ j‖ ≤
          K * theta ^ j := by
  let A : ℝ → V →L[ℂ] V := F
  let contour : Set (ℝ × ℂ) :=
    Set.Icc (-alpha0) alpha0 ×ˢ Metric.sphere (0 : ℂ) theta
  have hcompact : IsCompact contour := by
    simpa [contour] using
      (isCompact_Icc.prod (isCompact_sphere (0 : ℂ) theta))
  have hAcontinuousOn : ContinuousOn A (Set.Icc (-alpha0) alpha0) := by
    simpa [A] using hFcontinuousOn
  have hresolvent_continuousOn :
      ContinuousOn (fun p : ℝ × ℂ => resolvent (A p.1) p.2) contour := by
    intro p hp
    have hp_alpha : p.1 ∈ Set.Icc (-alpha0) alpha0 := hp.1
    have hp_circle : p.2 ∈ Metric.sphere (0 : ℂ) theta := hp.2
    have habs : |p.1| ≤ alpha0 := abs_le.mpr hp_alpha
    have hz_norm : ‖p.2‖ = theta := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hp_circle
    have hz_not_mem : p.2 ∉ spectrum ℂ (A p.1) := by
      intro hz
      have hz_lt := hspectrum_inside p.1 habs p.2 (by simpa [A] using hz)
      linarith
    have hunit : IsUnit (algebraMap ℂ (V →L[ℂ] V) p.2 - A p.1) :=
      spectrum.mem_resolventSet_iff.mp (by
        simpa only [spectrum, Set.mem_compl_iff, not_not] using hz_not_mem)
    have hscalar : ContinuousAt
        (fun q : ℝ × ℂ => algebraMap ℂ (V →L[ℂ] V) q.2) p := by
      fun_prop
    have hA : ContinuousWithinAt (fun q : ℝ × ℂ => A q.1) contour p :=
      hAcontinuousOn p.1 hp_alpha |>.comp continuousAt_fst.continuousWithinAt
        (fun _ hq => hq.1)
    have hsub : ContinuousWithinAt
        (fun q : ℝ × ℂ => algebraMap ℂ (V →L[ℂ] V) q.2 - A q.1)
        contour p :=
      hscalar.continuousWithinAt.sub hA
    obtain ⟨u, hu⟩ := hunit
    have hinverse : ContinuousAt Ring.inverse
        (algebraMap ℂ (V →L[ℂ] V) p.2 - A p.1) := by
      rw [← hu]
      exact NormedRing.inverse_continuousAt u
    have hcomp := @ContinuousAt.comp_continuousWithinAt
      (ℝ × ℂ) (V →L[ℂ] V) (V →L[ℂ] V) _ _ _
      (fun q : ℝ × ℂ => algebraMap ℂ (V →L[ℂ] V) q.2 - A q.1)
      contour p Ring.inverse hinverse hsub
    simpa [resolvent, Function.comp_def] using hcomp
  obtain ⟨M, hM⟩ := hcompact.exists_bound_of_continuousOn hresolvent_continuousOn
  let Fc : {alpha : ℝ // |alpha| ≤ alpha0} → Module.End ℂ V :=
    fun alpha => (F alpha).toLinearMap
  obtain ⟨K, hK_nonneg, hK⟩ :=
    Module.End.uniform_pow_norm_le_of_spectrum_inside_circle_of_resolvent_bound
      Fc theta M htheta_pos
      (fun alpha z hz => hspectrum_inside alpha alpha.property z (by
        have heq : Module.End.toContinuousLinearMap V (F alpha).toLinearMap =
            F alpha := rfl
        rw [heq] at hz
        exact hz))
      (fun alpha z hz => hM (alpha, z) (by
        refine ⟨?_, ?_⟩
        · exact (abs_le.mp alpha.property)
        · simpa [Metric.mem_sphere, dist_eq_norm] using hz))
  exact ⟨K, hK_nonneg, fun alpha halpha j => by
    simpa [Fc] using hK ⟨alpha, halpha⟩ j⟩

end Module.End
