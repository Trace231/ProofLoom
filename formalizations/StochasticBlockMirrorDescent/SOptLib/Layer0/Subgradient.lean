import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Seminorm
import Mathlib.Topology.MetricSpace.Basic
import SOptLib.Glue.Analysis
import SOptLib.Model.Subdifferential

open scoped BigOperators InnerProductSpace

namespace SOptLib

/-- Two one-sided bounded subgradient inequalities imply an absolute Lipschitz bound.

If `g x` and `g y` are supporting subgradients at two carrier points and both
subgradients have norm at most `M`, then the objective values differ by at most
`M` times the distance between the evaluated points.

Layer: Layer0 | Gap: Level 1 (subgradient Lipschitz bound)
Proof: rearrange the two support inequalities into upper bounds for
  `f x - f y` and `f y - f x`, control each inner product with
  `real_inner_le_norm`, and combine the two one-sided estimates using `abs_le`.
Source: Mathlib inner product norm inequalities and real absolute-value order APIs
Used in: stochastic mirror descent Lipschitz control from uniformly bounded subgradients
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic mirror descent -/
theorem abs_sub_le_of_subgradient_norm_bound
    {P E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : P → ℝ) (eval : P → E) (g : P → E) (M : ℝ) {x y : P}
    (hx_support : f x + ⟪g x, eval y - eval x⟫_ℝ ≤ f y)
    (hy_support : f y + ⟪g y, eval x - eval y⟫_ℝ ≤ f x)
    (hx_norm : ‖g x‖ ≤ M) (hy_norm : ‖g y‖ ≤ M) :
    ‖f x - f y‖ ≤ M * ‖eval x - eval y‖ := by
  have hxy :
      f x - f y ≤ M * ‖eval x - eval y‖ := by
    have hdiff :
        f x - f y ≤ ⟪g x, eval x - eval y⟫_ℝ := by
      calc
        f x - f y ≤ -⟪g x, eval y - eval x⟫_ℝ := by linarith
        _ = ⟪g x, eval x - eval y⟫_ℝ := by
          have hsub : eval x - eval y = -(eval y - eval x) := by
            abel
          rw [hsub, inner_neg_right]
    have hinner :
        ⟪g x, eval x - eval y⟫_ℝ ≤ ‖g x‖ * ‖eval x - eval y‖ :=
      real_inner_le_norm _ _
    have hM :
        ‖g x‖ * ‖eval x - eval y‖ ≤ M * ‖eval x - eval y‖ :=
      mul_le_mul_of_nonneg_right hx_norm (norm_nonneg _)
    exact hdiff.trans (hinner.trans hM)
  have hyx :
      f y - f x ≤ M * ‖eval x - eval y‖ := by
    have hdiff :
        f y - f x ≤ ⟪g y, eval y - eval x⟫_ℝ := by
      calc
        f y - f x ≤ -⟪g y, eval x - eval y⟫_ℝ := by linarith
        _ = ⟪g y, eval y - eval x⟫_ℝ := by
          have hsub : eval y - eval x = -(eval x - eval y) := by
            abel
          rw [hsub, inner_neg_right]
    have hinner :
        ⟪g y, eval y - eval x⟫_ℝ ≤ ‖g y‖ * ‖eval y - eval x‖ :=
      real_inner_le_norm _ _
    have hM :
        ‖g y‖ * ‖eval y - eval x‖ ≤ M * ‖eval y - eval x‖ :=
      mul_le_mul_of_nonneg_right hy_norm (norm_nonneg _)
    have hbound : f y - f x ≤ M * ‖eval y - eval x‖ :=
      hdiff.trans (hinner.trans hM)
    simpa [norm_sub_rev] using hbound
  have hneg : -(M * ‖eval x - eval y‖) ≤ f x - f y := by
    linarith
  simpa [Real.norm_eq_abs] using abs_le.mpr ⟨hneg, hxy⟩

/-- Bounded carrier subgradients make the objective Lipschitz along evaluation.

If every carrier point has a supporting subgradient with norm at most `M`, then
the objective values differ by at most `M` times the distance between evaluated
carrier points.

Layer: Layer0 | Gap: Level 1 (bounded subgradients imply Lipschitz on carrier)
Proof: apply the two supporting-subgradient inequalities in opposite directions
  and combine them with the uniform norm bound via the inner-product Cauchy
  Schwarz estimate packaged in `abs_sub_le_of_subgradient_norm_bound`.
Source: Mathlib inner product norm inequalities and real absolute-value order APIs
Used in: stochastic mirror descent Lipschitz control from bounded mean-oracle subgradients
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem lipschitzOn_of_forall_subgradient_norm_le
    {P E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : P → ℝ) (eval : P → E) (g : P → E) (M : ℝ)
    (h_subgradient : ∀ x y : P, f x + ⟪g x, eval y - eval x⟫_ℝ ≤ f y)
    (h_norm : ∀ x : P, ‖g x‖ ≤ M) :
    ∀ x y : P, ‖f x - f y‖ ≤ M * ‖eval x - eval y‖ := by
  intro x y
  exact abs_sub_le_of_subgradient_norm_bound f eval g M
    (h_subgradient x y) (h_subgradient y x) (h_norm x) (h_norm y)

/-- A pointwise mean-oracle subgradient hypothesis specializes to one carrier point.

If the mean oracle `g` belongs to the carrier subdifferential of `f` at every
carrier point, then it belongs to that carrier subdifferential at the chosen
carrier point `x`.

Layer: Layer0 | Gap: Level 0 (mean-oracle carrier subgradient specialization)
Proof: specialize the pointwise carrier-subdifferential assumption at `x`.
  The proof is direct implication elimination.
Source: Mathlib subtype and set membership APIs
Used in: stochastic mirror descent unbiased oracle carrier-subgradient check
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem meanOracle_mem_carrierSubdifferential
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X : Set E) (f : {x : E // x ∈ X} → ℝ) (g : {x : E // x ∈ X} → E)
    (h_meanOracle_subgradient : ∀ x : {x : E // x ∈ X},
      g x ∈ SOptLib.carrierSubdifferential f x) (x : {x : E // x ∈ X}) :
    g x ∈ SOptLib.carrierSubdifferential f x := by
  exact h_meanOracle_subgradient x

end SOptLib

/-- Root-namespace compatibility wrapper for carrier-subdifferential
membership transport.

Mirrors `SOptLib.meanOracle_mem_carrierSubdifferential` at the root
namespace so legacy callsites that look up the lemma without the `SOptLib`
prefix still resolve.

Layer: Layer0 | Gap: Level 0 (root-namespace alias for mean-oracle
  carrier-subgradient specialization)
Proof: direct delegation to `SOptLib.meanOracle_mem_carrierSubdifferential`.
Source: Mathlib subtype and set membership APIs
Used in: stochastic mirror descent unbiased oracle carrier-subgradient check
  (root-namespace callsites)
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem meanOracle_mem_carrierSubdifferential
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X : Set E) (f : {x : E // x ∈ X} → ℝ) (g : {x : E // x ∈ X} → E)
    (h_meanOracle_subgradient : ∀ x : {x : E // x ∈ X},
      g x ∈ SOptLib.carrierSubdifferential f x) (x : {x : E // x ∈ X}) :
    g x ∈ SOptLib.carrierSubdifferential f x := by
  exact SOptLib.meanOracle_mem_carrierSubdifferential X f g h_meanOracle_subgradient x

/-- Two-sided supporting inequalities plus an absolute pairing bound make a
real objective measurable.

If `g x` supports the real objective `f` at every carrier point and each
support pairing against a displacement is bounded by `C * dist x y`, then `f`
is Lipschitz, hence measurable.

Layer: Layer0 | Gap: Level 1 (supporting inequality to measurable objective)
Proof: rearrange the two support inequalities into opposite one-sided bounds
  for `f x - f y`, control both by the absolute pairing estimate, package the
  resulting norm-difference estimate as a Lipschitz map, then use Lipschitz
  measurability.
Source: Mathlib real inner-product support inequalities, ordered real absolute
  values, and metric Lipschitz measurability APIs
Used in: stochastic block mirror descent feasible-objective measurability from
  block-dual bounded mean subgradients
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem measurable_of_supporting_inequality_and_abs_inner_bound
    {P E : Type*} [PseudoMetricSpace P] [MeasurableSpace P] [OpensMeasurableSpace P]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : P → ℝ) (g : P → E) (eval : P → E) (C : ℝ)
    (hsupport : ∀ x y : P, f x + ⟪g x, eval y - eval x⟫_ℝ ≤ f y)
    (hinner : ∀ x y : P, |⟪g x, eval y - eval x⟫_ℝ| ≤ C * dist x y) :
    Measurable f := by
  have hdiff :
      ∀ x y : P, ‖f x - f y‖ ≤ C * dist x y := by
    intro x y
    have hxy_support := hsupport x y
    have hyx_support := hsupport y x
    have hxy :
        f x - f y ≤ C * dist x y := by
      have hgap :
          f x - f y ≤ -⟪g x, eval y - eval x⟫_ℝ := by
        linarith
      exact hgap.trans ((neg_le_abs _).trans (hinner x y))
    have hyx :
        f y - f x ≤ C * dist x y := by
      have hgap :
          f y - f x ≤ -⟪g y, eval x - eval y⟫_ℝ := by
        linarith
      exact hgap.trans ((neg_le_abs _).trans (by simpa [dist_comm] using hinner y x))
    have hneg : -(C * dist x y) ≤ f x - f y := by
      linarith
    simpa [Real.norm_eq_abs] using abs_le.mpr ⟨hneg, hxy⟩
  exact (lipschitzWith_of_norm_sub_le_mul f C hdiff).measurable

/-- Block-dual bounds control the absolute ambient pairing by carrier distance.

If an ambient vector field is reconstructed from finitely many lifted block
components, each block component satisfies a dual-support bound, and each block
primal seminorm is controlled by the ambient norm after a coordinate map, then
the ambient inner product against any carrier displacement is Lipschitz in the
carrier distance.

Layer: Layer0 | Gap: Level 1 (finite block-dual displacement support bound)
Proof: expand the ambient pairing through the finite block reconstruction,
apply the triangle inequality over the finite sum, bound each block term by
the dual-support and coordinate operator-norm estimates, then compare the
ambient displacement norm to the carrier distance.
Source: Mathlib finite sums, real Hilbert inner products, seminorms, and
  continuous-linear-map operator norm APIs
Used in: stochastic block mirror descent feasible-objective measurability from
  block-dual bounded mean subgradients
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem abs_inner_le_dist_of_block_dual_bounds
    {I P E : Type*} [Fintype I] [PseudoMetricSpace P]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {B : I → Type*} [∀ i, NormedAddCommGroup (B i)]
    [∀ i, InnerProductSpace ℝ (B i)]
    (eval : P → E) (coord : ∀ i, E →L[ℝ] B i) (lift : ∀ i, B i → E)
    (g : P → E) (gBlock : ∀ i, P → B i)
    (p : ∀ i, Seminorm ℝ (B i)) (dual : I → P → ℝ) (M : I → ℝ)
    (hM_nonneg : ∀ i, 0 ≤ M i)
    (hK_exists : ∀ i, ∃ K : ℝ, 0 ≤ K ∧ ∀ d : B i, p i d ≤ K * ‖d‖)
    (hrepr : ∀ x, g x = Finset.sum Finset.univ (fun i => lift i (gBlock i x)))
    (hpair : ∀ i ζ d, ⟪lift i ζ, d⟫_ℝ = ⟪ζ, coord i d⟫_ℝ)
    (hsupport : ∀ i x d, |⟪gBlock i x, coord i d⟫_ℝ| ≤
      dual i x * p i (coord i d))
    (hdual_le : ∀ i x, dual i x ≤ M i)
    (hdist : ∀ x y, ‖eval y - eval x‖ ≤ dist x y) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x y : P, |⟪g x, eval y - eval x⟫_ℝ| ≤ C * dist x y := by
  classical
  choose K hK_nonneg hK_bound using hK_exists
  let C : ℝ := Finset.sum Finset.univ (fun i => M i * K i * ‖coord i‖)
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    refine Finset.sum_nonneg ?_
    intro i _hi
    exact mul_nonneg (mul_nonneg (hM_nonneg i) (hK_nonneg i)) (norm_nonneg _)
  refine ⟨C, hC_nonneg, ?_⟩
  intro x y
  let d : E := eval y - eval x
  have hsum :
      |⟪g x, d⟫_ℝ| ≤
        Finset.sum Finset.univ (fun i => (M i * K i * ‖coord i‖) * ‖d‖) := by
    calc
      |⟪g x, d⟫_ℝ|
          = |Finset.sum Finset.univ (fun i => ⟪lift i (gBlock i x), d⟫_ℝ)| := by
              rw [hrepr x, sum_inner]
      _ ≤ Finset.sum Finset.univ (fun i => |⟪lift i (gBlock i x), d⟫_ℝ|) := by
              simpa using
                (Finset.abs_sum_le_sum_abs
                  (fun i => ⟪lift i (gBlock i x), d⟫_ℝ) Finset.univ)
      _ ≤ Finset.sum Finset.univ (fun i => (M i * K i * ‖coord i‖) * ‖d‖) := by
              refine Finset.sum_le_sum ?_
              intro i _hi
              have hcoord : ‖coord i d‖ ≤ ‖coord i‖ * ‖d‖ :=
                (coord i).le_opNorm d
              have hprimal :
                  p i (coord i d) ≤ (K i * ‖coord i‖) * ‖d‖ := by
                calc
                  p i (coord i d) ≤ K i * ‖coord i d‖ := hK_bound i (coord i d)
                  _ ≤ K i * (‖coord i‖ * ‖d‖) :=
                    mul_le_mul_of_nonneg_left hcoord (hK_nonneg i)
                  _ = (K i * ‖coord i‖) * ‖d‖ := by ring
              have hdual_mul :
                  dual i x * p i (coord i d) ≤ M i * p i (coord i d) :=
                mul_le_mul_of_nonneg_right (hdual_le i x) (apply_nonneg (p i) (coord i d))
              have hprimal_mul :
                  M i * p i (coord i d) ≤
                    M i * ((K i * ‖coord i‖) * ‖d‖) :=
                mul_le_mul_of_nonneg_left hprimal (hM_nonneg i)
              calc
                |⟪lift i (gBlock i x), d⟫_ℝ|
                    = |⟪gBlock i x, coord i d⟫_ℝ| := by rw [hpair]
                _ ≤ dual i x * p i (coord i d) := hsupport i x d
                _ ≤ M i * p i (coord i d) := hdual_mul
                _ ≤ M i * ((K i * ‖coord i‖) * ‖d‖) := hprimal_mul
                _ = (M i * K i * ‖coord i‖) * ‖d‖ := by ring
  have hsum_const :
      Finset.sum Finset.univ (fun i => (M i * K i * ‖coord i‖) * ‖d‖) =
        (Finset.sum Finset.univ (fun i => M i * K i * ‖coord i‖)) * ‖d‖ := by
    simp [Finset.sum_mul]
  have hCx_nonneg : 0 ≤ Finset.sum Finset.univ (fun i => M i * K i * ‖coord i‖) := by
    refine Finset.sum_nonneg ?_
    intro i _hi
    exact mul_nonneg (mul_nonneg (hM_nonneg i) (hK_nonneg i)) (norm_nonneg _)
  calc
    |⟪g x, eval y - eval x⟫_ℝ| = |⟪g x, d⟫_ℝ| := by rfl
    _ ≤ Finset.sum Finset.univ (fun i => (M i * K i * ‖coord i‖) * ‖d‖) := hsum
    _ = (Finset.sum Finset.univ (fun i => M i * K i * ‖coord i‖)) * ‖d‖ := hsum_const
    _ ≤ (Finset.sum Finset.univ (fun i => M i * K i * ‖coord i‖)) * dist x y :=
      mul_le_mul_of_nonneg_left (hdist x y) hCx_nonneg
    _ ≤ C * dist x y := by
      have hleC :
          Finset.sum Finset.univ (fun i => M i * K i * ‖coord i‖) ≤ C := by
        rfl
      exact mul_le_mul_of_nonneg_right hleC (dist_nonneg)

/-- A block-decomposed vector has its absolute ambient pairing bounded by
the sum of block dual bounds times block radii.

If an ambient vector is reconstructed from finitely many lifted block
components, the lifts pair with ambient displacements through block coordinates,
and each block pairing is controlled by a dual bound and a radius, then the
ambient pairing is controlled by the finite sum of the majorizing products.

Layer: Layer0 | Gap: Level 1 (finite block-dual radius inner-product bound)
Proof: expand the ambient pairing through the finite block reconstruction,
apply the triangle inequality over the finite sum, transport each summand to
the block pairing, and use monotonicity of multiplication with nonnegative
block radii and dual majorants.
Source: Mathlib finite sums, real Hilbert inner products, absolute-value order,
  and ordered-ring product inequalities
Used in: stochastic block mirror descent deterministic mean-oracle displacement
  control before scalar oracle-noise domination
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem abs_inner_block_sum_le_sum_dual_bound_mul_radius
    {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {B : ι → Type*} [∀ i, NormedAddCommGroup (B i)]
    [∀ i, InnerProductSpace ℝ (B i)]
    (lift : ∀ i, B i → E) (coord : ∀ i, E → B i)
    (g : E) (gBlock : ∀ i, B i) (d : E)
    (dual radius M R : ι → ℝ)
    (hrepr : g = Finset.sum Finset.univ (fun i => lift i (gBlock i)))
    (hpair : ∀ i (ζ : B i) (v : E), ⟪lift i ζ, v⟫_ℝ = ⟪ζ, coord i v⟫_ℝ)
    (hsupport : ∀ i, |⟪gBlock i, coord i d⟫_ℝ| ≤ dual i * radius i)
    (hdual_le : ∀ i, dual i ≤ M i)
    (hradius_nonneg : ∀ i, 0 ≤ radius i)
    (hradius_le : ∀ i, radius i ≤ R i)
    (hM_nonneg : ∀ i, 0 ≤ M i) :
    |⟪g, d⟫_ℝ| ≤ Finset.sum Finset.univ (fun i => M i * R i) := by
  calc
    |⟪g, d⟫_ℝ|
        = |Finset.sum Finset.univ (fun i => ⟪lift i (gBlock i), d⟫_ℝ)| := by
            rw [hrepr, sum_inner]
    _ ≤ Finset.sum Finset.univ (fun i => |⟪lift i (gBlock i), d⟫_ℝ|) := by
            simpa using
              (Finset.abs_sum_le_sum_abs
                (fun i => ⟪lift i (gBlock i), d⟫_ℝ) Finset.univ)
    _ ≤ Finset.sum Finset.univ (fun i => M i * R i) := by
            refine Finset.sum_le_sum ?_
            intro i _hi
            have hmajor : dual i * radius i ≤ M i * R i :=
              mul_le_mul (hdual_le i) (hradius_le i) (hradius_nonneg i) (hM_nonneg i)
            calc
              |⟪lift i (gBlock i), d⟫_ℝ| = |⟪gBlock i, coord i d⟫_ℝ| := by
                rw [hpair]
              _ ≤ dual i * radius i := hsupport i
              _ ≤ M i * R i := hmajor
