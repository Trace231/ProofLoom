import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Seminorm
import Mathlib.Data.Real.Archimedean
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

open MeasureTheory
open scoped BigOperators ENNReal InnerProductSpace MatrixOrder

namespace Seminorm

/-- A seminorm separates points when its zero set is exactly `{0}`.

This is the nondegeneracy condition that upgrades a seminorm-shaped datum into
a genuine norm-like object while still keeping the datum as a bundled
`Seminorm`.

Layer: Model | Concept: Norm
Proof: (definitional construction; trivial-kernel predicate for a bundled seminorm)
Source: Mathlib seminorm API and locally convex separating-seminorm terminology
Used in: stochastic block mirror descent block primal norm nondegeneracy
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic block mirror descent -/
def IsSeparating {𝕜 E : Type*} [SeminormedRing 𝕜] [AddGroup E] [SMul 𝕜 E]
    (p : Seminorm 𝕜 E) : Prop :=
  ∀ x, p x = 0 ↔ x = 0

end Seminorm

namespace SOptLib

/-- In a finite dependent Hilbert product, pairing with a single-coordinate
insertion reads the same coordinate of the ambient vector.

This is the finite `PiLp` analogue of the `lp.inner_single_right` support
calculation: all coordinates except the inserted one vanish in the product
inner-product sum.

Layer: Model | Gap: Level 0 (finite PiLp single-coordinate inner pairing)
Proof: expand the finite product inner product with `PiLp.inner_apply`, then
  collapse the finite sum to the inserted coordinate using `Finset.sum_eq_single`
  and the support API for `PiLp.single`.
Source: Mathlib finite `PiLp` inner-product and single-coordinate insertion APIs
Used in: stochastic block mirror descent conversion between block oracle
  pairings and ambient product-space pairings
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem piLp_inner_coord_single
    {𝕜 : Type*} [RCLike 𝕜]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Block : ι → Type*} [∀ i, NormedAddCommGroup (Block i)]
    [∀ i, InnerProductSpace 𝕜 (Block i)]
    (i : ι) (v : PiLp 2 Block) (u : Block i) :
    ⟪v i, u⟫_𝕜 = ⟪v, PiLp.single 2 i u⟫_𝕜 := by
  rw [PiLp.inner_apply (x := v) (y := PiLp.single 2 i u)]
  symm
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Pi.single_eq_of_ne hji]
  · intro hi
    simp at hi

/-- A finite sum of all single-coordinate insertions of a `PiLp` point
reconstructs the point.

For a finite dependent `PiLp` product, inserting each coordinate of `v` with
`PiLp.single` and summing over all indices gives back `v`.

Layer: Model | Gap: Level 0 (finite PiLp single-coordinate reconstruction)
Proof: use finite product extensionality and reduce each coordinate to the
  unique surviving `PiLp.single` term in the finite sum.
Source: Mathlib finite dependent products, `PiLp.single`, and finite
  big-operator coordinate APIs
Used in: stochastic block mirror descent reconstruction of an ambient gradient
  from lifted block coordinates
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem finset_sum_piLp_single_apply_self
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Block : ι → Type*} [∀ i, NormedAddCommGroup (Block i)]
    {p : ℝ≥0∞} (v : PiLp p Block) :
    Finset.sum Finset.univ (fun i => PiLp.single p i (v i)) = v := by
  ext j
  simp

/-- The canonical dual norm associated with a primal seminorm is the support
function of the primal unit ball under the real inner product pairing.

Layer: Model | Concept: Norm
Proof: (definitional construction; support function over the seminorm unit ball)
Source: Functional analysis dual norms and support functions of unit balls
Used in: stochastic block mirror descent block oracle dual norms derived from primal norms
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine
  Learning, stochastic block mirror descent -/
noncomputable def canonicalDualNorm
    {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℝ B]
    (p : Seminorm ℝ B) (zeta : B) : ℝ :=
  sSup {r : ℝ | ∃ d : B, p d ≤ 1 ∧ r = |inner ℝ zeta d|}

/-- The defining support-function formula for the canonical dual norm associated
with a primal seminorm.

Layer: Model | Gap: Level 0 (canonical dual norm formula)
Proof: by rfl after unfolding canonicalDualNorm
Source: Functional analysis dual norms and support functions of unit balls
Used in: stochastic block mirror descent block oracle dual norms derived from primal norms
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine
  Learning, stochastic block mirror descent -/
@[simp]
theorem canonicalDualNorm_eq_sSup
    {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℝ B]
    (p : Seminorm ℝ B) (zeta : B) :
    canonicalDualNorm p zeta =
      sSup {r : ℝ | ∃ d : B, p d ≤ 1 ∧ r = |inner ℝ zeta d|} := rfl

/-- A primal-unit vector is bounded by the canonical dual support value.

For a canonical dual norm defined as the supremum of absolute inner products
over the primal seminorm unit ball, every particular unit-ball vector gives a
support value below that supremum whenever the support set is bounded above.

Layer: Model | Gap: Level 0 (canonical dual norm unit-ball support bound)
Proof: unfold the canonical dual norm to its `sSup` formula, insert the primal
  unit vector as a support-set witness, and apply `le_csSup`.
Source: Functional analysis dual norms, support functions of unit balls, and
  conditionally complete lattice supremum APIs
Used in: stochastic block mirror descent support-function subadditivity for
  block dual norms
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem abs_inner_le_canonicalDualNorm_of_primal_le_one
    {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℝ B]
    (p : Seminorm ℝ B) {zeta u : B}
    (h_bdd : BddAbove {r : ℝ | ∃ d : B, p d ≤ 1 ∧ r = |inner ℝ zeta d|})
    (hu : p u ≤ 1) :
    |inner ℝ zeta u| ≤ canonicalDualNorm p zeta := by
  rw [canonicalDualNorm_eq_sSup]
  exact le_csSup h_bdd ⟨u, hu, rfl⟩

/-- The canonical dual norm bounds every inner product by dual norm times
the primal seminorm.

For a separating primal seminorm, the usual duality inequality follows from the
unit-ball support formula: nonzero vectors are rescaled into the primal unit
ball, while zero-seminorm vectors vanish by separation.

Layer: Model | Gap: Level 1 (canonical primal-dual support inequality)
Proof: split on whether the primal seminorm of `d` is zero; in the nonzero
  case rescale `d` into the primal unit ball, apply the unit-ball support
  bound, and multiply back by the positive seminorm value.
Source: Functional analysis dual norms, support functions of unit balls, and
  ordered-field scaling
Used in: stochastic block mirror descent block oracle inner-product estimates
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem abs_inner_le_canonicalDualNorm_mul
    {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℝ B]
    (p : Seminorm ℝ B) (hp : p.IsSeparating) {zeta d : B}
    (h_bdd : BddAbove {r : ℝ | ∃ u : B, p u ≤ 1 ∧ r = |inner ℝ zeta u|}) :
    |inner ℝ zeta d| ≤ canonicalDualNorm p zeta * p d := by
  classical
  by_cases hd0 : p d = 0
  · have hd : d = 0 := (hp d).mp hd0
    simp [hd]
  · have hpd_nonneg : 0 ≤ p d := apply_nonneg p d
    have hpd_pos : 0 < p d := lt_of_le_of_ne hpd_nonneg (Ne.symm hd0)
    let u : B := (p d)⁻¹ • d
    have hu_le : p u ≤ 1 := by
      simp [u, map_smul_eq_mul, abs_of_pos hpd_pos, hpd_pos.ne']
    have hsup : |inner ℝ zeta u| ≤ canonicalDualNorm p zeta :=
      abs_inner_le_canonicalDualNorm_of_primal_le_one
        (p := p) (zeta := zeta) (u := u) h_bdd hu_le
    have hscale : |inner ℝ zeta u| = (p d)⁻¹ * |inner ℝ zeta d| := by
      simp [u, inner_smul_right, abs_mul, abs_of_pos (inv_pos.mpr hpd_pos)]
    have hinv_le :
        (p d)⁻¹ * |inner ℝ zeta d| ≤ canonicalDualNorm p zeta := by
      simpa [hscale] using hsup
    calc
      |inner ℝ zeta d| = ((p d)⁻¹ * |inner ℝ zeta d|) * p d := by
        field_simp [hpd_pos.ne']
      _ ≤ canonicalDualNorm p zeta * p d :=
        mul_le_mul_of_nonneg_right hinv_le hpd_pos.le

/-- The support set defining a canonical dual seminorm is bounded above when
the primal seminorm unit ball is ambient-bounded.

If every vector in the primal seminorm unit ball has ambient norm at most `C`,
then Cauchy-Schwarz uniformly bounds the absolute inner-product support values
by `‖ζ‖ * C`.

Layer: Model | Gap: Level 1 (canonical dual support-set boundedness)
Proof: unpack support-set membership, apply the localized primal-unit-ball
  bound, then combine it with the real Hilbert-space Cauchy-Schwarz inequality.
Source: Functional analysis dual norms, support functions of unit balls, and
  Hilbert-space Cauchy-Schwarz inequalities
Used in: stochastic block mirror descent block oracle dual norms derived from
  finite-dimensional primal block norms
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine
  Learning, stochastic block mirror descent -/
theorem canonicalDualNorm_supportSet_bddAbove
    {B : Type*} [SeminormedAddCommGroup B] [InnerProductSpace ℝ B]
    (p : Seminorm ℝ B) (zeta : B)
    (hcontrol : ∃ C : ℝ, ∀ x : B, p x ≤ 1 -> ‖x‖ ≤ C) :
    BddAbove {r : ℝ | ∃ u : B, p u ≤ 1 ∧ r = |inner ℝ zeta u|} := by
  rcases hcontrol with ⟨C, hC⟩
  refine ⟨‖zeta‖ * C, ?_⟩
  intro r hr
  rcases hr with ⟨u, hpu, rfl⟩
  have hinner : |inner ℝ zeta u| ≤ ‖zeta‖ * ‖u‖ := by
    simpa using (norm_inner_le_norm (𝕜 := ℝ) zeta u)
  have hu_norm : ‖u‖ ≤ C := hC u hpu
  exact hinner.trans (mul_le_mul_of_nonneg_left hu_norm (norm_nonneg zeta))

/-- A canonical dual norm induced by a primal seminorm is bounded by the
ambient norm times any primal-to-ambient control constant.

If every vector in the primal seminorm unit ball has ambient norm at most `C`,
then the support function of the primal unit ball is at most `C * ‖ζ‖`.

Layer: Model | Gap: Level 1 (canonical dual norm ambient control)
Proof: unfold the canonical dual norm as a supremum over the primal unit ball,
  bound each support value by Cauchy-Schwarz, and use the control hypothesis to
  bound every primal-unit vector by `C`.
Source: Functional analysis dual norms, support functions of unit balls, and
  Hilbert-space Cauchy-Schwarz inequalities
Used in: stochastic block mirror descent block oracle measurability and L2 bounds
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine
  Learning, stochastic block mirror descent -/
theorem canonicalDualNorm_le_norm_mul_control
    {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℝ B]
    (p : Seminorm ℝ B) {C : ℝ}
    (hC : ∀ x : B, p x ≤ 1 -> ‖x‖ ≤ C) (zeta : B) :
    canonicalDualNorm p zeta ≤ ‖zeta‖ * C := by
  classical
  let A : Set ℝ := {r : ℝ | ∃ u : B, p u ≤ 1 ∧ r = |inner ℝ zeta u|}
  have hA_nonempty : A.Nonempty := by
    refine ⟨0, ?_⟩
    refine ⟨0, ?_, ?_⟩
    · simp
    · simp
  rw [canonicalDualNorm_eq_sSup]
  refine csSup_le hA_nonempty ?_
  intro r hr
  rcases hr with ⟨u, hpu, rfl⟩
  have hinner : |inner ℝ zeta u| ≤ ‖zeta‖ * ‖u‖ := by
    simpa using (norm_inner_le_norm (𝕜 := ℝ) zeta u)
  have hu_norm : ‖u‖ ≤ C := hC u hpu
  exact hinner.trans (mul_le_mul_of_nonneg_left hu_norm (norm_nonneg zeta))

/-- The canonical dual norm induced by a primal seminorm is subadditive.

For a support-function dual norm over the primal seminorm unit ball, every
support value of `zeta + eta` is bounded by the sum of the corresponding
support values of `zeta` and `eta`, hence by the two canonical dual norms.

Layer: Model | Gap: Level 1 (canonical dual norm subadditivity)
Proof: unfold the left-hand canonical dual norm as a supremum over the primal
  unit ball, bound each support value by the absolute-value triangle
  inequality, and compare the two summands to their support suprema.
Source: Functional analysis dual norms, support functions of unit balls, and
  Mathlib order-theoretic supremum APIs
Used in: stochastic block mirror descent Lipschitz control for block dual norms
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem canonicalDualNorm_add_le
    {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℝ B]
    (p : Seminorm ℝ B) (zeta eta : B)
    (h_zeta_bdd :
      BddAbove {r : ℝ | ∃ u : B, p u ≤ 1 ∧ r = |inner ℝ zeta u|})
    (h_eta_bdd :
      BddAbove {r : ℝ | ∃ u : B, p u ≤ 1 ∧ r = |inner ℝ eta u|}) :
    canonicalDualNorm p (zeta + eta) ≤
      canonicalDualNorm p zeta + canonicalDualNorm p eta := by
  classical
  let A : Set ℝ := {r : ℝ | ∃ u : B, p u ≤ 1 ∧ r = |inner ℝ (zeta + eta) u|}
  have hA_nonempty : A.Nonempty := by
    refine ⟨0, ?_⟩
    refine ⟨0, ?_, ?_⟩
    · simp
    · simp
  rw [canonicalDualNorm_eq_sSup]
  change sSup A ≤ canonicalDualNorm p zeta + canonicalDualNorm p eta
  refine csSup_le hA_nonempty ?_
  intro r hr
  rcases hr with ⟨u, hpu, rfl⟩
  have hzeta_le : |inner ℝ zeta u| ≤ canonicalDualNorm p zeta :=
    abs_inner_le_canonicalDualNorm_of_primal_le_one
      (p := p) (zeta := zeta) (u := u) h_zeta_bdd hpu
  have heta_le : |inner ℝ eta u| ≤ canonicalDualNorm p eta :=
    abs_inner_le_canonicalDualNorm_of_primal_le_one
      (p := p) (zeta := eta) (u := u) h_eta_bdd hpu
  have htri :
      |inner ℝ (zeta + eta) u| ≤ |inner ℝ zeta u| + |inner ℝ eta u| := by
    simpa [inner_add_left] using abs_add_le (inner ℝ zeta u) (inner ℝ eta u)
  linarith

/-- The canonical dual norm induced by a primal seminorm is Lipschitz under
ambient control of the primal unit ball.

If every vector in the primal seminorm unit ball has ambient norm at most `C`,
then changing the dual argument from `eta` to `zeta` changes the induced support
function by at most `C * ‖zeta - eta‖`.

Layer: Model | Gap: Level 1 (canonical dual norm Lipschitz control)
Proof: use support-function subadditivity in both directions, bound the
  difference term by the ambient-control lemma, and finish with
  `abs_sub_le_iff`.
Source: Functional analysis dual norms, support functions of unit balls, and
  normed-space triangle estimates
Used in: stochastic block mirror descent continuity of block dual norms
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem canonicalDualNorm_lipschitz_control
    {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℝ B]
    (p : Seminorm ℝ B) {C : ℝ}
    (hC : ∀ x : B, p x ≤ 1 -> ‖x‖ ≤ C) (zeta eta : B) :
    |canonicalDualNorm p zeta - canonicalDualNorm p eta| ≤
      C * ‖zeta - eta‖ := by
  classical
  have hbdd : ∀ xi : B,
      BddAbove {r : ℝ | ∃ u : B, p u ≤ 1 ∧ r = |inner ℝ xi u|} := by
    intro xi
    exact canonicalDualNorm_supportSet_bddAbove
      (p := p) (zeta := xi) ⟨C, hC⟩
  have hupper : ∀ xi : B,
      canonicalDualNorm p xi ≤ C * ‖xi‖ := by
    intro xi
    have h := canonicalDualNorm_le_norm_mul_control (p := p) (C := C) hC xi
    linarith
  have hζ_le :
      canonicalDualNorm p zeta ≤
        canonicalDualNorm p eta + C * ‖zeta - eta‖ := by
    have hsub := canonicalDualNorm_add_le
      (p := p) (zeta := eta) (eta := zeta - eta)
      (hbdd eta) (hbdd (zeta - eta))
    have hsum : eta + (zeta - eta) = zeta := by abel
    rw [hsum] at hsub
    have hdiff := hupper (zeta - eta)
    linarith
  have hη_le :
      canonicalDualNorm p eta ≤
        canonicalDualNorm p zeta + C * ‖zeta - eta‖ := by
    have hsub := canonicalDualNorm_add_le
      (p := p) (zeta := zeta) (eta := eta - zeta)
      (hbdd zeta) (hbdd (eta - zeta))
    have hsum : zeta + (eta - zeta) = eta := by abel
    rw [hsum] at hsub
    have hdiff := hupper (eta - zeta)
    have hnorm : ‖eta - zeta‖ = ‖zeta - eta‖ := by rw [norm_sub_rev]
    have hdiff' : canonicalDualNorm p (eta - zeta) ≤ C * ‖zeta - eta‖ := by
      simpa [hnorm] using hdiff
    linarith
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- The canonical dual norm induced by a primal seminorm is continuous under
ambient control of the primal unit ball.

If every vector in the primal seminorm unit ball has ambient norm at most `C`,
then the support-function dual norm varies continuously with its dual vector.

Layer: Model | Gap: Level 1 (canonical dual norm continuity)
Proof: derive an epsilon-delta continuity proof from the canonical dual norm
  Lipschitz estimate, using the zero vector to infer nonnegativity of the
  control constant.
Source: Functional analysis dual norms, support functions of unit balls, and
  Mathlib metric continuity APIs
Used in: stochastic block mirror descent measurability of squared block dual norms
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem canonicalDualNorm_continuous
    {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℝ B]
    (p : Seminorm ℝ B) {C : ℝ}
    (hC : ∀ x : B, p x ≤ 1 -> ‖x‖ ≤ C) :
    Continuous (fun zeta : B => canonicalDualNorm p zeta) := by
  classical
  have hC0 : 0 ≤ C := by
    have hzero : p (0 : B) ≤ 1 := by simp
    simpa using hC (0 : B) hzero
  rw [Metric.continuous_iff]
  intro x eps heps
  have hC1pos : 0 < C + 1 := by linarith
  refine ⟨eps / (C + 1), div_pos heps hC1pos, ?_⟩
  intro y hy
  have hy_norm : ‖y - x‖ < eps / (C + 1) := by
    simpa [dist_eq_norm] using hy
  have hlip := canonicalDualNorm_lipschitz_control (p := p) (C := C) hC y x
  have hCnorm_le : C * ‖y - x‖ ≤ (C + 1) * ‖y - x‖ := by
    exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
  have hmul : (C + 1) * ‖y - x‖ < eps := by
    have hmul' := mul_lt_mul_of_pos_left hy_norm hC1pos
    have hcancel : (C + 1) * (eps / (C + 1)) = eps := by
      field_simp [ne_of_gt hC1pos]
    simpa [hcancel] using hmul'
  have hdist_le :
      dist (canonicalDualNorm p y) (canonicalDualNorm p x) ≤ C * ‖y - x‖ := by
    simpa [Real.dist_eq] using hlip
  exact lt_of_le_of_lt hdist_le (lt_of_le_of_lt hCnorm_le hmul)

/-- A canonical dual norm induced by a primal seminorm is nonnegative.

The support set contains the zero support value, because the zero vector is in
the primal seminorm unit ball. If the set is bounded above, this is the usual
`le_csSup` argument; if not, Lean's real supremum convention rewrites the
unbounded supremum to `0`.

Layer: Model | Gap: Level 1 (canonical dual norm nonnegativity)
Proof: unfold the canonical dual norm as a supremum over the primal unit ball,
  put the zero support value in the support set, and split on boundedness of
  that set to use either `le_csSup` or `Real.sSup_of_not_bddAbove`.
Source: Functional analysis dual norms, support functions of unit balls, and
  Mathlib order-theoretic supremum API for real sets
Used in: stochastic block mirror descent Jensen/L2 estimates for block oracle
  dual norms
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine
  Learning, stochastic block mirror descent -/
theorem canonicalDualNorm_nonneg
    {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℝ B]
    (p : Seminorm ℝ B) (zeta : B) :
    0 ≤ canonicalDualNorm p zeta := by
  classical
  let A : Set ℝ := {r : ℝ | ∃ d : B, p d ≤ 1 ∧ r = |inner ℝ zeta d|}
  have hzero_mem : (0 : ℝ) ∈ A := by
    refine ⟨0, ?_, ?_⟩
    · simp
    · simp
  rw [canonicalDualNorm_eq_sSup]
  change 0 ≤ sSup A
  by_cases hA_bdd : BddAbove A
  · exact le_csSup hA_bdd hzero_mem
  · rw [Real.sSup_of_not_bddAbove hA_bdd]

/-- The canonical support-function dual norm of a Bochner integral is bounded
by the integral of the pointwise canonical dual norm.

This is the sublinearity/Jensen inequality for a dual norm presented as the
support function of a primal seminorm unit ball. The boundedness hypothesis is
only required at the integrand values, where `le_csSup` extracts the pointwise
support bound.

Layer: Model | Gap: Level 1 (support-function Jensen inequality)
Proof: bound each support value at the mean by commuting the fixed inner-product
  functional through the Bochner integral, applying `abs_integral_le_integral_abs`,
  and comparing pointwise support values by `le_csSup`.
Source: Functional analysis support functions of unit balls and Mathlib
  Bochner integral continuous-linear-map APIs
Used in: stochastic block mirror descent deterministic mean bound for block
  oracle dual norms
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine
  Learning, stochastic block mirror descent -/
theorem canonicalDualNorm_integral_le_integral
    {Ω B : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup B] [InnerProductSpace ℝ B] [CompleteSpace B]
    {μ : Measure Ω} (p : Seminorm ℝ B)
    {Y : Ω → B}
    (hY_support_bdd :
      ∀ ω, BddAbove {r : ℝ | ∃ d : B, p d ≤ 1 ∧ r = |inner ℝ (Y ω) d|})
    (hY : Integrable Y μ)
    (hdual : Integrable (fun ω => canonicalDualNorm p (Y ω)) μ) :
    canonicalDualNorm p (∫ ω, Y ω ∂μ) ≤
      ∫ ω, canonicalDualNorm p (Y ω) ∂μ := by
  classical
  let A : Set ℝ :=
    {r : ℝ | ∃ d : B, p d ≤ 1 ∧ r = |inner ℝ (∫ ω, Y ω ∂μ) d|}
  have hA_nonempty : A.Nonempty := by
    refine ⟨0, ?_⟩
    refine ⟨0, ?_, ?_⟩
    · simp
    · simp
  rw [canonicalDualNorm_eq_sSup]
  change sSup A ≤ ∫ ω, canonicalDualNorm p (Y ω) ∂μ
  refine csSup_le hA_nonempty ?_
  intro r hr
  rcases hr with ⟨d, hpd, rfl⟩
  have hinner_int : Integrable (fun ω => inner ℝ (Y ω) d) μ := by
    simpa [real_inner_comm] using (innerSL ℝ d).integrable_comp hY
  have hinner_comm :
      inner ℝ (∫ ω, Y ω ∂μ) d = ∫ ω, inner ℝ (Y ω) d ∂μ := by
    have h := (ContinuousLinearMap.integral_comp_comm (innerSL ℝ d) hY).symm
    simpa [real_inner_comm] using h
  have habs_le :
      |∫ ω, inner ℝ (Y ω) d ∂μ| ≤ ∫ ω, |inner ℝ (Y ω) d| ∂μ :=
    abs_integral_le_integral_abs
  have hpoint :
      ∀ ω, |inner ℝ (Y ω) d| ≤ canonicalDualNorm p (Y ω) := by
    intro ω
    have hmem :
        |inner ℝ (Y ω) d| ∈
          {r : ℝ | ∃ u : B, p u ≤ 1 ∧ r = |inner ℝ (Y ω) u|} := by
      exact ⟨d, hpd, rfl⟩
    rw [canonicalDualNorm_eq_sSup]
    exact le_csSup (hY_support_bdd ω) hmem
  have hmono :
      ∫ ω, |inner ℝ (Y ω) d| ∂μ ≤
        ∫ ω, canonicalDualNorm p (Y ω) ∂μ := by
    exact integral_mono hinner_int.abs hdual hpoint
  calc
    |inner ℝ (∫ ω, Y ω ∂μ) d| = |∫ ω, inner ℝ (Y ω) d ∂μ| := by
      rw [hinner_comm]
    _ ≤ ∫ ω, |inner ℝ (Y ω) d| ∂μ := habs_le
    _ ≤ ∫ ω, canonicalDualNorm p (Y ω) ∂μ := hmono

/-- Integrating an inverse-probability weighted block lift reconstructs the
ambient vector.

If a finite block law assigns singleton mass `p i` to index `i`, each
probability is positive, and the unweighted lifted coordinates sum to `v`,
then the Bochner integral of the sampled inverse-weighted lift is exactly `v`.

Layer: Model | Gap: Level 1 (finite block-sampling lift reconstruction)
Proof: expand the Bochner integral over the finite index type with
  `MeasureTheory.integral_fintype`; convert singleton masses to real weights,
  cancel `pᵢ * pᵢ⁻¹`, and apply the supplied lift-coordinate reconstruction.
Source: Mathlib Bochner integral finite-type expansion and finite coordinate
  reconstruction algebra
Used in: stochastic block mirror descent sampled lifted block oracle
  unbiasedness
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/main_theorem/proof/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem integral_weighted_block_lift_coord_eq_self
    {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {B : ι → Type*}
    (μ : MeasureTheory.Measure ι) [MeasureTheory.IsFiniteMeasure μ] (p : ι → ℝ)
    (coord : ∀ i, E → B i) (lift : ∀ i, B i → E) (v : E)
    (hμ_singleton : ∀ i, μ ({i} : Set ι) = ENNReal.ofReal (p i))
    (hp_pos : ∀ i, 0 < p i)
    (hreconstruct : Finset.sum Finset.univ (fun i => lift i (coord i v)) = v) :
    ∫ i, (p i)⁻¹ • lift i (coord i v) ∂μ = v := by
  rw [MeasureTheory.integral_fintype (μ := μ)]
  · calc
      Finset.sum Finset.univ
          (fun i => (μ.real ({i} : Set ι)) • ((p i)⁻¹ • lift i (coord i v)))
          = Finset.sum Finset.univ (fun i => lift i (coord i v)) := by
            apply Finset.sum_congr rfl
            intro i _hi
            have hμreal : μ.real ({i} : Set ι) = p i := by
              rw [MeasureTheory.Measure.real]
              rw [hμ_singleton i]
              simp [le_of_lt (hp_pos i)]
            rw [hμreal]
            rw [smul_smul]
            have hpne : p i ≠ 0 := ne_of_gt (hp_pos i)
            field_simp [hpne]
            simp
      _ = v := hreconstruct
  · exact MeasureTheory.Integrable.of_finite

/-- In a real inner product space, the paper-facing dual norm is realized by the
ambient norm under the Riesz self-duality identification.
Layer: Model | Concept: Norm
Proof: (definitional construction; Euclidean dual-norm realization via inner product)
Source: Euclidean/Riesz self-duality for Hilbert-space norms
Used in: stochastic mirror descent oracle bounds and variance hypotheses
Book citation: book/FOML/StochasticMirrorDescent.json#/assumptions/4/math
Book citation: book/FOML/StochasticMirrorDescent.json#/assumptions/6/math
Origin algorithm: FOML stochastic mirror descent -/
noncomputable def dualNorm
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (g : E) : ℝ :=
  ‖g‖

/-- Definitional formula for the inner-product-space dual norm realization.
Layer: Model | Gap: Level 0 (dual norm formula)
Proof: expand the self-dual norm definition
Source: Euclidean/Riesz self-duality for Hilbert-space norms
Used in: stochastic mirror descent oracle bounds and variance hypotheses
Book citation: book/FOML/StochasticMirrorDescent.json#/assumptions/4/math
Book citation: book/FOML/StochasticMirrorDescent.json#/assumptions/6/math
Origin algorithm: FOML stochastic mirror descent -/
@[simp]
theorem dualNorm_eq_norm
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (g : E) :
    dualNorm g = ‖g‖ := by
  rfl

/-- Squaring the self-dual norm realization gives the squared ambient norm.
Layer: Model | Gap: Level 0 (squared dual norm formula)
Proof: expand the self-dual norm definition
Source: Euclidean/Riesz self-duality for Hilbert-space norms
Used in: stochastic mirror descent oracle variance hypotheses
Book citation: book/FOML/StochasticMirrorDescent.json#/assumptions/6/math
Origin algorithm: FOML stochastic mirror descent -/
@[simp]
theorem dualNorm_sq_eq_norm_sq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (g : E) :
    dualNorm g ^ 2 = ‖g‖ ^ 2 := by
  rfl

end SOptLib

namespace Matrix

-- Generalization plan (G0):
-- concept/name: trace-plus-inverse-trace matrix potential, named
--   `Matrix.traceInversePotential`; orig was `theorem7_equation6_potential`
-- generality used: an arbitrary finite index type with decidable equality, a real
--   coefficient, and a real square matrix; no positivity, invertibility, measure,
--   convexity, smoothness, stochastic-oracle, or algorithm-state assumptions
-- portable call pattern: full-matrix adaptive-gradient and matrix FTRL analyses choose
--   this regularized trace potential while changing the coordinate type, coefficient,
--   and positive-definite preconditioner
-- counterargument checked: although its construction is a short formula, the
--   trace-plus-inverse-trace regularizer is a stable named matrix potential used as the
--   objective component in FTL/BTL minimization, not paper-local bookkeeping; naming it
--   also lets its nonnegativity and square-root-minimizer API share one object
-- coverage search: symbol search for "trace inverse matrix potential equality" found
--   only separate trace and inverse-metric quadratic-form declarations; Mathlib semantic
--   search for the full formula found `Matrix.trace` and its linearity API but no named
--   combined potential, so coverage is partial rather than duplicative
-- minimal hypotheses: `Fintype` is needed by `Matrix.trace`, and `DecidableEq` by the
--   total matrix inverse; the real scalar is retained for the intended ordered spectral API

/-- The trace-plus-inverse-trace potential of a finite real square matrix.

For coefficient `c`, this matrix regularizer is
`Tr(H) + c * Tr(H⁻¹)`, using Mathlib's total matrix inverse.

Layer: Model | Concept: trace-plus-inverse-trace matrix potential
Proof: (definitional construction; add the matrix trace to a scalar multiple of the inverse matrix trace)
Source: Mathlib finite-matrix trace and total matrix inverse, together with the standard matrix FTRL trace regularizer
Used in: full-matrix adaptive-gradient and matrix follow-the-regularized-leader bounds whose positive-definite square-root preconditioner minimizes a trace objective
Book citation: book/research/Source.json#/key_lemmas/8/proof/9
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Theorem 7 matrix regret analysis -/
noncomputable def traceInversePotential {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ℝ) (H : Matrix ι ι ℝ) : ℝ :=
  trace H + c * trace H⁻¹

/-- The trace-plus-inverse-trace potential unfolds to its defining trace formula.

Layer: Model | Gap: Level 0 (trace-plus-inverse-trace potential specification)
Proof: by rfl after unfolding `Matrix.traceInversePotential`
Source: Mathlib finite-matrix trace and total matrix inverse
Used in: expanding the named matrix potential inside FTL/BTL objectives and positive-definite square-root minimizer calculations
Book citation: book/research/Source.json#/key_lemmas/8/proof/9
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Theorem 7 matrix regret analysis -/
@[simp]
theorem traceInversePotential_def {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ℝ) (H : Matrix ι ι ℝ) :
    traceInversePotential c H = trace H + c * trace H⁻¹ :=
  rfl

/-- The trace-plus-inverse-trace potential is nonnegative on positive semidefinite
matrices when its coefficient is nonnegative.

Layer: Model | Gap: Level 0 (nonnegativity of the trace-plus-inverse-trace potential)
Proof: both a positive semidefinite matrix and its inverse have nonnegative trace;
multiply the latter inequality by the nonnegative coefficient and add
Source: Mathlib positive-semidefinite inverse and trace nonnegativity APIs
Used in: lower bounds for matrix FTRL objectives and adaptive-gradient potentials -/
theorem traceInversePotential_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    {c : ℝ} {H : Matrix ι ι ℝ} (hc : 0 ≤ c) (hH : H.PosSemidef) :
    0 ≤ traceInversePotential c H := by
  rw [traceInversePotential_def]
  exact add_nonneg hH.trace_nonneg (mul_nonneg hc hH.inv.trace_nonneg)

end Matrix

namespace Matrix

-- Generalization plan (G0):
-- concept/name: regularized prefix Gram matrix, named `Matrix.regularizedPrefixGram`;
--   orig was `theorem7_hhat_prefix_base`
-- generality used: an arbitrary finite coordinate type with decidable equality, a finite
--   real vector stream, an arbitrary real ridge coefficient, and a prefix endpoint; no
--   algorithm state, rank, measure, convexity, smoothness, or oracle assumptions are used
-- portable call pattern: full-matrix AdaGrad, online Newton, and matrix/tensor adaptive
--   preconditioner proofs form the same ridge-plus-prefix covariance matrix while changing
--   the vector stream, coordinate type, ridge coefficient, and prefix endpoint
-- counterargument checked: although the construction is a single formula, regularized
--   empirical Gram/covariance matrices are a recognized recurring adaptive-metric object;
--   the positivity API below gives the name value beyond a caller-side expression
-- coverage search: searched SOptLib/project symbols for "regularized prefix Gram matrix"
--   and "finite prefix sum outer products identity matrix", and Mathlib semantically for
--   the full formula; Mathlib provides `Matrix.vecMulVec` and its PSD theorem, while the
--   only full-form hits were private paper-local declarations, so coverage is partial
-- minimal hypotheses: `DecidableEq ι` supplies the identity matrix in the definition;
--   `Finite ι` is required only by the corresponding positivity API theorems

/-- The ridge-regularized Gram matrix of a finite vector stream up to a strict prefix.

At endpoint `N`, this is the ridge coefficient times the identity plus the sum of
`g s g sᵀ` over exactly those finite indices whose natural value is less than `N`.

Layer: Model | Concept: ridge-regularized prefix Gram matrix
Proof: (definitional construction; scalar identity ridge plus a strict-prefix sum of vector outer products)
Source: Mathlib `Matrix.vecMulVec`, finite big operators, and identity matrices
Used in: full-matrix adaptive-gradient, online Newton, and tensor-preconditioner analyses that take spectral powers of accumulated gradient outer products
Book citation: book/research/Source.json#/key_lemmas/8/proof/8
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 1 matrix preconditioner -/
noncomputable def regularizedPrefixGram
    {ι : Type*} [DecidableEq ι] {T : Nat}
    (g : Fin T → ι → ℝ) (ridge : ℝ) (N : Fin (T + 1)) : Matrix ι ι ℝ :=
  ridge • (1 : Matrix ι ι ℝ) +
    ∑ s : Fin T, if s.1 < N.1 then Matrix.vecMulVec (g s) (g s) else 0

/-- A regularized prefix Gram matrix unfolds to its ridge and strict-prefix outer-product
sum.

Layer: Model | Gap: Level 0 (regularized prefix Gram matrix specification)
Proof: by rfl after unfolding `Matrix.regularizedPrefixGram`
Source: Mathlib `Matrix.vecMulVec`, finite big operators, and identity matrices
Used in: rewriting named adaptive preconditioner bases into the source-level ridge-plus-gradient-outer-product formula
Book citation: book/research/Source.json#/key_lemmas/8/proof/8
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 1 matrix preconditioner -/
@[simp]
theorem regularizedPrefixGram_def
    {ι : Type*} [DecidableEq ι] {T : Nat}
    (g : Fin T → ι → ℝ) (ridge : ℝ) (N : Fin (T + 1)) :
    regularizedPrefixGram g ridge N =
      ridge • (1 : Matrix ι ι ℝ) +
        ∑ s : Fin T, if s.1 < N.1 then Matrix.vecMulVec (g s) (g s) else 0 :=
  rfl

/-- A regularized prefix Gram matrix is positive semidefinite when its ridge is
nonnegative.

Layer: Model | Gap: Level 0 (positive semidefiniteness of a regularized prefix Gram matrix)
Proof: each real vector outer product is positive semidefinite; close the finite prefix sum under addition and add the nonnegative scalar multiple of the identity
Source: Mathlib positive-semidefinite vector outer products, finite sums, scalar multiplication, and identity matrices
Used in: establishing the domain certificate for spectral powers of adaptive full-matrix preconditioner bases
Book citation: book/research/Source.json#/key_lemmas/8/proof/8
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 1 matrix preconditioner -/
theorem regularizedPrefixGram_posSemidef
    {ι : Type*} [Finite ι] [DecidableEq ι] {T : Nat}
    (g : Fin T → ι → ℝ) {ridge : ℝ} (hridge : 0 ≤ ridge)
    (N : Fin (T + 1)) :
    (regularizedPrefixGram g ridge N).PosSemidef := by
  classical
  have hprefix :
      (∑ s : Fin T, if s.1 < N.1 then Matrix.vecMulVec (g s) (g s) else 0 :
        Matrix ι ι ℝ).PosSemidef := by
    exact Finset.sum_induction
      (fun s : Fin T =>
        if s.1 < N.1 then Matrix.vecMulVec (g s) (g s) else 0)
      (fun A : Matrix ι ι ℝ => A.PosSemidef)
      (fun _ _ hA hB => hA.add hB)
      Matrix.PosSemidef.zero
      (by
        intro s _
        by_cases hsN : s.1 < N.1
        · simpa [hsN] using Matrix.posSemidef_vecMulVec_self_star (g s)
        · simpa [hsN] using
            (Matrix.PosSemidef.zero : (0 : Matrix ι ι ℝ).PosSemidef))
  rw [regularizedPrefixGram_def]
  exact (Matrix.PosSemidef.one.smul hridge).add hprefix

/-- A regularized prefix Gram matrix is positive definite when its ridge is positive.

Layer: Model | Gap: Level 0 (positive definiteness of a regularized prefix Gram matrix)
Proof: a positive scalar multiple of the identity is positive definite, the prefix outer-product sum is positive semidefinite, and positive definiteness is preserved by adding it
Source: Mathlib positive-definite identity scaling and positive-semidefinite vector outer-product finite sums
Used in: justifying inverse metrics and negative matrix powers for ridge-regularized adaptive preconditioners
Book citation: book/research/Source.json#/key_lemmas/8/proof/8
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithm 1 matrix preconditioner -/
theorem regularizedPrefixGram_posDef
    {ι : Type*} [Finite ι] [DecidableEq ι] {T : Nat}
    (g : Fin T → ι → ℝ) {ridge : ℝ} (hridge : 0 < ridge)
    (N : Fin (T + 1)) :
    (regularizedPrefixGram g ridge N).PosDef := by
  have hprefix :
      (∑ s : Fin T, if s.1 < N.1 then Matrix.vecMulVec (g s) (g s) else 0 :
        Matrix ι ι ℝ).PosSemidef := by
    simpa [regularizedPrefixGram] using
      (regularizedPrefixGram_posSemidef g (ridge := 0) (le_refl 0) N)
  rw [regularizedPrefixGram_def]
  exact (Matrix.PosDef.one.smul hridge).add_posSemidef hprefix

end Matrix

namespace Matrix

-- Generalization plan (G0):
-- concept/name: competitor rewrite for a trace-regularized inverse-matrix
--   objective under a square identity; orig was the local block
--   `traceInversePotential_competitor_rewrite`
-- generality used: an arbitrary finite index type with decidable equality,
--   four real matrix/scalar parameters, and only the pointwise square identity;
--   no positivity, invertibility, measure, convexity, smoothness, oracle, or
--   algorithm-state assumptions are used
-- portable call pattern: matrix FTRL, full-matrix AdaGrad, and Shampoo-style
--   square-root minimization proofs rewrite the regularized objective at a
--   changing competitor while the Gram matrix, coefficient, square root, and
--   competitor vary and the square-identity contract remains fixed
-- counterargument checked: this is not paper-local traceability or a pure
--   rename; it packages the reusable transition from a regularized inverse
--   objective to the matrix AM-GM comparison form, and unlike the nearby
--   terminal-value lemma it applies to an arbitrary competitor without an
--   invertibility hypothesis
-- coverage search: symbol searches for "matrix trace product inverse plus trace
--   inverse potential equals trace square product inverse plus trace from square
--   identity" and "traceInversePotential square identity competitor" found the
--   distinct `trace_mul_inv_add_traceInversePotential_eq_two_trace_of_square`,
--   which evaluates at `H` and assumes `IsUnit H`; Mathlib semantic search found
--   only `Matrix.trace_add`, `Matrix.trace_smul`, and the base trace API, so
--   coverage is partial rather than full
-- minimal hypotheses: `Fintype` is needed by trace and `DecidableEq` by matrix
--   multiplication and total inverse; the square identity is the sole
--   mathematical hypothesis, and positivity/invertibility assumptions were
--   removed because the algebraic cancellation does not use them

/-- If `H` squares to a scalar identity plus `M`, the trace-regularized inverse
objective at any competitor `K` equals the matrix-square comparison objective.

Layer: Model | Gap: Level 1 (regularized inverse-matrix competitor objective rewrite)
Proof: solve the square identity for `M`, distribute multiplication by the competitor inverse, then use trace linearity and scalar compatibility to cancel the regularization terms.
Source: Mathlib finite-matrix trace, scalar multiplication, matrix multiplication, and total nonsingular-inverse APIs
Used in: matrix FTRL, full-matrix AdaGrad, and Shampoo square-root minimization arguments immediately before applying a trace matrix AM-GM inequality to an arbitrary positive-definite competitor
Book citation: book/research/Source.json#/key_lemmas/8/proof/10
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Theorem 7 matrix regret analysis -/
theorem trace_mul_inv_add_traceInversePotential_eq_trace_square_mul_inv_add_trace_of_square
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (c : ℝ) (H K : Matrix ι ι ℝ)
    (hHsqr : H * H = c • (1 : Matrix ι ι ℝ) + M) :
    trace (M * K⁻¹) + traceInversePotential c K =
      trace (H * H * K⁻¹) + trace K := by
  have hM : M = H * H - c • (1 : Matrix ι ι ℝ) := by
    rw [hHsqr]
    abel
  rw [hM, traceInversePotential_def]
  simp [sub_mul]

end Matrix

namespace Matrix

-- Generalization plan (G0):
-- concept/name: exact value of a trace-plus-inverse-trace objective at an
--   invertible matrix satisfying a regularized square identity; orig was
--   `trace_regularized_sqrt_objective_eq_two_trace_of_square_identity`
-- generality used: an arbitrary finite index type with decidable equality,
--   real square matrices, a real regularization coefficient, invertibility of
--   the square root, and the pointwise square identity; positivity is unused
-- portable call pattern: matrix FTRL and full-matrix adaptive-gradient proofs
--   change the Gram/covariance matrix, regularization coefficient, and chosen
--   invertible square root while retaining `H * H = c • 1 + M`
-- counterargument checked: this is not paper-local traceability or a pure
--   wrapper; it composes the square identity, nonsingular-inverse cancellation,
--   trace linearity, and the named potential to eliminate the full objective
-- coverage search: symbol queries for "matrix trace product inverse plus trace
--   inverse potential equals twice trace square identity" and "traceInversePotential
--   square matrix inverse trace equality" found only `Matrix.traceInversePotential`
--   and its unfolding theorem; Mathlib semantic search found `Matrix.trace`,
--   `Matrix.trace_add`, and inverse/conjugation lemmas, but no theorem with this
--   objective-value contract, so existing coverage is partial
-- minimal hypotheses: `Fintype` supports trace, `DecidableEq` supports matrix
--   multiplication and nonsingular inverse, and `IsUnit H` is exactly the
--   cancellation property used; no positive-definiteness or finite-dimensional
--   vector-space assumption beyond the finite matrix index is needed

/-- If an invertible matrix squares to a scalar identity plus `M`, then the sum
of `trace (M * H⁻¹)` and the trace-plus-inverse-trace potential at `H` is
twice the trace of `H`.

Layer: Model | Gap: Level 1 (regularized matrix trace objective value at an invertible square root)
Proof: solve the square identity for `M`, distribute multiplication by `H⁻¹`, cancel `H * H⁻¹` using invertibility, and use trace linearity before ring normalization.
Source: Mathlib finite-matrix trace and nonsingular-inverse APIs, together with the standard matrix square-root identity for trace-regularized FTRL objectives
Used in: matrix FTRL and full-matrix adaptive-gradient potential arguments that evaluate the terminal objective at its invertible regularized square root
Book citation: book/research/Source.json#/key_lemmas/8/proof/14
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Theorem 7 matrix regret analysis -/
theorem trace_mul_inv_add_traceInversePotential_eq_two_trace_of_square
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (c : ℝ) (H : Matrix ι ι ℝ)
    (hH : IsUnit H) (hHsqr : H * H = c • (1 : Matrix ι ι ℝ) + M) :
    trace (M * H⁻¹) + traceInversePotential c H = 2 * trace H := by
  have hHdet : IsUnit H.det := (isUnit_iff_isUnit_det H).mp hH
  have hM : M = H * H - c • (1 : Matrix ι ι ℝ) := by
    rw [hHsqr]
    abel
  rw [hM, traceInversePotential_def]
  simp [sub_mul, mul_assoc, mul_nonsing_inv H hHdet]
  ring

end Matrix

namespace Matrix

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
private theorem two_mul_trace_le_trace_mul_mul_inv_add_trace_of_posDef_local
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

-- Generalization plan (G0):
-- concept/name: minimization of the trace-plus-inverse-trace matrix objective
--   by a positive-definite square root, named
--   `Matrix.traceInversePotential_objective_minimized_of_square`; orig was
--   `trace_regularized_sqrt_minimizer_of_square_identity`
-- generality used: an arbitrary finite index type with decidable equality,
--   real square matrices, a real coefficient, invertibility and Hermitianity
--   of the proposed minimizer, positive definiteness of the competitor, and
--   the pointwise square identity; no measure, convexity, smoothness,
--   stochastic-oracle, or algorithm state
-- portable call pattern: full-matrix AdaGrad, matrix FTRL, and adaptive mirror
--   descent change the accumulated covariance matrix, regularization
--   coefficient, certified square root, and competitor while retaining the
--   same positive-definite minimizer inequality under `H * H = c • 1 + M`
-- counterargument checked: this is not merely paper-local traceability or a
--   one-line rename; it packages two objective-identification bridges with a
--   noncommutative matrix trace Young inequality into the reusable minimizer
--   contract needed by future matrix-adaptive proofs
-- coverage search: symbol queries for "trace inverse potential objective
--   minimized positive definite square identity" and "matrix trace objective
--   inequality square root positive definite competitor" found the two
--   objective rewrites and `Matrix.two_mul_trace_le_trace_mul_mul_inv_add_trace_of_posDef`
--   as partial components, but no theorem with this minimizer conclusion;
--   Mathlib semantic search returned square-root and positive-definite matrix
--   APIs but no trace-objective minimization theorem
-- minimal hypotheses: `Fintype` and `DecidableEq` support finite matrix trace,
--   multiplication, and total inverse; the proposed minimizer needs only the
--   invertibility used to evaluate its objective and the Hermitianity used by
--   trace Young, while the competitor remains positive definite

/-- An invertible Hermitian matrix whose square is `c • 1 + M` minimizes the
trace-linear objective augmented by the trace-plus-inverse-trace potential
among positive-definite competitors.

Layer: Model | Gap: Level 2 (positive-definite square-root minimizer for a trace-regularized inverse-matrix objective)
Proof: evaluate the objective at the certified square root, rewrite the competitor objective using the square identity, and compare them with the positive-definite matrix trace Young inequality.
Source: Mathlib finite-matrix trace, nonsingular inverse, positive-definite matrix order, and the matrix trace Young inequality obtained by noncommutative square completion
Used in: full-matrix adaptive-gradient and matrix-FTRL follow-the-leader steps that certify the regularized accumulated-covariance square root as the minimizing preconditioner
Book citation: book/research/Source.json#/key_lemmas/8/proof/11
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Theorem 7 matrix regret analysis -/
theorem traceInversePotential_objective_minimized_of_square
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (c : ℝ) (H K : Matrix ι ι ℝ)
    (hHunit : IsUnit H) (hHherm : H.IsHermitian) (hK : K.PosDef)
    (hHsqr : H * H = c • (1 : Matrix ι ι ℝ) + M) :
    trace (M * H⁻¹) + traceInversePotential c H ≤
      trace (M * K⁻¹) + traceInversePotential c K := by
  calc
    trace (M * H⁻¹) + traceInversePotential c H = 2 * trace H :=
      trace_mul_inv_add_traceInversePotential_eq_two_trace_of_square
        M c H hHunit hHsqr
    _ ≤ trace (H * H * K⁻¹) + trace K :=
      two_mul_trace_le_trace_mul_mul_inv_add_trace_of_posDef_local H K hHherm hK
    _ = trace (M * K⁻¹) + traceInversePotential c K :=
      (trace_mul_inv_add_traceInversePotential_eq_trace_square_mul_inv_add_trace_of_square
        M c H K hHsqr).symm

end Matrix

namespace Matrix

-- Generalization plan (G0):
-- concept/name: the canonical CFC square root minimizes a trace-plus-inverse-trace
--   matrix objective, named `Matrix.cfc_sqrt_minimizes_traceInversePotential_objective`;
--   orig was `trace_regularized_sqrt_minimizer_of_posDef`
-- generality used: an arbitrary finite decidable index type, real square matrix,
--   real regularization coefficient, positive-definite regularized matrix, and
--   positive-definite competitor; no algorithm state, measure, or convexity assumptions
-- portable call pattern: full-matrix AdaGrad and matrix FTRL change the accumulated
--   covariance matrix, regularization coefficient, finite coordinate type, and competitor
--   while using the same canonical-square-root minimizer conclusion
-- counterargument checked: this is not paper-local traceability or a duplicate of the
--   certified-square theorem; it selects Mathlib's canonical `CFC.sqrt` and discharges
--   that theorem's invertibility, Hermitianity, and square-witness premises from one
--   positive-definiteness certificate
-- coverage search: queries "CFC square root minimizes trace inverse potential objective
--   positive definite competitor", "positive definite matrix square root square equals
--   matrix", and the corresponding Mathlib semantic query found `PosDef.posDef_sqrt`,
--   `CFC.sqrt_mul_sqrt_self`, and the already-staged certified-square minimizer as
--   partial components, but no theorem exposing this canonical minimizer contract
-- minimal hypotheses: positive definiteness of the regularized matrix supplies all facts
--   required of its CFC square root; positive definiteness of the competitor is retained

/-- The CFC square root of a positive-definite scalar-regularized matrix minimizes
the trace-linear objective augmented by the trace-plus-inverse-trace potential among
positive-definite competitors.

Layer: Model | Gap: Level 1 (canonical CFC square-root minimizer for a trace-regularized inverse-matrix objective)
Proof: specialize the certified-square minimizer theorem; positive definiteness gives a positive-definite CFC square root, and the CFC square-root product law supplies its square identity.
Source: Mathlib continuous functional calculus square roots and positive-definite finite matrices, combined with the trace matrix AM-GM minimizer theorem
Used in: full-matrix adaptive-gradient and matrix-FTRL follow-the-leader steps that choose the regularized accumulated-covariance square root as the minimizing preconditioner
Book citation: book/research/Source.json#/key_lemmas/8/proof/11
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Theorem 7 matrix regret analysis -/
theorem cfc_sqrt_minimizes_traceInversePotential_objective
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (c : ℝ)
    (hA : (c • (1 : Matrix ι ι ℝ) + M).PosDef)
    (K : Matrix ι ι ℝ) (hK : K.PosDef) :
    trace (M * (CFC.sqrt (c • (1 : Matrix ι ι ℝ) + M))⁻¹) +
        traceInversePotential c (CFC.sqrt (c • (1 : Matrix ι ι ℝ) + M)) ≤
      trace (M * K⁻¹) + traceInversePotential c K := by
  have hroot : (CFC.sqrt (c • (1 : Matrix ι ι ℝ) + M)).PosDef :=
    Matrix.isStrictlyPositive_iff_posDef.mp hA.isStrictlyPositive.sqrt
  exact traceInversePotential_objective_minimized_of_square
    M c (CFC.sqrt (c • (1 : Matrix ι ι ℝ) + M)) K
    hroot.isUnit hroot.1 hK
    (CFC.sqrt_mul_sqrt_self (c • (1 : Matrix ι ι ℝ) + M))

end Matrix


-- Merged from Staging/affineDirectionDualNorm.lean
open scoped InnerProductSpace

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: affine-direction dual norm; orig was affineDirectionDualNorm.
-- generality used: arbitrary carrier set in a real inner-product normed additive group, with a bundled primal seminorm and a dual vector; no measure, convexity, smoothness, oracle, completeness, or finite-dimensional assumptions.
-- portable call pattern: carrier-based smoothness and gradient-memory estimates call the same restricted support function while changing X, the primal seminorm, and the gradient or oracle residual vector.
-- counterargument checked: not paper-local traceability because future constrained stochastic-optimization proofs need a support dual over feasible affine directions; not a wrapper around Mathlib operator norm because the unit set is seminorm-based and restricted to an affine-span direction.
-- coverage search: checked SOptLib canonicalDualNorm/canonicalDualNorm_eq_sSup and Mathlib ContinuousLinearMap.sSup_unitClosedBall_eq_norm; they cover ambient norm balls, not the affine-direction seminorm support set.
-- minimal hypotheses: finite dimensionality and seminorm separation are unnecessary for this definitional object; all remaining hypotheses are needed to state affineSpan and the real inner product pairing.

/-- The dual support function of a primal seminorm restricted to affine-span directions.

For a carrier `X`, only directions in `(affineSpan ℝ X).direction` are tested in
the primal unit ball. This is the intrinsic dual gauge used when gradients or
subgradients are modeled on a feasible affine hull rather than all ambient
directions.

Layer: Model | Concept: Norm
Proof: (definitional construction; support function over the affine-direction primal unit ball)
Source: Functional analysis dual norms, support functions of unit balls, and affine subspace direction spaces
Used in: randomized gradient extrapolation component smoothness and gradient-memory estimates over feasible affine directions
Book citation: book/FOML/RandomGradientExtrapolation.json#/assumptions/1/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, randomized gradient extrapolation method -/
noncomputable def affineDirectionDualNorm
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X : Set E) (p : Seminorm ℝ E) (zeta : E) : ℝ :=
  sSup {r : ℝ |
    ∃ d : E, d ∈ (affineSpan ℝ X).direction ∧ p d ≤ 1 ∧ r = |⟪zeta, d⟫_ℝ|}

/-- The defining support-function formula for the affine-direction dual norm.

Layer: Model | Gap: Level 0 (affine-direction dual norm formula)
Proof: by rfl after unfolding affineDirectionDualNorm
Source: Functional analysis dual norms, support functions of unit balls, and affine subspace direction spaces
Used in: randomized gradient extrapolation component smoothness and gradient-memory estimates over feasible affine directions
Book citation: book/FOML/RandomGradientExtrapolation.json#/assumptions/1/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, randomized gradient extrapolation method -/
@[simp]
theorem affineDirectionDualNorm_eq_sSup
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X : Set E) (p : Seminorm ℝ E) (zeta : E) :
    affineDirectionDualNorm X p zeta =
      sSup {r : ℝ |
        ∃ d : E, d ∈ (affineSpan ℝ X).direction ∧ p d ≤ 1 ∧ r = |⟪zeta, d⟫_ℝ|} :=
  rfl

/-- The affine-direction dual support value is nonnegative.

The support set contains the value witnessed by the zero direction. If the
support set is bounded above, this follows from `le_csSup`; otherwise Lean's
real supremum convention rewrites the unbounded supremum to `0`.

Layer: Model | Gap: Level 1 (affine-direction dual norm nonnegativity)
Proof: unfold the support formula, insert the zero affine direction, and split
  on boundedness of the support set.
Source: Functional analysis dual norms, support functions of unit balls, and
  Mathlib order-theoretic supremum API for real sets
Used in: randomized gradient extrapolation component smoothness and
  gradient-memory estimates over feasible affine directions
Book citation: book/FOML/RandomGradientExtrapolation.json#/assumptions/1/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized gradient extrapolation method -/
theorem affineDirectionDualNorm_nonneg
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X : Set E) (p : Seminorm ℝ E) (zeta : E) :
    0 ≤ affineDirectionDualNorm X p zeta := by
  classical
  let A : Set ℝ := {r : ℝ |
    ∃ d : E, d ∈ (affineSpan ℝ X).direction ∧ p d ≤ 1 ∧ r = |⟪zeta, d⟫_ℝ|}
  have hzero_mem : (0 : ℝ) ∈ A := by
    refine ⟨0, ?_, ?_, ?_⟩
    · exact (affineSpan ℝ X).direction.zero_mem
    · simp
    · simp
  rw [affineDirectionDualNorm_eq_sSup]
  change 0 ≤ sSup A
  by_cases hA_bdd : BddAbove A
  · exact le_csSup hA_bdd hzero_mem
  · rw [Real.sSup_of_not_bddAbove hA_bdd]

end SOptLib

-- Merged from Staging/affineDirectionDualNorm_add_le.lean
open scoped InnerProductSpace

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: affine-direction dual norm subadditivity; orig was affineDirectionDualNorm_add_le_of_separating.
-- generality used: arbitrary carrier set in a finite-dimensional real inner-product normed additive group, with a bundled primal seminorm and its separating hypothesis; no measure, convexity, smoothness, oracle, completeness, or algorithm state assumptions.
-- portable call pattern: carrier smoothness and stochastic residual proofs split a dual vector into two gradient or oracle residual vectors while reusing the same restricted support-function subadditivity over feasible affine directions.
-- counterargument checked: not paper-local traceability because the statement is the triangle inequality for the named affine-direction support dual; not covered by Mathlib operator-norm support lemmas, and `SOptLib.canonicalDualNorm_add_le` is the unrestricted primal-unit-ball analogue rather than the affine-direction-restricted statement.
-- coverage search: searched CATALOG/SOptLib/Staging for `affineDirectionDualNorm`, `canonicalDualNorm_add_le`, `support function`, and `dual norm subadditive`; LeanSearch for "support function supremum over unit ball subadditive absolute inner product" returned operator-norm `sSup_unitClosedBall_eq_norm` lemmas, with no affine-direction seminorm support theorem.
-- minimal hypotheses: the two affine-direction support sets for the split dual vectors are bounded above; finite-dimensional separating-seminorm assumptions are one caller-side way to prove these localized bounds.

/-- The affine-direction dual norm is subadditive when the split support sets are bounded.

For a support-function dual norm over the primal seminorm unit ball restricted
to `(affineSpan ℝ X).direction`, every support value of `zeta + eta` is bounded
by the sum of the corresponding support values of `zeta` and `eta`.

Layer: Model | Gap: Level 1 (affine-direction dual norm subadditivity)
Proof: unfold the left-hand supremum and apply the absolute-value triangle
  inequality pointwise before comparing to the two support suprema using the
  localized boundedness hypotheses.
Source: Functional analysis dual norms, support functions of unit balls,
  affine subspace direction spaces, and Mathlib order-theoretic supremum APIs
Used in: randomized gradient extrapolation memory-gradient split and carrier
  smoothness estimates over feasible affine directions
Book citation: book/FOML/RandomGradientExtrapolation.json#/algorithm_spec/steps/4
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized gradient extrapolation method -/
theorem affineDirectionDualNorm_add_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X : Set E) (p : Seminorm ℝ E) (zeta eta : E)
    (hzeta : BddAbove {r : ℝ |
      ∃ u : E, u ∈ (affineSpan ℝ X).direction ∧
        p u ≤ 1 ∧ r = |inner ℝ zeta u|})
    (heta : BddAbove {r : ℝ |
      ∃ u : E, u ∈ (affineSpan ℝ X).direction ∧
        p u ≤ 1 ∧ r = |inner ℝ eta u|}) :
    affineDirectionDualNorm X p (zeta + eta) ≤
      affineDirectionDualNorm X p zeta + affineDirectionDualNorm X p eta := by
  classical
  let A : Set ℝ := {r : ℝ |
    ∃ u : E, u ∈ (affineSpan ℝ X).direction ∧
      p u ≤ 1 ∧ r = |inner ℝ (zeta + eta) u|}
  have hA_nonempty : A.Nonempty := by
    refine ⟨0, ?_⟩
    refine ⟨0, ?_, ?_, ?_⟩
    · exact (affineSpan ℝ X).direction.zero_mem
    · simp
    · simp
  rw [affineDirectionDualNorm_eq_sSup]
  change sSup A ≤
    sSup {r : ℝ |
      ∃ u : E, u ∈ (affineSpan ℝ X).direction ∧
        p u ≤ 1 ∧ r = |inner ℝ zeta u|} +
    sSup {r : ℝ |
      ∃ u : E, u ∈ (affineSpan ℝ X).direction ∧
        p u ≤ 1 ∧ r = |inner ℝ eta u|}
  refine csSup_le hA_nonempty ?_
  intro r hr
  rcases hr with ⟨u, hu_dir, hpu, rfl⟩
  have hzeta_le :
      |inner ℝ zeta u| ≤
        sSup {r : ℝ |
          ∃ u : E, u ∈ (affineSpan ℝ X).direction ∧
            p u ≤ 1 ∧ r = |inner ℝ zeta u|} :=
    le_csSup hzeta ⟨u, hu_dir, hpu, rfl⟩
  have heta_le :
      |inner ℝ eta u| ≤
        sSup {r : ℝ |
          ∃ u : E, u ∈ (affineSpan ℝ X).direction ∧
            p u ≤ 1 ∧ r = |inner ℝ eta u|} :=
    le_csSup heta ⟨u, hu_dir, hpu, rfl⟩
  have htri :
      |inner ℝ (zeta + eta) u| ≤
        |inner ℝ zeta u| + |inner ℝ eta u| := by
    simpa [inner_add_left] using abs_add_le (inner ℝ zeta u) (inner ℝ eta u)
  linarith

end SOptLib

-- Merged from Staging/affineDirectionDualNorm_add_sq_le_two_mul_sq_add_two_mul_sq.lean
open scoped InnerProductSpace

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: affine-direction dual norm squared two-term split; orig was dualNorm_add_sq_le_two_mul_dualNorm_sq_add_two_mul_dualNorm_sq.
-- generality used: arbitrary carrier set in a real inner-product normed additive group, with localized boundedness assumptions for the two split support sets; no finite-dimensionality, measure, convexity, smoothness, oracle, completeness, or algorithm state assumptions.
-- portable call pattern: variance-reduced gradient memory and affine-carrier smoothness proofs split one residual into two dual vectors while keeping the same squared affine-direction support-dual estimate.
-- counterargument checked: not paper-local traceability because this is the Young-type square bound for the named affine-direction support dual; not covered by Mathlib's ambient norm square bound or SOptLib's unrestricted canonical dual norm API, and not a pure wrapper because the proof packages affine-direction subadditivity and support-dual nonnegativity.
-- coverage search: searched CATALOG/SOptLib/Staging for `affineDirectionDualNorm`, `dual norm square`, `add_sq`, and `two_mul`; `SOptLib.norm_add_sq_le_two_mul_norm_sq_add_two_mul_norm_sq` covers ambient norms, staged `affineDirectionDualNorm_add_le` covers only the unsquared triangle inequality, and LeanSearch returned general subadditive-sum APIs rather than this affine-direction support-dual square estimate.
-- minimal hypotheses: the two affine-direction support sets for the split dual vectors are bounded above, exactly as required by affine-direction support-dual subadditivity; all algorithm-specific setup hypotheses are removed.

/-- The squared affine-direction dual norm of a sum is bounded by twice the two
split squared dual norms.

This is the support-dual analogue of the usual two-term Young bound
`‖a + b‖^2 ≤ 2‖a‖^2 + 2‖b‖^2`, specialized to the affine-direction dual
support function induced by a primal seminorm.

Layer: Model | Gap: Level 1 (affine-direction dual norm square split)
Proof: apply affine-direction dual-norm subadditivity, square using
  nonnegativity of the support dual, and finish with the real square
  inequality `(x + y)^2 ≤ 2*x^2 + 2*y^2`.
Source: Functional analysis dual norms, support functions of seminorm unit
  balls, affine subspace direction spaces, and real Young inequalities
Used in: randomized gradient extrapolation memory-gradient residual splitting
  over feasible affine directions
Book citation: book/FOML/RandomGradientExtrapolation.json#/algorithm_spec/steps/4
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized gradient extrapolation method -/
theorem affineDirectionDualNorm_add_sq_le_two_mul_sq_add_two_mul_sq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X : Set E) (p : Seminorm ℝ E) (a b : E)
    (ha : BddAbove {r : ℝ |
      ∃ u : E, u ∈ (affineSpan ℝ X).direction ∧
        p u ≤ 1 ∧ r = |inner ℝ a u|})
    (hb : BddAbove {r : ℝ |
      ∃ u : E, u ∈ (affineSpan ℝ X).direction ∧
        p u ≤ 1 ∧ r = |inner ℝ b u|}) :
    affineDirectionDualNorm X p (a + b) ^ 2 ≤
      2 * affineDirectionDualNorm X p a ^ 2 +
        2 * affineDirectionDualNorm X p b ^ 2 := by
  classical
  have hadd :
      affineDirectionDualNorm X p (a + b) ≤
        affineDirectionDualNorm X p a + affineDirectionDualNorm X p b :=
    affineDirectionDualNorm_add_le (X := X) (p := p) (zeta := a) (eta := b)
      ha hb
  have hnonneg : 0 ≤ affineDirectionDualNorm X p (a + b) :=
    affineDirectionDualNorm_nonneg X p (a + b)
  have hsq :
      affineDirectionDualNorm X p (a + b) ^ 2 ≤
        (affineDirectionDualNorm X p a + affineDirectionDualNorm X p b) ^ 2 := by
    nlinarith [hadd, hnonneg]
  have hsplit :
      (affineDirectionDualNorm X p a + affineDirectionDualNorm X p b) ^ 2 ≤
        2 * affineDirectionDualNorm X p a ^ 2 +
          2 * affineDirectionDualNorm X p b ^ 2 := by
    nlinarith [sq_nonneg (affineDirectionDualNorm X p a - affineDirectionDualNorm X p b)]
  exact hsq.trans hsplit

end SOptLib

-- Merged from Staging/abs_inner_le_affineDirectionDualNorm_mul.lean
open scoped InnerProductSpace

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: affine-direction primal-dual support inequality; orig was dualNorm_inner_le_mul_primalNorm_for_component_smoothness.
-- generality used: arbitrary carrier set in a real inner-product normed additive group, with a bundled separating primal seminorm and localized support-set boundedness; no measure, convexity, smoothness, oracle, completeness, finite-dimensionality, or algorithm state assumptions.
-- portable call pattern: carrier-based smoothness, projected gradient, and variance-reduced residual estimates call the same affine-direction primal-dual inequality while changing the carrier `X`, primal seminorm `p`, dual vector `zeta`, and feasible direction `d`.
-- counterargument checked: not paper-local traceability because this is the support inequality for the named affine-direction dual gauge; not a pure wrapper around `canonicalDualNorm` because the support set is restricted to `(affineSpan ℝ X).direction`, and not covered by Mathlib's ambient Cauchy-Schwarz lemmas.
-- coverage search: searched CATALOG/SOptLib/Staging for `affineDirectionDualNorm`, `canonicalDualNorm`, `abs_inner`, and `support function`; `SOptLib.abs_inner_le_canonicalDualNorm_mul` covers the unrestricted seminorm unit ball only, while staged `affineDirectionDualNorm_add_le` covers subadditivity, not this primal-dual support inequality; LeanSearch returned Cauchy-Schwarz inner-product bounds but no affine-direction seminorm support theorem.
-- minimal hypotheses: localized boundedness of the affine-direction support set is used for the supremum comparison, `p.IsSeparating` turns `p d = 0` into `d = 0`, and the direction hypothesis is pointwise on `d`.

/-- The affine-direction dual norm bounds every feasible-direction inner product.

For a separating primal seminorm, a nonzero feasible direction can be rescaled
into the affine-direction primal unit ball. The support-function definition of
`affineDirectionDualNorm` then yields the usual primal-dual inequality.

Layer: Model | Gap: Level 1 (affine-direction primal-dual support inequality)
Proof: split on whether the primal seminorm of `d` is zero; in the nonzero
  case rescale `d` into the affine-direction primal unit ball, compare with the
  support supremum, and multiply back by the positive seminorm value.
Source: Functional analysis dual norms, support functions of seminorm unit
  balls, affine subspace direction spaces, and Hilbert-space Cauchy-Schwarz
Used in: randomized gradient extrapolation component smoothness and projected
  gradient residual estimates over feasible affine directions
Book citation: book/FOML/RandomGradientExtrapolation.json#/algorithm_spec/assumptions
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized gradient extrapolation method -/
theorem abs_inner_le_affineDirectionDualNorm_mul
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {X : Set E}
    (p : Seminorm ℝ E) (hp : p.IsSeparating) {zeta d : E}
    (h_bdd : BddAbove {r : ℝ |
      ∃ u : E, u ∈ (affineSpan ℝ X).direction ∧
        p u ≤ 1 ∧ r = |inner ℝ zeta u|})
    (hd : d ∈ (affineSpan ℝ X).direction) :
    |⟪zeta, d⟫_ℝ| ≤ affineDirectionDualNorm X p zeta * p d := by
  classical
  by_cases hd0 : p d = 0
  · have hd_zero : d = 0 := (hp d).mp hd0
    simp [hd_zero]
  · have hpd_nonneg : 0 ≤ p d := apply_nonneg p d
    have hpd_pos : 0 < p d := lt_of_le_of_ne hpd_nonneg (Ne.symm hd0)
    let u : E := (p d)⁻¹ • d
    have hu_dir : u ∈ (affineSpan ℝ X).direction := by
      exact (affineSpan ℝ X).direction.smul_mem _ hd
    have hu_le : p u ≤ 1 := by
      simp [u, map_smul_eq_mul, abs_of_pos hpd_pos, hpd_pos.ne']
    have hsup : |inner ℝ zeta u| ≤ affineDirectionDualNorm X p zeta := by
      rw [affineDirectionDualNorm_eq_sSup]
      exact le_csSup h_bdd ⟨u, hu_dir, hu_le, rfl⟩
    have hscale : |inner ℝ zeta u| = (p d)⁻¹ * |inner ℝ zeta d| := by
      simp [u, inner_smul_right, abs_mul, abs_of_pos (inv_pos.mpr hpd_pos)]
    have hinv_le :
        (p d)⁻¹ * |inner ℝ zeta d| ≤ affineDirectionDualNorm X p zeta := by
      simpa [hscale] using hsup
    calc
      |inner ℝ zeta d| = ((p d)⁻¹ * |inner ℝ zeta d|) * p d := by
        field_simp [hpd_pos.ne']
      _ ≤ affineDirectionDualNorm X p zeta * p d :=
        mul_le_mul_of_nonneg_right hinv_le hpd_pos.le

end SOptLib

-- Merged from Staging/affineDirectionDualNorm_zero.lean
open scoped InnerProductSpace

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: affine-direction dual norm zero value; orig was dualNorm_zero.
-- generality used: arbitrary carrier set in a real inner-product normed additive group, with a bundled primal seminorm; no measure, convexity, smoothness, oracle, completeness, finite-dimensionality, or separating hypothesis.
-- portable call pattern: zero residual branches in constrained stochastic-gradient and variance-reduced memory estimates call the same affine-direction support simplification while changing the carrier set, primal seminorm, and source of the residual vector.
-- counterargument checked: not paper-local traceability because this is the zero-value API for the promoted affine-direction support dual; not a caller-side pure expression because it keeps proofs from unfolding the support-function set each time; not covered by the unrestricted `canonicalDualNorm_nonneg` API.
-- coverage search: searched CATALOG/SOptLib/Staging and the algorithm file for `affineDirectionDualNorm`, `dualNorm_zero`, `zero`, and `support`; relevant hits were the defining `affineDirectionDualNorm`, `affineDirectionDualNorm_nonneg`, subadditivity, and inner-product support bounds, none stating the zero-vector equality. LeanSearch for support-function dual norm zero returned unrelated function-support and seminorm-zero lemmas, with no affine-direction seminorm support theorem.
-- minimal hypotheses: all hypotheses are needed only to state affineSpan directions and the real inner product; no boundedness, separation, or finite-dimensional control is used because the support set is exactly `{0}`.

/-- The affine-direction dual support value of the zero dual vector is zero.

When the dual vector is zero, every affine-direction support value is the single
real value `0`, so the supremum over the primal seminorm unit directions is
`0`.

Layer: Model | Gap: Level 0 (affine-direction dual norm zero value)
Proof: unfold the affine-direction support-function formula, identify the
  support set with the singleton `{0}`, and use `csSup_singleton`.
Source: Functional analysis support functions of seminorm unit balls and
  Mathlib affine subspace direction APIs
Used in: randomized gradient extrapolation zero residual branches for
  nonselected memory-gradient updates over feasible affine directions
Book citation: book/FOML/RandomGradientExtrapolation.json#/algorithm_spec/steps/4
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized gradient extrapolation method -/
@[simp]
theorem affineDirectionDualNorm_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X : Set E) (p : Seminorm ℝ E) :
    affineDirectionDualNorm X p (0 : E) = 0 := by
  rw [affineDirectionDualNorm_eq_sSup]
  have hset :
      {r : ℝ |
        ∃ d : E, d ∈ (affineSpan ℝ X).direction ∧
          p d ≤ 1 ∧ r = |⟪(0 : E), d⟫_ℝ|} = ({0} : Set ℝ) := by
    ext r
    constructor
    · intro hr
      rcases hr with ⟨d, hd_dir, hpd, rfl⟩
      simp
    · intro hr
      refine ⟨0, ?_, ?_, ?_⟩
      · exact (affineSpan ℝ X).direction.zero_mem
      · simp
      · simpa using hr
  rw [hset, csSup_singleton]

end SOptLib

-- Phase 4 batch 1 merge from Staging/dependentProductNormSq.lean
namespace SOptLib

-- Generalization plan (G0):
-- concept/name: finite dependent-product squared norm energy; orig was blockNormSq
-- generality used: finite dependent index type and a norm on each coordinate type; no measure, convexity, smoothness, oracle, group, or finite-dimensional assumptions are used
-- portable call pattern: block-coordinate, randomized coordinate, and finite-product stationarity proofs use the same coordinate energy while changing the block family, index set, and normed coordinate models
-- counterargument checked: the body is a single finite sum, but it names the reusable product-coordinate energy that recurs in stationarity and sampling bounds; Mathlib's closest PiLp norm-square identity describes an ambient PiLp norm rather than this raw dependent-coordinate energy definition
-- coverage search: queried "finite dependent product squared norm equals sum coordinate squared norms", "dependent product norm square finite sum coordinate norms", and "dependentProductNormSq"; hits included PiLp.norm_sq_eq_of_L2, expectedRootSumSqNorm, and finite weighted squared-norm inequalities, but no full duplicate definition of the raw dependent product energy
-- minimal hypotheses: strengthened source assumptions were dropped to [Fintype i] and coordinate [Norm]; all remaining assumptions are needed to form the finite sum of squared coordinate norms

/-- The finite coordinate energy of a dependent product, given by the sum of
squared coordinate norms.

Layer: Model | Concept: finite dependent-product squared norm energy
Proof: (definitional construction; finite sum over all coordinate squared norms)
Source: Mathlib finite sums and norm notation for finite dependent products
Used in: stochastic block mirror descent stationarity and sampled-block descent
  bounds that compare a full product certificate with coordinate certificates
Book citation: book/FOML/NonconvexStochasticBlockMirrorDescent.json#/assumptions/5
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic block mirror descent -/
noncomputable def dependentProductNormSq
    {ι : Type*} [Fintype ι]
    {Block : ι → Type*} [∀ i, Norm (Block i)]
    (x : ∀ i, Block i) : ℝ :=
  ∑ i, ‖x i‖ ^ 2

/-- The finite dependent-product squared norm energy unfolds to the sum of
squared coordinate norms.

Layer: Model | Gap: Level 0 (finite dependent-product norm-square unfolding)
Proof: by rfl after unfolding `dependentProductNormSq`.
Source: Mathlib finite sums and norm notation for finite dependent products
Used in: stochastic block mirror descent proofs that rewrite the named product
  stationarity certificate into coordinate-wise squared norm sums
Book citation: book/FOML/NonconvexStochasticBlockMirrorDescent.json#/assumptions/5
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic block mirror descent -/
@[simp]
theorem dependentProductNormSq_def
    {ι : Type*} [Fintype ι]
    {Block : ι → Type*} [∀ i, Norm (Block i)]
    (x : ∀ i, Block i) :
    dependentProductNormSq x = ∑ i, ‖x i‖ ^ 2 := by
  rfl

/-- Compatibility spelling for the finite dependent-product squared norm
energy unfolding. -/
theorem dependentProductNormSq_eq_sum
    {ι : Type*} [Fintype ι]
    {Block : ι → Type*} [∀ i, Norm (Block i)]
    (x : ∀ i, Block i) :
    dependentProductNormSq x = ∑ i, ‖x i‖ ^ 2 :=
  dependentProductNormSq_def x

/-- The finite dependent-product squared norm energy is nonnegative. -/
theorem dependentProductNormSq_nonneg
    {ι : Type*} [Fintype ι]
    {Block : ι → Type*} [∀ i, SeminormedAddGroup (Block i)]
    (x : ∀ i, Block i) :
    0 ≤ dependentProductNormSq x := by
  rw [dependentProductNormSq_def]
  exact Finset.sum_nonneg fun i _ => sq_nonneg ‖x i‖

/-- The finite dependent-product squared norm energy is monotone under
coordinatewise norm domination. -/
theorem dependentProductNormSq_le_of_norm_le
    {ι : Type*} [Fintype ι]
    {Block : ι → Type*} [∀ i, SeminormedAddGroup (Block i)]
    {x y : ∀ i, Block i}
    (h : ∀ i, ‖x i‖ ≤ ‖y i‖) :
    dependentProductNormSq x ≤ dependentProductNormSq y := by
  rw [dependentProductNormSq_def, dependentProductNormSq_def]
  exact Finset.sum_le_sum fun i _ =>
    sq_le_sq'
      (le_trans (neg_nonpos.mpr (norm_nonneg (y i))) (norm_nonneg (x i)))
      (h i)

end SOptLib

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: twoBlockScaledProductNorm exposes the scaled two-block primal product seminorm; orig was sourceProductNorm.
-- generality used: two arbitrary real normed vector additive groups, bundled component seminorms, two real scale constants, and a `WithLp 2` product vector; no measure, finite-dimensional, inner-product, convexity, smoothness, oracle, or boundedness assumptions are used.
-- portable call pattern: two-block saddle-point, mirror-descent, and primal-dual algorithms can name the same product primal norm while changing component spaces, component seminorms, and diameter scales.
-- counterargument checked: not paper-local traceability because the diameter-scaled product seminorm is reused by product DGF normalization, residual uniqueness, continuity, integrability, and oracle Cauchy-Schwarz steps; not merely a caller-side expression because it gives the primal counterpart of the approved two-block scaled product dual norm a stable Model name and formula API.
-- coverage search: searched `two block scaled product norm square root seminorm diameter` and `weighted two block gauge square root component functions continuous`; top hits were `twoBlockScaledProductDualNorm`, `twoBlockDualGauge`, and `twoBlockScaledProductNorm_sq_nonpos_eq_zero`, all dual-gauge or theorem-only APIs and none defining the primal scaled product norm.
-- minimal hypotheses: finite-dimensional and inner-product assumptions were dropped; the remaining real vector-space structure is needed by `Seminorm ℝ`, and the normed additive group structure supports the `WithLp 2` product space used at call sites.

/-- The scaled two-block product seminorm built from component primal seminorms.

For component seminorms `pX` and `pY`, this is the square root of the sum of
the two component squared seminorms divided by the squared diameter scales
`2 * DX^2` and `2 * DY^2`.

Layer: Model | Concept: scaled two-block primal product seminorm
Proof: (definitional construction; square root of the sum of two diameter-scaled
  component seminorm squares on a `WithLp` product)
Source: Functional analysis product seminorms, weighted product norms, Mathlib
  seminorm API, and `WithLp` product projections
Used in: stochastic convex-concave saddle-point mirror descent when the product
  residual is measured by the scaled primal norm induced by two component
  seminorms and diameter constants
Book citation: book/FOML/StochasticConvexConcaveSaddlePoint.json#/assumptions/6
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent for stochastic convex-concave
  saddle point problems -/
noncomputable def twoBlockScaledProductNorm
    {EX EY : Type*}
    [AddCommGroup EX] [Module ℝ EX]
    [AddCommGroup EY] [Module ℝ EY]
    (pX : Seminorm ℝ EX) (pY : Seminorm ℝ EY)
    (DX DY : ℝ) (z : WithLp 2 (EX × EY)) : ℝ :=
  Real.sqrt
    ((pX z.fst) ^ 2 / (2 * DX ^ 2) +
      (pY z.snd) ^ 2 / (2 * DY ^ 2))

/-- The defining square-root formula for the scaled two-block product seminorm.

Layer: Model | Gap: Level 0 (scaled two-block primal product seminorm formula)
Proof: by rfl after unfolding `twoBlockScaledProductNorm`.
Source: Functional analysis product seminorms, weighted product norms, Mathlib
  seminorm API, and `WithLp` product projections
Used in: stochastic convex-concave saddle-point mirror descent when rewriting
  the named product primal norm to the displayed square-root sum of scaled
  component seminorms
Book citation: book/FOML/StochasticConvexConcaveSaddlePoint.json#/assumptions/6
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent for stochastic convex-concave
  saddle point problems -/
@[simp]
theorem twoBlockScaledProductNorm_def
    {EX EY : Type*}
    [AddCommGroup EX] [Module ℝ EX]
    [AddCommGroup EY] [Module ℝ EY]
    (pX : Seminorm ℝ EX) (pY : Seminorm ℝ EY)
    (DX DY : ℝ) (z : WithLp 2 (EX × EY)) :
    twoBlockScaledProductNorm pX pY DX DY z =
      Real.sqrt
        ((pX z.fst) ^ 2 / (2 * DX ^ 2) +
          (pY z.snd) ^ 2 / (2 * DY ^ 2)) := by
  rfl

-- Generalization plan (G0):
-- concept/name: twoBlockScaledProductDualNorm exposes the scaled two-block canonical product dual norm; orig was productDualNorm.
-- generality used: two arbitrary real Hilbert blocks, bundled component primal seminorms, two real scale constants, and a `WithLp 2` product dual vector; no measure, finite-dimensional, convexity, smoothness, oracle, or boundedness assumptions are used.
-- portable call pattern: two-block stochastic saddle-point, mirror-descent, and primal-dual algorithms can name the same product dual norm while changing component spaces, component seminorms, and diameter scales.
-- counterargument checked: not paper-local traceability because the canonical-dual specialization recurs in product-space oracle bounds; not merely a caller-side expression because it gives the product dual norm a stable Model name and immediate formula API; `twoBlockDualGauge` is a reusable generic ingredient but does not expose the canonical-dual product norm specialization.
-- coverage search: searched `two block scaled product dual norm canonical dual norm square root weighted sum` and `product dual gauge canonical dual norm WithLp fst snd weights`; top hits were `SOptLib.twoBlockDualGauge`, `SOptLib.canonicalDualNorm`, `SOptLib.twoBlockSignedDualNorm_sq`, and canonical dual-norm API, all partial and none defining the unsigned scaled canonical product dual norm.
-- minimal hypotheses: all already minimal for `canonicalDualNorm` on each block and `WithLp` product projections; no finite-dimensional, separating, measurability, probability, positivity, or support-boundedness hypotheses are needed for the definition or formula theorem.

/-- The scaled two-block product dual norm built from component canonical dual norms.

For component primal seminorms `pX` and `pY`, this is the weighted product
dual gauge on `WithLp 2 (EX × EY)` with weights `2 * DX^2` and `2 * DY^2`.

Layer: Model | Concept: scaled two-block canonical product dual norm
Proof: (definitional construction; specialization of the weighted two-block
  dual gauge to `WithLp` product projections and component canonical dual norms)
Source: Functional analysis product dual norms, support-function dual norms,
  Mathlib `WithLp` product projections, and weighted product gauges
Used in: stochastic convex-concave saddle-point mirror descent when the product
  oracle is measured by the scaled dual norm induced by the two component
  primal seminorms and diameter constants
Book citation: book/FOML/StochasticConvexConcaveSaddlePoint.json#/assumptions/6
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent for stochastic convex-concave
  saddle point problems -/
noncomputable def twoBlockScaledProductDualNorm
    {EX EY : Type*}
    [NormedAddCommGroup EX] [InnerProductSpace ℝ EX]
    [NormedAddCommGroup EY] [InnerProductSpace ℝ EY]
    (pX : Seminorm ℝ EX) (pY : Seminorm ℝ EY)
    (DX DY : ℝ) (zeta : WithLp 2 (EX × EY)) : ℝ :=
  Real.sqrt
    (2 * DX ^ 2 * (canonicalDualNorm pX zeta.fst) ^ 2 +
      2 * DY ^ 2 * (canonicalDualNorm pY zeta.snd) ^ 2)

/-- The defining square-root formula for the scaled two-block product dual norm.

Layer: Model | Gap: Level 0 (scaled two-block canonical product dual norm formula)
Proof: by rfl after unfolding `twoBlockScaledProductDualNorm` and
  `twoBlockDualGauge`.
Source: Functional analysis product dual norms, support-function dual norms,
  Mathlib `WithLp` product projections, and weighted product gauges
Used in: stochastic convex-concave saddle-point mirror descent when rewriting
  the named product dual norm to the displayed square-root sum of scaled
  component canonical dual norms
Book citation: book/FOML/StochasticConvexConcaveSaddlePoint.json#/assumptions/6
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent for stochastic convex-concave
  saddle point problems -/
@[simp]
theorem twoBlockScaledProductDualNorm_def
    {EX EY : Type*}
    [NormedAddCommGroup EX] [InnerProductSpace ℝ EX]
    [NormedAddCommGroup EY] [InnerProductSpace ℝ EY]
    (pX : Seminorm ℝ EX) (pY : Seminorm ℝ EY)
    (DX DY : ℝ) (zeta : WithLp 2 (EX × EY)) :
    twoBlockScaledProductDualNorm pX pY DX DY zeta =
      Real.sqrt
        (2 * DX ^ 2 * (canonicalDualNorm pX zeta.fst) ^ 2 +
          2 * DY ^ 2 * (canonicalDualNorm pY zeta.snd) ^ 2) := by
  rfl


-- Generalization plan (G0):
-- concept/name: twoBlockScaledProductNorm_continuous exposes continuity of the scaled two-block primal product seminorm; orig was productNorm_continuous.
-- generality used: two arbitrary real normed vector additive groups, bundled component seminorms, two real scale constants, and component continuity hypotheses; no measure, finite-dimensionality, inner-product, convexity, smoothness, oracle, or boundedness assumptions are used.
-- portable call pattern: two-block saddle-point, mirror-descent, and primal-dual algorithms proving measurability or integrability of residual gauges can call the same statement while changing component spaces, seminorms, and diameter scales.
-- counterargument checked: not paper-local traceability because the continuity step recurs whenever a scaled product seminorm is composed with random queries or compact product points; not merely a caller-side expression because it packages the product projections, square/division algebra, and square-root continuity around the named product norm; existing entries provide the product norm definition and finite-dimensional seminorm continuity but not this product-gauge continuity theorem.
-- coverage search: searched `two block scaled product norm continuous positive radii seminorm finite dimensional`, `seminorm continuous finite dimensional`, and LeanSearch `continuity of square root of sum of squares divided by constants of continuous seminorms on product`; top hits were `SOptLib.twoBlockScaledProductNorm`, `Seminorm.continuous_of_finiteDimensional`, `twoBlockScaledProductDualNorm_continuous`, and Mathlib `Continuous.sqrt`, all partial rather than this primal product continuity statement.
-- minimal hypotheses: finite-dimensionality is replaced by pointwise component continuity, inner-product assumptions are dropped, and positive scale assumptions are omitted because division by a fixed real constant preserves continuity even when the constant is zero.

/-- Continuity of the scaled two-block product seminorm from continuity of the
component seminorms.

For component seminorms `pX` and `pY`, the named product gauge is continuous on
the `WithLp 2` product whenever both component gauges are continuous.

Layer: Model | Gap: Level 1 (scaled two-block primal product seminorm continuity)
Proof: compose component seminorm continuity with the two `WithLp` projections,
  close the squared and diameter-scaled radicand by real continuity rules, then
  compose with real square-root continuity.
Source: Mathlib seminorm continuity API, real square-root continuity, algebraic
  continuity rules, and `WithLp` product projections
Used in: stochastic convex-concave saddle-point mirror descent measurability
  and compactness arguments for product-residual gauges built from component
  primal seminorms
Book citation: book/FOML/StochasticConvexConcaveSaddlePoint.json#/assumptions/6
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent for stochastic convex-concave
  saddle point problems -/
theorem twoBlockScaledProductNorm_continuous
    {EX EY : Type*}
    [NormedAddCommGroup EX] [NormedSpace ℝ EX]
    [NormedAddCommGroup EY] [NormedSpace ℝ EY]
    (pX : Seminorm ℝ EX) (pY : Seminorm ℝ EY)
    (DX DY : ℝ)
    (hpX : Continuous (fun x : EX => pX x))
    (hpY : Continuous (fun y : EY => pY y)) :
    Continuous
      (fun z : WithLp 2 (EX × EY) => twoBlockScaledProductNorm pX pY DX DY z) := by
  have hx :
      Continuous (fun z : WithLp 2 (EX × EY) => (pX z.fst) ^ 2) :=
    (hpX.comp (WithLp.continuous_fst 2 EX EY)).pow 2
  have hy :
      Continuous (fun z : WithLp 2 (EX × EY) => (pY z.snd) ^ 2) :=
    (hpY.comp (WithLp.continuous_snd 2 EX EY)).pow 2
  have hrad :
      Continuous (fun z : WithLp 2 (EX × EY) =>
        (pX z.fst) ^ 2 / (2 * DX ^ 2) +
          (pY z.snd) ^ 2 / (2 * DY ^ 2)) :=
    (hx.div_const (2 * DX ^ 2)).add (hy.div_const (2 * DY ^ 2))
  simpa [twoBlockScaledProductNorm] using Real.continuous_sqrt.comp hrad

-- Generalization plan (G0):
-- concept/name: two-block scaled product primal-dual support inequality; orig was twoBlockScaledProductDualNorm_mul_productNorm_support.
-- generality used: two arbitrary real Hilbert blocks, component primal seminorms, separating hypotheses, localized boundedness of each canonical-dual support set, positive block radii, and arbitrary product dual/primal vectors; no measure, convexity, smoothness, oracle, algorithm state, completeness, or finite-dimensionality assumptions are used.
-- portable call pattern: two-block saddle-point, mirror-descent, and primal-dual proofs call this when converting a product-space oracle inner product into the scaled product dual norm times the scaled product primal norm while changing component spaces, seminorms, radii, oracle vector `zeta`, and displacement `d`.
-- counterargument checked: not paper-local traceability because it packages the recurring product primal-dual Cauchy/support step for named scaled product gauges; not a pure wrapper because it composes two component support inequalities, product inner splitting, and weighted two-term Cauchy algebra; existing `abs_inner_le_canonicalDualNorm_mul` covers one block only and Mathlib Cauchy lemmas do not know the SOptLib product gauges.
-- coverage search: searched `two block scaled product dual norm bounds inner product by product norm separating seminorm`, `weighted two term product Cauchy square root inequality`, and LeanSearch for the weighted two-term square-root inequality; top hits were `SOptLib.abs_inner_le_canonicalDualNorm_mul`, `SOptLib.twoBlockScaledProductDualNorm`, `SOptLib.twoBlockScaledProductNorm`, Mathlib `Real.sum_mul_le_sqrt_mul_sqrt`, and the target-file private scalar lemma, all partial rather than this product support statement.
-- minimal hypotheses: finite-dimensionality was replaced by explicit per-vector support-set boundedness; separating hypotheses are only used through the component canonical-dual support inequality; positive radii are exactly needed for the weighted scalar Cauchy step.

/-- The scaled two-block product dual norm bounds product inner products.

For separating component seminorms, component canonical-dual support bounds
assemble into the primal-dual inequality for the named scaled two-block product
dual norm and scaled two-block product primal seminorm.

Layer: Model | Gap: Level 1 (scaled two-block product primal-dual support inequality)
Proof: apply the component canonical-dual support inequality in each block,
  split the `WithLp 2` product inner product into two absolute values, and
  close with the weighted two-term Cauchy inequality matching the scaled gauges.
Source: Functional analysis dual norms, support functions of seminorm unit
  balls, Mathlib real Hilbert product inner products, and weighted Cauchy
  inequalities
Used in: stochastic convex-concave saddle-point mirror descent when bounding
  oracle-noise and mean-oracle product pairings by product dual and primal
  gauges before integrability and regret estimates
Book citation: book/FOML/StochasticConvexConcaveSaddlePoint.json#/key_lemmas/0
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent for stochastic convex-concave
  saddle point problems -/
theorem abs_inner_le_twoBlockScaledProductDualNorm_mul_twoBlockScaledProductNorm
    {EX EY : Type*}
    [NormedAddCommGroup EX] [InnerProductSpace ℝ EX]
    [NormedAddCommGroup EY] [InnerProductSpace ℝ EY]
    (pX : Seminorm ℝ EX) (pY : Seminorm ℝ EY)
    (hpX : pX.IsSeparating) (hpY : pY.IsSeparating)
    {DX DY : ℝ}
    (zeta d : WithLp 2 (EX × EY))
    (hX_bdd : BddAbove {r : ℝ | ∃ u : EX, pX u ≤ 1 ∧ r = |inner ℝ zeta.fst u|})
    (hY_bdd : BddAbove {r : ℝ | ∃ u : EY, pY u ≤ 1 ∧ r = |inner ℝ zeta.snd u|})
    (hDX : 0 < DX) (hDY : 0 < DY) :
    |⟪zeta, d⟫_ℝ| ≤
      twoBlockScaledProductDualNorm pX pY DX DY zeta *
        twoBlockScaledProductNorm pX pY DX DY d := by
  let ux : ℝ := canonicalDualNorm pX zeta.fst
  let uy : ℝ := canonicalDualNorm pY zeta.snd
  let px : ℝ := pX d.fst
  let py : ℝ := pY d.snd
  have hx_support :
      |⟪zeta.fst, d.fst⟫_ℝ| ≤ ux * px := by
    simpa [ux, px] using
      (abs_inner_le_canonicalDualNorm_mul
        pX hpX (zeta := zeta.fst) (d := d.fst) hX_bdd)
  have hy_support :
      |⟪zeta.snd, d.snd⟫_ℝ| ≤ uy * py := by
    simpa [uy, py] using
      (abs_inner_le_canonicalDualNorm_mul
        pY hpY (zeta := zeta.snd) (d := d.snd) hY_bdd)
  have hsplit :
      |⟪zeta, d⟫_ℝ| ≤ |⟪zeta.fst, d.fst⟫_ℝ| + |⟪zeta.snd, d.snd⟫_ℝ| := by
    rw [WithLp.prod_inner_apply]
    exact abs_add_le _ _
  have hcomponent :
      |⟪zeta, d⟫_ℝ| ≤ ux * px + uy * py :=
    hsplit.trans (add_le_add hx_support hy_support)
  have hweighted :
      ux * px + uy * py ≤
        twoBlockScaledProductDualNorm pX pY DX DY zeta *
          twoBlockScaledProductNorm pX pY DX DY d := by
    have weighted_two_term_mul_le_sqrt :
        ∀ {a b c d α β : ℝ},
          0 ≤ a → 0 ≤ b → 0 ≤ c → 0 ≤ d → 0 < α → 0 < β →
            a * c + b * d ≤
              Real.sqrt (α * a ^ 2 + β * b ^ 2) *
                Real.sqrt (c ^ 2 / α + d ^ 2 / β) := by
      intro a b c d α β ha hb hc hd hα hβ
      have hleft_nonneg : 0 ≤ a * c + b * d :=
        add_nonneg (mul_nonneg ha hc) (mul_nonneg hb hd)
      have hrad1_nonneg : 0 ≤ α * a ^ 2 + β * b ^ 2 := by
        exact add_nonneg (mul_nonneg (le_of_lt hα) (sq_nonneg a))
          (mul_nonneg (le_of_lt hβ) (sq_nonneg b))
      have hrad2_nonneg : 0 ≤ c ^ 2 / α + d ^ 2 / β := by
        exact add_nonneg (div_nonneg (sq_nonneg c) (le_of_lt hα))
          (div_nonneg (sq_nonneg d) (le_of_lt hβ))
      have hright_nonneg :
          0 ≤ Real.sqrt (α * a ^ 2 + β * b ^ 2) *
            Real.sqrt (c ^ 2 / α + d ^ 2 / β) :=
        mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      rw [← sq_le_sq₀ hleft_nonneg hright_nonneg]
      rw [mul_pow, Real.sq_sqrt hrad1_nonneg, Real.sq_sqrt hrad2_nonneg]
      have hα_ne : α ≠ 0 := ne_of_gt hα
      have hβ_ne : β ≠ 0 := ne_of_gt hβ
      field_simp [hα_ne, hβ_ne]
      nlinarith [sq_nonneg (α * a * d - β * b * c)]
    have hDX' : 0 < 2 * DX ^ 2 := by
      nlinarith
    have hDY' : 0 < 2 * DY ^ 2 := by
      nlinarith
    have h :=
      weighted_two_term_mul_le_sqrt
        (a := ux) (b := uy) (c := px) (d := py)
        (α := 2 * DX ^ 2) (β := 2 * DY ^ 2)
        (canonicalDualNorm_nonneg pX zeta.fst)
        (canonicalDualNorm_nonneg pY zeta.snd)
        (apply_nonneg pX d.fst)
        (apply_nonneg pY d.snd)
        hDX' hDY'
    simpa [twoBlockScaledProductDualNorm_def, twoBlockScaledProductNorm_def, ux, uy, px, py] using h
  exact hcomponent.trans hweighted

end SOptLib


-- Phase 4 batch 2 merge from .sgd_phase3_staging/SOptLib/Model/canonicalDualNorm_neg.lean
open scoped InnerProductSpace

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: negation invariance of the canonical support-function dual norm; orig was canonicalDualNorm_neg and the name is already concept-derived.
-- generality used: real Hilbert-space carrier with NormedAddCommGroup and InnerProductSpace, a bundled Seminorm, and a pointwise dual vector; no measure, convexity, smoothness, oracle, finite-dimensional, or boundedness hypotheses.
-- portable call pattern: stochastic mirror-descent and saddle-point oracle estimates can replace a negated residual, gradient, or concave-block oracle by the same canonical dual norm; the seminorm and vector source change while the equality stays unchanged.
-- counterargument checked: not paper-local traceability because it is API for the SOptLib canonicalDualNorm definition; not a caller-side expression because callers should not unfold the support-function set to normalize a sign; not a duplicate of Mathlib inner_neg_left because that only rewrites the inner-product integrand.
-- coverage search: searched "canonical dual norm negation invariant seminorm support function" and "support function absolute inner product neg equals"; top SOptLib hits were canonicalDualNorm_eq_sSup, canonicalDualNorm_add_le, and canonicalDualNorm_nonneg, none stating negation invariance. LeanSearch found Mathlib inner_neg_left/inner_neg_right only, which are proof ingredients rather than the canonicalDualNorm statement.
-- minimal hypotheses: all already minimal for SOptLib.canonicalDualNorm; no finite-dimensional, separating, boundedness, measurability, or probability assumptions are used.

/-- Negating the dual vector does not change the canonical dual norm induced by a
primal seminorm.

For the support-function dual norm over a primal seminorm unit ball, the support
set is unchanged by negating the dual vector because every support value is the
absolute value of an inner product.

Layer: Model | Gap: Level 0 (canonical dual norm sign invariance)
Proof: unfold the canonical dual norm to its support-function formula, prove the
  defining support sets equal by extensionality, and use inner-product negation
  together with absolute-value symmetry.
Source: Functional analysis support functions of seminorm unit balls and
  Mathlib real Hilbert-space inner-product sign rules
Used in: stochastic convex-concave saddle-point oracle second-moment estimates
  when the concave-block oracle is represented with a negative sign
Book citation: book/FOML/StochasticConvexConcaveSaddlePoint.json#/assumptions/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent for stochastic convex-concave
  saddle point problems -/
theorem canonicalDualNorm_neg
    {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℝ B]
    (p : Seminorm ℝ B) (v : B) :
    canonicalDualNorm p (-v) = canonicalDualNorm p v := by
  rw [canonicalDualNorm_eq_sSup, canonicalDualNorm_eq_sSup]
  congr 1
  ext r
  constructor
  · rintro ⟨d, hd, rfl⟩
    refine ⟨d, hd, ?_⟩
    simp
  · rintro ⟨d, hd, rfl⟩
    refine ⟨d, hd, ?_⟩
    simp

end SOptLib


-- Phase 4 batch 2 merge from .sgd_phase3_staging/SOptLib/Model/canonicalDualNorm_sub_sq_le_two_mul_sq_add_two_mul_sq.lean
open scoped InnerProductSpace

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: canonical dual norm squared subtraction split; orig was canonicalDualNorm_sub_sq_le_two_sq_add_two_sq_block.
-- generality used: real Hilbert-space carrier with NormedAddCommGroup and InnerProductSpace, a bundled Seminorm, two dual vectors, and localized boundedness of the two support sets used by subadditivity; no finite-dimensional, separating, measure, convexity, smoothness, oracle, or algorithm state assumptions.
-- portable call pattern: stochastic oracle residual and mean-deviation proofs split a centered dual vector into a sampled term and deterministic mean term while changing the seminorm, vectors, and support-boundedness witnesses but keeping the same squared dual-norm estimate.
-- counterargument checked: not paper-local traceability because this is the Young-type square split for the named canonical support-function dual norm; not a pure wrapper because it packages canonicalDualNorm subadditivity, sign invariance, nonnegativity, and scalar square algebra; not covered by Mathlib ambient norm inequalities or the affine-direction dual-norm square lemma.
-- coverage search: searched CATALOG/SOptLib/Staging and lean_search_symbols for `canonical dual norm squared triangle inequality subtraction two times squares` and `canonicalDualNorm sub square less equal two canonicalDualNorm square add`; top hits were SOptLib.canonicalDualNorm_add_le, SOptLib.canonicalDualNorm_neg, SOptLib.canonicalDualNorm_nonneg, and SOptLib.affineDirectionDualNorm_add_sq_le_two_mul_sq_add_two_mul_sq, none stating this unrestricted canonical subtraction square split. LeanSearch for `square of subadditive nonnegative function bounded by twice squares of arguments` found Mathlib.add_sq_le as scalar algebra only.
-- minimal hypotheses: all algorithm-specific finite-dimensional and separating assumptions are replaced by the pointwise BddAbove hypotheses required by SOptLib.canonicalDualNorm_add_le; support boundedness is required for `a` and `-b`.

/-- The squared canonical dual norm of a difference is bounded by twice the
split squared dual norms.

This is the support-dual analogue of the usual two-term Young bound
`‖a - b‖^2 ≤ 2‖a‖^2 + 2‖b‖^2`, specialized to the canonical dual norm induced
by a primal seminorm.

Layer: Model | Gap: Level 1 (canonical dual norm square split)
Proof: apply canonical dual-norm subadditivity to `a + (-b)`, normalize the
  sign of the second term, square using nonnegativity of the support dual, and
  finish with the real square inequality `(x + y)^2 ≤ 2*x^2 + 2*y^2`.
Source: Functional analysis dual norms, support functions of seminorm unit
  balls, and Mathlib real Young inequalities
Used in: stochastic convex-concave saddle-point oracle residual estimates
  splitting a centered block oracle into sampled and mean dual-norm terms
Book citation: book/FOML/StochasticConvexConcaveSaddlePoint.json#/key_lemmas/0
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent for stochastic convex-concave
  saddle point problems -/
theorem canonicalDualNorm_sub_sq_le_two_mul_sq_add_two_mul_sq
    {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℝ B]
    (p : Seminorm ℝ B) (a b : B)
    (ha : BddAbove {r : ℝ | ∃ u : B, p u ≤ 1 ∧ r = |inner ℝ a u|})
    (hb : BddAbove {r : ℝ | ∃ u : B, p u ≤ 1 ∧ r = |inner ℝ (-b) u|}) :
    canonicalDualNorm p (a - b) ^ 2 ≤
      2 * canonicalDualNorm p a ^ 2 + 2 * canonicalDualNorm p b ^ 2 := by
  have hsub :
      canonicalDualNorm p (a - b) ≤
        canonicalDualNorm p a + canonicalDualNorm p (-b) := by
    simpa [sub_eq_add_neg] using
      canonicalDualNorm_add_le (p := p) (zeta := a) (eta := -b) ha hb
  have hnonneg : 0 ≤ canonicalDualNorm p (a - b) :=
    canonicalDualNorm_nonneg p (a - b)
  have hsq :
      canonicalDualNorm p (a - b) ^ 2 ≤
        (canonicalDualNorm p a + canonicalDualNorm p (-b)) ^ 2 := by
    nlinarith [hsub, hnonneg]
  have hsplit :
      (canonicalDualNorm p a + canonicalDualNorm p (-b)) ^ 2 ≤
        2 * canonicalDualNorm p a ^ 2 + 2 * canonicalDualNorm p (-b) ^ 2 := by
    nlinarith [sq_nonneg (canonicalDualNorm p a - canonicalDualNorm p (-b))]
  simpa [canonicalDualNorm_neg] using hsq.trans hsplit

end SOptLib


-- Phase 4 batch 2 merge from .sgd_phase3_staging/SOptLib/Model/twoBlockOracleSecondMomentScale.lean
namespace SOptLib

-- Generalization plan (G0):
-- concept/name: two-block oracle second-moment scale; orig was M and the staged name exposes the product-oracle scale whose square is the weighted sum of the two component moment budgets.
-- generality used: four real scalar parameters DX DY MX MY only; no carrier, measure, oracle, convexity, smoothness, topology, Hilbert, or finite-dimensional assumptions are needed for the scalar construction and its square/positivity API.
-- portable call pattern: stochastic mirror descent, mirror-prox, and primal-dual block algorithms combine component diameter scales and component oracle second-moment bounds into the same product-space second-moment scale while changing the oracle kernels, feasible sets, and component norms.
-- counterargument checked: not paper-local traceability because the scale is the reusable scalar endpoint for two-block oracle moment estimates and constant stepsize choices; not a duplicate of existing SOptLib block-oracle second-moment theorems, which consume a supplied scalar M but do not define the two-block product scale.
-- coverage search: searched "two block oracle second moment scale square positive" and "Real.sqrt sum weighted squares square equals radicand positive"; top hits were blockOracleSecondMoment_le_sq, blockOracleSecondMomentExpectation, and two_block_oracle_exponential_moment_bound, all partial because they cover moment hypotheses or exponential tails rather than this scalar product scale.
-- minimal hypotheses: the definition and square formula need no hypotheses because the radicand is a sum of nonnegative square terms; strict positivity needs exactly strict positivity of DX, DY, MX, and MY.

/-- The scalar two-block product-oracle second-moment scale.

It is the square root of the weighted sum
`2 * DX^2 * MX^2 + 2 * DY^2 * MY^2`, so it packages the product-space
constant whose square bounds the combined oracle second moment.

Layer: Model | Concept: two-block oracle second-moment scale
Proof: (definitional construction; square root of the weighted sum of two component diameter-square and moment-square products)
Source: Mathlib real square-root arithmetic and weighted product dual-norm formulas
Used in: stochastic convex-concave saddle-point mirror descent when combining the two component oracle second-moment budgets into the product-dual moment constant used by the constant stepsize
Book citation: book/FOML/StochasticConvexConcaveSaddlePoint.json#/assumptions/7
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic mirror descent for stochastic convex-concave saddle point problems -/
noncomputable def twoBlockOracleSecondMomentScale
    (DX DY MX MY : ℝ) : ℝ :=
  Real.sqrt (2 * DX ^ 2 * MX ^ 2 + 2 * DY ^ 2 * MY ^ 2)

/-- Definitional formula for the two-block oracle second-moment scale.

Layer: Model | Gap: Level 0 (two-block oracle second-moment scale formula)
Proof: by rfl after unfolding twoBlockOracleSecondMomentScale.
Source: Mathlib real square-root arithmetic and weighted product dual-norm formulas
Used in: stochastic convex-concave saddle-point mirror descent when rewriting the staged product-oracle moment scale to the displayed paper formula
Book citation: book/FOML/StochasticConvexConcaveSaddlePoint.json#/assumptions/7
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic mirror descent for stochastic convex-concave saddle point problems -/
@[simp]
theorem twoBlockOracleSecondMomentScale_def
    (DX DY MX MY : ℝ) :
    twoBlockOracleSecondMomentScale DX DY MX MY =
      Real.sqrt (2 * DX ^ 2 * MX ^ 2 + 2 * DY ^ 2 * MY ^ 2) := by
  rfl

/-- The square of the two-block oracle second-moment scale is its radicand.

Layer: Model | Gap: Level 0 (two-block oracle second-moment scale square formula)
Proof: apply `Real.sq_sqrt`; the radicand is nonnegative by positivity of squares.
Source: Mathlib real square-root arithmetic and ordered-ring square nonnegativity
Used in: stochastic convex-concave saddle-point mirror descent when replacing the product oracle moment bound `M^2` by the component expression
Book citation: book/FOML/StochasticConvexConcaveSaddlePoint.json#/assumptions/7
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic mirror descent for stochastic convex-concave saddle point problems -/
@[simp]
theorem twoBlockOracleSecondMomentScale_sq
    (DX DY MX MY : ℝ) :
    twoBlockOracleSecondMomentScale DX DY MX MY ^ 2 =
      2 * DX ^ 2 * MX ^ 2 + 2 * DY ^ 2 * MY ^ 2 := by
  exact Real.sq_sqrt (by positivity)

/-- The two-block oracle second-moment scale is positive under positive component scales.

Layer: Model | Gap: Level 0 (two-block oracle second-moment scale positivity)
Proof: prove both weighted square terms are strictly positive and apply real square-root positivity to their sum.
Source: Mathlib real square-root arithmetic and ordered-ring positivity for products of squares
Used in: stochastic convex-concave saddle-point mirror descent when using the product oracle scale in denominators and constant stepsize formulas
Book citation: book/FOML/StochasticConvexConcaveSaddlePoint.json#/assumptions/7
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic mirror descent for stochastic convex-concave saddle point problems -/
theorem twoBlockOracleSecondMomentScale_pos
    {DX DY MX MY : ℝ}
    (hDX : 0 < DX) (hDY : 0 < DY) (hMX : 0 < MX) (hMY : 0 < MY) :
    0 < twoBlockOracleSecondMomentScale DX DY MX MY := by
  rw [twoBlockOracleSecondMomentScale]
  apply Real.sqrt_pos_of_pos
  have hXterm : 0 < 2 * DX ^ 2 * MX ^ 2 := by
    exact mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) (sq_pos_of_pos hDX))
      (sq_pos_of_pos hMX)
  have hYterm : 0 < 2 * DY ^ 2 * MY ^ 2 := by
    exact mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) (sq_pos_of_pos hDY))
      (sq_pos_of_pos hMY)
  exact add_pos hXterm hYterm

end SOptLib


-- Phase 4 batch 2 merge from .sgd_phase3_staging/SOptLib/Model/twoBlockScaledProductDualNorm_sq_toLp_neg_right.lean
open scoped InnerProductSpace

namespace SOptLib

-- Generalization plan (G0):
-- concept/name: two-block scaled product dual norm square formula for a right-negated `WithLp.toLp` pair; orig was productDualNorm_sq_stochasticOracle_eq.
-- generality used: two arbitrary real Hilbert blocks, bundled component primal seminorms, arbitrary real scale constants, and pointwise component dual vectors; no measure, stochastic oracle, finite-dimensional, convexity, smoothness, boundedness, or positivity assumptions are used.
-- portable call pattern: two-block saddle-point and primal-dual stochastic mirror-descent proofs square the scaled product dual norm of a signed oracle/residual while changing component spaces, component seminorms, scale constants, and pointwise component vectors.
-- counterargument checked: not paper-local traceability because the signed second block is the standard saddle-product convention; not a caller-side expression because it packages the named product dual norm's square-root normalization with canonical-dual sign invariance; `twoBlockSignedDualNorm_sq` is the lower-level generic-gauge analogue, while this statement is over the approved named `twoBlockScaledProductDualNorm`.
-- coverage search: searched `scaled product dual norm square two block toLp negative right equals component dual norm squares` and `twoBlockScaledProductDualNorm square WithLp toLp gx negative gy equals scaled sum canonicalDualNorm squares`; top hits were `twoBlockScaledProductDualNorm_def`, `twoBlockScaledProductDualNorm`, lower-level `twoBlockSignedDualNorm_sq`, `canonicalDualNorm_neg`, and Mathlib `Real.sq_sqrt`, all partial or lower-level rather than this named product-dual-norm equality.
-- minimal hypotheses: all already minimal for `canonicalDualNorm` on each block and `WithLp.toLp` product projections; no finite-dimensional, separating, boundedness, measurability, probability, or scale nonnegativity assumptions are used because the radicand is a sum of squared real terms.

/-- Squaring the scaled two-block product dual norm of a right-negated
`WithLp.toLp` pair removes the square root and the second-block sign.

For arbitrary component seminorms and scale constants, evaluating the named
two-block scaled product dual norm on `(gx, -gy)` gives the scaled sum of the
squared component canonical dual norms of `gx` and `gy`.

Layer: Model | Gap: Level 1 (scaled signed two-block product dual norm square formula)
Proof: unfold the named scaled product dual norm, square the nonnegative
  square-root radicand, and rewrite the second canonical dual norm by sign
  invariance.
Source: Functional analysis product dual norms, support-function dual norms,
  Mathlib `WithLp` product projections, and real square-root identities
Used in: stochastic convex-concave saddle-point mirror descent when bounding
  sampled or mean signed product oracles by component second-moment bounds
Book citation: book/FOML/StochasticConvexConcaveSaddlePoint.json#/assumptions/6
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent for stochastic convex-concave
  saddle point problems -/
theorem twoBlockScaledProductDualNorm_sq_toLp_neg_right
    {EX EY : Type*}
    [NormedAddCommGroup EX] [InnerProductSpace ℝ EX]
    [NormedAddCommGroup EY] [InnerProductSpace ℝ EY]
    (pX : Seminorm ℝ EX) (pY : Seminorm ℝ EY)
    (DX DY : ℝ) (gx : EX) (gy : EY) :
    (twoBlockScaledProductDualNorm pX pY DX DY
        (WithLp.toLp 2 (gx, -gy))) ^ 2 =
      2 * DX ^ 2 * (canonicalDualNorm pX gx) ^ 2 +
        2 * DY ^ 2 * (canonicalDualNorm pY gy) ^ 2 := by
  rw [twoBlockScaledProductDualNorm_def]
  rw [Real.sq_sqrt]
  · simp only [WithLp.toLp_fst, WithLp.toLp_snd]
    rw [canonicalDualNorm_neg]
  · positivity

end SOptLib

-- Generalization plan (G0):
-- concept/name: induced operator norm between seminormed gauges; orig was `networkOperatorNorm`
-- generality used: arbitrary real normed spaces, bundled input/output seminorms, and a continuous linear map; no inner-product, completeness, finite-dimensional, measure, convexity, smoothness, or oracle assumptions
-- portable call pattern: decentralized, block-coordinate, and primal-dual algorithms can change their state spaces, explicit analysis seminorms, and linear coupling operator while retaining the same unit-ball supremum
-- counterargument checked: this is not merely the ambient continuous-linear-map norm because the analysis seminorms can differ from the carrier norms; bundling both seminorms makes the construction canonical rather than a formula-hypothesis wrapper
-- coverage search: queried `induced operator norm supremum output seminorm input seminorm unit ball`, `seminorm continuous linear map supremum unit ball`, and `support function unit ball operator bound`; Mathlib supplies `normSeminorm` and `Seminorm.comp`, and SOptLib supplies analogous `canonicalDualNorm`, but neither covers a map between distinct explicit seminorms
-- minimal hypotheses: normed additive commutative groups and real normed-space instances are exactly those required by the continuous linear map; no property of the map beyond evaluation is assumed


namespace SOptLib

/-- The operator norm induced by an input seminorm and an output seminorm.

It is the supremum of the output seminorm of `A x` over the closed input
seminorm unit ball. The ambient norms are used only to type the continuous
linear map and need not agree with either explicit seminorm.

Layer: Model | Concept: induced seminorm operator norm
Proof: (definitional construction; support supremum over the input-seminorm unit ball)
Source: Functional analysis induced operator norms, seminorm unit balls, and conditionally complete real suprema
Used in: decentralized and primal-dual convergence bounds that measure a linear coupling operator in explicit analysis seminorms rather than the carrier norms
Book citation: book/research/Source.json#/algorithm_spec/parameters/9
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic decentralized communication sliding -/
noncomputable def inducedSeminormOperatorNorm
    {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (p : Seminorm ℝ V) (q : Seminorm ℝ W) (A : V →L[ℝ] W) : ℝ :=
  sSup {c : ℝ | ∃ x : V, p x ≤ 1 ∧ c = q (A x)}

/-- The induced seminorm operator norm is its defining unit-ball support
supremum.

Layer: Model | Gap: Level 0 (induced seminorm operator norm formula)
Proof: by rfl after unfolding `inducedSeminormOperatorNorm`
Source: Functional analysis induced operator norms, seminorm unit balls, and conditionally complete real suprema
Used in: unfolding explicit operator constants when proving unit-vector and homogeneous image bounds for linear coupling maps
Book citation: book/research/Source.json#/algorithm_spec/parameters/9
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic decentralized communication sliding -/
@[simp]
theorem inducedSeminormOperatorNorm_eq_sSup
    {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (p : Seminorm ℝ V) (q : Seminorm ℝ W) (A : V →L[ℝ] W) :
    inducedSeminormOperatorNorm p q A =
      sSup {c : ℝ | ∃ x : V, p x ≤ 1 ∧ c = q (A x)} := by
  rfl

end SOptLib

-- Generalization plan (G0):
-- concept/name: finite dependent-product inner pairing; orig was `stackedInner`
-- generality used: an arbitrary real-or-complex scalar field, a finite index type, and a dependent family of normed additive commutative groups with coordinate inner-product spaces; no completeness, finite-dimensional, measure, convexity, smoothness, or oracle assumptions
-- portable call pattern: finite-product optimization, block-coordinate, and consensus proofs can change the finite index type, scalar field, and coordinate Hilbert spaces while retaining the same coordinate-sum pairing on raw dependent-function states
-- counterargument checked: Mathlib's `PiLp.inner_apply` covers the L2-wrapped carrier, not the raw dependent-function carrier used by algorithms whose ambient Pi norm remains the sup norm; the named raw-carrier pairing, coordinate specification, and PiLp bridge form a reusable API rather than a paper-local alias
-- coverage search: queried `finite dependent product inner product equals sum of coordinate inner products`, `dependent product inner sum coordinate inner products`, and `Pi.inner_apply`; Mathlib provides `PiLp.inner_apply` after conversion to `PiLp 2`, while SOptLib provides coordinate insertion lemmas on PiLp but no named pairing on raw dependent functions, so coverage is partial
-- minimal hypotheses: `Fintype`, `RCLike`, coordinate `NormedAddCommGroup`, and coordinate `InnerProductSpace` instances are exactly those needed for the finite coordinate sum and its PiLp bridge


open scoped BigOperators

namespace SOptLib

/-- The inner pairing on a finite raw dependent product is the sum of its
coordinate inner products.

Unlike Mathlib's inner product on `PiLp 2`, this named pairing keeps algorithm
states on their raw dependent-function carrier and does not replace that
carrier's inherited norm.

Layer: Model | Concept: finite dependent-product inner pairing
Proof: (definitional construction; finite sum of coordinate inner products)
Source: Mathlib finite big operators, real-or-complex inner-product spaces, and finite `PiLp` inner products
Used in: finite-agent consensus, block-coordinate optimization, and decentralized primal-dual gap calculations that pair raw Pi-valued states coordinatewise
Book citation: book/research/Source.json#/setup/saddle_point_problem
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic decentralized communication sliding -/
def dependentProductInner
    {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι]
    {Block : ι → Type*}
    [∀ i, NormedAddCommGroup (Block i)]
    [∀ i, InnerProductSpace 𝕜 (Block i)]
    (x y : ∀ i, Block i) : 𝕜 :=
  ∑ i, inner 𝕜 (x i) (y i)

/-- Evaluating the finite dependent-product inner pairing gives the sum of
the coordinate inner products.

Layer: Model | Gap: Level 0 (raw dependent-product inner pairing formula)
Proof: by rfl after unfolding `dependentProductInner`
Source: Mathlib finite big operators and real-or-complex inner-product spaces
Used in: expanding finite-agent and block-coordinate pairings into coordinate sums for algebraic and inequality arguments
Book citation: book/research/Source.json#/setup/saddle_point_problem
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic decentralized communication sliding -/
@[simp]
theorem dependentProductInner_def
    {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι]
    {Block : ι → Type*}
    [∀ i, NormedAddCommGroup (Block i)]
    [∀ i, InnerProductSpace 𝕜 (Block i)]
    (x y : ∀ i, Block i) :
    dependentProductInner x y = ∑ i, inner 𝕜 (x i) (y i) := by
  rfl

/-- The finite dependent-product inner pairing on raw functions agrees with
Mathlib's inner product after placing both functions in `PiLp 2`.

Layer: Model | Gap: Level 0 (raw dependent-product to PiLp inner-product bridge)
Proof: unfold the raw pairing and rewrite the PiLp inner product with `PiLp.inner_apply`
Source: Mathlib `WithLp.toLp` and `PiLp.inner_apply` for finite dependent Hilbert products
Used in: transferring finite-product optimization and consensus pairing calculations between raw Pi-valued algorithm states and Mathlib's L2 product-space API
Book citation: book/research/Source.json#/setup/saddle_point_problem
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic decentralized communication sliding -/
theorem dependentProductInner_eq_piLp_inner
    {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι]
    {Block : ι → Type*}
    [∀ i, NormedAddCommGroup (Block i)]
    [∀ i, InnerProductSpace 𝕜 (Block i)]
    (x y : ∀ i, Block i) :
    dependentProductInner x y =
      inner 𝕜 (WithLp.toLp 2 x) (WithLp.toLp 2 y) := by
  rw [PiLp.inner_apply]
  rfl

end SOptLib

-- Generalization plan (G0):
-- concept/name: Cauchy--Schwarz for the inner pairing and L2 seminorm of a finite dependent product; orig was `stackedInner_le_stackedNorm_mul`
-- generality used: a finite index type and a dependent family of seminormed additive commutative groups with real inner-product spaces; no completeness, finite-dimensional, measure, convexity, smoothness, oracle, or algorithm assumptions
-- portable call pattern: finite-product Hilbert, block-coordinate, and decentralized algorithms can vary the finite index and coordinate spaces while bounding the same coordinatewise pairing by the product of root-sum-square coordinate seminorms
-- counterargument checked: Mathlib directly covers scalar finite-sum Cauchy--Schwarz and Cauchy--Schwarz on the `PiLp 2` carrier, but not this raw dependent-family bridge at seminorm-level generality; the statement also composes with SOptLib's named dependent-product squared norm energy rather than introducing a duplicate norm definition
-- coverage search: queried `finite dependent product sum inner product upper bound product L2 norm Cauchy Schwarz`, `sum coordinate real inner less equal sqrt sum norm squared product`, and `dependent product inner l2 seminorm Cauchy Schwarz`; top partial hits were `Real.sum_mul_le_sqrt_mul_sqrt`, `real_inner_le_norm`, `PiLp.inner_apply`, and `SOptLib.dependentProductNormSq_eq_sum`, with no complete matching declaration
-- minimal hypotheses: `Fintype`, coordinate `SeminormedAddCommGroup`, and coordinate real `InnerProductSpace` instances are exactly those used; no nondegeneracy, completeness, or finite-dimensionality is required


open scoped BigOperators

namespace SOptLib

/-- The coordinatewise inner pairing of two finite dependent families is at
most the product of the square roots of their squared coordinate energies.

Layer: Model | Gap: Level 1 (finite dependent-product L2 Cauchy--Schwarz bridge)
Proof: bound each real coordinate inner product by the product of coordinate norms, sum those bounds, and apply finite scalar Cauchy--Schwarz; unfold the named dependent-product squared energies at the boundary
Source: Mathlib `real_inner_le_norm` and `Real.sum_mul_le_sqrt_mul_sqrt`, together with SOptLib's finite dependent-product squared norm energy
Used in: decentralized primal-dual and block-coordinate analyses that bound a raw coordinate-sum pairing by the product of stacked root-sum-square seminorms
Book citation: book/research/Source.json#/setup/saddle_point_problem
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic decentralized communication sliding -/
theorem dependentProductInner_le_l2Seminorm_mul
    {ι : Type*} [Fintype ι]
    {Block : ι → Type*}
    [∀ i, SeminormedAddCommGroup (Block i)]
    [∀ i, InnerProductSpace ℝ (Block i)]
    (x y : ∀ i, Block i) :
    (∑ i, inner ℝ (x i) (y i)) ≤
      Real.sqrt (dependentProductNormSq x) *
        Real.sqrt (dependentProductNormSq y) := by
  calc
    (∑ i, inner ℝ (x i) (y i)) ≤ ∑ i, ‖x i‖ * ‖y i‖ := by
      exact Finset.sum_le_sum fun i _ => real_inner_le_norm (x i) (y i)
    _ ≤ Real.sqrt (∑ i, ‖x i‖ ^ 2) *
        Real.sqrt (∑ i, ‖y i‖ ^ 2) := by
          simpa using
            (Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset ι)
              (fun i => ‖x i‖) (fun i => ‖y i‖))
    _ = Real.sqrt (dependentProductNormSq x) *
        Real.sqrt (dependentProductNormSq y) := by
          rw [dependentProductNormSq_def, dependentProductNormSq_def]

end SOptLib

-- Generalization plan (G0):
-- concept/name: triangle inequality for the finite dependent-product L2 seminorm; orig was `stackedNorm_add_le`
-- generality used: a finite index type and dependent coordinate seminormed additive commutative groups; no scalar action, inner product, completeness, finite-dimensionality, measure, convexity, smoothness, or oracle assumptions
-- portable call pattern: finite-agent decentralized, block-coordinate, and product-state proofs can bound the L2 seminorm of a sum while changing the finite index and every coordinate space
-- counterargument checked: Mathlib's `norm_add_le` proves the ambient `PiLp` result, but this theorem packages its recurring raw dependent-function specialization through `WithLp.toLp`; it is not tied to SDCS notation or assumptions
-- coverage search: queried `dependent product L2 norm addition triangle inequality` and `PiLp norm add upper bound`; SOptLib had dependent-product squared energy and Cauchy--Schwarz APIs but no addition theorem, while Mathlib supplied the strictly ambient `norm_add_le` plus `WithLp.toLp_add`
-- minimal hypotheses: `Fintype` supplies the finite `PiLp` seminorm and each coordinate needs only `SeminormedAddCommGroup`; all stronger source assumptions were removed


namespace SOptLib

/-- The L2 seminorm of the sum of two raw finite dependent-product points is at
most the sum of their L2 seminorms.

Layer: Model | Gap: Level 0 (raw dependent-product L2 triangle inequality)
Proof: transport pointwise addition through `WithLp.toLp_add` and apply the ambient `norm_add_le` on the finite `PiLp 2` product.
Source: Mathlib `PiLp` seminormed additive groups, `WithLp.toLp_add`, and the norm triangle inequality
Used in: decentralized residual estimates and block-product perturbation bounds that keep algorithm states as raw dependent functions
Book citation: book/research/Source.json#/assumptions/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic decentralized communication sliding -/
theorem dependentProductL2Seminorm_add_le
    {ι : Type*} [Fintype ι]
    {Block : ι → Type*} [∀ i, SeminormedAddCommGroup (Block i)]
    (x y : ∀ i, Block i) :
    ‖WithLp.toLp 2 (x + y)‖ ≤
      ‖WithLp.toLp 2 x‖ + ‖WithLp.toLp 2 y‖ := by
  simpa only [WithLp.toLp_add] using
    (norm_add_le (WithLp.toLp 2 x) (WithLp.toLp 2 y))

end SOptLib

-- Generalization plan (G0):
-- concept/name: zero separation for the finite dependent-product L2 seminorm; orig was `stackedNorm_eq_zero_iff`
-- generality used: a finite index type and dependent coordinate normed additive commutative groups; no scalar action, inner product, completeness, finite-dimensionality, measure, convexity, smoothness, or oracle assumptions
-- portable call pattern: finite-agent decentralized, block-coordinate, and raw-Pi product-state proofs can change the finite index and coordinate spaces while using zero product residual to recover coordinatewise zero and hence the zero state
-- counterargument checked: Mathlib's `norm_eq_zero` applies to the ambient `PiLp` value, but this theorem packages the recurring raw dependent-function conclusion after the `WithLp.toLp` carrier conversion; it is neither paper-local traceability nor a new formula definition
-- coverage search: queried `finite dependent product root sum square norm equals zero iff every coordinate zero`, `PiLp norm equals zero iff function zero`, and `dependentProductL2Seminorm eq zero iff`; Mathlib returned the ambient norm separation API and SOptLib returned product-energy and PiLp bridge results, but neither exposes this raw-product equivalence
-- minimal hypotheses: `Fintype` supplies the finite `PiLp` norm and each coordinate needs `NormedAddCommGroup` exactly so zero norm separates points; the source Hilbert, completeness, measurability, and setup assumptions are unused


namespace SOptLib

/-- The L2 norm of a raw finite dependent-product point is zero exactly when
the underlying dependent function is zero.

Layer: Model | Gap: Level 0 (raw dependent-product L2 zero separation)
Proof: apply ambient norm separation in the finite `PiLp 2` carrier, then use the injective raw-function-to-`PiLp` conversion to reflect its zero value.
Source: Mathlib finite `PiLp`, `WithLp.toLp`, and norm zero-separation APIs
Used in: finite-agent decentralized and block-coordinate proofs that turn a vanishing stacked residual norm into equality of the raw Pi-valued state with zero before normalization or uniqueness arguments
Book citation: book/research/Source.json#/assumptions/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic decentralized communication sliding -/
theorem dependentProductL2Seminorm_eq_zero_iff
    {ι : Type*} [Fintype ι]
    {Block : ι → Type*} [∀ i, NormedAddCommGroup (Block i)]
    (x : ∀ i, Block i) :
    ‖WithLp.toLp 2 x‖ = 0 ↔ x = 0 := by
  rw [norm_eq_zero, WithLp.toLp_eq_zero]

end SOptLib

-- Generalization plan (G0):
-- concept/name: bounded image of a finite dependent-product L2 unit ball under a continuous linear map; orig was `stacked_network_operator_unit_support_bddAbove`
-- generality used: independent finite input and output index types, dependent coordinate families of real normed spaces, and an arbitrary continuous linear map; no inner product, completeness, finite-dimensionality, measure, convexity, smoothness, or oracle assumptions
-- portable call pattern: finite-network, block-coordinate, and product-state algorithms can change both finite index sets, all coordinate spaces, and the continuous linear coupling map while reusing boundedness of output L2 values on the input L2 unit ball
-- counterargument checked: continuous-linear-map operator bounds use the raw Pi carrier's sup norm, so Mathlib's ambient unit-ball result does not directly cover the L2-defined unit ball or L2-valued image set; the finite-product norm-comparison bridge is substantive and paper-free
-- coverage search: queried `dependent product L2 seminorm image unit ball bounded above continuous linear map`, `bounded above image unit ball operator norm finite product L2`, and `continuous linear map norms bounded on the unit ball`; the closest SOptLib hit was `canonicalDualNorm_supportSet_bddAbove`, which assumes rather than proves an ambient bound, while Mathlib exposed only ambient operator-norm bounds
-- minimal hypotheses: finiteness is needed for both L2 square sums, and coordinate normed real vector spaces are exactly what the raw Pi continuous-linear-map type requires; finite-dimensionality and Hilbert structure from the source are unused


open scoped BigOperators

namespace SOptLib

/-- The dependent-product L2 values of a continuous linear map on a
dependent-product L2 unit ball form a set bounded above.

The input and output may use different finite dependent products. The proof
compares each L2 seminorm with the raw Pi carrier's sup norm, where the
continuous-linear-map operator norm applies.

Layer: Model | Gap: Level 1 (finite dependent-product L2 operator-image boundedness)
Proof: bound the input Pi norm coordinatewise by its L2 norm, apply the continuous-linear-map operator norm, and bound the output L2 square sum by output cardinality times the squared Pi norm.
Source: Mathlib finite `PiLp` L2 norm formulas, finite-sum order, and continuous-linear-map operator norms
Used in: finite-agent decentralized and block-coordinate proofs that justify the supremum defining an L2-induced norm of a linear coupling operator
Book citation: book/research/Source.json#/algorithm_spec/parameters/9
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic decentralized communication sliding -/
theorem bddAbove_dependentProductL2Seminorm_image_unitBall
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    {F : κ → Type*} [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
    (A : (∀ i, E i) →L[ℝ] (∀ i, F i)) :
    BddAbove {c : ℝ | ∃ x : ∀ i, E i,
      ‖WithLp.toLp 2 x‖ ≤ 1 ∧ c = ‖WithLp.toLp 2 (A x)‖} := by
  classical
  refine ⟨Real.sqrt ((Fintype.card κ : ℝ) * ‖A‖ ^ 2), ?_⟩
  intro c hc
  rcases hc with ⟨x, hx_unit, rfl⟩
  have hcoord_le_l2 : ∀ i, ‖x i‖ ≤ ‖WithLp.toLp 2 x‖ := by
    intro i
    have hsq : ‖x i‖ ^ 2 ≤ ∑ j, ‖x j‖ ^ 2 := by
      exact Finset.single_le_sum
        (fun j _hj => sq_nonneg (‖x j‖)) (by simp)
    rw [← PiLp.norm_sq_eq_of_L2 E (WithLp.toLp 2 x)] at hsq
    nlinarith [hsq, norm_nonneg (x i), norm_nonneg (WithLp.toLp 2 x)]
  have hx_pi : ‖x‖ ≤ 1 := by
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    exact (hcoord_le_l2 i).trans hx_unit
  have hA_pi : ‖A x‖ ≤ ‖A‖ := by
    simpa using A.le_opNorm_of_le hx_pi
  have hsum_image :
      (∑ i, ‖(A x) i‖ ^ 2) ≤ (Fintype.card κ : ℝ) * ‖A x‖ ^ 2 := by
    calc
      (∑ i, ‖(A x) i‖ ^ 2) ≤ ∑ _i : κ, ‖A x‖ ^ 2 := by
        exact Finset.sum_le_sum fun i _hi => by
          have hi := norm_le_pi_norm (A x) i
          nlinarith [norm_nonneg ((A x) i), norm_nonneg (A x)]
      _ = (Fintype.card κ : ℝ) * ‖A x‖ ^ 2 := by simp
  have hsquare_image :
      (Fintype.card κ : ℝ) * ‖A x‖ ^ 2 ≤
        (Fintype.card κ : ℝ) * ‖A‖ ^ 2 := by
    have hsq : ‖A x‖ ^ 2 ≤ ‖A‖ ^ 2 := by
      nlinarith [hA_pi, norm_nonneg (A x), norm_nonneg A]
    exact mul_le_mul_of_nonneg_left hsq (by positivity)
  rw [PiLp.norm_eq_of_L2]
  exact (Real.sqrt_le_sqrt hsum_image).trans (Real.sqrt_le_sqrt hsquare_image)

end SOptLib

-- Generalization plan (G0):
-- concept/name: unit-ball image bound for an induced seminorm operator norm; orig was `stacked_network_operator_norm_unit_le`
-- generality used: arbitrary real normed spaces, bundled input/output seminorms, a continuous linear map, boundedness of the defining support set, and one pointwise input-unit-ball hypothesis; no separation, inner-product, completeness, finite-dimensional, measure, convexity, smoothness, or oracle assumptions
-- portable call pattern: decentralized, primal-dual, and block-product analyses can vary their state spaces, explicit analysis seminorms, and linear coupling map while bounding each mapped unit-ball point by the same induced operator seminorm
-- counterargument checked: although the proof is the direct `le_csSup` specification step, it is not a pure rename or caller-side paper expression; Mathlib's ambient-norm theorem and SOptLib's canonical-dual inner-product theorem are specializations and do not cover distinct arbitrary input and output seminorms
-- coverage search: queried `seminorm continuous linear map image unit ball less than supremum induced operator norm bounded above` and `le sSup bounded above member seminorm image unit ball`; the closest hits were Mathlib's `ContinuousLinearMap.unit_le_opNorm` and SOptLib's `abs_inner_le_canonicalDualNorm_of_primal_le_one`, both partial specializations, while `inducedSeminormOperatorNorm_eq_sSup` only exposes the defining formula
-- minimal hypotheses: support-set boundedness is required by `le_csSup`, and `p x ≤ 1` is the pointwise membership condition; all typeclasses are inherited from the existing induced-seminorm operator-norm definition


namespace SOptLib

/-- A point in the input seminorm unit ball has mapped output seminorm at most
the induced seminorm operator norm.

For an induced operator seminorm defined as a real supremum, boundedness of the
unit-ball image support set makes every particular support value lie below that
supremum.

Layer: Model | Gap: Level 0 (induced seminorm operator unit-ball bound)
Proof: unfold the induced operator seminorm to its support supremum, insert the given unit-ball point as a member, and apply `le_csSup` using boundedness.
Source: Functional analysis induced operator seminorms and Mathlib conditionally complete real supremum APIs
Used in: decentralized and primal-dual energy estimates that bound a linear coupling image after normalizing an iterate or residual into an explicit seminorm unit ball
Book citation: book/research/Source.json#/algorithm_spec/parameters/9
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic decentralized communication sliding -/
theorem map_le_inducedSeminormOperatorNorm_of_le_one
    {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (p : Seminorm ℝ V) (q : Seminorm ℝ W) (A : V →L[ℝ] W)
    (h_bdd : BddAbove {c : ℝ | ∃ u : V, p u ≤ 1 ∧ c = q (A u)})
    (x : V) (hx : p x ≤ 1) :
    q (A x) ≤ inducedSeminormOperatorNorm p q A := by
  rw [inducedSeminormOperatorNorm_eq_sSup]
  exact le_csSup h_bdd ⟨x, hx, rfl⟩

end SOptLib

-- Generalization plan (G0):
-- concept/name: global image bound for an induced seminorm operator norm; orig was `stacked_network_operator_norm_le`
-- generality used: arbitrary real normed spaces, bundled input/output seminorms, a continuous linear map, separation of the input seminorm, and boundedness of its output support set; no inner-product, completeness, finite-dimensional, measure, convexity, smoothness, or oracle assumptions
-- portable call pattern: decentralized, primal-dual, and block-product analyses can vary their state spaces, analysis seminorms, and linear coupling map while using the same normalization step to bound every mapped vector
-- counterargument checked: this is not a caller-side rewrite or a pure wrapper; unlike Mathlib's ambient operator-norm inequality, it handles explicit seminorms, and unlike `abs_inner_le_canonicalDualNorm_mul`, it handles an arbitrary output seminorm after an arbitrary continuous linear map
-- coverage search: queried `output seminorm map bounded by induced operator norm times input seminorm separating bounded unit ball`, `seminorm linear map supremum unit ball homogeneous global bound`, and `operator seminorm map le norm mul separating seminorm`; Mathlib semantic search was unavailable, while symbol search found the distinct inner-product specialization `abs_inner_le_canonicalDualNorm_mul` and no full match
-- minimal hypotheses: input separation is needed for the zero-seminorm branch, and support-set boundedness is needed for the real supremum bound; all remaining assumptions come from the continuous-linear-map and seminorm types


namespace SOptLib

/-- An induced seminorm operator norm bounds the output seminorm of every image.

For a separating input seminorm whose unit-ball image values are bounded above,
the unit-ball supremum extends by homogeneity to a global operator inequality.

Layer: Model | Gap: Level 1 (induced seminorm operator global bound)
Proof: split on whether the input seminorm vanishes; separation handles the zero case, while inverse scaling puts every nonzero vector in the unit ball so `le_csSup` applies before scaling back.
Source: Functional analysis induced operator norms, seminorm homogeneity, and conditionally complete real supremum APIs
Used in: decentralized and primal-dual convergence proofs that bound a linear coupling image in an explicit product seminorm before squaring or applying a Young inequality
Book citation: book/research/Source.json#/algorithm_spec/parameters/9
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic decentralized communication sliding -/
theorem map_le_inducedSeminormOperatorNorm_mul
    {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (p : Seminorm ℝ V) (q : Seminorm ℝ W) (A : V →L[ℝ] W)
    (hp : p.IsSeparating)
    (h_bdd : BddAbove {c : ℝ | ∃ u : V, p u ≤ 1 ∧ c = q (A u)})
    (x : V) :
    q (A x) ≤ inducedSeminormOperatorNorm p q A * p x := by
  classical
  by_cases hx0 : p x = 0
  · have hx : x = 0 := (hp x).mp hx0
    simp [hx]
  · have hpx_pos : 0 < p x :=
      lt_of_le_of_ne (apply_nonneg p x) (Ne.symm hx0)
    let u : V := (p x)⁻¹ • x
    have hu_le : p u ≤ 1 := by
      simp [u, map_smul_eq_mul, abs_of_pos hpx_pos, hpx_pos.ne']
    have hsup : q (A u) ≤ inducedSeminormOperatorNorm p q A := by
      rw [inducedSeminormOperatorNorm_eq_sSup]
      exact le_csSup h_bdd ⟨u, hu_le, rfl⟩
    have hscale : q (A u) = (p x)⁻¹ * q (A x) := by
      simp [u, map_smul_eq_mul]
    rw [hscale] at hsup
    have hmul := mul_le_mul_of_nonneg_right hsup hpx_pos.le
    field_simp [hpx_pos.ne'] at hmul
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul

end SOptLib

-- Generalization plan (G0):
-- concept/name: squared image bound for an induced seminorm operator norm; orig was `stacked_network_operator_norm_sq_le`
-- generality used: arbitrary real normed spaces, bundled input/output seminorms, a continuous linear map, and boundedness of the output support set; no separation, inner-product, completeness, finite-dimensional, measure, convexity, smoothness, or oracle assumptions
-- portable call pattern: network, block, and primal-dual energy estimates can vary the state spaces, analysis seminorms, and linear operator while retaining the same squared global induced-seminorm bound
-- counterargument checked: this is not paper-local bookkeeping or a pure rename; boundedness of the entire unit-ball support forces the image seminorm to vanish on the kernel of the input seminorm, after which normalization and order preservation under squaring yield the global squared-energy estimate
-- coverage search: queried `squared seminorm image bounded by squared induced operator seminorm times squared input seminorm`, `induced seminorm operator norm nonnegative`, and `nonnegative real equals zero when all scalar multiples are bounded above`; Mathlib supplies `sq_le_sq₀`, while SOptLib's `map_le_inducedSeminormOperatorNorm_mul` requires a separating input seminorm, so neither covers the kernel-vanishing and normalized squared estimate under boundedness alone
-- minimal hypotheses: support-set boundedness is needed both for the support supremum and to force the output seminorm to vanish on the input-seminorm kernel; all remaining assumptions are required by the continuous-linear-map and seminorm types


namespace SOptLib

/-- The squared output seminorm of a linear image is bounded by the squared
induced seminorm operator norm times the squared input seminorm.

When the input unit-ball image values are bounded above, boundedness first
forces the output seminorm to vanish on the kernel of the input seminorm. The
usual normalization argument then gives a global estimate, which remains valid
after squaring both nonnegative sides.

Layer: Model | Gap: Level 1 (induced seminorm operator squared-energy bound)
Proof: use arbitrary scalar multiples to handle the zero-input-seminorm case, normalize by the input seminorm otherwise, and square the resulting nonnegative inequality via `sq_le_sq₀` before expanding the product square.
Source: Functional analysis induced operator seminorms, conditionally complete real suprema, and Mathlib ordered-ring square monotonicity
Used in: network, block, and primal-dual algorithm energy estimates that bound the squared analysis seminorm of a linear coupling image
Book citation: book/research/Source.json#/algorithm_spec/parameters/9
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic decentralized communication sliding -/
theorem map_sq_le_inducedSeminormOperatorNorm_sq_mul
    {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (p : Seminorm ℝ V) (q : Seminorm ℝ W) (A : V →L[ℝ] W)
    (h_bdd : BddAbove {c : ℝ | ∃ u : V, p u ≤ 1 ∧ c = q (A u)})
    (x : V) :
    q (A x) ^ 2 ≤ inducedSeminormOperatorNorm p q A ^ 2 * p x ^ 2 := by
  classical
  have hmap :
      q (A x) ≤ inducedSeminormOperatorNorm p q A * p x :=
    by
      by_cases hx0 : p x = 0
      · have hqx0 : q (A x) = 0 := by
          by_contra hqx_ne
          have hqx_pos : 0 < q (A x) :=
            lt_of_le_of_ne (apply_nonneg q (A x)) (Ne.symm hqx_ne)
          rcases h_bdd with ⟨C, hC⟩
          have hC_nonneg : 0 ≤ C :=
            hC ⟨0, by simp, by simp⟩
          let t : ℝ := (C + 1) / q (A x)
          have ht_pos : 0 < t :=
            div_pos (by linarith) hqx_pos
          have hptx : p (t • x) ≤ 1 := by
            simp [map_smul_eq_mul, hx0]
          have hscaled : q (A (t • x)) ≤ C :=
            hC ⟨t • x, hptx, rfl⟩
          have hscale : q (A (t • x)) = t * q (A x) := by
            simp [map_smul_eq_mul, abs_of_pos ht_pos]
          rw [hscale] at hscaled
          dsimp [t] at hscaled
          rw [div_mul_cancel₀ _ hqx_pos.ne'] at hscaled
          linarith
        simp [hqx0, hx0]
      · have hpx_pos : 0 < p x :=
          lt_of_le_of_ne (apply_nonneg p x) (Ne.symm hx0)
        let u : V := (p x)⁻¹ • x
        have hu_le : p u ≤ 1 := by
          simp [u, map_smul_eq_mul, abs_of_pos hpx_pos, hpx_pos.ne']
        have hsup : q (A u) ≤ inducedSeminormOperatorNorm p q A := by
          rw [inducedSeminormOperatorNorm_eq_sSup]
          exact le_csSup h_bdd ⟨u, hu_le, rfl⟩
        have hscale : q (A u) = (p x)⁻¹ * q (A x) := by
          simp [u, map_smul_eq_mul]
        rw [hscale] at hsup
        have hmul := mul_le_mul_of_nonneg_right hsup hpx_pos.le
        field_simp [hpx_pos.ne'] at hmul
        simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have hop_nonneg : 0 ≤ inducedSeminormOperatorNorm p q A := by
    rw [inducedSeminormOperatorNorm_eq_sSup]
    exact le_csSup h_bdd ⟨0, by simp, by simp⟩
  have hright_nonneg :
      0 ≤ inducedSeminormOperatorNorm p q A * p x :=
    mul_nonneg hop_nonneg (apply_nonneg p x)
  calc
    q (A x) ^ 2 ≤
        (inducedSeminormOperatorNorm p q A * p x) ^ 2 :=
      (sq_le_sq₀ (apply_nonneg q (A x)) hright_nonneg).2 hmap
    _ = inducedSeminormOperatorNorm p q A ^ 2 * p x ^ 2 := by
      rw [mul_pow]

end SOptLib
