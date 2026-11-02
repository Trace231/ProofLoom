import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Seminorm
import Mathlib.Data.Real.Archimedean
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Tactic

open MeasureTheory
open scoped BigOperators ENNReal InnerProductSpace

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
