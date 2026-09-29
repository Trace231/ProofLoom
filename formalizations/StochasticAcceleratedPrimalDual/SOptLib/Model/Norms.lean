import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Seminorm
import Mathlib.Data.Real.Archimedean
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

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

namespace SOptLib

/-- The canonical support-function dual norm vanishes at the zero dual vector.

At `0`, every absolute inner product in the primal unit-ball support set is
zero, while the zero primal vector witnesses that the support set is nonempty.
Thus the defining supremum is the supremum of the singleton `{0}`.

Layer: Model | Gap: Level 0 (canonical dual norm zero value)
Proof: unfold the canonical support-function formula, identify the support set
  with `{0}`, and evaluate the supremum of a singleton.
Source: Functional analysis dual norms, support functions of unit balls, and
  Mathlib order-theoretic supremum APIs
Used in: stochastic block mirror descent simplification of zero block dual norms
  derived from paper primal norms
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/assumptions/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
@[simp]
theorem canonicalDualNorm_zero
    {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℝ B]
    (p : Seminorm ℝ B) :
    SOptLib.canonicalDualNorm p (0 : B) = 0 := by
  classical
  rw [SOptLib.canonicalDualNorm_eq_sSup]
  have hset :
      {r : ℝ | ∃ d : B, p d ≤ 1 ∧ r = |inner ℝ (0 : B) d|} = ({0} : Set ℝ) := by
    ext r
    constructor
    · intro hr
      rcases hr with ⟨d, _hd, rfl⟩
      simp
    · intro hr
      rcases hr with rfl
      refine ⟨0, ?_, ?_⟩
      · simp
      · simp
  rw [hset]
  simp

end SOptLib
