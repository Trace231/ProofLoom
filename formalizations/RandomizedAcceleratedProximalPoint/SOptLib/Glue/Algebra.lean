import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Topology.Algebra.AffineSubspace
import Mathlib.Analysis.SpecialFunctions.Log.Base
-- SOptLib/Glue/Algebra.lean
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Interval.Finset.SuccPred
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic


open scoped BigOperators InnerProductSpace

/-- Telescope successive differences over a closed natural-number interval.

Layer: Glue | Gap: Level 2 (closed-interval telescope packaging)
Proof: induction on the right endpoint, splitting off the final index and
  simplifying the additive group expression.
Source: Mathlib finite sums over natural intervals
Used in: stochastic mirror descent output-window Bregman telescope
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan stochastic mirror descent -/
theorem sum_Icc_sub_succ {α : Type*} [AddCommGroup α] (a : ℕ → α) (s k : ℕ)
    (hsk : s ≤ k) :
    Finset.sum (Finset.Icc s k) (fun n => a n - a (n + 1)) = a s - a (k + 1) := by
  revert hsk
  refine Nat.le_induction ?base ?step k
  · simp
  · intro n hsn ih
    have hIcc : Finset.Icc s (n + 1) = insert (n + 1) (Finset.Icc s n) := by
      ext t
      simp [Finset.mem_Icc]
      omega
    have hnot : n + 1 ∉ Finset.Icc s n := by
      simp [Finset.mem_Icc]
    rw [hIcc, Finset.sum_insert hnot, ih]
    abel


/-- Bound the squared norm of a vector decomposed as a bounded part plus a residual.

Layer: Glue | Gap: Level 1 (packaged norm-square Young inequality)
Proof: triangle inequality, monotonicity of squaring on nonnegative reals, and
  `(a + b)^2 <= 2*a^2 + 2*b^2`.
Source: Mathlib normed additive groups and real arithmetic
Used in: stochastic mirror descent oracle magnitude bound
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan stochastic mirror descent -/
theorem norm_sq_le_two_mul_sq_add_sq_of_eq_add_of_norm_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G g δ : E) (M : ℝ)
    (h_eq : G = g + δ)
    (h_norm_le : ‖g‖ ≤ M) :
    ‖G‖ ^ 2 ≤ 2 * (M ^ 2 + ‖δ‖ ^ 2) := by
  subst G
  have hnorm : ‖g + δ‖ ^ 2 ≤ 2 * ‖g‖ ^ 2 + 2 * ‖δ‖ ^ 2 := by
    have h_norm : ‖g + δ‖ ≤ ‖g‖ + ‖δ‖ := norm_add_le g δ
    have h_sq : ‖g + δ‖ ^ 2 ≤ (‖g‖ + ‖δ‖) ^ 2 := by
      nlinarith [h_norm, norm_nonneg (g + δ), norm_nonneg g, norm_nonneg δ]
    have h_expand : (‖g‖ + ‖δ‖) ^ 2 ≤
        2 * ‖g‖ ^ 2 + 2 * ‖δ‖ ^ 2 := by
      nlinarith [sq_nonneg (‖g‖ - ‖δ‖)]
    exact h_sq.trans h_expand
  have hM_nonneg : 0 ≤ M := le_trans (norm_nonneg g) h_norm_le
  have hg_sq : ‖g‖ ^ 2 ≤ M ^ 2 := by
    nlinarith [h_norm_le, hM_nonneg, norm_nonneg g]
  nlinarith [hnorm, hg_sq]


/-- Continuous linear part of the `vaddConst` affine chart map.

Layer: Glue | Gap: Level 1 (chart linear part identification)
Proof: evaluate on a displacement and use `contLinear_map_vsub` at `0`; rewrite
with the explicit `vaddConst` formula at `0` and the chosen point.
Source: Mathlib affine subspace charts
Used in: stochastic mirror descent intrinsic carrier calculus
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan stochastic mirror descent -/
theorem AffineSubspace.vaddConst_contLinear_eq_subtypeL
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {A : AffineSubspace ℝ E} (a : A) (L : A.direction →ᴬ[ℝ] E)
    (hL_apply : ∀ du : A.direction, L du = (du : E) + a) :
    L.contLinear = A.direction.subtypeL := by
  ext du
  have hLdu : L.contLinear du = L du - L 0 := by
    simpa [vsub_eq_sub] using L.contLinear_map_vsub du 0
  have hLdu_apply : L du = (du : E) + a := hL_apply du
  have hLzero : L 0 = a := by simpa using hL_apply 0
  rw [hLdu, hLdu_apply, hLzero]
  simp


/-- Difference of two affine-subspace chart coordinates, included back into the ambient
space, is the ambient difference of the two affine points.

Layer: Glue | Gap: Level 1 (affine chart coordinate subtraction)
Proof: unfold the `vaddConst` affine chart, identify its linear part with the
  direction-submodule inclusion, and rewrite the chart images of the two points.
Source: Mathlib affine subspace charts
Used in: stochastic mirror descent intrinsic carrier chart algebra
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan stochastic mirror descent -/
theorem affineSpan_chartPoint_sub_subtypeL
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : AffineSubspace ℝ E) [Nonempty A] (anchor x y : A) :
    (A.direction.subtypeL)
      ((AffineIsometryEquiv.vaddConst ℝ anchor).symm y -
        (AffineIsometryEquiv.vaddConst ℝ anchor).symm x) =
        (y : E) - (x : E) := by
  classical
  let L : A.direction →ᴬ[ℝ] E :=
    A.subtypeA.comp
      ((AffineIsometryEquiv.vaddConst ℝ anchor).toContinuousAffineEquiv.toContinuousAffineMap)
  let uy : A.direction := (AffineIsometryEquiv.vaddConst ℝ anchor).symm y
  let ux : A.direction := (AffineIsometryEquiv.vaddConst ℝ anchor).symm x
  have hlin : L.contLinear (uy - ux) = L uy - L ux := by
    simpa [vsub_eq_sub] using L.contLinear_map_vsub uy ux
  have hy : L uy = y := by
    change (((AffineIsometryEquiv.vaddConst ℝ anchor).toContinuousAffineEquiv.toContinuousAffineMap
        uy : A) : E) = y
    simp [uy]
  have hx : L ux = x := by
    change (((AffineIsometryEquiv.vaddConst ℝ anchor).toContinuousAffineEquiv.toContinuousAffineMap
        ux : A) : E) = x
    simp [ux]
  have hLlin_apply : L.contLinear (uy - ux) = (A.direction.subtypeL) (uy - ux) := by
    let du : A.direction := uy - ux
    have hLdu : L.contLinear du = L du - L 0 := by
      simpa [vsub_eq_sub] using L.contLinear_map_vsub du 0
    have hLdu_apply : L du = (du : E) + anchor := by
      change (((AffineIsometryEquiv.vaddConst ℝ anchor).toContinuousAffineEquiv.toContinuousAffineMap
          du : A) : E) = (du : E) + anchor
      simp
    have hLzero : L 0 = anchor := by
      change (((AffineIsometryEquiv.vaddConst ℝ anchor).toContinuousAffineEquiv.toContinuousAffineMap
          (0 : A.direction) : A) : E) = anchor
      simp
    calc
      L.contLinear (uy - ux) = L.contLinear du := by simp [du]
      _ = (du : E) := by
        rw [hLdu, hLdu_apply, hLzero]
        simp
      _ = (A.direction.subtypeL) (uy - ux) := by simp [du]
  change (A.direction.subtypeL) (uy - ux) = (y : E) - (x : E)
  rw [← hLlin_apply, hlin, hy, hx]

/-- Each branch of a three-way real maximum is bounded by its positive ceiling.

If a natural-number choice is formed as `max 1 (Nat.ceil (max (max a b) c))`,
then the corresponding real number dominates all three real requirements
`a`, `b`, and `c`.

Layer: Glue | Gap: Level 0 (positive ceiling three-way maximum lower bounds)
Proof: combine the branch inequalities into the nested maximum with
  `le_max_left` and `le_max_right`, use `Nat.le_ceil`, and pass through the
  positive natural totalization by `Nat.le_max_right`.
Source: Mathlib natural ceiling and lattice-order APIs for real maxima
Used in: two-phase randomized stochastic mirror descent per-run SFO budget
  choice lower bounds for deterministic, variance-balancing, and stability terms
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/parameters
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
theorem le_positive_ceil_threeway_max
    (a b c : ℝ) :
    a ≤ ((max 1 (Nat.ceil (max (max a b) c))) : ℕ) ∧
    b ≤ ((max 1 (Nat.ceil (max (max a b) c))) : ℕ) ∧
    c ≤ ((max 1 (Nat.ceil (max (max a b) c))) : ℕ) := by
  have hceil : max (max a b) c ≤ (Nat.ceil (max (max a b) c) : ℝ) :=
    Nat.le_ceil _
  have hchoice :
      (Nat.ceil (max (max a b) c) : ℝ) ≤
        ((max 1 (Nat.ceil (max (max a b) c))) : ℕ) := by
    exact_mod_cast (Nat.le_max_right 1 (Nat.ceil (max (max a b) c)))
  constructor
  · exact le_trans (le_trans (le_trans (le_max_left a b)
      (le_max_left (max a b) c)) hceil) hchoice
  constructor
  · exact le_trans (le_trans (le_trans (le_max_right a b)
      (le_max_left (max a b) c)) hceil) hchoice
  · exact le_trans (le_trans (le_max_right (max a b) c) hceil) hchoice

namespace Finset

/-- A finite family divided by its nonzero total sum has total mass one.

For any finite index set, if `W` is the sum of the real weights over that set
and `W` is nonzero, then the normalized weights `w i / W` sum to one.

Layer: Glue | Gap: Level 0 (finite normalized real weights)
Proof: factor the common denominator out of the finite sum with
  `Finset.sum_div`, rewrite the numerator using the denominator identity, and
  cancel by `div_self`.
Source: Mathlib finite sums and real field division APIs
Used in: nonconvex stochastic mirror descent randomized stopping distribution
  normalization
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/output/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
theorem sum_div_sum_eq_one {ι : Type*} (s : Finset ι) (w : ι → ℝ) (W : ℝ)
    (hW : W = ∑ i ∈ s, w i) (hW_ne : W ≠ 0) :
    (∑ i ∈ s, w i / W) = 1 := by
  calc
    (∑ i ∈ s, w i / W) = (∑ i ∈ s, w i) / W := by
      rw [← Finset.sum_div]
    _ = W / W := by
      rw [← hW]
    _ = 1 := div_self hW_ne

end Finset

namespace Finset

/-- Pull a constant out of a nested finite sum as the sum of inner cardinalities.

For a finite outer index set and a finite inner index set depending on the
outer index, adding the same constant to every inner summand contributes the
constant multiplied by the total number of inner summands.

Layer: Glue | Gap: Level 0 (nested finite-sum constant extraction)
Proof: apply Mathlib's single-finset constant-addition identity on each inner
  finset, distribute the outer sum over addition, then collect the cardinality
  weights with `Finset.mul_sum`.
Source: Mathlib finite big-operator algebra over commutative semirings
Used in: nonconvex stochastic conditional-gradient epochwise variance-floor
  aggregation
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem sum_sum_add_const {I J R : Type*} [CommSemiring R]
    (outer : Finset I) (inner : I → Finset J) (A : I → J → R) (c : R) :
    (∑ i ∈ outer, ∑ j ∈ inner i, (A i j + c)) =
      (∑ i ∈ outer, ∑ j ∈ inner i, A i j) +
        c * ∑ i ∈ outer, ((inner i).card : R) := by
  calc
    (∑ i ∈ outer, ∑ j ∈ inner i, (A i j + c)) =
        ∑ i ∈ outer,
          ((∑ j ∈ inner i, A i j) + ((inner i).card : R) * c) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [← Finset.sum_add_card_nsmul]
      simp [nsmul_eq_mul]
    _ =
        (∑ i ∈ outer, ∑ j ∈ inner i, A i j) +
          ∑ i ∈ outer, ((inner i).card : R) * c := by
      rw [Finset.sum_add_distrib]
    _ =
        (∑ i ∈ outer, ∑ j ∈ inner i, A i j) +
          c * ∑ i ∈ outer, ((inner i).card : R) := by
      rw [← Finset.sum_mul]
      ring

/-- A subset sum scaled by a nonnegative right factor is bounded by the full sum
scaled by the same factor.

If every element added when passing from `active` to `full` has nonnegative
weight and the common right factor is nonnegative, the active scaled sum is at
most the full unscaled sum multiplied by that factor.

Layer: Glue | Gap: Level 0 (finite subset sum with common nonnegative factor)
Proof: apply `Finset.sum_le_sum_of_subset_of_nonneg` to extend the sum from
  `active` to `full`, multiply the resulting inequality by the nonnegative
  factor, and rewrite the left side with `Finset.sum_mul`.
Source: Mathlib finite sums over finsets and ordered semiring product monotonicity
Used in: stochastic nonconvex conditional gradient active-epoch error budget
  extension from selected steps to the full epoch window
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem sum_subset_mul_nonneg_right_le {ι R : Type*}
    [CommSemiring R] [PartialOrder R] [IsOrderedRing R]
    (active full : Finset ι) (a : ι → R) (M : R)
    (hsubset : active ⊆ full)
    (ha_nonneg : ∀ j ∈ full, j ∉ active → 0 ≤ a j)
    (hM_nonneg : 0 ≤ M) :
    (∑ j ∈ active, a j * M) ≤ (∑ j ∈ full, a j) * M := by
  have hsum_subset :
      (∑ j ∈ active, a j) ≤ (∑ j ∈ full, a j) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset ha_nonneg
  have hmul :=
    mul_le_mul_of_nonneg_right hsum_subset hM_nonneg
  simpa [Finset.sum_mul] using hmul

end Finset

namespace SOptLib

/-- The squared norm of a sum is bounded by twice the squared norms of its terms.

For any elements of a seminormed additive commutative group, the triangle
inequality and the scalar estimate `(x + y)^2 <= 2*x^2 + 2*y^2` give this
two-term Young bound.

Layer: Glue | Gap: Level 1 (binary norm-square Young inequality)
Proof: apply the norm triangle inequality, square both sides using
  nonnegativity of norms, and finish with the real square inequality.
Source: Mathlib seminormed additive groups and real arithmetic inequalities
Used in: stochastic conditional-gradient residual L2 closure and stochastic
  mirror-descent oracle error decomposition
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem norm_add_sq_le_two_mul_norm_sq_add_two_mul_norm_sq
    {E : Type*} [SeminormedAddCommGroup E] (a b : E) :
    ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h_norm : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le a b
  have h_sq : ‖a + b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 := by
    nlinarith [h_norm, norm_nonneg (a + b), norm_nonneg a, norm_nonneg b]
  have h_expand : (‖a‖ + ‖b‖) ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
    nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
  exact h_sq.trans h_expand

end SOptLib

-- Batch 1 promoted from Staging/sum_Icc_predecessor_count_le_pred_mul_sum.lean
/-- A closed lower-triangular predecessor sum is bounded by `(t - 1)` copies of
the total nonnegative mass.

For a nonnegative real sequence on `{1, ..., t}`, each row
`sum_{i=2..j} a (i - 1)` is bounded by the total mass, and the first row is
zero. Hence only the `t - 1` rows indexed by `Icc 2 t` contribute to the final
cardinality factor.

Layer: Glue | Gap: Level 1 (sharp closed-interval triangular predecessor count)
Proof: reindex each predecessor row by the injective map `i ↦ i - 1`, compare
  the image with `Icc 1 t` using nonnegative subset monotonicity, remove the
  zero first row, and rewrite the remaining row count as `t - 1`.
Source: Mathlib finite sums over natural intervals, image sums, subset
  monotonicity for nonnegative summands, and interval cardinality APIs
Used in: nonconvex variance-reduced mirror descent epochwise estimator-error
  residual summation
Book citation: book/FOML/NonconvexVarianceReducedMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex variance-reduced mirror descent -/
theorem sum_Icc_predecessor_count_le_pred_mul_sum
    {M : Type*} [AddCommMonoid M] [PartialOrder M] [AddLeftMono M]
    (a : ℕ → M) (t : ℕ)
    (ha_nonneg : ∀ r ∈ Finset.Icc 1 t, 0 ≤ a r) :
    Finset.sum (Finset.Icc 1 t)
        (fun j => Finset.sum (Finset.Icc 2 j) (fun i => a (i - 1))) ≤
      (t - 1) • Finset.sum (Finset.Icc 1 t) a := by
  classical
  by_cases ht_zero : t = 0
  · simp [ht_zero]
  have ht_pos : 1 ≤ t := Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero ht_zero)
  let total : M := Finset.sum (Finset.Icc 1 t) a
  have hinner_le :
      ∀ j ∈ Finset.Icc 2 t,
        Finset.sum (Finset.Icc 2 j) (fun i => a (i - 1)) ≤ total := by
    intro j hj
    let predSet : Finset ℕ := (Finset.Icc 2 j).image (fun i => i - 1)
    have hinj : Set.InjOn (fun i : ℕ => i - 1) (Finset.Icc 2 j) := by
      intro x hx y hy hxy
      simp only [Finset.mem_coe, Finset.mem_Icc] at hx hy
      have hxpred : x = (x - 1) + 1 := by omega
      have hypred : y = (y - 1) + 1 := by omega
      rw [hxpred, hypred]
      simpa [Nat.succ_eq_add_one] using congrArg Nat.succ hxy
    have hsum_image :
        Finset.sum predSet a =
          Finset.sum (Finset.Icc 2 j) (fun i => a (i - 1)) := by
      simpa [predSet] using
        (Finset.sum_image (s := Finset.Icc 2 j) (f := a)
          (g := fun i : ℕ => i - 1) hinj)
    have hsubset : predSet ⊆ Finset.Icc 1 t := by
      intro r hr
      rcases Finset.mem_image.mp hr with ⟨i, hi, hir⟩
      have hi' : i ∈ Finset.Icc 2 j := hi
      rw [← hir]
      simp only [Finset.mem_Icc] at hi' hj ⊢
      omega
    have hnonneg :
        ∀ x ∈ Finset.Icc 1 t, x ∉ predSet → 0 ≤ a x := by
      intro x hx _hnot
      exact ha_nonneg x hx
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hsubset hnonneg
    calc
      Finset.sum (Finset.Icc 2 j) (fun i => a (i - 1)) =
          Finset.sum predSet a := hsum_image.symm
      _ ≤ Finset.sum (Finset.Icc 1 t) a := hle
      _ = total := rfl
  have hrow_one :
      Finset.sum (Finset.Icc 2 1) (fun i => a (i - 1)) = 0 := by
    simp
  have hIcc_split : Finset.Icc 1 t = insert 1 (Finset.Icc 2 t) := by
    ext j
    constructor
    · intro hj
      simp only [Finset.mem_Icc] at hj
      by_cases h : j = 1
      · simp [h]
      · simp only [Finset.mem_insert, Finset.mem_Icc]
        right
        omega
    · intro hj
      simp only [Finset.mem_insert, Finset.mem_Icc] at hj ⊢
      rcases hj with h | h
      · omega
      · omega
  have hone_not_mem : 1 ∉ Finset.Icc 2 t := by
    simp
  have houter_split :
      Finset.sum (Finset.Icc 1 t)
          (fun j => Finset.sum (Finset.Icc 2 j) (fun i => a (i - 1))) =
        Finset.sum (Finset.Icc 2 t)
          (fun j => Finset.sum (Finset.Icc 2 j) (fun i => a (i - 1))) := by
    rw [hIcc_split, Finset.sum_insert hone_not_mem]
    rw [hrow_one]
    simp
  have hsum_rows :
      Finset.sum (Finset.Icc 2 t)
          (fun j => Finset.sum (Finset.Icc 2 j) (fun i => a (i - 1))) ≤
        (Finset.Icc 2 t).card • total := by
    exact Finset.sum_le_card_nsmul (Finset.Icc 2 t)
      (fun j => Finset.sum (Finset.Icc 2 j) (fun i => a (i - 1))) total hinner_le
  have hcard_nat : (Finset.Icc 2 t).card = t - 1 := by
    rw [Nat.card_Icc]
    omega
  calc
    Finset.sum (Finset.Icc 1 t)
        (fun j => Finset.sum (Finset.Icc 2 j) (fun i => a (i - 1))) =
        Finset.sum (Finset.Icc 2 t)
          (fun j => Finset.sum (Finset.Icc 2 j) (fun i => a (i - 1))) := houter_split
    _ ≤ (Finset.Icc 2 t).card • total := hsum_rows
    _ = (t - 1) • Finset.sum (Finset.Icc 1 t) a := by
      rw [hcard_nat]

-- Batch 1 promoted from Staging/sum_Icc_error_le_scaled_predecessor_mass.lean
/-- A pointwise scaled predecessor-mass bound gives a scaled total error budget.

If each error term on `Icc 1 t` is bounded by a batch-normalized sum of
predecessor masses and the two scalar factors in that row bound multiply to
one, then the total error is controlled by `(t - 1) / batch` times the total
mass, with any nonnegative outer coefficient.

Layer: Glue | Gap: Level 1 (scaled predecessor-mass error aggregation)
Proof: normalize the pointwise row bounds using `scale * stepScale = 1`, sum
  over `Icc 1 t`, apply the triangular predecessor-count lemma, and multiply by
  the nonnegative outer coefficient.
Source: Mathlib finite sums over natural intervals, ordered-field scalar
  arithmetic, and finite-sum monotonicity APIs
Used in: nonconvex variance-reduced mirror descent epochwise estimator-error
  residual summation
Book citation: book/FOML/NonconvexVarianceReducedMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex variance-reduced mirror descent -/
theorem sum_Icc_error_le_scaled_predecessor_mass
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (E G : ℕ → K) (scale stepScale batch C : K) (t : ℕ) (ht_pos : 1 ≤ t)
    (hscale_step : scale * stepScale = 1)
    (hbatch_pos : 0 < batch)
    (hC_nonneg : 0 ≤ C)
    (hG_nonneg : ∀ r ∈ Finset.Icc 1 t, 0 ≤ G r)
    (hpoint :
      ∀ j ∈ Finset.Icc 1 t,
        E j ≤ (scale / batch) *
          Finset.sum (Finset.Icc 2 j) (fun i => stepScale * G (i - 1))) :
    C * Finset.sum (Finset.Icc 1 t) E ≤
      (C * ((t : K) - 1) / batch) * Finset.sum (Finset.Icc 1 t) G := by
  have hpoint_norm :
      ∀ j ∈ Finset.Icc 1 t,
        E j ≤ (1 / batch) *
          Finset.sum (Finset.Icc 2 j) (fun i => G (i - 1)) := by
    intro j hj
    have h := hpoint j hj
    have hcoef :
        (scale / batch) *
            Finset.sum (Finset.Icc 2 j) (fun i => stepScale * G (i - 1)) =
          (1 / batch) *
            Finset.sum (Finset.Icc 2 j) (fun i => G (i - 1)) := by
      rw [← Finset.mul_sum]
      calc
        (scale / batch) *
            (stepScale *
              Finset.sum (Finset.Icc 2 j) (fun i => G (i - 1))) =
          ((scale * stepScale) / batch) *
            Finset.sum (Finset.Icc 2 j) (fun i => G (i - 1)) := by
            ring
        _ =
          (1 / batch) *
            Finset.sum (Finset.Icc 2 j) (fun i => G (i - 1)) := by
            rw [hscale_step]
    simpa [hcoef] using h
  have hsumE :
      Finset.sum (Finset.Icc 1 t) E ≤
        (1 / batch) *
          Finset.sum (Finset.Icc 1 t)
            (fun j => Finset.sum (Finset.Icc 2 j) (fun i => G (i - 1))) := by
    calc
      Finset.sum (Finset.Icc 1 t) E ≤
          Finset.sum (Finset.Icc 1 t)
            (fun j => (1 / batch) *
              Finset.sum (Finset.Icc 2 j) (fun i => G (i - 1))) := by
            exact Finset.sum_le_sum hpoint_norm
      _ =
          (1 / batch) *
            Finset.sum (Finset.Icc 1 t)
              (fun j => Finset.sum (Finset.Icc 2 j) (fun i => G (i - 1))) := by
            rw [Finset.mul_sum]
  have htri :
      Finset.sum (Finset.Icc 1 t)
          (fun j => Finset.sum (Finset.Icc 2 j) (fun i => G (i - 1))) ≤
        ((t : K) - 1) * Finset.sum (Finset.Icc 1 t) G := by
    have htri_nsmul :=
      sum_Icc_predecessor_count_le_pred_mul_sum G t hG_nonneg
    have hcast : ((t - 1 : ℕ) : K) = (t : K) - 1 := by
      have ht_eq : ((t - 1 : ℕ) : K) + 1 = (t : K) := by
        exact_mod_cast (Nat.sub_add_cancel ht_pos)
      linarith
    simpa [nsmul_eq_mul, hcast] using htri_nsmul
  have hinv_batch_nonneg : 0 ≤ 1 / batch := by
    positivity
  have hsumE_scaled :
      Finset.sum (Finset.Icc 1 t) E ≤
        (((t : K) - 1) / batch) * Finset.sum (Finset.Icc 1 t) G := by
    calc
      Finset.sum (Finset.Icc 1 t) E ≤
          (1 / batch) *
            Finset.sum (Finset.Icc 1 t)
              (fun j => Finset.sum (Finset.Icc 2 j) (fun i => G (i - 1))) := hsumE
      _ ≤
          (1 / batch) *
            (((t : K) - 1) * Finset.sum (Finset.Icc 1 t) G) := by
            exact mul_le_mul_of_nonneg_left htri hinv_batch_nonneg
      _ =
          (((t : K) - 1) / batch) * Finset.sum (Finset.Icc 1 t) G := by
            ring
  calc
    C * Finset.sum (Finset.Icc 1 t) E ≤
        C * ((((t : K) - 1) / batch) * Finset.sum (Finset.Icc 1 t) G) := by
          exact mul_le_mul_of_nonneg_left hsumE_scaled hC_nonneg
    _ = (C * ((t : K) - 1) / batch) * Finset.sum (Finset.Icc 1 t) G := by
          ring

-- Batch 1 promoted from Staging/Icc_descent_telescope_with_error_absorption.lean
/-- A closed-interval one-step scalar bound telescopes after absorbing a sum budget.

If every step satisfies
`A (j + 1) + p * E j <= A j - c * G j + d * D j`, and the accumulated
`d * D` contribution is bounded by `errorCoeff` times the accumulated gap, then
the potential telescopes from `A 1` to `A (t + 1)` and the error budget reduces
the gap coefficient from `c` to `c - errorCoeff`.

Layer: Glue | Gap: Level 1 (closed-interval scalar step telescope with sum-budget absorption)
Proof: sum the pointwise inequalities over `Finset.Icc 1 t`, factor scalar
  multiples out of finite sums, rewrite the potential drops by
  `sum_Icc_sub_succ`, and apply the aggregate error budget by linear arithmetic.
Source: Mathlib finite sums over natural intervals and ordered-ring arithmetic
Used in: nonconvex variance-reduced mirror descent epochwise one-step descent
  summation after estimator-error budget absorption
Book citation: book/FOML/NonconvexVarianceReducedMirrorDescent.json#/key_lemmas
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex variance-reduced mirror descent -/
theorem sum_Icc_step_telescope_le_of_sum_budget
    {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (A E G D : ℕ → R) (p c d errorCoeff : R) (t : ℕ) (ht_pos : 1 ≤ t)
    (hstep :
      ∀ j ∈ Finset.Icc 1 t,
        A (j + 1) + p * E j ≤ A j - c * G j + d * D j)
    (herror :
      d * Finset.sum (Finset.Icc 1 t) D ≤
        errorCoeff * Finset.sum (Finset.Icc 1 t) G) :
    A (t + 1) + p * Finset.sum (Finset.Icc 1 t) E ≤
      A 1 - (c - errorCoeff) * Finset.sum (Finset.Icc 1 t) G := by
  classical
  have hstep' :
      ∀ j ∈ Finset.Icc 1 t,
        p * E j ≤ (A j - A (j + 1)) - c * G j + d * D j := by
    intro j hj
    have hj_step := hstep j hj
    linarith
  have hsum :
      p * Finset.sum (Finset.Icc 1 t) E ≤
        Finset.sum (Finset.Icc 1 t) (fun j => A j - A (j + 1)) -
          c * Finset.sum (Finset.Icc 1 t) G +
          d * Finset.sum (Finset.Icc 1 t) D := by
    have hsum_step :
        Finset.sum (Finset.Icc 1 t) (fun j => p * E j) ≤
          Finset.sum (Finset.Icc 1 t)
            (fun j => (A j - A (j + 1)) - c * G j + d * D j) := by
      exact Finset.sum_le_sum hstep'
    calc
      p * Finset.sum (Finset.Icc 1 t) E =
          Finset.sum (Finset.Icc 1 t) (fun j => p * E j) := by
            rw [Finset.mul_sum]
      _ ≤
          Finset.sum (Finset.Icc 1 t)
            (fun j => (A j - A (j + 1)) - c * G j + d * D j) := hsum_step
      _ =
          Finset.sum (Finset.Icc 1 t) (fun j => A j - A (j + 1)) -
            c * Finset.sum (Finset.Icc 1 t) G +
            d * Finset.sum (Finset.Icc 1 t) D := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
              Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
  have htelescope :
      Finset.sum (Finset.Icc 1 t) (fun j => A j - A (j + 1)) =
        A 1 - A (t + 1) := by
    exact sum_Icc_sub_succ A 1 t ht_pos
  have hcombined :
      p * Finset.sum (Finset.Icc 1 t) E ≤
        A 1 - A (t + 1) -
          c * Finset.sum (Finset.Icc 1 t) G +
          errorCoeff * Finset.sum (Finset.Icc 1 t) G := by
    rw [htelescope] at hsum
    linarith
  linarith

-- Batch 1 promoted from Staging/norm_sq_add_inner_le_stoch_sq_add_delta_sq_of_perturb_budget.lean
/-- A perturbation budget controls a squared norm plus a residual inner product.

If `x` is within `‖err‖` of `base`, and the scalar budget
`gamma + 4 * p ≤ 2 * p / q` holds, then the squared norm of `x` and the
`gamma`-scaled residual inner product are absorbed by the squares of `base` and
`err`.

Layer: Glue | Gap: Level 1 (combined Hilbert perturbation Young budget)
Proof: use the triangle inequality to bound `‖x‖` by
  `‖base‖ + ‖err‖`, Cauchy-Schwarz for the inner product, and the scalar
  budget as a discriminant condition for the remaining quadratic form.
Source: Mathlib real Hilbert-space Cauchy-Schwarz, norm triangle inequality,
  and ordered-field square completion APIs
Book citation: book/FOML/NonconvexVarianceReducedMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex variance-reduced mirror descent -/
theorem norm_sq_add_inner_le_base_sq_add_err_sq_of_norm_sub_le_of_budget
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    {gamma p q : ℝ} (hgamma : 0 ≤ gamma) (hp : 0 < p) (hq : 0 < q)
    (hbudget : gamma + 4 * p ≤ 2 * p / q)
    {x base err : E}
    (hdist : ‖x - base‖ ≤ ‖err‖) :
    p * ‖x‖ ^ 2 + gamma * ⟪err, base⟫_ℝ ≤
      2 * p * ‖base‖ ^ 2 + (gamma / (2 * q) + 2 * p) * ‖err‖ ^ 2 := by
  have hq_ne : q ≠ 0 := ne_of_gt hq
  have hp_nonneg : 0 ≤ p := le_of_lt hp
  have hnorm_x : ‖x‖ ≤ ‖base‖ + ‖err‖ := by
    calc
      ‖x‖ = ‖base + (x - base)‖ := by
        congr 1
        abel
      _ ≤ ‖base‖ + ‖x - base‖ := norm_add_le base (x - base)
      _ ≤ ‖base‖ + ‖err‖ := by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_left hdist ‖base‖
  have hnorm_x_sq : ‖x‖ ^ 2 ≤ (‖base‖ + ‖err‖) ^ 2 := by
    exact sq_le_sq'
      (by nlinarith [norm_nonneg x, norm_nonneg base, norm_nonneg err])
      hnorm_x
  have hx_part :
      p * ‖x‖ ^ 2 ≤ p * (‖base‖ + ‖err‖) ^ 2 := by
    exact mul_le_mul_of_nonneg_left hnorm_x_sq hp_nonneg
  have hinner : ⟪err, base⟫_ℝ ≤ ‖err‖ * ‖base‖ :=
    real_inner_le_norm err base
  have hinner_part :
      gamma * ⟪err, base⟫_ℝ ≤ gamma * (‖err‖ * ‖base‖) := by
    exact mul_le_mul_of_nonneg_left hinner hgamma
  have hdisc :
      (2 * p + gamma) ^ 2 ≤ 4 * p * (gamma / (2 * q) + p) := by
    have hb := mul_le_mul_of_nonneg_left hbudget hgamma
    field_simp [hq_ne] at hb ⊢
    nlinarith
  have hquad_nonneg :
      0 ≤ p * ‖base‖ ^ 2 + (gamma / (2 * q) + p) * ‖err‖ ^ 2 -
        (2 * p + gamma) * (‖err‖ * ‖base‖) := by
    have hsq :
        0 ≤ (2 * p * ‖base‖ - (2 * p + gamma) * ‖err‖) ^ 2 :=
      sq_nonneg _
    have hdisc_scaled :
        (2 * p + gamma) ^ 2 * ‖err‖ ^ 2 ≤
          (4 * p * (gamma / (2 * q) + p)) * ‖err‖ ^ 2 := by
      exact mul_le_mul_of_nonneg_right hdisc (sq_nonneg ‖err‖)
    nlinarith [hp]
  have hscalar :
      p * (‖base‖ + ‖err‖) ^ 2 + gamma * (‖err‖ * ‖base‖) ≤
        2 * p * ‖base‖ ^ 2 + (gamma / (2 * q) + 2 * p) * ‖err‖ ^ 2 := by
    nlinarith [hquad_nonneg]
  nlinarith

-- Batch 1 promoted from Staging/div_natCast_max_one_ceil_div_le.lean
/-- Dividing a scalar budget by its positive natural ceiling horizon is at most
the tolerance.

For `eta > 0`, the positive natural horizon
`max 1 (Nat.ceil (A / eta))` is large enough that `A / N <= eta`.

Layer: Glue | Gap: Level 0 (positive ceiling denominator bound)
Proof: use the positive-ceiling lower bound for `A / eta`, clear the positive
  denominator `eta`, then clear the positive natural horizon denominator.
Source: Mathlib natural ceiling, natural-number maximum, and ordered-field
  division APIs
Used in: variance-reduced stochastic mirror descent complexity proofs selecting
  an iteration horizon from a real accuracy budget
Book citation: book/FOML/NonconvexVarianceReducedMirrorDescent.json#/algorithm_spec/parameters
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex variance-reduced mirror descent -/
theorem div_natCast_max_one_ceil_div_le {K : Type*}
    [Semifield K] [LinearOrder K] [IsStrictOrderedRing K] [FloorSemiring K]
    (A eta : K) (heta : 0 < eta) :
    A / ((max 1 (Nat.ceil (A / eta)) : ℕ) : K) ≤ eta := by
  let N : ℕ := max 1 (Nat.ceil (A / eta))
  have hN_pos_nat : 0 < N := by
    exact Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 (Nat.ceil (A / eta)))
  have hN_pos : 0 < (N : K) := by
    exact_mod_cast hN_pos_nat
  have hN_lower : A / eta ≤ (N : K) := by
    have hceil : A / eta ≤ (Nat.ceil (A / eta) : K) :=
      Nat.le_ceil (A / eta)
    have hmax : (Nat.ceil (A / eta) : K) ≤ (N : K) := by
      change (Nat.ceil (A / eta) : K) ≤
        ((max 1 (Nat.ceil (A / eta)) : ℕ) : K)
      exact_mod_cast (Nat.le_max_right 1 (Nat.ceil (A / eta)))
    exact hceil.trans hmax
  have hA_le : A ≤ eta * (N : K) := by
    have hmul := (div_le_iff₀ heta).mp hN_lower
    simpa [mul_comm] using hmul
  change A / (N : K) ≤ eta
  rw [div_le_iff₀ hN_pos]
  exact hA_le

-- Batch 1 promoted from Staging/sum_Icc_one_add_eq_sum_Icc_one_add_shift.lean
/-- Split a one-based closed-prefix sum into an initial prefix and a shifted tail.

For any additive commutative monoid-valued sequence, the sum over
`{1, ..., a + t}` is the sum over `{1, ..., a}` plus the shifted tail
indexed by `{1, ..., t}`.

Layer: Glue | Gap: Level 0 (one-based closed-interval prefix split)
Proof: induction on the tail length, peeling the final endpoint from both
  closed intervals with `Finset.sum_Icc_succ_top` and reassociating sums.
Source: Mathlib finite sums over natural intervals
Used in: variance-reduced stochastic mirror descent epoch-to-global prefix split
Book citation: book/FOML/NonconvexVarianceReducedMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex variance-reduced mirror descent -/
theorem sum_Icc_one_add_eq_sum_Icc_one_add_shift
    {R : Type*} [AddCommMonoid R] (A : ℕ → R) (a t : ℕ) :
    Finset.sum (Finset.Icc 1 (a + t)) A =
      Finset.sum (Finset.Icc 1 a) A +
        Finset.sum (Finset.Icc 1 t) (fun j => A (a + j)) := by
  induction t with
  | zero =>
      simp
  | succ t ih =>
      have htop_left : 1 ≤ a + t + 1 := by omega
      have htop_right : 1 ≤ t + 1 := by omega
      rw [Nat.add_succ, Finset.sum_Icc_succ_top htop_left,
        Finset.sum_Icc_succ_top htop_right, ih]
      simp [add_assoc]

/-- The prefix/offset `Sum` index map is injective when the two Nat-index ranges are disjoint.

The left branch sends `r : Fin N` to `r.val`; the right branch sends
`r : Fin t` to `offset + r.val`.  A disjointness proof between the prefix range
and the offset image rules out cross-branch collisions.

Layer: Glue | Gap: Level 1 (finite prefix-offset Sum index embedding)
Proof: split on the two `Sum` branches; same-branch collisions reduce to
  injectivity of `Fin.val` and addition by a fixed offset, while cross-branch
  collisions contradict the supplied finset disjointness.
Source: Mathlib finite sets, `Fin`, `Sum`, and natural-number arithmetic APIs
Used in: randomized accelerated proximal-point prefix/fresh-block independence
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
theorem sum_fin_range_offset_injective_of_disjoint
    (N offset t : ℕ)
    (hdisj :
      Disjoint
        (Finset.range N)
        (Finset.image (fun r : Fin t => offset + r.1) Finset.univ)) :
    Function.Injective (fun z : Fin N ⊕ Fin t =>
      match z with
      | Sum.inl r => r.1
      | Sum.inr r => offset + r.1) := by
  classical
  intro a b hab
  cases a with
  | inl r =>
      cases b with
      | inl q =>
          have hnat : r.1 = q.1 := by
            simpa using hab
          exact congrArg Sum.inl (Fin.ext hnat)
      | inr q =>
          have hnat : r.1 = offset + q.1 := by
            simpa using hab
          have hrange : r.1 ∈ Finset.range N :=
            Finset.mem_range.mpr r.2
          have himage :
              r.1 ∈ Finset.image (fun u : Fin t => offset + u.1) Finset.univ := by
            rw [hnat]
            exact Finset.mem_image.mpr ⟨q, Finset.mem_univ q, rfl⟩
          exact False.elim ((Finset.disjoint_left.mp hdisj hrange) himage)
  | inr r =>
      cases b with
      | inl q =>
          have hnat : offset + r.1 = q.1 := by
            simpa using hab
          have hqrange : q.1 ∈ Finset.range N :=
            Finset.mem_range.mpr q.2
          have hrimage :
              q.1 ∈ Finset.image (fun u : Fin t => offset + u.1) Finset.univ := by
            simpa [hnat] using
              (Finset.mem_image.mpr ⟨r, Finset.mem_univ r, rfl⟩ :
                offset + r.1 ∈
                  Finset.image (fun u : Fin t => offset + u.1) Finset.univ)
          exact False.elim ((Finset.disjoint_left.mp hdisj hqrange) hrimage)
      | inr q =>
          have hnat : offset + r.1 = offset + q.1 := by
            simpa using hab
          exact congrArg Sum.inr (Fin.ext (Nat.add_left_cancel hnat))

/-- Reindex a zero-based strict-prefix subtype sum as an attached one-based interval sum.

For summands whose type depends on the proofs `1 <= t` and `t <= s`, the map
`n |-> n + 1` identifies the finite type `{n // n < s}` with `(Icc 1 s).attach`.

Layer: Glue | Gap: Level 0 (dependent finite-sum interval reindexing)
Proof: a `Finset.sum_bij` sends `n` to the attached index `n + 1`; surjectivity
  subtracts one from an attached interval point and uses `Nat.sub_add_cancel`.
Source: Mathlib finite sums over natural intervals and subtype extensionality APIs
Used in: randomized accelerated proximal-point residual-window reindexing from
  sampled strict prefixes to one-based inner-loop time windows
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
theorem sum_univ_subtype_lt_succ_eq_sum_Icc_attach
    {A : Type*} [AddCommMonoid A] (s : ℕ)
    (F : (t : ℕ) → 1 ≤ t → t ≤ s → A) :
    Finset.sum Finset.univ
        (fun n : {n : ℕ // n < s} =>
          F (n.1 + 1) (Nat.succ_pos n.1) (Nat.succ_le_of_lt n.2)) =
      Finset.sum (Finset.Icc 1 s).attach
        (fun t =>
          F t.1 (Finset.mem_Icc.mp t.2).1 (Finset.mem_Icc.mp t.2).2) := by
  classical
  refine Finset.sum_bij
    (fun n _hn =>
      ⟨n.1 + 1,
        Finset.mem_Icc.mpr ⟨Nat.succ_pos n.1, Nat.succ_le_of_lt n.2⟩⟩)
    ?_ ?_ ?_ ?_
  · intro n _hn
    exact Finset.mem_attach _ _
  · intro a _ha b _hb h
    exact Subtype.ext (Nat.succ.inj (congrArg Subtype.val h))
  · intro t ht
    rcases Finset.mem_Icc.mp t.2 with ⟨ht1, hts⟩
    refine ⟨⟨t.1 - 1, ?_⟩, Finset.mem_univ _, ?_⟩
    · have hsucc_le : (t.1 - 1) + 1 ≤ s := by
        simpa [Nat.sub_add_cancel ht1] using hts
      exact Nat.lt_of_succ_le hsucc_le
    · apply Subtype.ext
      exact Nat.sub_add_cancel ht1
  · intro n _hn
    rfl

/-- The relation `16 * c = m * (q - 1) * (q + 1)` implies two scalar rational
inequalities.

If real parameters satisfy `μ ≥ 0`, `m ≥ 1`, `q > 1`, and
`16 * c = m * (q - 1) * (q + 1)`, then the two rational inequalities hold.

Layer: Glue | Gap: Level 1 (scalar rational inequality normalization)
Proof: solve for `c`, clear the positive denominators by `field_simp`, and
  discharge the resulting polynomial inequalities with nonlinear arithmetic.
Source: Mathlib ordered-field arithmetic and real nonlinear arithmetic tactics
Used in: randomized accelerated proximal-point scalar parameter verification
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
theorem two_rational_inequalities_of_sixteen_mul_eq_mul_sub_one_mul_add_one
    {μ m c q : ℝ}
    (hμ_nonneg : 0 ≤ μ) (hm_ge_one : 1 ≤ m) (hq_gt_one : 1 < q)
    (hc : 16 * c = m * (q - 1) * (q + 1)) :
    ((m * (q + 1) / 2 - 1) * μ / 4 ≥
        (m - 1) ^ 2 * (μ * c) / (m ^ 2 * ((q - 1) / 2))) ∧
      ((m * (q + 1) / 2 - 1) * μ / 2 ≥
        (1 - 2 / (m * (q + 1))) * (μ * c) / ((q - 1) / 2) +
          (m - 1) ^ 2 * (μ * c) / (m ^ 2 * ((q - 1) / 2))) := by
  rcases lt_or_eq_of_le hμ_nonneg with hμ_pos | rfl
  · have hμ_ne : μ ≠ 0 := ne_of_gt hμ_pos
    have hm_pos : 0 < m := lt_of_lt_of_le zero_lt_one hm_ge_one
    have hm_ne : m ≠ 0 := ne_of_gt hm_pos
    have hqsub_pos : 0 < q - 1 := by linarith
    have hqsub_ne : q - 1 ≠ 0 := ne_of_gt hqsub_pos
    have hqadd_pos : 0 < q + 1 := by linarith
    have hqadd_ne : q + 1 ≠ 0 := ne_of_gt hqadd_pos
    have hm_qadd_ne : m * (q + 1) ≠ 0 := mul_ne_zero hm_ne hqadd_ne
    have hhalf_qsub_ne : (q - 1) / 2 ≠ 0 := by positivity
    have hcore_scalar : 0 ≤ (2 * m - 1) * q - 1 := by
      nlinarith [hm_ge_one, hq_gt_one]
    have hc_solve : c = m * (q - 1) * (q + 1) / 16 := by
      linarith [hc]
    have hprod_core : 0 ≤ m * (q - 1) * ((2 * m - 1) * q - 1) := by
      exact mul_nonneg (mul_nonneg (le_of_lt hm_pos) (le_of_lt hqsub_pos)) hcore_scalar
    have hprod_core_qadd_half :
        0 ≤ m * (q - 1) * (q + 1) * ((2 * m - 1) * q - 1) / 2 := by
      have hprod_core_qadd :
          0 ≤ m * (q - 1) * (q + 1) * ((2 * m - 1) * q - 1) := by
        exact mul_nonneg
          (mul_nonneg
            (mul_nonneg (le_of_lt hm_pos) (le_of_lt hqsub_pos))
            (le_of_lt hqadd_pos))
          hcore_scalar
      positivity
    have hcleared23 :
        (m - 1) ^ 2 * c * 2 ^ 2 * 4 ≤
          m ^ 2 * (q - 1) * (m * (q + 1) - 2) := by
      rw [hc_solve]
      nlinarith [hprod_core]
    have hcleared24 :
        2 ^ 3 * c * (m * (m * (q + 1) - 2) + (q + 1) * (m - 1) ^ 2) ≤
          m ^ 2 * (q + 1) * (m * (q + 1) - 2) * (q - 1) := by
      rw [hc_solve]
      nlinarith [hprod_core_qadd_half]
    constructor
    · field_simp [hμ_ne, hm_ne, hqsub_ne, hqadd_ne, hhalf_qsub_ne]
      nlinarith [hcleared23]
    · field_simp [hμ_ne, hm_ne, hqsub_ne, hqadd_ne, hm_qadd_ne, hhalf_qsub_ne]
      nlinarith [hcleared24]
  · simp

namespace SOptLib

/-- An inverse-scaled affine blend converts to the corresponding displacement identity.

If `y = (1 + tau)⁻¹ • (center + tau • xPrev)` and `1 + tau ≠ 0`, then the
scaled displacement from the refreshed point back to the previous point is the
displacement from the center to the refreshed point.

Layer: Glue | Gap: Level 0 (inverse-scaled affine-blend displacement)
Proof: multiply the defining equation by `1 + tau`, expand `(1 + tau) • y`,
  solve for `tau • xPrev`, and cancel the common `tau • y` term.
Source: Mathlib module algebra over fields and additive-group cancellation
Used in: randomized accelerated proximal-point component-memory affine refresh
  and variance-reduced memory-refresh displacement rewrites
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec/steps/5
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
theorem smul_sub_eq_sub_of_eq_inv_one_add_smul_add
    {K E : Type*} [DivisionSemiring K] [AddCommGroup E] [Module K E]
    {tau : K} (hden : (1 : K) + tau ≠ 0) {xPrev center y : E}
    (hy : y = ((1 : K) + tau)⁻¹ • (center + tau • xPrev)) :
    tau • (xPrev - y) = y - center := by
  have hscale : ((1 : K) + tau) • y = center + tau • xPrev := by
    rw [hy]
    have hmul : ((1 : K) + tau) * ((1 : K) + tau)⁻¹ = (1 : K) := by
      exact mul_inv_cancel₀ hden
    rw [smul_smul]
    rw [hmul, one_smul]
  have hscale' : y + tau • y = center + tau • xPrev := by
    simpa [add_smul, one_smul, add_comm, add_left_comm, add_assoc] using hscale
  have hxPrev_eq : tau • xPrev = y + tau • y - center := by
    calc
      tau • xPrev = center + tau • xPrev - center := by abel
      _ = y + tau • y - center := by rw [← hscale']
  calc
    tau • (xPrev - y) = tau • xPrev - tau • y := by rw [smul_sub]
    _ = (y + tau • y - center) - tau • y := by rw [hxPrev_eq]
    _ = y - center := by abel

end SOptLib

/-- A refresh sample coordinate precedes a later recursive mini-batch cutoff.

If epoch `r` is no later than epoch `s`, the refresh mini-batch has size `m`,
`m` fits inside one epoch's `T` recursive mini-batches of size `b`, and there
is at least one initial refresh block before the recursive sample blocks, then
every refresh coordinate `r*m+i` lies before the recursive cutoff indexed by
`s * T + (t - 1)` for any within-epoch step `t`.

Layer: Glue | Gap: Level 0 (epoch refresh block before recursive cutoff)
Proof: bound `r*m+i` by the end of epoch `s`'s refresh block, compare `m` with
  `T*b`, use `1 ≤ N` to pay for the final refresh block, and unfold the
  fixed-epoch encoder to expose the recursive cutoff.
Source: Mathlib natural-number ordered semiring arithmetic
Used in: stochastic variance-reduced conditional-gradient adaptedness of
  refresh-gradient sums before later recursive mini-batch samples
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/steps/0
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem refresh_index_lt_epoch_recursive_cutoff
    {N m T b r s t i : ℕ}
    (hr : r ≤ s)
    (hi : i < m)
    (hN_pos : 1 ≤ N)
    (hm_le_T_mul_b : m ≤ T * b) :
    r * m + i < N * m + (s * T + (t - 1)) * b := by
  have hri : r * m + i < r * m + m := by
    omega
  have hrsm : r * m + m ≤ s * m + m := by
    exact Nat.add_le_add_right (Nat.mul_le_mul_right m hr) m
  have hsm : s * m ≤ s * (T * b) := by
    exact Nat.mul_le_mul_left s hm_le_T_mul_b
  have hmN : m ≤ N * m := by
    nlinarith
  have hbound : r * m + i < s * (T * b) + N * m := by
    have hsumm : s * m + m ≤ s * (T * b) + N * m := by
      nlinarith
    exact lt_of_lt_of_le hri (le_trans hrsm hsumm)
  have hglobal :
      s * (T * b) + N * m ≤ N * m + (s * T + (t - 1)) * b := by
    nlinarith
  exact lt_of_lt_of_le hbound hglobal

/-- The squared norm of a finite average is bounded by the average squared norm.

For any nonempty finite index set, scaling the sum of vectors by the inverse
cardinality has squared norm at most the corresponding inverse-cardinality
average of the squared norms.

Layer: Glue | Gap: Level 1 (finite-average squared-norm bound)
Proof: apply the norm triangle inequality to the vector sum, bound the square
  of the scalar norm sum by Chebyshev's finite-sum square inequality, and cancel
  the positive cardinality factor by real-field arithmetic.
Source: Mathlib normed additive groups and Chebyshev finite-sum inequalities
Used in: stochastic mini-batch estimator average second-moment control
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem norm_sq_inv_card_smul_sum_le_inv_card_mul_sum_norm_sq
    {ι E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Finset ι) (f : ι → E) (hs : 0 < s.card) :
    ‖((s.card : ℝ)⁻¹) • ∑ i ∈ s, f i‖ ^ 2 ≤
      (s.card : ℝ)⁻¹ * ∑ i ∈ s, ‖f i‖ ^ 2 := by
  have hs_pos : 0 < (s.card : ℝ) := by
    exact_mod_cast hs
  have hsum_norm : ‖∑ i ∈ s, f i‖ ≤ ∑ i ∈ s, ‖f i‖ := by
    simpa using norm_sum_le (s := s) (f := f)
  have hsq_norm : ‖∑ i ∈ s, f i‖ ^ 2 ≤ (∑ i ∈ s, ‖f i‖) ^ 2 := by
    nlinarith [hsum_norm, norm_nonneg (∑ i ∈ s, f i)]
  have hsq_sum :
      (∑ i ∈ s, ‖f i‖) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 := by
    exact sq_sum_le_card_mul_sum_sq
  calc
    ‖((s.card : ℝ)⁻¹) • ∑ i ∈ s, f i‖ ^ 2 =
        ((s.card : ℝ)⁻¹) ^ 2 * ‖∑ i ∈ s, f i‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs_pos), mul_pow]
    _ ≤ ((s.card : ℝ)⁻¹) ^ 2 * ((s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2) := by
      gcongr
      exact le_trans hsq_norm hsq_sum
    _ = (s.card : ℝ)⁻¹ * ∑ i ∈ s, ‖f i‖ ^ 2 := by
      field_simp [hs_pos.ne']

/-- A positive square-root-normalized product cannot be nonpositive.

If `D`, `sigma`, `m`, and `alphaSum` are positive real scalars, then the
normalized floor contribution `(D * sigma / sqrt m) * alphaSum` is strictly
positive, so it is impossible for it to be at most zero.

Layer: Glue | Gap: Level 0 (square-root-normalized positive product)
Proof: `sqrt m` is positive from `m > 0`; positive multiplication and division
  make the normalized coefficient and final product positive, contradicting
  `≤ 0`.
Source: Mathlib real square-root and ordered-field positivity APIs
Used in: stochastic nonconvex conditional-gradient mini-batch L1 floor
  non-erasure in the final convergence-rate obstruction
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/convergence_results
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem not_mul_div_sqrt_mul_le_zero_of_pos
    {D sigma m alphaSum : ℝ} (hD : 0 < D) (hsigma : 0 < sigma) (hm : 0 < m)
    (halphaSum : 0 < alphaSum) :
    ¬ (D * sigma / Real.sqrt m) * alphaSum ≤ 0 := by
  have hsqrt_pos : 0 < Real.sqrt m := Real.sqrt_pos.2 hm
  have hcoeff_pos : 0 < D * sigma / Real.sqrt m :=
    div_pos (mul_pos hD hsigma) hsqrt_pos
  have hterm_pos : 0 < (D * sigma / Real.sqrt m) * alphaSum :=
    mul_pos hcoeff_pos halphaSum
  intro hle
  exact (not_le_of_gt hterm_pos) hle

/-- Young's inequality with a positive scale in descent-normalized form.

For a positive scale `L`, the product `alpha * (e * D)` is bounded by a
quadratic term in `e` with coefficient `1 / (2 * L)` and a quadratic term in
`alpha * D` with coefficient `L / 2`.

Layer: Glue | Gap: Level 1 (scaled scalar Young absorption)
Proof: derive `2 * L * (alpha * (e * D)) <= e^2 + L^2 * alpha^2 * D^2` from
  the nonnegativity of a square, divide by the positive denominator `2 * L`,
  and normalize the coefficients by field arithmetic.
Source: Mathlib ordered-field arithmetic and scalar Young inequality algebra
Used in: stochastic nonconvex conditional gradient estimator-error diameter
  absorption in one-step smooth descent
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem mul_mul_le_inv_two_mul_add_half_mul_sq
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (alpha e D L : R) (hL : 0 < L) :
    alpha * (e * D) ≤
      (1 / (2 * L)) * e ^ 2 + (L / 2) * alpha ^ 2 * D ^ 2 := by
  have hsq : 0 ≤ (e - L * alpha * D) ^ 2 := sq_nonneg _
  have hmain :
      2 * L * (alpha * (e * D)) ≤ e ^ 2 + L ^ 2 * alpha ^ 2 * D ^ 2 := by
    nlinarith [hsq]
  have hden_pos : 0 < 2 * L := mul_pos two_pos hL
  calc
    alpha * (e * D) =
        (2 * L * (alpha * (e * D))) / (2 * L) := by
      have hden_ne : 2 * L ≠ 0 := ne_of_gt hden_pos
      calc
        alpha * (e * D) = (alpha * (e * D)) * ((2 * L) / (2 * L)) := by
          rw [div_self hden_ne]
          ring
        _ = (2 * L * (alpha * (e * D))) / (2 * L) := by
          field_simp [hden_ne]
    _ ≤ (e ^ 2 + L ^ 2 * alpha ^ 2 * D ^ 2) / (2 * L) := by
      exact div_le_div_of_nonneg_right hmain (le_of_lt hden_pos)
    _ = (1 / (2 * L)) * e ^ 2 + (L / 2) * alpha ^ 2 * D ^ 2 := by
      field_simp [ne_of_gt hL, ne_of_gt hden_pos]

/-- A finite image over a nonempty finite index type has attained min and max selectors.

This packages the common finite-run facts for `Finset.univ.image value`: the
image is nonempty, its `min'` and `max'` are attained by indices, and every
indexed value lies between those selected extrema.

Layer: Glue | Gap: Level 0 (finite image extremum selector package)
Proof: choose an index for nonemptiness, use `Finset.min'_mem` and
  `Finset.max'_mem` for selector membership, and recover indices with
  `Finset.mem_image`; comparisons use `Finset.min'_le` and `Finset.le_max'`.
Source: Mathlib finite-set extrema API for linearly ordered finsets
Used in: nonconvex stochastic mirror descent finite-run exact stationarity and validation-error extrema
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/convergence_results/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, nonconvex stochastic mirror descent -/
theorem finite_image_min_max_attainment_pack
    {ι α : Type*} [Fintype ι] [Nonempty ι] [LinearOrder α]
    (value : ι → α) :
    (Finset.univ.image value).Nonempty ∧
      (∀ h : (Finset.univ.image value).Nonempty,
        ∃ i : ι, (Finset.univ.image value).min' h = value i) ∧
      (∀ (h : (Finset.univ.image value).Nonempty) (i : ι),
        (Finset.univ.image value).min' h ≤ value i) ∧
      (∀ h : (Finset.univ.image value).Nonempty,
        ∃ i : ι, (Finset.univ.image value).max' h = value i) ∧
      (∀ (h : (Finset.univ.image value).Nonempty) (i : ι),
        value i ≤ (Finset.univ.image value).max' h) := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨i⟩ := ‹Nonempty ι›
    exact ⟨value i, by simp⟩
  · intro h
    have hmem :
        (Finset.univ.image value).min' h ∈ Finset.univ.image value :=
      Finset.min'_mem (Finset.univ.image value) h
    rcases Finset.mem_image.mp hmem with ⟨i, _hi, hi⟩
    exact ⟨i, hi.symm⟩
  · intro _h i
    exact Finset.min'_le (Finset.univ.image value) (value i) (by simp)
  · intro h
    have hmem :
        (Finset.univ.image value).max' h ∈ Finset.univ.image value :=
      Finset.max'_mem (Finset.univ.image value) h
    rcases Finset.mem_image.mp hmem with ⟨i, _hi, hi⟩
    exact ⟨i, hi.symm⟩
  · intro _h i
    exact Finset.le_max' (Finset.univ.image value) (value i) (by simp)

/-- Centering commutes with a finite average whose denominator is the finset cardinality.

This rewrites the average of `z i - c` over a nonempty finset as the average
of `z i` minus the same constant `c`.

Layer: Glue | Gap: Level 1 (finite average centering algebra)
Proof: expand finite sums over subtraction and constants, then cancel the
  cardinality factor using scalar associativity and the nonzero cardinality.
Source: Mathlib finite sums, modules over real scalars, and field simplification
Used in: stochastic mirror descent mini-batch residual centering
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem inv_card_smul_sum_sub_const_eq
    {ι E : Type*} [AddCommGroup E] [Module ℝ E]
    (s : Finset ι) (z : ι → E) (c : E) (hs : 0 < s.card) :
    ((s.card : ℝ)⁻¹) • Finset.sum s (fun i => z i - c) =
      ((s.card : ℝ)⁻¹) • Finset.sum s z - c := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, smul_sub]
  congr 1
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  have hcard_ne : (s.card : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hs
  have hmul : (s.card : ℝ)⁻¹ * (s.card : ℝ) = 1 := by
    field_simp [hcard_ne]
  rw [hmul, one_smul]

/-- A finite indexed real minimum is strictly above a threshold iff every indexed value is.

For a nonempty finite index type, the minimum is represented by Mathlib's
`Finset.min'` on the universal image of the indexed family.

Layer: Glue | Gap: Level 0 (finite indexed strict minimum tail equivalence)
Proof: one direction uses `Finset.min'_le` for each indexed value; the reverse
  direction uses `Finset.min'_mem` to recover an index attaining the finite minimum.
Source: Mathlib finite-set image and minimum APIs for linearly ordered finsets
Used in: nonconvex stochastic mirror descent conversion from strict finite
  optimization minimum tail to all-runs strict exact projected-gradient tail
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/convergence_results/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
theorem finite_min_gt_iff_forall_gt
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → ℝ) (t : ℝ) :
    (Finset.univ.image f).min'
        (by
          classical
          exact ⟨f (Classical.choice inferInstance), by simp⟩) > t ↔
      ∀ i : ι, f i > t := by
  classical
  constructor
  · intro h i
    exact lt_of_lt_of_le h (Finset.min'_le (Finset.univ.image f) (f i) (by simp))
  · intro h
    let hnonempty : (Finset.univ.image f).Nonempty :=
      ⟨f (Classical.choice inferInstance), by simp⟩
    have hmem :
        (Finset.univ.image f).min' hnonempty ∈ Finset.univ.image f :=
      Finset.min'_mem (Finset.univ.image f) hnonempty
    rcases Finset.mem_image.mp hmem with ⟨i, _hi, hi⟩
    simpa [hnonempty, hi] using h i

namespace Finset

/-- A finite sum is positive when every summand on a nonempty support is positive.

This names the common finite-support positivity pattern for ordered additive
commutative monoids, separating the nonempty witness from the pointwise
strict-positivity hypothesis.

Layer: Glue | Gap: Level 0 (finite sum positivity from nonempty support)
Proof: direct application of Mathlib's `Finset.sum_pos`, which proves strict
  positivity by comparing the sum with the zero sum over the same nonempty set.
Source: Mathlib finite sums over ordered additive commutative monoids
Used in: nonconvex stochastic mirror descent randomized output denominator positivity
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/output/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
theorem sum_pos_of_nonempty {ι α : Type*}
    [AddCommMonoid α] [Preorder α] [IsOrderedCancelAddMonoid α] [AddLeftStrictMono α]
    (s : Finset ι) (w : ι → α)
    (hw_pos : ∀ i ∈ s, 0 < w i)
    (hs_nonempty : s.Nonempty) :
    0 < ∑ i ∈ s, w i := by
  exact Finset.sum_pos hw_pos hs_nonempty

end Finset

/-- Absorb a product-controlled cross term into one half-square and two residual squares.

If `ip` is bounded by `a * (b + a)` and the active weight satisfies `w = γ / 2`,
then multiplying by a nonnegative `γ` is controlled by the Young inequality
`a * b ≤ a ^ 2 + b ^ 2 / 4`.

Layer: Glue | Gap: Level 1 (Young absorption for product-controlled cross terms)
Proof: multiply the assumed cross-term bound by the nonnegative coefficient
  and combine it with the scalar Young inequality proved from a square.
Source: Mathlib real ordered-ring arithmetic and Young inequality algebra
Used in: nonconvex stochastic mirror descent residual/exact projected-gradient
  cross-term absorption in the one-step descent recursion
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
theorem mul_le_half_sq_add_two_mul_sq_of_le_mul_add
    {γ w a b ip : ℝ}
    (hγ : 0 ≤ γ) (hw : w = γ / 2)
    (hinner : ip ≤ a * (b + a)) :
    γ * ip ≤ (w / 2) * b ^ 2 + 2 * γ * a ^ 2 := by
  have hyoung : a * b ≤ a ^ 2 + (1 / 4 : ℝ) * b ^ 2 := by
    nlinarith [sq_nonneg (a - b / 2)]
  have hmul := mul_le_mul_of_nonneg_left hinner hγ
  nlinarith [hmul, hyoung, hw]

/-- A real number is bounded by the positive natural totalization of its ceiling.

For any real requirement `x`, taking `Nat.ceil x` and then wrapping the
natural number in `max 1` preserves the lower bound after casting back to
`ℝ`.

Layer: Glue | Gap: Level 0 (positive ceiling lower bound)
Proof: first bound `x` by its natural ceiling using `Nat.le_ceil`, then use the
  right branch of the natural-number maximum and cast the inequality to `ℝ`.
Source: Mathlib natural ceiling and natural-number lattice-order APIs
Used in: two-phase randomized stochastic mirror descent validation sample
  count lower bound for the post-optimization empirical check
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/parameters
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
theorem le_positive_ceil_max_one (x : ℝ) :
    x ≤ ((max 1 (Nat.ceil x)) : ℕ) := by
  exact le_trans (Nat.le_ceil x)
    (by
      change (Nat.ceil x : ℝ) ≤ ((max 1 (Nat.ceil x)) : ℕ)
      exact_mod_cast (Nat.le_max_right 1 (Nat.ceil x)))

/-- A validation-count lower bound makes the variance validation term at most half
the target tolerance.

If the chosen validation count `T` dominates
`24 * S * σ ^ 2 / (Λ * ε)`, then the variance contribution
`6 * (2 * S / Λ) * σ ^ 2 / T` is bounded by `ε / 2`.

Layer: Glue | Gap: Level 1 (validation-count algebra packaging)
Proof: clear denominators using positivity of `Λ`, `ε`, and `T`; normalize the
  displayed validation term by field simplification and finish by nonlinear arithmetic.
Source: Mathlib ordered field division and nonlinear real arithmetic APIs
Used in: stochastic mirror descent validation sample count controls selected-output variance
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic mirror descent -/
theorem validation_term_le_half_of_count_choice
    (S σ T ε Λ : ℝ)
    (hε : 0 < ε) (hΛ_pos : 0 < Λ) (hT_pos : 0 < T)
    (hT_lower : 24 * S * σ ^ 2 / (Λ * ε) ≤ T) :
    6 * (2 * S / Λ) * σ ^ 2 / T ≤ ε / 2 := by
  have hden_pos : 0 < Λ * ε := mul_pos hΛ_pos hε
  have hT_lower' : 24 * S * σ ^ 2 ≤ T * (Λ * ε) := by
    rwa [div_le_iff₀ hden_pos] at hT_lower
  calc
    6 * (2 * S / Λ) * σ ^ 2 / T =
        12 * S * σ ^ 2 / (Λ * T) := by
      field_simp [ne_of_gt hΛ_pos, ne_of_gt hT_pos]
      ring
    _ ≤ ε / 2 := by
      rw [div_le_iff₀ (mul_pos hΛ_pos hT_pos)]
      nlinarith

/-- The expanded RSMD one-run budget bound at the totalized paper budget choice is at most half the target accuracy.

The three ceiling lower bounds in the positive budget choice control the
deterministic descent term, the stochastic balancing term, and the internal
maximum in the budget formula, leaving the displayed `ε / 2` budget split.

Layer: Glue | Gap: Level 1 (closed-form stochastic mirror descent budget arithmetic)
Proof: use the three ceiling lower bounds for the selected natural budget,
  reduce the maximum in the budget formula to `1`, and finish the two budget
  terms by ordered-field arithmetic and square-root monotonicity.
Source: Mathlib real square-root, natural ceiling, maximum, and ordered-field APIs
Used in: two-phase randomized stochastic mirror descent proof that the selected per-run SFO budget makes the one-run stationarity budget contribute at most half of the accuracy target
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/parameters
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
theorem budget_bound_le_half_of_budget_choice
    (L D σ Dtilde ε : ℝ)
    (hL_pos : 0 < L) (hDtilde_pos : 0 < Dtilde) (hσ_nonneg : 0 ≤ σ)
    (hε : 0 < ε) :
    let N : ℕ :=
      max 1
        (Nat.ceil
          (max
            (max (512 * L ^ 2 * D ^ 2 / ε)
              (((Dtilde + D ^ 2 / Dtilde) *
                  (128 * Real.sqrt 6 * L * σ / ε)) ^ 2))
            (3 * σ ^ 2 / (8 * L ^ 2 * Dtilde ^ 2))))
    8 * L *
      (16 * L * D ^ 2 / (N : ℝ) +
        4 * Real.sqrt 6 * σ / Real.sqrt (N : ℝ) *
          (D ^ 2 / Dtilde +
            Dtilde *
              max 1 (Real.sqrt 6 * σ /
                (4 * L * Dtilde * Real.sqrt (N : ℝ))))) ≤ ε / 2 := by
  dsimp only
  let N : ℕ :=
    max 1
      (Nat.ceil
        (max
          (max (512 * L ^ 2 * D ^ 2 / ε)
            (((Dtilde + D ^ 2 / Dtilde) *
                (128 * Real.sqrt 6 * L * σ / ε)) ^ 2))
          (3 * σ ^ 2 / (8 * L ^ 2 * Dtilde ^ 2))))
  have hN_nat : 0 < N := by
    dsimp [N]
    exact Nat.lt_of_lt_of_le (by norm_num) (Nat.le_max_left 1 _)
  have hN : 0 < (N : ℝ) := by
    exact_mod_cast hN_nat
  have hsqrtN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hN
  rcases le_positive_ceil_threeway_max
      (512 * L ^ 2 * D ^ 2 / ε)
      (((Dtilde + D ^ 2 / Dtilde) *
          (128 * Real.sqrt 6 * L * σ / ε)) ^ 2)
      (3 * σ ^ 2 / (8 * L ^ 2 * Dtilde ^ 2)) with ⟨hA, hB, hC⟩
  have hfirst :
      128 * L ^ 2 * D ^ 2 / (N : ℝ) ≤ ε / 4 := by
    have hA' :
        512 * L ^ 2 * D ^ 2 ≤ (N : ℝ) * ε := by
      have hA0 : 512 * L ^ 2 * D ^ 2 / ε ≤ (N : ℝ) := by
        simpa [N] using hA
      rw [div_le_iff₀ hε] at hA0
      simpa [mul_comm, mul_left_comm, mul_assoc] using hA0
    rw [div_le_iff₀ hN]
    nlinarith
  have hmax :
      max 1 (Real.sqrt 6 * σ /
        (4 * L * Dtilde * Real.sqrt (N : ℝ))) = 1 := by
    let r : ℝ := Real.sqrt 6 * σ /
      (4 * L * Dtilde * Real.sqrt (N : ℝ))
    have hden_pos : 0 < 4 * L * Dtilde * Real.sqrt (N : ℝ) := by
      have hpos := mul_pos
        (mul_pos (mul_pos (show 0 < (4 : ℝ) by norm_num) hL_pos)
          hDtilde_pos) hsqrtN
      simpa [mul_assoc] using hpos
    have hr_nonneg : 0 ≤ r := by
      dsimp [r]
      exact div_nonneg (mul_nonneg (Real.sqrt_nonneg 6) hσ_nonneg)
        (le_of_lt hden_pos)
    have hdenC_pos : 0 < 8 * L ^ 2 * Dtilde ^ 2 := by
      have hL_sq : 0 < L ^ 2 :=
        sq_pos_of_ne_zero (ne_of_gt hL_pos)
      have hD_sq : 0 < Dtilde ^ 2 :=
        sq_pos_of_ne_zero (ne_of_gt hDtilde_pos)
      exact mul_pos (mul_pos (show 0 < (8 : ℝ) by norm_num) hL_sq) hD_sq
    have hC' :
        3 * σ ^ 2 ≤ (N : ℝ) * (8 * L ^ 2 * Dtilde ^ 2) := by
      have hC0 : 3 * σ ^ 2 / (8 * L ^ 2 * Dtilde ^ 2) ≤ (N : ℝ) := by
        simpa [N] using hC
      rw [div_le_iff₀ hdenC_pos] at hC0
      simpa [mul_comm, mul_left_comm, mul_assoc] using hC0
    have hnumden_sq :
        (Real.sqrt 6 * σ) ^ 2 ≤
          (4 * L * Dtilde * Real.sqrt (N : ℝ)) ^ 2 := by
      rw [mul_pow, mul_pow, mul_pow]
      rw [Real.sq_sqrt (show 0 ≤ (6 : ℝ) by norm_num), Real.sq_sqrt (le_of_lt hN)]
      ring_nf
      nlinarith
    have hr_sq_le : r ^ 2 ≤ 1 := by
      dsimp [r]
      rw [div_pow]
      rw [div_le_iff₀ (pow_pos hden_pos 2)]
      simpa using hnumden_sq
    have hr_le_one : r ≤ 1 := by
      have hr_sq_le' : r ^ 2 ≤ 1 ^ 2 := by
        simpa using hr_sq_le
      exact (sq_le_sq₀ hr_nonneg zero_le_one).mp hr_sq_le'
    simpa [r] using max_eq_left hr_le_one
  have hsecond :
      32 * Real.sqrt 6 * L * σ / Real.sqrt (N : ℝ) *
          (D ^ 2 / Dtilde + Dtilde) ≤ ε / 4 := by
    let B : ℝ :=
      (Dtilde + D ^ 2 / Dtilde) *
        (128 * Real.sqrt 6 * L * σ / ε)
    have hA_nonneg : 0 ≤ Dtilde + D ^ 2 / Dtilde := by
      exact add_nonneg (le_of_lt hDtilde_pos)
        (div_nonneg (sq_nonneg D) (le_of_lt hDtilde_pos))
    have hfactor_nonneg : 0 ≤ 128 * Real.sqrt 6 * L * σ / ε := by
      exact div_nonneg
        (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg 6))
          (le_of_lt hL_pos)) hσ_nonneg)
        (le_of_lt hε)
    have hB_nonneg : 0 ≤ B := by
      dsimp [B]
      exact mul_nonneg hA_nonneg hfactor_nonneg
    have hB_sqrt : B ≤ Real.sqrt (N : ℝ) := by
      have hB0 : B ^ 2 ≤ (N : ℝ) := by
        simpa [B, N, add_comm] using hB
      have hsqrt := Real.sqrt_le_sqrt hB0
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hB_nonneg] at hsqrt
      exact hsqrt
    dsimp [B] at hB_sqrt
    field_simp [ne_of_gt hε, ne_of_gt hsqrtN, ne_of_gt hDtilde_pos] at hB_sqrt ⊢
    ring_nf at hB_sqrt ⊢
    nlinarith
  calc
    8 * L *
      (16 * L * D ^ 2 / (N : ℝ) +
        4 * Real.sqrt 6 * σ / Real.sqrt (N : ℝ) *
          (D ^ 2 / Dtilde +
            Dtilde *
              max 1 (Real.sqrt 6 * σ /
                (4 * L * Dtilde * Real.sqrt (N : ℝ)))))
        = 128 * L ^ 2 * D ^ 2 / (N : ℝ) +
          32 * Real.sqrt 6 * L * σ / Real.sqrt (N : ℝ) *
            (D ^ 2 / Dtilde + Dtilde) := by
          rw [hmax]
          ring
    _ ≤ ε / 4 + ε / 4 := add_le_add hfirst hsecond
    _ = ε / 2 := by ring

/-- A zero-based telescoping sum is bounded by its first term when the tail is nonnegative.

For any ordered additive group, the range sum of successive drops
`A t - A (t + 1)` telescopes to `A 0 - A j`; a nonnegative terminal value
therefore gives an upper bound by `A 0`.

Layer: Glue | Gap: Level 0 (range telescope inequality with nonnegative tail)
Proof: rewrite the finite range sum with Mathlib's `Finset.sum_range_sub'`,
  then apply the ordered-additive-group fact that subtracting a nonnegative
  element does not increase a value.
Source: Mathlib finite sums over natural ranges and ordered additive groups
Used in: stochastic block mirror descent aggregate Bregman potential telescope
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem sum_range_sub_succ_le_first_of_last_nonneg
    {α : Type*} [AddCommGroup α] [LE α] [AddLeftMono α]
    (A : ℕ → α) (j : ℕ) (hterm : 0 ≤ A j) :
    (∑ t ∈ Finset.range j, (A t - A (t + 1))) ≤ A 0 := by
  rw [Finset.sum_range_sub']
  exact sub_le_self (A 0) hterm

/-- A square sum over a finite set is bounded by a cardinality ceiling times the
square of a pointwise maximum.

If every term `a i` on `s` is nonnegative and at most `M`, and `s.card` is at
most the natural budget `b`, then the sum of squared terms is at most
`b * M^2`.

Layer: Glue | Gap: Level 0 (finite square-sum maximum bound)
Proof: square each pointwise nonnegative bound, apply `Finset.sum_le_card_nsmul`
  to compare the finite sum with a constant sum, and use the supplied
  cardinality ceiling.
Source: Mathlib finite sums and ordered real arithmetic
Used in: nonconvex stochastic conditional-gradient epoch-difference estimator
  budget controlled by the per-epoch maximum stepsize
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem sum_sq_le_card_mul_max_sq
    {ι : Type*} (s : Finset ι) (a : ι → ℝ) (M : ℝ) (b : ℕ)
    (hcard : s.card ≤ b)
    (ha_nonneg : ∀ i ∈ s, 0 ≤ a i)
    (ha_le : ∀ i ∈ s, a i ≤ M) :
    Finset.sum s (fun i => a i ^ 2) ≤ (b : ℝ) * M ^ 2 := by
  have hterm : ∀ i ∈ s, a i ^ 2 ≤ M ^ 2 := by
    intro i hi
    nlinarith [ha_nonneg i hi, ha_le i hi]
  have hsum_card :
      Finset.sum s (fun i => a i ^ 2) ≤ (s.card : ℝ) * M ^ 2 := by
    have h := Finset.sum_le_card_nsmul s (fun i => a i ^ 2) (M ^ 2) hterm
    simpa [nsmul_eq_mul] using h
  have hcard_le_b : (s.card : ℝ) ≤ b := by
    exact_mod_cast hcard
  exact le_trans hsum_card (mul_le_mul_of_nonneg_right hcard_le_b (sq_nonneg M))

/-- A triangular predecessor sum over an active prefix is bounded by `T` copies
of the active mass.

If the active set is exactly the indices in `Icc 1 T` satisfying a prefix-closed
predicate, then each lower-triangular predecessor window `i - 1`, for
`2 ≤ i ≤ j`, lies inside the same active set whenever `j` is active. Thus each
inner triangular sum is bounded by the full active sum, and summing over at most
`T` active indices gives the result.

Layer: Glue | Gap: Level 1 (active-prefix triangular predecessor counting)
Proof: reindex each predecessor window by the injective map `i ↦ i - 1`, compare
  the image sum with the active sum by subset monotonicity for nonnegative
  summands, then use the active-set cardinal bound by `Icc 1 T`.
Source: Mathlib finite sums over intervals, image sums, subset monotonicity,
  and cardinal bounds for finite sets
Used in: nonconvex stochastic conditional-gradient epochwise predecessor
  stepsize-square budget
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/main_theorem/proof/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic conditional gradient -/
theorem sum_active_triangular_predecessor_le_card_mul_sum
    (active : Finset ℕ) (T : ℕ) (a : ℕ → ℝ) (P : ℕ → Prop)
    (hactive : ∀ r, r ∈ active ↔ r ∈ Finset.Icc 1 T ∧ P r)
    (hprefix : ∀ {i j : ℕ}, i ≤ j → P j → P i)
    (ha_nonneg : ∀ r ∈ active, 0 ≤ a r) :
    Finset.sum active
        (fun j => Finset.sum (Finset.Icc 2 j) (fun i => a (i - 1))) ≤
      (T : ℝ) * Finset.sum active a := by
  classical
  have hinner :
      ∀ j ∈ active,
        Finset.sum (Finset.Icc 2 j) (fun i => a (i - 1)) ≤
          Finset.sum active a := by
    intro j hj
    let predSet : Finset ℕ := (Finset.Icc 2 j).image (fun i => i - 1)
    have hinj : Set.InjOn (fun i : ℕ => i - 1) (Finset.Icc 2 j) := by
      intro x hx y hy hxy
      simp only [Finset.mem_coe, Finset.mem_Icc] at hx hy
      have hxpred : x = (x - 1) + 1 := by omega
      have hypred : y = (y - 1) + 1 := by omega
      rw [hxpred, hypred]
      simpa [Nat.succ_eq_add_one] using congrArg Nat.succ hxy
    have hsum_image :
        Finset.sum predSet a =
          Finset.sum (Finset.Icc 2 j) (fun i => a (i - 1)) := by
      simpa [predSet] using
        (Finset.sum_image (s := Finset.Icc 2 j) (f := a)
          (g := fun i : ℕ => i - 1) hinj)
    have hsubset : predSet ⊆ active := by
      intro r hr
      rcases Finset.mem_image.mp hr with ⟨i, hi, hir⟩
      have hi' : i ∈ Finset.Icc 2 j := hi
      have hij : i ≤ j := (Finset.mem_Icc.mp hi').2
      have hji : j ∈ Finset.Icc 1 T ∧ P j := (hactive j).mp hj
      have hr_range : r ∈ Finset.Icc 1 T := by
        rw [← hir]
        simp only [Finset.mem_Icc] at hi' hji ⊢
        omega
      have hrP : P r := by
        rw [← hir]
        apply hprefix (i := i - 1) (j := j)
        · exact Nat.le_trans (Nat.sub_le i 1) hij
        · exact hji.2
      exact (hactive r).mpr ⟨hr_range, hrP⟩
    have hnonneg :
        ∀ x ∈ active, x ∉ predSet → 0 ≤ a x := by
      intro x hx _hnot
      exact ha_nonneg x hx
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hsubset hnonneg
    exact (le_of_eq hsum_image.symm).trans hle
  have hsum_to_card :
      Finset.sum active
          (fun j => Finset.sum (Finset.Icc 2 j) (fun i => a (i - 1))) ≤
        (active.card : ℝ) * Finset.sum active a := by
    calc
      Finset.sum active
          (fun j => Finset.sum (Finset.Icc 2 j) (fun i => a (i - 1)))
          ≤ Finset.sum active (fun _ => Finset.sum active a) := by
            exact Finset.sum_le_sum hinner
      _ = (active.card : ℝ) * Finset.sum active a := by
            simp [nsmul_eq_mul]
  have hcard : active.card ≤ T := by
    have hsubset_active : active ⊆ Finset.Icc 1 T := by
      intro r hr
      exact (hactive r).mp hr |>.1
    have hcard_le : active.card ≤ (Finset.Icc 1 T).card :=
      Finset.card_le_card hsubset_active
    simpa using hcard_le
  have hmass_nonneg : 0 ≤ Finset.sum active a :=
    Finset.sum_nonneg (fun r hr => ha_nonneg r hr)
  have hcard_real : (active.card : ℝ) ≤ T := by
    exact_mod_cast hcard
  exact hsum_to_card.trans (mul_le_mul_of_nonneg_right hcard_real hmass_nonneg)

/-- A multi-epoch triangular predecessor sum is bounded by a global finite-sum
budget.

For each epoch, active steps are a prefix-closed subset of `Icc 1 T`, so the
lower-triangular predecessor sum over that epoch is bounded by `T` copies of
the active indexed mass. If the active indexed mass reindexes to a global
window and `T ≤ b`, the total triangular sum is bounded by `b` times the
global window mass.

Layer: Glue | Gap: Level 1 (multi-epoch active-prefix triangular counting)
Proof: apply the one-prefix triangular predecessor bound in each epoch, sum the
  resulting inequalities, rewrite the active indexed mass as the global window
  mass, and enlarge the natural scalar budget using nonnegativity.
Source: Mathlib finite sums over intervals, active-prefix image counting, and
  ordered real scalar multiplication
Used in: nonconvex stochastic conditional-gradient global predecessor
  stepsize-square budget
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/main_theorem/proof/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic conditional gradient -/
theorem active_triangular_predecessor_sum_le_batch_mul_global_sum
    {A K : Type*} (epochs : Finset A) (active : A → Finset ℕ)
    (T b : ℕ) (idx : A → ℕ → K) (a : K → ℝ) (P : A → ℕ → Prop)
    (window : Finset K)
    (hactive : ∀ s r, r ∈ active s ↔ r ∈ Finset.Icc 1 T ∧ P s r)
    (hprefix : ∀ s {i j : ℕ}, i ≤ j → P s j → P s i)
    (hactive_eq_global :
      Finset.sum epochs (fun s => Finset.sum (active s) (fun r => a (idx s r))) =
        Finset.sum window a)
    (hb_ge_T : T ≤ b)
    (ha_nonneg : ∀ s ∈ epochs, ∀ r ∈ active s, 0 ≤ a (idx s r)) :
    Finset.sum epochs
        (fun s => Finset.sum (active s)
          (fun j => Finset.sum (Finset.Icc 2 j) (fun i => a (idx s (i - 1))))) ≤
      (b : ℝ) * Finset.sum window a := by
  classical
  let activeMass : ℝ :=
    Finset.sum epochs (fun s => Finset.sum (active s) (fun r => a (idx s r)))
  let globalMass : ℝ := Finset.sum window a
  have hone :
      ∀ s ∈ epochs,
        Finset.sum (active s)
            (fun j => Finset.sum (Finset.Icc 2 j) (fun i => a (idx s (i - 1)))) ≤
          (T : ℝ) * Finset.sum (active s) (fun r => a (idx s r)) := by
    intro s hs
    exact
      sum_active_triangular_predecessor_le_card_mul_sum
        (active := active s) (T := T) (a := fun r => a (idx s r))
        (P := P s) (hactive := hactive s)
        (hprefix := fun {i j} hij hpj => hprefix s hij hpj)
        (ha_nonneg := ha_nonneg s hs)
  have hsum_to_active :
      Finset.sum epochs
          (fun s => Finset.sum (active s)
            (fun j => Finset.sum (Finset.Icc 2 j) (fun i => a (idx s (i - 1))))) ≤
        (T : ℝ) * activeMass := by
    calc
      Finset.sum epochs
          (fun s => Finset.sum (active s)
            (fun j => Finset.sum (Finset.Icc 2 j) (fun i => a (idx s (i - 1)))))
          ≤ Finset.sum epochs
              (fun s => (T : ℝ) * Finset.sum (active s) (fun r => a (idx s r))) := by
              exact Finset.sum_le_sum hone
      _ = (T : ℝ) * activeMass := by
              dsimp [activeMass]
              rw [Finset.mul_sum]
  have hglobal_nonneg : 0 ≤ globalMass := by
    have hactive_nonneg : 0 ≤ activeMass := by
      dsimp [activeMass]
      exact Finset.sum_nonneg
        (fun s hs => Finset.sum_nonneg (fun r hr => ha_nonneg s hs r hr))
    dsimp [globalMass]
    rw [← hactive_eq_global]
    exact hactive_nonneg
  have hT_le_b_real : (T : ℝ) ≤ b := by
    exact_mod_cast hb_ge_T
  have hTb :
      (T : ℝ) * globalMass ≤ (b : ℝ) * globalMass :=
    mul_le_mul_of_nonneg_right hT_le_b_real hglobal_nonneg
  calc
    Finset.sum epochs
        (fun s => Finset.sum (active s)
          (fun j => Finset.sum (Finset.Icc 2 j) (fun i => a (idx s (i - 1)))))
        ≤ (T : ℝ) * activeMass := hsum_to_active
    _ = (T : ℝ) * globalMass := by
      dsimp [activeMass, globalMass]
      rw [hactive_eq_global]
    _ ≤ (b : ℝ) * globalMass := hTb

/-- A finite weighted residual sum vanishes around its weighted mean.

If the weights over a finite set sum to one and `μ` is the corresponding
weighted mean of a family `a`, then the weighted sum of the centered residuals
`a i - μ` is zero.

Layer: Glue | Gap: Level 0 (finite weighted residual centering)
Proof: expand scalar multiplication over subtraction, split the finite sum,
  factor the constant residual center, and cancel using weight normalization
  and the supplied weighted-mean equality.
Source: Mathlib finite sums and module scalar-distribution APIs
Used in: stochastic nonconvex conditional gradient component-gradient residual
  centering before mini-batch second-moment control
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem finset_weighted_residual_sum_eq_zero
    {K ι E : Type*} [Semiring K] [AddCommGroup E] [Module K E]
    (s : Finset ι) (q : ι → K) (a : ι → E) (μ : E)
    (hqsum : Finset.sum s q = 1)
    (hmean : Finset.sum s (fun i => q i • a i) = μ) :
    Finset.sum s (fun i => q i • (a i - μ)) = 0 := by
  calc
    Finset.sum s (fun i => q i • (a i - μ))
        =
      Finset.sum s (fun i => q i • a i) -
        Finset.sum s (fun i => q i • μ) := by
        rw [← Finset.sum_sub_distrib]
        simp [smul_sub]
    _ = μ - (Finset.sum s q) • μ := by
        rw [hmean]
        rw [Finset.sum_smul]
    _ = 0 := by
        rw [hqsum]
        simp

/-- A finite weighted centered second moment equals the uncentered second
moment minus the squared norm of the weighted mean.

For real weights summing to one on a finite set, if `μ` is the weighted
average of a Hilbert-valued family `a`, then the weighted sum of
`‖a i - μ‖ ^ 2` is the weighted sum of `‖a i‖ ^ 2` minus `‖μ‖ ^ 2`.

Layer: Glue | Gap: Level 1 (finite weighted Hilbert variance identity)
Proof: expand each centered square using the real inner-product polarization
  identity, commute finite sums through the three terms, then use the weighted
  mean and weight-normalization equalities.
Source: Mathlib finite sums and real inner-product space norm-square identities
Used in: stochastic nonconvex conditional gradient mini-batch residual variance
  reduction
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem finset_weighted_variance_eq_second_moment_sub_norm_mean_sq
    {ι E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s : Finset ι) (q : ι → ℝ) (a : ι → E) (μ : E)
    (hqsum : Finset.sum s q = 1)
    (hmean : Finset.sum s (fun i => q i • a i) = μ) :
    Finset.sum s (fun i => q i * ‖a i - μ‖ ^ 2) =
      Finset.sum s (fun i => q i * ‖a i‖ ^ 2) - ‖μ‖ ^ 2 := by
  classical
  have hinner_sum :
      Finset.sum s (fun i => q i * ⟪a i, μ⟫_ℝ) = ‖μ‖ ^ 2 := by
    calc
      Finset.sum s (fun i => q i * ⟪a i, μ⟫_ℝ)
          = Finset.sum s (fun i => ⟪q i • a i, μ⟫_ℝ) := by
              refine Finset.sum_congr rfl ?_
              intro i _hi
              rw [inner_smul_left]
              simp
      _ = ⟪Finset.sum s (fun i => q i • a i), μ⟫_ℝ := by
              simpa using
                (sum_inner (s := s) (f := fun i => q i • a i) μ).symm
      _ = ‖μ‖ ^ 2 := by
              rw [hmean]
              simp
  have hconst_sum :
      Finset.sum s (fun i => q i * ‖μ‖ ^ 2) = ‖μ‖ ^ 2 := by
    rw [← Finset.sum_mul, hqsum, one_mul]
  calc
    Finset.sum s (fun i => q i * ‖a i - μ‖ ^ 2)
        =
      Finset.sum s
        (fun i => q i * ‖a i‖ ^ 2 -
          2 * (q i * ⟪a i, μ⟫_ℝ) + q i * ‖μ‖ ^ 2) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          rw [norm_sub_sq_real]
          ring
    _ =
      Finset.sum s (fun i => q i * ‖a i‖ ^ 2) -
        2 * Finset.sum s (fun i => q i * ⟪a i, μ⟫_ℝ) +
        Finset.sum s (fun i => q i * ‖μ‖ ^ 2) := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    _ = Finset.sum s (fun i => q i * ‖a i‖ ^ 2) - ‖μ‖ ^ 2 := by
          rw [hinner_sum, hconst_sum]
          ring

namespace Finset

/-- A finite weighted centered second moment is bounded by the corresponding
uncentered second moment.

For real weights summing to one on a finite set, if `μ` is the weighted
average of a Hilbert-valued family `a`, then the weighted sum of
`‖a i - μ‖ ^ 2` is at most the weighted sum of `‖a i‖ ^ 2`.

Layer: Glue | Gap: Level 1 (finite weighted Hilbert variance bound)
Proof: rewrite the centered second moment using the finite weighted variance
  identity, then discard the nonnegative squared norm of the weighted mean.
Source: Mathlib finite sums, real inner-product norm-square identities, and
  ordered real arithmetic
Used in: stochastic nonconvex conditional gradient component-law diagonal
  residual variance budget
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem weighted_variance_le_second_moment
    {ι E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s : Finset ι) (q : ι → ℝ) (a : ι → E) (μ : E)
    (hqsum : Finset.sum s q = 1)
    (hmean : Finset.sum s (fun i => q i • a i) = μ) :
    Finset.sum s (fun i => q i * ‖a i - μ‖ ^ 2) ≤
      Finset.sum s (fun i => q i * ‖a i‖ ^ 2) := by
  rw [finset_weighted_variance_eq_second_moment_sub_norm_mean_sq
    (s := s) q a μ hqsum hmean]
  nlinarith [sq_nonneg ‖μ‖]

end Finset

/-- A weighted two-point center has squared distance bounded by the matching
weighted squared distances to its endpoints.

For a nonnegative scalar `r`, the center
`(r / (1 + r)) • u + (1 / (1 + r)) • v` has the standard Hilbert-space
two-point norm-square bound after multiplying by `(1 + r) / 2`.

Layer: Glue | Gap: Level 1 (two-point weighted-center norm-square bound)
Proof: rewrite the displacement from the center as the normalized weighted sum
  of endpoint displacements, bound its norm by the weighted sum of endpoint
  norms, and apply the real weighted-square inequality.
Source: Mathlib normed real vector spaces and ordered-field norm-square algebra
Used in: stochastic accelerated gradient descent weighted auxiliary-center
  absorption in the composite prox descent estimate
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
theorem weighted_sq_norm_sub_center_le
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    {u v y : E} {r : ℝ} (hr : 0 ≤ r) :
    ((1 + r) / 2) *
        ‖y - ((r / (1 + r)) • u + (1 / (1 + r)) • v)‖ ^ 2 ≤
      (1 / 2) * ‖v - y‖ ^ 2 + (r / 2) * ‖u - y‖ ^ 2 := by
  have hden_pos : 0 < 1 + r := by linarith
  have hden_ne : 1 + r ≠ 0 := ne_of_gt hden_pos
  have hcenter :
      y - ((r / (1 + r)) • u + (1 / (1 + r)) • v) =
        (r / (1 + r)) • (y - u) + (1 / (1 + r)) • (y - v) := by
    have hcoeff : r / (1 + r) + 1 / (1 + r) = 1 := by
      field_simp [hden_ne]
      ring
    calc
      y - ((r / (1 + r)) • u + (1 / (1 + r)) • v)
          = ((r / (1 + r)) • y + (1 / (1 + r)) • y) -
              ((r / (1 + r)) • u + (1 / (1 + r)) • v) := by
              rw [← add_smul, hcoeff, one_smul]
      _ = (r / (1 + r)) • (y - u) + (1 / (1 + r)) • (y - v) := by
              module
  rw [hcenter]
  have ha_nonneg : 0 ≤ r / (1 + r) := div_nonneg hr hden_pos.le
  have hb_nonneg : 0 ≤ 1 / (1 + r) := div_nonneg zero_le_one hden_pos.le
  have hcoef_nonneg : 0 ≤ (1 + r) / 2 := by positivity
  have hr_abs : |r| = r := abs_of_nonneg hr
  have hden_abs : |1 + r| = 1 + r := abs_of_pos hden_pos
  have hnorm :
      ‖(r / (1 + r)) • (y - u) + (1 / (1 + r)) • (y - v)‖ ≤
        (r / (1 + r)) * ‖u - y‖ + (1 / (1 + r)) * ‖v - y‖ := by
    calc
      ‖(r / (1 + r)) • (y - u) + (1 / (1 + r)) • (y - v)‖
          ≤ ‖(r / (1 + r)) • (y - u)‖ +
              ‖(1 / (1 + r)) • (y - v)‖ := norm_add_le _ _
      _ = (r / (1 + r)) * ‖u - y‖ + (1 / (1 + r)) * ‖v - y‖ := by
          simp [norm_smul, Real.norm_eq_abs, hr_abs, hden_abs, norm_sub_rev]
  have hcombo_nonneg :
      0 ≤ (r / (1 + r)) * ‖u - y‖ + (1 / (1 + r)) * ‖v - y‖ := by
    exact add_nonneg
      (mul_nonneg ha_nonneg (norm_nonneg _))
      (mul_nonneg hb_nonneg (norm_nonneg _))
  have hsq :
      ‖(r / (1 + r)) • (y - u) + (1 / (1 + r)) • (y - v)‖ ^ 2 ≤
        ((r / (1 + r)) * ‖u - y‖ + (1 / (1 + r)) * ‖v - y‖) ^ 2 := by
    nlinarith [hnorm,
      norm_nonneg ((r / (1 + r)) • (y - u) + (1 / (1 + r)) • (y - v)),
      hcombo_nonneg]
  have hweighted_sq :
      ((1 + r) / 2) *
          ((r / (1 + r)) * ‖u - y‖ + (1 / (1 + r)) * ‖v - y‖) ^ 2 ≤
        (1 / 2) * ‖v - y‖ ^ 2 + (r / 2) * ‖u - y‖ ^ 2 := by
    have hscalar :
        (r * ‖u - y‖ + ‖v - y‖) ^ 2 ≤
          (1 + r) * (r * ‖u - y‖ ^ 2 + ‖v - y‖ ^ 2) := by
      nlinarith [hr, sq_nonneg (‖u - y‖ - ‖v - y‖)]
    field_simp [hden_ne]
    nlinarith
  exact (mul_le_mul_of_nonneg_left hsq hcoef_nonneg).trans hweighted_sq

/-- A weighted scalar telescope with bridged coefficients preserves the terminal tail.

If a potential sequence `V` is nonnegative on the finite interior window and is
weighted by coefficients satisfying `c (n + 1) <= c n * beta n` there, then the
weighted drops
`c t * (V (t - 1) - beta t * V t)` over `[1, k]` are bounded by the initial
weighted potential minus the terminal weighted tail.

Layer: Glue | Gap: Level 1 (weighted scalar telescope with coefficient bridge)
Proof: induct on the right endpoint of the closed interval; the bridge
  inequality makes the newly exposed middle coefficient nonnegative, which
  carries the terminal tail through the induction.
Source: Mathlib finite sums over natural intervals and ordered real arithmetic
Used in: accelerated stochastic gradient descent Bregman-potential telescope
  under monotone estimate-sequence weights
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
theorem sum_weighted_sub_mul_le_first_sub_tail
    {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (c beta V : ℕ → R) (k : ℕ) (hk : 1 ≤ k)
    (hV_nonneg : ∀ n, 1 ≤ n → n < k → 0 ≤ V n)
    (hc_mono : ∀ n, 1 ≤ n → n < k → c (n + 1) ≤ c n * beta n) :
    Finset.sum (Finset.Icc 1 k) (fun t =>
        c t * (V (t - 1) - beta t * V t)) ≤
      c 1 * V 0 - c k * beta k * V k := by
  classical
  have hstrong : ∀ m, (hm : 1 ≤ m) → m ≤ k →
      Finset.sum (Finset.Icc 1 m) (fun t =>
          c t * (V (t - 1) - beta t * V t)) ≤
        c 1 * V 0 - c m * beta m * V m := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base =>
      intro _hbase_le
      simp
      ring_nf
      exact le_refl (c 1 * V 0 - c 1 * beta 1 * V 1)
    | succ n hn ih =>
      intro hsucc_le
      have hn1 : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
      rw [Finset.sum_Icc_succ_top hn1]
      have hpred : n + 1 - 1 = n := Nat.succ_sub_one n
      have hn_lt_k : n < k := Nat.lt_of_succ_le hsucc_le
      have hbridge : 0 ≤ (c n * beta n - c (n + 1)) * V n := by
        exact mul_nonneg (sub_nonneg.mpr (hc_mono n hn hn_lt_k))
          (hV_nonneg n hn hn_lt_k)
      have ih' := ih (Nat.le_trans (Nat.le_succ n) hsucc_le)
      rw [hpred]
      nlinarith
  exact hstrong k hk (le_refl k)

/-- A scaled linear Hilbert residual minus a positive quadratic is bounded by
the squared linear coefficient over the denominator.

If `gamma` and `D` are positive, the expression
`(M + ‖δ‖) * ‖d‖ - D / (2 * gamma) * ‖d‖^2` is bounded by the usual completed
square `gamma * (M + ‖δ‖)^2 / (2 * D)`.  The inner-product residual
`-⟪δ, d⟫` is first dominated by `‖δ‖ * ‖d‖`.

Layer: Glue | Gap: Level 1 (Hilbert residual completion square)
Proof: apply Cauchy-Schwarz to bound the inner product, then complete the
  scalar square with positive `gamma` and denominator `D`, and finally multiply
  by the nonnegative scale.
Source: Mathlib real Hilbert-space Cauchy-Schwarz and ordered-field square
  completion APIs
Used in: stochastic accelerated gradient descent stochastic-error absorption
  after the prox-model descent inequality
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec/steps/2/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
theorem scaled_linear_inner_quadratic_le_square_over_denominator
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {M gamma D a : ℝ} {δ d : E}
    (ha : 0 ≤ a) (hgamma : 0 < gamma) (hD : 0 < D) :
    a * (M * ‖d‖ - ⟪δ, d⟫_ℝ - D / (2 * gamma) * ‖d‖ ^ 2) ≤
      a * gamma * (M + ‖δ‖) ^ 2 / (2 * D) := by
  have hinner_abs : |⟪δ, d⟫_ℝ| ≤ ‖δ‖ * ‖d‖ :=
    abs_real_inner_le_norm δ d
  have hinner : -⟪δ, d⟫_ℝ ≤ ‖δ‖ * ‖d‖ := by
    exact le_trans (neg_le_abs _) hinner_abs
  have hlinear :
      M * ‖d‖ - ⟪δ, d⟫_ℝ ≤ (M + ‖δ‖) * ‖d‖ := by
    nlinarith [hinner, norm_nonneg d]
  have hsq : 0 ≤ (D * ‖d‖ - gamma * (M + ‖δ‖)) ^ 2 :=
    sq_nonneg _
  have hyoung :
      (M + ‖δ‖) * ‖d‖ - D / (2 * gamma) * ‖d‖ ^ 2 ≤
        gamma * (M + ‖δ‖) ^ 2 / (2 * D) := by
    field_simp [ne_of_gt hgamma, ne_of_gt hD]
    nlinarith [hsq, hgamma, hD]
  have hscalar :
      M * ‖d‖ - ⟪δ, d⟫_ℝ - D / (2 * gamma) * ‖d‖ ^ 2 ≤
        gamma * (M + ‖δ‖) ^ 2 / (2 * D) := by
    linarith
  have hmul := mul_le_mul_of_nonneg_left hscalar ha
  calc
    a * (M * ‖d‖ - ⟪δ, d⟫_ℝ - D / (2 * gamma) * ‖d‖ ^ 2)
        ≤ a * (gamma * (M + ‖δ‖) ^ 2 / (2 * D)) := hmul
    _ = a * gamma * (M + ‖δ‖) ^ 2 / (2 * D) := by ring

/-- Two affine-difference coefficients induced by a cross-multiplied coupling.

If `q * (1 - alpha) * (1 + mu * gamma) = alpha * (1 - q)`, then the
coefficients of the previous average and previous center in the difference
between an affine average and its search point have the normalized form used
to factor out `alpha`.

Layer: Glue | Gap: Level 1 (affine coefficient normalization)
Proof: clear the shared nonzero denominator in each scalar identity with
  field simplification, then use the cross-multiplied relation to finish the
  resulting polynomial equality.
Source: Mathlib ordered-field simplification and polynomial arithmetic APIs
Used in: stochastic accelerated gradient descent conversion of the averaged
  iterate displacement into an auxiliary-point prox displacement
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec/steps/3/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
theorem coefficients_for_average_minus_search_eq_alpha_step_minus_center
    (alpha q mu gamma : ℝ)
    (hden : 1 + mu * gamma ≠ 0)
    (hrel : q * (1 - alpha) * (1 + mu * gamma) = alpha * (1 - q)) :
    (1 - alpha) - (1 - q) =
        -(alpha * mu * gamma * (1 + mu * gamma)⁻¹) +
          alpha * q * mu * gamma * (1 + mu * gamma)⁻¹ ∧
      -q =
        -alpha * (1 + mu * gamma)⁻¹ -
          alpha * q * mu * gamma * (1 + mu * gamma)⁻¹ := by
  constructor
  · field_simp [hden]
    nlinarith [hrel]
  · field_simp [hden]
    nlinarith [hrel]

/-- Averaged-update displacement from a search point factors through a weighted center.

If the search point is `(1 - q) • xBarPrev + q • xPrev`, the weighted center
is the normalized blend of the search point and previous iterate with weights
`mu * gamma` and `1`, and the scalar `q`/`alpha` coupling holds, then the
average-minus-search displacement is `alpha` times the next-minus-center
displacement.

Layer: Glue | Gap: Level 1 (accelerated affine displacement transport)
Proof: first use the scalar coefficient-normalization lemma induced by the
  `q`/`alpha` coupling, then rewrite the vector displacement by module
  arithmetic and the weighted-center formula.
Source: accelerated stochastic approximation affine update algebra and
  Mathlib real module arithmetic APIs
Used in: stochastic accelerated gradient descent conversion of the smoothness
  displacement into the prox-center displacement in the one-step descent proof
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec/steps/2/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
theorem average_sub_search_eq_alpha_smul_step_sub_weighted_center
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (alpha q mu gamma : ℝ)
    (xBarPrev xPrev xUnder xNext xPlus : E)
    (hden : 1 + mu * gamma ≠ 0)
    (hrel : q * (1 - alpha) * (1 + mu * gamma) = alpha * (1 - q))
    (hsearch : xUnder = (1 - q) • xBarPrev + q • xPrev)
    (hcenter :
      xPlus =
        (mu * gamma / (1 + mu * gamma)) • xUnder +
          (1 / (1 + mu * gamma)) • xPrev) :
    (1 - alpha) • xBarPrev + alpha • xNext - xUnder =
      alpha • (xNext - xPlus) := by
  have hcoefs :=
    coefficients_for_average_minus_search_eq_alpha_step_minus_center
      alpha q mu gamma hden hrel
  have hcoef_bar :
      (1 - alpha) - (1 - q) =
        -(alpha * mu * gamma * (1 + mu * gamma)⁻¹) +
          alpha * q * mu * gamma * (1 + mu * gamma)⁻¹ := hcoefs.1
  have hcoef_prev :
      -q =
        -alpha * (1 + mu * gamma)⁻¹ -
          alpha * q * mu * gamma * (1 + mu * gamma)⁻¹ := hcoefs.2
  calc
    (1 - alpha) • xBarPrev + alpha • xNext - xUnder
        =
          ((1 - alpha) - (1 - q)) • xBarPrev +
            (-q) • xPrev +
              alpha • xNext := by
        rw [hsearch]
        module
    _ =
          (-(alpha * mu * gamma * (1 + mu * gamma)⁻¹) +
            alpha * q * mu * gamma * (1 + mu * gamma)⁻¹) • xBarPrev +
            (-alpha * (1 + mu * gamma)⁻¹ -
              alpha * q * mu * gamma * (1 + mu * gamma)⁻¹) • xPrev +
              alpha • xNext := by
        rw [hcoef_bar, hcoef_prev]
    _ = alpha • (xNext - xPlus) := by
        rw [hcenter, hsearch]
        field_simp [hden]
        module

/-- A weighted scalar recurrence telescopes over a finite one-based window.

If `A t` satisfies a one-step recurrence with contraction coefficient
`1 - alpha t`, source term `L`, and two additive tails `B` and `D`, and if
`Gamma` follows the same contraction from one positive time to the next, then
subtracting the `Gamma`-weighted source sum leaves exactly the initial boundary
and the two `Gamma`-normalized tail sums.

Layer: Glue | Gap: Level 1 (weighted scalar recurrence telescope with tails)
Proof: induct on the right endpoint of the closed interval. The successor case
  splits each `Finset.Icc` sum at the top index, cancels the exposed
  denominators, scales the induction hypothesis by the nonnegative contraction,
  and closes by ordered-field arithmetic.
Source: Mathlib finite sums over natural intervals, field division, and
  ordered-field arithmetic
Used in: accelerated stochastic gradient descent estimate-sequence recurrence
  telescope with Gamma-normalized Bregman and stochastic error tails
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
theorem finite_window_weighted_recurrence_telescope_with_tail_sums
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (alpha gamma Gamma A L B D : ℕ → R) (k : ℕ) (hk : 1 ≤ k)
    (hgamma_ne : ∀ t, 1 ≤ t → gamma t ≠ 0)
    (hGamma_ne : ∀ t, 1 ≤ t → Gamma t ≠ 0)
    (hGamma_one : Gamma 1 = 1)
    (halpha_one : alpha 1 = 1)
    (halpha_le_one : ∀ t, 1 ≤ t → alpha t ≤ 1)
    (hGamma_succ :
      ∀ t, 1 ≤ t → Gamma (t + 1) = (1 - alpha (t + 1)) * Gamma t)
    (hstep : ∀ t, 1 ≤ t →
      A t ≤ (1 - alpha t) * A (t - 1) + alpha t * L t +
        alpha t / gamma t * B t + D t) :
    A k - Gamma k *
        Finset.sum (Finset.Icc 1 k) (fun t => alpha t / Gamma t * L t) ≤
      Gamma k * (1 - alpha 1) * A 0 +
        Gamma k *
          Finset.sum (Finset.Icc 1 k)
            (fun t => alpha t / (gamma t * Gamma t) * B t) +
        Gamma k *
          Finset.sum (Finset.Icc 1 k) (fun t => D t / Gamma t) := by
  classical
  let SL : ℕ → R := fun m =>
    Finset.sum (Finset.Icc 1 m) (fun t => alpha t / Gamma t * L t)
  let SB : ℕ → R := fun m =>
    Finset.sum (Finset.Icc 1 m) (fun t => alpha t / (gamma t * Gamma t) * B t)
  let SD : ℕ → R := fun m =>
    Finset.sum (Finset.Icc 1 m) (fun t => D t / Gamma t)
  change
    A k - Gamma k * SL k ≤
      Gamma k * (1 - alpha 1) * A 0 + Gamma k * SB k + Gamma k * SD k
  refine Nat.le_induction ?base ?step k hk
  · have hstep1 := hstep 1 le_rfl
    have hstep1' :
        A 1 ≤ L 1 + (1 / gamma 1) * B 1 + D 1 := by
      simpa [halpha_one] using hstep1
    rw [one_div] at hstep1'
    simp [SL, SB, SD, hGamma_one, halpha_one]
    linarith
  · intro n hn ih
    have hn1 : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
    have hcoef_nonneg : 0 ≤ 1 - alpha (n + 1) := by
      exact sub_nonneg.mpr (halpha_le_one (n + 1) hn1)
    have hrec := hGamma_succ n hn
    have hGtop : Gamma (n + 1) ≠ 0 := hGamma_ne (n + 1) hn1
    have hγtop : gamma (n + 1) ≠ 0 := hgamma_ne (n + 1) hn1
    have hSL_succ :
        SL (n + 1) =
          SL n + alpha (n + 1) / Gamma (n + 1) * L (n + 1) := by
      dsimp [SL]
      rw [Finset.sum_Icc_succ_top hn1]
    have hSB_succ :
        SB (n + 1) =
          SB n + alpha (n + 1) / (gamma (n + 1) * Gamma (n + 1)) *
            B (n + 1) := by
      dsimp [SB]
      rw [Finset.sum_Icc_succ_top hn1]
    have hSD_succ :
        SD (n + 1) = SD n + D (n + 1) / Gamma (n + 1) := by
      dsimp [SD]
      rw [Finset.sum_Icc_succ_top hn1]
    have htopL :
        Gamma (n + 1) *
            (alpha (n + 1) / Gamma (n + 1) * L (n + 1)) =
          alpha (n + 1) * L (n + 1) := by
      field_simp [hGtop]
    have htopB :
        Gamma (n + 1) *
            (alpha (n + 1) / (gamma (n + 1) * Gamma (n + 1)) *
              B (n + 1)) =
          alpha (n + 1) / gamma (n + 1) * B (n + 1) := by
      field_simp [hγtop, hGtop]
    have htopD :
        Gamma (n + 1) * (D (n + 1) / Gamma (n + 1)) = D (n + 1) := by
      field_simp [hGtop]
    have hih_scaled := mul_le_mul_of_nonneg_left ih hcoef_nonneg
    have hstep_top :
        A (n + 1) ≤
          (1 - alpha (n + 1)) * A n + alpha (n + 1) * L (n + 1) +
            alpha (n + 1) / gamma (n + 1) * B (n + 1) + D (n + 1) := by
      simpa using hstep (n + 1) hn1
    calc
      A (n + 1) - Gamma (n + 1) * SL (n + 1)
          = A (n + 1) -
              Gamma (n + 1) *
                (SL n + alpha (n + 1) / Gamma (n + 1) * L (n + 1)) := by
              rw [hSL_succ]
      _ = A (n + 1) - Gamma (n + 1) * SL n -
            alpha (n + 1) * L (n + 1) := by
              rw [mul_add, htopL]
              ring
      _ ≤ (1 - alpha (n + 1)) * (A n - Gamma n * SL n) +
            alpha (n + 1) / gamma (n + 1) * B (n + 1) + D (n + 1) := by
              rw [hrec]
              nlinarith
      _ ≤ (1 - alpha (n + 1)) *
              (Gamma n * (1 - alpha 1) * A 0 + Gamma n * SB n +
                Gamma n * SD n) +
            alpha (n + 1) / gamma (n + 1) * B (n + 1) + D (n + 1) := by
              nlinarith
      _ =
          Gamma (n + 1) * (1 - alpha 1) * A 0 +
            (Gamma (n + 1) * SB n +
              alpha (n + 1) / gamma (n + 1) * B (n + 1)) +
            (Gamma (n + 1) * SD n + D (n + 1)) := by
              rw [hrec]
              ring
      _ =
          Gamma (n + 1) * (1 - alpha 1) * A 0 +
            Gamma (n + 1) * SB (n + 1) +
            Gamma (n + 1) * SD (n + 1) := by
              rw [hSB_succ, hSD_succ]
              rw [mul_add, mul_add, htopB, htopD]

/-- Uniform finite average of a one-hot update.

For a finite type, the normalized sum of a table equal to `a` at one selected
index and `b` elsewhere is `b` plus the inverse-cardinality-scaled increment
`a - b`.

Layer: Glue | Gap: Level 0 (finite uniform one-hot average algebra)
Proof: rewrite the one-hot sum as the constant sum plus a single delta term,
  then cancel the finite cardinality scalar by real-field arithmetic.
Source: Mathlib finite sums, decidable finite-type equality, and real module
  scalar algebra
Used in: randomized accelerated proximal-point component-table refresh average
  after conditioning on a uniformly selected finite-sum index
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
theorem finite_uniform_average_ite_eq_inv_card_smul_sub_add
    {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup V] [Module ℝ V]
    (i : ι) (a b : V) :
    ((Fintype.card ι : ℝ)⁻¹) •
        Finset.sum Finset.univ (fun j : ι => if i = j then a else b) =
      ((Fintype.card ι : ℝ)⁻¹) • (a - b) + b := by
  classical
  have hsum_delta :
      Finset.sum Finset.univ (fun j : ι => if i = j then a - b else (0 : V)) = a - b := by
    simpa using (Finset.sum_ite_eq (i := i) (f := fun _j : ι => a - b))
  have hsum :
      Finset.sum Finset.univ (fun j : ι => if i = j then a else b) =
        (Fintype.card ι : ℝ) • b + (a - b) := by
    calc
      Finset.sum Finset.univ (fun j : ι => if i = j then a else b)
          =
        Finset.sum Finset.univ (fun j : ι => b + if i = j then a - b else (0 : V)) := by
          refine Finset.sum_congr rfl ?_
          intro j _hj
          by_cases hij : i = j
          · simp [hij]
          · simp [hij]
      _ =
        Finset.sum Finset.univ (fun _j : ι => b) +
          Finset.sum Finset.univ (fun j : ι => if i = j then a - b else 0) := by
          rw [Finset.sum_add_distrib]
      _ = (Fintype.card ι : ℝ) • b + (a - b) := by
          rw [Finset.sum_const, Finset.card_univ, hsum_delta,
            ← Nat.cast_smul_eq_nsmul ℝ]
  have hcard_ne : (Fintype.card ι : ℝ) ≠ 0 := by
    have hpos : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i⟩
    exact_mod_cast Nat.ne_of_gt hpos
  rw [hsum]
  calc
    ((Fintype.card ι : ℝ)⁻¹) •
          ((Fintype.card ι : ℝ) • b + (a - b)) =
        ((Fintype.card ι : ℝ)⁻¹) • ((Fintype.card ι : ℝ) • b) +
          ((Fintype.card ι : ℝ)⁻¹) • (a - b) := by
      rw [smul_add]
    _ = ((Fintype.card ι : ℝ)⁻¹) • (a - b) + b := by
      rw [smul_smul]
      have hmul : (Fintype.card ι : ℝ)⁻¹ * (Fintype.card ι : ℝ) = 1 := by
        field_simp [hcard_ne]
      rw [hmul, one_smul, add_comm]

/-- A finite uniform average absorbs a centered memory table and a double-sum correction.

For a nonempty finite index type, adding the averaged component contribution and
the averaged transposed two-index correction equals the finite uniform average of
the component plus the centered memory residual and row correction, all multiplied
by the same scalar.

Layer: Glue | Gap: Level 1 (finite uniform centered double-sum algebra)
Proof: commute the two finite sums, expand sums over addition and subtraction,
  cancel the inverse-cardinality factor using nonemptiness, and close the real
  polynomial identity by ring normalization.
Source: Mathlib finite sums, finite cardinality, and real field arithmetic
Used in: randomized accelerated proximal-point current component estimator
  normalization after memory centering and two-index correction expansion
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
theorem finiteUniformAverage_add_centered_double_sum
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (gamma : ℝ) (component Aprev : ι → ℝ) (B : ι → ι → ℝ) :
    gamma * ((Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ component) +
        gamma * ((Fintype.card ι : ℝ)⁻¹ * (Fintype.card ι : ℝ)⁻¹ *
          Finset.sum Finset.univ
            (fun i : ι => Finset.sum Finset.univ (fun j : ι => B j i))) =
      gamma *
        ((Fintype.card ι : ℝ)⁻¹ *
          Finset.sum Finset.univ
            (fun j : ι =>
              component j + Aprev j -
                (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ Aprev +
                (Fintype.card ι : ℝ)⁻¹ *
                  Finset.sum Finset.univ (fun i : ι => B j i))) := by
  classical
  let c : ℝ := Fintype.card ι
  have hc_ne : c ≠ 0 := by
    have hpos : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr inferInstance
    have hne : (Fintype.card ι : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt hpos
    simp [c, hne]
  have hB_comm :
      Finset.sum Finset.univ
          (fun i : ι => Finset.sum Finset.univ (fun j : ι => B j i)) =
        Finset.sum Finset.univ
          (fun j : ι => Finset.sum Finset.univ (fun i : ι => B j i)) := by
    exact Finset.sum_comm
  change
    gamma * (c⁻¹ * Finset.sum Finset.univ component) +
        gamma * (c⁻¹ * c⁻¹ *
          Finset.sum Finset.univ
            (fun i : ι => Finset.sum Finset.univ (fun j : ι => B j i))) =
      gamma *
        (c⁻¹ *
          Finset.sum Finset.univ
            (fun j : ι =>
              component j + Aprev j -
                c⁻¹ * Finset.sum Finset.univ Aprev +
                c⁻¹ * Finset.sum Finset.univ (fun i : ι => B j i)))
  rw [hB_comm]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [Finset.sum_const, Finset.card_univ]
  simp only [nsmul_eq_mul]
  rw [show (Fintype.card ι : ℝ) = c by rfl]
  rw [← Finset.mul_sum]
  have hcancelA :
      c * (c⁻¹ * Finset.sum Finset.univ Aprev) =
        Finset.sum Finset.univ Aprev := by
    rw [← mul_assoc, mul_inv_cancel₀ hc_ne, one_mul]
  rw [hcancelA]
  ring

/-- A finite-sum scalar inner-product regrouping identity.

The identity expands two averaged inner products and regroups scalar component
terms and vector-valued component terms into three finite sums.

Layer: Glue | Gap: Level 1 (finite-sum inner-product scalar expansion)
Proof: expand inner products over finite sums with `sum_inner`, distribute
  finite sums over addition and subtraction, then close the scalar polynomial
  identity by ring normalization.
Source: Mathlib finite sums and real inner-product space algebra
Used in: finite-sum scalar comparisons that split averaged inner-product terms
  into three grouped sums -/
theorem finset_inner_scalar_three_way_expansion
    {ι E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s : Finset ι)
    (gamma invCard phiNext phiStar : ℝ)
    (xNext xStar xTilde : E)
    (psiStar psiHat : ι → ℝ)
    (gStar gHat yTilde xHat : ι → E) :
    gamma *
        (phiNext +
          invCard * Finset.sum s psiStar +
          ⟪invCard • Finset.sum s gStar, xNext - xStar⟫_ℝ +
          -(phiStar +
            invCard * Finset.sum s
              (fun i : ι => psiHat i + ⟪gHat i, xStar - xHat i⟫_ℝ))) =
      gamma *
          (phiNext - phiStar +
            ⟪invCard • Finset.sum s yTilde, xNext - xStar⟫_ℝ) +
        gamma *
          (invCard *
            Finset.sum s
              (fun i : ι =>
                psiStar i - ⟪gStar i, xStar⟫_ℝ -
                  (psiHat i - ⟪gHat i, xHat i⟫_ℝ +
                    ⟪gHat i - gStar i, xTilde⟫_ℝ))) +
        gamma *
          (invCard *
            Finset.sum s
              (fun i : ι =>
                ⟪gHat i - gStar i, xTilde⟫_ℝ -
                  ⟪yTilde i - gStar i, xNext⟫_ℝ +
                  ⟪yTilde i - gHat i, xStar⟫_ℝ)) := by
  classical
  let SpsiStar : ℝ := Finset.sum s psiStar
  let SpsiHat : ℝ := Finset.sum s psiHat
  let SgStarNext : ℝ := Finset.sum s (fun i : ι => ⟪gStar i, xNext⟫_ℝ)
  let SgStarStar : ℝ := Finset.sum s (fun i : ι => ⟪gStar i, xStar⟫_ℝ)
  let SgStarTilde : ℝ := Finset.sum s (fun i : ι => ⟪gStar i, xTilde⟫_ℝ)
  let SgHatStar : ℝ := Finset.sum s (fun i : ι => ⟪gHat i, xStar⟫_ℝ)
  let SgHatHat : ℝ := Finset.sum s (fun i : ι => ⟪gHat i, xHat i⟫_ℝ)
  let SgHatTilde : ℝ := Finset.sum s (fun i : ι => ⟪gHat i, xTilde⟫_ℝ)
  let SyNext : ℝ := Finset.sum s (fun i : ι => ⟪yTilde i, xNext⟫_ℝ)
  let SyStar : ℝ := Finset.sum s (fun i : ι => ⟪yTilde i, xStar⟫_ℝ)
  have hAvgStar :
      ⟪invCard • Finset.sum s gStar, xNext - xStar⟫_ℝ =
        invCard * (SgStarNext - SgStarStar) := by
    rw [inner_smul_left, sum_inner]
    simp_rw [inner_sub_right]
    simp [SgStarNext, SgStarStar, Finset.sum_sub_distrib]
  have hAvgY :
      ⟪invCard • Finset.sum s yTilde, xNext - xStar⟫_ℝ =
        invCard * (SyNext - SyStar) := by
    rw [inner_smul_left, sum_inner]
    simp_rw [inner_sub_right]
    simp [SyNext, SyStar, Finset.sum_sub_distrib]
  have hQHat :
      Finset.sum s
          (fun i : ι => psiHat i + ⟪gHat i, xStar - xHat i⟫_ℝ) =
        SpsiHat + (SgHatStar - SgHatHat) := by
    simp_rw [inner_sub_right]
    simp [SpsiHat, SgHatStar, SgHatHat, Finset.sum_add_distrib,
      Finset.sum_sub_distrib]
  have hDelta1 :
      Finset.sum s
          (fun i : ι =>
            psiStar i - ⟪gStar i, xStar⟫_ℝ -
              (psiHat i - ⟪gHat i, xHat i⟫_ℝ +
                ⟪gHat i - gStar i, xTilde⟫_ℝ)) =
        SpsiStar - SgStarStar - (SpsiHat - SgHatHat +
          (SgHatTilde - SgStarTilde)) := by
    simp_rw [inner_sub_left]
    simp [SpsiStar, SpsiHat, SgStarStar, SgHatHat, SgHatTilde, SgStarTilde,
      Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hDelta2 :
      Finset.sum s
          (fun i : ι =>
            ⟪gHat i - gStar i, xTilde⟫_ℝ -
              ⟪yTilde i - gStar i, xNext⟫_ℝ +
              ⟪yTilde i - gHat i, xStar⟫_ℝ) =
        (SgHatTilde - SgStarTilde) - (SyNext - SgStarNext) +
          (SyStar - SgHatStar) := by
    simp_rw [inner_sub_left]
    simp [SgHatTilde, SgStarTilde, SyNext, SgStarNext, SyStar, SgHatStar,
      Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hAvgStar, hAvgY, hQHat, hDelta1, hDelta2]
  ring

/-- A positive-leading ordered-field quadratic eventually dominates any lower target.

The witness is chosen nonnegative, so callers can use it directly as a radius
or norm threshold in coercivity arguments.

Layer: Glue | Gap: Level 0 (positive quadratic lower-tail radius)
Proof: choose a maximum controlling the linear coefficient and target offset;
  split the quadratic budget into two halves and absorb the linear and constant
  terms by ordered-field arithmetic.
Source: Mathlib ordered-field arithmetic, absolute values, and lattice maxima
Used in: randomized accelerated proximal-point compact truncation after reducing
  a noncompact prox objective to a scalar quadratic lower bound
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal point -/
theorem exists_nonneg_forall_le_quadratic_sub_linear_of_pos
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {a : R} (ha : 0 < a) (b c B : R) :
    ∃ R₀ : R, 0 ≤ R₀ ∧ ∀ r : R, R₀ ≤ r → B ≤ a * r ^ 2 - b * r + c := by
  let R₀ : R := max 1 (max ((2 * |b|) / a) ((2 * |B - c|) / a))
  refine ⟨R₀, ?_, ?_⟩
  · dsimp [R₀]
    exact le_trans (by norm_num : (0 : R) ≤ 1) (le_max_left _ _)
  · intro r hr
    have hR_one : (1 : R) ≤ R₀ := by
      dsimp [R₀]
      exact le_max_left _ _
    have hR_b : (2 * |b|) / a ≤ R₀ := by
      dsimp [R₀]
      exact le_trans (le_max_left _ _) (le_max_right _ _)
    have hR_B : (2 * |B - c|) / a ≤ R₀ := by
      dsimp [R₀]
      exact le_trans (le_max_right _ _) (le_max_right _ _)
    have hr_one : (1 : R) ≤ r := le_trans hR_one hr
    have hr_nonneg : 0 ≤ r := by linarith
    have hb_div : (2 * |b|) / a ≤ r := le_trans hR_b hr
    have hB_div : (2 * |B - c|) / a ≤ r := le_trans hR_B hr
    have hb_lin : 2 * |b| ≤ a * r := by
      simpa [mul_comm] using (div_le_iff₀ ha).mp hb_div
    have hB_lin : 2 * |B - c| ≤ a * r := by
      simpa [mul_comm] using (div_le_iff₀ ha).mp hB_div
    have hb_abs_mul : |b| * r ≤ (a * r ^ 2) / 2 := by
      nlinarith [hb_lin, hr_nonneg]
    have hB_abs_quad : |B - c| ≤ (a * r ^ 2) / 2 := by
      have har_le_quad : a * r ≤ a * r ^ 2 := by
        have hr_le_sq : r ≤ r ^ 2 := by
          have hprod : 0 ≤ r * (r - 1) :=
            mul_nonneg hr_nonneg (sub_nonneg.mpr hr_one)
          nlinarith
        exact mul_le_mul_of_nonneg_left hr_le_sq (le_of_lt ha)
      nlinarith [hB_lin, har_le_quad]
    have hneg_linear : -b * r ≥ -|b| * r := by
      have hb_le_abs : b ≤ |b| := le_abs_self b
      nlinarith [hb_le_abs, hr_nonneg]
    have htarget : B - c ≤ |B - c| := le_abs_self (B - c)
    nlinarith [hb_abs_mul, hB_abs_quad, hneg_linear, htarget]

/-- Equality of length-`n` finite vectors restricts to equality of their length-`m`
prefixes whenever `m <= n`.

Layer: Glue | Gap: Level 0 (finite prefix restriction congruence)
Proof: apply function extensionality on the shorter prefix and evaluate the
  original equality at the canonical `Fin.castLE` inclusion.
Source: Mathlib finite ordinal function extensionality and `Fin.castLE`
Used in: randomized accelerated proximal-point prefix-determinism integrability
  reductions for previous-iterate sample windows
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
theorem fin_prefix_eq_of_le {α : Type*} {m n : ℕ} {f g : Fin n → α}
    (hmn : m ≤ n) (hfg : f = g) :
    (fun r : Fin m => f (Fin.castLE hmn r)) =
      (fun r : Fin m => g (Fin.castLE hmn r)) := by
  funext r
  exact congrFun hfg (Fin.castLE hmn r)

/-- Adding a nonnegative fixed-center linear shift to a pointwise Lipschitz
map increases the Lipschitz constant by the shift coefficient.

For points represented by an arbitrary type `P`, the distance is measured after
an evaluation map into the normed vector space. This form applies directly to
carrier-subtype gradients without first building a global `LipschitzWith`.

Layer: Glue | Gap: Level 1 (pointwise Lipschitz bound for shifted gradients)
Proof: split the shifted difference into the base difference plus the linear
  shift difference, use the triangle inequality, compute the shift norm by
  `norm_smul`, and collect constants.
Source: Mathlib normed real vector spaces and Lipschitz map algebra
Used in: randomized accelerated proximal-point component subproblem
  regularized-gradient smoothness
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
theorem norm_add_nonneg_smul_sub_center_sub_le
    {P E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (g : P → E) (eval : P → E) (L c : ℝ) (z : E)
    (hc_nonneg : 0 ≤ c) (x y : P)
    (hg : ‖g x - g y‖ ≤ L * ‖eval x - eval y‖) :
    ‖(g x + c • (eval x - z)) - (g y + c • (eval y - z))‖ ≤
      (L + c) * ‖eval x - eval y‖ := by
  have hshift :
      ‖c • (eval x - z) - c • (eval y - z)‖ =
        c * ‖eval x - eval y‖ := by
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg hc_nonneg]
    congr 1
    abel_nf
  have hsplit :
      (g x + c • (eval x - z)) - (g y + c • (eval y - z)) =
        (g x - g y) + (c • (eval x - z) - c • (eval y - z)) := by
    abel
  calc
    ‖(g x + c • (eval x - z)) - (g y + c • (eval y - z))‖ =
        ‖(g x - g y) + (c • (eval x - z) - c • (eval y - z))‖ := by
      rw [hsplit]
    _ ≤ ‖g x - g y‖ + ‖c • (eval x - z) - c • (eval y - z)‖ := by
      exact norm_add_le _ _
    _ ≤ L * ‖eval x - eval y‖ + c * ‖eval x - eval y‖ := by
      exact add_le_add hg (le_of_eq hshift)
    _ = (L + c) * ‖eval x - eval y‖ := by
      ring

/-- A sampled Hilbert correction is absorbed by a quadratic coefficient and budget.

If the quadratic coefficient `A` dominates `c ^ 2 * L / tau` and the budget `B`
dominates `(1 / (2 * L)) * ‖g‖ ^ 2`, then the correction term
`c * ⟪g, v⟫_ℝ` is absorbed by `A * ‖v‖ ^ 2 + (tau / 2) * B`, after any
nonnegative outer scale `gamma`.

Layer: Glue | Gap: Level 1 (sampled inner-product Young absorption from budget)
Proof: dominate the inner product by Cauchy-Schwarz, prove the base
  completed-square inequality at coefficient `c ^ 2 * L / tau`, and add the
  nonnegative slack from the coefficient and budget hypotheses.
Source: Mathlib real Hilbert-space Cauchy-Schwarz and ordered-field square
  completion APIs
Used in: randomized accelerated proximal-point terminal sampled-correction
  residual absorption
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal point -/
theorem young_absorb_sample_correction_of_cocoercive_budget
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    {L tau A gamma c B : ℝ} {g v : E}
    (hL : 0 < L) (htau : 0 < tau) (hgamma : 0 ≤ gamma)
    (hc : 0 ≤ c) (hcoef : c ^ 2 * L / tau ≤ A)
    (hbudget : (1 / (2 * L)) * ‖g‖ ^ 2 ≤ B) :
    0 ≤ gamma * (A * ‖v‖ ^ 2 + (tau / 2) * B - c * ⟪g, v⟫_ℝ) := by
  have hL_nonneg : 0 ≤ L := le_of_lt hL
  have htau_nonneg : 0 ≤ tau := le_of_lt htau
  have hL_ne : L ≠ 0 := ne_of_gt hL
  have htau_ne : tau ≠ 0 := ne_of_gt htau
  have hinner_le : c * ⟪g, v⟫_ℝ ≤ c * (‖g‖ * ‖v‖) := by
    exact mul_le_mul_of_nonneg_left
      (le_trans (le_abs_self _) (abs_real_inner_le_norm g v)) hc
  have hbudget_scaled :
      (tau / 2) * ((1 / (2 * L)) * ‖g‖ ^ 2) ≤ (tau / 2) * B := by
    exact mul_le_mul_of_nonneg_left hbudget
      (div_nonneg htau_nonneg (by norm_num : (0 : ℝ) ≤ 2))
  have hquad_base :
      0 ≤ c ^ 2 * L / tau * ‖v‖ ^ 2 +
          (tau / 2) * ((1 / (2 * L)) * ‖g‖ ^ 2) -
          c * (‖g‖ * ‖v‖) := by
    have hsquare : 0 ≤ (2 * c * L * ‖v‖ - tau * ‖g‖) ^ 2 := sq_nonneg _
    field_simp [hL_ne, htau_ne]
    nlinarith [hsquare]
  have hquad :
      0 ≤ A * ‖v‖ ^ 2 + (tau / 2) * B - c * ⟪g, v⟫_ℝ := by
    have hA_slack :
        0 ≤ (A - c ^ 2 * L / tau) * ‖v‖ ^ 2 := by
      exact mul_nonneg (sub_nonneg.mpr hcoef) (sq_nonneg _)
    have hB_slack :
        0 ≤ (tau / 2) * B -
          (tau / 2) * ((1 / (2 * L)) * ‖g‖ ^ 2) := by
      exact sub_nonneg.mpr hbudget_scaled
    have hinner_slack :
        0 ≤ c * (‖g‖ * ‖v‖) - c * ⟪g, v⟫_ℝ := by
      exact sub_nonneg.mpr hinner_le
    nlinarith [hquad_base, hA_slack, hB_slack, hinner_slack]
  exact mul_nonneg hgamma hquad

/-- A Hilbert-space inner product is absorbed by a quadratic coefficient and budget.

If the quadratic coefficient `A` dominates `c ^ 2 * L / tau` and the budget `B`
dominates `(1 / (2 * L)) * ‖g‖ ^ 2`, then the inner-product term
`c * ⟪g, v⟫_ℝ` is absorbed by `A * ‖v‖ ^ 2 + (tau / 2) * B` after any
nonnegative outer scale `gamma`.

Layer: Glue | Gap: Level 1 (inner-product Young absorption from norm-square budget)
Proof: dominate the inner product by Cauchy-Schwarz, prove the base
  completed-square inequality at coefficient `c ^ 2 * L / tau`, and add the
  nonnegative slack from the coefficient and budget hypotheses.
Source: Mathlib real Hilbert-space Cauchy-Schwarz and ordered-field square
  completion APIs -/
theorem young_absorb_inner_of_norm_sq_budget
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    {L tau A gamma c B : ℝ} {g v : E}
    (hL : 0 < L) (htau : 0 < tau) (hgamma : 0 ≤ gamma)
    (hc : 0 ≤ c) (hcoef : c ^ 2 * L / tau ≤ A)
    (hbudget : (1 / (2 * L)) * ‖g‖ ^ 2 ≤ B) :
    0 ≤ gamma * (A * ‖v‖ ^ 2 + (tau / 2) * B - c * ⟪g, v⟫_ℝ) := by
  exact young_absorb_sample_correction_of_cocoercive_budget hL htau hgamma hc hcoef hbudget

/-- An averaged Hilbert cross term is absorbed by a quadratic budget.

If the coefficient `A` dominates `L / (m * (1 + tau))`, then the averaged
linear term `-(1 / m) * ⟪u, v⟫_ℝ` is controlled by the quadratic terms in `u`
and `v`.

Layer: Glue | Gap: Level 1 (averaged inner-product Young absorption)
Proof: bound the inner product by Cauchy-Schwarz, prove the exact scalar
  completed-square inequality at the base coefficient, and add the nonnegative
  coefficient slack from the lower bound on `A`.
Source: Mathlib real Hilbert-space Cauchy-Schwarz and ordered-field square
  completion APIs
Used in: randomized accelerated proximal-point terminal component-average
  residual absorption
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal point -/
theorem young_absorb_average_inner_with_quadratic_budget
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    {m L tau A : ℝ} {u v : E}
    (hm : 0 < m) (hL : 0 < L) (htau : 0 ≤ tau)
    (hA : A ≥ L / (m * (1 + tau))) :
    0 ≤ (A / m) * ‖v‖ ^ 2 - (1 / m) * ⟪u, v⟫_ℝ +
      (1 + tau) / (4 * L) * ‖u‖ ^ 2 := by
  have hone_tau_pos : 0 < 1 + tau := by linarith
  have hm_ne : m ≠ 0 := ne_of_gt hm
  have hL_ne : L ≠ 0 := ne_of_gt hL
  have hone_tau_ne : 1 + tau ≠ 0 := ne_of_gt hone_tau_pos
  have hbase_coeff_le :
      L / (m ^ 2 * (1 + tau)) ≤ A / m := by
    have hscale := mul_le_mul_of_nonneg_right hA (inv_nonneg.mpr (le_of_lt hm))
    have hleft :
        L / (m * (1 + tau)) * m⁻¹ = L / (m ^ 2 * (1 + tau)) := by
      field_simp [hm_ne, hone_tau_ne]
    have hright : A * m⁻¹ = A / m := by
      field_simp [hm_ne]
    rw [hleft, hright] at hscale
    simpa [div_eq_mul_inv] using hscale
  have hinner_le : ⟪u, v⟫_ℝ ≤ ‖u‖ * ‖v‖ := by
    exact le_trans (le_abs_self _) (abs_real_inner_le_norm u v)
  have hbase :
      0 ≤ L / (m ^ 2 * (1 + tau)) * ‖v‖ ^ 2 -
          (1 / m) * (‖u‖ * ‖v‖) +
          (1 + tau) / (4 * L) * ‖u‖ ^ 2 := by
    have hsquare :
        0 ≤ (2 * L * ‖v‖ - m * (1 + tau) * ‖u‖) ^ 2 := sq_nonneg _
    field_simp [hm_ne, hL_ne, hone_tau_ne]
    nlinarith [hsquare]
  have hcoeff_nonneg :
      0 ≤ (A / m - L / (m ^ 2 * (1 + tau))) * ‖v‖ ^ 2 := by
    exact mul_nonneg (sub_nonneg.mpr hbase_coeff_le) (sq_nonneg _)
  have hinner_slack :
      0 ≤ (1 / m) * (‖u‖ * ‖v‖ - ⟪u, v⟫_ℝ) := by
    exact mul_nonneg (by positivity) (sub_nonneg.mpr hinner_le)
  have hsum :
      0 ≤
        (L / (m ^ 2 * (1 + tau)) * ‖v‖ ^ 2 -
            (1 / m) * (‖u‖ * ‖v‖) +
            (1 + tau) / (4 * L) * ‖u‖ ^ 2) +
          ((A / m - L / (m ^ 2 * (1 + tau))) * ‖v‖ ^ 2) +
          ((1 / m) * (‖u‖ * ‖v‖ - ⟪u, v⟫_ℝ)) := by
    nlinarith [hbase, hcoeff_nonneg, hinner_slack]
  calc
    0 ≤
        (L / (m ^ 2 * (1 + tau)) * ‖v‖ ^ 2 -
            (1 / m) * (‖u‖ * ‖v‖) +
            (1 + tau) / (4 * L) * ‖u‖ ^ 2) +
          ((A / m - L / (m ^ 2 * (1 + tau))) * ‖v‖ ^ 2) +
          ((1 / m) * (‖u‖ * ‖v‖ - ⟪u, v⟫_ℝ)) := hsum
    _ = (A / m) * ‖v‖ ^ 2 - (1 / m) * ⟪u, v⟫_ℝ +
          (1 + tau) / (4 * L) * ‖u‖ ^ 2 := by
      ring

/-- Two adjacent correction inner products are absorbed by current and previous budgets.

If the current and previous correction vectors each have a norm-square budget,
the adjacent weight relation `gammaPrev = alpha * gammaCur` converts the current
Young term to the previous weight, and the leftover quadratic coefficient is
nonnegative, then the combined current/previous correction group is nonnegative.

Layer: Glue | Gap: Level 1 (adjacent two-correction Young absorption)
Proof: apply the one-correction budget absorption twice, rewrite the current
  term through the adjacent weight relation, add the nonnegative leftover
  quadratic slack, and normalize the real algebra.
Source: Mathlib real Hilbert-space Cauchy-Schwarz and ordered-field square
  completion APIs
Used in: randomized accelerated proximal-point interior residual absorption for
  adjacent current and previous gradient-memory corrections
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal point -/
theorem young_absorb_two_adjacent_corrections
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    {L tauPrev tauCur eta alpha gammaPrev gammaCur c BPrev BCur : ℝ}
    {gCur gPrev d : E}
    (hL : 0 < L) (htauPrev : 0 < tauPrev) (htauCur : 0 < tauCur)
    (hgammaCur : 0 ≤ gammaCur) (halpha : 0 ≤ alpha) (hc : 0 ≤ c)
    (hshift : gammaPrev = alpha * gammaCur)
    (hcoef : 0 ≤ gammaPrev *
      (eta - alpha * L / tauCur - c ^ 2 * L / tauPrev))
    (hbcur : (1 / (2 * L)) * ‖gCur‖ ^ 2 ≤ BCur)
    (hbprev : (1 / (2 * L)) * ‖gPrev‖ ^ 2 ≤ BPrev) :
    0 ≤
      gammaPrev * (eta * ‖d‖ ^ 2) +
        gammaCur * ((tauCur / 2) * BCur) +
        gammaPrev * ((tauPrev / 2) * BPrev) +
        gammaPrev * (⟪gCur, d⟫_ℝ + c * ⟪gPrev, d⟫_ℝ) := by
  have hcur_raw :
      0 ≤ gammaCur *
        ((alpha ^ 2 * L / tauCur) * ‖d‖ ^ 2 +
          (tauCur / 2) * BCur - alpha * ⟪-gCur, d⟫_ℝ) := by
    exact
      young_absorb_inner_of_norm_sq_budget
        (L := L) (tau := tauCur) (A := alpha ^ 2 * L / tauCur)
        (gamma := gammaCur) (c := alpha) (B := BCur) (g := -gCur) (v := d)
        hL htauCur hgammaCur halpha le_rfl (by simpa using hbcur)
  have hcur :
      0 ≤
        gammaPrev * ((alpha * L / tauCur) * ‖d‖ ^ 2) +
          gammaCur * ((tauCur / 2) * BCur) +
          gammaPrev * ⟪gCur, d⟫_ℝ := by
    have hrewrite :
        gammaCur *
            ((alpha ^ 2 * L / tauCur) * ‖d‖ ^ 2 +
              (tauCur / 2) * BCur - alpha * ⟪-gCur, d⟫_ℝ) =
          gammaPrev * ((alpha * L / tauCur) * ‖d‖ ^ 2) +
            gammaCur * ((tauCur / 2) * BCur) +
            gammaPrev * ⟪gCur, d⟫_ℝ := by
      rw [hshift]
      simp [inner_neg_left]
      ring
    rw [hrewrite] at hcur_raw
    exact hcur_raw
  have hgammaPrev : 0 ≤ gammaPrev := by
    rw [hshift]
    exact mul_nonneg halpha hgammaCur
  have hprev :
      0 ≤
        gammaPrev *
          ((c ^ 2 * L / tauPrev) * ‖d‖ ^ 2 +
            (tauPrev / 2) * BPrev + c * ⟪gPrev, d⟫_ℝ) := by
    have hprev_raw :
        0 ≤ gammaPrev *
          ((c ^ 2 * L / tauPrev) * ‖d‖ ^ 2 +
            (tauPrev / 2) * BPrev - c * ⟪-gPrev, d⟫_ℝ) := by
      exact
        young_absorb_inner_of_norm_sq_budget
          (L := L) (tau := tauPrev) (A := c ^ 2 * L / tauPrev)
          (gamma := gammaPrev) (c := c) (B := BPrev) (g := -gPrev) (v := d)
          hL htauPrev hgammaPrev hc le_rfl (by simpa using hbprev)
    simpa [inner_neg_left] using hprev_raw
  have hslack :
      0 ≤
        gammaPrev *
          ((eta - alpha * L / tauCur - c ^ 2 * L / tauPrev) * ‖d‖ ^ 2) := by
    have hscaled :
        0 ≤
          (gammaPrev *
            (eta - alpha * L / tauCur - c ^ 2 * L / tauPrev)) * ‖d‖ ^ 2 := by
      exact mul_nonneg hcoef (sq_nonneg _)
    convert hscaled using 1
    ring
  nlinarith [hcur, hprev, hslack]

/-- A lagged auxiliary recurrence can be absorbed into the primary finite-window sum.

If `C n` is controlled by a nonnegative coefficient `c` times a primary term plus the
previous auxiliary state, and the auxiliary state `B n` satisfies the same lagged
recurrence with coefficient `q < 1`, then summing over a one-based window bounds the
current sum by `c / (1 - q)` times the primary sum.

Layer: Glue | Gap: Level 1 (lagged auxiliary recurrence absorption)
Proof: sum both pointwise recurrences, telescope the lagged auxiliary difference
  using `sum_Icc_sub_succ`, then isolate the auxiliary sum through the positive
  denominator `1 - q`.
Source: Mathlib finite sums over natural intervals and ordered-field algebra
Used in: accelerated proximal and variance-reduced convergence proofs absorbing a
  lagged memory-error recurrence into the current error budget
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine
  Learning, randomized accelerated proximal-point method -/
theorem sum_le_div_one_sub_of_lagged_aux_recurrence
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (A C B : ℕ → R) (k : ℕ) (c q : R)
    (hk : 1 ≤ k)
    (hc_nonneg : 0 ≤ c)
    (hq_lt_one : q < 1)
    (hB_boundary : B 0 ≤ B k)
    (hC_step : ∀ n ∈ Finset.Icc 1 k,
      C n ≤ c * (A n + B (n - 1)))
    (hB_step : ∀ n ∈ Finset.Icc 1 k,
      B n ≤ q * (A n + B (n - 1))) :
    Finset.sum (Finset.Icc 1 k) C ≤
      c / (1 - q) * Finset.sum (Finset.Icc 1 k) A := by
  classical
  let s : Finset ℕ := Finset.Icc 1 k
  let A_sum : R := Finset.sum s A
  let C_sum : R := Finset.sum s C
  let B_prev_sum : R := Finset.sum s (fun n => B (n - 1))
  let B_cur_sum : R := Finset.sum s B
  have hden_pos : 0 < 1 - q := by linarith
  have hC_sum_le :
      C_sum ≤ c * (A_sum + B_prev_sum) := by
    have hsum :
        Finset.sum s C ≤
          Finset.sum s (fun n => c * (A n + B (n - 1))) := by
      exact Finset.sum_le_sum (by
        intro n hn
        exact hC_step n (by simpa [s] using hn))
    have hexpand :
        Finset.sum s (fun n => c * (A n + B (n - 1))) =
          c * (A_sum + B_prev_sum) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
    exact hsum.trans_eq hexpand
  have hB_cur_sum_le :
      B_cur_sum ≤ q * (A_sum + B_prev_sum) := by
    have hsum :
        Finset.sum s B ≤
          Finset.sum s (fun n => q * (A n + B (n - 1))) := by
      exact Finset.sum_le_sum (by
        intro n hn
        exact hB_step n (by simpa [s] using hn))
    have hexpand :
        Finset.sum s (fun n => q * (A n + B (n - 1))) =
          q * (A_sum + B_prev_sum) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
    exact hsum.trans_eq hexpand
  have hprev_le_cur : B_prev_sum ≤ B_cur_sum := by
    have hdrop_eq :
        Finset.sum s (fun n => B (n - 1) - B n) = B 0 - B k := by
      simpa [s] using
        (sum_Icc_sub_succ (fun n => B (n - 1)) 1 k hk)
    have hdiff_eq :
        B_prev_sum - B_cur_sum =
          Finset.sum s (fun n => B (n - 1) - B n) := by
      rw [Finset.sum_sub_distrib]
    have hdiff_nonpos : B_prev_sum - B_cur_sum ≤ 0 := by
      calc
        B_prev_sum - B_cur_sum =
            Finset.sum s (fun n => B (n - 1) - B n) := hdiff_eq
        _ = B 0 - B k := hdrop_eq
        _ ≤ 0 := by
          linarith
    linarith
  have hprev_le_recur : B_prev_sum ≤ q * (A_sum + B_prev_sum) :=
    hprev_le_cur.trans hB_cur_sum_le
  have hprev_mul : (1 - q) * B_prev_sum ≤ q * A_sum := by
    nlinarith
  have hprev_bound : B_prev_sum ≤ q / (1 - q) * A_sum := by
    calc
      B_prev_sum = (1 - q)⁻¹ * ((1 - q) * B_prev_sum) := by
        field_simp [ne_of_gt hden_pos]
      _ ≤ (1 - q)⁻¹ * (q * A_sum) := by
        exact mul_le_mul_of_nonneg_left hprev_mul
          (inv_nonneg.mpr (le_of_lt hden_pos))
      _ = q / (1 - q) * A_sum := by
        field_simp [ne_of_gt hden_pos]
  have hsum_arg :
      A_sum + B_prev_sum ≤ (1 - q)⁻¹ * A_sum := by
    calc
      A_sum + B_prev_sum ≤ A_sum + q / (1 - q) * A_sum := by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_left hprev_bound A_sum
      _ = (1 - q)⁻¹ * A_sum := by
        field_simp [ne_of_gt hden_pos]
        ring
  have hscaled :
      c * (A_sum + B_prev_sum) ≤
        c * ((1 - q)⁻¹ * A_sum) :=
    mul_le_mul_of_nonneg_left hsum_arg hc_nonneg
  calc
    Finset.sum (Finset.Icc 1 k) C = C_sum := by rfl
    _ ≤ c * (A_sum + B_prev_sum) := hC_sum_le
    _ ≤ c * ((1 - q)⁻¹ * A_sum) := hscaled
    _ = c / (1 - q) * Finset.sum (Finset.Icc 1 k) A := by
      field_simp [ne_of_gt hden_pos]
      ring

/-- A finite one-based descent window with a lagged carry is bounded by the
endpoint objective gap plus the current carry sum.

If each step satisfies `F n + c * A n <= F (n-1) + c * C (n-1)`, then summing
over `Finset.Icc 1 k` telescopes the `F` terms.  The lagged carry
`C (n-1)` is reindexed into the current carry sum using `C 0 = 0` and
`0 <= C k`, then scaled by the nonnegative coefficient `c`.

Layer: Glue | Gap: Level 1 (finite-window lagged carry telescope)
Proof: sum the pointwise inequalities, use `sum_Icc_sub_succ` for the objective
  and carry telescopes, and compare the lagged carry sum to the current carry
  sum before applying the endpoint gap bound.
Source: Mathlib finite sums over natural intervals and ordered ring algebra
Used in: randomized accelerated proximal-point pathwise objective telescope with
  lagged proximal-displacement carry terms
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
theorem sum_Icc_le_gap_add_sum_of_lagged_step
    {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (F A C : ℕ → R) (k : ℕ) (c gap : R)
    (hk : 1 ≤ k)
    (hc_nonneg : 0 ≤ c)
    (hstep : ∀ n ∈ Finset.Icc 1 k,
      F n + c * A n ≤ F (n - 1) + c * C (n - 1))
    (hC0 : C 0 = 0)
    (hC_terminal_nonneg : 0 ≤ C k)
    (hend : F 0 - F k ≤ gap) :
    c * Finset.sum (Finset.Icc 1 k) A ≤
      gap + c * Finset.sum (Finset.Icc 1 k) C := by
  classical
  let s : Finset ℕ := Finset.Icc 1 k
  have hpoint :
      ∀ n ∈ s, c * A n ≤ (F (n - 1) - F n) + c * C (n - 1) := by
    intro n hn
    have hn' : n ∈ Finset.Icc 1 k := by simpa [s] using hn
    have h := hstep n hn'
    nlinarith
  have hsum :
      Finset.sum s (fun n => c * A n) ≤
        Finset.sum s (fun n => (F (n - 1) - F n) + c * C (n - 1)) := by
    exact Finset.sum_le_sum hpoint
  have hleft :
      Finset.sum s (fun n => c * A n) = c * Finset.sum s A := by
    rw [Finset.mul_sum]
  have hright :
      Finset.sum s (fun n => (F (n - 1) - F n) + c * C (n - 1)) =
        (F 0 - F k) + c * Finset.sum s (fun n => C (n - 1)) := by
    rw [Finset.sum_add_distrib, Finset.mul_sum]
    have htel :
        Finset.sum s (fun n => F (n - 1) - F n) = F 0 - F k := by
      simpa [s] using (sum_Icc_sub_succ (fun n => F (n - 1)) 1 k hk)
    rw [htel]
  have hprev_le_cur :
      Finset.sum s (fun n => C (n - 1)) ≤ Finset.sum s C := by
    have hdrop_eq :
        Finset.sum s (fun n => C (n - 1) - C n) = C 0 - C k := by
      simpa [s] using (sum_Icc_sub_succ (fun n => C (n - 1)) 1 k hk)
    have hdiff_eq :
        Finset.sum s (fun n => C (n - 1)) - Finset.sum s C =
          Finset.sum s (fun n => C (n - 1) - C n) := by
      rw [Finset.sum_sub_distrib]
    have hdiff_nonpos :
        Finset.sum s (fun n => C (n - 1)) - Finset.sum s C ≤ 0 := by
      calc
        Finset.sum s (fun n => C (n - 1)) - Finset.sum s C =
            Finset.sum s (fun n => C (n - 1) - C n) := hdiff_eq
        _ = C 0 - C k := hdrop_eq
        _ ≤ 0 := by
          rw [hC0]
          linarith
    linarith
  have hmain :
      c * Finset.sum s A ≤ (F 0 - F k) + c * Finset.sum s (fun n => C (n - 1)) := by
    calc
      c * Finset.sum s A = Finset.sum s (fun n => c * A n) := hleft.symm
      _ ≤ Finset.sum s (fun n => (F (n - 1) - F n) + c * C (n - 1)) := hsum
      _ = (F 0 - F k) + c * Finset.sum s (fun n => C (n - 1)) := hright
  have hCscaled :
      c * Finset.sum s (fun n => C (n - 1)) ≤ c * Finset.sum s C :=
    mul_le_mul_of_nonneg_left hprev_le_cur hc_nonneg
  calc
    c * Finset.sum (Finset.Icc 1 k) A =
        c * Finset.sum s A := by rfl
    _ ≤ (F 0 - F k) + c * Finset.sum s (fun n => C (n - 1)) := hmain
    _ ≤ gap + c * Finset.sum s C := by
      nlinarith
    _ = gap + c * Finset.sum (Finset.Icc 1 k) C := by rfl

/-- Coupled scalar sums are bounded after absorbing a `q / 6` current-sum term.

If `C_sum` is controlled by `q / (6 * (1 - q))` times `A_sum`, and the
objective inequality controls `A_sum` up to the same `C_sum`, then both sums are
bounded by the objective gap with denominator `6 - 7 * q`.

Layer: Glue | Gap: Level 1 (coupled scalar sum absorption)
Proof: move the current-sum bound into the objective inequality, prove the
  remaining coefficient is positive from `0 < 6 - 7 * q`, divide by it, and
  substitute the resulting `A_sum` bound back into the `C_sum` bound.
Source: Mathlib ordered-field arithmetic and linear ordered ring inequalities
Used in: accelerated proximal-point summed displacement absorption after a
  finite objective telescope and a lagged recurrence bound
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal point -/
theorem bounds_of_coupled_sum_absorption_q_six
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {mu q gap A_sum C_sum : R}
    (hmu_pos : 0 < mu)
    (hq_nonneg : 0 ≤ q)
    (hdenom_core_pos : 0 < 6 - 7 * q)
    (hcurrent : C_sum ≤ q / (6 * (1 - q)) * A_sum)
    (hobjective : (3 * mu / 2) * A_sum ≤ gap + (3 * mu / 2) * C_sum) :
    A_sum ≤ 4 * (1 - q) / (mu * (6 - 7 * q)) * gap ∧
      C_sum ≤ 2 * q / (3 * mu * (6 - 7 * q)) * gap := by
  have hden_one_pos : 0 < 1 - q := by
    nlinarith [hdenom_core_pos]
  have hmu_denom_pos : 0 < mu * (6 - 7 * q) :=
    mul_pos hmu_pos hdenom_core_pos
  have hr_nonneg : 0 ≤ q / (6 * (1 - q)) := by
    exact div_nonneg hq_nonneg (mul_nonneg (by norm_num) (le_of_lt hden_one_pos))
  have hcoef_pos :
      0 < (3 * mu / 2) * (1 - q / (6 * (1 - q))) := by
    have hinner_pos : 0 < 1 - q / (6 * (1 - q)) := by
      field_simp [ne_of_gt hden_one_pos]
      nlinarith [hdenom_core_pos]
    positivity
  have hA_scaled :
      ((3 * mu / 2) * (1 - q / (6 * (1 - q)))) * A_sum ≤ gap := by
    have hC_scaled :
        (3 * mu / 2) * C_sum ≤
          (3 * mu / 2) * (q / (6 * (1 - q)) * A_sum) := by
      exact mul_le_mul_of_nonneg_left hcurrent (by positivity)
    nlinarith
  have hA_bound :
      A_sum ≤ 4 * (1 - q) / (mu * (6 - 7 * q)) * gap := by
    calc
      A_sum =
          ((3 * mu / 2) * (1 - q / (6 * (1 - q))))⁻¹ *
            (((3 * mu / 2) * (1 - q / (6 * (1 - q)))) * A_sum) := by
        rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hcoef_pos), one_mul]
      _ ≤
          ((3 * mu / 2) * (1 - q / (6 * (1 - q))))⁻¹ * gap := by
        exact mul_le_mul_of_nonneg_left hA_scaled
          (inv_nonneg.mpr (le_of_lt hcoef_pos))
      _ = 4 * (1 - q) / (mu * (6 - 7 * q)) * gap := by
        field_simp [ne_of_gt hmu_pos, ne_of_gt hden_one_pos,
          ne_of_gt hdenom_core_pos, ne_of_gt hmu_denom_pos]
        ring
  have hC_bound :
      C_sum ≤ 2 * q / (3 * mu * (6 - 7 * q)) * gap := by
    calc
      C_sum ≤ q / (6 * (1 - q)) * A_sum := hcurrent
      _ ≤ q / (6 * (1 - q)) *
          (4 * (1 - q) / (mu * (6 - 7 * q)) * gap) := by
        exact mul_le_mul_of_nonneg_left hA_bound hr_nonneg
      _ = 2 * q / (3 * mu * (6 - 7 * q)) * gap := by
        field_simp [ne_of_gt hmu_pos, ne_of_gt hden_one_pos,
          ne_of_gt hdenom_core_pos]
        ring
  exact ⟨hA_bound, hC_bound⟩

/-- An inverse product bound absorbs a positive multiplier into two inverse branch bounds.

If a quantity `q` is bounded by `(M * C)⁻¹`, multiplying by the positive `M`
gives a `C⁻¹` bound. Any positive lower bounds `A ≤ C` and `B ≤ C` then convert
that bound into the two inverse estimates `A⁻¹` and `B⁻¹`.

Layer: Glue | Gap: Level 0 (ordered-field inverse-product absorption)
Proof: multiply the product-inverse bound by the nonnegative multiplier, cancel
  the positive factor in `(M * C)⁻¹`, and use inverse monotonicity on positive
  denominators for the two branch bounds.
Source: Mathlib ordered-field inverse monotonicity and field simplification APIs
Used in: accelerated proximal-point rate absorption from a common maximum
  inner-loop denominator into separate residual and distance estimates
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/main_theorem/proof/6
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
theorem mul_le_inv_bounds_of_le_inv_mul_max_bound
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {M A B C q : K}
    (hM_pos : 0 < M)
    (hA_pos : 0 < A)
    (hB_pos : 0 < B)
    (hA_le_C : A ≤ C)
    (hB_le_C : B ≤ C)
    (hq : q ≤ (M * C)⁻¹) :
    M * q ≤ A⁻¹ ∧ M * q ≤ B⁻¹ := by
  have hC_pos : 0 < C := lt_of_lt_of_le hA_pos hA_le_C
  have hq_le_Cinv : M * q ≤ C⁻¹ := by
    calc
      M * q ≤ M * (M * C)⁻¹ :=
        mul_le_mul_of_nonneg_left hq (le_of_lt hM_pos)
      _ = C⁻¹ := by
        field_simp [ne_of_gt hM_pos, ne_of_gt hC_pos]
  have hCinv_le_Ainv : C⁻¹ ≤ A⁻¹ := by
    have hle := one_div_le_one_div_of_le hA_pos hA_le_C
    simpa [one_div] using hle
  have hCinv_le_Binv : C⁻¹ ≤ B⁻¹ := by
    have hle := one_div_le_one_div_of_le hB_pos hB_le_C
    simpa [one_div] using hle
  exact ⟨le_trans hq_le_Cinv hCinv_le_Ainv, le_trans hq_le_Cinv hCinv_le_Binv⟩

namespace SOptLib

/-- A two-coefficient weighted scalar telescope preserves the terminal tail.

If a potential sequence is nonnegative on the interior of `Icc 1 k` and adjacent
coefficients satisfy `c (n + 1) <= d n`, then the weighted drops
`c t * V (t - 1) - d t * V t` telescope to at most the first incoming term
minus the terminal outgoing term.

Layer: Glue | Gap: Level 1 (two-coefficient weighted scalar telescope)
Proof: induct on the right endpoint of the closed interval; the coefficient
  bridge and nonnegative interior potential make each exposed middle term
  nonpositive, so the induction preserves the terminal tail.
Source: Mathlib finite sums over natural intervals and ordered-ring arithmetic
Used in: randomized accelerated proximal-point Bregman and component-memory
  potential telescopes with adjacent coefficient bridges
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point -/
theorem sum_Icc_two_coeff_telescope_le
    {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (c d V : ℕ → R) (k : ℕ) (hk : 1 ≤ k)
    (hV_nonneg : ∀ n, 1 ≤ n → n < k → 0 ≤ V n)
    (hbridge : ∀ n, 1 ≤ n → n < k → c (n + 1) ≤ d n) :
    Finset.sum (Finset.Icc 1 k) (fun t => c t * V (t - 1) - d t * V t) ≤
      c 1 * V 0 - d k * V k := by
  classical
  have hstrong : ∀ m, (hm : 1 ≤ m) → m ≤ k →
      Finset.sum (Finset.Icc 1 m) (fun t => c t * V (t - 1) - d t * V t) ≤
        c 1 * V 0 - d m * V m := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base =>
        intro _hbase_le
        simp
    | succ n hn ih =>
        intro hsucc_le
        have hn1 : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
        rw [Finset.sum_Icc_succ_top hn1]
        rw [Nat.succ_sub_one]
        have hn_le_k : n ≤ k := Nat.le_of_succ_le hsucc_le
        have hn_lt_k : n < k := Nat.lt_of_succ_le hsucc_le
        have hmiddle : c (n + 1) * V n - d n * V n ≤ 0 := by
          have hcoef : c (n + 1) - d n ≤ 0 :=
            sub_nonpos.mpr (hbridge n hn hn_lt_k)
          have hmul : (c (n + 1) - d n) * V n ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg hcoef (hV_nonneg n hn hn_lt_k)
          simpa [sub_mul] using hmul
        have hprev := ih hn_le_k
        nlinarith
  exact hstrong k hk le_rfl

/-- A linear functional plus centered norm-square regularizer restricts to a
scalar quadratic along an affine line.

For the line `ut + a • d`, the model value equals the base value at `ut` plus
the quadratic coefficient `beta * ‖d‖^2 / 2` times `a^2`, minus the directional
linear coefficient `⟪beta • (u - ut) - g, d⟫` times `a`.

Layer: Glue | Gap: Level 1 (Hilbert line-search quadratic expansion)
Proof: rewrite the shifted line displacement, expand `‖x + y‖^2` by
  `norm_add_sq_real`, and close the remaining scalar identity by ring
  normalization.
Source: Mathlib real inner-product norm-square identities and commutative-ring
  normalization APIs
Used in: stochastic conditional-gradient sliding inner line search when
  converting the selected affine segment objective into a scalar quadratic
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
theorem linear_centered_quadratic_along_line_eq_quadratic
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g u ut d : E) (beta a : ℝ) :
    ⟪g, ut + a • d⟫_ℝ + beta / 2 * ‖ut + a • d - u‖ ^ 2 =
      (⟪g, ut⟫_ℝ + beta / 2 * ‖ut - u‖ ^ 2) +
        ((beta * ‖d‖ ^ 2) / 2) * a ^ 2 -
          ⟪beta • (u - ut) - g, d⟫_ℝ * a := by
  have hline_sub : ut + a • d - u = (ut - u) + a • d := by
    abel
  rw [hline_sub]
  simp [norm_add_sq_real, inner_add_right, inner_sub_left, inner_smul_left,
    inner_smul_right, norm_smul]
  have habs_mul_sq : (|a| * ‖d‖) ^ 2 = (a * ‖d‖) ^ 2 := by
    rw [mul_pow, mul_pow, sq_abs]
  rw [habs_mul_sq]
  ring

/-- Convert an approximate projected-gradient inequality into a squared-distance drop.

If the perturbed vector `g + beta • (up - u)` has inner product at most `eta`
against the comparison direction `up - x`, then the unperturbed inner product is
bounded by `eta` plus the standard Hilbert three-point distance difference.

Layer: Glue | Gap: Level 1 (Hilbert projection distance-drop algebra)
Proof: split the inner product over addition and scalar multiplication, expand
  the Hilbert three-point identity with `norm_sub_sq_real`, then discharge the
  scalar inequality by ordered-ring arithmetic.
Source: Mathlib real inner-product norm-square expansion APIs
Used in: approximate projection and conditional-gradient sliding distance-drop
  conversion before one-step descent recursions
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
theorem inner_le_eta_add_half_smul_norm_sub_sq_sub_of_add_smul_inner_le
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    {g u up x : E} {beta eta : ℝ}
    (hproj : ⟪g + beta • (up - u), up - x⟫_ℝ ≤ eta) :
    ⟪g, up - x⟫_ℝ ≤
      eta + beta / 2 * (‖u - x‖ ^ 2 - ‖up - x‖ ^ 2 - ‖up - u‖ ^ 2) := by
  have hsplit :
      ⟪g + beta • (up - u), up - x⟫_ℝ =
        ⟪g, up - x⟫_ℝ + beta * ⟪up - u, up - x⟫_ℝ := by
    simp [inner_add_left, inner_smul_left]
  have hthree :
      ⟪up - u, up - x⟫_ℝ =
        (‖up - x‖ ^ 2 + ‖up - u‖ ^ 2 - ‖u - x‖ ^ 2) / 2 := by
    have hnorm := norm_sub_sq_real (up - x) (up - u)
    have hsub : (up - x) - (up - u) = u - x := by
      abel
    rw [hsub] at hnorm
    have hcomm : ⟪up - x, up - u⟫_ℝ = ⟪up - u, up - x⟫_ℝ := by
      rw [real_inner_comm]
    nlinarith
  rw [hsplit, hthree] at hproj
  nlinarith

/-- A triangular weighted-sum budget over `Icc 1 T` gives a pointwise bound.

If the one-based weighted sum of a scalar sequence is at most `3 * T * A`, then
some index in the window has value at most `6 * A / (T + 1)`.

Layer: Glue | Gap: Level 0 (one-based triangular weighted-average extraction)
Proof: compare the weighted sum to the same positive natural weights times the
  candidate constant, use the triangular `Icc 1 T` sum identity, and apply
  `Finset.exists_le_of_sum_le`; positivity of the selected natural weight
  cancels it from the selected inequality.
Source: Mathlib finite sums over natural intervals and finite-set ordered
  averaging APIs
Used in: stochastic conditional-gradient sliding extraction of a small Wolfe
  gap from a triangular weighted finite-window telescope
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec/steps
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
theorem exists_le_of_weighted_sum_Icc_one_le
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K]
    (T : ℕ) (A : K) (u : ℕ → K)
    (hT_pos : 1 ≤ T)
    (hsum : Finset.sum (Finset.Icc 1 T) (fun j => (j : K) * u j) ≤
      3 * (T : K) * A) :
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ T ∧ u j ≤
      6 * A / (((T + 1 : ℕ) : K)) := by
  classical
  let B : K := 6 * A / (((T + 1 : ℕ) : K))
  have hden_pos : 0 < (((T + 1 : ℕ) : K)) := by
    exact_mod_cast Nat.succ_pos T
  have hden_ne : (((T + 1 : ℕ) : K)) ≠ 0 := ne_of_gt hden_pos
  have hs_nonempty : (Finset.Icc 1 T).Nonempty := by
    exact ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hT_pos⟩⟩
  have htri_all :
      ∀ T : ℕ,
        Finset.sum (Finset.Icc 1 T) (fun j => (j : K)) =
          (T : K) * (((T + 1 : ℕ) : K)) / 2 := by
    intro T
    induction T with
    | zero =>
        simp
    | succ T ih =>
        have htop : 1 ≤ T + 1 := Nat.succ_pos T
        rw [Finset.sum_Icc_succ_top htop, ih]
        norm_num
        ring
  have htri :
      Finset.sum (Finset.Icc 1 T) (fun j => (j : K)) =
        (T : K) * (((T + 1 : ℕ) : K)) / 2 :=
    htri_all T
  have hsumB :
      Finset.sum (Finset.Icc 1 T) (fun j => (j : K) * B) =
        3 * (T : K) * A := by
    calc
      Finset.sum (Finset.Icc 1 T) (fun j => (j : K) * B)
          = Finset.sum (Finset.Icc 1 T) (fun j => (j : K)) * B := by
            rw [Finset.sum_mul]
      _ = ((T : K) * (((T + 1 : ℕ) : K)) / 2) * B := by
            rw [htri]
      _ = 3 * (T : K) * A := by
            dsimp [B]
            field_simp [hden_ne]
            ring
  have hle_sum :
      Finset.sum (Finset.Icc 1 T) (fun j => (j : K) * u j) ≤
        Finset.sum (Finset.Icc 1 T) (fun j => (j : K) * B) := by
    rw [hsumB]
    exact hsum
  rcases Finset.exists_le_of_sum_le hs_nonempty hle_sum with ⟨j, hjmem, hjmul⟩
  have hj_bounds := Finset.mem_Icc.mp hjmem
  have hj_pos : 0 < (j : K) := by
    exact_mod_cast hj_bounds.1
  have hu_le_B : u j ≤ B := by
    exact le_of_mul_le_mul_left hjmul hj_pos
  refine ⟨j, hj_bounds.1, hj_bounds.2, ?_⟩
  simpa [B] using hu_le_B

end SOptLib

-- Batch 2 promoted from .sgd_phase3_staging/SOptLib/Glue/div_nat_succ_positiveCeil_le.lean
-- Generalization plan (G0):
-- concept/name: div_nat_succ_positiveCeil_le exposes the scalar positive-ceiling
-- denominator bound that converts an `A / (T + 1)` rate into a target tolerance;
-- orig was positive_ceiling_turns_gap_bound_into_stop.
-- generality used: real scalars only; no measure, convexity, smoothness, oracle,
-- or finite-dimensional hypotheses are used.
-- portable call pattern: termination proofs for conditional-gradient,
-- projection-sliding, and stochastic-gradient subroutines choose
-- `T = max 1 (Nat.ceil (A / eta))`; their numerator `A` and tolerance `eta`
-- vary, while the conclusion `A / (T + 1) <= eta` is unchanged.
-- counterargument checked: this is not paper-local traceability because it is the
-- recurring scalar bridge from a ceiling horizon to a stopping certificate; not a
-- pure wrapper because existing `le_positive_ceil_max_one` gives only
-- `A / eta <= T`, leaving denominator clearing and successor monotonicity.
-- coverage search: searched catalog/source for `ceil`, `positive ceiling`,
-- `Nat.ceil`, `max 1`, and the precise `A / (max 1 ceil (A / eta) + 1) <= eta`
-- shape; top SOptLib hits were `le_positive_ceil_max_one`,
-- `le_positive_ceil_threeway_max`, and `natCast_max_one_ceil_le_add_two`, all
-- partial; LeanSearch returned ENat/NNReal ceiling facts but no duplicate.
-- minimal hypotheses: `0 < eta` is the only denominator-clearing hypothesis
-- needed; the numerator need not be nonnegative because the ceiling lower bound
-- handles arbitrary real `A / eta`.

/-- A positive ceiling horizon makes an `A / (T + 1)` rate at most the tolerance.

For positive `eta`, choose `T = max 1 (Nat.ceil (A / eta))`.  Then the
successor denominator is large enough to turn the scalar rate `A / (T + 1)`
into the stopping certificate `<= eta`.

Layer: Glue | Gap: Level 0 (positive-ceiling successor denominator bound)
Proof: use the positive-ceiling lower bound for `A / eta`, multiply by the
  positive tolerance, pass from `T` to `T + 1`, and clear the positive natural
  denominator.
Source: Mathlib real ordered-field arithmetic and natural ceiling APIs
Used in: stochastic conditional-gradient sliding termination converts the
  ceiling inner-loop horizon rate into a Wolfe-gap stopping certificate
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
theorem div_nat_succ_positiveCeil_le
    (A eta : ℝ) (heta : 0 < eta) :
    let T : ℕ := max 1 (Nat.ceil (A / eta))
    A / (((T + 1 : ℕ) : ℝ)) ≤ eta := by
  let T : ℕ := max 1 (Nat.ceil (A / eta))
  have hceil : A / eta ≤ (T : ℝ) := by
    simpa [T] using le_positive_ceil_max_one (A / eta)
  have heta_nonneg : 0 ≤ eta := le_of_lt heta
  have heta_ne : eta ≠ 0 := ne_of_gt heta
  have hA_le_etaT : A ≤ eta * (T : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hceil heta_nonneg
    have hleft : eta * (A / eta) = A := by
      field_simp [heta_ne]
    nlinarith
  have hT_le_succ : (T : ℝ) ≤ (((T + 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.le_succ T
  have hA_le_eta_succ : A ≤ eta * (((T + 1 : ℕ) : ℝ)) := by
    have hmul := mul_le_mul_of_nonneg_left hT_le_succ heta_nonneg
    nlinarith
  have hden_pos : 0 < (((T + 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.succ_pos T
  rw [div_le_iff₀ hden_pos]
  exact hA_le_eta_succ


-- Batch 2 promoted from .sgd_phase3_staging/SOptLib/Glue/argmin_Icc_zero_one_pos_quadratic_eq_min_one.lean
/-!
-- Generalization plan (G0):
-- concept/name: argmin_Icc_zero_one_pos_quadratic_eq_min_one exposes the
--   closed-form minimizer of a positive scalar quadratic on the unit interval;
--   orig was scalar_quadratic_interval_argmin_eq_min_one, renamed away from
--   local line-search and CndG proof labels.
-- generality used: an arbitrary linear ordered field with scalar parameters
--   `alpha`, `den`, and `q`; no measure, independence, integrability,
--   convexity, smoothness, oracle, filtration, topology, or finite-dimensional
--   assumptions are used.
-- portable call pattern: projected scalar line-search proofs in Frank-Wolfe,
--   conditional-gradient, projection-sliding, and proximal-gradient variants
--   can change the positive denominator, quotient, and selected minimizer while
--   reusing the same conclusion that the interval minimizer is `min 1 q`.
-- counterargument checked: not paper-local traceability because the statement
--   is a paper-free ordered-field argmin certificate; not a caller-side
--   expression because it packages the nontrivial uniqueness/clamping argument
--   from the minimizer inequality, interval membership, and quotient
--   nonnegativity.
-- coverage search: searched SOptLib catalog/source for `argmin`, `Icc`,
--   `quadratic`, `min one`, and the precise source declaration; LeanSearch for
--   "real quadratic function positive coefficient minimizer on interval zero
--   one equals min one q" returned only general convex minimizer APIs such as
--   `ConvexOn.isMinOn_of_rightDeriv_eq_zero` and compact argmin facts.  No
--   Mathlib or SOptLib hit gives this closed-form interval clamp selector.
-- minimal hypotheses: the denominator positivity, quotient nonnegativity,
--   interval membership, and pointwise minimizer inequality are all used; the
--   proof generalizes from `ℝ` to an arbitrary linear ordered field.
-/

/-- A positive scalar quadratic minimized on `[0,1]` selects the upper clamp
`min 1 q`.

If `alpha` minimizes `a ↦ (den / 2) * a ^ 2 - den * q * a` over the unit
interval, with `den > 0` and `q >= 0`, then `alpha` is the projection of the
unconstrained minimizer `q` onto `[0,1]`.

Layer: Glue | Gap: Level 1 (unit-interval quadratic argmin clamp)
Proof: compare the minimizer with `q` when `q <= 1` and with `1` when
  `q > 1`; completing the square or factoring the endpoint difference makes
  any other selected minimizer impossible by ordered-field arithmetic.
Source: ordered-field algebra for one-dimensional convex quadratics on closed
  intervals
Used in: projected scalar line-search quotient identification for conditional
  gradient and projection-sliding updates
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec/steps/6
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
theorem argmin_Icc_zero_one_pos_quadratic_eq_min_one
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {alpha den q : R} (hden : 0 < den) (hq0 : 0 ≤ q)
    (halpha : alpha ∈ Set.Icc (0 : R) 1)
    (hmin : ∀ a ∈ Set.Icc (0 : R) 1,
      (den / 2) * alpha ^ 2 - den * q * alpha ≤
        (den / 2) * a ^ 2 - den * q * a) :
    alpha = min 1 q := by
  rcases halpha with ⟨halpha0, halpha1⟩
  by_cases hq1 : q ≤ 1
  · have hqmem : q ∈ Set.Icc (0 : R) 1 := ⟨hq0, hq1⟩
    have hle := hmin q hqmem
    have hdiff :
        ((den / 2) * alpha ^ 2 - den * q * alpha) -
            ((den / 2) * q ^ 2 - den * q * q) =
          (den / 2) * (alpha - q) ^ 2 := by
      ring
    have hle0 :
        ((den / 2) * alpha ^ 2 - den * q * alpha) -
            ((den / 2) * q ^ 2 - den * q * q) ≤ 0 :=
      sub_nonpos.mpr hle
    have hnonneg : 0 ≤ (den / 2) * (alpha - q) ^ 2 :=
      mul_nonneg (le_of_lt (half_pos hden)) (sq_nonneg _)
    have hprod_le : (den / 2) * (alpha - q) ^ 2 ≤ 0 := by
      nlinarith
    have hprod_eq : (den / 2) * (alpha - q) ^ 2 = 0 :=
      le_antisymm hprod_le hnonneg
    have hden_half_ne : den / 2 ≠ 0 := ne_of_gt (half_pos hden)
    have hsq : (alpha - q) ^ 2 = 0 := by
      rcases mul_eq_zero.mp hprod_eq with hzero | hzero
      · exact False.elim (hden_half_ne hzero)
      · exact hzero
    have halphaq : alpha = q := by
      have hsub : alpha - q = 0 := sq_eq_zero_iff.mp hsq
      linarith
    simp [hq1, halphaq]
  · have hqgt : 1 < q := lt_of_not_ge hq1
    have h1mem : (1 : R) ∈ Set.Icc (0 : R) 1 := by norm_num
    have hle := hmin 1 h1mem
    have hdiff :
        ((den / 2) * alpha ^ 2 - den * q * alpha) -
            ((den / 2) * 1 ^ 2 - den * q * 1) =
          (den / 2) * (alpha - 1) * (alpha + 1 - 2 * q) := by
      ring
    have hle0 :
        ((den / 2) * alpha ^ 2 - den * q * alpha) -
            ((den / 2) * 1 ^ 2 - den * q * 1) ≤ 0 :=
      sub_nonpos.mpr hle
    by_contra halphane
    have hmin_eq : min (1 : R) q = 1 := by
      exact min_eq_left (le_of_lt hqgt)
    have halphane_one : alpha ≠ 1 := by
      intro halphaone
      exact halphane (by simpa [hmin_eq] using halphaone)
    have halphalt : alpha < 1 := lt_of_le_of_ne halpha1 halphane_one
    have hleft_neg : alpha - 1 < 0 := by linarith
    have hright_neg : alpha + 1 - 2 * q < 0 := by linarith
    have hmul_pos : 0 < (alpha - 1) * (alpha + 1 - 2 * q) :=
      mul_pos_of_neg_of_neg hleft_neg hright_neg
    have hprod_pos : 0 < (den / 2) * ((alpha - 1) * (alpha + 1 - 2 * q)) :=
      mul_pos (half_pos hden) hmul_pos
    have hprod_le : (den / 2) * ((alpha - 1) * (alpha + 1 - 2 * q)) ≤ 0 := by
      nlinarith
    nlinarith


-- Batch 2 promoted from .sgd_phase3_staging/SOptLib/Glue/sum_Icc_coeff_mul_shifted_sub_eq_sum_coeff_sub_mul_sub_tail.lean
/-!
-- Generalization plan (G0):
-- concept/name: sum_Icc_coeff_mul_shifted_sub_eq_sum_coeff_sub_mul_sub_tail exposes a one-based shifted finite-difference summation-by-parts identity; orig was weighted_shifted_drop_summation_by_parts.
-- generality used: arbitrary coefficient and potential sequences valued in a commutative ring; no measure, carrier, convexity, smoothness, oracle, filtration, order, or finite-dimensional assumptions are used.
-- portable call pattern: conditional-gradient, accelerated, mirror-descent, and proximal finite-window proofs can rewrite a weighted shifted potential drop into adjacent coefficient differences plus a terminal tail while changing only the coefficient sequence and potential.
-- counterargument checked: not paper-local traceability because the identity is paper-free finite-sum algebra; not a pure wrapper because the call-site needs the adjacent-difference normal form, and existing SOptLib telescope lemmas are inequalities with monotonicity/nonnegativity hypotheses rather than this equality.
-- coverage search: searched catalog and sources for `summation`, `telescope`, `sum_Icc`, `coeff`, `shifted`, and `two_coeff`; SOptLib hits `sum_Icc_sub_succ`, `sum_weighted_sub_mul_le_first_sub_tail`, and `sum_Icc_two_coeff_telescope_le` are partial, while LeanSearch hits `Finset.sum_Ico_by_parts` and `Finset.sum_Ioc_by_parts` are Abel summation forms over prefix sums, not this shifted adjacent-difference boundary identity.
-- minimal hypotheses: the no-left-boundary formula requires exactly `c 0 = 0`; without it the missing initial term `c 0 * Delta 2` makes the statement false.
-/

namespace SOptLib

/-- Shifted weighted finite differences telescope into adjacent coefficient differences.

If the initial coefficient vanishes, then the weighted drop
`c j * (Delta (j + 1) - Delta (j + 2))` over `Icc 1 N` equals the sum of
adjacent coefficient differences against `Delta (j + 1)`, minus the terminal
tail.

Layer: Glue | Gap: Level 1 (shifted coefficient summation by parts)
Proof: induction on the upper endpoint, splitting the last point of both
  `Icc` sums with `Finset.sum_Icc_succ_top`, then ring-normalizing the exposed
  boundary terms.
Source: Mathlib finite sums over natural intervals and commutative-ring
  arithmetic
Used in: stochastic conditional-gradient sliding shifted Delta-drop telescope
  before coefficient-specific scalar bounds
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec/steps
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
theorem sum_Icc_coeff_mul_shifted_sub_eq_sum_coeff_sub_mul_sub_tail
    {R : Type*} [CommRing R] (N : ℕ) (c Delta : ℕ → R)
    (hc_zero : c 0 = 0) :
    Finset.sum (Finset.Icc 1 N)
        (fun j => c j * (Delta (j + 1) - Delta (j + 2))) =
      Finset.sum (Finset.Icc 1 N)
        (fun j => (c j - c (j - 1)) * Delta (j + 1)) -
        c N * Delta (N + 2) := by
  induction N with
  | zero =>
      simp [hc_zero]
  | succ n ih =>
      have htop : 1 ≤ n + 1 := Nat.succ_pos n
      rw [Finset.sum_Icc_succ_top htop, Finset.sum_Icc_succ_top htop, ih]
      have hpred : n + 1 - 1 = n := by omega
      rw [hpred]
      ring_nf

end SOptLib


-- Batch 2 promoted from .sgd_phase3_staging/SOptLib/Glue/sum_Icc_shifted_delta_drop_mul_nat_mul_nat_add_two_le.lean
/-!
-- Generalization plan (G0):
-- concept/name: sum_Icc_shifted_delta_drop_mul_nat_mul_nat_add_two_le exposes a scalar shifted Delta-drop finite-sum bound with triangular natural coefficients; orig was shifted_delta_drop_sum_le_two_mul.
-- generality used: ordered-field-valued natural-indexed sequences only; no measure, carrier, convexity, smoothness, oracle, filtration, or finite-dimensional assumptions are used.
-- portable call pattern: conditional-gradient sliding, accelerated conditional-gradient, and mirror/proximal finite-window convergence proofs can call this after proving a shifted residual rate `Delta (t+1) <= 2*A/(t+1)`; the scalar sequence and budget `A` change while the `2*T*A` conclusion shape stays fixed.
-- counterargument checked: not paper-local traceability because the statement is paper-free finite-sum algebra; not a wrapper over the already staged weighted-gap theorem because this is the reusable inner Delta-drop estimate consumed by that broader aggregation.
-- coverage search: searched catalog/sources for `shifted_delta_drop`, `sum_Icc`, `weighted drop`, and `summation`; SOptLib hits `sum_Icc_coeff_mul_shifted_sub_eq_sum_coeff_sub_mul_sub_tail`, `weighted_sum_le_three_mul_of_shifted_delta_step`, and `sum_Icc_two_coeff_telescope_le` are partial, while LeanSearch returned forward-difference identities rather than this coefficient-specific ordered bound.
-- minimal hypotheses: removed the unused `1 <= T` assumption and weakened global nonnegativity of `Delta` to the terminal fact `0 <= Delta (T + 2)` plus the local rate bound on `Icc 1 T`.
-/

namespace SOptLib

/-- A shifted Delta-drop telescope with triangular coefficients is bounded by `2*T*A`.

If `Delta (j+1) <= 2*A/(j+1)` on `Icc 1 T` and the terminal shifted potential
is nonnegative, then the weighted sum of drops with coefficients
`j * (j + 2) / 2` is at most `2*T*A`.

Layer: Glue | Gap: Level 1 (shifted Delta-drop triangular-coefficient bound)
Proof: rewrite the shifted drops by the adjacent-coefficient summation-by-parts
  identity, drop the nonnegative terminal tail, bound each coefficient-weighted
  residual by `2*A`, and count the `T` summands.
Source: Mathlib finite sums over natural intervals, real ordered-field
  arithmetic, and Abel-style summation by parts
Used in: stochastic conditional-gradient sliding shifted residual telescope
  before weighted Wolfe-gap aggregation
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec/steps
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
theorem sum_Icc_shifted_delta_drop_mul_nat_mul_nat_add_two_le
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K]
    (T : ℕ) (A : K) (Delta : ℕ → K)
    (hA_nonneg : 0 ≤ A)
    (hDelta_terminal_nonneg : 0 ≤ Delta (T + 2))
    (hDelta_bound : ∀ j, j ∈ Finset.Icc 1 T →
      Delta (j + 1) ≤ 2 * A / (((j + 1 : ℕ) : K))) :
    Finset.sum (Finset.Icc 1 T)
        (fun j => ((j : K) * (((j + 2 : ℕ) : K)) / 2) *
          (Delta (j + 1) - Delta (j + 2))) ≤
      2 * (T : K) * A := by
  classical
  let c : ℕ → K := fun j => ((j : K) * (((j + 2 : ℕ) : K)) / 2)
  have htelescope :
      Finset.sum (Finset.Icc 1 T)
          (fun j => c j * (Delta (j + 1) - Delta (j + 2))) =
        Finset.sum (Finset.Icc 1 T)
          (fun j => (c j - c (j - 1)) * Delta (j + 1)) -
          c T * Delta (T + 2) := by
    exact SOptLib.sum_Icc_coeff_mul_shifted_sub_eq_sum_coeff_sub_mul_sub_tail
      (N := T) (c := c) (Delta := Delta) (by simp [c])
  have htail_nonneg : 0 ≤ c T * Delta (T + 2) := by
    have hc_nonneg : 0 ≤ c T := by
      dsimp [c]
      positivity
    exact mul_nonneg hc_nonneg hDelta_terminal_nonneg
  have hdrop_le :
      Finset.sum (Finset.Icc 1 T)
          (fun j => c j * (Delta (j + 1) - Delta (j + 2))) ≤
        Finset.sum (Finset.Icc 1 T)
          (fun j => (c j - c (j - 1)) * Delta (j + 1)) := by
    rw [htelescope]
    linarith
  have hterm : ∀ j, j ∈ Finset.Icc 1 T →
      (c j - c (j - 1)) * Delta (j + 1) ≤ 2 * A := by
    intro j hj
    have hj_bounds := Finset.mem_Icc.mp hj
    have hcoef_eq : c j - c (j - 1) = (2 * (j : K) + 1) / 2 := by
      dsimp [c]
      have hj_sub : j - 1 + 2 = j + 1 := by omega
      rw [hj_sub]
      rw [Nat.cast_sub hj_bounds.1]
      norm_num
      ring
    have hcoef_nonneg : 0 ≤ c j - c (j - 1) := by
      rw [hcoef_eq]
      nlinarith [show (0 : K) ≤ j by exact_mod_cast Nat.zero_le j]
    have hD_bound := hDelta_bound j hj
    have hmul := mul_le_mul_of_nonneg_left hD_bound hcoef_nonneg
    have hscalar : (c j - c (j - 1)) *
        (2 * A / (((j + 1 : ℕ) : K))) ≤ 2 * A := by
      rw [hcoef_eq]
      have hden_pos : 0 < (((j + 1 : ℕ) : K)) := by
        exact_mod_cast Nat.succ_pos j
      have hnum_le :
          (2 * (j : K) + 1) * A ≤
            (2 * (((j + 1 : ℕ) : K))) * A := by
        have hbase : 2 * (j : K) + 1 ≤
            2 * (((j + 1 : ℕ) : K)) := by
          norm_num
          nlinarith
        exact mul_le_mul_of_nonneg_right hbase hA_nonneg
      field_simp [ne_of_gt hden_pos]
      nlinarith
    exact le_trans hmul hscalar
  calc
    Finset.sum (Finset.Icc 1 T)
        (fun j => ((j : K) * (((j + 2 : ℕ) : K)) / 2) *
          (Delta (j + 1) - Delta (j + 2)))
        = Finset.sum (Finset.Icc 1 T)
          (fun j => c j * (Delta (j + 1) - Delta (j + 2))) := by simp [c]
    _ ≤ Finset.sum (Finset.Icc 1 T)
          (fun j => (c j - c (j - 1)) * Delta (j + 1)) := hdrop_le
    _ ≤ Finset.sum (Finset.Icc 1 T) (fun _j => 2 * A) := by
          exact Finset.sum_le_sum hterm
    _ = 2 * (T : K) * A := by
          rw [Finset.sum_const]
          have hcard : (Finset.Icc 1 T).card = T := by
            rw [Nat.card_Icc]
            omega
          simp [hcard]
          ring

end SOptLib


-- Batch 2 promoted from .sgd_phase3_staging/SOptLib/Glue/weighted_gap_sum_le_three_mul_of_shifted_delta_step.lean
/-!
-- Generalization plan (G0):
-- concept/name: weighted_gap_sum_le_three_mul_of_shifted_delta_step exposes a scalar weighted-gap aggregation from shifted Delta drops plus a small tail; orig was shifted_weighted_delta_telescope_sum_bound.
-- generality used: real-valued natural-indexed sequences only; no measure, carrier, convexity, smoothness, oracle, filtration, or finite-dimensional assumptions are used.
-- portable call pattern: conditional-gradient sliding, accelerated conditional-gradient, and mirror/proximal finite-window proofs can call this after proving a one-step weighted gap bound by a shifted potential drop and an `A * j / (j + 2)` tail; only the gap sequence, potential sequence, and scalar budget `A` change.
-- counterargument checked: not paper-local traceability because the statement is paper-free scalar algebra; not a one-line wrapper because it combines summation of pointwise bounds, shifted summation by parts, coefficient arithmetic, terminal-tail dropping, and tail-budget counting.
-- coverage search: searched catalog and sources for `weighted gap`, `shifted Delta`, `telescope`, `sum_Icc_two_coeff`, and `three`; SOptLib hits `sum_Icc_two_coeff_telescope_le`, `sum_weighted_sub_mul_le_first_sub_tail`, `summed_one_step_gap_bound_of_telescope`, and active weighted-gap aggregators are partial, while LeanSearch returned only ordinary finite-difference telescope lemmas such as `Finset.sum_range_sub'`.
-- minimal hypotheses: weakened the original global Delta nonnegativity to the terminal fact `0 <= Delta (T + 2)` and the global rate to the local window bound used in the finite sum; `0 <= A` is retained for coefficient and tail estimates, while no positivity of `T` is needed.
-/

namespace SOptLib

/-- A shifted Delta-drop one-step bound controls a triangular weighted gap sum.

If every weighted gap on `Icc 1 T` is bounded by the shifted potential drop
with coefficient `j * (j + 2) / 2` plus the tail `A * j / (j + 2)`, and the
shifted potential satisfies the rate `Delta (j + 1) <= 2*A/(j+1)` on the same
window, then the weighted gap sum is at most `3*T*A`.

Layer: Glue | Gap: Level 1 (shifted Delta weighted-gap aggregation)
Proof: sum the one-step inequalities, apply shifted summation by parts to the
  Delta-drop term, drop the nonnegative terminal tail, bound every adjacent
  coefficient term by `2*A`, and count the elementary tail budget by `T*A`.
Source: Mathlib finite sums over natural intervals, real ordered-field
  arithmetic, and Abel-style summation by parts
Used in: stochastic conditional-gradient sliding shifted Wolfe-gap telescope
  after the one-step line-search descent inequality
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec/steps
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
theorem weighted_gap_sum_le_three_mul_of_shifted_delta_step
    (T : ℕ) (A : ℝ) (Delta gap : ℕ → ℝ)
    (hA_nonneg : 0 ≤ A)
    (hDelta_terminal_nonneg : 0 ≤ Delta (T + 2))
    (hDelta_bound : ∀ j, j ∈ Finset.Icc 1 T →
      Delta (j + 1) ≤ 2 * A / (((j + 1 : ℕ) : ℝ)))
    (hstep : ∀ j, j ∈ Finset.Icc 1 T →
      (j : ℝ) * gap j ≤
        ((j : ℝ) * (((j + 2 : ℕ) : ℝ)) / 2) *
            (Delta (j + 1) - Delta (j + 2)) +
          A * (j : ℝ) / (((j + 2 : ℕ) : ℝ))) :
    Finset.sum (Finset.Icc 1 T) (fun j => (j : ℝ) * gap j) ≤
      3 * (T : ℝ) * A := by
  classical
  let drop : ℕ → ℝ := fun j =>
    ((j : ℝ) * (((j + 2 : ℕ) : ℝ)) / 2) *
      (Delta (j + 1) - Delta (j + 2))
  let tail : ℕ → ℝ := fun j => A * (j : ℝ) / (((j + 2 : ℕ) : ℝ))
  have hsum_step :
      Finset.sum (Finset.Icc 1 T) (fun j => (j : ℝ) * gap j) ≤
        Finset.sum (Finset.Icc 1 T) (fun j => drop j + tail j) := by
    exact Finset.sum_le_sum (fun j hj => by
      simpa [drop, tail] using hstep j hj)
  have hdrop :
      Finset.sum (Finset.Icc 1 T) drop ≤ 2 * (T : ℝ) * A := by
    let c : ℕ → ℝ := fun j => ((j : ℝ) * (((j + 2 : ℕ) : ℝ)) / 2)
    have htelescope :
        Finset.sum (Finset.Icc 1 T)
            (fun j => c j * (Delta (j + 1) - Delta (j + 2))) =
          Finset.sum (Finset.Icc 1 T)
            (fun j => (c j - c (j - 1)) * Delta (j + 1)) -
            c T * Delta (T + 2) := by
      exact SOptLib.sum_Icc_coeff_mul_shifted_sub_eq_sum_coeff_sub_mul_sub_tail
        (N := T) (c := c) (Delta := Delta) (by simp [c])
    have htail_nonneg : 0 ≤ c T * Delta (T + 2) := by
      have hc_nonneg : 0 ≤ c T := by
        dsimp [c]
        positivity
      exact mul_nonneg hc_nonneg hDelta_terminal_nonneg
    have hdrop_le :
        Finset.sum (Finset.Icc 1 T)
            (fun j => c j * (Delta (j + 1) - Delta (j + 2))) ≤
          Finset.sum (Finset.Icc 1 T)
            (fun j => (c j - c (j - 1)) * Delta (j + 1)) := by
      rw [htelescope]
      linarith
    have hterm : ∀ j, j ∈ Finset.Icc 1 T →
        (c j - c (j - 1)) * Delta (j + 1) ≤ 2 * A := by
      intro j hj
      have hj_bounds := Finset.mem_Icc.mp hj
      have hcoef_eq : c j - c (j - 1) = (2 * (j : ℝ) + 1) / 2 := by
        dsimp [c]
        have hj_sub : j - 1 + 2 = j + 1 := by omega
        rw [hj_sub]
        rw [Nat.cast_sub hj_bounds.1]
        norm_num
        ring
      have hcoef_nonneg : 0 ≤ c j - c (j - 1) := by
        rw [hcoef_eq]
        nlinarith [show (0 : ℝ) ≤ j by exact_mod_cast Nat.zero_le j]
      have hD_bound := hDelta_bound j hj
      have hmul := mul_le_mul_of_nonneg_left hD_bound hcoef_nonneg
      have hscalar : (c j - c (j - 1)) *
          (2 * A / (((j + 1 : ℕ) : ℝ))) ≤ 2 * A := by
        rw [hcoef_eq]
        have hden_pos : 0 < (((j + 1 : ℕ) : ℝ)) := by
          exact_mod_cast Nat.succ_pos j
        have hnum_le :
            (2 * (j : ℝ) + 1) * A ≤
              (2 * (((j + 1 : ℕ) : ℝ))) * A := by
          have hbase : 2 * (j : ℝ) + 1 ≤
              2 * (((j + 1 : ℕ) : ℝ)) := by
            norm_num
            nlinarith
          exact mul_le_mul_of_nonneg_right hbase hA_nonneg
        field_simp [ne_of_gt hden_pos]
        nlinarith
      exact le_trans hmul hscalar
    calc
      Finset.sum (Finset.Icc 1 T) drop
          =
        Finset.sum (Finset.Icc 1 T)
          (fun j => c j * (Delta (j + 1) - Delta (j + 2))) := by simp [drop, c]
      _ ≤ Finset.sum (Finset.Icc 1 T)
            (fun j => (c j - c (j - 1)) * Delta (j + 1)) := hdrop_le
      _ ≤ Finset.sum (Finset.Icc 1 T) (fun _j => 2 * A) := by
            exact Finset.sum_le_sum hterm
      _ = 2 * (T : ℝ) * A := by
            rw [Finset.sum_const]
            have hcard : (Finset.Icc 1 T).card = T := by
              rw [Nat.card_Icc]
              omega
            simp [hcard]
            ring
  have htail_point : ∀ j, j ∈ Finset.Icc 1 T → tail j ≤ A := by
    intro j _hj
    have hden_pos : 0 < (((j + 2 : ℕ) : ℝ)) := by
      exact_mod_cast Nat.succ_pos (j + 1)
    have hj_le : (j : ℝ) ≤ (((j + 2 : ℕ) : ℝ)) := by
      exact_mod_cast (show j ≤ j + 2 by omega)
    have hfrac_le : (j : ℝ) / (((j + 2 : ℕ) : ℝ)) ≤ 1 := by
      have hdiv :
          (j : ℝ) / (((j + 2 : ℕ) : ℝ)) ≤
            (((j + 2 : ℕ) : ℝ)) / (((j + 2 : ℕ) : ℝ)) :=
        div_le_div_of_nonneg_right hj_le (le_of_lt hden_pos)
      calc
        (j : ℝ) / (((j + 2 : ℕ) : ℝ)) ≤
            (((j + 2 : ℕ) : ℝ)) / (((j + 2 : ℕ) : ℝ)) := hdiv
        _ = 1 := div_self (ne_of_gt hden_pos)
    have hmul := mul_le_mul_of_nonneg_left hfrac_le hA_nonneg
    simpa [tail, div_eq_mul_inv, mul_assoc] using hmul
  have htail :
      Finset.sum (Finset.Icc 1 T) tail ≤ (T : ℝ) * A := by
    calc
      Finset.sum (Finset.Icc 1 T) tail
          ≤ Finset.sum (Finset.Icc 1 T) (fun _ => A) := by
            exact Finset.sum_le_sum htail_point
      _ = (T : ℝ) * A := by
            rw [Finset.sum_const]
            simp
  calc
    Finset.sum (Finset.Icc 1 T) (fun j => (j : ℝ) * gap j)
        ≤ Finset.sum (Finset.Icc 1 T) (fun j => drop j + tail j) := hsum_step
    _ = Finset.sum (Finset.Icc 1 T) drop +
          Finset.sum (Finset.Icc 1 T) tail := by
          rw [Finset.sum_add_distrib]
    _ ≤ 3 * (T : ℝ) * A := by
          nlinarith [hdrop, htail]

end SOptLib


-- Batch 2 promoted from .sgd_phase3_staging/SOptLib/Glue/sum_Icc_mono_coeff_mul_sub_le_terminal_sub_tail.lean
open scoped BigOperators

-- Generalization plan (G0):
-- concept/name: nondecreasing-coefficient finite potential-drop telescope; orig was
--   sum_Icc_increasing_coeff_distance_drop_le_terminal_with_tail.
-- generality used: pure ordered-ring algebra over a natural closed interval; no
--   measure, convexity, smoothness, oracle, or Hilbert-space structure is used.
-- portable call pattern: stochastic first-order and conditional-gradient analyses
--   that sum nondecreasing nonnegative weights against potential drops; the
--   coefficient sequence, potential, cap, and terminal index change while the
--   endpoint-tail conclusion stays the same.
-- counterargument checked: not paper-local traceability and not a one-line wrapper;
--   existing SOptLib telescope lemmas cover decreasing or bridged outgoing
--   coefficients, whereas this lemma uses a uniform cap to handle increasing
--   coefficients.
-- coverage search: queried catalog/rg for sum_Icc, weighted, telescope, terminal,
--   tail, coeff; read SOptLib.sum_weighted_sub_mul_le_first_sub_tail and
--   SOptLib.sum_Icc_two_coeff_telescope_le (partial, opposite coefficient shape);
--   LeanSearch for the natural-language statement returned a transient 502.
-- minimal hypotheses: removed the source lemma's unused nonnegativity of V; kept
--   pointwise nonnegativity of coefficients only on the finite active window and
--   pointwise upper bounds on V only up to k.

/-- A nondecreasing weighted potential-drop telescope is bounded by the terminal
coefficient times the uniform cap, with the terminal tail retained.

If `a` is nonnegative and nondecreasing on `[1, k]`, and `V n <= D` for every
`n <= k`, then the finite sum of weighted drops
`a t * (V (t - 1) - V t)` is at most `a k * D - a k * V k`.

Layer: Glue | Gap: Level 1 (nondecreasing weighted potential telescope)
Proof: induct on the right endpoint of `Finset.Icc 1 m`; in the successor
  case, monotonicity makes the exposed coefficient difference nonnegative, and
  the pointwise cap on `V n` controls the middle term.
Source: Mathlib finite sums over natural intervals and ordered-ring arithmetic
Used in: stochastic conditional-gradient sliding distance-potential telescope
  under nondecreasing ratio weights
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
theorem sum_Icc_mono_coeff_mul_sub_le_terminal_sub_tail
    {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (a V : ℕ → R) (D : R) (k : ℕ) (hk : 1 ≤ k)
    (ha_mono : ∀ n, 1 ≤ n → n < k → a n ≤ a (n + 1))
    (ha_nonneg : ∀ n, 1 ≤ n → n ≤ k → 0 ≤ a n)
    (hV_le : ∀ n, n ≤ k → V n ≤ D) :
    Finset.sum (Finset.Icc 1 k) (fun t => a t * (V (t - 1) - V t)) ≤
      a k * D - a k * V k := by
  classical
  have hstrong : ∀ m, (hm : 1 ≤ m) → m ≤ k →
      Finset.sum (Finset.Icc 1 m) (fun t => a t * (V (t - 1) - V t)) ≤
        a m * D - a m * V m := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base =>
        intro hbase_le
        have ha1 : 0 ≤ a 1 := ha_nonneg 1 le_rfl hbase_le
        have hV0 : V 0 ≤ D := hV_le 0 (Nat.zero_le k)
        have hmul : a 1 * V 0 ≤ a 1 * D :=
          mul_le_mul_of_nonneg_left hV0 ha1
        calc
          Finset.sum (Finset.Icc 1 1) (fun t => a t * (V (t - 1) - V t)) =
              a 1 * (V (1 - 1) - V 1) := by simp
          _ = a 1 * V 0 - a 1 * V 1 := by ring
          _ ≤ a 1 * D - a 1 * V 1 := sub_le_sub_right hmul (a 1 * V 1)
    | succ n hn ih =>
        intro hsucc_le
        have hn_succ_pos : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
        rw [Finset.sum_Icc_succ_top hn_succ_pos, Nat.succ_sub_one]
        have hn_le_k : n ≤ k := Nat.le_trans (Nat.le_succ n) hsucc_le
        have hn_lt_k : n < k := Nat.lt_of_succ_le hsucc_le
        have hprev := ih hn_le_k
        have hcoef_nonneg : 0 ≤ a (n + 1) - a n := by
          exact sub_nonneg.mpr (ha_mono n hn hn_lt_k)
        have hVn_le : V n ≤ D := hV_le n hn_le_k
        have hmiddle :
            (a (n + 1) - a n) * V n ≤ (a (n + 1) - a n) * D :=
          mul_le_mul_of_nonneg_left hVn_le hcoef_nonneg
        nlinarith
  exact hstrong k hk le_rfl


-- Batch 2 promoted from .sgd_phase3_staging/SOptLib/Glue/sum_Icc_mono_coeff_mul_sub_le_terminal.lean
open scoped BigOperators

-- Generalization plan (G0):
-- concept/name: nondecreasing-coefficient finite potential-drop telescope with
--   terminal-tail drop; orig was sum_Icc_increasing_coeff_distance_drop_le_terminal.
-- generality used: pure ordered-ring algebra over a natural closed interval; no
--   measure, convexity, smoothness, oracle, Hilbert-space, or finite-dimensional
--   structure is used.
-- portable call pattern: stochastic first-order and conditional-gradient analyses
--   that only need the coarse bound after summing nondecreasing nonnegative
--   weights against potential drops; the coefficient sequence, potential cap,
--   terminal index, and potential nonnegativity proof vary while the conclusion
--   keeps the same scalar telescope shape.
-- counterargument checked: overlaps the retained-tail theorem staged this round,
--   but differs as the common coarse corollary that callers use after dropping a
--   nonnegative terminal product; not paper-local traceability and not covered by
--   the two-coefficient decreasing telescope API.
-- coverage search: queried catalog/rg for sum_Icc, weighted, telescope, terminal,
--   tail, coeff, monotone; read SOptLib.sum_Icc_two_coeff_telescope_le and
--   the retained-tail companion lemma (partial/stronger);
--   LeanSearch for the natural-language statement found no direct Mathlib
--   finite-sum telescope match before timing out.
-- minimal hypotheses: uses coefficient monotonicity on [1,k), coefficient
--   nonnegativity only at k for the dropped tail and through the retained-tail
--   theorem on [1,k], potential nonnegativity only at k, and the cap V n <= D
--   only for n <= k.

/-- A nondecreasing weighted potential-drop telescope is bounded by the terminal
coefficient times a uniform cap.

If `a` is nonnegative and nondecreasing on `[1, k]`, `V n <= D` for every
`n <= k`, and the terminal potential is nonnegative, then the finite sum of
weighted drops `a t * (V (t - 1) - V t)` is at most `a k * D`.

Layer: Glue | Gap: Level 1 (coarse nondecreasing weighted potential telescope)
Proof: apply the retained-tail telescope bound, then discard the terminal
  product `a k * V k` using nonnegativity of the terminal coefficient and
  terminal potential.
Source: Mathlib finite sums over natural intervals and ordered-ring arithmetic
Used in: stochastic conditional-gradient sliding distance-potential telescope
  after dropping a nonnegative terminal distance term
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
theorem sum_Icc_mono_coeff_mul_sub_le_terminal
    {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (a V : ℕ → R) (D : R) (k : ℕ) (hk : 1 ≤ k)
    (ha_mono : ∀ n, 1 ≤ n → n < k → a n ≤ a (n + 1))
    (ha_nonneg : ∀ n, 1 ≤ n → n ≤ k → 0 ≤ a n)
    (hV_nonneg_terminal : 0 ≤ V k)
    (hV_le : ∀ n, n ≤ k → V n ≤ D) :
    Finset.sum (Finset.Icc 1 k) (fun t => a t * (V (t - 1) - V t)) ≤
      a k * D := by
  have htail :=
    sum_Icc_mono_coeff_mul_sub_le_terminal_sub_tail
      a V D k hk ha_mono ha_nonneg hV_le
  have htail_nonneg : 0 ≤ a k * V k :=
    mul_nonneg (ha_nonneg k hk le_rfl) hV_nonneg_terminal
  linarith


-- Batch 2 promoted from .sgd_phase3_staging/SOptLib/Glue/sum_Icc_one_natCast_eq.lean
/-!
-- Generalization plan (G0):
-- concept/name: sum_Icc_one_natCast_eq exposes the triangular-number identity for one-based finite natural intervals after casting to a scalar field; orig was sum_Icc_one_to_nat_cast
-- generality used: a natural horizon `T` and casts into an ordered field-like scalar type; no measure, carrier, convexity, smoothness, oracle, filtration, or finite-dimensional assumptions are used
-- portable call pattern: weighted-average, randomized-output, conditional-gradient, mirror-descent, and accelerated finite-window proofs with one-based weights `j` can normalize by the triangular denominator while changing only the horizon and scalar type
-- counterargument checked: not paper-local traceability because one-based triangular weights recur across stochastic-optimization averaging arguments; not a pure wrapper because Mathlib's `Finset.sum_range_id` covers zero-based natural `range` sums, not the closed one-based interval with scalar casts and division used at call sites
-- coverage search: searched `sum Icc 1 nat cast triangular`, catalog tokens `sum_Icc_one`, `natCast_eq`, `triangular`, and LeanSearch for the one-based natural-cast sum; Mathlib hit `Finset.sum_range_id` is partial/zero-based, SOptLib hits cover predecessor triangular budget bounds rather than this exact closed form
-- minimal hypotheses: all already minimal for the generalized scalar statement; the proof uses finite interval sums, natural casts, field division by `2`, and ring normalization
-/

namespace SOptLib

/-- The one-based sum of natural-number weights is the triangular number.

For a natural horizon `T`, summing the scalar casts of `1, ..., T` gives
`T * (T + 1) / 2`.

Layer: Glue | Gap: Level 0 (one-based triangular natural-cast sum)
Proof: induct on the upper endpoint, split off the final interval point with
  `Finset.sum_Icc_succ_top`, and close the scalar arithmetic by normalization.
Source: Mathlib finite sums over natural intervals and natural-number casts into
  ordered fields
Used in: stochastic conditional-gradient sliding weighted-average extraction
  from one-based triangular Wolfe-gap weights
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec/steps
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
theorem sum_Icc_one_natCast_eq
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] (T : ℕ) :
    Finset.sum (Finset.Icc 1 T) (fun j => (j : K)) =
      (T : K) * (((T + 1 : ℕ) : K)) / 2 := by
  induction T with
  | zero =>
      simp
  | succ T ih =>
      have htop : 1 ≤ T + 1 := Nat.succ_pos T
      rw [Finset.sum_Icc_succ_top htop, ih]
      norm_num
      ring

end SOptLib


-- Batch 2 promoted from .sgd_phase3_staging/SOptLib/Glue/two_div_nat_succ_cast_mem_Icc.lean
/-!
-- Generalization plan (G0):
-- concept/name: two_div_nat_succ_cast_mem_Icc exposes unit-interval membership for the one-based natural reciprocal weight `2 / (t + 1)`; orig was two_div_nat_succ_mem_Icc
-- generality used: a natural index `t` with `1 ≤ t`, cast to real scalars; no measure, carrier, convexity, smoothness, oracle, filtration, typeclass, or finite-dimensional assumptions are used
-- portable call pattern: conditional-gradient, Frank-Wolfe, and accelerated finite-horizon proofs using the classical trial weight `λ_{t+1} = 2 / (t + 1)` can supply their local positive index and call this interval-membership fact before convex-combination or line-search comparisons
-- counterargument checked: not paper-local traceability because this is a reusable arithmetic admissibility fact for a standard one-based weight; not a pure wrapper because Mathlib's `unitInterval.div_mem` covers nonnegative quotients but does not package the natural cast denominator arithmetic
-- coverage search: searched `2 / ((t + 1 : Nat) : Real) Set.Icc 0 1`, catalog tokens `two_div_nat`, `nat_succ`, `Icc`, and LeanSearch for natural `2/(t+1)` in the unit interval; Mathlib hit `unitInterval.div_mem` is a partial quotient lemma, SOptLib had no existing natural-index specialization
-- minimal hypotheses: all already minimal; `1 ≤ t` is exactly what proves the denominator is at least `2`
-/

namespace SOptLib

/-- The one-based natural weight `2 / (t + 1)` belongs to the unit interval for
every natural index `t ≥ 1`.

This packages the cast arithmetic needed before using the weight as a convex
combination or line-search parameter.

Layer: Glue | Gap: Level 0 (one-based natural reciprocal unit-interval bound)
Proof: cast `0 < t + 1` and `2 ≤ t + 1` to the reals, then use monotonicity of
  division by a nonnegative denominator and cancel the denominator.
Source: Mathlib natural-number casts and ordered real-field division APIs
Used in: stochastic conditional-gradient sliding CndG line-search trial-step
  admissibility before the inner-loop descent comparison
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec/steps
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
theorem two_div_nat_succ_cast_mem_Icc (t : ℕ) (ht : 1 ≤ t) :
    (2 : ℝ) / ((t + 1 : ℕ) : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  have hden_pos : 0 < ((t + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_pos t
  have htwo_le : (2 : ℝ) ≤ ((t + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ ht
  constructor
  · exact div_nonneg (by norm_num) (le_of_lt hden_pos)
  · have hdiv :
        (2 : ℝ) / ((t + 1 : ℕ) : ℝ) ≤
          ((t + 1 : ℕ) : ℝ) / ((t + 1 : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right htwo_le (le_of_lt hden_pos)
    calc
      (2 : ℝ) / ((t + 1 : ℕ) : ℝ) ≤
          ((t + 1 : ℕ) : ℝ) / ((t + 1 : ℕ) : ℝ) := hdiv
      _ = 1 := div_self (ne_of_gt hden_pos)

end SOptLib

namespace SOptLib

theorem div_nat_succ_positive_ceil_le
    (A eta : ℝ) (heta : 0 < eta) :
    let T : ℕ := max 1 (Nat.ceil (A / eta))
    A / (((T + 1 : ℕ) : ℝ)) ≤ eta :=
  div_nat_succ_positiveCeil_le A eta heta

theorem weighted_sum_le_three_mul_of_shifted_delta_step
    (T : ℕ) (A : ℝ) (Delta gap : ℕ → ℝ)
    (hA_nonneg : 0 ≤ A)
    (hDelta_terminal_nonneg : 0 ≤ Delta (T + 2))
    (hDelta_bound : ∀ j, j ∈ Finset.Icc 1 T →
      Delta (j + 1) ≤ 2 * A / (((j + 1 : ℕ) : ℝ)))
    (hstep : ∀ j, j ∈ Finset.Icc 1 T →
      (j : ℝ) * gap j ≤
        ((j : ℝ) * (((j + 2 : ℕ) : ℝ)) / 2) *
            (Delta (j + 1) - Delta (j + 2)) +
          A * (j : ℝ) / (((j + 2 : ℕ) : ℝ))) :
    Finset.sum (Finset.Icc 1 T) (fun j => (j : ℝ) * gap j) ≤
      3 * (T : ℝ) * A :=
  weighted_gap_sum_le_three_mul_of_shifted_delta_step
    T A Delta gap hA_nonneg hDelta_terminal_nonneg hDelta_bound hstep

theorem two_div_nat_cast_mem_Icc
    {K : Type*} [Semifield K] [LinearOrder K] [IsStrictOrderedRing K]
    (n : ℕ) (hn : 2 ≤ n) :
    (2 : K) / (n : K) ∈ Set.Icc (0 : K) 1 := by
  have hden_pos : 0 < (n : K) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hn)
  have htwo_le : (2 : K) ≤ (n : K) := by
    exact_mod_cast hn
  constructor
  · exact div_nonneg (by norm_num) (le_of_lt hden_pos)
  · have hdiv :
        (2 : K) / (n : K) ≤ (n : K) / (n : K) :=
      div_le_div_of_nonneg_right htwo_le (le_of_lt hden_pos)
    calc
      (2 : K) / (n : K) ≤ (n : K) / (n : K) := hdiv
      _ = 1 := div_self (ne_of_gt hden_pos)

end SOptLib

-- Batch 2 promoted from Staging/neg_inner_le_half_mul_norm_sq_add_inv_two_mul_norm_sq.lean
open scoped InnerProductSpace

-- Generalization plan (G0):
-- concept/name: Hilbert-space Young absorption for a negative inner product;
--   orig was inner_neg_le_half_sq_add_inv_sq_of_pos and was renamed away from
--   local residual/descent notation.
-- generality used: arbitrary real inner-product seminormed additive group `E`;
--   no measure, convexity, smoothness, oracle, or finite-dimensional hypotheses.
-- portable call pattern: any stochastic-gradient or conditional-gradient
--   descent proof that absorbs an estimator residual `delta` against a
--   displacement `d`; only the positive scalar `q` and the two vectors change.
-- counterargument checked: this is a short wrapper around Cauchy-Schwarz plus
--   scalar Young, but it exposes the exact reusable Hilbert residual
--   absorption boundary; existing SOptLib young lemmas include additional
--   budget/scale hypotheses or completed-square terms and do not directly
--   cover this two-term pointwise inequality.
-- coverage search: searched `inner norm young half inverse neg_inner` in
--   docs/CATALOG.md and SOptLib, plus LeanSearch for the negative-inner
--   pointwise Young shape; top hits were `abs_real_inner_le_norm`,
--   `scaled_linear_inner_quadratic_le_square_over_denominator`, and
--   `young_absorb_inner_of_norm_sq_budget`, all partial rather than full.
-- minimal hypotheses: all already minimal for this real inner-product/norm
--   statement; positivity of `q` is exactly needed for the inverse coefficient.

/-- A negative Hilbert inner product is absorbed by a positive quadratic split.

For any positive scalar `q`, Cauchy-Schwarz and Young's inequality give
`-<delta,d> <= (q/2)*||d||^2 + (1/(2*q))*||delta||^2`.

Layer: Glue | Gap: Level 1 (Hilbert residual Young absorption)
Proof: bound the negative inner product by Cauchy-Schwarz, then apply the
  nonnegativity of `(q * ‖d‖ - ‖delta‖)^2` after clearing the positive
  denominator.
Source: Mathlib real Hilbert-space Cauchy-Schwarz and ordered-field square
  completion APIs
Used in: stochastic conditional-gradient sliding descent residual absorption
Book citation: book/FOML/StochasticNonconvexCGSliding.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional-gradient sliding -/
theorem neg_inner_le_half_mul_norm_sq_add_inv_two_mul_norm_sq
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    {q : ℝ} (hq : 0 < q) (delta d : E) :
    -⟪delta, d⟫_ℝ ≤
      (q / 2) * ‖d‖ ^ 2 + (1 / (2 * q)) * ‖delta‖ ^ 2 := by
  have hq_ne : q ≠ 0 := ne_of_gt hq
  have hcs : -⟪delta, d⟫_ℝ ≤ ‖delta‖ * ‖d‖ := by
    exact le_trans (neg_le_abs _) (abs_real_inner_le_norm delta d)
  have hyoung :
      ‖delta‖ * ‖d‖ ≤
        (q / 2) * ‖d‖ ^ 2 + (1 / (2 * q)) * ‖delta‖ ^ 2 := by
    have hsquare : 0 ≤ (q * ‖d‖ - ‖delta‖) ^ 2 := sq_nonneg _
    field_simp [hq_ne] at hsquare ⊢
    nlinarith [hsquare]
  exact le_trans hcs hyoung


-- Batch 2 promoted from Staging/min_one_clamp_pos_quadratic_le.lean
-- Generalization plan (G0):
-- concept/name: min_one_clamp_pos_quadratic_le exposes the scalar
--   unit-interval clamp minimizer inequality for a positive one-dimensional
--   quadratic; orig name was already paper-free.
-- generality used: arbitrary linear ordered field with parameters `den`, `q`,
--   and trial point `a`; no measure, topology, convexity, smoothness, oracle,
--   filtration, or finite-dimensional assumptions are used.
-- portable call pattern: projected scalar line-search proofs in
--   conditional-gradient, Frank-Wolfe, projection-sliding, and proximal-gradient
--   methods vary the positive denominator, quotient, and trial step while
--   reusing that the clamped quotient is no worse than any unit-interval step.
-- counterargument checked: not paper-local traceability because the statement
--   is a paper-free ordered-field inequality; not a caller-side expression
--   because it packages the nontrivial clamp case split and quadratic
--   arithmetic; complementary rather than duplicate to
--   argmin_Icc_zero_one_pos_quadratic_eq_min_one, which proves the reverse
--   equality from an abstract argmin certificate.
-- coverage search: searched SOptLib catalog/source for `clamp`, `quadratic`,
--   `argmin`, `min one`, and the precise source name; closest SOptLib hit was
--   `argmin_Icc_zero_one_pos_quadratic_eq_min_one`, which has the inverse
--   certificate-to-clamp direction. LeanSearch for "positive quadratic on
--   interval zero one clamped minimizer inequality min one q" returned general
--   convexity/order hits such as `ConcaveOn.min_le_of_mem_Icc`,
--   `QuadraticMap.PosDef.nonneg`, and `sq_le`, but no closed-form clamp
--   minimizer inequality.
-- minimal hypotheses: denominator positivity and unit-interval membership are
--   used; the proof generalizes from `ℝ` to an arbitrary linear ordered field.
--   The original caller also assumed `0 ≤ q`, but the inequality itself does
--   not require it.

/-- The upper clamp `min 1 q` minimizes a positive scalar quadratic on `[0,1]`.

For `den > 0`, evaluating
`a ↦ (den / 2) * a ^ 2 - den * q * a` at the clamped unconstrained minimizer
`min 1 q` is no larger than evaluating it at any `a ∈ [0,1]`.

Layer: Glue | Gap: Level 1 (unit-interval quadratic clamp inequality)
Proof: split on `q <= 1`; the interior case is completing the square at `q`,
  and the exterior case factors the endpoint difference at `1`.
Source: ordered-field algebra for one-dimensional convex quadratics on closed
  intervals
Used in: projected scalar line-search decrease comparison for conditional
  gradient and projection-sliding updates
Book citation: book/FOML/StochasticNonconvexCGSliding.json#/algorithm_spec/steps/6
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional-gradient sliding -/
theorem min_one_clamp_pos_quadratic_le
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {den q a : R} (hden : 0 < den) (ha : a ∈ Set.Icc (0 : R) 1) :
    (den / 2) * (min 1 q) ^ 2 - den * q * (min 1 q) ≤
      (den / 2) * a ^ 2 - den * q * a := by
  rcases ha with ⟨_ha0, ha1⟩
  by_cases hq1 : q ≤ 1
  · have hmin : min (1 : R) q = q := min_eq_right hq1
    rw [hmin]
    have hsq : 0 ≤ (a - q) ^ 2 := sq_nonneg (a - q)
    have hdiff :
        ((den / 2) * a ^ 2 - den * q * a) -
            ((den / 2) * q ^ 2 - den * q * q) =
          (den / 2) * (a - q) ^ 2 := by
      ring
    nlinarith [half_pos hden, hsq]
  · have hqgt : 1 < q := lt_of_not_ge hq1
    have hmin : min (1 : R) q = 1 := min_eq_left (le_of_lt hqgt)
    rw [hmin]
    have hleft : a - 1 ≤ 0 := by linarith
    have hright : a + 1 - 2 * q < 0 := by linarith
    have hprod_nonneg : 0 ≤ (a - 1) * (a + 1 - 2 * q) :=
      mul_nonneg_of_nonpos_of_nonpos hleft (le_of_lt hright)
    have hdiff :
        ((den / 2) * a ^ 2 - den * q * a) -
            ((den / 2) * 1 ^ 2 - den * q * 1) =
          (den / 2) * (a - 1) * (a + 1 - 2 * q) := by
      ring
    nlinarith [half_pos hden, hprod_nonneg]

-- Generalization plan (G0):
-- concept/name: inner product with an affine-line displacement; orig was
--   `affine_lineMap_inner_sub_right_eq`, renamed to expose the `lineMap` and
--   right-subtraction algebra rather than a paper-local proof block.
-- generality used: an arbitrary real inner product space via
--   `NormedAddCommGroup` and `InnerProductSpace`; no measure, convexity,
--   smoothness, oracle, completeness, or finite-dimensional hypotheses are used.
-- portable call pattern: Bregman segment-derivative proofs for mirror descent,
--   proximal methods, and variance-reduced acceleration instantiate `g`, `a`,
--   `z`, `u`, and `t` to remove the repeated linearization term along a segment.
-- counterargument checked: this is a short wrapper over Mathlib affine-line and
--   inner-product algebra, but not a pure rename of one existing theorem; it
--   packages a recurring compound rewrite that otherwise obscures derivative
--   proofs with local `hseg_sub` and `inner_sub_right` calculations.
-- coverage search: project/catalog search for `lineMap`, `inner sub right`,
--   `affine_lineMap`, and `inner_lineMap` found repeated local calculations but
--   no staged or SOptLib theorem with this statement; LeanSearch returned
--   `AffineMap.lineMap_vsub_left`, `AffineMap.lineMap_apply_module'`, and
--   `inner_sub_right` as partial Mathlib ingredients, not a full duplicate.
-- minimal hypotheses: all already minimal for real inner-product algebra; the
--   proof only uses additive-group/module structure supplied by the inner
--   product space and the scalar field is fixed to `ℝ` by the optimization API.

/-- Inner products against an affine-line point differ by the segment displacement.

For a fixed vector `g` and anchor `a`, subtracting the value at `z` from the
linearization at `lineMap z u t` gives `t` times the linearization in the
direction `u - z`.

Layer: Glue | Gap: Level 0 (affine-line inner-product subtraction)
Proof: combine `inner_sub_right` with the affine-line displacement formula
  `AffineMap.lineMap_vsub_left`, then normalize scalar multiplication in the
  right inner-product argument.
Source: Mathlib affine maps and real inner-product subtraction APIs
Used in: Bregman segment-derivative linearization rewrites for variance-reduced
  accelerated and mirror/proximal descent analyses
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem inner_lineMap_sub_right_sub_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g a z u : E) (t : ℝ) :
    ⟪g, AffineMap.lineMap z u t - a⟫_ℝ - ⟪g, z - a⟫_ℝ =
      t * ⟪g, u - z⟫_ℝ := by
  calc
    ⟪g, AffineMap.lineMap z u t - a⟫_ℝ - ⟪g, z - a⟫_ℝ =
        ⟪g, (AffineMap.lineMap z u t - a) - (z - a)⟫_ℝ := by
      rw [← inner_sub_right]
    _ = ⟪g, AffineMap.lineMap z u t - z⟫_ℝ := by
      congr 1
      abel
    _ = ⟪g, t • (u - z)⟫_ℝ := by
      simp [AffineMap.lineMap_apply_module']
    _ = t * ⟪g, u - z⟫_ℝ := by
      simp [inner_smul_right]

namespace Finset

-- Batch 4 promoted from Staging/Finset_weighted_inner_sum_eq_zero_of_weighted_sum_eq_zero.lean
-- Generalization plan (G0):
-- concept/name: finite weighted inner-product cancellation from vector
--   centering; orig was
--   `componentConditionalExpectation_inner_const_of_residual_mean_zero`,
--   renamed away from component conditional expectation and algorithm setup
--   terminology.
-- generality used: arbitrary finite index set, real weights, and a real
--   inner-product target with `[SeminormedAddCommGroup E]` and
--   `[InnerProductSpace Real E]`; no measure, independence, integrability,
--   convexity, smoothness, oracle, completeness, or finite-dimensional
--   assumptions are used.
-- portable call pattern: finite-law stochastic proofs, including
--   variance-reduced, coordinate, mini-batch, and importance-sampled
--   estimators, instantiate a residual family `R`, weights `q`, and a fixed
--   deterministic direction `u` to turn vector centering into scalar
--   inner-product cancellation.
-- counterargument checked: the proof is short and follows from `sum_inner`,
--   but it is not a pure rename of a single Mathlib theorem because it packages
--   the weighted scalar summand and zero-conclusion form used at stochastic
--   estimator call sites; it is not paper-local traceability because the
--   statement has no setup fields or algorithm vocabulary.
-- coverage search: searched CATALOG.md/SOptLib/Staging/Algorithms for
--   `weighted inner sum zero`, `sum inner weighted sum`, `residual mean zero`,
--   and `inner const`; relevant partial hits were
--   `SOptLib.finset_weighted_residual_sum_eq_zero`,
--   `SOptLib.finset_weighted_variance_eq_second_moment_sub_norm_mean_sq`,
--   `SOptLib.integral_inner_sub_mean_eq_zero_of_integral_eq`, and
--   measure-level martingale/oracle inner-product cancellation lemmas.
--   LeanSearch for "finite sum weighted inner product equals inner product of
--   weighted sum" returned Mathlib `sum_inner`, `inner_sum`, and Finsupp
--   variants, but no finite-weighted zero-conclusion theorem with this
--   statement shape.
-- minimal hypotheses: all already minimal; `[SeminormedAddCommGroup E]` and
--   `[InnerProductSpace Real E]` are exactly the typeclasses needed for finite
--   sums, scalar multiplication, and real inner products.

/-- A weighted finite sum of inner products vanishes when the weighted vector sum vanishes.

For a finite residual family `R`, real weights `q`, and a fixed direction `u`,
the scalar weighted sum of `⟪R i, u⟫_Real` is zero as soon as the weighted vector
sum of `R` is zero.

Layer: Glue | Gap: Level 0 (finite weighted inner-product cancellation)
Proof: rewrite each scalar-weighted inner product as the inner product of the
  weighted vector, commute the finite sum through the inner product with
  `sum_inner`, and use the supplied vector centering equality.
Source: Mathlib finite sums and real inner-product space algebra
Used in: finite-sum variance-reduced accelerated-gradient residual centering
  when converting vector zero mean into fixed-direction scalar cancellation
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem weighted_inner_sum_eq_zero_of_weighted_sum_eq_zero
    {ι E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace Real E]
    (s : Finset ι) (q : ι -> Real) (R : ι -> E) (u : E)
    (hR : s.sum (fun i => q i • R i) = 0) :
    s.sum (fun i => q i * ⟪R i, u⟫_Real) = 0 := by
  have hinner :
      s.sum (fun i => q i * ⟪R i, u⟫_Real) =
        ⟪s.sum (fun i => q i • R i), u⟫_Real := by
    calc
      s.sum (fun i => q i * ⟪R i, u⟫_Real)
          = s.sum (fun i => ⟪q i • R i, u⟫_Real) := by
              refine Finset.sum_congr rfl ?_
              intro i _hi
              rw [inner_smul_left]
              simp
      _ = ⟪s.sum (fun i => q i • R i), u⟫_Real := by
              simpa using
                (sum_inner (s := s) (f := fun i => q i • R i) u).symm
  simpa [hR] using hinner

end Finset

namespace SOptLib

-- Batch 4 promoted from Staging/weighted_sum_nonneg_mul_budget_add_zero_mean_le.lean
-- Generalization plan (G0):
-- concept/name: finite weighted-sum budget bound with zero-mean residual; orig was
--   `componentConditionalExpectation_nonneg_mul_budget_add_zero_mean`, renamed away
--   from component conditional expectation and variance-reduced algorithm setup
--   terminology.
-- generality used: arbitrary finite set and ordered commutative-semiring weights,
--   budget summand, residual summand, and coefficients; no measure,
--   independence, integrability, convexity, smoothness, oracle, normed-space,
--   or finite-dimensional assumptions are used.
-- portable call pattern: variance-reduced, martingale-difference, coordinate,
--   and mini-batch stochastic proofs can instantiate different finite laws,
--   residual terms, budget terms, and scalar coefficients while using the same
--   conclusion that the nonnegative scaled budget controls the mixed weighted
--   sum after zero-mean cancellation.
-- counterargument checked: the proof is finite-sum linearity plus one scalar
--   monotonicity step, but it is not a pure rename of one Mathlib lemma and is
--   not paper-local traceability; it packages the recurring stochastic-proof
--   boundary "budget term plus zero-mean residual term" after finite expectation
--   expansion.
-- coverage search: searched CATALOG.md/SOptLib/Staging/Algorithms for
--   `weighted sum`, `zero mean`, `budget`, `mul_budget`, and related finite
--   residual terms; relevant partial hits were
--   `Finset.weighted_inner_sum_eq_zero_of_weighted_sum_eq_zero`,
--   `SOptLib.finset_weighted_residual_sum_eq_zero`,
--   `SOptLib.finset_weighted_variance_eq_second_moment_sub_norm_mean_sq`, and
--   measure-level finite-PMF expectation transport lemmas. LeanSearch for the
--   precise finite weighted-sum budget and zero-mean statement returned convex
--   combination, Finsupp weight, and Jensen results, but no theorem covering
--   this scalar inequality shape.
-- minimal hypotheses: all already minimal; the proof uses only finite-sum
--   commutative-semiring algebra, ordered multiplication by a nonnegative
--   scalar, `hV`, `hU`, and nonnegativity of the left scalar multiplier `a`.

/-- A nonnegative multiple of a finite weighted budget absorbs a zero-mean residual.

If the weighted sum of `V` over `s` is zero and the weighted sum of `U` is bounded by
`C`, then the weighted sum of `a * U + b * V` is bounded by `a * C` whenever
`a` is nonnegative.

Layer: Glue | Gap: Level 0 (finite weighted budget plus zero-mean residual)
Proof: expand the weighted finite sum by distributivity, factor out the scalar
  coefficients, cancel the zero-mean residual sum, and apply monotonicity of
  multiplication by a nonnegative scalar.
Source: Mathlib finite big-operator algebra and ordered scalar arithmetic
Used in: variance-reduced accelerated-gradient residual algebra where a
  zero-mean estimator error is added to a bounded second-moment budget
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem weighted_sum_nonneg_mul_budget_add_zero_mean_le
    {ι R : Type*} [CommSemiring R] [Preorder R] [PosMulMono R]
    (s : Finset ι) (w U V : ι -> R) (a b C : R)
    (ha : 0 <= a)
    (hV : s.sum (fun i : ι => w i * V i) = 0)
    (hU : s.sum (fun i : ι => w i * U i) <= C) :
    s.sum (fun i : ι => w i * (a * U i + b * V i)) <= a * C := by
  calc
    s.sum (fun i : ι => w i * (a * U i + b * V i))
        = a * s.sum (fun i : ι => w i * U i) +
            b * s.sum (fun i : ι => w i * V i) := by
          simp [mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_left_comm]
    _ = a * s.sum (fun i : ι => w i * U i) := by
          rw [hV]
          simp
    _ <= a * C := mul_le_mul_of_nonneg_left hU ha

-- Batch 4 promoted from Staging/finset_weighted_sq_norm_sub_triangle_split.lean
-- Generalization plan (G0):
-- concept/name: finite weighted squared-norm triangle split; orig was
--   `finiteCarrierGradientGapRelationLeft_triangle_split`, renamed away from
--   carrier-gradient and variance-reduced algorithm terminology.
-- generality used: arbitrary finite summation set, arbitrary index and point
--   types, and a seminormed additive commutative group for the values; no
--   measure, convexity, smoothness, oracle, inner-product, or finite-dimensional
--   structure is used.
-- portable call pattern: variance-reduced, mini-batch, coordinate, and
--   importance-sampled stochastic-optimization proofs can split a weighted
--   second-moment gap through an anchor; the family, weights, finite index set,
--   and three points vary while the weighted triangle conclusion stays fixed.
-- counterargument checked: the pointwise Young inequality is already in
--   `SOptLib.norm_add_sq_le_two_mul_norm_sq_add_two_mul_norm_sq`, but callers
--   still repeatedly need the finite weighted-sum aggregation; this is not a
--   paper-local traceability wrapper because the statement has no algorithm
--   vocabulary or setup fields.
-- coverage search: searched `weighted sq norm triangle split`,
--   `finset weighted norm sub`, and `sum norm square` across CATALOG/SOptLib
--   and Mathlib semantic search. Hits included the pointwise
--   `SOptLib.norm_add_sq_le_two_mul_norm_sq_add_two_mul_norm_sq`,
--   finite-average Cauchy bounds, and weighted variance identities, but no
--   theorem covered this weighted anchor split.
-- minimal hypotheses: nonnegativity of weights is required only on the
--   summation set; `[SeminormedAddCommGroup E]` is enough for norm, subtraction,
--   and the pointwise norm-square triangle inequality.

/-- A finite weighted squared-norm gap splits through any anchor point.

For a nonnegative real weight on each index in a finite set, the weighted sum of
`‖A i x - A i z‖ ^ 2` is bounded by twice the corresponding sums through an
intermediate anchor `y`.

Layer: Glue | Gap: Level 1 (finite weighted norm-square triangle split)
Proof: apply the two-term norm-square Young inequality pointwise after writing
  `A i x - A i z` as a sum through `A i y`; multiply by the nonnegative weight,
  sum over the finite set, and distribute the two constant factors.
Source: Mathlib finite sums, seminormed additive groups, and ordered real
  arithmetic
Used in: variance-reduced accelerated gradient descent splitting the finite
  component-gradient second-moment gap through the snapshot anchor
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem finset_weighted_sq_norm_sub_triangle_split
    {ι X E : Type*} [SeminormedAddCommGroup E]
    (s : Finset ι) (w : ι -> Real) (A : ι -> X -> E)
    (x z y : X)
    (hw_nonneg : ∀ i ∈ s, 0 <= w i) :
    (∑ i ∈ s, w i * ‖A i x - A i z‖ ^ 2) <=
      2 * (∑ i ∈ s, w i * ‖A i x - A i y‖ ^ 2) +
        2 * (∑ i ∈ s, w i * ‖A i z - A i y‖ ^ 2) := by
  have hsum :
      (∑ i ∈ s, w i * ‖A i x - A i z‖ ^ 2) <=
        ∑ i ∈ s,
          (2 * (w i * ‖A i x - A i y‖ ^ 2) +
            2 * (w i * ‖A i z - A i y‖ ^ 2)) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    have hdiff :
        A i x - A i z = (A i x - A i y) + (A i y - A i z) := by
      abel_nf
    have hsymm :
        ‖A i y - A i z‖ ^ 2 = ‖A i z - A i y‖ ^ 2 := by
      rw [← norm_neg (A i y - A i z)]
      congr 1
      abel_nf
    have hsq :
        ‖A i x - A i z‖ ^ 2 <=
          2 * ‖A i x - A i y‖ ^ 2 + 2 * ‖A i z - A i y‖ ^ 2 := by
      calc
        ‖A i x - A i z‖ ^ 2 =
            ‖(A i x - A i y) + (A i y - A i z)‖ ^ 2 := by
          rw [hdiff]
        _ <= 2 * ‖A i x - A i y‖ ^ 2 +
            2 * ‖A i y - A i z‖ ^ 2 :=
          SOptLib.norm_add_sq_le_two_mul_norm_sq_add_two_mul_norm_sq
            (A i x - A i y) (A i y - A i z)
        _ = 2 * ‖A i x - A i y‖ ^ 2 +
            2 * ‖A i z - A i y‖ ^ 2 := by
          rw [hsymm]
    have hscaled := mul_le_mul_of_nonneg_left hsq (hw_nonneg i hi)
    nlinarith
  calc
    (∑ i ∈ s, w i * ‖A i x - A i z‖ ^ 2) <=
        ∑ i ∈ s,
          (2 * (w i * ‖A i x - A i y‖ ^ 2) +
            2 * (w i * ‖A i z - A i y‖ ^ 2)) := hsum
    _ =
      2 * (∑ i ∈ s, w i * ‖A i x - A i y‖ ^ 2) +
        2 * (∑ i ∈ s, w i * ‖A i z - A i y‖ ^ 2) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

-- Batch 4 promoted from Staging/finset_sum_mul_sq_norm_le_of_norm_le.lean
-- Generalization plan (G0):
-- concept/name: finite weighted squared-norm monotonicity under pointwise norm
--   domination; orig was `finite_weighted_sq_norm_le_of_pointwise_norm_le`,
--   renamed away from carrier-gradient and algorithm-local wording.
-- generality used: arbitrary finite summation set, real weights, and values in
--   a seminormed additive commutative group; no measure, convexity,
--   smoothness, oracle, inner-product, or finite-dimensional structure is
--   used.
-- portable call pattern: variance-reduced, mini-batch, projected-gradient, and
--   coordinate stochastic-optimization proofs compare a weighted second-moment
--   expression after replacing each summand by a norm-dominated surrogate; the
--   index set, weights, and vector families change while the finite weighted
--   squared-norm comparison stays fixed.
-- counterargument checked: this is not paper-local traceability because the
--   statement contains only a Finset, real nonnegative weights, and pointwise
--   norm domination. It is more than a pure rename of `sum_le_sum` because it
--   packages the recurring square monotonicity and nonnegative scaling needed
--   at finite second-moment call sites.
-- coverage search: searched `weighted sq norm`, `sum norm square`,
--   `finite sum nonnegative weights squared norm pointwise norm inequality`,
--   and the registry. Hits included weighted variance identities,
--   `SOptLib.norm_add_sq_le_two_mul_norm_sq_add_two_mul_norm_sq`, and the
--   staged `finset_weighted_sq_norm_sub_triangle_split`; those cover variance
--   decomposition or triangle splitting, not monotonicity under pointwise norm
--   domination. LeanSearch was unavailable due DNS failure, so no Mathlib
--   semantic hit could be confirmed.
-- minimal hypotheses: nonnegativity of each weight and pointwise norm
--   domination are required only on the summation set; `[SeminormedAddCommGroup
--   E]` is enough for norms and no finite-dimensional assumption is used.

/-- A finite weighted squared-norm sum is monotone under pointwise norm domination.

If every coefficient in a finite real-weighted sum is nonnegative and
`‖a i‖ ≤ ‖b i‖` on the summation set, then the weighted sum of `‖a i‖ ^ 2`
is bounded by the corresponding weighted sum of `‖b i‖ ^ 2`.

Layer: Glue | Gap: Level 0 (finite weighted squared-norm monotonicity)
Proof: square the pointwise norm bound using nonnegativity of norms, multiply
  by the nonnegative coefficient, and sum the resulting pointwise inequalities.
Source: Mathlib finite sums over `Finset`, seminormed additive groups, and
  ordered real arithmetic
Used in: variance-reduced accelerated gradient descent comparison of projected
  carrier-gradient second moments with raw within-gradient second moments
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem finset_sum_mul_sq_norm_le_of_norm_le
    {ι E : Type*} [SeminormedAddCommGroup E]
    (s : Finset ι) (c : ι -> ℝ) (a b : ι -> E)
    (hc_nonneg : ∀ i ∈ s, 0 <= c i)
    (h_norm_le : ∀ i ∈ s, ‖a i‖ <= ‖b i‖) :
    (∑ i ∈ s, c i * ‖a i‖ ^ 2) <=
      ∑ i ∈ s, c i * ‖b i‖ ^ 2 := by
  refine Finset.sum_le_sum ?_
  intro i hi
  have hsq : ‖a i‖ ^ 2 <= ‖b i‖ ^ 2 := by
    nlinarith [h_norm_le i hi, norm_nonneg (a i), norm_nonneg (b i)]
  exact mul_le_mul_of_nonneg_left hsq (hc_nonneg i hi)

-- Batch 4 promoted from .sgd_phase3_staging/SOptLib/Glue/gap_le_pow_rate_of_four_mul_budget.lean
-- Generalization plan (G0):
-- concept/name: gap_le_pow_rate_of_four_mul_budget exposes scalar
--   denominator-clearing from a four-times-budget epoch coefficient to a
--   power-of-two rate; orig was first_phase_expected_gap_rate_of_fourT_budget.
-- generality used: real scalars only; no carrier type, measure, independence,
--   integrability, convexity, smoothness, oracle, filtration, or
--   finite-dimensional hypotheses are used.
-- portable call pattern: first-phase accelerated finite-sum, restarted
--   accelerated, and variance-reduced convergence proofs can call this after
--   proving `(4*T/(3*L))*Gap <= D0/(3*L)` and identifying `4*T` with the
--   epoch power `2^(s+1)`; `Gap`, `D0`, `L`, `T`, and `s` change.
-- counterargument checked: this is short scalar algebra, but not merely
--   paper-local traceability: the same rate handoff occurs in multiple
--   accelerated first-phase proofs once a Lyapunov budget is normalized by an
--   epoch length. It is not covered by existing coefficient/remainder lemmas,
--   which do not include the denominator-clearing and power-of-two rewrite.
-- coverage search: searched catalog, SOptLib, Staging, and LeanSearch for
--   `gap`, `pow rate`, `four mul budget`, denominator clearing, and division
--   lemmas. Relevant hits were `gap_le_div_of_coeff_le_and_nonneg_remainder`
--   and Mathlib `le_div_iff₀`/`div_le_of_le_mul₀`; these are proof ingredients
--   or different coefficient-normalization shapes, not this packaged rate.
-- minimal hypotheses: `0 < L`, the scaled budget inequality, and the exact
--   positive power identity `4*T = 2^(s+1)`; positivity of `T` follows from
--   that identity.

/-- A four-times epoch budget gives a power-of-two gap rate.

If the scaled budget `(4*T/(3*L))*Gap` is at most `D0/(3*L)` and the epoch
scale satisfies `4*T = 2^(s+1)`, then `Gap <= D0/2^(s+1)`.

Layer: Glue | Gap: Level 0 (power-of-two scalar rate clearing)
Proof: multiply the scaled inequality by the positive denominator `3*L`, divide
  by the positive scale `4*T`, and rewrite that scale by the power identity.
Source: Mathlib ordered-field division, positive-denominator inequalities, and
  natural powers of real scalars
Used in: variance-reduced accelerated gradient first-phase expected-gap rate
  extraction from an epoch Lyapunov budget
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/key_lemmas/16/proof
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem gap_le_pow_rate_of_four_mul_budget
    (L D0 Gap T : ℝ) (s : ℕ)
    (hL_pos : 0 < L)
    (hscaled : (4 * T / (3 * L)) * Gap <= D0 / (3 * L))
    (hpow : 4 * T = (2 : ℝ) ^ (s + 1)) :
    Gap <= D0 / (2 : ℝ) ^ (s + 1) := by
  have hthreeL_pos : 0 < 3 * L := by positivity
  have hclear : (4 * T) * Gap <= D0 := by
    have hmul := mul_le_mul_of_nonneg_right hscaled (le_of_lt hthreeL_pos)
    have hleft : ((4 * T / (3 * L)) * Gap) * (3 * L) = (4 * T) * Gap := by
      field_simp [ne_of_gt hthreeL_pos]
    have hright : (D0 / (3 * L)) * (3 * L) = D0 := by
      field_simp [ne_of_gt hthreeL_pos]
    simpa [hleft, hright] using hmul
  have hden_pos : 0 < 4 * T := by
    rw [hpow]
    positivity
  have hdiv : Gap <= D0 / (4 * T) := by
    have hclear_comm : Gap * (4 * T) <= D0 := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hclear
    exact (le_div_iff₀ hden_pos).2 hclear_comm
  calc
    Gap <= D0 / (4 * T) := hdiv
    _ = D0 / (2 : ℝ) ^ (s + 1) := by rw [hpow]

-- Batch 4 promoted from Staging/le_half_of_budget_eq_two_mul_add_nonneg.lean
-- Generalization plan (G0):
-- concept/name: le_half_of_budget_eq_two_mul_add_nonneg exposes the scalar
--   half-budget consequence of writing a budget as twice a quantity plus a
--   nonnegative residual; orig was
--   gap_le_half_budget_of_budget_eq_two_gap_add_nonneg.
-- generality used: arbitrary partially ordered strict ordered semifield scalars; no carrier type,
--   measure, convexity, smoothness, oracle, filtration, or finite-dimensional
--   hypotheses are used.
-- portable call pattern: initial-epoch stochastic optimization proofs for
--   accelerated, proximal, and mirror-descent methods can vary the objective
--   gap, residual term, and budget formula while preserving the same scalar
--   conclusion that the leading term is at most half the budget.
-- counterargument checked: this is not paper-local traceability because the
--   argument is exactly the reusable scalar step that drops a nonnegative
--   residual from an initial potential budget. It overlaps with the staged
--   `gap_le_div_of_coeff_le_and_nonneg_remainder`, but strengthens the exact
--   equality case by removing the unnecessary nonnegativity hypothesis on the
--   leading quantity.
-- coverage search: searched catalog, SOptLib, Staging, and Mathlib LeanSearch
--   for half budget, two times gap plus residual, nonnegative remainder, and
--   gap/div coefficient normalization. Mathlib hits such as
--   `half_le_self_iff` are proof ingredients, and the SOptLib/Staging hit
--   `gap_le_div_of_coeff_le_and_nonneg_remainder` is partial rather than full
--   coverage because it assumes `0 <= gap`.
-- minimal hypotheses: all already minimal; the equality and residual
--   nonnegativity are sufficient, and no nonnegativity of the leading quantity
--   or budget is needed.

/-- If a budget is twice a quantity plus a nonnegative residual, the quantity
is at most half the budget.

Layer: Glue | Gap: Level 1 (half-budget extraction from nonnegative residual)
Proof: rewrite the budget identity, divide the nonnegative residual by two,
  and use ordered-semifield arithmetic to identify the resulting half-budget.
Source: Mathlib ordered-semifield arithmetic and nonnegative division APIs
Used in: variance-reduced accelerated gradient initial-epoch gap extraction
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem le_half_of_budget_eq_two_mul_add_nonneg
    {R : Type*} [Semifield R] [PartialOrder R] [PosMulReflectLT R] [IsStrictOrderedRing R]
    (gap residual budget : R)
    (hbudget : budget = 2 * gap + residual)
    (hresidual_nonneg : 0 <= residual) :
    gap <= budget / 2 := by
  subst budget
  have htwo_nonneg : (0 : R) <= 2 := by norm_num
  have hresidual_half_nonneg : 0 <= residual / 2 :=
    div_nonneg hresidual_nonneg htwo_nonneg
  calc
    gap <= gap + residual / 2 := le_add_of_nonneg_right hresidual_half_nonneg
    _ = (2 * gap + residual) / 2 := by ring

-- Batch 4 promoted from Staging/geometric_tail_mass_lower_bound_of_coeff_le.lean
-- Generalization plan (G0):
-- concept/name: geometric tail mass lower bound from an expansion coefficient;
--   orig was `geometric_tail_theta_mass_lower_bound_of_coeff`, renamed away
--   from theta-schedule internals while keeping the mathematical tail-mass and
--   coefficient-comparison content.
-- generality used: an ordered commutative semiring and scalar parameters
--   `gammaT`, `c0`, `p`, `sumGamma`, `thetaMass`, and `coeff`; no measure,
--   independence, integrability, topology, norm, inner product, convexity,
--   smoothness, oracle, filtration, or finite-dimensional hypotheses are used.
-- portable call pattern: accelerated tail-schedule proofs supply a closed-form
--   mass expansion, nonnegativity of the retained gamma mass, and a lower bound
--   comparing the desired `p * gammaT` coefficient with the expansion
--   coefficient; the same conclusion converts the expansion into the lower
--   bound needed for a contraction or retained-potential estimate.
-- counterargument checked: the proof is short, but it is not merely a caller
--   expression because it packages the recurring expansion-plus-coefficient
--   replacement step used after geometric theta-mass identities; it is not
--   paper-local after removing theorem numbers, setup fields, and schedule
--   definitions.
-- coverage search: searched CATALOG.md/SOptLib/Staging/Algorithms for
--   `geometric_tail`, `tail mass`, `coefficient lower bound`, `thetaMass`,
--   `coeff * sum`, and `mul_le_mul_of_nonneg_right`; closest hits were the
--   terminal-adjusted theta expansion and the half-power tail coefficient
--   lower bound, neither combines an arbitrary mass expansion with coefficient
--   replacement. LeanSearch returned monotone multiplication lemmas such as
--   `mul_le_mul_of_nonneg_right`, but no packaged expansion bridge.
-- minimal hypotheses: all algorithm assumptions reduce to the pointwise mass
--   expansion, the coefficient comparison `p * gammaT <= coeff`, and
--   nonnegativity of `sumGamma`.

/-- A mass expansion with a larger retained coefficient gives a geometric tail
mass lower bound.

If a tail mass expands as `gammaT * c0 + coeff * sumGamma`, the retained gamma
mass is nonnegative, and `p * gammaT <= coeff`, then replacing the expansion
coefficient by `p * gammaT` gives the lower bound
`gammaT * (c0 + p * sumGamma) <= thetaMass`.

Layer: Glue | Gap: Level 1 (geometric tail-mass coefficient replacement)
Proof: distribute the desired product, multiply the coefficient comparison by
  the nonnegative gamma mass, add the common base term, and rewrite with the
  supplied mass expansion.
Source: Mathlib ordered commutative semirings and monotone multiplication APIs
Used in: variance-reduced accelerated-gradient linear-tail theta-mass lower
  bound after the geometric coefficient comparison
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/key_lemmas/18/proof/9
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem geometric_tail_mass_lower_bound_of_coeff_le
    {K : Type*} [CommSemiring K] [PartialOrder K] [IsOrderedRing K]
    (gammaT c0 p sumGamma thetaMass coeff : K)
    (hmass_eq : thetaMass = gammaT * c0 + coeff * sumGamma)
    (hcoeff_le : p * gammaT <= coeff)
    (hsumGamma_nonneg : 0 <= sumGamma) :
    gammaT * (c0 + p * sumGamma) <= thetaMass := by
  calc
    gammaT * (c0 + p * sumGamma) =
        gammaT * c0 + (p * gammaT) * sumGamma := by
          ring
    _ <= gammaT * c0 + coeff * sumGamma := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_left
              (mul_le_mul_of_nonneg_right hcoeff_le hsumGamma_nonneg)
              (gammaT * c0)
    _ = thetaMass := hmass_eq.symm

-- Batch 4 promoted from Staging/sub_mul_le_absorb_add_mul_of_le.lean
-- Generalization plan (G0):
-- concept/name: sub_mul_le_absorb_add_mul_of_le exposes scalar absorption of a lower
--   model term into the same snapshot value after the leftover coefficient is nonnegative;
--   orig was lemma516_noise_bracket_le_snapshot.
-- generality used: an abstract ordered ring hierarchy is enough; no measure,
--   convexity, smoothness, oracle, topology, or finite-dimensional assumptions are used.
-- portable call pattern: descent and estimate-substitution proofs replace a linear
--   model value by a snapshot/objective value while the coefficient names and scalar
--   quantities vary but the mixed-bracket conclusion is unchanged.
-- counterargument checked: the theorem is short, but it is not merely paper
--   traceability; it packages the recurring two-step caller pattern of nonnegative
--   multiplication followed by coefficient absorption.
-- coverage search: searched SOptLib catalog/source for sub_mul, absorb_add_mul,
--   noise_bracket, and mul_le_mul_of_nonneg_left; close hits are Young/telescope
--   absorption lemmas with different conclusions. LeanSearch returned only primitive
--   multiplication-monotonicity lemmas such as IsOrderedRing.toPosMulMono and
--   Mathlib.Tactic.LinearCombination.mul_const_le, not this normalized bracket.
-- minimal hypotheses: all already minimal apart from generalizing Real to Mathlib's
--   explicit ordered-ring typeclasses.

/-- A nonnegative leftover coefficient absorbs a lower scalar into a snapshot scalar.

If `lin <= fval`, then a mixed bracket with coefficient `p - lambda` on `lin`
and coefficient `lambda` on `fval` is bounded by the normalized bracket
`p * fval`, provided the leftover coefficient is nonnegative.

Layer: Glue | Gap: Level 0 (scalar mixed-bracket absorption)
Proof: multiply the pointwise bound by the nonnegative leftover coefficient,
  add the shared snapshot term, and normalize the two coefficients by
  `← add_mul` and `sub_add_cancel`.
Source: Mathlib ordered-ring multiplication monotonicity and ring normalization APIs
Used in: variance-reduced accelerated descent proof after substituting an oracle-noise
  estimate into a linearized objective bracket
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine
  Learning, variance-reduced accelerated gradient descent -/
theorem sub_mul_le_absorb_add_mul_of_le {R : Type*}
    [Ring R] [PartialOrder R] [IsOrderedRing R]
    (p lambda lin fval : R)
    (hcoef : 0 <= p - lambda) (hlin : lin <= fval) :
    (p - lambda) * lin + lambda * fval <= p * fval := by
  have hscaled : (p - lambda) * lin <= (p - lambda) * fval :=
    mul_le_mul_of_nonneg_left hlin hcoef
  calc
    (p - lambda) * lin + lambda * fval
        <= (p - lambda) * fval + lambda * fval := by
          exact add_le_add_left hscaled (lambda * fval)
    _ = p * fval := by
          rw [← add_mul, sub_add_cancel]

-- Batch 4 promoted from Staging/finset_weighted_expectation_rescale_predivided_recurrence.lean
-- Generalization plan (G0):
-- concept/name: finite weighted expectation rescaling of a pre-divided
--   recurrence; orig was `lemma516_rescale_pre_expectation`.
-- generality used: arbitrary finite support, ordered-field normalized
--   weights, and scalar observables only; no measure, filtration, convexity,
--   smoothness, oracle, Hilbert-space, or finite-dimensional hypotheses are
--   used once the finite recurrence is available.
-- portable call pattern: accelerated stochastic-gradient, proximal, and
--   variance-reduced Lyapunov proofs can call this after deriving a finite
--   conditional-expectation recurrence in the pre-divided form
--   `A + alpha / gamma * B`; weights, observables, objective endpoints, and
--   schedule scalars change while the rescaled conclusion stays the same.
-- counterargument checked: not paper-local traceability because the statement
--   removes all algorithm objects and packages the reusable positive-ratio
--   rescaling plus constant-expectation normalization; not a named inner
--   formula because the proof has no recognized mathematical object beyond
--   finite weighted expectation algebra.
-- coverage search: searched SOptLib, Staging, the round registry, and Mathlib
--   LeanSearch for weighted expectation, finite sum rescale, predivided
--   recurrence, gamma/alpha normalization, and weighted-potential endpoint
--   rescaling; hits included finite expectation primitives, variance bounds,
--   selected-output expectation wrappers, and weighted-potential endpoint
--   coefficient lemmas, but no declaration with this pre-divided recurrence
--   shape and normalized constant subtraction.
-- minimal hypotheses: `0 < alpha`, `0 < gamma`, normalized weights
--   `sum w = 1`, and the pre-divided recurrence are exactly the facts used.

/-- Rescale a normalized finite weighted recurrence from pre-divided form.

If a normalized finite weighted sum bounds `A + alpha / gamma * B`,
then positive `alpha` and `gamma` allow multiplication by `gamma / alpha` and
subtraction of the target constant to produce the recurrence for
`gamma / alpha * (A - target) + B`.

Layer: Glue | Gap: Level 1 (finite weighted pre-divided recurrence rescaling)
Proof: multiply the pre-divided inequality by the positive ratio
  `gamma / alpha`, use finite-sum linearity and `sum w = 1` to move the target
  constant through the weighted expectation, then simplify by field arithmetic.
Source: Mathlib finite big-operator algebra and ordered-field inequalities
Used in: variance-reduced accelerated gradient descent conditional Lyapunov
  recurrence rescaling from pre-divided expectation form
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/key_lemmas/14/proof/5
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem finset_weighted_expectation_rescale_predivided_recurrence
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {ι : Type*} (s : Finset ι)
    (w A B : ι → R)
    (gamma alpha p basePrev baseTarget baseSnapshot tailPrev : R)
    (halpha_pos : 0 < alpha) (hgamma_pos : 0 < gamma)
    (hw_sum : Finset.sum s w = 1)
    (hpre :
      Finset.sum s (fun i =>
          w i * (A i + (alpha / gamma) * B i)) ≤
        (1 - alpha - p) * basePrev +
          alpha * baseTarget +
          p * baseSnapshot +
          (alpha / gamma) * tailPrev) :
    Finset.sum s (fun i =>
        w i * (gamma / alpha * (A i - baseTarget) + B i)) ≤
      gamma / alpha * (1 - alpha - p) * (basePrev - baseTarget) +
        gamma / alpha * p * (baseSnapshot - baseTarget) + tailPrev := by
  classical
  let k : R := gamma / alpha
  have hk_pos : 0 < k := by
    dsimp [k]
    exact div_pos hgamma_pos halpha_pos
  have hleft :
      Finset.sum s (fun i =>
          w i * (gamma / alpha * (A i - baseTarget) + B i)) =
        k *
            Finset.sum s (fun i =>
              w i * (A i + (alpha / gamma) * B i)) -
          k * baseTarget := by
    calc
      Finset.sum s (fun i =>
          w i * (gamma / alpha * (A i - baseTarget) + B i)) =
        Finset.sum s (fun i =>
          k * (w i * (A i + (alpha / gamma) * B i)) -
            (k * baseTarget) * w i) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          dsimp [k]
          field_simp [ne_of_gt halpha_pos, ne_of_gt hgamma_pos]
          ring
      _ =
          Finset.sum s (fun i =>
            k * (w i * (A i + (alpha / gamma) * B i))) -
          Finset.sum s (fun i => (k * baseTarget) * w i) := by
          rw [Finset.sum_sub_distrib]
      _ =
        k *
            Finset.sum s (fun i =>
              w i * (A i + (alpha / gamma) * B i)) -
          (k * baseTarget) * Finset.sum s w := by
          rw [Finset.mul_sum, Finset.mul_sum]
      _ =
        k *
            Finset.sum s (fun i =>
              w i * (A i + (alpha / gamma) * B i)) -
          k * baseTarget := by
          rw [hw_sum]
          ring
  have hscaled :
      k *
          Finset.sum s (fun i =>
            w i * (A i + (alpha / gamma) * B i)) ≤
        k *
          ((1 - alpha - p) * basePrev +
            alpha * baseTarget +
            p * baseSnapshot +
            (alpha / gamma) * tailPrev) :=
    mul_le_mul_of_nonneg_left hpre (le_of_lt hk_pos)
  calc
    Finset.sum s (fun i =>
        w i * (gamma / alpha * (A i - baseTarget) + B i)) =
        k *
            Finset.sum s (fun i =>
              w i * (A i + (alpha / gamma) * B i)) -
          k * baseTarget := hleft
    _ ≤
        k *
          ((1 - alpha - p) * basePrev +
            alpha * baseTarget +
            p * baseSnapshot +
            (alpha / gamma) * tailPrev) -
          k * baseTarget :=
        sub_le_sub_right hscaled (k * baseTarget)
    _ =
      gamma / alpha * (1 - alpha - p) * (basePrev - baseTarget) +
        gamma / alpha * p * (baseSnapshot - baseTarget) + tailPrev := by
        dsimp [k]
        field_simp [ne_of_gt halpha_pos, ne_of_gt hgamma_pos]
        ring

-- Batch 4 promoted from Staging/first_phase_doubling_epoch_chain_le_initial.lean
-- Generalization plan (G0):
-- concept/name: first-phase doubling epoch chain inequality; orig was `lemma518_scalar_first_phase_epoch_chain`, renamed away from theorem numbering and paper lemma labels
-- generality used: a generic linear ordered field for scalar gap and potential values, an abstract natural epoch-length schedule, and pointwise one-step recurrence/doubling hypotheses; no measure, convexity, smoothness, oracle, filtration, topology, norm, inner product, or finite-dimensional structure is used
-- portable call pattern: accelerated finite-sum and variance-reduced first-phase proofs chain epoch Lyapunov recurrences backward to the initial gap; the schedule `T`, scalar sequences `G` and `B`, terminal epoch `s`, and proof of the one-step recurrence change while the final initial-bound shape stays the same
-- counterargument checked: not paper-local traceability because the statement is paper-name-free scalar recurrence composition; not a caller-side expression because it hides the induction, predecessor restriction, and coefficient rewrite forced by `T r = 2 * T (r - 1)`; Mathlib geometric-recursion lemmas do not cover the additive two-sequence Lyapunov form
-- coverage search: searched project/SOptLib/Staging/catalog tokens `doubling`, `epoch_chain`, `first_phase`, `T (r - 1)`, and `2 * T`; relevant hits were the concrete `doublingThenFrozenEpochLength` schedule and cutoff bounds, but none chained arbitrary gap/potential recurrences; LeanSearch returned generic geometric sequence lemmas such as `le_geom`, which do not cover the additive `G`/`B` recurrence with schedule-dependent coefficients
-- minimal hypotheses: all already minimal for this statement; the original `Real` carrier was generalized to a linear ordered field and all optimization-specific setup fields were replaced by pointwise scalar hypotheses

/-- Chain first-phase Lyapunov epoch inequalities along a doubling epoch schedule.

If the first epoch has length one, later first-phase epochs double the previous
length, and each epoch bounds its current weighted gap plus potential by the
previous weighted gap plus potential, then the terminal epoch is bounded by the
initial gap and potential with the first-epoch coefficient.

Layer: Glue | Gap: Level 1 (doubling-schedule Lyapunov recurrence chain)
Proof: induction on the terminal epoch. The successor step restricts the
  recurrence hypotheses to the previous epoch and rewrites the predecessor
  coefficient using the doubling identity.
Source: Mathlib natural-number induction, natural casts, and ordered-field
  algebra APIs
Used in: variance-reduced accelerated gradient first-phase Lyapunov recursion
  chaining
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem first_phase_doubling_epoch_chain_le_initial
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (L : K)
    (T : Nat -> Nat) (G B : Nat -> K)
    (s : Nat)
    (hT1 : T 1 = 1)
    (hdouble : forall r, 2 <= r -> r <= s -> T r = 2 * T (r - 1))
    (hstep :
      forall r, 1 <= r -> r <= s ->
        (4 * ((T r : Nat) : K) / (3 * L)) * G r + B r <=
          (2 * ((T r : Nat) : K) / (3 * L)) * G (r - 1) + B (r - 1)) :
    1 <= s ->
      (4 * ((T s : Nat) : K) / (3 * L)) * G s + B s <=
        (2 / (3 * L)) * G 0 + B 0 := by
  intro hs
  revert hdouble hstep
  induction s with
  | zero =>
      intro _hdouble _hstep
      omega
  | succ r ih =>
      intro hdouble hstep
      by_cases hbase : r = 0
      · subst r
        have hcur := hstep 1 (by norm_num) (by norm_num)
        have hcoef :
            (2 * ((T 1 : Nat) : K) / (3 * L)) * G (1 - 1) + B (1 - 1) =
              (2 / (3 * L)) * G 0 + B 0 := by
          rw [hT1]
          norm_num
        exact hcur.trans (le_of_eq hcoef)
      · have hr_pos : 1 <= r := Nat.succ_le_iff.mp (Nat.pos_of_ne_zero hbase)
        have hcur := hstep (r + 1) (by omega) (by omega)
        have hdouble_prev :
            forall q, 2 <= q -> q <= r -> T q = 2 * T (q - 1) := by
          intro q hq2 hqr
          exact hdouble q hq2 (Nat.le_trans hqr (Nat.le_succ r))
        have hstep_prev :
            forall q, 1 <= q -> q <= r ->
              (4 * ((T q : Nat) : K) / (3 * L)) * G q + B q <=
                (2 * ((T q : Nat) : K) / (3 * L)) * G (q - 1) + B (q - 1) := by
          intro q hq1 hqr
          exact hstep q hq1 (Nat.le_trans hqr (Nat.le_succ r))
        have hprev := ih hr_pos hdouble_prev hstep_prev
        have hd : T (r + 1) = 2 * T r := by
          have hr2 : 2 <= r + 1 := by omega
          have hraw := hdouble (r + 1) hr2 (by omega)
          simpa [Nat.add_sub_cancel] using hraw
        have hdK :
            ((T (r + 1) : Nat) : K) = 2 * ((T r : Nat) : K) := by
          rw [hd]
          norm_num [Nat.cast_mul]
        have hcoef :
            (2 * ((T (r + 1) : Nat) : K) / (3 * L)) * G ((r + 1) - 1) +
                B ((r + 1) - 1) =
              (4 * ((T r : Nat) : K) / (3 * L)) * G r + B r := by
          rw [hdK, Nat.add_sub_cancel]
          ring_nf
        exact hcur.trans ((le_of_eq hcoef).trans hprev)

-- Batch 4 promoted from Staging/sum_range_succ_add_weighted_tail_le_mul_add_initial_of_step.lean
-- Generalization plan (G0):
-- concept/name: zero-based scalar recurrence telescope with retained weighted
--   tail; orig was lemma518_scalar_one_epoch_telescope.
-- generality used: ordered commutative-ring scalars and natural-indexed
--   sequences only; no measure, independence, integrability, convexity,
--   smoothness, oracle, carrier, or finite-dimensional hypotheses are used.
-- portable call pattern: variance-reduced, accelerated, mirror-descent, and
--   proximal epoch proofs can instantiate `A` as the one-step gap term, `B` as
--   the potential, `C` as an epoch budget, and `betaTail` as a retained tail
--   coefficient while preserving the same telescoped bound.
-- counterargument checked: not paper-local traceability because all
--   algorithm fields and theorem numbers are removed; not a pure wrapper
--   because the statement packages summing the step recurrence, exposing the
--   endpoint potential, and retaining a weighted shifted potential sum.
-- coverage search: searched catalog/source for range telescope, weighted
--   tail, recurrence, zero-based, sum_Icc_two_coeff, and finite_window; SOptLib
--   hits sum_range_sub_succ_le_first_of_last_nonneg,
--   finite_window_weighted_recurrence_telescope_with_tail_sums, and
--   sum_Icc_two_coeff_telescope_le are partial but have different window,
--   coefficient, or terminal-tail shapes. LeanSearch returned Mathlib
--   Finset.sum_range_sub' and adjacent finite-difference identities, not this
--   recurrence inequality with retained shifted-tail sum.
-- minimal hypotheses: all already minimal for the algebraic proof: one
--   pointwise recurrence over `k < T`; no nonnegativity of `betaTail` or `B`
--   is needed because the weighted tail is retained rather than dropped.

/-- A zero-based scalar recurrence telescopes with a retained weighted tail.

If each step bounds `A (k + 1) + (1 + betaTail) * B (k + 1)` by a constant
budget plus the previous potential `B k`, then summing over `range T` retains
the endpoint `B T` and the weighted shifted tail `betaTail * sum B (k + 1)`.

Layer: Glue | Gap: Level 1 (zero-based scalar recurrence telescope with tail)
Proof: induct on the range length, split both finite sums at the top index, use
  the top recurrence to bound the newly exposed summand, and close by ordered
  ring arithmetic.
Source: Mathlib finite sums over natural ranges and ordered-ring arithmetic
Used in: variance-reduced accelerated gradient descent one-epoch potential
  telescope after the printed one-step recurrence is summed
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/key_lemmas/13/proof
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem sum_range_succ_add_weighted_tail_le_mul_add_initial_of_step
    {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (T : Nat) (A B : Nat -> R) (C betaTail : R)
    (hstep :
      forall k, k < T ->
        A (k + 1) + (1 + betaTail) * B (k + 1) <= C + B k) :
    (Finset.range T).sum (fun k => A (k + 1)) + B T +
        betaTail * (Finset.range T).sum (fun k => B (k + 1)) <=
      (T : R) * C + B 0 := by
  induction T with
  | zero =>
      simp
  | succ T ih =>
      have hstep_prev :
          forall k, k < T ->
            A (k + 1) + (1 + betaTail) * B (k + 1) <= C + B k := by
        intro k hk
        exact hstep k (Nat.lt_trans hk (Nat.lt_succ_self T))
      have hih := ih hstep_prev
      have htop := hstep T (Nat.lt_succ_self T)
      have htop' :
          A (T + 1) + (1 + betaTail) * B (T + 1) - B T <= C := by
        linarith
      calc
        (Finset.range (T + 1)).sum (fun k => A (k + 1)) + B (T + 1) +
            betaTail * (Finset.range (T + 1)).sum (fun k => B (k + 1))
            = ((Finset.range T).sum (fun k => A (k + 1)) + B T +
                betaTail * (Finset.range T).sum (fun k => B (k + 1))) +
                (A (T + 1) + (1 + betaTail) * B (T + 1) - B T) := by
              rw [Finset.sum_range_succ, Finset.sum_range_succ]
              ring
        _ <= (T : R) * C + B 0 + C := by
              exact add_le_add hih htop'
        _ = ((T + 1 : Nat) : R) * C + B 0 := by
              norm_num [Nat.cast_add, Nat.cast_one]
              ring

-- Batch 4 promoted from Staging/five_fourths_le_one_add_two_mu_div_three_L_pow_of_half_le_epoch_length.lean
-- Generalization plan (G0):
-- concept/name: geometric-power lower bound from half-length and large-condition assumptions; orig was `lemma519_geometric_gamma_epoch_lower_bound`
-- generality used: Glue-layer ordered-field scalar parameters `m`, `L`, `mu` and a natural epoch length `T`; no carrier type, measure, convexity, smoothness, oracle, filtration, or finite-dimensional assumptions
-- portable call pattern: strongly-convex finite-sum epoch proofs lower-bound a geometric normalization factor after showing `T >= m/2` and a large-regime condition `3*L/(4*mu) <= m`; component counts, smoothness constants, and curvature constants change while the conclusion shape stays fixed
-- counterargument checked: not paper-local traceability because the theorem isolates a reusable scalar normalization step; not a pure wrapper because it composes denominator clearing, half-length transfer, and Bernoulli's inequality; not already covered by Mathlib/SOptLib as a single callable lemma
-- coverage search: searched project/SOptLib/Staging tokens `five_fourths`, `5 / 4`, `geometric gamma lower`, `one_add pow half epoch`, and LeanSearch queries for Bernoulli and the `3*L/(4*mu)` scalar implication; Mathlib hit `one_add_mul_le_pow`, while existing staging hits `geometricEpochGamma` and `half_le_two_pow_floor_log_div_log_two` cover only ingredients, not this combined lower bound
-- minimal hypotheses: all already minimal for this proof shape: `0 < L` and `0 < mu` clear denominators and make the increment nonnegative; `m / 2 <= T` and `3 * L / (4 * mu) <= m` are the two scalar bounds consumed directly

/-- A half-length epoch and a large-regime condition force a `5/4` geometric lower bound.

If `T` is at least half of a scale `m`, and `m` is at least `3*L/(4*mu)`,
then the geometric factor with increment `mu * (2/(3*L))` is at least `5/4`.

Layer: Glue | Gap: Level 0 (geometric lower bound from half epoch length)
Proof: clear the large-regime denominator to get a quarter-unit linear budget,
  transfer it through the half-length bound, then apply Mathlib's Bernoulli
  inequality `one_add_mul_le_pow`.
Source: Mathlib ordered-field arithmetic and natural-power Bernoulli inequality
Used in: variance-reduced accelerated-gradient large-regime epoch contraction
  normalization
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/key_lemmas/14/proof/4
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem five_fourths_le_one_add_two_mu_div_three_scale_pow_of_half_le_exponent
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (m L mu : K) (T : Nat)
    (hL : 0 < L) (hmu : 0 < mu)
    (hT_half : m / 2 <= (T : K))
    (hlarge : 3 * L / (4 * mu) <= m) :
    (5 / 4 : K) <= (1 + mu * (2 / (3 * L))) ^ T := by
  have hincr_nonneg : 0 <= mu * (2 / (3 * L)) := by
    positivity
  have hlinear_at_m :
      (1 / 4 : K) <= (m / 2) * (mu * (2 / (3 * L))) := by
    have hlarge_mul :
        (3 * L / (4 * mu)) * (4 * mu) <= m * (4 * mu) := by
      exact mul_le_mul_of_nonneg_right hlarge (by positivity)
    have hlarge_cleared : 3 * L <= m * (4 * mu) := by
      have hden_pos : 0 < 4 * mu := by positivity
      field_simp [ne_of_gt hden_pos] at hlarge_mul
      nlinarith
    have hcoef_eq :
        (m / 2) * (mu * (2 / (3 * L))) = m * mu / (3 * L) := by
      field_simp [ne_of_gt hL]
    rw [hcoef_eq]
    rw [le_div_iff₀ (by positivity : 0 < 3 * L)]
    nlinarith
  have hlinear :
      (1 / 4 : K) <= (T : K) * (mu * (2 / (3 * L))) := by
    have hmul :=
      mul_le_mul_of_nonneg_right hT_half hincr_nonneg
    exact hlinear_at_m.trans hmul
  have hfive :
      (5 / 4 : K) <= 1 + (T : K) * (mu * (2 / (3 * L))) := by
    nlinarith
  have hbern :
      1 + (T : K) * (mu * (2 / (3 * L))) <=
        (1 + mu * (2 / (3 * L))) ^ T := by
    exact one_add_mul_le_pow (by nlinarith : -2 <= mu * (2 / (3 * L))) T
  exact hfive.trans hbern

-- Batch 4 promoted from Staging/le_pow_mul_of_backward_contraction_on_Ioc.lean
-- Generalization plan (G0):
-- concept/name: closed-form geometric bound from a backward one-step
--   contraction on a natural half-open interval; orig was
--   lemma519_scalar_epoch_contraction_chain.
-- generality used: ordered commutative-ring scalars and natural-indexed
--   sequences only; no measure, independence, integrability, convexity,
--   smoothness, oracle, carrier, or finite-dimensional hypotheses are used.
-- portable call pattern: epoch-level convergence proofs for accelerated,
--   mirror-descent, proximal, and variance-reduced methods can instantiate
--   `P` as a Lyapunov or gap sequence and `q` as the one-step contraction
--   factor after proving `P r <= q * P (r - 1)` over `c < r <= s`.
-- counterargument checked: not paper-local traceability because the statement
--   removes all theorem numbers, Lan-specific constants, schedules, and setup
--   fields; not a pure wrapper because it packages the induction that turns a
--   local backward recurrence into the endpoint power bound.
-- coverage search: searched SOptLib catalog/source and Mathlib sources for
--   contraction, recurrence, le_pow, pow_mul, backward, and Ioc. Relevant
--   SOptLib hits finite_window_weighted_recurrence_telescope_with_tail_sums
--   and sum_le_div_one_sub_of_lagged_aux_recurrence telescope finite-window or
--   lagged sums, while Mathlib hits were primitive power/order lemmas and
--   asymptotic facts, not this interval-indexed recurrence-to-power theorem.
-- minimal hypotheses: a pointwise one-step bound on `c < r <= s`, `0 <= q`,
--   and monotonicity of multiplication by a nonnegative left factor.

/-- A backward one-step contraction on `c < r <= s` gives a closed-form power bound.

If every step in the natural interval from `c + 1` through `s` satisfies
`P r <= q * P (r - 1)` and `q` is nonnegative, then the endpoint is bounded by
`q ^ (s - c)` times the base value.

Layer: Glue | Gap: Level 0 (geometric contraction chain over natural intervals)
Proof: induction on the right endpoint of the interval. The successor case
  applies the top one-step contraction, invokes the induction hypothesis on the
  restricted interval, and multiplies by the nonnegative contraction factor.
Source: Mathlib natural-number induction, powers, and ordered-ring
  multiplication monotonicity
Used in: variance-reduced accelerated gradient epoch Lyapunov contraction after
  each epoch has been shown to contract by a fixed scalar factor
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/key_lemmas/14/proof
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem le_pow_mul_of_backward_contraction_on_Ioc
    {R : Type*} [Monoid R] [Zero R] [Preorder R] [PosMulMono R]
    (P : Nat -> R) (q : R) (c s : Nat) (hcs : c <= s) (hq_nonneg : 0 <= q)
    (hstep : forall r, c < r -> r <= s -> P r <= q * P (r - 1)) :
    P s <= q ^ (s - c) * P c := by
  induction s, hcs using Nat.le_induction with
  | base =>
      simp
  | succ t hct ih =>
      have hstep_top : P (t + 1) <= q * P ((t + 1) - 1) :=
        hstep (t + 1) (by omega) (by omega)
      have hstep_restricted :
          forall r, c < r -> r <= t -> P r <= q * P (r - 1) := by
        intro r hcr hrt
        exact hstep r hcr (by omega)
      have ih' : P t <= q ^ (t - c) * P c :=
        ih hstep_restricted
      calc
        P (t + 1) <= q * P ((t + 1) - 1) := hstep_top
        _ = q * P t := by
          simp
        _ <= q * (q ^ (t - c) * P c) := by
          exact mul_le_mul_of_nonneg_left ih' hq_nonneg
        _ = q ^ ((t + 1) - c) * P c := by
          have hsub : (t + 1) - c = (t - c) + 1 := by omega
          rw [hsub, pow_succ']
          simp [mul_assoc]

-- Batch 4 promoted from .sgd_phase3_staging/SOptLib/Glue/geometric_rate_from_cutoff_potential_bound.lean
-- Generalization plan (G0):
-- concept/name: geometric rate from a cutoff-normalized potential bound; orig
--   was `lemma519_scalar_rate_from_potential_bound`, renamed away from the
--   paper lemma number and the fixed base `4 / 5`.
-- generality used: real scalar coefficients and natural-number powers only; no
--   measure, filtration, independence, integrability, convexity, smoothness,
--   oracle, carrier, or finite-dimensional hypotheses are used once the
--   potential bound and cutoff coefficient comparison have been proved.
-- portable call pattern: accelerated, variance-reduced, proximal, and
--   mirror-descent convergence proofs can call this after an epoch contraction
--   gives a normalized potential bound with base `rho`, and a cutoff estimate
--   proves `(2 * T)⁻¹ <= rho ^ c`; the schedules, potentials, and objective
--   gaps change while the final `Gap <= rho ^ s * D0` conclusion stays fixed.
-- counterargument checked: not paper-local traceability or a pure wrapper; the
--   statement removes the Lan-specific theorem number and fixed contraction
--   base while preserving the reusable coefficient normalization that combines
--   a potential bound, an initial budget, and a cutoff power comparison. It is
--   not decomposed into abstract formula parameters because the displayed
--   `3 * L / 2` and `D0 / (3 * L * T)` normalization is the concrete scalar
--   handoff future callers prove, not a separate recognized mathematical
--   object needing a def.
-- coverage search: searched SOptLib catalog/source for geometric, rate,
--   cutoff, normalized potential, contraction, `rho`, `D0`, and `Gap`; relevant
--   hits were `normalized_potential_contraction_of_weighted_recursion`,
--   `le_pow_mul_of_backward_contraction_on_Ioc`, and weighted-potential
--   endpoint rescaling lemmas, which prove the recurrence or earlier
--   coefficient rescaling but not this final cutoff-normalized scalar rate.
--   LeanSearch for "real inequality geometric rate from potential bound cutoff
--   coefficient rho powers" returned `le_geom`, `lt_geom`, and asymptotic
--   geometric facts, none of which cover the potential-normalization handoff.
-- minimal hypotheses: pointwise scalar assumptions only: positivity of `L` and
--   `T`, nonnegativity of `rho` and `D0`, the anchor order `c <= s`, the cutoff
--   coefficient comparison, and the two caller-supplied potential inequalities.

/-- Convert a cutoff-normalized potential estimate into a geometric gap rate.

If a gap is bounded by `(3 * L / 2)` times a potential, the potential is bounded
by `rho ^ (s - c) * (D0 / (3 * L * T))`, and the cutoff coefficient satisfies
`(2 * T)⁻¹ <= rho ^ c`, then the gap is bounded by `rho ^ s * D0`.

Layer: Glue | Gap: Level 1 (cutoff-normalized geometric rate handoff)
Proof: scale the potential bound by the nonnegative gap coefficient, combine
  the cutoff coefficient comparison with the remaining geometric power, and
  simplify the concrete `(3 * L / 2)` and `D0 / (3 * L * T)` normalization by
  ordered-field arithmetic.
Source: Mathlib real ordered-field arithmetic, natural powers, and monotonicity
  of multiplication over inequalities
Used in: variance-reduced accelerated gradient large-component linear-rate
  conclusion after the epoch potential contraction and cutoff denominator
  comparison
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/key_lemmas/14/proof/7
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem geometric_rate_from_cutoff_potential_bound
    (rho L T D0 Gap P : Real) (c s : Nat)
    (hrho_nonneg : 0 <= rho)
    (hL : 0 < L) (hT : 0 < T) (hD0 : 0 <= D0) (hcs : c <= s)
    (hcoef_base : (2 * T)⁻¹ <= rho ^ c)
    (hGap : Gap <= (3 * L / 2) * P)
    (hP : P <= rho ^ (s - c) * (D0 / (3 * L * T))) :
    Gap <= rho ^ s * D0 := by
  have hscaled :
      Gap <=
        (3 * L / 2) *
          (rho ^ (s - c) * (D0 / (3 * L * T))) := by
    exact hGap.trans (mul_le_mul_of_nonneg_left hP (by positivity))
  have hcoef_total :
      rho ^ (s - c) * (2 * T)⁻¹ <= rho ^ s := by
    have hmul := mul_le_mul_of_nonneg_left hcoef_base
      (pow_nonneg hrho_nonneg (s - c))
    have hpow :
        rho ^ (s - c) * rho ^ c = rho ^ s := by
      rw [← pow_add]
      have hadd : s - c + c = s := by omega
      rw [hadd]
    simpa [hpow] using hmul
  have hcoefD :
      (rho ^ (s - c) * (2 * T)⁻¹) * D0 <=
        (rho ^ s) * D0 :=
    mul_le_mul_of_nonneg_right hcoef_total hD0
  have hnormalize :
      (3 * L / 2) *
          (rho ^ (s - c) * (D0 / (3 * L * T))) =
        (rho ^ (s - c) * (2 * T)⁻¹) * D0 := by
    field_simp [ne_of_gt hL, ne_of_gt hT]
  exact hscaled.trans (by simpa [hnormalize] using hcoefD)

-- Batch 4 promoted from Staging/sum_range_succ_add_weighted_tail_le_sum_add_initial_of_step.lean
-- Generalization plan (G0):
-- concept/name: zero-based adjacent-weight scalar recurrence telescope with
--   retained endpoint tail; orig was lemma519_scalar_weighted_one_epoch_telescope.
-- generality used: ordered commutative-ring scalars and natural-indexed
--   sequences only; no measure, independence, integrability, convexity,
--   smoothness, oracle, carrier, or finite-dimensional hypotheses are used.
-- portable call pattern: variance-reduced, accelerated, mirror-descent, and
--   proximal epoch proofs can instantiate `A` as the one-step gap term, `B` as
--   the potential, `C` as the per-step budget, and `W` as the adjacent
--   potential weight while preserving the same telescoped endpoint bound.
-- counterargument checked: not paper-local traceability because all setup
--   fields and theorem numbers are removed; not a duplicate of the already
--   staged `sum_range_succ_add_weighted_tail_le_mul_add_initial_of_step`,
--   whose recurrence has constant budget and a `(1 + betaTail)` shifted-tail
--   sum rather than arbitrary adjacent weights `W k`.
-- coverage search: searched catalog/source for range telescope, weighted
--   recurrence, adjacent weight, zero-based, finite_window, and two_coeff;
--   SOptLib hits sum_range_sub_succ_le_first_of_last_nonneg,
--   finite_window_weighted_recurrence_telescope_with_tail_sums,
--   sum_weighted_sub_mul_le_first_sub_tail, and sum_Icc_two_coeff_telescope_le
--   are partial because they use drop-form differences, one-based windows, or
--   nonnegative interior tails rather than this zero-based recurrence shape.
-- minimal hypotheses: all already minimal for the algebraic proof: one initial
--   normalization `W 0 = 1` and one pointwise recurrence over `k < T`; no
--   nonnegativity of weights or potentials is needed because the final tail is
--   retained rather than discarded.

/-- A zero-based adjacent-weight scalar recurrence telescopes to its initial potential.

If each step bounds `A (k + 1) + W (k + 1) * B (k + 1)` by the current budget
plus the previous weighted potential `W k * B k`, then summing over `range T`
retains the endpoint `W T * B T` and leaves only the initial potential `B 0`
when `W 0 = 1`.

Layer: Glue | Gap: Level 1 (zero-based adjacent-weight recurrence telescope)
Proof: induct on the range length, split the top finite-sum terms with
  `Finset.sum_range_succ`, apply the exposed one-step recurrence, and close by
  ordered-ring arithmetic.
Source: Mathlib finite sums over natural ranges and ordered-ring arithmetic
Used in: variance-reduced accelerated gradient descent one-epoch weighted
  potential telescope after a printed one-step recurrence is summed
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/key_lemmas/14/proof/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem sum_range_succ_add_weighted_tail_le_sum_add_initial_of_step
    {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (T : Nat) (A B C W : Nat -> R)
    (hW0 : W 0 = 1)
    (hstep :
      forall k, k < T ->
        A (k + 1) + W (k + 1) * B (k + 1) <= C k + W k * B k) :
    (Finset.range T).sum (fun k => A (k + 1)) + W T * B T <=
      (Finset.range T).sum C + B 0 := by
  induction T with
  | zero =>
      simp [hW0]
  | succ T ih =>
      have hstep_prev :
          forall k, k < T ->
            A (k + 1) + W (k + 1) * B (k + 1) <= C k + W k * B k := by
        intro k hk
        exact hstep k (Nat.lt_trans hk (Nat.lt_succ_self T))
      have hih := ih hstep_prev
      have htop := hstep T (Nat.lt_succ_self T)
      have htop' :
          A (T + 1) + W (T + 1) * B (T + 1) - W T * B T <= C T := by
        linarith
      calc
        (Finset.range (T + 1)).sum (fun k => A (k + 1)) +
            W (T + 1) * B (T + 1)
            =
          ((Finset.range T).sum (fun k => A (k + 1)) + W T * B T) +
            (A (T + 1) + W (T + 1) * B (T + 1) - W T * B T) := by
            rw [Finset.sum_range_succ]
            ring
        _ <= (Finset.range T).sum C + B 0 + C T := by
            exact add_le_add hih htop'
        _ = (Finset.range (T + 1)).sum C + B 0 := by
            rw [Finset.sum_range_succ]
            ring

-- Batch 4 promoted from Staging/normalized_potential_contraction_of_weighted_recursion.lean
-- Generalization plan (G0):
-- concept/name: normalized potential contraction from a weighted recursion; orig was
--   lemma519_weighted_recursion_to_potential_contraction_scalar.
-- generality used: ordered-field scalar coefficients and potentials only; no measure,
--   filtration, convexity, smoothness, oracle, carrier, or finite-dimensional
--   hypotheses are used after the weighted recursion and nonnegativity facts
--   have been proved.
-- portable call pattern: accelerated, mirror-descent, proximal, and
--   variance-reduced convergence proofs can call this after an epoch telescope
--   gives `b * theta * G + Gamma * B <= a * theta * Gprev + Bprev` and side
--   estimates give `rho * a <= b` and `rho <= Gamma`; the concrete schedules,
--   objective gaps, and Bregman potentials change while the normalized
--   contraction conclusion stays the same.
-- counterargument checked: not paper-local traceability or a pure wrapper; the
--   statement removes all Lan-specific constants and captures the reusable
--   coefficient absorption step from a weighted recursion to a normalized
--   Lyapunov contraction. It is not just caller-side notation because the proof
--   combines positive rescaling, two coefficient comparisons, and retained-term
--   nonnegativity.
-- coverage search: searched SOptLib catalog/source for potential, weighted
--   recursion, normalized, contraction, Gamma, and rho; relevant hits were
--   finite_window_weighted_recurrence_telescope_with_tail_sums,
--   sum_weighted_sub_mul_le_first_sub_tail, and weighted potential rescaling
--   lemmas, which telescope or rewrite finite windows but do not state this
--   scalar normalized contraction implication. LeanSearch for "real inequality
--   weighted recursion normalized potential contraction" returned mean and
--   recurrence asymptotic lemmas, not this coefficient-absorption shape.
-- minimal hypotheses: all already minimal for the ordered-field proof: positivity of
--   `theta` and `rho`, nonnegativity only of the retained current terms `G`
--   and `B`, the weighted recursion, the previous-theta identity, and the two
--   coefficient lower bounds.

/-- A weighted scalar recursion contracts the normalized two-term potential.

If the weighted recursion has current coefficients `b` and `Gamma`, the
normalized current coefficients are dominated after scaling by `rho`, and the
retained current terms are nonnegative, then the normalized potential contracts
by the factor `rho^-1`.

Layer: Glue | Gap: Level 1 (weighted recursion to normalized potential contraction)
Proof: divide the weighted recursion by the positive mass `theta`, absorb the
  normalized current coefficients using `rho * a <= b` and `rho <= Gamma`, then
  multiply by the nonnegative inverse of `rho`.
Source: Mathlib ordered-field arithmetic, positive inverse, and monotonicity of
  multiplication over inequalities
Used in: variance-reduced accelerated gradient epoch Lyapunov contraction after
  weighted telescoping and Gamma lower-bound estimates
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/key_lemmas/14/proof/5
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem normalized_potential_contraction_of_weighted_recursion
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (a b rho theta thetaPrev Gamma G Gprev B Bprev : R)
    (hrho_pos : 0 < rho)
    (htheta_pos : 0 < theta)
    (htheta_prev_eq : thetaPrev = theta)
    (hweighted :
      b * theta * G + Gamma * B <= a * theta * Gprev + Bprev)
    (hcoeff_gap : rho * a <= b)
    (hcoeff_tail : rho <= Gamma)
    (hG_nonneg : 0 <= G)
    (hB_nonneg : 0 <= B) :
    a * G + theta⁻¹ * B <=
      rho⁻¹ * (a * Gprev + thetaPrev⁻¹ * Bprev) := by
  have htheta_inv_nonneg : 0 <= theta⁻¹ := le_of_lt (inv_pos.mpr htheta_pos)
  have hweighted_div :
      b * G + Gamma * (theta⁻¹ * B) <=
        a * Gprev + theta⁻¹ * Bprev := by
    have hmul := mul_le_mul_of_nonneg_left hweighted htheta_inv_nonneg
    have hleft :
        theta⁻¹ * (b * theta * G + Gamma * B) =
          b * G + Gamma * (theta⁻¹ * B) := by
      field_simp [ne_of_gt htheta_pos]
    have hright :
        theta⁻¹ * (a * theta * Gprev + Bprev) =
          a * Gprev + theta⁻¹ * Bprev := by
      field_simp [ne_of_gt htheta_pos]
    calc
      b * G + Gamma * (theta⁻¹ * B) =
          theta⁻¹ * (b * theta * G + Gamma * B) := hleft.symm
      _ <= theta⁻¹ * (a * theta * Gprev + Bprev) := hmul
      _ = a * Gprev + theta⁻¹ * Bprev := hright
  have hscaled_left :
      rho * (a * G + theta⁻¹ * B) <=
        b * G + Gamma * (theta⁻¹ * B) := by
    have hgap_coeff :
        rho * (a * G) <= b * G := by
      calc
        rho * (a * G) = (rho * a) * G := by ring
        _ <= b * G := mul_le_mul_of_nonneg_right hcoeff_gap hG_nonneg
    have hb_coeff :
        rho * (theta⁻¹ * B) <= Gamma * (theta⁻¹ * B) := by
      exact
        mul_le_mul_of_nonneg_right hcoeff_tail
          (mul_nonneg htheta_inv_nonneg hB_nonneg)
    calc
      rho * (a * G + theta⁻¹ * B) =
          rho * (a * G) + rho * (theta⁻¹ * B) := by ring
      _ <= b * G + Gamma * (theta⁻¹ * B) := add_le_add hgap_coeff hb_coeff
  have hscaled :
      rho * (a * G + theta⁻¹ * B) <=
        a * Gprev + theta⁻¹ * Bprev :=
    hscaled_left.trans hweighted_div
  have hmul := mul_le_mul_of_nonneg_left hscaled (le_of_lt (inv_pos.mpr hrho_pos))
  calc
    a * G + theta⁻¹ * B =
        rho⁻¹ * (rho * (a * G + theta⁻¹ * B)) := by
          field_simp [ne_of_gt hrho_pos]
    _ <= rho⁻¹ * (a * Gprev + theta⁻¹ * Bprev) := hmul
    _ = rho⁻¹ * (a * Gprev + thetaPrev⁻¹ * Bprev) := by
          rw [htheta_prev_eq]

-- Batch 4 promoted from Staging/gap_le_sixteen_mul_div_of_coeff_lower_and_retained_lyapunov.lean
-- Generalization plan (G0):
-- concept/name: le_sixteen_mul_div_of_coeff_lower_and_add_nonneg_le
--   exposes a scalar ordered-field normalization step from a lower bound on a
--   coefficient and an upper bound with an added nonnegative term.
-- generality used: arbitrary linear ordered field scalar parameters; no carrier
--   type, measure, convexity, smoothness predicate, oracle, filtration, or
--   finite-dimensional hypotheses are used.
-- portable call pattern: convergence proofs can call this after an intermediate
--   scalar estimate gives `c * x + r <= d / (3 * l)` and schedule estimates give
--   `a / (48 * l) <= c`; only the scalar constants and proofs of nonnegativity
--   change while the endpoint rate shape is fixed.
-- counterargument checked: not paper-local traceability because the statement
--   is paper-free scalar algebra and captures a reusable nonnegative-remainder
--   drop plus coefficient-normalization step; not a pure wrapper because it
--   combines coefficient absorption, dropping an added nonnegative term, and
--   division by a positive coefficient.
-- coverage search: searched SOptLib, Staging, and the catalog for `sixteen`,
--   `coefficient`, `A / (48 * L)`, and related inequality shapes; related hits
--   were finite-window telescope and contraction lemmas, plus the staged
--   intermediate coefficient lower bound, but none state this final scalar
--   extraction. LeanSearch returned unrelated ordered-field and ODE facts, not
--   this inequality shape.
-- minimal hypotheses: positivity of `l` and `a`, nonnegativity of `x` and `r`,
--   the coefficient lower bound, and the single scalar upper-bound inequality.

/-- A coefficient lower bound and an added nonnegative term imply a scalar rate.

If `c * x + r` is bounded by `d / (3 * l)`, the added term `r` is
nonnegative, and `c` dominates `a / (48 * l)`, then `x` is at most
`16 * d / a`.

Layer: Glue (coefficient normalization with nonnegative addend)
Proof: absorb the coefficient lower bound against the nonnegative `x`, drop the
  added nonnegative term from the upper bound, then divide by the positive
  coefficient `a / (48 * l)` and normalize the constants.
Source: Mathlib ordered-field arithmetic and monotonicity of
  multiplication and division over inequalities. -/
theorem le_sixteen_mul_div_of_coeff_lower_and_add_nonneg_le
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (l a c d x r : R)
    (hl : 0 < l) (ha : 0 < a)
    (hx_nonneg : 0 <= x) (hr_nonneg : 0 <= r)
    (hc_lower : a / (48 * l) <= c)
    (hadd_le : c * x + r <= d / (3 * l)) :
    x <= 16 * d / a := by
  have hc_pos : 0 < a / (48 * l) := by
    exact div_pos ha (mul_pos (by norm_num) hl)
  have hc_mul_le : (a / (48 * l)) * x <= c * x :=
    mul_le_mul_of_nonneg_right hc_lower hx_nonneg
  have hcx_le : c * x <= d / (3 * l) := by
    linarith
  have hmain : (a / (48 * l)) * x <= d / (3 * l) :=
    hc_mul_le.trans hcx_le
  have hdiv :
      ((a / (48 * l)) * x) / (a / (48 * l)) <=
        (d / (3 * l)) / (a / (48 * l)) :=
    div_le_div_of_nonneg_right hmain (le_of_lt hc_pos)
  have hleft :
      ((a / (48 * l)) * x) / (a / (48 * l)) = x := by
    field_simp [ne_of_gt hc_pos]
  have hright :
      (d / (3 * l)) / (a / (48 * l)) = 16 * d / a := by
    field_simp [ne_of_gt hl, ne_of_gt ha]
    ring
  simpa [hleft, hright] using hdiv

-- Batch 4 promoted from Staging/gap_le_div_of_coeff_le_and_nonneg_remainder.lean
-- Generalization plan (G0):
-- concept/name: gap_le_div_of_coeff_le_and_nonneg_remainder exposes the
--   coefficient-normalization step for isolating a nonnegative scalar from a
--   linear bound with a nonnegative remainder; orig was
--   lemma520_scalar_rate_from_intermediate_lyapunov_pre.
-- generality used: arbitrary linear ordered field scalars; no carrier type,
--   measure, convexity, smoothness, oracle, filtration, or finite-dimensional
--   hypotheses are used.
-- portable call pattern: stochastic-gradient, mirror-descent, and
--   variance-reduced convergence proofs can call this after a terminal
--   potential inequality `c * gap + rem <= budget` and a schedule lower bound
--   `c0 <= c`; only the scalar coefficient, retained remainder, and budget
--   constants change.
-- counterargument checked: a related staged theorem
--   le_sixteen_mul_div_of_coeff_lower_and_add_nonneg_le is specialized to the
--   `a / (48 * l)` and `d / (3 * l)` constants; this theorem strengthens it
--   by exposing the reusable ordered-field normalization shape. Mathlib has
--   division monotonicity lemmas, but no single theorem packaging coefficient
--   absorption, dropping a nonnegative addend, and normalizing by a lower
--   coefficient.
-- coverage search: searched SOptLib, Staging, and the catalog for gap/div,
--   coefficient, budget, remainder, and nonnegative addend; read the full
--   signature of le_sixteen_mul_div_of_coeff_lower_and_add_nonneg_le as a
--   partial specialized hit. LeanSearch returned div_le_of_le_mul0,
--   div_le_div0, and div_le_div_of_nonneg_right as proof ingredients, not this
--   packaged statement.
-- minimal hypotheses: `0 < c0`, `0 <= gap`, `0 <= rem`, `c0 <= c`, and
--   `c * gap + rem <= budget`; all are consumed directly.

/-- A positive lower coefficient isolates a nonnegative term from a bound with
a nonnegative remainder.

If `c0 <= c`, `gap` and `rem` are nonnegative, and `c * gap + rem <= budget`,
then `gap <= budget / c0`.

Layer: Glue | Gap: Level 1 (coefficient normalization with nonnegative remainder)
Proof: multiply the coefficient lower bound by the nonnegative gap, drop the
  nonnegative remainder from the upper bound, and divide by the positive lower
  coefficient.
Source: Mathlib ordered-field arithmetic, inequality monotonicity for
  multiplication, and division monotonicity over nonnegative denominators
Used in: variance-reduced accelerated gradient terminal gap extraction from a
  retained-potential convergence inequality
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem gap_le_div_of_coeff_le_and_nonneg_remainder
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (c0 c gap rem budget : R)
    (hc0_pos : 0 < c0)
    (hgap_nonneg : 0 <= gap)
    (hrem_nonneg : 0 <= rem)
    (hc0_le_c : c0 <= c)
    (hbound : c * gap + rem <= budget) :
    gap <= budget / c0 := by
  have hc0_gap_le : c0 * gap <= c * gap :=
    mul_le_mul_of_nonneg_right hc0_le_c hgap_nonneg
  have hc_gap_le : c * gap <= budget := by
    linarith
  have hmain : c0 * gap <= budget :=
    hc0_gap_le.trans hc_gap_le
  have hdiv : (c0 * gap) / c0 <= budget / c0 :=
    div_le_div_of_nonneg_right hmain (le_of_lt hc0_pos)
  have hleft : (c0 * gap) / c0 = gap := by
    field_simp [ne_of_gt hc0_pos]
  simpa [hleft] using hdiv

-- Batch 4 promoted from Staging/retained_potential_le_cutoff_of_step_and_coeff_domination.lean
-- Generalization plan (G0):
-- concept/name: retained potential bound from cutoff by one-step recurrence and
--   adjacent coefficient domination; orig was
--   lemma520_smooth_epoch_scalar_chain_from_cutoff.
-- generality used: natural-indexed scalar sequences with only the order and
--   operation monotonicity needed for the recurrence chain; no
--   measure, independence, integrability, convexity, smoothness, oracle,
--   carrier, filtration, or finite-dimensional assumptions are used.
-- portable call pattern: accelerated, mirror-descent, proximal, and
--   variance-reduced epoch proofs can call this after proving
--   `L r * Gap r + B r <= R r * Gap (r - 1) + B (r - 1)`, adjacent coefficient
--   domination `R (j + 1) <= L j`, and nonnegativity of retained gaps on
--   `c <= j < s`; the schedules, gap certificate, and retained potential vary
--   while the terminal-to-cutoff conclusion stays fixed.
-- counterargument checked: not paper-local traceability because the statement
--   has no Lan constants, theorem numbers, setup fields, or schedule formulas;
--   not a one-line wrapper because it packages the induction that repeatedly
--   absorbs the right coefficient into the previous left coefficient.
-- coverage search: searched SOptLib catalog/source and staging for retained
--   potential, cutoff, coefficient domination, backward contraction, Gap/B, and
--   recurrence chain. Relevant hits include
--   le_pow_mul_of_backward_contraction_on_Ioc and
--   normalized_potential_contraction_of_weighted_recursion, but those handle a
--   fixed multiplicative contraction or a single normalized weighted recursion,
--   not this arbitrary-cutoff two-term retained-potential chain.
-- minimal hypotheses: pointwise step inequalities only on `c < r <= s`,
--   coefficient domination and gap nonnegativity only on `c <= j < s`; no
--   nonnegativity of `B`, `L`, or `R` is needed because the retained `B` terms
--   are carried exactly.

/-- A retained two-term potential at a terminal epoch is bounded by its cutoff value.

If each backward step bounds `L r * Gap r + B r` by the previous retained
potential using coefficient `R r`, and every adjacent coefficient satisfies
`R (j + 1) <= L j` on nonnegative gaps, then the terminal retained potential is
bounded by the cutoff retained potential.

Layer: Glue | Gap: Level 1 (retained potential chain with coefficient domination)
Proof: induction on the distance from the cutoff. The successor step applies
  the one-step recurrence, uses coefficient domination with gap nonnegativity
  to replace `R t * Gap (t - 1)` by `L (t - 1) * Gap (t - 1)`, and invokes the
  induction hypothesis at the previous epoch.
Source: Mathlib natural-number induction and unbundled monotonicity for
  addition on the right and multiplication by a nonnegative right factor
Used in: variance-reduced accelerated gradient epoch Lyapunov chain from an
  intermediate smooth epoch back to the cutoff epoch
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/key_lemmas/15/proof
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem retained_potential_le_cutoff_of_step_and_coeff_domination
    {α : Type*} [Mul α] [Zero α] [Preorder α] [MulPosMono α] [Add α] [AddRightMono α]
    (c s : Nat) (L R Gap B : Nat -> α)
    (hcs : c <= s)
    (hstep :
      forall r, c < r -> r <= s ->
        L r * Gap r + B r <= R r * Gap (r - 1) + B (r - 1))
    (hcoeff :
      forall j, c <= j -> j < s -> R (j + 1) <= L j)
    (hGap_nonneg :
      forall j, c <= j -> j < s -> 0 <= Gap j) :
    L s * Gap s + B s <= L c * Gap c + B c := by
  have hmain :
      forall d t, c <= t -> t <= s -> t - c = d ->
        L t * Gap t + B t <= L c * Gap c + B c := by
    intro d
    induction d with
    | zero =>
        intro t hct _hts htc
        have ht_eq : t = c := by omega
        subst t
        rfl
    | succ d ih =>
        intro t hct hts htc
        have hc_lt_t : c < t := by omega
        have hc_le_prev : c <= t - 1 := by omega
        have hprev_lt_s : t - 1 < s := by omega
        have hprev_sub : (t - 1) - c = d := by omega
        have hprev_le_s : t - 1 <= s := Nat.le_of_lt hprev_lt_s
        have hnext := hstep t hc_lt_t hts
        have hbridge :
            R t * Gap (t - 1) + B (t - 1) <=
              L (t - 1) * Gap (t - 1) + B (t - 1) := by
          have ht_prev_succ : t - 1 + 1 = t := by omega
          have hmul :
              R t * Gap (t - 1) <= L (t - 1) * Gap (t - 1) := by
            rw [← ht_prev_succ]
            exact
              mul_le_mul_of_nonneg_right
                (hcoeff (t - 1) hc_le_prev hprev_lt_s)
                (hGap_nonneg (t - 1) hc_le_prev hprev_lt_s)
          exact add_le_add_left hmul (B (t - 1))
        exact hnext.trans
          (hbridge.trans (ih (t - 1) hc_le_prev hprev_le_s hprev_sub))
  exact hmain (s - c) s hcs le_rfl rfl

-- Batch 5 promoted from Staging/sum_range_terminal_else_mul_eq_diff_sum_add_initial.lean
/-- A terminal-exception coefficient range sum is an adjacent-difference sum
plus the initial correction.

For a positive finite window, weighting the terminal shifted value by `g` and
every earlier shifted value by `g - c` is the same as summing
`g * A (k + 1) - c * A k` and restoring the initial term `c * A 0`.

Layer: Glue | Gap: Level 1 (terminal-exception range coefficient rewrite)
Proof: induction on the window length, splitting the final range summand with
  `Finset.sum_range_succ`; the terminal and nonterminal branches are then
  identified by arithmetic and finite-sum congruence.
Source: Mathlib finite sums over natural ranges and non-unital,
  non-associative ring arithmetic
Used in: variance-reduced accelerated gradient descent smooth epoch proof
  converting terminal theta weights into a difference-form scalar telescope
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/key_lemmas/15/proof
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem sum_range_terminal_else_mul_eq_diff_sum_add_initial
    {R : Type*} [NonUnitalNonAssocRing R]
    (T : Nat) (A : Nat -> R) (g c : R) (hTpos : 0 < T) :
    (Finset.range T).sum
        (fun k => (if k + 1 = T then g else g - c) * A (k + 1)) =
      (Finset.range T).sum (fun k => g * A (k + 1) - c * A k) +
        c * A 0 := by
  induction T with
  | zero =>
      omega
  | succ T ih =>
      cases T with
      | zero =>
          simp
      | succ T =>
          have hTpos' : 0 < T + 1 := Nat.succ_pos T
          have ih' := ih hTpos'
          have hprev_ne_top :
              forall k, k < T + 1 -> k + 1 ≠ T + 1 + 1 := by
            intro k hk
            omega
          have hprev_sum :
              (Finset.range (T + 1)).sum
                  (fun k =>
                    (if k + 1 = T + 1 then g else g - c) * A (k + 1)) =
                (Finset.range T).sum (fun k => (g - c) * A (k + 1)) +
                  g * A (T + 1) := by
            rw [Finset.sum_range_succ]
            rw [if_pos rfl]
            refine congrArg (fun z => z + g * A (T + 1)) ?_
            refine Finset.sum_congr rfl ?_
            intro k hk
            have hk_ne : k + 1 ≠ T + 1 := by
              have hklt : k < T := Finset.mem_range.mp hk
              omega
            rw [if_neg hk_ne]
          have hall_prev :
              (Finset.range (T + 1)).sum
                  (fun k => (g - c) * A (k + 1)) =
                (Finset.range (T + 1)).sum
                    (fun k =>
                      (if k + 1 = T + 1 then g else g - c) * A (k + 1)) -
                  c * A (T + 1) := by
            rw [hprev_sum, Finset.sum_range_succ]
            noncomm_ring
          have hdiff_succ :
              (Finset.range (T + 1 + 1)).sum
                  (fun k => g * A (k + 1) - c * A k) =
                (Finset.range (T + 1)).sum
                    (fun k => g * A (k + 1) - c * A k) +
                  (g * A (T + 1 + 1) - c * A (T + 1)) := by
            rw [Finset.sum_range_succ]
          calc
            (Finset.range (T + 1 + 1)).sum
                (fun k =>
                  (if k + 1 = T + 1 + 1 then g else g - c) * A (k + 1)) =
              (Finset.range (T + 1)).sum
                  (fun k =>
                    (if k + 1 = T + 1 + 1 then g else g - c) * A (k + 1)) +
                g * A (T + 1 + 1) := by
                rw [Finset.sum_range_succ]
                simp
            _ =
              (Finset.range (T + 1)).sum
                  (fun k => (g - c) * A (k + 1)) +
                g * A (T + 1 + 1) := by
                refine congrArg (fun z => z + g * A (T + 1 + 1)) ?_
                refine Finset.sum_congr rfl ?_
                intro k hk
                rw [if_neg (hprev_ne_top k (Finset.mem_range.mp hk))]
            _ =
              ((Finset.range (T + 1)).sum
                  (fun k =>
                    (if k + 1 = T + 1 then g else g - c) * A (k + 1)) -
                c * A (T + 1)) +
                g * A (T + 1 + 1) := by
                rw [hall_prev]
            _ =
              ((Finset.range (T + 1)).sum
                  (fun k => g * A (k + 1) - c * A k) + c * A 0 -
                c * A (T + 1)) +
                g * A (T + 1 + 1) := by
                rw [ih']
            _ =
              (Finset.range (T + 1 + 1)).sum
                  (fun k => g * A (k + 1) - c * A k) +
                c * A 0 := by
                rw [hdiff_succ]
                noncomm_ring

-- Batch 5 promoted from Staging/smooth_terminal_weighted_gap_telescope_of_step.lean
/-- A terminal-exception finite-sum bound follows from a one-step recurrence.

If a scalar recurrence controls the next value of `A` plus a weighted next
value of `B` by the previous values and a fixed base term, then the
terminal-exception weighted sum of `A` plus the terminal value of `B` is bounded
by the corresponding base coefficient and the initial value of `B`.

Layer: Glue | Role: terminal-exception scalar recurrence telescope
Proof: rewrite the terminal-exception weighted sum as a difference-form
  sum plus the initial correction, apply the zero-based scalar recurrence
  telescope with retained tail term, and drop the nonnegative tail
  sum. -/
theorem sum_range_terminal_else_mul_le_const_mul_add_initial_of_step
    {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (T : Nat) (A B : Nat -> R)
    (base g alpha p betaTail : R)
    (hTpos : 0 < T)
    (hstep :
      forall k, k < T ->
        g * A (k + 1) + (1 + betaTail) * B (k + 1) <=
          g * (1 - alpha - p) * A k + g * p * base + B k)
    (hA0 : A 0 = base)
    (hbetaTail_nonneg : 0 <= betaTail)
    (hB_nonneg : forall k, k < T -> 0 <= B (k + 1)) :
    (Finset.range T).sum
        (fun k =>
          (if k + 1 = T then g else g * (alpha + p)) * A (k + 1)) +
        B T <=
      (g * (1 - alpha) + ((T - 1 : Nat) : R) * (g * p)) * base + B 0 := by
  let c : R := g * (1 - alpha - p)
  let D : Nat -> R := fun k => g * A k - c * A (k - 1)
  have hdiffStep :
      forall k, k < T ->
        D (k + 1) + (1 + betaTail) * B (k + 1) <=
          g * p * base + B k := by
    intro k hk
    have hbase := hstep k hk
    dsimp [D, c]
    linarith
  have htel :=
    sum_range_succ_add_weighted_tail_le_mul_add_initial_of_step
      T D B (g * p * base) betaTail hdiffStep
  have hres_nonneg :
      0 <= betaTail * (Finset.range T).sum (fun k => B (k + 1)) := by
    exact mul_nonneg hbetaTail_nonneg
      (Finset.sum_nonneg (by
        intro k hk
        exact hB_nonneg k (Finset.mem_range.mp hk)))
  have htel_drop :
      (Finset.range T).sum (fun k => D (k + 1)) + B T <=
        (T : R) * (g * p * base) + B 0 := by
    linarith
  have hweights :
      (Finset.range T).sum
          (fun k =>
            (if k + 1 = T then g else g * (alpha + p)) * A (k + 1)) =
        (Finset.range T).sum (fun k => D (k + 1)) + c * A 0 := by
    have hdiff :=
      sum_range_terminal_else_mul_eq_diff_sum_add_initial
        T A g c hTpos
    have hcoeff : g - c = g * (alpha + p) := by
      dsimp [c]
      ring
    simpa [D, c, Nat.add_sub_cancel, hcoeff] using hdiff
  calc
    (Finset.range T).sum
        (fun k =>
          (if k + 1 = T then g else g * (alpha + p)) * A (k + 1)) +
        B T =
      ((Finset.range T).sum (fun k => D (k + 1)) + B T) + c * A 0 := by
        rw [hweights]
        ring
    _ <=
      ((T : R) * (g * p * base) + B 0) + c * A 0 := by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_right htel_drop (c * A 0)
    _ =
      (g * (1 - alpha) + ((T - 1 : Nat) : R) * (g * p)) * base + B 0 := by
        rw [hA0]
        dsimp [c]
        have hTsub : (T : R) = ((T - 1 : Nat) : R) + 1 := by
          have hsucc : T = (T - 1) + 1 := by omega
          rw [hsucc]
          norm_num
        rw [hTsub]
        ring

-- Batch 5 promoted from Staging/sum_range_if_succ_eq_last_else_const.lean
/-- A finite range sum with one terminal value and a constant interior value has
the expected closed form.

For a positive length `N`, the last index contributes `a` and the preceding
`N - 1` indices contribute repeated copies of `b`; for `N = 0`, the empty sum is
zero.

Layer: Glue | Gap: Level 0 (terminal-exception finite range mass)
Proof: split the final summand with `Finset.sum_range_succ`, identify every
  earlier branch as the constant interior value, and simplify the repeated
  constant sum to an `nsmul`.
Source: Mathlib finite sums over natural ranges and additive commutative monoids
Used in: variance-reduced accelerated gradient descent epoch-weight
  normalization for a terminal-adjusted output schedule
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem sum_range_if_succ_eq_last_else_const
    {M : Type*} [AddCommMonoid M]
    (N : Nat) (a b : M) :
    (Finset.range N).sum (fun k => if k + 1 = N then a else b) =
      if N = 0 then 0 else a + (N - 1) • b := by
  induction N with
  | zero =>
      simp
  | succ N _ih =>
      cases N with
      | zero =>
          simp
      | succ N =>
          have hprev_ne_top : forall k, k < N + 1 -> k + 1 ≠ N + 1 + 1 := by
            intro k hk
            omega
          calc
            (Finset.range (N + 1 + 1)).sum
                (fun k => if k + 1 = N + 1 + 1 then a else b) =
              (Finset.range (N + 1)).sum
                  (fun k => if k + 1 = N + 1 + 1 then a else b) + a := by
                rw [Finset.sum_range_succ]
                simp
            _ = (Finset.range (N + 1)).sum (fun _k => b) + a := by
                refine congrArg (fun z => z + a) ?_
                refine Finset.sum_congr rfl ?_
                intro k hk
                exact if_neg (hprev_ne_top k (Finset.mem_range.mp hk))
            _ = (N + 1) • b + a := by
                simp
            _ = a + ((N + 1 + 1) - 1) • b := by
                have hsub : (N + 1 + 1) - 1 = N + 1 := by omega
                rw [hsub]
                rw [add_comm]
            _ = (if N + 1 + 1 = 0 then 0
                  else a + ((N + 1 + 1) - 1) • b) := by
                simp

-- Batch 5 promoted from Staging/pow_mul_potential_le_of_one_step_backwards.lean
/-- A backward multiplicative potential inequality iterates to an endpoint bound.

If every step in the natural interval from `c + 1` through `s` satisfies
`rho * P r <= P (r - 1)` and `rho` is nonnegative, then the terminal potential
multiplied by `rho^(s-c)` is bounded by the base potential.

Layer: Glue | Gap: Level 0 (backward multiplicative potential chain)
Proof: induction on the right endpoint of the interval. The successor case
  peels off the top step, multiplies it by the nonnegative accumulated power,
  and applies the induction hypothesis on the restricted interval.
Source: Mathlib natural-number induction, powers, and ordered-semiring
  multiplication monotonicity
Used in: variance-reduced accelerated gradient tail analysis propagating a
  retained Lyapunov potential from the terminal epoch back to the tail anchor
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/key_lemmas/14/proof
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem pow_mul_potential_le_of_one_step_backwards
    {R : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
    (rho : R) (P : Nat -> R) (c s : Nat) (hcs : c <= s)
    (hrho_nonneg : 0 <= rho)
    (hstep : forall r, c < r -> r <= s -> rho * P r <= P (r - 1)) :
    rho ^ (s - c) * P s <= P c := by
  induction s, hcs using Nat.le_induction with
  | base =>
      simp
  | succ t hct ih =>
      have hstep_top : rho * P (t + 1) <= P t := by
        simpa using hstep (t + 1) (by omega) (by omega)
      have hstep_restricted :
          forall r, c < r -> r <= t -> rho * P r <= P (r - 1) := by
        intro r hcr hrt
        exact hstep r hcr (by omega)
      have ih' : rho ^ (t - c) * P t <= P c :=
        ih hstep_restricted
      calc
        rho ^ ((t + 1) - c) * P (t + 1) =
            rho ^ (t - c) * (rho * P (t + 1)) := by
              have hsub : (t + 1) - c = (t - c) + 1 := by omega
              rw [hsub, pow_succ]
              simp [mul_assoc]
        _ <= rho ^ (t - c) * P t := by
              exact mul_le_mul_of_nonneg_left hstep_top
                (pow_nonneg hrho_nonneg (t - c))
        _ <= P c := ih'

-- Batch 5 promoted from Staging/sum_range_weighted_tail_epoch_telescope_le.lean
/-- A zero-based weighted recurrence telescopes with a lagged correction.

Suppose a one-step recurrence has current term
`weight k * (scale * value (k + 1))`, weighted endpoint potential
`weight (k + 1) * potential (k + 1)`, lagged correction
`weight k * (scale * lagCoeff * value k)`, and a constant source
`weight k * (scale * sourceCoeff * sourceValue)`. If the displayed weighted
total is the sum of current terms minus the nonzero lagged corrections, then
summing the recurrence retains only the terminal weighted potential and the
accumulated source coefficient.

Layer: Glue | Gap: Level 1 (zero-based weighted tail recurrence telescope)
Proof: apply the adjacent-weight scalar recurrence telescope with the combined
  lagged-correction/source budget, split that budget over `range n`, and use
  ordered-ring arithmetic with the supplied weighted-sum identity.
Source: Mathlib finite sums over natural ranges and ordered-ring arithmetic
Used in: variance-reduced accelerated gradient descent tail recursion
  after the weighted one-step inequality is summed
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/key_lemmas/14/proof/4
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem sum_range_weighted_lagged_source_telescope_le
    {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (n : Nat) (scale lagCoeff sourceCoeff sourceValue weightedTotal : R)
    (weight value potential : Nat -> R)
    (hn_pos : 0 < n)
    (hweight_zero : weight 0 = 1)
    (hvalue_zero : value 0 = sourceValue)
    (hweighted_sum :
      scale * weightedTotal =
        (Finset.range n).sum (fun k => weight k * (scale * value (k + 1))) -
          (Finset.range n).sum
            (fun k => if k = 0 then 0 else weight k * (scale * lagCoeff * value k)))
    (hstep :
      forall k, k < n ->
        weight k * (scale * value (k + 1)) + weight (k + 1) * potential (k + 1) <=
          (weight k * (scale * lagCoeff * value k) +
              weight k * (scale * sourceCoeff * sourceValue)) +
            weight k * potential k) :
    scale * weightedTotal + weight n * potential n <=
      scale * (lagCoeff + sourceCoeff * (Finset.range n).sum weight) * sourceValue +
        potential 0 := by
  classical
  let C : Nat -> R := fun k =>
    weight k * (scale * lagCoeff * value k) +
      weight k * (scale * sourceCoeff * sourceValue)
  have htel :=
    sum_range_succ_add_weighted_tail_le_sum_add_initial_of_step
      n (fun k => weight (k - 1) * (scale * value k)) potential C weight hweight_zero
      (by
        intro k hk
        simpa [C, Nat.add_sub_cancel, add_assoc] using hstep k hk)
  have hsplit_pos :
      forall N : Nat, 0 < N ->
        (Finset.range N).sum C =
          (Finset.range N).sum
              (fun k =>
                if k = 0 then 0 else weight k * (scale * lagCoeff * value k)) +
            scale * (lagCoeff + sourceCoeff * (Finset.range N).sum weight) *
              sourceValue := by
    intro N hN
    induction N with
    | zero =>
        omega
    | succ N ih =>
        by_cases hNzero : N = 0
        · subst N
          simp [C, hweight_zero, hvalue_zero]
          ring
        · have hNpos : 0 < N := Nat.pos_of_ne_zero hNzero
          have ihN := ih hNpos
          rw [Finset.sum_range_succ, Finset.sum_range_succ, ihN]
          simp [hNzero]
          rw [Finset.sum_range_succ]
          ring
  have hsplit :
      (Finset.range n).sum C =
        (Finset.range n).sum
            (fun k => if k = 0 then 0 else weight k * (scale * lagCoeff * value k)) +
          scale * (lagCoeff + sourceCoeff * (Finset.range n).sum weight) *
            sourceValue :=
    hsplit_pos n hn_pos
  have htel' :
      (Finset.range n).sum (fun k => weight k * (scale * value (k + 1))) +
          weight n * potential n <=
        (Finset.range n).sum
            (fun k => if k = 0 then 0 else weight k * (scale * lagCoeff * value k)) +
          scale * (lagCoeff + sourceCoeff * (Finset.range n).sum weight) *
            sourceValue + potential 0 := by
    simpa [C, Nat.add_sub_cancel, hsplit, add_assoc] using htel
  linarith

-- Batch 5 promoted from Staging/sum_range_succ_drop_last_eq_drop_first.lean
/-- Shifting a finite range sum by successor and dropping the terminal shifted
index is the same as dropping the initial unshifted index.

For a family `F`, both sides sum the same terms `F 1, ..., F (T - 1)` over a
zero-based `range T`, with one side written in shifted coordinates and the
other in unshifted coordinates.

Layer: Glue | Gap: Level 0 (finite range shifted-support reindexing)
Proof: split a positive range on both the terminal and initial side using
  `Finset.sum_range_succ` and `Finset.sum_range_succ'`; the remaining summands
  agree by pointwise simplification under the range bound.
Source: Mathlib finite sums over natural ranges and additive commutative monoids
Used in: variance-reduced accelerated gradient descent terminal-adjusted
  weighted-gap telescope after shifting one-step terms from `k + 1` to `k`
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/key_lemmas/16/proof
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem sum_range_succ_drop_last_eq_drop_first
    {M : Type*} [AddCommMonoid M]
    (T : Nat) (F : Nat -> M) :
    (Finset.range T).sum (fun k => if k + 1 = T then 0 else F (k + 1)) =
      (Finset.range T).sum (fun k => if k = 0 then 0 else F k) := by
  cases T with
  | zero =>
      simp
  | succ T =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ']
      simp only [if_true, Nat.succ_ne_zero, add_zero]
      refine Finset.sum_congr rfl ?_
      intro k hk
      simp only [Finset.mem_range] at hk
      have hne : k ≠ T := by omega
      simp [hne]

-- Batch 5 promoted from Staging/half_mul_one_add_delta_pow_le_tail_coeff.lean
/-- A predecessor power bound and accumulated-increment lower bound give a tail
coefficient lower bound.

If `0 <= delta`, `T * delta <= alpha`, and the predecessor power
`(1 + delta)^(T - 1)` is bounded by its linearization, then half of the
terminal power is bounded by the terminal adjusted coefficient
`1 - (1 - alpha - 1/2) * (1 + delta)`.

Layer: Glue | Gap: Level 1 (terminal power tail-coefficient comparison)
Proof: multiply the predecessor power bound by the nonnegative half-base
  factor, use `T * delta <= alpha` to raise the intermediate coefficient, and
  finish by ordered-field arithmetic.
Source: Mathlib ordered-field arithmetic, natural casts, and finite natural
  powers
Used in: variance-reduced accelerated-gradient linear-tail theta-mass lower
  bound after the geometric predecessor power estimate
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/key_lemmas/18/proof/9
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem half_mul_one_add_delta_pow_le_tail_coeff
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (T : Nat) (alpha delta : K) (hTpos : 0 < T)
    (hdelta : 0 <= delta) (halpha_ge : (T : K) * delta <= alpha)
    (hpow : (1 + delta) ^ (T - 1) <=
      1 + 2 * (((T - 1 : Nat) : K)) * delta) :
    (1 / 2 : K) * (1 + delta) ^ T <=
      1 - (1 - alpha - (1 / 2 : K)) * (1 + delta) := by
  have hbase_nonneg : 0 <= 1 + delta := by linarith
  have hhalf_base_nonneg : 0 <= (1 / 2 : K) * (1 + delta) := by positivity
  have hT_cast_sub : (((T - 1 : Nat) : K)) = (T : K) - 1 := by
    have hT_one : 1 <= T := Nat.succ_le_of_lt hTpos
    exact_mod_cast Nat.sub_eq_iff_eq_add hT_one |>.mpr (by omega)
  have halpha_minus :
      (T : K) * delta - delta <= alpha - delta := by
    linarith
  have hfirst :
      (1 + delta) * (alpha - delta + (1 / 2 : K)) <=
        1 - (1 - alpha - (1 / 2 : K)) * (1 + delta) := by
    have hsq : 0 <= delta ^ 2 := sq_nonneg delta
    nlinarith
  have hsecond :
      (1 + delta) *
          ((((T - 1 : Nat) : K)) * delta + (1 / 2 : K)) <=
        (1 + delta) * (alpha - delta + (1 / 2 : K)) := by
    apply mul_le_mul_of_nonneg_left ?_ hbase_nonneg
    rw [hT_cast_sub]
    linarith
  have hthird :
      (1 / 2 : K) * (1 + delta) * (1 + delta) ^ (T - 1) <=
        (1 + delta) *
          ((((T - 1 : Nat) : K)) * delta + (1 / 2 : K)) := by
    have hscaled :=
      mul_le_mul_of_nonneg_left hpow hhalf_base_nonneg
    calc
      (1 / 2 : K) * (1 + delta) * (1 + delta) ^ (T - 1) <=
          (1 / 2 : K) * (1 + delta) *
            (1 + 2 * (((T - 1 : Nat) : K)) * delta) := hscaled
      _ = (1 + delta) *
            ((((T - 1 : Nat) : K)) * delta + (1 / 2 : K)) := by ring
  have hpow_succ :
      (1 + delta) ^ T = (1 + delta) * (1 + delta) ^ (T - 1) := by
    cases T with
    | zero => omega
    | succ T' =>
        simp [pow_succ]
        ring
  calc
    (1 / 2 : K) * (1 + delta) ^ T =
        (1 / 2 : K) * ((1 + delta) * (1 + delta) ^ (T - 1)) := by
          rw [hpow_succ]
    _ = (1 / 2 : K) * (1 + delta) * (1 + delta) ^ (T - 1) := by ring
    _ <= (1 + delta) *
        ((((T - 1 : Nat) : K)) * delta + (1 / 2 : K)) := hthird
    _ <= (1 + delta) * (alpha - delta + (1 / 2 : K)) := hsecond
    _ <= 1 - (1 - alpha - (1 / 2 : K)) * (1 + delta) := hfirst

-- Batch 5 promoted from Staging/sum_range_terminal_geometric_sub_eq_tail_add_scaled_sum.lean
/-- A terminal-adjusted geometric subtraction sum expands into a tail mass plus
a scaled geometric prefix sum.

For a positive finite window, keep the terminal summand `base^(N-1)` unchanged
and use `base^k - c * base^(k+1)` at every earlier index. The total equals the
terminal correction `c * base^N` plus `(1 - c * base)` times the ordinary
geometric range sum.

Layer: Glue | Gap: Level 1 (terminal-adjusted geometric finite-sum rewrite)
Proof: split a positive range as `range (N + 1)`, identify all previous
  indices as nonterminal, shift the geometric powers by one factor of `base`,
  and finish by ring normalization.
Source: Mathlib finite sums over natural ranges, natural powers in rings, and
  ring normalization
Used in: variance-reduced accelerated gradient descent tail-output weight
  normalization before the small-epoch scalar telescope
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/key_lemmas/15/proof
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem sum_range_terminal_geometric_sub_eq_tail_add_scaled_sum
    {R : Type*} [Ring R] (N : Nat) (base c : R) (hN : 0 < N) :
    (Finset.range N).sum
        (fun k => if k + 1 = N then base ^ k else base ^ k - c * base ^ (k + 1)) =
      c * base ^ N + (1 - c * base) *
        (Finset.range N).sum (fun k => base ^ k) := by
  cases N with
  | zero =>
      omega
  | succ N =>
      have hprev_ne_top :
          forall k, k < N -> Not (k + 1 = N + 1) := by
        intro k hk
        omega
      have hprev :
          (Finset.range N).sum
              (fun k =>
                if k + 1 = N + 1 then base ^ k else base ^ k - c * base ^ (k + 1)) =
            (Finset.range N).sum (fun k => base ^ k - c * base ^ (k + 1)) := by
        refine Finset.sum_congr rfl ?_
        intro k hk
        rw [if_neg (hprev_ne_top k (Finset.mem_range.mp hk))]
      have hshift :
          (Finset.range N).sum (fun k => base ^ (k + 1)) =
            base * (Finset.range N).sum (fun k => base ^ k) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro k _hk
        rw [pow_succ']
      have hshift_c :
          (Finset.range N).sum (fun k => c * base ^ (k + 1)) =
            c * (base * (Finset.range N).sum (fun k => base ^ k)) := by
        rw [hshift.symm]
        rw [Finset.mul_sum]
      rw [Finset.sum_range_succ]
      rw [if_pos rfl]
      rw [hprev]
      rw [Finset.sum_sub_distrib]
      rw [hshift_c]
      rw [Finset.sum_range_succ]
      rw [pow_succ']
      noncomm_ring

-- Batch 5 promoted from Staging/two_pow_floor_log_div_log_two_le_self.lean
/-- The base-two power at the natural floor of `log m / log 2` is at most `m`.

For any real scale at least one, the largest dyadic epoch length selected by
the real floor-log expression is bounded by the scale itself.

Layer: Glue | Gap: Level 0 (real floor-log dyadic power bound)
Proof: rewrite `log m / log 2` as `Real.logb 2 m`, use nonnegativity to compare
  the natural floor with the real logarithm, and convert back through
  `Real.le_logb_iff_rpow_le`.
Source: Mathlib real logarithm-base and natural floor APIs
Used in: variance-reduced accelerated finite-sum cutoff algebra bounding the
  last doubling epoch length by the component count
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem two_pow_floor_log_div_log_two_le_self
    {m : ℝ} (hm : (1 : ℝ) ≤ m) :
    (2 : ℝ) ^ Nat.floor (Real.log m / Real.log 2) ≤ m := by
  let k : ℕ := Nat.floor (Real.log m / Real.log 2)
  have hm_pos : 0 < m := zero_lt_one.trans_le hm
  have hlogb_eq : Real.log m / Real.log 2 = Real.logb 2 m := by
    rw [Real.log_div_log]
  have hlogb_nonneg : 0 ≤ Real.logb 2 m :=
    Real.logb_nonneg (by norm_num) hm
  have hk_le_logb : (k : ℝ) ≤ Real.logb 2 m := by
    have hfloor_le := Nat.floor_le hlogb_nonneg
    simpa [k, hlogb_eq] using hfloor_le
  have hpow_le : (2 : ℝ) ^ (k : ℝ) ≤ m := by
    exact
      (Real.le_logb_iff_rpow_le (b := (2 : ℝ)) (by norm_num) hm_pos).mp
        hk_le_logb
  simpa [k, Real.rpow_natCast] using hpow_le

-- Batch 5 promoted from Staging/div_sq_add_mul_le_of_sqrt_le_nat.lean
/-- A square-root natural selector controls a shifted squared-denominator rate.

If a natural offset `q` is at least `sqrt (a / (m * eps))`, then any positive
shift `c` in the squared denominator leaves the rate `a / (((q + c)^2) * m)`
bounded by `eps`.

Layer: Glue | Gap: Level 0 (square-root selector denominator inversion)
Proof: square the nonnegative square-root comparison, clear the positive
  `m * eps` denominator, dominate `q^2` by `(q + c)^2`, and clear the final
  positive denominator.
Source: Mathlib real square-root and ordered-field arithmetic APIs
Used in: variance-reduced accelerated finite-sum smooth-case selector inversion
  from an epoch offset lower bound to an expected objective-gap tolerance
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/key_lemmas/10/proof/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem div_sq_add_mul_le_of_sqrt_le_nat
    {a m eps c : ℝ} {q : ℕ}
    (ha_nonneg : 0 ≤ a) (hm_pos : 0 < m) (heps_pos : 0 < eps)
    (hc_pos : 0 < c)
    (hq : Real.sqrt (a / (m * eps)) ≤ (q : ℝ)) :
    a / ((((q : ℝ) + c) ^ 2) * m) ≤ eps := by
  have hx_nonneg : 0 ≤ a / (m * eps) := by
    positivity
  have hq_sq_ge_x : a / (m * eps) ≤ (q : ℝ) ^ 2 := by
    have hs := Real.sq_sqrt hx_nonneg
    have hsqrt_nonneg : 0 ≤ Real.sqrt (a / (m * eps)) :=
      Real.sqrt_nonneg _
    nlinarith
  have hden_x_pos : 0 < m * eps := mul_pos hm_pos heps_pos
  have hclear : a ≤ (q : ℝ) ^ 2 * (m * eps) := by
    have := (div_le_iff₀ hden_x_pos).1 hq_sq_ge_x
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  have hq_nonneg : 0 ≤ (q : ℝ) := by
    exact_mod_cast Nat.zero_le q
  have hq_sq_le_qc_sq : (q : ℝ) ^ 2 ≤ ((q : ℝ) + c) ^ 2 := by
    nlinarith [mul_nonneg hq_nonneg (le_of_lt hc_pos), sq_nonneg c]
  have hclear_shift : a ≤ ((q : ℝ) + c) ^ 2 * (m * eps) := by
    have hmul := mul_le_mul_of_nonneg_right hq_sq_le_qc_sq (le_of_lt hden_x_pos)
    exact hclear.trans hmul
  have hden_pos : 0 < (((q : ℝ) + c) ^ 2 * m) := by
    have hqc_pos : 0 < (q : ℝ) + c := by
      linarith
    exact mul_pos (sq_pos_of_pos hqc_pos) hm_pos
  rw [div_le_iff₀ hden_pos]
  calc
    a ≤ ((q : ℝ) + c) ^ 2 * (m * eps) := hclear_shift
    _ = eps * ((((q : ℝ) + c) ^ 2) * m) := by ring

-- Batch 5 promoted from Staging/Icc_retained_weighted_gap_telescope_le.lean
/-- A one-step scalar recurrence telescopes with retained middle gap weights.

If `L r * Gap r + B r <= R r * Gap (r - 1) + B (r - 1)` for every positive
time, then summing from `1` to `s` retains the intermediate weights
`(L j - R (j + 1)) * Gap j` over `Icc 1 (s - 1)` and leaves the initial
right coefficient and budget.

Layer: Glue | Gap: Level 1 (retained scalar Lyapunov recurrence telescope)
Proof: induction on the terminal index. The successor step splits the closed
  interval at the top index, exposes the retained middle coefficient, and
  combines it with the one-step recurrence by ordered-ring arithmetic.
Source: Mathlib finite sums over natural intervals and ordered-ring arithmetic
Used in: variance-reduced accelerated gradient descent epoch Lyapunov chain
  before dropping or comparing retained cross-epoch objective-gap weights
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem Icc_retained_weighted_gap_telescope_le
    {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (L Rcoeff Gap B : ℕ → R) (s : ℕ) (hs : 1 ≤ s)
    (hstep :
      ∀ r, 1 ≤ r →
        L r * Gap r + B r ≤ Rcoeff r * Gap (r - 1) + B (r - 1)) :
    L s * Gap s +
        (Finset.Icc 1 (s - 1)).sum
          (fun j => (L j - Rcoeff (j + 1)) * Gap j) +
        B s ≤
      Rcoeff 1 * Gap 0 + B 0 := by
  classical
  refine Nat.le_induction ?base ?succ s hs
  · simpa using hstep 1 le_rfl
  · intro n hn ih
    have hstep_top := hstep (n + 1) (by omega)
    have hsum_succ :
        (Finset.Icc 1 n).sum (fun j => (L j - Rcoeff (j + 1)) * Gap j) =
          (Finset.Icc 1 (n - 1)).sum
              (fun j => (L j - Rcoeff (j + 1)) * Gap j) +
            (L n - Rcoeff (n + 1)) * Gap n := by
      rw [show n = (n - 1) + 1 by omega]
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n - 1 + 1)]
      simp
    have hbridge :
        L (n + 1) * Gap (n + 1) +
              (Finset.Icc 1 n).sum
                (fun j => (L j - Rcoeff (j + 1)) * Gap j) +
              B (n + 1) ≤
            L n * Gap n +
              (Finset.Icc 1 (n - 1)).sum
                (fun j => (L j - Rcoeff (j + 1)) * Gap j) +
              B n := by
      rw [hsum_succ]
      have hstep_top' :
          L (n + 1) * Gap (n + 1) + B (n + 1) ≤
            Rcoeff (n + 1) * Gap n + B n := by
        simpa using hstep_top
      nlinarith
    exact hbridge.trans ih

-- Batch 5 promoted from Staging/mul_sqrt_const_div_mul_le_sqrt_mul_div.lean
/-- A square-root factor normalized by a positive multiplicative scale.

For nonnegative `K` and `D`, multiplying `sqrt (K * D / (m * eps))` by a
positive scale `m` is bounded by the product of the constant square root and
the normalized rate `sqrt (m * D / eps)`.

Layer: Glue | Gap: Level 0 (square-root product/division normalization)
Proof: square the two nonnegative sides, rewrite square roots with
  `Real.sq_sqrt`, clear the positive denominators, and finish by field
  normalization.
Source: Mathlib real square-root and ordered-field arithmetic APIs
Used in: variance-reduced accelerated finite-sum high-accuracy complexity
  display converting a generated square-root epoch length to the printed
  component-gradient rate
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem mul_sqrt_const_div_mul_le_sqrt_mul_div
    {m D eps K : Real}
    (hm_pos : 0 < m) (hD_nonneg : 0 <= D) (heps_pos : 0 < eps)
    (hK_nonneg : 0 <= K) :
    m * Real.sqrt (K * D / (m * eps)) <=
      Real.sqrt K * Real.sqrt (m * D / eps) := by
  have hleft_nonneg : 0 <= m * Real.sqrt (K * D / (m * eps)) := by
    positivity
  have hright_nonneg : 0 <= Real.sqrt K * Real.sqrt (m * D / eps) := by
    positivity
  rw [← sq_le_sq₀ hleft_nonneg hright_nonneg]
  have harg_left : 0 <= K * D / (m * eps) := by
    positivity
  have harg_right : 0 <= m * D / eps := by
    positivity
  rw [mul_pow, Real.sq_sqrt harg_left, mul_pow, Real.sq_sqrt hK_nonneg,
    Real.sq_sqrt harg_right]
  field_simp [ne_of_gt hm_pos, ne_of_gt heps_pos]
  ring_nf
  exact le_rfl

-- Batch 5 promoted from Staging/half_le_two_pow_floor_log_div_log_two.lean
/-- The dyadic power selected by `floor (log m / log 2)` is at least half of `m`.

For any positive real scale, the base-two floor-log selector chooses a natural
dyadic size whose successor dyadic size strictly exceeds the scale.

Layer: Glue | Gap: Level 0 (real floor-log dyadic half lower bound)
Proof: rewrite `log m / log 2` as `Real.logb 2 m`, use the strict upper
  bound on `Nat.floor`, convert through `Real.logb_lt_iff_lt_rpow`, and cast
  the successor dyadic power back to a natural power.
Source: Mathlib real logarithm-base and natural floor APIs
Used in: variance-reduced accelerated finite-sum cutoff algebra lower-bounding
  the last doubling epoch length by half the component count
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem half_le_two_pow_floor_log_div_log_two
    (m : ℝ) (hm : 0 < m) :
    m / 2 ≤ (((2 : ℕ) ^ Nat.floor (Real.log m / Real.log 2) : ℕ) : ℝ) := by
  let k : ℕ := Nat.floor (Real.log m / Real.log 2)
  have hlogb_eq : Real.log m / Real.log 2 = Real.logb 2 m := by
    rw [Real.log_div_log]
  have hfloor_lt : Real.logb 2 m < (k : ℝ) + 1 := by
    have hraw := Nat.lt_floor_add_one (Real.log m / Real.log 2)
    simpa [k, hlogb_eq] using hraw
  have hm_lt_pow : m < (2 : ℝ) ^ ((k : ℝ) + 1) := by
    exact (Real.logb_lt_iff_lt_rpow (b := (2 : ℝ)) (by norm_num) hm).mp
      hfloor_lt
  have hpow_succ_cast :
      (2 : ℝ) ^ ((k : ℝ) + 1) =
        2 * (((2 : ℕ) ^ k : ℕ) : ℝ) := by
    rw [show (k : ℝ) + 1 = ((k + 1 : ℕ) : ℝ) by norm_num]
    rw [Real.rpow_natCast]
    rw [show k + 1 = Nat.succ k by omega, pow_succ]
    have hcast_pow : (2 : ℝ) ^ k = (((2 : ℕ) ^ k : ℕ) : ℝ) := by
      norm_num [Nat.cast_pow]
    rw [hcast_pow]
    rw [mul_comm]
  rw [hpow_succ_cast] at hm_lt_pow
  have hhalf_lt : m / 2 < (((2 : ℕ) ^ k : ℕ) : ℝ) := by
    rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)]
    nlinarith
  exact le_of_lt (by simpa [k] using hhalf_lt)

-- Batch 5 promoted from Staging/two_div_le_sqrt_of_sqrt_lt_of_mul_eq_four.lean
/-- A reciprocal offset is bounded by a square-root branch under product normalization.

If `A * B = 4` and the reciprocal-side square-root scale satisfies
`sqrt B < d`, then the positive reciprocal `2 / d` is at most `sqrt A`.

Layer: Glue | Gap: Level 0 (reciprocal square-root product normalization)
Proof: convert `sqrt B < d` into `B < d^2`, multiply by the positive `A`, clear
  the positive denominator in `(2 / d)^2 <= A`, and apply the real square-root
  order criterion.
Source: Mathlib real square-root and ordered-field arithmetic APIs
Used in: variance-reduced accelerated finite-sum tail-regime alpha branch
  selection from a reciprocal epoch offset
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/key_lemmas/10/proof/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem two_div_le_sqrt_of_sqrt_lt_of_mul_eq_four
    {A B d : ℝ}
    (hB_nonneg : 0 <= B) (hd_pos : 0 < d)
    (hsqrtB_lt_d : Real.sqrt B < d)
    (hAB : A * B = 4) :
    2 / d <= Real.sqrt A := by
  have hA_pos : 0 < A := by
    by_contra hA_not_pos
    have hA_nonpos : A <= 0 := le_of_not_gt hA_not_pos
    have hmul_nonpos : A * B <= 0 :=
      mul_nonpos_of_nonpos_of_nonneg hA_nonpos hB_nonneg
    rw [hAB] at hmul_nonpos
    norm_num at hmul_nonpos
  have hB_lt_dsq : B < d ^ 2 := by
    exact (Real.sqrt_lt hB_nonneg (le_of_lt hd_pos)).mp hsqrtB_lt_d
  have hfour_lt_Adsq : 4 < A * d ^ 2 := by
    calc
      (4 : ℝ) = A * B := by rw [hAB]
      _ < A * d ^ 2 := mul_lt_mul_of_pos_left hB_lt_dsq hA_pos
  have hsq_le : (2 / d) ^ 2 <= A := by
    rw [div_pow]
    rw [div_le_iff₀ (sq_pos_of_pos hd_pos)]
    nlinarith [hfour_lt_Adsq]
  have hleft_pos : 0 < 2 / d := div_pos (by norm_num) hd_pos
  rw [Real.le_sqrt' hleft_pos]
  exact hsq_le

-- Batch 5 promoted from Staging/sum_Icc_refresh_add_epochLength_le_two_mul_refresh_mul_epochs.lean
/-- A one-based sum of refresh costs plus bounded epoch lengths is at most
twice the refresh cost per epoch.

For epochs `1, ..., Smax`, each summand pays a fixed `refresh` cost plus a
variable `epochLength s`. If every epoch length in the interval is at most
`refresh`, the whole natural-number sum, cast to `Real`, is bounded by
`2 * refresh * Smax`.

Layer: Glue | Gap: Level 0 (variable-epoch finite-sum interval accounting)
Proof: bound each summand by `2 * refresh`, sum the pointwise inequalities, and
  use the cardinality of `Finset.Icc 1 Smax`.
Source: Mathlib finite sums over natural intervals, natural-number casts, and
  ordered-ring arithmetic
Used in: variance-reduced accelerated-gradient component-gradient accounting
  after proving each variable inner epoch is no longer than a full refresh
Book citation: book/FOML/VarianceReducedAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, variance-reduced accelerated gradient descent -/
theorem sum_Icc_refresh_add_epochLength_le_two_mul_refresh_mul_epochs
    (refresh Smax : Nat) (epochLength : Nat → Nat)
    (h_epochLength_le :
      ∀ s, s ∈ Finset.Icc 1 Smax → (epochLength s : ℝ) ≤ (refresh : ℝ)) :
    (((Finset.Icc 1 Smax).sum (fun s => refresh + epochLength s) : Nat) : ℝ) ≤
      2 * (refresh : ℝ) * (Smax : ℝ) := by
  classical
  have hterm :
      ∀ s, s ∈ Finset.Icc 1 Smax →
        ((refresh + epochLength s : Nat) : ℝ) ≤ 2 * (refresh : ℝ) := by
    intro s hs
    have hT := h_epochLength_le s hs
    calc
      ((refresh + epochLength s : Nat) : ℝ) =
          (refresh : ℝ) + (epochLength s : ℝ) := by
            simp [Nat.cast_add]
      _ ≤ (refresh : ℝ) + (refresh : ℝ) := by
            exact add_le_add (le_refl (refresh : ℝ)) hT
      _ = 2 * (refresh : ℝ) := by ring
  have hsum :
      (((Finset.Icc 1 Smax).sum
          (fun s => refresh + epochLength s) : Nat) : ℝ) ≤
        (Finset.Icc 1 Smax).sum (fun _s => 2 * (refresh : ℝ)) := by
    rw [Nat.cast_sum]
    exact Finset.sum_le_sum hterm
  have hcard : (Finset.Icc 1 Smax).card = Smax := by
    rw [Nat.card_Icc]
    omega
  have hconst :
      (Finset.Icc 1 Smax).sum (fun _s => 2 * (refresh : ℝ)) =
        2 * (refresh : ℝ) * (Smax : ℝ) := by
    simp [hcard, mul_comm, mul_left_comm]
  simpa [hconst] using hsum

end SOptLib

-- Generalization plan (G0):
-- concept/name: ordered-field right-limit removal of a positive secant factor;
--   orig was dualBregman_cross_limit_block and renamed away from Bregman/paper
--   terminology to expose the scalar order lemma.
-- generality used: ordered field scalars only; no measure, convexity, smoothness,
--   oracle, normed-space, or finite-dimensional assumptions are used.
-- portable call pattern: convex-analysis secant-limit steps in mirror descent,
--   primal-dual, and proximal proofs can instantiate `A` and `B` after proving
--   `A * (1 - s) <= B` for every `0 < s <= 1`.
-- counterargument checked: the proof is short but not a pure rename; it packages
--   a recurring positive secant-factor removal by contradiction.
-- coverage search: searched SOptLib catalog/source and Mathlib source for
--   `le_of_forall_pos_le_add`, `one_sub`, `mul_one_sub`, and forall-positive
--   one-sided limit shapes; hits expose the epsilon principle but not this
--   secant-factor specialization.
-- minimal hypotheses: `hsecant 1` gives `0 <= B`, which is enough for the
--   contradiction argument; the quantified hypothesis already has minimal
--   pointwise interval assumptions.

/-- Remove a vanishing right-secancy factor from an ordered-field upper bound.

If `A * (1 - s) <= B` for every `s` with `0 < s <= 1`, then sending `s`
to zero from the right gives `A <= B`.

Layer: Glue | Gap: Level 0 (one-sided secant-factor limit)
Proof: argue by contradiction with `s = (A - B) / (2 * A)`; `hsecant 1`
  gives `0 <= B`, so `B < A` implies `0 < A`, and the resulting secant
  inequality simplifies to `A <= B`.
Source: Mathlib ordered field arithmetic APIs
Used in: random primal-dual gradient dual Bregman cross-term lower bound
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
theorem le_of_forall_pos_le_one_mul_one_sub_le {K : Type*}
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] {A B : K}
    (hsecant : ∀ s : K, 0 < s → s ≤ 1 → A * (1 - s) ≤ B) :
    A ≤ B := by
  by_contra hle
  have hBA : B < A := not_le.mp hle
  have hB_nonneg : 0 ≤ B := by
    simpa using hsecant 1 zero_lt_one le_rfl
  have hA_pos : 0 < A := lt_of_le_of_lt hB_nonneg hBA
  have hAB_pos : 0 < A - B := sub_pos.mpr hBA
  have hden_pos : 0 < 2 * A := mul_pos two_pos hA_pos
  let s : K := (A - B) / (2 * A)
  have hspos : 0 < s := by
    dsimp [s]
    exact div_pos hAB_pos hden_pos
  have hsle : s ≤ 1 := by
    dsimp [s]
    rw [div_le_one₀ hden_pos]
    · nlinarith [hB_nonneg]
  have hs_bound := hsecant s hspos hsle
  have hs_eq : A * (1 - s) = (A + B) / 2 := by
    dsimp [s]
    field_simp [hA_pos.ne']
    ring
  nlinarith [hs_bound, hs_eq]

open scoped BigOperators InnerProductSpace

-- Generalization plan (G0):
-- concept/name: finite weighted-sum expansion for the left slot of a real inner product;
--   orig was `finset_inner_sum_smul_left_eq_sum_mul_inner`, renamed away from
--   implementation-local `finset_` prefix while preserving the Mathlib-style
--   `inner_sum`/`smul` vocabulary.
-- generality used: arbitrary finite index type, real weights, vector family, and
--   comparator in a real inner-product space with `[SeminormedAddCommGroup E]`
--   and `[InnerProductSpace Real E]`; no measure, filtration, convexity,
--   smoothness, oracle, completeness, or finite-dimensional assumptions are used.
-- portable call pattern: weighted-output affine proofs in stochastic primal-dual,
--   mirror-descent, coordinate, and mini-batch methods vary the finite index set,
--   weights, vector family, and comparator while preserving this left-slot
--   inner-product expansion.
-- counterargument checked: the proof is short and composes Mathlib `sum_inner`
--   with `inner_smul_left`, but it is not a pure rename of one Mathlib theorem;
--   Mathlib supplies the unweighted finite-sum expansion and single scalar
--   rule separately, while this statement packages the weighted Finset form used
--   directly at algorithm call sites.
-- coverage search: searched CATALOG.md/SOptLib/Staging for `inner_sum`,
--   `sum_inner`, `weighted_inner`, and `sum_smul`; the closest SOptLib hit was
--   `Finset.weighted_inner_sum_eq_zero_of_weighted_sum_eq_zero`, which assumes
--   a weighted vector sum is zero and proves a zero scalar conclusion rather
--   than this equality. LeanSearch for "inner product of finite sum of scalar
--   multiples equals sum of scalars times inner products" returned Mathlib
--   `inner_sum`, `sum_inner`, `inner_smul_real_left`, and Finsupp variants, but
--   no direct Finset weighted left-slot equality.
-- minimal hypotheses: strengthened from the algorithm context to the Mathlib
--   primitive level; `[SeminormedAddCommGroup E]` and `[InnerProductSpace Real E]`
--   are exactly what `sum_inner` and left-slot scalar linearity require.

/-- The inner product of a weighted finite sum in the left slot is the weighted
sum of the corresponding inner products.

Layer: Glue | Gap: Level 0 (finite weighted inner-product expansion)
Proof: commute the finite sum out of the left slot with `sum_inner`, then
  simplify each scalar multiple by left-slot scalar linearity of the real inner
  product.
Source: Mathlib finite sums and real inner-product space algebra
Used in: stochastic primal-dual weighted-output affine saddle-gap expansion
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
theorem inner_sum_smul_left_eq_sum_mul_inner
    {β E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace Real E]
    (s : Finset β) (c : β -> Real) (v : β -> E) (u : E) :
    ⟪∑ i ∈ s, c i • v i, u⟫_Real =
      ∑ i ∈ s, c i * ⟪v i, u⟫_Real := by
  rw [sum_inner]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  simp [inner_smul_left]

open scoped BigOperators InnerProductSpace

-- Generalization plan (G0):
-- concept/name: finite weighted-sum expansion for the right slot of an inner product;
--   orig was `finset_inner_sum_smul_right_eq_sum_mul_inner`, renamed away from
--   implementation-local `finset_` prefix while preserving the Mathlib-style
--   `inner_sum`/`smul` vocabulary.
-- generality used: arbitrary finite index type, `RCLike` weights, vector family, and
--   comparator in an inner-product space with `[SeminormedAddCommGroup E]`
--   and `[InnerProductSpace 𝕜 E]`; no measure, filtration, convexity,
--   smoothness, oracle, completeness, or finite-dimensional assumptions are used.
-- portable call pattern: weighted-output affine proofs in stochastic primal-dual,
--   mirror-descent, coordinate, and mini-batch methods vary the finite index set,
--   weights, vector family, and comparator while preserving this right-slot
--   inner-product expansion.
-- counterargument checked: the proof is short and composes Mathlib `inner_sum`
--   with `inner_smul_right`, but it is not a pure rename of one Mathlib theorem;
--   Mathlib supplies the unweighted finite-sum expansion and single scalar
--   rule separately, while this statement packages the weighted Finset form used
--   directly at algorithm call sites. The already-staged left-slot companion is
--   structurally different because it expands the first argument of `inner`.
-- coverage search: searched CATALOG.md/SOptLib/Staging for `inner_sum`,
--   `sum_inner`, `weighted_inner`, and `sum_smul`; the closest SOptLib hit was
--   `Finset.weighted_inner_sum_eq_zero_of_weighted_sum_eq_zero`, which assumes
--   a weighted vector sum is zero and proves a zero scalar conclusion rather
--   than this equality. LeanSearch for "inner product finite sum scalar
--   multiples right slot equals sum scalar times inner product" returned Mathlib
--   `inner_sum`, `inner_smul_right`, and `Finsupp.inner_sum`, but no direct
--   Finset weighted right-slot equality.
-- minimal hypotheses: strengthened from the algorithm context to the Mathlib
--   primitive level; `[RCLike 𝕜]`, `[SeminormedAddCommGroup E]`, and
--   `[InnerProductSpace 𝕜 E]`
--   are exactly what `inner_sum` and right-slot scalar linearity require.

/-- The inner product of a weighted finite sum in the right slot is the weighted
sum of the corresponding inner products.

Layer: Glue | Gap: Level 0 (finite weighted inner-product expansion)
Proof: commute the finite sum out of the right slot with `inner_sum`, then
  simplify each scalar multiple by right-slot scalar linearity of the real inner
  product.
Source: Mathlib finite sums and real inner-product space algebra
Used in: stochastic primal-dual weighted-output affine saddle-gap expansion
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
theorem inner_sum_smul_right_eq_sum_mul_inner
    {𝕜 β E : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (s : Finset β) (u : E) (c : β -> 𝕜) (v : β -> E) :
    ⟪u, ∑ i ∈ s, c i • v i⟫_𝕜 =
      ∑ i ∈ s, c i * ⟪u, v i⟫_𝕜 := by
  rw [inner_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  simp [inner_smul_right]

open scoped InnerProductSpace

-- Generalization plan (G0):
-- concept/name: affine-offset linearity for a real inner product; orig was the
--   local `hrewrite` block inside a dual-conjugate convexity proof, renamed to
--   expose the weighted affine combination and shared constant subtraction.
-- generality used: arbitrary real inner-product space via
--   `SeminormedAddCommGroup` and `InnerProductSpace`; no measure, convexity,
--   smoothness, oracle, completeness, or finite-dimensional hypotheses are used.
-- portable call pattern: support-function, Fenchel-conjugate, and affine
--   finite-average convexity proofs vary the probe vector, endpoints, weights,
--   and shared offset while preserving the same scalarized affine rewrite.
-- counterargument checked: this is a short wrapper over `inner_add_right`,
--   `inner_smul_right`, and `ring`, but not a pure rename of one Mathlib or
--   SOptLib theorem; it packages the recurring compound rewrite that turns a
--   supremum/Fenchel pointwise bound for a mixed vector into weighted endpoint
--   bounds.
-- coverage search: searched catalog/project for `inner_affine`,
--   `affine_sub_const`, `weighted_sub`, `inner sub const`, and `weighted inner`;
--   closest SOptLib hits were finite weighted inner-sum expansion lemmas and
--   `inner_lineMap_sub_right_sub_eq`, which cover finite sums or line-map
--   displacement rather than this two-weight shared-offset equality. LeanSearch
--   for the natural-language statement returned affine-combination and
--   `inner_sum` ingredients, not a full duplicate.
-- minimal hypotheses: all already minimal for the intended real optimization
--   API; the proof only uses additive-group/module structure supplied by a real
--   inner-product space and the scalar field is fixed to `ℝ` by the call sites.

/-- A shared constant offset distributes across a two-point affine inner-product
combination.

When two real weights sum to one, subtracting the same scalar from the inner
product against their affine combination equals the corresponding weighted sum
of the two offset inner products.

Layer: Glue | Gap: Level 0 (affine inner-product offset rewrite)
Proof: expand the right slot with `inner_add_right` and `inner_smul_right`,
  replace the shared offset by `(a + b) * c`, and normalize with ring algebra.
Source: Mathlib real inner-product linearity and commutative ring normalization
Used in: random primal-dual gradient Fenchel-conjugate convexity for mixed dual
  points, and reusable support-function convexity rewrites
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
theorem inner_affine_sub_const_eq_weighted_sub
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y₁ y₂ : E) (a b c : ℝ) (hab : a + b = 1) :
    ⟪x, a • y₁ + b • y₂⟫_ℝ - c =
      a * (⟪x, y₁⟫_ℝ - c) + b * (⟪x, y₂⟫_ℝ - c) := by
  calc
    ⟪x, a • y₁ + b • y₂⟫_ℝ - c =
        a * ⟪x, y₁⟫_ℝ + b * ⟪x, y₂⟫_ℝ - c := by
      simp [inner_add_right, inner_smul_right]
    _ = a * ⟪x, y₁⟫_ℝ + b * ⟪x, y₂⟫_ℝ - (a + b) * c := by
      rw [hab]
      ring
    _ = a * (⟪x, y₁⟫_ℝ - c) + b * (⟪x, y₂⟫_ℝ - c) := by
      ring

open scoped BigOperators

-- Generalization plan (G0):
-- concept/name: normalized finite weighted-average squared-distance Jensen bound; orig was
--   norm_sq_weighted_average_sub_le_weighted_sum.
-- generality used: finite index set, nonnegative real weights, positive real
--   normalizer, and a real normed-space-valued family; no measure, smoothness,
--   oracle, inner product, completeness, or finite-dimensional assumptions are used.
-- portable call pattern: weighted-output and averaged-iterate convergence proofs
--   call this after identifying an output point as a normalized weighted sum;
--   the time window, weights, iterate family, reference point, and normalizer
--   vary while the squared-distance bound has the same shape.
-- counterargument checked: not paper-local traceability and not a pure wrapper;
--   it packages the nonuniform norm-square Jensen step directly. Mathlib Jensen
--   can derive related scalar convex-function bounds, but does not provide this
--   normalized squared-distance theorem in the required call shape.
-- coverage search: searched CATALOG.md/SOptLib for weighted average norm square,
--   norm_sq, weighted variance, and Jensen; relevant partial hits were
--   norm_sq_inv_card_smul_sum_le_inv_card_mul_sum_norm_sq,
--   finset_weighted_variance_eq_second_moment_sub_norm_mean_sq,
--   Finset.weighted_variance_le_second_moment, weighted_sq_norm_sub_center_le,
--   and convexOn_weighted_average_le_weighted_sum. LeanSearch returned
--   ConvexOn.map_centerMass_le and ConvexOn.map_sum_le as partial Mathlib
--   Jensen APIs, not this squared-distance normalized-weight theorem.
-- minimal hypotheses: the carrier is any real seminormed normed space; no
--   inner product, finite-dimensional, completeness, measure, or topology
--   hypothesis is used.

/-- The squared distance from a normalized finite weighted average is bounded by
the normalized weighted sum of squared distances.

For nonnegative weights with positive total normalizer `W`, if `xbar` is the
corresponding normalized weighted average of `p`, then its squared distance to
`z` is at most the normalized weighted second moment about `z`.

Layer: Glue | Gap: Level 1 (finite weighted squared-distance Jensen bound)
Proof: normalize the weights by `W`, rewrite the displacement from `z` as
  the normalized weighted mean of displacements, use the norm triangle
  inequality, then apply scalar weighted Jensen to the square function.
Source: Mathlib finite sums, normed-space triangle inequalities, and scalar
  weighted mean inequalities
Used in: randomized primal-dual gradient weighted-output squared-distance
  control, and future averaged-iterate convergence bounds with nonuniform
  output weights
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec/output/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized primal-dual gradient -/
theorem norm_sq_weighted_average_sub_le_inv_mul_sum
    {κ E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Finset κ) (γ : κ → ℝ) (p : κ → E)
    (xbar z : E) (W : ℝ)
    (hγ_nonneg : ∀ i ∈ s, 0 ≤ γ i)
    (hW_pos : 0 < W)
    (hW_eq : W = ∑ i ∈ s, γ i)
    (hxbar : xbar = W⁻¹ • ∑ i ∈ s, γ i • p i) :
    ‖xbar - z‖ ^ 2 ≤
      W⁻¹ * ∑ i ∈ s, γ i * ‖p i - z‖ ^ 2 := by
  classical
  let q : κ → ℝ := fun i => W⁻¹ * γ i
  have hW_ne : W ≠ 0 := ne_of_gt hW_pos
  have hqsum : ∑ i ∈ s, q i = 1 := by
    calc
      ∑ i ∈ s, q i = W⁻¹ * ∑ i ∈ s, γ i := by
        simp [q, Finset.mul_sum]
      _ = W⁻¹ * W := by rw [← hW_eq]
      _ = 1 := inv_mul_cancel₀ hW_ne
  have hq_nonneg : ∀ i ∈ s, 0 ≤ q i := by
    intro i hi
    exact mul_nonneg (inv_nonneg.mpr hW_pos.le) (hγ_nonneg i hi)
  have hsum_q_smul_p :
      (∑ i ∈ s, q i • p i) = W⁻¹ • ∑ i ∈ s, γ i • p i := by
    calc
      (∑ i ∈ s, q i • p i) =
          ∑ i ∈ s, (W⁻¹ * γ i) • p i := by
            simp [q]
      _ = ∑ i ∈ s, W⁻¹ • (γ i • p i) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            simp [smul_smul]
      _ = W⁻¹ • ∑ i ∈ s, γ i • p i := by
            rw [Finset.smul_sum]
  have hsum_q_smul_z :
      (∑ i ∈ s, q i • z) = z := by
    calc
      (∑ i ∈ s, q i • z) = (∑ i ∈ s, q i) • z := by
        rw [Finset.sum_smul]
      _ = z := by rw [hqsum, one_smul]
  have hmean : (∑ i ∈ s, q i • (p i - z)) = xbar - z := by
    calc
      (∑ i ∈ s, q i • (p i - z)) =
          ∑ i ∈ s, (q i • p i - q i • z) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            simp [smul_sub]
      _ = (∑ i ∈ s, q i • p i) - (∑ i ∈ s, q i • z) := by
            rw [Finset.sum_sub_distrib]
      _ = W⁻¹ • ∑ i ∈ s, γ i • p i - z := by
            rw [hsum_q_smul_p, hsum_q_smul_z]
      _ = xbar - z := by
            rw [← hxbar]
  have hnorm_le :
      ‖xbar - z‖ ≤ ∑ i ∈ s, q i * ‖p i - z‖ := by
    calc
      ‖xbar - z‖ = ‖∑ i ∈ s, q i • (p i - z)‖ := by
        rw [hmean]
      _ ≤ ∑ i ∈ s, ‖q i • (p i - z)‖ := by
        simpa using norm_sum_le (s := s) (f := fun i => q i • (p i - z))
      _ = ∑ i ∈ s, q i * ‖p i - z‖ := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [norm_smul, Real.norm_of_nonneg (hq_nonneg i hi)]
  have hnorm_sq_le :
      ‖xbar - z‖ ^ 2 ≤ (∑ i ∈ s, q i * ‖p i - z‖) ^ 2 := by
    nlinarith [hnorm_le, norm_nonneg (xbar - z)]
  have hscalar_sq :
      (∑ i ∈ s, q i * ‖p i - z‖) ^ 2 ≤
        ∑ i ∈ s, q i * ‖p i - z‖ ^ 2 := by
    simpa using
      (Real.pow_arith_mean_le_arith_mean_pow
        (s := s) (w := q) (z := fun i => ‖p i - z‖)
        hq_nonneg hqsum (fun i _hi => norm_nonneg (p i - z)) 2)
  have hweighted_le :
      ‖xbar - z‖ ^ 2 ≤ ∑ i ∈ s, q i * ‖p i - z‖ ^ 2 :=
    le_trans hnorm_sq_le hscalar_sq
  have hright :
      (∑ i ∈ s, q i * ‖p i - z‖ ^ 2) =
        W⁻¹ * ∑ i ∈ s, γ i * ‖p i - z‖ ^ 2 := by
    calc
      (∑ i ∈ s, q i * ‖p i - z‖ ^ 2) =
          ∑ i ∈ s, W⁻¹ * (γ i * ‖p i - z‖ ^ 2) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            simp [q, mul_assoc]
      _ = W⁻¹ * ∑ i ∈ s, γ i * ‖p i - z‖ ^ 2 := by
            rw [Finset.mul_sum]
  rwa [hright] at hweighted_le

-- Generalization plan (G0):
-- concept/name: `eq_zero_of_pos_mul_norm_sq_le_zero` exposes the
--   positive-quadratic collapse of a displacement from a localized
--   nonpositive budget; orig was the local
--   `quadratic_budget_zero_lipschitz_forces_displacement_zero` pattern.
-- generality used: arbitrary normed additive group `E`, a positive
--   real coefficient `a`, and a pointwise nonpositive bound; no measure,
--   independence, convexity, smoothness, oracle, inner-product, or
--   finite-dimensional hypotheses are used.
-- portable call pattern: degenerate Lipschitz branches in stochastic
--   Young/Bregman budget proofs where a positive quadratic coefficient bounds a
--   displacement by a budget already reduced to zero.
-- counterargument checked: Mathlib has `norm_le_zero_iff` and `norm_eq_zero`,
--   but no lemma combines a positive half-quadratic budget with a zero right
--   scale; SOptLib Young absorption lemmas handle positive Lipschitz branches
--   and do not discharge this degeneracy.
-- coverage search: searched CATALOG/SOptLib/Staging for `half norm sq zero
--   scale`, `eq_zero norm sq`, and `zero Lipschitz quadratic budget`; LeanSearch
--   for the positive-coefficient norm-square collapse returned Mathlib
--   `norm_le_zero_iff`, `norm_eq_zero`, and inner-product nonpositivity lemmas,
--   all partial rather than full.
-- minimal hypotheses: `0 < a` and `a * ‖v‖ ^ 2 ≤ 0` are exactly the localized
--   hypotheses needed for the collapse.

/-- A positive quadratic coefficient with a nonpositive squared-norm budget
forces the displacement to be zero.

If `0 < a` and `a * ‖v‖ ^ 2 ≤ 0`, then the nonnegative squared norm of `v` is
forced to vanish.

Layer: Glue | Gap: Level 0 (zero-scale positive quadratic collapse)
Proof: the product of two positive factors would be positive, contradicting the
  nonpositive budget.
Source: Mathlib normed additive groups and real ordered-ring arithmetic
Used in: randomized primal-dual gradient degenerate Lipschitz branch of
  Young/Bregman absorption
Book citation: book/FOML/RandomPrimalDualGradient.json#/key_lemmas/7/proof/10
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized primal-dual gradient -/
theorem eq_zero_of_pos_mul_norm_sq_le_zero
    {E : Type*} [NormedAddGroup E]
    {a : ℝ} {v : E}
    (ha : 0 < a)
    (h : a * ‖v‖ ^ 2 ≤ 0) :
    v = 0 := by
  by_contra hv
  have hnorm_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hsq_pos : 0 < ‖v‖ ^ 2 := pow_pos hnorm_pos 2
  have hmul_pos : 0 < a * ‖v‖ ^ 2 := mul_pos ha hsq_pos
  nlinarith

open scoped InnerProductSpace

-- Generalization plan (G0):
-- concept/name: inverse_probability_inner_half_absorb_of_quadratic_budget exposes
--   inverse-probability Young absorption with half of a quadratic/Bregman
--   budget; orig was
--   proposition51_dual_young_absorb_inverse_inner_half_with_sourceQuotient.
-- generality used: real scalars and a real inner-product seminormed additive
--   group `[SeminormedAddCommGroup E] [InnerProductSpace ℝ E]`; no measure,
--   independence, convexity, smoothness, oracle, or finite-dimensional
--   hypotheses are used after replacing the Bregman lower bound by the
--   pointwise scalar budget `m / 2 * ‖v‖ ^ 2 ≤ L * W`.
-- portable call pattern: block-sampled primal-dual, randomized coordinate,
--   and variance-reduced mirror/prox proofs vary the block count `m`, step
--   `τ`, probability `p`, local scale `L`, source vector `u`, displacement
--   `v`, and budget value `W`, while reusing the same inverse-probability
--   half-budget Young absorption including the degenerate `L = 0` branch.
-- counterargument checked: not paper-local traceability because the theorem
--   has no setup fields, quotient wrappers, theorem numbers, or algorithm
--   objects; not a pure wrapper because existing positive-`L` Young lemmas do
--   not cover the zero-scale branch forced by the quadratic budget.
-- coverage search: searched CATALOG/SOptLib/Staging for `inverse_probability`,
--   `quadratic_budget`, `young_absorb_inner`, `half budget`, and source
--   quotient terms; closest hits were
--   `young_absorb_inner_of_norm_sq_budget`,
--   `young_absorb_average_inner_with_quadratic_budget`,
--   `young_absorb_two_adjacent_corrections`, and
--   `eq_zero_of_pos_mul_norm_sq_le_zero`, all partial rather than full.
-- minimal hypotheses: positivity of `m`, `τ`, and `p`, nonnegativity of `L`
--   and `W`, and the pointwise quadratic budget are exactly what the proof
--   uses; no `p ≤ 1` or finite-dimensional assumption is needed.

/-- An inverse-probability inner product is absorbed by half of a quadratic budget.

If a displacement has quadratic lower budget
`m / 2 * ‖v‖ ^ 2 ≤ L * W`, then the weighted source term
`-(L * β ^ 2) / (m * τ * p) * ‖u‖ ^ 2` is absorbed by the inverse-probability
inner product plus half of the `τ * W` budget. The statement includes the
degenerate `L = 0` branch, where the budget forces `‖v‖ = 0`.

Layer: Glue | Gap: Level 1 (inverse-probability half-budget Young absorption)
Proof: split on `L = 0`; in the zero branch the positive quadratic budget
  forces the displacement norm to vanish, and in the positive branch Hilbert
  Young absorption is scaled by `1 / p` and the quadratic budget.
Source: Mathlib real Hilbert-space Young inequality and ordered-field algebra
Used in: randomized primal-dual gradient sampled dual Bregman Young absorption
Book citation: book/FOML/RandomPrimalDualGradient.json#/key_lemmas/7/proof/10
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized primal-dual gradient -/
theorem inverse_probability_inner_half_absorb_of_quadratic_budget
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    {m τ p L β W : ℝ} {u v : E}
    (hm_pos : 0 < m) (hτ_pos : 0 < τ) (hp_pos : 0 < p)
    (hL_nonneg : 0 ≤ L) (hW_nonneg : 0 ≤ W)
    (hquad : m / 2 * ‖v‖ ^ 2 ≤ L * W) :
    - ((L * β ^ 2) / (m * τ * p) * ‖u‖ ^ 2) ≤
      (1 / p) * β * ⟪u, v⟫_ℝ + (τ / 2) * (1 / p) * W := by
  have hm_ne : m ≠ 0 := ne_of_gt hm_pos
  have hτ_ne : τ ≠ 0 := ne_of_gt hτ_pos
  have hp_ne : p ≠ 0 := ne_of_gt hp_pos
  by_cases hL_zero : L = 0
  · have hquad_zero : m / 2 * ‖v‖ ^ 2 ≤ 0 := by
      simpa [hL_zero] using hquad
    have hnorm_sq_zero : ‖v‖ ^ 2 = 0 := by
      have hhalf_pos : 0 < m / 2 := by nlinarith
      have hmul_nonneg : 0 ≤ m / 2 * ‖v‖ ^ 2 :=
        mul_nonneg (le_of_lt hhalf_pos) (sq_nonneg _)
      have hmul_zero : m / 2 * ‖v‖ ^ 2 = 0 :=
        le_antisymm hquad_zero hmul_nonneg
      rcases mul_eq_zero.mp hmul_zero with hhalf_zero | hsq_zero
      · exact False.elim (ne_of_gt hhalf_pos hhalf_zero)
      · exact hsq_zero
    have hnorm_zero : ‖v‖ = 0 :=
      sq_eq_zero_iff.mp hnorm_sq_zero
    have hinner_zero : ⟪u, v⟫_ℝ = 0 := by
      have habs_le : |⟪u, v⟫_ℝ| ≤ 0 := by
        simpa [hnorm_zero] using abs_real_inner_le_norm u v
      exact abs_eq_zero.mp (le_antisymm habs_le (abs_nonneg _))
    have hright_nonneg :
        0 ≤ (1 / p) * β * ⟪u, v⟫_ℝ + (τ / 2) * (1 / p) * W := by
      rw [hinner_zero]
      simp only [mul_zero, zero_add]
      exact mul_nonneg
        (mul_nonneg (div_nonneg (le_of_lt hτ_pos) (by norm_num))
          (one_div_nonneg.mpr (le_of_lt hp_pos)))
        hW_nonneg
    simpa [hL_zero] using hright_nonneg
  · have hL_pos : 0 < L := lt_of_le_of_ne hL_nonneg (Ne.symm hL_zero)
    have hL_ne : L ≠ 0 := ne_of_gt hL_pos
    let a : ℝ := m * τ / (2 * L)
    have ha_pos : 0 < a := by
      exact div_pos (mul_pos hm_pos hτ_pos) (mul_pos (by norm_num) hL_pos)
    have hYoung :=
      neg_inner_le_half_mul_norm_sq_add_inv_two_mul_norm_sq
        (E := E) (q := a) ha_pos (β • u) v
    have hnorm : ‖β • u‖ ^ 2 = β ^ 2 * ‖u‖ ^ 2 := by
      rw [norm_smul]
      calc
        (‖β‖ * ‖u‖) ^ 2 = ‖β‖ ^ 2 * ‖u‖ ^ 2 := by ring
        _ = β ^ 2 * ‖u‖ ^ 2 := by
          simp [Real.norm_eq_abs, sq_abs]
    have hbudget :
        (a / 2) * ‖v‖ ^ 2 ≤ (τ / 2) * W := by
      have hscale_nonneg : 0 ≤ τ / (2 * L) := by
        exact div_nonneg (le_of_lt hτ_pos)
          (mul_nonneg (by norm_num) (le_of_lt hL_pos))
      calc
        (a / 2) * ‖v‖ ^ 2 =
            (τ / (2 * L)) * (m / 2 * ‖v‖ ^ 2) := by
              simp [a]
              field_simp [hm_ne, hτ_ne, hL_ne]
        _ ≤ (τ / (2 * L)) * (L * W) :=
              mul_le_mul_of_nonneg_left hquad hscale_nonneg
        _ = (τ / 2) * W := by
              field_simp [hL_ne]
    have hYoungBudget :
        -(β * ⟪u, v⟫_ℝ) ≤
          (τ / 2) * W + (1 / (2 * a)) * (β ^ 2 * ‖u‖ ^ 2) := by
      have hYoung' :
          -(β * ⟪u, v⟫_ℝ) ≤
            (a / 2) * ‖v‖ ^ 2 + (1 / (2 * a)) * (β ^ 2 * ‖u‖ ^ 2) := by
        simpa [inner_smul_left, hnorm] using hYoung
      nlinarith
    have hmove :
        - ((1 / (2 * a)) * (β ^ 2 * ‖u‖ ^ 2)) ≤
          β * ⟪u, v⟫_ℝ + (τ / 2) * W := by
      linarith
    have hscaled :
        (1 / p) * (- ((1 / (2 * a)) * (β ^ 2 * ‖u‖ ^ 2))) ≤
          (1 / p) * (β * ⟪u, v⟫_ℝ + (τ / 2) * W) := by
      exact mul_le_mul_of_nonneg_left hmove
        (one_div_nonneg.mpr (le_of_lt hp_pos))
    have hleft_eq :
        - ((L * β ^ 2) / (m * τ * p) * ‖u‖ ^ 2) =
          (1 / p) * (- ((1 / (2 * a)) * (β ^ 2 * ‖u‖ ^ 2))) := by
      simp [a]
      field_simp [hm_ne, hτ_ne, hL_ne, hp_ne]
    calc
      - ((L * β ^ 2) / (m * τ * p) * ‖u‖ ^ 2) =
          (1 / p) * (- ((1 / (2 * a)) * (β ^ 2 * ‖u‖ ^ 2))) := hleft_eq
      _ ≤ (1 / p) * (β * ⟪u, v⟫_ℝ + (τ / 2) * W) := hscaled
      _ = (1 / p) * β * ⟪u, v⟫_ℝ + (τ / 2) * (1 / p) * W := by
        ring

-- Generalization plan (G0):
-- concept/name: reciprocal coefficient solve for a two-branch affine mixture;
--   orig was solve_mixture_eq_of_inv_mul_probability_eq_one, renamed away from
--   the local proof-block wording and probability-specific names.
-- generality used: an arbitrary commutative ring and five scalar parameters
--   only; no measure, filtration, independence, integrability, convexity,
--   smoothness, oracle, carrier, order, field, or finite-dimensional hypotheses
--   are used once the reciprocal product equality is available.
-- portable call pattern: importance-sampling, randomized-coordinate, and
--   block-coordinate analyses can call this when a current quantity is split as
--   `A = p * H + (1 - p) * C` and the selected branch must be solved using a
--   reciprocal coefficient; `A`, `H`, `C`, `p`, and `inv` change while the
--   solved-mixture conclusion keeps the same shape.
-- counterargument checked: not paper-local traceability and not just a
--   caller-side expression; the statement packages the recurring reciprocal
--   mixture solve that otherwise expands into coefficient bookkeeping. It is
--   not decomposed into a def because the expression is scalar algebra rather
--   than a named mathematical object such as a probability law or prox
--   objective.
-- coverage search: searched SOptLib catalog/source for inv_mul, one_sub,
--   mul_add, eq_inv, mixture, weighted, and reciprocal coefficient; relevant
--   partial hits covered affine-blend displacement and reciprocal coefficient
--   bounds, not this equality solve. LeanSearch for "linear equation solve
--   affine combination reciprocal p" returned Mathlib affine-combination APIs
--   and Holder reciprocal lemmas, which do not cover this scalar statement.
-- minimal hypotheses: generalized from real scalars to `[Ring K]`; the only
--   hypotheses needed are the mixture equality and `inv * p = 1`.

/-- Solve a two-branch scalar mixture using a reciprocal coefficient.

If `A = p * H + (1 - p) * C` and `inv * p = 1`, then the selected branch
`H` is obtained from the aggregate `A` by subtracting the complementary branch
with coefficient `inv - 1`.

Layer: Glue | Gap: Level 0 (reciprocal two-branch mixture solve)
Proof: rewrite the aggregate with the mixture identity, replace the selected
  coefficient by `inv * p`, and normalize the remaining noncommutative-ring
  expression by `noncomm_ring`.
Source: Mathlib noncommutative-ring normalization and scalar affine-combination algebra
Used in: randomized primal-dual gradient dual Bregman substitution after
  splitting a sampled block expectation into selected and complementary branches
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec/steps
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized primal-dual gradient -/
theorem eq_inv_mul_sub_inv_sub_one_mul_of_eq_mul_add_one_sub_mul
    {K : Type*} [Ring K] {A H C p inv : K}
    (hA : A = p * H + (1 - p) * C)
    (hinv : inv * p = 1) :
    H = inv * A - (inv - 1) * C := by
  have hcoef : inv * (1 - p) - (inv - 1) = 0 := by
    calc
      inv * (1 - p) - (inv - 1) = 1 - inv * p := by noncomm_ring
      _ = 0 := by rw [hinv]; noncomm_ring
  rw [hA]
  calc
    H = 1 * H + 0 * C := by noncomm_ring
    _ = (inv * p) * H + (inv * (1 - p) - (inv - 1)) * C := by
      rw [hinv, hcoef]
    _ = inv * (p * H + (1 - p) * C) - (inv - 1) * C := by noncomm_ring

open scoped BigOperators

-- Generalization plan (G0):
-- concept/name: one-based closed-interval finite geometric sum; orig was
--   `sum_Icc_one_based_geom_mul`, renamed to expose the `Icc 1 k` power-sum
--   identity and its multiplication by `q - 1`.
-- generality used: an arbitrary `Ring` is enough; no measure, filtration,
--   convexity, smoothness, or oracle assumptions are involved.
-- portable call pattern: finite-window stochastic-optimization rate proofs
--   with one-based geometric output weights instantiate the base `q` and
--   endpoint `k` while reusing the same closed-interval geometric-sum
--   evaluation before normalizing an ergodic bound.
-- counterargument checked: Mathlib already has the half-open `Ico` and
--   `range` geometric-sum identities, but not this closed one-based `Icc`
--   packaging; this avoids reindexing at every one-based output window.
-- coverage search: searched SOptLib/catalog/source for `sum_Icc_one`,
--   `geometric`, `Icc pow`, and `pow_succ_sub`; relevant partial hits were
--   non-geometric `Icc` sum rewrites and terminal-adjusted geometric sums.
--   LeanSearch returned Mathlib `geom_sum_Ico_mul`, `geom_sum_mul`, and
--   `geom_sum_Ico`, which cover half-open/range windows but not the exact
--   closed `Finset.Icc 1 k` statement.
-- minimal hypotheses: all already minimal; generalized from `ℝ` to an
--   arbitrary ring.

/-- A one-based closed-interval geometric sum times `q - 1` telescopes to the
endpoint powers.

The closed interval `Finset.Icc 1 k` is the one-based form often used for
finite output windows; this lemma packages the conversion to Mathlib's
half-open geometric-sum theorem.

Layer: Glue | Gap: Level 0 (one-based closed-interval geometric sum)
Proof: rewrite `Finset.Icc 1 k` as `Finset.Ico 1 (k + 1)` and apply Mathlib's
  half-open finite geometric-sum identity.
Source: Mathlib finite geometric sums in rings and successor interval rewrites
Used in: randomized primal-dual gradient one-based output-window normalizer
  evaluation before the half-geometric primal-gap rate
Book citation: book/FOML/RandomPrimalDualGradient.json#/main_theorem/proof/14
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized primal-dual gradient -/
theorem sum_Icc_one_pow_mul_sub_eq_pow_succ_sub {R : Type*} [Ring R] (q : R) (k : ℕ) :
    (∑ t ∈ Finset.Icc 1 k, q ^ t) * (q - 1) = q ^ (k + 1) - q := by
  rw [← Finset.Ico_add_one_right_eq_Icc 1 k]
  simpa using geom_sum_Ico_mul q (Nat.succ_le_succ (Nat.zero_le k))

-- Generalization plan (G0):
-- concept/name: one-based closed finite-window initial split; orig was sum_Icc_one_eq_first_add_tail and the Mathlib-style name is already paper-free.
-- generality used: natural-number closed intervals and an arbitrary AddCommMonoid-valued summand; no measure, convexity, smoothness, or oracle assumptions are used.
-- portable call pattern: one-based stochastic optimization recurrences split the first budget or coupling term from the positive-time tail while changing only the summand family and horizon.
-- counterargument checked: this is a short wrapper around Mathlib interval APIs, but the closed-window `Icc 1 k` to `A 1 + Icc 2 k` form is the repeated caller-side shape rather than paper traceability.
-- coverage search: LeanSearch for "sum over Finset Icc 1 k equals first term plus sum over Icc 2 k" found `Finset.sum_eq_sum_Ico_succ_bot`, `Finset.sum_Icc_succ_top`, and `Finset.add_sum_Ioc_eq_sum_Icc`; SOptLib search found terminal/telescope interval lemmas but no initial closed-window tail split.
-- minimal hypotheses: all already minimal; only `[AddCommMonoid M]`, `A : ℕ → M`, and `1 ≤ k` are needed.


open scoped BigOperators

/-- Split a one-based closed finite sum into its first summand and the tail.

For any additive commutative monoid, the closed natural-number window
`Icc 1 k` decomposes as the initial index `1` plus the closed tail `Icc 2 k`
when the horizon is positive.

Layer: Glue | Gap: Level 0 (one-based closed-window initial split)
Proof: rewrite both closed intervals as half-open intervals ending at `k + 1`,
  then apply Mathlib's `Finset.sum_eq_sum_Ico_succ_bot`.
Source: Mathlib finite sums over natural intervals
Used in: random primal-dual gradient one-based recurrence algebra splitting the
  initial coupling or budget term before bounding the positive-time tail
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
theorem sum_Icc_one_eq_first_add_tail {M : Type*} [AddCommMonoid M]
    (A : ℕ → M) (k : ℕ) (hk : 1 ≤ k) :
    (∑ t ∈ Finset.Icc 1 k, A t) =
      A 1 + ∑ t ∈ Finset.Icc 2 k, A t := by
  rw [← Finset.Ico_add_one_right_eq_Icc, ← Finset.Ico_add_one_right_eq_Icc]
  exact Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_le_succ hk) A

-- Generalization plan (G0):
-- concept/name: one-based closed finite-window terminal split with lagged tail;
--   orig was `sum_Icc_one_eq_terminal_add_lagged`, retained because it names the
--   `Finset.Icc` window, terminal endpoint, and predecessor-indexed tail without
--   paper vocabulary.
-- generality used: natural-number closed intervals and an arbitrary
--   AddCommMonoid-valued summand; no measure, filtration, independence,
--   integrability, convexity, smoothness, oracle, carrier, or finite-dimensional
--   hypotheses are used.
-- portable call pattern: one-based stochastic optimization recurrences split
--   a terminal budget from a predecessor-indexed window before allocating
--   terminal and lagged bounds; only the summand family and horizon change.
-- counterargument checked: this is a short consequence of Mathlib interval APIs,
--   but Mathlib's endpoint lemmas do not expose the recurring closed-window
--   `Icc 1 k` to terminal plus `Icc 2 k` predecessor-tail shape directly, and
--   the statement is paper-free finite-sum algebra rather than traceability.
-- coverage search: LeanSearch for "sum over Finset Icc 1 k equals terminal term
--   plus sum from 2 to k of previous index" found `Finset.sum_Icc_succ_top`,
--   `Finset.sum_eq_sum_Ico_succ_bot`, and range/Ico endpoint splits; SOptLib
--   search found `sum_Icc_one_eq_first_add_tail`,
--   `sum_Icc_weighted_lagged_cancel_eq_terminal`, and lagged telescope
--   inequalities, but no terminal predecessor-tail split.
-- minimal hypotheses: all already minimal; only `[AddCommMonoid M]`,
--   `A : ℕ → M`, and `1 ≤ k` are needed.


open scoped BigOperators

/-- Split a one-based closed finite sum into its terminal summand and lagged tail.

For any additive commutative monoid, the closed natural-number window
`Icc 1 k` decomposes as the terminal index `k` plus the predecessor-indexed
tail over `Icc 2 k` when the horizon is positive.

Layer: Glue | Gap: Level 0 (one-based closed-window terminal lagged split)
Proof: induction on the terminal index, splitting both closed intervals at the
  top index with `Finset.sum_Icc_succ_top`; commutative monoid arithmetic
  rearranges the endpoint and lagged-tail terms.
Source: Mathlib finite sums over natural intervals
Used in: random primal-dual gradient one-based recurrence algebra separating a
  terminal budget from predecessor-indexed positive-time terms
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
theorem sum_Icc_one_eq_terminal_add_lagged {M : Type*} [AddCommMonoid M]
    (A : ℕ → M) (k : ℕ) (hk : 1 ≤ k) :
    (∑ t ∈ Finset.Icc 1 k, A t) =
      A k + ∑ t ∈ Finset.Icc 2 k, A (t - 1) := by
  classical
  induction k with
  | zero =>
      omega
  | succ n ih =>
      by_cases hn : n = 0
      · subst n
        simp
      · have hn_pos : 1 ≤ n := by omega
        have htop1 : 1 ≤ n + 1 := by omega
        have htop2 : 2 ≤ n + 1 := by omega
        have hih := ih hn_pos
        rw [Finset.sum_Icc_succ_top htop1]
        rw [Finset.sum_Icc_succ_top htop2]
        rw [hih]
        rw [show n + 1 - 1 = n by omega]
        simp [add_comm, add_left_comm]

-- Generalization plan (G0):
-- concept/name: exact weighted lagged finite-sum cancellation on a one-based
--   closed interval; orig was `sum_Icc_weighted_lagged_cancel_eq_terminal`,
--   retained because it names the Mathlib-style `Finset.Icc` summation shape,
--   the adjacent lag, and the terminal residue without paper vocabulary.
-- generality used: commutative-ring scalars and natural-indexed
--   sequences only; no measure, filtration, independence, integrability,
--   convexity, smoothness, oracle, carrier, or finite-dimensional hypotheses
--   are used.
-- portable call pattern: accelerated, primal-dual, variance-reduced, and
--   lagged-recurrence proofs instantiate `a`, `b`, and `H` with their adjacent
--   weights, coefficient bridge, and potential/coupling sequence to collapse
--   current and predecessor windows to the terminal `-a k * H k` term.
-- counterargument checked: not paper-local traceability because the statement
--   is a paper-free finite-sum identity used whenever `b t = a (t - 1)`;
--   not a pure wrapper because Mathlib telescope lemmas cover difference sums
--   over one interval, while this packages cancellation between two differently
--   indexed `Icc` windows.
-- coverage search: searched SOptLib catalog/source for weighted lagged cancel,
--   `Icc` predecessor, terminal equality, and telescope; closest hits were
--   `sum_range_weighted_lagged_source_telescope_le`,
--   `sum_Icc_two_coeff_telescope_le`, `sum_Icc_mono_coeff_mul_sub_le_terminal`,
--   and `sum_Icc_coeff_mul_shifted_sub_eq_sum_coeff_sub_mul_sub_tail`, all
--   inequality or different shifted-difference telescopes. LeanSearch returned
--   `Finset.sum_Ico_sub`, `Finset.sum_range_sub`, and related standard
--   difference telescopes, not this two-window lagged cancellation.
-- minimal hypotheses: only the nonempty one-based window `1 <= k` and the
--   pointwise bridge `b t = a (t - 1)` on `2 <= t <= k` are used; the
--   scalar finite-sum telescope needs no order structure because the
--   proof is equational ring arithmetic.

/-- Adjacent weighted current and lagged `Icc` sums cancel to the terminal term.

If the lagged coefficient satisfies `b t = a (t - 1)` throughout the positive
window, then the current window `∑ t in Icc 1 k, -a t * H t` and the lagged
window `∑ t in Icc 2 k, b t * H (t - 1)` cancel at every interior index,
leaving only `-a k * H k`.

Layer: Glue | Gap: Level 1 (one-based lagged finite-sum cancellation)
Proof: induction on the terminal index, splitting both closed intervals at the
  top index with `Finset.sum_Icc_succ_top`; the bridge rewrites the new lagged
  coefficient and ring arithmetic cancels the interior terms.
Source: Mathlib finite sums over natural intervals and ring arithmetic
Used in: random primal-dual gradient pathwise coupling telescope after the
  adjacent coefficient bridge has been established
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
theorem sum_Icc_weighted_lagged_cancel_eq_terminal
    {R : Type*} [CommRing R]
    (a b H : ℕ → R) (k : ℕ) (hk : 1 ≤ k)
    (hbridge : ∀ t, 2 ≤ t → t ≤ k → b t = a (t - 1)) :
    (∑ t ∈ Finset.Icc 1 k, (-a t * H t)) +
        ∑ t ∈ Finset.Icc 2 k, b t * H (t - 1) =
      -a k * H k := by
  classical
  induction k with
  | zero =>
      omega
  | succ n ih =>
      by_cases hn : n = 0
      · subst n
        simp
      · have hn_pos : 1 ≤ n := by omega
        have htop1 : 1 ≤ n + 1 := by omega
        have htop2 : 2 ≤ n + 1 := by omega
        have hbridge_n :
            ∀ t, 2 ≤ t → t ≤ n → b t = a (t - 1) := by
          intro t ht2 htn
          exact hbridge t ht2 (by omega)
        have hih := ih hn_pos hbridge_n
        rw [Finset.sum_Icc_succ_top htop1]
        rw [Finset.sum_Icc_succ_top htop2]
        have hlast : b (n + 1) = a n := by
          simpa using hbridge (n + 1) (by omega) le_rfl
        rw [show n + 1 - 1 = n by omega, hlast]
        have hcancel :
            (∑ t ∈ Finset.Icc 1 n, (-a t * H t)) +
                ∑ t ∈ Finset.Icc 2 n, b t * H (t - 1) +
              a n * H n = 0 := by
          rw [hih]
          ring
        linear_combination hcancel

open scoped BigOperators

-- Generalization plan (G0):
-- concept/name: weighted finite-sum regrouping from a pointwise current/lagged
--   decomposition; orig was `sum_Icc_weighted_coupling_regroup_from_pointwise`,
--   retained because it names the Mathlib-style `Finset.Icc` summation shape,
--   the weighted coupling decomposition, and the pointwise hypothesis without
--   paper vocabulary.
-- generality used: commutative-ring scalars and natural-indexed sequences
--   only; no measure, filtration, independence, integrability, convexity,
--   smoothness, oracle, carrier, topology, order, or finite-dimensional
--   hypotheses are used.
-- portable call pattern: primal-dual, accelerated, mirror-descent, and
--   variance-reduced convergence proofs instantiate `C`, `H`, `Ecur`,
--   `Eprev`, weights, and the terminal cancellation `T` after proving a
--   pointwise current/historical expansion, obtaining the same terminal-plus-
--   error weighted regrouping equality.
-- counterargument checked: not paper-local traceability because the statement
--   is source-free finite-sum algebra; not a caller-side expression because it
--   combines the first/tail split, pointwise historical expansion, lagged
--   cancellation, and error-sum separation into one reusable proof step.
-- coverage search: searched project/SOptLib/Staging for weighted coupling
--   regrouping, pointwise Icc regroup, lagged cancel, and first-tail split;
--   the closest existing entries are `sum_Icc_one_eq_first_add_tail` and
--   `sum_Icc_weighted_lagged_cancel_eq_terminal`, which provide components
--   but not the full `C/H/Ecur/Eprev` regrouping. LeanSearch for finite `Icc`
--   split/regroup found `Finset.sum_eq_sum_Ico_succ_bot`,
--   `Finset.add_sum_Ioc_eq_sum_Icc`, and related interval split lemmas, not
--   this weighted pointwise decomposition.
-- minimal hypotheses: all algorithm fields are reduced to pointwise scalar
--   equalities: the nonempty one-based window `1 <= k`, the base equality at
--   index `1`, the historical expansion only on `Icc 2 k`, and the supplied
--   lagged cancellation identity.

/-- Regroup a weighted current/lagged coupling expansion over a one-based window.

If `C 1 = H 1`, and on the tail `C t` decomposes as the current coupling
`H t` minus a lagged coupling `α t * H (t - 1)` minus two error terms, then
any weighted cancellation of the current and lagged `H` windows transfers to a
weighted regrouping of `-C` as the same terminal term plus the error window.

Layer: Glue | Gap: Level 1 (pointwise weighted coupling regrouping)
Proof: split the one-based closed windows into the first summand and the
  `Icc 2 k` tail, rewrite tail summands by the pointwise decomposition, separate
  the three finite sums with `Finset.sum_add_distrib`, and apply the supplied
  lagged cancellation identity.
Source: Mathlib finite sums over natural intervals and commutative-ring
  arithmetic
Used in: random primal-dual gradient pathwise coupling expansion converting
  current and historical terms into a terminal coupling plus error sums
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
theorem sum_Icc_weighted_coupling_regroup_from_pointwise
    {R : Type*} [CommRing R]
    (θ α C H Ecur Eprev : ℕ → R) (T : R)
    (k : ℕ) (hk : 1 ≤ k)
    (hbase : C 1 = H 1)
    (hhist :
      ∀ t ∈ Finset.Icc 2 k,
        C t = H t - α t * H (t - 1) - (Ecur t + Eprev t))
    (hcancel :
      (∑ t ∈ Finset.Icc 1 k, (-θ t * H t)) +
          ∑ t ∈ Finset.Icc 2 k, (α t * θ t) * H (t - 1) = T) :
    (∑ t ∈ Finset.Icc 1 k, θ t * (- C t)) =
      T + ∑ t ∈ Finset.Icc 2 k, θ t * (Ecur t + Eprev t) := by
  classical
  have hsplitC :
      (∑ t ∈ Finset.Icc 1 k, θ t * (- C t)) =
        θ 1 * (- C 1) + ∑ t ∈ Finset.Icc 2 k, θ t * (- C t) :=
    sum_Icc_one_eq_first_add_tail (fun t => θ t * (- C t)) k hk
  have hsplitH :
      (∑ t ∈ Finset.Icc 1 k, (-θ t * H t)) =
        (-θ 1 * H 1) + ∑ t ∈ Finset.Icc 2 k, (-θ t * H t) :=
    sum_Icc_one_eq_first_add_tail (fun t => (-θ t * H t)) k hk
  have htail :
      (∑ t ∈ Finset.Icc 2 k, θ t * (- C t)) =
        ∑ t ∈ Finset.Icc 2 k,
          ((-θ t * H t) + (α t * θ t) * H (t - 1) +
            θ t * (Ecur t + Eprev t)) := by
    refine Finset.sum_congr rfl ?_
    intro t ht
    rw [hhist t ht]
    ring
  have htail_split :
      (∑ t ∈ Finset.Icc 2 k,
          ((-θ t * H t) + (α t * θ t) * H (t - 1) +
            θ t * (Ecur t + Eprev t))) =
        (∑ t ∈ Finset.Icc 2 k, (-θ t * H t)) +
          ∑ t ∈ Finset.Icc 2 k, (α t * θ t) * H (t - 1) +
          ∑ t ∈ Finset.Icc 2 k, θ t * (Ecur t + Eprev t) := by
    simp only [Finset.sum_add_distrib]
  calc
    (∑ t ∈ Finset.Icc 1 k, θ t * (- C t)) =
        θ 1 * (- C 1) + ∑ t ∈ Finset.Icc 2 k, θ t * (- C t) := hsplitC
    _ = (-θ 1 * H 1) + ∑ t ∈ Finset.Icc 2 k, θ t * (- C t) := by
        rw [hbase]
        ring
    _ =
        (-θ 1 * H 1) +
          ∑ t ∈ Finset.Icc 2 k,
            ((-θ t * H t) + (α t * θ t) * H (t - 1) +
              θ t * (Ecur t + Eprev t)) := by
        rw [htail]
    _ =
        ((-θ 1 * H 1) + ∑ t ∈ Finset.Icc 2 k, (-θ t * H t)) +
          ∑ t ∈ Finset.Icc 2 k, (α t * θ t) * H (t - 1) +
          ∑ t ∈ Finset.Icc 2 k, θ t * (Ecur t + Eprev t) := by
        rw [htail_split]
        ring
    _ =
        (∑ t ∈ Finset.Icc 1 k, (-θ t * H t)) +
          ∑ t ∈ Finset.Icc 2 k, (α t * θ t) * H (t - 1) +
          ∑ t ∈ Finset.Icc 2 k, θ t * (Ecur t + Eprev t) := by
        rw [hsplitH]
    _ = T + ∑ t ∈ Finset.Icc 2 k, θ t * (Ecur t + Eprev t) := by
        rw [hcancel]

open scoped BigOperators

-- Generalization plan (G0):
-- concept/name: weighted three-way residual finite-sum regrouping; orig was
--   sum_weighted_three_way_residual_split and the name is already paper-free.
-- generality used: arbitrary finite index set and non-unital non-associative
--   ring codomain;
--   no measure, convexity, smoothness, oracle, or order assumptions are used.
-- portable call pattern: endpoint and telescope assemblies in stochastic
--   primal-dual, mirror-descent, and variance-reduced proofs can change the
--   index set, weights, and residual families while preserving this split.
-- counterargument checked: this is a short algebra wrapper, but it packages a
--   recurring caller-side regrouping boundary not expressed by one existing
--   Mathlib/SOptLib theorem; no paper-local names remain in the statement.
-- coverage search: searched catalog and sources for `three_way`,
--   `residual_split`, `weighted residual`, and LeanSearch query "finite sum
--   weighted residual regroup"; Mathlib hits `Finset.sum_add_distrib`,
--   `Finset.sum_sub_distrib`, `Finset.sum_add_sum_comm`, and SOptLib hits
--   `finset_weighted_residual_sum_eq_zero` and
--   `finset_inner_scalar_three_way_expansion` are partial, not this four-family
--   weighted regrouping identity.
-- minimal hypotheses: the algorithm-specific real statement generalizes to
--   `[NonUnitalNonAssocRing beta]`; `DecidableEq alpha` is needed only for the
--   bounded-sum notation, and no nonempty hypotheses are needed.

/-- A weighted finite sum of `((P - Q) + D) + R` splits into grouped sums.

This packages the algebraic regrouping that turns a pointwise primal-minus-tail
term, an auxiliary residual, and a remainder into separate weighted sums of
`P`, `D`, and `R - Q`.

Layer: Glue | Gap: Level 0 (weighted finite-sum residual regrouping)
Proof: rewrite each summand by noncommutative ring normalization, then distribute
  the finite sum over the two additions.
Source: Mathlib finite sums over non-unital rings and noncommutative ring
  normalization
Used in: random primal-dual gradient endpoint assembly after local primal,
  dual, and coupling-residual bounds have been summed
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
theorem sum_weighted_three_way_residual_split {alpha beta : Type*} [DecidableEq alpha]
    [NonUnitalNonAssocRing beta]
    (s : Finset alpha) (theta P D R Q : alpha -> beta) :
    (∑ t ∈ s, theta t * (((P t - Q t) + D t) + R t)) =
      (∑ t ∈ s, theta t * P t) +
        (∑ t ∈ s, theta t * D t) +
          (∑ t ∈ s, theta t * (R t - Q t)) := by
  calc
    (∑ t ∈ s, theta t * (((P t - Q t) + D t) + R t)) =
        ∑ t ∈ s, (theta t * P t + theta t * D t + theta t * (R t - Q t)) := by
      refine Finset.sum_congr rfl ?_
      intro t _ht
      noncomm_ring
    _ = (∑ t ∈ s, theta t * P t) +
        (∑ t ∈ s, theta t * D t) +
          (∑ t ∈ s, theta t * (R t - Q t)) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]

open scoped BigOperators

-- Generalization plan (G0):
-- concept/name: three Young budget allocation over a one-based closed finite
--   window; orig was `proposition51_scalar_young_allocation_le`, renamed away
--   from the paper proposition number to expose the reusable scalar allocation.
-- generality used: natural-indexed ordered-field scalar sequences and a
--   one-based finite window; no measure, filtration, independence, integrability,
--   convexity, smoothness, oracle, carrier, topology, or finite-dimensional
--   hypotheses are used.
-- portable call pattern: primal-dual, mirror-descent, accelerated, and
--   variance-reduced proofs that have terminal, current, and previous Young
--   inequalities plus a regrouping identity can instantiate the scalar
--   schedules, residuals, and budgets while keeping this conclusion unchanged.
-- counterargument checked: this is not only paper traceability because the
--   statement is paper-free scalar finite-sum algebra over an ordered field; it
--   is not a pure wrapper
--   around one Mathlib lemma because it combines three inequalities, two
--   closed-window endpoint splits, and a nonnegative initial half-budget.
-- coverage search: searched SOptLib/Staging/catalog for `young budget
--   allocation`, `scalar_young_allocation`, `terminal current previous`, and
--   `Icc budget`; relevant hits were endpoint split lemmas
--   `sum_Icc_one_eq_first_add_tail`, `sum_Icc_one_eq_terminal_add_lagged`, and
--   local Young absorption lemmas, but none state this three-budget allocation.
-- minimal hypotheses: all already minimal for the proof shape: ordered-field
--   scalar arithmetic, `1 <= k`, the regrouping equality, three Young/budget
--   inequalities, and nonnegativity of the initial dual half-budget.

/-- Allocate terminal, current, and previous Young budgets over `Icc 1 k`.

Given a one-based regrouping identity for the `C` terms, a terminal Young
inequality, two tail Young inequalities, and a nonnegative initial half-budget,
the terminal residual and the two lagged residual windows are bounded by the
weighted primal-plus-coupling-plus-dual residual sum.

Layer: Glue | Gap: Level 1 (three Young budget finite-window allocation)
Proof: split the primal and dual sums at the terminal and initial endpoints,
  add the three Young inequalities, separate the half-budget sums, and close
  the scalar allocation with ordered-field arithmetic.
Source: Mathlib finite sums over natural intervals and ordered scalar arithmetic
Used in: random primal-dual gradient pathwise residual proof allocating
  terminal, current, and previous Young half-budgets
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized primal-dual gradient -/
theorem three_young_budget_allocation_Icc_le
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (θ η U C A B D SQk SQcur SQprev E F : ℕ → R)
    (k : ℕ) (hk : 1 ≤ k)
    (hRegroup :
      (∑ t ∈ Finset.Icc 1 k, θ t * (- C t)) =
        -θ k * (A k + B k) +
          ∑ t ∈ Finset.Icc 2 k, θ t * (E t + F t))
    (hTerminal :
      θ k * (-SQk k * U k) ≤ θ k * (-B k + D k / 2))
    (hCurrent :
      (∑ t ∈ Finset.Icc 2 k, -θ (t - 1) * SQcur t * U (t - 1)) ≤
        ∑ t ∈ Finset.Icc 2 k, θ t * (E t + D t / 2))
    (hPrevious :
      (∑ t ∈ Finset.Icc 2 k, -θ (t - 1) * SQprev t * U (t - 1)) ≤
        ∑ t ∈ Finset.Icc 2 k,
          (θ t * F t + θ (t - 1) * (D (t - 1) / 2)))
    (hDinit : 0 ≤ θ 1 * (D 1 / 2)) :
    θ k * (η k / 4 * U k - A k) +
        θ k * (η k / 4 - SQk k) * U k +
      ∑ t ∈ Finset.Icc 2 k,
        θ (t - 1) * (η (t - 1) / 2 - (SQcur t + SQprev t)) * U (t - 1) ≤
      ∑ t ∈ Finset.Icc 1 k,
        θ t * (η t / 2 * U t - C t + D t) := by
  classical
  let P : ℕ → R := fun t => θ t * (η t / 2 * U t)
  let T : ℕ → R := fun t => θ t * (D t / 2)
  have hPrimalSplit :
      (∑ t ∈ Finset.Icc 1 k, P t) =
        P k + ∑ t ∈ Finset.Icc 2 k, P (t - 1) :=
    sum_Icc_one_eq_terminal_add_lagged P k hk
  have hDualFirst :
      (∑ t ∈ Finset.Icc 1 k, T t) =
        T 1 + ∑ t ∈ Finset.Icc 2 k, T t :=
    sum_Icc_one_eq_first_add_tail T k hk
  have hDualTerminal :
      (∑ t ∈ Finset.Icc 1 k, T t) =
        T k + ∑ t ∈ Finset.Icc 2 k, T (t - 1) :=
    sum_Icc_one_eq_terminal_add_lagged T k hk
  have hDualAlloc :
      T k + (∑ t ∈ Finset.Icc 2 k, T t) +
          (∑ t ∈ Finset.Icc 2 k, T (t - 1)) ≤
        2 * (∑ t ∈ Finset.Icc 1 k, T t) := by
    have hTinit : 0 ≤ T 1 := by
      dsimp [T]
      exact hDinit
    nlinarith [hDualFirst, hDualTerminal, hTinit]
  have hYoung :
        θ k * (-SQk k * U k) +
          (∑ t ∈ Finset.Icc 2 k, -θ (t - 1) * SQcur t * U (t - 1)) +
          (∑ t ∈ Finset.Icc 2 k, -θ (t - 1) * SQprev t * U (t - 1)) ≤
        θ k * (-B k + D k / 2) +
          (∑ t ∈ Finset.Icc 2 k, θ t * (E t + D t / 2)) +
          (∑ t ∈ Finset.Icc 2 k,
            (θ t * F t + θ (t - 1) * (D (t - 1) / 2))) := by
    exact add_le_add (add_le_add hTerminal hCurrent) hPrevious
  have hHistLeft :
      (∑ t ∈ Finset.Icc 2 k,
        θ (t - 1) * (η (t - 1) / 2 - (SQcur t + SQprev t)) * U (t - 1)) =
      (∑ t ∈ Finset.Icc 2 k, P (t - 1)) +
        (∑ t ∈ Finset.Icc 2 k, -θ (t - 1) * SQcur t * U (t - 1)) +
        (∑ t ∈ Finset.Icc 2 k, -θ (t - 1) * SQprev t * U (t - 1)) := by
    dsimp [P]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro t ht
    ring
  have hTerminalLeft :
      θ k * (η k / 4 * U k - A k) +
          θ k * (η k / 4 - SQk k) * U k =
        P k - θ k * A k + θ k * (-SQk k * U k) := by
    dsimp [P]
    ring
  have hYoungExpanded :
      θ k * (-SQk k * U k) +
          (∑ t ∈ Finset.Icc 2 k, -θ (t - 1) * SQcur t * U (t - 1)) +
          (∑ t ∈ Finset.Icc 2 k, -θ (t - 1) * SQprev t * U (t - 1)) ≤
        -θ k * B k +
          (∑ t ∈ Finset.Icc 2 k, θ t * (E t + F t)) +
          (T k + (∑ t ∈ Finset.Icc 2 k, T t) +
            (∑ t ∈ Finset.Icc 2 k, T (t - 1))) := by
    have hcurSplit :
        (∑ t ∈ Finset.Icc 2 k, θ t * (E t + D t / 2)) =
          (∑ t ∈ Finset.Icc 2 k, θ t * E t) +
            (∑ t ∈ Finset.Icc 2 k, T t) := by
      dsimp [T]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro t ht
      ring
    have hprevSplit :
        (∑ t ∈ Finset.Icc 2 k,
            (θ t * F t + θ (t - 1) * (D (t - 1) / 2))) =
          (∑ t ∈ Finset.Icc 2 k, θ t * F t) +
            (∑ t ∈ Finset.Icc 2 k, T (t - 1)) := by
      dsimp [T]
      rw [← Finset.sum_add_distrib]
    have hefSplit :
        (∑ t ∈ Finset.Icc 2 k, θ t * (E t + F t)) =
          (∑ t ∈ Finset.Icc 2 k, θ t * E t) +
            (∑ t ∈ Finset.Icc 2 k, θ t * F t) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro t ht
      ring
    calc
      θ k * (-SQk k * U k) +
          (∑ t ∈ Finset.Icc 2 k, -θ (t - 1) * SQcur t * U (t - 1)) +
          (∑ t ∈ Finset.Icc 2 k, -θ (t - 1) * SQprev t * U (t - 1))
          ≤
        θ k * (-B k + D k / 2) +
          (∑ t ∈ Finset.Icc 2 k, θ t * (E t + D t / 2)) +
          (∑ t ∈ Finset.Icc 2 k,
            (θ t * F t + θ (t - 1) * (D (t - 1) / 2))) := hYoung
      _ =
        -θ k * B k +
          (∑ t ∈ Finset.Icc 2 k, θ t * (E t + F t)) +
          (T k + (∑ t ∈ Finset.Icc 2 k, T t) +
            (∑ t ∈ Finset.Icc 2 k, T (t - 1))) := by
        rw [hcurSplit, hprevSplit, hefSplit]
        dsimp [T]
        ring
  have hYoungApplied :
      θ k * (η k / 4 * U k - A k) +
          θ k * (η k / 4 - SQk k) * U k +
        ∑ t ∈ Finset.Icc 2 k,
          θ (t - 1) * (η (t - 1) / 2 - (SQcur t + SQprev t)) * U (t - 1)
        ≤
      (P k + ∑ t ∈ Finset.Icc 2 k, P (t - 1)) +
        (-θ k * (A k + B k) +
          ∑ t ∈ Finset.Icc 2 k, θ t * (E t + F t)) +
        (T k + (∑ t ∈ Finset.Icc 2 k, T t) +
          (∑ t ∈ Finset.Icc 2 k, T (t - 1))) := by
    rw [hTerminalLeft, hHistLeft]
    nlinarith [hYoungExpanded]
  calc
    θ k * (η k / 4 * U k - A k) +
        θ k * (η k / 4 - SQk k) * U k +
      ∑ t ∈ Finset.Icc 2 k,
        θ (t - 1) * (η (t - 1) / 2 - (SQcur t + SQprev t)) * U (t - 1)
        ≤
      (P k + ∑ t ∈ Finset.Icc 2 k, P (t - 1)) +
        (-θ k * (A k + B k) +
          ∑ t ∈ Finset.Icc 2 k, θ t * (E t + F t)) +
        (T k + (∑ t ∈ Finset.Icc 2 k, T t) +
          (∑ t ∈ Finset.Icc 2 k, T (t - 1))) := hYoungApplied
    _ ≤
      (∑ t ∈ Finset.Icc 1 k, P t) +
        (∑ t ∈ Finset.Icc 1 k, θ t * (- C t)) +
        2 * (∑ t ∈ Finset.Icc 1 k, T t) := by
        nlinarith [hPrimalSplit, hRegroup, hDualAlloc]
    _ =
      ∑ t ∈ Finset.Icc 1 k,
        θ t * (η t / 2 * U t - C t + D t) := by
        dsimp [P, T]
        rw [Finset.mul_sum]
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl ?_
        intro t ht
        ring

open scoped BigOperators InnerProductSpace

-- Generalization plan (G0):
-- concept/name: finite inverse-probability terminal Young aggregation; orig
--   was terminal_residual_inverse_probability_young_aggregation, renamed away
--   from proposition numbering and random-primal-dual-gradient internals.
-- generality used: arbitrary finite index type and real Hilbert-space vectors
--   with a separated norm; no measure, filtration, convexity, smoothness,
--   oracle, or Bregman structure is used after pointwise nonnegativity and
--   quadratic-budget hypotheses are supplied.
-- portable call pattern: block-coordinate primal-dual, randomized mirror-prox,
--   and coordinate extragradient terminal-residual proofs vary the
--   probabilities, local Lipschitz constants, terminal budgets, vectors, and
--   aggregate stepsize condition while reusing the same inverse-probability
--   Young aggregation.
-- counterargument checked: not paper-local traceability because the statement
--   exposes the reusable finite-family absorption step; not a caller-side
--   expression because it combines zero-coefficient cases, pointwise
--   Cauchy/Young estimates, finite-sum inner-product linearity, and aggregate
--   coefficient absorption.
-- coverage search: searched SOptLib/Mathlib for `Young inequality inner product
--   finite sum inverse probability terminal nonnegative`, `finite sum Young
--   weighted inverse probability`, and nearby algebra helpers; Mathlib hits
--   were scalar Young/Hölder inequalities, and SOptLib hits included
--   `neg_inner_le_half_mul_norm_sq_add_inv_two_mul_norm_sq` and
--   `young_absorb_average_inner_with_quadratic_budget`, but none state this
--   inverse-probability finite terminal aggregation or handle the `L_i = 0`
--   branch under a pointwise quadratic budget.
-- minimal hypotheses: global algorithm assumptions are reduced to
--   `p_i > 0`, `L_i >= 0`, `W_i >= 0`, `m > 0`, `tau > 0`, pointwise
--   quadratic budgets, and the aggregate coefficient identity/bound.

/-- A finite inverse-probability Young aggregation makes the terminal residual
bracket nonnegative.

If each block vector has quadratic budget
`(m / 2) * ‖v_i‖^2 <= L_i * W_i`, positive sampling weight `p_i`, and
nonnegative budget `W_i`, then the inverse-probability budget terms absorb the
inner product with the finite sum whenever the aggregate coefficient
`q = (sum_i p_i L_i) / (m * tau)` is at most `eta / 2`.

Layer: Glue | Gap: Level 1 (finite inverse-probability Young aggregation)
Proof: prove a blockwise Cauchy/Young lower bound, with a separate zero
  `L_i` branch forced by the quadratic budget; sum the block bounds and absorb
  the remaining quadratic coefficient using the aggregate condition.
Source: Mathlib finite sums, real Hilbert-space Cauchy-Schwarz, and ordered
  field Young-inequality algebra
Used in: random primal-dual gradient terminal residual absorption after
  coordinatewise Bregman lower bounds
Book citation: book/FOML/RandomPrimalDualGradient.json#/key_lemmas/6/proof/12
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
theorem finite_sum_inverse_probability_terminal_young_nonneg
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p L W : ι → ℝ) (u : E) (v : ι → E) (m tau eta q : ℝ)
    (hp : ∀ i : ι, 0 < p i)
    (hL : ∀ i : ι, 0 ≤ L i)
    (hW : ∀ i : ι, 0 ≤ W i)
    (hm : 0 < m) (htau : 0 < tau)
    (hquad : ∀ i : ι, m / 2 * ‖v i‖ ^ 2 ≤ L i * W i)
    (hq : q = (∑ i : ι, p i * L i) / (m * tau))
    (hq_le : q ≤ eta / 2) :
    0 ≤ eta / 4 * ‖u‖ ^ 2 - ⟪u, ∑ i : ι, v i⟫_ℝ +
      ∑ i : ι, (1 / p i) * tau * W i := by
  classical
  have hm_ne : m ≠ 0 := ne_of_gt hm
  have htau_nonneg : 0 ≤ tau := le_of_lt htau
  have htau_ne : tau ≠ 0 := ne_of_gt htau
  have hden_ne : m * tau ≠ 0 := mul_ne_zero hm_ne htau_ne
  have hblock : ∀ i : ι,
      - (((p i * L i) / (m * tau)) / 2) * ‖u‖ ^ 2 ≤
        -⟪u, v i⟫_ℝ + (1 / p i) * tau * W i := by
    intro i
    by_cases hL_zero : L i = 0
    · have hquad_zero : m / 2 * ‖v i‖ ^ 2 ≤ 0 := by
        simpa [hL_zero] using hquad i
      have hv_sq_nonpos : ‖v i‖ ^ 2 ≤ 0 := by
        nlinarith [hquad_zero, hm]
      have hv_norm_zero : ‖v i‖ = 0 := by
        nlinarith [sq_nonneg ‖v i‖, hv_sq_nonpos]
      have hv_zero : v i = 0 := by
        exact (norm_eq_zero.mp hv_norm_zero : v i = 0)
      have hcoef_nonneg : 0 ≤ (1 / p i) * tau :=
        mul_nonneg (one_div_nonneg.mpr (le_of_lt (hp i))) htau_nonneg
      have hright_nonneg :
          0 ≤ -⟪u, v i⟫_ℝ + (1 / p i) * tau * W i := by
        have hinner_zero : -⟪u, v i⟫_ℝ = 0 := by
          simp [hv_zero]
        rw [hinner_zero, zero_add]
        exact mul_nonneg hcoef_nonneg (hW i)
      simpa [hL_zero] using hright_nonneg
    · have hL_pos : 0 < L i := lt_of_le_of_ne (hL i) (Ne.symm hL_zero)
      have hL_ne : L i ≠ 0 := ne_of_gt hL_pos
      have hp_ne : p i ≠ 0 := ne_of_gt (hp i)
      let a : ℝ := m * tau / (L i * p i)
      have ha_pos : 0 < a :=
        div_pos (mul_pos hm htau) (mul_pos hL_pos (hp i))
      have ha_ne : a ≠ 0 := ne_of_gt ha_pos
      have hYoung :
          ⟪u, v i⟫_ℝ ≤
            (a / 2) * ‖v i‖ ^ 2 + (1 / (2 * a)) * ‖u‖ ^ 2 := by
        have h :=
          neg_inner_le_half_mul_norm_sq_add_inv_two_mul_norm_sq
            (E := E) ha_pos (-u) (v i)
        simpa using h
      have hscale_nonneg : 0 ≤ tau * (1 / p i) / L i := by
        exact div_nonneg
          (mul_nonneg htau_nonneg
            (one_div_nonneg.mpr (le_of_lt (hp i))))
          (le_of_lt hL_pos)
      have hbudget :
          (a / 2) * ‖v i‖ ^ 2 ≤ (1 / p i) * tau * W i := by
        calc
          (a / 2) * ‖v i‖ ^ 2 =
              (tau * (1 / p i) / L i) * (m / 2 * ‖v i‖ ^ 2) := by
                change (m * tau / (L i * p i) / 2) * ‖v i‖ ^ 2 =
                  (tau * (1 / p i) / L i) * (m / 2 * ‖v i‖ ^ 2)
                field_simp [hm_ne, htau_ne, hL_ne, hp_ne]
          _ ≤ (tau * (1 / p i) / L i) * (L i * W i) :=
                mul_le_mul_of_nonneg_left (hquad i) hscale_nonneg
          _ = (1 / p i) * tau * W i := by
                field_simp [hL_ne, hp_ne]
      have hYoungBudget :
          - (1 / (2 * a)) * ‖u‖ ^ 2 ≤
            -⟪u, v i⟫_ℝ + (1 / p i) * tau * W i := by
        have hYoung' :
            - (1 / (2 * a)) * ‖u‖ ^ 2 ≤
              -⟪u, v i⟫_ℝ + (a / 2) * ‖v i‖ ^ 2 := by
          nlinarith [hYoung]
        nlinarith [hYoung', hbudget]
      have hsource_eq :
          - (((p i * L i) / (m * tau)) / 2) * ‖u‖ ^ 2 =
            - (1 / (2 * a)) * ‖u‖ ^ 2 := by
        rw [show a = m * tau / (L i * p i) by rfl]
        field_simp [hm_ne, htau_ne, hL_ne, hp_ne]
      calc
        - (((p i * L i) / (m * tau)) / 2) * ‖u‖ ^ 2 =
            - (1 / (2 * a)) * ‖u‖ ^ 2 := hsource_eq
        _ ≤ -⟪u, v i⟫_ℝ + (1 / p i) * tau * W i := hYoungBudget
  have hsumBlock :
      (∑ i : ι, - (((p i * L i) / (m * tau)) / 2) * ‖u‖ ^ 2) ≤
        ∑ i : ι, (-⟪u, v i⟫_ℝ + (1 / p i) * tau * W i) := by
    exact Finset.sum_le_sum (fun i _hi => hblock i)
  have hleft :
      (∑ i : ι, - (((p i * L i) / (m * tau)) / 2) * ‖u‖ ^ 2) =
        - (q / 2) * ‖u‖ ^ 2 := by
    rw [hq]
    simp [div_eq_mul_inv, Finset.sum_mul]
  have hright :
      (∑ i : ι, (-⟪u, v i⟫_ℝ + (1 / p i) * tau * W i)) =
        -⟪u, ∑ i : ι, v i⟫_ℝ +
          ∑ i : ι, (1 / p i) * tau * W i := by
    rw [Finset.sum_add_distrib]
    have hinner :
        ⟪u, ∑ i : ι, v i⟫_ℝ = ∑ i : ι, ⟪u, v i⟫_ℝ := by
      simpa using
        (inner_sum (𝕜 := ℝ) (s := (Finset.univ : Finset ι))
          (f := fun i : ι => v i) (x := u))
    calc
      (∑ x : ι, -⟪u, v x⟫_ℝ) +
          ∑ x : ι, (1 / p x) * tau * W x =
          -(∑ x : ι, ⟪u, v x⟫_ℝ) +
            ∑ x : ι, (1 / p x) * tau * W x := by
            rw [Finset.sum_neg_distrib]
      _ = -⟪u, ∑ i : ι, v i⟫_ℝ +
          ∑ i : ι, (1 / p i) * tau * W i := by
            rw [← hinner]
  have hresidual_lower :
      - (q / 2) * ‖u‖ ^ 2 ≤
        -⟪u, ∑ i : ι, v i⟫_ℝ +
          ∑ i : ι, (1 / p i) * tau * W i := by
    calc
      - (q / 2) * ‖u‖ ^ 2 =
          (∑ i : ι, - (((p i * L i) / (m * tau)) / 2) * ‖u‖ ^ 2) := hleft.symm
      _ ≤ ∑ i : ι, (-⟪u, v i⟫_ℝ + (1 / p i) * tau * W i) := hsumBlock
      _ = -⟪u, ∑ i : ι, v i⟫_ℝ +
          ∑ i : ι, (1 / p i) * tau * W i := hright
  have hcoef_nonneg : 0 ≤ (eta / 4 - q / 2) * ‖u‖ ^ 2 := by
    have hcoef : 0 ≤ eta / 4 - q / 2 := by
      nlinarith
    exact mul_nonneg hcoef (sq_nonneg _)
  nlinarith [hcoef_nonneg, hresidual_lower]


-- Promoted from Staging/weighted_inverse_probability_adjacent_coeff_le.lean
-- Generalization plan (G0):
-- concept/name: weighted inverse-probability adjacent coefficient bridge; orig
--   was theorem51_condition_46_division_free, renamed away from theorem numbers
--   and paper-local sampling/setup names while keeping the telescope coefficient
--   concept visible.
-- generality used: an arbitrary linear ordered field and scalar parameters
--   `p`, `tau`, `alpha`, `theta`, and `thetaPrev`; no measure, filtration,
--   independence, integrability, convexity, smoothness, oracle, carrier, or
--   finite-dimensional hypotheses are used once the pointwise probability lower
--   bound and adjacent weight equality are available.
-- portable call pattern: randomized coordinate, block-coordinate primal-dual,
--   and importance-sampled mirror/proximal analyses can call this at the
--   adjacent-potential telescope handoff; the sampling lower bound, relaxation
--   parameter, and weight sequence change while the coefficient bridge keeps
--   the same shape.
-- counterargument checked: not paper-local traceability because the statement
--   is paper-free scalar ordered-field algebra used before a generic
--   two-coefficient telescope; not a pure wrapper because existing endpoint
--   reciprocal bounds do not produce the adjacent previous-weight coefficient.
--   The expression is not extracted as a def because it is coefficient algebra,
--   not a recognized standalone mathematical object like a Bregman divergence
--   or prox objective.
-- coverage search: searched catalog/source for inverse probability, adjacent
--   coefficient, reciprocal coefficient, thetaPrev, alpha theta, and telescope;
--   SOptLib hits `sum_Icc_two_coeff_telescope_le` and
--   `inv_mul_one_add_sub_one_le_div_of_mul_one_add_le` are partial telescope and
--   endpoint ingredients, not this bridge. LeanSearch returned Mathlib
--   reciprocal monotonicity lemmas such as `one_div_le_one_div_of_le`, which are
--   proof ingredients rather than the compound adjacent coefficient statement.
-- minimal hypotheses: generalized from setup fields to pointwise scalar facts;
--   `0 < p`, `(1 - alpha) * (1 + tau) <= p`, `0 <= theta`, and
--   `thetaPrev = alpha * theta` are the hypotheses used by the proof.

/-- A weighted inverse-probability coefficient is bounded by the adjacent
previous-weight coefficient.

If a positive sampling scalar satisfies `(1 - alpha) * (1 + tau) <= p` and the
previous weight is `alpha * theta`, then the current weighted reciprocal
coefficient `theta * (p⁻¹ * (1 + tau) - 1)` is dominated by the adjacent
coefficient `p⁻¹ * thetaPrev * (1 + tau)`.

Layer: Glue | Gap: Level 0 (weighted inverse-probability adjacent coefficient bridge)
Proof: rewrite the reciprocal coefficient as `((1 + tau) - p) / p`, compare
  numerators using the probability lower bound, multiply by the nonnegative
  current weight, and rewrite the adjacent weight equality.
Source: Mathlib ordered-field division and ordered-ring normalization APIs
Used in: randomized primal-dual gradient dual-potential telescope coefficient
  handoff under inverse-probability sampling
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec/proof/theorem_5_1
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized primal-dual gradient -/
theorem weighted_inverse_probability_adjacent_coeff_le
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {p tau alpha theta thetaPrev : K}
    (hp_pos : 0 < p)
    (hprob : (1 - alpha) * (1 + tau) <= p)
    (htheta_nonneg : 0 <= theta)
    (hthetaPrev : thetaPrev = alpha * theta) :
    theta * (p⁻¹ * (1 + tau) - 1) <= p⁻¹ * thetaPrev * (1 + tau) := by
  have hp_ne : p ≠ 0 := ne_of_gt hp_pos
  have hnum : (1 + tau) - p <= alpha * (1 + tau) := by
    nlinarith [hprob]
  have hdiv :
      ((1 + tau) - p) / p <= (alpha * (1 + tau)) / p :=
    div_le_div_of_nonneg_right hnum hp_pos.le
  have hcoef : p⁻¹ * (1 + tau) - 1 <= p⁻¹ * alpha * (1 + tau) := by
    calc
      p⁻¹ * (1 + tau) - 1 = ((1 + tau) - p) / p := by
        field_simp [hp_ne]
      _ <= (alpha * (1 + tau)) / p := hdiv
      _ = p⁻¹ * alpha * (1 + tau) := by
        field_simp [hp_ne]
  calc
    theta * (p⁻¹ * (1 + tau) - 1)
        <= theta * (p⁻¹ * alpha * (1 + tau)) :=
          mul_le_mul_of_nonneg_left hcoef htheta_nonneg
    _ = p⁻¹ * thetaPrev * (1 + tau) := by
      rw [hthetaPrev]
      ring


-- Promoted from Staging/weighted_stepsize_le_adjacent_potential_coeff.lean
-- Generalization plan (G0):
-- concept/name: weighted stepsize adjacent potential coefficient bridge; orig
--   was theorem51_condition_47_division_free, renamed away from theorem numbers
--   and paper-local setup/output-weight fields while exposing the scalar
--   coefficient handoff used by weighted potential telescopes.
-- generality used: an arbitrary preordered commutative semiring with
--   Mathlib's nonnegative-left-multiplication monotonicity class, and scalar parameters `eta`,
--   `mu`, `alpha`, `theta`, and `thetaPrev`; no measure, filtration,
--   independence, integrability, convexity, smoothness, oracle, carrier, or
--   finite-dimensional hypotheses are used after the pointwise schedule
--   inequality and adjacent weight equality are available.
-- portable call pattern: weighted primal, mirror, proximal, and accelerated
--   potential telescopes can call this at the adjacent coefficient handoff; the
--   stepsize, strong-convexity/prox coefficient, contraction parameter, and
--   adjacent weights vary while the conclusion `theta * eta <=
--   thetaPrev * (mu + eta)` keeps the same shape.
-- counterargument checked: not paper-local traceability because the statement
--   is paper-free scalar ordered algebra used before generic two-coefficient
--   telescopes; not a pure caller-side expression because it packages the
--   recurring multiplication-by-current-weight and adjacent-weight rewrite.
--   The expression is not extracted as a def because it is coefficient algebra,
--   not a recognized standalone mathematical object like a Bregman divergence
--   or prox objective.
-- coverage search: searched project/SOptLib/Staging/catalog for weighted
--   stepsize, adjacent potential coefficient, `thetaPrev = alpha * theta`,
--   `mu + eta`, and `eta <= alpha`; relevant hits were
--   `sum_Icc_two_coeff_telescope_le`,
--   `weighted_inverse_probability_adjacent_coeff_le`, and
--   `geometric_rate_of_terminal_budget`, which are respectively a telescope
--   consumer, a different inverse-probability dual coefficient bridge, and a
--   terminal-budget rate theorem. LeanSearch returned generic ordered
--   multiplication lemmas such as `mul_le_mul_left'` and
--   `le_mul_of_le_mul_of_nonneg_right`, not this compound adjacent coefficient
--   statement.
-- minimal hypotheses: generalized from setup fields to the pointwise scalar
--   facts `eta <= alpha * (mu + eta)`, `0 <= theta`, and
--   `thetaPrev = alpha * theta`; all other algorithm assumptions were removed.

/-- A scalar product is bounded by an adjacent product with an added term.

If the stepsize satisfies `eta <= alpha * (mu + eta)` and the previous weight is
`alpha * theta`, then multiplying by a nonnegative current weight gives the
adjacent coefficient bridge `theta * eta <= thetaPrev * (mu + eta)`.

Layer: Glue | Gap: Level 0 (weighted stepsize adjacent potential coefficient bridge)
Proof: multiply the scalar schedule inequality by the nonnegative current
  weight, then rewrite the previous weight as `alpha * theta` and normalize the
  commutative semiring product.
Source: Mathlib ordered commutative semiring multiplication monotonicity APIs
Used in: randomized primal-dual gradient primal-potential telescope coefficient
  handoff under constant stepsize and adjacent output weights
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec/proof/theorem_5_1
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized primal-dual gradient -/
theorem mul_le_mul_add_of_le_mul_add_of_nonneg_left_of_eq_mul
    {K : Type*} [CommSemiring K] [Preorder K] [PosMulMono K]
    {eta mu alpha theta thetaPrev : K}
    (heta_le : eta <= alpha * (mu + eta))
    (htheta_nonneg : 0 <= theta)
    (hthetaPrev : thetaPrev = alpha * theta) :
    theta * eta <= thetaPrev * (mu + eta) := by
  calc
    theta * eta <= theta * (alpha * (mu + eta)) :=
      mul_le_mul_of_nonneg_left heta_le htheta_nonneg
    _ = thetaPrev * (mu + eta) := by
      rw [hthetaPrev]
      ring


-- Promoted from Staging/prob_weighted_lipschitz_average_le_half_stepsize.lean
open scoped BigOperators

-- Generalization plan (G0):
-- concept/name: finite weighted-sum scalar half bound; orig was
--   theorem51_condition_50_division_free, renamed away from theorem number,
--   proposition condition numbering, and paper setup fields.
-- generality used: an explicit finite set and a linear ordered field; no
--   measure, filtration, independence, integrability, convexity, smoothness,
--   oracle, carrier, vector-space, or finite-dimensional structure is used.
-- portable call pattern: finite weighted scalar budgets with nonnegative
--   normalized weights and pointwise scaled bounds can reuse the same aggregate
--   half-coefficient conclusion before a terminal Young absorption.
-- counterargument checked: not paper-local traceability because the statement
--   is paper-free finite weighted scalar algebra; not a caller-side expression
--   because it packages the recurring passage from pointwise
--   `4 * a_i / m <= eta * tau * w_i` bounds and `sum w_i = 1` to an aggregate
--   half coefficient. No inner formula is extracted as a def because the
--   expression is a transient weighted-sum budget, not a recognized
--   mathematical object such as Bregman divergence or a prox objective.
-- minimal hypotheses: `0 < m`, `0 <= tau`, `0 <= eta`, pointwise
--   nonnegative weights on the finite set, normalized total weight, and the
--   pointwise scaled bounds; the upper weight bound is derived internally.

/-- A pointwise scaled bound gives a half bound for a normalized finite
weighted sum.

If nonnegative weights on a finite set sum to one and each summand satisfies
`4 * a_i / m <= eta * tau * w_i`, then
`(sum_i w_i * a_i) / (m * (1 + tau)) <= eta / 2`.

Layer: Glue | Gap: Level 0 (finite weighted scalar half bound)
Proof: derive `w_i <= 1` from nonnegativity and normalization, turn each
  pointwise bound into `w_i * a_i <= coeff * w_i` using `w_i ^ 2 <= w_i`,
  sum over the finite set, normalize by `sum_i w_i = 1`, and compare the
  resulting scalar fraction to `eta / 2`.
Source: Mathlib finite sums and ordered-field arithmetic -/
theorem finset_weighted_sum_div_le_half_of_pointwise_four_mul_div_le
    {ι R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (s : Finset ι) (p a : ι → R) (m tau eta : R)
    (hm_pos : 0 < m)
    (htau_nonneg : 0 ≤ tau)
    (heta_nonneg : 0 ≤ eta)
    (hp_nonneg : ∀ i ∈ s, 0 ≤ p i)
    (hpsum : (∑ i ∈ s, p i) = 1)
    (hpoint : ∀ i ∈ s, (4 * a i) / m ≤ eta * tau * p i) :
    (∑ i ∈ s, p i * a i) / (m * (1 + tau)) ≤ eta / 2 := by
  classical
  let coeff : R := m * eta * tau / 4
  have hm_ne : m ≠ 0 := ne_of_gt hm_pos
  have hcoeff_nonneg : 0 ≤ coeff := by
    dsimp [coeff]
    positivity
  have hp_le_one : ∀ i ∈ s, p i ≤ 1 := by
    intro i hi
    have hsingle : p i ≤ ∑ j ∈ s, p j :=
      Finset.single_le_sum (fun j hj => hp_nonneg j hj) hi
    simpa [hpsum] using hsingle
  have hpoint_weighted :
      ∀ i ∈ s, p i * a i ≤ coeff * p i := by
    intro i hi
    have hp_sq_le : p i ^ 2 ≤ p i := by
      nlinarith [hp_nonneg i hi, hp_le_one i hi]
    have hbase : (4 * a i) / m ≤ eta * tau * p i := hpoint i hi
    have ha_le : a i ≤ m * eta * tau * p i / 4 := by
      have hmul := mul_le_mul_of_nonneg_right hbase hm_pos.le
      have hmul' : 4 * a i ≤ eta * tau * p i * m := by
        calc
          4 * a i = (4 * a i) / m * m := by
            field_simp [hm_ne]
          _ ≤ eta * tau * p i * m := hmul
      nlinarith
    have hfirst : p i * a i ≤ coeff * p i ^ 2 := by
      have hmul := mul_le_mul_of_nonneg_left ha_le (hp_nonneg i hi)
      dsimp [coeff] at hmul ⊢
      nlinarith
    have hsecond : coeff * p i ^ 2 ≤ coeff * p i :=
      mul_le_mul_of_nonneg_left hp_sq_le hcoeff_nonneg
    exact le_trans hfirst hsecond
  have hsum_le : (∑ i ∈ s, p i * a i) ≤ coeff := by
    calc
      (∑ i ∈ s, p i * a i) ≤ ∑ i ∈ s, coeff * p i :=
        Finset.sum_le_sum (fun i hi => hpoint_weighted i hi)
      _ = coeff * (∑ i ∈ s, p i) := by
        rw [Finset.mul_sum]
      _ = coeff := by
        rw [hpsum, mul_one]
  have hden_pos : 0 < m * (1 + tau) := by
    exact mul_pos hm_pos (by nlinarith)
  have hscalar : coeff / (m * (1 + tau)) ≤ eta / 2 := by
    rw [div_le_iff₀ hden_pos]
    dsimp [coeff]
    nlinarith [hm_pos, htau_nonneg, heta_nonneg]
  exact le_trans (div_le_div_of_nonneg_right hsum_le hden_pos.le) hscalar


-- Promoted from Staging/inverse_probability_inner_half_absorb_of_lipschitz_budget.lean
open scoped InnerProductSpace

-- Generalization plan (G0):
-- concept/name: inverse_probability_inner_half_absorb_of_lipschitz_budget
--   exposes the scalar Lipschitz/probability budget that upgrades an
--   inverse-probability Young absorption to an `eta / 4` half-budget bound;
--   orig was theorem51_dual_young_absorb_inverse_inner_half_division_free.
-- generality used: real scalars and a real inner-product seminormed additive
--   group `[SeminormedAddCommGroup E] [InnerProductSpace ℝ E]`; no measure,
--   filtration, convexity, smoothness, oracle, or finite-dimensional
--   hypotheses are used once the pointwise quadratic lower budget is supplied.
-- portable call pattern: randomized block primal-dual, coordinate mirror-prox,
--   and variance-reduced coordinate proofs vary `m`, `p`, `L`, `tau`, `eta`,
--   the sampled displacement, and the budget value while reusing the same
--   condition `4 * L / m ≤ eta * tau * p` and `beta ^ 2 ≤ 1` to absorb an
--   inverse-probability cross term by `eta / 4 * ‖u‖ ^ 2`.
-- counterargument checked: not a duplicate of
--   `inverse_probability_inner_half_absorb_of_quadratic_budget`, which consumes
--   an explicit source quotient coefficient; this theorem proves the reusable
--   Lipschitz/probability reduction to the final `eta / 4` coefficient.
-- coverage search: searched CATALOG/SOptLib/Staging by `inverse_probability`,
--   `young_absorb_inner`, `half budget`, `lipschitz budget`, and
--   `quadratic_budget`; closest hits were
--   `inverse_probability_inner_half_absorb_of_quadratic_budget`,
--   `young_absorb_inner_of_norm_sq_budget`,
--   `young_absorb_average_inner_with_quadratic_budget`, and Mathlib
--   `Real.young_inequality`, all partial rather than this statement shape.
-- minimal hypotheses: positivity of `m`, `p`, and `eta`, nonnegativity of
--   `L` and `W`, the pointwise quadratic budget, the scalar
--   Lipschitz/probability inequality, and `beta ^ 2 ≤ 1` are exactly what the
--   proof uses; no probability measure or finite-dimensional assumption is
--   needed.

/-- A Lipschitz/probability scalar budget gives half-budget inverse-probability
Young absorption.

If the pointwise quadratic budget is available and the scalar condition
`4 * L / m ≤ eta * tau * p` holds, then the inverse-probability cross term with
`beta ^ 2 ≤ 1` is absorbed by the `eta / 4` squared-norm budget plus half of the
`tau * W` budget. The statement includes the degenerate `L = 0` branch, where
the quadratic budget forces the sampled displacement to vanish.

Layer: Glue | Gap: Level 1 (inverse-probability Lipschitz-budget Young absorption)
Proof: split on `L = 0`; in the positive branch call the quadratic-budget
  inverse-probability absorption theorem and use the Lipschitz/probability
  condition with `beta ^ 2 ≤ 1` to compare its coefficient with `eta / 4`.
Source: Mathlib real Hilbert-space Young inequality and ordered-field algebra
Used in: randomized primal-dual gradient sampled dual Bregman Young absorption
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized primal-dual gradient -/
theorem inverse_probability_inner_half_absorb_of_lipschitz_budget
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    {m p L tau eta beta W : ℝ} {u v : E}
    (hm_pos : 0 < m) (hp_pos : 0 < p) (heta_pos : 0 < eta)
    (hL_nonneg : 0 ≤ L) (hW_nonneg : 0 ≤ W)
    (hquad : m / 2 * ‖v‖ ^ 2 ≤ L * W)
    (hlip : 4 * L / m ≤ eta * tau * p)
    (hbeta_sq_le_one : beta ^ 2 ≤ 1) :
    - (eta / 4 * ‖u‖ ^ 2) ≤
      (1 / p) * beta * ⟪u, v⟫_ℝ + (tau / 2) * (1 / p) * W := by
  have hm_ne : m ≠ 0 := ne_of_gt hm_pos
  have hp_ne : p ≠ 0 := ne_of_gt hp_pos
  have htau_nonneg : 0 ≤ tau := by
    have hleft_nonneg : 0 ≤ 4 * L / m :=
      div_nonneg (mul_nonneg (by norm_num) hL_nonneg) (le_of_lt hm_pos)
    have hrhs_nonneg : 0 ≤ eta * tau * p := le_trans hleft_nonneg hlip
    have hprod_nonneg : 0 ≤ tau * (eta * p) := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using hrhs_nonneg
    exact nonneg_of_mul_nonneg_left hprod_nonneg (mul_pos heta_pos hp_pos)
  by_cases hL_zero : L = 0
  · have hquad_zero : m / 2 * ‖v‖ ^ 2 ≤ 0 := by
      simpa [hL_zero] using hquad
    have hnorm_sq_zero : ‖v‖ ^ 2 = 0 := by
      have hhalf_pos : 0 < m / 2 := by nlinarith
      have hmul_nonneg : 0 ≤ m / 2 * ‖v‖ ^ 2 :=
        mul_nonneg (le_of_lt hhalf_pos) (sq_nonneg _)
      have hmul_zero : m / 2 * ‖v‖ ^ 2 = 0 :=
        le_antisymm hquad_zero hmul_nonneg
      rcases mul_eq_zero.mp hmul_zero with hhalf_zero | hsq_zero
      · exact False.elim (ne_of_gt hhalf_pos hhalf_zero)
      · exact hsq_zero
    have hnorm_zero : ‖v‖ = 0 :=
      sq_eq_zero_iff.mp hnorm_sq_zero
    have hinner_zero : ⟪u, v⟫_ℝ = 0 := by
      have habs_le : |⟪u, v⟫_ℝ| ≤ 0 := by
        simpa [hnorm_zero] using abs_real_inner_le_norm u v
      exact abs_eq_zero.mp (le_antisymm habs_le (abs_nonneg _))
    have hright_nonneg :
        0 ≤ (1 / p) * beta * ⟪u, v⟫_ℝ + (tau / 2) * (1 / p) * W := by
      have hcoef_nonneg : 0 ≤ (tau / 2) * (1 / p) :=
        mul_nonneg (div_nonneg htau_nonneg (by norm_num))
          (one_div_nonneg.mpr (le_of_lt hp_pos))
      have hbudget_nonneg : 0 ≤ (tau / 2) * (1 / p) * W :=
        mul_nonneg hcoef_nonneg hW_nonneg
      rw [hinner_zero]
      simp only [mul_zero, zero_add]
      exact hbudget_nonneg
    have hleft_nonpos : - (eta / 4 * ‖u‖ ^ 2) ≤ 0 := by
      have hnonneg : 0 ≤ eta / 4 * ‖u‖ ^ 2 :=
        mul_nonneg (div_nonneg (le_of_lt heta_pos) (by norm_num)) (sq_nonneg _)
      nlinarith
    exact le_trans hleft_nonpos hright_nonneg
  · have hL_pos : 0 < L := lt_of_le_of_ne hL_nonneg (Ne.symm hL_zero)
    have htau_pos : 0 < tau := by
      have hleft_pos : 0 < 4 * L / m :=
        div_pos (mul_pos (by norm_num) hL_pos) hm_pos
      have hrhs_pos : 0 < eta * tau * p := lt_of_lt_of_le hleft_pos hlip
      have hprod_pos : 0 < tau * (eta * p) := by
        simpa [mul_assoc, mul_comm, mul_left_comm] using hrhs_pos
      exact pos_of_mul_pos_left hprod_pos (mul_pos heta_pos hp_pos).le
    have hden_pos : 0 < m * tau * p := mul_pos (mul_pos hm_pos htau_pos) hp_pos
    have hquot :
        (L * beta ^ 2) / (m * tau * p) ≤ eta / 4 := by
      have hfourLbeta_le : 4 * L * beta ^ 2 ≤ 4 * L := by
        have hscale :
            (4 * L) * beta ^ 2 ≤ (4 * L) * 1 :=
          mul_le_mul_of_nonneg_left hbeta_sq_le_one
            (mul_nonneg (by norm_num) hL_nonneg)
        nlinarith
      have hmain : 4 * L ≤ eta * tau * p * m := by
        have hm_mul := mul_le_mul_of_nonneg_right hlip hm_pos.le
        calc
          4 * L = (4 * L) / m * m := by
            field_simp [hm_ne]
          _ ≤ eta * tau * p * m := hm_mul
      have hcross : 4 * (L * beta ^ 2) ≤ eta * (m * tau * p) := by
        nlinarith [hfourLbeta_le, hmain]
      rw [div_le_iff₀ hden_pos]
      nlinarith [hcross]
    have hleft_le :
        - (eta / 4 * ‖u‖ ^ 2) ≤
          - (((L * beta ^ 2) / (m * tau * p)) * ‖u‖ ^ 2) := by
      have hmul := mul_le_mul_of_nonneg_right hquot (sq_nonneg ‖u‖)
      nlinarith
    have hbase :=
      inverse_probability_inner_half_absorb_of_quadratic_budget
        (E := E) (m := m) (τ := tau) (p := p) (L := L) (β := beta)
        (W := W) (u := u) (v := v)
        hm_pos htau_pos hp_pos hL_nonneg hW_nonneg hquad
    exact le_trans hleft_le hbase


-- Promoted from Staging/geometric_rate_of_terminal_budget.lean
-- Generalization plan (G0):
-- concept/name: geometric rate from a terminal weighted budget; orig was
--   theorem51_expected_bregman_distance_rate_from_terminal_budget, renamed away
--   from the theorem number and expected-Bregman paper wrapper.
-- generality used: real scalar coefficients and natural-number powers only; no
--   carrier type, measure, filtration, independence, integrability, convexity,
--   smoothness, oracle, or finite-dimensional hypotheses are used after the
--   terminal potential budget has been proved.
-- portable call pattern: stochastic mirror-descent, primal-dual, accelerated,
--   and proximal convergence proofs can call this after deriving a terminal
--   potential budget with inverse-geometric weight `alpha^{-t}`; `F`, `V0`,
--   `mu`, `eta`, `Lf`, `alpha`, and `t` vary while the final geometric rate has
--   the same shape.
-- counterargument checked: not paper-local traceability and not a pure wrapper;
--   the statement packages the recurring scalar handoff from a weighted
--   terminal budget to an unweighted geometric rate. It is not decomposed into a
--   def because the expression is coefficient normalization, not a separate
--   recognized mathematical object like a Bregman divergence or prox objective.
-- coverage search: searched SOptLib catalog/source for geometric rate, terminal
--   budget, budget rate, `alpha ^ t`, `eta / alpha`, and division budget;
--   relevant partial hits included `geometric_rate_from_cutoff_potential_bound`
--   and `gap_le_pow_rate_of_four_mul_budget`, which cover different
--   coefficient-normalization shapes. LeanSearch returned generic `div_le` and
--   ordered-field division lemmas, not this compound terminal-budget handoff.
-- minimal hypotheses: pointwise scalar assumptions only: `0 < alpha`,
--   `1 - alpha ≠ 0`, `0 < eta`, the coefficient condition
--   `eta <= alpha * (mu + eta)`, nonnegativity of `F`, and the terminal budget.

/-- A terminal inverse-geometric budget gives an unweighted geometric rate.

If a nonnegative quantity `F` appears in a terminal budget with coefficient
`(mu + eta) * alpha^{-t}`, and `eta <= alpha * (mu + eta)`, then dividing by the
positive lower coefficient gives the rate
`F <= (1 + Lf * alpha / ((1 - alpha) * eta)) * alpha^t * V0`.

Layer: Glue | Gap: Level 1 (terminal-budget geometric rate handoff)
Proof: lower-bound the terminal coefficient by `(eta / alpha) * alpha^{-t}`,
  divide by that positive factor, and simplify the resulting real scalar
  quotient by ordered-field arithmetic.
Source: Mathlib real ordered-field division, natural powers, and monotonicity
  of multiplication over inequalities
Used in: randomized primal-dual gradient terminal Bregman-distance rate
  extraction after the weighted terminal potential budget
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec/convergence/theorem_5_1
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized primal-dual gradient -/
theorem geometric_rate_of_terminal_budget
    (mu eta alpha Lf F V0 : ℝ) (t : ℕ)
    (h_alpha_pos : 0 < alpha)
    (h_one_sub_ne : 1 - alpha ≠ 0)
    (h_eta_pos : 0 < eta)
    (h_eta_le : eta ≤ alpha * (mu + eta))
    (hF_nonneg : 0 ≤ F)
    (hbudget :
      (mu + eta) * (1 / alpha ^ t) * F ≤
        eta * (1 / alpha) * V0 +
          (1 / alpha) * (alpha / (1 - alpha)) * (Lf * V0)) :
    F ≤ (1 + (Lf * alpha) / ((1 - alpha) * eta)) * alpha ^ t * V0 := by
  have h_alpha_ne : alpha ≠ 0 := ne_of_gt h_alpha_pos
  have h_eta_ne : eta ≠ 0 := ne_of_gt h_eta_pos
  have hpow_pos : 0 < alpha ^ t := pow_pos h_alpha_pos t
  have hpow_ne : alpha ^ t ≠ 0 := pow_ne_zero t h_alpha_ne
  have hBudgetClean :
      (mu + eta) * ((1 / alpha ^ t) * F) ≤
        (eta / alpha + Lf / (1 - alpha)) * V0 := by
    have hleft :
        (mu + eta) * (1 / alpha ^ t) * F =
          (mu + eta) * ((1 / alpha ^ t) * F) := by ring
    have hright :
        eta * (1 / alpha) * V0 +
            (1 / alpha) * (alpha / (1 - alpha)) * (Lf * V0) =
          (eta / alpha + Lf / (1 - alpha)) * V0 := by
      field_simp [h_alpha_ne, h_one_sub_ne]
    rw [hleft, hright] at hbudget
    exact hbudget
  have hcoef : eta / alpha ≤ mu + eta := by
    rw [div_le_iff₀ h_alpha_pos]
    simpa [mul_comm, mul_left_comm, mul_assoc] using h_eta_le
  have hfactor_nonneg : 0 ≤ (1 / alpha ^ t) * F :=
    mul_nonneg (one_div_pos.mpr hpow_pos).le hF_nonneg
  have hLower :
      (eta / alpha) * ((1 / alpha ^ t) * F) ≤
        (mu + eta) * ((1 / alpha ^ t) * F) :=
    mul_le_mul_of_nonneg_right hcoef hfactor_nonneg
  have hScaledBudget :
      (eta / alpha) * ((1 / alpha ^ t) * F) ≤
        (eta / alpha + Lf / (1 - alpha)) * V0 :=
    le_trans hLower hBudgetClean
  have hscale_pos : 0 < (eta / alpha) * (1 / alpha ^ t) :=
    mul_pos (div_pos h_eta_pos h_alpha_pos) (one_div_pos.mpr hpow_pos)
  have hF_le_div :
      F ≤ ((eta / alpha + Lf / (1 - alpha)) * V0) /
        ((eta / alpha) * (1 / alpha ^ t)) := by
    rw [le_div_iff₀ hscale_pos]
    simpa [mul_assoc, mul_comm, mul_left_comm] using hScaledBudget
  have hscalar :
      ((eta / alpha + Lf / (1 - alpha)) * V0) /
          ((eta / alpha) * (1 / alpha ^ t)) =
        (1 + (Lf * alpha) / ((1 - alpha) * eta)) * alpha ^ t * V0 := by
    field_simp [h_alpha_ne, h_one_sub_ne, h_eta_ne, hpow_ne]
  exact le_trans hF_le_div (le_of_eq hscalar)


-- Promoted from Staging/final_gap_geometric_scalar_combine.lean
-- Generalization plan (G0):
-- concept/name: scalar half-geometric coefficient combiner; renamed away from
--   the theorem number and paper-local wrapper.
-- generality used: real scalar coefficients and natural-number powers only; no
--   carrier type, measure, filtration, independence, integrability, convexity,
--   smoothness, oracle, or finite-dimensional hypotheses are used after the two
--   contribution bounds have been proved.
-- portable call pattern: stochastic mirror-descent, primal-dual, accelerated,
--   and proximal convergence proofs can call this after separately bounding two
--   additive scalar contributions by an `alpha^k` term and an `alpha^(k/2)`
--   term; the scalar coefficients vary while the final half-geometric
--   coefficient algebra stays the same.
-- counterargument checked: not paper-local traceability and not a pure wrapper;
--   the statement packages recurring scalar coefficient normalization from two
--   convergence contributions to one final rate. It is not decomposed into a def
--   because the expression is coefficient algebra, not a recognized named
--   mathematical object.
-- coverage search: searched SOptLib catalog/source and staging for geometric
--   scalar combine, half-geometric, `Real.rpow`, `alpha ^ k`, and the
--   `(3 - 2 * alpha) / (1 - alpha)` coefficient shape. Relevant hits such as
--   `geometric_rate_of_terminal_budget`, `inv_nat_pow_eq_rpow_neg_mul`, and
--   `rpow_tail_prefactor_le_of_ratio_le` cover terminal-budget or rpow
--   primitives, not this two-contribution coefficient combiner. LeanSearch
--   returned Mathlib's `Real.rpow_le_rpow_of_exponent_ge` as the exponent
--   monotonicity ingredient but no full scalar-combination lemma.
-- minimal hypotheses: pointwise scalar assumptions only: `0 < alpha`,
--   `alpha < 1`, the one needed denominator nonzeroness, the localized
--   nonnegativity of the product multiplied across `alpha^k ≤ alpha^(k/2)`,
--   plus the two input contribution bounds.

/-- Combine an `alpha^k` contribution and a half-geometric contribution into one
half-geometric scalar bound.

If the first term is bounded by
`alpha^k * ((c / alpha) + d / (1 - alpha)) * v` and the second by the
corresponding half-geometric coefficient, then their sum is bounded by the
single `alpha^(k/2)` expression with the collected
`(3 - 2 * alpha) / (1 - alpha)` coefficient.

Layer: Glue | Role: Level 1 half-geometric scalar coefficient combiner
Proof: use monotonicity of `Real.rpow` on bases in `(0,1)` to replace
  `alpha^k` by `alpha^(k/2)`, add the two contribution bounds, and normalize
  the resulting ordered-field expression.
Source: Mathlib real powers, ordered-field division, and monotonicity of
  multiplication over inequalities
Used in: convergence-rate assembly after two scalar contribution estimates have
  been proved
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec/convergence/theorem_5_1
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized primal-dual gradient -/
theorem add_le_rpow_half_mul_collected_coeff_of_le_pow_and_le_rpow_half
    (c alpha d v term₁ term₂ : ℝ) (k : ℕ)
    (h_alpha_pos : 0 < alpha)
    (h_alpha_lt_one : alpha < 1)
    (hc_ne : c ≠ 0)
    (hprod_nonneg : 0 ≤ (((1 / alpha) * c + (1 / (1 - alpha)) * d) * v))
    (hterm₁ :
      term₁ ≤
        alpha ^ k * ((1 / alpha) * c + (1 / (1 - alpha)) * d) * v)
    (hterm₂ :
      term₂ ≤
        d *
          (2 * Real.rpow alpha ((k : ℝ) / 2) *
            (1 + (d * alpha) / ((1 - alpha) * c)) * v)) :
    term₁ + term₂ ≤
      Real.rpow alpha ((k : ℝ) / 2) *
        ((1 / alpha) * c +
          ((3 - 2 * alpha) / (1 - alpha)) * d +
          (2 * d ^ 2 * alpha) / ((1 - alpha) * c)) *
        v := by
  let R : ℝ := Real.rpow alpha ((k : ℝ) / 2)
  let A : ℝ := (1 / alpha) * c + (1 / (1 - alpha)) * d
  let B : ℝ := 1 + (d * alpha) / ((1 - alpha) * c)
  have hpow_le_rpow : alpha ^ k ≤ R := by
    have hkhalf : (k : ℝ) / 2 ≤ (k : ℝ) := by
      nlinarith [show (0 : ℝ) ≤ (k : ℝ) from Nat.cast_nonneg k]
    have hrpow :
        Real.rpow alpha (k : ℝ) ≤ R :=
      Real.rpow_le_rpow_of_exponent_ge h_alpha_pos h_alpha_lt_one.le hkhalf
    simpa [R, Real.rpow_natCast] using hrpow
  have hAv_nonneg : 0 ≤ A * v := by
    simpa [A] using hprod_nonneg
  have hterm₁_rpow : alpha ^ k * A * v ≤ R * A * v := by
    have h := mul_le_mul_of_nonneg_right hpow_le_rpow hAv_nonneg
    simpa [R, mul_assoc] using h
  have hsum :
      term₁ + term₂ ≤ R * A * v + d * (2 * R * B * v) :=
    add_le_add (le_trans (by simpa [A, mul_assoc] using hterm₁) hterm₁_rpow)
      (by simpa [R, B, mul_assoc] using hterm₂)
  refine le_trans hsum ?_
  have h_alpha_ne : alpha ≠ 0 := ne_of_gt h_alpha_pos
  have h_one_sub_ne : 1 - alpha ≠ 0 := by
    exact sub_ne_zero.mpr (ne_of_gt h_alpha_lt_one)
  have h_den_ne : (1 - alpha) * c ≠ 0 := mul_ne_zero h_one_sub_ne hc_ne
  have hscalar :
      R * A * v + d * (2 * R * B * v) =
        Real.rpow alpha ((k : ℝ) / 2) *
          ((1 / alpha) * c +
            ((3 - 2 * alpha) / (1 - alpha)) * d +
            (2 * d ^ 2 * alpha) / ((1 - alpha) * c)) *
          v := by
    dsimp [A, B, R]
    field_simp [h_alpha_ne, h_one_sub_ne, hc_ne, h_den_ne]
    ring
  exact le_of_eq hscalar


-- Promoted from Staging/inv_mul_one_add_sub_one_le_div_of_mul_one_add_le.lean
-- Generalization plan (G0):
-- concept/name: inverse-probability endpoint coefficient bound; orig was
--   theorem51_inverse_probability_initial_coefficient_le, renamed away from
--   the theorem number and paper-specific sampling-probability wrapper.
-- generality used: an arbitrary linear ordered field and three scalar
--   parameters only; no measure, filtration, independence, integrability,
--   convexity, smoothness, oracle, carrier, or finite-dimensional hypotheses
--   are used once the probability lower bound is available.
-- portable call pattern: randomized coordinate, importance-sampling, and
--   block-coordinate primal-dual analyses can call this after proving a lower
--   sampling-probability bound `(1 - alpha) * (1 + tau) <= p`; the meanings of
--   `alpha`, `tau`, and `p` vary while the reciprocal endpoint coefficient
--   bound keeps the same shape.
-- counterargument checked: not paper-local traceability and not a pure wrapper;
--   the statement packages a recurring reciprocal-coefficient handoff. It is
--   not decomposed into a def because the expression is scalar coefficient
--   algebra, not a separate recognized object like a probability law or prox
--   objective.
-- coverage search: searched SOptLib catalog/source for inverse probability,
--   reciprocal coefficient, one_add, div one_sub, and mul_one_add; relevant
--   partial hits covered inverse-product absorption and oracle
--   inverse-probability integrability, not this endpoint bound. LeanSearch
--   returned Mathlib `one_div_le_one_div_of_le` and related reciprocal
--   monotonicity lemmas, which are proof ingredients rather than the compound
--   coefficient inequality.
-- minimal hypotheses: all already minimal for this ordered-field proof:
--   `0 < p`, `0 < 1 - alpha`, and `(1 - alpha) * (1 + tau) <= p`.

/-- A lower bound on a positive sampling scalar controls the reciprocal endpoint
coefficient.

If `(1 - alpha) * (1 + tau)` is at most a positive scalar `p` and
`1 - alpha` is positive, then the inverse-scaled coefficient
`p⁻¹ * (1 + tau) - 1` is bounded by `alpha / (1 - alpha)`.

Layer: Glue | Gap: Level 0 (ordered-field reciprocal coefficient bound)
Proof: clear the positive denominators `p` and `1 - alpha` by field
  simplification, then the remaining inequality is exactly the supplied lower
  bound after ordered-ring normalization.
Source: Mathlib ordered-field division and positivity APIs
Used in: randomized primal-dual gradient endpoint inverse-probability
  coefficient bound before applying the initial dual-distance estimate
Book citation: book/FOML/RandomPrimalDualGradient.json#/main_theorem/proof/step_4
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized primal-dual gradient -/
theorem inv_mul_one_add_sub_one_le_div_of_mul_one_add_le
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {alpha tau p : K}
    (hp_pos : 0 < p)
    (hone_sub_pos : 0 < 1 - alpha)
    (hprob : (1 - alpha) * (1 + tau) ≤ p) :
    p⁻¹ * (1 + tau) - 1 ≤ alpha / (1 - alpha) := by
  field_simp [ne_of_gt hp_pos, ne_of_gt hone_sub_pos]
  nlinarith [hprob]


-- Promoted from Staging/one_based_geometric_half_ratio_le.lean
open scoped BigOperators

-- Generalization plan (G0):
-- concept/name: one-based geometric half-ratio bound; orig was
--   `theorem51_output_weight_half_geometric_bound`, renamed away from the
--   theorem number and output-weight vocabulary to expose the scalar ratio of
--   a geometric numerator to a squared-geometric denominator.
-- generality used: linear ordered-field arithmetic over a base `q`; no measure,
--   filtration, convexity, smoothness, oracle, vector-space, or finite
--   dimensional assumptions are involved.
-- portable call pattern: geometric weighted-output rate proofs instantiate the
--   growth base `q > 1` and terminal time `k`, while the normalized
--   half-power mass bound stays unchanged across primal-dual, mirror-descent,
--   and accelerated weighted-average estimates.
-- counterargument checked: this is not paper-local traceability because the
--   statement contains only one-based finite geometric sums and a scalar
--   normalized ratio; it is not a one-line wrapper around Mathlib, since
--   Mathlib's geometric-sum facts give closed forms but not this ratio bound.
-- coverage search: searched project/catalog/source for `geometric`, `Icc`,
--   `half ratio`, `output weight sum`, and `one_based`; the relevant existing
--   staged hit is `sum_Icc_one_pow_mul_sub_eq_pow_succ_sub`, which supplies
--   only the closed-form geometric-sum identity. LeanSearch returned Mathlib
--   `geom_sum_mul`, `geom_sum_of_lt_one`, `sum_geometric_two_le`, and
--   `tsum_geometric_inv_two_ge`; these are range/tail formulas or base-two
--   bounds, not the normalized one-based ratio here.
-- minimal hypotheses: generalized from `0 < alpha < 1` and
--   `q = alpha^(-1/2)` to the only scalar fact used by the proof, `1 < q`;
--   the empty-window case `k = 0` is handled directly.

/-- A one-based geometric half-ratio is bounded by twice the inverse terminal
power.

For a growth base `q > 1`, the ratio between the one-based sum of `q^t` and the
one-based sum of `(q^2)^t` is at most `2 / q^k`. This packages the scalar
normalizer estimate used when half-power geometric error bounds are averaged
with full-power geometric output weights.

Layer: Glue | Gap: Level 1 (one-based geometric half-ratio normalizer)
Proof: evaluate both one-based geometric sums by the closed-form `Icc 1 k`
  identity, clear positive factors, and reduce the remaining comparison to
  ordered-field arithmetic.
Source: Mathlib finite geometric sums, ordered-field powers, and real
  inequality arithmetic
Used in: randomized primal-dual gradient weighted-output Bregman average rate
  normalization from half-power decay to terminal half-power decay
Book citation: book/FOML/RandomPrimalDualGradient.json#/main_theorem/proof/14
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized primal-dual gradient -/
theorem one_based_geometric_half_ratio_le {K : Type*}
    [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (q : K) (k : ℕ) (hq_gt_one : 1 < q) :
    (∑ t ∈ Finset.Icc 1 k, (q ^ 2) ^ t)⁻¹ *
        ∑ t ∈ Finset.Icc 1 k, q ^ t ≤
      2 * (q ^ k)⁻¹ := by
  classical
  by_cases hk0 : k = 0
  · subst k
    simp
  have hk : 1 ≤ k := by omega
  have hq_pos : 0 < q := lt_trans zero_lt_one hq_gt_one
  have hq_ne_one : q - 1 ≠ 0 := sub_ne_zero.mpr hq_gt_one.ne'
  have hq_sq_ne_one : q ^ 2 - 1 ≠ 0 := by
    have hq_sq_gt_one : 1 < q ^ 2 := by nlinarith [hq_gt_one]
    exact sub_ne_zero.mpr hq_sq_gt_one.ne'
  have hnum_geom :
      (∑ t ∈ Finset.Icc 1 k, q ^ t) * (q - 1) =
        q ^ (k + 1) - q := by
    exact sum_Icc_one_pow_mul_sub_eq_pow_succ_sub q k
  have hden_geom :
      (∑ t ∈ Finset.Icc 1 k, (q ^ 2) ^ t) * (q ^ 2 - 1) =
        (q ^ 2) ^ (k + 1) - q ^ 2 := by
    exact sum_Icc_one_pow_mul_sub_eq_pow_succ_sub (q ^ 2) k
  have hnum_closed :
      (∑ t ∈ Finset.Icc 1 k, q ^ t) =
        q * (q ^ k - 1) / (q - 1) := by
    rw [eq_div_iff hq_ne_one]
    rw [hnum_geom]
    ring
  have hpow_sq : (q ^ 2) ^ k = (q ^ k) ^ 2 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
  have hden_closed :
      (∑ t ∈ Finset.Icc 1 k, (q ^ 2) ^ t) =
        q ^ 2 * ((q ^ k) ^ 2 - 1) / (q ^ 2 - 1) := by
    rw [eq_div_iff hq_sq_ne_one]
    rw [hden_geom]
    rw [pow_succ', hpow_sq]
    ring
  have hqk_gt_one : 1 < q ^ k := one_lt_pow₀ hq_gt_one (by omega)
  have hqk_pos : 0 < q ^ k := lt_trans zero_lt_one hqk_gt_one
  have hq_ne_zero : q ≠ 0 := ne_of_gt hq_pos
  have hqminus_pos : 0 < q - 1 := sub_pos.mpr hq_gt_one
  have hq_sqminus_pos : 0 < q ^ 2 - 1 := by nlinarith [hq_gt_one]
  have hqk_sub_pos : 0 < q ^ k - 1 := sub_pos.mpr hqk_gt_one
  have hqk_sq_sub_pos : 0 < (q ^ k) ^ 2 - 1 := by
    nlinarith [hqk_gt_one]
  have hden_pos :
      0 < ∑ t ∈ Finset.Icc 1 k, (q ^ 2) ^ t := by
    rw [hden_closed]
    exact div_pos
      (mul_pos (sq_pos_of_ne_zero hq_ne_zero) hqk_sq_sub_pos)
      hq_sqminus_pos
  have hcross_poly :
      (q ^ k) * (q + 1) ≤ 2 * q * (q ^ k + 1) := by
    nlinarith [hq_gt_one, hqk_gt_one]
  have hcross_sums :
      (q ^ k) * (∑ t ∈ Finset.Icc 1 k, q ^ t) ≤
        2 * (∑ t ∈ Finset.Icc 1 k, (q ^ 2) ^ t) := by
    rw [hnum_closed, hden_closed]
    rw [← mul_div_assoc, ← mul_div_assoc]
    rw [div_le_div_iff₀ hqminus_pos hq_sqminus_pos]
    have hscale_nonneg : 0 ≤ q * (q ^ k - 1) :=
      (mul_pos hq_pos hqk_sub_pos).le
    have hscaled :=
      mul_le_mul_of_nonneg_left hcross_poly hscale_nonneg
    nlinarith [hscaled]
  have hdiv :
      (∑ t ∈ Finset.Icc 1 k, q ^ t) /
          (∑ t ∈ Finset.Icc 1 k, (q ^ 2) ^ t) ≤
        2 / (q ^ k) := by
    rw [div_le_div_iff₀ hden_pos hqk_pos]
    simpa [mul_assoc, mul_comm, mul_left_comm] using hcross_sums
  simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hdiv

/-- A contraction-base half-geometric output normalizer is bounded by the
terminal half power.

This is the `α`-contraction specialization of
`one_based_geometric_half_ratio_le`, with `q = α^(-1/2)`. The denominator is
written as the full inverse-power geometric mass and the numerator as the
half-power mass used in contraction-rate estimates.

Layer: Glue | Gap: Level 1 (contraction half-geometric normalizer)
Proof: instantiate the geometric half-ratio theorem at `q = α^(-1/2)`, then
  convert natural powers of `q` to the displayed real-power contraction form.
Source: Mathlib real-power arithmetic, ordered-field powers, and finite
  geometric sums
Used in: randomized primal-dual gradient weighted-output Bregman average rate
  normalization from half-power decay to terminal half-power decay
Book citation: book/FOML/RandomPrimalDualGradient.json#/main_theorem/proof/14
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized primal-dual gradient -/
theorem one_based_geometric_half_ratio_rpow_le (α : ℝ) (k : ℕ)
    (hα_pos : 0 < α) (hα_lt_one : α < 1) :
    (∑ t ∈ Finset.Icc 1 k, (α ^ t)⁻¹)⁻¹ *
        ∑ t ∈ Finset.Icc 1 k, Real.rpow α (-(t : ℝ) / 2) ≤
      2 * Real.rpow α ((k : ℝ) / 2) := by
  classical
  by_cases hk0 : k = 0
  · subst k
    simp
  let q : ℝ := Real.rpow α (-(1 : ℝ) / 2)
  have hq_gt_one : 1 < q := by
    dsimp [q]
    exact Real.one_lt_rpow_of_pos_of_lt_one_of_neg hα_pos hα_lt_one (by norm_num)
  have hqpow (t : ℕ) :
      Real.rpow α (-(t : ℝ) / 2) = q ^ t := by
    dsimp [q]
    calc
      Real.rpow α (-(t : ℝ) / 2)
          = Real.rpow α ((-(1 : ℝ) / 2) * (t : ℝ)) := by
              congr 1
              ring
      _ = (Real.rpow α (-(1 : ℝ) / 2)) ^ t :=
              Real.rpow_mul_natCast hα_pos.le (-(1 : ℝ) / 2) t
  have hden_eq :
      (∑ t ∈ Finset.Icc 1 k, (α ^ t)⁻¹) =
        ∑ t ∈ Finset.Icc 1 k, (q ^ 2) ^ t := by
    refine Finset.sum_congr rfl ?_
    intro t ht
    have hinv :
        (α ^ t)⁻¹ = Real.rpow α (-(t : ℝ)) := by
      simpa [pow_one, one_mul] using
        (inv_nat_pow_eq_rpow_neg_mul α 1 t)
    have hq2 :
        (q ^ 2) ^ t = Real.rpow α (-(t : ℝ)) := by
      rw [← pow_mul]
      rw [← hqpow (2 * t)]
      congr 1
      norm_num
      ring
    rw [hinv]
    exact hq2.symm
  have hnum_eq :
      (∑ t ∈ Finset.Icc 1 k, Real.rpow α (-(t : ℝ) / 2)) =
        ∑ t ∈ Finset.Icc 1 k, q ^ t := by
    refine Finset.sum_congr rfl ?_
    intro t ht
    exact hqpow t
  have hrhs :
      Real.rpow α ((k : ℝ) / 2) = (q ^ k)⁻¹ := by
    have hkq :
        q ^ k = (Real.rpow α ((k : ℝ) / 2))⁻¹ := by
      calc
        q ^ k = Real.rpow α (-(k : ℝ) / 2) := by
          rw [← hqpow k]
        _ = Real.rpow α (-((k : ℝ) / 2)) := by
          congr 1
          ring
        _ = (Real.rpow α ((k : ℝ) / 2))⁻¹ :=
          Real.rpow_neg hα_pos.le ((k : ℝ) / 2)
    rw [hkq]
    simp
  rw [hden_eq, hnum_eq, hrhs]
  exact one_based_geometric_half_ratio_le q k hq_gt_one


-- Promoted from Staging/weighted_average_geometric_rate_le_half_power.lean
open scoped BigOperators

-- Generalization plan (G0):
-- concept/name: weighted average geometric rate half-power bound; orig was
--   `theorem51_weighted_bregman_average_rate`, renamed away from the theorem
--   number and Bregman/output vocabulary to expose the scalar finite-window
--   aggregation step.
-- generality used: real scalar sequence `F`, constants `C` and `V0`, a
--   contraction base `alpha`, and one-based finite sums; no carrier type,
--   measure, filtration, independence, integrability, convexity, smoothness,
--   oracle, or finite-dimensional hypotheses are used after the pointwise
--   geometric rate is available.
-- portable call pattern: stochastic mirror-descent, primal-dual, accelerated,
--   proximal, and variance-reduced convergence proofs can call this after
--   proving per-time rates `F t <= C * alpha^t * V0` and choosing
--   inverse-power output weights; `F`, `C`, `V0`, `alpha`, and the window end
--   vary while the normalized half-power conclusion stays fixed.
-- counterargument checked: not paper-local traceability and not a pure wrapper;
--   the statement combines pointwise geometric rates, nonnegative inverse
--   weighting, half-power loosening, and the finite geometric normalizer. It is
--   not decomposed into a def because the displayed expression is scalar
--   coefficient aggregation, not a separate recognized mathematical object.
-- coverage search: searched SOptLib/catalog/source and staging for weighted
--   average geometric rate, half power, normalized output, inverse-power
--   weights, and one-based geometric ratios. Relevant partial hits were
--   `one_based_geometric_half_ratio_rpow_le`, which proves only the scalar
--   normalizer, `expected_bound_of_weighted_sum_bound`, which transports an
--   already-proved numerator bound, and `inverse_power_weight`, which names the
--   weight schedule but does not aggregate rates. LeanSearch returned
--   `Finset.centerMass` and Jensen/mean inequalities, not this finite
--   inverse-geometric rate aggregation.
-- minimal hypotheses: pointwise scalar assumptions only: `0 < alpha`,
--   `alpha < 1`, nonnegativity of `C * V0`, and the per-time geometric upper
--   bound on `F` over `Icc 1 k`; the empty-window case is handled directly.

/-- A weighted average of geometric-rate terms has a terminal half-power rate.

If `F t` is bounded on the one-based window by `C * alpha^t * V0`, then the
finite average weighted by inverse powers `alpha^{-t}` is bounded by
`2 * alpha^(k/2) * C * V0`.

Layer: Glue | Gap: Level 1 (inverse-geometric weighted-average rate aggregation)
Proof: multiply the pointwise rate by nonnegative inverse-power weights, cancel
  the matching `alpha^t` factor, loosen the constant numerator by
  `alpha^{-t/2}`, and apply the one-based half-geometric normalizer bound.
Source: Mathlib real powers, finite sums over natural intervals, and ordered
  real-field inequality APIs
Used in: randomized primal-dual gradient weighted-output Bregman average rate
  normalization after per-time geometric Bregman-distance estimates
Book citation: book/FOML/RandomPrimalDualGradient.json#/main_theorem/proof/14
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized primal-dual gradient -/
theorem weighted_average_geometric_rate_le_half_power
    (alpha C V0 : ℝ) (k : ℕ) (F : ℕ → ℝ)
    (halpha_pos : 0 < alpha)
    (halpha_lt_one : alpha < 1)
    (hCV_nonneg : 0 ≤ C * V0)
    (hF : ∀ t ∈ Finset.Icc 1 k, F t ≤ C * alpha ^ t * V0) :
    (∑ t ∈ Finset.Icc 1 k, (alpha ^ t)⁻¹)⁻¹ *
        ∑ t ∈ Finset.Icc 1 k, (alpha ^ t)⁻¹ * F t ≤
      2 * Real.rpow alpha ((k : ℝ) / 2) * C * V0 := by
  classical
  by_cases hk0 : k = 0
  · subst k
    have hnonneg : 0 ≤ 2 * (C * V0) :=
      mul_nonneg (by norm_num) hCV_nonneg
    simpa [mul_assoc] using hnonneg
  have hk : 1 ≤ k := by omega
  have halpha_ne : alpha ≠ 0 := ne_of_gt halpha_pos
  have hsum_le :
      (∑ t ∈ Finset.Icc 1 k, (alpha ^ t)⁻¹ * F t) ≤
        ∑ t ∈ Finset.Icc 1 k, Real.rpow alpha (-(t : ℝ) / 2) * (C * V0) := by
    refine Finset.sum_le_sum ?_
    intro t ht
    have hweight_nonneg : 0 ≤ (alpha ^ t)⁻¹ :=
      inv_nonneg.mpr (pow_nonneg halpha_pos.le t)
    have hweighted :
        (alpha ^ t)⁻¹ * F t ≤ (alpha ^ t)⁻¹ * (C * alpha ^ t * V0) :=
      mul_le_mul_of_nonneg_left (hF t ht) hweight_nonneg
    have hcollapse :
        (alpha ^ t)⁻¹ * (C * alpha ^ t * V0) = C * V0 := by
      field_simp [pow_ne_zero t halpha_ne]
    have hexp_nonpos : -(t : ℝ) / 2 ≤ 0 := by
      have ht_nonneg : 0 ≤ (t : ℝ) := Nat.cast_nonneg t
      nlinarith
    have hrpow_ge_one : 1 ≤ Real.rpow alpha (-(t : ℝ) / 2) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos halpha_pos halpha_lt_one.le
        hexp_nonpos
    have hloosen : C * V0 ≤ Real.rpow alpha (-(t : ℝ) / 2) * (C * V0) := by
      simpa [one_mul] using
        mul_le_mul_of_nonneg_right hrpow_ge_one hCV_nonneg
    exact hweighted.trans (by simpa [hcollapse] using hloosen)
  have hmass_pos : 0 < ∑ t ∈ Finset.Icc 1 k, (alpha ^ t)⁻¹ := by
    have hnonneg :
        ∀ t ∈ Finset.Icc 1 k, 0 ≤ (alpha ^ t)⁻¹ := by
      intro t _ht
      exact inv_nonneg.mpr (pow_nonneg halpha_pos.le t)
    have hmem : 1 ∈ Finset.Icc 1 k := Finset.mem_Icc.mpr ⟨le_rfl, hk⟩
    have hpos : 0 < (alpha ^ 1)⁻¹ := inv_pos.mpr (pow_pos halpha_pos 1)
    exact Finset.sum_pos' hnonneg ⟨1, hmem, hpos⟩
  have hnormalized_le :
      (∑ t ∈ Finset.Icc 1 k, (alpha ^ t)⁻¹)⁻¹ *
          ∑ t ∈ Finset.Icc 1 k, (alpha ^ t)⁻¹ * F t ≤
        (∑ t ∈ Finset.Icc 1 k, (alpha ^ t)⁻¹)⁻¹ *
          ∑ t ∈ Finset.Icc 1 k, Real.rpow alpha (-(t : ℝ) / 2) * (C * V0) :=
    mul_le_mul_of_nonneg_left hsum_le (inv_nonneg.mpr hmass_pos.le)
  have hfactor :
      (∑ t ∈ Finset.Icc 1 k, (alpha ^ t)⁻¹)⁻¹ *
          ∑ t ∈ Finset.Icc 1 k, Real.rpow alpha (-(t : ℝ) / 2) * (C * V0) =
        ((∑ t ∈ Finset.Icc 1 k, (alpha ^ t)⁻¹)⁻¹ *
          ∑ t ∈ Finset.Icc 1 k, Real.rpow alpha (-(t : ℝ) / 2)) * (C * V0) := by
    rw [← Finset.sum_mul]
    ring
  have hscalar :
      (∑ t ∈ Finset.Icc 1 k, (alpha ^ t)⁻¹)⁻¹ *
          ∑ t ∈ Finset.Icc 1 k, Real.rpow alpha (-(t : ℝ) / 2) ≤
        2 * Real.rpow alpha ((k : ℝ) / 2) :=
    one_based_geometric_half_ratio_rpow_le alpha k halpha_pos halpha_lt_one
  have hscaled :
      ((∑ t ∈ Finset.Icc 1 k, (alpha ^ t)⁻¹)⁻¹ *
          ∑ t ∈ Finset.Icc 1 k, Real.rpow alpha (-(t : ℝ) / 2)) * (C * V0) ≤
        (2 * Real.rpow alpha ((k : ℝ) / 2)) * (C * V0) :=
    mul_le_mul_of_nonneg_right hscalar hCV_nonneg
  calc
    (∑ t ∈ Finset.Icc 1 k, (alpha ^ t)⁻¹)⁻¹ *
        ∑ t ∈ Finset.Icc 1 k, (alpha ^ t)⁻¹ * F t
        ≤ (∑ t ∈ Finset.Icc 1 k, (alpha ^ t)⁻¹)⁻¹ *
          ∑ t ∈ Finset.Icc 1 k, Real.rpow alpha (-(t : ℝ) / 2) * (C * V0) :=
            hnormalized_le
    _ = ((∑ t ∈ Finset.Icc 1 k, (alpha ^ t)⁻¹)⁻¹ *
          ∑ t ∈ Finset.Icc 1 k, Real.rpow alpha (-(t : ℝ) / 2)) * (C * V0) :=
            hfactor
    _ ≤ (2 * Real.rpow alpha ((k : ℝ) / 2)) * (C * V0) := hscaled
    _ = 2 * Real.rpow alpha ((k : ℝ) / 2) * C * V0 := by ring

-- Merged from Staging/add_sub_le_of_sub_le_add_add_sub_and_add_le.lean
-- Generalization plan (G0):
-- concept/name: ordered scalar budget composition by eliminating an intermediate
--   additive term; orig was `component_and_prox_scalar_combine`
-- generality used: arbitrary preordered additive group scalars with monotone
--   addition; no measure, carrier,
--   convexity, smoothness, oracle, filtration, or finite-dimensional assumptions.
-- portable call pattern: descent proofs for proximal, mirror, variance-reduced,
--   and gradient-extrapolation methods can call this after deriving a component
--   inequality with an intermediate table term and a prox inequality bounding
--   that same table plus a new residual; the named scalar quantities and bounds
--   change while the conclusion shape stays fixed.
-- counterargument checked: this is short ordered arithmetic, but not merely
--   paper-local traceability because it packages a recurring descent-proof
--   composition boundary; not a pure rename because no single Mathlib/SOptLib
--   theorem covers the two-hypothesis intermediate-term elimination statement.
-- coverage search: searched SOptLib/CATALOG and project tokens `T + N <= B`,
--   `A - f <= C + G + T - P`, `scalar budget combine`, and LeanSearch for the
--   precise real inequality; Mathlib hits such as `add_tsub_le_assoc`,
--   `add_le_of_le_tsub_left_of_le`, and `Mathlib.Tactic.Linarith.sub_nonpos_of_le`
--   are only subtraction/order ingredients, not the composed statement.
-- minimal hypotheses: weakened from concrete `ℝ` to ordered additive typeclasses; all
--   remaining hypotheses are exactly the two input inequalities.

/-- Combine two scalar upper bounds by eliminating an intermediate additive term.

If one inequality bounds `A - f` by a budget containing `T`, and a second
inequality bounds `T + N` by `B`, then the residual `N - f` can be moved to
the left while replacing the intermediate `T` by `B`.

Layer: Glue | Gap: Level 0 (ordered scalar intermediate-term elimination)
Proof: normalize both hypotheses as linear inequalities and close by
  ordered additive arithmetic.
Source: Mathlib ordered additive arithmetic and linear inequality normalization
Used in: stochastic gradient extrapolation one-step component bound combined
  with a prox-step scalar residual bound
Book citation: book/FOML/RandomGradientExtrapolation.json#/key_lemmas/18
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized gradient extrapolation method -/
theorem add_sub_le_of_sub_le_add_add_sub_and_add_le
    {K : Type*} [AddCommGroup K] [Preorder K] [IsOrderedAddMonoid K]
    {A f C G T P N B : K}
    (hcomp : A - f ≤ C + G + T - P) (hprox : T + N ≤ B) :
    A + (N - f) ≤ C + G + B - P := by
  calc
    A + (N - f) = (A - f) + N := by abel
    _ ≤ (C + G + T - P) + N := by
      simpa [add_assoc, add_comm, add_left_comm] using add_le_add_right hcomp N
    _ = C + G + (T + N) - P := by abel
    _ ≤ C + G + B - P := by
      simpa [add_assoc, add_comm, add_left_comm] using
        add_le_add_right (add_le_add_left hprox (C + G)) (-P)

-- Merged from Staging/sum_Icc_weighted_lagged_inner_telescope_eq_terminal_sub.lean
open scoped BigOperators InnerProductSpace

-- Generalization plan (G0):
-- concept/name: weighted lagged inner-product finite-sum telescope; orig was
--   `gradient_extrapolation_scalar_telescope_of_coeff`, renamed away from
--   algorithm-specific gradient-extrapolation vocabulary to expose the
--   `Finset.Icc` weighted lagged-inner telescope.
-- generality used: arbitrary real inner-product space with natural-indexed
--   scalar weights and vector sequences; no measure, filtration, independence,
--   integrability, convexity, smoothness, oracle, or finite-dimensional
--   hypotheses are used.
-- portable call pattern: accelerated, variance-reduced, and lagged-memory
--   stochastic optimization proofs use a coefficient bridge
--   `theta t * alpha t / m = theta (t - 1)` to collapse current and previous
--   inner-product windows, while `theta`, `alpha`, `m`, the anchor, iterate
--   sequence, and lagged delta sequence change.
-- counterargument checked: this is not only paper traceability because the
--   statement is paper-free finite-sum algebra and no source-mapping objects
--   remain; it is not a duplicate of existing lagged cancellation lemmas
--   because the lagged inner product is expanded into a previous terminal term
--   plus a step residual, producing a terminal-minus-residual identity.
-- coverage search: searched SOptLib/catalog/source for `weighted lagged`,
--   `inner`, `Icc`, `terminal`, `residual`, and `telescope`; the closest hit
--   `sum_Icc_weighted_lagged_cancel_eq_terminal` cancels abstract scalar
--   windows but has no inner-product step residual. LeanSearch returned
--   Mathlib finite-difference telescopes such as `Finset.sum_Ico_sub` and
--   summation-by-parts lemmas, which do not cover this lagged `Icc` shape.
-- minimal hypotheses: all already minimal; only `1 <= k`, the coefficient
--   bridge on `2 <= t <= k`, and `delta 0 = 0` are used.

/-- A weighted lagged inner-product window telescopes to a terminal term minus step residuals.

If `theta t * alpha t / m = theta (t - 1)` on the positive tail, then the
one-based weighted sum of current inner products minus lagged inner products
collapses to the terminal current inner product and a residual sum involving
successive vector increments.

Layer: Glue | Gap: Level 1 (weighted lagged inner-product telescope)
Proof: induct on the terminal index, split both `Icc` sums at the top index,
  rewrite the lagged inner product with `inner_add_left`, use the coefficient
  bridge at the new endpoint, and close by ring arithmetic.
Source: Mathlib finite sums over natural intervals and real inner-product
  bilinearity
Used in: stochastic lagged-memory gradient and acceleration telescopes after
  the adjacent coefficient bridge has been established
Book citation: book/FOML/RandomGradientExtrapolation.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random gradient extrapolation -/
theorem sum_Icc_weighted_lagged_inner_telescope_eq_terminal_sub
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (theta alpha : ℕ → ℝ) (m : ℝ)
    (x : E) (xseq delta : ℕ → E) {k : ℕ} (hk : 1 ≤ k)
    (hcoeff :
      ∀ t, 2 ≤ t → t ≤ k →
        theta t * alpha t / m = theta (t - 1))
    (hdelta_zero : delta 0 = 0) :
    Finset.sum (Finset.Icc 1 k)
        (fun t =>
          theta t *
            (⟪xseq t - x, delta t⟫_ℝ -
              (alpha t / m) *
                ⟪xseq t - x, delta (t - 1)⟫_ℝ)) =
      theta k * ⟪xseq k - x, delta k⟫_ℝ -
        Finset.sum (Finset.Icc 2 k)
          (fun t =>
            (theta t * alpha t / m) *
              ⟪xseq t - xseq (t - 1), delta (t - 1)⟫_ℝ) := by
  classical
  let A : ℕ → ℝ := fun t => ⟪xseq t - x, delta t⟫_ℝ
  let Lag : ℕ → ℝ := fun t => ⟪xseq t - x, delta (t - 1)⟫_ℝ
  let Step : ℕ → ℝ := fun t => ⟪xseq t - xseq (t - 1), delta (t - 1)⟫_ℝ
  change
    Finset.sum (Finset.Icc 1 k)
        (fun t => theta t * (A t - (alpha t / m) * Lag t)) =
      theta k * A k -
        Finset.sum (Finset.Icc 2 k)
          (fun t => (theta t * alpha t / m) * Step t)
  revert hcoeff
  refine Nat.le_induction ?base ?succ k hk
  · intro _hcoeff
    have hLag1 : Lag 1 = 0 := by
      dsimp [Lag]
      simp [hdelta_zero]
    simp [A, Step, hLag1]
  · intro n hn ih hcoeff
    have hcoeff_n :
        ∀ t, 2 ≤ t → t ≤ n →
          theta t * alpha t / m = theta (t - 1) := by
      intro t ht2 htle
      exact hcoeff t ht2 (Nat.le_trans htle (Nat.le_succ n))
    have ih' := ih hcoeff_n
    have hn1 : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
    have hn2 : 2 ≤ n + 1 := Nat.succ_le_succ hn
    have hcoef :
        theta (n + 1) * alpha (n + 1) / m = theta n := by
      simpa [Nat.succ_sub_one] using hcoeff (n + 1) hn2 le_rfl
    have hcoef' :
        theta (n + 1) * (alpha (n + 1) / m) = theta n := by
      rw [← hcoef]
      ring
    have hLag_succ : Lag (n + 1) = A n + Step (n + 1) := by
      have hvec :
          xseq (n + 1) - x =
            (xseq n - x) + (xseq (n + 1) - xseq n) := by
        abel
      dsimp [Lag, A, Step]
      rw [hvec, inner_add_left]
    have hcoef_mul :
        theta (n + 1) * (alpha (n + 1) / m * (A n + Step (n + 1))) =
          theta n * (A n + Step (n + 1)) := by
      rw [← mul_assoc, hcoef']
    rw [Finset.sum_Icc_succ_top hn1]
    rw [Finset.sum_Icc_succ_top hn2]
    rw [ih']
    rw [hLag_succ, hcoef]
    rw [mul_sub, hcoef_mul]
    ring

-- Merged from Staging/sum_Icc_one_eq_sum_range_succ.lean
open scoped BigOperators

-- Generalization plan (G0):
-- concept/name: closed natural interval to zero-based successor range reindexing;
--   orig was `outputWindow_sum_eq_range_succ`, renamed away from output-window
--   algorithm vocabulary to expose the finite-sum index shift.
-- generality used: arbitrary additive commutative monoid values indexed by
--   natural numbers; no measure, filtration, independence, integrability,
--   convexity, smoothness, oracle, Hilbert-space, or finite-dimensional
--   hypotheses are used.
-- portable call pattern: one-based output-window and epoch-window stochastic
--   optimization proofs reindex sums over `1, ..., k` to a zero-based
--   `Finset.range k` before applying geometric-sum or range-recursion APIs;
--   only the payload family and terminal index change.
-- counterargument checked: this is a short wrapper around Mathlib's half-open
--   `Finset.sum_Ico_eq_sum_range`, but it is not a pure rename because future
--   callers naturally have closed one-based windows and would otherwise repeat
--   the `Icc` to `Ico` conversion at every geometric-sum call site.
-- coverage search: searched catalog/SOptLib/source for `sum_Icc`,
--   `range_succ`, `Icc one range`, and `outputWindow_sum_eq_range_succ`;
--   closest SOptLib hits are telescope and terminal-drop range lemmas with
--   different statements. LeanSearch found Mathlib `Finset.sum_Ico_eq_sum_range`
--   and `Finset.sum_Icc_succ_top`, which are partial but do not state the
--   closed `Finset.Icc 1 k` successor-range identity directly.
-- minimal hypotheses: generalized from real-valued sums to `[AddCommMonoid M]`;
--   all hypotheses are typeclass-minimal for finite sums.

/-- A one-based closed natural interval sum is a zero-based successor range sum.

This rewrites `sum_{t = 1}^k F t` as `sum_{j < k} F (j + 1)`, the form used by
range-based geometric-sum and recurrence lemmas.

Layer: Glue | Gap: Level 0 (closed one-based interval to range reindexing)
Proof: convert `Finset.Icc 1 k` to the half-open interval `Finset.Ico 1 (k + 1)`
  and apply Mathlib's `Finset.sum_Ico_eq_sum_range`.
Source: Mathlib finite sums over natural-number intervals
Used in: randomized gradient extrapolation output-window reindexing before
  applying zero-based geometric-sum bounds
Book citation: book/FOML/RandomGradientExtrapolation.json#/algorithm_spec/steps/8/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized gradient extrapolation method -/
theorem sum_Icc_one_eq_sum_range_succ
    {M : Type*} [AddCommMonoid M] (k : ℕ) (F : ℕ → M) :
    Finset.sum (Finset.Icc 1 k) F =
      (Finset.range k).sum (fun j => F (j + 1)) := by
  rw [← Finset.Ico_add_one_right_eq_Icc 1 k]
  simpa [Nat.add_comm] using Finset.sum_Ico_eq_sum_range F 1 (k + 1)


-- Merged from Staging/residual_coeff_nonpos_of_two_mul_alpha_mul_L_le.lean
-- Generalization plan (G0):
-- concept/name: ordered-field residual coefficient nonpositivity from a cross-product
--   side condition; orig was
--   `proposition56_cross_residual_coefficient_nonpos_positive_domain`.
-- generality used: scalar ordered-field arithmetic; no measure,
--   convexity, smoothness, oracle, or finite-dimensional hypotheses.
-- portable call pattern: residual-square absorption in randomized block,
--   accelerated, and variance-reduced stochastic optimization proofs; `theta`,
--   `alpha`, `tau`, `L`, `m`, and `eta` vary while the same coefficient
--   nonpositivity conclusion follows from `2 * alpha * L ≤ m * eta * tau`.
-- counterargument checked: this is not only paper traceability because the
--   formula is the recurring Young-absorption coefficient comparison; it is
--   not a pure wrapper around a named Mathlib lemma.
-- coverage search: searched SOptLib/catalog for `residual_coeff`,
--   `coeff nonpos`, `two_mul alpha L`, and `alpha L eta tau`; related hits
--   package norm or expectation absorptions, not this scalar coefficient.
--   LeanSearch for the precise inequality found only generic order/division
--   lemmas such as `tsub_nonpos` and Young inequalities, not this statement.
-- minimal hypotheses: no algorithm assumptions retained; only positivity of
--   the two denominator products and nonnegativity of the scaling coefficient
--   are used.

/-- A nonnegative scale preserves a residual coefficient comparison.

If the cross condition `2 * alpha * L ≤ m * eta * tau` holds with positive
denominator factors, then the scaled difference of the divided coefficients is
nonpositive.

Layer: Glue | Gap: Level 0 (ordered-field divided residual coefficient comparison)
Proof: divide the cross-product inequality by the positive denominators, scale
  by the nonnegative coefficient, and rewrite subtraction as a nonpositive
  comparison.
Source: Mathlib ordered field division and nonlinear arithmetic APIs
Used in: randomized gradient extrapolation residual-square absorption
Book citation: book/FOML/RandomGradientExtrapolation.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random gradient extrapolation method -/
theorem residual_coeff_nonpos_of_two_mul_alpha_mul_L_le
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (theta alpha tau L m eta : R)
    (hm_eta_pos : 0 < m * eta) (htwo_L_pos : 0 < 2 * L)
    (htheta_nonneg : 0 ≤ theta)
    (hcross : 2 * alpha * L ≤ m * eta * tau) :
    theta * alpha / (m * eta) - theta * tau / (2 * L) ≤ 0 := by
  have hbase : alpha / (m * eta) ≤ tau / (2 * L) := by
    have hm_ne : m ≠ 0 := by
      intro hm
      rw [hm, zero_mul] at hm_eta_pos
      exact (lt_irrefl (0 : R)) hm_eta_pos
    have heta_ne : eta ≠ 0 := by
      intro heta
      rw [heta, mul_zero] at hm_eta_pos
      exact (lt_irrefl (0 : R)) hm_eta_pos
    have hL_ne : L ≠ 0 := by
      intro hL
      rw [hL, mul_zero] at htwo_L_pos
      exact (lt_irrefl (0 : R)) htwo_L_pos
    have hden_nonneg : 0 ≤ (m * eta) * (2 * L) :=
      (mul_pos hm_eta_pos htwo_L_pos).le
    have hnum : alpha * (2 * L) ≤ tau * (m * eta) := by
      nlinarith [hcross]
    calc
      alpha / (m * eta) =
          (alpha * (2 * L)) / ((m * eta) * (2 * L)) := by
            field_simp [hm_eta_pos.ne', htwo_L_pos.ne', hm_ne, heta_ne, hL_ne]
      _ ≤ (tau * (m * eta)) / ((m * eta) * (2 * L)) :=
          div_le_div_of_nonneg_right hnum hden_nonneg
      _ = tau / (2 * L) := by
          field_simp [hm_eta_pos.ne', htwo_L_pos.ne', hm_ne, heta_ne, hL_ne]
  have hscaled :
      theta * (alpha / (m * eta)) ≤ theta * (tau / (2 * L)) :=
    mul_le_mul_of_nonneg_left hbase htheta_nonneg
  have hscaled' :
      theta * alpha / (m * eta) ≤ theta * tau / (2 * L) := by
    convert hscaled using 1 <;> ring
  linarith


-- Merged from Staging/le_two_mul_div_of_nonneg_add_half_mul_le.lean
-- Generalization plan (G0):
-- concept/name: ordered-field half-coefficient division bound; orig was
--   `proposition56_pre_delta_to_v_bound_positive_domain`.
-- generality used: scalar ordered-field arithmetic only; no measure,
--   independence, integrability, topology, norm, inner product, convexity,
--   smoothness, oracle, filtration, or finite-dimensional hypotheses are used.
-- portable call pattern: convergence proofs that first obtain a nonnegative
--   auxiliary gap sum plus a positive half-coefficient times a target value
--   bounded by a budget can drop the auxiliary term and divide by the positive
--   coefficient; `qSum`, `v`, `Delta`, and `den` vary while the conclusion has
--   the same `2 * Delta / den` shape.
-- counterargument checked: the proof is short, but it packages a recurring
--   final scalar bridge after telescoping or residual aggregation; it is not a
--   paper-local traceability wrapper and not a pure rename of a named Mathlib
--   theorem.
-- coverage search: searched SOptLib/catalog and project sources for
--   `half`, `two_mul`, `qSum`, `nonneg add half`, and `pre_delta`; related hits
--   are Young/residual coefficient and budget-specific lemmas, not this
--   division bridge. LeanSearch for the precise natural-language statement
--   returned unrelated denominator and continued-fraction lemmas, so no full
--   Mathlib/SOptLib duplicate was found.
-- minimal hypotheses: all algorithm assumptions are replaced by pointwise
--   scalar hypotheses `0 <= qSum`, `0 < den`, and
--   `qSum + (den / 2) * v <= Delta`.

/-- Drop a nonnegative auxiliary term and divide a positive half coefficient.

If `qSum` is nonnegative and `qSum + (den / 2) * v` is bounded by `Delta`,
then a positive `den` gives the normalized target bound `v <= 2 * Delta / den`.

Layer: Glue | Gap: Level 0 (ordered-field half-coefficient division bound)
Proof: drop the nonnegative auxiliary term, divide by the positive
  coefficient `den / 2`, and normalize the resulting denominator by field
  arithmetic.
Source: Mathlib ordered-field division and nonlinear arithmetic APIs
Used in: stochastic optimization convergence proofs after telescoping a
  nonnegative gap sum and retaining a terminal potential term
Book citation: book/FOML/RandomGradientExtrapolation.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random gradient extrapolation method -/
theorem le_two_mul_div_of_nonneg_add_half_mul_le
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (qSum v Delta den : R)
    (hq_nonneg : 0 <= qSum)
    (hden_pos : 0 < den)
    (hpre : qSum + (den / 2) * v <= Delta) :
    v <= 2 * Delta / den := by
  have hcoeff_pos : 0 < den / 2 := div_pos hden_pos (by norm_num)
  have hcoeff_le : (den / 2) * v <= Delta := by
    nlinarith [hpre, hq_nonneg]
  have hv_le_div : v <= Delta / (den / 2) := by
    rw [le_div_iff₀ hcoeff_pos]
    simpa [mul_comm] using hcoeff_le
  calc
    v <= Delta / (den / 2) := hv_le_div
    _ = 2 * Delta / den := by
      field_simp [ne_of_gt hden_pos]


-- Merged from Staging/finite_sum_residual_terminal_assembly.lean
open scoped BigOperators

-- Generalization plan (G0):
-- concept/name: finite-sum ordered-field rearrangement.
-- generality used: arbitrary finite index type and scalar values in an
--   ordered field.
-- portable call pattern: finite-index calculations after the caller supplies an
--   aggregate inequality, endpoint equality, one sum upper bound, and three sum
--   identities.
-- coverage search: Mathlib search found generic finite-sum distribution and
--   ordered-ring arithmetic facts, but not this already-composed rearrangement.
-- minimal hypotheses: all remaining hypotheses are used.

/-- Rearrange finite-sum scalar decompositions in an ordered field.

Given an inequality between two finite sums, an endpoint identity, one finite-sum
upper bound, and three finite-sum identities, this packages the ordered-field
calculation that moves half of one endpoint term to the left-hand side.

Layer: Glue | Gap: Level 1 (finite-sum ordered-field rearrangement)
Proof: subtract a common finite sum from both sides, split finite sums over
  addition and subtraction, rewrite the supplied aggregate hypotheses, and close
  by ordered-field algebra.
Source: Mathlib finite big-operator distributivity and ordered field arithmetic
Used in: finite-sum endpoint calculations with a retained half endpoint term -/
theorem finset_sum_add_half_le_of_aggregate_decompositions
    {α R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (s : Finset α)
    (a c e b u d n : α → R)
    (xEnd xStart yStart yEnd zEnd zStart uTotal dStart dEnd : R)
    (hstep :
      Finset.sum s (fun t => a t + n t) ≤
        Finset.sum s (fun t => c t + e t + (b t - u t) - d t))
    (hx :
      Finset.sum s (fun t => a t - c t) = xEnd - xStart)
    (hz :
      Finset.sum s e = zEnd - zStart)
    (hy :
      Finset.sum s b ≤ yStart - yEnd)
    (hd :
      Finset.sum s d = dStart + dEnd)
    (hu :
      Finset.sum s u = uTotal) :
    xEnd + Finset.sum s n + yEnd / 2 ≤
      xStart + yStart +
        ((-zStart) - uTotal - dStart) +
        (zEnd - yEnd / 2 - dEnd) := by
  have hleft_decomp :
      Finset.sum s (fun t => a t + n t) - Finset.sum s c =
        Finset.sum s (fun t => a t - c t) + Finset.sum s n := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    ring
  have hright_decomp :
      Finset.sum s (fun t => c t + e t + (b t - u t) - d t) -
          Finset.sum s c =
        Finset.sum s e + Finset.sum s b - Finset.sum s u - Finset.sum s d := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_sub_distrib]
    ring
  have hmain :
      Finset.sum s (fun t => a t - c t) + Finset.sum s n ≤
        Finset.sum s e + Finset.sum s b - Finset.sum s u - Finset.sum s d := by
    calc
      Finset.sum s (fun t => a t - c t) + Finset.sum s n
          = Finset.sum s (fun t => a t + n t) - Finset.sum s c :=
            hleft_decomp.symm
      _ ≤ Finset.sum s (fun t => c t + e t + (b t - u t) - d t) -
            Finset.sum s c := sub_le_sub_right hstep _
      _ = Finset.sum s e + Finset.sum s b - Finset.sum s u - Finset.sum s d :=
            hright_decomp
  nlinarith


-- Merged from Staging/two_mul_theta_div_le_two_mul_theta_mul_alpha_div_of_mul_eta_le.lean
-- Generalization plan (G1):
-- concept/name: ordered-field nonnegative coefficient denominator transfer; orig
--   was `proposition56_terminal_stale_coefficient_le_positive_domain`, renamed
--   away from proposition numbering and stale-gradient terminology and
--   generalized away from the paper-specific `2 * theta` / `m * etaNext`
--   instantiation.
-- generality used: scalar ordered-field arithmetic only; no measure,
--   independence, integrability, topology, norm, inner product, convexity,
--   smoothness, oracle, filtration, carrier, or finite-dimensional hypotheses
--   are used once the denominator bridge is available.
-- portable call pattern: weighted residual or noise-budget handoffs in
--   stochastic gradient, mirror, coordinate, accelerated, and variance-reduced
--   analyses can call this after proving a positive-denominator bridge
--   `d <= alpha * M`; the terminal coefficient, scaling factor, and two
--   denominator scales vary while the conclusion keeps the same shape.
-- counterargument checked: the proof is short and uses Mathlib reciprocal
--   monotonicity ingredients, but it is not only paper traceability: it packages
--   a recurring final coefficient transfer from a denominator bridge to a
--   scaled terminal coefficient. It is not extracted as a def because the
--   expression is scalar coefficient algebra, not a recognized standalone
--   mathematical object like a Bregman divergence or prox objective.
-- coverage search: searched catalog/source for `two_mul_theta`,
--   `terminal_stale_coefficient`, `mul_eta`, `alpha * M`, denominator transfer,
--   and division coefficient bounds. The existing staged theorem
--   `mul_eta_le_alpha_mul_of_weighted_eta_le_and_coeff_eq` proves the upstream
--   bridge `m * etaNext <= alpha * M`, but does not perform this division
--   transfer. LeanSearch returned Mathlib reciprocal/division monotonicity
--   lemmas such as `one_div_le_one_div_of_le`, `div_le_div_of_nonneg_right`,
--   and `div_le_div_iff_of_pos_left`, which are proof ingredients rather than
--   this compound coefficient statement.
-- minimal hypotheses: generalized from setup fields to pointwise scalar facts
--   `0 <= c`, `0 < M`, `0 < d`, and `d <= alpha * M`; all algorithm
--   assumptions were removed.

/-- Transfer a terminal coefficient bound across a positive denominator bridge.

If the positive denominator bridge `d <= alpha * M` holds, then scaling by a
nonnegative coefficient gives `c / M <= c * alpha / d`.

Layer: Glue | Gap: Level 0 (terminal coefficient denominator transfer)
Proof: convert the bridge into a reciprocal-style bound between the two
  positive denominators, multiply by the nonnegative coefficient `c`, and
  normalize the field expressions.
Source: Mathlib ordered-field division, positivity, and ring-normalization APIs
Used in: randomized gradient extrapolation terminal residual coefficient handoff
  from a mass-eta bridge to the final stale-gradient coefficient
Book citation: book/FOML/RandomGradientExtrapolation.json#/algorithm_spec/proof/proposition_5_6/terminal_residual
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random gradient extrapolation method -/
theorem div_le_mul_div_of_nonneg_of_pos_of_pos_of_le_mul
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (c M alpha d : R)
    (hc_nonneg : 0 <= c)
    (hM_pos : 0 < M)
    (hd_pos : 0 < d)
    (hbridge : d <= alpha * M) :
    c / M <= c * alpha / d := by
  have hbase : 1 / M <= alpha / d := by
    field_simp [hM_pos.ne', hd_pos.ne']
    nlinarith [hbridge]
  have hscaled :
      c * (1 / M) <= c * (alpha / d) :=
    mul_le_mul_of_nonneg_left hbase hc_nonneg
  convert hscaled using 1 <;> ring


-- Merged from Staging/dualSize_sub_sq_le_two_mul_sub_sq_add_two_mul_sub_sq.lean
-- Generalization plan (G0):
-- concept/name: dual-size squared split through an intermediate point; orig was proposition56_y_memory_dualNorm_split_positive_domain.
-- generality used: arbitrary additive commutative group carrier and real-valued size function; no measure, convexity, smoothness, oracle, filtration, normed-space, or finite-dimensional assumptions.
-- portable call pattern: gradient-memory, variance-reduced, proximal-gradient, and mirror-descent residual proofs can split a table difference `a - c` through an intermediate value `b` after supplying the same two-term square bound for their chosen dual-size functional.
-- counterargument checked: this is short additive algebra, but not paper-local traceability because it packages the recurring caller step of applying a sum-square size inequality to two successive differences; it is not a pure rename of the existing norm or affine-direction dual-norm sum-square lemmas, which do not expose the intermediate-point subtraction form.
-- coverage search: searched CATALOG/SOptLib/Staging and the algorithm file for `dualSize_sub_sq`, `sub_sq_le`, `two_mul_sub`, `norm_add_sq`, and `affineDirectionDualNorm add_sq`; existing hits cover ambient or affine-direction sums, while this statement abstracts the subtraction-through-intermediate specialization over any real-valued dual-size.
-- minimal hypotheses: the proof uses only an additive group structure and a reusable two-term square bound for `D`; all paper-specific setup, boundedness, separating, and finite-dimensional hypotheses remain at the caller that proves that bound.

/-- A real-valued size with a two-term square bound splits a difference through
an intermediate point.

If `D` satisfies `D (x + y)^2 <= 2 D x^2 + 2 D y^2`, then the difference
from `a` to `c` can be bounded by splitting through `b`.

Layer: Glue | Gap: Level 0 (intermediate-point dual-size square split)
Proof: rewrite `a - c` as `(a - b) + (b - c)` in an additive
  group, then apply the supplied two-term square bound for the size function.
Source: Mathlib additive group normalization and ordered real
  arithmetic
Used in: randomized gradient extrapolation memory-gradient residual splitting
  through the stored component gradient
Book citation: book/FOML/RandomGradientExtrapolation.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized gradient extrapolation method -/
theorem size_sub_sq_le_two_mul_size_sub_sq_add_two_mul_size_sub_sq_of_add_sq
    {E : Type*} [AddGroup E] (D : E → ℝ) (a b c : E)
    (hadd_sq : ∀ x y : E, D (x + y) ^ 2 ≤ 2 * D x ^ 2 + 2 * D y ^ 2) :
    D (a - c) ^ 2 ≤ 2 * D (a - b) ^ 2 + 2 * D (b - c) ^ 2 := by
  have hdecomp : a - c = (a - b) + (b - c) := by
    simp [sub_eq_add_neg, add_assoc]
  rw [hdecomp]
  exact hadd_sq (a - b) (b - c)


-- Merged from Staging/mul_eta_le_alpha_mul_of_weighted_eta_le_and_coeff_eq.lean
-- Generalization plan (G0):
-- concept/name: positive-weight cancellation bridge for terminal coefficient
--   inequalities; orig was `propositionSideConditions_terminal_eta_bridge`,
--   renamed away from proposition and paper side-condition terminology.
-- generality used: an arbitrary ordered commutative semiring with strict
--   nonnegative multiplication monotonicity and positive multiplication
--   reflection; no measure, filtration, independence,
--   integrability, convexity, smoothness, oracle, carrier, vector-space, or
--   finite-dimensional hypotheses are used once the two scalar side conditions
--   are available.
-- portable call pattern: weighted-potential telescopes in stochastic gradient,
--   mirror, block-coordinate, accelerated, and variance-reduced analyses can
--   use this at the terminal coefficient handoff; the positive weight,
--   adjacent coefficient equality, nonnegative scaling coefficient, and
--   weighted eta inequality vary while the conclusion `m * etaNext <= alpha * M`
--   keeps the same shape.
-- counterargument checked: not paper-local traceability because the statement
--   is paper-free scalar ordered algebra used after generic weighted telescope
--   side conditions; not a caller-side expression because it packages the
--   recurring multiply-by-alpha, coefficient rewrite, and cancellation through
--   a positive weight. The expression is not extracted as a def because it is
--   coefficient algebra, not a recognized standalone mathematical object.
-- coverage search: searched catalog/source for `weighted eta`, `terminal eta`,
--   `thetaNext`, `m * eta`, `alpha * M`, and coefficient equality. SOptLib hits
--   `mul_le_mul_add_of_le_mul_add_of_nonneg_left_of_eq_mul` and
--   `weighted_inverse_probability_adjacent_coeff_le` are adjacent-weight
--   coefficient bridges, but they do not cancel a positive terminal weight from
--   a weighted eta inequality. LeanSearch returned generic ordered
--   multiplication/cancellation lemmas such as `smul_le_smul_iff_of_pos_left`,
--   not this compound coefficient-handoff statement.
-- minimal hypotheses: generalized from setup fields to pointwise scalar facts
--   `0 < theta`, `0 <= alpha`, `m * theta = alpha * thetaNext`, and
--   `thetaNext * etaNext <= theta * M`; all algorithm assumptions were removed.

/-- Cancel a positive terminal weight from a weighted eta coefficient bridge.

If `thetaNext * etaNext <= theta * M`, the coefficient relation
`m * theta = alpha * thetaNext` holds, `theta` is positive, and `alpha` is
nonnegative, then the unweighted terminal inequality
`m * etaNext <= alpha * M` follows.

Layer: Glue | Gap: Level 0 (terminal weighted coefficient cancellation)
Proof: scale the weighted inequality by the nonnegative coefficient, rewrite
  the coefficient equality to compare the same positive `theta` multiples, and
  cancel the positive factor.
Source: Mathlib ordered semiring multiplication monotonicity and cancellation APIs
Used in: randomized gradient extrapolation terminal residual coefficient handoff
Book citation: book/FOML/RandomGradientExtrapolation.json#/algorithm_spec/proof/proposition_5_6/terminal_residual
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random gradient extrapolation method -/
theorem mul_eta_le_alpha_mul_of_weighted_eta_le_and_coeff_eq
    {K : Type*} [CommSemiring K] [Preorder K] [PosMulMono K] [PosMulReflectLE K]
    {m alpha theta thetaNext etaNext M : K}
    (htheta_pos : 0 < theta)
    (halpha_nonneg : 0 <= alpha)
    (hcoeff : m * theta = alpha * thetaNext)
    (hweighted : thetaNext * etaNext <= theta * M) :
    m * etaNext <= alpha * M := by
  have hscaled :
      alpha * (thetaNext * etaNext) <= alpha * (theta * M) :=
    mul_le_mul_of_nonneg_left hweighted halpha_nonneg
  have htheta_scaled :
      theta * (m * etaNext) <= theta * (alpha * M) := by
    calc
      theta * (m * etaNext) = (m * theta) * etaNext := by ac_rfl
      _ = (alpha * thetaNext) * etaNext := by rw [hcoeff]
      _ = alpha * (thetaNext * etaNext) := by ac_rfl
      _ <= alpha * (theta * M) := hscaled
      _ = theta * (alpha * M) := by ac_rfl
  exact le_of_mul_le_mul_left htheta_scaled htheta_pos


-- Merged from Staging/inner_fintype_average_auxiliary_lagged_decomposition.lean
open scoped BigOperators InnerProductSpace

namespace SOptLib

/-- A finite-sum inner product decomposes through an affine two-point expansion.

If every index solves the same affine identity
`xNext = ca • a i + cb • b i` on a finite set, with `ca + cb = 1`, then the inner product
against a scaled finite sum splits into the corresponding scaled sum of
displacements from any comparison point `x`.

Layer: Glue | Gap: Level 1 (finite-sum affine inner-product split)
Proof: expand the finite sum through the left slot of the real inner product,
  rewrite `xNext - x` using the affine identity, and simplify by right-slot
  linearity and symmetry of the real inner product.
Source: Mathlib finite sums and real inner-product space algebra
Used in: accelerated and finite-memory stochastic-optimization one-step
  comparison gap expansions after solving an affine update identity -/
theorem inner_smul_sum_affine_combination_sub_eq
    {ι E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s : Finset ι) (g a b : ι → E) (xNext x : E) (scale ca cb : ℝ)
    (hcoeff : ca + cb = 1)
    (haffine : ∀ i ∈ s, xNext = ca • a i + cb • b i) :
    ⟪scale • Finset.sum s g, xNext - x⟫_ℝ =
      scale *
        Finset.sum s
          (fun i => ca * ⟪a i - x, g i⟫_ℝ + cb * ⟪b i - x, g i⟫_ℝ) := by
  classical
  calc
    ⟪scale • Finset.sum s g, xNext - x⟫_ℝ =
        scale * Finset.sum s (fun i : ι => ⟪g i, xNext - x⟫_ℝ) := by
      rw [inner_smul_left, sum_inner]
      simp
    _ =
        scale *
          Finset.sum s
            (fun i => ca * ⟪a i - x, g i⟫_ℝ + cb * ⟪b i - x, g i⟫_ℝ) := by
      have hsum :
          Finset.sum s (fun i : ι => ⟪g i, xNext - x⟫_ℝ) =
            Finset.sum s
              (fun i => ca * ⟪a i - x, g i⟫_ℝ + cb * ⟪b i - x, g i⟫_ℝ) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        have hdiff :
            xNext - x = ca • (a i - x) + cb • (b i - x) := by
          calc
            xNext - x = (ca • a i + cb • b i) - x := by
              rw [haffine i hi]
            _ = ca • (a i - x) + cb • (b i - x) := by
              have hx : x = (ca + cb) • x := by
                rw [hcoeff]
                simp
              nth_rewrite 1 [hx]
              module
        rw [hdiff]
        simp [inner_add_right, inner_smul_right, real_inner_comm]
      rw [hsum]

end SOptLib


-- Merged from Staging/mul_one_sub_sqrt_schedule_alpha_le_half.lean
-- Generalization plan (G0):
-- concept/name: square-root denominator contraction half-budget; orig was
--   `theorem54_card_mul_one_minus_alpha_le_half`, renamed away from theorem
--   numbering and cardinal/setup notation while exposing the reusable scalar
--   budget `m * (1 - alpha) <= 1/2`.
-- generality used: real scalar component-count surrogate `m`, curvature `mu`,
--   and smoothness scale `L`; no carrier, measure, convexity, smoothness
--   predicate, oracle, filtration, topology, norm, inner product, or
--   finite-dimensional hypotheses are used.
-- portable call pattern: strongly-convex finite-sum accelerated and
--   variance-reduced proofs instantiate the component-count scale,
--   curvature, and smoothness bound to show the square-root contraction
--   schedule leaves a small `m * (1 - alpha)` geometric-mass budget.
-- counterargument checked: this is not only paper traceability because it
--   removes the algorithm setup record and packages a reusable square-root
--   schedule inequality; it is not a pure wrapper since Mathlib only supplies
--   the underlying sqrt/order lemmas, and the statement uses the named
--   schedule def rather than an abstract formula hypothesis.
-- coverage search: searched project/SOptLib/Staging/catalog for
--   `sqrt schedule`, `one_sub alpha half`, `mul_one_sub`, and the precise
--   denominator formula; hits include `sqrtDenominatorContractionAlpha`,
--   its interval theorem, and `sqrt_schedule_cross_terminal_bounds`, but none
--   state the half-budget inequality. LeanSearch returned generic
--   `Real.le_sqrt`, `Real.sqrt_lt`, and `Real.sqrt_one_add_le` facts only.
-- minimal hypotheses: the proof needs exactly `0 < m`, `0 < mu`, and
--   `0 <= L`; all finite-cardinality and setup-field assumptions are caller
--   instantiations.

/-- A square-root denominator contraction leaves at most half a component budget.

For `alpha = 1 - (m + sqrt (m^2 + 16*m*L/mu))⁻¹`, nonnegative smoothness and
positive `m` and `mu` imply `m * (1 - alpha) <= 1/2`.

Layer: Glue | Gap: Level 0 (square-root contraction half-budget)
Proof: compare `m` with the square root of `m^2 + 16*m*L/mu`, so the
  denominator `m + sqrt (...)` is at least `2*m`; reciprocal monotonicity then
  gives the half-budget after clearing the positive factor `m`.
Source: Mathlib real square-root and ordered-field reciprocal APIs for
  finite-sum parameter-choice algebra
Used in: randomized gradient extrapolation and related finite-sum
  strongly-convex proofs that convert a square-root contraction schedule into
  a small stale-gradient geometric-mass budget
Book citation: book/FOML/RandomGradientExtrapolation.json#/main_theorem/proof
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized gradient extrapolation method -/
theorem mul_one_sub_sqrt_schedule_alpha_le_half
    {m mu L : ℝ}
    (hm_pos : 0 < m) (hmu_pos : 0 < mu) (hL_nonneg : 0 ≤ L) :
    m * (1 - (1 - (m + Real.sqrt (m ^ 2 + 16 * m * L / mu))⁻¹)) ≤ 1 / 2 := by
  let B : ℝ := Real.sqrt (m ^ 2 + 16 * m * L / mu)
  let D : ℝ := m + B
  have hm_nonneg : 0 ≤ m := hm_pos.le
  have hterm_nonneg : 0 ≤ 16 * m * L / mu := by
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hm_pos.le) hL_nonneg)
      hmu_pos.le
  have hrad_nonneg : 0 ≤ m ^ 2 + 16 * m * L / mu := by
    nlinarith [sq_nonneg m, hterm_nonneg]
  have hm_le_B : m ≤ B := by
    dsimp [B]
    rw [Real.le_sqrt hm_nonneg hrad_nonneg]
    nlinarith [hterm_nonneg]
  have hD_ge : 2 * m ≤ D := by
    dsimp [D]
    linarith
  have hD_pos : 0 < D := by
    dsimp [D]
    have hB_nonneg : 0 ≤ B := by
      dsimp [B]
      exact Real.sqrt_nonneg _
    linarith
  have htwo_m_pos : 0 < 2 * m := by nlinarith
  have hone_minus :
      1 - (1 - (m + Real.sqrt (m ^ 2 + 16 * m * L / mu))⁻¹) = D⁻¹ := by
    dsimp [D, B]
    ring
  have hinv_le : D⁻¹ ≤ (2 * m)⁻¹ := inv_anti₀ htwo_m_pos hD_ge
  calc
    m * (1 - (1 - (m + Real.sqrt (m ^ 2 + 16 * m * L / mu))⁻¹)) = m * D⁻¹ := by
      rw [hone_minus]
    _ ≤ m * (2 * m)⁻¹ := mul_le_mul_of_nonneg_left hinv_le hm_pos.le
    _ = 1 / 2 := by
      field_simp [ne_of_gt hm_pos]


-- Merged from Staging/inverse_power_output_mass_inv_mul_one_sub_inv.lean
open scoped BigOperators

-- Generalization plan (G0):
-- concept/name: one-based inverse-power geometric sum normalization; orig was
--   `theorem54_inverse_geometric_output_mass`, renamed away from theorem-number
--   and output-distribution vocabulary to expose the closed-form finite
--   inverse-power denominator identity.
-- generality used: arbitrary field scalar base `a` and natural terminal index
--   `k`, with only the nonzero denominator hypotheses needed for field
--   simplification. Real ordered output-window uses derive these hypotheses
--   from `0 < a`, `a < 1`, and `1 <= k`.
-- portable call pattern: finite one-based inverse-power weights
--   `theta_t = a^{-t}` normalize denominator-clearing steps by replacing the
--   inverse total mass times `(1 - a)^{-1}` with `a^k / (1 - a^k)`; future
--   callers change the algorithm, weight source, and terminal index while
--   preserving the same scalar conclusion.
-- counterargument checked: Mathlib has finite geometric-sum APIs such as
--   `geom_sum_inv`, `geom_sum_mul_neg`, and interval/range conversion lemmas,
--   but this theorem packages the recurring one-based inverse-power
--   denominator-clearing shape rather than a pure theorem-number wrapper.
-- coverage search: LeanSearch returned Mathlib `geom_sum_inv`, `geom_sum_eq`,
--   `geom_sum_Ico`, and infinite geometric series lemmas, all partial rather
--   than this normalized one-based formula.
-- minimal hypotheses: `a ≠ 0` supports inverse powers and `a ^ k ≠ 1`
--   exactly excludes the terminal denominator; no order or paper setup fields
--   remain.

/-- Normalize a one-based finite sum of inverse powers.

Over a field, if `a ≠ 0` and `a ^ k ≠ 1`, the inverse total mass of the
weights `a^{-t}`, `t = 1, ..., k`, multiplied by `(1 - a)^{-1}` is
`a^k / (1 - a^k)`.

Layer: Glue | Gap: Level 0 (finite inverse-power sum normalization)
Proof: prove the finite one-based inverse-power mass identity by induction on
  the terminal index, then clear the nonzero scalar denominators with field
  simplification.
Source: Mathlib finite sums over natural intervals, natural-number powers, and
  field simplification APIs
Used in: randomized gradient extrapolation conversion of finite inverse-power
  weights into the final geometric rate coefficient
Book citation: book/FOML/RandomGradientExtrapolation.json#/theorem_5_4/statement_math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized gradient extrapolation method -/
theorem inv_sum_Icc_one_pow_inv_mul_one_sub_inv
    {K : Type*} [Field K] {a : K} {k : ℕ} (ha_ne : a ≠ 0) (hpow_ne_one : a ^ k ≠ 1) :
    (Finset.sum (Finset.Icc 1 k) (fun t => (a ^ t)⁻¹))⁻¹ * (1 - a)⁻¹ =
      a ^ k / (1 - a ^ k) := by
  have hpow_ne : ∀ n : ℕ, a ^ n ≠ 0 := fun n => pow_ne_zero n ha_ne
  have hmass :
      ∀ n : ℕ,
        Finset.sum (Finset.Icc 1 n) (fun t => (a ^ t)⁻¹) *
            (a ^ n * (1 - a)) =
          1 - a ^ n := by
    intro n
    induction n with
    | zero =>
        simp
    | succ n ih =>
        have hsum :
            Finset.sum (Finset.Icc 1 (n + 1)) (fun t => (a ^ t)⁻¹) =
              Finset.sum (Finset.Icc 1 n) (fun t => (a ^ t)⁻¹) +
                (a ^ (n + 1))⁻¹ := by
          rw [Finset.sum_Icc_succ_top (Nat.succ_pos n)]
        rw [hsum]
        calc
          (Finset.sum (Finset.Icc 1 n) (fun t => (a ^ t)⁻¹) +
                (a ^ (n + 1))⁻¹) *
              (a ^ (n + 1) * (1 - a))
              =
            a * (Finset.sum (Finset.Icc 1 n) (fun t => (a ^ t)⁻¹) *
                (a ^ n * (1 - a))) + (1 - a) := by
              field_simp [hpow_ne n, hpow_ne (n + 1), ha_ne]
              ring
          _ = a * (1 - a ^ n) + (1 - a) := by rw [ih]
          _ = 1 - a ^ (n + 1) := by ring
  have ha_ne_one : a ≠ 1 := by
    intro ha_one
    exact hpow_ne_one (by simp [ha_one])
  have hden_ne : 1 - a ≠ 0 := by
    exact sub_ne_zero.mpr (Ne.symm ha_ne_one)
  have htail_ne : 1 - a ^ k ≠ 0 := by
    exact sub_ne_zero.mpr (Ne.symm hpow_ne_one)
  have hmass_k := hmass k
  have hmass_k' :
      Finset.sum (Finset.Icc 1 k) (fun t => (a ^ t)⁻¹) * (1 - a) * a ^ k =
        1 - a ^ k := by
    calc
      Finset.sum (Finset.Icc 1 k) (fun t => (a ^ t)⁻¹) * (1 - a) * a ^ k
          =
        Finset.sum (Finset.Icc 1 k) (fun t => (a ^ t)⁻¹) * (a ^ k * (1 - a)) := by
          ring
      _ = 1 - a ^ k := hmass_k
  have hsum_ne : Finset.sum (Finset.Icc 1 k) (fun t => (a ^ t)⁻¹) ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hmass_k
    exact htail_ne hmass_k.symm
  field_simp [hsum_ne, hpow_ne k, hden_ne, htail_ne]
  rw [← hmass_k']
  ring


-- Merged from Staging/inv_mul_sum_range_stale_geometric_le_two_mul.lean
open scoped BigOperators

-- Generalization plan (G0):
-- concept/name: scaled finite geometric mass bound for the ratio `(m - 1) / (m * a)`;
--   orig was `theorem54_scaled_stale_geometric_sum_le_two_card`, renamed away
--   from theorem-number wording while retaining the reusable finite geometric
--   mass pattern.
-- generality used: ordered-field scalar parameters `m` and `a`, and a natural
--   horizon `k`; no measure, convexity, smoothness, finite-dimensional, or
--   algorithm setup assumptions are used.
-- portable call pattern: analyses with this finite geometric ratio instantiate
--   the count `m`, contraction `a`, and horizon `k`; once the same lower bound
--   on `a` is proved, the scaled geometric mass is bounded by `2 * m`.
-- counterargument checked: this is not only paper-local traceability because it
--   packages the reusable ordered-field consequence connecting the lower bound
--   on `a` with the finite geometric ratio; the inner finite geometric
--   sum bound itself is left unextracted because Mathlib covers that standard
--   series shape.
-- coverage search: LeanSearch returned Mathlib `geom_sum_Ico_le_of_lt_one`,
--   `geom_sum_of_lt_one`, and infinite geometric-series lemmas; project search
--   found only the local private helper and a declined staging attempt for the
--   inner `sum_range_geometric_le_inv_one_sub`, so no staged SOptLib theorem
--   covers this scaled ratio statement.
-- minimal hypotheses: `1 <= m` gives positivity of `m` and nonnegativity of
--   `m - 1`; `0 < a` supports the scaling and denominator; the lower bound on
--   `a` is exactly what proves both the ratio is below one and
--   `(2 * m)⁻¹ <= a * (1 - (m - 1) / (m * a))`.

/-- A scaled finite geometric mass with ratio `(m - 1) / (m * a)` is bounded by `2 * m`.

If `m >= 1`, `a > 0`, and `a >= (2*m - 1)/(2*m)`, then the scaled finite
geometric sum `a⁻¹ * sum_{j < k} ((m - 1)/(m*a))^j` is at most `2*m`.

Layer: Glue | Gap: Level 1 (scaled geometric mass bound)
Proof: first bound the finite geometric sum by `(1 - r)⁻¹` for
  `r = (m - 1)/(m*a)`, then use the lower bound on `a` to compare
  `(a * (1 - r))⁻¹` with `2*m`.
Source: Mathlib finite geometric sums, ordered-field division, and inverse
  antitonicity APIs
Used in: randomized gradient extrapolation stale-memory noise budget reduction
Book citation: book/FOML/RandomGradientExtrapolation.json#/main_theorem/proof
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized gradient extrapolation method -/
theorem inv_mul_sum_range_sub_one_div_mul_le_two_mul_of_lower_bound
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {m a : K} {k : ℕ}
    (hm_ge_one : 1 ≤ m)
    (ha_pos : 0 < a)
    (ha_lower : (2 * m - 1) / (2 * m) ≤ a) :
    a⁻¹ * (Finset.range k).sum (fun j => ((m - 1) / (m * a)) ^ j) ≤ 2 * m := by
  let r : K := (m - 1) / (m * a)
  have hm_pos : 0 < m := lt_of_lt_of_le zero_lt_one hm_ge_one
  have hm_nonneg : 0 ≤ m := hm_pos.le
  have hm_ne : m ≠ 0 := ne_of_gt hm_pos
  have ha_ne : a ≠ 0 := ne_of_gt ha_pos
  have hden_pos : 0 < m * a := mul_pos hm_pos ha_pos
  have hden_ne : m * a ≠ 0 := ne_of_gt hden_pos
  have hm_minus_nonneg : 0 ≤ m - 1 := by linarith
  have hr_nonneg : 0 ≤ r := by
    dsimp [r]
    exact div_nonneg hm_minus_nonneg hden_pos.le
  have hma_lower : (2 * m - 1) / 2 ≤ m * a := by
    have hmul := mul_le_mul_of_nonneg_left ha_lower (show 0 ≤ m by exact hm_nonneg)
    have hrewrite :
        m * ((2 * m - 1) / (2 * m)) = (2 * m - 1) / 2 := by
      field_simp [hm_ne]
    nlinarith
  have hma_gt : m - 1 < m * a := by
    nlinarith [hma_lower]
  have hr_lt_one : r < 1 := by
    dsimp [r]
    exact (div_lt_one hden_pos).mpr hma_gt
  have hgeom :
      (Finset.range k).sum (fun j => r ^ j) ≤ (1 - r)⁻¹ := by
    have hrange_eq : Finset.range k = Finset.Ico 0 k := by
      ext j
      simp
    calc
      (Finset.range k).sum (fun j => r ^ j)
          = (Finset.Ico 0 k).sum (fun j => r ^ j) := by rw [hrange_eq]
      _ ≤ r ^ 0 / (1 - r) :=
          geom_sum_Ico_le_of_lt_one (x := r) (m := 0) (n := k) hr_nonneg hr_lt_one
      _ = (1 - r)⁻¹ := by simp [one_div]
  have hscaled :
      a⁻¹ * (Finset.range k).sum (fun j => r ^ j) ≤ a⁻¹ * (1 - r)⁻¹ :=
    mul_le_mul_of_nonneg_left hgeom (inv_nonneg.mpr ha_pos.le)
  have hone_sub_pos : 0 < 1 - r := sub_pos.mpr hr_lt_one
  have hc_lower : (2 * m)⁻¹ ≤ a * (1 - r) := by
    dsimp [r]
    have htwo_m_ne : 2 * m ≠ 0 := by nlinarith
    field_simp [hm_ne, ha_ne, hden_ne, htwo_m_ne]
    nlinarith [hma_lower]
  have hc_inv_le : (a * (1 - r))⁻¹ ≤ 2 * m := by
    have htwo_m_pos : 0 < 2 * m := by nlinarith
    have hlower_pos : 0 < (2 * m)⁻¹ := inv_pos.mpr htwo_m_pos
    have hstep := inv_anti₀ hlower_pos hc_lower
    have hrewrite : ((2 * m)⁻¹)⁻¹ = 2 * m := inv_inv (2 * m)
    simpa [hrewrite] using hstep
  calc
    a⁻¹ * (Finset.range k).sum (fun j => ((m - 1) / (m * a)) ^ j)
        = a⁻¹ * (Finset.range k).sum (fun j => r ^ j) := by
          simp [r]
    _ ≤ a⁻¹ * (1 - r)⁻¹ := hscaled
    _ = (a * (1 - r))⁻¹ := by
          field_simp [ha_ne, ne_of_gt hone_sub_pos]
    _ ≤ 2 * m := hc_inv_le


-- Merged from Staging/sqrt_schedule_cross_terminal_bounds.lean
-- Generalization plan (G0):
-- concept/name: square-root schedule cross and terminal scalar bounds; orig was
--   `theorem54_sqrt_budget_cross_terminal_scalar`, renamed away from theorem
--   numbering and paper-local `Lhat`/setup notation while exposing the
--   reusable closed-form parameter-choice side conditions.
-- generality used: real scalar component-count surrogate `m`, curvature `mu`,
--   smoothness scale `L`, and contraction `a`; no carrier, measure,
--   convexity, oracle, filtration, topology, norm, inner product, or
--   finite-dimensional hypotheses are used.
-- portable call pattern: finite-sum accelerated and variance-reduced
--   strongly-convex proofs instantiate component count, curvature,
--   smoothness, and a square-root denominator alpha definition to discharge
--   cross-residual and terminal-residual scalar side conditions.
-- counterargument checked: this is not only paper traceability because the
--   theorem removes the algorithm setup record and packages the nontrivial
--   square-root denominator algebra used by schedule side-condition proofs;
--   it is not a pure wrapper around Mathlib sqrt facts.
-- coverage search: searched project/SOptLib for `sqrt schedule cross terminal
--   bounds`, `Real.sqrt m^2 16 m L mu`, and catalog tokens around sqrt budget;
--   LeanSearch returned only generic `Real.sqrt` order lemmas such as
--   `Real.le_sqrt_of_sq_le` and `Real.sqrt_le_iff`; existing SOptLib schedule
--   hits cover different square-root formulas or geometric mass bounds.
-- minimal hypotheses: the proof needs exactly `0 < m`, `0 < mu`, `0 <= L`,
--   `0 < a`, and the pointwise closed-form alpha equation; all algorithm
--   setup fields and policy hypotheses were dropped.

/-- A square-root denominator schedule gives cross and terminal scalar bounds.

For `a = 1 - (m + sqrt (m^2 + 16*m*L/mu))⁻¹`, the induced factors
`((m * (1 - a))⁻¹ - 1)` and `a/(1-a) * mu` satisfy the two scalar
side-condition inequalities used to absorb cross-residual and terminal terms.

Layer: Glue | Gap: Level 1 (square-root schedule side-condition bounds)
Proof: set `B = sqrt (m^2 + 16*m*L/mu)` and `D = m + B`; the alpha equation
  rewrites the schedule factors to `B/m` and `a*D*mu`, while `B^2*mu`
  gives the required lower bound by ordered-field arithmetic.
Source: Mathlib real square-root and ordered-field division APIs for
  finite-sum parameter-choice algebra
Used in: randomized gradient extrapolation proof that the square-root
  finite-sum schedule satisfies cross-residual and terminal-residual
  coefficient side conditions
Book citation: book/FOML/RandomGradientExtrapolation.json#/main_theorem/proof
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized gradient extrapolation method -/
theorem sqrt_schedule_cross_terminal_bounds
    {m mu L a : ℝ}
    (hm_pos : 0 < m) (hmu_pos : 0 < mu) (hL_nonneg : 0 ≤ L)
    (ha_pos : 0 < a)
    (ha_def : a = 1 - (m + Real.sqrt (m ^ 2 + 16 * m * L / mu))⁻¹) :
    2 * (m * a) * L ≤
        m * (((m * (1 - a))⁻¹ - 1)) * (a / (1 - a) * mu) ∧
      4 * L ≤
        (((m * (1 - a))⁻¹ - 1)) * (mu + a / (1 - a) * mu) := by
  let B : ℝ := Real.sqrt (m ^ 2 + 16 * m * L / mu)
  let D : ℝ := m + B
  have hm_ne : m ≠ 0 := ne_of_gt hm_pos
  have hmu_ne : mu ≠ 0 := ne_of_gt hmu_pos
  have hterm_nonneg : 0 ≤ 16 * m * L / mu := by
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hm_pos.le) hL_nonneg)
      hmu_pos.le
  have hrad_nonneg : 0 ≤ m ^ 2 + 16 * m * L / mu := by
    nlinarith [sq_nonneg m, hterm_nonneg]
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact Real.sqrt_nonneg _
  have hB_sq : B ^ 2 = m ^ 2 + 16 * m * L / mu := by
    dsimp [B]
    rw [Real.sq_sqrt hrad_nonneg]
  have hD_pos : 0 < D := by
    dsimp [D]
    linarith
  have hD_ne : D ≠ 0 := ne_of_gt hD_pos
  have hone_minus : 1 - a = D⁻¹ := by
    change 1 - a = D⁻¹
    rw [ha_def]
    dsimp [D, B]
    ring
  have hcross_factor_eq : ((m * (1 - a))⁻¹ - 1) = B / m := by
    rw [hone_minus]
    field_simp [hm_ne, hD_ne]
    dsimp [D]
    ring
  have heta_eq : a / (1 - a) * mu = a * D * mu := by
    rw [hone_minus]
    field_simp [hD_ne]
  have haD_eq : a * D = D - 1 := by
    have ha_eq' : a = 1 - D⁻¹ := by linarith [hone_minus]
    rw [ha_eq']
    field_simp [hD_ne]
  have heta_sum_eq : mu + a / (1 - a) * mu = D * mu := by
    rw [heta_eq]
    rw [haD_eq]
    ring
  have hB_sq_mu_eq : B ^ 2 * mu = m ^ 2 * mu + 16 * m * L := by
    rw [hB_sq]
    field_simp [hmu_ne]
  have hB_sq_mu_ge : 16 * m * L ≤ B ^ 2 * mu := by
    have hnonneg : 0 ≤ m ^ 2 * mu := mul_nonneg (sq_nonneg m) hmu_pos.le
    nlinarith
  have hD_ge_B : B ≤ D := by
    dsimp [D]
    linarith
  have hBsq_le_BD : B ^ 2 * mu ≤ B * D * mu := by
    have hmul : B * B ≤ B * D := mul_le_mul_of_nonneg_left hD_ge_B hB_nonneg
    have hmulmu : B * B * mu ≤ B * D * mu :=
      mul_le_mul_of_nonneg_right hmul hmu_pos.le
    nlinarith
  have hBD_ge_16 : 16 * m * L ≤ B * D * mu :=
    le_trans hB_sq_mu_ge hBsq_le_BD
  have hcross_base : 2 * m * L ≤ B * D * mu := by
    nlinarith [hBD_ge_16, hm_pos.le, hL_nonneg]
  have hcross_mul : (2 * m * L) * a ≤ (B * D * mu) * a :=
    mul_le_mul_of_nonneg_right hcross_base ha_pos.le
  have hterminal_base : 4 * L ≤ B * D * mu / m := by
    have hfour_m : 4 * m * L ≤ B * D * mu := by
      nlinarith [hBD_ge_16, hm_pos.le, hL_nonneg]
    have hdiv :
        (4 * m * L) / m ≤ (B * D * mu) / m :=
      div_le_div_of_nonneg_right hfour_m hm_pos.le
    calc
      4 * L = (4 * m * L) / m := by
        field_simp [hm_ne]
      _ ≤ (B * D * mu) / m := hdiv
  constructor
  · rw [hcross_factor_eq, heta_eq]
    calc
      2 * (m * a) * L = (2 * m * L) * a := by ring
      _ ≤ (B * D * mu) * a := hcross_mul
      _ = m * (B / m) * (a * D * mu) := by
        field_simp [hm_ne]
  · rw [hcross_factor_eq, heta_sum_eq]
    calc
      4 * L ≤ B * D * mu / m := hterminal_base
      _ = (B / m) * (D * mu) := by
        field_simp [hm_ne]


-- Merged from Staging/stale_geometric_noise_budget_le_delta_noise.lean
open scoped BigOperators

-- Generalization plan (G0):
-- concept/name: stale geometric noise budget absorption; orig was
--   `theorem54_stale_noise_budget_le_delta_noise`, renamed away from theorem
--   numbering and Delta-specific paper notation while retaining the
--   mathematical role of absorbing a stale finite-geometric noise tail into an
--   initial variance budget coefficient.
-- generality used: ordered-field scalar parameters `m`, `mu`, `a`, and
--   `sigma0`, plus a natural horizon `k`; no measure, filtration, topology,
--   norm, inner product, convexity, smoothness, oracle, or finite-dimensional
--   hypotheses are used.
-- portable call pattern: accelerated finite-sum, variance-reduced, and
--   block-coordinate stochastic analyses with a stale/noise geometric tail
--   instantiate the component count `m`, contraction `a`, strong-convexity or
--   curvature scale `mu`, and variance scale `sigma0`; once the same lower
--   bound on `a` and budget `m * (1 - a) <= 1 / 2` are proved, the same
--   coefficient comparison discharges the noise absorption.
-- counterargument checked: this is not only paper-local traceability because
--   it packages the reusable combination of a finite geometric mass bound with
--   the `m * (1 - a)` budget; it is not a pure wrapper around Mathlib because
--   Mathlib supplies only the geometric-series ingredients, not this
--   stochastic-optimization coefficient absorption.
-- coverage search: searched project/SOptLib/Staging for stale/geometric/noise/
--   budget/delta and read `inv_mul_sum_range_sub_one_div_mul_le_two_mul_of_lower_bound`,
--   `staleGradientGeometricInitialBudget`, and
--   `strongConvexInitialVarianceBudget`; LeanSearch for "real geometric series
--   noise budget alpha power inequality" returned Mathlib geometric sum lemmas
--   including `geom_sum_Ico_le_of_lt_one`, `geom_sum_lt`, and
--   `Nat.geom_sum_le`, all partial rather than this scaled noise absorption.
-- minimal hypotheses: all algorithm setup fields are replaced by scalar
--   inequalities; `1 <= m`, `0 < mu`, `0 < a`, `a < 1`, the geometric lower
--   bound on `a`, and `m * (1 - a) <= 1 / 2` are exactly what the proof uses.

/-- A stale geometric noise tail fits into the inverse contraction variance budget.

If the finite geometric mass with ratio `(m - 1) / (m * a)` is controlled by
the lower bound on `a`, and the remaining scalar budget satisfies
`m * (1 - a) <= 1 / 2`, then the scaled stale-noise term is bounded by
`(1 - a)⁻¹ * sigma0^2 / (m * mu)`.

Layer: Glue | Gap: Level 1 (stale geometric noise coefficient absorption)
Proof: use the staged scaled finite-geometric mass bound, multiply by the
  nonnegative noise scale, then clear ordered-field denominators and use the
  quadratic consequence of `m * (1 - a) <= 1 / 2`.
Source: Mathlib finite geometric sums, ordered-field division, and quadratic
  nonnegativity APIs
Used in: randomized gradient extrapolation stale-memory noise budget reduction
Book citation: book/FOML/RandomGradientExtrapolation.json#/main_theorem/proof/8
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized gradient extrapolation method -/
theorem stale_geometric_noise_budget_le_inverse_contraction_variance_budget
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {m mu a sigma0 : K} {k : ℕ}
    (hm_ge_one : 1 ≤ m)
    (hmu_pos : 0 < mu)
    (ha_pos : 0 < a)
    (ha_lt_one : a < 1)
    (ha_lower : (2 * m - 1) / (2 * m) ≤ a)
    (hm_one_minus : m * (1 - a) ≤ 1 / 2) :
    (2 * (1 - a) / mu) *
        (a⁻¹ * (Finset.range k).sum (fun j => ((m - 1) / (m * a)) ^ j)) *
        sigma0 ^ 2 ≤
      (1 - a)⁻¹ * (sigma0 ^ 2 / (m * mu)) := by
  have hm_pos : 0 < m := lt_of_lt_of_le zero_lt_one hm_ge_one
  have hmu_ne : mu ≠ 0 := ne_of_gt hmu_pos
  have hm_ne : m ≠ 0 := ne_of_gt hm_pos
  have h1ma_pos : 0 < 1 - a := sub_pos.mpr ha_lt_one
  have h1ma_ne : 1 - a ≠ 0 := ne_of_gt h1ma_pos
  have hscale_nonneg : 0 ≤ 2 * (1 - a) / mu := by
    exact div_nonneg
      (mul_nonneg (by norm_num) h1ma_pos.le)
      hmu_pos.le
  have hgeom :
      a⁻¹ * (Finset.range k).sum (fun j => ((m - 1) / (m * a)) ^ j) ≤ 2 * m :=
    inv_mul_sum_range_sub_one_div_mul_le_two_mul_of_lower_bound
      (m := m) (a := a) (k := k) hm_ge_one ha_pos ha_lower
  have hscaled :
      (2 * (1 - a) / mu) *
          (a⁻¹ * (Finset.range k).sum (fun j => ((m - 1) / (m * a)) ^ j)) *
          sigma0 ^ 2 ≤
        (2 * (1 - a) / mu) * (2 * m) * sigma0 ^ 2 := by
    have hleft :=
      mul_le_mul_of_nonneg_left hgeom hscale_nonneg
    exact mul_le_mul_of_nonneg_right hleft (sq_nonneg sigma0)
  have hb_nonneg : 0 ≤ m * (1 - a) :=
    mul_nonneg hm_pos.le h1ma_pos.le
  have hbudget_coeff :
      (2 * (1 - a) / mu) * (2 * m) ≤
        (1 - a)⁻¹ * (1 / (m * mu)) := by
    have hsq : 4 * (m * (1 - a)) ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg (m * (1 - a)), hm_one_minus, hb_nonneg]
    field_simp [hmu_ne, hm_ne, h1ma_ne]
    nlinarith [hsq, hb_nonneg]
  have hbudget_scaled :
      (2 * (1 - a) / mu) * (2 * m) * sigma0 ^ 2 ≤
        ((1 - a)⁻¹ * (1 / (m * mu))) * sigma0 ^ 2 :=
    mul_le_mul_of_nonneg_right hbudget_coeff (sq_nonneg sigma0)
  calc
    (2 * (1 - a) / mu) *
        (a⁻¹ * (Finset.range k).sum (fun j => ((m - 1) / (m * a)) ^ j)) *
        sigma0 ^ 2
        ≤ (2 * (1 - a) / mu) * (2 * m) * sigma0 ^ 2 := hscaled
    _ ≤ ((1 - a)⁻¹ * (1 / (m * mu))) * sigma0 ^ 2 := hbudget_scaled
    _ = (1 - a)⁻¹ * (sigma0 ^ 2 / (m * mu)) := by
      field_simp [hm_ne, hmu_ne]
