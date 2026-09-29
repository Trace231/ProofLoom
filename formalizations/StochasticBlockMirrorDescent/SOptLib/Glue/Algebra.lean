import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Topology.Algebra.AffineSubspace
-- SOptLib/Glue/Algebra.lean
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Analysis.Normed.Module.Basic
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
