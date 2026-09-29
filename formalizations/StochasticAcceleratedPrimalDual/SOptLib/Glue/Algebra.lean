import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import Mathlib.Analysis.InnerProductSpace.Adjoint
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

/-- Each nonnegative finite real weight whose total mass is one is at most one.

This is the unbundled finite-probability-vector component bound: for a family
of real weights indexed by a finite type, pointwise nonnegativity and
`∑ i, p i = 1` imply `p i ≤ 1` for every component.

Layer: Glue | Gap: Level 0 (finite probability component bound)
Proof: rewrite the right-hand side using the total-mass identity and apply
  `Finset.single_le_sum` to the nonnegative family over `Finset.univ`.
Source: Mathlib finite sums over ordered additive monoids
Used in: stochastic block-coordinate sampling inverse-probability bounds
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/assumptions/4
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem finset_weight_le_one_of_nonneg_sum_eq_one
    {ι : Type*} [Fintype ι] (p : ι → ℝ) (i : ι)
    (hp_nonneg : ∀ j, 0 ≤ p j)
    (hp_sum : Finset.sum Finset.univ p = 1) :
    p i ≤ 1 := by
  rw [← hp_sum]
  exact Finset.single_le_sum
    (fun j _hj => hp_nonneg j) (Finset.mem_univ i)

/-- Inverse-scale average and midpoint formulas imply the APD displacement identities.

If the next averaged point and the midpoint are both inverse-`β` affine blends
with the same previous average, then their difference is the inverse-scaled
step displacement, the midpoint rescales to the previous-average/previous-point
combination, and the target displacement can be recentered from the midpoint to
the previous point.

Layer: Glue | Gap: Level 1 (inverse-scale average midpoint displacement algebra)
Proof: rewrite with the two affine formulas, use module normalization for the
  additive identities, and use field simplification for the two inverse-scale
  coefficient cancellations.
Source: Mathlib real module algebra, scalar inverse cancellation, and `module`
  normalization tactics
Used in: accelerated stochastic primal-dual smooth aggregate bound recentering
  from inverse-beta midpoint and running average formulas
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem apd_average_midpoint_displacement_identities
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (β : ℝ) (xBarPrev xPrev xNext xBarNext xMid xTarget : E)
    (hβ_ne : β ≠ 0)
    (hxbar_eq :
      xBarNext = (1 - β⁻¹) • xBarPrev + β⁻¹ • xNext)
    (hxmid_eq :
      xMid = (1 - β⁻¹) • xBarPrev + β⁻¹ • xPrev) :
    xBarNext - xMid = β⁻¹ • (xNext - xPrev) ∧
      β • xMid = (β - 1) • xBarPrev + xPrev ∧
      (β - 1) • (xBarPrev - xMid) + (xTarget - xMid) =
        xTarget - xPrev := by
  have hbar_disp : xBarNext - xMid = β⁻¹ • (xNext - xPrev) := by
    rw [hxbar_eq, hxmid_eq]
    module
  have hcoef_left : β * (1 - β⁻¹) = β - 1 := by
    field_simp [hβ_ne]
  have hcoef_right : β * β⁻¹ = 1 := by
    field_simp [hβ_ne]
  have hxmid_scaled : β • xMid = (β - 1) • xBarPrev + xPrev := by
    rw [hxmid_eq, smul_add, smul_smul, smul_smul, hcoef_left, hcoef_right, one_smul]
  have hmid_comb :
      (β - 1) • (xBarPrev - xMid) + (xTarget - xMid) =
        xTarget - xPrev := by
    calc
      (β - 1) • (xBarPrev - xMid) + (xTarget - xMid)
          = (β - 1) • xBarPrev + xTarget - β • xMid := by
              module
      _ = xTarget - xPrev := by
              rw [hxmid_scaled]
              module
  exact ⟨hbar_disp, hxmid_scaled, hmid_comb⟩

/-- A beta-gamma product shifts back one time step under inverse-coupled recurrences.

If `beta i - 1` is generated by multiplying the previous beta value by
`theta i`, while `gamma i` is generated by multiplying the previous gamma value
by `(theta i)^{-1}`, then the product `(beta i - 1) * gamma i` is exactly the
previous beta-gamma product.

Layer: Glue | Gap: Level 0 (accelerated scalar weight-product shift)
Proof: rewrite the two one-step recurrences at the current index, cancel the
  nonzero `theta i` factor with its inverse, and normalize associativity.
Source: Mathlib field inversion and natural-number predecessor arithmetic
Used in: stochastic accelerated primal-dual finite-difference telescope for
  weighted saddle-gap terms
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec/analysis/lemmas
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
theorem beta_sub_one_mul_gamma_eq_prev_of_recurrence
    {R : Type*} [Field R]
    (beta gamma theta : ℕ → R) (i : ℕ) (hi : 2 ≤ i)
    (hbeta_rec : ∀ t, 1 ≤ t → beta (t + 1) - 1 = beta t * theta (t + 1))
    (hgamma_rec : ∀ t, 2 ≤ t → gamma t = (theta t)⁻¹ * gamma (t - 1))
    (htheta_ne : theta i ≠ 0) :
    (beta i - 1) * gamma i = beta (i - 1) * gamma (i - 1) := by
  have hi_prev : 1 ≤ i - 1 := by omega
  have hidx : i - 1 + 1 = i := by omega
  have hbeta_i : beta i - 1 = beta (i - 1) * theta i := by
    simpa [hidx] using hbeta_rec (i - 1) hi_prev
  have hgamma_i : gamma i = (theta i)⁻¹ * gamma (i - 1) := by
    simpa using hgamma_rec i hi
  rw [hbeta_i, hgamma_i]
  calc
    (beta (i - 1) * theta i) * ((theta i)⁻¹ * gamma (i - 1)) =
        beta (i - 1) * ((theta i * (theta i)⁻¹) * gamma (i - 1)) := by
      ring
    _ = beta (i - 1) * (1 * gamma (i - 1)) := by
      rw [mul_inv_cancel₀ htheta_ne]
    _ = beta (i - 1) * gamma (i - 1) := by
      ring

/-- A one-based scalar recurrence with nonnegative multiplicative increments stays at least one.

If `beta 1 = 1` and each successor satisfies
`beta (t + 1) - 1 = beta t * theta (t + 1)` with `theta` nonnegative from
time `2` onward, then every positive-time `beta t` is at least `1`.

Layer: Glue | Gap: Level 0 (one-based scalar recurrence lower-bound preservation)
Proof: induction on the natural time index. The successor step rewrites
  `beta (t + 1) - 1`, proves the product nonnegative, and uses `sub_nonneg`.
Source: Mathlib ordered-ring arithmetic and natural-number induction APIs
Used in: stochastic accelerated primal-dual reciprocal averaging weights before
  midpoint and aggregate convex-combination rewrites
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec/parameters
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
theorem one_le_beta_of_recurrence
    {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R]
    (beta theta : ℕ → R)
    (hbeta_one : beta 1 = 1)
    (hbeta_rec : ∀ t, 1 ≤ t → beta (t + 1) - 1 = beta t * theta (t + 1))
    (htheta_nonneg : ∀ t, 2 ≤ t → 0 ≤ theta t)
    (t : ℕ) (ht : 1 ≤ t) :
    1 ≤ beta t := by
  induction t with
  | zero =>
      omega
  | succ k ih =>
      cases k with
      | zero =>
          simp [hbeta_one]
      | succ j =>
          have hk : 1 ≤ Nat.succ j := by omega
          have htheta : 0 ≤ theta (Nat.succ (Nat.succ j)) :=
            htheta_nonneg (Nat.succ (Nat.succ j)) (by omega)
          have hbeta_prev : 1 ≤ beta (Nat.succ j) := ih hk
          have hbeta_prev_nonneg : 0 ≤ beta (Nat.succ j) :=
            le_trans zero_le_one hbeta_prev
          have hprod_nonneg :
              0 ≤ beta (Nat.succ j) * theta (Nat.succ (Nat.succ j)) :=
            mul_nonneg hbeta_prev_nonneg htheta
          have hsub_nonneg : 0 ≤ beta (Nat.succ (Nat.succ j)) - 1 := by
            simpa [hbeta_rec (Nat.succ j) hk] using hprod_nonneg
          exact sub_nonneg.mp hsub_nonneg

/-- A beta-weighted aggregate recurrence collapses linear-map bilinear terms on
either side of the inner product.

If `β • xBarNext - (β - 1) • xBarPrev = xNext` and similarly for `y`, then the
corresponding beta-weighted bilinear terms against fixed targets collapse to
the bilinear terms at the next iterates.

Layer: Glue | Gap: Level 1 (beta aggregate bilinear collapse)
Proof: push scalar subtraction through the continuous linear map and the real
  inner product on the left and right arguments, then rewrite with the supplied
  aggregate-collapse equations.
Source: Mathlib continuous-linear-map linearity and real inner-product algebra APIs
Used in: accelerated primal-dual saddle-gap aggregate bilinear-term collapse
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem linearMap_inner_beta_aggregate_collapse
    {X Y : Type*} [SeminormedAddCommGroup X] [SeminormedAddCommGroup Y]
    [InnerProductSpace ℝ X] [InnerProductSpace ℝ Y]
    (A : X →L[ℝ] Y) (β : ℝ)
    (xBarPrev xBarNext xNext xTarget : X)
    (yBarPrev yBarNext yNext yTarget : Y)
    (hxagg : β • xBarNext - (β - 1) • xBarPrev = xNext)
    (hyagg : β • yBarNext - (β - 1) • yBarPrev = yNext) :
    (β * ⟪A xBarNext, yTarget⟫_ℝ -
        (β - 1) * ⟪A xBarPrev, yTarget⟫_ℝ =
      ⟪A xNext, yTarget⟫_ℝ) ∧
    (β * ⟪A xTarget, yBarNext⟫_ℝ -
        (β - 1) * ⟪A xTarget, yBarPrev⟫_ℝ =
      ⟪A xTarget, yNext⟫_ℝ) := by
  constructor
  · calc
      β * ⟪A xBarNext, yTarget⟫_ℝ -
          (β - 1) * ⟪A xBarPrev, yTarget⟫_ℝ
          = ⟪A (β • xBarNext - (β - 1) • xBarPrev), yTarget⟫_ℝ := by
              rw [map_sub, map_smul, map_smul, inner_sub_left,
                real_inner_smul_left, real_inner_smul_left]
      _ = ⟪A xNext, yTarget⟫_ℝ := by rw [hxagg]
  · calc
      β * ⟪A xTarget, yBarNext⟫_ℝ -
          (β - 1) * ⟪A xTarget, yBarPrev⟫_ℝ
          = ⟪A xTarget, β • yBarNext - (β - 1) • yBarPrev⟫_ℝ := by
              rw [inner_sub_right, real_inner_smul_right, real_inner_smul_right]
      _ = ⟪A xTarget, yNext⟫_ℝ := by rw [hyagg]

/-- A reciprocal schedule recurrence preserves an adjacent quotient under a
theta-to-denominator ratio bound.

If `gamma i = (theta i)⁻¹ * gamma (i - 1)`, the denominator schedule is
positive at the two adjacent indices, and `theta i <= s (i - 1) / s i`, then
`gamma / s` is monotone across this adjacent step.

Layer: Glue | Gap: Level 1 (reciprocal schedule quotient monotonicity)
Proof: clear the positive denominator in the theta-ratio assumption, use
  antitonicity of inversion on positive reals, scale by the nonnegative
  previous gamma weight, and rewrite by the reciprocal recurrence.
Source: Mathlib ordered real field division, inversion, and linear arithmetic
  APIs for scalar schedule algebra
Used in: stochastic accelerated primal-dual Young-coupling and Bregman-boundary
  monotonicity for tau and eta schedules
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec/parameters
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem gamma_div_schedule_mono_of_theta_le_ratio
    (gamma theta s : ℕ → ℝ) (i : ℕ)
    (htheta_pos : 0 < theta i)
    (hs_prev_pos : 0 < s (i - 1))
    (hs_pos : 0 < s i)
    (hgamma_prev_nonneg : 0 ≤ gamma (i - 1))
    (htheta_le_ratio : theta i ≤ s (i - 1) / s i)
    (hgamma_rec : gamma i = (theta i)⁻¹ * gamma (i - 1)) :
    gamma (i - 1) / s (i - 1) ≤ gamma i / s i := by
  have hden_le : theta i * s i ≤ s (i - 1) := by
    have hmul := mul_le_mul_of_nonneg_right htheta_le_ratio (le_of_lt hs_pos)
    have hdiv : (s (i - 1) / s i) * s i = s (i - 1) := by
      field_simp [ne_of_gt hs_pos]
    nlinarith [hmul, hdiv]
  have hinv_le :
      (s (i - 1))⁻¹ ≤ (theta i * s i)⁻¹ := by
    exact (inv_le_inv₀ hs_prev_pos (mul_pos htheta_pos hs_pos)).mpr hden_le
  have hscale :
      gamma (i - 1) * (s (i - 1))⁻¹ ≤
        gamma (i - 1) * (theta i * s i)⁻¹ :=
    mul_le_mul_of_nonneg_left hinv_le hgamma_prev_nonneg
  calc
    gamma (i - 1) / s (i - 1)
        = gamma (i - 1) * (s (i - 1))⁻¹ := by ring
    _ ≤ gamma (i - 1) * (theta i * s i)⁻¹ := hscale
    _ = gamma i / s i := by
      rw [hgamma_rec]
      field_simp [ne_of_gt htheta_pos, ne_of_gt hs_pos]

/-- A one-based reciprocal scalar recurrence preserves positivity.

If the initial weight `gamma 1` is positive and each later weight is obtained
by multiplying the previous weight by the inverse of a positive `theta`, then
all positive-time weights are positive.

Layer: Glue | Gap: Level 0 (reciprocal scalar recurrence positivity)
Proof: strong induction on the natural time index. The step uses positivity of
  the reciprocal factor and the induction hypothesis at the predecessor.
Source: Mathlib ordered-field inversion, multiplication positivity, and
  natural-number strong induction APIs
Used in: stochastic accelerated primal-dual and accelerated mirror-prox
  schedule positivity before reciprocal averaging and weighted telescopes
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec/parameters
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem gamma_pos_of_inverse_theta_recurrence
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (gamma theta : ℕ → K)
    (hgamma_one_pos : 0 < gamma 1)
    (hgamma_rec : ∀ t, 2 ≤ t → gamma t = (theta t)⁻¹ * gamma (t - 1))
    (htheta_pos : ∀ t, 2 ≤ t → 0 < theta t)
    (i : ℕ) (hi : 1 ≤ i) :
    0 < gamma i := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
      by_cases hbase : i = 1
      · simpa [hbase] using hgamma_one_pos
      · have hi2 : 2 ≤ i := by omega
        have hprev : 0 < gamma (i - 1) := ih (i - 1) (by omega) (by omega)
        have htheta : 0 < theta i := htheta_pos i hi2
        rw [hgamma_rec i hi2]
        exact mul_pos (inv_pos.mpr htheta) hprev

/-- A guarded one-based predecessor-difference sum telescopes to its final value.

On the closed interval `1..t`, the first branch contributes `C 1` and each
later branch contributes `C i - C (i - 1)`, so all intermediate terms cancel.

Layer: Glue | Gap: Level 0 (guarded closed-interval predecessor telescope)
Proof: induction on the right endpoint, split the final interval term with
  `Finset.sum_Icc_succ_top`, simplify the guarded boundary cases, and cancel
  in the additive group.
Source: Mathlib finite sums over natural closed intervals and natural-number
  predecessor arithmetic
Used in: stochastic accelerated primal-dual coupling-boundary telescope
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
theorem sum_Icc_one_sub_predecessor_eq_last {α : Type*} [AddCommGroup α]
    (C : ℕ → α) (t : ℕ) (ht : 1 ≤ t) :
    Finset.sum (Finset.Icc 1 t)
        (fun i => if 1 ≤ i then C i - (if 2 ≤ i then C (i - 1) else 0) else 0) =
      C t := by
  classical
  revert ht
  induction t with
  | zero =>
      intro ht
      omega
  | succ k ih =>
      intro ht
      cases k with
      | zero =>
          simp
      | succ j =>
          have hjpos : 1 ≤ Nat.succ j := by omega
          have hsplit :
              Finset.sum (Finset.Icc 1 (Nat.succ (Nat.succ j)))
                  (fun i =>
                    if 1 ≤ i then C i - (if 2 ≤ i then C (i - 1) else 0) else 0) =
                Finset.sum (Finset.Icc 1 (Nat.succ j))
                    (fun i =>
                      if 1 ≤ i then C i - (if 2 ≤ i then C (i - 1) else 0) else 0) +
                  (C (Nat.succ (Nat.succ j)) - C (Nat.succ j)) := by
            have htop :=
              Finset.sum_Icc_succ_top
                (by omega : 1 ≤ Nat.succ (Nat.succ j))
                (fun i =>
                  if 1 ≤ i then C i - (if 2 ≤ i then C (i - 1) else 0) else 0)
            simpa using htop
          calc
            Finset.sum (Finset.Icc 1 (Nat.succ (Nat.succ j)))
                (fun i =>
                  if 1 ≤ i then C i - (if 2 ≤ i then C (i - 1) else 0) else 0) =
                Finset.sum (Finset.Icc 1 (Nat.succ j))
                    (fun i =>
                      if 1 ≤ i then C i - (if 2 ≤ i then C (i - 1) else 0) else 0) +
                  (C (Nat.succ (Nat.succ j)) - C (Nat.succ j)) := hsplit
            _ = C (Nat.succ j) +
                  (C (Nat.succ (Nat.succ j)) - C (Nat.succ j)) := by
                rw [ih hjpos]
            _ = C (Nat.succ (Nat.succ j)) := by
                abel

/-- Isolate the second summand in a scaled two-term real inequality after
splitting the scaled first summand.

If `gamma * (raw + gdiff)` is bounded by `rhs`, and the scaled `raw` term
has been split as `gamma * deltaInner - gamma * targetInner`, then the second
scaled term is bounded by `rhs` minus the residual contribution plus the
target contribution.

Layer: Glue | Gap: Level 0 (scaled additive-term isolation)
Proof: expand the ordered real inequality with the supplied scaled split and
  discharge the rearrangement by linear arithmetic.
Source: Mathlib ordered-ring arithmetic and linear inequality normalization
Used in: stochastic primal-dual one-step descent after oracle residual/target
  decomposition
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
theorem mul_add_sub_isolate_second_term
    (gamma raw deltaInner targetInner gdiff rhs : ℝ)
    (hbound : gamma * (raw + gdiff) ≤ rhs)
    (hsplit : gamma * raw = gamma * deltaInner - gamma * targetInner) :
    gamma * gdiff ≤ rhs - gamma * deltaInner + gamma * targetInner := by
  linarith

/-- A lagged adjoint bilinear expression cancels to current coupling plus two lag
couplings split through an intermediate dual point.

This packages the algebraic step where the adjoint pairing
`⟪A† yNext, xNext - zx⟫` is moved through `A`, the current `γ`-weighted
terms collect into `⟪A (xNext - xPrev), zy - yNext⟫`, and the previous
`γPrev`-weighted lag increment is split at `yPrev`.

Layer: Glue | Gap: Level 1 (adjoint lagged bilinear cancellation)
Proof: rewrite the adjoint pairing with `ContinuousLinearMap.adjoint_inner_right`,
  expand linear-map subtraction and inner-product subtraction, then normalize
  the real scalar algebra.
Source: Mathlib continuous-linear-map adjoints and real inner-product algebra APIs
Used in: stochastic accelerated primal-dual lagged extrapolation coupling cancellation
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec/steps
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic accelerated primal-dual -/
theorem linearMap_adjoint_lagged_bilinear_cancellation
    {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [InnerProductSpace ℝ X] [InnerProductSpace ℝ Y]
    [CompleteSpace X] [CompleteSpace Y]
    (A : X →L[ℝ] Y) (γ γPrev : ℝ)
    (xPrev xNext xLag zx : X) (yPrev yNext zy : Y) :
    -γ * ⟪A.adjoint yNext, xNext - zx⟫_ℝ +
      γ * ⟪A xNext, zy⟫_ℝ -
      γ * ⟪A zx, yNext⟫_ℝ +
      γ * ⟪A xPrev, yNext - zy⟫_ℝ +
      γPrev * ⟪A xLag, yNext - zy⟫_ℝ =
    γ * ⟪A (xNext - xPrev), zy - yNext⟫_ℝ -
      γPrev * ⟪A xLag, zy - yPrev⟫_ℝ -
      γPrev * ⟪A xLag, yPrev - yNext⟫_ℝ := by
  have hAT :
      ⟪A.adjoint yNext, xNext - zx⟫_ℝ =
        ⟪A (xNext - zx), yNext⟫_ℝ := by
    calc
      ⟪A.adjoint yNext, xNext - zx⟫_ℝ =
          ⟪xNext - zx, A.adjoint yNext⟫_ℝ := by
            rw [real_inner_comm]
      _ = ⟪A (xNext - zx), yNext⟫_ℝ :=
            ContinuousLinearMap.adjoint_inner_right (A := A) (xNext - zx) yNext
  rw [hAT]
  simp only [ContinuousLinearMap.map_sub, inner_sub_left, inner_sub_right]
  ring

/-- Add two scalar descent bounds and rewrite their coupling, square, and noise
terms into the final one-step right-hand side.

This is the ordered-field algebra step used after independent lemmas have
already supplied a primal bound, a dual bound, a bilinear coupling identity, a
squared-step normalization, and the additive noise split.

Layer: Glue | Gap: Level 1 (one-step scalar descent-bound assembly)
Proof: combine the two upper bounds and the three scalar rewrite identities by
  linear arithmetic over real ordered rings.
Source: Mathlib real ordered-ring linear arithmetic and subtraction APIs
Used in: stochastic accelerated primal-dual one-step descent assembly after
  prox, bilinear-coupling, squared-step, and oracle-noise estimates
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
theorem add_two_bounds_with_bilinear_square_noise_assembly
    (a b q c e vx sx vy sy atTerm dxn dyn gt coupling square : ℝ)
    (hgrad : a ≤ vx - sx - atTerm - dxn)
    (hhatg : b ≤ vy - sy - dyn + gt)
    (hbilinear : -atTerm + c - e + gt = coupling)
    (hx_square : -sx + q = square)
    (hnoise_expand : -(dxn + dyn) = -dxn - dyn) :
    a + b + q + c - e ≤
      vx + vy + coupling + square - sy - (dxn + dyn) := by
  have hnoise_rhs :
      vx + vy + coupling + square - sy - (dxn + dyn) =
        vx + vy + coupling + square - sy - dxn - dyn := by
    calc
      vx + vy + coupling + square - sy - (dxn + dyn)
          = vx + vy + coupling + square - sy + -(dxn + dyn) := by ring
      _ = vx + vy + coupling + square - sy + (-dxn - dyn) := by
          rw [hnoise_expand]
      _ = vx + vy + coupling + square - sy - dxn - dyn := by ring
  rw [hnoise_rhs]
  linarith [hgrad, hhatg, hbilinear, hx_square]

/-- Sum a guarded family of negative linear-map bilinear couplings after Young absorption.

On every finite-set index where both predicates are active, the pointwise
operator-norm Young bound controls `-gammaPrev i * <A (dx i), dy i>`.  Summing
those pointwise inequalities gives the corresponding guarded finite-window
bound with indexed coefficients.

Layer: Glue | Gap: Level 1 (guarded finite-sum operator Young absorption)
Proof: apply `Finset.sum_le_sum`; on active guarded indices use the pointwise
  operator Young bound with ratio transport, and simplify inactive branches to
  `0 ≤ 0`.
Source: Mathlib finite-sum order API, real inner-product Cauchy-Schwarz, and
  continuous linear-map operator norm bounds
Used in: stochastic accelerated primal-dual lagged bilinear-coupling absorption
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem sum_lag_cross_young_bound
    {ι E F : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    [SeminormedAddCommGroup F] [InnerProductSpace ℝ F]
    (s : Finset ι) (guard active : ι → Prop)
    [DecidablePred guard] [DecidablePred active]
    (A : E →L[ℝ] F) (dx : ι → E) (dy : ι → F)
    (gammaPrev gammaNext tauPrev tau p : ι → ℝ)
    (hgammaPrev : ∀ i, i ∈ s → guard i → active i → 0 < gammaPrev i)
    (htauPrev : ∀ i, i ∈ s → guard i → active i → 0 < tauPrev i)
    (htau : ∀ i, i ∈ s → guard i → active i → 0 < tau i)
    (hp : ∀ i, i ∈ s → guard i → active i → 0 < p i)
    (hratio :
      ∀ i, i ∈ s → guard i → active i → gammaPrev i / tauPrev i ≤ gammaNext i / tau i) :
    Finset.sum s (fun i =>
        if _hg : guard i then
          if _ha : active i then
            -gammaPrev i * ⟪A (dx i), dy i⟫_ℝ
          else 0
        else 0) ≤
      Finset.sum s (fun i =>
        if _hg : guard i then
          if _ha : active i then
            gammaPrev i * tauPrev i / (2 * p i) * (‖A‖ ^ 2 * ‖dx i‖ ^ 2) +
              p i * gammaNext i / (2 * tau i) * ‖dy i‖ ^ 2
          else 0
        else 0) := by
  classical
  refine Finset.sum_le_sum ?_
  intro i hi
  by_cases hg : guard i
  · by_cases ha : active i
    · have hinner_nonpos :
          -⟪A (dx i), dy i⟫_ℝ ≤ ‖A (dx i)‖ * ‖dy i‖ := by
        have habs : |⟪A (dx i), dy i⟫_ℝ| ≤ ‖A (dx i)‖ * ‖dy i‖ :=
          by simpa [Real.norm_eq_abs] using
            norm_inner_le_norm (𝕜 := ℝ) (A (dx i)) (dy i)
        exact le_trans (neg_le_abs _) habs
      have hinner_scaled :
          -gammaPrev i * ⟪A (dx i), dy i⟫_ℝ ≤
            gammaPrev i * (‖A (dx i)‖ * ‖dy i‖) := by
        have h := mul_le_mul_of_nonneg_left hinner_nonpos
          (le_of_lt (hgammaPrev i hi hg ha))
        nlinarith
      have hA : ‖A (dx i)‖ ≤ ‖A‖ * ‖dx i‖ :=
        A.le_opNorm (dx i)
      have hprod :
          gammaPrev i * (‖A (dx i)‖ * ‖dy i‖) ≤
            gammaPrev i * ((‖A‖ * ‖dx i‖) * ‖dy i‖) := by
        have hmul := mul_le_mul_of_nonneg_right hA (norm_nonneg (dy i))
        exact mul_le_mul_of_nonneg_left hmul
          (le_of_lt (hgammaPrev i hi hg ha))
      let L : ℝ := p i / (gammaPrev i * tauPrev i)
      have hL : 0 < L := by
        exact div_pos (hp i hi hg ha)
          (mul_pos (hgammaPrev i hi hg ha) (htauPrev i hi hg ha))
      have hyoung :=
        mul_mul_le_inv_two_mul_add_half_mul_sq
          (R := ℝ) (‖dy i‖) (‖A‖ * ‖dx i‖) (gammaPrev i) L hL
      have hyoung_norm :
          gammaPrev i * ((‖A‖ * ‖dx i‖) * ‖dy i‖) ≤
            gammaPrev i * tauPrev i / (2 * p i) * (‖A‖ ^ 2 * ‖dx i‖ ^ 2) +
              p i * gammaPrev i / (2 * tauPrev i) * ‖dy i‖ ^ 2 := by
        dsimp [L] at hyoung
        convert hyoung using 1
        · ring
        · field_simp [ne_of_gt (hp i hi hg ha), ne_of_gt (hgammaPrev i hi hg ha),
            ne_of_gt (htauPrev i hi hg ha)]
      have hycoeff :
          p i * gammaPrev i / (2 * tauPrev i) * ‖dy i‖ ^ 2 ≤
            p i * gammaNext i / (2 * tau i) * ‖dy i‖ ^ 2 := by
        have hmul := mul_le_mul_of_nonneg_left (hratio i hi hg ha)
          (le_of_lt (half_pos (hp i hi hg ha)))
        have hmul2 := mul_le_mul_of_nonneg_right hmul (sq_nonneg ‖dy i‖)
        have hleft :
            (p i / 2) * (gammaPrev i / tauPrev i) * ‖dy i‖ ^ 2 =
              p i * gammaPrev i / (2 * tauPrev i) * ‖dy i‖ ^ 2 := by
          field_simp [ne_of_gt (htauPrev i hi hg ha)]
        have hright :
            (p i / 2) * (gammaNext i / tau i) * ‖dy i‖ ^ 2 =
              p i * gammaNext i / (2 * tau i) * ‖dy i‖ ^ 2 := by
          field_simp [ne_of_gt (htau i hi hg ha)]
        simpa [hleft, hright] using hmul2
      have hraise :
          gammaPrev i * tauPrev i / (2 * p i) * (‖A‖ ^ 2 * ‖dx i‖ ^ 2) +
              p i * gammaPrev i / (2 * tauPrev i) * ‖dy i‖ ^ 2 ≤
            gammaPrev i * tauPrev i / (2 * p i) * (‖A‖ ^ 2 * ‖dx i‖ ^ 2) +
              p i * gammaNext i / (2 * tau i) * ‖dy i‖ ^ 2 :=
        by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_left hycoeff
              (gammaPrev i * tauPrev i / (2 * p i) * (‖A‖ ^ 2 * ‖dx i‖ ^ 2))
      exact (by
        simpa [hg, ha] using
          le_trans hinner_scaled (le_trans hprod (le_trans hyoung_norm hraise)))
    · simpa [hg, ha] using (le_rfl : (0 : ℝ) ≤ 0)
  · simpa [hg] using (le_rfl : (0 : ℝ) ≤ 0)

/-- A one-based shifted-difference recurrence telescopes to the terminal potential.

If the first step equals `W 1` and every later step is `W i - W (i - 1)`,
then summing the steps over `1..t` leaves only the terminal value `W t`.

Layer: Glue | Gap: Level 0 (one-based shifted-difference telescope)
Proof: induction on the right endpoint, splitting the final closed-interval
  term with `Finset.sum_Icc_succ_top`; the base and predecessor boundary cases
  are discharged by natural-number arithmetic and additive-group cancellation.
Source: Mathlib finite sums over natural closed intervals and natural-number
  predecessor arithmetic
Used in: stochastic accelerated primal-dual weighted averaged-output telescope
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
theorem sum_Icc_shifted_sub_telescope_from_one {α : Type*} [AddCommGroup α]
    (W stepTerm : ℕ → α) (t : ℕ) (ht : 1 ≤ t)
    (hbase_step : stepTerm 1 = W 1)
    (hstep_succ : ∀ i, 2 ≤ i → stepTerm i = W i - W (i - 1)) :
    Finset.sum (Finset.Icc 1 t) stepTerm = W t := by
  classical
  revert ht
  induction t with
  | zero =>
      intro ht
      omega
  | succ k ih =>
      intro ht
      cases k with
      | zero =>
          simpa using hbase_step
      | succ j =>
          have hjpos : 1 ≤ Nat.succ j := by omega
          have htop : 2 ≤ Nat.succ (Nat.succ j) := by omega
          have hsum_top :
              Finset.sum (Finset.Icc 1 (Nat.succ (Nat.succ j))) stepTerm =
                Finset.sum (Finset.Icc 1 (Nat.succ j)) stepTerm +
                  stepTerm (Nat.succ (Nat.succ j)) := by
            simpa using
              (Finset.sum_Icc_succ_top
                (by omega : 1 ≤ Nat.succ (Nat.succ j)) stepTerm)
          have hih :
              Finset.sum (Finset.Icc 1 (Nat.succ j)) stepTerm =
                W (Nat.succ j) :=
            ih hjpos
          have htop_step :
              stepTerm (Nat.succ (Nat.succ j)) =
                W (Nat.succ (Nat.succ j)) - W (Nat.succ j) := by
            simpa using hstep_succ (Nat.succ (Nat.succ j)) htop
          calc
            Finset.sum (Finset.Icc 1 (Nat.succ (Nat.succ j))) stepTerm =
                Finset.sum (Finset.Icc 1 (Nat.succ j)) stepTerm +
                  stepTerm (Nat.succ (Nat.succ j)) := hsum_top
            _ = W (Nat.succ j) + (W (Nat.succ (Nat.succ j)) - W (Nat.succ j)) := by
                rw [hih, htop_step]
            _ = W (Nat.succ (Nat.succ j)) := by
                abel

/-- Absorb a Young square term using a scalar parameter-coupling condition.

If the coupling budget
`q / eta - L / beta - A_norm ^ 2 * tau / p` is nonnegative, then multiplying
it by a nonnegative weight and a squared norm gives the absorbed quadratic
inequality used after a Young split.

Layer: Glue | Gap: Level 1 (scalar square absorption from parameter coupling)
Proof: halve the coupling budget, multiply it by the nonnegative weighted
  square, and rewrite the resulting nonnegative difference by ring arithmetic.
Source: Mathlib seminormed additive groups and ordered real-ring arithmetic
Used in: stochastic accelerated primal-dual primal-square Young absorption
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem x_square_young_absorb_of_param_coupling
    {E : Type*} [SeminormedAddCommGroup E]
    (gamma eta beta tau L A_norm p q : ℝ) (dx : E)
    (hgamma : 0 ≤ gamma)
    (hcoupling : 0 ≤ q / eta - L / beta - A_norm ^ 2 * tau / p) :
    -gamma * (1 / (2 * eta) - L / (2 * beta)) * ‖dx‖ ^ 2 +
      gamma * tau / (2 * p) * (A_norm ^ 2 * ‖dx‖ ^ 2) ≤
      -((1 - q) * gamma / (2 * eta)) * ‖dx‖ ^ 2 := by
  have hcoupling_half :
      0 ≤ q / (2 * eta) - L / (2 * beta) - A_norm ^ 2 * tau / (2 * p) := by
    have hhalf := mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) hcoupling
    convert hhalf using 1
    ring
  have hsq : 0 ≤ ‖dx‖ ^ 2 := sq_nonneg ‖dx‖
  have hbudget :
      0 ≤ gamma * ‖dx‖ ^ 2 *
        (q / (2 * eta) - L / (2 * beta) - A_norm ^ 2 * tau / (2 * p)) := by
    exact mul_nonneg (mul_nonneg hgamma hsq) hcoupling_half
  have hdiff :
      -((1 - q) * gamma / (2 * eta)) * ‖dx‖ ^ 2 -
        (-gamma * (1 / (2 * eta) - L / (2 * beta)) * ‖dx‖ ^ 2 +
          gamma * tau / (2 * p) * (A_norm ^ 2 * ‖dx‖ ^ 2)) =
        gamma * ‖dx‖ ^ 2 *
          (q / (2 * eta) - L / (2 * beta) - A_norm ^ 2 * tau / (2 * p)) := by
    ring
  nlinarith

-- Generalization plan (G0):
-- concept/name: branch absorption for a y-square Young budget with `p ∈ (0, 1)`; orig was generated_y_square_young_branch_pointwise.
-- generality used: arbitrary seminormed additive commutative group for the displacement norm, pointwise real scalars `p`, `gamma`, and `tau`, and an arbitrary decidable branch proposition; no measure, filtration, convexity, smoothness, oracle, or finite-dimensional assumptions are used.
-- portable call pattern: accelerated primal-dual, mirror-prox, and extragradient proofs often sum Young-window square budgets only on an active branch, while subtracting the full displacement square at every index; schedules and branch predicates change, but the scalar absorption conclusion stays the same.
-- counterargument checked: not paper-local traceability because the statement removes SAPD iterates and keeps only the reusable scalar/norm branch absorption; not a duplicate of the coefficient identity because this proves an inequality for inactive branches where the positive `p` budget is absent.
-- coverage search: searched `generated_y_square_young_branch_pointwise`, `y_square branch Young absorb active`, catalog Young/coefficient hits, and LeanSearch for active real norm-square branch inequalities; Mathlib has order/ring primitives and SOptLib has the adjacent y-square coefficient equality, but no guarded branch absorption theorem.
-- minimal hypotheses: `p ∈ Ioo 0 1` supplies the nonnegative budget coefficient, `gamma ≥ 0` and `tau > 0` make `gamma / (2 * tau)` nonnegative; no upper-bound use beyond the standard interval hypothesis is needed here.

/-- Absorb a possibly inactive y-square Young budget into the full square penalty.

If the branch is active, the left side is exactly the coefficient
`-(1 - p)`.  If the branch is inactive, the omitted budget is nonnegative
because `p ∈ (0, 1)`, `gamma ≥ 0`, and `tau > 0`.

Layer: Glue | Gap: Level 1 (guarded y-square Young budget absorption)
Proof: split on the branch proposition; the active case is ring arithmetic,
  and the inactive case follows from nonnegativity of the omitted `p`-weighted
  square budget.
Source: Mathlib ordered real-ring arithmetic and norm-square nonnegativity
Used in: stochastic accelerated primal-dual y-square absorption in the
  finite Young window
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem y_square_branch_absorb_of_p_mem_Ioo
    {E : Type*} [SeminormedAddCommGroup E]
    (p gamma tau : ℝ) (dy : E) (active : Prop) [Decidable active]
    (hp : p ∈ Set.Ioo (0 : ℝ) 1)
    (hgamma : 0 ≤ gamma) (htau : 0 < tau) :
    (if _hactive : active then
        p * gamma / (2 * tau) * ‖dy‖ ^ 2
      else 0) -
      gamma / (2 * tau) * ‖dy‖ ^ 2 ≤
      -((1 - p) * gamma / (2 * tau)) * ‖dy‖ ^ 2 := by
  classical
  by_cases hactive : active
  · simp [hactive]
    ring_nf
    exact le_rfl
  · have hp_nonneg : 0 ≤ p := le_of_lt hp.1
    have hden : 0 ≤ 2 * tau := mul_nonneg (by norm_num) (le_of_lt htau)
    have hcoeff : 0 ≤ gamma / (2 * tau) := div_nonneg hgamma hden
    have hsq : 0 ≤ ‖dy‖ ^ 2 := sq_nonneg _
    have hbudget : 0 ≤ p * (gamma / (2 * tau)) * ‖dy‖ ^ 2 :=
      mul_nonneg (mul_nonneg hp_nonneg hcoeff) hsq
    have hdiff :
        -((1 - p) * gamma / (2 * tau)) * ‖dy‖ ^ 2 -
            (0 - gamma / (2 * tau) * ‖dy‖ ^ 2) =
          p * (gamma / (2 * tau)) * ‖dy‖ ^ 2 := by
      ring
    simpa [hactive] using
      (by
        nlinarith [hbudget, hdiff] :
          0 - gamma / (2 * tau) * ‖dy‖ ^ 2 ≤
            -((1 - p) * gamma / (2 * tau)) * ‖dy‖ ^ 2)

/-- Sum a branchwise square absorption inequality over a finite window.

Layer: Glue | Gap: Level 1 (finite-window guarded square absorption)
Proof: rewrite the difference of sums with `Finset.sum_sub_distrib`, then
  apply `Finset.sum_le_sum` and discharge each index by the scalar
  nonnegativity budget.
Source: Mathlib finite-sum order API and real norm-square arithmetic
Used in: stochastic accelerated primal-dual Young-window absorption after
  reindexing the y-square branch
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem sum_guarded_sq_absorb_of_nonneg
    {ι E : Type*} [SeminormedAddCommGroup E]
    (s : Finset ι) (dy : ι → E) (p : ℝ) (coeff : ι → ℝ)
    (active : ι → Prop) [DecidablePred active]
    (hp : 0 ≤ p) (hcoeff : ∀ i, i ∈ s → 0 ≤ coeff i) :
    Finset.sum s (fun i =>
        if active i then p * coeff i * ‖dy i‖ ^ 2 else 0) -
      Finset.sum s (fun i => coeff i * ‖dy i‖ ^ 2) ≤
      Finset.sum s (fun i => -((1 - p) * coeff i) * ‖dy i‖ ^ 2) := by
  classical
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum ?_
  intro i hi
  by_cases hactive : active i
  · simp [hactive]
    ring_nf
    exact le_rfl
  · have hbudget : 0 ≤ p * coeff i * ‖dy i‖ ^ 2 :=
      mul_nonneg (mul_nonneg hp (hcoeff i hi)) (sq_nonneg _)
    have hdiff :
        -((1 - p) * coeff i) * ‖dy i‖ ^ 2 -
            (0 - coeff i * ‖dy i‖ ^ 2) =
          p * coeff i * ‖dy i‖ ^ 2 := by
      ring
    simpa [hactive] using
      (by
        nlinarith [hbudget, hdiff] :
          0 - coeff i * ‖dy i‖ ^ 2 ≤
            -((1 - p) * coeff i) * ‖dy i‖ ^ 2)

-- Generalization plan (G0):
-- concept/name: finite-window y-square branch absorption; orig was generated_y_square_young_absorption
-- generality used: an arbitrary finite set of natural indices, a lower-bound witness `1 ≤ i` on the support, an arbitrary seminormed additive commutative group for the displacement norms, and pointwise real schedules `p`, `gamma`, and `tau`; no measure, filtration, convexity, smoothness, oracle, or finite-dimensional assumptions are used
-- portable call pattern: accelerated primal-dual, mirror-prox, and extragradient proofs sum branchwise Young absorptions over a finite window, while the active branch and schedule coefficients change from algorithm to algorithm
-- counterargument checked: not paper-local traceability because the theorem strips SAPD iterates away and packages the reusable finite-sum lift of a pointwise absorption inequality; not a duplicate of `Finset.sum_le_sum` because it keeps the branch structure and coefficient normalization together
-- coverage search: searched `generated_y_square_young_absorption`, `y_square branch absorption`, `sum_le_sum`, and nearby Young-absorption catalog entries; Mathlib has the finite-sum monotonicity API, and SOptLib has the pointwise guarded absorption lemma, but no finite-window branch absorption packaging
-- minimal hypotheses: only pointwise nonnegativity of `p` and of `gamma i / (2 * tau i)` on the summation support are needed; all other algorithmic structure is caller-side

/-- Sum a branchwise y-square absorption inequality over a finite window.

Each summand is controlled by the pointwise guarded Young absorption lemma.
The outer `1 ≤ i` guard is preserved so the theorem specializes directly to
SAPD-style finite windows over `Finset.Icc 1 t`.

Layer: Glue | Gap: Level 1 (finite-window y-square branch absorption)
Proof: rewrite the difference of sums with `Finset.sum_sub_distrib`, then
  apply `Finset.sum_le_sum` and discharge each index by the pointwise guarded
  absorption lemma.
Source: Mathlib finite-sum order API and real norm-square arithmetic
Used in: stochastic accelerated primal-dual Young-window absorption after
  reindexing the y-square branch
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem sum_y_square_branch_absorption
    {E : Type*} [SeminormedAddCommGroup E]
    (s : Finset ℕ) (h1 : ∀ i ∈ s, 1 ≤ i)
    (dy : ℕ → E) (p : ℝ) (gamma tau : ℕ → ℝ)
    (hp : 0 ≤ p)
    (hcoeff : ∀ i ∈ s, 0 ≤ gamma i / (2 * tau i)) :
    Finset.sum s (fun i =>
        if _hi : 1 ≤ i then
          if _h2 : 2 ≤ i then
            p * gamma i / (2 * tau i) * ‖dy i‖ ^ 2
          else 0
        else 0) -
      Finset.sum s (fun i =>
        if _hi : 1 ≤ i then
          gamma i / (2 * tau i) * ‖dy i‖ ^ 2
        else 0) ≤
      Finset.sum s (fun i =>
        if _hi : 1 ≤ i then
          -((1 - p) * gamma i / (2 * tau i)) * ‖dy i‖ ^ 2
        else 0) := by
  classical
  let coeff : ℕ → ℝ := fun i => gamma i / (2 * tau i)
  have hgeneric :
      Finset.sum s (fun i =>
          if 2 ≤ i then p * coeff i * ‖dy i‖ ^ 2 else 0) -
        Finset.sum s (fun i => coeff i * ‖dy i‖ ^ 2) ≤
        Finset.sum s (fun i => -((1 - p) * coeff i) * ‖dy i‖ ^ 2) := by
    exact sum_guarded_sq_absorb_of_nonneg s dy p coeff (fun i : ℕ => 2 ≤ i) hp
      (by simpa [coeff] using hcoeff)
  have hfirst :
      Finset.sum s (fun i =>
          if _hi : 1 ≤ i then
            if _h2 : 2 ≤ i then
              p * gamma i / (2 * tau i) * ‖dy i‖ ^ 2
            else 0
          else 0) =
        Finset.sum s (fun i =>
          if 2 ≤ i then p * coeff i * ‖dy i‖ ^ 2 else 0) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hi1 : 1 ≤ i := h1 i hi
    by_cases h2 : 2 ≤ i
    · have hscalar :
          p * gamma i / (2 * tau i) = p * (gamma i / (2 * tau i)) := by ring
      simp [hi1, h2, coeff, hscalar]
    · simp [hi1, h2]
  have hsecond :
      Finset.sum s (fun i =>
          if _hi : 1 ≤ i then
            gamma i / (2 * tau i) * ‖dy i‖ ^ 2
          else 0) =
        Finset.sum s (fun i => coeff i * ‖dy i‖ ^ 2) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    simp [h1 i hi, coeff]
  have hthird :
      Finset.sum s (fun i =>
          if _hi : 1 ≤ i then
            -((1 - p) * gamma i / (2 * tau i)) * ‖dy i‖ ^ 2
          else 0) =
        Finset.sum s (fun i => -((1 - p) * coeff i) * ‖dy i‖ ^ 2) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hscalar :
        (1 - p) * gamma i / (2 * tau i) =
          (1 - p) * (gamma i / (2 * tau i)) := by ring
    simp [h1 i hi, coeff, hscalar]
  rw [hfirst, hsecond, hthird]
  exact hgeneric

-- Generalization plan (G0):
-- concept/name: y-square coefficient subtraction normalization; orig was generated_y_square_young_pointwise
-- generality used: an arbitrary seminormed additive commutative group for the displacement terms, with only pointwise real scalars p gamma tau; no measure, filtration, convexity, smoothness, oracle, or finite-dimensional assumptions
-- portable call pattern: accelerated primal-dual and mirror-prox y-square absorption steps where a reversed norm term is normalized before the Young-window coefficient is collected; the block states and schedules change while the scalar identity stays the same
-- counterargument checked: this is not merely paper-local traceability because it packages the reusable symmetry-and-coefficient rewrite for any normed displacement; it is not a caller-side expression because the normalization is the proof step consumed by later finite-window absorptions
-- coverage search: searched `generated_y_square_young_pointwise`, `y square coefficient subtraction normalization`, `norm_sub_rev`, and catalog Young/coefficient hits; Mathlib gives the norm symmetry and scalar ring algebra, and SOptLib has adjacent Young-absorption lemmas, but no exact packaged identity for this subtraction normalization
-- minimal hypotheses: all already minimal; no positivity or extra structure is required beyond the seminormed additive group and real scalars

/-- Normalize the y-square coefficient after reversing a norm difference.

When the two norms differ only by swapping the subtraction order, the
`p`-weighted square minus the unweighted square collapses to the coefficient
`-(1 - p)`.

Layer: Glue | Gap: Level 0 (y-square coefficient normalization)
Proof: rewrite the reversed norm with `norm_sub_rev` and finish by ring
  arithmetic.
Source: Mathlib norm symmetry and ordered real-ring arithmetic
Used in: stochastic accelerated primal-dual y-square absorption in the `Λ_i(z)`
  Young window
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic accelerated primal-dual -/
theorem y_square_young_coeff_sub_eq
    {E : Type*} [SeminormedAddCommGroup E]
    (p gamma tau : ℝ) (x y : E) :
    p * gamma / (2 * tau) * ‖x - y‖ ^ 2 - gamma / (2 * tau) * ‖y - x‖ ^ 2 =
      -((1 - p) * gamma / (2 * tau)) * ‖y - x‖ ^ 2 := by
  rw [norm_sub_rev x y]
  ring

-- Generalization plan (G0):
-- concept/name: operator-norm Young bound for a negative linear-map bilinear coupling
--   with a raised ratio coefficient; orig was generated_young_coupling_bound.
-- generality used: two arbitrary real inner-product seminormed additive groups, one
--   continuous linear map, pointwise vectors, and real scalar positivity/ratio
--   hypotheses; no measure, convexity, smoothness, oracle, or iterate structure is used.
-- portable call pattern: accelerated primal-dual, mirror-prox, and extragradient
--   one-step estimates where a lagged `-gamma * <A dx, dy>` coupling is bounded by
--   Young square terms and a schedule monotonicity fact raises the `y` coefficient.
-- counterargument checked: not paper-local traceability because the statement packages
--   Cauchy-Schwarz/operator norm control, scaled Young absorption, and coefficient
--   transport; not a pure wrapper around schedule fields or a caller-side expression.
-- coverage search: searched `Young inequality inner product continuous linear map
--   operator norm ratio coefficient`, `generated_young_coupling_bound`,
--   `inner operator Young gamma tau`, and catalog Young/operator hits. Mathlib covers
--   operator norm and Cauchy-Schwarz separately; SOptLib has scalar Young and a
--   different tail-absorption linear-map lemma, but no ratio-raised negative-coupling
--   bound with this conclusion.
-- minimal hypotheses: pointwise positivity of `gammaPrev`, `tauPrev`, `tau`, and `p`,
--   plus the ratio comparison `gammaPrev / tauPrev ≤ gammaNext / tau`.

/-- Bound a negative linear-map bilinear coupling by Young square terms.

For positive `gammaPrev`, `tauPrev`, `tau`, and `p`, the coupling
`-gammaPrev * <A dx, dy>` is controlled by an operator-norm square in `dx` and
a `dy` square.  The `dy` coefficient may be raised from
`gammaPrev / tauPrev` to any larger ratio `gammaNext / tau`.

Layer: Glue | Gap: Level 1 (operator-norm Young coupling with ratio transport)
Proof: bound the negative inner product by Cauchy-Schwarz and the operator norm,
  apply the scaled scalar Young inequality, then raise the `dy` coefficient by
  the supplied ratio comparison.
Source: Mathlib real inner-product Cauchy-Schwarz, continuous linear map operator
  norm bounds, and ordered-field Young inequality algebra
Used in: stochastic accelerated primal-dual lagged bilinear-coupling absorption
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem neg_gamma_inner_linear_le_young_with_ratio
    {E F : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    [SeminormedAddCommGroup F] [InnerProductSpace ℝ F]
    (A : E →L[ℝ] F) (dx : E) (dy : F)
    (gammaPrev gammaNext tauPrev tau p : ℝ)
    (hgammaPrev : 0 < gammaPrev) (htauPrev : 0 < tauPrev)
    (htau : 0 < tau) (hp : 0 < p)
    (hratio : gammaPrev / tauPrev ≤ gammaNext / tau) :
    -gammaPrev * ⟪A dx, dy⟫_ℝ ≤
      gammaPrev * tauPrev / (2 * p) * (‖A‖ ^ 2 * ‖dx‖ ^ 2) +
        p * gammaNext / (2 * tau) * ‖dy‖ ^ 2 := by
  have hinner_nonpos :
      -⟪A dx, dy⟫_ℝ ≤ ‖A dx‖ * ‖dy‖ := by
    have habs : |⟪A dx, dy⟫_ℝ| ≤ ‖A dx‖ * ‖dy‖ :=
      by simpa [Real.norm_eq_abs] using
        norm_inner_le_norm (𝕜 := ℝ) (A dx) dy
    have hneg : -⟪A dx, dy⟫_ℝ ≤ |⟪A dx, dy⟫_ℝ| :=
      neg_le_abs _
    exact le_trans hneg habs
  have hinner_scaled :
      -gammaPrev * ⟪A dx, dy⟫_ℝ ≤
        gammaPrev * (‖A dx‖ * ‖dy‖) := by
    have h := mul_le_mul_of_nonneg_left hinner_nonpos (le_of_lt hgammaPrev)
    nlinarith
  have hA : ‖A dx‖ ≤ ‖A‖ * ‖dx‖ :=
    A.le_opNorm dx
  have hprod :
      gammaPrev * (‖A dx‖ * ‖dy‖) ≤
        gammaPrev * ((‖A‖ * ‖dx‖) * ‖dy‖) := by
    have hmul := mul_le_mul_of_nonneg_right hA (norm_nonneg dy)
    exact mul_le_mul_of_nonneg_left hmul (le_of_lt hgammaPrev)
  let L : ℝ := p / (gammaPrev * tauPrev)
  have hL : 0 < L := by
    exact div_pos hp (mul_pos hgammaPrev htauPrev)
  have hyoung :=
    mul_mul_le_inv_two_mul_add_half_mul_sq
      (R := ℝ) (‖dy‖) (‖A‖ * ‖dx‖) gammaPrev L hL
  have hyoung_norm :
      gammaPrev * ((‖A‖ * ‖dx‖) * ‖dy‖) ≤
        gammaPrev * tauPrev / (2 * p) * (‖A‖ ^ 2 * ‖dx‖ ^ 2) +
          p * gammaPrev / (2 * tauPrev) * ‖dy‖ ^ 2 := by
    have hraw := hyoung
    dsimp [L] at hraw
    have hleft :
        ‖dy‖ * ((‖A‖ * ‖dx‖) * gammaPrev) =
          gammaPrev * ((‖A‖ * ‖dx‖) * ‖dy‖) := by
      ring
    convert hraw using 1
    · ring
    · field_simp [ne_of_gt hp, ne_of_gt hgammaPrev, ne_of_gt htauPrev]
  have hycoeff :
      p * gammaPrev / (2 * tauPrev) * ‖dy‖ ^ 2 ≤
        p * gammaNext / (2 * tau) * ‖dy‖ ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hratio (le_of_lt (half_pos hp))
    have hmul2 := mul_le_mul_of_nonneg_right hmul (sq_nonneg ‖dy‖)
    have hleft :
        (p / 2) * (gammaPrev / tauPrev) * ‖dy‖ ^ 2 =
          p * gammaPrev / (2 * tauPrev) * ‖dy‖ ^ 2 := by
      field_simp [ne_of_gt htauPrev]
    have hright :
        (p / 2) * (gammaNext / tau) * ‖dy‖ ^ 2 =
          p * gammaNext / (2 * tau) * ‖dy‖ ^ 2 := by
      field_simp [ne_of_gt htau]
    simpa [hleft, hright] using hmul2
  have hraise :
      gammaPrev * tauPrev / (2 * p) * (‖A‖ ^ 2 * ‖dx‖ ^ 2) +
          p * gammaPrev / (2 * tauPrev) * ‖dy‖ ^ 2 ≤
        gammaPrev * tauPrev / (2 * p) * (‖A‖ ^ 2 * ‖dx‖ ^ 2) +
          p * gammaNext / (2 * tau) * ‖dy‖ ^ 2 :=
    by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_left hycoeff
          (gammaPrev * tauPrev / (2 * p) * (‖A‖ ^ 2 * ‖dx‖ ^ 2))
  exact le_trans hinner_scaled (le_trans hprod (le_trans hyoung_norm hraise))

-- Generalization plan (G0):
-- concept/name: inverse-scale convex weights; orig was inv_beta_convex_weights.
-- generality used: real ordered-field scalar only; no measure, topology,
--   convexity, smoothness, oracle, norm, or finite-dimensional assumptions.
-- portable call pattern: accelerated stochastic methods convert a scale bound
--   `1 ≤ beta_t` into the two nonnegative affine weights
--   `1 - beta_t⁻¹` and `beta_t⁻¹` for midpoint, search-point, or running-average
--   feasibility proofs; the scale sequence and time index change while the
--   convex-weight conclusion stays the same.
-- counterargument checked: this is a short wrapper around standard inverse
--   facts, but no single Mathlib/SOptLib declaration found packages the
--   nonnegativity pair and sum-to-one equality needed by `Convex` two-point
--   membership calls; existing SOptLib iterate APIs assume an interval
--   coefficient instead of deriving it from `1 ≤ b`.
-- coverage search: LeanSearch query "if one is less than a real number then
--   inverse and one minus inverse are nonnegative and sum to one" returned
--   Holder-conjugate and inverse comparison facts, not this convex-weight
--   triple; project search for "convex_weights", "inv weights", and
--   "1 - _⁻¹" found local candidates and iterate feasibility lemmas but no
--   general scalar theorem.
-- minimal hypotheses: all already minimal; the proof needs only `1 ≤ b`, from
--   which `0 ≤ b`, `0 ≤ b⁻¹`, and `b⁻¹ ≤ 1` follow.

/-- The inverse of a real scale at least one gives two convex weights.

If `1 ≤ b`, then `1 - b⁻¹` and `b⁻¹` are nonnegative real coefficients whose
sum is one. This packages the scalar side condition used before applying
two-point convex-combination membership lemmas.

Layer: Glue | Gap: Level 0 (inverse-scale convex weights)
Proof: derive nonnegativity and the upper bound on `b⁻¹` from ordered-field
  inverse comparison facts, then close the affine-weight sum by ring arithmetic.
Source: Mathlib ordered-field inverse comparison and real polynomial
  normalization APIs
Used in: accelerated stochastic primal-dual midpoint and running-average
  feasibility from inverse acceleration-scale coefficients
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec/steps/0/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem inv_convex_weights_of_one_le (b : ℝ) (hb : 1 ≤ b) :
    0 ≤ 1 - b⁻¹ ∧
      0 ≤ b⁻¹ ∧
      1 - b⁻¹ + b⁻¹ = 1 := by
  have hb_nonneg : 0 ≤ b := le_trans zero_le_one hb
  have hinv_nonneg : 0 ≤ b⁻¹ := inv_nonneg.mpr hb_nonneg
  have hinv_le_one : b⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hb
  exact ⟨sub_nonneg.mpr hinv_le_one, hinv_nonneg, by ring⟩

-- Generalization plan (G0):
-- concept/name: `two_center_residual_nonneg_to_three_point_ineq` exposes the
--   scalar residual rearrangement behind a two-anchor three-point inequality;
--   orig was `lemma_3_5_of_bregman_residual`.
-- generality used: only ordered real scalar algebra is used; no carrier,
--   measure, convexity, smoothness, oracle, norm, or inner-product hypotheses
--   are needed once the residual inequality has been established.
-- portable call pattern: accelerated mirror-descent, accelerated primal-dual,
--   and mirror-prox proofs after a two-anchor Bregman residual is nonnegative;
--   the function values, Bregman values, and weights vary while the final
--   three-point inequality has the same scalar shape.
-- counterargument checked: this is a short arithmetic leaf, but it is not a
--   paper-local traceability wrapper; it packages a recurring residual-to-final
--   inequality normalization distinct from the existing summand-isolation
--   helpers `left_le_sub_sub_of_add_add_le` and
--   `mul_left_le_sub_sub_of_mul_add_add_le`.
-- coverage search: searched project/SOptLib for `residual_nonneg`,
--   `two_center_residual`, and `three_point`; LeanSearch for real residual
--   rearrangement returned unrelated mean-inequality and generic subtraction
--   lemmas. Existing Bregman three-point lemmas cover the analytic identity,
--   not this two-center scalar residual rearrangement.
-- minimal hypotheses: all hypotheses are already pointwise scalar assumptions;
--   no nonnegativity of weights or Bregman values is used.

/-- Nonnegativity of a two-center residual gives the corresponding three-point
inequality.

The variables represent two function values `ph`, `pu`, two pairs of directed
center terms, a common endpoint term, and arbitrary scalar weights.

Layer: Glue | Gap: Level 0 (two-center residual scalar rearrangement)
Proof: expand the residual inequality and normalize the ordered real-ring
  expression by linear arithmetic.
Source: Mathlib ordered real-ring arithmetic and linear arithmetic tactics
Used in: accelerated primal-dual and accelerated mirror-descent two-anchor
  Bregman residual conversion to a final three-point prox inequality
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/key_lemmas
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem two_center_residual_nonneg_to_three_point_ineq
    (pu ph bu1 bh1 bu2 bh2 buh mu1 mu2 : ℝ)
    (hres :
      0 ≤ pu - ph + mu1 * (bu1 - bh1 - buh) +
        mu2 * (bu2 - bh2 - buh)) :
    ph + mu1 * bh1 + mu2 * bh2 ≤
      pu + mu1 * bu1 + mu2 * bu2 - (mu1 + mu2) * buh := by
  linarith

-- Generalization plan (G0):
-- concept/name: half-scaled nonnegativity of a scalar parameter-coupling budget;
--   orig was param_coupling_half_nonneg.
-- generality used: pure real ordered-ring arithmetic; no carrier space, measure,
--   convexity, smoothness, oracle, or iterate structure is used.
-- portable call pattern: accelerated primal-dual, mirror-prox, and primal-dual
--   splitting one-step estimates where a nonnegative parameter-coupling budget is
--   used after a one-half Young split; the scalar schedules and operator-norm
--   bound change while the conclusion shape stays the same.
-- counterargument checked: this is small, but not only paper traceability because
--   the same half-normalization is already embedded inside staged Young absorption
--   lemmas; it isolates the reusable scalar budget step without setup fields.
-- coverage search: searched `parameter coupling half coefficient nonnegative q eta
--   beta norm tau p`, `half nonnegative mul_nonneg one half real`, and SOptLib
--   catalog/source hits for `param_coupling`, `half_nonneg`, and `Young absorb`;
--   Mathlib has `mul_nonneg`, while SOptLib has downstream absorption lemmas but
--   no standalone theorem for this scalar half-normalization.
-- minimal hypotheses: one pointwise nonnegativity hypothesis on the unscaled
--   coupling budget; no positivity of denominators is needed because division is
--   over total real inverses.

/-- A nonnegative scalar coupling budget remains nonnegative after halving all
three coefficient denominators.

This packages the arithmetic step that converts a parameter-coupling condition
into the half-coefficient form produced by a Young inequality split.

Layer: Glue | Gap: Level 0 (scalar parameter-coupling half-normalization)
Proof: multiply the supplied nonnegative budget by the nonnegative scalar
  `1 / 2`, then rewrite the result by real-ring arithmetic.
Source: Mathlib ordered real-ring arithmetic and scalar nonnegativity APIs
Used in: stochastic accelerated primal-dual Young square absorption from a
  parameter-coupling budget
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec/parameters
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem half_param_coupling_nonneg
    (q eta L beta A_norm tau p : ℝ)
    (hcoupling : 0 ≤ q / eta - L / beta - A_norm ^ 2 * tau / p) :
    0 ≤ q / (2 * eta) - L / (2 * beta) - A_norm ^ 2 * tau / (2 * p) := by
  have hhalf := mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) hcoupling
  convert hhalf using 1
  ring

-- Generalization plan (G0):
-- concept/name: `mul_inner_add_add_left` exposes a common scalar multiplier
--   applied to left-additivity of the inner product over a three-term sum; orig
--   was `real_inner_add_add_left_scaled`.
-- generality used: arbitrary `RCLike` scalar field, `SeminormedAddCommGroup`
--   carrier, and `InnerProductSpace`; no measure, convexity, smoothness, or
--   oracle hypotheses are involved.
-- portable call pattern: accelerated primal-dual, stochastic mirror descent,
--   and variance-reduced proofs that keep a stepsize or weight outside a
--   decomposed inner product before isolating descent/noise/coupling terms.
-- counterargument checked: it is a one-line consequence of Mathlib
--   `inner_add_left` and the staged `inner_add_add_left`, but the scaled
--   common-factor rewrite is a distinct goal shape used before ordered
--   term-isolation lemmas; it is not paper-local traceability.
-- coverage search: queried `mul inner add add left`,
--   `inner product additivity left argument multiplied by scalar`, and
--   `inner_add_add_left`; Mathlib hits were binary `inner_add_left` variants,
--   and SOptLib/Staging had only the unscaled three-term lemma.
-- minimal hypotheses: all hypotheses are inherited from Mathlib
--   `inner_add_left`; the original real-only `NormedAddCommGroup` assumption
--   was generalized to `RCLike` and `SeminormedAddCommGroup`.

/-- A common scalar multiplier preserves three-term additivity of the inner product
in the left argument.

This packages the rewrite from a scaled inner product of a decomposed vector to a
scaled sum of the three scalar inner products, without distributing the common
multiplier across the summands.

Layer: Glue | Gap: Level 0 (scaled three-term inner-product additivity)
Proof: rewrite the inner product twice with Mathlib's binary `inner_add_left`;
  the common left multiplier is preserved by congruence.
Source: Mathlib real and complex inner-product-space additivity APIs
Used in: accelerated primal-dual one-step prox-noise decomposition before
  scaled term isolation
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem mul_inner_add_add_left
    {𝕜 E : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (γ : 𝕜) (u v w d : E) :
    γ * ⟪u + v + w, d⟫_𝕜 =
      γ * (⟪u, d⟫_𝕜 + ⟪v, d⟫_𝕜 + ⟪w, d⟫_𝕜) := by
  rw [inner_add_left (u + v) w d, inner_add_left u v d]

-- Generalization plan (G0):
-- concept/name: scalar sum-of-squares budget obstruction; orig was
--   sigmaX_sq_rejects_extra_hatf_mismatch_budget.
-- generality used: real ordered-ring arithmetic only; no measure, filtration,
--   convexity, smoothness, oracle, Hilbert-space, or finite-dimensional
--   assumptions are used.
-- portable call pattern: stochastic accelerated primal-dual, mirror-prox, and
--   stochastic gradient proofs that compare an expanded componentwise variance
--   budget against a previously named combined root-sum-square noise scale; the
--   component constants and nonnegative residual budget change while the
--   contradiction shape stays fixed.
-- counterargument checked: this is close to caller-side arithmetic, but it
--   prevents an invalid budget collapse behind a reusable named scalar
--   obstruction; it is not a pure rename of one Mathlib lemma or paper-local
--   traceability.
-- coverage search: rg over SOptLib, Staging, and the catalog for
--   "two_sq combined_sq add_extra not_sq budget" found norm-square Young
--   bounds and unrelated nonpositive obstruction lemmas; LeanSearch for
--   "real numbers positive square nonnegative extra not less equal same square
--   sum" returned square-root/square nonnegativity facts and `add_sq_le`, with
--   no full budget-obstruction statement.
-- minimal hypotheses: one defining equality for the combined square, a
--   nonnegative extra budget, and positivity of the duplicated square
--   component.

/-- A positive duplicated square plus a nonnegative extra budget cannot fit
under the original two-square combined budget.

If `combined` is `a^2 + b^2`, then the expanded budget
`2*a^2 + 2*M + b^2` is strictly too large whenever `a > 0` and `M >= 0`.

Layer: Glue | Gap: Level 0 (sum-of-squares budget obstruction)
Proof: rewrite the combined budget to `a^2 + b^2`, derive positivity of
  `a^2`, and finish by ordered real arithmetic.
Source: Mathlib ordered-ring square positivity and `nlinarith`
Used in: stochastic accelerated primal-dual variance-budget audit preventing
  absorption of an additional gradient-mismatch budget into a combined
  root-sum-square primal-noise scale
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/assumptions/8/math
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
theorem not_two_sq_add_extra_le_combined_sq
    (a b M combined : ℝ)
    (hcombined : combined = a ^ 2 + b ^ 2)
    (hM : 0 ≤ M)
    (ha : 0 < a) :
    ¬ (2 * a ^ 2 + 2 * M + b ^ 2 ≤ combined) := by
  intro hcollapse
  rw [hcombined] at hcollapse
  have ha_sq_pos : 0 < a ^ 2 := sq_pos_of_pos ha
  nlinarith

-- Generalization plan (G0):
-- concept/name: closed natural interval predecessor reindexing; orig was sum_Icc_two_predecessor.
-- generality used: arbitrary AddCommMonoid-valued summands over natural indices; no measure,
--   convexity, smoothness, oracle, or finite-dimensional assumptions.
-- portable call pattern: stochastic accelerated primal-dual and mirror/prox proofs that shift
--   a one-step predecessor energy from indices i = 2..t to the window 1..t-1.
-- counterargument checked: this is a short finite-sum wrapper, but it is not paper-local and
--   packages a recurring off-by-one branch that otherwise obscures algorithmic energy sums.
-- coverage search: queried "Finset sum Icc pred predecessor if 2 <= i" and
--   "sum_Icc succ pred Finset"; SOptLib hits were telescopes or triangular upper bounds,
--   not this AddCommMonoid equality; LeanSearch timed out.
-- minimal hypotheses: all already minimal; the proof only needs zero, addition, and finite sums.

/-- Reindex a guarded predecessor sum over `1..t` as the unguarded sum over `1..t-1`.

The `i = 1` branch contributes zero, and every remaining index `i` contributes
the predecessor term `f (i - 1)`.

Layer: Glue | Gap: Level 0 (closed-interval predecessor reindexing)
Proof: induction on the right endpoint, splitting the final term with
  `Finset.sum_Icc_succ_top`; the small natural-number boundary cases are
  discharged by simplification and `omega`.
Source: Mathlib finite sums over natural closed intervals
Used in: stochastic accelerated primal-dual shifted Young-energy aggregation
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
theorem sum_Icc_if_two_le_pred_eq_sum_Icc_pred {α : Type*} [AddCommMonoid α]
    (f : ℕ → α) (t : ℕ) :
    Finset.sum (Finset.Icc 1 t) (fun i => if 2 ≤ i then f (i - 1) else 0) =
      Finset.sum (Finset.Icc 1 (t - 1)) f := by
  classical
  induction t with
  | zero =>
      simp
  | succ k ih =>
      cases k with
      | zero =>
          simp
      | succ k =>
          have htop :
              Finset.sum (Finset.Icc 1 (Nat.succ (Nat.succ k)))
                  (fun i => if 2 ≤ i then f (i - 1) else 0) =
                Finset.sum (Finset.Icc 1 (Nat.succ k))
                    (fun i => if 2 ≤ i then f (i - 1) else 0) +
                  f (Nat.succ k) := by
            have hsplit :=
              Finset.sum_Icc_succ_top
                (by omega : 1 ≤ Nat.succ (Nat.succ k))
                (fun i => if 2 ≤ i then f (i - 1) else 0)
            simpa using hsplit
          calc
            Finset.sum (Finset.Icc 1 (Nat.succ (Nat.succ k)))
                (fun i => if 2 ≤ i then f (i - 1) else 0) =
                Finset.sum (Finset.Icc 1 (Nat.succ k))
                    (fun i => if 2 ≤ i then f (i - 1) else 0) +
                  f (Nat.succ k) := htop
            _ = Finset.sum (Finset.Icc 1 (Nat.succ k - 1)) f +
                  f (Nat.succ k) := by
                rw [ih]
            _ = Finset.sum (Finset.Icc 1 (Nat.succ k)) f := by
                rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ Nat.succ k) f]
                congr 1
            _ = Finset.sum (Finset.Icc 1 (Nat.succ (Nat.succ k) - 1)) f := by
                congr 1

namespace Finset

-- Generalization plan (G0):
-- concept/name: one-based natural finite-sum reindexing from `range j` to `Icc 1 j`;
--   orig was local `hshift_sum`.
-- generality used: arbitrary AddCommMonoid-valued summands over natural indices; no measure,
--   convexity, smoothness, oracle, or finite-dimensional assumptions.
-- portable call pattern: stochastic mirror descent, accelerated primal-dual, and
--   variance-reduced mirror-descent summation steps that prove a zero-based bound and
--   then state it over the paper's positive-time output window.
-- counterargument checked: this is short finite-sum glue, but not paper-local; it packages
--   the recurring off-by-one bridge between Mathlib `range` sums and one-based algorithm
--   windows. Mathlib has half-open interval forms, but not this closed `Icc 1 j` wrapper.
-- coverage search: searched SOptLib catalog/source and `lean_search_symbols` for
--   "Finset sum range succ Icc one"; hits were closed-interval telescopes and predecessor
--   reindexing lemmas, not this pure range-to-Icc shift. LeanSearch found
--   `Finset.sum_Ico_eq_sum_range` and `Finset.sum_range_eq_add_Ico`, partial Mathlib
--   coverage over `Ico`, but no full duplicate of the closed one-based statement.
-- minimal hypotheses: all already minimal; the proof only needs zero, addition, and finite sums.

/-- Reindex a shifted range sum as a one-based closed-interval sum.

For any additive commutative monoid-valued sequence, summing `F (t + 1)` over
`t = 0, ..., j - 1` is the same as summing `F t` over `t = 1, ..., j`.

Layer: Glue | Gap: Level 0 (one-based finite-sum reindexing)
Proof: use `Finset.sum_bij` with the successor map from `range j` to
  `Icc 1 j`; injectivity and surjectivity are natural-number arithmetic.
Source: Mathlib finite sums over natural ranges and closed intervals
Used in: stochastic mirror descent and accelerated primal-dual positive-time
  summation windows after zero-based recursion bounds
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
theorem sum_range_succ_eq_sum_Icc_one {α : Type*} [AddCommMonoid α]
    (F : ℕ → α) (j : ℕ) :
    (∑ t ∈ range j, F (t + 1)) = ∑ t ∈ Icc 1 j, F t := by
  refine sum_bij (fun t _ => t + 1) ?_ ?_ ?_ ?_
  · intro t ht
    simp only [mem_range, mem_Icc] at ht ⊢
    omega
  · intro a ha b hb hab
    have hsucc : a + 1 = b + 1 := by simpa using hab
    omega
  · intro b hb
    refine ⟨b - 1, ?_, ?_⟩
    · simp only [mem_range]
      simp only [mem_Icc] at hb
      omega
    · simp only [mem_Icc] at hb
      exact Nat.sub_add_cancel hb.1
  · intro t ht
    rfl

end Finset

-- Generalization plan (G0):
-- concept/name: guarded two-lag closed-interval predecessor reindexing; orig was
--   generated_young_x_predecessor_sum_eq.
-- generality used: arbitrary AddCommMonoid-valued two-lag summands over natural
--   indices; no measure, convexity, smoothness, oracle, or finite-dimensional
--   assumptions.
-- portable call pattern: accelerated primal-dual, mirror-prox, and momentum proofs
--   that shift a lagged square or energy term from the active `i = 2..t` window to
--   the predecessor window `1..t-1`.
-- counterargument checked: near-duplicate risk is real; the staged
--   `sum_Icc_if_two_le_pred_eq_sum_Icc_pred` covers the unguarded one-argument
--   shift. This variant adds the ubiquitous outer positivity guard and two-lag
--   `(i - 1, i - 2)` normalization needed by generated predecessor-energy terms.
-- coverage search: searched SOptLib catalog/source for "predecessor", "sum_Icc",
--   "if 2 <= i", and "triangular"; hits were `sum_Icc_sub_succ`,
--   `active_triangular_predecessor_sum_le_batch_mul_global_sum`, and staged
--   `sum_Icc_if_two_le_pred_eq_sum_Icc_pred`. LeanSearch returned Mathlib
--   interval-sum shift lemmas but no full guarded two-lag equality.
-- minimal hypotheses: all already minimal; the proof uses only zero, addition,
--   finite sums, and natural predecessor arithmetic.

/-- Reindex a guarded two-lag predecessor sum over `1..t` as a predecessor window.

The outer `1 <= i` guard is redundant on `Icc 1 t`; the `i = 1` branch
contributes zero, and every later index contributes the two-lag term
`f (i - 1) (i - 2)`, which reindexes to `f i (i - 1)` over `1..t-1`.

Layer: Glue | Gap: Level 0 (guarded two-lag predecessor reindexing)
Proof: first remove the redundant lower-bound guard and normalize the two
  predecessor indices by finite-sum congruence; then apply the one-argument
  closed-interval predecessor reindexing lemma.
Source: Mathlib finite sums over natural closed intervals and natural-number
  predecessor arithmetic
Used in: stochastic accelerated primal-dual shifted Young-energy aggregation
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
theorem sum_young_x_predecessor_eq {α : Type*} [AddCommMonoid α]
    (f : ℕ → ℕ → α) (t : ℕ) :
    Finset.sum (Finset.Icc 1 t) (fun i =>
        if _hi : 1 ≤ i then
          if _h2 : 2 ≤ i then f (i - 1) (i - 2) else 0
        else 0) =
      Finset.sum (Finset.Icc 1 (t - 1)) (fun i => f i (i - 1)) := by
  classical
  let g : ℕ → α := fun i => f i (i - 1)
  have hguard :
      Finset.sum (Finset.Icc 1 t) (fun i =>
          if _hi : 1 ≤ i then
            if _h2 : 2 ≤ i then f (i - 1) (i - 2) else 0
          else 0) =
        Finset.sum (Finset.Icc 1 t) (fun i =>
          if 2 ≤ i then g (i - 1) else 0) := by
    refine Finset.sum_congr rfl ?_
    intro i hiIcc
    have hi : 1 ≤ i := (Finset.mem_Icc.mp hiIcc).1
    by_cases h2 : 2 ≤ i
    · have hidx : i - 1 - 1 = i - 2 := by omega
      simp [hi, h2, g, hidx]
    · simp [hi, h2]
  calc
    Finset.sum (Finset.Icc 1 t) (fun i =>
        if _hi : 1 ≤ i then
          if _h2 : 2 ≤ i then f (i - 1) (i - 2) else 0
        else 0) =
        Finset.sum (Finset.Icc 1 t) (fun i =>
          if 2 ≤ i then g (i - 1) else 0) := hguard
    _ = Finset.sum (Finset.Icc 1 (t - 1)) g :=
        sum_Icc_if_two_le_pred_eq_sum_Icc_pred g t
    _ = Finset.sum (Finset.Icc 1 (t - 1)) (fun i => f i (i - 1)) := by
        rfl

-- Generalization plan (G0):
-- concept/name: operator-norm Young absorption of a terminal linear-map coupling into a tail;
--   orig was terminal_coupling_young_tail_absorption.
-- generality used: two arbitrary real inner-product normed additive groups, one continuous
--   linear map, pointwise vectors, and real scalar coefficient/tail assumptions; no measure,
--   convexity, smoothness, or oracle structure is used.
-- portable call pattern: accelerated primal-dual and mirror-prox endpoint estimates where
--   a terminal bilinear coupling is retained after a Bregman telescope; the map, vectors,
--   step weights, square coefficient, and tail supplier change while the conclusion shape
--   stays the same.
-- counterargument checked: not merely paper traceability because it packages Cauchy-Schwarz,
--   scaled Young, coefficient coupling, and half-square-to-tail absorption; not a pure wrapper
--   around the local setup fields.
-- coverage search: searched `inner norm square Young linear map tail coupling`,
--   `Cauchy Schwarz Young inequality linear map inner product subtract square coefficient bound tail`,
--   and SOptLib catalog hits for Young/tail/Bregman; Mathlib has Cauchy-Schwarz and SOptLib has
--   scalar Young/noise absorption, but no full linear-map square-budget-to-tail absorption.
-- minimal hypotheses: pointwise positivity of `gamma`, `tau`, `p`, the bound `p ≤ 1`,
--   the scalar coefficient coupling, and the half-square tail lower bound.

/-- A linear-map inner product minus a coupled square coefficient is absorbed by a tail.

If the square coefficient dominates the Young coefficient
`‖A‖ ^ 2 * tau / (2 * p)`, and the tail dominates `1/2 * ‖dy‖ ^ 2`, then
the positive weighted coupling `gamma * ⟪A dx, dy⟫` minus the square penalty is
bounded by `gamma / tau` times the tail.

Layer: Glue | Gap: Level 1 (linear-map Young tail absorption)
Proof: bound the inner product by the operator norm and Cauchy-Schwarz, apply
  scaled scalar Young's inequality, spend the coefficient-coupling budget on
  the `dx` square, and use the half-square tail lower bound with `p ≤ 1`.
Source: Mathlib real inner-product Cauchy-Schwarz, continuous linear map operator
  norm bounds, and ordered-field Young inequality algebra
Used in: stochastic accelerated primal-dual endpoint Bregman-tail absorption
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem linearMap_inner_sub_squareCoeff_le_tail_of_coupling
    {EX EY : Type*} [NormedAddCommGroup EX] [InnerProductSpace ℝ EX]
    [NormedAddCommGroup EY] [InnerProductSpace ℝ EY]
    (A : EX →L[ℝ] EY) (dx : EX) (dy : EY)
    (gamma tau p squareCoeff tailY : ℝ)
    (hgamma : 0 < gamma) (htau : 0 < tau) (hp_pos : 0 < p) (hp_le_one : p ≤ 1)
    (hcoupling : 0 ≤ squareCoeff - ‖A‖ ^ 2 * tau / (2 * p))
    (htail : (1 / 2 : ℝ) * ‖dy‖ ^ 2 ≤ tailY) :
    gamma * ⟪A dx, dy⟫_ℝ - gamma * squareCoeff * ‖dx‖ ^ 2 ≤
      gamma / tau * tailY := by
  have hinner :
      ⟪A dx, dy⟫_ℝ ≤ ‖A‖ * ‖dx‖ * ‖dy‖ := by
    have h₁ : ⟪A dx, dy⟫_ℝ ≤ ‖A dx‖ * ‖dy‖ :=
      real_inner_le_norm (A dx) dy
    have h₂ : ‖A dx‖ * ‖dy‖ ≤ (‖A‖ * ‖dx‖) * ‖dy‖ :=
      mul_le_mul_of_nonneg_right (A.le_opNorm dx) (norm_nonneg dy)
    nlinarith
  have hscaled :
      gamma * ⟪A dx, dy⟫_ℝ ≤
        gamma * ((‖A‖ * ‖dx‖) * ‖dy‖) := by
    exact mul_le_mul_of_nonneg_left (by simpa [mul_assoc] using hinner) (le_of_lt hgamma)
  let L : ℝ := p / (gamma * tau)
  have hL : 0 < L := by
    exact div_pos hp_pos (mul_pos hgamma htau)
  have hyoung :=
    mul_mul_le_inv_two_mul_add_half_mul_sq
      (R := ℝ) ‖dy‖ (‖A‖ * ‖dx‖) gamma L hL
  have hyoung_norm :
      gamma * ((‖A‖ * ‖dx‖) * ‖dy‖) ≤
        gamma * tau / (2 * p) * (‖A‖ ^ 2 * ‖dx‖ ^ 2) +
          p * gamma / (2 * tau) * ‖dy‖ ^ 2 := by
    have hraw := hyoung
    dsimp [L] at hraw
    convert hraw using 1
    · ring
    · field_simp [ne_of_gt hp_pos, ne_of_gt hgamma, ne_of_gt htau]
  have hbudget :
      0 ≤ gamma * ‖dx‖ ^ 2 *
        (squareCoeff - ‖A‖ ^ 2 * tau / (2 * p)) := by
    exact mul_nonneg (mul_nonneg (le_of_lt hgamma) (sq_nonneg ‖dx‖)) hcoupling
  have hyoung_norm' :
      gamma * ((‖A‖ * ‖dx‖) * ‖dy‖) ≤
        gamma * ‖dx‖ ^ 2 * (‖A‖ ^ 2 * tau / (2 * p)) +
          p * gamma / (2 * tau) * ‖dy‖ ^ 2 := by
    have hfirst :
        gamma * tau / (2 * p) * (‖A‖ ^ 2 * ‖dx‖ ^ 2) =
          gamma * ‖dx‖ ^ 2 * (‖A‖ ^ 2 * tau / (2 * p)) := by
      ring
    simpa [hfirst] using hyoung_norm
  have hto_sq :
      gamma * ⟪A dx, dy⟫_ℝ - gamma * squareCoeff * ‖dx‖ ^ 2 ≤
        p * gamma / (2 * tau) * ‖dy‖ ^ 2 := by
    nlinarith [hscaled, hyoung_norm', hbudget]
  have htail_nonneg : 0 ≤ tailY := by
    nlinarith [htail, sq_nonneg ‖dy‖]
  have hcoeff_nonneg : 0 ≤ p * gamma / tau := by
    positivity
  have hcoeff_le :
      p * gamma / tau ≤ gamma / tau := by
    have hbase :
        p * (gamma / tau) ≤ 1 * (gamma / tau) :=
      mul_le_mul_of_nonneg_right hp_le_one
        (div_nonneg (le_of_lt hgamma) (le_of_lt htau))
    simpa [mul_div_assoc] using hbase
  have htail_coeff :
      p * gamma / tau * tailY ≤ gamma / tau * tailY :=
    mul_le_mul_of_nonneg_right hcoeff_le htail_nonneg
  have hsq_to_tail :
      p * gamma / (2 * tau) * ‖dy‖ ^ 2 ≤ gamma / tau * tailY := by
    calc
      p * gamma / (2 * tau) * ‖dy‖ ^ 2 =
          (p * gamma / tau) * ((1 / 2 : ℝ) * ‖dy‖ ^ 2) := by
            field_simp [ne_of_gt htau]
      _ ≤ (p * gamma / tau) * tailY :=
            mul_le_mul_of_nonneg_left htail hcoeff_nonneg
      _ ≤ gamma / tau * tailY := htail_coeff
  exact le_trans hto_sq hsq_to_tail

-- Generalization plan (G0):
-- concept/name: Abel-style weighted forward-difference telescope with retained tail;
--   orig was weighted_forward_diff_sum_le_last_mul_bound_sub_tail.
-- generality used: real scalar sequences over natural-time closed intervals; no measure,
--   convexity, smoothness, or oracle assumptions are used.
-- portable call pattern: accelerated stochastic-gradient, accelerated primal-dual, and
--   mirror-prox proofs that sum increasing weights times bounded nonnegative potential
--   drops while retaining the terminal potential for a later absorption step.
-- counterargument checked: not paper-local traceability, because the statement is a
--   paper-free finite-sum Abel telescope; not a one-line wrapper around an existing
--   SOptLib theorem, since bridged-coefficient telescopes have different summands and
--   hypotheses.
-- coverage search: catalog and lean_search_symbols for "weighted scalar telescope
--   forward difference last mul bound sub tail sum Icc" found sum_Icc_sub_succ,
--   sum_weighted_sub_mul_le_first_sub_tail, and
--   finite_window_weighted_recurrence_telescope_with_tail_sums; these are partial hits,
--   not full coverage. LeanSearch for Abel finite weighted forward differences timed out.
-- minimal hypotheses: pointwise monotonicity, nonnegativity, and upper-bound hypotheses
--   only on the finite indices used by the proof.

/-- A closed-interval Abel telescope for increasing weights and bounded potentials.

If `a` is nonnegative and increasing on `[1, t]`, and `v` is nonnegative through
the terminal index and bounded above by `D` on `[1, t]`, then the weighted sum of
forward drops is bounded by the last weight times the bound, with the final
weighted potential retained as a negative tail.

Layer: Glue | Gap: Level 1 (weighted forward-difference Abel telescope with tail)
Proof: induction on the right endpoint of the closed interval; split the final
  summand with `Finset.sum_Icc_succ_top`, use monotonicity of the weight to make
  the exposed Abel coefficient nonnegative, and close by ordered real arithmetic.
Source: Mathlib finite sums over natural intervals and ordered real arithmetic
Used in: accelerated primal-dual and accelerated-gradient Bregman-potential
  telescopes where the terminal weighted Bregman term is absorbed later
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
theorem sum_Icc_weighted_forward_diff_le_last_mul_bound_sub_tail
    (a v : ℕ → ℝ) (D : ℝ) (t : ℕ) (ht : 1 ≤ t)
    (ha_mono : ∀ i, 2 ≤ i → i ≤ t → a (i - 1) ≤ a i)
    (ha_nonneg : ∀ i, 1 ≤ i → i ≤ t → 0 ≤ a i)
    (hv_nonneg : ∀ i, 1 ≤ i → i ≤ t + 1 → 0 ≤ v i)
    (hv_bound : ∀ i, 1 ≤ i → i ≤ t → v i ≤ D) :
    Finset.sum (Finset.Icc 1 t) (fun i => a i * (v i - v (i + 1))) ≤
      a t * D - a t * v (t + 1) := by
  classical
  induction t, ht using Nat.le_induction with
  | base =>
      have ha1 : 0 ≤ a 1 := ha_nonneg 1 le_rfl le_rfl
      have hv1 : v 1 ≤ D := hv_bound 1 le_rfl le_rfl
      have hv2 : 0 ≤ v 2 := hv_nonneg 2 (by omega) (by omega)
      simp
      nlinarith
  | succ n hn ih =>
      have hsum_succ :
          Finset.sum (Finset.Icc 1 (n + 1))
              (fun i => a i * (v i - v (i + 1))) =
            Finset.sum (Finset.Icc 1 n)
              (fun i => a i * (v i - v (i + 1))) +
              a (n + 1) * (v (n + 1) - v (n + 2)) := by
        rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
      have hih :
          Finset.sum (Finset.Icc 1 n) (fun i => a i * (v i - v (i + 1))) ≤
            a n * D - a n * v (n + 1) := by
        exact ih
          (fun i hi2 hit =>
            ha_mono i hi2 (by omega))
          (fun i hi1 hit =>
            ha_nonneg i hi1 (by omega))
          (fun i hi1 hit =>
            hv_nonneg i hi1 (by omega))
          (fun i hi1 hit =>
            hv_bound i hi1 (by omega))
      have hmono : a n ≤ a (n + 1) := ha_mono (n + 1) (by omega) le_rfl
      have hv_bound' : v (n + 1) ≤ D := hv_bound (n + 1) (by omega) le_rfl
      have hv_tail : 0 ≤ v (n + 1) := hv_nonneg (n + 1) (by omega) (by omega)
      rw [hsum_succ]
      nlinarith

-- Generalization plan (G0):
-- concept/name: Abel-style weighted forward-difference telescope with the terminal
--   nonnegative tail discarded; orig was weighted_forward_diff_sum_le_last_mul_bound.
-- generality used: ordered-commutative-ring scalar sequences over natural-time closed
--   intervals; no measure, convexity, smoothness, oracle, or finite-dimensional
--   assumptions are used.
-- portable call pattern: accelerated stochastic-gradient, accelerated primal-dual, and
--   mirror-prox proofs that sum increasing weights times bounded nonnegative potential
--   drops and need a clean last-weight-times-diameter boundary term.
-- counterargument checked: not paper-local traceability, because this is a paper-free
--   finite-sum Abel telescope; not a pure duplicate of the retained-tail companion,
--   because callers use the weaker terminal-bound form after proving endpoint
--   nonnegativity rather than carrying the terminal potential into later absorption.
-- coverage search: rg and lean_search_symbols for "weighted forward diff last mul
--   bound", "sum Icc weighted forward difference", and "Abel telescope" found
--   sum_Icc_sub_succ and the staged retained-tail companion; these are partial or
--   stronger-with-extra-tail hits, not this terminal-bound statement. LeanSearch for
--   weighted finite forward differences timed out.
-- minimal hypotheses: pointwise monotonicity on the finite window, initial and final
--   weight nonnegativity, terminal potential nonnegativity, and finite-window upper
--   bounds; no global sequence nonnegativity is needed.

/-- A closed-interval Abel telescope for increasing weights and bounded potentials.

If `a` is increasing on `[1, t]`, its initial and terminal weights are
nonnegative, `v (t + 1)` is nonnegative, and `v` is bounded above by `D` on
`[1, t]`, then the weighted sum of forward drops is bounded by the last weight
times `D`.

Layer: Glue | Gap: Level 1 (weighted forward-difference Abel telescope)
Proof: apply the retained-tail Abel telescope and discard the nonpositive
  terminal contribution using endpoint nonnegativity of the weight and
  potential.
Source: Mathlib finite sums over natural intervals and ordered real arithmetic
Used in: accelerated primal-dual and accelerated-gradient Bregman-potential
  telescopes producing a last-weight-times-diameter boundary term
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
theorem sum_Icc_weighted_forward_diff_le_last_mul_bound
    (a v : ℕ → ℝ) (D : ℝ) (t : ℕ) (ht : 1 ≤ t)
    (ha_mono : ∀ i, 2 ≤ i → i ≤ t → a (i - 1) ≤ a i)
    (ha_nonneg : ∀ i, 1 ≤ i → i ≤ t → 0 ≤ a i)
    (ha_t_nonneg : 0 ≤ a t)
    (hv_nonneg : ∀ i, 1 ≤ i → i ≤ t + 1 → 0 ≤ v i)
    (hv_tail_nonneg : 0 ≤ v (t + 1))
    (hv_bound : ∀ i, 1 ≤ i → i ≤ t → v i ≤ D) :
    Finset.sum (Finset.Icc 1 t) (fun i => a i * (v i - v (i + 1))) ≤
      a t * D := by
  have htail :=
    sum_Icc_weighted_forward_diff_le_last_mul_bound_sub_tail
      a v D t ht ha_mono ha_nonneg hv_nonneg hv_bound
  have htail_nonneg : 0 ≤ a t * v (t + 1) :=
    mul_nonneg ha_t_nonneg hv_tail_nonneg
  nlinarith

/-- Combine four finite-window absorption components into one residual bound.

If the negated lag-cross sum is controlled by two Young budgets, the x- and
y-square budgets are separately absorbed, and the noise term is just the
negative of a residual summand, then the full lag/x/y/noise remainder is bounded
by the retained terminal contribution plus the collected residual sum. -/
theorem finite_window_four_term_absorption_bridge
    {ι : Type*} (s : Finset ι)
    (lagCross youngX youngY xSq ySq noise lambdaX lambdaY lambdaNoise lambda :
      ι → ℝ)
    (terminal : ℝ)
    (hlag :
      -Finset.sum s lagCross ≤ Finset.sum s youngX + Finset.sum s youngY)
    (hx :
      Finset.sum s youngX - Finset.sum s xSq ≤
        terminal + Finset.sum s lambdaX)
    (hy :
      Finset.sum s youngY - Finset.sum s ySq ≤ Finset.sum s lambdaY)
    (hnoise : -Finset.sum s noise = Finset.sum s lambdaNoise)
    (hlambda :
      Finset.sum s lambdaX + Finset.sum s lambdaY +
          Finset.sum s lambdaNoise =
        Finset.sum s lambda) :
    -Finset.sum s lagCross - Finset.sum s xSq - Finset.sum s ySq -
        Finset.sum s noise ≤
      terminal + Finset.sum s lambda := by
  calc
    -Finset.sum s lagCross - Finset.sum s xSq - Finset.sum s ySq -
        Finset.sum s noise
        ≤ (Finset.sum s youngX + Finset.sum s youngY) -
            Finset.sum s xSq - Finset.sum s ySq - Finset.sum s noise := by
          nlinarith
    _ = (Finset.sum s youngX - Finset.sum s xSq) +
          (Finset.sum s youngY - Finset.sum s ySq) -
          Finset.sum s noise := by
          ring
    _ ≤ (terminal + Finset.sum s lambdaX) +
          Finset.sum s lambdaY + Finset.sum s lambdaNoise := by
          nlinarith
    _ = terminal + Finset.sum s lambda := by
          rw [← hlambda]
          ring

/-- Sum a predecessor-window Young absorption and split off the terminal square.

If `young i - square i` is absorbed by `absorbed i` on the predecessor window
`1..t-1`, and the omitted top penalty `-square t` decomposes as a retained
terminal contribution plus `absorbed t`, then the full `1..t` square sum is
bounded by the terminal contribution and the full absorbed sum. -/
theorem finite_window_young_absorption_with_terminal_split
    (young square absorbed : ℕ → ℝ) (terminal : ℝ)
    (t : ℕ) (ht : 1 ≤ t)
    (hpoint :
      ∀ i : ℕ, 1 ≤ i → i ≤ t - 1 → young i - square i ≤ absorbed i)
    (hterminal : -square t = terminal + absorbed t) :
    Finset.sum (Finset.Icc 1 (t - 1)) young -
        Finset.sum (Finset.Icc 1 t) square ≤
      terminal + Finset.sum (Finset.Icc 1 t) absorbed := by
  classical
  cases t with
  | zero =>
      omega
  | succ k =>
      have hsum_point :
          Finset.sum (Finset.Icc 1 k) (fun i => young i - square i) ≤
            Finset.sum (Finset.Icc 1 k) absorbed := by
        refine Finset.sum_le_sum ?_
        intro i hiIcc
        exact hpoint i (Finset.mem_Icc.mp hiIcc).1 (by
          simpa using (Finset.mem_Icc.mp hiIcc).2)
      have hsum_point' :
          Finset.sum (Finset.Icc 1 k) young -
              Finset.sum (Finset.Icc 1 k) square ≤
            Finset.sum (Finset.Icc 1 k) absorbed := by
        simpa [Finset.sum_sub_distrib] using hsum_point
      have hsquare_top :
          Finset.sum (Finset.Icc 1 (Nat.succ k)) square =
            Finset.sum (Finset.Icc 1 k) square + square (Nat.succ k) := by
        simpa using
          (Finset.sum_Icc_succ_top (by omega : 1 ≤ Nat.succ k) square)
      have habsorbed_top :
          Finset.sum (Finset.Icc 1 (Nat.succ k)) absorbed =
            Finset.sum (Finset.Icc 1 k) absorbed + absorbed (Nat.succ k) := by
        simpa using
          (Finset.sum_Icc_succ_top (by omega : 1 ≤ Nat.succ k) absorbed)
      calc
        Finset.sum (Finset.Icc 1 (Nat.succ k - 1)) young -
            Finset.sum (Finset.Icc 1 (Nat.succ k)) square =
          Finset.sum (Finset.Icc 1 k) young -
            (Finset.sum (Finset.Icc 1 k) square + square (Nat.succ k)) := by
            rw [hsquare_top]
            simp
        _ =
          (Finset.sum (Finset.Icc 1 k) young -
              Finset.sum (Finset.Icc 1 k) square) -
            square (Nat.succ k) := by
            ring
        _ ≤ Finset.sum (Finset.Icc 1 k) absorbed - square (Nat.succ k) := by
            nlinarith
        _ = Finset.sum (Finset.Icc 1 k) absorbed +
            (terminal + absorbed (Nat.succ k)) := by
            rw [← hterminal]
            ring
        _ = terminal + Finset.sum (Finset.Icc 1 (Nat.succ k)) absorbed := by
            rw [habsorbed_top]
            ring

namespace SOptLib

/-- A positive-time guarded pointwise inequality sums over `Finset.Icc 1 t`. -/
theorem sum_Icc_guarded_le_guarded_of_le_on_Icc
    {α : Type*} [AddCommMonoid α] [PartialOrder α] [AddLeftMono α]
    {left right : (i : ℕ) → 1 ≤ i → α} (t : ℕ)
    (hstep : ∀ i, ∀ hi : 1 ≤ i, i ∈ Finset.Icc 1 t → left i hi ≤ right i hi) :
    Finset.sum (Finset.Icc 1 t) (fun i =>
        if hi : 1 ≤ i then left i hi else 0) ≤
      Finset.sum (Finset.Icc 1 t) (fun i =>
        if hi : 1 ≤ i then right i hi else 0) := by
  classical
  refine Finset.sum_le_sum ?_
  intro i hiIcc
  have hi : 1 ≤ i := (Finset.mem_Icc.mp hiIcc).1
  simpa [hi] using hstep i hi hiIcc

end SOptLib
