import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
-- SOptLib/Glue/Calculus.lean
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Order.Basic


open Topology
open scoped BigOperators InnerProductSpace

/-- A right derivative at the left endpoint of an interval is nonnegative when the
endpoint is a minimum on that interval.

Layer: Glue | Gap: Level 1 (one-sided first-order condition on a compact interval)
Proof: restrict the derivative to `(a, b]`, identify that neighborhood with the
  right-neighborhood of `a`, and pass the nonnegative difference quotients to the
  limit.
Source: Mathlib one-dimensional derivative and order-topology APIs
Used in: stochastic mirror descent constrained first-order condition
Book citation: book/PAPER/ALG.json#/stochastic_mirror_descent
Origin algorithm: Lan stochastic mirror descent -/
theorem hasDerivWithinAt_nonneg_of_isMinOn_Icc_left
    {φ : ℝ → ℝ} {D a b : ℝ}
    (hab : a < b)
    (hderiv : HasDerivWithinAt φ D (Set.Icc a b) a)
    (hmin : ∀ t ∈ Set.Icc a b, φ a ≤ φ t) :
    0 ≤ D := by
  have hderivIoc : HasDerivWithinAt φ D (Set.Ioc a b) a :=
    hderiv.mono Set.Ioc_subset_Icc_self
  have htendIoc :
      Filter.Tendsto (slope φ a) (𝓝[Set.Ioc a b] a) (𝓝 D) := by
    exact (hasDerivWithinAt_iff_tendsto_slope' (by simp)).mp hderivIoc
  have htend : Filter.Tendsto (slope φ a) (𝓝[>] a) (𝓝 D) := by
    simpa [nhdsWithin_Ioc_eq_nhdsGT hab] using htendIoc
  haveI : Filter.NeBot (𝓝[>] a) := nhdsGT_neBot a
  apply ge_of_tendsto htend
  filter_upwards [Ioc_mem_nhdsGT hab] with t ht
  have hdiff : 0 ≤ φ t - φ a :=
    sub_nonneg.mpr (hmin t ⟨ht.1.le, ht.2⟩)
  have hden : 0 ≤ t - a := sub_nonneg.mpr ht.1.le
  have hslope : 0 ≤ (φ t - φ a) / (t - a) := div_nonneg hdiff hden
  simpa [slope_def_field] using hslope

/-- A right derivative at the left endpoint of `[0, 1]` is nonnegative when the
endpoint is a minimum on that interval.

Layer: Glue | Gap: Level 0 (right endpoint derivative sign from interval minimum)
Proof: apply Mathlib's one-dimensional endpoint first-order condition for
  `HasDerivWithinAt` on `Icc`, with `0 < 1` discharged by arithmetic.
Source: Mathlib interval calculus and within-derivative APIs
Used in: stochastic mirror descent constrained segment first-order condition
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic mirror descent -/
theorem right_derivative_nonneg_of_min_on_Icc
    {φ : ℝ → ℝ} {D : ℝ}
    (hderiv : HasDerivWithinAt φ D (Set.Icc (0 : ℝ) 1) 0)
    (hmin : ∀ t ∈ Set.Icc (0 : ℝ) 1, φ 0 ≤ φ t) :
    0 ≤ D := by
  exact hasDerivWithinAt_nonneg_of_isMinOn_Icc_left (by norm_num) hderiv hmin


/-- First-order condition for a constrained minimizer on a convex set.

If `z` minimizes `Φ` on a convex feasible set `T` and `Φ` has within-derivative
`F'` at `z` along `T`, then every feasible direction `y - z` has nonnegative
directional derivative.

Layer: Glue | Gap: Level 1 (constrained first-order condition from within derivative)
Proof: restrict `Φ` to the segment from `z` to `y`, apply the one-dimensional
  right-endpoint derivative condition on `[0, 1]`, and identify the derivative
  by the chain rule.
Source: Mathlib convex segments and within-derivative APIs
Used in: stochastic mirror descent constrained first-order condition chart
Book citation: book/PAPER/ALG.json#/stochastic_mirror_descent
Origin algorithm: Lan stochastic mirror descent -/
theorem Convex.first_order_condition_of_isMinOn_hasFDerivWithinAt
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {T : Set H} {Φ : H → ℝ} {z y : H} {F' : H →L[ℝ] ℝ}
    (hTconv : Convex ℝ T) (hz : z ∈ T) (hy : y ∈ T)
    (hmin : ∀ u ∈ T, Φ z ≤ Φ u)
    (hderiv : HasFDerivWithinAt Φ F' T z) :
    0 ≤ F' (y - z) := by
  let line : ℝ → H := fun t => z + t • (y - z)
  let φ : ℝ → ℝ := fun t => Φ (line t)
  have hmaps : Set.MapsTo line (Set.Icc (0 : ℝ) 1) T := by
    intro t ht
    have hmem : AffineMap.lineMap z y t ∈ T := hTconv.lineMap_mem hz hy ht
    have hline_eq : line t = AffineMap.lineMap z y t := by
      simp [line, AffineMap.lineMap_apply_module', add_comm]
    rw [hline_eq]
    exact hmem
  have hφmin : ∀ t ∈ Set.Icc (0 : ℝ) 1, φ 0 ≤ φ t := by
    intro t ht
    exact by simpa [φ, line] using hmin (line t) (hmaps ht)
  have hline_deriv : HasDerivWithinAt line (y - z) (Set.Icc (0 : ℝ) 1) 0 := by
    have hline_at : HasDerivAt (fun t : ℝ => z + t • (y - z)) (y - z) 0 := by
      simpa [line] using ((hasDerivAt_id (0 : ℝ)).smul_const (y - z)).const_add z
    simpa [line] using hline_at.hasDerivWithinAt
  have hφderiv : HasDerivWithinAt φ (F' (y - z)) (Set.Icc (0 : ℝ) 1) 0 := by
    have hcomp := hderiv.comp_hasDerivWithinAt_of_eq 0 hline_deriv hmaps (by simp [line])
    simpa [φ, line] using hcomp
  exact hasDerivWithinAt_nonneg_of_isMinOn_Icc_left (by norm_num) hφderiv hφmin

namespace DifferentiableOn

/-- Differentiability on the intrinsic interior follows from `C¹` regularity there.

Layer: Glue | Gap: Level 0 (C¹ regularity implies differentiability on intrinsic interior)
Proof: applies the Mathlib `ContDiffOn.differentiableOn_one` projection to the
  smoothness hypothesis on `intrinsicInterior ℝ X`.
Source: Mathlib smooth calculus APIs for `ContDiffOn` and differentiability on sets
Used in: stochastic mirror descent regularizer differentiability on the feasible
  set intrinsic interior
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem of_contDiffOn_one_intrinsicInterior
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (vInt : E → ℝ)
    (hvInt : ContDiffOn ℝ 1 vInt (intrinsicInterior ℝ X)) :
    DifferentiableOn ℝ vInt (intrinsicInterior ℝ X) := by
  exact hvInt.differentiableOn_one

end DifferentiableOn

open scoped InnerProductSpace

/-- First-order smoothness turns a carrier-chart gradient identity into a within derivative.

If `f` is `C¹` on `T` at `u` and its `fderivWithin` is identified with the
linear functional obtained from `grad` after composing with the carrier chart
linear map `L'`, then `f` has that prescribed within derivative. This is the
`gradientWithin` bridge used when `carrierGradientFrom` represents the carrier
chart function's within derivative.

Layer: Layer0 | Gap: Level 0 (within-derivative gradient identification)
Proof: `ContDiffOn.differentiableOn_one` gives differentiability within `T`,
  `DifferentiableWithinAt.hasFDerivWithinAt` supplies the canonical derivative,
  and the claimed derivative follows by rewriting with the gradient identity.
Source: Mathlib calculus `ContDiffOn`, `DifferentiableWithinAt`, and
  `fderivWithin` APIs
Used in: stochastic mirror descent carrier-chart gradientWithin derivative bridge
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem hasFDerivWithinAt_of_contDiffOn_gradientWithin_comp
    {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : Set H) (f : H → ℝ) (L' : H →L[ℝ] E) (u : H) (grad : E)
    (hcontDiff : ContDiffOn ℝ 1 f T) (hu : u ∈ T)
    (hgrad : fderivWithin ℝ f T u = ((innerSL ℝ) grad).comp L') :
    HasFDerivWithinAt f (((innerSL ℝ) grad).comp L') T u := by
  have hfdiff : DifferentiableWithinAt ℝ f T u := hcontDiff.differentiableOn_one u hu
  have hbase : HasFDerivWithinAt f (fderivWithin ℝ f T u) T u := hfdiff.hasFDerivWithinAt
  simpa [hgrad] using hbase

/-- A scalar function whose within-derivative is bounded by an affine function on
`[0, 1]` is bounded above by the corresponding integral estimate.

Layer: Glue | Gap: Level 1 (one-dimensional derivative bound integration)
Proof: subtract the quadratic affine antiderivative from the function, prove
  monotonicity on `[0, 1]` from nonnegative within-derivatives, and evaluate at
  the endpoints.
Source: Mathlib one-dimensional within-derivative monotonicity APIs on intervals
Used in: stochastic mirror descent smooth objective upper bound along a unit segment
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic mirror descent -/
theorem le_value_add_of_hasDerivWithinAt_le_affine_on_Icc
    (F phi : ℝ → ℝ) (A B : ℝ)
    (hderiv : ∀ (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1),
      HasDerivWithinAt F (phi t) (Set.Icc (0 : ℝ) 1) t)
    (hbound : ∀ (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1),
      phi t ≤ A + B * t) :
    F 1 ≤ F 0 + A + B / 2 := by
  let I : Set ℝ := Set.Icc (0 : ℝ) 1
  let q : ℝ → ℝ := fun t => F 0 + A * t + (B / 2) * t ^ 2 - F t
  have hq_deriv_Icc : ∀ (t : ℝ), t ∈ I →
      HasDerivWithinAt q (A + B * t - phi t) I t := by
    intro t ht
    have h0 : HasDerivWithinAt (fun _ : ℝ => F 0) 0 I t := by
      simpa using (hasDerivWithinAt_const (c := F 0) (s := I) (x := t))
    have hA : HasDerivWithinAt (fun u : ℝ => A * u) A I t := by
      simpa using ((hasDerivWithinAt_id t I).const_mul A)
    have hB : HasDerivWithinAt (fun u : ℝ => (B / 2) * u ^ 2) (B * t) I t := by
      have hp : HasDerivWithinAt (fun u : ℝ => u ^ 2) (2 * t ^ (2 - 1)) I t := by
        simpa using (hasDerivWithinAt_pow (2 : ℕ) (x := t) (s := I))
      have h := hp.const_mul (B / 2)
      convert h using 1 <;> ring
    have hsum := (h0.add hA).add hB
    have hq := hsum.sub (hderiv t ht)
    convert hq using 1 <;> ring
  have hq_cont : ContinuousOn q I := by
    intro t ht
    exact (hq_deriv_Icc t ht).continuousWithinAt
  have hq_deriv_int : ∀ (t : ℝ), t ∈ interior I →
      HasDerivWithinAt q (A + B * t - phi t) (interior I) t := by
    intro t ht
    exact (hq_deriv_Icc t (interior_subset ht)).mono interior_subset
  have hq_nonneg : ∀ (t : ℝ), t ∈ interior I → 0 ≤ A + B * t - phi t := by
    intro t ht
    have hb := hbound t (interior_subset ht)
    linarith
  have hmono : MonotoneOn q I :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0 : ℝ) 1)
      hq_cont hq_deriv_int hq_nonneg
  have h01 : q 0 ≤ q 1 :=
    hmono (by norm_num [I]) (by norm_num [I]) (by norm_num)
  dsimp [q] at h01
  norm_num at h01
  linarith

/-- Carrier form of the standard `L`-smooth quadratic upper bound on a convex set.

For a function represented on a carrier subtype by an ambient `C¹` function, if
the selected carrier gradient agrees with the within derivative and is
`L`-Lipschitz along feasible carrier points, then the usual descent lemma holds
between any two feasible points.

Layer: Glue | Gap: Level 2 (carrier smoothness quadratic upper bound)
Proof: restrict the ambient function to the feasible segment, identify the
  one-dimensional derivative by the within-derivative chain rule, bound the
  derivative error by the carrier gradient Lipschitz hypothesis and
  Cauchy-Schwarz, then integrate the affine derivative bound on `[0, 1]`.
Source: Mathlib convex segments, within-derivative chain rule, and Hilbert-space
  Cauchy-Schwarz APIs
Used in: nonconvex stochastic mirror descent smooth objective decrease on the
  feasible carrier before the prox descent algebra
Book citation: book/FOML/StochasticZerothOrderComposite.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic gradient free mirror descent -/
theorem Convex.carrier_smooth_quadratic_upper_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X : Set E) (f : {x : E // x ∈ X} → ℝ) (F : E → ℝ)
    (grad : {x : E // x ∈ X} → E) (L : ℝ)
    (hX : Convex ℝ X)
    (hF_eval : ∀ (z : E) (hz : z ∈ X), F z = f ⟨z, hz⟩)
    (hF_contDiff : ContDiffOn ℝ 1 F X)
    (hgrad :
      ∀ (z : {x : E // x ∈ X}) (d : E),
        (fderivWithin ℝ F X z.1) d = ⟪grad z, d⟫_ℝ)
    (hgrad_lipschitz :
      ∀ x y : {x : E // x ∈ X},
        ‖grad y - grad x‖ ≤ L * ‖y.1 - x.1‖)
    (x y : {x : E // x ∈ X}) :
    f y ≤ f x + ⟪grad x, y.1 - x.1⟫_ℝ +
      (L / 2) * ‖y.1 - x.1‖ ^ 2 := by
  let d : E := y.1 - x.1
  let s : Set ℝ := Set.Icc (0 : ℝ) 1
  let line : ℝ → E := fun t => AffineMap.lineMap x.1 y.1 t
  let Fseg : ℝ → ℝ := fun t => F (line t)
  have hF0 : Fseg 0 = f x := by
    simpa [Fseg, line] using hF_eval x.1 x.2
  have hF1 : Fseg 1 = f y := by
    simpa [Fseg, line] using hF_eval y.1 y.2
  have hline_mem : ∀ t ∈ s, line t ∈ X := by
    intro t ht
    exact hX.lineMap_mem x.2 y.2 ht
  have hmaps : Set.MapsTo line s X := by
    intro t ht
    exact hline_mem t ht
  have hderiv : ∀ (t : ℝ) (ht : t ∈ s),
      HasDerivWithinAt Fseg
        ⟪grad ⟨line t, hX.lineMap_mem x.2 y.2 ht⟩, d⟫_ℝ s t := by
    intro t ht
    have hline_deriv : HasDerivWithinAt line d s t := by
      simpa [line, d] using
        (AffineMap.hasDerivWithinAt_lineMap (a := x.1) (b := y.1)
          (s := s) (x := t))
    have hfdiffOn : DifferentiableOn ℝ F X :=
      hF_contDiff.differentiableOn_one
    have hfdiff : DifferentiableWithinAt ℝ F X (line t) :=
      hfdiffOn (line t) (hline_mem t ht)
    have hfseg : HasDerivWithinAt Fseg
        ((fderivWithin ℝ F X (line t)) d) s t := by
      simpa [Fseg, Function.comp_def] using
        hfdiff.hasFDerivWithinAt.comp_hasDerivWithinAt_of_eq t hline_deriv hmaps
          (by simp [line])
    have hgrad_apply :
        (fderivWithin ℝ F X (line t)) d =
          ⟪grad ⟨line t, hX.lineMap_mem x.2 y.2 ht⟩, d⟫_ℝ :=
      hgrad ⟨line t, hX.lineMap_mem x.2 y.2 ht⟩ d
    simpa [hgrad_apply] using hfseg
  have hbound : ∀ (t : ℝ) (ht : t ∈ s),
      ⟪grad ⟨line t, hX.lineMap_mem x.2 y.2 ht⟩, d⟫_ℝ ≤
        ⟪grad x, d⟫_ℝ + L * t * ‖d‖ ^ 2 := by
    intro t ht
    let zt : {x : E // x ∈ X} := ⟨line t, hX.lineMap_mem x.2 y.2 ht⟩
    have ht_nonneg : 0 ≤ t := ht.1
    have hseg_sub : zt.1 - x.1 = t • d := by
      simp [zt, line, d, AffineMap.lineMap_apply_module']
    have hnorm_line : ‖zt.1 - x.1‖ = t * ‖d‖ := by
      rw [hseg_sub, norm_smul, Real.norm_of_nonneg ht_nonneg]
    have hlip : ‖grad zt - grad x‖ ≤ L * (t * ‖d‖) := by
      calc
        ‖grad zt - grad x‖ ≤ L * ‖zt.1 - x.1‖ :=
          hgrad_lipschitz x zt
        _ = L * (t * ‖d‖) := by rw [hnorm_line]
    have hinner_diff :
        ⟪grad zt, d⟫_ℝ - ⟪grad x, d⟫_ℝ =
          ⟪grad zt - grad x, d⟫_ℝ := by
      rw [inner_sub_left]
    have hcs :
        ⟪grad zt - grad x, d⟫_ℝ ≤ ‖grad zt - grad x‖ * ‖d‖ := by
      calc
        ⟪grad zt - grad x, d⟫_ℝ
            ≤ |⟪grad zt - grad x, d⟫_ℝ| := le_abs_self _
        _ ≤ ‖grad zt - grad x‖ * ‖d‖ :=
          abs_real_inner_le_norm (grad zt - grad x) d
    have hmul :
        ‖grad zt - grad x‖ * ‖d‖ ≤ L * t * ‖d‖ ^ 2 := by
      have hmul' :
          ‖grad zt - grad x‖ * ‖d‖ ≤
            (L * (t * ‖d‖)) * ‖d‖ :=
        mul_le_mul_of_nonneg_right hlip (norm_nonneg d)
      calc
        ‖grad zt - grad x‖ * ‖d‖
            ≤ (L * (t * ‖d‖)) * ‖d‖ := hmul'
        _ = L * t * ‖d‖ ^ 2 := by ring
    have hdiff_le :
        ⟪grad zt, d⟫_ℝ - ⟪grad x, d⟫_ℝ ≤
          L * t * ‖d‖ ^ 2 := by
      calc
        ⟪grad zt, d⟫_ℝ - ⟪grad x, d⟫_ℝ
            = ⟪grad zt - grad x, d⟫_ℝ := hinner_diff
        _ ≤ ‖grad zt - grad x‖ * ‖d‖ := hcs
        _ ≤ L * t * ‖d‖ ^ 2 := hmul
    linarith
  let phi : ℝ → ℝ := fun t =>
    if ht : t ∈ s then
      ⟪grad ⟨line t, hX.lineMap_mem x.2 y.2 ht⟩, d⟫_ℝ
    else 0
  have hderiv_phi : ∀ (t : ℝ) (ht : t ∈ s),
      HasDerivWithinAt Fseg (phi t) s t := by
    intro t ht
    rw [show phi t =
        ⟪grad ⟨line t, hX.lineMap_mem x.2 y.2 ht⟩, d⟫_ℝ by
      dsimp [phi]
      rw [dif_pos ht]]
    exact hderiv t ht
  have hbound_phi : ∀ (t : ℝ) (ht : t ∈ s),
      phi t ≤ ⟪grad x, d⟫_ℝ + (L * ‖d‖ ^ 2) * t := by
    intro t ht
    have hb := hbound t ht
    rw [show phi t =
        ⟪grad ⟨line t, hX.lineMap_mem x.2 y.2 ht⟩, d⟫_ℝ by
      dsimp [phi]
      rw [dif_pos ht]]
    simpa [mul_assoc, mul_comm, mul_left_comm] using hb
  have hscalar :
      Fseg 1 ≤ Fseg 0 + ⟪grad x, d⟫_ℝ + (L * ‖d‖ ^ 2) / 2 := by
    exact le_value_add_of_hasDerivWithinAt_le_affine_on_Icc Fseg phi
      ⟪grad x, d⟫_ℝ (L * ‖d‖ ^ 2) hderiv_phi hbound_phi
  rw [hF0, hF1] at hscalar
  change f y ≤ f x + ⟪grad x, y.1 - x.1⟫_ℝ +
    (L / 2) * ‖y.1 - x.1‖ ^ 2
  rw [show d = y.1 - x.1 by rfl] at hscalar
  calc
    f y ≤ f x + ⟪grad x, y.1 - x.1⟫_ℝ +
        (L * ‖y.1 - x.1‖ ^ 2) / 2 := hscalar
    _ = f x + ⟪grad x, y.1 - x.1⟫_ℝ +
        (L / 2) * ‖y.1 - x.1‖ ^ 2 := by ring

/-- A `C¹` function on a uniquely differentiable set has continuous
`gradientWithin` on the carrier subtype.

The statement packages the common route from continuity of within derivatives
on `X` to continuity of the selected inner-product gradient as a map out of
`{x // x ∈ X}`.

Layer: Glue | Gap: Level 0 (within-gradient subtype continuity)
Proof: use `ContDiffOn.continuousOn_fderivWithin` under `UniqueDiffOn`, compose
  with the subtype projection, and transport continuity through the inverse
  Riesz equivalence used by `gradientWithin`.
Source: Mathlib smooth within-calculus, unique differentiability, subtype
  topology, and real inner-product duality APIs
Used in: stochastic block mirror descent distance-generator gradient continuity
  and stochastic mirror descent prox-map continuity
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/assumptions/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem continuous_gradientWithin_subtype_of_contDiffOn_uniqueDiffOn
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {X : Set E} {ν : E → ℝ}
    (hν : ContDiffOn ℝ 1 ν X) (huniq : UniqueDiffOn ℝ X) :
    Continuous (fun z : {x : E // x ∈ X} => gradientWithin ν X z.1) := by
  have hfder : ContinuousOn (fderivWithin ℝ ν X) X := by
    exact hν.continuousOn_fderivWithin huniq (by norm_num)
  have hfder_sub : Continuous (fun z : {x : E // x ∈ X} =>
      fderivWithin ℝ ν X z.1) := by
    exact hfder.comp_continuous continuous_subtype_val (fun z => z.2)
  have hdual : Continuous (fun z : {x : E // x ∈ X} =>
      (InnerProductSpace.toDual ℝ E).symm (fderivWithin ℝ ν X z.1)) := by
    exact (InnerProductSpace.toDual ℝ E).symm.continuous.comp hfder_sub
  simpa [gradientWithin] using hdual

/-- Carrier form of the standard `L`-smooth quadratic upper bound on a convex set.

For a function represented on a carrier subtype by an ambient function, if a
selected carrier gradient gives a `HasGradientWithinAt` derivative at every
feasible point and is `L`-Lipschitz along feasible carrier points, then the
usual quadratic upper model bounds the carrier objective between any two
feasible points.

Layer: Glue | Gap: Level 2 (carrier smoothness quadratic upper bound from within gradients)
Proof: restrict the ambient function to the feasible segment, identify the
  one-dimensional derivative by the within-gradient chain rule, bound the
  derivative error by carrier Lipschitzness and Cauchy-Schwarz, then integrate
  the affine derivative bound on `[0, 1]`.
Source: Mathlib convex segments, within-gradient chain rule, Hilbert-space
  Cauchy-Schwarz, and one-dimensional derivative-bound integration APIs
Used in: constrained smooth objective decrease before proximal and mirror
  descent algebra in stochastic optimization proofs
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
theorem Convex.carrier_smooth_quadratic_upper_bound_of_hasGradientWithinAt_lipschitz
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {X : Set E} (f : {x : E // x ∈ X} → ℝ) (F : E → ℝ)
    (grad : {x : E // x ∈ X} → E) (L : ℝ)
    (hX : Convex ℝ X)
    (hF_eval : ∀ (z : E) (hz : z ∈ X), F z = f ⟨z, hz⟩)
    (hgrad :
      ∀ (z : {x : E // x ∈ X}), HasGradientWithinAt F (grad z) X z.1)
    (hgrad_lipschitz :
      ∀ x y : {x : E // x ∈ X},
        ‖grad y - grad x‖ ≤ L * ‖y.1 - x.1‖)
    (x y : {x : E // x ∈ X}) :
    f x - f y - ⟪grad y, x.1 - y.1⟫_ℝ ≤
      (L / 2) * ‖x.1 - y.1‖ ^ 2 := by
  let d : E := x.1 - y.1
  let s : Set ℝ := Set.Icc (0 : ℝ) 1
  let line : ℝ → E := fun t => AffineMap.lineMap y.1 x.1 t
  let Fseg : ℝ → ℝ := fun t => F (line t)
  have hF0 : Fseg 0 = f y := by
    simpa [Fseg, line] using hF_eval y.1 y.2
  have hF1 : Fseg 1 = f x := by
    simpa [Fseg, line] using hF_eval x.1 x.2
  have hline_mem : ∀ t ∈ s, line t ∈ X := by
    intro t ht
    exact hX.lineMap_mem y.2 x.2 ht
  have hmaps : Set.MapsTo line s X := by
    intro t ht
    exact hline_mem t ht
  have hderiv : ∀ (t : ℝ) (ht : t ∈ s),
      HasDerivWithinAt Fseg
        ⟪grad ⟨line t, hX.lineMap_mem y.2 x.2 ht⟩, d⟫_ℝ s t := by
    intro t ht
    have hline_deriv : HasDerivWithinAt line d s t := by
      simpa [line, d] using
        (AffineMap.hasDerivWithinAt_lineMap (a := y.1) (b := x.1)
          (s := s) (x := t))
    have hfseg : HasDerivWithinAt Fseg
        ((InnerProductSpace.toDual ℝ E
            (grad ⟨line t, hX.lineMap_mem y.2 x.2 ht⟩)) d) s t := by
      simpa [Fseg, Function.comp_def] using
        (hgrad ⟨line t, hX.lineMap_mem y.2 x.2 ht⟩).hasFDerivWithinAt
          |>.comp_hasDerivWithinAt_of_eq t hline_deriv hmaps (by simp [line])
    simpa using hfseg
  have hbound : ∀ (t : ℝ) (ht : t ∈ s),
      ⟪grad ⟨line t, hX.lineMap_mem y.2 x.2 ht⟩, d⟫_ℝ ≤
        ⟪grad y, d⟫_ℝ + L * t * ‖d‖ ^ 2 := by
    intro t ht
    let zt : {x : E // x ∈ X} := ⟨line t, hX.lineMap_mem y.2 x.2 ht⟩
    have ht_nonneg : 0 ≤ t := ht.1
    have hseg_sub : zt.1 - y.1 = t • d := by
      simp [zt, line, d, AffineMap.lineMap_apply_module']
    have hnorm_line : ‖zt.1 - y.1‖ = t * ‖d‖ := by
      rw [hseg_sub, norm_smul, Real.norm_of_nonneg ht_nonneg]
    have hlip : ‖grad zt - grad y‖ ≤ L * (t * ‖d‖) := by
      calc
        ‖grad zt - grad y‖ ≤ L * ‖zt.1 - y.1‖ :=
          hgrad_lipschitz y zt
        _ = L * (t * ‖d‖) := by rw [hnorm_line]
    have hinner_diff :
        ⟪grad zt, d⟫_ℝ - ⟪grad y, d⟫_ℝ =
          ⟪grad zt - grad y, d⟫_ℝ := by
      rw [inner_sub_left]
    have hcs :
        ⟪grad zt - grad y, d⟫_ℝ ≤ ‖grad zt - grad y‖ * ‖d‖ := by
      calc
        ⟪grad zt - grad y, d⟫_ℝ
            ≤ |⟪grad zt - grad y, d⟫_ℝ| := le_abs_self _
        _ ≤ ‖grad zt - grad y‖ * ‖d‖ :=
          abs_real_inner_le_norm (grad zt - grad y) d
    have hmul :
        ‖grad zt - grad y‖ * ‖d‖ ≤ L * t * ‖d‖ ^ 2 := by
      have hmul' :
          ‖grad zt - grad y‖ * ‖d‖ ≤
            (L * (t * ‖d‖)) * ‖d‖ :=
        mul_le_mul_of_nonneg_right hlip (norm_nonneg d)
      calc
        ‖grad zt - grad y‖ * ‖d‖
            ≤ (L * (t * ‖d‖)) * ‖d‖ := hmul'
        _ = L * t * ‖d‖ ^ 2 := by ring
    have hdiff_le :
        ⟪grad zt, d⟫_ℝ - ⟪grad y, d⟫_ℝ ≤
          L * t * ‖d‖ ^ 2 := by
      calc
        ⟪grad zt, d⟫_ℝ - ⟪grad y, d⟫_ℝ
            = ⟪grad zt - grad y, d⟫_ℝ := hinner_diff
        _ ≤ ‖grad zt - grad y‖ * ‖d‖ := hcs
        _ ≤ L * t * ‖d‖ ^ 2 := hmul
    linarith
  let phi : ℝ → ℝ := fun t =>
    if ht : t ∈ s then
      ⟪grad ⟨line t, hX.lineMap_mem y.2 x.2 ht⟩, d⟫_ℝ
    else 0
  have hderiv_phi : ∀ (t : ℝ) (ht : t ∈ s),
      HasDerivWithinAt Fseg (phi t) s t := by
    intro t ht
    rw [show phi t =
        ⟪grad ⟨line t, hX.lineMap_mem y.2 x.2 ht⟩, d⟫_ℝ by
      dsimp [phi]
      rw [dif_pos ht]]
    exact hderiv t ht
  have hbound_phi : ∀ (t : ℝ) (ht : t ∈ s),
      phi t ≤ ⟪grad y, d⟫_ℝ + (L * ‖d‖ ^ 2) * t := by
    intro t ht
    have hb := hbound t ht
    rw [show phi t =
        ⟪grad ⟨line t, hX.lineMap_mem y.2 x.2 ht⟩, d⟫_ℝ by
      dsimp [phi]
      rw [dif_pos ht]]
    simpa [mul_assoc, mul_comm, mul_left_comm] using hb
  have hscalar :
      Fseg 1 ≤ Fseg 0 + ⟪grad y, d⟫_ℝ + (L * ‖d‖ ^ 2) / 2 := by
    exact le_value_add_of_hasDerivWithinAt_le_affine_on_Icc Fseg phi
      ⟪grad y, d⟫_ℝ (L * ‖d‖ ^ 2) hderiv_phi hbound_phi
  rw [hF0, hF1] at hscalar
  rw [show d = x.1 - y.1 by rfl] at hscalar
  nlinarith

namespace SOptLib

/-- The within-gradient of a normalized finite average is the normalized average
of the component within-gradients.

If every component objective has a prescribed within-gradient at `x` along
`X`, then the finite average objective has the finite average of those
gradients as a within-gradient at the same constrained point.

Layer: Glue | Gap: Level 1 (finite average constrained gradient calculus)
Proof: sum the component Fréchet derivatives within `X`, scale the scalar-valued
  derivative by the inverse component count, and convert back through the
  Hilbert-space gradient/dual identification.
Source: Mathlib finite Fréchet-derivative sums and Hilbert-space gradient APIs
Used in: randomized accelerated proximal-point finite-sum gradient bridge on
  the feasible set
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
theorem HasGradientWithinAt.fintype_average
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (F : ι → E → ℝ) (G : ι → E → E) (X : Set E) (x : E)
    (hF : ∀ i : ι, HasGradientWithinAt (F i) (G i x) X x) :
    HasGradientWithinAt
      (fun z : E => (Fintype.card ι : ℝ)⁻¹ *
        Finset.sum Finset.univ (fun i : ι => F i z))
      ((Fintype.card ι : ℝ)⁻¹ •
        Finset.sum Finset.univ (fun i : ι => G i x)) X x := by
  classical
  have hsum : HasFDerivWithinAt
      (fun z : E => Finset.sum Finset.univ (fun i : ι => F i z))
      (Finset.sum Finset.univ
        (fun i : ι => InnerProductSpace.toDual ℝ E (G i x))) X x := by
    refine HasFDerivWithinAt.fun_sum ?_
    intro i _hi
    exact (hF i).hasFDerivWithinAt
  have hscaled := hsum.const_smul ((Fintype.card ι : ℝ)⁻¹)
  convert hscaled.hasGradientWithinAt using 1
  simp [map_smul, map_sum]

end SOptLib

/-- Adding a centered squared-norm regularizer adds its Hilbert gradient.

If `f` has within-gradient `g` at `x` along `X`, then
`y ↦ f y + mu * ‖y - z‖ ^ 2` has within-gradient
`g + (2 * mu) • (x - z)` at the same constrained point.

Layer: Glue | Gap: Level 1 (centered quadratic regularizer within-gradient)
Proof: convert the base gradient to a Fréchet derivative, differentiate the
  translation `y ↦ y - z`, apply Mathlib's squared-norm derivative rule, scale
  by `mu`, add derivatives, and convert back through the Hilbert-space
  gradient/dual identification.
Source: Mathlib Hilbert-space gradient APIs and `HasFDerivWithinAt.norm_sq`
Used in: randomized accelerated proximal-point component subproblem derivative
  bridge for quadratic regularization on a feasible set
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
theorem HasGradientWithinAt.add_const_mul_norm_sub_sq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} {g : E} {X : Set E} {x : E} (hf : HasGradientWithinAt f g X x)
    (mu : ℝ) (z : E) :
    HasGradientWithinAt (fun y : E => f y + mu * ‖y - z‖ ^ 2)
      (g + (2 * mu) • (x - z)) X x := by
  have hf' := hf.hasFDerivWithinAt
  have hsub : HasFDerivWithinAt (fun y : E => y - z) (1 : E →L[ℝ] E) X x := by
    simpa using ((hasFDerivAt_id x).sub_const z).hasFDerivWithinAt
  have hsq : HasFDerivWithinAt (fun y : E => ‖y - z‖ ^ 2)
      (2 • (innerSL ℝ (x - z)).comp (1 : E →L[ℝ] E)) X x := by
    simpa using hsub.norm_sq
  have hq0 := hsq.const_mul mu
  have hq : HasFDerivWithinAt (fun y : E => mu * ‖y - z‖ ^ 2)
      (InnerProductSpace.toDual ℝ E ((2 * mu) • (x - z))) X x := by
    convert hq0 using 1
    ext y
    simp [mul_comm, mul_left_comm]
  have h := hf'.add hq
  simpa [map_add, map_smul] using h.hasGradientWithinAt

/-- The centered quadratic `y ↦ (mu / 2) * ‖y - z‖ ^ 2` has gradient
`mu • (x - z)` at `x`.

Layer: Glue | Gap: Level 0 (centered quadratic Hilbert gradient)
Proof: differentiate the translation `y ↦ y - z`, apply Mathlib's squared-norm
  Fréchet derivative rule, scale by `mu / 2`, and convert the resulting dual map
  to `HasGradientAt`.
Source: Mathlib Hilbert-space calculus APIs and `HasFDerivAt.norm_sq`
Used in: quadratic-regularized proximal subproblem first-order conditions
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
theorem hasGradientAt_const_mul_norm_sub_sq_centered
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (mu : ℝ) (z x : E) :
    HasGradientAt (fun y : E => (mu / 2) * ‖y - z‖ ^ 2) (mu • (x - z)) x := by
  have hsub : HasFDerivAt (fun y : E => y - z) (1 : E →L[ℝ] E) x := by
    simpa using ((hasFDerivAt_id x).sub_const z)
  have hsq : HasFDerivAt (fun y : E => ‖y - z‖ ^ 2)
      (2 • (innerSL ℝ (x - z)).comp (1 : E →L[ℝ] E)) x := by
    simpa using hsub.norm_sq
  have hq0 := hsq.const_mul (mu / 2)
  have hq : HasFDerivAt (fun y : E => (mu / 2) * ‖y - z‖ ^ 2)
      (InnerProductSpace.toDual ℝ E (mu • (x - z))) x := by
    convert hq0 using 1
    ext y
    simp [mul_comm, mul_left_comm]
    ring
  simpa using hq.hasGradientAt

/-- Pointwise norm control bounds directional inner-product growth.

This is the local estimate used before integrating a one-dimensional derivative
bound in smooth-descent proofs. It isolates the Hilbert-space
Cauchy-Schwarz/norm-control part from the surrounding calculus argument.

Layer: Glue | Gap: Level 1 (local norm-control inner-product bound)
Proof: apply Cauchy-Schwarz to `u - v`, use the local norm bound, then rearrange
  the inner-product difference.
Source: Mathlib Hilbert-space Cauchy-Schwarz and normed-space APIs
Used in: smooth-descent segment integration for constrained stochastic
  optimization methods
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
theorem inner_le_inner_add_mul_norm_sq_of_norm_sub_le
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v d : E) (C : ℝ) (h : ‖u - v‖ ≤ C * ‖d‖) :
    ⟪u, d⟫_ℝ ≤ ⟪v, d⟫_ℝ + C * ‖d‖ ^ 2 := by
  have hinner_diff :
      ⟪u, d⟫_ℝ - ⟪v, d⟫_ℝ = ⟪u - v, d⟫_ℝ := by
    rw [inner_sub_left]
  have hcs :
      ⟪u - v, d⟫_ℝ ≤ ‖u - v‖ * ‖d‖ :=
    real_inner_le_norm (u - v) d
  have hmul :
      ‖u - v‖ * ‖d‖ ≤ C * ‖d‖ ^ 2 := by
    have hmul' : ‖u - v‖ * ‖d‖ ≤ (C * ‖d‖) * ‖d‖ :=
      mul_le_mul_of_nonneg_right h (norm_nonneg d)
    calc
      ‖u - v‖ * ‖d‖ ≤ (C * ‖d‖) * ‖d‖ := hmul'
      _ = C * ‖d‖ ^ 2 := by ring
  have hdiff_le :
      ⟪u, d⟫_ℝ - ⟪v, d⟫_ℝ ≤ C * ‖d‖ ^ 2 := by
    calc
      ⟪u, d⟫_ℝ - ⟪v, d⟫_ℝ = ⟪u - v, d⟫_ℝ := hinner_diff
      _ ≤ ‖u - v‖ * ‖d‖ := hcs
      _ ≤ C * ‖d‖ ^ 2 := hmul
  simpa [add_comm, add_left_comm, add_assoc] using sub_le_iff_le_add.mp hdiff_le

namespace SOptLib

/-- A finite average plus a centered quadratic has the averaged gradient plus the
quadratic gradient within the feasible set.

If each component objective has the prescribed within-gradient at `x` along
`X`, then the objective
`y ↦ card⁻¹ * ∑ i, F i y + (mu / 2) * ‖y - z‖ ^ 2` has within-gradient
`card⁻¹ • ∑ i, gradF i x + mu • (x - z)`.

Layer: Glue | Gap: Level 1 (finite-average centered-quadratic gradient calculus)
Proof: apply the normalized finite-average `HasGradientWithinAt` rule, then add
  the centered squared-norm regularizer through the Hilbert-space gradient
  calculus lemma and simplify the factor `2 * (mu / 2)`.
Source: Mathlib finite Fréchet-derivative sums and Hilbert-space squared-norm
  gradient APIs
Used in: finite-sum proximal subproblem first-order condition on a feasible set
Book citation: book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized accelerated proximal-point method -/
theorem HasGradientWithinAt.fintype_average_add_centered_quadratic
    {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (F : ι → E → ℝ) (gradF : ι → E → E) (X : Set E) (mu : ℝ) (z x : E)
    (hF : ∀ i : ι, HasGradientWithinAt (F i) (gradF i x) X x) :
    HasGradientWithinAt
      (fun y : E =>
        (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ (fun i : ι => F i y) +
          (mu / 2) * ‖y - z‖ ^ 2)
      (((Fintype.card ι : ℝ)⁻¹ •
          Finset.sum Finset.univ (fun i : ι => gradF i x)) + mu • (x - z)) X x := by
  simpa [two_mul, mul_comm, mul_left_comm, mul_assoc] using
    (HasGradientWithinAt.fintype_average F gradF X x hF).add_const_mul_norm_sub_sq
      (mu / 2) z

end SOptLib

-- Batch 2 promoted from .sgd_phase3_staging/SOptLib/Glue/ConvexOn_firstOrderLinearModel_le_of_hasGradientWithinAt.lean
/-!
-- Generalization plan (G0):
-- concept/name: convex first-order support inequality for the named
--   first-order linear model; orig was `linearModel_le_f_of_mem`, renamed away
--   from setup fields and stochastic conditional-gradient notation.
-- generality used: real Hilbert-space carrier with `[NormedAddCommGroup E]`,
--   `[InnerProductSpace ℝ E]`, and `[CompleteSpace E]`; no measure,
--   filtration, independence, integrability, compactness, oracle, smoothness,
--   or finite-dimensional assumption is used. Convexity is exactly
--   `Convex ℝ X` plus `ConvexOn ℝ X f`, and differentiability is the
--   pointwise `HasGradientWithinAt f g X z`.
-- portable call pattern: constrained smooth convex descent, stochastic
--   gradient, mirror-descent, proximal-gradient, and conditional-gradient
--   proofs can replace a linearization at a feasible point by the true
--   objective value at another feasible point while changing only `X`, `f`,
--   the selected gradient vector, and the two feasible points.
-- counterargument checked: not paper-local traceability because this is the
--   standard supporting-hyperplane inequality for convex differentiable
--   functions; not a pure wrapper because Mathlib supplies only the
--   one-dimensional slope step and SOptLib has the model def but no theorem
--   connecting `ConvexOn`/`HasGradientWithinAt` to that model.
-- coverage search: searched SOptLib catalog/source for `firstOrderLinearModel`,
--   `first_order_linear_model`, `HasGradientWithinAt`, `supporting
--   inequality`, and `ConvexOn`; relevant hits were the staged
--   `SOptLib.first_order_linear_model`, `Convex.first_order_condition...` for
--   minimizers, and smooth upper-bound carrier lemmas, none of which prove this
--   convex support inequality. LeanSearch for "convex function first order
--   supporting hyperplane has gradient within at" found Mathlib
--   `ConvexOn.le_slope_of_hasDerivAt`/within slope lemmas, which are the
--   one-dimensional ingredient rather than the packaged Hilbert-space result.
-- minimal hypotheses: global gradient field generalized to a single vector
--   `g`; all remaining assumptions are used directly by the segment and
--   slope proof.
-/

open scoped InnerProductSpace

/-- A convex function lies above its first-order linear model at feasible points.

If `f` is convex on a convex set `X` and has within-gradient `g` at a feasible
base point `z`, then the Taylor affine model at `z` evaluated at any feasible
`x` is bounded above by `f x`.

Layer: Glue | Gap: Level 1 (convex first-order support inequality)
Proof: restrict `f` to the feasible segment from `z` to `x`, use the
  one-dimensional convex slope bound at the left endpoint, and identify the
  segment derivative by the within-gradient chain rule.
Source: Mathlib convex segment, `ConvexOn` slope, affine-map derivative, and
  within-gradient calculus APIs
Used in: stochastic conditional-gradient sliding replacement of a local
  linearized objective model by the true convex objective value
Book citation: book/FOML/StochasticConditionalGradientSliding.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic conditional-gradient sliding -/
theorem ConvexOn.firstOrderLinearModel_le_of_hasGradientWithinAt
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {X : Set E} {f : E → ℝ} {g z x : E}
    (hX : Convex ℝ X) (hf : ConvexOn ℝ X f)
    (hz : z ∈ X) (hx : x ∈ X)
    (hgrad : HasGradientWithinAt f g X z) :
    f z + ⟪g, x - z⟫_ℝ ≤ f x := by
  let I : Set ℝ := Set.Icc (0 : ℝ) 1
  let line : ℝ → E := fun t => AffineMap.lineMap z x t
  have hline_mem : I ⊆ line ⁻¹' X := by
    intro t ht
    change line t ∈ X
    simpa [line] using hX.lineMap_mem hz hx ht
  have hconv_line : ConvexOn ℝ I (fun t => f (line t)) := by
    simpa [line, I] using
      (hf.comp_affineMap (AffineMap.lineMap z x)).subset hline_mem
        (convex_Icc 0 1)
  have hmaps : Set.MapsTo line I X := by
    intro t ht
    exact hline_mem ht
  have hline_deriv :
      HasDerivWithinAt line (x - z) I 0 := by
    simpa [line, I] using
      (AffineMap.hasDerivWithinAt_lineMap (a := z) (b := x)
        (s := I) (x := (0 : ℝ)))
  have hfline :
      HasDerivWithinAt (fun t => f (line t)) (⟪g, x - z⟫_ℝ) I 0 := by
    have hcomp :=
      hgrad.hasFDerivWithinAt.comp_hasDerivWithinAt_of_eq 0 hline_deriv hmaps
        (by simp [line])
    simpa [line] using hcomp
  have hslope :
      ⟪g, x - z⟫_ℝ ≤ slope (fun t => f (line t)) 0 1 := by
    exact hconv_line.le_slope_of_hasDerivWithinAt
      (x := (0 : ℝ)) (y := (1 : ℝ))
      (by norm_num [I]) (by norm_num [I]) (by norm_num) hfline
  have hslope_eval :
      slope (fun t => f (line t)) 0 1 = f x - f z := by
    simp [slope, line]
  rw [hslope_eval] at hslope
  linarith

theorem ConvexOn.first_order_linear_model_le_of_hasGradientWithinAt
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {X : Set E} {f : E → ℝ} {g z x : E}
    (hf : ConvexOn ℝ X f) (hz : z ∈ X) (hx : x ∈ X)
    (hgrad : HasGradientWithinAt f g X z) :
    f z + ⟪g, x - z⟫_ℝ ≤ f x :=
  ConvexOn.firstOrderLinearModel_le_of_hasGradientWithinAt hf.1 hf hz hx hgrad


-- Promoted from Staging/eq_gradient_of_hasGradientAt_of_affine_minorant_touch.lean
open scoped InnerProductSpace

-- Generalization plan (G0):
-- concept/name: equality of a touching affine lower support slope with the
--   gradient; orig was affine_minorant_touch_gradient_eq, renamed away from the
--   random-primal-dual-gradient local helper name.
-- generality used: arbitrary real Hilbert decision space `E`, scalar objective
--   `F`, point `x0`, gradient `g`, affine slope `a`, and intercept `c`; no
--   measure, filtration, independence, integrability, convexity, smoothness
--   constants, algorithm updates, or finite-dimensionality is used.
-- portable call pattern: Fenchel-dual saddle proofs, KKT support proofs, and
--   cutting-plane lower-model arguments identify the slope of a globally
--   touching affine lower support with the pointwise gradient while varying
--   the function, touch point, affine vector, and intercept.
-- counterargument checked: this is not paper-local traceability because it is
--   the standard unconstrained first-order identification for a touching lower
--   support; it is not a pure wrapper over a single Mathlib/SOptLib lemma,
--   since the proof composes the affine residual minimum, the Hilbert gradient
--   API, and the existing constrained first-order condition.
-- coverage search: searched project/catalog tokens `affine_minorant`,
--   `minorant`, `touch`, `support gradient`, and `HasGradientAt`; relevant
--   hits were the local random-primal-dual helper, Fenchel support lemmas, and
--   `Convex.first_order_condition_of_isMinOn_hasFDerivWithinAt`, but no theorem
--   stating the touching-affine-gradient equality. LeanSearch for "touching
--   affine lower bound differentiable function slope equals gradient" returned
--   generic gradient selector and convex one-dimensional slope lemmas, not this
--   statement.
-- minimal hypotheses: global minorization and equality at the single touch
--   point are exactly what makes the affine residual globally minimized at
--   `x0`; finite dimensionality and global differentiability are dropped.

/-- A globally touching affine lower support has the same slope as the gradient.

If `F` has gradient `g` at `x0`, and the affine function
`x ↦ ⟪x, a⟫_ℝ - c` lies below `F` everywhere while touching it at `x0`, then
the affine slope `a` equals the gradient `g`.

Layer: Glue | Gap: Level 1 (touching affine support gradient identification)
Proof: subtract the affine minorant from `F`, so the residual has a global
  minimum at the touch point; the first-order condition on `Set.univ` forces
  the residual gradient `g - a` to have nonpositive squared norm, hence vanish.
Source: Mathlib Hilbert-space gradient calculus and SOptLib constrained
  first-order condition APIs
Used in: random primal-dual gradient Fenchel saddle proof identifying the
  touching product-dual affine minorant slope with the average objective
  gradient
Book citation: book/FOML/RandomPrimalDualGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, random primal-dual gradient -/
theorem eq_gradient_of_hasGradientAt_of_affine_minorant_touch
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {F : E → ℝ} {g a x0 : E} {c : ℝ}
    (hgrad : HasGradientAt F g x0)
    (hminor : ∀ x : E, ⟪x, a⟫_ℝ - c ≤ F x)
    (htouch : ⟪x0, a⟫_ℝ - c = F x0) :
    a = g := by
  classical
  let Φ : E → ℝ := fun x => F x - (⟪x, a⟫_ℝ - c)
  let G : E := g - a
  have hmin : ∀ u ∈ (Set.univ : Set E), Φ x0 ≤ Φ u := by
    intro u _hu
    have hx0 : Φ x0 = 0 := by
      simp [Φ, htouch]
    have hu : 0 ≤ Φ u := by
      have h := hminor u
      simp [Φ]
      linarith
    linarith
  have hF : HasFDerivAt F ((innerSL ℝ) g) x0 := hgrad.hasFDerivAt
  have hlin0 :
      HasFDerivAt (fun x : E => ⟪a, x⟫_ℝ - c) ((innerSL ℝ) a) x0 :=
    ((innerSL ℝ a).hasFDerivAt.sub_const c)
  have hlin :
      HasFDerivAt (fun x : E => ⟪x, a⟫_ℝ - c) ((innerSL ℝ) a) x0 := by
    simpa [real_inner_comm] using hlin0
  have hderiv :
      HasFDerivWithinAt Φ ((innerSL ℝ) G) (Set.univ : Set E) x0 := by
    have hsub := hF.sub hlin
    convert hsub.hasFDerivWithinAt using 1
    · ext v
      simp [G, ContinuousLinearMap.sub_apply]
  have hdir :=
    Convex.first_order_condition_of_isMinOn_hasFDerivWithinAt
      (T := (Set.univ : Set E)) (Φ := Φ) (z := x0) (y := x0 - G)
      (F' := (innerSL ℝ) G) convex_univ (by simp) (by simp) hmin hderiv
  have hnonpos : ⟪G, G⟫_ℝ ≤ 0 := by
    have hdir' : 0 ≤ ((innerSL ℝ) G) (-G) := by
      convert hdir using 2
      abel
    have hneg : 0 ≤ -⟪G, G⟫_ℝ := by
      simpa [inner_neg_right] using hdir'
    linarith
  have hzero_inner : ⟪G, G⟫_ℝ = 0 := by
    have hnonneg : 0 ≤ ⟪G, G⟫_ℝ := by
      exact inner_self_nonneg (𝕜 := ℝ) (x := G)
    linarith
  have hGzero : G = 0 := inner_self_eq_zero.mp hzero_inner
  exact (sub_eq_zero.mp hGzero).symm

-- Promoted from Staging/hasGradientAt_integral_of_dominated_of_gradient_le.lean
-- Generalization plan (G0):
-- concept/name: differentiation under a Bochner integral for Hilbert-space gradients; orig was section3_objective_hasGradientAt_integral_stochasticGradient
-- generality used: arbitrary measurable space and measure; complete real inner-product domain; no probability, convexity, smoothness, or oracle assumptions
-- portable call pattern: expected-objective proofs for SGD, variance reduction, and stochastic momentum replace the loss, gradient field, measure, query, and integrable domination function while retaining the integral-gradient conclusion
-- counterargument checked: not paper-local or a pure wrapper because Mathlib supplies only the continuous-linear-map derivative theorem, not the gradient-valued contract or the toDual/integral bridge
-- coverage search: queried “gradient of integral equals integral of gradients under integrable domination” and the precise HasGradientAt shape; Mathlib has hasFDerivAt_integral_of_dominated_of_fderiv_le, while SOptLib has only finite-average gradient results
-- minimal hypotheses: probability and finite-dimensional assumptions dropped; completeness is required by Mathlib's Hilbert-space Riesz duality API, while gradient and domination assumptions are restricted to a neighborhood of the differentiation point

open MeasureTheory
open Topology
open scoped InnerProductSpace

/-- A dominated pointwise gradient field differentiates through a scalar Bochner integral.

Layer: Glue | Gap: Level 1 (gradient-valued differentiation under the integral)
Proof: convert pointwise gradients to Fréchet derivatives through `toDual`, apply Mathlib's dominated parametric-integral theorem, and commute the linear isometry `toDual` with the Bochner integral.
Source: Mathlib parametric Bochner integral calculus and real Hilbert-space gradient/dual APIs
Used in: expected-loss objectives for stochastic gradient, variance-reduced, and recursive-momentum methods when identifying the objective gradient with the mean sample gradient
Book citation: book/STORM/StochasticRecursiveMomentum.json#/assumptions
Origin algorithm: Cutkosky and Orabona, Momentum-Based Variance Reduction in Non-Convex SGD - STOchastic Recursive Momentum -/
theorem hasGradientAt_integral_of_dominated_of_gradient_le
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (μ : Measure Ω) (F : E → Ω → ℝ) (gradF : E → Ω → E)
    (x : E) (s : Set E) (bound : Ω → ℝ)
    (hs : s ∈ 𝓝 x)
    (hF_meas : ∀ᶠ z in 𝓝 x, AEStronglyMeasurable (F z) μ)
    (hF_int : Integrable (F x) μ)
    (hgrad_meas : AEStronglyMeasurable (gradF x) μ)
    (hbound : ∀ᵐ ω ∂μ, ∀ z ∈ s, ‖gradF z ω‖ ≤ bound ω)
    (hbound_int : Integrable bound μ)
    (hgradient : ∀ᵐ ω ∂μ, ∀ z ∈ s, HasGradientAt (F · ω) (gradF z ω) z) :
    HasGradientAt (fun z : E => ∫ ω, F z ω ∂μ) (∫ ω, gradF x ω ∂μ) x := by
  let F' : E → Ω → E →L[ℝ] ℝ := fun z ω =>
    InnerProductSpace.toDual ℝ E (gradF z ω)
  have hF'_meas : AEStronglyMeasurable (F' x) μ := by
    exact (InnerProductSpace.toDual ℝ E).continuous.comp_aestronglyMeasurable hgrad_meas
  have hbound' : ∀ᵐ ω ∂μ, ∀ z ∈ s, ‖F' z ω‖ ≤ bound ω := by
    filter_upwards [hbound] with ω hω
    intro z hz
    simpa [F'] using hω z hz
  have hdiff : ∀ᵐ ω ∂μ, ∀ z ∈ s,
      HasFDerivAt (F · ω) (F' z ω) z := by
    filter_upwards [hgradient] with ω hω
    intro z hz
    simpa [F'] using (hω z hz).hasFDerivAt
  have hderiv :
      HasFDerivAt (fun z : E => ∫ ω, F z ω ∂μ) (∫ ω, F' x ω ∂μ) x :=
    hasFDerivAt_integral_of_dominated_of_fderiv_le
      (μ := μ) (F := F) (F' := F') (x₀ := x)
      (bound := bound) (s := s) hs
      hF_meas hF_int hF'_meas hbound' hbound_int hdiff
  have hdual_integral :
      (∫ ω, F' x ω ∂μ) =
        InnerProductSpace.toDual ℝ E (∫ ω, gradF x ω ∂μ) := by
    simpa [F'] using
      (InnerProductSpace.toDual ℝ E).toLinearIsometry.integral_comp_comm (gradF x)
  rw [hdual_integral] at hderiv
  simpa using hderiv.hasGradientAt


-- Merged from Staging/gradient_comp_continuousLinearMap_of_fderiv_pairing.lean

open scoped InnerProductSpace

-- Generalization plan (G0):
-- concept/name: gradient transport through a continuous linear coordinate map
--   from a Fréchet derivative pairing; orig was the repeated local pattern
--   `flattened_gradient_transport_pattern`
-- generality used: an arbitrary normed source space over an `RCLike` scalar field,
--   an arbitrary complete inner-product coordinate space over the same field,
--   a continuous linear map, and pointwise
--   Fréchet-derivative and pairing hypotheses; no measure, finite-dimensionality,
--   convexity, smoothness, oracle, or algorithm assumptions are used
-- portable call pattern: matrix, tensor, block-coordinate, and charted algorithms
--   transport a derivative from an ambient carrier to Hilbert coordinates while
--   changing the carrier, coordinate space, encoding map, objective, point,
--   derivative, and represented gradient but retaining the same gradient conclusion
-- counterargument checked: this is not paper-local traceability or a pure rename;
--   it composes the Fréchet chain rule with a Riesz pairing identification, a
--   recurring proof boundary not provided by either underlying Mathlib lemma alone
-- coverage search: symbol and semantic searches for gradients of functions
--   precomposed with continuous linear maps found Mathlib's
--   `HasFDerivAt.hasGradientAt`, `hasGradientAt_iff_hasFDerivAt`, and the derivative
--   composition API, plus SOptLib's distinct within-derivative theorem
--   `hasFDerivWithinAt_of_contDiffOn_gradientWithin_comp`; coverage is partial
-- minimal hypotheses: the derivative and pairing assumptions are pointwise;
--   completeness is required only on the Hilbert coordinate space by Mathlib's
--   gradient/dual equivalence, and the ambient source needs only normed-space structure

/-- A Fréchet derivative represented by an inner-product pairing after a continuous
linear coordinate map gives the corresponding gradient of the precomposed function.

Layer: Glue | Gap: Level 1 (continuous-linear coordinate transport from derivative pairing to gradient)
Proof: compose the supplied Fréchet derivative with the continuous linear map, identify the composed functional with the Riesz dual using the pairing hypothesis, and convert the result to `HasGradientAt`.
Source: Mathlib Fréchet chain rule for continuous linear maps and Hilbert-space `hasGradientAt_iff_hasFDerivAt`
Used in: matrix, tensor, block-coordinate, and charted adaptive-gradient proofs that flatten an ambient loss and transport its represented derivative to coordinate-space gradients
Book citation: book/research/Source.json#/additional_algorithm_specs/0/steps/1
Origin algorithm: Gupta, Koren, and Singer, Shampoo: Preconditioned Stochastic Tensor Optimization, Algorithms 1, 2, and 3 -/
theorem gradient_comp_continuousLinearMap_of_fderiv_pairing
    {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (L : F →L[𝕜] E) (f : E → 𝕜) (D : E →L[𝕜] 𝕜) (x g : F)
    (hf : HasFDerivAt f D (L x))
    (hpair : ∀ v : F, D (L v) = inner 𝕜 g v) :
    HasGradientAt (fun v : F ↦ f (L v)) g x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hcomp : HasFDerivAt (f ∘ L) (D.comp L) x :=
    hf.comp x L.hasFDerivAt
  have hdual : D.comp L = InnerProductSpace.toDual 𝕜 F g := by
    ext v
    simpa [InnerProductSpace.toDual_apply_apply] using hpair v
  simpa [Function.comp_def, hdual] using hcomp

/-! Promoted from Staging/HasDerivAt_mul_of_eq_zero_left_of_continuousAt_right.lean. -/


-- Generalization plan (G0):
-- concept/name: mixed-regularity product derivative at a vanishing left factor;
--   orig was hasDerivAt_mul_of_hasDerivAt_zero_left_continuousAt
-- generality used: arbitrary nontrivially normed field, normed algebra, base point,
--   derivative, and pointwise derivative/vanishing/continuity hypotheses
-- portable call pattern: perturbation and asymptotic first-variation proofs where a
--   differentiable vanishing scale multiplies an observable that is only continuous;
--   the functions, base point, derivative, and observable value may all change
-- counterargument checked: not paper-local or a pure wrapper; Mathlib's product rule
--   requires differentiability of the right factor, while this result needs only continuity
-- coverage search: queries "derivative product left factor equals zero right factor
--   continuous at point" and "HasDerivAt mul continuousAt eq zero" found Mathlib
--   HasDerivAt.fun_mul/HasDerivAt.mul, whose complete signatures require both derivatives,
--   and no SOptLib theorem with this mixed-regularity contract
-- minimal hypotheses: all hypotheses are pointwise; no finite-dimensional, completeness,
--   measure, convexity, or global regularity assumptions are used

/-- If the left factor vanishes and has a derivative at a point, multiplying it by a
right factor continuous at that point preserves differentiability, with derivative equal
to the left derivative times the right value.

Layer: Glue | Gap: Level 1 (mixed-regularity product derivative at a vanishing factor)
Proof: use the slope characterization of `HasDerivAt`; the product slope factors into the
  left slope and the right value because the left factor vanishes, then pass to the limit.
Source: Mathlib one-dimensional derivative slope characterization and filter limit algebra
Used in: slow-mode first-variation and perturbation expansions where endpoint and phase-sum
  observables are continuous but no derivative of those observables is available
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/14/proof/2
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem HasDerivAt.mul_of_eq_zero_left_of_continuousAt_right
    {𝕜 𝔸 : Type*} [NontriviallyNormedField 𝕜]
    [NormedRing 𝔸] [NormedAlgebra 𝕜 𝔸]
    {x : 𝕜} {f g : 𝕜 → 𝔸} {f' : 𝔸}
    (hf : HasDerivAt f f' x) (hf0 : f x = 0)
    (hg : ContinuousAt g x) :
    HasDerivAt (fun y => f y * g y) (f' * g x) x := by
  rw [hasDerivAt_iff_tendsto_slope] at hf ⊢
  have hprod := hf.mul (hg.mono_left nhdsWithin_le_nhds)
  refine hprod.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y _hy
  simp [slope, hf0]

/-! Promoted from Staging/hasDerivAt_one_sub_sq_at_zero_of_value_one.lean. -/


-- Generalization plan (G0):
-- concept/name: derivative of a normalized squared-complement at zero;
--   orig was quadraticScalarPeriodDenominator_hasDerivAt_zero
-- generality used: an arbitrary nontrivially normed field, a scalar function,
--   and pointwise value and derivative hypotheses; no measure, convexity,
--   smoothness, oracle, or finite-dimensional assumptions
-- portable call pattern: stability, resolvent, and geometric-quotient proofs
--   differentiate `1 - Gamma^2` while changing the multiplier `Gamma` and its
--   first-order decay coefficient
-- counterargument checked: Mathlib supplies the power and constant-subtraction
--   derivative rules separately, but no theorem packages the normalized value-one,
--   negative-derivative contract that yields the positive doubled coefficient
-- coverage search: queries "derivative one minus square at point from function
--   value and derivative" and "HasDerivAt pow square derivative"; Mathlib
--   `HasDerivAt.fun_pow` and `HasDerivAt.const_sub` are partial coverage, and
--   SOptLib and this round's registry contain no full statement match
-- minimal hypotheses: both hypotheses are pointwise and used; the source's
--   algorithm setup, finite index type, and classical reasoning are unnecessary

/-- If a scalar function equals one at zero and has derivative `-d` there, then
`1 - Gamma^2` has derivative `2 * d` at zero.

Layer: Glue | Gap: Level 0 (normalized squared-complement derivative at zero)
Proof: apply Mathlib's power derivative rule, subtract the resulting square from one, and simplify using the value-one hypothesis.
Source: Mathlib one-variable calculus `HasDerivAt.fun_pow` and `HasDerivAt.sub`
Used in: stability, resolvent, and geometric-quotient expansions of a normalized multiplier with a positive first-order decay coefficient
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/15/proof/3
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem hasDerivAt_one_sub_sq_at_zero_of_value_one
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] (Gamma : 𝕜 → 𝕜) (d : 𝕜)
    (hGamma : HasDerivAt Gamma (-d) 0) (hGamma0 : Gamma 0 = 1) :
    HasDerivAt (fun x : 𝕜 ↦ 1 - Gamma x ^ 2) (2 * d) 0 := by
  have hsq := hGamma.fun_pow 2
  have hsq' : HasDerivAt (fun x : 𝕜 ↦ Gamma x ^ 2) (-2 * d) 0 := by
    convert hsq using 1
    rw [hGamma0]
    ring
  have hden := HasDerivAt.sub (hasDerivAt_const (0 : 𝕜) (1 : 𝕜)) hsq'
  convert hden using 1
  all_goals ring

/-! Promoted from Staging/hasDerivAt_finset_prod_one_sub_mul_zero.lean. -/


open scoped BigOperators

-- Generalization plan (G0):
-- concept/name: derivative at zero of a finite product of normalized affine factors;
--   orig was quadraticScalarPeriodMultiplier_hasDerivAt_zero
-- generality used: an arbitrary finite set of indices and coefficient family over a
--   nontrivially normed field; no measure, convexity, smoothness, oracle, or
--   finite-dimensional assumptions
-- portable call pattern: periodic stability and perturbation proofs differentiate a
--   normalized product while changing the finite phase set and its coefficient family
-- counterargument checked: this is not paper-local traceability or a pure wrapper;
--   Mathlib's product rule leaves an erase-product sum, while this theorem packages the
--   reusable zero-point simplification to the negative coefficient sum
-- coverage search: queries "derivative at zero finite product one minus variable times
--   coefficients equals negative sum" and "HasDerivAt finset product affine factors";
--   Mathlib HasDerivAt.finset_prod is partial coverage, and SOptLib has no full match
-- minimal hypotheses: all already minimal; an explicit Finset removes the source's
--   unnecessary Fintype and Nonempty assumptions

/-- The derivative at zero of a finite product of factors `1 - x * d i` is the
negative sum of their coefficients.

Layer: Glue | Gap: Level 0 (normalized affine finite-product derivative at zero)
Proof: apply Mathlib's finite-product derivative rule to the affine factors, then
  simplify every complementary factor at zero and collect the negative sum.
Source: Mathlib one-variable derivative rules for finite products and affine functions
Used in: periodic stability and perturbation expansions of a normalized multiplier over a finite phase set
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/15/proof/0
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem hasDerivAt_finset_prod_one_sub_mul_zero
    {𝕜 I : Type*} [NontriviallyNormedField 𝕜] (s : Finset I) (d : I → 𝕜) :
    HasDerivAt (fun x : 𝕜 ↦ ∏ i ∈ s, (1 - x * d i))
      (-(∑ i ∈ s, d i)) 0 := by
  classical
  have hraw :=
    HasDerivAt.fun_finset_prod
      (u := s)
      (f := fun (i : I) (x : 𝕜) ↦ 1 - x * d i)
      (f' := fun i ↦ -d i)
      (x := (0 : 𝕜)) (by
        intro i _hi
        have hlin : HasDerivAt (fun x : 𝕜 ↦ x * d i) (d i) 0 := by
          simpa using ((hasDerivAt_id' (0 : 𝕜)).mul_const (d i))
        have hsub := hlin.hasFDerivAt.const_sub 1
        simpa using hsub.hasDerivAt)
  simpa using hraw

/-! Promoted from Staging/HasDerivAt_eigenvalue_eq_left_apply_operator_deriv.lean. -/


-- Generalization plan (G0):
-- concept/name: derivative of an eigenvalue branch paired with a normalized left eigenfunctional; orig was simple_eigenvalue_branch_derivative_pairing
-- generality used: a normed space over an arbitrary nontrivially normed field, a differentiable continuous-linear operator family, scalar eigenvalue branch, vector eigenbranch, and a base point; no completeness or finite-dimensional assumptions
-- portable call pattern: spectral perturbation, Markov-chain sensitivity, and distributed-consensus linearization arguments vary the operator family, base eigenvalue, eigenvector branches, and normalized left-right pair while reusing the same eigenvalue derivative formula
-- counterargument checked: this is not paper-local traceability or a one-line rename; it combines the continuous-linear application product rule, eventual eigenpair identity, derivative uniqueness, and left-eigenfunctional cancellation into a reusable sensitivity theorem
-- coverage search: queries "eigenvalue derivative equals left functional applied to operator derivative normalized left right eigenvectors" and "differentiate operator eigenvector equation pair left eigenfunctional cancellation" found only the paper-local declaration; Mathlib LeanSearch found derivative primitives but no eigenvalue-sensitivity theorem, while HasDerivAt.clm_apply and HasDerivAt.smul cover only component steps
-- minimal hypotheses: pointwise derivatives at an arbitrary base point, an eventual eigenpair equation, the base right-vector identity, a normalized left-right pairing, and the pointwise cancellation of the eigenvector-derivative term; all are used and no finite-dimensional or simplicity hypothesis is required

/-- The derivative of a differentiable eigenvalue branch is the normalized left
eigenfunctional applied to the operator derivative on the base right eigenvector.

Layer: Glue | Gap: Level 1 (normalized eigenvalue-branch sensitivity identity)
Proof: differentiate the operator application and scalar-vector product with Mathlib's continuous-linear application and smul rules, identify their derivatives using the eventual eigenpair equation, then apply the normalized left eigenfunctional and cancel the eigenvector-derivative terms.
Source: Mathlib `HasDerivAt.clm_apply`, `HasDerivAt.smul`, and derivative uniqueness; standard first-order perturbation theory for a simple eigenvalue
Used in: spectral perturbation and distributed-consensus linearization steps that recover a slow-mode multiplier derivative from normalized left and right base modes
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12/proof/4
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, periodic spectral decomposition -/
theorem HasDerivAt.eigenvalue_eq_left_apply_operator_deriv
    {𝕜 V : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    {A : 𝕜 → (V →L[𝕜] V)} {gamma : 𝕜 → 𝕜} {r : 𝕜 → V}
    {x gammaDeriv : 𝕜} {Aderiv : V →L[𝕜] V}
    {rderiv right : V} {left : V →L[𝕜] 𝕜}
    (hA : HasDerivAt A Aderiv x)
    (hgamma : HasDerivAt gamma gammaDeriv x)
    (hr : HasDerivAt r rderiv x)
    (hcancel : left (A x rderiv) = gamma x * left rderiv)
    (hright : r x = right)
    (hnormalized : left right = 1)
    (heigen : ∀ᶠ t : 𝕜 in nhds x, A t (r t) = gamma t • r t) :
    HasDerivAt gamma (left (Aderiv right)) x := by
  have hoperatorDeriv :
      HasDerivAt (fun t : 𝕜 => A t (r t))
        (Aderiv (r x) + A x rderiv) x :=
    hA.clm_apply hr
  have heigenvalueDeriv :
      HasDerivAt (fun t : 𝕜 => gamma t • r t)
        (gamma x • rderiv + gammaDeriv • r x) x := by
    simpa only [Pi.smul_apply] using hgamma.smul hr
  have hderivEq :
      Aderiv (r x) + A x rderiv =
        gamma x • rderiv + gammaDeriv • r x :=
    hoperatorDeriv.unique (heigenvalueDeriv.congr_of_eventuallyEq heigen)
  have hpaired := congrArg left hderivEq
  rw [hright] at hpaired
  simp only [map_add, map_smul, smul_eq_mul, hcancel, hnormalized, mul_one]
    at hpaired
  have hgammaDeriv : gammaDeriv = left (Aderiv right) := by
    have hcancelled :
        gamma x * left rderiv + left (Aderiv right) =
          gamma x * left rderiv + gammaDeriv := by
      calc
        gamma x * left rderiv + left (Aderiv right) =
            left (Aderiv right) + gamma x * left rderiv := add_comm _ _
        _ = gamma x * left rderiv + gammaDeriv := hpaired
    exact (add_left_cancel hcancelled).symm
  exact hgamma.congr_deriv hgammaDeriv

/-! Promoted from Staging/eventuallyAnalytic_eigenbranch_hasDerivAt_pairing.lean. -/


open Filter Topology

-- Generalization plan (G0):
-- concept/name: derivative existence and left-right eigenvalue sensitivity from pointwise differentiability; orig was normalized_eigenbranch_derivative_pairing_eventual
-- generality used: an arbitrary nontrivially normed field, normed operator and vector spaces, a continuous-linear representation of operators as endomorphisms, pointwise differentiable operator/scalar/vector families at an arbitrary base point, and a local eigenpair equation; no completeness or finite-dimensional assumptions
-- portable call pattern: differentiable perturbation proofs for matrix or abstract stochastic transition, consensus, preconditioner, and Hessian operators vary the operator representation, family, base point, eigenvalue, eigenvectors, and normalization functional while retaining the same derivative-existence and sensitivity conclusion
-- counterargument checked: the existing HasDerivAt eigenvalue-sensitivity theorem covers the final identity only after all derivative witnesses are supplied; this theorem is not a pure rename because it extracts those witnesses from pointwise differentiability and packages the recurring one-call perturbation step
-- coverage search: a symbol query for existence of the operator derivative and the left-functional eigenvalue formula from pointwise differentiability and a local eigenpair equation found HasDerivAt.eigenvalue_eq_left_apply_operator_deriv as a component but no theorem deriving all witnesses from those premises
-- minimal hypotheses: the operator, scalar, and vector families are differentiable only at the base point; the eigenpair equation is eventual near that point; normalization is pointwise, and the left-eigenfunctional relation is stated directly as continuous-linear-map composition

/-- Pointwise differentiability and a local eigenpair equation give an operator
derivative witness and identify the eigenvalue derivative by applying a normalized
left eigenfunctional to the operator derivative at the right eigenvector.

Layer: Glue | Gap: Level 1 (derivative extraction and normalized eigenvalue sensitivity)
Proof: extract derivative witnesses from `DifferentiableAt.hasDerivAt` and apply `HasDerivAt.eigenvalue_eq_left_apply_operator_deriv` after deriving the left-eigenfunctional cancellation.
Source: Mathlib Fréchet calculus and standard first-order perturbation theory for a normalized eigenvalue branch
Used in: differentiable perturbation of stochastic transition, distributed-consensus, preconditioner, and Hessian operators when converting a local eigenpair equation into a scalar sensitivity formula
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/12/proof/4
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, periodic spectral decomposition -/
theorem exists_hasDerivAt_eigenvalue_eq_left_apply_operator_deriv_of_differentiableAt
    {𝕜 Operator V : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup Operator] [NormedSpace 𝕜 Operator]
    [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    (toOperator : Operator →L[𝕜] (V →L[𝕜] V))
    (A : 𝕜 → Operator) (gamma : 𝕜 → 𝕜) (r : 𝕜 → V)
    (x lambda0 : 𝕜) (right : V) (left : V →L[𝕜] 𝕜)
    (hA : DifferentiableAt 𝕜 A x)
    (hgamma : DifferentiableAt 𝕜 gamma x)
    (hr : DifferentiableAt 𝕜 r x)
    (hleft : left.comp (toOperator (A x)) = lambda0 • left)
    (hright : r x = right)
    (hnormalized : left right = 1)
    (hgamma0 : gamma x = lambda0)
    (heigen : ∀ᶠ t : 𝕜 in nhds x,
      toOperator (A t) (r t) = gamma t • r t) :
    ∃ Aderiv : Operator,
      HasDerivAt A Aderiv x ∧
        HasDerivAt gamma (left (toOperator Aderiv right)) x := by
  obtain ⟨Aderiv, hAderiv⟩ :
      ∃ Aderiv : Operator, HasDerivAt A Aderiv x :=
    ⟨_, hA.hasDerivAt⟩
  have hAoperator :
      HasDerivAt (fun t => toOperator (A t)) (toOperator Aderiv) x :=
    (toOperator.hasFDerivAt :
      HasFDerivAt toOperator toOperator (A x)).comp_hasDerivAt x hAderiv
  have hgammaDeriv :
      HasDerivAt gamma ((fderiv 𝕜 gamma x) 1) x :=
    hgamma.hasDerivAt
  have hrDeriv :
      HasDerivAt r ((fderiv 𝕜 r x) 1) x :=
    hr.hasDerivAt
  have hcancel :
      left (toOperator (A x) ((fderiv 𝕜 r x) 1)) =
        gamma x * left ((fderiv 𝕜 r x) 1) := by
    simpa [hgamma0] using congrArg
      (fun L : V →L[𝕜] 𝕜 => L ((fderiv 𝕜 r x) 1)) hleft
  refine ⟨Aderiv, hAderiv, ?_⟩
  exact HasDerivAt.eigenvalue_eq_left_apply_operator_deriv
    hAoperator hgammaDeriv hrDeriv hcancel hright hnormalized heigen

/-! Promoted from Staging/HasDerivAt_left_eigenfunctional_apply_operator_deriv.lean. -/


-- Generalization plan (G0):
-- concept/name: product rule for a differentiable left eigenfunctional and operator family; orig was weightedState_left_eigenrow_derivative_pairing
-- generality used: an arbitrary nontrivially normed field, a normed vector space, differentiable continuous-linear operator and functional families, an arbitrary base point, and one fixed test vector; no completeness or finite-dimensional assumptions
-- portable call pattern: spectral perturbation, Markov-chain sensitivity, and distributed-consensus proofs vary the Banach space, operator family, multiplier branch, moving left eigenfunctional, base point, and test vector while reusing the differentiated left-eigenrelation identity
-- counterargument checked: this is not paper-local row bookkeeping or a pure wrapper; it packages two continuous-linear product rules, an eventual left-eigenfunctional relation, derivative uniqueness, and evaluation on a test vector, and it is dual to rather than duplicated by the staged right-eigenvector eigenvalue-sensitivity theorem
-- coverage search: queries "derivative moving left eigenfunctional composed operator equals multiplier functional derivative", "HasDerivAt continuous linear map composition operator product rule apply", and "continuous linear functional derivative applied moving vector product rule" found Mathlib's HasDerivAt.clm_comp and HasDerivAt.smul as component rules and the distinct staged HasDerivAt.eigenvalue_eq_left_apply_operator_deriv, but no theorem with this complete differentiated left-eigenrelation conclusion
-- minimal hypotheses: pointwise derivatives at the base point and an eventual left-eigenfunctional equation; the base multiplier is retained as gamma x, so no normalization, eigenvalue simplicity, completeness, or finite-dimensional hypothesis is needed

/-- Differentiating a moving left eigenfunctional relation and evaluating it on
a fixed vector gives the two operator-product terms and two multiplier-product
terms.

Layer: Glue | Gap: Level 1 (differentiated left-eigenfunctional relation)
Proof: apply Mathlib's continuous-linear composition and scalar-action product rules, identify their derivatives using the eventual eigenfunctional equation, and evaluate the resulting continuous-linear-map equality on the fixed vector.
Source: Mathlib `HasDerivAt.clm_comp`, `HasDerivAt.smul`, and derivative uniqueness; standard first-order spectral perturbation calculus
Used in: spectral perturbation and periodic distributed-consensus linearization steps that identify a moving projected left coordinate from the period-operator derivative and multiplier derivative
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/14/proof/2
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, quadratic slow-mode comparison -/
theorem HasDerivAt.left_eigenfunctional_apply_operator_deriv
    {𝕜 V : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    {A : 𝕜 → (V →L[𝕜] V)} {gamma : 𝕜 → 𝕜}
    {ell : 𝕜 → (V →L[𝕜] 𝕜)}
    {x gammaDeriv : 𝕜} {Aderiv : V →L[𝕜] V}
    {ellDeriv : V →L[𝕜] 𝕜}
    (hA : HasDerivAt A Aderiv x)
    (hgamma : HasDerivAt gamma gammaDeriv x)
    (hell : HasDerivAt ell ellDeriv x)
    (heigen : ∀ᶠ t : 𝕜 in nhds x, (ell t).comp (A t) = gamma t • ell t)
    (z : V) :
    ellDeriv (A x z) + ell x (Aderiv z) =
      gammaDeriv * ell x z + gamma x * ellDeriv z := by
  have hleft := hell.clm_comp hA
  have hright := hgamma.smul hell
  have hderiv := hleft.unique (hright.congr_of_eventuallyEq heigen)
  have hz := congrArg (fun f : V →L[𝕜] 𝕜 => f z) hderiv
  simpa [add_comm] using hz

/-! Promoted from Staging/HasDerivAt_clm_sub_apply_of_continuousAt.lean. -/


-- Generalization plan (G0):
-- concept/name: derivative of a centered continuous-linear-map path applied to a
--   continuous vector path; orig was weightedState_row_sub_hasDerivAt_zero_of_continuousAt
-- generality used: arbitrary nontrivially normed field and arbitrary normed domain and
--   codomain spaces; only pointwise derivative and continuity hypotheses at the base point
-- portable call pattern: perturbation and first-variation proofs where a differentiable
--   moving linear functional or operator is centered at its base value and applied to a
--   state path known only to be continuous; the spaces, operator path, state path, and base
--   point may change while the conclusion retains the same form
-- counterargument checked: not paper-local or a pure wrapper; Mathlib's application product
--   rule requires differentiability of both paths, whereas centering permits the strictly
--   weaker continuity hypothesis on the vector path
-- coverage search: queries "continuous linear map application derivative vanishing map
--   factor continuous vector" and "HasDerivAt clm apply continuousAt zero" found Mathlib
--   HasDerivAt.clm_apply and deriv_clm_apply, whose full signatures require differentiability
--   of the vector path; no Mathlib or SOptLib declaration has this mixed-regularity contract
-- minimal hypotheses: all hypotheses are pointwise; no completeness, finite-dimensional,
--   measure, convexity, inner-product, or global regularity assumptions are used

/-- A differentiable path of continuous linear maps, centered at its value at the base
point, can be applied to a merely continuous vector path; its derivative is the derivative
map applied to the base vector.

Layer: Glue | Gap: Level 1 (mixed-regularity derivative of centered operator application)
Proof: use the slope characterization of `HasDerivAt`; centering identifies the output slope
  with the operator-path slope applied to the vector path, and joint continuity of continuous
  linear map application passes both factors to their limits.
Source: Mathlib derivative slope characterization and continuous-linear-map application
  continuity in normed spaces
Used in: periodic push--pull first-variation arguments where a centered spectral row acts on
  a corrected state orbit that is continuous in the perturbation but need not be differentiable
Book citation: book/TimeVaryingPushPull/TimeVaryingPushPull.json#/key_lemmas/14/proof/2
Origin algorithm: Feiming Wang, Stochastic Push--Pull Gradient Tracking on Fixed Exogenous Periodic Directed Networks, TimeVaryingStochasticPushPull -/
theorem HasDerivAt.clm_sub_apply_of_continuousAt
    {𝕜 V W : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    {ell : 𝕜 → V →L[𝕜] W} {ell' : V →L[𝕜] W}
    {z : 𝕜 → V} {x : 𝕜}
    (hell : HasDerivAt ell ell' x) (hz : ContinuousAt z x) :
    HasDerivAt (fun y => (ell y - ell x) (z y)) (ell' (z x)) x := by
  rw [hasDerivAt_iff_tendsto_slope] at hell ⊢
  have hz' : Filter.Tendsto z (nhdsWithin x {x}ᶜ) (nhds (z x)) :=
    hz.mono_left nhdsWithin_le_nhds
  have hpair :
      Filter.Tendsto (fun y => (slope ell x y, z y)) (nhdsWithin x {x}ᶜ)
        (nhds (ell', z x)) :=
    by simpa only [nhds_prod_eq] using hell.prodMk hz'
  have happly : Continuous (fun p : (V →L[𝕜] W) × V => p.1 p.2) :=
    (isBoundedBilinearMap_apply (𝕜 := 𝕜) (E := V) (F := W)).continuous
  have happ :
      Filter.Tendsto (fun y => (slope ell x y) (z y)) (nhdsWithin x {x}ᶜ)
        (nhds (ell' (z x))) :=
    (happly.tendsto (ell', z x)).comp hpair
  refine happ.congr' ?_
  filter_upwards with y
  change
    ((y - x)⁻¹ • (ell y - ell x)) (z y) =
      (y - x)⁻¹ • ((ell y - ell x) (z y) - (ell x - ell x) (z x))
  simp only [sub_self, ContinuousLinearMap.zero_apply, sub_zero,
    ContinuousLinearMap.smul_apply]
