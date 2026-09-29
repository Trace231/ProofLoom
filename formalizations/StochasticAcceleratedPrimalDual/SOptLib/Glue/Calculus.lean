-- SOptLib/Glue/Calculus.lean
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Topology.Order.Basic


open Topology

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


open scoped InnerProductSpace

-- Generalization plan (G0):
-- concept/name: chain rule from a Hilbert-space gradient to the scalar derivative
--   along an affine segment; orig was hasDerivWithinAt_along_affine_segment_of_hasGradientAt_block.
-- generality used: a complete real inner-product space, a scalar function, two
--   segment endpoints, and one pointwise `HasGradientAt`; no measure,
--   filtration, convexity, oracle, or algorithm data.
-- portable call pattern: Bregman lower-bound and prox-step first-order proofs
--   in stochastic mirror descent, accelerated gradient, and primal-dual methods
--   can replace their local composition block while changing only the potential,
--   selected gradient, and segment endpoints.
-- counterargument checked: this is not paper traceability or a pure rename; it
--   packages a recurring nontrivial composition of the gradient/Frechet API with
--   affine line-map derivatives. Mathlib has the component lemmas but not this
--   endpoint segment specialization.
-- coverage search: queried `HasGradientAt hasDerivWithinAt lineMap zero`, direct
--   project `rg` for `HasGradientAt` plus `AffineMap.hasDerivWithinAt_lineMap`,
--   and LeanSearch for "HasGradientAt derivative of composition with lineMap at
--   zero inner product direction"; top hits were `AffineMap.hasDerivAt_lineMap`,
--   `AffineMap.hasDerivWithinAt_lineMap`, `HasGradientAt.hasFDerivAt`, and
--   line-derivative APIs, all partial rather than full coverage.
-- minimal hypotheses: pointwise `HasGradientAt` at the left endpoint is the only
--   smoothness hypothesis; finite-dimensionality is not used.

/-- A pointwise gradient gives the one-dimensional derivative along an affine segment.

For a scalar function on a real Hilbert space, if `grad` is a gradient of `v`
at the left endpoint `a`, then the restriction `t ↦ v (lineMap a b t)` has
right-within derivative `⟪grad, b - a⟫_ℝ` at `0` on `[0, 1]`.

Layer: Glue | Gap: Level 0 (gradient chain rule along affine segment)
Proof: compose the Frechet derivative supplied by `HasGradientAt` with
  Mathlib's derivative of `AffineMap.lineMap`, then rewrite the Hilbert dual
  action as the real inner product.
Source: Mathlib `HasGradientAt`, Frechet derivative chain rule, and affine
  line-map derivative APIs
Used in: stochastic mirror descent and accelerated primal-dual Bregman segment
  first-order calculations
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem HasGradientAt.hasDerivWithinAt_comp_lineMap_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {v : E → ℝ} {grad a b : E}
    (hgrad : HasGradientAt v grad a) :
    HasDerivWithinAt (fun t : ℝ => v (AffineMap.lineMap a b t))
      ⟪grad, b - a⟫_ℝ (Set.Icc (0 : ℝ) 1) 0 := by
  have hline :
      HasDerivWithinAt (fun t : ℝ => AffineMap.lineMap a b t)
        (b - a) (Set.Icc (0 : ℝ) 1) 0 := by
    simpa using
      (AffineMap.hasDerivWithinAt_lineMap (a := a) (b := b)
        (s := Set.Icc (0 : ℝ) 1) (x := (0 : ℝ)))
  have hcomp :=
    hgrad.hasFDerivAt.comp_hasDerivWithinAt_of_eq
      (x := (0 : ℝ)) hline (by simp)
  simpa [Function.comp_def, InnerProductSpace.toDual_apply_apply] using hcomp
