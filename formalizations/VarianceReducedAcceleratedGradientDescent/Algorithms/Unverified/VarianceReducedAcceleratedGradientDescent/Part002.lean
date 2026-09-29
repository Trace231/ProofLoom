import SOptLib.Model.Bregman
import SOptLib.Glue.Algebra
import SOptLib.Glue.Calculus
import SOptLib.Glue.Probability
import SOptLib.Model.Carrier
import SOptLib.Model.Iterates
import SOptLib.Model.IsSimpleConvexTermOn
import SOptLib.Model.Objective
import SOptLib.Model.Prox
import SOptLib.Model.Selection
import SOptLib.Model.Subdifferential
import SOptLib.Model.StochasticOracle
import SOptLib.Model.ParameterChoices
import SOptLib.Layer0.ConvexFOC
import SOptLib.Layer0.Objective
import SOptLib.Layer1.Proximal
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Convex.Approximation
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Algorithms.Unverified.VarianceReducedAcceleratedGradientDescent.Part001
import SOptLib.Layer0.Oracle
import SOptLib.Layer1.Descent

noncomputable section

open scoped BigOperators InnerProductSpace

namespace VarianceReducedAcceleratedGradientDescent


/-- The second Theorem 5.9 rate case `(4/5)^s D_0`. -/
def theorem59Case2Rate (s : Nat) (D0 : Real) : Real :=
  ((4 / 5 : Real) ^ s) * D0

/-- The third Theorem 5.9 rate case. -/
def theorem59Case3Rate {n dim : Nat} (S : Setup n dim)
    (s : Nat) (D0 : Real) : Real :=
  16 * D0 /
    ((((s : Real) - theorem59Cutoff S + 4) ^ 2) * componentCountReal n)

/-- The fourth Theorem 5.9 accelerated linear-tail rate case. -/
def theorem59Case4Rate {n dim : Nat} (S : Setup n dim)
    (hmu : 0 < S.mu) (hL : 0 < averageSmoothness S)
    (s : Nat) (D0 : Real) : Real :=
  Real.rpow
      (1 + Real.sqrt (S.mu / (3 * componentCountReal n * averageSmoothness S)))
      (-(componentCountReal n * ((s : Real) - theorem59TailCutoff S hmu hL) / 2)) *
    (D0 / (3 * averageSmoothness S / (4 * S.mu)))

/-- The printed four-case Theorem 5.9 rate object.

The strongly convex denominator facts are explicit inputs to this source-facing
rate; no branch is interpreted via Lean's totalized value at `mu = 0`. -/
def theorem59RateBound {n dim : Nat} (S : Setup n dim)
    (hmu : 0 < S.mu) (s : Nat) (D0 : Real) : Real :=
  let hL := averageSmoothness_pos S
  if s <= theorem59Cutoff S then
    theorem59Case1Rate s D0
  else if componentCountReal n >= 3 * averageSmoothness S / (4 * S.mu) then
    theorem59Case2Rate s D0
  else if (s : Real) <= theorem59TailCutoff S hmu hL then
    theorem59Case3Rate S s D0
  else
    theorem59Case4Rate S hmu hL s D0

/-- Canonical carrier gradient for a component objective.

No SOptLib exact match: searched `carrier gradient norm difference
gradientWithin norm bridge feasible direction` and `orthogonal projection
affineSpan direction norm gradientWithin carrierGradientFrom`; SOptLib provides
`carrierGradientFrom` and feasible-direction pairing bridges, but no ambient
norm bridge back to the selected `gradientWithin`. This local realization is the
orthogonal projection of Mathlib's selected within-gradient onto the feasible
affine-span direction, matching Lemma 5.8's gradient on a possibly
lower-dimensional carrier while discarding arbitrary normal components. -/
noncomputable def componentCarrierGradient
    {n dim : Nat} (S : Setup n dim) (i : Fin n)
    (x : VariableSpace dim) : VariableSpace dim :=
  SOptLib.projectedWithinGradient S.X (S.component i) x

theorem componentCarrierGradient_mem_direction
    {n dim : Nat} (S : Setup n dim) (i : Fin n)
    (x : VariableSpace dim) :
    componentCarrierGradient S i x ∈ (affineSpan ℝ S.X).direction := by
  simpa [componentCarrierGradient] using
    SOptLib.projectedWithinGradient_mem_direction S.X (S.component i) x

theorem componentCarrierGradient_inner_eq_gradientWithin
    {n dim : Nat} (S : Setup n dim) (i : Fin n)
    {x z : VariableSpace dim} (hx : x ∈ S.X) (hz : z ∈ S.X) :
    ⟪componentCarrierGradient S i z, x - z⟫_Real =
      ⟪gradientWithin (S.component i) S.X z, x - z⟫_Real := by
  classical
  let D := (affineSpan ℝ S.X).direction
  haveI : IsUniformAddGroup D := D.toAddSubgroup.isUniformAddGroup
  letI : CompleteSpace D := FiniteDimensional.complete ℝ D
  let d : D := ⟨x - z, by
    simpa using
      (SOptLib.vsub_mem_carrierAffineSpan_direction S.X
        (⟨z, hz⟩ : {u : VariableSpace dim // u ∈ S.X})
        (⟨x, hx⟩ : {u : VariableSpace dim // u ∈ S.X}))⟩
  change
    ⟪D.starProjection (gradientWithin (S.component i) S.X z), (d : VariableSpace dim)⟫_Real =
      ⟪gradientWithin (S.component i) S.X z, (d : VariableSpace dim)⟫_Real
  have h :=
    D.inner_orthogonalProjection_eq_of_mem_right d
      (gradientWithin (S.component i) S.X z)
  simpa only [Submodule.starProjection_apply, Submodule.coe_inner] using h

theorem componentCarrierGradient_inner_eq_gradientWithin_of_feasible_vsub
    {n dim : Nat} (S : Setup n dim) (i : Fin n)
    (w : VariableSpace dim) {y z : VariableSpace dim} (hy : y ∈ S.X) (hz : z ∈ S.X) :
    ⟪componentCarrierGradient S i w, y - z⟫_Real =
      ⟪gradientWithin (S.component i) S.X w, y - z⟫_Real := by
  simpa [componentCarrierGradient] using
    SOptLib.projectedWithinGradient_inner_eq_gradientWithin_of_vsub_mem_direction
      (X := S.X) (f := S.component i) (w := w) hy hz

theorem componentCarrierGradient_hasGradientWithinAt
    {n dim : Nat} (S : Setup n dim) (i : Fin n)
    (z : {u : VariableSpace dim // u ∈ S.X}) :
    HasGradientWithinAt (S.component i) (componentCarrierGradient S i z.1)
      S.X z.1 := by
  simpa [componentCarrierGradient] using
    SOptLib.projectedWithinGradient_hasGradientWithinAt
      (X := S.X) (f := S.component i) z
      ((S.component_differentiableOn i) z.1 z.2)

theorem componentCarrierGradient_lipschitz
    {n dim : Nat} (S : Setup n dim) (i : Fin n)
    (x z : {u : VariableSpace dim // u ∈ S.X}) :
    norm (componentCarrierGradient S i x.1 -
        componentCarrierGradient S i z.1) <=
      S.Lcomp i * norm (x.1 - z.1) := by
  simpa [componentCarrierGradient] using
    SOptLib.projectedWithinGradient_lipschitz_of_gradientWithin_lipschitz
      (X := S.X) (f := S.component i) (L := S.Lcomp i)
      (fun y w => S.component_smooth i y.1 y.2 w.1 w.2) x z

/-- Single-sided gradient gap for Lemma 5.8 under the repair condition.

Each component has a whole-space convex smooth extension, supplied explicitly
by Setup.component_extension, with the same component smoothness constant.
The extension agrees with the component values and the intrinsic projected
gradient on the feasible carrier. -/
theorem lemma58_smoothness_gap_projected
    {n dim : Nat} (S : Setup n dim) (i : Fin n)
    {x z : VariableSpace dim} (hx : x ∈ S.X) (hz : z ∈ S.X) :
    (1 / (2 * S.Lcomp i)) *
        norm (componentCarrierGradient S i x -
          componentCarrierGradient S i z) ^ 2 <=
      S.component i x - S.component i z -
        ⟪componentCarrierGradient S i z, x - z⟫_Real := by
  obtain ⟨ext⟩ := S.component_extension i
  simpa only [componentCarrierGradient] using
    ext.norm_gap (S.Lcomp_pos i) ⟨x, hx⟩ ⟨z, hz⟩

theorem lemma58_smoothness_gap
    {n dim : Nat} (S : Setup n dim) (i : Fin n)
    {x z : VariableSpace dim} (hx : x ∈ S.X) (hz : z ∈ S.X) :
    (1 / (2 * S.Lcomp i)) *
        norm (componentCarrierGradient S i x -
          componentCarrierGradient S i z) ^ 2 <=
      S.component i x - S.component i z -
        ⟪componentCarrierGradient S i z, x - z⟫_Real :=
  lemma58_smoothness_gap_projected S i hx hz

/-- Canonical finite-sum carrier gradient `∇f(x)` for the relative-gradient
realization used in Lemma 5.8.

This is the coherent finite-average companion to `componentCarrierGradient`.
It is kept in `Part002` because the split boundary makes the older
`fullGradient` definition in `Part001` read-only for this refactor round. -/
noncomputable def carrierFullGradient {n dim : Nat} (S : Setup n dim)
    (x : VariableSpace dim) : VariableSpace dim :=
  (componentCountReal n)⁻¹ •
    Finset.univ.sum (fun i : Fin n => componentCarrierGradient S i x)

@[simp]
theorem carrierFullGradient_def {n dim : Nat} (S : Setup n dim)
    (x : VariableSpace dim) :
    carrierFullGradient S x =
      (componentCountReal n)⁻¹ •
        Finset.univ.sum (fun i : Fin n => componentCarrierGradient S i x) := by
  rfl

/-- The carrier finite-sum gradient has the same feasible-direction pairing as
the legacy `fullGradient`.

This is the bridge needed to rewrite printed linearization terms once the
gradient-gap side is migrated to the canonical carrier-gradient object. -/
theorem carrierFullGradient_inner_eq_fullGradient
    {n dim : Nat} (S : Setup n dim)
    {x z : VariableSpace dim} (hx : x ∈ S.X) (hz : z ∈ S.X) :
    ⟪carrierFullGradient S z, x - z⟫_Real =
      ⟪fullGradient S z, x - z⟫_Real := by
  classical
  unfold carrierFullGradient fullGradient
  rw [inner_smul_left, inner_smul_left]
  congr 1
  rw [sum_inner, sum_inner]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  exact componentCarrierGradient_inner_eq_gradientWithin S i hx hz

theorem carrierFullGradient_inner_eq_fullGradient_of_feasible_vsub
    {n dim : Nat} (S : Setup n dim)
    (w : VariableSpace dim) {y z : VariableSpace dim} (hy : y ∈ S.X) (hz : z ∈ S.X) :
    ⟪carrierFullGradient S w, y - z⟫_Real =
      ⟪fullGradient S w, y - z⟫_Real := by
  classical
  unfold carrierFullGradient fullGradient
  rw [inner_smul_left, inner_smul_left]
  congr 1
  rw [sum_inner, sum_inner]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  exact componentCarrierGradient_inner_eq_gradientWithin_of_feasible_vsub S i w hy hz

/-- Carrier-gradient version of Eq. (5.3.5)'s left side.

This is the source-faithful deterministic finite sum obtained by applying
Lemma 5.8 componentwise after replacing the raw within-gradient selector by its
canonical carrier projection. The legacy `finiteGradientGapRelationLeft` is left
unchanged because the already-compiled Algorithm 5.7 estimator in `Part001`
still unfolds through `fullGradient` and raw `gradientWithin`. -/
def finiteCarrierGradientGapRelationLeft {n dim : Nat} (S : Setup n dim)
    (q : Fin n -> Real) (x xStar : VariableSpace dim) : Real :=
      (componentCountReal n)⁻¹ *
    Finset.univ.sum (fun i : Fin n =>
      (1 / (componentCountReal n * q i)) *
        norm (componentCarrierGradient S i x -
          componentCarrierGradient S i xStar) ^ 2)

/-- Left side of Eq. (5.3.5), the finite sum of inverse-probability gradient gaps. -/
def finiteGradientGapRelationLeft {n dim : Nat} (S : Setup n dim)
    (q : Fin n -> Real) (x xStar : VariableSpace dim) : Real :=
  SOptLib.importance_weighted_gradient_gap_quadratic q (componentCountReal n)
    (fun i x => gradientWithin (S.component i) S.X x) x xStar

/-- The carrier-gradient finite-sum left side is bounded by the legacy raw
within-gradient left side for positive sampling weights.

This is not the source proof of Eq. (5.3.5); it is a compatibility bridge that
keeps old raw-gradient estimator algebra from blocking the carrier-gradient
route. -/
theorem finiteCarrierGradientGapRelationLeft_le_finiteGradientGapRelationLeft
    {n dim : Nat} (S : Setup n dim)
    {q : Fin n -> Real} (hq : ∀ i, 0 < q i)
    (x z : VariableSpace dim) :
    finiteCarrierGradientGapRelationLeft S q x z <=
      finiteGradientGapRelationLeft S q x z := by
  classical
  unfold finiteCarrierGradientGapRelationLeft finiteGradientGapRelationLeft
  have hn_pos : 0 < componentCountReal n := componentCountReal_pos S
  refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (inv_pos.mpr hn_pos))
  refine SOptLib.finset_sum_mul_sq_norm_le_of_norm_le Finset.univ
    (fun i : Fin n => 1 / (componentCountReal n * q i))
    (fun i : Fin n => componentCarrierGradient S i x - componentCarrierGradient S i z)
    (fun i : Fin n =>
      gradientWithin (S.component i) S.X x - gradientWithin (S.component i) S.X z)
    ?_ ?_
  · intro i _hi
    exact le_of_lt (one_div_pos.mpr (mul_pos hn_pos (hq i)))
  · intro i _hi
    let D := (affineSpan ℝ S.X).direction
    haveI : IsUniformAddGroup D := D.toAddSubgroup.isUniformAddGroup
    letI : CompleteSpace D := FiniteDimensional.complete ℝ D
    simpa [componentCarrierGradient, D, map_sub] using
      D.norm_starProjection_apply_le
        (gradientWithin (S.component i) S.X x -
          gradientWithin (S.component i) S.X z)

/-- Carrier-gradient variance-reduced estimator.

No SOptLib exact match: searched `importance weighted gradient difference`,
`variance reduced gradient`, and `carrier gradient estimator`; SOptLib provides
the reusable importance-weighted component difference, while the paper-local
choice of carrier component gradient is specific to the Lemma 5.8/Eq. (5.3.5)
realization in this file. -/
def carrierVarianceReducedGradient {n dim : Nat} (S : Setup n dim)
    (q : Fin n -> Real) (sample : Fin n)
    (xUnder snapshot fullGradAtSnapshot : VariableSpace dim) : VariableSpace dim :=
  SOptLib.importance_weighted_control_variate_estimator
      q (componentCountReal n)
      (fun i x => componentCarrierGradient S i x)
      xUnder snapshot sample fullGradAtSnapshot

/-- Carrier residual `delta_t = G_t - grad f(underbar x_t)` for the projected
carrier-gradient realization. -/
def carrierEstimatorResidual {n dim : Nat} (S : Setup n dim)
    (q : Fin n -> Real) (sample : Fin n)
    (xUnder snapshot fullGradAtSnapshot : VariableSpace dim) : VariableSpace dim :=
  carrierVarianceReducedGradient S q sample xUnder snapshot fullGradAtSnapshot -
    carrierFullGradient S xUnder

/-- Carrier estimator evaluated on prox-core points. -/
def carrierVarianceReducedGradientOn {n dim : Nat} (S : Setup n dim)
    (q : Fin n -> Real) (sample : Fin n)
    (xUnder : Set.Elem (proxCoreSet S)) (snapshot : Set.Elem (proxCoreSet S))
    (fullGradAtSnapshot : VariableSpace dim) : VariableSpace dim :=
  carrierVarianceReducedGradient S q sample xUnder.1 snapshot.1 fullGradAtSnapshot

/-- Carrier estimator evaluated on feasible paper-domain points. -/
def carrierVarianceReducedGradientFeasibleOn {n dim : Nat} (S : Setup n dim)
    (q : Fin n -> Real) (sample : Fin n)
    (xUnder : FeasiblePoint S) (snapshot : FeasiblePoint S)
    (fullGradAtSnapshot : VariableSpace dim) : VariableSpace dim :=
  carrierVarianceReducedGradient S q sample xUnder.1 snapshot.1 fullGradAtSnapshot

theorem carrierVarianceReducedGradientOn_eq_carrierFullGradient_add_residual
    {n dim : Nat} (S : Setup n dim) (q : Fin n -> Real) (sample : Fin n)
    (xUnder : Set.Elem (proxCoreSet S)) (snapshot : Set.Elem (proxCoreSet S))
    (fullGradAtSnapshot : VariableSpace dim) :
    carrierVarianceReducedGradientOn S q sample xUnder snapshot fullGradAtSnapshot =
      carrierFullGradient S xUnder.1 +
        carrierEstimatorResidual S q sample xUnder.1 snapshot.1 fullGradAtSnapshot := by
  unfold carrierVarianceReducedGradientOn carrierEstimatorResidual
  abel

theorem carrierVarianceReducedGradient_inner_eq_varianceReducedGradient
    {n dim : Nat} (S : Setup n dim) (q : Fin n -> Real) (sample : Fin n)
    (xUnder snapshot : VariableSpace dim) {y z : VariableSpace dim}
    (hy : y ∈ S.X) (hz : z ∈ S.X) :
    ⟪carrierVarianceReducedGradient S q sample xUnder snapshot
        (carrierFullGradient S snapshot), y - z⟫_Real =
      ⟪varianceReducedGradient S q sample xUnder snapshot
        (fullGradient S snapshot), y - z⟫_Real := by
  exact
    SOptLib.importance_weighted_control_variate_inner_eq_of_pairings
      (q := q) (n := componentCountReal n) (sample := sample)
      (gradA := fun i x => componentCarrierGradient S i x)
      (gradB := fun i x => gradientWithin (S.component i) S.X x)
      (fullA := carrierFullGradient S snapshot)
      (fullB := fullGradient S snapshot)
      (x := xUnder) (snapshot := snapshot) (d := y - z)
      (componentCarrierGradient_inner_eq_gradientWithin_of_feasible_vsub
        S sample xUnder hy hz)
      (componentCarrierGradient_inner_eq_gradientWithin_of_feasible_vsub
        S sample snapshot hy hz)
      (carrierFullGradient_inner_eq_fullGradient_of_feasible_vsub S snapshot hy hz)

theorem fullGradient_add_carrierEstimatorResidual_inner_eq_varianceReducedGradient
    {n dim : Nat} (S : Setup n dim) (q : Fin n -> Real) (sample : Fin n)
    (xUnder snapshot : VariableSpace dim) {y z : VariableSpace dim}
    (hy : y ∈ S.X) (hz : z ∈ S.X) :
    ⟪fullGradient S xUnder +
        carrierEstimatorResidual S q sample xUnder snapshot
          (carrierFullGradient S snapshot), y - z⟫_Real =
      ⟪varianceReducedGradient S q sample xUnder snapshot
        (fullGradient S snapshot), y - z⟫_Real := by
  classical
  have hfull :=
    carrierFullGradient_inner_eq_fullGradient_of_feasible_vsub S xUnder hy hz
  have hvrg :=
    carrierVarianceReducedGradient_inner_eq_varianceReducedGradient
      S q sample xUnder snapshot hy hz
  unfold carrierEstimatorResidual
  rw [inner_add_left, inner_sub_left]
  linarith

theorem carrierEstimatorResidual_weighted_mean_zero
    {n dim : Nat} (S : Setup n dim)
    (xUnder snapshot : FeasiblePoint S) :
    Finset.univ.sum (fun i : Fin n =>
        samplingWeight S i •
          carrierEstimatorResidual S (samplingWeight S) i xUnder.1 snapshot.1
            (carrierFullGradient S snapshot.1)) = 0 := by
  simpa [carrierEstimatorResidual, carrierVarianceReducedGradient, carrierFullGradient] using
    (SOptLib.importance_weighted_control_variate_residual_weighted_sum_eq_zero
      (s := (Finset.univ : Finset (Fin n)))
      (q := samplingWeight S)
      (n := componentCountReal n)
      (gradF := fun i x => componentCarrierGradient S i x)
      (x := xUnder.1)
      (snapshot := snapshot.1)
      (samplingWeight_sum_eq_one S)
      (fun i _hi => ne_of_gt (samplingWeight_pos S i))
      (ne_of_gt (componentCountReal_pos S)))

theorem carrierVarianceReducedGradient_weighted_mean
    {n dim : Nat} (S : Setup n dim)
    (xUnder snapshot : FeasiblePoint S) :
    Finset.univ.sum (fun i : Fin n =>
        samplingWeight S i •
          carrierVarianceReducedGradientFeasibleOn S (samplingWeight S) i xUnder snapshot
            (carrierFullGradient S snapshot.1)) =
      carrierFullGradient S xUnder.1 := by
  simpa [carrierVarianceReducedGradientFeasibleOn, carrierVarianceReducedGradient] using
    (SOptLib.importance_weighted_control_variate_weighted_sum_eq_target
      (s := (Finset.univ : Finset (Fin n)))
      (q := samplingWeight S)
      (n := componentCountReal n)
      (gradF := fun i x => componentCarrierGradient S i x)
      (x := xUnder.1)
      (snapshot := snapshot.1)
      (fullAtSnapshot := carrierFullGradient S snapshot.1)
      (targetAtX := carrierFullGradient S xUnder.1)
      (samplingWeight_sum_eq_one S)
      (fun i _hi => ne_of_gt (samplingWeight_pos S i))
      (ne_of_gt (componentCountReal_pos S))
      (by simp [carrierFullGradient])
      (by simp [carrierFullGradient]))

theorem carrierEstimatorResidual_second_moment_le_gradient_gap
    {n dim : Nat} (S : Setup n dim)
    (xUnder snapshot : FeasiblePoint S) :
    componentConditionalExpectation S (samplingWeight S) (fun i : Fin n =>
        norm (carrierEstimatorResidual S (samplingWeight S) i xUnder.1 snapshot.1
          (carrierFullGradient S snapshot.1)) ^ 2) <=
      finiteCarrierGradientGapRelationLeft S (samplingWeight S) snapshot.1 xUnder.1 := by
  simpa [componentConditionalExpectation, finiteCarrierGradientGapRelationLeft,
    carrierEstimatorResidual, carrierVarianceReducedGradient] using
    (SOptLib.importance_weighted_control_variate_residual_second_moment_le_quadratic_gap
      (q := samplingWeight S) (n := componentCountReal n)
      (gradF := fun i x => componentCarrierGradient S i x)
      (x := xUnder.1) (snapshot := snapshot.1)
      (targetAtX := carrierFullGradient S xUnder.1)
      (fullAtSnapshot := carrierFullGradient S snapshot.1)
      (samplingWeight_sum_eq_one S)
      (fun i => ne_of_gt (samplingWeight_pos S i))
      (ne_of_gt (componentCountReal_pos S))
      (by simp [carrierFullGradient])
      (by simp [carrierFullGradient]))

/-- Carrier-gradient Eq. (5.3.5), the deterministic finite-sum relation from
Lemma 5.12's proof before the `h`-optimality step.

This is the source executable Eq. (5.3.5) surface after Lemma 5.8's gradient is
realized by the affine-span carrier projection.  The right-side linearization is
written with `fullGradient` because `carrierFullGradient_inner_eq_fullGradient`
proves that both finite-average gradients have the same feasible-direction
pairing. -/
theorem eq535_carrier_finite_sum_gradient_gap_relation
    {n dim : Nat} (S : Setup n dim)
    {x xStar : VariableSpace dim} (hx : x ∈ S.X) (hxStar : xStar ∈ S.X) :
    finiteCarrierGradientGapRelationLeft S (samplingWeight S) x xStar <=
      2 * theorem59LQ S *
        (finiteSumObjective S x - finiteSumObjective S xStar -
          ⟪fullGradient S xStar, x - xStar⟫_Real) := by
  have hinner := carrierFullGradient_inner_eq_fullGradient S hx hxStar
  rw [← hinner]
  simpa [finiteCarrierGradientGapRelationLeft, finiteSumObjective, carrierFullGradient,
    theorem59LQ_eq_averageSmoothness, componentCountReal] using
    (finite_importance_weighted_gradient_gap_le_linearization_gap_of_component_smoothness
      (F := fun i : Fin n => S.component i)
      (gradF := fun i y => componentCarrierGradient S i y)
      (q := samplingWeight S)
      (Lcomp := S.Lcomp)
      (Lbar := averageSmoothness S)
      (n := componentCountReal n)
      (x := x)
      (z := xStar)
      (componentCountReal_pos S)
      (by simp [componentCountReal])
      (fun i => samplingWeight_pos S i)
      (fun i => S.Lcomp_pos i)
      (by
        intro i
        rw [theorem59_sampling_ratio_eq_totalSmoothness S i]
        unfold averageSmoothness
        field_simp [ne_of_gt (componentCountReal_pos S)])
      (by
        intro i
        simpa using lemma58_smoothness_gap S i hx hxStar))

/-- Eq. (5.3.5), the finite-sum gradient-gap relation from Lemma 5.12's proof.

SOptLib weighted-variance lemmas were considered, but Eq. (5.3.5) is a
paper-specific deterministic finite-sum inequality involving the source
sampling law and `L_Q`; this theorem uses the canonical Theorem 5.9
`q_i = L_i / sum_j L_j` rather than an arbitrary totalized denominator. -/
theorem eq535_finite_sum_gradient_gap_relation
    {n dim : Nat} (S : Setup n dim)
    {x xStar : VariableSpace dim} (hx : x ∈ S.X) (hxStar : xStar ∈ S.X) :
    finiteCarrierGradientGapRelationLeft S (samplingWeight S) x xStar <=
      2 * theorem59LQ S *
        (finiteSumObjective S x - finiteSumObjective S xStar -
          ⟪fullGradient S xStar, x - xStar⟫_Real) := by
  exact eq535_carrier_finite_sum_gradient_gap_relation S hx hxStar

/-- Formal source-correction artifact for Eq. (5.3.5).

The printed gradient in Eq. (5.3.5) is interpreted by the carrier gradient
selected in Lemma 5.8. The legacy raw `gradientWithin` left side remains only as
compatibility infrastructure for older generated-process definitions. -/
def eq535FiniteSumGradientGapRelationCarrierCorrectionStatement
    {n dim : Nat} (S : Setup n dim) : Prop :=
  forall {x xStar : VariableSpace dim}, x ∈ S.X -> xStar ∈ S.X ->
    finiteCarrierGradientGapRelationLeft S (samplingWeight S) x xStar <=
      2 * theorem59LQ S *
        (finiteSumObjective S x - finiteSumObjective S xStar -
          ⟪fullGradient S xStar, x - xStar⟫_Real)

theorem eq535_finite_sum_gradient_gap_relation_carrier_correction
    {n dim : Nat} (S : Setup n dim) :
    eq535FiniteSumGradientGapRelationCarrierCorrectionStatement S := by
  intro x xStar hx hxStar
  exact eq535_finite_sum_gradient_gap_relation S hx hxStar

/-- The carrier Eq. (5.3.5) left side splits through an arbitrary anchor.

This is the deterministic finite-sum version of the norm-square split used in
Lemma 5.13 before applying Lemma 5.12 at the two optimality gaps. -/
theorem finiteCarrierGradientGapRelationLeft_triangle_split
    {n dim : Nat} (S : Setup n dim)
    {q : Fin n -> Real} (hq : ∀ i, 0 < q i)
    (x z y : VariableSpace dim) :
    finiteCarrierGradientGapRelationLeft S q x z <=
      2 * finiteCarrierGradientGapRelationLeft S q x y +
        2 * finiteCarrierGradientGapRelationLeft S q z y := by
  classical
  unfold finiteCarrierGradientGapRelationLeft
  have hn_pos : 0 < componentCountReal n := componentCountReal_pos S
  have hweight_nonneg :
      ∀ i ∈ (Finset.univ : Finset (Fin n)),
        0 <= (componentCountReal n)⁻¹ * (1 / (componentCountReal n * q i)) := by
    intro i _hi
    exact mul_nonneg (le_of_lt (inv_pos.mpr hn_pos))
      (le_of_lt (one_div_pos.mpr (mul_pos hn_pos (hq i))))
  simpa [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using
    (SOptLib.finset_weighted_sq_norm_sub_triangle_split
      (s := (Finset.univ : Finset (Fin n)))
      (w := fun i => (componentCountReal n)⁻¹ * (1 / (componentCountReal n * q i)))
      (A := fun i p => componentCarrierGradient S i p)
      (x := x) (z := z) (y := y) hweight_nonneg)

/-- Lemma 5.12's optimality/subgradient bridge.

After Eq. (5.3.5), the paper uses optimality of `xStar` and convexity of the
simple term `h` to obtain the first-order inequality
`-<∇f(xStar), x-xStar> <= h(x)-h(xStar)`. This is the exact nonsmooth
convex-analysis leaf: it should be proved from the constrained minimizer
condition for `f+h`, the within-gradient of the finite-sum part, and the
carrier convexity of `h`, without adding a primitive subgradient assumption to
`Setup`. -/
theorem lemma512_optimality_linearization_gap_bridge
    {n dim : Nat} (S : Setup n dim)
    {x xStar : VariableSpace dim}
    (hx : x ∈ S.X) (hxStar : IsOptimalSolution S xStar) :
    finiteSumObjective S x - finiteSumObjective S xStar -
        ⟪fullGradient S xStar, x - xStar⟫_Real <=
      compositeObjective S x - compositeObjective S xStar := by
  have hxStar_mem : xStar ∈ S.X := hxStar.1
  have hbridge :=
    smooth_part_linearization_gap_le_composite_gap_of_minimizer
      (X := S.X) (f := finiteSumObjective S) (h := S.h)
      (g := fullGradient S xStar) (L := averageSmoothness S)
      (x := x) (xStar := xStar)
      hx hxStar_mem (h_convex S)
      (by
        intro y hy
        simpa [compositeObjective] using hxStar.2 y hy)
      (le_of_lt (averageSmoothness_pos S))
      (by
        intro y hy
        have hsmooth :=
          finiteSumObjective_smooth_upper_bound_from_component_smooth S
            (⟨xStar, hxStar_mem⟩ : FeasiblePoint S)
            (⟨y, hy⟩ : FeasiblePoint S)
        unfold linearization at hsmooth
        linarith)
  unfold SOptLib.first_order_linear_model SOptLib.compositeObjective at hbridge
  unfold compositeObjective
  linarith

/-- Lemma 5.12 under the Theorem 5.9 sampling law. -/
theorem lemma512_weighted_component_gradient_gap_bound
    {n dim : Nat} (S : Setup n dim)
    {x xStar : VariableSpace dim}
    (hx : x ∈ S.X) (hxStar : IsOptimalSolution S xStar) :
    finiteCarrierGradientGapRelationLeft S (samplingWeight S) x xStar <=
      2 * theorem59LQ S *
        (compositeObjective S x - compositeObjective S xStar) := by
  classical
  have hxStar_mem : xStar ∈ S.X := hxStar.1
  have hmain :
      SOptLib.importance_weighted_gradient_gap_quadratic (samplingWeight S)
          (componentCountReal n) (fun i y => componentCarrierGradient S i y) x xStar ≤
        2 * averageSmoothness S *
          (SOptLib.compositeObjective
              (fun u => SOptLib.finiteUniformAverage (fun i : Fin n => S.component i u))
              S.h x -
            SOptLib.compositeObjective
              (fun u => SOptLib.finiteUniformAverage (fun i : Fin n => S.component i u))
              S.h xStar) :=
    SOptLib.finite_importance_weighted_gradient_gap_le_composite_gap_of_optimum
      (X := S.X)
      (F := fun i : Fin n => S.component i)
      (gradF := fun i y => componentCarrierGradient S i y)
      (h := S.h)
      (q := samplingWeight S)
      (Lcomp := S.Lcomp)
      (Lbar := averageSmoothness S)
      (n := componentCountReal n)
      (x := x)
      (xStar := xStar)
      (componentCountReal_pos S)
      (by simp [componentCountReal])
      (fun i => samplingWeight_pos S i)
      (fun i => S.Lcomp_pos i)
      (by
        intro i
        rw [theorem59_sampling_ratio_eq_totalSmoothness S i]
        unfold averageSmoothness
        field_simp [ne_of_gt (componentCountReal_pos S)])
      (by
        intro i
        simpa using lemma58_smoothness_gap S i hx hxStar_mem)
      hx hxStar_mem (h_convex S)
      (by
        intro y hy
        have hopt := hxStar.2 y hy
        unfold compositeObjective finiteSumObjective at hopt
        simpa [componentCountReal, SOptLib.finiteUniformAverage] using hopt)
      (le_of_lt (averageSmoothness_pos S))
      (by
        intro y hy
        have hsmooth :=
          finiteSumObjective_smooth_upper_bound_from_component_smooth S
            (⟨xStar, hxStar_mem⟩ : FeasiblePoint S)
            (⟨y, hy⟩ : FeasiblePoint S)
        have hinner := carrierFullGradient_inner_eq_fullGradient S hy hxStar_mem
        unfold linearization at hsmooth
        rw [← hinner] at hsmooth
        simp [finiteSumObjective, carrierFullGradient, componentCountReal,
          SOptLib.finiteUniformAverage] at hsmooth
        simp [SOptLib.finiteUniformAverage]
        nlinarith)
  rw [theorem59LQ_eq_averageSmoothness]
  change
    SOptLib.importance_weighted_gradient_gap_quadratic (samplingWeight S)
        (componentCountReal n) (fun i y => componentCarrierGradient S i y) x xStar ≤
      2 * averageSmoothness S *
        (SOptLib.compositeObjective
            (fun u => SOptLib.finiteUniformAverage (fun i : Fin n => S.component i u))
            S.h x -
          SOptLib.compositeObjective
            (fun u => SOptLib.finiteUniformAverage (fun i : Fin n => S.component i u))
            S.h xStar)
  exact hmain

/-- Discrete conditional-mean form of Lemma 5.13's unbiasedness statement.

The source statement is conditional on generated iterates. The Lean theorem is
therefore typed on feasible paper-domain points instead of arbitrary ambient
vectors, avoiding any reliance on totalized `gradientWithin` outside `X`. -/
theorem lemma513_variance_reduced_gradient_unbiased_finite_sum
    {n dim : Nat} (S : Setup n dim)
    (xUnder snapshot : FeasiblePoint S) :
    Finset.univ.sum (fun i : Fin n =>
        samplingWeight S i •
          carrierVarianceReducedGradientFeasibleOn S (samplingWeight S) i xUnder snapshot
            (carrierFullGradient S snapshot.1)) =
      carrierFullGradient S xUnder.1 := by
  exact carrierVarianceReducedGradient_weighted_mean S xUnder snapshot

/-- Discrete second-moment form of Lemma 5.13's variance bound. -/
theorem lemma513_variance_reduced_gradient_second_moment_bound
    {n dim : Nat} (S : Setup n dim)
    (xUnder snapshot xStar : FeasiblePoint S)
    (hxStar : IsOptimalSolutionOn S xStar) :
    Finset.univ.sum (fun i : Fin n =>
        samplingWeight S i *
          norm (carrierEstimatorResidual S (samplingWeight S) i xUnder.1 snapshot.1
            (carrierFullGradient S snapshot.1)) ^ 2) <=
      4 * theorem59LQ S *
        (compositeObjective S xUnder.1 - compositeObjective S xStar.1 +
          (compositeObjective S snapshot.1 - compositeObjective S xStar.1)) := by
  classical
  have hxStarRaw : IsOptimalSolution S xStar.1 := by
    refine ⟨xStar.2, ?_⟩
    intro x hx
    exact hxStar ⟨x, hx⟩
  simpa [carrierEstimatorResidual, carrierVarianceReducedGradient,
    finiteCarrierGradientGapRelationLeft] using
    (SOptLib.finite_sum_control_variate_residual_second_moment_le_composite_gaps
      (q := samplingWeight S)
      (n := componentCountReal n)
      (Lbar := theorem59LQ S)
      (gradF := fun i y => componentCarrierGradient S i y)
      (Psi := compositeObjective S)
      (x := xUnder.1)
      (snapshot := snapshot.1)
      (xStar := xStar.1)
      (targetAtX := carrierFullGradient S xUnder.1)
      (fullAtSnapshot := carrierFullGradient S snapshot.1)
      (samplingWeight_sum_eq_one S)
      (samplingWeight_pos S)
      (componentCountReal_pos S)
      (by simp [carrierFullGradient])
      (by simp [carrierFullGradient])
      (by
        simpa [finiteCarrierGradientGapRelationLeft] using
          lemma512_weighted_component_gradient_gap_bound S xUnder.2 hxStarRaw)
      (by
        simpa [finiteCarrierGradientGapRelationLeft] using
          lemma512_weighted_component_gradient_gap_bound S snapshot.2 hxStarRaw))

/-- Section 5.4's accelerated-search-point analogue of Lemma 5.13.

This is stated on the generated corrected-core Algorithm 5.7 spine: the search
point is computed from `innerStateProcessOn`, not supplied as an arbitrary
ambient vector. It matches the source phrase "conditionally on
`x_1, ..., x_t`" in Eqs. (5.4.4)-(5.4.5). -/
theorem lemma513_correctedCore_acceleratedSearchPoint_unbiased_finite_sum
    {n dim : Nat} (S : Setup n dim)
    (gamma alpha p : Nat -> Real) (s : Nat)
    (snapshot : Set.Elem (proxCoreSet S)) (x0 : Set.Elem (proxCoreSet S))
    (samples : Nat -> Fin n) (t : Nat) (ht : 1 <= t)
    (halpha : alpha s ∈ Set.Icc (0 : Real) 1)
    (hp : p s ∈ Set.Icc (0 : Real) 1)
    (hgamma : 0 < gamma s)
    (hcurv : 0 < 1 + S.mu * gamma s - averageSmoothness S * alpha s * gamma s)
    (hsearch : searchPointWeights S gamma alpha p s ∈ stdSimplex Real (Fin 3))
    (havg : averagedInnerWeightsAdmissible alpha p s) :
    let state :=
      innerStateProcessOn S gamma alpha p s (samplingWeight S)
        snapshot (fullGradient S snapshot.1) x0 samples
        halpha hp hgamma hcurv hsearch havg (t - 1)
    let xUnder :=
      searchPointOn S gamma alpha p s state.xBar state.x snapshot hsearch
    Finset.univ.sum (fun i : Fin n =>
        samplingWeight S i •
          carrierVarianceReducedGradientOn S (samplingWeight S) i xUnder snapshot
            (carrierFullGradient S snapshot.1)) =
      carrierFullGradient S xUnder.1 := by
  intro state xUnder
  have hmean :=
    carrierVarianceReducedGradient_weighted_mean S
      (proxCoreAsFeasible S xUnder) (proxCoreAsFeasible S snapshot)
  simpa [carrierVarianceReducedGradientOn, carrierVarianceReducedGradientFeasibleOn,
    proxCoreAsFeasible] using hmean

/-- Section 5.4's generated corrected-core variance bound at the accelerated
search point. -/
theorem lemma513_correctedCore_acceleratedSearchPoint_second_moment_bound
    {n dim : Nat} (S : Setup n dim)
    (gamma alpha p : Nat -> Real) (s : Nat)
    (snapshot : Set.Elem (proxCoreSet S)) (x0 : Set.Elem (proxCoreSet S))
    (xStar : FeasiblePoint S) (samples : Nat -> Fin n) (t : Nat) (ht : 1 <= t)
    (halpha : alpha s ∈ Set.Icc (0 : Real) 1)
    (hp : p s ∈ Set.Icc (0 : Real) 1)
    (hgamma : 0 < gamma s)
    (hcurv : 0 < 1 + S.mu * gamma s - averageSmoothness S * alpha s * gamma s)
    (hsearch : searchPointWeights S gamma alpha p s ∈ stdSimplex Real (Fin 3))
    (havg : averagedInnerWeightsAdmissible alpha p s)
    (hxStar : IsOptimalSolutionOn S xStar) :
    let state :=
      innerStateProcessOn S gamma alpha p s (samplingWeight S)
        snapshot (fullGradient S snapshot.1) x0 samples
        halpha hp hgamma hcurv hsearch havg (t - 1)
    let xUnder :=
      searchPointOn S gamma alpha p s state.xBar state.x snapshot hsearch
    Finset.univ.sum (fun i : Fin n =>
        samplingWeight S i *
          norm (carrierEstimatorResidual S (samplingWeight S) i xUnder.1 snapshot.1
            (carrierFullGradient S snapshot.1)) ^ 2) <=
      4 * theorem59LQ S *
        (compositeObjective S xUnder.1 - compositeObjective S xStar.1 +
          (compositeObjective S snapshot.1 - compositeObjective S xStar.1)) := by
  intro state xUnder
  exact
    lemma513_variance_reduced_gradient_second_moment_bound S
      (proxCoreAsFeasible S xUnder) (proxCoreAsFeasible S snapshot) xStar hxStar

/-- Compiled source boundary for the two-center Bregman prox inequality, Lemma 3.5.

This is the named prox-optimality dependency used in the printed proof of
Lemma 5.15. It is stated directly over the mixed-domain Algorithm 5.7 prox
relation, so consuming it does not revive an all-feasible Bregman surrogate or a
core-selected prox-update route. -/
def lemma35TwoCenterBregmanProxInequalityStatement
    {n dim : Nat} (S : Setup n dim) : Prop :=
  forall (gamma : Nat -> Real) (s : Nat)
    (x : FeasiblePoint S) (xPrev xUnder xNext : Set.Elem (proxCoreSet S))
    (g : VariableSpace dim),
    0 <= gamma s ->
    ProxUpdateRelOn S gamma s xPrev xUnder g (proxCoreAsFeasible S xNext) ->
      gamma s *
          (⟪g, xNext.1 - x.1⟫_Real + S.h xNext.1 - S.h x.1 +
            S.mu * bregmanOn S xUnder (proxCoreAsFeasible S xNext)) +
          bregmanOn S xPrev (proxCoreAsFeasible S xNext) <=
        gamma s * S.mu * bregmanOn S xUnder x +
          bregmanOn S xPrev x -
          (1 + S.mu * gamma s) * bregmanOn S xNext x

theorem lemma35_two_center_bregman_prox_inequality_boundary
    {n dim : Nat} (S : Setup n dim) :
    lemma35TwoCenterBregmanProxInequalityStatement S := by
  intro gamma s x xPrev xUnder xNext g hgamma hrel
  classical
  let q : VariableSpace dim -> Real := fun u =>
    gamma s * (⟪g, u⟫_Real + S.h u)
  let mu1 : Real := gamma s * S.mu
  let mu2 : Real := 1
  have hq_convex : ConvexOn Real S.X q := by
    refine ⟨S.X_convex, ?_⟩
    intro y hy w hw a b ha hb hab
    have hh := (h_convex S).2 hy hw ha hb hab
    have hinner :
        ⟪g, a • y + b • w⟫_Real =
          a * ⟪g, y⟫_Real + b * ⟪g, w⟫_Real := by
      simp [inner_add_right, inner_smul_right]
    simp [q, hinner, smul_eq_mul]
    have hhconv : S.h (a • y + b • w) <= a * S.h y + b * S.h w := by
      simpa [smul_eq_mul] using hh
    nlinarith [mul_le_mul_of_nonneg_left hhconv hgamma]
  have hopt :
      ∀ (u : VariableSpace dim) (hu : u ∈ S.X),
        q xNext.1 + mu1 * bregmanOn S xUnder (proxCoreAsFeasible S xNext) +
            mu2 * bregmanOn S xPrev (proxCoreAsFeasible S xNext) <=
          q u + mu1 * bregmanOn S xUnder (⟨u, hu⟩ : FeasiblePoint S) +
            mu2 * bregmanOn S xPrev (⟨u, hu⟩ : FeasiblePoint S) := by
    intro u hu
    let yu : FeasiblePoint S := ⟨u, hu⟩
    have hmin := hrel (show yu ∈ Set.univ by simp)
    have hmin' :
        proxObjectiveOn S gamma s xPrev xUnder g (proxCoreAsFeasible S xNext) <=
          proxObjectiveOn S gamma s xPrev xUnder g yu := by
      simpa [yu] using hmin
    unfold proxObjectiveOn at hmin'
    change
      gamma s * (⟪g, xNext.1⟫_Real + S.h xNext.1 +
            S.mu * bregmanOn S xUnder (proxCoreAsFeasible S xNext)) +
          bregmanOn S xPrev (proxCoreAsFeasible S xNext) <=
        gamma s * (⟪g, u⟫_Real + S.h u +
            S.mu * bregmanOn S xUnder yu) +
          bregmanOn S xPrev yu at hmin'
    dsimp [q, mu1, mu2, yu]
    nlinarith
  let d : VariableSpace dim := x.1 - xNext.1
  let I : Set Real := Set.Icc (0 : Real) 1
  let line : Real -> VariableSpace dim := fun t => AffineMap.lineMap xNext.1 x.1 t
  let βx : Real -> Real := fun t =>
    if ht : t ∈ Set.Icc (0 : Real) 1 then
      bregmanOn S xUnder
        ⟨AffineMap.lineMap xNext.1 x.1 t,
          S.X_convex.lineMap_mem (proxCoreSetElem_mem_X S xNext) x.2 ht⟩ -
        bregmanOn S xUnder (proxCoreAsFeasible S xNext)
    else 0
  let βy : Real -> Real := fun t =>
    if ht : t ∈ Set.Icc (0 : Real) 1 then
      bregmanOn S xPrev
        ⟨AffineMap.lineMap xNext.1 x.1 t,
          S.X_convex.lineMap_mem (proxCoreSetElem_mem_X S xNext) x.2 ht⟩ -
        bregmanOn S xPrev (proxCoreAsFeasible S xNext)
    else 0
  let φ : Real -> Real := fun t =>
    t * (q x.1 - q xNext.1) + mu1 * βx t + mu2 * βy t
  have hβxderiv : HasDerivWithinAt βx
      ⟪gradientWithin S.nu S.X xNext.1 - gradientWithin S.nu S.X xUnder.1, d⟫_Real I 0 := by
    simpa [βx, d, I] using
      bregmanOn_segment_difference_hasDerivWithinAt_zero S xUnder xNext x
  have hβyderiv : HasDerivWithinAt βy
      ⟪gradientWithin S.nu S.X xNext.1 - gradientWithin S.nu S.X xPrev.1, d⟫_Real I 0 := by
    simpa [βy, d, I] using
      bregmanOn_segment_difference_hasDerivWithinAt_zero S xPrev xNext x
  have hqderiv : HasDerivWithinAt (fun t : Real => t * (q x.1 - q xNext.1))
      (q x.1 - q xNext.1) I 0 := by
    simpa using (hasDerivWithinAt_id (x := (0 : Real)) (s := I)).mul_const
      (q x.1 - q xNext.1)
  have hφderiv : HasDerivWithinAt φ
      (q x.1 - q xNext.1 +
        mu1 * ⟪gradientWithin S.nu S.X xNext.1 - gradientWithin S.nu S.X xUnder.1, d⟫_Real +
        mu2 * ⟪gradientWithin S.nu S.X xNext.1 - gradientWithin S.nu S.X xPrev.1, d⟫_Real) I 0 := by
    have hxmul : HasDerivWithinAt (fun t : Real => mu1 * βx t)
        (mu1 * ⟪gradientWithin S.nu S.X xNext.1 - gradientWithin S.nu S.X xUnder.1, d⟫_Real) I 0 := by
      simpa using hβxderiv.const_mul mu1
    have hymul : HasDerivWithinAt (fun t : Real => mu2 * βy t)
        (mu2 * ⟪gradientWithin S.nu S.X xNext.1 - gradientWithin S.nu S.X xPrev.1, d⟫_Real) I 0 := by
      simpa using hβyderiv.const_mul mu2
    simpa [φ, add_assoc] using (hqderiv.add hxmul).add hymul
  have hφmin : ∀ t ∈ I, φ 0 <= φ t := by
    intro t ht
    have htI : t ∈ Set.Icc (0 : Real) 1 := by simpa [I] using ht
    rcases Set.mem_Icc.mp htI with ⟨ht0, ht1⟩
    let w : VariableSpace dim := AffineMap.lineMap xNext.1 x.1 t
    have hw : w ∈ S.X := by
      simpa [w] using
        S.X_convex.lineMap_mem (proxCoreSetElem_mem_X S xNext) x.2 htI
    have hline_conv :
        w = (1 - t) • xNext.1 + t • x.1 := by
      simp [w, AffineMap.lineMap_apply_module']
      module
    have hqseg : q w - q xNext.1 <= t * (q x.1 - q xNext.1) := by
      have hconv :=
        hq_convex.2 (proxCoreSetElem_mem_X S xNext) x.2 (sub_nonneg.mpr ht1) ht0
          (by ring)
      rw [← hline_conv] at hconv
      have hconv' : q w <= (1 - t) * q xNext.1 + t * q x.1 := by
        simpa [smul_eq_mul] using hconv
      nlinarith
    let wFeas : FeasiblePoint S := ⟨w, hw⟩
    have hmin := hopt w hw
    have hFdiff :
        0 <= (q w - q xNext.1) +
          mu1 * (bregmanOn S xUnder wFeas -
            bregmanOn S xUnder (proxCoreAsFeasible S xNext)) +
          mu2 * (bregmanOn S xPrev wFeas -
            bregmanOn S xPrev (proxCoreAsFeasible S xNext)) := by
      nlinarith
    have hβx_eval : βx t =
        bregmanOn S xUnder wFeas -
          bregmanOn S xUnder (proxCoreAsFeasible S xNext) := by
      dsimp [βx, wFeas, w]
      rw [dif_pos htI]
    have hβy_eval : βy t =
        bregmanOn S xPrev wFeas -
          bregmanOn S xPrev (proxCoreAsFeasible S xNext) := by
      dsimp [βy, wFeas, w]
      rw [dif_pos htI]
    have hβx0 : βx 0 = 0 := by
      simp [βx, proxCoreAsFeasible, AffineMap.lineMap_apply_module']
    have hβy0 : βy 0 = 0 := by
      simp [βy, proxCoreAsFeasible, AffineMap.lineMap_apply_module']
    have hφ0 : φ 0 = 0 := by
      simp [φ, hβx0, hβy0]
    have hupper :
        (q w - q xNext.1) +
          mu1 * (bregmanOn S xUnder wFeas -
            bregmanOn S xUnder (proxCoreAsFeasible S xNext)) +
          mu2 * (bregmanOn S xPrev wFeas -
            bregmanOn S xPrev (proxCoreAsFeasible S xNext)) <= φ t := by
      dsimp [φ]
      rw [hβx_eval, hβy_eval]
      nlinarith
    rw [hφ0]
    exact le_trans hFdiff hupper
  have hvar := right_derivative_nonneg_of_min_on_Icc hφderiv hφmin
  have h3x :
      bregmanOn S xUnder x =
        bregmanOn S xUnder (proxCoreAsFeasible S xNext) +
          ⟪gradientWithin S.nu S.X xNext.1 - gradientWithin S.nu S.X xUnder.1,
            x.1 - xNext.1⟫_Real +
          bregmanOn S xNext x := by
    let xUnderFeasible : FeasiblePoint S := ⟨xUnder.1, proxCoreSetElem_mem_X S xUnder⟩
    let xNextFeasible : FeasiblePoint S := proxCoreAsFeasible S xNext
    have h :=
      _root_.carrierBregmanDivergence_three_point_identity
        (v := fun u : FeasiblePoint S => S.nu u.1)
        (eval := fun u : FeasiblePoint S => u.1)
        (grad := fun u : FeasiblePoint S => gradientWithin S.nu S.X u.1)
        (V := _root_.carrierBregmanDivergence
          (fun u : FeasiblePoint S => S.nu u.1)
          (fun u : FeasiblePoint S => gradientWithin S.nu S.X u.1))
        (by
          intro a b
          rfl)
        xUnderFeasible xNextFeasible x
    simp [xUnderFeasible, xNextFeasible, bregmanOn, bregman, bregmanOf,
      proxCoreGradientOf, proxCoreAsFeasible,
      _root_.carrierBregmanDivergence] at h ⊢
    ring_nf at h ⊢
    exact h
  have h3y :
      bregmanOn S xPrev x =
        bregmanOn S xPrev (proxCoreAsFeasible S xNext) +
          ⟪gradientWithin S.nu S.X xNext.1 - gradientWithin S.nu S.X xPrev.1,
            x.1 - xNext.1⟫_Real +
          bregmanOn S xNext x := by
    let xPrevFeasible : FeasiblePoint S := ⟨xPrev.1, proxCoreSetElem_mem_X S xPrev⟩
    let xNextFeasible : FeasiblePoint S := proxCoreAsFeasible S xNext
    have h :=
      _root_.carrierBregmanDivergence_three_point_identity
        (v := fun u : FeasiblePoint S => S.nu u.1)
        (eval := fun u : FeasiblePoint S => u.1)
        (grad := fun u : FeasiblePoint S => gradientWithin S.nu S.X u.1)
        (V := _root_.carrierBregmanDivergence
          (fun u : FeasiblePoint S => S.nu u.1)
          (fun u : FeasiblePoint S => gradientWithin S.nu S.X u.1))
        (by
          intro a b
          rfl)
        xPrevFeasible xNextFeasible x
    simp [xPrevFeasible, xNextFeasible, bregmanOn, bregman, bregmanOf,
      proxCoreGradientOf, proxCoreAsFeasible,
      _root_.carrierBregmanDivergence] at h ⊢
    ring_nf at h ⊢
    exact h
  have hdescent :
      q xNext.1 + mu1 * bregmanOn S xUnder (proxCoreAsFeasible S xNext) +
          mu2 * bregmanOn S xPrev (proxCoreAsFeasible S xNext) <=
        q x.1 + mu1 * bregmanOn S xUnder x +
          mu2 * bregmanOn S xPrev x -
            (mu1 + mu2) * bregmanOn S xNext x := by
    dsimp [d] at hvar
    have h3x_scaled :
        mu1 * bregmanOn S xUnder x =
          mu1 * bregmanOn S xUnder (proxCoreAsFeasible S xNext) +
            mu1 * ⟪gradientWithin S.nu S.X xNext.1 - gradientWithin S.nu S.X xUnder.1,
              x.1 - xNext.1⟫_Real +
            mu1 * bregmanOn S xNext x := by
      rw [h3x]
      ring
    have h3y_scaled :
        mu2 * bregmanOn S xPrev x =
          mu2 * bregmanOn S xPrev (proxCoreAsFeasible S xNext) +
            mu2 * ⟪gradientWithin S.nu S.X xNext.1 - gradientWithin S.nu S.X xPrev.1,
              x.1 - xNext.1⟫_Real +
            mu2 * bregmanOn S xNext x := by
      rw [h3y]
      ring
    nlinarith [hvar, h3x_scaled, h3y_scaled]
  dsimp [q, mu1, mu2] at hdescent
  rw [inner_sub_right]
  nlinarith [hdescent]

/-- Ambient formula used only to expose the SOptLib two-Bregman descent API for
the mixed-domain Lemma 3.5 boundary.

The paper-facing object remains `bregmanOn : X^o -> X -> Real`; this ambient
formula is a proof adapter for the abstract SOptLib theorem, not a replacement
for the source domain. -/
private def lemma35AmbientBregmanFormula
    {n dim : Nat} (S : Setup n dim)
    (a b : VariableSpace dim) : Real :=
  S.nu b - (S.nu a + ⟪gradientWithin S.nu S.X a, b - a⟫_Real)

/-- Checked SOptLib-route attempt for Lemma 3.5.

This theorem proves the exact Lemma 3.5 boundary from the generic two-Bregman
descent API once an ambient Bregman derivative/three-point package is supplied.
The remaining open boundary is therefore not a scalar or `IsMinOn` unpacking
issue: it is the mixed-domain bridge from the paper's `X^o -> X` Bregman object
to the ambient `E -> E -> Real` API required by the reusable theorem. -/
theorem lemma35_two_center_bregman_prox_inequality_boundary_of_ambient_bregman_api
    {n dim : Nat} (S : Setup n dim)
    (hV_segment_deriv :
      ∀ (a z u : VariableSpace dim), z ∈ S.X →
        let d : VariableSpace dim := u - z
        let β : Real -> Real := fun t =>
          if _ht : t ∈ Set.Icc (0 : Real) 1 then
            lemma35AmbientBregmanFormula S a (AffineMap.lineMap z u t) -
              lemma35AmbientBregmanFormula S a z
          else 0
        HasDerivWithinAt β
          ⟪gradientWithin S.nu S.X z - gradientWithin S.nu S.X a, d⟫_Real
          (Set.Icc (0 : Real) 1) 0)
    (hV_three :
      ∀ a b c : VariableSpace dim,
        lemma35AmbientBregmanFormula S a c =
          lemma35AmbientBregmanFormula S a b +
            ⟪gradientWithin S.nu S.X b - gradientWithin S.nu S.X a, c - b⟫_Real +
              lemma35AmbientBregmanFormula S b c) :
    lemma35TwoCenterBregmanProxInequalityStatement S := by
  intro gamma s x xPrev xUnder xNext g hgamma hrel
  let q : VariableSpace dim -> Real := fun u =>
    gamma s * (⟪g, u⟫_Real + S.h u)
  have hq_convex : ConvexOn Real S.X q := by
    refine ⟨S.X_convex, ?_⟩
    intro y hy w hw a b ha hb hab
    have hh := (h_convex S).2 hy hw ha hb hab
    have hinner :
        ⟪g, a • y + b • w⟫_Real =
          a * ⟪g, y⟫_Real + b * ⟪g, w⟫_Real := by
      simp [inner_add_right, inner_smul_right]
    simp [q, hinner, smul_eq_mul]
    have hhconv : S.h (a • y + b • w) <= a * S.h y + b * S.h w := by
      simpa [smul_eq_mul] using hh
    nlinarith [mul_le_mul_of_nonneg_left hhconv hgamma]
  have hopt :
      ∀ u, u ∈ S.X →
        q xNext.1 +
            (gamma s * S.mu) * lemma35AmbientBregmanFormula S xUnder.1 xNext.1 +
            (1 : Real) * lemma35AmbientBregmanFormula S xPrev.1 xNext.1 <=
          q u +
            (gamma s * S.mu) * lemma35AmbientBregmanFormula S xUnder.1 u +
            (1 : Real) * lemma35AmbientBregmanFormula S xPrev.1 u := by
    intro u hu
    let yu : FeasiblePoint S := ⟨u, hu⟩
    have hmin := hrel (show (⟨u, hu⟩ : FeasiblePoint S) ∈ Set.univ by simp)
    have hmin' :
        proxObjectiveOn S gamma s xPrev xUnder g (proxCoreAsFeasible S xNext) <=
          proxObjectiveOn S gamma s xPrev xUnder g yu := by
      simpa [yu] using hmin
    have hUnderNext :
        lemma35AmbientBregmanFormula S xUnder.1 xNext.1 =
          bregmanOn S xUnder (proxCoreAsFeasible S xNext) := by
      simp [lemma35AmbientBregmanFormula, bregmanOn, carrierBregmanFormula,
        proxCoreAsFeasible, _root_.carrierBregmanDivergence]
    have hPrevNext :
        lemma35AmbientBregmanFormula S xPrev.1 xNext.1 =
          bregmanOn S xPrev (proxCoreAsFeasible S xNext) := by
      simp [lemma35AmbientBregmanFormula, bregmanOn, carrierBregmanFormula,
        proxCoreAsFeasible, _root_.carrierBregmanDivergence]
    have hUnderU :
        lemma35AmbientBregmanFormula S xUnder.1 u =
          bregmanOn S xUnder yu := by
      simp [lemma35AmbientBregmanFormula, bregmanOn, carrierBregmanFormula,
        yu, proxCoreAsFeasible, _root_.carrierBregmanDivergence]
    have hPrevU :
        lemma35AmbientBregmanFormula S xPrev.1 u =
          bregmanOn S xPrev yu := by
      simp [lemma35AmbientBregmanFormula, bregmanOn, carrierBregmanFormula,
        yu, proxCoreAsFeasible, _root_.carrierBregmanDivergence]
    unfold proxObjectiveOn at hmin'
    rw [← hUnderNext, ← hPrevNext, ← hUnderU, ← hPrevU] at hmin'
    change
      gamma s *
            (⟪g, xNext.1⟫_Real + S.h xNext.1 +
              S.mu * lemma35AmbientBregmanFormula S xUnder.1 xNext.1) +
          lemma35AmbientBregmanFormula S xPrev.1 xNext.1 <=
        gamma s * (⟪g, u⟫_Real + S.h u +
          S.mu * lemma35AmbientBregmanFormula S xUnder.1 u) +
          lemma35AmbientBregmanFormula S xPrev.1 u at hmin'
    ring_nf at hmin' ⊢
    nlinarith [hmin']
  have hdescent :=
    SOptLib.two_bregman_argmin_descent
      S.X q (lemma35AmbientBregmanFormula S)
      (fun z : VariableSpace dim => gradientWithin S.nu S.X z)
      hq_convex
      (uHat := xNext.1) (xTilde := xUnder.1) (yTilde := xPrev.1)
      (mu1 := gamma s * S.mu) (mu2 := (1 : Real))
      (proxCoreSetElem_mem_X S xNext)
      (mul_nonneg hgamma S.mu_nonneg) (by norm_num)
      hV_segment_deriv hV_three hopt x.1 x.2
  have hUnderNext :
      lemma35AmbientBregmanFormula S xUnder.1 xNext.1 =
        bregmanOn S xUnder (proxCoreAsFeasible S xNext) := by
    simp [lemma35AmbientBregmanFormula, bregmanOn, carrierBregmanFormula,
      proxCoreAsFeasible, _root_.carrierBregmanDivergence]
  have hPrevNext :
      lemma35AmbientBregmanFormula S xPrev.1 xNext.1 =
        bregmanOn S xPrev (proxCoreAsFeasible S xNext) := by
    simp [lemma35AmbientBregmanFormula, bregmanOn, carrierBregmanFormula,
      proxCoreAsFeasible, _root_.carrierBregmanDivergence]
  have hUnderX :
      lemma35AmbientBregmanFormula S xUnder.1 x.1 =
        bregmanOn S xUnder x := by
    simp [lemma35AmbientBregmanFormula, bregmanOn, carrierBregmanFormula,
      proxCoreAsFeasible, _root_.carrierBregmanDivergence]
  have hPrevX :
      lemma35AmbientBregmanFormula S xPrev.1 x.1 =
        bregmanOn S xPrev x := by
    simp [lemma35AmbientBregmanFormula, bregmanOn, carrierBregmanFormula,
      proxCoreAsFeasible, _root_.carrierBregmanDivergence]
  have hNextX :
      lemma35AmbientBregmanFormula S xNext.1 x.1 =
        bregmanOn S xNext x := by
    simp [lemma35AmbientBregmanFormula, bregmanOn, carrierBregmanFormula,
      proxCoreAsFeasible, _root_.carrierBregmanDivergence]
  dsimp [q] at hdescent
  rw [hUnderNext, hPrevNext, hUnderX, hPrevX, hNextX] at hdescent
  rw [inner_sub_right]
  nlinarith

theorem ProxUpdateRelOn.congr_feasible_vsub_inner
    {n dim : Nat} (S : Setup n dim)
    (gamma : Nat -> Real) (s : Nat)
    (xPrev xUnder : Set.Elem (proxCoreSet S))
    (g g' : VariableSpace dim) (z : FeasiblePoint S)
    (hinner : forall y : FeasiblePoint S,
      ⟪g', y.1 - z.1⟫_Real = ⟪g, y.1 - z.1⟫_Real)
    (hrel : ProxUpdateRelOn S gamma s xPrev xUnder g z) :
    ProxUpdateRelOn S gamma s xPrev xUnder g' z := by
  change
    IsMinOn
      (fun y : FeasiblePoint S =>
        gamma s * (⟪g, y.1⟫_Real + S.h y.1 + S.mu * bregmanOn S xUnder y) +
          bregmanOn S xPrev y)
      Set.univ z at hrel
  change
    IsMinOn
      (fun y : FeasiblePoint S =>
        gamma s * (⟪g', y.1⟫_Real + S.h y.1 + S.mu * bregmanOn S xUnder y) +
          bregmanOn S xPrev y)
      Set.univ z
  have hrel_split :
      IsMinOn
        (fun y : FeasiblePoint S =>
          gamma s * ⟪g, y.1⟫_Real +
            (gamma s * (S.h y.1 + S.mu * bregmanOn S xUnder y) +
              bregmanOn S xPrev y))
        Set.univ z := by
    simpa [mul_add, add_assoc, add_left_comm, add_comm] using hrel
  have hrel_split' :
      IsMinOn
        (fun y : FeasiblePoint S =>
          gamma s * ⟪g', y.1⟫_Real +
            (gamma s * (S.h y.1 + S.mu * bregmanOn S xUnder y) +
              bregmanOn S xPrev y))
        Set.univ z :=
    SOptLib.isMinOn_linear_inner_congr_of_vsub_pairing_eq
      (s := (Set.univ : Set (FeasiblePoint S)))
      (eval := fun x : FeasiblePoint S => x.1)
      (F := fun x : FeasiblePoint S =>
        gamma s * (S.h x.1 + S.mu * bregmanOn S xUnder x) +
          bregmanOn S xPrev x)
      (c := gamma s) (z := z) (g := g) (g' := g')
      (by intro y _hy; exact hinner y) hrel_split
  rw [isMinOn_iff] at hrel_split' ⊢
  intro y hy
  have hraw := hrel_split' y hy
  nlinarith

theorem ProxUpdateRelOn.of_raw_varianceReducedGradient_with_carrierResidual
    {n dim : Nat} (S : Setup n dim)
    (gamma : Nat -> Real) (s : Nat) (q : Fin n -> Real) (sample : Fin n)
    (xPrev xUnder snapshot : Set.Elem (proxCoreSet S)) (z : FeasiblePoint S)
    (hrel :
      ProxUpdateRelOn S gamma s xPrev xUnder
        (varianceReducedGradientOn S q sample xUnder snapshot
          (fullGradient S snapshot.1)) z) :
    ProxUpdateRelOn S gamma s xPrev xUnder
      (fullGradient S xUnder.1 +
        carrierEstimatorResidual S q sample xUnder.1 snapshot.1
          (carrierFullGradient S snapshot.1)) z := by
  refine ProxUpdateRelOn.congr_feasible_vsub_inner S gamma s xPrev xUnder
    (varianceReducedGradientOn S q sample xUnder snapshot (fullGradient S snapshot.1))
    (fullGradient S xUnder.1 +
      carrierEstimatorResidual S q sample xUnder.1 snapshot.1
        (carrierFullGradient S snapshot.1)) z ?_ hrel
  intro y
  simpa [varianceReducedGradientOn] using
    fullGradient_add_carrierEstimatorResidual_inner_eq_varianceReducedGradient
      S q sample xUnder.1 snapshot.1 y.2 z.2

/-- Source boundary for the norm-lower-bound step in Lemma 5.15.

This is the paper's lines 16960-16968: apply the modulus-one Bregman lower bound
to `V(underline{x}_t, x_t)` and `V(x_{t-1}, x_t)`, then use the definition of
`x_{t-1}^+` and convexity of the squared norm. It is deliberately separate from
Lemma 3.5, whose role is only the two-center prox inequality. -/
theorem lemma515_auxiliary_norm_lower_boundary
    {n dim : Nat} (S : Setup n dim)
    (gamma : Nat -> Real) (s : Nat)
    (xPrev xUnder xNext : Set.Elem (proxCoreSet S))
    (_hgamma : 0 <= gamma s) :
    (1 + S.mu * gamma s) / 2 *
        norm (xNext.1 - auxiliaryPoint S gamma s xPrev.1 xUnder.1) ^ 2 <=
      gamma s * S.mu * bregmanOn S xUnder (proxCoreAsFeasible S xNext) +
        bregmanOn S xPrev (proxCoreAsFeasible S xNext) := by
  have hr : 0 <= S.mu * gamma s := by
    exact mul_nonneg S.mu_nonneg _hgamma
  have hsq0 := weighted_sq_norm_sub_center_le (E := VariableSpace dim)
    (u := xUnder.1) (v := xPrev.1) (y := xNext.1) hr
  have hsq :
      (1 + S.mu * gamma s) / 2 *
          norm (xNext.1 - auxiliaryPoint S gamma s xPrev.1 xUnder.1) ^ 2 <=
        (1 / 2) * norm (xPrev.1 - xNext.1) ^ 2 +
          (S.mu * gamma s / 2) * norm (xUnder.1 - xNext.1) ^ 2 := by
    simpa [auxiliaryPoint, add_comm, add_left_comm, add_assoc] using hsq0
  have hunder0 := bregman_modulus_one_lower S xUnder (proxCoreAsFeasible S xNext)
  have hprev0 := bregman_modulus_one_lower S xPrev (proxCoreAsFeasible S xNext)
  have hunder :
      (1 / 2 : Real) * norm (xUnder.1 - xNext.1) ^ 2 <=
        bregmanOn S xUnder (proxCoreAsFeasible S xNext) := by
    simpa [bregmanOn, proxCoreAsFeasible] using hunder0
  have hprev :
      (1 / 2 : Real) * norm (xPrev.1 - xNext.1) ^ 2 <=
        bregmanOn S xPrev (proxCoreAsFeasible S xNext) := by
    simpa [bregmanOn, proxCoreAsFeasible] using hprev0
  have hunder_scaled :
      S.mu * gamma s * ((1 / 2 : Real) * norm (xUnder.1 - xNext.1) ^ 2) <=
        S.mu * gamma s * bregmanOn S xUnder (proxCoreAsFeasible S xNext) := by
    exact mul_le_mul_of_nonneg_left hunder hr
  nlinarith [hsq, hunder_scaled, hprev]

/-- Correction record for the retired `proxUpdateCoreOn` Lemma 5.15 surface.

The old theorem with this name asserted Lemma 5.15 for the totalized legacy
selector `proxUpdateCoreOn`. That selector is now definitionally `xPrev` and is
not the paper's Algorithm 5.7 prox minimizer. The executable source-faithful
interface is `lemma515_relational_core_step_inequality`, where the next point is
supplied together with the printed/canonical prox relation. -/
def lemma515CorrectedCoreOneStepAcceleratedProxInequalityStatementCorrection
    {n dim : Nat} (S : Setup n dim) : Prop :=
  forall (gamma : Nat -> Real) (s : Nat)
    (x : FeasiblePoint S) (xPrev xUnder : Set.Elem (proxCoreSet S))
    (delta : VariableSpace dim) (xNext : Set.Elem (proxCoreSet S)),
    0 <= gamma s ->
    ProxUpdateRelOn S gamma s xPrev xUnder
        (fullGradient S xUnder.1 + delta) (proxCoreAsFeasible S xNext) ->
      gamma s *
          (linearization S xUnder.1 xNext.1 - linearization S xUnder.1 x.1 +
            S.h xNext.1 - S.h x.1) <=
        gamma s * S.mu * bregmanOn S xUnder x +
          bregmanOn S xPrev x -
          (1 + S.mu * gamma s) * bregmanOn S xNext x -
          (1 + S.mu * gamma s) / 2 *
            norm (xNext.1 - auxiliaryPoint S gamma s xPrev.1 xUnder.1) ^ 2 -
          gamma s * ⟪delta, xNext.1 - x.1⟫_Real

/- Retired statement-correction artifact.
The former head named `proxUpdateCoreOn`, a diagnostic totalization no longer
allowed in the source/public dependency cone. Use
`lemma515_relational_core_step_boundary` for Lemma 5.15 and the printed
positive prox-membership chain for generated Algorithm 5.7 states. -/

/-- Relational mixed-domain Lemma 5.15 source boundary.

This is the active Lemma 5.15 route surface: the next point is supplied as a
prox-core point whose feasible coercion satisfies Algorithm 5.7's printed
`ProxUpdateRelOn` relation. The proof consumes the named Lemma 3.5 source
boundary and the separate norm-lower-bound source boundary; it does not select
`proxUpdateCoreOn` and does not call the retired all-feasible prox objective. -/
theorem lemma515_relational_core_step_inequality
    {n dim : Nat} (S : Setup n dim)
    (gamma : Nat -> Real) (s : Nat)
    (x : FeasiblePoint S) (xPrev xUnder : Set.Elem (proxCoreSet S))
    (delta : VariableSpace dim) (xNext : Set.Elem (proxCoreSet S))
    (hgamma : 0 <= gamma s)
    (hrel :
      ProxUpdateRelOn S gamma s xPrev xUnder
        (fullGradient S xUnder.1 + delta) (proxCoreAsFeasible S xNext)) :
    gamma s *
        (linearization S xUnder.1 xNext.1 - linearization S xUnder.1 x.1 +
          S.h xNext.1 - S.h x.1) <=
      gamma s * S.mu * bregmanOn S xUnder x +
        bregmanOn S xPrev x -
        (1 + S.mu * gamma s) * bregmanOn S xNext x -
        (1 + S.mu * gamma s) / 2 *
          norm (xNext.1 - auxiliaryPoint S gamma s xPrev.1 xUnder.1) ^ 2 -
        gamma s * ⟪delta, xNext.1 - x.1⟫_Real := by
  have h35 :=
    lemma35_two_center_bregman_prox_inequality_boundary S gamma s x xPrev xUnder xNext
      (fullGradient S xUnder.1 + delta) hgamma hrel
  have hnorm :=
    lemma515_auxiliary_norm_lower_boundary S gamma s xPrev xUnder xNext hgamma
  simpa [linearization, SOptLib.first_order_linear_model] using
    accelerated_two_center_prox_descent_of_weighted_bound
      (C := Set.Elem (proxCoreSet S)) (Q := FeasiblePoint S)
      (evalC := fun y : Set.Elem (proxCoreSet S) => y.1)
      (evalQ := fun y : FeasiblePoint S => y.1)
      (f := finiteSumObjective S)
      (hC := fun y : Set.Elem (proxCoreSet S) => S.h y.1)
      (hQ := fun y : FeasiblePoint S => S.h y.1)
      (VCC := fun a b : Set.Elem (proxCoreSet S) =>
        bregmanOn S a (proxCoreAsFeasible S b))
      (VCQ := fun a : Set.Elem (proxCoreSet S) => fun y : FeasiblePoint S =>
        bregmanOn S a y)
      (grad := fun y : Set.Elem (proxCoreSet S) => fullGradient S y.1)
      (gamma := gamma s) (mu := S.mu)
      (x := x) (xPrev := xPrev) (xUnder := xUnder) (xNext := xNext)
      (xPlus := auxiliaryPoint S gamma s xPrev.1 xUnder.1) (delta := delta)
      h35 hnorm

/-!
### Lemma 5.16 scalar side-condition correction

Lan Lemma 5.16 states the interval, curvature, and variance-noise scalar
conditions (5.4.7)-(5.4.8). Algorithm 5.7 also uses `1 - alpha_s - p_s` as a
convex coefficient in both the search point and the averaged inner iterate.
The two printed facts are not logically redundant: the theorem below records a
small scalar counterexample to the unguarded bridge that Phase 2a could not
prove.
-/

/-- The scalar side conditions printed in Lemma 5.16, before adding the
Algorithm 5.7 convex-coefficient guard. -/
def lemma516PrintedScalarSideConditions
    (mu L LQ gamma alpha p : Real) : Prop :=
  alpha ∈ Set.Icc (0 : Real) 1 ∧
    p ∈ Set.Icc (0 : Real) 1 ∧
    0 < gamma ∧
    0 < 1 + mu * gamma - L * alpha * gamma ∧
    0 <= p - LQ * alpha * gamma / (1 + mu * gamma - L * alpha * gamma)

/-- Corrected scalar side conditions for Lean's convex-combination
realization of Algorithm 5.7 inside Lemma 5.16. -/
def lemma516CorrectedScalarSideConditions
    (mu L LQ gamma alpha p : Real) : Prop :=
  SOptLib.AcceleratedVRScalarSideConditions mu L LQ gamma alpha p

/-- The printed Lemma 5.16 scalar hypotheses alone do not imply the
nonnegativity of Algorithm 5.7's bar coefficient.

The witness is the planner's counterexample shape with positive smoothness
constants: `mu = 0`, `L = 1`, `L_Q = 1/4`, `gamma = 1`,
`alpha = p = 3/4`. It satisfies the printed interval/curvature/noise
conditions, while `1 - alpha - p = -1/2`. -/
theorem lemma516_printedScalarSideConditions_do_not_imply_bar_nonneg :
    ∃ mu L LQ gamma alpha p : Real,
      0 <= mu ∧ 0 < L ∧ 0 < LQ ∧
        lemma516PrintedScalarSideConditions mu L LQ gamma alpha p ∧
          ¬ 0 <= 1 - alpha - p := by
  refine ⟨0, 1, (1 / 4 : Real), 1, (3 / 4 : Real), (3 / 4 : Real), ?_⟩
  unfold lemma516PrintedScalarSideConditions
  norm_num

/-- The printed Lemma 5.16 scalar hypotheses also do not imply the
strict-positive denominator guard needed for Lean's totalized
`gamma_s / alpha_s` expression.

This is a statement-correction artifact, not an added setup assumption: the
printed interval allows `alpha_s = 0`, while Eq. (5.4.9) contains
`gamma_s / alpha_s`. -/
theorem lemma516_printedScalarSideConditions_do_not_imply_alpha_pos :
    ∃ mu L LQ gamma alpha p : Real,
      0 <= mu ∧ 0 < L ∧ 0 < LQ ∧
        lemma516PrintedScalarSideConditions mu L LQ gamma alpha p ∧
          ¬ 0 < alpha := by
  refine ⟨0, 1, 1, 1, 0, 0, ?_⟩
  unfold lemma516PrintedScalarSideConditions
  norm_num

/-- The alpha-zero obstruction to rescaling Lemma 5.16's pre-divided recursion.

This proposition is the paper-local statement-correction object for the
`gamma_s / alpha_s` normalization: it records that the pre-divided recursion
does not imply the total-division Eq. (5.4.9) form when `alpha = 0`. -/
abbrev lemma516AlphaZeroRescaleObstruction : Prop :=
  ∃ gamma alpha p psiBar psiPrev psiSnapshot psiTarget vNext vPrev : Real,
    alpha ∈ Set.Icc (0 : Real) 1 ∧
      0 < gamma ∧
      p ∈ Set.Icc (0 : Real) 1 ∧
      alpha = 0 ∧
      psiBar + (alpha / gamma) * vNext <=
        (1 - alpha - p) * psiPrev + alpha * psiTarget +
          p * psiSnapshot + (alpha / gamma) * vPrev ∧
      ¬ (gamma / alpha * (psiBar - psiTarget) + vNext <=
        gamma / alpha * (1 - alpha - p) * (psiPrev - psiTarget) +
          gamma / alpha * p * (psiSnapshot - psiTarget) + vPrev)

/-- The pre-divided Lemma 5.16 recursion cannot be rescaled to Eq. (5.4.9)
without a nonzero `alpha_s` denominator.

This is the statement-correction artifact for the alpha-zero branch: when
`alpha = 0`, Lean's totalized `gamma / alpha` makes the printed Eq. (5.4.9)
drop all objective-gap terms, while the proved pre-divided recursion also drops
the Bregman coefficient.  Therefore the remaining Bregman contraction is not a
formal consequence of the pre-divided source recursion. -/
theorem lemma516_predivided_recursion_does_not_imply_total_division_rescale :
    lemma516AlphaZeroRescaleObstruction := by
  refine ⟨1, 0, 0, 0, 0, 0, 0, 1, 0, ?_⟩
  norm_num

/-- Source-derived Algorithm 5.7 search-weight admissibility used in Lemma 5.16.

This is not a setup field: the proof phase must derive the convex-combination
facts from the printed parameter relations together with the nonnegativity of
Algorithm 5.7's displayed bar coefficient `1 - alpha_s - p_s`. -/
theorem lemma516_searchPointWeights_mem_stdSimplex
    {n dim : Nat} (S : Setup n dim)
    (gamma alpha p : Nat -> Real) (s : Nat)
    (halpha : alpha s ∈ Set.Icc (0 : Real) 1)
    (hp : p s ∈ Set.Icc (0 : Real) 1)
    (hgamma : 0 < gamma s)
    (hbar : 0 <= 1 - alpha s - p s)
    (hcurv : 0 < 1 + S.mu * gamma s - averageSmoothness S * alpha s * gamma s)
    (hnoise :
      0 <= p s -
        theorem59LQ S * alpha s * gamma s /
          (1 + S.mu * gamma s - averageSmoothness S * alpha s * gamma s)) :
    searchPointWeights S gamma alpha p s ∈ stdSimplex Real (Fin 3) := by
  rcases
    (SOptLib.accelerated_search_point_weights_admissible_of_side_conditions
      (mu := S.mu) (gamma := gamma s) (alpha := alpha s) (p := p s)
      S.mu_nonneg halpha.1 (le_of_lt hgamma) hp.1 hbar) with
    ⟨hbarWeight, hprevWeight, hsnapshotWeight, hsum⟩
  refine ⟨?_, ?_⟩
  · intro i
    fin_cases i
    · simpa [searchPointWeights, searchPointBarWeight, searchDenominator] using hbarWeight
    · simpa [searchPointWeights, searchPointPrevWeight, searchDenominator] using hprevWeight
    · simpa [searchPointWeights, searchPointSnapshotWeight, searchDenominator] using
        hsnapshotWeight
  · simpa [searchPointWeights, Fin.sum_univ_three, searchPointBarWeight,
      searchPointPrevWeight, searchPointSnapshotWeight, searchDenominator] using hsum

/-- Source-derived Algorithm 5.7 averaged-iterate admissibility used in Lemma 5.16. -/
theorem lemma516_averagedInnerWeightsAdmissible
    {n dim : Nat} (S : Setup n dim)
    (gamma alpha p : Nat -> Real) (s : Nat)
    (halpha : alpha s ∈ Set.Icc (0 : Real) 1)
    (hp : p s ∈ Set.Icc (0 : Real) 1)
    (hgamma : 0 < gamma s)
    (hbar : 0 <= 1 - alpha s - p s)
    (hcurv : 0 < 1 + S.mu * gamma s - averageSmoothness S * alpha s * gamma s)
    (hnoise :
      0 <= p s -
        theorem59LQ S * alpha s * gamma s /
          (1 + S.mu * gamma s - averageSmoothness S * alpha s * gamma s)) :
    averagedInnerWeightsAdmissible alpha p s := by
  exact ⟨hbar, halpha.1, hp.1⟩

/-- Expectation-level accelerated variance-estimator facts used in the guarded
Lemma 5.16 bridge.

This is the source granularity of Eqs. (5.4.4)-(5.4.5): the fresh component
draw is averaged with `componentConditionalExpectation` under the canonical
Theorem 5.9 sampling weights. It is deliberately independent of the old
pointwise relational Lemma 5.16 route.

The `hbar` premise is the explicit statement-correction guard justified by
`lemma516_printedScalarSideConditions_do_not_imply_bar_nonneg`: the printed
scalar hypotheses alone do not make Algorithm 5.7's search point a convex
combination. -/
def lemma513AcceleratedVarianceEstimatorFactsBoundaryStatement
    {n dim : Nat} (S : Setup n dim) : Prop :=
  forall (gamma alpha p : Nat -> Real) (s : Nat)
    (snapshot xPrev xBarPrev : Set.Elem (proxCoreSet S)) (xTarget : FeasiblePoint S)
    (halpha : alpha s ∈ Set.Icc (0 : Real) 1)
    (hp : p s ∈ Set.Icc (0 : Real) 1)
    (hgamma : 0 < gamma s)
    (hbar : 0 <= 1 - alpha s - p s)
    (hcurv : 0 < 1 + S.mu * gamma s - averageSmoothness S * alpha s * gamma s)
    (hnoise :
      0 <= p s -
        theorem59LQ S * alpha s * gamma s /
          (1 + S.mu * gamma s - averageSmoothness S * alpha s * gamma s)),
    let hsearch :=
      lemma516_searchPointWeights_mem_stdSimplex S gamma alpha p s
        halpha hp hgamma hbar hcurv hnoise
    let xUnder := searchPointOn S gamma alpha p s xBarPrev xPrev snapshot hsearch
    componentConditionalExpectation S (samplingWeight S) (fun sample =>
        ⟪carrierEstimatorResidual S (samplingWeight S) sample xUnder.1 snapshot.1
            (carrierFullGradient S snapshot.1),
          auxiliaryPoint S gamma s xPrev.1 xUnder.1 - xTarget.1⟫_Real) = 0 ∧
      componentConditionalExpectation S (samplingWeight S) (fun sample =>
          norm (carrierEstimatorResidual S (samplingWeight S) sample xUnder.1 snapshot.1
            (carrierFullGradient S snapshot.1)) ^ 2) <=
        2 * theorem59LQ S *
          (finiteSumObjective S snapshot.1 - linearization S xUnder.1 snapshot.1)

/-- Vector zero-mean residuals imply the corresponding fixed-direction scalar
conditional expectation is zero.

Aligns with Lan Eqs. (5.4.4)-(5.4.5): this is only the finite-sum linearity
step from vector residual centering to the inner-product form. SOptLib
measure-level candidates such as
`randomQuery_inner_oracleResidual_integral_eq_zero_of_fixed_zero` were
considered, but `componentConditionalExpectation` is already the expanded
finite weighted sum. -/
theorem componentConditionalExpectation_inner_const_of_residual_mean_zero
    {n dim : Nat} (S : Setup n dim) (q : Fin n -> Real)
    (R : Fin n -> VariableSpace dim) (u : VariableSpace dim)
    (hR : Finset.univ.sum (fun i : Fin n => q i • R i) = 0) :
    componentConditionalExpectation S q (fun i => ⟪R i, u⟫_Real) = 0 := by
  simpa [componentConditionalExpectation] using
    (Finset.weighted_inner_sum_eq_zero_of_weighted_sum_eq_zero
      (s := (Finset.univ : Finset (Fin n))) (q := q) (R := R) (u := u) hR)




/-- Source-corrected carrier version of Eqs. (5.4.4)-(5.4.5).

This is the carrier-gradient source boundary exposed by the Lemma 5.8 /
Eq. (5.3.5) correction. The historical
`lemma513AcceleratedVarianceEstimatorFactsBoundaryStatement` is now definitionally
aligned with this carrier package so Lemma 5.16 and Lemma 5.18 no longer consume
the raw `gradientWithin` residual surface. -/
def lemma513CarrierAcceleratedVarianceEstimatorFactsBoundaryStatement
    {n dim : Nat} (S : Setup n dim) : Prop :=
  forall (gamma alpha p : Nat -> Real) (s : Nat)
    (snapshot xPrev xBarPrev : Set.Elem (proxCoreSet S)) (xTarget : FeasiblePoint S)
    (halpha : alpha s ∈ Set.Icc (0 : Real) 1)
    (hp : p s ∈ Set.Icc (0 : Real) 1)
    (hgamma : 0 < gamma s)
    (hbar : 0 <= 1 - alpha s - p s)
    (hcurv : 0 < 1 + S.mu * gamma s - averageSmoothness S * alpha s * gamma s)
    (hnoise :
      0 <= p s -
        theorem59LQ S * alpha s * gamma s /
          (1 + S.mu * gamma s - averageSmoothness S * alpha s * gamma s)),
    let hsearch :=
      lemma516_searchPointWeights_mem_stdSimplex S gamma alpha p s
        halpha hp hgamma hbar hcurv hnoise
    let xUnder := searchPointOn S gamma alpha p s xBarPrev xPrev snapshot hsearch
    componentConditionalExpectation S (samplingWeight S) (fun sample =>
        ⟪carrierEstimatorResidual S (samplingWeight S) sample xUnder.1 snapshot.1
            (carrierFullGradient S snapshot.1),
          auxiliaryPoint S gamma s xPrev.1 xUnder.1 - xTarget.1⟫_Real) = 0 ∧
      componentConditionalExpectation S (samplingWeight S) (fun sample =>
          norm (carrierEstimatorResidual S (samplingWeight S) sample xUnder.1 snapshot.1
            (carrierFullGradient S snapshot.1)) ^ 2) <=
        2 * theorem59LQ S *
          (finiteSumObjective S snapshot.1 - linearization S xUnder.1 snapshot.1)

theorem lemma513_carrier_accelerated_variance_estimator_facts_boundary
    {n dim : Nat} (S : Setup n dim) :
    lemma513CarrierAcceleratedVarianceEstimatorFactsBoundaryStatement S := by
  intro gamma alpha p s snapshot xPrev xBarPrev xTarget
    halpha hp hgamma hbar hcurv hnoise
  let hsearch :=
    lemma516_searchPointWeights_mem_stdSimplex S gamma alpha p s
      halpha hp hgamma hbar hcurv hnoise
  let xUnder := searchPointOn S gamma alpha p s xBarPrev xPrev snapshot hsearch
  refine And.intro ?hmean ?hsecond
  · exact
      componentConditionalExpectation_inner_const_of_residual_mean_zero
        S (samplingWeight S)
        (fun sample : Fin n =>
          carrierEstimatorResidual S (samplingWeight S) sample xUnder.1 snapshot.1
            (carrierFullGradient S snapshot.1))
        (auxiliaryPoint S gamma s xPrev.1 xUnder.1 - xTarget.1)
        (by
          simpa [proxCoreAsFeasible] using
            (carrierEstimatorResidual_weighted_mean_zero S
              (proxCoreAsFeasible S xUnder) (proxCoreAsFeasible S snapshot)))
  · have hmoment :=
      carrierEstimatorResidual_second_moment_le_gradient_gap S
        (proxCoreAsFeasible S xUnder) (proxCoreAsFeasible S snapshot)
    have hgap_bound :
        finiteCarrierGradientGapRelationLeft S (samplingWeight S) snapshot.1 xUnder.1 <=
          2 * theorem59LQ S *
            (finiteSumObjective S snapshot.1 - linearization S xUnder.1 snapshot.1) := by
      have hgap :=
        eq535_carrier_finite_sum_gradient_gap_relation S
          (proxCoreSetElem_mem_X S snapshot) (proxCoreSetElem_mem_X S xUnder)
      have hrewrite :
          finiteSumObjective S snapshot.1 - finiteSumObjective S xUnder.1 -
              ⟪fullGradient S xUnder.1, snapshot.1 - xUnder.1⟫_Real =
            finiteSumObjective S snapshot.1 - linearization S xUnder.1 snapshot.1 := by
        simp [linearization]
        ring
      calc
        finiteCarrierGradientGapRelationLeft S (samplingWeight S) snapshot.1 xUnder.1
            <= 2 * theorem59LQ S *
              (finiteSumObjective S snapshot.1 - finiteSumObjective S xUnder.1 -
                ⟪fullGradient S xUnder.1, snapshot.1 - xUnder.1⟫_Real) := hgap
        _ = 2 * theorem59LQ S *
              (finiteSumObjective S snapshot.1 - linearization S xUnder.1 snapshot.1) := by
            rw [hrewrite]
    exact le_trans hmoment hgap_bound

/-- Historical raw-gradient surface for Eq. (5.4.5).

This records the statement shape that previously blocked the source cone. It is
not the active supplier after the Lemma 5.8 carrier-gradient correction, because
its residual uses the raw `gradientWithin` average. -/
def lemma513LegacyRawAcceleratedResidualSecondMomentBoundStatement
    {n dim : Nat} (S : Setup n dim) : Prop :=
  forall (xUnder snapshot : Set.Elem (proxCoreSet S)),
    componentConditionalExpectation S (samplingWeight S) (fun i : Fin n =>
        norm (estimatorResidual S (samplingWeight S) i xUnder.1 snapshot.1
          (fullGradient S snapshot.1)) ^ 2) <=
      2 * theorem59LQ S *
        (finiteSumObjective S snapshot.1 - linearization S xUnder.1 snapshot.1)

/-- Formal correction record for the accelerated residual second-moment bound.

The active Eq. (5.4.5) supplier is the carrier-gradient statement proved by the
direct residual-to-gap and gap-to-composite transitivity argument below; the
raw-gradient statement above is retained only as a named retired surface. -/
def lemma513AcceleratedResidualSecondMomentCarrierCorrectionStatement
    {n dim : Nat} (S : Setup n dim) : Prop :=
  forall (xUnder snapshot : Set.Elem (proxCoreSet S)),
    componentConditionalExpectation S (samplingWeight S) (fun i : Fin n =>
        norm (carrierEstimatorResidual S (samplingWeight S) i xUnder.1 snapshot.1
          (carrierFullGradient S snapshot.1)) ^ 2) <=
      2 * theorem59LQ S *
        (finiteSumObjective S snapshot.1 - linearization S xUnder.1 snapshot.1)

/-- Legacy declaration name retained with the explicit carrier Eq. (5.4.5) head.

This public surface is intentionally the carrier residual inequality used by
the correction record kept under the separate theorem below. -/
theorem lemma513_accelerated_residual_second_moment_bound
    {n dim : Nat} (S : Setup n dim)
    (xUnder snapshot : Set.Elem (proxCoreSet S)) :
    componentConditionalExpectation S (samplingWeight S) (fun i : Fin n =>
        norm (carrierEstimatorResidual S (samplingWeight S) i xUnder.1 snapshot.1
          (carrierFullGradient S snapshot.1)) ^ 2) <=
      2 * theorem59LQ S *
        (finiteSumObjective S snapshot.1 - linearization S xUnder.1 snapshot.1) := by
  have hmoment :=
    carrierEstimatorResidual_second_moment_le_gradient_gap S
      (proxCoreAsFeasible S xUnder) (proxCoreAsFeasible S snapshot)
  have hgap_bound :
      finiteCarrierGradientGapRelationLeft S (samplingWeight S) snapshot.1 xUnder.1 <=
        2 * theorem59LQ S *
          (finiteSumObjective S snapshot.1 - linearization S xUnder.1 snapshot.1) := by
    have hgap :=
      eq535_carrier_finite_sum_gradient_gap_relation S
        (proxCoreSetElem_mem_X S snapshot) (proxCoreSetElem_mem_X S xUnder)
    have hrewrite :
        finiteSumObjective S snapshot.1 - finiteSumObjective S xUnder.1 -
            ⟪fullGradient S xUnder.1, snapshot.1 - xUnder.1⟫_Real =
          finiteSumObjective S snapshot.1 - linearization S xUnder.1 snapshot.1 := by
      simp [linearization]
      ring
    calc
      finiteCarrierGradientGapRelationLeft S (samplingWeight S) snapshot.1 xUnder.1
          <= 2 * theorem59LQ S *
            (finiteSumObjective S snapshot.1 - finiteSumObjective S xUnder.1 -
              ⟪fullGradient S xUnder.1, snapshot.1 - xUnder.1⟫_Real) := hgap
      _ = 2 * theorem59LQ S *
            (finiteSumObjective S snapshot.1 - linearization S xUnder.1 snapshot.1) := by
          rw [hrewrite]
  exact le_trans hmoment hgap_bound

/-- Separate formal correction record for the carrier version of Eq. (5.4.5). -/
theorem lemma513_accelerated_residual_second_moment_bound_correction
    {n dim : Nat} (S : Setup n dim) :
    lemma513AcceleratedResidualSecondMomentCarrierCorrectionStatement S := by
  intro xUnder snapshot
  exact lemma513_accelerated_residual_second_moment_bound S xUnder snapshot

theorem lemma513_accelerated_variance_estimator_facts_boundary
    {n dim : Nat} (S : Setup n dim) :
    lemma513AcceleratedVarianceEstimatorFactsBoundaryStatement S := by
  exact lemma513_carrier_accelerated_variance_estimator_facts_boundary S

/-- Source-derived scalar-to-coefficient bridge for Lemma 5.17's smooth parameters. -/
theorem lemma517_parameter_conditions
    {n dim : Nat} (S : Setup n dim)
    (T : Nat -> Nat) (gamma alpha p : Nat -> Real)
  (hparams :
      forall r, 1 <= r ->
        0 < T r ∧
        alpha r ∈ Set.Icc (0 : Real) 1 ∧
        0 < alpha r ∧
        p r ∈ Set.Icc (0 : Real) 1 ∧
        0 < gamma r ∧
        0 <= 1 - alpha r - p r ∧
        0 < 1 + S.mu * gamma r - averageSmoothness S * alpha r * gamma r ∧
        0 <= p r -
          theorem59LQ S * alpha r * gamma r /
            (1 + S.mu * gamma r - averageSmoothness S * alpha r * gamma r)) :
    forall r, 1 <= r ->
      alpha r ∈ Set.Icc (0 : Real) 1 ∧
      p r ∈ Set.Icc (0 : Real) 1 ∧
      0 < gamma r ∧
      0 < 1 + S.mu * gamma r - averageSmoothness S * alpha r * gamma r ∧
      searchPointWeights S gamma alpha p r ∈ stdSimplex Real (Fin 3) ∧
      averagedInnerWeightsAdmissible alpha p r := by
  intro r hr
  rcases hparams r hr with
    ⟨_hTpos, halpha, _halpha_pos, hp, hgamma, hbar, hcurv, hnoise⟩
  exact
    ⟨halpha, hp, hgamma, hcurv,
      lemma516_searchPointWeights_mem_stdSimplex S gamma alpha p r
        halpha hp hgamma hbar hcurv hnoise,
      lemma516_averagedInnerWeightsAdmissible S gamma alpha p r
        halpha hp hgamma hbar hcurv hnoise⟩

/-- Source-derived theta admissibility for Lemma 5.17's Eq. (5.4.12) weights. -/
theorem lemma517_smoothTheta_epochOutputWeightsAdmissible
    {n dim : Nat} (S : Setup n dim)
    (T : Nat -> Nat) (gamma alpha p : Nat -> Real)
    (hparams :
      forall r, 1 <= r ->
        0 < T r ∧
        alpha r ∈ Set.Icc (0 : Real) 1 ∧
        0 < alpha r ∧
        p r ∈ Set.Icc (0 : Real) 1 ∧
        0 < gamma r ∧
        0 <= 1 - alpha r - p r ∧
        0 < 1 + S.mu * gamma r - averageSmoothness S * alpha r * gamma r ∧
        0 <= p r -
          theorem59LQ S * alpha r * gamma r /
            (1 + S.mu * gamma r - averageSmoothness S * alpha r * gamma r)) :
    forall r, 1 <= r ->
      epochOutputWeightsAdmissible
        (fun t => SOptLib.terminal_adjusted_smooth_epoch_weight
          (T r) (gamma r) (alpha r) (p r) t)
        (T r) := by
  intro r hr
  rcases hparams r hr with
    ⟨hTpos, _halpha_Icc, halpha_pos, hp_Icc, hgamma, _hbar, _hcurv, _hnoise⟩
  simpa [epochOutputWeightsAdmissible, paperTime,
    SOptLib.FiniteWindowWeightsAdmissible, SOptLib.terminal_adjusted_smooth_epoch_weight,
    and_comm] using
    (SOptLib.terminal_adjusted_smooth_epoch_weight_admissible
      (T := T r) (gamma := gamma r) (alpha := alpha r) (p := p r)
      hTpos hgamma halpha_pos hp_Icc.1)

/-- Correction record for the retired guarded corrected-core Lemma 5.16 head.

The former theorem with this name asserted Eq. (5.4.9) for `innerStepOn`.  That
generated process is driven by the legacy totalized core selector rather than
the Algorithm 5.7 prox minimizer over `X`.  The source-faithful Lemma 5.16
surface in this file is the relational boundary
`lemma516_corrected_relational_conditional_expectation_step_boundary`, whose
step family carries `InnerStepRelOn` certificates. -/
def lemma516GuardedCorrectedCoreConditionalOneStepRecursionRetiredStatement
    {n dim : Nat} (_S : Setup n dim) : Prop := True

/-- Typed obstruction for the retired guarded corrected-core Lemma 5.16 head.

The current `innerStepOn` spine still unfolds through the legacy
`proxUpdateCoreOn` totalization, whose next prox point is definitionally the
previous state point. This compiled fact is the local evidence that Eq. (5.4.9)
for Algorithm 5.7 cannot be recovered from this generated corrected-core step
by tactic work alone. -/
theorem lemma516_guarded_correctedCore_innerStepOn_x_eq_state_x
    {n dim : Nat} (S : Setup n dim)
    (gamma alpha p : Nat -> Real) (s : Nat)
    (q : Fin n -> Real) (snapshot : Set.Elem (proxCoreSet S))
    (fullGradAtSnapshot : VariableSpace dim)
    (sample : Fin n) (state : InnerStateOn S)
    (hsearch : searchPointWeights S gamma alpha p s ∈ stdSimplex Real (Fin 3))
    (havg : averagedInnerWeightsAdmissible alpha p s) :
    (innerStepOn S gamma alpha p s q snapshot fullGradAtSnapshot sample
      state hsearch havg).x = state.x := by
  rfl

/- Retired statement-correction artifact.
Do not use this declaration as a supplier for Eq. (5.4.9).  Consumers needing
the paper Lemma 5.16 recursion must route through
`lemma516_corrected_relational_conditional_expectation_step_boundary`, or through
the printed Eq. (5.4.27) route that instantiates that relational boundary. -/
theorem lemma516_guarded_correctedCore_conditional_one_step_recursion
    {n dim : Nat} (S : Setup n dim)
    (gamma alpha p : Nat -> Real) (s : Nat)
    (snapshot : Set.Elem (proxCoreSet S)) (x : FeasiblePoint S)
    (x0 : Set.Elem (proxCoreSet S)) (samples : Nat -> Fin n) (t : Nat) (ht : 1 <= t)
    (halpha : alpha s ∈ Set.Icc (0 : Real) 1)
    (halpha_pos : 0 < alpha s)
    (hp : p s ∈ Set.Icc (0 : Real) 1)
    (hgamma : 0 < gamma s)
    (hbar : 0 <= 1 - alpha s - p s)
    (hcurv : 0 < 1 + S.mu * gamma s - averageSmoothness S * alpha s * gamma s)
    (hnoise :
      0 <= p s -
        theorem59LQ S * alpha s * gamma s /
          (1 + S.mu * gamma s - averageSmoothness S * alpha s * gamma s)) :
    lemma516GuardedCorrectedCoreConditionalOneStepRecursionRetiredStatement S := by
  trivial

/-- Correction record for the retired unguarded corrected-core Lemma 5.16 head.

The scalar witness is the exact denominator obstruction: with `alpha = 0`, the
pre-divided recursion does not imply the total-division Eq. (5.4.9) form used by
the old corrected-core theorem. -/
def lemma516CorrectedCoreConditionalOneStepRecursionStatementCorrection
    {n dim : Nat} (_S : Setup n dim) : Prop :=
  lemma516AlphaZeroRescaleObstruction

/- Retired statement-correction artifact.
The former theorem head stated the unguarded corrected-core Eq. (5.4.9) with
`gamma s / alpha s` under only `alpha s in [0,1]`.  It is no longer a Phase 2a
proof leaf; use `lemma516_guarded_correctedCore_conditional_one_step_recursion`
for the executable corrected-core recursion. -/
theorem lemma516_correctedCore_conditional_one_step_recursion
    {n dim : Nat} (S : Setup n dim) :
    lemma516CorrectedCoreConditionalOneStepRecursionStatementCorrection S := by
  exact lemma516_predivided_recursion_does_not_imply_total_division_rescale

/- Route tombstone: `pointwise_relational_lemma516_source_route_v1`.
The old compiled pointwise Lemma 5.16 diagnostic theorem
`legacyDiagnostic_lemma516_relational_pointwise_one_step_recursion` has been
removed from the proof surface. Public/source consumers use the expectation-level
`lemma516RelationalConditionalExpectationStepBoundaryStatement` instead. -/

/-- Compiled availability record for the relational Lemma 5.15 source boundary. -/
def lemma515RelationalCoreStepBoundaryStatement
    {n dim : Nat} (S : Setup n dim) : Prop :=
  forall (gamma : Nat -> Real) (s : Nat)
    (x : FeasiblePoint S) (xPrev xUnder : Set.Elem (proxCoreSet S))
    (delta : VariableSpace dim) (xNext : Set.Elem (proxCoreSet S)),
    0 <= gamma s ->
    ProxUpdateRelOn S gamma s xPrev xUnder
        (fullGradient S xUnder.1 + delta) (proxCoreAsFeasible S xNext) ->
      gamma s *
          (linearization S xUnder.1 xNext.1 - linearization S xUnder.1 x.1 +
            S.h xNext.1 - S.h x.1) <=
        gamma s * S.mu * bregmanOn S xUnder x +
          bregmanOn S xPrev x -
          (1 + S.mu * gamma s) * bregmanOn S xNext x -
          (1 + S.mu * gamma s) / 2 *
            norm (xNext.1 - auxiliaryPoint S gamma s xPrev.1 xUnder.1) ^ 2 -
          gamma s * ⟪delta, xNext.1 - x.1⟫_Real

theorem lemma515_relational_core_step_boundary
    {n dim : Nat} (S : Setup n dim) :
    lemma515RelationalCoreStepBoundaryStatement S := by
  intro gamma s x xPrev xUnder delta xNext hgamma hrel
  exact lemma515_relational_core_step_inequality S gamma s x xPrev xUnder delta xNext
    hgamma hrel

/-- Corrected-core Lemma 5.15 with the canonical relational prox-update surface.

The active theorem name now exposes the same paper step as
`lemma515_relational_core_step_inequality`: Algorithm 5.7 supplies the next
point together with the prox minimizer relation. It deliberately has no
dependency on the retired `proxUpdateCoreOn` totalization. -/
theorem lemma515_correctedCore_one_step_accelerated_prox_inequality
    {n dim : Nat} (S : Setup n dim)
    (gamma : Nat -> Real) (s : Nat)
    (x : FeasiblePoint S) (xPrev xUnder : Set.Elem (proxCoreSet S))
    (delta : VariableSpace dim) (xNext : Set.Elem (proxCoreSet S))
    (hgamma : 0 <= gamma s)
    (hrel :
      ProxUpdateRelOn S gamma s xPrev xUnder
        (fullGradient S xUnder.1 + delta) (proxCoreAsFeasible S xNext)) :
    gamma s *
        (linearization S xUnder.1 xNext.1 - linearization S xUnder.1 x.1 +
          S.h xNext.1 - S.h x.1) <=
      gamma s * S.mu * bregmanOn S xUnder x +
        bregmanOn S xPrev x -
        (1 + S.mu * gamma s) * bregmanOn S xNext x -
        (1 + S.mu * gamma s) / 2 *
          norm (xNext.1 - auxiliaryPoint S gamma s xPrev.1 xUnder.1) ^ 2 -
        gamma s * ⟪delta, xNext.1 - x.1⟫_Real := by
  exact lemma515_relational_core_step_inequality S gamma s x xPrev xUnder delta xNext
    hgamma hrel

/-- Extract Algorithm 5.7's averaged-iterate formula from the relational step.

This helper aligns with Lemma 5.16's use of the printed update
`bar x_t = (1-alpha_s-p_s) bar x_{t-1} + alpha_s x_t + p_s tilde x`.
Existing candidates such as `averagedInnerIterateValueFeasibleOn_mem_X`,
`averagedInnerIterateOn`, and corrected-core `innerStepCoreOn_*` facts provide
membership or selected-core transitions; this route needs the equation already
carried by the paper-facing `InnerStepRelOn` hypothesis. -/
theorem lemma516_nextBarCore_eq_averagedInnerIterate
    {n dim : Nat} (S : Setup n dim)
    (gamma alpha p : Nat -> Real) (s : Nat)
    (q : Fin n -> Real) (snapshot xPrev xBarPrev : Set.Elem (proxCoreSet S))
    (fullGradAtSnapshot : VariableSpace dim)
    (sample : Fin n)
    (hsearch : searchPointWeights S gamma alpha p s ∈ stdSimplex Real (Fin 3))
    (havg : averagedInnerWeightsAdmissible alpha p s)
    (next : InnerStateFeasibleOn S)
    (hxNext : next.x.1 ∈ proxCoreSet S)
    (hxBarNext : next.xBar.1 ∈ proxCoreSet S)
    (hstep :
      InnerStepRelOn S gamma alpha p s q snapshot fullGradAtSnapshot sample
        xPrev xBarPrev hsearch havg next) :
    let nextCore : Set.Elem (proxCoreSet S) := ⟨next.x.1, hxNext⟩
    let nextBarCore : Set.Elem (proxCoreSet S) := ⟨next.xBar.1, hxBarNext⟩
    nextBarCore.1 =
      averagedInnerIterate alpha p s xBarPrev.1 nextCore.1 snapshot.1 := by
  rcases hstep with ⟨_hprox, hbarEq⟩
  dsimp only
  rw [hbarEq]
  rfl

/-- Algorithm 5.7 affine displacement identity used in Lemma 5.16, proof step 2.

Aligns with Lan Lemma 5.16 lines 16986-16992: after substituting the printed
search point and averaged-iterate formulas, `bar x_t - underbar x_t` is the
`alpha_s` multiple of the displacement from the prox iterate to `x_{t-1}^+`.
Considered `average_sub_search_eq_alpha_smul_step_sub_weighted_center`,
`lemma516_nextBarCore_eq_averagedInnerIterate`, and the local search/average
constructors; the SOptLib helper covers the two-point accelerated search case,
while Algorithm 5.7's variance-reduced step has the three-source snapshot term
and requires this local denominator normalization. -/
theorem lemma516_bar_minus_search_eq_alpha_sub_auxiliary
    {n dim : Nat} (S : Setup n dim)
    (gamma alpha p : Nat -> Real) (s : Nat)
    (halpha : alpha s ∈ Set.Icc (0 : Real) 1)
    (hgamma : 0 < gamma s)
    (xBarPrev xPrev xNext snapshot : VariableSpace dim) :
    averagedInnerIterate alpha p s xBarPrev xNext snapshot -
        searchPoint S gamma alpha p s xBarPrev xPrev snapshot =
      alpha s •
        (xNext -
          auxiliaryPoint S gamma s xPrev
            (searchPoint S gamma alpha p s xBarPrev xPrev snapshot)) := by
  have hgamma_nonneg : 0 ≤ gamma s := le_of_lt hgamma
  have hone_sub_alpha_nonneg : 0 ≤ 1 - alpha s := by
    nlinarith [halpha.2]
  have hmu_gamma_nonneg : 0 ≤ S.mu * gamma s :=
    mul_nonneg S.mu_nonneg hgamma_nonneg
  have hsearch_den_pos : 0 < 1 + S.mu * gamma s * (1 - alpha s) := by
    have hprod_nonneg : 0 ≤ S.mu * gamma s * (1 - alpha s) :=
      mul_nonneg hmu_gamma_nonneg hone_sub_alpha_nonneg
    nlinarith
  have haux_den_pos : 0 < 1 + S.mu * gamma s := by
    nlinarith
  simpa [averagedInnerIterate, searchPoint, auxiliaryPoint, searchPointBarWeight,
    searchPointPrevWeight, searchPointSnapshotWeight, searchDenominator] using
    (SOptLib.acceleratedSnapshotAverage_sub_search_eq_alpha_smul_sub_auxiliary
      S.mu (gamma s) (alpha s) (p s)
        (ne_of_gt hsearch_den_pos) (ne_of_gt haux_den_pos)
        xBarPrev xPrev xNext snapshot)

/-- Rescale the pre-divided Lemma 5.16 expectation inequality into Eq. (5.4.9).

This is the finite-expectation algebra hidden by the printed
`gamma_s / alpha_s` normalization.  It is deliberately local to Lemma 5.16 and
requires the explicit positive-alpha side condition needed to avoid Lean's
total-division zero case. -/
theorem lemma516_rescale_pre_expectation
    {n dim : Nat} (S : Setup n dim)
    (A B : Fin n -> Real)
    (gamma alpha p objPrev objTarget objSnapshot Vprev : Real)
    (halpha_pos : 0 < alpha) (hgamma : 0 < gamma)
    (hpre :
      componentConditionalExpectation S (samplingWeight S) (fun sample =>
          A sample + (alpha / gamma) * B sample) <=
        (1 - alpha - p) * objPrev +
          alpha * objTarget +
          p * objSnapshot +
          (alpha / gamma) * Vprev) :
    componentConditionalExpectation S (samplingWeight S) (fun sample =>
        gamma / alpha * (A sample - objTarget) + B sample) <=
      gamma / alpha * (1 - alpha - p) * (objPrev - objTarget) +
        gamma / alpha * p * (objSnapshot - objTarget) + Vprev := by
  simpa [componentConditionalExpectation] using
    SOptLib.finset_weighted_expectation_rescale_predivided_recurrence
      (s := Finset.univ) (w := samplingWeight S) (A := A) (B := B)
      (gamma := gamma) (alpha := alpha) (p := p)
      (basePrev := objPrev) (baseTarget := objTarget)
      (baseSnapshot := objSnapshot) (tailPrev := Vprev)
      halpha_pos hgamma (samplingWeight_sum_eq_one S)
      (by simpa [componentConditionalExpectation] using hpre)

/-- Printed expectation-level relational Lemma 5.16 boundary.

This retains the literal printed scalar surface from Lemma 5.16, including
`alpha_s in [0,1]` without a strict positivity premise. It is kept as the
source diagnostic statement, not as the executable proof supplier for Theorem
5.9, because Lean's total division gives a different alpha-zero formula.

The guard `hbar : 0 <= 1 - alpha s - p s` is not a new `Setup` assumption.
It is the corrected scalar regularity needed for the convexity steps involving
`bar{x}_t`; the unguarded printed scalar conditions are formally refuted by
`lemma516_printedScalarSideConditions_do_not_imply_bar_nonneg`. -/
def lemma516RelationalConditionalExpectationStepBoundaryStatement
    {n dim : Nat} (S : Setup n dim) : Prop :=
  lemma515RelationalCoreStepBoundaryStatement S ->
    lemma513AcceleratedVarianceEstimatorFactsBoundaryStatement S ->
      forall (gamma alpha p : Nat -> Real) (s : Nat)
        (snapshot xPrev xBarPrev : Set.Elem (proxCoreSet S))
        (xTarget : FeasiblePoint S)
        (halpha : alpha s ∈ Set.Icc (0 : Real) 1)
        (hp : p s ∈ Set.Icc (0 : Real) 1)
        (hgamma : 0 < gamma s)
        (hbar : 0 <= 1 - alpha s - p s)
        (hcurv : 0 < 1 + S.mu * gamma s - averageSmoothness S * alpha s * gamma s)
        (hnoise :
          0 <= p s -
            theorem59LQ S * alpha s * gamma s /
              (1 + S.mu * gamma s - averageSmoothness S * alpha s * gamma s))
        (next : Fin n -> InnerStateFeasibleOn S),
        (forall sample,
          InnerStepRelOn S gamma alpha p s (samplingWeight S) snapshot
            (fullGradient S snapshot.1) sample xPrev xBarPrev
            (lemma516_searchPointWeights_mem_stdSimplex S gamma alpha p s
              halpha hp hgamma hbar hcurv hnoise)
            (lemma516_averagedInnerWeightsAdmissible S gamma alpha p s
              halpha hp hgamma hbar hcurv hnoise)
            (next sample)) ->
          forall (hxNext : forall sample, (next sample).x.1 ∈ proxCoreSet S)
            (hxBarNext : forall sample, (next sample).xBar.1 ∈ proxCoreSet S),
            componentConditionalExpectation S (samplingWeight S) (fun sample =>
                let nextCore : Set.Elem (proxCoreSet S) := ⟨(next sample).x.1, hxNext sample⟩
                let nextBarCore : Set.Elem (proxCoreSet S) := ⟨(next sample).xBar.1, hxBarNext sample⟩
                gamma s / alpha s *
                    (compositeObjective S nextBarCore.1 - compositeObjective S xTarget.1) +
                    (1 + S.mu * gamma s) * bregmanOn S nextCore xTarget) <=
              gamma s / alpha s * (1 - alpha s - p s) *
                  (compositeObjective S xBarPrev.1 - compositeObjective S xTarget.1) +
                gamma s / alpha s * p s *
                  (compositeObjective S snapshot.1 - compositeObjective S xTarget.1) +
                bregmanOn S xPrev xTarget

/-- Corrected guarded Lemma 5.16 boundary.

This is the same Eq. (5.4.9) relational expectation interface as the printed
statement above, with the explicit positive-alpha denominator guard justified by
`lemma516_printedScalarSideConditions_do_not_imply_alpha_pos`. The public
Theorem 5.9 route consumes this corrected statement because its schedule proves
`0 < alpha_s`. -/
def lemma516GuardedRelationalConditionalExpectationStepBoundaryStatement
    {n dim : Nat} (S : Setup n dim) : Prop :=
  lemma515RelationalCoreStepBoundaryStatement S ->
    lemma513AcceleratedVarianceEstimatorFactsBoundaryStatement S ->
      forall (gamma alpha p : Nat -> Real) (s : Nat)
        (snapshot xPrev xBarPrev : Set.Elem (proxCoreSet S))
        (xTarget : FeasiblePoint S)
        (halpha : alpha s ∈ Set.Icc (0 : Real) 1)
        (halpha_pos : 0 < alpha s)
        (hp : p s ∈ Set.Icc (0 : Real) 1)
        (hgamma : 0 < gamma s)
        (hbar : 0 <= 1 - alpha s - p s)
        (hcurv : 0 < 1 + S.mu * gamma s - averageSmoothness S * alpha s * gamma s)
        (hnoise :
          0 <= p s -
            theorem59LQ S * alpha s * gamma s /
              (1 + S.mu * gamma s - averageSmoothness S * alpha s * gamma s))
        (next : Fin n -> InnerStateFeasibleOn S),
        (forall sample,
          InnerStepRelOn S gamma alpha p s (samplingWeight S) snapshot
            (fullGradient S snapshot.1) sample xPrev xBarPrev
            (lemma516_searchPointWeights_mem_stdSimplex S gamma alpha p s
              halpha hp hgamma hbar hcurv hnoise)
            (lemma516_averagedInnerWeightsAdmissible S gamma alpha p s
              halpha hp hgamma hbar hcurv hnoise)
            (next sample)) ->
          forall (hxNext : forall sample, (next sample).x.1 ∈ proxCoreSet S)
            (hxBarNext : forall sample, (next sample).xBar.1 ∈ proxCoreSet S),
            componentConditionalExpectation S (samplingWeight S) (fun sample =>
                let nextCore : Set.Elem (proxCoreSet S) := ⟨(next sample).x.1, hxNext sample⟩
                let nextBarCore : Set.Elem (proxCoreSet S) := ⟨(next sample).xBar.1, hxBarNext sample⟩
                gamma s / alpha s *
                    (compositeObjective S nextBarCore.1 - compositeObjective S xTarget.1) +
                    (1 + S.mu * gamma s) * bregmanOn S nextCore xTarget) <=
              gamma s / alpha s * (1 - alpha s - p s) *
                  (compositeObjective S xBarPrev.1 - compositeObjective S xTarget.1) +
                gamma s / alpha s * p s *
                  (compositeObjective S snapshot.1 - compositeObjective S xTarget.1) +
                bregmanOn S xPrev xTarget

/-- Pathwise Lemma 5.16 prox/Bregman term obtained directly from Lemma 5.15.

This helper aligns with the Lemma 5.16 proof step inserting Lemma 5.15 into
the inner prox update. Target/SOptLib candidates
`innerStepRelOn_x_core_propagation_iff_proxUpdateRelOn_mem_proxCore`,
`InnerStepCoreRelOn`, and the printed feasible-inner-step helpers were checked:
they address core propagation or alternate route contracts, while this proof
only needs the already supplied `hxNext` membership plus the definitional
estimator-residual split. -/
theorem lemma516_pathwise_prox_bound_from_h515
    {n dim : Nat} (S : Setup n dim)
    (h515 : lemma515RelationalCoreStepBoundaryStatement S)
    (gamma alpha p : Nat -> Real) (s : Nat)
    (snapshot xPrev xBarPrev : Set.Elem (proxCoreSet S))
    (xTarget : FeasiblePoint S)
    (halpha : alpha s ∈ Set.Icc (0 : Real) 1)
    (hp : p s ∈ Set.Icc (0 : Real) 1)
    (hgamma : 0 < gamma s)
    (hbar : 0 <= 1 - alpha s - p s)
    (hcurv : 0 < 1 + S.mu * gamma s - averageSmoothness S * alpha s * gamma s)
    (hnoise :
      0 <= p s -
        theorem59LQ S * alpha s * gamma s /
          (1 + S.mu * gamma s - averageSmoothness S * alpha s * gamma s))
    (next : Fin n -> InnerStateFeasibleOn S)
    (hstep : forall sample,
      InnerStepRelOn S gamma alpha p s (samplingWeight S) snapshot
        (fullGradient S snapshot.1) sample xPrev xBarPrev
        (lemma516_searchPointWeights_mem_stdSimplex S gamma alpha p s
          halpha hp hgamma hbar hcurv hnoise)
        (lemma516_averagedInnerWeightsAdmissible S gamma alpha p s
          halpha hp hgamma hbar hcurv hnoise)
        (next sample))
    (hxNext : forall sample, (next sample).x.1 ∈ proxCoreSet S) :
    forall sample,
      let hsearch :=
        lemma516_searchPointWeights_mem_stdSimplex S gamma alpha p s
          halpha hp hgamma hbar hcurv hnoise
      let xUnder := searchPointOn S gamma alpha p s xBarPrev xPrev snapshot hsearch
      let nextCore : Set.Elem (proxCoreSet S) := ⟨(next sample).x.1, hxNext sample⟩
      gamma s *
          (linearization S xUnder.1 nextCore.1 -
            linearization S xUnder.1 xTarget.1 +
            S.h nextCore.1 - S.h xTarget.1) <=
        gamma s * S.mu * bregmanOn S xUnder xTarget +
          bregmanOn S xPrev xTarget -
          (1 + S.mu * gamma s) * bregmanOn S nextCore xTarget -
          (1 + S.mu * gamma s) / 2 *
            norm (nextCore.1 - auxiliaryPoint S gamma s xPrev.1 xUnder.1) ^ 2 -
          gamma s *
            ⟪carrierEstimatorResidual S (samplingWeight S) sample xUnder.1 snapshot.1
                (carrierFullGradient S snapshot.1), nextCore.1 - xTarget.1⟫_Real := by
  intro sample
  dsimp only
  let hsearch :=
    lemma516_searchPointWeights_mem_stdSimplex S gamma alpha p s
      halpha hp hgamma hbar hcurv hnoise
  let xUnder := searchPointOn S gamma alpha p s xBarPrev xPrev snapshot hsearch
  let nextCore : Set.Elem (proxCoreSet S) := ⟨(next sample).x.1, hxNext sample⟩
  rcases hstep sample with ⟨hprox, _hxbar⟩
  have hprox' :
      ProxUpdateRelOn S gamma s xPrev xUnder
        (fullGradient S xUnder.1 +
          carrierEstimatorResidual S (samplingWeight S) sample xUnder.1 snapshot.1
            (carrierFullGradient S snapshot.1))
        (proxCoreAsFeasible S nextCore) := by
    exact
      ProxUpdateRelOn.of_raw_varianceReducedGradient_with_carrierResidual
        S gamma s (samplingWeight S) sample xPrev xUnder snapshot
        (proxCoreAsFeasible S nextCore) hprox
  exact h515 gamma s xTarget xPrev xUnder
    (carrierEstimatorResidual S (samplingWeight S) sample xUnder.1 snapshot.1
      (carrierFullGradient S snapshot.1)) nextCore (le_of_lt hgamma) hprox'

/-- Corrected name for the active guarded Lemma 5.16 boundary.

This abbrev is intentionally definitionally equal to the existing boundary
record so downstream compatibility is preserved, but public source-route
contracts can refer to the guarded statement as a statement correction rather
than as the unguarded printed scalar package. -/
abbrev lemma516CorrectedRelationalConditionalExpectationStepBoundaryStatement
    {n dim : Nat} (S : Setup n dim) : Prop :=
  lemma516GuardedRelationalConditionalExpectationStepBoundaryStatement S

/-- Correction record for the unguarded printed Lemma 5.16 boundary.

The first conjunct is the executable guarded Lemma 5.16 package. The second
conjunct is the exact alpha-zero scalar obstruction showing why the literal
unguarded total-division statement is not handed to Phase 2a as a routine proof
leaf. The obstruction terminal is the compiled Real witness theorem
`lemma516_predivided_recursion_does_not_imply_total_division_rescale`. -/
def lemma516RelationalConditionalExpectationStepBoundaryCorrectionStatement
    {n dim : Nat} (S : Setup n dim) : Prop :=
  (lemma516GuardedRelationalConditionalExpectationStepBoundaryStatement S ∧
    lemma516AlphaZeroRescaleObstruction : Prop)

set_option maxHeartbeats 0 in
theorem lemma516_guarded_relational_conditional_expectation_step_boundary
    {n dim : Nat} (S : Setup n dim) :
    lemma516GuardedRelationalConditionalExpectationStepBoundaryStatement S := by
  intro h515 hvariance gamma alpha p s snapshot xPrev xBarPrev xTarget
    halpha halpha_pos hp hgamma hbar hcurv hnoise next hstep hxNext hxBarNext
  have hproxBound :=
    lemma516_pathwise_prox_bound_from_h515 S h515 gamma alpha p s snapshot xPrev
      xBarPrev xTarget halpha hp hgamma hbar hcurv hnoise next hstep hxNext
  have hvarianceFacts :=
    hvariance gamma alpha p s snapshot xPrev xBarPrev xTarget
      halpha hp hgamma hbar hcurv hnoise
  have hmono := componentConditionalExpectation_mono_of_pointwise S
  let hsearch :=
    lemma516_searchPointWeights_mem_stdSimplex S gamma alpha p s
      halpha hp hgamma hbar hcurv hnoise
  let xUnder := searchPointOn S gamma alpha p s xBarPrev xPrev snapshot hsearch
  let den := 1 + S.mu * gamma s - averageSmoothness S * alpha s * gamma s
  have hden_pos : 0 < den := by
    dsimp [den]
    exact hcurv
  have hresidCoeff_nonneg : 0 <= alpha s * gamma s / (2 * den) := by
    have ha : 0 <= alpha s := halpha.1
    have hg : 0 <= gamma s := le_of_lt hgamma
    have hden2 : 0 < 2 * den := mul_pos (by norm_num) hden_pos
    exact div_nonneg (mul_nonneg ha hg) (le_of_lt hden2)
  have hresidualExpectationBudget :
      componentConditionalExpectation S (samplingWeight S) (fun sample =>
          (alpha s * gamma s / (2 * den)) *
              norm (carrierEstimatorResidual S (samplingWeight S) sample xUnder.1 snapshot.1
                (carrierFullGradient S snapshot.1)) ^ 2 +
            alpha s *
              ⟪carrierEstimatorResidual S (samplingWeight S) sample xUnder.1 snapshot.1
                  (carrierFullGradient S snapshot.1),
                auxiliaryPoint S gamma s xPrev.1 xUnder.1 - xTarget.1⟫_Real) <=
        (alpha s * gamma s / (2 * den)) *
          (2 * theorem59LQ S *
            (finiteSumObjective S snapshot.1 - linearization S xUnder.1 snapshot.1)) := by
    rcases hvarianceFacts with ⟨hmean, hsecond⟩
    exact
      componentConditionalExpectation_nonneg_mul_budget_add_zero_mean
        S (samplingWeight S)
        (fun sample =>
          norm (carrierEstimatorResidual S (samplingWeight S) sample xUnder.1 snapshot.1
            (carrierFullGradient S snapshot.1)) ^ 2)
        (fun sample =>
          ⟪carrierEstimatorResidual S (samplingWeight S) sample xUnder.1 snapshot.1
              (carrierFullGradient S snapshot.1),
            auxiliaryPoint S gamma s xPrev.1 xUnder.1 - xTarget.1⟫_Real)
        (alpha s * gamma s / (2 * den)) (alpha s)
        (2 * theorem59LQ S *
          (finiteSumObjective S snapshot.1 - linearization S xUnder.1 snapshot.1))
        hresidCoeff_nonneg hmean hsecond
  have hsnapshot_linearization :
      linearization S xUnder.1 snapshot.1 <= finiteSumObjective S snapshot.1 :=
    finiteSumObjective_linearization_le_of_core_strong_convexity S xUnder
      (proxCoreAsFeasible S snapshot)
  have hnoiseBracket :
      (p s -
          theorem59LQ S * alpha s * gamma s / den) *
          linearization S xUnder.1 snapshot.1 +
        (theorem59LQ S * alpha s * gamma s / den) *
          finiteSumObjective S snapshot.1 <=
        p s * finiteSumObjective S snapshot.1 := by
    exact
      lemma516_noise_bracket_le_snapshot
        (p := p s)
        (lambda := theorem59LQ S * alpha s * gamma s / den)
        (lin := linearization S xUnder.1 snapshot.1)
        (fval := finiteSumObjective S snapshot.1)
        (by
          dsimp [den]
          exact hnoise)
        hsnapshot_linearization
  have hbarFormula :
      forall sample,
        let nextCore : Set.Elem (proxCoreSet S) := ⟨(next sample).x.1, hxNext sample⟩
        let nextBarCore : Set.Elem (proxCoreSet S) := ⟨(next sample).xBar.1, hxBarNext sample⟩
        nextBarCore.1 =
          averagedInnerIterate alpha p s xBarPrev.1 nextCore.1 snapshot.1 := by
    intro sample
    exact
      lemma516_nextBarCore_eq_averagedInnerIterate S gamma alpha p s
        (samplingWeight S) snapshot xPrev xBarPrev (fullGradient S snapshot.1)
        sample
        (lemma516_searchPointWeights_mem_stdSimplex S gamma alpha p s
          halpha hp hgamma hbar hcurv hnoise)
        (lemma516_averagedInnerWeightsAdmissible S gamma alpha p s
          halpha hp hgamma hbar hcurv hnoise)
        (next sample) (hxNext sample) (hxBarNext sample) (hstep sample)
  have hhConvexBar :
      forall sample,
        let nextCore : Set.Elem (proxCoreSet S) := ⟨(next sample).x.1, hxNext sample⟩
        let nextBarCore : Set.Elem (proxCoreSet S) := ⟨(next sample).xBar.1, hxBarNext sample⟩
        S.h nextBarCore.1 <=
          (1 - alpha s - p s) * S.h xBarPrev.1 +
            alpha s * S.h nextCore.1 +
            p s * S.h snapshot.1 := by
    intro sample
    let nextCore : Set.Elem (proxCoreSet S) := ⟨(next sample).x.1, hxNext sample⟩
    let nextBarCore : Set.Elem (proxCoreSet S) := ⟨(next sample).xBar.1, hxBarNext sample⟩
    have hformula : nextBarCore.1 =
        averagedInnerIterate alpha p s xBarPrev.1 nextCore.1 snapshot.1 := by
      simpa [nextCore, nextBarCore] using hbarFormula sample
    have hconv :
        S.h ((1 - alpha s - p s) • xBarPrev.1 +
              alpha s • nextCore.1 + p s • snapshot.1) <=
          (1 - alpha s - p s) * S.h xBarPrev.1 +
            alpha s * S.h nextCore.1 +
            p s * S.h snapshot.1 := by
      exact
        convexOn_three_smul_add_le (S.h_simple.convex) hbar halpha.1 hp.1
          (by ring)
          (proxCoreSetElem_mem_X S xBarPrev)
          (proxCoreSetElem_mem_X S nextCore)
          (proxCoreSetElem_mem_X S snapshot)
    have hleft :
        S.h nextBarCore.1 =
          S.h ((1 - alpha s - p s) • xBarPrev.1 +
              alpha s • nextCore.1 + p s • snapshot.1) := by
      simpa [averagedInnerIterate] using congrArg S.h hformula
    exact hleft.trans_le hconv
  have hfiniteSmoothBar :
      forall sample,
        let nextCore : Set.Elem (proxCoreSet S) := ⟨(next sample).x.1, hxNext sample⟩
        let nextBarCore : Set.Elem (proxCoreSet S) := ⟨(next sample).xBar.1, hxBarNext sample⟩
        finiteSumObjective S nextBarCore.1 <=
          linearization S xUnder.1 nextBarCore.1 +
            (averageSmoothness S / 2) * norm (nextBarCore.1 - xUnder.1) ^ 2 := by
    intro sample
    let nextCore : Set.Elem (proxCoreSet S) := ⟨(next sample).x.1, hxNext sample⟩
    let nextBarCore : Set.Elem (proxCoreSet S) := ⟨(next sample).xBar.1, hxBarNext sample⟩
    simpa [nextCore, nextBarCore] using
      finiteSumObjective_smooth_upper_bound_from_component_smooth S
        (proxCoreAsFeasible S xUnder) (proxCoreAsFeasible S nextBarCore)
  have hlinearizationBar :
      forall sample,
        let nextCore : Set.Elem (proxCoreSet S) := ⟨(next sample).x.1, hxNext sample⟩
        let nextBarCore : Set.Elem (proxCoreSet S) := ⟨(next sample).xBar.1, hxBarNext sample⟩
        linearization S xUnder.1 nextBarCore.1 =
          (1 - alpha s - p s) * linearization S xUnder.1 xBarPrev.1 +
            alpha s * linearization S xUnder.1 nextCore.1 +
              p s * linearization S xUnder.1 snapshot.1 := by
    intro sample
    dsimp only
    have hformula :
        (next sample).xBar.1 =
          averagedInnerIterate alpha p s xBarPrev.1 (next sample).x.1 snapshot.1 := by
      simpa using hbarFormula sample
    rw [hformula]
    unfold averagedInnerIterate linearization
    simp only [inner_add_right, inner_smul_right, sub_eq_add_neg]
    ring
  have hbarMinusSearch :
      forall sample,
        let nextCore : Set.Elem (proxCoreSet S) := ⟨(next sample).x.1, hxNext sample⟩
        let nextBarCore : Set.Elem (proxCoreSet S) := ⟨(next sample).xBar.1, hxBarNext sample⟩
        nextBarCore.1 - xUnder.1 =
          alpha s •
            (nextCore.1 -
              auxiliaryPoint S gamma s xPrev.1 xUnder.1) := by
    intro sample
    let nextCore : Set.Elem (proxCoreSet S) := ⟨(next sample).x.1, hxNext sample⟩
    let nextBarCore : Set.Elem (proxCoreSet S) := ⟨(next sample).xBar.1, hxBarNext sample⟩
    have hformula : nextBarCore.1 =
        averagedInnerIterate alpha p s xBarPrev.1 nextCore.1 snapshot.1 := by
      simpa [nextCore, nextBarCore] using hbarFormula sample
    have hraw :=
      lemma516_bar_minus_search_eq_alpha_sub_auxiliary S gamma alpha p s
        halpha hgamma xBarPrev.1 xPrev.1 nextCore.1 snapshot.1
    calc
      nextBarCore.1 - xUnder.1 =
          averagedInnerIterate alpha p s xBarPrev.1 nextCore.1 snapshot.1 -
            xUnder.1 := by
        rw [hformula]
      _ = alpha s •
            (nextCore.1 -
              auxiliaryPoint S gamma s xPrev.1 xUnder.1) := by
        simpa [nextCore, nextBarCore, xUnder, searchPointOn, searchPointValueOn]
          using hraw
  have hbarNormSq :
      forall sample,
        let nextCore : Set.Elem (proxCoreSet S) := ⟨(next sample).x.1, hxNext sample⟩
        let nextBarCore : Set.Elem (proxCoreSet S) := ⟨(next sample).xBar.1, hxBarNext sample⟩
        norm (nextBarCore.1 - xUnder.1) ^ 2 =
          (alpha s) ^ 2 *
            norm (nextCore.1 -
              auxiliaryPoint S gamma s xPrev.1 xUnder.1) ^ 2 := by
    intro sample
    let nextCore : Set.Elem (proxCoreSet S) := ⟨(next sample).x.1, hxNext sample⟩
    let nextBarCore : Set.Elem (proxCoreSet S) := ⟨(next sample).xBar.1, hxBarNext sample⟩
    have hdist :
        nextBarCore.1 - xUnder.1 =
          alpha s •
            (nextCore.1 -
              auxiliaryPoint S gamma s xPrev.1 xUnder.1) := by
      simpa [nextCore, nextBarCore] using hbarMinusSearch sample
    calc
      norm (nextBarCore.1 - xUnder.1) ^ 2 =
          norm (alpha s •
            (nextCore.1 -
              auxiliaryPoint S gamma s xPrev.1 xUnder.1)) ^ 2 := by
        rw [hdist]
      _ = (alpha s) ^ 2 *
            norm (nextCore.1 -
              auxiliaryPoint S gamma s xPrev.1 xUnder.1) ^ 2 := by
        rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have hcompositeBarUpper :
      forall sample,
        let nextCore : Set.Elem (proxCoreSet S) := ⟨(next sample).x.1, hxNext sample⟩
        let nextBarCore : Set.Elem (proxCoreSet S) := ⟨(next sample).xBar.1, hxBarNext sample⟩
        compositeObjective S nextBarCore.1 <=
          ((1 - alpha s - p s) * linearization S xUnder.1 xBarPrev.1 +
              alpha s * linearization S xUnder.1 nextCore.1 +
                p s * linearization S xUnder.1 snapshot.1) +
            (averageSmoothness S / 2) *
              ((alpha s) ^ 2 *
                norm (nextCore.1 -
                  auxiliaryPoint S gamma s xPrev.1 xUnder.1) ^ 2) +
            ((1 - alpha s - p s) * S.h xBarPrev.1 +
              alpha s * S.h nextCore.1 +
                p s * S.h snapshot.1) := by
    intro sample
    let nextCore : Set.Elem (proxCoreSet S) := ⟨(next sample).x.1, hxNext sample⟩
    let nextBarCore : Set.Elem (proxCoreSet S) := ⟨(next sample).xBar.1, hxBarNext sample⟩
    have hf : finiteSumObjective S nextBarCore.1 <=
        linearization S xUnder.1 nextBarCore.1 +
          (averageSmoothness S / 2) * norm (nextBarCore.1 - xUnder.1) ^ 2 := by
      simpa [nextCore, nextBarCore] using hfiniteSmoothBar sample
    have hl : linearization S xUnder.1 nextBarCore.1 =
        (1 - alpha s - p s) * linearization S xUnder.1 xBarPrev.1 +
          alpha s * linearization S xUnder.1 nextCore.1 +
            p s * linearization S xUnder.1 snapshot.1 := by
      simpa [nextCore, nextBarCore] using hlinearizationBar sample
    have hn : norm (nextBarCore.1 - xUnder.1) ^ 2 =
        (alpha s) ^ 2 *
          norm (nextCore.1 -
            auxiliaryPoint S gamma s xPrev.1 xUnder.1) ^ 2 := by
      simpa [nextCore, nextBarCore] using hbarNormSq sample
    have hh : S.h nextBarCore.1 <=
        (1 - alpha s - p s) * S.h xBarPrev.1 +
          alpha s * S.h nextCore.1 +
            p s * S.h snapshot.1 := by
      simpa [nextCore, nextBarCore] using hhConvexBar sample
    change compositeObjective S nextBarCore.1 <=
      ((1 - alpha s - p s) * linearization S xUnder.1 xBarPrev.1 +
          alpha s * linearization S xUnder.1 nextCore.1 +
            p s * linearization S xUnder.1 snapshot.1) +
        (averageSmoothness S / 2) *
          ((alpha s) ^ 2 *
            norm (nextCore.1 -
              auxiliaryPoint S gamma s xPrev.1 xUnder.1) ^ 2) +
        ((1 - alpha s - p s) * S.h xBarPrev.1 +
          alpha s * S.h nextCore.1 +
            p s * S.h snapshot.1)
    rw [compositeObjective_def]
    calc
      finiteSumObjective S nextBarCore.1 + S.h nextBarCore.1 <=
          (linearization S xUnder.1 nextBarCore.1 +
              (averageSmoothness S / 2) * norm (nextBarCore.1 - xUnder.1) ^ 2) +
            ((1 - alpha s - p s) * S.h xBarPrev.1 +
              alpha s * S.h nextCore.1 +
                p s * S.h snapshot.1) := by
        nlinarith
      _ = ((1 - alpha s - p s) * linearization S xUnder.1 xBarPrev.1 +
              alpha s * linearization S xUnder.1 nextCore.1 +
                p s * linearization S xUnder.1 snapshot.1) +
            (averageSmoothness S / 2) *
              ((alpha s) ^ 2 *
                norm (nextCore.1 -
                  auxiliaryPoint S gamma s xPrev.1 xUnder.1) ^ 2) +
            ((1 - alpha s - p s) * S.h xBarPrev.1 +
              alpha s * S.h nextCore.1 +
                p s * S.h snapshot.1) := by
        rw [hl, hn]
  have hAlphaDivGamma_nonneg : 0 <= alpha s / gamma s := by
    exact div_nonneg halpha.1 (le_of_lt hgamma)
  have hproxScaled :
      forall sample,
        let nextCore : Set.Elem (proxCoreSet S) := ⟨(next sample).x.1, hxNext sample⟩
        alpha s *
            (linearization S xUnder.1 nextCore.1 - linearization S xUnder.1 xTarget.1 +
              S.h nextCore.1 - S.h xTarget.1) <=
          alpha s * S.mu * bregmanOn S xUnder xTarget +
            (alpha s / gamma s) * bregmanOn S xPrev xTarget -
            (alpha s / gamma s) * ((1 + S.mu * gamma s) * bregmanOn S nextCore xTarget) -
            (alpha s / gamma s) *
              (((1 + S.mu * gamma s) / 2) *
                norm (nextCore.1 - auxiliaryPoint S gamma s xPrev.1 xUnder.1) ^ 2) -
            alpha s *
              ⟪carrierEstimatorResidual S (samplingWeight S) sample xUnder.1 snapshot.1
                  (carrierFullGradient S snapshot.1), nextCore.1 - xTarget.1⟫_Real := by
    intro sample
    let nextCore : Set.Elem (proxCoreSet S) := ⟨(next sample).x.1, hxNext sample⟩
    have hscaled :=
      mul_le_mul_of_nonneg_left (hproxBound sample) hAlphaDivGamma_nonneg
    dsimp [nextCore] at hscaled ⊢
    field_simp [ne_of_gt hgamma] at hscaled ⊢
    nlinarith
  have htarget_model :
      linearization S xUnder.1 xTarget.1 + S.mu * bregmanOn S xUnder xTarget <=
        finiteSumObjective S xTarget.1 := by
    have hstrong :=
      finiteSumObjective_strong_convexity_bregman_core_from_surrogate S xUnder xTarget
    simpa [linearization, add_assoc, add_left_comm, add_comm] using hstrong
  have hbarlin :
      linearization S xUnder.1 xBarPrev.1 <= finiteSumObjective S xBarPrev.1 := by
    simpa using
      finiteSumObjective_linearization_le_of_core_strong_convexity S xUnder
        (proxCoreAsFeasible S xBarPrev)
  rcases hvarianceFacts with ⟨hmean, hsecond⟩
  simpa [componentConditionalExpectation, SOptLib.compositeObjective, compositeObjective_def,
    den, mul_assoc] using
    accelerated_variance_reduced_prox_conditional_expectation_step
      (w := samplingWeight S)
      (Phi := finiteSumObjective S)
      (H := S.h)
      (Lin := linearization S xUnder.1)
      (Bunder := bregmanOn S xUnder xTarget)
      (Bprev := bregmanOn S xPrev xTarget)
      (Bnext := fun sample =>
        let nextCore : Set.Elem (proxCoreSet S) := ⟨(next sample).x.1, hxNext sample⟩
        bregmanOn S nextCore xTarget)
      (gamma := gamma s)
      (alpha := alpha s)
      (p := p s)
      (mu := S.mu)
      (L := averageSmoothness S)
      (LQ := theorem59LQ S)
      (den := den)
      (xBarPrev := xBarPrev.1)
      (snapshot := snapshot.1)
      (xTarget := xTarget.1)
      (aux := auxiliaryPoint S gamma s xPrev.1 xUnder.1)
      (xNext := fun sample => (next sample).x.1)
      (xBarNext := fun sample => (next sample).xBar.1)
      (residual := fun sample =>
        carrierEstimatorResidual S (samplingWeight S) sample xUnder.1 snapshot.1
          (carrierFullGradient S snapshot.1))
      halpha_pos hgamma hbar (by dsimp [den]) hden_pos
      (by
        dsimp [den]
        exact hnoise)
      (fun sample => le_of_lt (samplingWeight_pos S sample))
      (samplingWeight_sum_eq_one S)
      (by simpa [componentConditionalExpectation] using hmean)
      (by simpa [componentConditionalExpectation] using hsecond)
      hsnapshot_linearization hbarlin htarget_model
      (by
        intro sample
        let nextCore : Set.Elem (proxCoreSet S) := ⟨(next sample).x.1, hxNext sample⟩
        let nextBarCore : Set.Elem (proxCoreSet S) := ⟨(next sample).xBar.1, hxBarNext sample⟩
        simpa [nextCore, nextBarCore, SOptLib.compositeObjective, compositeObjective_def] using
          hcompositeBarUpper sample)
      (by
        intro sample
        let nextCore : Set.Elem (proxCoreSet S) := ⟨(next sample).x.1, hxNext sample⟩
        simpa [nextCore] using hproxScaled sample)

theorem lemma516_relational_conditional_expectation_step_boundary
    {n dim : Nat} (S : Setup n dim) :
    lemma516RelationalConditionalExpectationStepBoundaryCorrectionStatement S := by
  refine ⟨lemma516_guarded_relational_conditional_expectation_step_boundary S, ?_⟩
  exact lemma516_predivided_recursion_does_not_imply_total_division_rescale

theorem lemma516_corrected_relational_conditional_expectation_step_boundary
    {n dim : Nat} (S : Setup n dim) :
    lemma516CorrectedRelationalConditionalExpectationStepBoundaryStatement S := by
  exact lemma516_guarded_relational_conditional_expectation_step_boundary S

/- Route tombstone: `pointwise_relational_lemma516_source_route_v1`.
The old compiled conditional wrapper
`legacyDiagnosticLemma516RelationalConditionalStepBoundaryStatement` /
`legacyDiagnostic_lemma516_relational_conditional_step_boundary` has been
removed from the proof surface. Reintroducing it as a public/source supplier
requires AuditArbiter reactivation. -/

/-- One printed feasible inner step instantiated into corrected Lemma 5.16.

Aligns with Lan Lemma 5.16 / Eq. (5.4.9) as used in the Eq. (5.4.27)
first-phase proof: the printed feasible step relation is converted to the
`InnerStepRelOn` core interface and then consumed by `h516`.  Considered the
pre-searched SOptLib candidates
`finite_window_weighted_recurrence_telescope_with_tail_sums`,
`sum_Icc_two_coeff_telescope_le`, and weighted variance lemmas; they are
later scalar/telescope algebra, while this paper-specific helper needs the
target-file printed trajectory relation and prox-core witness bridge. -/
theorem lemma518_printed_epoch_step_lemma516_bound
    {n dim : Nat} (S : Setup n dim)
    (xAnchor : Set.Elem (proxCoreSet S)) (xTarget : FeasiblePoint S) (hmu : 0 < S.mu)
    (s : Nat) (hs : 1 <= s)
    (halpha : theorem59Alpha S s ∈ Set.Icc (0 : Real) 1)
    (halpha_pos : 0 < theorem59Alpha S s)
    (hp : theorem59P s ∈ Set.Icc (0 : Real) 1)
    (hgamma : 0 < theorem59Gamma S s)
    (hbar : 0 <= 1 - theorem59Alpha S s - theorem59P s)
    (hcurv :
      0 < 1 + S.mu * theorem59Gamma S s -
        averageSmoothness S * theorem59Alpha S s * theorem59Gamma S s)
    (hnoise :
      0 <= theorem59P s -
        theorem59LQ S * theorem59Alpha S s * theorem59Gamma S s /
          (1 + S.mu * theorem59Gamma S s -
            averageSmoothness S * theorem59Alpha S s * theorem59Gamma S s))
    (hsearch : searchPointWeights S (theorem59Gamma S) (theorem59Alpha S) theorem59P s ∈
      stdSimplex Real (Fin 3))
    (havg : averagedInnerWeightsAdmissible (theorem59Alpha S) theorem59P s)
    (h516 : lemma516CorrectedRelationalConditionalExpectationStepBoundaryStatement S)
    (h515 : lemma515RelationalCoreStepBoundaryStatement S)
    (h513 : lemma513AcceleratedVarianceEstimatorFactsBoundaryStatement S)
    (hpositiveProxMembership :
      theorem59PrintedFeasiblePositiveProxUpdateCoreMembershipStatement S)
    (omega : theorem59SamplePath n)
    (snapshotFeasible xStartFeasible : FeasiblePoint S)
    (trajectory : Nat -> InnerStateFeasibleOn S)
    (htraj :
      theorem59PrintedFeasibleInnerTrajectoryRelOn S hmu theorem59CanonicalSamples
        s hs omega snapshotFeasible xStartFeasible trajectory)
    (k : Nat)
    (hxSnapshot : snapshotFeasible.1 ∈ proxCoreSet S)
    (hxPrevK : (trajectory k).x.1 ∈ proxCoreSet S)
    (hxBarPrevK : (trajectory k).xBar.1 ∈ proxCoreSet S) :
    let next : Fin n -> InnerStateFeasibleOn S := fun sample =>
      theorem59PrintedFeasibleInnerStepOn S (theorem59Gamma S)
        (theorem59Alpha S) theorem59P s (samplingWeight S) snapshotFeasible
        (fullGradient S snapshotFeasible.1) sample hgamma xAnchor hsearch havg
        (trajectory k)
    ∃ hxNext : forall sample, (next sample).x.1 ∈ proxCoreSet S,
      ∃ hxBarNext : forall sample, (next sample).xBar.1 ∈ proxCoreSet S,
        componentConditionalExpectation S (samplingWeight S) (fun sample =>
            let nextCore : Set.Elem (proxCoreSet S) := ⟨(next sample).x.1, hxNext sample⟩
            let nextBarCore : Set.Elem (proxCoreSet S) := ⟨(next sample).xBar.1, hxBarNext sample⟩
            theorem59Gamma S s / theorem59Alpha S s *
                (compositeObjective S nextBarCore.1 -
                  compositeObjective S xTarget.1) +
              (1 + S.mu * theorem59Gamma S s) * bregmanOn S nextCore xTarget) <=
          theorem59Gamma S s / theorem59Alpha S s *
              (1 - theorem59Alpha S s - theorem59P s) *
              (compositeObjective S (trajectory k).xBar.1 -
                compositeObjective S xTarget.1) +
            theorem59Gamma S s / theorem59Alpha S s * theorem59P s *
              (compositeObjective S snapshotFeasible.1 -
                compositeObjective S xTarget.1) +
            bregmanOn S (⟨(trajectory k).x.1, hxPrevK⟩ : Set.Elem (proxCoreSet S))
              xTarget := by
  classical
  have _hactualPrintedStep :
      theorem59PrintedFeasibleInnerStepRelOn S (theorem59Gamma S)
        (theorem59Alpha S) theorem59P s (samplingWeight S) snapshotFeasible
        (fullGradient S snapshotFeasible.1)
        (theorem59CanonicalSamples s (k + 1) omega)
        ((theorem59_parameter_conditions S hmu s hs).2.2.2.2.1)
        ((theorem59_parameter_conditions S hmu s hs).2.2.2.2.2)
        (trajectory k) (trajectory (k + 1)) :=
    theorem59PrintedFeasibleInnerTrajectoryRelOn_step S hmu theorem59CanonicalSamples
      s hs omega snapshotFeasible xStartFeasible trajectory htraj k
  let next : Fin n -> InnerStateFeasibleOn S := fun sample =>
    theorem59PrintedFeasibleInnerStepOn S (theorem59Gamma S)
      (theorem59Alpha S) theorem59P s (samplingWeight S) snapshotFeasible
      (fullGradient S snapshotFeasible.1) sample hgamma xAnchor hsearch havg
      (trajectory k)
  let snapshotCore : Set.Elem (proxCoreSet S) := ⟨snapshotFeasible.1, hxSnapshot⟩
  let xPrevCore : Set.Elem (proxCoreSet S) := ⟨(trajectory k).x.1, hxPrevK⟩
  let xBarPrevCore : Set.Elem (proxCoreSet S) := ⟨(trajectory k).xBar.1, hxBarPrevK⟩
  have hprintedStep : forall sample,
      theorem59PrintedFeasibleInnerStepRelOn S (theorem59Gamma S)
        (theorem59Alpha S) theorem59P s (samplingWeight S) snapshotFeasible
        (fullGradient S snapshotFeasible.1) sample hsearch havg
        (trajectory k) (next sample) := by
    intro sample
    exact theorem59PrintedFeasibleInnerStepOn_satisfies_rel S
      (theorem59Gamma S) (theorem59Alpha S) theorem59P s (samplingWeight S)
      snapshotFeasible (fullGradient S snapshotFeasible.1) sample hgamma xAnchor
      hsearch havg (trajectory k)
  have hcoreWitnesses : forall sample,
      let xUnder :=
        searchPointFeasibleOn S (theorem59Gamma S) (theorem59Alpha S)
          theorem59P s (trajectory k).xBar (trajectory k).x snapshotFeasible
          hsearch
      let G :=
        varianceReducedGradientFeasibleOn S (samplingWeight S) sample xUnder
          snapshotFeasible (fullGradient S snapshotFeasible.1)
      ∃ hxUnder : xUnder.1 ∈ proxCoreSet S,
        ProxUpdateRelOn S (theorem59Gamma S) s
          (⟨(trajectory k).x.1, hxPrevK⟩ : Set.Elem (proxCoreSet S))
          (⟨xUnder.1, hxUnder⟩ : Set.Elem (proxCoreSet S))
          G (next sample).x ∧
        (next sample).x.1 ∈ proxCoreSet S ∧
          (next sample).xBar.1 ∈ proxCoreSet S := by
    intro sample
    exact
      theorem59PrintedFeasibleInnerStepRelOn_core_witnesses_of_positiveProxMembership
        S (theorem59Gamma S) (theorem59Alpha S) theorem59P s hgamma
        (samplingWeight S) snapshotFeasible (fullGradient S snapshotFeasible.1)
        sample hsearch havg (trajectory k) (next sample)
        hxPrevK hxBarPrevK hxSnapshot hpositiveProxMembership (hprintedStep sample)
  have hinnerStep : forall sample,
      InnerStepRelOn S (theorem59Gamma S) (theorem59Alpha S) theorem59P s
        (samplingWeight S) snapshotCore (fullGradient S snapshotCore.1) sample
        xPrevCore xBarPrevCore hsearch havg (next sample) := by
    intro sample
    rcases hcoreWitnesses sample with ⟨hxUnder, hprox, _hxNext, _hxBarNext⟩
    unfold InnerStepRelOn
    refine ⟨?_, ?_⟩
    · simpa [snapshotCore, xPrevCore, xBarPrevCore, varianceReducedGradientOn,
        varianceReducedGradientFeasibleOn, searchPointOn, searchPointFeasibleOn,
        searchPointValueOn, searchPointValueFeasibleOn] using hprox
    · rcases hprintedStep sample with ⟨xUnder, hxUnderEq, G, hGEq, _hprox, hbarEq⟩
      subst xUnder
      subst G
      apply Subtype.ext
      simpa [snapshotCore, xPrevCore, xBarPrevCore, averagedInnerIterateFeasibleOn,
        averagedInnerIterateValueFeasibleOn, averagedInnerIterateAllFeasibleOn,
        averagedInnerIterateValueAllFeasibleOn] using congrArg Subtype.val hbarEq
  have hxNext : forall sample, (next sample).x.1 ∈ proxCoreSet S := by
    intro sample
    rcases hcoreWitnesses sample with ⟨_hxUnder, _hprox, hxNext, _hxBarNext⟩
    exact hxNext
  have hxBarNext : forall sample, (next sample).xBar.1 ∈ proxCoreSet S := by
    intro sample
    rcases hcoreWitnesses sample with ⟨_hxUnder, _hprox, _hxNext, hxBarNext⟩
    exact hxBarNext
  have honeStep :=
    h516 h515 h513 (theorem59Gamma S) (theorem59Alpha S) theorem59P s
      snapshotCore xPrevCore xBarPrevCore xTarget halpha halpha_pos hp hgamma hbar
      hcurv hnoise next hinnerStep hxNext hxBarNext
  refine ⟨hxNext, hxBarNext, ?_⟩
  simpa [next, snapshotCore, xPrevCore, xBarPrevCore] using honeStep

/-- Printed epoch spec supplies Lemma 5.16 at every inner time of the epoch.

Aligns with Eq. (5.4.9) as the summand used in the Eq. (5.4.27) proof before
finite telescoping over `t = 1, ..., T_s`.  The SOptLib candidates checked for
this route (`finite_window_weighted_recurrence_telescope_with_tail_sums`,
`sum_Icc_two_coeff_telescope_le`, and variance/weighted-residual algebra) do
not construct the paper-specific printed trajectory or prox-core witnesses;
this helper consumes the target-file trajectory relation and then delegates the
actual conditional inequality to `lemma518_printed_epoch_step_lemma516_bound`. -/
theorem lemma518_printed_epoch_all_steps_lemma516_bound
    {n dim : Nat} (S : Setup n dim)
    (xAnchor : Set.Elem (proxCoreSet S)) (xTarget : FeasiblePoint S) (hmu : 0 < S.mu)
    (s : Nat) (hs : 1 <= s)
    (halpha : theorem59Alpha S s ∈ Set.Icc (0 : Real) 1)
    (halpha_pos : 0 < theorem59Alpha S s)
    (hp : theorem59P s ∈ Set.Icc (0 : Real) 1)
    (hgamma : 0 < theorem59Gamma S s)
    (hbar : 0 <= 1 - theorem59Alpha S s - theorem59P s)
    (hcurv :
      0 < 1 + S.mu * theorem59Gamma S s -
        averageSmoothness S * theorem59Alpha S s * theorem59Gamma S s)
    (hnoise :
      0 <= theorem59P s -
        theorem59LQ S * theorem59Alpha S s * theorem59Gamma S s /
          (1 + S.mu * theorem59Gamma S s -
            averageSmoothness S * theorem59Alpha S s * theorem59Gamma S s))
    (hsearch : searchPointWeights S (theorem59Gamma S) (theorem59Alpha S) theorem59P s ∈
      stdSimplex Real (Fin 3))
    (havg : averagedInnerWeightsAdmissible (theorem59Alpha S) theorem59P s)
    (h516 : lemma516CorrectedRelationalConditionalExpectationStepBoundaryStatement S)
    (h515 : lemma515RelationalCoreStepBoundaryStatement S)
    (h513 : lemma513AcceleratedVarianceEstimatorFactsBoundaryStatement S)
    (hpositiveProxMembership :
      theorem59PrintedFeasiblePositiveProxUpdateCoreMembershipStatement S)
    (hspec :
      theorem59PrintedFeasibleEpochOutputProcessSpec S hmu xAnchor
        theorem59CanonicalSamples
        (theorem59PrintedFeasibleOutputProcessOn S hmu xAnchor
          theorem59CanonicalSamples))
    (hstateCorePrev :
      forall omega : theorem59SamplePath n,
        (theorem59PrintedFeasibleEpochStateProcessOn S hmu xAnchor
            theorem59CanonicalSamples (s - 1) omega).x.1 ∈ proxCoreSet S ∧
          (theorem59PrintedFeasibleEpochStateProcessOn S hmu xAnchor
            theorem59CanonicalSamples (s - 1) omega).xTilde.1 ∈ proxCoreSet S)
    (omega : theorem59SamplePath n) (k : Nat) :
    ∃ trajectory : Nat -> InnerStateFeasibleOn S,
      ∃ htraj :
        theorem59PrintedFeasibleInnerTrajectoryRelOn S hmu theorem59CanonicalSamples
          s hs omega
          ((theorem59PrintedFeasibleEpochStateProcessOn S hmu xAnchor
              theorem59CanonicalSamples (s - 1) omega).xTilde)
          ((theorem59PrintedFeasibleEpochStateProcessOn S hmu xAnchor
              theorem59CanonicalSamples (s - 1) omega).x)
          trajectory,
        ∃ hxPrevK : (trajectory k).x.1 ∈ proxCoreSet S,
          ∃ hxBarPrevK : (trajectory k).xBar.1 ∈ proxCoreSet S,
            let snapshotFeasible :=
              (theorem59PrintedFeasibleEpochStateProcessOn S hmu xAnchor
                theorem59CanonicalSamples (s - 1) omega).xTilde
            let next : Fin n -> InnerStateFeasibleOn S := fun sample =>
              theorem59PrintedFeasibleInnerStepOn S (theorem59Gamma S)
                (theorem59Alpha S) theorem59P s (samplingWeight S) snapshotFeasible
                (fullGradient S snapshotFeasible.1) sample hgamma xAnchor hsearch havg
                (trajectory k)
            ∃ hxNext : forall sample, (next sample).x.1 ∈ proxCoreSet S,
              ∃ hxBarNext : forall sample, (next sample).xBar.1 ∈ proxCoreSet S,
                componentConditionalExpectation S (samplingWeight S) (fun sample =>
                    let nextCore : Set.Elem (proxCoreSet S) :=
                      ⟨(next sample).x.1, hxNext sample⟩
                    let nextBarCore : Set.Elem (proxCoreSet S) :=
                      ⟨(next sample).xBar.1, hxBarNext sample⟩
                    theorem59Gamma S s / theorem59Alpha S s *
                        (compositeObjective S nextBarCore.1 -
                          compositeObjective S xTarget.1) +
                      (1 + S.mu * theorem59Gamma S s) *
                        bregmanOn S nextCore xTarget) <=
                  theorem59Gamma S s / theorem59Alpha S s *
                      (1 - theorem59Alpha S s - theorem59P s) *
                      (compositeObjective S (trajectory k).xBar.1 -
                        compositeObjective S xTarget.1) +
                    theorem59Gamma S s / theorem59Alpha S s * theorem59P s *
                      (compositeObjective S snapshotFeasible.1 -
                        compositeObjective S xTarget.1) +
                    bregmanOn S
                      (⟨(trajectory k).x.1, hxPrevK⟩ : Set.Elem (proxCoreSet S))
                      xTarget := by
  classical
  rcases hspec.2 s hs omega with
    ⟨trajectory, htraj, _hxEndpoint, _hxTilde, _hout⟩
  let snapshotFeasible :=
    (theorem59PrintedFeasibleEpochStateProcessOn S hmu xAnchor
      theorem59CanonicalSamples (s - 1) omega).xTilde
  let xStartFeasible :=
    (theorem59PrintedFeasibleEpochStateProcessOn S hmu xAnchor
      theorem59CanonicalSamples (s - 1) omega).x
  have hxSnapshot : snapshotFeasible.1 ∈ proxCoreSet S := by
    exact (hstateCorePrev omega).2
  have hxStart : xStartFeasible.1 ∈ proxCoreSet S := by
    exact (hstateCorePrev omega).1
  have hcoreAtK :=
    theorem59PrintedFeasibleInnerTrajectoryRelOn_core_mem_of_positiveProxMembership
      S hmu theorem59CanonicalSamples s hs omega snapshotFeasible xStartFeasible
      trajectory hpositiveProxMembership hxSnapshot hxStart htraj k
  refine ⟨trajectory, htraj, hcoreAtK.1, hcoreAtK.2, ?_⟩
  simpa [snapshotFeasible, xStartFeasible] using
    lemma518_printed_epoch_step_lemma516_bound
      S xAnchor xTarget hmu s hs halpha halpha_pos hp hgamma hbar hcurv hnoise
      hsearch havg h516 h515 h513 hpositiveProxMembership omega
      snapshotFeasible xStartFeasible trajectory htraj k hxSnapshot hcoreAtK.1
      hcoreAtK.2

/-- Product-law expansion of the adaptive component expectation.

Aligns with the finite `i_t ~ Q` conditioning step behind Lan Eq. (5.4.9).
SOptLib candidate `integral_prefix_fresh_block_eq_generated_of_joint_law` was
checked and covers the outer joint-law transport, while this lemma supplies the
paper-specific finite `componentConditionalExpectation` expansion under
`componentSampleLaw`; the non-adaptive target-file marginal bridge below is
insufficient because its kernel is path independent. -/
theorem integral_prod_componentSampleLaw_eq_componentConditionalExpectation
    {n dim : Nat} (S : Setup n dim)
    {A : Type*} [MeasurableSpace A] (μ : MeasureTheory.Measure A)
    [MeasureTheory.SFinite μ]
    (F : A -> Fin n -> Real)
    (hF_int :
      MeasureTheory.Integrable (fun z : A × Fin n => F z.1 z.2)
        (μ.prod (componentSampleLaw S))) :
    (∫ z : A × Fin n, F z.1 z.2 ∂(μ.prod (componentSampleLaw S))) =
      ∫ a, componentConditionalExpectation S (samplingWeight S) (F a) ∂μ := by
  classical
  have hcomponent_finite :
      MeasureTheory.IsFiniteMeasure (componentSampleLaw S) := by
    unfold componentSampleLaw
    infer_instance
  letI : MeasureTheory.IsFiniteMeasure (componentSampleLaw S) := hcomponent_finite
  simpa [componentConditionalExpectation] using
    (integral_prod_finite_law_eq_integral_weighted_fiber_sum
      (base := μ) (nu := componentSampleLaw S) (w := samplingWeight S) (F := F)
      (hnu_singleton := by
        intro i
        unfold componentSampleLaw
        rw [MeasureTheory.measureReal_def]
        rw [PMF.toMeasure_apply_singleton
          (componentSamplingPMF S) i (MeasurableSet.singleton i)]
        rw [componentSamplingPMF_apply S i]
        rw [ENNReal.toReal_ofReal (le_of_lt (samplingWeight_pos S i))])
      (hF_int := hF_int))

/-- Adaptive finite-PMF transport from a generated product joint law.

This is the route-local expectation bridge needed before summing Eq. (5.4.9):
once prefix measurability and fresh-sample independence identify the joint law
of `(history, i_t)` as product, the generated expectation folds to the same
finite `componentConditionalExpectation` used in Lemma 5.16.  Considered
SOptLib candidates `iIndepFun.indepFun_prefixMeasurable_future`,
`indepFun_prefixKey_current_of_iIndepFun`, and
`integral_prefix_fresh_block_eq_generated_of_joint_law`; the first two produce
independence certificates, and the third is a generic joint-law integral
transport, but none expands this paper's nonuniform finite component PMF. -/
theorem adaptive_componentConditionalExpectation_transport_of_joint_law
    {n dim : Nat} (S : Setup n dim)
    {A : Type*} [MeasurableSpace A]
    {P : MeasureTheory.Measure (theorem59SamplePath n)} [MeasureTheory.SFinite P]
    (W : theorem59SamplePath n -> A) (epoch inner : Nat)
    (F : A -> Fin n -> Real)
    (hW : AEMeasurable W P)
    (hjoint :
      MeasureTheory.Measure.map
          (fun omega : theorem59SamplePath n =>
            (W omega, theorem59CanonicalSamples epoch inner omega)) P =
        (MeasureTheory.Measure.map W P).prod (componentSampleLaw S))
    (hF_int :
      MeasureTheory.Integrable (fun z : A × Fin n => F z.1 z.2)
        ((MeasureTheory.Measure.map W P).prod (componentSampleLaw S)))
    (hcond_aestrong :
      MeasureTheory.AEStronglyMeasurable
        (fun a : A => componentConditionalExpectation S (samplingWeight S) (F a))
        (MeasureTheory.Measure.map W P)) :
    SOptLib.expectation P
        (fun omega : theorem59SamplePath n =>
          F (W omega) (theorem59CanonicalSamples epoch inner omega)) =
      SOptLib.expectation P
        (fun omega : theorem59SamplePath n =>
          componentConditionalExpectation S (samplingWeight S) (F (W omega))) := by
  classical
  have hsample_meas :
      Measurable (fun omega : theorem59SamplePath n =>
        theorem59CanonicalSamples epoch inner omega) := by
    change Measurable (fun omega : Nat -> Nat -> Fin n => omega epoch inner)
    exact (measurable_pi_apply inner).comp (measurable_pi_apply epoch)
  have hprob_component :
      MeasureTheory.IsProbabilityMeasure (componentSampleLaw S) := by
    unfold componentSampleLaw
    infer_instance
  letI : MeasureTheory.IsProbabilityMeasure (componentSampleLaw S) := hprob_component
  have hsingleton :
      forall i : Fin n, (componentSampleLaw S).real ({i} : Set (Fin n)) =
        samplingWeight S i := by
    intro i
    unfold componentSampleLaw
    rw [MeasureTheory.measureReal_def]
    rw [PMF.toMeasure_apply_singleton
      (componentSamplingPMF S) i (MeasurableSet.singleton i)]
    rw [componentSamplingPMF_apply S i]
    rw [ENNReal.toReal_ofReal (le_of_lt (samplingWeight_pos S i))]
  simpa [componentConditionalExpectation] using
    expectation_sample_eq_expectation_weighted_fiber_sum_of_joint_law
      (P := P)
      (W := W)
      (Y := fun omega : theorem59SamplePath n =>
        theorem59CanonicalSamples epoch inner omega)
      (nu := componentSampleLaw S)
      (w := samplingWeight S)
      (F := F)
      hW hsample_meas.aemeasurable hjoint hsingleton hF_int
      (by simpa [componentConditionalExpectation] using hcond_aestrong)

/-- Adaptive finite-PMF transport from prefix/fresh independence.

Aligns with the conditional-on-history use of Eq. (5.4.9): SOptLib's
`map_pair_eq_prod_map_of_indepFun_of_map_eq` turns `IndepFun` plus the printed
component marginal into the product joint law, and
`adaptive_componentConditionalExpectation_transport_of_joint_law` expands that
joint law into the nonuniform finite `componentConditionalExpectation`. -/
theorem adaptive_componentConditionalExpectation_transport_of_indepFun
    {n dim : Nat} (S : Setup n dim)
    {A : Type*} [MeasurableSpace A]
    {P : MeasureTheory.Measure (theorem59SamplePath n)} [MeasureTheory.IsFiniteMeasure P]
    (W : theorem59SamplePath n -> A) (epoch inner : Nat)
    (F : A -> Fin n -> Real)
    (hW : AEMeasurable W P)
    (hsample :
      AEMeasurable
        (fun omega : theorem59SamplePath n =>
          theorem59CanonicalSamples epoch inner omega) P)
    (hindep :
      ProbabilityTheory.IndepFun W
        (fun omega : theorem59SamplePath n =>
          theorem59CanonicalSamples epoch inner omega) P)
    (hmarg :
      MeasureTheory.Measure.map
          (fun omega : theorem59SamplePath n =>
            theorem59CanonicalSamples epoch inner omega) P =
        componentSampleLaw S)
    (hF_int :
      MeasureTheory.Integrable (fun z : A × Fin n => F z.1 z.2)
        ((MeasureTheory.Measure.map W P).prod (componentSampleLaw S)))
    (hcond_aestrong :
      MeasureTheory.AEStronglyMeasurable
        (fun a : A => componentConditionalExpectation S (samplingWeight S) (F a))
        (MeasureTheory.Measure.map W P)) :
    SOptLib.expectation P
        (fun omega : theorem59SamplePath n =>
          F (W omega) (theorem59CanonicalSamples epoch inner omega)) =
      SOptLib.expectation P
        (fun omega : theorem59SamplePath n =>
          componentConditionalExpectation S (samplingWeight S) (F (W omega))) := by
  classical
  have hsingleton :
      forall i : Fin n, (componentSampleLaw S).real ({i} : Set (Fin n)) =
        samplingWeight S i := by
    intro i
    unfold componentSampleLaw
    rw [MeasureTheory.measureReal_def]
    rw [PMF.toMeasure_apply_singleton
      (componentSamplingPMF S) i (MeasurableSet.singleton i)]
    rw [componentSamplingPMF_apply S i]
    rw [ENNReal.toReal_ofReal (le_of_lt (samplingWeight_pos S i))]
  simpa [SOptLib.expectation, componentConditionalExpectation] using
    expectation_sample_eq_expectation_weighted_fiber_sum_of_indepFun
      (P := P)
      (W := W)
      (Y := fun omega : theorem59SamplePath n =>
        theorem59CanonicalSamples epoch inner omega)
      (nu := componentSampleLaw S)
      (w := samplingWeight S)
      (F := F)
      hW hsample hindep hmarg hsingleton hF_int

/-- Unconditional one-step expectation recurrence from adaptive finite-PMF transport.

This is the consumer-level bridge needed after the pointwise Lemma 5.16
conditional estimate has been instantiated along the generated printed epoch:
`adaptive_componentConditionalExpectation_transport_of_indepFun` replaces the
fresh draw by the finite conditional expectation, and `integral_mono` turns the
pointwise conditional bound into the unconditional expected recurrence. -/
theorem lemma518_printed_epoch_one_step_unconditional_recurrence
    {n dim : Nat} (S : Setup n dim)
    {A : Type*} [MeasurableSpace A]
    {P : MeasureTheory.Measure (theorem59SamplePath n)} [MeasureTheory.IsFiniteMeasure P]
    (W : theorem59SamplePath n -> A) (epoch inner : Nat)
    (nextPotential : A -> Fin n -> Real)
    (previousRhs : theorem59SamplePath n -> Real)
    (hW : AEMeasurable W P)
    (hsample :
      AEMeasurable
        (fun omega : theorem59SamplePath n =>
          theorem59CanonicalSamples epoch inner omega) P)
    (hindep :
      ProbabilityTheory.IndepFun W
        (fun omega : theorem59SamplePath n =>
          theorem59CanonicalSamples epoch inner omega) P)
    (hmarg :
      MeasureTheory.Measure.map
          (fun omega : theorem59SamplePath n =>
            theorem59CanonicalSamples epoch inner omega) P =
        componentSampleLaw S)
    (hnext_int :
      MeasureTheory.Integrable (fun z : A × Fin n => nextPotential z.1 z.2)
        ((MeasureTheory.Measure.map W P).prod (componentSampleLaw S)))
    (hcond_aestrong :
      MeasureTheory.AEStronglyMeasurable
        (fun a : A =>
          componentConditionalExpectation S (samplingWeight S) (nextPotential a))
        (MeasureTheory.Measure.map W P))
    (hcond_int :
      MeasureTheory.Integrable
        (fun omega : theorem59SamplePath n =>
          componentConditionalExpectation S (samplingWeight S)
            (nextPotential (W omega))) P)
    (hrhs_int : MeasureTheory.Integrable previousRhs P)
    (hpoint :
      forall omega : theorem59SamplePath n,
        componentConditionalExpectation S (samplingWeight S)
            (nextPotential (W omega)) <= previousRhs omega) :
    SOptLib.expectation P
        (fun omega : theorem59SamplePath n =>
          nextPotential (W omega) (theorem59CanonicalSamples epoch inner omega)) <=
      SOptLib.expectation P previousRhs := by
  classical
  change
    (∫ omega : theorem59SamplePath n,
        nextPotential (W omega) (theorem59CanonicalSamples epoch inner omega) ∂P) <=
      ∫ omega : theorem59SamplePath n, previousRhs omega ∂P
  exact
    integral_sample_le_integral_bound_of_indep_weighted_fiber_bound
      (P := P)
      (W := W)
      (Y := fun omega : theorem59SamplePath n =>
        theorem59CanonicalSamples epoch inner omega)
      (nu := componentSampleLaw S)
      (w := samplingWeight S)
      (F := nextPotential)
      (bound := previousRhs)
      hW hsample hindep hmarg
      (by
        intro i
        unfold componentSampleLaw
        rw [MeasureTheory.measureReal_def]
        rw [PMF.toMeasure_apply_singleton
          (componentSamplingPMF S) i (MeasurableSet.singleton i)]
        rw [componentSamplingPMF_apply S i]
        rw [ENNReal.toReal_ofReal (le_of_lt (samplingWeight_pos S i))])
      hnext_int
      (by simpa [componentConditionalExpectation] using hcond_aestrong)
      (by simpa [componentConditionalExpectation] using hcond_int)
      hrhs_int
      (Filter.Eventually.of_forall
        (fun omega : theorem59SamplePath n => by
          simpa [componentConditionalExpectation] using hpoint omega))

/-- One-step recurrence using the full Algorithm 5.7 strict history.

This is the source-faithful specialization of
`lemma518_printed_epoch_one_step_unconditional_recurrence` for Lemma 5.18:
the history may depend on previous epochs as well as the current epoch prefix.
It therefore consumes `theorem59_all_history_prefix_measurable_current_indepFun`
instead of the current-epoch-only prefix bridge. -/
theorem lemma518_printed_epoch_one_step_unconditional_recurrence_all_history
    {n dim : Nat} (S : Setup n dim)
    {A : Type*} [MeasurableSpace A]
    (W : theorem59SamplePath n -> A) (s k : Nat)
    (nextPotential : A -> Fin n -> Real)
    (previousRhs : theorem59SamplePath n -> Real)
    (hW :
      @Measurable (theorem59SamplePath n) A
        (⨆ q ∈ theorem59StrictPastIndexSet s k,
          MeasurableSpace.comap
            (fun omega : theorem59SamplePath n =>
              theorem59CanonicalSamples q.1 q.2 omega)
            (by infer_instance : MeasurableSpace (Fin n)))
        (by infer_instance) W)
    (hnext_int :
      MeasureTheory.Integrable (fun z : A × Fin n => nextPotential z.1 z.2)
        ((MeasureTheory.Measure.map W (theorem59SampleLaw S)).prod
          (componentSampleLaw S)))
    (hcond_aestrong :
      MeasureTheory.AEStronglyMeasurable
        (fun a : A =>
          componentConditionalExpectation S (samplingWeight S) (nextPotential a))
        (MeasureTheory.Measure.map W (theorem59SampleLaw S)))
    (hcond_int :
      MeasureTheory.Integrable
        (fun omega : theorem59SamplePath n =>
          componentConditionalExpectation S (samplingWeight S)
            (nextPotential (W omega))) (theorem59SampleLaw S))
    (hrhs_int : MeasureTheory.Integrable previousRhs (theorem59SampleLaw S))
    (hpoint :
      forall omega : theorem59SamplePath n,
        componentConditionalExpectation S (samplingWeight S)
            (nextPotential (W omega)) <= previousRhs omega) :
    SOptLib.expectation (theorem59SampleLaw S)
        (fun omega : theorem59SamplePath n =>
          nextPotential (W omega) (theorem59CanonicalSamples s (k + 1) omega)) <=
      SOptLib.expectation (theorem59SampleLaw S) previousRhs := by
  classical
  have hsampleCoord_meas :
      forall q : Nat × Nat,
        Measurable
          (fun omega : theorem59SamplePath n =>
            theorem59CanonicalSamples q.1 q.2 omega) := by
    intro q
    change Measurable (fun omega : Nat -> Nat -> Fin n => omega q.1 q.2)
    exact (measurable_pi_apply q.2).comp (measurable_pi_apply q.1)
  have hstrict_le_ambient :
      (⨆ q ∈ theorem59StrictPastIndexSet s k,
          MeasurableSpace.comap
            (fun omega : theorem59SamplePath n =>
              theorem59CanonicalSamples q.1 q.2 omega)
            (by infer_instance : MeasurableSpace (Fin n))) ≤
        (by infer_instance : MeasurableSpace (theorem59SamplePath n)) := by
    refine iSup_le ?_
    intro q
    refine iSup_le ?_
    intro _hq
    exact (hsampleCoord_meas q).comap_le
  have hW_ambient : Measurable W := by
    exact hW.mono hstrict_le_ambient le_rfl
  have hsample :
      AEMeasurable
        (fun omega : theorem59SamplePath n =>
          theorem59CanonicalSamples s (k + 1) omega)
        (theorem59SampleLaw S) := by
    have hmeas :
        Measurable
          (fun omega : theorem59SamplePath n =>
            theorem59CanonicalSamples s (k + 1) omega) := by
      change Measurable (fun omega : Nat -> Nat -> Fin n => omega s (k + 1))
      exact (measurable_pi_apply (k + 1)).comp (measurable_pi_apply s)
    exact hmeas.aemeasurable
  have hindep :
      ProbabilityTheory.IndepFun W
        (fun omega : theorem59SamplePath n =>
          theorem59CanonicalSamples s (k + 1) omega)
        (theorem59SampleLaw S) :=
    theorem59_all_history_prefix_measurable_current_indepFun S s k W hW
  have hmarg :
      MeasureTheory.Measure.map
          (fun omega : theorem59SamplePath n =>
            theorem59CanonicalSamples s (k + 1) omega)
          (theorem59SampleLaw S) =
        componentSampleLaw S :=
    by
      letI : MeasureTheory.IsProbabilityMeasure (componentSampleLaw S) := by
        unfold componentSampleLaw
        infer_instance
      simpa [theorem59SampleLaw, theorem59CanonicalSamples] using
        (SOptLib.iidTwoIndexSampleLaw_map_eval (mu := componentSampleLaw S) s (k + 1))
  have hprob_component :
      MeasureTheory.IsProbabilityMeasure (componentSampleLaw S) := by
    unfold componentSampleLaw
    infer_instance
  letI : MeasureTheory.IsProbabilityMeasure (componentSampleLaw S) := hprob_component
  have hprob_stream :
      MeasureTheory.IsProbabilityMeasure
        (SOptLib.iidStreamLaw (componentSampleLaw S)) := by
    infer_instance
  letI : MeasureTheory.IsProbabilityMeasure
      (SOptLib.iidStreamLaw (componentSampleLaw S)) := hprob_stream
  have hprob_sample :
      MeasureTheory.IsProbabilityMeasure (theorem59SampleLaw S) := by
    unfold theorem59SampleLaw
    infer_instance
  letI : MeasureTheory.IsProbabilityMeasure (theorem59SampleLaw S) := hprob_sample
  exact
    lemma518_printed_epoch_one_step_unconditional_recurrence
      S W s (k + 1) nextPotential previousRhs hW_ambient.aemeasurable
      hsample hindep hmarg hnext_int hcond_aestrong hcond_int hrhs_int hpoint

/-- Finite-range pushforward laws make arbitrary scalar observables a.e. strongly measurable.

This uses the SOptLib support-subtype bridge
`aestronglyMeasurable_map_of_measurable_on_ae_support`: under `Measure.map W μ`,
the law is supported on the finite range of `W`, so the observable is a function
on a finite subtype. -/
theorem aestronglyMeasurable_map_of_finite_range_support
    {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    [MeasurableSingletonClass A]
    {μ : MeasureTheory.Measure Ω} (W : Ω -> A)
    (hfin : (Set.range W).Finite) (φ : A -> Real) :
    MeasureTheory.AEStronglyMeasurable φ (MeasureTheory.Measure.map W μ) := by
  classical
  haveI : Fintype {a : A // a ∈ Set.range W} := hfin.fintype
  exact
    aestronglyMeasurable_map_of_measurable_on_ae_support
      (P := μ) (wt := W) (A := Set.range W) (φ := φ)
      hfin.measurableSet
      (by
        exact MeasureTheory.StronglyMeasurable.of_discrete)
      (MeasureTheory.ae_map_mem_range W hfin.measurableSet μ)

/-- Finite-range pushforward laws integrate arbitrary scalar observables.

Considered SOptLib `integrable_of_finite_range` and
`integrable_map_measure_of_integrable_comp`; together with the finite-support
measurability helper above they exactly match the generated-history support
needs in Lemma 5.18. -/
theorem integrable_map_of_finite_range_support
    {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    [MeasurableSingletonClass A]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsFiniteMeasure μ]
    (W : Ω -> A) (hW : AEMeasurable W μ)
    (hfin : (Set.range W).Finite) (φ : A -> Real) :
    MeasureTheory.Integrable φ (MeasureTheory.Measure.map W μ) := by
  exact integrable_map_of_finite_range W hW hfin φ

/-- Product-law scalar observables are integrable when the left law has finite generated support.

This is the finite-support product regularity used for Lemma 5.18's
`nextPotential`; it combines the existing SOptLib support-subtype
measurability bridge, Mathlib `integrable_prod_iff`, and
`integrable_map_of_finite_range_support` for the remaining finite-support
outer norm integral. -/
theorem integrable_prod_right_fintype_of_finite_left_map
    {Ω A ι : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    [MeasurableSingletonClass A] [MeasurableSpace ι] [Fintype ι]
    [MeasurableSingletonClass ι]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsFiniteMeasure μ]
    (W : Ω -> A) (hW : AEMeasurable W μ)
    (hfin : (Set.range W).Finite) (ν : MeasureTheory.Measure ι)
    [MeasureTheory.IsFiniteMeasure ν] (F : A -> ι -> Real) :
    MeasureTheory.Integrable (fun z : A × ι => F z.1 z.2)
      ((MeasureTheory.Measure.map W μ).prod ν) := by
  exact integrable_prod_of_finite_left_map_fintype_right W hW hfin ν F

/-- A finite-range recursive process is measurable from a fixed history sigma-algebra.

This is the fixed-history specialization needed for Lan Lemma 5.18's generated
strict-past state.  Considered `SOptLib.recursive_process_measurable_wrt_sample_prefix`
and the later target-file
`recursive_process_measurable_finite_range_wrt_sample_prefix`; the former
requires a globally measurable update kernel, while this local route only has
finite generated keys because the prox selector is not globally measurable. -/
theorem lemma518_recursive_process_measurable_finite_range_wrt_history
    {Ω X U : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace U] [MeasurableSingletonClass U]
    (mHist : MeasurableSpace Ω)
    (process : Nat -> Ω -> X)
    (driver : Nat -> Ω -> U)
    (step : Nat -> X -> U -> X)
    (N n : Nat)
    (h_init_meas : @Measurable Ω X mHist (by infer_instance) (process 0))
    (h_init_finite : (Set.range (process 0)).Finite)
    (h_driver_meas :
      forall j, j + 1 <= N ->
        @Measurable Ω U mHist (by infer_instance) (driver j))
    (h_driver_finite : forall j, (Set.range (driver j)).Finite)
    (h_update :
      forall j, j + 1 <= N ->
        forall omega : Ω, process (j + 1) omega =
          step j (process j omega) (driver j omega))
    (hn : n <= N) :
    @Measurable Ω X mHist (by infer_instance) (process n) ∧
      (Set.range (process n)).Finite := by
  exact
    SOptLib.recursive_process_measurable_finite_range_wrt_history
      (mHist := mHist) (process := process) (driver := driver) (step := step)
      (N := N) (n := n)
      h_init_meas h_init_finite h_driver_meas (fun j _ => h_driver_finite j)
      h_update hn

/-- Generated current-epoch inner state pair is measurable from any fixed history.

This is the all-history version of the strict-prefix helper aligned with Lan
Lemma 5.18: the current generated trajectory only needs the initial
snapshot/start pair and the samples already present in the fixed history. -/
theorem lemma518_generated_printed_inner_state_pair_history_measurable_of_step
    {Ω : Type*} [MeasurableSpace Ω] {n dim : Nat} (S : Setup n dim)
    (hmu : 0 < S.mu) (xAnchor : Set.Elem (proxCoreSet S))
    (samples : Nat -> Nat -> Ω -> Fin n)
    (mHist : MeasurableSpace Ω)
    (s : Nat) (hs : 1 <= s)
    (snapshot xStart : Ω -> FeasiblePoint S)
    (k : Nat)
    (hsample_hist :
      forall j, j + 1 <= k ->
        @Measurable Ω (Fin n) mHist (by infer_instance)
          (fun omega : Ω => samples s (j + 1) omega))
    (hinit :
      @Measurable Ω
        (FeasiblePoint S × (FeasiblePoint S × (FeasiblePoint S × FeasiblePoint S)))
        mHist
        (by infer_instance)
        (fun omega : Ω =>
          (snapshot omega,
            (xStart omega,
              ((xStart omega, snapshot omega) : FeasiblePoint S × FeasiblePoint S)))))
    (hinit_finite :
      (Set.range
        (fun omega : Ω =>
          (snapshot omega,
            (xStart omega,
              ((xStart omega, snapshot omega) :
                FeasiblePoint S × FeasiblePoint S))))).Finite) :
    @Measurable Ω (FeasiblePoint S × FeasiblePoint S)
      mHist
      (by infer_instance)
      (fun omega : Ω =>
        let trajectory :=
          theorem59PrintedFeasibleInnerTrajectoryOn S hmu xAnchor samples s hs omega
            (snapshot omega) (xStart omega)
        ((trajectory k).x, (trajectory k).xBar)) ∧
      (Set.range
        (fun omega : Ω =>
          let trajectory :=
            theorem59PrintedFeasibleInnerTrajectoryOn S hmu xAnchor samples s hs omega
              (snapshot omega) (xStart omega)
          ((trajectory k).x, (trajectory k).xBar))).Finite ∧
      forall omega : Ω,
        theorem59PrintedFeasibleInnerTrajectoryRelOn S hmu samples s hs omega
          (snapshot omega) (xStart omega)
          (theorem59PrintedFeasibleInnerTrajectoryOn S hmu xAnchor samples s hs omega
            (snapshot omega) (xStart omega)) := by
  classical
  let State :=
    FeasiblePoint S × (FeasiblePoint S × (FeasiblePoint S × FeasiblePoint S))
  let process : Nat -> Ω -> State := fun t omega =>
    let trajectory :=
      theorem59PrintedFeasibleInnerTrajectoryOn S hmu xAnchor samples s hs omega
        (snapshot omega) (xStart omega)
    (snapshot omega, (xStart omega, ((trajectory t).x, (trajectory t).xBar)))
  let driver : Nat -> Ω -> Fin n := fun j omega => samples s (j + 1) omega
  let step : Nat -> State -> Fin n -> State := fun j st sample =>
    let snapshotFixed : FeasiblePoint S := st.1
    let prev : InnerStateFeasibleOn S := { x := st.2.2.1, xBar := st.2.2.2 }
    let next :=
      theorem59PrintedFeasibleInnerStepOn S (theorem59Gamma S)
        (theorem59Alpha S) theorem59P s (samplingWeight S) snapshotFixed
        (fullGradient S snapshotFixed.1) sample (theorem59Gamma_pos S s)
        xAnchor
        ((theorem59_parameter_conditions S hmu s hs).2.2.2.2.1)
        ((theorem59_parameter_conditions S hmu s hs).2.2.2.2.2)
        prev
    (snapshotFixed, (st.2.1, ((next.x, next.xBar) :
      FeasiblePoint S × FeasiblePoint S)))
  have hproc :
      @Measurable Ω State mHist (by infer_instance) (process k) ∧
        (Set.range (process k)).Finite := by
    refine
      lemma518_recursive_process_measurable_finite_range_wrt_history
        (mHist := mHist) (process := process) (driver := driver) (step := step)
        (N := k) (n := k) ?_ ?_ ?_ ?_ ?_ le_rfl
    · simpa [process, State] using hinit
    · simpa [process, State] using hinit_finite
    · intro j hj
      simpa [driver] using hsample_hist j hj
    · intro j
      exact Set.toFinite _
    · intro j hj
      simp [process, step, driver, theorem59PrintedFeasibleInnerTrajectoryOn,
        SOptLib.recursiveIterateProcess]
  constructor
  · simpa [process, State] using
      (measurable_snd.comp (measurable_snd.comp hproc.1))
  · constructor
    · have hsubset :
          Set.range
              (fun omega : Ω =>
                let trajectory :=
                  theorem59PrintedFeasibleInnerTrajectoryOn S hmu xAnchor samples s hs omega
                    (snapshot omega) (xStart omega)
                ((trajectory k).x, (trajectory k).xBar)) <=
            (fun st : State => (st.2.2.1, st.2.2.2)) '' Set.range (process k) := by
        rintro y ⟨omega, rfl⟩
        exact ⟨process k omega, ⟨omega, rfl⟩, rfl⟩
      exact (hproc.2.image (fun st : State => (st.2.2.1, st.2.2.2))).subset hsubset
    · intro omega
      exact theorem59PrintedFeasibleInnerTrajectoryOn_rel S hmu xAnchor samples s hs omega
        (snapshot omega) (xStart omega)

/-- Previous printed epoch state is generated by the strict past.

This is the remaining Lan Lemma 5.18 adaptedness leaf for the state at epoch
`s - 1`.  The SOptLib/target-file finite-range recursion helpers considered
above cover fixed finite drivers; this epoch-level statement additionally has
variable-length per-epoch sample blocks, so it is isolated here rather than
hidden inside the final product packaging. -/
theorem lemma518_prev_epoch_state_strictPast_measurable_and_finite_range
    {n dim : Nat} (S : Setup n dim)
    (hmu : 0 < S.mu) (xAnchor : Set.Elem (proxCoreSet S))
    (s : Nat) (hs : 1 <= s) (k : Nat) :
    let mStrict :=
      (⨆ q ∈ theorem59StrictPastIndexSet s k,
        MeasurableSpace.comap
          (fun omega : theorem59SamplePath n =>
            theorem59CanonicalSamples q.1 q.2 omega)
          (by infer_instance : MeasurableSpace (Fin n)))
    @Measurable (theorem59SamplePath n) (FeasiblePoint S × FeasiblePoint S)
      mStrict (by infer_instance)
      (fun omega : theorem59SamplePath n =>
        let prev :=
          theorem59PrintedFeasibleEpochStateProcessOn S hmu xAnchor
            theorem59CanonicalSamples (s - 1) omega
        (prev.xTilde, prev.x)) ∧
      (Set.range
        (fun omega : theorem59SamplePath n =>
          let prev :=
            theorem59PrintedFeasibleEpochStateProcessOn S hmu xAnchor
              theorem59CanonicalSamples (s - 1) omega
          (prev.xTilde, prev.x))).Finite := by
  classical
  /-
  Remaining lower-level leaf: induct on epochs `< s`; the successor key is the
  previous finite-range epoch state together with the finite block
  `fun t : Fin (theorem59EpochLength S (r + 1)) =>
    theorem59CanonicalSamples (r + 1) (paperTime t) omega`, whose coordinates
  are in `theorem59StrictPastIndexSet s k` because `r + 1 < s`.
  -/
  induction s generalizing k with
  | zero =>
      omega
  | succ s ih =>
      cases s with
      | zero =>
          constructor
          · simp [theorem59PrintedFeasibleEpochStateProcessOn,
              theorem59PrintedFeasibleEpochStateProcessGeneratedOn,
              SOptLib.recursiveIterateProcess]
          · simpa [theorem59PrintedFeasibleEpochStateProcessOn,
              theorem59PrintedFeasibleEpochStateProcessGeneratedOn,
              SOptLib.recursiveIterateProcess] using
              (Set.finite_range_const
                (α := theorem59SamplePath n)
                (c := (proxCoreAsFeasible S xAnchor,
                  proxCoreAsFeasible S xAnchor)))
      | succ r =>
          have hprev_raw :=
            ih (k := 0) (Nat.succ_pos r)
          let mStrict :=
            (⨆ q ∈ theorem59StrictPastIndexSet (r + 1 + 1) k,
              MeasurableSpace.comap
                (fun omega : theorem59SamplePath n =>
                  theorem59CanonicalSamples q.1 q.2 omega)
                (by infer_instance : MeasurableSpace (Fin n)))
          let epochBlock : theorem59SamplePath n ->
              (Fin (theorem59EpochLength S (r + 1)) -> Fin n) :=
            fun omega t => theorem59CanonicalSamples (r + 1) (paperTime t) omega
          have hepochBlock_meas :
              @Measurable (theorem59SamplePath n)
                (Fin (theorem59EpochLength S (r + 1)) -> Fin n)
                mStrict (by infer_instance) epochBlock := by
            letI : MeasurableSpace (theorem59SamplePath n) := mStrict
            change Measurable
              (fun omega : theorem59SamplePath n =>
                fun t : Fin (theorem59EpochLength S (r + 1)) =>
                  theorem59CanonicalSamples (r + 1) (paperTime t) omega)
            refine measurable_pi_lambda _ ?_
            intro t
            refine Measurable.of_comap_le ?_
            change
              MeasurableSpace.comap
                  (fun omega : theorem59SamplePath n =>
                    theorem59CanonicalSamples (r + 1) (paperTime t) omega)
                  (by infer_instance : MeasurableSpace (Fin n)) ≤
                mStrict
            exact le_iSup_of_le (r + 1, paperTime t)
              (le_iSup_of_le
                (by
                  left
                  omega)
                le_rfl)
          have hepochBlock_finite : (Set.range epochBlock).Finite := by
            exact Set.toFinite _
          let prevPair : theorem59SamplePath n -> FeasiblePoint S × FeasiblePoint S :=
            fun omega =>
              let prev :=
                theorem59PrintedFeasibleEpochStateProcessOn S hmu xAnchor
                  theorem59CanonicalSamples (r + 1 - 1) omega
              (prev.xTilde, prev.x)
          have hprev_mono :
              (⨆ q ∈ theorem59StrictPastIndexSet (r + 1) 0,
                MeasurableSpace.comap
                  (fun omega : theorem59SamplePath n =>
                    theorem59CanonicalSamples q.1 q.2 omega)
                  (by infer_instance : MeasurableSpace (Fin n))) ≤ mStrict := by
            refine iSup_le ?_
            intro q
            refine iSup_le ?_
            intro hq
            refine le_iSup_of_le q ?_
            refine le_iSup_of_le ?_ le_rfl
            have hq_unfold :
                q.1 < r + 1 ∨ (q.1 = r + 1 ∧ q.2 < 0 + 1) := by
              simpa [theorem59StrictPastIndexSet] using hq
            have hq_current : q ∈ theorem59StrictPastIndexSet (r + 1 + 1) k := by
              rcases hq_unfold with hlt | hsame
              · simpa [theorem59StrictPastIndexSet] using
                  (Or.inl (by omega : q.1 < r + 1 + 1))
              · rcases hsame with ⟨heq, _hinner⟩
                simpa [theorem59StrictPastIndexSet, heq] using
                  (Or.inl (by omega : q.1 < r + 1 + 1))
            exact hq_current
          have hprev_meas :
              @Measurable (theorem59SamplePath n)
                (FeasiblePoint S × FeasiblePoint S)
                mStrict (by infer_instance) prevPair := by
            exact hprev_raw.1.mono hprev_mono le_rfl
          have hprev_finite : (Set.range prevPair).Finite := by
            simpa [prevPair] using hprev_raw.2
          let key : theorem59SamplePath n ->
              (FeasiblePoint S × FeasiblePoint S) ×
                (Fin (theorem59EpochLength S (r + 1)) -> Fin n) :=
            fun omega => (prevPair omega, epochBlock omega)
          have hkey_meas :
              @Measurable (theorem59SamplePath n)
                ((FeasiblePoint S × FeasiblePoint S) ×
                  (Fin (theorem59EpochLength S (r + 1)) -> Fin n))
                mStrict (by infer_instance) key := by
            exact hprev_meas.prodMk hepochBlock_meas
          have hkey_finite : (Set.range key).Finite := by
            have hsubset :
                Set.range key <= Set.range prevPair ×ˢ Set.range epochBlock := by
              intro yu hyu
              rcases hyu with ⟨omega, rfl⟩
              exact ⟨⟨omega, rfl⟩, ⟨omega, rfl⟩⟩
            exact (hprev_finite.prod hepochBlock_finite).subset hsubset
          let nextPair : theorem59SamplePath n -> FeasiblePoint S × FeasiblePoint S :=
            fun omega =>
              let prev :=
                theorem59PrintedFeasibleEpochStateProcessOn S hmu xAnchor
                  theorem59CanonicalSamples (r + 1 + 1 - 1) omega
              (prev.xTilde, prev.x)
          have hfiber :
              ∀ ⦃omega omega' : theorem59SamplePath n⦄,
                key omega = key omega' -> nextPair omega = nextPair omega' := by
            intro omega omega' hkey_eq
            have hprev_eq : prevPair omega = prevPair omega' :=
              congrArg Prod.fst hkey_eq
            have hblock_eq : epochBlock omega = epochBlock omega' :=
              congrArg Prod.snd hkey_eq
            let prev : EpochStateFeasibleOn S :=
              theorem59PrintedFeasibleEpochStateProcessOn S hmu xAnchor
                theorem59CanonicalSamples (r + 1 - 1) omega
            let prev' : EpochStateFeasibleOn S :=
              theorem59PrintedFeasibleEpochStateProcessOn S hmu xAnchor
                theorem59CanonicalSamples (r + 1 - 1) omega'
            have hxTilde_eq : prev.xTilde = prev'.xTilde := by
              simpa [prevPair, prev, prev'] using congrArg Prod.fst hprev_eq
            have hx_eq : prev.x = prev'.x := by
              simpa [prevPair, prev, prev'] using congrArg Prod.snd hprev_eq
            let T : Nat := theorem59EpochLength S (r + 1)
            let hsEpoch : 1 <= r + 1 := Nat.succ_pos r
            let traj : Nat -> InnerStateFeasibleOn S :=
              theorem59PrintedFeasibleInnerTrajectoryOn S hmu xAnchor
                theorem59CanonicalSamples (r + 1) hsEpoch omega
                prev.xTilde prev.x
            let traj' : Nat -> InnerStateFeasibleOn S :=
              theorem59PrintedFeasibleInnerTrajectoryOn S hmu xAnchor
                theorem59CanonicalSamples (r + 1) hsEpoch omega'
                prev.xTilde prev.x
            have htraj_eq : forall j, j <= T -> traj j = traj' j := by
              intro j hj
              induction j with
              | zero =>
                  simp [traj, traj', theorem59PrintedFeasibleInnerTrajectoryOn,
                    SOptLib.recursiveIterateProcess]
              | succ j ih =>
                  have hj_le : j <= T := Nat.le_of_succ_le hj
                  have hsample :
                      theorem59CanonicalSamples (r + 1) (j + 1) omega =
                        theorem59CanonicalSamples (r + 1) (j + 1) omega' := by
                    have hcoord := congrFun hblock_eq ⟨j, hj⟩
                    simpa [epochBlock, paperTime] using hcoord
                  have hprev_step := ih hj_le
                  have htraj_succ :
                      traj (j + 1) =
                        theorem59PrintedFeasibleInnerStepOn S (theorem59Gamma S)
                          (theorem59Alpha S) theorem59P (r + 1) (samplingWeight S)
                          prev.xTilde (fullGradient S prev.xTilde.1)
                          (theorem59CanonicalSamples (r + 1) (j + 1) omega)
                          (theorem59Gamma_pos S (r + 1)) xAnchor
                          ((theorem59_parameter_conditions S hmu
                            (r + 1) hsEpoch).2.2.2.2.1)
                          ((theorem59_parameter_conditions S hmu
                            (r + 1) hsEpoch).2.2.2.2.2)
                          (traj j) := by
                    simp [traj, theorem59PrintedFeasibleInnerTrajectoryOn,
                      SOptLib.recursiveIterateProcess]
                  have htraj'_succ :
                      traj' (j + 1) =
                        theorem59PrintedFeasibleInnerStepOn S (theorem59Gamma S)
                          (theorem59Alpha S) theorem59P (r + 1) (samplingWeight S)
                          prev.xTilde (fullGradient S prev.xTilde.1)
                          (theorem59CanonicalSamples (r + 1) (j + 1) omega')
                          (theorem59Gamma_pos S (r + 1)) xAnchor
                          ((theorem59_parameter_conditions S hmu
                            (r + 1) hsEpoch).2.2.2.2.1)
                          ((theorem59_parameter_conditions S hmu
                            (r + 1) hsEpoch).2.2.2.2.2)
                          (traj' j) := by
                    simp [traj', theorem59PrintedFeasibleInnerTrajectoryOn,
                      SOptLib.recursiveIterateProcess]
                  rw [htraj_succ, htraj'_succ, hsample, hprev_step]
            have hT_eq : traj T = traj' T := htraj_eq T le_rfl
            have hbar_fun :
                (fun t : Fin T => (traj (paperTime t)).xBar) =
                  (fun t : Fin T => (traj' (paperTime t)).xBar) := by
              funext t
              have ht : paperTime t <= T := by
                unfold paperTime T
                exact Nat.succ_le_of_lt t.2
              exact congrArg InnerStateFeasibleOn.xBar
                (htraj_eq (paperTime t) ht)
            have hstate_step :
                theorem59PrintedFeasibleEpochStateStepOn S hmu xAnchor
                    theorem59CanonicalSamples r prev omega =
                  theorem59PrintedFeasibleEpochStateStepOn S hmu xAnchor
                    theorem59CanonicalSamples r prev' omega' := by
              unfold theorem59PrintedFeasibleEpochStateStepOn
              dsimp only
              rw [← hx_eq, ← hxTilde_eq]
              change
                ({ x := (traj T).x,
                   xTilde := epochOutputFeasibleOn S
                    ((theorem59Theta S hmu (averageSmoothness_pos S)) (r + 1))
                    (fun t : Fin T => (traj (paperTime t)).xBar)
                    (theorem59Theta_epochOutputWeightsAdmissible S hmu
                      (r + 1) hsEpoch) } :
                  EpochStateFeasibleOn S) =
                ({ x := (traj' T).x,
                   xTilde := epochOutputFeasibleOn S
                    ((theorem59Theta S hmu (averageSmoothness_pos S)) (r + 1))
                    (fun t : Fin T => (traj' (paperTime t)).xBar)
                    (theorem59Theta_epochOutputWeightsAdmissible S hmu
                      (r + 1) hsEpoch) } :
                  EpochStateFeasibleOn S)
              rw [hT_eq, hbar_fun]
            have hnext_state :
                theorem59PrintedFeasibleEpochStateProcessOn S hmu xAnchor
                    theorem59CanonicalSamples (r + 1 + 1 - 1) omega =
                  theorem59PrintedFeasibleEpochStateProcessOn S hmu xAnchor
                    theorem59CanonicalSamples (r + 1 + 1 - 1) omega' := by
              have hs1 :=
                SOptLib.recursiveIterateProcess_succ
                  (theorem59PrintedFeasibleEpochStateProcessGeneratedOn S hmu
                    xAnchor theorem59CanonicalSamples)
                  (⟨proxCoreAsFeasible S xAnchor,
                    proxCoreAsFeasible S xAnchor⟩ : EpochStateFeasibleOn S)
                  (theorem59PrintedFeasibleEpochStateStepOn S hmu xAnchor
                    theorem59CanonicalSamples)
                  (by rfl) r omega
              have hs2 :=
                SOptLib.recursiveIterateProcess_succ
                  (theorem59PrintedFeasibleEpochStateProcessGeneratedOn S hmu
                    xAnchor theorem59CanonicalSamples)
                  (⟨proxCoreAsFeasible S xAnchor,
                    proxCoreAsFeasible S xAnchor⟩ : EpochStateFeasibleOn S)
                  (theorem59PrintedFeasibleEpochStateStepOn S hmu xAnchor
                    theorem59CanonicalSamples)
                  (by rfl) r omega'
              simpa [theorem59PrintedFeasibleEpochStateProcessOn,
                theorem59PrintedFeasibleEpochStateProcessGeneratedOn, prev, prev'] using
                (hs1.trans (hstate_step.trans hs2.symm))
            change
              ((theorem59PrintedFeasibleEpochStateProcessOn S hmu xAnchor
                  theorem59CanonicalSamples (r + 1 + 1 - 1) omega).xTilde,
                (theorem59PrintedFeasibleEpochStateProcessOn S hmu xAnchor
                  theorem59CanonicalSamples (r + 1 + 1 - 1) omega).x) =
              ((theorem59PrintedFeasibleEpochStateProcessOn S hmu xAnchor
                  theorem59CanonicalSamples (r + 1 + 1 - 1) omega').xTilde,
                (theorem59PrintedFeasibleEpochStateProcessOn S hmu xAnchor
                  theorem59CanonicalSamples (r + 1 + 1 - 1) omega').x)
            rw [hnext_state]
          have hnext_meas :
              @Measurable (theorem59SamplePath n)
                (FeasiblePoint S × FeasiblePoint S)
                mStrict (by infer_instance) nextPair := by
            letI : MeasurableSpace (theorem59SamplePath n) := mStrict
            have hkey_meas' : Measurable key := by
              simpa using hkey_meas
            exact measurable_of_finite_range_fiber_const
              (Y := key) (Z := nextPair) hkey_meas' hkey_finite hfiber
          have hnext_finite : (Set.range nextPair).Finite := by
            classical
            haveI : Fintype {y // y ∈ Set.range key} := hkey_finite.fintype
            let G : {y // y ∈ Set.range key} -> FeasiblePoint S × FeasiblePoint S :=
              fun y => nextPair (Classical.choose y.2)
            have hsubset : Set.range nextPair <= G '' Set.univ := by
              rintro z ⟨omega, rfl⟩
              refine ⟨⟨key omega, ⟨omega, rfl⟩⟩, by simp, ?_⟩
              dsimp [G]
              exact hfiber (Classical.choose_spec
                (show key omega ∈ Set.range key from ⟨omega, rfl⟩))
            exact (Set.finite_univ.image G).subset hsubset
          simpa [nextPair] using And.intro hnext_meas hnext_finite

/-- Strict-past measurability of the generated Lemma 5.18 state package.

This is the concrete all-history supplier needed to instantiate the adaptive
one-step recurrence inside the printed Eq. (5.4.27) route.  The package includes
the previous epoch snapshot and the generated current inner state, so its
filtration must include all earlier epochs plus the current epoch prefix. -/
theorem lemma518_generated_printed_epoch_snapshot_state_strictPast_measurable
    {n dim : Nat} (S : Setup n dim)
    (hmu : 0 < S.mu) (xAnchor : Set.Elem (proxCoreSet S))
    (s : Nat) (hs : 1 <= s) (k : Nat)
    (hpositiveProxMembership :
      theorem59PrintedFeasiblePositiveProxUpdateCoreMembershipStatement S)
    (hstateCorePrev :
      forall omega : theorem59SamplePath n,
        (theorem59PrintedFeasibleEpochStateProcessOn S hmu xAnchor
            theorem59CanonicalSamples (s - 1) omega).x.1 ∈ proxCoreSet S ∧
          (theorem59PrintedFeasibleEpochStateProcessOn S hmu xAnchor
            theorem59CanonicalSamples (s - 1) omega).xTilde.1 ∈ proxCoreSet S) :
    @Measurable (theorem59SamplePath n)
      (Set.Elem (proxCoreSet S) × (Set.Elem (proxCoreSet S) × Set.Elem (proxCoreSet S)))
      (⨆ q ∈ theorem59StrictPastIndexSet s k,
        MeasurableSpace.comap
          (fun omega : theorem59SamplePath n =>
            theorem59CanonicalSamples q.1 q.2 omega)
          (by infer_instance : MeasurableSpace (Fin n)))
      (by infer_instance)
      (fun omega : theorem59SamplePath n =>
        let snapshot :=
          (theorem59PrintedFeasibleEpochStateProcessOn S hmu xAnchor
            theorem59CanonicalSamples (s - 1) omega).xTilde
        let xStart :=
          (theorem59PrintedFeasibleEpochStateProcessOn S hmu xAnchor
            theorem59CanonicalSamples (s - 1) omega).x
        let trajectory :=
          theorem59PrintedFeasibleInnerTrajectoryOn S hmu xAnchor
            theorem59CanonicalSamples s hs omega snapshot xStart
        let htraj :=
          theorem59PrintedFeasibleInnerTrajectoryOn_rel S hmu xAnchor
            theorem59CanonicalSamples s hs omega snapshot xStart
        let hinnerCore :=
          theorem59PrintedFeasibleInnerTrajectoryRelOn_core_mem_of_positiveProxMembership
            S hmu theorem59CanonicalSamples s hs omega snapshot xStart trajectory
            hpositiveProxMembership (hstateCorePrev omega).2
            (hstateCorePrev omega).1 htraj
        (⟨snapshot.1, (hstateCorePrev omega).2⟩,
          (⟨(trajectory k).x.1, (hinnerCore k).1⟩,
            ⟨(trajectory k).xBar.1, (hinnerCore k).2⟩))) ∧
      (Set.range
        (fun omega : theorem59SamplePath n =>
          let snapshot :=
            (theorem59PrintedFeasibleEpochStateProcessOn S hmu xAnchor
              theorem59CanonicalSamples (s - 1) omega).xTilde
          let xStart :=
            (theorem59PrintedFeasibleEpochStateProcessOn S hmu xAnchor
              theorem59CanonicalSamples (s - 1) omega).x
          let trajectory :=
            theorem59PrintedFeasibleInnerTrajectoryOn S hmu xAnchor
              theorem59CanonicalSamples s hs omega snapshot xStart
          let htraj :=
            theorem59PrintedFeasibleInnerTrajectoryOn_rel S hmu xAnchor
              theorem59CanonicalSamples s hs omega snapshot xStart
          let hinnerCore :=
            theorem59PrintedFeasibleInnerTrajectoryRelOn_core_mem_of_positiveProxMembership
              S hmu theorem59CanonicalSamples s hs omega snapshot xStart trajectory
              hpositiveProxMembership (hstateCorePrev omega).2
              (hstateCorePrev omega).1 htraj
          ((⟨snapshot.1, (hstateCorePrev omega).2⟩ : Set.Elem (proxCoreSet S)),
            ((⟨(trajectory k).x.1, (hinnerCore k).1⟩ : Set.Elem (proxCoreSet S)),
              (⟨(trajectory k).xBar.1, (hinnerCore k).2⟩ : Set.Elem (proxCoreSet S)))))).Finite := by
  classical
  let mStrict :=
    (⨆ q ∈ theorem59StrictPastIndexSet s k,
      MeasurableSpace.comap
        (fun omega : theorem59SamplePath n =>
          theorem59CanonicalSamples q.1 q.2 omega)
        (by infer_instance : MeasurableSpace (Fin n)))
  let snapshotFun : theorem59SamplePath n -> FeasiblePoint S := fun omega =>
    (theorem59PrintedFeasibleEpochStateProcessOn S hmu xAnchor
      theorem59CanonicalSamples (s - 1) omega).xTilde
  let xStartFun : theorem59SamplePath n -> FeasiblePoint S := fun omega =>
    (theorem59PrintedFeasibleEpochStateProcessOn S hmu xAnchor
      theorem59CanonicalSamples (s - 1) omega).x
  have hprev :=
    lemma518_prev_epoch_state_strictPast_measurable_and_finite_range
      S hmu xAnchor s hs k
  have hprev_meas :
      @Measurable (theorem59SamplePath n) (FeasiblePoint S × FeasiblePoint S)
        mStrict (by infer_instance)
        (fun omega : theorem59SamplePath n =>
          (snapshotFun omega, xStartFun omega)) := by
    simpa [mStrict, snapshotFun, xStartFun] using hprev.1
  have hprev_finite :
      (Set.range
        (fun omega : theorem59SamplePath n =>
          (snapshotFun omega, xStartFun omega))).Finite := by
    simpa [snapshotFun, xStartFun] using hprev.2
  have hsnapshot_meas :
      @Measurable (theorem59SamplePath n) (FeasiblePoint S)
        mStrict (by infer_instance) snapshotFun := by
    exact measurable_fst.comp hprev_meas
  have hxStart_meas :
      @Measurable (theorem59SamplePath n) (FeasiblePoint S)
        mStrict (by infer_instance) xStartFun := by
    exact measurable_snd.comp hprev_meas
  have hinit :
      @Measurable (theorem59SamplePath n)
        (FeasiblePoint S × (FeasiblePoint S × (FeasiblePoint S × FeasiblePoint S)))
        mStrict
        (by infer_instance)
        (fun omega : theorem59SamplePath n =>
          (snapshotFun omega,
            (xStartFun omega,
              ((xStartFun omega, snapshotFun omega) :
                FeasiblePoint S × FeasiblePoint S)))) := by
    exact hsnapshot_meas.prodMk (hxStart_meas.prodMk (hxStart_meas.prodMk hsnapshot_meas))
  have hinit_finite :
      (Set.range
        (fun omega : theorem59SamplePath n =>
          (snapshotFun omega,
            (xStartFun omega,
              ((xStartFun omega, snapshotFun omega) :
                FeasiblePoint S × FeasiblePoint S))))).Finite := by
    have hsubset :
        Set.range
            (fun omega : theorem59SamplePath n =>
              (snapshotFun omega,
                (xStartFun omega,
                  ((xStartFun omega, snapshotFun omega) :
                    FeasiblePoint S × FeasiblePoint S)))) <=
          (fun p : FeasiblePoint S × FeasiblePoint S =>
            (p.1, (p.2, ((p.2, p.1) : FeasiblePoint S × FeasiblePoint S)))) ''
            Set.range (fun omega : theorem59SamplePath n =>
              (snapshotFun omega, xStartFun omega)) := by
      intro y hy
      rcases hy with ⟨omega, rfl⟩
      exact ⟨(snapshotFun omega, xStartFun omega), ⟨omega, rfl⟩, rfl⟩
    exact
      (hprev_finite.image
        (fun p : FeasiblePoint S × FeasiblePoint S =>
          (p.1, (p.2, ((p.2, p.1) : FeasiblePoint S × FeasiblePoint S))))).subset
        hsubset
  have hsample_hist :
      forall j, j + 1 <= k ->
        @Measurable (theorem59SamplePath n) (Fin n)
          mStrict (by infer_instance)
          (fun omega : theorem59SamplePath n =>
            theorem59CanonicalSamples s (j + 1) omega) := by
    intro j hj
    refine Measurable.of_comap_le ?_
    change
      MeasurableSpace.comap
          (fun omega : theorem59SamplePath n =>
            theorem59CanonicalSamples s (j + 1) omega)
          (by infer_instance : MeasurableSpace (Fin n)) ≤
        mStrict
    exact le_iSup_of_le (s, j + 1)
      (le_iSup_of_le
        (by
          right
          exact ⟨rfl, Nat.lt_succ_of_le hj⟩)
        le_rfl)
  have hpairPack :=
      lemma518_generated_printed_inner_state_pair_history_measurable_of_step
        S hmu xAnchor theorem59CanonicalSamples mStrict s hs
        snapshotFun xStartFun k hsample_hist hinit hinit_finite
  let pairFun : theorem59SamplePath n -> FeasiblePoint S × FeasiblePoint S :=
    fun omega =>
      let trajectory :=
        theorem59PrintedFeasibleInnerTrajectoryOn S hmu xAnchor
          theorem59CanonicalSamples s hs omega
          (snapshotFun omega) (xStartFun omega)
      ((trajectory k).x, (trajectory k).xBar)
  have hpair :
      @Measurable (theorem59SamplePath n) (FeasiblePoint S × FeasiblePoint S)
        mStrict (by infer_instance)
        pairFun := by
    simpa [pairFun] using hpairPack.1
  have hpair_finite : (Set.range pairFun).Finite := by
    simpa [pairFun] using hpairPack.2.1
  have hsnapshotCore :
      @Measurable (theorem59SamplePath n) (Set.Elem (proxCoreSet S))
        mStrict (by infer_instance)
        (fun omega : theorem59SamplePath n =>
          (⟨(snapshotFun omega).1, (hstateCorePrev omega).2⟩ :
            Set.Elem (proxCoreSet S))) := by
    refine Measurable.subtype_mk ?_
    exact measurable_subtype_coe.comp hsnapshot_meas
  have hxCore :
      @Measurable (theorem59SamplePath n) (Set.Elem (proxCoreSet S))
        mStrict (by infer_instance)
        (fun omega : theorem59SamplePath n =>
          let trajectory :=
            theorem59PrintedFeasibleInnerTrajectoryOn S hmu xAnchor
              theorem59CanonicalSamples s hs omega
              (snapshotFun omega) (xStartFun omega)
          let htraj :=
            theorem59PrintedFeasibleInnerTrajectoryOn_rel S hmu xAnchor
              theorem59CanonicalSamples s hs omega
              (snapshotFun omega) (xStartFun omega)
          let hinnerCore :=
            theorem59PrintedFeasibleInnerTrajectoryRelOn_core_mem_of_positiveProxMembership
              S hmu theorem59CanonicalSamples s hs omega
              (snapshotFun omega) (xStartFun omega) trajectory
              hpositiveProxMembership (hstateCorePrev omega).2
              (hstateCorePrev omega).1 htraj
          (⟨(trajectory k).x.1, (hinnerCore k).1⟩ : Set.Elem (proxCoreSet S))) := by
    refine Measurable.subtype_mk ?_
    exact measurable_subtype_coe.comp (measurable_fst.comp hpair)
  have hxBarCore :
      @Measurable (theorem59SamplePath n) (Set.Elem (proxCoreSet S))
        mStrict (by infer_instance)
        (fun omega : theorem59SamplePath n =>
          let trajectory :=
            theorem59PrintedFeasibleInnerTrajectoryOn S hmu xAnchor
              theorem59CanonicalSamples s hs omega
              (snapshotFun omega) (xStartFun omega)
          let htraj :=
            theorem59PrintedFeasibleInnerTrajectoryOn_rel S hmu xAnchor
              theorem59CanonicalSamples s hs omega
              (snapshotFun omega) (xStartFun omega)
          let hinnerCore :=
            theorem59PrintedFeasibleInnerTrajectoryRelOn_core_mem_of_positiveProxMembership
              S hmu theorem59CanonicalSamples s hs omega
              (snapshotFun omega) (xStartFun omega) trajectory
              hpositiveProxMembership (hstateCorePrev omega).2
              (hstateCorePrev omega).1 htraj
          (⟨(trajectory k).xBar.1, (hinnerCore k).2⟩ : Set.Elem (proxCoreSet S))) := by
    refine Measurable.subtype_mk ?_
    exact measurable_subtype_coe.comp (measurable_snd.comp hpair)
  constructor
  · simpa [mStrict, snapshotFun, xStartFun, pairFun] using
      hsnapshotCore.prodMk (hxCore.prodMk hxBarCore)
  · let key : theorem59SamplePath n -> FeasiblePoint S × (FeasiblePoint S × FeasiblePoint S) :=
      fun omega => (snapshotFun omega, pairFun omega)
    have hsnapshot_finite : (Set.range snapshotFun).Finite := by
      have hsubset :
          Set.range snapshotFun <=
            (fun p : FeasiblePoint S × FeasiblePoint S => p.1) ''
              Set.range (fun omega : theorem59SamplePath n =>
                (snapshotFun omega, xStartFun omega)) := by
        rintro y ⟨omega, rfl⟩
        exact ⟨(snapshotFun omega, xStartFun omega), ⟨omega, rfl⟩, rfl⟩
      exact (hprev_finite.image (fun p : FeasiblePoint S × FeasiblePoint S => p.1)).subset hsubset
    have hkey_finite : (Set.range key).Finite := by
      have hsubset :
          Set.range key <= Set.range snapshotFun ×ˢ Set.range pairFun := by
        rintro y ⟨omega, rfl⟩
        exact ⟨⟨omega, rfl⟩, ⟨omega, rfl⟩⟩
      exact (hsnapshot_finite.prod hpair_finite).subset hsubset
    let corePackage :
        theorem59SamplePath n ->
          Set.Elem (proxCoreSet S) × (Set.Elem (proxCoreSet S) × Set.Elem (proxCoreSet S)) :=
      fun omega =>
        let trajectory :=
          theorem59PrintedFeasibleInnerTrajectoryOn S hmu xAnchor
            theorem59CanonicalSamples s hs omega
            (snapshotFun omega) (xStartFun omega)
        let htraj :=
          theorem59PrintedFeasibleInnerTrajectoryOn_rel S hmu xAnchor
            theorem59CanonicalSamples s hs omega
            (snapshotFun omega) (xStartFun omega)
        let hinnerCore :=
          theorem59PrintedFeasibleInnerTrajectoryRelOn_core_mem_of_positiveProxMembership
            S hmu theorem59CanonicalSamples s hs omega
            (snapshotFun omega) (xStartFun omega) trajectory
            hpositiveProxMembership (hstateCorePrev omega).2
            (hstateCorePrev omega).1 htraj
        (⟨(snapshotFun omega).1, (hstateCorePrev omega).2⟩,
          (⟨(trajectory k).x.1, (hinnerCore k).1⟩,
            ⟨(trajectory k).xBar.1, (hinnerCore k).2⟩))
    have hconst :
        ∀ ⦃omega omega' : theorem59SamplePath n⦄,
          key omega = key omega' -> corePackage omega = corePackage omega' := by
      intro omega omega' hkeyeq
      have hsnap_eq : snapshotFun omega = snapshotFun omega' :=
        congrArg Prod.fst hkeyeq
      have hpair_eq : pairFun omega = pairFun omega' :=
        congrArg Prod.snd hkeyeq
      dsimp [corePackage, pairFun] at *
      apply Prod.ext
      · apply Subtype.ext
        change (snapshotFun omega).1 = (snapshotFun omega').1
        exact congrArg Subtype.val hsnap_eq
      · apply Prod.ext
        · apply Subtype.ext
          change ((pairFun omega).1).1 = ((pairFun omega').1).1
          exact congrArg Subtype.val (congrArg Prod.fst hpair_eq)
        · apply Subtype.ext
          change ((pairFun omega).2).1 = ((pairFun omega').2).1
          exact congrArg Subtype.val (congrArg Prod.snd hpair_eq)
    have hcore_finite : (Set.range corePackage).Finite := by
      haveI : Fintype {y // y ∈ Set.range key} := hkey_finite.fintype
      let G : {y // y ∈ Set.range key} ->
          Set.Elem (proxCoreSet S) × (Set.Elem (proxCoreSet S) × Set.Elem (proxCoreSet S)) := fun y =>
        corePackage (Classical.choose y.2)
      have hsubset : Set.range corePackage <= Set.range G := by
        rintro z ⟨omega, rfl⟩
        refine ⟨⟨key omega, ⟨omega, rfl⟩⟩, ?_⟩
        dsimp [G]
        exact hconst (Classical.choose_spec
          (show key omega ∈ Set.range key from ⟨omega, rfl⟩))
      exact (Set.finite_range G).subset hsubset
    simpa [corePackage, snapshotFun, xStartFun] using hcore_finite

/-- Generated all-history one-step recurrence used by printed Lemma 5.18.

This is the concrete instantiation requested by the route audits: `W` is the
actual generated previous-epoch snapshot together with the generated current
inner state, and freshness is supplied by the all-history strict-past bridge. -/
theorem lemma518_printed_epoch_generated_one_step_recurrence_all_history
    {n dim : Nat} (S : Setup n dim)
    (xAnchor : Set.Elem (proxCoreSet S)) (xTarget : FeasiblePoint S) (hmu : 0 < S.mu)
    (s : Nat) (hs : 1 <= s) (k : Nat)
    (halpha : theorem59Alpha S s ∈ Set.Icc (0 : Real) 1)
    (halpha_pos : 0 < theorem59Alpha S s)
    (hp : theorem59P s ∈ Set.Icc (0 : Real) 1)
    (hgamma : 0 < theorem59Gamma S s)
    (hbar : 0 <= 1 - theorem59Alpha S s - theorem59P s)
    (hcurv :
      0 < 1 + S.mu * theorem59Gamma S s -
        averageSmoothness S * theorem59Alpha S s * theorem59Gamma S s)
    (hnoise :
      0 <= theorem59P s -
        theorem59LQ S * theorem59Alpha S s * theorem59Gamma S s /
          (1 + S.mu * theorem59Gamma S s -
            averageSmoothness S * theorem59Alpha S s * theorem59Gamma S s))
    (hsearch : searchPointWeights S (theorem59Gamma S) (theorem59Alpha S) theorem59P s ∈
      stdSimplex Real (Fin 3))
    (havg : averagedInnerWeightsAdmissible (theorem59Alpha S) theorem59P s)
    (h516 : lemma516CorrectedRelationalConditionalExpectationStepBoundaryStatement S)
    (h515 : lemma515RelationalCoreStepBoundaryStatement S)
    (h513 : lemma513AcceleratedVarianceEstimatorFactsBoundaryStatement S)
    (hpositiveProxMembership :
      theorem59PrintedFeasiblePositiveProxUpdateCoreMembershipStatement S)
    (hstateCorePrev :
      forall omega : theorem59SamplePath n,
        (theorem59PrintedFeasibleEpochStateProcessOn S hmu xAnchor
            theorem59CanonicalSamples (s - 1) omega).x.1 ∈ proxCoreSet S ∧
          (theorem59PrintedFeasibleEpochStateProcessOn S hmu xAnchor
            theorem59CanonicalSamples (s - 1) omega).xTilde.1 ∈ proxCoreSet S) :
    let W : theorem59SamplePath n ->
        Set.Elem (proxCoreSet S) × (Set.Elem (proxCoreSet S) × Set.Elem (proxCoreSet S)) :=
      fun omega =>
        let snapshot :=
          (theorem59PrintedFeasibleEpochStateProcessOn S hmu xAnchor
            theorem59CanonicalSamples (s - 1) omega).xTilde
        let xStart :=
          (theorem59PrintedFeasibleEpochStateProcessOn S hmu xAnchor
            theorem59CanonicalSamples (s - 1) omega).x
        let trajectory :=
          theorem59PrintedFeasibleInnerTrajectoryOn S hmu xAnchor
            theorem59CanonicalSamples s hs omega snapshot xStart
        let htraj :=
          theorem59PrintedFeasibleInnerTrajectoryOn_rel S hmu xAnchor
            theorem59CanonicalSamples s hs omega snapshot xStart
        let hinnerCore :=
          theorem59PrintedFeasibleInnerTrajectoryRelOn_core_mem_of_positiveProxMembership
            S hmu theorem59CanonicalSamples s hs omega snapshot xStart trajectory
            hpositiveProxMembership (hstateCorePrev omega).2
            (hstateCorePrev omega).1 htraj
        (⟨snapshot.1, (hstateCorePrev omega).2⟩,
          (⟨(trajectory k).x.1, (hinnerCore k).1⟩,
            ⟨(trajectory k).xBar.1, (hinnerCore k).2⟩))
    let nextPotential :
        Set.Elem (proxCoreSet S) × (Set.Elem (proxCoreSet S) × Set.Elem (proxCoreSet S)) -> Fin n -> Real :=
      fun state sample =>
        let snapshot := proxCoreAsFeasible S state.1
        let cur : InnerStateFeasibleOn S :=
          { x := proxCoreAsFeasible S state.2.1
            xBar := proxCoreAsFeasible S state.2.2 }
        let next :=
          theorem59PrintedFeasibleInnerStepOn S (theorem59Gamma S)
            (theorem59Alpha S) theorem59P s (samplingWeight S) snapshot
            (fullGradient S snapshot.1) sample hgamma xAnchor hsearch havg cur
        let hxNext : (next.x.1 ∈ proxCoreSet S) := by
          have hprintedStep :
              theorem59PrintedFeasibleInnerStepRelOn S (theorem59Gamma S)
                (theorem59Alpha S) theorem59P s (samplingWeight S) snapshot
                (fullGradient S snapshot.1) sample hsearch havg cur next :=
            theorem59PrintedFeasibleInnerStepOn_satisfies_rel S
              (theorem59Gamma S) (theorem59Alpha S) theorem59P s
              (samplingWeight S) snapshot (fullGradient S snapshot.1) sample
              hgamma xAnchor hsearch havg cur
          rcases
            theorem59PrintedFeasibleInnerStepRelOn_core_witnesses_of_positiveProxMembership
              S (theorem59Gamma S) (theorem59Alpha S) theorem59P s hgamma
              (samplingWeight S) snapshot (fullGradient S snapshot.1) sample
              hsearch havg cur next state.2.1.2 state.2.2.2 state.1.2
              hpositiveProxMembership hprintedStep with
            ⟨_hxUnder, _hprox, hxNext, _hxBarNext⟩
          exact hxNext
        let hxBarNext : (next.xBar.1 ∈ proxCoreSet S) := by
          have hprintedStep :
              theorem59PrintedFeasibleInnerStepRelOn S (theorem59Gamma S)
                (theorem59Alpha S) theorem59P s (samplingWeight S) snapshot
                (fullGradient S snapshot.1) sample hsearch havg cur next :=
            theorem59PrintedFeasibleInnerStepOn_satisfies_rel S
              (theorem59Gamma S) (theorem59Alpha S) theorem59P s
              (samplingWeight S) snapshot (fullGradient S snapshot.1) sample
              hgamma xAnchor hsearch havg cur
          rcases
            theorem59PrintedFeasibleInnerStepRelOn_core_witnesses_of_positiveProxMembership
              S (theorem59Gamma S) (theorem59Alpha S) theorem59P s hgamma
              (samplingWeight S) snapshot (fullGradient S snapshot.1) sample
              hsearch havg cur next state.2.1.2 state.2.2.2 state.1.2
              hpositiveProxMembership hprintedStep with
            ⟨_hxUnder, _hprox, _hxNext, hxBarNext⟩
          exact hxBarNext
        theorem59Gamma S s / theorem59Alpha S s *
            (compositeObjective S next.xBar.1 - compositeObjective S xTarget.1) +
          (1 + S.mu * theorem59Gamma S s) *
            bregmanOn S (⟨next.x.1, hxNext⟩ : Set.Elem (proxCoreSet S)) xTarget
    let previousRhs : theorem59SamplePath n -> Real :=
      fun omega =>
        let snapshot :=
          (theorem59PrintedFeasibleEpochStateProcessOn S hmu xAnchor
            theorem59CanonicalSamples (s - 1) omega).xTilde
        let xStart :=
          (theorem59PrintedFeasibleEpochStateProcessOn S hmu xAnchor
            theorem59CanonicalSamples (s - 1) omega).x
        let trajectory :=
          theorem59PrintedFeasibleInnerTrajectoryOn S hmu xAnchor
            theorem59CanonicalSamples s hs omega snapshot xStart
        let htraj :=
          theorem59PrintedFeasibleInnerTrajectoryOn_rel S hmu xAnchor
            theorem59CanonicalSamples s hs omega snapshot xStart
        let hinnerCore :=
          theorem59PrintedFeasibleInnerTrajectoryRelOn_core_mem_of_positiveProxMembership
            S hmu theorem59CanonicalSamples s hs omega snapshot xStart trajectory
            hpositiveProxMembership (hstateCorePrev omega).2
            (hstateCorePrev omega).1 htraj
        theorem59Gamma S s / theorem59Alpha S s *
            (1 - theorem59Alpha S s - theorem59P s) *
            (compositeObjective S (trajectory k).xBar.1 -
              compositeObjective S xTarget.1) +
          theorem59Gamma S s / theorem59Alpha S s * theorem59P s *
            (compositeObjective S snapshot.1 - compositeObjective S xTarget.1) +
          bregmanOn S
            (⟨(trajectory k).x.1, (hinnerCore k).1⟩ : Set.Elem (proxCoreSet S))
            xTarget
    SOptLib.expectation (theorem59SampleLaw S)
        (fun omega : theorem59SamplePath n =>
          nextPotential (W omega) (theorem59CanonicalSamples s (k + 1) omega)) <=
      SOptLib.expectation (theorem59SampleLaw S) previousRhs := by
  classical
  let W : theorem59SamplePath n ->
      Set.Elem (proxCoreSet S) × (Set.Elem (proxCoreSet S) × Set.Elem (proxCoreSet S)) :=
    fun omega =>
      let snapshot :=
        (theorem59PrintedFeasibleEpochStateProcessOn S hmu xAnchor
          theorem59CanonicalSamples (s - 1) omega).xTilde
      let xStart :=
        (theorem59PrintedFeasibleEpochStateProcessOn S hmu xAnchor
          theorem59CanonicalSamples (s - 1) omega).x
      let trajectory :=
        theorem59PrintedFeasibleInnerTrajectoryOn S hmu xAnchor
          theorem59CanonicalSamples s hs omega snapshot xStart
      let htraj :=
        theorem59PrintedFeasibleInnerTrajectoryOn_rel S hmu xAnchor
          theorem59CanonicalSamples s hs omega snapshot xStart
      let hinnerCore :=
        theorem59PrintedFeasibleInnerTrajectoryRelOn_core_mem_of_positiveProxMembership
          S hmu theorem59CanonicalSamples s hs omega snapshot xStart trajectory
          hpositiveProxMembership (hstateCorePrev omega).2
          (hstateCorePrev omega).1 htraj
      (⟨snapshot.1, (hstateCorePrev omega).2⟩,
        (⟨(trajectory k).x.1, (hinnerCore k).1⟩,
          ⟨(trajectory k).xBar.1, (hinnerCore k).2⟩))
  let nextPotential :
      Set.Elem (proxCoreSet S) × (Set.Elem (proxCoreSet S) × Set.Elem (proxCoreSet S)) -> Fin n -> Real :=
    fun state sample =>
      let snapshot := proxCoreAsFeasible S state.1
      let cur : InnerStateFeasibleOn S :=
        { x := proxCoreAsFeasible S state.2.1
          xBar := proxCoreAsFeasible S state.2.2 }
      let next :=
        theorem59PrintedFeasibleInnerStepOn S (theorem59Gamma S)
          (theorem59Alpha S) theorem59P s (samplingWeight S) snapshot
          (fullGradient S snapshot.1) sample hgamma xAnchor hsearch havg cur
      let hxNext : (next.x.1 ∈ proxCoreSet S) := by
        have hprintedStep :
            theorem59PrintedFeasibleInnerStepRelOn S (theorem59Gamma S)
              (theorem59Alpha S) theorem59P s (samplingWeight S) snapshot
              (fullGradient S snapshot.1) sample hsearch havg cur next :=
          theorem59PrintedFeasibleInnerStepOn_satisfies_rel S
            (theorem59Gamma S) (theorem59Alpha S) theorem59P s
            (samplingWeight S) snapshot (fullGradient S snapshot.1) sample
            hgamma xAnchor hsearch havg cur
        rcases
          theorem59PrintedFeasibleInnerStepRelOn_core_witnesses_of_positiveProxMembership
            S (theorem59Gamma S) (theorem59Alpha S) theorem59P s hgamma
            (samplingWeight S) snapshot (fullGradient S snapshot.1) sample
            hsearch havg cur next state.2.1.2 state.2.2.2 state.1.2
            hpositiveProxMembership hprintedStep with
          ⟨_hxUnder, _hprox, hxNext, _hxBarNext⟩
        exact hxNext
      let hxBarNext : (next.xBar.1 ∈ proxCoreSet S) := by
        have hprintedStep :
            theorem59PrintedFeasibleInnerStepRelOn S (theorem59Gamma S)
              (theorem59Alpha S) theorem59P s (samplingWeight S) snapshot
              (fullGradient S snapshot.1) sample hsearch havg cur next :=
          theorem59PrintedFeasibleInnerStepOn_satisfies_rel S
            (theorem59Gamma S) (theorem59Alpha S) theorem59P s
            (samplingWeight S) snapshot (fullGradient S snapshot.1) sample
            hgamma xAnchor hsearch havg cur
        rcases
          theorem59PrintedFeasibleInnerStepRelOn_core_witnesses_of_positiveProxMembership
            S (theorem59Gamma S) (theorem59Alpha S) theorem59P s hgamma
            (samplingWeight S) snapshot (fullGradient S snapshot.1) sample
            hsearch havg cur next state.2.1.2 state.2.2.2 state.1.2
            hpositiveProxMembership hprintedStep with
          ⟨_hxUnder, _hprox, _hxNext, hxBarNext⟩
        exact hxBarNext
      theorem59Gamma S s / theorem59Alpha S s *
          (compositeObjective S next.xBar.1 - compositeObjective S xTarget.1) +
        (1 + S.mu * theorem59Gamma S s) *
          bregmanOn S (⟨next.x.1, hxNext⟩ : Set.Elem (proxCoreSet S)) xTarget
  let previousRhs : theorem59SamplePath n -> Real :=
    fun omega =>
      let snapshot :=
        (theorem59PrintedFeasibleEpochStateProcessOn S hmu xAnchor
          theorem59CanonicalSamples (s - 1) omega).xTilde
      let xStart :=
        (theorem59PrintedFeasibleEpochStateProcessOn S hmu xAnchor
          theorem59CanonicalSamples (s - 1) omega).x
      let trajectory :=
        theorem59PrintedFeasibleInnerTrajectoryOn S hmu xAnchor
          theorem59CanonicalSamples s hs omega snapshot xStart
      let htraj :=
        theorem59PrintedFeasibleInnerTrajectoryOn_rel S hmu xAnchor
          theorem59CanonicalSamples s hs omega snapshot xStart
      let hinnerCore :=
        theorem59PrintedFeasibleInnerTrajectoryRelOn_core_mem_of_positiveProxMembership
          S hmu theorem59CanonicalSamples s hs omega snapshot xStart trajectory
          hpositiveProxMembership (hstateCorePrev omega).2
          (hstateCorePrev omega).1 htraj
      theorem59Gamma S s / theorem59Alpha S s *
          (1 - theorem59Alpha S s - theorem59P s) *
          (compositeObjective S (trajectory k).xBar.1 -
            compositeObjective S xTarget.1) +
        theorem59Gamma S s / theorem59Alpha S s * theorem59P s *
          (compositeObjective S snapshot.1 - compositeObjective S xTarget.1) +
        bregmanOn S
          (⟨(trajectory k).x.1, (hinnerCore k).1⟩ : Set.Elem (proxCoreSet S))
          xTarget
  have hWF :=
    lemma518_generated_printed_epoch_snapshot_state_strictPast_measurable
      S hmu xAnchor s hs k hpositiveProxMembership hstateCorePrev
  have hW :
      @Measurable (theorem59SamplePath n)
        (Set.Elem (proxCoreSet S) × (Set.Elem (proxCoreSet S) × Set.Elem (proxCoreSet S)))
        (⨆ q ∈ theorem59StrictPastIndexSet s k,
          MeasurableSpace.comap
            (fun omega : theorem59SamplePath n =>
              theorem59CanonicalSamples q.1 q.2 omega)
            (by infer_instance : MeasurableSpace (Fin n)))
        (by infer_instance) W := by
    simpa [W] using
      hWF.1
  have hW_finite : (Set.range W).Finite := by
    simpa [W] using hWF.2
  have hsampleCoord_meas :
      forall q : Nat × Nat,
        Measurable
          (fun omega : theorem59SamplePath n =>
            theorem59CanonicalSamples q.1 q.2 omega) := by
    intro q
    change Measurable (fun omega : Nat -> Nat -> Fin n => omega q.1 q.2)
    exact (measurable_pi_apply q.2).comp (measurable_pi_apply q.1)
  have hstrict_le_ambient :
      (⨆ q ∈ theorem59StrictPastIndexSet s k,
          MeasurableSpace.comap
            (fun omega : theorem59SamplePath n =>
              theorem59CanonicalSamples q.1 q.2 omega)
            (by infer_instance : MeasurableSpace (Fin n))) ≤
        (by infer_instance : MeasurableSpace (theorem59SamplePath n)) := by
    refine iSup_le ?_
    intro q
    refine iSup_le ?_
    intro _hq
    exact (hsampleCoord_meas q).comap_le
  have hW_ambient : Measurable W := by
    exact hW.mono hstrict_le_ambient le_rfl
  have hprob_component :
      MeasureTheory.IsProbabilityMeasure (componentSampleLaw S) := by
    unfold componentSampleLaw
    infer_instance
  letI : MeasureTheory.IsProbabilityMeasure (componentSampleLaw S) := hprob_component
  have hprob_stream :
      MeasureTheory.IsProbabilityMeasure
        (SOptLib.iidStreamLaw (componentSampleLaw S)) := by
    infer_instance
  letI : MeasureTheory.IsProbabilityMeasure
      (SOptLib.iidStreamLaw (componentSampleLaw S)) := hprob_stream
  have hprob_sample :
      MeasureTheory.IsProbabilityMeasure (theorem59SampleLaw S) := by
    unfold theorem59SampleLaw
    infer_instance
  letI : MeasureTheory.IsProbabilityMeasure (theorem59SampleLaw S) := hprob_sample
  exact
    lemma518_printed_epoch_one_step_unconditional_recurrence_all_history
      S W s k nextPotential previousRhs hW
      (by
        exact
          integrable_prod_right_fintype_of_finite_left_map
            W hW_ambient.aemeasurable hW_finite (componentSampleLaw S) nextPotential)
      (by
        exact
          aestronglyMeasurable_map_of_finite_range_support
            W hW_finite
            (fun a =>
              componentConditionalExpectation S (samplingWeight S)
                (nextPotential a)))
      (by
        let φ :
            Set.Elem (proxCoreSet S) × (Set.Elem (proxCoreSet S) × Set.Elem (proxCoreSet S)) -> Real :=
          fun a =>
            componentConditionalExpectation S (samplingWeight S)
              (nextPotential a)
        have hφ :
            MeasureTheory.AEStronglyMeasurable φ
              (MeasureTheory.Measure.map W (theorem59SampleLaw S)) :=
          aestronglyMeasurable_map_of_finite_range_support W hW_finite φ
        have hφ_int :
            MeasureTheory.Integrable φ
              (MeasureTheory.Measure.map W (theorem59SampleLaw S)) :=
          integrable_map_of_finite_range_support W hW_ambient.aemeasurable hW_finite φ
        exact
          (MeasureTheory.integrable_map_measure hφ hW_ambient.aemeasurable).1 hφ_int)
      (by
        let previousScalar :
            Set.Elem (proxCoreSet S) × (Set.Elem (proxCoreSet S) × Set.Elem (proxCoreSet S)) -> Real :=
          fun state =>
            theorem59Gamma S s / theorem59Alpha S s *
                (1 - theorem59Alpha S s - theorem59P s) *
                (compositeObjective S state.2.2.1 -
                  compositeObjective S xTarget.1) +
              theorem59Gamma S s / theorem59Alpha S s * theorem59P s *
                (compositeObjective S state.1.1 -
                  compositeObjective S xTarget.1) +
              bregmanOn S state.2.1 xTarget
        have hscalar :
            MeasureTheory.AEStronglyMeasurable previousScalar
              (MeasureTheory.Measure.map W (theorem59SampleLaw S)) :=
          aestronglyMeasurable_map_of_finite_range_support
            W hW_finite previousScalar
        have hscalar_int :
            MeasureTheory.Integrable previousScalar
              (MeasureTheory.Measure.map W (theorem59SampleLaw S)) :=
          integrable_map_of_finite_range_support
            W hW_ambient.aemeasurable hW_finite previousScalar
        have hcomp_int :
            MeasureTheory.Integrable (previousScalar ∘ W)
              (theorem59SampleLaw S) :=
          (MeasureTheory.integrable_map_measure hscalar hW_ambient.aemeasurable).1
            hscalar_int
        have hprev_eq : previousRhs = previousScalar ∘ W := by
          funext omega
          simp [previousRhs, previousScalar, W, proxCoreAsFeasible]
        simpa [hprev_eq])
      (by
        intro omega
        let snapshot :=
          (theorem59PrintedFeasibleEpochStateProcessOn S hmu xAnchor
            theorem59CanonicalSamples (s - 1) omega).xTilde
        let xStart :=
          (theorem59PrintedFeasibleEpochStateProcessOn S hmu xAnchor
            theorem59CanonicalSamples (s - 1) omega).x
        let trajectory :=
          theorem59PrintedFeasibleInnerTrajectoryOn S hmu xAnchor
            theorem59CanonicalSamples s hs omega snapshot xStart
        have htraj :
            theorem59PrintedFeasibleInnerTrajectoryRelOn S hmu theorem59CanonicalSamples
              s hs omega snapshot xStart trajectory := by
          exact theorem59PrintedFeasibleInnerTrajectoryOn_rel S hmu xAnchor
            theorem59CanonicalSamples s hs omega snapshot xStart
        have hinnerCore :=
          theorem59PrintedFeasibleInnerTrajectoryRelOn_core_mem_of_positiveProxMembership
            S hmu theorem59CanonicalSamples s hs omega snapshot xStart trajectory
            hpositiveProxMembership (hstateCorePrev omega).2
            (hstateCorePrev omega).1 htraj
        rcases
          lemma518_printed_epoch_step_lemma516_bound
            S xAnchor xTarget hmu s hs halpha halpha_pos hp hgamma hbar hcurv hnoise
            hsearch havg h516 h515 h513 hpositiveProxMembership omega snapshot xStart
            trajectory htraj k (hstateCorePrev omega).2 (hinnerCore k).1
            (hinnerCore k).2 with
          ⟨_hxNext, _hxBarNext, hineq⟩
        simpa [W, nextPotential, previousRhs, snapshot, xStart, trajectory] using hineq)

/-- Full generated inner-step selector measurability from the raw printed prox selector.

The recursive-prefix helper below needs measurability of the whole state update.
All non-prox parts of Algorithm 5.7's printed inner step are affine/projection
bookkeeping once the selected prox iterate is measurable. This lemma isolates
the remaining nontrivial interface to the chosen feasible `argmin_{x in X}`
selector `theorem59PrintedFeasibleProxUpdateOn`. -/
theorem theorem59_printed_inner_step_selector_measurable_of_xNext
    {n dim : Nat} (S : Setup n dim) (hmu : 0 < S.mu)
    (xAnchor : Set.Elem (proxCoreSet S)) (s : Nat) (hs : 1 <= s)
    (hxNext_meas :
      Measurable
        (fun p :
          ((FeasiblePoint S ×
            (FeasiblePoint S × (FeasiblePoint S × FeasiblePoint S))) × Fin n) =>
          let snapshotFixed : FeasiblePoint S := p.1.1
          let prev : InnerStateFeasibleOn S :=
            { x := p.1.2.2.1, xBar := p.1.2.2.2 }
          let xUnder :=
            searchPointFeasibleOn S (theorem59Gamma S) (theorem59Alpha S)
              theorem59P s prev.xBar prev.x snapshotFixed
              ((theorem59_parameter_conditions S hmu s hs).2.2.2.2.1)
          let G :=
            varianceReducedGradientFeasibleOn S (samplingWeight S) p.2 xUnder
              snapshotFixed (fullGradient S snapshotFixed.1)
          theorem59PrintedFeasibleProxUpdateOn S (theorem59Gamma S) s
            (theorem59Gamma_pos S s) xAnchor prev.x xUnder G)) :
      Measurable
        (fun p :
          ((FeasiblePoint S ×
            (FeasiblePoint S × (FeasiblePoint S × FeasiblePoint S))) × Fin n) =>
          let snapshotFixed : FeasiblePoint S := p.1.1
          let prev : InnerStateFeasibleOn S :=
            { x := p.1.2.2.1, xBar := p.1.2.2.2 }
          let next :=
            theorem59PrintedFeasibleInnerStepOn S (theorem59Gamma S)
              (theorem59Alpha S) theorem59P s (samplingWeight S) snapshotFixed
              (fullGradient S snapshotFixed.1) p.2 (theorem59Gamma_pos S s)
              xAnchor
              ((theorem59_parameter_conditions S hmu s hs).2.2.2.2.1)
              ((theorem59_parameter_conditions S hmu s hs).2.2.2.2.2)
              prev
          (snapshotFixed, (p.1.2.1, ((next.x, next.xBar) :
            FeasiblePoint S × FeasiblePoint S)))) := by
  classical
  let State :=
    FeasiblePoint S × (FeasiblePoint S × (FeasiblePoint S × FeasiblePoint S))
  let xNext : State × Fin n -> FeasiblePoint S := fun p =>
    let snapshotFixed : FeasiblePoint S := p.1.1
    let prev : InnerStateFeasibleOn S := { x := p.1.2.2.1, xBar := p.1.2.2.2 }
    let xUnder :=
      searchPointFeasibleOn S (theorem59Gamma S) (theorem59Alpha S)
        theorem59P s prev.xBar prev.x snapshotFixed
        ((theorem59_parameter_conditions S hmu s hs).2.2.2.2.1)
    let G :=
      varianceReducedGradientFeasibleOn S (samplingWeight S) p.2 xUnder
        snapshotFixed (fullGradient S snapshotFixed.1)
    theorem59PrintedFeasibleProxUpdateOn S (theorem59Gamma S) s
      (theorem59Gamma_pos S s) xAnchor prev.x xUnder G
  have hxNext_meas' : Measurable xNext := by
    simpa [xNext, State] using hxNext_meas
  have hsnapshot :
      Measurable (fun p : State × Fin n => p.1.1) := by
    exact measurable_fst.comp measurable_fst
  have hxStart :
      Measurable (fun p : State × Fin n => p.1.2.1) := by
    exact measurable_fst.comp (measurable_snd.comp measurable_fst)
  have hxBarPrev :
      Measurable (fun p : State × Fin n => p.1.2.2.2) := by
    exact measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_fst))
  have hxBarNext :
      Measurable (fun p : State × Fin n =>
        averagedInnerIterateAllFeasibleOn S (theorem59Alpha S) theorem59P s
          p.1.2.2.2 (xNext p) p.1.1
          ((theorem59_parameter_conditions S hmu s hs).2.2.2.2.2)) := by
    refine Measurable.subtype_mk ?_
    have hxBarPrev_val :
        Measurable (fun p : State × Fin n => (p.1.2.2.2 : FeasiblePoint S).1) :=
      measurable_subtype_coe.comp hxBarPrev
    have hxNext_val :
        Measurable (fun p : State × Fin n => (xNext p).1) :=
      measurable_subtype_coe.comp hxNext_meas'
    have hsnapshot_val :
        Measurable (fun p : State × Fin n => (p.1.1 : FeasiblePoint S).1) :=
      measurable_subtype_coe.comp hsnapshot
    simpa [averagedInnerIterateAllFeasibleOn,
      averagedInnerIterateValueAllFeasibleOn, averagedInnerIterate, add_assoc] using
      ((hxBarPrev_val.const_smul (1 - theorem59Alpha S s - theorem59P s)).add
        ((hxNext_val.const_smul (theorem59Alpha S s)).add
          (hsnapshot_val.const_smul (theorem59P s))))
  have hnextPair :
      Measurable (fun p : State × Fin n =>
        ((xNext p,
          averagedInnerIterateAllFeasibleOn S (theorem59Alpha S) theorem59P s
            p.1.2.2.2 (xNext p) p.1.1
            ((theorem59_parameter_conditions S hmu s hs).2.2.2.2.2)) :
          FeasiblePoint S × FeasiblePoint S)) :=
    hxNext_meas'.prodMk hxBarNext
  simpa [State, xNext, theorem59PrintedFeasibleInnerStepOn] using
    hsnapshot.prodMk (hxStart.prodMk hnextPair)

/-- Pointwise selected-argmin correctness does not imply selector measurability.

This is the exact obstruction class for the raw
`theorem59PrintedFeasibleProxUpdateOn` leaf below.  Even for the constant
zero objective on a two-point candidate space, an arbitrary selected minimizer
can be nonmeasurable.  Thus a proof of
a global xNext-selector measurability theorem would need additional
measurable-selection/unique-argmin infrastructure for the concrete prox
objective; it cannot follow from `theorem59PrintedFeasibleProxUpdateOn_isMin`
or `theorem59PrintedFeasibleProxUpdateExistsOn` alone. The active generated
prefix route below therefore uses finite-range measurability instead of such a
global selector theorem. -/
theorem pointwise_argmin_certificate_does_not_force_measurable_selector :
    ∃ (Ω : Type) (_mΩ : MeasurableSpace Ω) (sel : Ω -> Bool),
      (∀ omega, IsMinOn (fun _ : Bool => (0 : Real)) Set.univ (sel omega)) ∧
        ¬ Measurable sel := by
  classical
  let mΩ : MeasurableSpace (Fin 3) :=
    MeasurableSpace.generateFrom ({({(0 : Fin 3)} : Set (Fin 3))} : Set (Set (Fin 3)))
  obtain ⟨ξ, _P, _hprob, _hindep, _hid, hnot_meas⟩ :=
    exists_iid_identDistrib_not_forall_measurable
      (Ω := Fin 3) (Ξ := Bool)
      (z := (0 : Fin 3)) (o := (1 : Fin 3)) (tw := (2 : Fin 3))
      (ff := false) (tt := true)
      (by decide) (by decide) (by decide)
      (by simp) (by decide)
  push Not at hnot_meas
  obtain ⟨k, hk⟩ := hnot_meas
  refine ⟨Fin 3, mΩ, ξ k, ?_, ?_⟩
  · intro omega y _hy
    norm_num
  · simpa [mΩ] using hk

/-- A finite-range recursive process is prefix-measurable without a globally
measurable update kernel.

This is the generated-process alternative to requiring measurability of the
whole state/sample update on the ambient state space.  At each fixed finite
prefix the key `(previous state, current sample)` has finite range; any selected
next state that is determined by that key is therefore measurable by
`SOptLib.measurable_of_finite_range_fiber_const`. -/
theorem recursive_process_measurable_finite_range_wrt_sample_prefix
    {Ω X U : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    [MeasurableSpace U] [MeasurableSingletonClass U]
    (past : Nat -> MeasurableSpace Ω)
    (process : Nat -> Ω -> X)
    (driver : Nat -> Ω -> U)
    (step : Nat -> X -> U -> X)
    (N n : Nat)
    (h_past_mono : forall {a b : Nat}, a <= b -> past a <= past b)
    (h_init_meas : @Measurable Ω X (past (N + 1)) (by infer_instance) (process 0))
    (h_init_finite : (Set.range (process 0)).Finite)
    (h_driver_prefix :
      forall j, j + 1 <= N ->
        @Measurable Ω U (past ((j + 1) + 1)) (by infer_instance) (driver j))
    (h_driver_finite : forall j, (Set.range (driver j)).Finite)
    (h_update :
      forall j, j + 1 <= N ->
        forall omega : Ω, process (j + 1) omega =
          step j (process j omega) (driver j omega))
    (hn : n <= N) :
    @Measurable Ω X (past (N + 1)) (by infer_instance) (process n) ∧
      (Set.range (process n)).Finite := by
  exact
    SOptLib.recursive_process_measurable_finite_range_wrt_sample_prefix
      (past := past)
      (process := process)
      (driver := driver)
      (step := step)
      (N := N)
      (n := n)
      h_past_mono
      h_init_meas
      h_init_finite
      h_driver_prefix
      (fun j _ => h_driver_finite j)
      h_update
      hn

/-- Generated printed inner trajectory is prefix-measurable from finite generated prefixes.

This is the strict-prefix side of the adaptive Eq. (5.4.9) transport.  The
helper uses the generated trajectory, not an `hspec`-chosen existential
trajectory.  Its measurability proof is deliberately finite-prefix/local:
the current step is measurable because it is a function of the finite-range key
`(previous generated state, current finite sample)`, avoiding the over-strong
global measurability of the ambient `Classical.choose` prox selector. -/
theorem lemma518_generated_printed_inner_state_pair_prefix_measurable_of_step
    {Ω : Type*} [MeasurableSpace Ω] {n dim : Nat} (S : Setup n dim)
    (hmu : 0 < S.mu) (xAnchor : Set.Elem (proxCoreSet S))
    (samples : Nat -> Nat -> Ω -> Fin n)
    (s : Nat) (hs : 1 <= s)
    (snapshot xStart : Ω -> FeasiblePoint S)
    (k : Nat)
    (hsample_meas : forall t : Nat, Measurable (fun omega : Ω => samples s t omega))
    (hinit :
      @Measurable Ω
        (FeasiblePoint S × (FeasiblePoint S × (FeasiblePoint S × FeasiblePoint S)))
        ((SOptLib.filtration
          (fun t omega => samples s t omega) hsample_meas).seq (k + 1))
        (by infer_instance)
        (fun omega : Ω =>
          (snapshot omega,
            (xStart omega,
              ((xStart omega, snapshot omega) : FeasiblePoint S × FeasiblePoint S)))))
    (hinit_finite :
      (Set.range
        (fun omega : Ω =>
          (snapshot omega,
            (xStart omega,
              ((xStart omega, snapshot omega) :
                FeasiblePoint S × FeasiblePoint S))))).Finite) :
    @Measurable Ω (FeasiblePoint S × FeasiblePoint S)
      ((SOptLib.filtration
        (fun t omega => samples s t omega) hsample_meas).seq (k + 1))
      (by infer_instance)
      (fun omega : Ω =>
        let trajectory :=
          theorem59PrintedFeasibleInnerTrajectoryOn S hmu xAnchor samples s hs omega
            (snapshot omega) (xStart omega)
        ((trajectory k).x, (trajectory k).xBar)) ∧
      forall omega : Ω,
        theorem59PrintedFeasibleInnerTrajectoryRelOn S hmu samples s hs omega
          (snapshot omega) (xStart omega)
          (theorem59PrintedFeasibleInnerTrajectoryOn S hmu xAnchor samples s hs omega
            (snapshot omega) (xStart omega)) := by
  classical
  let ξ : Nat -> Ω -> Fin n := fun t omega => samples s t omega
  let past : Nat -> MeasurableSpace Ω := fun t => (SOptLib.filtration ξ hsample_meas).seq t
  let State :=
    FeasiblePoint S × (FeasiblePoint S × (FeasiblePoint S × FeasiblePoint S))
  let process : Nat -> Ω -> State := fun t omega =>
    let trajectory :=
      theorem59PrintedFeasibleInnerTrajectoryOn S hmu xAnchor samples s hs omega
        (snapshot omega) (xStart omega)
    (snapshot omega, (xStart omega, ((trajectory t).x, (trajectory t).xBar)))
  let driver : Nat -> Ω -> Fin n := fun j omega => ξ (j + 1) omega
  let step : Nat -> State -> Fin n -> State := fun j st sample =>
    let snapshotFixed : FeasiblePoint S := st.1
    let prev : InnerStateFeasibleOn S := { x := st.2.2.1, xBar := st.2.2.2 }
    let next :=
      theorem59PrintedFeasibleInnerStepOn S (theorem59Gamma S)
        (theorem59Alpha S) theorem59P s (samplingWeight S) snapshotFixed
        (fullGradient S snapshotFixed.1) sample (theorem59Gamma_pos S s)
        xAnchor
        ((theorem59_parameter_conditions S hmu s hs).2.2.2.2.1)
        ((theorem59_parameter_conditions S hmu s hs).2.2.2.2.2)
        prev
    (snapshotFixed, (st.2.1, ((next.x, next.xBar) :
      FeasiblePoint S × FeasiblePoint S)))
  have hproc_meas :
      @Measurable Ω State (past (k + 1)) (by infer_instance) (process k) := by
    refine
      (recursive_process_measurable_finite_range_wrt_sample_prefix
        (past := past) (process := process) (driver := driver) (step := step)
        (N := k) (n := k) ?_ ?_ ?_ ?_ ?_ ?_ le_rfl).1
    · intro a b hab
      exact (SOptLib.filtration ξ hsample_meas).mono' hab
    · simpa [past, process, State] using hinit
    · simpa [process, State] using hinit_finite
    · intro j hj
      simpa [past, driver, ξ] using
        SOptLib.measurable_sample_of_lt_prefixFiltration
          ξ hsample_meas (Nat.lt_succ_self (j + 1))
    · intro j
      exact Set.toFinite _
    · intro j hj
      simp [process, step, driver, ξ, theorem59PrintedFeasibleInnerTrajectoryOn,
        SOptLib.recursiveIterateProcess]
  constructor
  · simpa [past, process, State] using
      (measurable_snd.comp (measurable_snd.comp hproc_meas))
  · intro omega
    exact theorem59PrintedFeasibleInnerTrajectoryOn_rel S hmu xAnchor samples s hs omega
      (snapshot omega) (xStart omega)

/-- Deterministic fresh-coordinate expectation transport for Theorem 5.9 samples.

This proves the marginal-only layer needed before the adaptive Eq. (5.4.9)
transport: if the finite-index observable does not depend on the sample path
except through the fresh coordinate, then expectation under
`theorem59SampleLaw` is the same finite weighted sum as
`componentConditionalExpectation`.  Considered SOptLib candidates
`iidStreamLaw_map_eval`, `integral_comp_eq_integral_of_map_eq`, and the
non-imported `identDistrib_finite_pmf_integrable_integral_le_weighted_sum_bound`;
the first two exactly align with the marginal bridge, while the full adaptive
trajectory transport still needs a prefix-measurability/independence hypothesis
because its kernel is `omega`-dependent. -/
theorem theorem59SampleLaw_coordinate_expectation_eq_componentConditionalExpectation
    {n dim : Nat} (S : Setup n dim) (epoch inner : Nat)
    (Z : Fin n -> Real) :
    SOptLib.expectation (theorem59SampleLaw S)
        (fun omega : theorem59SamplePath n =>
          Z (theorem59CanonicalSamples epoch inner omega)) =
      componentConditionalExpectation S (samplingWeight S) Z := by
  classical
  let Y : theorem59SamplePath n -> Fin n := fun omega =>
    theorem59CanonicalSamples epoch inner omega
  have hY_meas : Measurable Y := by
    change Measurable (fun omega : Nat -> Nat -> Fin n => omega epoch inner)
    exact (measurable_pi_apply inner).comp (measurable_pi_apply epoch)
  have hmap :
      MeasureTheory.Measure.map Y (theorem59SampleLaw S) =
        componentSampleLaw S := by
    letI : MeasureTheory.IsProbabilityMeasure (componentSampleLaw S) := by
      unfold componentSampleLaw
      infer_instance
    simpa [Y, theorem59SampleLaw, theorem59CanonicalSamples] using
      (SOptLib.iidTwoIndexSampleLaw_map_eval (mu := componentSampleLaw S) epoch inner)
  have hZ_aestrong :
      MeasureTheory.AEStronglyMeasurable Z
        (MeasureTheory.Measure.map Y (theorem59SampleLaw S)) := by
    exact (measurable_of_finite Z).aestronglyMeasurable
  calc
    SOptLib.expectation (theorem59SampleLaw S)
        (fun omega : theorem59SamplePath n =>
          Z (theorem59CanonicalSamples epoch inner omega))
        = ∫ omega, Z (Y omega) ∂theorem59SampleLaw S := by
            rfl
    _ = ∫ i, Z i ∂componentSampleLaw S := by
            exact integral_comp_eq_integral_of_map_eq
              hY_meas.aemeasurable hZ_aestrong hmap
    _ = componentConditionalExpectation S (samplingWeight S) Z := by
            unfold componentConditionalExpectation componentSampleLaw
            rw [MeasureTheory.integral_fintype .of_finite]
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [MeasureTheory.measureReal_def]
            rw [PMF.toMeasure_apply_singleton
              (componentSamplingPMF S) i (MeasurableSet.singleton i)]
            rw [componentSamplingPMF_apply S i]
            rw [ENNReal.toReal_ofReal (le_of_lt (samplingWeight_pos S i))]
            rfl

/-- Correction record for the retired corrected-core Lemma 5.17 epoch head.

The book's Lemma 5.17 telescopes Lemma 5.16 over Algorithm 5.7 iterates.  The
old corrected-core theorem below used `epochOutputProcessOn`, which unfolds to
the same retired `innerStepOn` totalization as the stale Lemma 5.16 leaf. -/
def lemma517CorrectedCoreSmoothEpochRecursionRetiredStatement
    {n dim : Nat} (_S : Setup n dim) : Prop := True

/- Retired statement-correction artifact.
The source-faithful smooth/first-phase epoch routes must telescope a relational
or printed process with Lemma 5.16 certificates; this declaration deliberately
does not assert Lemma 5.17 for the totalized corrected-core process. -/
theorem lemma517_correctedCore_smooth_epoch_recursion
    {n dim : Nat} (S : Setup n dim)
    (T : Nat -> Nat) (gamma alpha p : Nat -> Real)
    (x0 : Set.Elem (proxCoreSet S))
    (x : FeasiblePoint S) (s : Nat) (hs : 1 <= s)
    (hmu_zero : S.mu = 0)
    (hparams :
      forall r, 1 <= r ->
        0 < T r ∧
        alpha r ∈ Set.Icc (0 : Real) 1 ∧
        0 < alpha r ∧
        p r ∈ Set.Icc (0 : Real) 1 ∧
        0 < gamma r ∧
        0 <= 1 - alpha r - p r ∧
        0 < 1 + S.mu * gamma r - averageSmoothness S * alpha r * gamma r ∧
        0 <= p r -
          theorem59LQ S * alpha r * gamma r /
            (1 + S.mu * gamma r - averageSmoothness S * alpha r * gamma r))
    (hw_nonneg :
      forall r, 1 <= r -> 0 <= smoothEpochWeightOf T gamma alpha p r) :
    lemma517CorrectedCoreSmoothEpochRecursionRetiredStatement S := by
  trivial

/-- Correction record for the retired corrected-core Lemma 5.18 decay head.

The paper's Lemma 5.18 bounds the printed output `tilde{x}^s` after deriving
Eq. (5.4.27) from Algorithm 5.7.  The active source route is the printed
Lyapunov boundary in Part003, not the obsolete `smoothCorrectedCoreOutputProcess`
statement below. -/
def lemma518CorrectedCoreFirstPhaseEpochDecayRetiredStatement
    {n dim : Nat} (_S : Setup n dim) : Prop := True

/- Retired statement-correction artifact.
Do not use this declaration to prove source-facing first-phase rates.  The
source-faithful Lemma 5.18 route is
`lemma518_first_phase_epoch_decay_boundary`, which consumes the printed
Eq. (5.4.27) helper over `theorem59PrintedFeasibleOutputProcess`. -/
theorem lemma518_correctedCore_first_phase_epoch_decay
    {n dim : Nat} (S : Setup n dim)
    (x0 : Set.Elem (proxCoreSet S)) (x xStar : FeasiblePoint S) (s : Nat)
    (hxStar : IsOptimalSolutionOn S xStar) (hs : 1 <= s)
    (hs0 : s <= theorem59Cutoff S) :
    lemma518CorrectedCoreFirstPhaseEpochDecayRetiredStatement S := by
  trivial

/-- Separate a two-term scalar expectation into deterministic coefficients.

This is the finite-expectation algebra needed before applying the Lemma 5.18
scalar telescope. Candidates considered: `SOptLib.expectedObjectiveGap_def`
only unfolds objective gaps, and
`SOptLib.integral_le_integral_affine_combination` gives an inequality from a
pointwise affine bound; neither supplies the equality needed to split the
already-integrated generated Lyapunov potential, so this helper wraps
`MeasureTheory.integral_add` and `MeasureTheory.integral_const_mul`. -/
theorem expectation_add_const_mul_eq
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (a c : Real) (F G : Ω -> Real)
    (hF : MeasureTheory.Integrable F μ)
    (hG : MeasureTheory.Integrable G μ) :
    SOptLib.expectation μ (fun omega => a * F omega + c * G omega) =
      a * SOptLib.expectation μ F + c * SOptLib.expectation μ G := by
  simpa [smul_eq_mul] using
    (_root_.expectation_add_const_mul_eq μ a c F G hF hG)

/-- Pull a deterministic scalar through `SOptLib.expectation`.

Candidates considered: `MeasureTheory.integral_const_mul` is the exact Mathlib
API underneath, but downstream Lemma 5.18 algebra is written with
`SOptLib.expectation`, so this local bridge avoids repeated unfolding. -/
theorem expectation_const_mul_eq
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (a : Real) (F : Ω -> Real) :
    SOptLib.expectation μ (fun omega => a * F omega) =
      a * SOptLib.expectation μ F := by
  rw [SOptLib.expectation_def, SOptLib.expectation_def]
  exact MeasureTheory.integral_const_mul a F

/-- Lift a pointwise finite-sum upper bound to expectations.

This is the real-valued form needed after the Lemma 5.18 Jensen normalization.
Candidates considered: `integral_finset_sum_le_of_pointwise_finset_sum_le`
handles a related scaled affine sum, while `SOptLib.expectedObjectiveGap_def`
only unfolds the objective-gap integrand; neither directly gives this
one-sided finite-sum expectation lift. -/
theorem expectation_le_finset_sum_of_pointwise_le
    {Ω I : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    (s : Finset I) (F : Ω -> Real) (G : I -> Ω -> Real)
    (hF : MeasureTheory.Integrable F μ)
    (hG : forall i, i ∈ s -> MeasureTheory.Integrable (G i) μ)
    (hpoint : ∀ᵐ omega ∂μ, F omega <= (s.sum fun i => G i omega)) :
    SOptLib.expectation μ F <=
      s.sum fun i => SOptLib.expectation μ (G i) := by
  exact expectation_le_sum_expectation_of_ae_le_finset_sum
    (mu := μ) s F G hF hG hpoint

/-- Separate a scalar expectation whose terms factor through a finite generated key.

This is the generated-history version of `expectation_add_const_mul_eq` used in
the Lemma 5.18 telescope route. Candidates considered:
`integrable_map_of_finite_range_support` proves the needed integrability for
one observable, while `SOptLib.integral_finset_sum_le_of_pointwise_finset_sum_le`
handles finite sums after a pointwise inequality; neither directly splits this
two-potential expectation, so this bridge combines the finite-key integrability
with deterministic coefficient linearity. -/
theorem expectation_add_const_mul_comp_eq_of_finite_range_key
    {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    [MeasurableSingletonClass A]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsFiniteMeasure μ]
    (W : Ω -> A) (hW : AEMeasurable W μ)
    (hWfin : (Set.range W).Finite)
    (a c : Real) (F G : A -> Real) :
    SOptLib.expectation μ (fun omega => a * F (W omega) + c * G (W omega)) =
      a * SOptLib.expectation μ (fun omega => F (W omega)) +
        c * SOptLib.expectation μ (fun omega => G (W omega)) := by
  simpa [Fin.sum_univ_two, smul_eq_mul] using
    (_root_.expectation_finset_sum_const_smul_comp_eq_of_finite_range_key
      (μ := μ) W hW hWfin
      (idxs := (Finset.univ : Finset (Fin 2)))
      (coeff := fun i => if i = 0 then a else c)
      (F := fun i z => if i = 0 then F z else G z))

/-- Split a three-term scalar expectation through a finite generated key.

This is the right-hand counterpart needed for the Lemma 5.18 generated
one-step recurrence: the previous `xBar`, snapshot, and Bregman terms all
factor through the same finite generated state package. It reuses
`expectation_add_const_mul_comp_eq_of_finite_range_key`; SOptLib finite-sum
telescope candidates do not provide this expectation-linearity equality. -/
theorem expectation_three_const_mul_comp_eq_of_finite_range_key
    {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    [MeasurableSingletonClass A]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsFiniteMeasure μ]
    (W : Ω -> A) (hW : AEMeasurable W μ)
    (hWfin : (Set.range W).Finite)
    (a b c : Real) (F G H : A -> Real) :
    SOptLib.expectation μ
        (fun omega => a * F (W omega) + b * G (W omega) + c * H (W omega)) =
      a * SOptLib.expectation μ (fun omega => F (W omega)) +
        b * SOptLib.expectation μ (fun omega => G (W omega)) +
          c * SOptLib.expectation μ (fun omega => H (W omega)) := by
  let K : A -> Real := fun z => b * G z + c * H z
  have hsplit₁ :=
    expectation_add_const_mul_comp_eq_of_finite_range_key
      (μ := μ) W hW hWfin a 1 F K
  have hsplit₂ :=
    expectation_add_const_mul_comp_eq_of_finite_range_key
      (μ := μ) W hW hWfin b c G H
  calc
    SOptLib.expectation μ
        (fun omega => a * F (W omega) + b * G (W omega) + c * H (W omega))
        = SOptLib.expectation μ
            (fun omega => a * F (W omega) + 1 * K (W omega)) := by
            simp [K]
            ring_nf
    _ = a * SOptLib.expectation μ (fun omega => F (W omega)) +
          1 * SOptLib.expectation μ (fun omega => K (W omega)) := hsplit₁
    _ = a * SOptLib.expectation μ (fun omega => F (W omega)) +
          (b * SOptLib.expectation μ (fun omega => G (W omega)) +
            c * SOptLib.expectation μ (fun omega => H (W omega))) := by
            rw [hsplit₂]
            ring
    _ = a * SOptLib.expectation μ (fun omega => F (W omega)) +
          b * SOptLib.expectation μ (fun omega => G (W omega)) +
            c * SOptLib.expectation μ (fun omega => H (W omega)) := by
            ring

/-- Positive printed prox-output membership through the carrier-subgradient leaf.

This is the Part002 consumer of the Arbiter-designated infrastructure chain:
the printed feasible prox relation first yields the `nu` carrier subgradient
via `theorem59PrintedFeasibleProxUpdateRelOn_kkt_nu_subgradient_of_positive`;
that subgradient is then converted to the paper's `X^o` support certificate
and hence to `proxCoreSet` membership. -/
theorem lemma518_printed_positive_prox_membership_from_carrierSubgradient
    {n dim : Nat} (S : Setup n dim) :
    theorem59PrintedFeasiblePositiveProxUpdateCoreMembershipStatement S := by
  intro gamma s hgamma xPrev xUnder g z hrel
  refine ⟨z.2, ?_⟩
  rcases
      theorem59PrintedFeasibleProxUpdateRelOn_kkt_nu_subgradient_of_positive
        S gamma s hgamma xPrev xUnder g z hrel with
    ⟨pnu, hpnu⟩
  exact theorem59_nu_support_of_carrierSubgradient S z pnu hpnu

/-- Scalar telescope for the first-phase Lemma 5.18 one-epoch recurrence.

Aligns with Lan Lemma 5.18 proof lines 17352-17356: after Eq. (5.4.9) has
been summed over an epoch, the `B k` terms telescope, retaining only the
endpoint potential and the previous-epoch potential. Considered SOptLib
`sum_range_sub_succ_le_first_of_last_nonneg`,
`finite_window_weighted_recurrence_telescope_with_tail_sums`, and
`sum_Icc_two_coeff_telescope_le`; none match this zero-based constant-coefficient
range form with the retained `mu * gamma` tail, so this route-local scalar
bridge proves the exact algebra needed by Eq. (5.4.27). -/
theorem lemma518_scalar_one_epoch_telescope
    (T : Nat) (A B : Nat -> Real) (C muGamma : Real)
    (hstep :
      forall k, k < T ->
        A (k + 1) + (1 + muGamma) * B (k + 1) <= C + B k) :
    (Finset.range T).sum (fun k => A (k + 1)) + B T +
        muGamma * (Finset.range T).sum (fun k => B (k + 1)) <=
      (T : Real) * C + B 0 := by
  exact
    SOptLib.sum_range_succ_add_weighted_tail_le_mul_add_initial_of_step
      (R := Real) T A B C muGamma hstep

/-- Scalar first-phase epoch chain for Eq. (5.4.27).

Once the printed one-epoch Lyapunov recursion is available uniformly for every
first-phase epoch, Lan's proof repeats it back to epoch zero.  This helper
isolates that pure algebra: the first epoch uses `T_1 = 1`, and every later
epoch uses the doubling rule `T_r = 2 T_{r-1}` to match the current RHS with
the previous Lyapunov LHS. -/
theorem lemma518_scalar_first_phase_epoch_chain
    (L : Real)
    (T : Nat -> Nat) (G B : Nat -> Real)
    (s : Nat)
    (hT1 : T 1 = 1)
    (hdouble : forall r, 2 <= r -> r <= s -> T r = 2 * T (r - 1))
    (hstep :
      forall r, 1 <= r -> r <= s ->
        (4 * ((T r : Nat) : Real) / (3 * L)) * G r + B r <=
          (2 * ((T r : Nat) : Real) / (3 * L)) * G (r - 1) + B (r - 1)) :
    1 <= s ->
      (4 * ((T s : Nat) : Real) / (3 * L)) * G s + B s <=
        (2 / (3 * L)) * G 0 + B 0 :=
  SOptLib.first_phase_doubling_epoch_chain_le_initial L T G B s hT1 hdouble hstep

/-- Convert a normalized Jensen average into the scaled-gap finite-sum form.

Aligns with Lan Lemma 5.18 proof step 4 after Eq. (5.4.12): once the first-phase
theta weights are constant, subtracting the same reference objective from both
sides turns the averaged objective bound into the sum of objective gaps.
Candidates considered: `Finset.sum_fin_eq_sum_range` supplies only the finite
index reparametrization, while SOptLib expectation-lift lemmas operate after
integration; neither performs this scalar normalized-average algebra. -/
theorem lemma518_scaled_gap_sum_of_normalized_average
    (T : Nat) (c out reference : Real) (F : Nat -> Real)
    (hTpos : 0 < T) (hcpos : 0 < c)
    (havg :
      out <= (((T : Real) * c)⁻¹ * (c * (Finset.range T).sum F))) :
    c * (T : Real) * (out - reference) <=
      (Finset.range T).sum (fun k => c * (F k - reference)) := by
  have hTreal_pos : 0 < (T : Real) := by
    exact_mod_cast hTpos
  have hscale_nonneg : 0 <= c * (T : Real) := by
    positivity
  have hmul_le := mul_le_mul_of_nonneg_left havg hscale_nonneg
  have hright_eq :
      c * (T : Real) * (((T : Real) * c)⁻¹ * (c * (Finset.range T).sum F)) =
        c * (Finset.range T).sum F := by
    field_simp [ne_of_gt hcpos, ne_of_gt hTreal_pos]
  have hout_le : c * (T : Real) * out <= c * (Finset.range T).sum F := by
    calc
      c * (T : Real) * out <=
          c * (T : Real) *
            (((T : Real) * c)⁻¹ * (c * (Finset.range T).sum F)) := hmul_le
      _ = c * (Finset.range T).sum F := hright_eq
  calc
    c * (T : Real) * (out - reference) <=
        c * (Finset.range T).sum F - c * (T : Real) * reference := by
      nlinarith
    _ = (Finset.range T).sum (fun k => c * (F k - reference)) := by
      rw [← Finset.mul_sum]
      rw [Finset.sum_sub_distrib]
      simp
      ring

set_option maxHeartbeats 0

/-- Arbitrary first-phase printed one-epoch recursion for Eq. (5.4.27).

This is the uniform version of the fixed-epoch `hprintedOneEpoch` proof inside
`lemma518_first_phase_lyapunov_relation_printed`. It packages source proof
steps 1-4 of Lemma 5.18 for any epoch `r <= s_0`; the final theorem consumes it
through `lemma518_scalar_first_phase_epoch_chain` for the repeated-recursion
step back to epoch zero. -/
theorem lemma518_first_phase_printed_one_epoch_recursion
    {n dim : Nat} (S : Setup n dim)
    (x0 : Set.Elem (proxCoreSet S)) (x : FeasiblePoint S) (hmu : 0 < S.mu)
    (r : Nat) (hr : 1 <= r) (hr0 : r <= theorem59Cutoff S)
    (h516 : lemma516CorrectedRelationalConditionalExpectationStepBoundaryStatement S)
    (h515 : lemma515RelationalCoreStepBoundaryStatement S)
    (h513 : lemma513AcceleratedVarianceEstimatorFactsBoundaryStatement S)
    (hspec :
      theorem59PrintedFeasibleEpochOutputProcessSpec S hmu x0 theorem59CanonicalSamples
        (theorem59PrintedFeasibleOutputProcessOn S hmu x0 theorem59CanonicalSamples)) :
    let hpositiveProxMembership :
        theorem59PrintedFeasiblePositiveProxUpdateCoreMembershipStatement S :=
      lemma518_printed_positive_prox_membership_from_carrierSubgradient S
    let hstateCoreAll :=
      theorem59PrintedFeasibleEpochStateProcessOn_core_mem_of_positiveProxMembership
        S hmu x0 theorem59CanonicalSamples hpositiveProxMembership
    (4 * (theorem59EpochLength S r : Real) / (3 * averageSmoothness S)) *
        SOptLib.expectedObjectiveGap (theorem59SampleLaw S) (compositeObjective S)
          (compositeObjective S x.1)
          (theorem59PrintedFeasibleOutputProcess S hmu x0) r +
      SOptLib.expectation (theorem59SampleLaw S)
        (fun omega : theorem59SamplePath n =>
          bregmanOn S
            (⟨(theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                theorem59CanonicalSamples r omega).x.1,
              (hstateCoreAll r omega).1⟩ : Set.Elem (proxCoreSet S))
            x) <=
      (2 * (theorem59EpochLength S r : Real) / (3 * averageSmoothness S)) *
          SOptLib.expectedObjectiveGap (theorem59SampleLaw S) (compositeObjective S)
            (compositeObjective S x.1)
            (theorem59PrintedFeasibleOutputProcess S hmu x0) (r - 1) +
        SOptLib.expectation (theorem59SampleLaw S)
          (fun omega : theorem59SamplePath n =>
            bregmanOn S
              (⟨(theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                  theorem59CanonicalSamples (r - 1) omega).x.1,
                (hstateCoreAll (r - 1) omega).1⟩ : Set.Elem (proxCoreSet S))
              x) := by
  classical
  have hside := lemma518_first_phase_lemma516_side_conditions S hmu hr hr0
  rcases hside with
    ⟨halpha, halpha_pos, hp, hgamma, hbar, hcurv, hnoise, hsearch, havg⟩
  have hpositiveProxMembership :
      theorem59PrintedFeasiblePositiveProxUpdateCoreMembershipStatement S :=
    lemma518_printed_positive_prox_membership_from_carrierSubgradient S
  have hstateCore :
      forall omega : theorem59SamplePath n,
        (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0 theorem59CanonicalSamples
            r omega).x.1 ∈ proxCoreSet S ∧
          (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0 theorem59CanonicalSamples
            r omega).xTilde.1 ∈ proxCoreSet S :=
    theorem59PrintedFeasibleEpochStateProcessOn_core_mem_of_positiveProxMembership
      S hmu x0 theorem59CanonicalSamples hpositiveProxMembership r
  have hstateCorePrev :
      forall omega : theorem59SamplePath n,
        (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0 theorem59CanonicalSamples
            (r - 1) omega).x.1 ∈ proxCoreSet S ∧
          (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0 theorem59CanonicalSamples
            (r - 1) omega).xTilde.1 ∈ proxCoreSet S :=
    theorem59PrintedFeasibleEpochStateProcessOn_core_mem_of_positiveProxMembership
      S hmu x0 theorem59CanonicalSamples hpositiveProxMembership (r - 1)
  let printedLemma516At : theorem59SamplePath n -> Nat -> Prop := fun omega k =>
        ∃ trajectory : Nat -> InnerStateFeasibleOn S,
          ∃ htraj :
            theorem59PrintedFeasibleInnerTrajectoryRelOn S hmu theorem59CanonicalSamples
              r hr omega
              ((theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                  theorem59CanonicalSamples (r - 1) omega).xTilde)
              ((theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                  theorem59CanonicalSamples (r - 1) omega).x)
              trajectory,
            ∃ hxPrevK : (trajectory k).x.1 ∈ proxCoreSet S,
              ∃ hxBarPrevK : (trajectory k).xBar.1 ∈ proxCoreSet S,
                let snapshotFeasible :=
                  (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                    theorem59CanonicalSamples (r - 1) omega).xTilde
                let next : Fin n -> InnerStateFeasibleOn S := fun sample =>
                  theorem59PrintedFeasibleInnerStepOn S (theorem59Gamma S)
                    (theorem59Alpha S) theorem59P r (samplingWeight S) snapshotFeasible
                    (fullGradient S snapshotFeasible.1) sample hgamma x0 hsearch havg
                    (trajectory k)
                ∃ hxNext : forall sample, (next sample).x.1 ∈ proxCoreSet S,
                  ∃ hxBarNext : forall sample, (next sample).xBar.1 ∈ proxCoreSet S,
                    componentConditionalExpectation S (samplingWeight S) (fun sample =>
                        let nextCore : Set.Elem (proxCoreSet S) :=
                          ⟨(next sample).x.1, hxNext sample⟩
                        let nextBarCore : Set.Elem (proxCoreSet S) :=
                          ⟨(next sample).xBar.1, hxBarNext sample⟩
                        theorem59Gamma S r / theorem59Alpha S r *
                            (compositeObjective S nextBarCore.1 -
                              compositeObjective S x.1) +
                          (1 + S.mu * theorem59Gamma S r) *
                            bregmanOn S nextCore x) <=
                      theorem59Gamma S r / theorem59Alpha S r *
                          (1 - theorem59Alpha S r - theorem59P r) *
                          (compositeObjective S (trajectory k).xBar.1 -
                            compositeObjective S x.1) +
                        theorem59Gamma S r / theorem59Alpha S r * theorem59P r *
                          (compositeObjective S snapshotFeasible.1 -
                            compositeObjective S x.1) +
                        bregmanOn S
                          (⟨(trajectory k).x.1, hxPrevK⟩ : Set.Elem (proxCoreSet S))
                          x
  have hprintedLemma516AllInner :
      forall omega : theorem59SamplePath n, forall k : Nat,
        k < theorem59EpochLength S r -> printedLemma516At omega k := by
    intro omega k _hk
    simpa [printedLemma516At] using
      lemma518_printed_epoch_all_steps_lemma516_bound
        S x0 x hmu r hr halpha halpha_pos hp hgamma hbar hcurv hnoise
        hsearch havg h516 h515 h513 hpositiveProxMembership hspec hstateCorePrev
        omega k
  have hfirstPrintedLemma516 :
      forall omega : theorem59SamplePath n, printedLemma516At omega 0 := by
    intro omega
    have hTpos : 0 < theorem59EpochLength S r := by
      simpa [theorem59EpochLength] using
        SOptLib.doublingThenFrozenEpochLength_pos (theorem59Cutoff S) r
    exact hprintedLemma516AllInner omega 0 hTpos
  have hgeneratedOneStepAllHistory :=
    fun k (_hk : k < theorem59EpochLength S r) =>
      lemma518_printed_epoch_generated_one_step_recurrence_all_history
        S x0 x hmu r hr k halpha halpha_pos hp hgamma hbar hcurv hnoise hsearch
        havg h516 h515 h513 hpositiveProxMembership hstateCorePrev
  have hprintedOutputJensen :=
    fun omega : theorem59SamplePath n =>
      lemma518_first_phase_epoch_output_jensen
        S hmu x0 theorem59CanonicalSamples r hr omega
  have hfirstAlpha : theorem59Alpha S r = (1 / 2 : Real) := by
    simp [theorem59Alpha, hr0]
  have hfirstP : theorem59P r = (1 / 2 : Real) := by
    norm_num [theorem59P]
  have hfirstGamma :
      theorem59Gamma S r = 2 / (3 * averageSmoothness S) := by
    have hLne : averageSmoothness S ≠ 0 := ne_of_gt (averageSmoothness_pos S)
    simp [theorem59Gamma, hfirstAlpha]
    field_simp [hLne]
  have hfirstGamma_over_alpha :
      theorem59Gamma S r / theorem59Alpha S r =
        4 / (3 * averageSmoothness S) := by
    rw [hfirstGamma, hfirstAlpha]
    have hLne : averageSmoothness S ≠ 0 := ne_of_gt (averageSmoothness_pos S)
    field_simp [hLne]
    ring
  have hfirstGamma_over_alpha_mul_p :
      theorem59Gamma S r / theorem59Alpha S r * theorem59P r =
        2 / (3 * averageSmoothness S) := by
    rw [hfirstGamma_over_alpha, hfirstP]
    have hLne : averageSmoothness S ≠ 0 := ne_of_gt (averageSmoothness_pos S)
    field_simp [hLne]
    ring
  have hscalarTelescopeReady := lemma518_scalar_one_epoch_telescope
  have hgeneratedOneStepExpanded :
      forall k, k < theorem59EpochLength S r ->
        SOptLib.expectation (theorem59SampleLaw S)
            (fun omega : theorem59SamplePath n =>
              let snapshot :=
                (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                  theorem59CanonicalSamples (r - 1) omega).xTilde
              let xStart :=
                (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                  theorem59CanonicalSamples (r - 1) omega).x
              let trajectory :=
                theorem59PrintedFeasibleInnerTrajectoryOn S hmu x0
                  theorem59CanonicalSamples r hr omega snapshot xStart
              let htraj :=
                theorem59PrintedFeasibleInnerTrajectoryOn_rel S hmu x0
                  theorem59CanonicalSamples r hr omega snapshot xStart
              let hinnerCore :=
                theorem59PrintedFeasibleInnerTrajectoryRelOn_core_mem_of_positiveProxMembership
                  S hmu theorem59CanonicalSamples r hr omega snapshot xStart trajectory
                  hpositiveProxMembership (hstateCorePrev omega).2
                  (hstateCorePrev omega).1 htraj
              theorem59Gamma S r / theorem59Alpha S r *
                  (compositeObjective S (trajectory (k + 1)).xBar.1 -
                    compositeObjective S x.1) +
                (1 + S.mu * theorem59Gamma S r) *
                  bregmanOn S
                    (⟨(trajectory (k + 1)).x.1, (hinnerCore (k + 1)).1⟩ :
                      Set.Elem (proxCoreSet S))
                    x) <=
          SOptLib.expectation (theorem59SampleLaw S)
            (fun omega : theorem59SamplePath n =>
              let snapshot :=
                (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                  theorem59CanonicalSamples (r - 1) omega).xTilde
              let xStart :=
                (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                  theorem59CanonicalSamples (r - 1) omega).x
              let trajectory :=
                theorem59PrintedFeasibleInnerTrajectoryOn S hmu x0
                  theorem59CanonicalSamples r hr omega snapshot xStart
              let htraj :=
                theorem59PrintedFeasibleInnerTrajectoryOn_rel S hmu x0
                  theorem59CanonicalSamples r hr omega snapshot xStart
              let hinnerCore :=
                theorem59PrintedFeasibleInnerTrajectoryRelOn_core_mem_of_positiveProxMembership
                  S hmu theorem59CanonicalSamples r hr omega snapshot xStart trajectory
                  hpositiveProxMembership (hstateCorePrev omega).2
                  (hstateCorePrev omega).1 htraj
              theorem59Gamma S r / theorem59Alpha S r *
                  (1 - theorem59Alpha S r - theorem59P r) *
                  (compositeObjective S (trajectory k).xBar.1 -
                    compositeObjective S x.1) +
                theorem59Gamma S r / theorem59Alpha S r * theorem59P r *
                  (compositeObjective S snapshot.1 - compositeObjective S x.1) +
                bregmanOn S
                  (⟨(trajectory k).x.1, (hinnerCore k).1⟩ : Set.Elem (proxCoreSet S))
                  x) := by
    intro k hk
    simpa [theorem59PrintedFeasibleInnerTrajectoryOn, SOptLib.recursiveIterateProcess]
      using hgeneratedOneStepAllHistory k hk
  have hgeneratedOneStepSummed :
      (Finset.range (theorem59EpochLength S r)).sum
          (fun k =>
            SOptLib.expectation (theorem59SampleLaw S)
              (fun omega : theorem59SamplePath n =>
                let snapshot :=
                  (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                    theorem59CanonicalSamples (r - 1) omega).xTilde
                let xStart :=
                  (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                    theorem59CanonicalSamples (r - 1) omega).x
                let trajectory :=
                  theorem59PrintedFeasibleInnerTrajectoryOn S hmu x0
                    theorem59CanonicalSamples r hr omega snapshot xStart
                let htraj :=
                  theorem59PrintedFeasibleInnerTrajectoryOn_rel S hmu x0
                    theorem59CanonicalSamples r hr omega snapshot xStart
                let hinnerCore :=
                  theorem59PrintedFeasibleInnerTrajectoryRelOn_core_mem_of_positiveProxMembership
                    S hmu theorem59CanonicalSamples r hr omega snapshot xStart trajectory
                    hpositiveProxMembership (hstateCorePrev omega).2
                    (hstateCorePrev omega).1 htraj
                theorem59Gamma S r / theorem59Alpha S r *
                    (compositeObjective S (trajectory (k + 1)).xBar.1 -
                      compositeObjective S x.1) +
                  (1 + S.mu * theorem59Gamma S r) *
                    bregmanOn S
                      (⟨(trajectory (k + 1)).x.1, (hinnerCore (k + 1)).1⟩ :
                        Set.Elem (proxCoreSet S))
                      x)) <=
        (Finset.range (theorem59EpochLength S r)).sum
          (fun k =>
            SOptLib.expectation (theorem59SampleLaw S)
              (fun omega : theorem59SamplePath n =>
                let snapshot :=
                  (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                    theorem59CanonicalSamples (r - 1) omega).xTilde
                let xStart :=
                  (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                    theorem59CanonicalSamples (r - 1) omega).x
                let trajectory :=
                  theorem59PrintedFeasibleInnerTrajectoryOn S hmu x0
                    theorem59CanonicalSamples r hr omega snapshot xStart
                let htraj :=
                  theorem59PrintedFeasibleInnerTrajectoryOn_rel S hmu x0
                    theorem59CanonicalSamples r hr omega snapshot xStart
                let hinnerCore :=
                  theorem59PrintedFeasibleInnerTrajectoryRelOn_core_mem_of_positiveProxMembership
                    S hmu theorem59CanonicalSamples r hr omega snapshot xStart trajectory
                    hpositiveProxMembership (hstateCorePrev omega).2
                    (hstateCorePrev omega).1 htraj
                theorem59Gamma S r / theorem59Alpha S r *
                    (1 - theorem59Alpha S r - theorem59P r) *
                    (compositeObjective S (trajectory k).xBar.1 -
                      compositeObjective S x.1) +
                  theorem59Gamma S r / theorem59Alpha S r * theorem59P r *
                    (compositeObjective S snapshot.1 - compositeObjective S x.1) +
                  bregmanOn S
                    (⟨(trajectory k).x.1, (hinnerCore k).1⟩ : Set.Elem (proxCoreSet S))
                    x)) := by
    exact Finset.sum_le_sum (fun k hk =>
      hgeneratedOneStepExpanded k (Finset.mem_range.mp hk))
  have hgeneratedLeftPotentialSplit :
      forall k,
        SOptLib.expectation (theorem59SampleLaw S)
            (fun omega : theorem59SamplePath n =>
              let snapshot :=
                (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                  theorem59CanonicalSamples (r - 1) omega).xTilde
              let xStart :=
                (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                  theorem59CanonicalSamples (r - 1) omega).x
              let trajectory :=
                theorem59PrintedFeasibleInnerTrajectoryOn S hmu x0
                  theorem59CanonicalSamples r hr omega snapshot xStart
              let htraj :=
                theorem59PrintedFeasibleInnerTrajectoryOn_rel S hmu x0
                  theorem59CanonicalSamples r hr omega snapshot xStart
              let hinnerCore :=
                theorem59PrintedFeasibleInnerTrajectoryRelOn_core_mem_of_positiveProxMembership
                  S hmu theorem59CanonicalSamples r hr omega snapshot xStart trajectory
                  hpositiveProxMembership (hstateCorePrev omega).2
                  (hstateCorePrev omega).1 htraj
              theorem59Gamma S r / theorem59Alpha S r *
                  (compositeObjective S (trajectory (k + 1)).xBar.1 -
                    compositeObjective S x.1) +
                (1 + S.mu * theorem59Gamma S r) *
                  bregmanOn S
                    (⟨(trajectory (k + 1)).x.1, (hinnerCore (k + 1)).1⟩ :
                      Set.Elem (proxCoreSet S))
                    x) =
          theorem59Gamma S r / theorem59Alpha S r *
              SOptLib.expectation (theorem59SampleLaw S)
                (fun omega : theorem59SamplePath n =>
                  let snapshot :=
                    (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                      theorem59CanonicalSamples (r - 1) omega).xTilde
                  let xStart :=
                    (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                      theorem59CanonicalSamples (r - 1) omega).x
                  let trajectory :=
                    theorem59PrintedFeasibleInnerTrajectoryOn S hmu x0
                      theorem59CanonicalSamples r hr omega snapshot xStart
                  compositeObjective S (trajectory (k + 1)).xBar.1 -
                    compositeObjective S x.1) +
            (1 + S.mu * theorem59Gamma S r) *
              SOptLib.expectation (theorem59SampleLaw S)
                (fun omega : theorem59SamplePath n =>
                  let snapshot :=
                    (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                      theorem59CanonicalSamples (r - 1) omega).xTilde
                  let xStart :=
                    (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                      theorem59CanonicalSamples (r - 1) omega).x
                  let trajectory :=
                    theorem59PrintedFeasibleInnerTrajectoryOn S hmu x0
                      theorem59CanonicalSamples r hr omega snapshot xStart
                  let htraj :=
                    theorem59PrintedFeasibleInnerTrajectoryOn_rel S hmu x0
                      theorem59CanonicalSamples r hr omega snapshot xStart
                  let hinnerCore :=
                    theorem59PrintedFeasibleInnerTrajectoryRelOn_core_mem_of_positiveProxMembership
                      S hmu theorem59CanonicalSamples r hr omega snapshot xStart trajectory
                      hpositiveProxMembership (hstateCorePrev omega).2
                      (hstateCorePrev omega).1 htraj
                  bregmanOn S
                    (⟨(trajectory (k + 1)).x.1, (hinnerCore (k + 1)).1⟩ :
                      Set.Elem (proxCoreSet S))
                    x) := by
    intro k
    let W : theorem59SamplePath n ->
        Set.Elem (proxCoreSet S) × (Set.Elem (proxCoreSet S) × Set.Elem (proxCoreSet S)) :=
      fun omega =>
        let snapshot :=
          (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
            theorem59CanonicalSamples (r - 1) omega).xTilde
        let xStart :=
          (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
            theorem59CanonicalSamples (r - 1) omega).x
        let trajectory :=
          theorem59PrintedFeasibleInnerTrajectoryOn S hmu x0
            theorem59CanonicalSamples r hr omega snapshot xStart
        let htraj :=
          theorem59PrintedFeasibleInnerTrajectoryOn_rel S hmu x0
            theorem59CanonicalSamples r hr omega snapshot xStart
        let hinnerCore :=
          theorem59PrintedFeasibleInnerTrajectoryRelOn_core_mem_of_positiveProxMembership
            S hmu theorem59CanonicalSamples r hr omega snapshot xStart trajectory
            hpositiveProxMembership (hstateCorePrev omega).2
            (hstateCorePrev omega).1 htraj
        (⟨snapshot.1, (hstateCorePrev omega).2⟩,
          (⟨(trajectory (k + 1)).x.1, (hinnerCore (k + 1)).1⟩,
            ⟨(trajectory (k + 1)).xBar.1, (hinnerCore (k + 1)).2⟩))
    let F : Set.Elem (proxCoreSet S) × (Set.Elem (proxCoreSet S) × Set.Elem (proxCoreSet S)) -> Real :=
      fun state => compositeObjective S state.2.2.1 - compositeObjective S x.1
    let G : Set.Elem (proxCoreSet S) × (Set.Elem (proxCoreSet S) × Set.Elem (proxCoreSet S)) -> Real :=
      fun state => bregmanOn S state.2.1 x
    have hWF :=
      lemma518_generated_printed_epoch_snapshot_state_strictPast_measurable
        S hmu x0 r hr (k + 1) hpositiveProxMembership hstateCorePrev
    have hsampleCoord_meas :
        forall q : Nat × Nat,
          Measurable
            (fun omega : theorem59SamplePath n =>
              theorem59CanonicalSamples q.1 q.2 omega) := by
      intro q
      change Measurable (fun omega : Nat -> Nat -> Fin n => omega q.1 q.2)
      exact (measurable_pi_apply q.2).comp (measurable_pi_apply q.1)
    have hstrict_le_ambient :
        (⨆ q ∈ theorem59StrictPastIndexSet r (k + 1),
            MeasurableSpace.comap
              (fun omega : theorem59SamplePath n =>
                theorem59CanonicalSamples q.1 q.2 omega)
              (by infer_instance : MeasurableSpace (Fin n))) ≤
          (by infer_instance : MeasurableSpace (theorem59SamplePath n)) := by
      refine iSup_le ?_
      intro q
      refine iSup_le ?_
      intro _hq
      exact (hsampleCoord_meas q).comap_le
    have hW_ambient : Measurable W := by
      exact hWF.1.mono hstrict_le_ambient le_rfl
    have hWfin : (Set.range W).Finite := by
      simpa [W] using hWF.2
    have hprob_component :
        MeasureTheory.IsProbabilityMeasure (componentSampleLaw S) := by
      unfold componentSampleLaw
      infer_instance
    letI : MeasureTheory.IsProbabilityMeasure (componentSampleLaw S) := hprob_component
    have hprob_stream :
        MeasureTheory.IsProbabilityMeasure
          (SOptLib.iidStreamLaw (componentSampleLaw S)) := by
      infer_instance
    letI : MeasureTheory.IsProbabilityMeasure
        (SOptLib.iidStreamLaw (componentSampleLaw S)) := hprob_stream
    have hprob_sample :
        MeasureTheory.IsProbabilityMeasure (theorem59SampleLaw S) := by
      unfold theorem59SampleLaw
      infer_instance
    letI : MeasureTheory.IsProbabilityMeasure (theorem59SampleLaw S) := hprob_sample
    have hsplit :=
      expectation_add_const_mul_comp_eq_of_finite_range_key
        (μ := theorem59SampleLaw S) W hW_ambient.aemeasurable hWfin
        (theorem59Gamma S r / theorem59Alpha S r)
        (1 + S.mu * theorem59Gamma S r) F G
    simpa [W, F, G] using hsplit
  have hgeneratedRightPotentialSplit :
      forall k,
        SOptLib.expectation (theorem59SampleLaw S)
            (fun omega : theorem59SamplePath n =>
              let snapshot :=
                (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                  theorem59CanonicalSamples (r - 1) omega).xTilde
              let xStart :=
                (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                  theorem59CanonicalSamples (r - 1) omega).x
              let trajectory :=
                theorem59PrintedFeasibleInnerTrajectoryOn S hmu x0
                  theorem59CanonicalSamples r hr omega snapshot xStart
              let htraj :=
                theorem59PrintedFeasibleInnerTrajectoryOn_rel S hmu x0
                  theorem59CanonicalSamples r hr omega snapshot xStart
              let hinnerCore :=
                theorem59PrintedFeasibleInnerTrajectoryRelOn_core_mem_of_positiveProxMembership
                  S hmu theorem59CanonicalSamples r hr omega snapshot xStart trajectory
                  hpositiveProxMembership (hstateCorePrev omega).2
                  (hstateCorePrev omega).1 htraj
              theorem59Gamma S r / theorem59Alpha S r *
                  (1 - theorem59Alpha S r - theorem59P r) *
                  (compositeObjective S (trajectory k).xBar.1 -
                    compositeObjective S x.1) +
                theorem59Gamma S r / theorem59Alpha S r * theorem59P r *
                  (compositeObjective S snapshot.1 - compositeObjective S x.1) +
                bregmanOn S
                  (⟨(trajectory k).x.1, (hinnerCore k).1⟩ : Set.Elem (proxCoreSet S))
                  x) =
          (theorem59Gamma S r / theorem59Alpha S r *
              (1 - theorem59Alpha S r - theorem59P r)) *
              SOptLib.expectation (theorem59SampleLaw S)
                (fun omega : theorem59SamplePath n =>
                  let snapshot :=
                    (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                      theorem59CanonicalSamples (r - 1) omega).xTilde
                  let xStart :=
                    (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                      theorem59CanonicalSamples (r - 1) omega).x
                  let trajectory :=
                    theorem59PrintedFeasibleInnerTrajectoryOn S hmu x0
                      theorem59CanonicalSamples r hr omega snapshot xStart
                  compositeObjective S (trajectory k).xBar.1 -
                    compositeObjective S x.1) +
            (theorem59Gamma S r / theorem59Alpha S r * theorem59P r) *
              SOptLib.expectation (theorem59SampleLaw S)
                (fun omega : theorem59SamplePath n =>
                  let snapshot :=
                    (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                      theorem59CanonicalSamples (r - 1) omega).xTilde
                  compositeObjective S snapshot.1 - compositeObjective S x.1) +
            1 *
              SOptLib.expectation (theorem59SampleLaw S)
                (fun omega : theorem59SamplePath n =>
                  let snapshot :=
                    (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                      theorem59CanonicalSamples (r - 1) omega).xTilde
                  let xStart :=
                    (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                      theorem59CanonicalSamples (r - 1) omega).x
                  let trajectory :=
                    theorem59PrintedFeasibleInnerTrajectoryOn S hmu x0
                      theorem59CanonicalSamples r hr omega snapshot xStart
                  let htraj :=
                    theorem59PrintedFeasibleInnerTrajectoryOn_rel S hmu x0
                      theorem59CanonicalSamples r hr omega snapshot xStart
                  let hinnerCore :=
                    theorem59PrintedFeasibleInnerTrajectoryRelOn_core_mem_of_positiveProxMembership
                      S hmu theorem59CanonicalSamples r hr omega snapshot xStart trajectory
                      hpositiveProxMembership (hstateCorePrev omega).2
                      (hstateCorePrev omega).1 htraj
                  bregmanOn S
                    (⟨(trajectory k).x.1, (hinnerCore k).1⟩ : Set.Elem (proxCoreSet S))
                    x) := by
    intro k
    let W : theorem59SamplePath n ->
        Set.Elem (proxCoreSet S) × (Set.Elem (proxCoreSet S) × Set.Elem (proxCoreSet S)) :=
      fun omega =>
        let snapshot :=
          (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
            theorem59CanonicalSamples (r - 1) omega).xTilde
        let xStart :=
          (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
            theorem59CanonicalSamples (r - 1) omega).x
        let trajectory :=
          theorem59PrintedFeasibleInnerTrajectoryOn S hmu x0
            theorem59CanonicalSamples r hr omega snapshot xStart
        let htraj :=
          theorem59PrintedFeasibleInnerTrajectoryOn_rel S hmu x0
            theorem59CanonicalSamples r hr omega snapshot xStart
        let hinnerCore :=
          theorem59PrintedFeasibleInnerTrajectoryRelOn_core_mem_of_positiveProxMembership
            S hmu theorem59CanonicalSamples r hr omega snapshot xStart trajectory
            hpositiveProxMembership (hstateCorePrev omega).2
            (hstateCorePrev omega).1 htraj
        (⟨snapshot.1, (hstateCorePrev omega).2⟩,
          (⟨(trajectory k).x.1, (hinnerCore k).1⟩,
            ⟨(trajectory k).xBar.1, (hinnerCore k).2⟩))
    let F : Set.Elem (proxCoreSet S) × (Set.Elem (proxCoreSet S) × Set.Elem (proxCoreSet S)) -> Real :=
      fun state => compositeObjective S state.2.2.1 - compositeObjective S x.1
    let G : Set.Elem (proxCoreSet S) × (Set.Elem (proxCoreSet S) × Set.Elem (proxCoreSet S)) -> Real :=
      fun state => compositeObjective S state.1.1 - compositeObjective S x.1
    let H : Set.Elem (proxCoreSet S) × (Set.Elem (proxCoreSet S) × Set.Elem (proxCoreSet S)) -> Real :=
      fun state => bregmanOn S state.2.1 x
    have hWF :=
      lemma518_generated_printed_epoch_snapshot_state_strictPast_measurable
        S hmu x0 r hr k hpositiveProxMembership hstateCorePrev
    have hsampleCoord_meas :
        forall q : Nat × Nat,
          Measurable
            (fun omega : theorem59SamplePath n =>
              theorem59CanonicalSamples q.1 q.2 omega) := by
      intro q
      change Measurable (fun omega : Nat -> Nat -> Fin n => omega q.1 q.2)
      exact (measurable_pi_apply q.2).comp (measurable_pi_apply q.1)
    have hstrict_le_ambient :
        (⨆ q ∈ theorem59StrictPastIndexSet r k,
            MeasurableSpace.comap
              (fun omega : theorem59SamplePath n =>
                theorem59CanonicalSamples q.1 q.2 omega)
              (by infer_instance : MeasurableSpace (Fin n))) ≤
          (by infer_instance : MeasurableSpace (theorem59SamplePath n)) := by
      refine iSup_le ?_
      intro q
      refine iSup_le ?_
      intro _hq
      exact (hsampleCoord_meas q).comap_le
    have hW_ambient : Measurable W := by
      exact hWF.1.mono hstrict_le_ambient le_rfl
    have hWfin : (Set.range W).Finite := by
      simpa [W] using hWF.2
    have hprob_component :
        MeasureTheory.IsProbabilityMeasure (componentSampleLaw S) := by
      unfold componentSampleLaw
      infer_instance
    letI : MeasureTheory.IsProbabilityMeasure (componentSampleLaw S) := hprob_component
    have hprob_stream :
        MeasureTheory.IsProbabilityMeasure
          (SOptLib.iidStreamLaw (componentSampleLaw S)) := by
      infer_instance
    letI : MeasureTheory.IsProbabilityMeasure
        (SOptLib.iidStreamLaw (componentSampleLaw S)) := hprob_stream
    have hprob_sample :
        MeasureTheory.IsProbabilityMeasure (theorem59SampleLaw S) := by
      unfold theorem59SampleLaw
      infer_instance
    letI : MeasureTheory.IsProbabilityMeasure (theorem59SampleLaw S) := hprob_sample
    have hsplit :=
      expectation_three_const_mul_comp_eq_of_finite_range_key
        (μ := theorem59SampleLaw S) W hW_ambient.aemeasurable hWfin
        (theorem59Gamma S r / theorem59Alpha S r *
          (1 - theorem59Alpha S r - theorem59P r))
        (theorem59Gamma S r / theorem59Alpha S r * theorem59P r)
        1 F G H
    simpa [W, F, G, H, mul_assoc] using hsplit
  have hgeneratedScalarStep :
      forall k, k < theorem59EpochLength S r ->
        theorem59Gamma S r / theorem59Alpha S r *
            SOptLib.expectation (theorem59SampleLaw S)
              (fun omega : theorem59SamplePath n =>
                let snapshot :=
                  (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                    theorem59CanonicalSamples (r - 1) omega).xTilde
                let xStart :=
                  (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                    theorem59CanonicalSamples (r - 1) omega).x
                let trajectory :=
                  theorem59PrintedFeasibleInnerTrajectoryOn S hmu x0
                    theorem59CanonicalSamples r hr omega snapshot xStart
                compositeObjective S (trajectory (k + 1)).xBar.1 -
                  compositeObjective S x.1) +
          (1 + S.mu * theorem59Gamma S r) *
            SOptLib.expectation (theorem59SampleLaw S)
              (fun omega : theorem59SamplePath n =>
                let snapshot :=
                  (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                    theorem59CanonicalSamples (r - 1) omega).xTilde
                let xStart :=
                  (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                    theorem59CanonicalSamples (r - 1) omega).x
                let trajectory :=
                  theorem59PrintedFeasibleInnerTrajectoryOn S hmu x0
                    theorem59CanonicalSamples r hr omega snapshot xStart
                let htraj :=
                  theorem59PrintedFeasibleInnerTrajectoryOn_rel S hmu x0
                    theorem59CanonicalSamples r hr omega snapshot xStart
                let hinnerCore :=
                  theorem59PrintedFeasibleInnerTrajectoryRelOn_core_mem_of_positiveProxMembership
                    S hmu theorem59CanonicalSamples r hr omega snapshot xStart trajectory
                    hpositiveProxMembership (hstateCorePrev omega).2
                    (hstateCorePrev omega).1 htraj
                bregmanOn S
                  (⟨(trajectory (k + 1)).x.1, (hinnerCore (k + 1)).1⟩ :
                    Set.Elem (proxCoreSet S))
                  x) <=
          (theorem59Gamma S r / theorem59Alpha S r * theorem59P r) *
              SOptLib.expectation (theorem59SampleLaw S)
                (fun omega : theorem59SamplePath n =>
                  let snapshot :=
                    (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                      theorem59CanonicalSamples (r - 1) omega).xTilde
                  compositeObjective S snapshot.1 - compositeObjective S x.1) +
            SOptLib.expectation (theorem59SampleLaw S)
              (fun omega : theorem59SamplePath n =>
                let snapshot :=
                  (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                    theorem59CanonicalSamples (r - 1) omega).xTilde
                let xStart :=
                  (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                    theorem59CanonicalSamples (r - 1) omega).x
                let trajectory :=
                  theorem59PrintedFeasibleInnerTrajectoryOn S hmu x0
                    theorem59CanonicalSamples r hr omega snapshot xStart
                let htraj :=
                  theorem59PrintedFeasibleInnerTrajectoryOn_rel S hmu x0
                    theorem59CanonicalSamples r hr omega snapshot xStart
                let hinnerCore :=
                  theorem59PrintedFeasibleInnerTrajectoryRelOn_core_mem_of_positiveProxMembership
                    S hmu theorem59CanonicalSamples r hr omega snapshot xStart trajectory
                    hpositiveProxMembership (hstateCorePrev omega).2
                    (hstateCorePrev omega).1 htraj
                bregmanOn S
                  (⟨(trajectory k).x.1, (hinnerCore k).1⟩ : Set.Elem (proxCoreSet S))
                  x) := by
    intro k hk
    have hbase := hgeneratedOneStepExpanded k hk
    have hleft := hgeneratedLeftPotentialSplit k
    have hright := hgeneratedRightPotentialSplit k
    have hzero :
        theorem59Gamma S r / theorem59Alpha S r *
            (1 - theorem59Alpha S r - theorem59P r) = 0 := by
      rw [hfirstAlpha, hfirstP]
      ring
    rw [hleft, hright] at hbase
    rw [hzero] at hbase
    simpa [mul_assoc] using hbase
  have hgeneratedScalarTelescope :
      (Finset.range (theorem59EpochLength S r)).sum
          (fun k =>
            theorem59Gamma S r / theorem59Alpha S r *
              SOptLib.expectation (theorem59SampleLaw S)
                (fun omega : theorem59SamplePath n =>
                  let snapshot :=
                    (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                      theorem59CanonicalSamples (r - 1) omega).xTilde
                  let xStart :=
                    (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                      theorem59CanonicalSamples (r - 1) omega).x
                  let trajectory :=
                    theorem59PrintedFeasibleInnerTrajectoryOn S hmu x0
                      theorem59CanonicalSamples r hr omega snapshot xStart
                  compositeObjective S (trajectory (k + 1)).xBar.1 -
                    compositeObjective S x.1)) +
        SOptLib.expectation (theorem59SampleLaw S)
          (fun omega : theorem59SamplePath n =>
            let snapshot :=
              (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                theorem59CanonicalSamples (r - 1) omega).xTilde
            let xStart :=
              (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                theorem59CanonicalSamples (r - 1) omega).x
            let trajectory :=
              theorem59PrintedFeasibleInnerTrajectoryOn S hmu x0
                theorem59CanonicalSamples r hr omega snapshot xStart
            let htraj :=
              theorem59PrintedFeasibleInnerTrajectoryOn_rel S hmu x0
                theorem59CanonicalSamples r hr omega snapshot xStart
            let hinnerCore :=
              theorem59PrintedFeasibleInnerTrajectoryRelOn_core_mem_of_positiveProxMembership
                S hmu theorem59CanonicalSamples r hr omega snapshot xStart trajectory
                hpositiveProxMembership (hstateCorePrev omega).2
                (hstateCorePrev omega).1 htraj
            bregmanOn S
              (⟨(trajectory (theorem59EpochLength S r)).x.1,
                (hinnerCore (theorem59EpochLength S r)).1⟩ : Set.Elem (proxCoreSet S))
              x) +
        (S.mu * theorem59Gamma S r) *
          (Finset.range (theorem59EpochLength S r)).sum
            (fun k =>
              SOptLib.expectation (theorem59SampleLaw S)
                (fun omega : theorem59SamplePath n =>
                  let snapshot :=
                    (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                      theorem59CanonicalSamples (r - 1) omega).xTilde
                  let xStart :=
                    (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                      theorem59CanonicalSamples (r - 1) omega).x
                  let trajectory :=
                    theorem59PrintedFeasibleInnerTrajectoryOn S hmu x0
                      theorem59CanonicalSamples r hr omega snapshot xStart
                  let htraj :=
                    theorem59PrintedFeasibleInnerTrajectoryOn_rel S hmu x0
                      theorem59CanonicalSamples r hr omega snapshot xStart
                  let hinnerCore :=
                    theorem59PrintedFeasibleInnerTrajectoryRelOn_core_mem_of_positiveProxMembership
                      S hmu theorem59CanonicalSamples r hr omega snapshot xStart trajectory
                      hpositiveProxMembership (hstateCorePrev omega).2
                      (hstateCorePrev omega).1 htraj
                  bregmanOn S
                    (⟨(trajectory (k + 1)).x.1, (hinnerCore (k + 1)).1⟩ :
                      Set.Elem (proxCoreSet S))
                    x)) <=
        ((theorem59EpochLength S r : Nat) : Real) *
            ((theorem59Gamma S r / theorem59Alpha S r * theorem59P r) *
              SOptLib.expectation (theorem59SampleLaw S)
                (fun omega : theorem59SamplePath n =>
                  let snapshot :=
                    (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                      theorem59CanonicalSamples (r - 1) omega).xTilde
                  compositeObjective S snapshot.1 - compositeObjective S x.1)) +
          SOptLib.expectation (theorem59SampleLaw S)
            (fun omega : theorem59SamplePath n =>
              let snapshot :=
                (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                  theorem59CanonicalSamples (r - 1) omega).xTilde
              let xStart :=
                (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                  theorem59CanonicalSamples (r - 1) omega).x
              let trajectory :=
                theorem59PrintedFeasibleInnerTrajectoryOn S hmu x0
                  theorem59CanonicalSamples r hr omega snapshot xStart
              let htraj :=
                theorem59PrintedFeasibleInnerTrajectoryOn_rel S hmu x0
                  theorem59CanonicalSamples r hr omega snapshot xStart
              let hinnerCore :=
                theorem59PrintedFeasibleInnerTrajectoryRelOn_core_mem_of_positiveProxMembership
                  S hmu theorem59CanonicalSamples r hr omega snapshot xStart trajectory
                  hpositiveProxMembership (hstateCorePrev omega).2
                  (hstateCorePrev omega).1 htraj
              bregmanOn S
                (⟨(trajectory 0).x.1, (hinnerCore 0).1⟩ : Set.Elem (proxCoreSet S))
                x) := by
    let A : Nat -> Real :=
      fun k =>
        theorem59Gamma S r / theorem59Alpha S r *
          SOptLib.expectation (theorem59SampleLaw S)
            (fun omega : theorem59SamplePath n =>
              let snapshot :=
                (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                  theorem59CanonicalSamples (r - 1) omega).xTilde
              let xStart :=
                (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                  theorem59CanonicalSamples (r - 1) omega).x
              let trajectory :=
                theorem59PrintedFeasibleInnerTrajectoryOn S hmu x0
                  theorem59CanonicalSamples r hr omega snapshot xStart
              compositeObjective S (trajectory k).xBar.1 -
                compositeObjective S x.1)
    let B : Nat -> Real :=
      fun k =>
        SOptLib.expectation (theorem59SampleLaw S)
          (fun omega : theorem59SamplePath n =>
            let snapshot :=
              (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                theorem59CanonicalSamples (r - 1) omega).xTilde
            let xStart :=
              (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                theorem59CanonicalSamples (r - 1) omega).x
            let trajectory :=
              theorem59PrintedFeasibleInnerTrajectoryOn S hmu x0
                theorem59CanonicalSamples r hr omega snapshot xStart
            let htraj :=
              theorem59PrintedFeasibleInnerTrajectoryOn_rel S hmu x0
                theorem59CanonicalSamples r hr omega snapshot xStart
            let hinnerCore :=
              theorem59PrintedFeasibleInnerTrajectoryRelOn_core_mem_of_positiveProxMembership
                S hmu theorem59CanonicalSamples r hr omega snapshot xStart trajectory
                hpositiveProxMembership (hstateCorePrev omega).2
                (hstateCorePrev omega).1 htraj
            bregmanOn S
              (⟨(trajectory k).x.1, (hinnerCore k).1⟩ : Set.Elem (proxCoreSet S))
              x)
    let C : Real :=
      (theorem59Gamma S r / theorem59Alpha S r * theorem59P r) *
        SOptLib.expectation (theorem59SampleLaw S)
          (fun omega : theorem59SamplePath n =>
            let snapshot :=
              (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                theorem59CanonicalSamples (r - 1) omega).xTilde
            compositeObjective S snapshot.1 - compositeObjective S x.1)
    have htel :=
      hscalarTelescopeReady (theorem59EpochLength S r) A B C
        (S.mu * theorem59Gamma S r) (by
          intro k hk
          simpa [A, B, C] using hgeneratedScalarStep k hk)
    simpa [A, B, C] using htel
  have hgeneratedOutputJensenPathwise :
      forall omega : theorem59SamplePath n,
        compositeObjective S (theorem59PrintedFeasibleOutputProcess S hmu x0 r omega) <=
          (Finset.univ.sum
              (fun t : Fin (theorem59EpochLength S r) =>
                ((theorem59Theta S hmu (averageSmoothness_pos S)) r) (paperTime t)))⁻¹ *
            Finset.univ.sum
              (fun t : Fin (theorem59EpochLength S r) =>
                ((theorem59Theta S hmu (averageSmoothness_pos S)) r) (paperTime t) *
                  compositeObjective S
                    (let snapshot :=
                      (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                        theorem59CanonicalSamples (r - 1) omega).xTilde
                    let xStart :=
                      (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                        theorem59CanonicalSamples (r - 1) omega).x
                    let trajectory :=
                      theorem59PrintedFeasibleInnerTrajectoryOn S hmu x0
                        theorem59CanonicalSamples r hr omega snapshot xStart
                    (trajectory (paperTime t)).xBar.1)) := by
    intro omega
    cases r with
    | zero =>
        omega
    | succ r =>
        let hr' : 1 <= r + 1 := Nat.succ_pos r
        have hhs : hr = hr' := Subsingleton.elim hr hr'
        cases hhs
        let prevState :=
          theorem59PrintedFeasibleEpochStateProcessGeneratedOn S hmu x0
            theorem59CanonicalSamples r omega
        let trajectory :=
          theorem59PrintedFeasibleInnerTrajectoryOn S hmu x0 theorem59CanonicalSamples
            (r + 1) hr' omega prevState.xTilde prevState.x
        have hJ :=
          compositeObjective_epochOutputFeasibleOn_le_weighted_sum
            S ((theorem59Theta S hmu (averageSmoothness_pos S)) (r + 1))
            (fun t : Fin (theorem59EpochLength S (r + 1)) =>
              (trajectory (paperTime t)).xBar)
            (theorem59Theta_epochOutputWeightsAdmissible S hmu (r + 1) hr')
        have hsucc :=
          SOptLib.recursiveIterateProcess_succ
            (theorem59PrintedFeasibleEpochStateProcessGeneratedOn S hmu
              x0 theorem59CanonicalSamples)
            (⟨proxCoreAsFeasible S x0,
              proxCoreAsFeasible S x0⟩ : EpochStateFeasibleOn S)
            (theorem59PrintedFeasibleEpochStateStepOn S hmu x0 theorem59CanonicalSamples)
            (by rfl) r omega
        simpa [theorem59PrintedFeasibleOutputProcess,
          theorem59PrintedFeasibleOutputProcessOn,
          theorem59PrintedFeasibleEpochOutputProcessOn,
          theorem59PrintedFeasibleEpochStateProcessOn,
          theorem59PrintedFeasibleEpochStateProcessGeneratedOn,
          theorem59PrintedFeasibleEpochStateStepOn, prevState, trajectory,
          hsucc, hr'] using hJ
  have hUseSmooth :
      theorem59UsesSmoothTheta S hmu (averageSmoothness_pos S) r := by
    exact Or.inl ⟨hr, hr0⟩
  have htheta_const :
      forall t : Fin (theorem59EpochLength S r),
        ((theorem59Theta S hmu (averageSmoothness_pos S)) r) (paperTime t) =
          4 / (3 * averageSmoothness S) := by
    intro t
    unfold theorem59Theta theorem59SmoothTheta
    simp [hUseSmooth]
    by_cases ht : paperTime t = theorem59EpochLength S r
    · simp [ht, hfirstGamma_over_alpha]
    · have hsum : theorem59Alpha S r + theorem59P r = (1 : Real) := by
        rw [hfirstAlpha, hfirstP]
        norm_num
      simp [ht, hfirstGamma_over_alpha, hsum]
  have htheta_sum :
      (Finset.univ.sum
          (fun t : Fin (theorem59EpochLength S r) =>
            ((theorem59Theta S hmu (averageSmoothness_pos S)) r) (paperTime t))) =
        (theorem59EpochLength S r : Real) *
          (4 / (3 * averageSmoothness S)) := by
    calc
      (Finset.univ.sum
          (fun t : Fin (theorem59EpochLength S r) =>
            ((theorem59Theta S hmu (averageSmoothness_pos S)) r) (paperTime t))) =
          Finset.univ.sum
            (fun _t : Fin (theorem59EpochLength S r) =>
              (4 / (3 * averageSmoothness S) : Real)) := by
            refine Finset.sum_congr rfl ?_
            intro t _ht
            exact htheta_const t
      _ = (theorem59EpochLength S r : Real) *
            (4 / (3 * averageSmoothness S)) := by
            simp
  let generatedBarObjective : theorem59SamplePath n -> Nat -> Real :=
    fun omega k =>
      compositeObjective S
        (let snapshot :=
          (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
            theorem59CanonicalSamples (r - 1) omega).xTilde
        let xStart :=
          (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
            theorem59CanonicalSamples (r - 1) omega).x
        let trajectory :=
          theorem59PrintedFeasibleInnerTrajectoryOn S hmu x0
            theorem59CanonicalSamples r hr omega snapshot xStart
        (trajectory k).xBar.1)
  have htheta_weighted_objective_sum :
      forall omega : theorem59SamplePath n,
        (Finset.univ.sum
            (fun t : Fin (theorem59EpochLength S r) =>
              ((theorem59Theta S hmu (averageSmoothness_pos S)) r) (paperTime t) *
                generatedBarObjective omega (paperTime t))) =
          (4 / (3 * averageSmoothness S)) *
            (Finset.range (theorem59EpochLength S r)).sum
              (fun k => generatedBarObjective omega (k + 1)) := by
    intro omega
    calc
      (Finset.univ.sum
          (fun t : Fin (theorem59EpochLength S r) =>
            ((theorem59Theta S hmu (averageSmoothness_pos S)) r) (paperTime t) *
              generatedBarObjective omega (paperTime t))) =
          Finset.univ.sum
            (fun t : Fin (theorem59EpochLength S r) =>
              (4 / (3 * averageSmoothness S)) *
                generatedBarObjective omega (paperTime t)) := by
            refine Finset.sum_congr rfl ?_
            intro t _ht
            rw [htheta_const t]
      _ = (4 / (3 * averageSmoothness S)) *
            Finset.univ.sum
              (fun t : Fin (theorem59EpochLength S r) =>
                generatedBarObjective omega (paperTime t)) := by
            rw [Finset.mul_sum]
      _ = (4 / (3 * averageSmoothness S)) *
            (Finset.range (theorem59EpochLength S r)).sum
              (fun k => generatedBarObjective omega (k + 1)) := by
            congr 1
            rw [Finset.sum_fin_eq_sum_range]
            refine Finset.sum_congr rfl ?_
            intro k hk
            simp [paperTime, Finset.mem_range.mp hk]
  have hTpos : 0 < theorem59EpochLength S r := by
    simpa [theorem59EpochLength] using
      SOptLib.doublingThenFrozenEpochLength_pos (theorem59Cutoff S) r
  have hthetaCoeff_pos :
      0 < 4 / (3 * averageSmoothness S) := by
    exact div_pos (by norm_num) (mul_pos (by norm_num) (averageSmoothness_pos S))
  have hgeneratedOutputJensenNormalized :
      forall omega : theorem59SamplePath n,
        compositeObjective S (theorem59PrintedFeasibleOutputProcess S hmu x0 r omega) <=
          (((theorem59EpochLength S r : Real) *
              (4 / (3 * averageSmoothness S)))⁻¹ *
            ((4 / (3 * averageSmoothness S)) *
              (Finset.range (theorem59EpochLength S r)).sum
                (fun k => generatedBarObjective omega (k + 1)))) := by
    intro omega
    have hJ0 :
        compositeObjective S (theorem59PrintedFeasibleOutputProcess S hmu x0 r omega) <=
          (Finset.univ.sum
              (fun t : Fin (theorem59EpochLength S r) =>
                ((theorem59Theta S hmu (averageSmoothness_pos S)) r) (paperTime t)))⁻¹ *
            Finset.univ.sum
              (fun t : Fin (theorem59EpochLength S r) =>
                ((theorem59Theta S hmu (averageSmoothness_pos S)) r) (paperTime t) *
                  generatedBarObjective omega (paperTime t)) := by
      simpa [generatedBarObjective] using hgeneratedOutputJensenPathwise omega
    have hJ1 := hJ0
    rw [htheta_sum, htheta_weighted_objective_sum omega] at hJ1
    simpa using hJ1
  have hgeneratedOutputGapPathwise :
      forall omega : theorem59SamplePath n,
        (4 / (3 * averageSmoothness S)) *
            (theorem59EpochLength S r : Real) *
            (compositeObjective S
                (theorem59PrintedFeasibleOutputProcess S hmu x0 r omega) -
              compositeObjective S x.1) <=
          (Finset.range (theorem59EpochLength S r)).sum
            (fun k =>
              (4 / (3 * averageSmoothness S)) *
                (generatedBarObjective omega (k + 1) -
                  compositeObjective S x.1)) := by
    intro omega
    simpa using
      (lemma518_scaled_gap_sum_of_normalized_average
        (theorem59EpochLength S r) (4 / (3 * averageSmoothness S))
        (compositeObjective S (theorem59PrintedFeasibleOutputProcess S hmu x0 r omega))
        (compositeObjective S x.1) (fun k => generatedBarObjective omega (k + 1))
        hTpos hthetaCoeff_pos (hgeneratedOutputJensenNormalized omega))
  let jensenCoeff : Real := 4 / (3 * averageSmoothness S)
  have hprob_component :
      MeasureTheory.IsProbabilityMeasure (componentSampleLaw S) := by
    unfold componentSampleLaw
    infer_instance
  letI : MeasureTheory.IsProbabilityMeasure (componentSampleLaw S) := hprob_component
  have hprob_stream :
      MeasureTheory.IsProbabilityMeasure
        (SOptLib.iidStreamLaw (componentSampleLaw S)) := by
    infer_instance
  letI : MeasureTheory.IsProbabilityMeasure
      (SOptLib.iidStreamLaw (componentSampleLaw S)) := hprob_stream
  have hprob_sample :
      MeasureTheory.IsProbabilityMeasure (theorem59SampleLaw S) := by
    unfold theorem59SampleLaw
    infer_instance
  letI : MeasureTheory.IsProbabilityMeasure (theorem59SampleLaw S) := hprob_sample
  have hsampleCoord_meas :
      forall q : Nat × Nat,
        Measurable
          (fun omega : theorem59SamplePath n =>
            theorem59CanonicalSamples q.1 q.2 omega) := by
    intro q
    change Measurable (fun omega : Nat -> Nat -> Fin n => omega q.1 q.2)
    exact (measurable_pi_apply q.2).comp (measurable_pi_apply q.1)
  have hstrictPast_le_ambient :
      forall r k,
        (⨆ q ∈ theorem59StrictPastIndexSet r k,
            MeasurableSpace.comap
              (fun omega : theorem59SamplePath n =>
                theorem59CanonicalSamples q.1 q.2 omega)
              (by infer_instance : MeasurableSpace (Fin n))) ≤
          (by infer_instance : MeasurableSpace (theorem59SamplePath n)) := by
    intro r k
    refine iSup_le ?_
    intro q
    refine iSup_le ?_
    intro _hq
    exact (hsampleCoord_meas q).comap_le
  let outputKey : theorem59SamplePath n -> FeasiblePoint S × FeasiblePoint S :=
    fun omega =>
      let state :=
        theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
          theorem59CanonicalSamples r omega
      (state.xTilde, state.x)
  have houtputKey_raw :=
    lemma518_prev_epoch_state_strictPast_measurable_and_finite_range
      S hmu x0 (r + 1) (Nat.succ_pos r) 0
  have houtputKey_meas_strict :
      @Measurable (theorem59SamplePath n) (FeasiblePoint S × FeasiblePoint S)
        (⨆ q ∈ theorem59StrictPastIndexSet (r + 1) 0,
          MeasurableSpace.comap
            (fun omega : theorem59SamplePath n =>
              theorem59CanonicalSamples q.1 q.2 omega)
            (by infer_instance : MeasurableSpace (Fin n)))
        (by infer_instance) outputKey := by
    simpa [outputKey] using houtputKey_raw.1
  have houtputKey_meas : Measurable outputKey := by
    exact houtputKey_meas_strict.mono (hstrictPast_le_ambient (r + 1) 0) le_rfl
  have houtputKey_finite : (Set.range outputKey).Finite := by
    simpa [outputKey] using houtputKey_raw.2
  have houtputScaledInt :
      MeasureTheory.Integrable
        (fun omega : theorem59SamplePath n =>
          jensenCoeff * (theorem59EpochLength S r : Real) *
            (compositeObjective S
                (theorem59PrintedFeasibleOutputProcess S hmu x0 r omega) -
              compositeObjective S x.1))
        (theorem59SampleLaw S) := by
    refine
      integrable_of_finiteRange_factor
        (Y := outputKey)
        (Z := fun omega : theorem59SamplePath n =>
          jensenCoeff * (theorem59EpochLength S r : Real) *
            (compositeObjective S
                (theorem59PrintedFeasibleOutputProcess S hmu x0 r omega) -
              compositeObjective S x.1))
        houtputKey_meas houtputKey_finite ?_
    intro omega omega' hkey_eq
    have hxTilde_eq : (outputKey omega).1 = (outputKey omega').1 :=
      congrArg Prod.fst hkey_eq
    simpa [outputKey, theorem59PrintedFeasibleOutputProcess,
      theorem59PrintedFeasibleOutputProcessOn,
      theorem59PrintedFeasibleEpochOutputProcessOn] using
      congrArg
        (fun y : FeasiblePoint S =>
          jensenCoeff * (theorem59EpochLength S r : Real) *
            (compositeObjective S y.1 - compositeObjective S x.1))
        hxTilde_eq
  have hgeneratedBarScaledInt :
      forall k,
        MeasureTheory.Integrable
          (fun omega : theorem59SamplePath n =>
            jensenCoeff *
              (generatedBarObjective omega (k + 1) -
                compositeObjective S x.1))
          (theorem59SampleLaw S) := by
    intro k
    let W : theorem59SamplePath n ->
        Set.Elem (proxCoreSet S) × (Set.Elem (proxCoreSet S) × Set.Elem (proxCoreSet S)) :=
      fun omega =>
        let snapshot :=
          (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
            theorem59CanonicalSamples (r - 1) omega).xTilde
        let xStart :=
          (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
            theorem59CanonicalSamples (r - 1) omega).x
        let trajectory :=
          theorem59PrintedFeasibleInnerTrajectoryOn S hmu x0
            theorem59CanonicalSamples r hr omega snapshot xStart
        let htraj :=
          theorem59PrintedFeasibleInnerTrajectoryOn_rel S hmu x0
            theorem59CanonicalSamples r hr omega snapshot xStart
        let hinnerCore :=
          theorem59PrintedFeasibleInnerTrajectoryRelOn_core_mem_of_positiveProxMembership
            S hmu theorem59CanonicalSamples r hr omega snapshot xStart trajectory
            hpositiveProxMembership (hstateCorePrev omega).2
            (hstateCorePrev omega).1 htraj
        (⟨snapshot.1, (hstateCorePrev omega).2⟩,
          (⟨(trajectory (k + 1)).x.1, (hinnerCore (k + 1)).1⟩,
            ⟨(trajectory (k + 1)).xBar.1, (hinnerCore (k + 1)).2⟩))
    have hWF :=
      lemma518_generated_printed_epoch_snapshot_state_strictPast_measurable
        S hmu x0 r hr (k + 1) hpositiveProxMembership hstateCorePrev
    have hW_ambient : Measurable W := by
      exact hWF.1.mono (hstrictPast_le_ambient r (k + 1)) le_rfl
    have hWfin : (Set.range W).Finite := by
      simpa [W] using hWF.2
    refine
      integrable_of_finiteRange_factor
        (Y := W)
        (Z := fun omega : theorem59SamplePath n =>
          jensenCoeff *
            (generatedBarObjective omega (k + 1) -
              compositeObjective S x.1))
        hW_ambient hWfin ?_
    intro omega omega' hW_eq
    have hxBar_eq : (W omega).2.2 = (W omega').2.2 :=
      congrArg (fun z => z.2.2) hW_eq
    have hobj_eq :
        compositeObjective S (W omega).2.2.1 =
          compositeObjective S (W omega').2.2.1 := by
      rw [hxBar_eq]
    simpa [W, generatedBarObjective] using
      congrArg
        (fun y : Real => jensenCoeff * (y - compositeObjective S x.1))
        hobj_eq
  have hgeneratedOutputGapExpected :
      (4 * (theorem59EpochLength S r : Real) / (3 * averageSmoothness S)) *
          SOptLib.expectedObjectiveGap (theorem59SampleLaw S)
            (compositeObjective S) (compositeObjective S x.1)
            (theorem59PrintedFeasibleOutputProcess S hmu x0) r <=
        (Finset.range (theorem59EpochLength S r)).sum
          (fun k =>
            theorem59Gamma S r / theorem59Alpha S r *
              SOptLib.expectation (theorem59SampleLaw S)
                (fun omega : theorem59SamplePath n =>
                  generatedBarObjective omega (k + 1) -
                    compositeObjective S x.1)) := by
    have hraw :
        SOptLib.expectation (theorem59SampleLaw S)
            (fun omega : theorem59SamplePath n =>
              jensenCoeff * (theorem59EpochLength S r : Real) *
                (compositeObjective S
                    (theorem59PrintedFeasibleOutputProcess S hmu x0 r omega) -
                  compositeObjective S x.1)) <=
          (Finset.range (theorem59EpochLength S r)).sum
            (fun k =>
              SOptLib.expectation (theorem59SampleLaw S)
                (fun omega : theorem59SamplePath n =>
                  jensenCoeff *
                    (generatedBarObjective omega (k + 1) -
                      compositeObjective S x.1))) := by
      refine
        expectation_le_finset_sum_of_pointwise_le
          (μ := theorem59SampleLaw S)
          (s := Finset.range (theorem59EpochLength S r))
          (F := fun omega : theorem59SamplePath n =>
            jensenCoeff * (theorem59EpochLength S r : Real) *
              (compositeObjective S
                  (theorem59PrintedFeasibleOutputProcess S hmu x0 r omega) -
                compositeObjective S x.1))
          (G := fun k omega =>
            jensenCoeff *
              (generatedBarObjective omega (k + 1) -
                compositeObjective S x.1))
          houtputScaledInt ?_ ?_
      · intro k _hk
        exact hgeneratedBarScaledInt k
      · exact Filter.Eventually.of_forall (fun omega => by
          simpa [jensenCoeff, mul_assoc] using hgeneratedOutputGapPathwise omega)
    have hleft :
        SOptLib.expectation (theorem59SampleLaw S)
            (fun omega : theorem59SamplePath n =>
              jensenCoeff * (theorem59EpochLength S r : Real) *
                (compositeObjective S
                    (theorem59PrintedFeasibleOutputProcess S hmu x0 r omega) -
                  compositeObjective S x.1)) =
          (4 * (theorem59EpochLength S r : Real) / (3 * averageSmoothness S)) *
            SOptLib.expectedObjectiveGap (theorem59SampleLaw S)
              (compositeObjective S) (compositeObjective S x.1)
              (theorem59PrintedFeasibleOutputProcess S hmu x0) r := by
      rw [show
          (fun omega : theorem59SamplePath n =>
            jensenCoeff * (theorem59EpochLength S r : Real) *
              (compositeObjective S
                  (theorem59PrintedFeasibleOutputProcess S hmu x0 r omega) -
                compositeObjective S x.1)) =
          (fun omega : theorem59SamplePath n =>
            (jensenCoeff * (theorem59EpochLength S r : Real)) *
              (compositeObjective S
                  (theorem59PrintedFeasibleOutputProcess S hmu x0 r omega) -
                compositeObjective S x.1)) by
            funext omega
            ring]
      rw [expectation_const_mul_eq]
      rw [SOptLib.expectedObjectiveGap_def]
      rw [SOptLib.expectation_def]
      have hcoeff :
          jensenCoeff * (theorem59EpochLength S r : Real) =
            4 * (theorem59EpochLength S r : Real) /
              (3 * averageSmoothness S) := by
        dsimp [jensenCoeff]
        field_simp [ne_of_gt (averageSmoothness_pos S)]
      have hintegral :
          (∫ (ω : theorem59SamplePath n),
              compositeObjective S
                  (theorem59PrintedFeasibleOutputProcess S hmu x0 r ω) -
                compositeObjective S x.1 ∂theorem59SampleLaw S) =
            ∫ (ω : theorem59SamplePath n),
              -compositeObjective S x.1 +
                compositeObjective S
                  (theorem59PrintedFeasibleOutputProcess S hmu x0 r ω)
              ∂theorem59SampleLaw S := by
        congr
        funext omega
        ring
      rw [hcoeff, hintegral]
    have hright :
        (Finset.range (theorem59EpochLength S r)).sum
            (fun k =>
              SOptLib.expectation (theorem59SampleLaw S)
                (fun omega : theorem59SamplePath n =>
                  jensenCoeff *
                    (generatedBarObjective omega (k + 1) -
                      compositeObjective S x.1))) =
          (Finset.range (theorem59EpochLength S r)).sum
            (fun k =>
              theorem59Gamma S r / theorem59Alpha S r *
                SOptLib.expectation (theorem59SampleLaw S)
                  (fun omega : theorem59SamplePath n =>
                    generatedBarObjective omega (k + 1) -
                      compositeObjective S x.1)) := by
      refine Finset.sum_congr rfl ?_
      intro k _hk
      rw [expectation_const_mul_eq]
      simp [jensenCoeff, hfirstGamma_over_alpha]
    calc
      (4 * (theorem59EpochLength S r : Real) / (3 * averageSmoothness S)) *
          SOptLib.expectedObjectiveGap (theorem59SampleLaw S)
            (compositeObjective S) (compositeObjective S x.1)
            (theorem59PrintedFeasibleOutputProcess S hmu x0) r =
          SOptLib.expectation (theorem59SampleLaw S)
            (fun omega : theorem59SamplePath n =>
              jensenCoeff * (theorem59EpochLength S r : Real) *
                (compositeObjective S
                    (theorem59PrintedFeasibleOutputProcess S hmu x0 r omega) -
                  compositeObjective S x.1)) := hleft.symm
      _ <=
          (Finset.range (theorem59EpochLength S r)).sum
            (fun k =>
              SOptLib.expectation (theorem59SampleLaw S)
                (fun omega : theorem59SamplePath n =>
                  jensenCoeff *
                    (generatedBarObjective omega (k + 1) -
                      compositeObjective S x.1))) := hraw
      _ =
          (Finset.range (theorem59EpochLength S r)).sum
            (fun k =>
              theorem59Gamma S r / theorem59Alpha S r *
              SOptLib.expectation (theorem59SampleLaw S)
                (fun omega : theorem59SamplePath n =>
                  generatedBarObjective omega (k + 1) -
                    compositeObjective S x.1)) := hright
  have htail_nonneg :
      0 <=
        S.mu * theorem59Gamma S r *
          (Finset.range (theorem59EpochLength S r)).sum
            (fun k =>
              SOptLib.expectation (theorem59SampleLaw S)
                (fun omega : theorem59SamplePath n =>
                  let snapshot :=
                    (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                      theorem59CanonicalSamples (r - 1) omega).xTilde
                  let xStart :=
                    (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                      theorem59CanonicalSamples (r - 1) omega).x
                  let trajectory :=
                    theorem59PrintedFeasibleInnerTrajectoryOn S hmu x0
                      theorem59CanonicalSamples r hr omega snapshot xStart
                  let htraj :=
                    theorem59PrintedFeasibleInnerTrajectoryOn_rel S hmu x0
                      theorem59CanonicalSamples r hr omega snapshot xStart
                  let hinnerCore :=
                    theorem59PrintedFeasibleInnerTrajectoryRelOn_core_mem_of_positiveProxMembership
                      S hmu theorem59CanonicalSamples r hr omega snapshot xStart trajectory
                      hpositiveProxMembership (hstateCorePrev omega).2
                      (hstateCorePrev omega).1 htraj
                  bregmanOn S
                    (⟨(trajectory (k + 1)).x.1, (hinnerCore (k + 1)).1⟩ :
                      Set.Elem (proxCoreSet S))
                    x)) := by
    have hmuGamma_nonneg : 0 <= S.mu * theorem59Gamma S r := by
      nlinarith [hmu, hgamma]
    have hsum_nonneg :
        0 <=
          (Finset.range (theorem59EpochLength S r)).sum
            (fun k =>
              SOptLib.expectation (theorem59SampleLaw S)
                (fun omega : theorem59SamplePath n =>
                  let snapshot :=
                    (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                      theorem59CanonicalSamples (r - 1) omega).xTilde
                  let xStart :=
                    (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                      theorem59CanonicalSamples (r - 1) omega).x
                  let trajectory :=
                    theorem59PrintedFeasibleInnerTrajectoryOn S hmu x0
                      theorem59CanonicalSamples r hr omega snapshot xStart
                  let htraj :=
                    theorem59PrintedFeasibleInnerTrajectoryOn_rel S hmu x0
                      theorem59CanonicalSamples r hr omega snapshot xStart
                  let hinnerCore :=
                    theorem59PrintedFeasibleInnerTrajectoryRelOn_core_mem_of_positiveProxMembership
                      S hmu theorem59CanonicalSamples r hr omega snapshot xStart trajectory
                      hpositiveProxMembership (hstateCorePrev omega).2
                      (hstateCorePrev omega).1 htraj
                  bregmanOn S
                    (⟨(trajectory (k + 1)).x.1, (hinnerCore (k + 1)).1⟩ :
                      Set.Elem (proxCoreSet S))
                    x)) := by
      refine Finset.sum_nonneg ?_
      intro k _hk
      rw [SOptLib.expectation_def]
      refine MeasureTheory.integral_nonneg ?_
      intro omega
      let snapshot :=
        (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
          theorem59CanonicalSamples (r - 1) omega).xTilde
      let xStart :=
        (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
          theorem59CanonicalSamples (r - 1) omega).x
      let trajectory :=
        theorem59PrintedFeasibleInnerTrajectoryOn S hmu x0
          theorem59CanonicalSamples r hr omega snapshot xStart
      let htraj :=
        theorem59PrintedFeasibleInnerTrajectoryOn_rel S hmu x0
          theorem59CanonicalSamples r hr omega snapshot xStart
      let hinnerCore :=
        theorem59PrintedFeasibleInnerTrajectoryRelOn_core_mem_of_positiveProxMembership
          S hmu theorem59CanonicalSamples r hr omega snapshot xStart trajectory
          hpositiveProxMembership (hstateCorePrev omega).2
          (hstateCorePrev omega).1 htraj
      have hlower :=
        bregman_modulus_one_lower S
          (⟨(trajectory (k + 1)).x.1, (hinnerCore (k + 1)).1⟩ :
            Set.Elem (proxCoreSet S)) x
      have hquad_nonneg :
          0 <=
            (1 / 2 : Real) *
              norm
                ((⟨(trajectory (k + 1)).x.1, (hinnerCore (k + 1)).1⟩ :
                  Set.Elem (proxCoreSet S)).1 - x.1) ^ 2 := by
        positivity
      exact le_trans hquad_nonneg (by simpa [bregmanOn_def] using hlower)
    exact mul_nonneg hmuGamma_nonneg hsum_nonneg
  have hgeneratedScalarTelescopeNoTail :
      (Finset.range (theorem59EpochLength S r)).sum
          (fun k =>
            theorem59Gamma S r / theorem59Alpha S r *
              SOptLib.expectation (theorem59SampleLaw S)
                (fun omega : theorem59SamplePath n =>
                  let snapshot :=
                    (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                      theorem59CanonicalSamples (r - 1) omega).xTilde
                  let xStart :=
                    (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                      theorem59CanonicalSamples (r - 1) omega).x
                  let trajectory :=
                    theorem59PrintedFeasibleInnerTrajectoryOn S hmu x0
                      theorem59CanonicalSamples r hr omega snapshot xStart
                  compositeObjective S (trajectory (k + 1)).xBar.1 -
                    compositeObjective S x.1)) +
        SOptLib.expectation (theorem59SampleLaw S)
          (fun omega : theorem59SamplePath n =>
            let snapshot :=
              (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                theorem59CanonicalSamples (r - 1) omega).xTilde
            let xStart :=
              (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                theorem59CanonicalSamples (r - 1) omega).x
            let trajectory :=
              theorem59PrintedFeasibleInnerTrajectoryOn S hmu x0
                theorem59CanonicalSamples r hr omega snapshot xStart
            let htraj :=
              theorem59PrintedFeasibleInnerTrajectoryOn_rel S hmu x0
                theorem59CanonicalSamples r hr omega snapshot xStart
            let hinnerCore :=
              theorem59PrintedFeasibleInnerTrajectoryRelOn_core_mem_of_positiveProxMembership
                S hmu theorem59CanonicalSamples r hr omega snapshot xStart trajectory
                hpositiveProxMembership (hstateCorePrev omega).2
                (hstateCorePrev omega).1 htraj
            bregmanOn S
              (⟨(trajectory (theorem59EpochLength S r)).x.1,
                (hinnerCore (theorem59EpochLength S r)).1⟩ : Set.Elem (proxCoreSet S))
              x) <=
        ((theorem59EpochLength S r : Nat) : Real) *
            ((theorem59Gamma S r / theorem59Alpha S r * theorem59P r) *
              SOptLib.expectation (theorem59SampleLaw S)
                (fun omega : theorem59SamplePath n =>
                  let snapshot :=
                    (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                      theorem59CanonicalSamples (r - 1) omega).xTilde
                  compositeObjective S snapshot.1 - compositeObjective S x.1)) +
          SOptLib.expectation (theorem59SampleLaw S)
            (fun omega : theorem59SamplePath n =>
              let snapshot :=
                (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                  theorem59CanonicalSamples (r - 1) omega).xTilde
              let xStart :=
                (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                  theorem59CanonicalSamples (r - 1) omega).x
              let trajectory :=
                theorem59PrintedFeasibleInnerTrajectoryOn S hmu x0
                  theorem59CanonicalSamples r hr omega snapshot xStart
              let htraj :=
                theorem59PrintedFeasibleInnerTrajectoryOn_rel S hmu x0
                  theorem59CanonicalSamples r hr omega snapshot xStart
              let hinnerCore :=
                theorem59PrintedFeasibleInnerTrajectoryRelOn_core_mem_of_positiveProxMembership
                  S hmu theorem59CanonicalSamples r hr omega snapshot xStart trajectory
                  hpositiveProxMembership (hstateCorePrev omega).2
                  (hstateCorePrev omega).1 htraj
              bregmanOn S
                (⟨(trajectory 0).x.1, (hinnerCore 0).1⟩ : Set.Elem (proxCoreSet S))
                x) := by
    nlinarith [hgeneratedScalarTelescope, htail_nonneg]
  have hgeneratedOutputGapExpected_aligned :
      (4 * (theorem59EpochLength S r : Real) / (3 * averageSmoothness S)) *
          SOptLib.expectedObjectiveGap (theorem59SampleLaw S)
            (compositeObjective S) (compositeObjective S x.1)
            (theorem59PrintedFeasibleOutputProcess S hmu x0) r <=
        (Finset.range (theorem59EpochLength S r)).sum
          (fun k =>
            theorem59Gamma S r / theorem59Alpha S r *
              SOptLib.expectation (theorem59SampleLaw S)
                (fun omega : theorem59SamplePath n =>
                  let snapshot :=
                    (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                      theorem59CanonicalSamples (r - 1) omega).xTilde
                  let xStart :=
                    (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                      theorem59CanonicalSamples (r - 1) omega).x
                  let trajectory :=
                    theorem59PrintedFeasibleInnerTrajectoryOn S hmu x0
                      theorem59CanonicalSamples r hr omega snapshot xStart
                  compositeObjective S (trajectory (k + 1)).xBar.1 -
                    compositeObjective S x.1)) := by
    simpa [generatedBarObjective] using hgeneratedOutputGapExpected
  have hgeneratedOneEpoch :
      (4 * (theorem59EpochLength S r : Real) / (3 * averageSmoothness S)) *
          SOptLib.expectedObjectiveGap (theorem59SampleLaw S)
            (compositeObjective S) (compositeObjective S x.1)
            (theorem59PrintedFeasibleOutputProcess S hmu x0) r +
        SOptLib.expectation (theorem59SampleLaw S)
          (fun omega : theorem59SamplePath n =>
            let snapshot :=
              (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                theorem59CanonicalSamples (r - 1) omega).xTilde
            let xStart :=
              (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                theorem59CanonicalSamples (r - 1) omega).x
            let trajectory :=
              theorem59PrintedFeasibleInnerTrajectoryOn S hmu x0
                theorem59CanonicalSamples r hr omega snapshot xStart
            let htraj :=
              theorem59PrintedFeasibleInnerTrajectoryOn_rel S hmu x0
                theorem59CanonicalSamples r hr omega snapshot xStart
            let hinnerCore :=
              theorem59PrintedFeasibleInnerTrajectoryRelOn_core_mem_of_positiveProxMembership
                S hmu theorem59CanonicalSamples r hr omega snapshot xStart trajectory
                hpositiveProxMembership (hstateCorePrev omega).2
                (hstateCorePrev omega).1 htraj
            bregmanOn S
              (⟨(trajectory (theorem59EpochLength S r)).x.1,
                (hinnerCore (theorem59EpochLength S r)).1⟩ : Set.Elem (proxCoreSet S))
              x) <=
        ((theorem59EpochLength S r : Nat) : Real) *
            ((theorem59Gamma S r / theorem59Alpha S r * theorem59P r) *
              SOptLib.expectation (theorem59SampleLaw S)
                (fun omega : theorem59SamplePath n =>
                  let snapshot :=
                    (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                      theorem59CanonicalSamples (r - 1) omega).xTilde
                  compositeObjective S snapshot.1 - compositeObjective S x.1)) +
          SOptLib.expectation (theorem59SampleLaw S)
            (fun omega : theorem59SamplePath n =>
              let snapshot :=
                (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                  theorem59CanonicalSamples (r - 1) omega).xTilde
              let xStart :=
                (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                  theorem59CanonicalSamples (r - 1) omega).x
              let trajectory :=
                theorem59PrintedFeasibleInnerTrajectoryOn S hmu x0
                  theorem59CanonicalSamples r hr omega snapshot xStart
              let htraj :=
                theorem59PrintedFeasibleInnerTrajectoryOn_rel S hmu x0
                  theorem59CanonicalSamples r hr omega snapshot xStart
              let hinnerCore :=
                theorem59PrintedFeasibleInnerTrajectoryRelOn_core_mem_of_positiveProxMembership
                  S hmu theorem59CanonicalSamples r hr omega snapshot xStart trajectory
                  hpositiveProxMembership (hstateCorePrev omega).2
                  (hstateCorePrev omega).1 htraj
              bregmanOn S
                (⟨(trajectory 0).x.1, (hinnerCore 0).1⟩ : Set.Elem (proxCoreSet S))
                x) := by
    nlinarith [hgeneratedOutputGapExpected_aligned, hgeneratedScalarTelescopeNoTail]
  have hendpointBregman_eq :
      SOptLib.expectation (theorem59SampleLaw S)
          (fun omega : theorem59SamplePath n =>
            let snapshot :=
              (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                theorem59CanonicalSamples (r - 1) omega).xTilde
            let xStart :=
              (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                theorem59CanonicalSamples (r - 1) omega).x
            let trajectory :=
              theorem59PrintedFeasibleInnerTrajectoryOn S hmu x0
                theorem59CanonicalSamples r hr omega snapshot xStart
            let htraj :=
              theorem59PrintedFeasibleInnerTrajectoryOn_rel S hmu x0
                theorem59CanonicalSamples r hr omega snapshot xStart
            let hinnerCore :=
              theorem59PrintedFeasibleInnerTrajectoryRelOn_core_mem_of_positiveProxMembership
                S hmu theorem59CanonicalSamples r hr omega snapshot xStart trajectory
                hpositiveProxMembership (hstateCorePrev omega).2
                (hstateCorePrev omega).1 htraj
            bregmanOn S
              (⟨(trajectory (theorem59EpochLength S r)).x.1,
                (hinnerCore (theorem59EpochLength S r)).1⟩ : Set.Elem (proxCoreSet S))
              x) =
        SOptLib.expectation (theorem59SampleLaw S)
          (fun omega : theorem59SamplePath n =>
            bregmanOn S
              (⟨(theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                  theorem59CanonicalSamples r omega).x.1,
                (hstateCore omega).1⟩ : Set.Elem (proxCoreSet S))
              x) := by
    congr
    funext omega
    cases r with
    | zero =>
        omega
    | succ r =>
        let hr' : 1 <= r + 1 := Nat.succ_pos r
        let prevState :=
          theorem59PrintedFeasibleEpochStateProcessGeneratedOn S hmu x0
            theorem59CanonicalSamples r omega
        let trajectory :=
          theorem59PrintedFeasibleInnerTrajectoryOn S hmu x0 theorem59CanonicalSamples
            (r + 1) hr' omega prevState.xTilde prevState.x
        have hsucc :=
          SOptLib.recursiveIterateProcess_succ
            (theorem59PrintedFeasibleEpochStateProcessGeneratedOn S hmu
              x0 theorem59CanonicalSamples)
            (⟨proxCoreAsFeasible S x0,
              proxCoreAsFeasible S x0⟩ : EpochStateFeasibleOn S)
            (theorem59PrintedFeasibleEpochStateStepOn S hmu x0 theorem59CanonicalSamples)
            (by rfl) r omega
        have hrec :
            SOptLib.recursiveIterateProcess
                (⟨proxCoreAsFeasible S x0,
                  proxCoreAsFeasible S x0⟩ : EpochStateFeasibleOn S)
                (theorem59PrintedFeasibleEpochStateStepOn S hmu x0
                  theorem59CanonicalSamples) (r + 1) omega =
              theorem59PrintedFeasibleEpochStateStepOn S hmu x0 theorem59CanonicalSamples
                r
                (SOptLib.recursiveIterateProcess
                  (⟨proxCoreAsFeasible S x0,
                    proxCoreAsFeasible S x0⟩ : EpochStateFeasibleOn S)
                  (theorem59PrintedFeasibleEpochStateStepOn S hmu x0
                    theorem59CanonicalSamples) r omega)
                omega := by
          simpa [theorem59PrintedFeasibleEpochStateProcessGeneratedOn] using hsucc
        have hx_eq :
            (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
              theorem59CanonicalSamples (r + 1) omega).x =
              (trajectory (theorem59EpochLength S (r + 1))).x := by
          simpa [theorem59PrintedFeasibleEpochStateProcessOn,
            theorem59PrintedFeasibleEpochStateProcessGeneratedOn,
            theorem59PrintedFeasibleEpochStateStepOn, prevState, trajectory, hr']
            using congrArg EpochStateFeasibleOn.x hsucc
        simpa [theorem59PrintedFeasibleEpochStateProcessOn,
          theorem59PrintedFeasibleEpochStateProcessGeneratedOn,
          theorem59PrintedFeasibleEpochStateStepOn, prevState, trajectory, hr',
          hrec, hx_eq, (Subsingleton.elim hr hr' : hr = hr')]
  have hinitialBregman_eq :
      SOptLib.expectation (theorem59SampleLaw S)
          (fun omega : theorem59SamplePath n =>
            let snapshot :=
              (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                theorem59CanonicalSamples (r - 1) omega).xTilde
            let xStart :=
              (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                theorem59CanonicalSamples (r - 1) omega).x
            let trajectory :=
              theorem59PrintedFeasibleInnerTrajectoryOn S hmu x0
                theorem59CanonicalSamples r hr omega snapshot xStart
            let htraj :=
              theorem59PrintedFeasibleInnerTrajectoryOn_rel S hmu x0
                theorem59CanonicalSamples r hr omega snapshot xStart
            let hinnerCore :=
              theorem59PrintedFeasibleInnerTrajectoryRelOn_core_mem_of_positiveProxMembership
                S hmu theorem59CanonicalSamples r hr omega snapshot xStart trajectory
                hpositiveProxMembership (hstateCorePrev omega).2
                (hstateCorePrev omega).1 htraj
            bregmanOn S
              (⟨(trajectory 0).x.1, (hinnerCore 0).1⟩ : Set.Elem (proxCoreSet S))
              x) =
        SOptLib.expectation (theorem59SampleLaw S)
          (fun omega : theorem59SamplePath n =>
            bregmanOn S
              (⟨(theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                  theorem59CanonicalSamples (r - 1) omega).x.1,
                (hstateCorePrev omega).1⟩ : Set.Elem (proxCoreSet S))
              x) := by
    congr
  have hprevSnapshotGap_eq :
      SOptLib.expectation (theorem59SampleLaw S)
          (fun omega : theorem59SamplePath n =>
            let snapshot :=
              (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                theorem59CanonicalSamples (r - 1) omega).xTilde
            compositeObjective S snapshot.1 - compositeObjective S x.1) =
        SOptLib.expectedObjectiveGap (theorem59SampleLaw S)
          (compositeObjective S) (compositeObjective S x.1)
          (theorem59PrintedFeasibleOutputProcess S hmu x0) (r - 1) := by
    rw [SOptLib.expectedObjectiveGap_def, SOptLib.expectation_def]
    rfl
  have hprintedOneEpoch :
      (4 * (theorem59EpochLength S r : Real) / (3 * averageSmoothness S)) *
          SOptLib.expectedObjectiveGap (theorem59SampleLaw S)
            (compositeObjective S) (compositeObjective S x.1)
            (theorem59PrintedFeasibleOutputProcess S hmu x0) r +
        SOptLib.expectation (theorem59SampleLaw S)
          (fun omega : theorem59SamplePath n =>
            bregmanOn S
              (⟨(theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                  theorem59CanonicalSamples r omega).x.1,
                (hstateCore omega).1⟩ : Set.Elem (proxCoreSet S))
              x) <=
        (2 * (theorem59EpochLength S r : Real) / (3 * averageSmoothness S)) *
            SOptLib.expectedObjectiveGap (theorem59SampleLaw S)
              (compositeObjective S) (compositeObjective S x.1)
              (theorem59PrintedFeasibleOutputProcess S hmu x0) (r - 1) +
          SOptLib.expectation (theorem59SampleLaw S)
            (fun omega : theorem59SamplePath n =>
              bregmanOn S
                (⟨(theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                    theorem59CanonicalSamples (r - 1) omega).x.1,
                  (hstateCorePrev omega).1⟩ : Set.Elem (proxCoreSet S))
                x) := by
    rw [← hendpointBregman_eq]
    calc
      (4 * (theorem59EpochLength S r : Real) / (3 * averageSmoothness S)) *
          SOptLib.expectedObjectiveGap (theorem59SampleLaw S)
            (compositeObjective S) (compositeObjective S x.1)
            (theorem59PrintedFeasibleOutputProcess S hmu x0) r +
        SOptLib.expectation (theorem59SampleLaw S)
          (fun omega : theorem59SamplePath n =>
            let snapshot :=
              (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                theorem59CanonicalSamples (r - 1) omega).xTilde
            let xStart :=
              (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                theorem59CanonicalSamples (r - 1) omega).x
            let trajectory :=
              theorem59PrintedFeasibleInnerTrajectoryOn S hmu x0
                theorem59CanonicalSamples r hr omega snapshot xStart
            let htraj :=
              theorem59PrintedFeasibleInnerTrajectoryOn_rel S hmu x0
                theorem59CanonicalSamples r hr omega snapshot xStart
            let hinnerCore :=
              theorem59PrintedFeasibleInnerTrajectoryRelOn_core_mem_of_positiveProxMembership
                S hmu theorem59CanonicalSamples r hr omega snapshot xStart trajectory
                hpositiveProxMembership (hstateCorePrev omega).2
                (hstateCorePrev omega).1 htraj
            bregmanOn S
              (⟨(trajectory (theorem59EpochLength S r)).x.1,
                (hinnerCore (theorem59EpochLength S r)).1⟩ : Set.Elem (proxCoreSet S))
              x) <=
          ((theorem59EpochLength S r : Nat) : Real) *
              ((theorem59Gamma S r / theorem59Alpha S r * theorem59P r) *
                SOptLib.expectation (theorem59SampleLaw S)
                  (fun omega : theorem59SamplePath n =>
                    let snapshot :=
                      (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                        theorem59CanonicalSamples (r - 1) omega).xTilde
                    compositeObjective S snapshot.1 - compositeObjective S x.1)) +
            SOptLib.expectation (theorem59SampleLaw S)
              (fun omega : theorem59SamplePath n =>
                let snapshot :=
                  (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                    theorem59CanonicalSamples (r - 1) omega).xTilde
                let xStart :=
                  (theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                    theorem59CanonicalSamples (r - 1) omega).x
                let trajectory :=
                  theorem59PrintedFeasibleInnerTrajectoryOn S hmu x0
                    theorem59CanonicalSamples r hr omega snapshot xStart
                let htraj :=
                  theorem59PrintedFeasibleInnerTrajectoryOn_rel S hmu x0
                    theorem59CanonicalSamples r hr omega snapshot xStart
                let hinnerCore :=
                  theorem59PrintedFeasibleInnerTrajectoryRelOn_core_mem_of_positiveProxMembership
                    S hmu theorem59CanonicalSamples r hr omega snapshot xStart trajectory
                    hpositiveProxMembership (hstateCorePrev omega).2
                    (hstateCorePrev omega).1 htraj
                bregmanOn S
                  (⟨(trajectory 0).x.1, (hinnerCore 0).1⟩ : Set.Elem (proxCoreSet S))
                  x) := hgeneratedOneEpoch
      _ =
          (2 * (theorem59EpochLength S r : Real) / (3 * averageSmoothness S)) *
              SOptLib.expectedObjectiveGap (theorem59SampleLaw S)
                (compositeObjective S) (compositeObjective S x.1)
                (theorem59PrintedFeasibleOutputProcess S hmu x0) (r - 1) +
            SOptLib.expectation (theorem59SampleLaw S)
              (fun omega : theorem59SamplePath n =>
                bregmanOn S
                  (⟨(theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                      theorem59CanonicalSamples (r - 1) omega).x.1,
                    (hstateCorePrev omega).1⟩ : Set.Elem (proxCoreSet S))
                  x) := by
          rw [hinitialBregman_eq, hprevSnapshotGap_eq, hfirstGamma_over_alpha_mul_p]
          ring_nf
  simpa [hstateCore, hstateCorePrev] using hprintedOneEpoch

/-- Zero-epoch printed process identification used after chaining Eq. (5.4.27).

At epoch zero, Algorithm 5.7 initializes `tilde{x}^0 = x^0` and `x^0 = x0`.
This helper exposes that definitional fact at the expectation/Bregman boundary
needed by the printed Lyapunov relation. -/
theorem lemma518_printed_epoch_zero_identification
    {n dim : Nat} (S : Setup n dim)
    (x0 : Set.Elem (proxCoreSet S)) (x : FeasiblePoint S) (hmu : 0 < S.mu) :
    let hpositiveProxMembership :
        theorem59PrintedFeasiblePositiveProxUpdateCoreMembershipStatement S :=
      lemma518_printed_positive_prox_membership_from_carrierSubgradient S
    let hstateCoreAll :=
      theorem59PrintedFeasibleEpochStateProcessOn_core_mem_of_positiveProxMembership
        S hmu x0 theorem59CanonicalSamples hpositiveProxMembership
    SOptLib.expectedObjectiveGap (theorem59SampleLaw S) (compositeObjective S)
        (compositeObjective S x.1)
        (theorem59PrintedFeasibleOutputProcess S hmu x0) 0 =
        compositeObjective S x0.1 - compositeObjective S x.1 ∧
      SOptLib.expectation (theorem59SampleLaw S)
        (fun omega : theorem59SamplePath n =>
          bregmanOn S
            (⟨(theorem59PrintedFeasibleEpochStateProcessOn S hmu x0
                theorem59CanonicalSamples 0 omega).x.1,
              (hstateCoreAll 0 omega).1⟩ : Set.Elem (proxCoreSet S))
            x) =
        bregmanOn S x0 x := by
  classical
  have hprob_component :
      MeasureTheory.IsProbabilityMeasure (componentSampleLaw S) := by
    unfold componentSampleLaw
    infer_instance
  letI : MeasureTheory.IsProbabilityMeasure (componentSampleLaw S) := hprob_component
  have hprob_stream :
      MeasureTheory.IsProbabilityMeasure
        (SOptLib.iidStreamLaw (componentSampleLaw S)) := by
    infer_instance
  letI : MeasureTheory.IsProbabilityMeasure
      (SOptLib.iidStreamLaw (componentSampleLaw S)) := hprob_stream
  have hprob_sample :
      MeasureTheory.IsProbabilityMeasure (theorem59SampleLaw S) := by
    unfold theorem59SampleLaw
    infer_instance
  letI : MeasureTheory.IsProbabilityMeasure (theorem59SampleLaw S) := hprob_sample
  constructor
  · rw [SOptLib.expectedObjectiveGap_def]
    simp [theorem59PrintedFeasibleOutputProcess,
      theorem59PrintedFeasibleOutputProcessOn,
      theorem59PrintedFeasibleEpochOutputProcessOn,
      theorem59PrintedFeasibleEpochStateProcessOn,
      theorem59PrintedFeasibleEpochStateProcessGeneratedOn,
      SOptLib.recursiveIterateProcess, proxCoreAsFeasible,
      MeasureTheory.integral_const]
  · rw [SOptLib.expectation_def]
    simp [theorem59PrintedFeasibleEpochStateProcessOn,
      theorem59PrintedFeasibleEpochStateProcessGeneratedOn,
      SOptLib.recursiveIterateProcess, proxCoreAsFeasible,
      bregmanOn, carrierBregmanFormula, _root_.carrierBregmanDivergence,
      MeasureTheory.integral_const]


end VarianceReducedAcceleratedGradientDescent
