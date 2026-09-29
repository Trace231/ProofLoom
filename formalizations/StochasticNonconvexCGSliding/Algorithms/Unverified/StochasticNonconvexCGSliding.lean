import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Topology.Compactness.Compact
import SOptLib.Model.BlockSampling
import SOptLib.Model.Bregman
import SOptLib.Model.Complexity
import SOptLib.Model.ConditionalGradient
import SOptLib.Model.Diameter
import SOptLib.Model.Iterates
import SOptLib.Model.Objective
import SOptLib.Model.Prox
import SOptLib.Model.Selection
import SOptLib.Model.StochasticOracle
import SOptLib.Glue.Algebra
import SOptLib.Glue.Probability
import SOptLib.Layer0.ConditionalGradient
import SOptLib.Layer0.ConvexFOC
import SOptLib.Layer0.Objective
import SOptLib.Layer0.Oracle
import SOptLib.Layer1.Descent
import SOptLib.Layer1.Telescope

/-!
Object-layer reconstruction for Lan's stochastic nonconvex conditional-gradient
sliding finite-sum method.

The file intentionally defines the paper's algorithmic objects before proof work:
the finite-sum objective, smoothness-proportional sampling weights, recursive
gradient estimator, CndG outer update, generated iterate process, exact projected
point, projected-gradient certificate, and randomized output masses.
-/

open scoped BigOperators
open scoped InnerProductSpace
open MeasureTheory
open ProbabilityTheory

namespace Algorithms.Unverified.StochasticNonconvexCGSliding

noncomputable section

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Source-facing data for the finite-sum nonconvex conditional-gradient sliding
problem.

The fields are exactly the paper's setup, assumptions, and parameter choices:
closed compact feasible set, finite smooth component functions, initial
point, schedules, `q_i = L_i/(mL)`, `b = 10T`, `gamma = 1/L`, and the CndG
tolerance `eta >= 0`.  Quantities such as `f`, `G_k`, `x_{k+1}`, projected
points, and output probabilities are definitions below, not witness fields. -/
structure Setup where
  /-- Feasible region `X` in Eq. (7.4.1). -/
  X : Set E
  /-- Initial point `x_1`. -/
  x₁ : E
  /-- Number `m` of finite-sum components. -/
  componentCount : ℕ
  /-- Component objectives `f_i`. -/
  componentObjective : Fin componentCount → E → ℝ
  /-- Component gradients `nabla f_i`. -/
  componentGradient : Fin componentCount → E → E
  /-- Component smoothness constants `L_i`. -/
  componentL : Fin componentCount → ℝ
  /-- Average smoothness constant `L = (1/m) sum_i L_i`. -/
  L : ℝ
  /-- Outer iteration horizon `N`. -/
  N : ℕ
  /-- Epoch length `T`. -/
  T : ℕ
  /-- Mini-batch size `b`. -/
  b : ℕ
  /-- Stepsize/output weights `alpha_k`. -/
  alpha : ℕ → ℝ
  /-- CndG inverse-curvature parameter `gamma`. -/
  gamma : ℝ
  /-- Distance-generating prox function `nu` whose Bregman distance is `V`. -/
  proxFunction : E → ℝ
  /-- Selected gradient of the prox function, used to realize `V(x,u)`. -/
  proxGradient : E → E
  /-- Lipschitz constant `L_nu` for the distance-generating function gradient. -/
  proxGradientL : ℝ
  /-- CndG accuracy `eta`. -/
  eta : ℝ
  /-- `X` is closed, as stated after Eq. (7.4.1). -/
  hX_closed : IsClosed X
  /-- `X` is compact, as stated after Eq. (7.4.1). -/
  hX_compact : IsCompact X
  /-- `X` is convex for the CndG procedure of Algorithm 7.6. -/
  hX_convex : Convex ℝ X
  /-- The initial point is feasible. -/
  hx₁_mem : x₁ ∈ X
  /-- There is at least one component in the finite sum. -/
  hcomponentCount_pos : 0 < componentCount
  /-- Component smoothness constants are positive. -/
  hcomponentL_pos : ∀ i : Fin componentCount, 0 < componentL i
  /-- The named `componentGradient` is the gradient of `componentObjective`. -/
  hcomponent_hasGradientAt :
    ∀ i : Fin componentCount, ∀ x : E, x ∈ X →
      HasGradientAt (componentObjective i) (componentGradient i x) x
  /-- Component gradients are Lipschitz with constants `L_i`. -/
  hcomponent_smooth :
    ∀ i : Fin componentCount, ∀ x y : E, x ∈ X → y ∈ X →
      ‖componentGradient i x - componentGradient i y‖ ≤ componentL i * ‖x - y‖
  /-- The prox function is a modulus-1 distance-generating function on `X`, as
  assumed after Eq. (7.5.2). -/
  hprox_dgf : IsDistanceGeneratingFunctionOn X proxFunction proxGradient
  /-- The gradient of `nu` is `L_nu`-Lipschitz on `X`, as assumed after
  Eq. (7.5.2). -/
  hproxGradient_lipschitz :
    ∀ x y : E, x ∈ X → y ∈ X →
      ‖proxGradient x - proxGradient y‖ ≤ proxGradientL * ‖x - y‖
  /-- Average smoothness identity `L = (1/m) sum_i L_i`, Eq. (6.5.2). -/
  hL_eq_average :
    L = (componentCount : ℝ)⁻¹ *
      Finset.sum Finset.univ (fun i : Fin componentCount => componentL i)
  /-- The output window is nonempty. -/
  hN_pos : 0 < N
  /-- The epoch length is nonempty. -/
  hT_pos : 0 < T
  /-- The recursive mini-batch is nonempty. -/
  hb_pos : 0 < b
  /-- The CndG tolerance satisfies `eta >= 0`, as stated after Eq. (7.5.7). -/
  heta_nonneg : 0 ≤ eta
  /-- The Theorem 7.18 batch choice `b = 10T`, Eq. (7.5.8). -/
  hb_eq_ten_mul_T : b = 10 * T
  /-- The Theorem 7.18 stepsize choice `gamma = 1/L`, Eq. (7.5.8). -/
  hgamma_eq_inv_L : gamma = L⁻¹

variable {E}



/-- SOptLib finite-average calculus identifies the finite-average gradient as the gradient of
the paper finite-sum objective on feasible points. -/
theorem finiteUniformAverage_hasGradientAt (S : Setup E) {x : E} (hx : x ∈ S.X) :
    HasGradientAt (SOptLib.finiteUniformAverage S.componentObjective) (SOptLib.finiteUniformAverage S.componentGradient x) x := by
  show HasGradientAt (fun z : E => SOptLib.finiteUniformAverage S.componentObjective z) (SOptLib.finiteUniformAverage S.componentGradient x) x
  simpa [SOptLib.finiteUniformAverage, SOptLib.finiteUniformAverage] using
    SOptLib.finiteAverageObjective_hasGradientAt
      S.componentObjective S.componentGradient x
      (fun i => S.hcomponent_hasGradientAt i x hx)

/-- The finite-average gradient is `L`-Lipschitz on the feasible set.

This aligns the component smoothness assumptions and Eq. (6.5.2)'s average
smoothness identity with the `hgrad_lipschitz` premise of
`smooth_quadratic_upper_bound_of_hasGradientAt_lipschitzOn_convex`. Candidates
considered: SOptLib supplies the final smooth quadratic upper-bound theorem and
finite-average gradient calculus, but no existing declaration specialized the
componentwise Lipschitz constants plus `L = m^{-1} sum L_i` into this
paper-local finite-average-gradient Lipschitz statement. -/
private theorem finiteAverageGradient_lipschitz_on_X (S : Setup E) {x y : E}
    (hx : x ∈ S.X) (hy : y ∈ S.X) :
    ‖SOptLib.finiteUniformAverage S.componentGradient x - SOptLib.finiteUniformAverage S.componentGradient y‖ ≤ S.L * ‖x - y‖ := by
  simpa [SOptLib.finiteUniformAverage] using
    (SOptLib.finiteAverageGradient_lipschitzOn_of_component_lipschitz
      S.X S.componentGradient S.componentL S.L
      (by
        simpa using S.hL_eq_average)
      S.hcomponent_smooth hx hy)

/-- Smooth quadratic upper model for the paper finite-sum objective.

This is Lan Theorem 7.18 proof step 3 in local object form, obtained by
specializing SOptLib's smooth quadratic upper-bound theorem with
`finiteUniformAverage_hasGradientAt` and `finiteAverageGradient_lipschitz_on_X`. -/
private theorem finiteUniformAverage_smooth_quadratic_upper_bound (S : Setup E)
    {x y : E} (hx : x ∈ S.X) (hy : y ∈ S.X) :
    SOptLib.finiteUniformAverage S.componentObjective y ≤
      SOptLib.finiteUniformAverage S.componentObjective x + ⟪SOptLib.finiteUniformAverage S.componentGradient x, y - x⟫_ℝ +
        (S.L / 2) * ‖y - x‖ ^ 2 := by
  simpa [SOptLib.finiteUniformAverage, SOptLib.finiteUniformAverage] using
    SOptLib.finiteUniformAverage_smooth_quadratic_upper_bound_of_component_lipschitz
      S.X S.componentObjective S.componentGradient S.componentL S.L
      S.hX_convex (by simpa using S.hL_eq_average)
      S.hcomponent_hasGradientAt S.hcomponent_smooth
      hx hy

/-- Existence of a minimizer for Eq. (7.4.1).

This is derived from the source-backed compact feasible set and smooth finite
sum; it is not a primitive `fStar` field. -/
theorem exists_finiteUniformAverage_minimizer (S : Setup E) :
    ∃ x : E, x ∈ S.X ∧ ∀ y : E, y ∈ S.X →
      SOptLib.finiteUniformAverage S.componentObjective x ≤ SOptLib.finiteUniformAverage S.componentObjective y := by
  exact
    SOptLib.finiteAverageObjective_minimum_exists_of_isCompact_continuousOn
      S.X S.componentObjective S.hX_compact ⟨S.x₁, S.hx₁_mem⟩
      (fun i => HasGradientAt.continuousOn (fun x hx => S.hcomponent_hasGradientAt i x hx))

/-- Canonical selected minimizer for `f^* := min_{x in X} f(x)`, Eq. (7.4.1).

Candidates considered: `SOptLib.Model.Objective` has compact optimizer helpers,
but their signatures require an explicit continuity premise.  The paper-local
finite-sum smoothness should derive continuity, so this selector is built from
the source-facing minimizer existence theorem and leaves that derivation as a
proof obligation. -/
def finiteSumMinimizer (S : Setup E) : E :=
  Classical.choose (exists_finiteUniformAverage_minimizer S)

/-- The selected minimizer is feasible and minimizes the finite-sum objective. -/
theorem finiteSumMinimizer_spec (S : Setup E) :
    finiteSumMinimizer S ∈ S.X ∧ ∀ y : E, y ∈ S.X →
      SOptLib.finiteUniformAverage S.componentObjective (finiteSumMinimizer S) ≤ SOptLib.finiteUniformAverage S.componentObjective y := by
  exact Classical.choose_spec (exists_finiteUniformAverage_minimizer S)

/-- Canonical optimal value `f^*` from Eq. (7.4.1). -/
def fStar (S : Setup E) : ℝ :=
  SOptLib.finiteUniformAverage S.componentObjective (finiteSumMinimizer S)

/-- The average smoothness constant is positive, derived from the positive
component constants and Eq. (6.5.2), not stored as a separate setup axiom. -/
theorem averageSmoothness_pos (S : Setup E) : 0 < S.L := by
  have hnonempty : (Finset.univ : Finset (Fin S.componentCount)).Nonempty := by
    refine ⟨⟨0, S.hcomponentCount_pos⟩, ?_⟩
    simp
  have hsum_pos :
      0 < Finset.sum Finset.univ (fun i : Fin S.componentCount => S.componentL i) := by
    exact Finset.sum_pos (fun i _ => S.hcomponentL_pos i) hnonempty
  have hcount_pos : 0 < (S.componentCount : ℝ) :=
    Nat.cast_pos.mpr S.hcomponentCount_pos
  rw [S.hL_eq_average]
  exact mul_pos (inv_pos.mpr hcount_pos) hsum_pos

/-- Smoothness-proportional sampling mass `q_i = L_i/(mL)`, Eq. (7.4.3).

SOptLib has importance-weight and PMF utilities, but the paper object here is
the literal scalar probability appearing in Eq. (7.4.3); this local definition
keeps that expression visible and SOptLib-agnostic at the source boundary. -/
def componentSamplingProbability (S : Setup E) (i : Fin S.componentCount) : ℝ :=
  S.componentL i / ((S.componentCount : ℝ) * S.L)

/-- The sampling masses from Eq. (7.4.3) form a probability vector.

The proof is a source-derived arithmetic obligation from positivity of the
component constants and Eq. (6.5.2), not an additional setup field. -/
theorem componentSamplingProbability_sum_one (S : Setup E) :
    Finset.sum Finset.univ (componentSamplingProbability S) = 1 := by
  simpa [componentSamplingProbability, SOptLib.smoothnessImportanceWeight] using
    (SOptLib.smoothnessImportanceWeight_sum_one_of_average
      (Lcomp := fun i : Fin S.componentCount => S.componentL i)
      (n := (S.componentCount : ℝ)) (L := S.L)
      (ne_of_gt (Nat.cast_pos.mpr S.hcomponentCount_pos))
      S.hL_eq_average
      (ne_of_gt (Finset.sum_pos (fun i _ => S.hcomponentL_pos i)
        ⟨⟨0, S.hcomponentCount_pos⟩, by simp⟩)))

/-- The smoothness-proportional masses are nonnegative.

This is a source-derived arithmetic obligation from `L_i > 0` and
`L = (1/m) sum_i L_i`, not a primitive probability-field assumption. -/
theorem componentSamplingProbability_nonneg (S : Setup E) :
    ∀ i : Fin S.componentCount, 0 ≤ componentSamplingProbability S i := by
  intro i
  unfold componentSamplingProbability
  have hcount_pos : 0 < (S.componentCount : ℝ) :=
    Nat.cast_pos.mpr S.hcomponentCount_pos
  have hL_pos : 0 < S.L := averageSmoothness_pos S
  have hden_pos : 0 < (S.componentCount : ℝ) * S.L :=
    mul_pos hcount_pos hL_pos
  exact div_nonneg (le_of_lt (S.hcomponentL_pos i)) (le_of_lt hden_pos)

/-- Canonical component-index PMF `Q = {q_1, ..., q_m}` from Algorithm 7.12.

This uses `SOptLib.PMF.ofFintypeOfReal`, whose signature exactly constructs a
finite PMF from nonnegative real masses summing to one; the masses themselves are
the literal Eq. (7.4.3) probabilities. -/
def componentSamplingPMF (S : Setup E) : PMF (Fin S.componentCount) :=
  SOptLib.smoothnessImportancePMF
    (Lcomp := fun i : Fin S.componentCount => S.componentL i)
    (n := (S.componentCount : ℝ)) (L := S.L)
    (fun i => le_of_lt (S.hcomponentL_pos i))
    (Nat.cast_pos.mpr S.hcomponentCount_pos)
    S.hL_eq_average
    (ne_of_gt (Finset.sum_pos (fun i _ => S.hcomponentL_pos i)
      ⟨⟨0, S.hcomponentCount_pos⟩, by simp⟩))

/-- Sample paths for Algorithm 7.12's i.i.d. mini-batches across all outer
iterations and all positions in the mini-batch. -/
abbrev AlgorithmSamplePath (S : Setup E) :=
  SOptLib.miniBatchSamplePath S.b (Fin S.componentCount)

/-- The coordinate mini-batch stream read from a canonical Algorithm 7.12 sample
path. -/
def algorithmBatchStream (S : Setup E) (k : ℕ) (r : Fin S.b)
    (ω : AlgorithmSamplePath S) : Fin S.componentCount :=
  ω k r

/-- Source-facing law specification for Algorithm 7.12 mini-batches: the
coordinates are independent and each has the finite law `Q` from Eq. (7.4.3).

This is the paper's "Generate i.i.d. samples ... according to Q" object.  The
law is kept as a canonical theorem-selected measure below so Theorem 7.18 is not
stated over arbitrary sample measures or arbitrary batch streams. -/
def algorithmSampleLawSpec (S : Setup E) (P : Measure (AlgorithmSamplePath S)) : Prop :=
  SOptLib.miniBatchIidLawSpec S.b (componentSamplingPMF S).toMeasure P

/-- Existence of the canonical product law for Algorithm 7.12 sample paths.

This is a construction obligation for the product of the displayed finite PMF
over countably many mini-batch coordinates, not an assumption in the theorem
head. -/
theorem exists_algorithmSampleLaw (S : Setup E) :
    ∃ P : Measure (AlgorithmSamplePath S), algorithmSampleLawSpec S P := by
  classical
  let μ : Measure (Fin S.componentCount) := (componentSamplingPMF S).toMeasure
  let P : Measure (AlgorithmSamplePath S) :=
    Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : Fin S.b => μ))
  refine ⟨P, ?_⟩
  unfold algorithmSampleLawSpec
  refine ⟨?_, ?_, ?_⟩
  · dsimp [P]
    infer_instance
  · dsimp [P, μ]
    -- Algorithm 7.12's iid mini-batch samples are the uncurry of this nested product law.
    simpa [AlgorithmSamplePath] using
      (ProbabilityTheory.iIndepFun_uncurry_infinitePi'
        (μ := fun _ : ℕ => fun _ : Fin S.b => (componentSamplingPMF S).toMeasure)
        (X := fun (_ : ℕ) (_ : Fin S.b) (a : Fin S.componentCount) => a)
        (by intro k r; exact measurable_id))
  · intro k r
    dsimp [P, μ]
    change Measure.map
        ((fun batch : Fin S.b → Fin S.componentCount => batch r) ∘
          (fun ω : AlgorithmSamplePath S => ω k))
        (Measure.infinitePi fun _ : ℕ =>
          Measure.infinitePi fun _ : Fin S.b => (componentSamplingPMF S).toMeasure) =
      (componentSamplingPMF S).toMeasure
    rw [← MeasureTheory.Measure.map_map]
    · have houter :
          Measure.map (fun ω : AlgorithmSamplePath S => ω k)
              (Measure.infinitePi fun _ : ℕ =>
                Measure.infinitePi fun _ : Fin S.b => (componentSamplingPMF S).toMeasure) =
            Measure.infinitePi (fun _ : Fin S.b => (componentSamplingPMF S).toMeasure) := by
        simpa [AlgorithmSamplePath] using
          (MeasureTheory.Measure.infinitePi_map_eval
            (μ := fun _ : ℕ =>
              Measure.infinitePi fun _ : Fin S.b => (componentSamplingPMF S).toMeasure) k)
      rw [houter]
      simpa using
        (MeasureTheory.Measure.infinitePi_map_eval
          (μ := fun _ : Fin S.b => (componentSamplingPMF S).toMeasure) r)
    · exact measurable_pi_apply r
    · fun_prop

/-- Canonical Algorithm 7.12 sample law generated from the source PMF `Q`. -/
def algorithmSampleLaw (S : Setup E) : Measure (AlgorithmSamplePath S) :=
  SOptLib.iidMiniBatchSampleLaw S.b (componentSamplingPMF S).toMeasure

/-- The canonical Algorithm 7.12 sample law has the source i.i.d. coordinate
law. -/
theorem algorithmSampleLaw_spec (S : Setup E) :
    algorithmSampleLawSpec S (algorithmSampleLaw S) := by
  simpa [algorithmSampleLawSpec, algorithmSampleLaw, AlgorithmSamplePath] using
    (SOptLib.iidMiniBatchSampleLaw_spec S.b (componentSamplingPMF S).toMeasure)

/-- Prox/Bregman distance `V(x,u)` generated by the paper's distance-generating
function `nu`.

This imports `carrierBregmanFormula`, the canonical Bregman formula
primitive; unlike the previous raw-distance field, `V` is now a definition from
`nu` and its selected gradient, matching Eq. (7.5.2)'s prox-function boundary. -/
def proxDistance (S : Setup E) (x u : E) : ℝ :=
  carrierBregmanFormula S.proxFunction id S.proxGradient x u

/-- The sampled single-component correction
`(nabla f_i(x) - nabla f_i(y))/(q_i m)` from Algorithm 7.12.

This is the paper-local specialization of SOptLib's inverse-probability
weighted component gradient-difference atom. -/
def sampledGradientCorrection (S : Setup E) (x y : E) (i : Fin S.componentCount) : E :=
  SOptLib.importance_weighted_gradient_difference
    (componentSamplingProbability S) (S.componentCount : ℝ) S.componentGradient x y i

/-- Mini-batch average of the sampled recursive correction in Algorithm 7.12. -/
def miniBatchCorrection (S : Setup E) (x y : E)
    (batch : Fin S.b → Fin S.componentCount) : E :=
  (S.b : ℝ)⁻¹ •
    Finset.sum Finset.univ (fun r : Fin S.b => sampledGradientCorrection S x y (batch r))

/-- Recursive estimator branch
`G_k = b^{-1} sum_{i in I_b} (...) + G_{k-1}` from Algorithm 7.12. -/
def recursiveMiniBatchGradient (S : Setup E) (x xPrev GPrev : E)
    (batch : Fin S.b → Fin S.componentCount) : E :=
  miniBatchCorrection S x xPrev batch + GPrev

/-- The paper's estimator update: full-gradient refresh at the first one-based
step of each epoch, and the recursive mini-batch estimator otherwise.

Algorithm 7.12 prints this as `k % T == 1`.  In the paper's epoch notation,
indices are decoded as `k = sT + t` with `t = 1, ..., T`; Lean's raw natural
modulo would make the printed test false at every epoch start when `T = 1`.
The canonical object-model predicate is therefore the one-based decoder
`SOptLib.stepOfIndex T k = 1`, equivalently `(k - 1) % T + 1 = 1`.

This replaces any theorem-local `G_k` hypothesis by a canonical definition
from Algorithm 7.12. -/
def gradientEstimatorUpdate (S : Setup E) (k : ℕ) (xPrev x GPrev : E)
    (batch : Fin S.b → Fin S.componentCount) : E :=
  if SOptLib.stepOfIndex S.T k = 1 then
    SOptLib.finiteUniformAverage S.componentGradient x
  else
    recursiveMiniBatchGradient S x xPrev GPrev batch

/-- The quadratic model `phi_k(u) = <G_k,u> + (1/(2 gamma)) ||u-x_k||^2`,
Eq. (7.5.6).

Candidates considered: `SOptLib.proxStep` and `SOptLib.paperMirrorObjective`
model a general Bregman/prox objective, but Eq. (7.5.6) is the literal Euclidean
quadratic conditional-gradient subproblem, so the local definition records the
paper expression directly. -/
def cndGModelValue (G x : E) (gamma : ℝ) (u : E) : ℝ :=
  ⟪G, u⟫_ℝ + (2 * gamma)⁻¹ * ‖u - x‖ ^ 2

/-- Euclidean projected-point model used by Lan Theorem 7.18:
`<g,u> + (1/(2 gamma)) ||u-x||^2`.

No SOptLib match: searched `Euclidean projection argmin quadratic model compact
convex minimizer` and `projected gradient Euclidean prox point quadratic
argmin`; the reusable hits either describe the generic projected-gradient
mapping or the local CndG quadratic minimizer.  Theorem 7.18 proof steps 1 and
9 use this literal Euclidean quadratic projected point `xhat`, while Eq.
(7.5.1)--(7.5.2)'s Bregman projected point remains encoded separately below. -/
def euclideanProjectedPointModelValue (S : Setup E) (x g : E) (gamma : ℝ)
    (u : E) : ℝ :=
  let _ : Setup E := S
  SOptLib.euclideanQuadraticProxModel x g gamma u

/-- Exact argmin specification for the Euclidean projected point `xhat` in
Theorem 7.18's proof. -/
def euclideanProjectedPointSpec (S : Setup E) (x g : E) (gamma : ℝ)
    (u : E) : Prop :=
  u ∈ S.X ∧ ∀ v : E, v ∈ S.X →
    euclideanProjectedPointModelValue S x g gamma u ≤
      euclideanProjectedPointModelValue S x g gamma v

/-- Continuity of the Euclidean quadratic projected-point model on the feasible
set.

This is the only side condition needed to select Theorem 7.18's `xhat` from the
compact-minimum theorem. -/
private theorem euclideanProjectedPointModelValue_continuousOn
    (S : Setup E) (x g : E) (gamma : ℝ) :
    ContinuousOn (fun u => euclideanProjectedPointModelValue S x g gamma u) S.X := by
  intro u _hu
  have hlin : ContinuousWithinAt (fun z : E => ⟪g, z⟫_ℝ) S.X u :=
    (continuous_const.inner continuous_id).continuousWithinAt
  have hquad :
      ContinuousWithinAt (fun z : E => gamma⁻¹ / 2 * ‖z - x‖ ^ 2) S.X u :=
    (((continuous_id.sub continuous_const).norm.pow 2).const_mul
      (gamma⁻¹ / 2)).continuousWithinAt
  simpa [euclideanProjectedPointModelValue] using hlin.add hquad

/-- Existence of the Euclidean projected point used in Theorem 7.18.

This is a compactness/continuity consequence of the stated feasible-set setup,
not a new setup assumption. -/
theorem exists_euclideanProjectedPoint (S : Setup E) (x g : E) (gamma : ℝ) :
    ∃ u : E, euclideanProjectedPointSpec S x g gamma u := by
  simpa [euclideanProjectedPointSpec, euclideanProjectedPointModelValue] using
    (SOptLib.euclideanQuadraticProxPoint_exists_of_isCompact
      S.hX_compact (⟨S.x₁, S.hx₁_mem⟩ : S.X.Nonempty) x g gamma)

/-- Canonical Euclidean projected point `xhat` from Theorem 7.18's proof. -/
def euclideanProjectedPoint (S : Setup E) (x g : E) (gamma : ℝ) : E :=
  SOptLib.euclideanQuadraticProxPoint
    S.hX_compact (⟨S.x₁, S.hx₁_mem⟩ : S.X.Nonempty) x g gamma

/-- The selected Euclidean projected point satisfies its argmin specification. -/
theorem euclideanProjectedPoint_spec (S : Setup E) (x g : E) (gamma : ℝ) :
    euclideanProjectedPointSpec S x g gamma
      (euclideanProjectedPoint S x g gamma) := by
  simpa [euclideanProjectedPointSpec, euclideanProjectedPointModelValue,
    euclideanProjectedPoint] using
      (SOptLib.euclideanQuadraticProxPoint_isEuclideanQuadraticProxModelMinimizerOn
        S.hX_compact (⟨S.x₁, S.hx₁_mem⟩ : S.X.Nonempty) x g gamma)

/-- The Theorem 7.18 projected-gradient certificate
`g_X,k = gamma^{-1}(x_k - xhat_{k+1})`.

This is deliberately separate from `exactProjectedGradient`, which encodes the
general Bregman projected point from Eq. (7.5.1)--(7.5.2). -/
def euclideanProjectedGradient (S : Setup E) (x : E) : E :=
  SOptLib.projectedGradient (fun y : E => y)
    (fun x g gamma => euclideanProjectedPoint S x g gamma)
    x (SOptLib.finiteUniformAverage S.componentGradient x) S.gamma

/-- The Euclidean projected-gradient mapping unfolds to the scaled displacement
from the Euclidean projected point. -/
theorem euclideanProjectedGradient_eq (S : Setup E) (x : E) :
    euclideanProjectedGradient S x =
      S.gamma⁻¹ • (x - euclideanProjectedPoint S x (SOptLib.finiteUniformAverage S.componentGradient x) S.gamma) := by
  rfl

/-- Projected-point model
`<g,u> + gamma^{-1} V(x,u)` from Eq. (7.5.2).

Candidates considered: `SOptLib.proxStep` selects an argmin of
`SOptLib.paperMirrorObjective`, but using it directly here would require
continuity/compactness side conditions at the source boundary.  The paper object
is therefore recorded literally, with solvability left as a theorem obligation. -/
def projectedPointModelValue (S : Setup E) (x g : E) (gamma : ℝ) (u : E) : ℝ :=
  ⟪g, u⟫_ℝ + gamma⁻¹ * proxDistance S x u

/-- Exact argmin specification for the generalized projected point over `X`,
Eq. (7.5.2). -/
def projectedPointSpec (S : Setup E) (x g : E) (gamma : ℝ) (u : E) : Prop :=
  u ∈ S.X ∧ ∀ v : E, v ∈ S.X →
    projectedPointModelValue S x g gamma u ≤ projectedPointModelValue S x g gamma v

/-- Existence of the exact projected point used in Eq. (7.5.2) and the proof of
Theorem 7.18.

This is a source-derived compactness/continuity obligation; it is deliberately a
theorem with proof debt rather than a setup field or theorem-head hypothesis. -/
theorem exists_projectedPoint (S : Setup E) (x g : E) (gamma : ℝ) :
    ∃ u : E, projectedPointSpec S x g gamma u := by
  have hXne : S.X.Nonempty := ⟨S.x₁, S.hx₁_mem⟩
  have hcont : ContinuousOn (projectedPointModelValue S x g gamma) S.X := by
    intro u hu
    have hnu_u : ContinuousWithinAt S.proxFunction S.X u :=
      (S.hprox_dgf.2.1 u hu).continuousAt.continuousWithinAt
    have hlin_g : ContinuousWithinAt (fun z : E => ⟪g, z⟫_ℝ) S.X u :=
      (continuous_const.inner continuous_id).continuousWithinAt
    have hlin_prox :
        ContinuousWithinAt (fun z : E => ⟪S.proxGradient x, z - x⟫_ℝ) S.X u :=
      (continuous_const.inner (continuous_id.sub continuous_const)).continuousWithinAt
    unfold projectedPointModelValue proxDistance carrierBregmanFormula
    exact hlin_g.add (((hnu_u.sub continuousWithinAt_const).sub hlin_prox).const_mul (gamma⁻¹))
  rcases SOptLib.objectiveMinimum_exists_of_isCompact_continuousOn
      (projectedPointModelValue S x g gamma) S.hX_compact hXne hcont with ⟨u, humin⟩
  refine ⟨u.1, ?_⟩
  constructor
  · exact u.2
  · intro v hv
    exact humin ⟨v, hv⟩

/-- Canonical exact projected point over `X` for the Bregman/prox model.

SOptLib's `proxStep` is a reusable Bregman argmin selector.  The paper's
Eq. (7.5.2) uses the literal `gamma^{-1} V(x,u)` projected-point model; this
definition chooses that exact model while later proofs may bridge to SOptLib. -/
def projectedPoint (S : Setup E) (x g : E) (gamma : ℝ) : E :=
  Classical.choose (exists_projectedPoint S x g gamma)

/-- The selected projected point satisfies its argmin specification. -/
theorem projectedPoint_spec (S : Setup E) (x g : E) (gamma : ℝ) :
    projectedPointSpec S x g gamma (projectedPoint S x g gamma) := by
  exact Classical.choose_spec (exists_projectedPoint S x g gamma)

/-- Exact generalized projected gradient
`g_X(x) = gamma^{-1}(x - x^+)`, Eq. (7.5.1).

This specializes `SOptLib.projectedGradient` to the paper's exact projected
point selector, aligning the file with the reusable projected-gradient mapping. -/
def exactProjectedGradient (S : Setup E) (x : E) : E :=
  SOptLib.projectedGradient id
    (fun x g gamma => projectedPoint S x g gamma) x (SOptLib.finiteUniformAverage S.componentGradient x) S.gamma

/-- The exact projected-gradient mapping unfolds to the scaled displacement. -/
theorem exactProjectedGradient_eq (S : Setup E) (x : E) :
    exactProjectedGradient S x =
      S.gamma⁻¹ • (x - projectedPoint S x (SOptLib.finiteUniformAverage S.componentGradient x) S.gamma) := by
  rfl

/-- Approximate CndG returned-point specification from Eq. (7.5.7). -/
def cndGUpdateSpec (S : Setup E) (G x : E) (gamma eta : ℝ) (y : E) : Prop :=
  SOptLib.IsApproxConditionalGradientUpdate S.X G x gamma eta y

/-- The feasible linear-oracle point `v_t` in Algorithm 7.6, Step 2.

This reuses `SOptLib.compactLinearModelMaximizer`, the compact feasible-set
shifted-linear maximizer.  It matches Eq. (7.2.4), which maximizes
`<g + beta (u_t-u), u_t-x>` over `x in X`; the previous choose-only CndG output
skipped this procedure-level object. -/
def cndGLinearOraclePoint (S : Setup E) (base direction : E) : E :=
  SOptLib.compactLinearModelMaximizer S.hX_compact ⟨S.x₁, S.hx₁_mem⟩ base direction

/-- The CndG gap `V_{g,u,beta}(u_t)` from Eq. (7.2.4). -/
def cndGGapValue (S : Setup E) (G u : E) (beta : ℝ) (ut : E) : ℝ :=
  let direction := G + beta • (ut - u)
  ⟪direction, ut - cndGLinearOraclePoint S ut direction⟫_ℝ

/-- The CndG line-search scalar `alpha_t` from Eq. (7.2.5), in its printed
closed form.

Candidates considered: `SOptLib.ConditionalGradient.segment_linear_quadratic_stepsize`
selects an argmin for the equivalent Eq. (7.2.6) segment problem, but the paper's
Algorithm 7.6 step uses the displayed quotient/min formula; this local definition
records that literal step while later proofs may bridge it to the SOptLib argmin
selector. -/
def cndGLineSearch (S : Setup E) (G u : E) (beta : ℝ) (ut : E) : ℝ :=
  let direction := G + beta • (ut - u)
  let vt := cndGLinearOraclePoint S ut direction
  SOptLib.ConditionalGradient.closed_form_segment_quadratic_line_search G u beta ut vt


/-- The generated inner CndG iterate sequence `u_t` from Algorithm 7.6.

The zero index represents the paper's `u_1 = u`.  A state whose gap already
passes Step 3 is held fixed, so selecting the first passing one-based index gives
the procedure output. -/
def cndGInnerIterate (S : Setup E) (G u : E) (beta eta : ℝ) : ℕ → E :=
  SOptLib.gap_stopped_iterate
    (gap := fun ut => cndGGapValue S G u beta ut)
    (move := fun ut =>
      let alpha := fun _ : ℕ => cndGLineSearch S G u beta ut
      let linearMinimizer := fun Gm => cndGLinearOraclePoint S ut (Gm + beta • (ut - u))
      SOptLib.conditionalGradientIterUpdate alpha linearMinimizer ut G 0)
    (eta := eta)
    (u0 := u)

private theorem cndGInnerIterate_succ (S : Setup E) (G u : E) (beta eta : ℝ)
    (n : ℕ) :
    cndGInnerIterate S G u beta eta (n + 1) =
      let ut := cndGInnerIterate S G u beta eta n
      if cndGGapValue S G u beta ut ≤ eta then
        ut
      else
        let alpha := fun _ : ℕ => cndGLineSearch S G u beta ut
        let linearMinimizer := fun Gm => cndGLinearOraclePoint S ut (Gm + beta • (ut - u))
        SOptLib.conditionalGradientIterUpdate alpha linearMinimizer ut G 0 := by
  simp [cndGInnerIterate]

/-- One-based view of the inner CndG iterates, matching Algorithm 7.6 notation. -/
def cndGInnerIterateOneBased (S : Setup E) (G u : E) (beta eta : ℝ) (t : ℕ) : E :=
  cndGInnerIterate S G u beta eta (t - 1)

/-- Raw non-stopping CndG move map used in Lan Theorem 7.9(c).

Search audit: `conditionalGradientIterUpdate` provides the repeated affine
conditional-gradient step used below. The running raw sequence is expressed at
call sites as Mathlib function iteration of this move map. -/
private def cndGRawInnerMove (S : Setup E) (G u : E) (beta : ℝ) (ut : E) : E :=
  let alpha := fun _ : ℕ => cndGLineSearch S G u beta ut
  let linearMinimizer := fun Gm => cndGLinearOraclePoint S ut (Gm + beta • (ut - u))
  SOptLib.conditionalGradientIterUpdate alpha linearMinimizer ut G 0


/-- One-based view of the raw non-stopping CndG iterates. -/
private def cndGRawInnerIterateOneBased (S : Setup E) (G u : E) (beta : ℝ)
    (t : ℕ) : E :=
  (fun n => (cndGRawInnerMove S G u beta)^[n] u) (t - 1)

/-- Termination proposition for the Algorithm 7.6 CndG stopping test in the
paper call `CndG(G, u, 1/gamma, eta)` from Eq. (7.5.5). -/
def paperCndGTerminates (S : Setup E) (G u : E) : Prop :=
    ∃ t : ℕ,
      (1 ≤ t ∧ cndGGapValue S G u S.gamma⁻¹
          (cndGInnerIterateOneBased S G u S.gamma⁻¹ S.eta t) ≤ S.eta) ∧
        (∀ s : ℕ, 1 ≤ s → s < t →
          ¬ (1 ≤ s ∧ cndGGapValue S G u S.gamma⁻¹
              (cndGInnerIterateOneBased S G u S.gamma⁻¹ S.eta s) ≤ S.eta))

/-- Feasibility invariant for the literal Algorithm 7.6 inner iterates.

Search audit: `compactLinearModelMaximizer_mem`, `compactLinearModelMaximizer_isMax`,
and `cndG_lineSearchQuotient_nonneg_of_current_mem` were considered; the first
two align with Algorithm 7.6 Step 2 and are used directly, while the quotient
lemma expects an `IsMaxOn` wrapper rather than this file's selected compact
maximizer. -/
private theorem cndG_inner_iterate_mem_of_start_mem (S : Setup E) (G u : E)
    (hu : u ∈ S.X) :
    ∀ n : ℕ, cndGInnerIterate S G u S.gamma⁻¹ S.eta n ∈ S.X := by
  let x := cndGInnerIterate S G u S.gamma⁻¹ S.eta
  let selected : ℕ → E := fun n =>
    let ut := x n
    let direction := G + S.gamma⁻¹ • (ut - u)
    cndGLinearOraclePoint S ut direction
  let alpha : ℕ → ℝ := fun n => cndGLineSearch S G u S.gamma⁻¹ (x n)
  change ∀ n : ℕ, x n ∈ S.X
  have hx0 : x 0 ∈ S.X := by
    simpa [x, cndGInnerIterate] using hu
  have hselected : ∀ n : ℕ, x n ∈ S.X → selected n ∈ S.X := by
    intro n hx
    let ut := x n
    let direction := G + S.gamma⁻¹ • (ut - u)
    exact
      SOptLib.compactLinearModelMaximizer_mem S.hX_compact
        ⟨S.x₁, S.hx₁_mem⟩ ut direction
  have halpha : ∀ n : ℕ, x n ∈ S.X → alpha n ∈ Set.Icc (0 : ℝ) 1 := by
    intro n hx
    let ut := x n
    let direction := G + S.gamma⁻¹ • (ut - u)
    let vt := cndGLinearOraclePoint S ut direction
    have hbeta_pos : 0 < S.gamma⁻¹ := by
      rw [S.hgamma_eq_inv_L]
      simpa using averageSmoothness_pos S
    have hmax0 :
        ⟪direction, ut - ut⟫_ℝ ≤ ⟪direction, ut - vt⟫_ℝ := by
      simpa [vt, direction, cndGLinearOraclePoint] using
        SOptLib.compactLinearModelMaximizer_isMax S.hX_compact
          ⟨S.x₁, S.hx₁_mem⟩ ut direction ut hx
    have hgap_nonneg : 0 ≤ ⟪direction, ut - vt⟫_ℝ := by
      simpa using hmax0
    have hnum_nonneg :
        0 ≤ ⟪S.gamma⁻¹ • (u - ut) - G, vt - ut⟫_ℝ := by
      simpa [direction, sub_eq_add_neg, inner_add_left, inner_add_right,
        inner_neg_left, inner_neg_right, inner_smul_left, inner_smul_right,
        add_comm, add_left_comm, add_assoc] using hgap_nonneg
    have hden_nonneg : 0 ≤ S.gamma⁻¹ * ‖vt - ut‖ ^ 2 := by
      exact mul_nonneg (le_of_lt hbeta_pos) (sq_nonneg ‖vt - ut‖)
    have hquot_nonneg :
        0 ≤ ⟪S.gamma⁻¹ • (u - ut) - G, vt - ut⟫_ℝ /
            (S.gamma⁻¹ * ‖vt - ut‖ ^ 2) := by
      exact div_nonneg hnum_nonneg hden_nonneg
    constructor
    · simpa [alpha, cndGLineSearch, direction, vt] using
        le_min zero_le_one hquot_nonneg
    · simp [alpha, cndGLineSearch]
  have hstep : ∀ n : ℕ,
      x (n + 1) = x n ∨
        x (n + 1) = (1 - alpha n) • x n + alpha n • selected n := by
    intro n
    by_cases hgap :
        cndGGapValue S G u S.gamma⁻¹
          (cndGInnerIterate S G u S.gamma⁻¹ S.eta n) ≤ S.eta
    · left
      simp [x, cndGInnerIterate_succ, hgap]
    · right
      simp [x, selected, alpha, cndGInnerIterate_succ, hgap,
        SOptLib.conditionalGradientIterUpdate]
  exact affine_iterate_mem_of_convex_update S.hX_convex x selected alpha hx0 hselected halpha hstep

/-- Feasibility invariant for the raw non-stopping CndG iterates.

Search audit: `compactLinearModelMaximizer_mem` and
`compactLinearModelMaximizer_isMax` align with Algorithm 7.6 Step 2 and are
used directly; the existing stopped feasibility helper cannot be reused because
the source telescope applies to the running sequence before termination. -/
private theorem cndG_raw_inner_iterate_mem_of_start_mem (S : Setup E) (G u : E)
    (hu : u ∈ S.X) :
    ∀ n : ℕ, (cndGRawInnerMove S G u S.gamma⁻¹)^[n] u ∈ S.X := by
  intro n
  exact
    Function.Iterate.rec
      (motive := fun x : E => x ∈ S.X)
      (a := u)
      hu
      (f := cndGRawInnerMove S G u S.gamma⁻¹)
      (app := fun ut ih => by
      let direction := G + S.gamma⁻¹ • (ut - u)
      let vt := cndGLinearOraclePoint S ut direction
      have hvt : vt ∈ S.X := by
        simpa [vt, direction, cndGLinearOraclePoint] using
          SOptLib.compactLinearModelMaximizer_mem S.hX_compact
            ⟨S.x₁, S.hx₁_mem⟩ ut direction
      have hbeta_pos : 0 < S.gamma⁻¹ := by
        rw [S.hgamma_eq_inv_L]
        simpa using averageSmoothness_pos S
      have hmax0 :
          ⟪direction, ut - ut⟫_ℝ ≤ ⟪direction, ut - vt⟫_ℝ := by
        simpa [vt, direction, cndGLinearOraclePoint] using
          SOptLib.compactLinearModelMaximizer_isMax S.hX_compact
            ⟨S.x₁, S.hx₁_mem⟩ ut direction ut ih
      have hgap_nonneg : 0 ≤ ⟪direction, ut - vt⟫_ℝ := by
        simpa using hmax0
      have hnum_nonneg :
          0 ≤ ⟪S.gamma⁻¹ • (u - ut) - G, vt - ut⟫_ℝ := by
        simpa [direction, sub_eq_add_neg, inner_add_left, inner_add_right,
          inner_neg_left, inner_neg_right, inner_smul_left, inner_smul_right,
          add_comm, add_left_comm, add_assoc] using hgap_nonneg
      have hden_nonneg : 0 ≤ S.gamma⁻¹ * ‖vt - ut‖ ^ 2 := by
        exact mul_nonneg (le_of_lt hbeta_pos) (sq_nonneg ‖vt - ut‖)
      have hquot_nonneg :
          0 ≤ ⟪S.gamma⁻¹ • (u - ut) - G, vt - ut⟫_ℝ /
              (S.gamma⁻¹ * ‖vt - ut‖ ^ 2) := by
        exact div_nonneg hnum_nonneg hden_nonneg
      have halpha :
          cndGLineSearch S G u S.gamma⁻¹ ut ∈ Set.Icc (0 : ℝ) 1 := by
        constructor
        · simpa [cndGLineSearch, direction, vt] using
            le_min zero_le_one hquot_nonneg
        · simpa [cndGLineSearch, direction, vt] using
            (min_le_left (1 : ℝ)
              (⟪S.gamma⁻¹ • (u - ut) - G, vt - ut⟫_ℝ /
                (S.gamma⁻¹ * ‖vt - ut‖ ^ 2)))
      have hline := S.hX_convex.lineMap_mem ih hvt halpha
      simpa [cndGRawInnerMove, SOptLib.conditionalGradientIterUpdate, direction, vt,
        AffineMap.lineMap_apply_module]
        using hline)
      n

/-- If no stopped iterate has yet passed Step 3, the stopped and raw CndG
recursions agree at the current zero-based index.

Search audit: no existing SOptLib stopping-prefix lemma matched this exact
totalized-vs-raw Algorithm 7.6 branch; this local bridge unfolds
`cndGInnerIterate` and the Mathlib iterate of `cndGRawInnerMove` directly. -/
private theorem cndG_inner_iterate_eq_raw_of_no_stop_lt
    (S : Setup E) (G u : E) (beta eta : ℝ) :
    ∀ n : ℕ,
      (∀ m : ℕ, m < n →
        ¬ cndGGapValue S G u beta (cndGInnerIterate S G u beta eta m) ≤ eta) →
      cndGInnerIterate S G u beta eta n = (fun n => (cndGRawInnerMove S G u beta)^[n] u) n := by
  exact
    SOptLib.stopped_iterate_eq_raw_of_no_stop_lt
      (cndGRawInnerMove S G u beta)
      (fun ut => cndGGapValue S G u beta ut ≤ eta)
      (cndGInnerIterate S G u beta eta)
      ((fun n => (cndGRawInnerMove S G u beta)^[n] u))
      (by simp [cndGInnerIterate])
      (by intro n; simp [cndGInnerIterate, cndGRawInnerMove])
      (by intro n; simp [Function.iterate_succ_apply'])

/-- A small raw CndG gap yields an actual witness for the stopped implementation.

Search audit: `exists_gap_stop_to_first` packages a witness into the first
stopping index but does not relate raw and totalized recursions; no SOptLib
prefix-transfer helper was found, so this theorem supplies the missing
Algorithm 7.6 Step 3 bridge. -/
private theorem cndG_raw_gap_witness_to_stopped_gap_witness
    (S : Setup E) (G u : E) :
    (∃ n : ℕ,
      cndGGapValue S G u S.gamma⁻¹
        ((fun n => (cndGRawInnerMove S G u S.gamma⁻¹)^[n] u) n) ≤ S.eta) →
    ∃ t : ℕ, 1 ≤ t ∧
      cndGGapValue S G u S.gamma⁻¹
        (cndGInnerIterateOneBased S G u S.gamma⁻¹ S.eta t) ≤ S.eta := by
  simpa [cndGInnerIterateOneBased] using
    SOptLib.exists_stopped_witness_of_raw_witness
      (stop := fun ut => cndGGapValue S G u S.gamma⁻¹ ut ≤ S.eta)
      (raw := (fun n => (cndGRawInnerMove S G u S.gamma⁻¹)^[n] u))
      (stopped := cndGInnerIterate S G u S.gamma⁻¹ S.eta)
      (h_prefix := fun n hno_lt =>
        cndG_inner_iterate_eq_raw_of_no_stop_lt S G u S.gamma⁻¹ S.eta n hno_lt)

/-- The displayed clamp `min 1 q` minimizes a positive scalar quadratic on
`[0,1]`.

Search audit: `argmin_Icc_zero_one_pos_quadratic_eq_min_one` proves the
uniqueness direction from an argmin certificate to the clamp, while
`segment_linear_quadratic_stepsize_minimizes` gives an abstract selector.  No
searched SOptLib lemma gave this reverse clamp-to-argmin inequality, which is
the scalar bridge needed to identify the paper's closed-form line search with
the segment argmin in Eq. (7.2.6). -/
private theorem min_one_clamp_pos_quadratic_le
    {den q a : ℝ} (hden : 0 < den) (hq0 : 0 ≤ q)
    (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    (den / 2) * (min 1 q) ^ 2 - den * q * (min 1 q) ≤
      (den / 2) * a ^ 2 - den * q * a := by
  exact (fun _ : 0 ≤ q =>
    _root_.min_one_clamp_pos_quadratic_le (den := den) (q := q) (a := a) hden ha) hq0

set_option maxHeartbeats 800000

/-- Scalar expansion of the local CndG line-search objective along the selected
segment.

Search audit: `SOptLib.linear_centered_quadratic_along_line_eq_quadratic`
exactly supplies the Hilbert-space expansion and is used directly; the abstract
`segment_linear_quadratic_stepsize_minimizes` selector was rejected here because
Lan Eq. (7.2.5) requires the literal displayed quotient used by
`cndGLineSearch`. -/
private theorem cndG_phi_segment_eq_quadratic
    (S : Setup E) (G u : E) (beta : ℝ) (ut : E) (a : ℝ) :
    let vt := cndGLinearOraclePoint S ut (G + beta • (ut - u))
    let d := vt - ut
    let den := beta * ‖d‖ ^ 2
    let num := ⟪beta • (u - ut) - G, d⟫_ℝ
    ⟪G, (1 - a) • ut + a • vt⟫_ℝ +
        beta / 2 * ‖(1 - a) • ut + a • vt - u‖ ^ 2 =
      (⟪G, ut⟫_ℝ + beta / 2 * ‖ut - u‖ ^ 2) +
        (den / 2) * a ^ 2 - num * a := by
  classical
  let vt := cndGLinearOraclePoint S ut (G + beta • (ut - u))
  let d := vt - ut
  simpa [vt, d, sub_eq_add_neg, add_smul, add_assoc, add_left_comm, add_comm] using
    (SOptLib.linear_centered_quadratic_along_line_eq_quadratic
      (g := G) (u := u) (ut := ut) (d := d) (beta := beta) (a := a))

/-- The printed quotient/min CndG line search is no worse than any feasible
segment weight for the centered quadratic model.

Search audit: considered
`SOptLib.ConditionalGradient.segment_linear_quadratic_stepsize_minimizes`, but it
minimizes SOptLib's abstract classical-choice stepsize, not this file's literal
Eq. (7.2.5) quotient.  The proof instead uses
`SOptLib.linear_centered_quadratic_along_line_eq_quadratic`,
`compactLinearModelMaximizer_isMax`, and the local
`min_one_clamp_pos_quadratic_le`, aligning with Lan Eq. (7.2.6). -/
private theorem cndg_closed_form_line_search_segment_min
    (S : Setup E) (G u : E) {beta : ℝ} {ut : E}
    (hut : ut ∈ S.X) (hbeta_pos : 0 < beta) :
    ∀ a ∈ Set.Icc (0 : ℝ) 1,
      ⟪G, SOptLib.conditionalGradientIterUpdate (fun _ : ℕ => cndGLineSearch S G u beta ut) (fun Gm => cndGLinearOraclePoint S ut (Gm + beta • (ut - u))) ut G 0⟫_ℝ +
          beta / 2 * ‖SOptLib.conditionalGradientIterUpdate (fun _ : ℕ => cndGLineSearch S G u beta ut) (fun Gm => cndGLinearOraclePoint S ut (Gm + beta • (ut - u))) ut G 0 - u‖ ^ 2 ≤
        ⟪G, (1 - a) • ut +
            a • cndGLinearOraclePoint S ut (G + beta • (ut - u))⟫_ℝ +
          beta / 2 *
            ‖(1 - a) • ut +
                a • cndGLinearOraclePoint S ut (G + beta • (ut - u)) - u‖ ^ 2 := by
  classical
  intro a ha
  let direction := G + beta • (ut - u)
  let vt := cndGLinearOraclePoint S ut direction
  have hmax :
      IsMaxOn (fun x : E => ⟪G + beta • (ut - u), ut - x⟫_ℝ) S.X vt := by
    rw [isMaxOn_iff]
    intro z hz
    simpa [vt, direction, cndGLinearOraclePoint] using
      SOptLib.compactLinearModelMaximizer_isMax S.hX_compact
        ⟨S.x₁, S.hx₁_mem⟩ ut direction z hz
  have hline :=
    SOptLib.ConditionalGradient.closed_form_segment_quadratic_line_search_minimizes
      (X := S.X) (G := G) (u := u) (beta := beta) (ut := ut) (v := vt)
      hut hmax hbeta_pos a ha
  simpa [SOptLib.conditionalGradientIterUpdate, cndGLineSearch, direction, vt] using hline

/-- Raw CndG successors inherit the closed-form line-search segment comparison.

Search audit: `SOptLib.one_based_line_search_iterate_succ_le_two_div` is the
generic one-based consumer, but this file's raw sequence is zero-based and uses
the literal quotient `cndGLineSearch`; the helper below specializes the proved
closed-form bridge to the raw Mathlib iterate without changing the algorithmic
objects. -/
private theorem cndg_raw_line_search_segment_min
    (S : Setup E) (G u : E) {beta : ℝ}
    (hmem : ∀ n : ℕ, (fun n => (cndGRawInnerMove S G u beta)^[n] u) n ∈ S.X)
    (hbeta_pos : 0 < beta) :
    ∀ n : ℕ, ∀ a ∈ Set.Icc (0 : ℝ) 1,
      ⟪G, (fun n => (cndGRawInnerMove S G u beta)^[n] u) (n + 1)⟫_ℝ +
          beta / 2 * ‖(fun n => (cndGRawInnerMove S G u beta)^[n] u) (n + 1) - u‖ ^ 2 ≤
        ⟪G, (1 - a) • (fun n => (cndGRawInnerMove S G u beta)^[n] u) n +
            a • cndGLinearOraclePoint S ((fun n => (cndGRawInnerMove S G u beta)^[n] u) n)
              (G + beta • ((fun n => (cndGRawInnerMove S G u beta)^[n] u) n - u))⟫_ℝ +
          beta / 2 *
            ‖(1 - a) • (fun n => (cndGRawInnerMove S G u beta)^[n] u) n +
                a • cndGLinearOraclePoint S ((fun n => (cndGRawInnerMove S G u beta)^[n] u) n)
                  (G + beta • ((fun n => (cndGRawInnerMove S G u beta)^[n] u) n - u)) - u‖ ^ 2 := by
  intro n a ha
  let ut := (fun n => (cndGRawInnerMove S G u beta)^[n] u) n
  have hline :=
    cndg_closed_form_line_search_segment_min
      (S := S) (G := G) (u := u) (beta := beta) (ut := ut)
      (hmem n) hbeta_pos a ha
  simpa [cndGRawInnerMove, Function.iterate_succ_apply', ut] using hline

/-- Raw CndG line-search descent in Wolfe-gap quadratic form.

Search audit: `SOptLib.line_search_iterate_succ_le_gap_quadratic` is the
matching abstract assembly lemma in `Layer1/Descent`; this route-local theorem
keeps the already-proved specialization to the file's raw zero-based sequence
and literal Eq. (7.2.5) line-search bridge in scope. -/
private theorem cndg_raw_line_search_gap_quadratic
    (S : Setup E) (G u : E) {beta : ℝ}
    (hmem : ∀ n : ℕ, (fun n => (cndGRawInnerMove S G u beta)^[n] u) n ∈ S.X)
    (hbeta_pos : 0 < beta) :
    ∀ n : ℕ, ∀ a ∈ Set.Icc (0 : ℝ) 1,
      let ut := (fun n => (cndGRawInnerMove S G u beta)^[n] u) n
      let vt := cndGLinearOraclePoint S ut (G + beta • (ut - u))
      ⟪G, (fun n => (cndGRawInnerMove S G u beta)^[n] u) (n + 1)⟫_ℝ +
          beta / 2 * ‖(fun n => (cndGRawInnerMove S G u beta)^[n] u) (n + 1) - u‖ ^ 2 ≤
        (⟪G, ut⟫_ℝ + beta / 2 * ‖ut - u‖ ^ 2) +
          (beta * ‖vt - ut‖ ^ 2 / 2) * a ^ 2 -
            cndGGapValue S G u beta ut * a := by
  intro n a ha
  let ut := (fun n => (cndGRawInnerMove S G u beta)^[n] u) n
  let vt := cndGLinearOraclePoint S ut (G + beta • (ut - u))
  let d := vt - ut
  let den := beta * ‖d‖ ^ 2
  let num := ⟪beta • (u - ut) - G, d⟫_ℝ
  have hline :=
    cndg_raw_line_search_segment_min
      (S := S) (G := G) (u := u) (beta := beta) hmem hbeta_pos n a ha
  have hline' :
      ⟪G, (fun n => (cndGRawInnerMove S G u beta)^[n] u) (n + 1)⟫_ℝ +
          beta / 2 * ‖(fun n => (cndGRawInnerMove S G u beta)^[n] u) (n + 1) - u‖ ^ 2 ≤
        ⟪G, (1 - a) • ut + a • vt⟫_ℝ +
          beta / 2 * ‖(1 - a) • ut + a • vt - u‖ ^ 2 := by
    simpa [ut, vt] using hline
  have hquad :
      ⟪G, (1 - a) • ut + a • vt⟫_ℝ +
          beta / 2 * ‖(1 - a) • ut + a • vt - u‖ ^ 2 =
        (⟪G, ut⟫_ℝ + beta / 2 * ‖ut - u‖ ^ 2) +
          (den / 2) * a ^ 2 - num * a := by
    simpa [ut, vt, d, den, num] using
      cndG_phi_segment_eq_quadratic S G u beta ut a
  have hnum :
      num = cndGGapValue S G u beta ut := by
    have hvec : beta • (u - ut) - G = -(G + beta • (ut - u)) := by
      module
    have hdiff : -(vt - ut) = ut - vt := by
      abel
    calc
      num = ⟪beta • (u - ut) - G, vt - ut⟫_ℝ := by
        rfl
      _ = ⟪-(G + beta • (ut - u)), vt - ut⟫_ℝ := by rw [hvec]
      _ = -⟪G + beta • (ut - u), vt - ut⟫_ℝ := by rw [inner_neg_left]
      _ = ⟪G + beta • (ut - u), ut - vt⟫_ℝ := by
        rw [← hdiff, inner_neg_right]
      _ = cndGGapValue S G u beta ut := by
        rfl
  have hquad' :
      ⟪G, (1 - a) • ut + a • vt⟫_ℝ +
          beta / 2 * ‖(1 - a) • ut + a • vt - u‖ ^ 2 =
        (⟪G, ut⟫_ℝ + beta / 2 * ‖ut - u‖ ^ 2) +
          (beta * ‖vt - ut‖ ^ 2 / 2) * a ^ 2 -
            cndGGapValue S G u beta ut * a := by
    simpa [d, den, num, hnum] using hquad
  nlinarith [hline', hquad']

/-- The CndG quadratic model attains its constrained minimum on `X`.

Search audit: `SOptLib.objectiveMinimum_exists_of_isCompact_continuousOn`
exactly matches Lan Theorem 7.9(c)'s `phi* := min_X phi` step; prox-objective
selectors were rejected because Eq. (7.2.7) is the literal Euclidean quadratic
model `⟪G,x⟫ + beta / 2 * ‖x-u‖^2`. -/
private theorem cndg_quadratic_model_minimizer_exists
    (S : Setup E) (G u : E) (beta : ℝ) :
    ∃ xMin : E, xMin ∈ S.X ∧ ∀ y : E, y ∈ S.X →
      ⟪G, xMin⟫_ℝ + beta / 2 * ‖xMin - u‖ ^ 2 ≤
        ⟪G, y⟫_ℝ + beta / 2 * ‖y - u‖ ^ 2 := by
  classical
  let phi : E → ℝ := fun x => ⟪G, x⟫_ℝ + beta / 2 * ‖x - u‖ ^ 2
  have hXne : S.X.Nonempty := ⟨S.x₁, S.hx₁_mem⟩
  have hcont : ContinuousOn phi S.X := by
    intro x hx
    have hlin : ContinuousWithinAt (fun z : E => ⟪G, z⟫_ℝ) S.X x :=
      (continuous_const.inner continuous_id).continuousWithinAt
    have hquad : ContinuousWithinAt (fun z : E => beta / 2 * ‖z - u‖ ^ 2) S.X x :=
      (((continuous_id.sub continuous_const).norm.pow 2).const_mul (beta / 2)).continuousWithinAt
    exact hlin.add hquad
  rcases SOptLib.objectiveMinimum_exists_of_isCompact_continuousOn
      phi S.hX_compact hXne hcont with ⟨xMin, hxMin⟩
  refine ⟨xMin.1, xMin.2, ?_⟩
  intro y hy
  exact hxMin ⟨y, hy⟩

/-- A selected CndG Wolfe gap dominates the CndG quadratic residual.

Search audit: `SOptLib.ConditionalGradient.centeredQuadratic_residual_le_maxLinearModelGap`
is the aligned Layer0 bridge for Lan's post-(7.2.24) comparison
`l_phi(u_t,v_t) <= phi(x)`; this helper only specializes its abstract
`IsMaxOn` premise to this file's compact linear oracle. -/
private theorem cndg_gap_ge_quadratic_residual
    (S : Setup E) (G u : E) {beta : ℝ} {ut x : E}
    (hbeta_nonneg : 0 ≤ beta) (hx : x ∈ S.X) :
    (⟪G, ut⟫_ℝ + beta / 2 * ‖ut - u‖ ^ 2) -
        (⟪G, x⟫_ℝ + beta / 2 * ‖x - u‖ ^ 2) ≤
      cndGGapValue S G u beta ut := by
  classical
  let direction := G + beta • (ut - u)
  let vt := cndGLinearOraclePoint S ut direction
  have hselected : IsMaxOn (fun y : E => ⟪direction, ut - y⟫_ℝ) S.X vt := by
    exact isMaxOn_iff.mpr (fun z hz => by
      simpa [vt, direction, cndGLinearOraclePoint] using
        SOptLib.compactLinearModelMaximizer_isMax S.hX_compact
          ⟨S.x₁, S.hx₁_mem⟩ ut direction z hz)
  have hres :=
    SOptLib.ConditionalGradient.centeredQuadratic_residual_le_maxLinearModelGap
      (X := S.X) (g := G) (center := u) (current := ut)
      (selected := vt) (x := x) (β := beta) hbeta_nonneg hx hselected
  simpa [cndGGapValue, cndGLinearOraclePoint, direction, vt] using hres

/-- Extract the small shifted Wolfe gap from a triangular weighted-sum budget.

Search audit: `SOptLib.exists_le_of_weighted_sum_Icc_one_le` exactly matches
Lan Theorem 7.9(c)'s final weighted-min extraction after Eq. (7.2.26), so this
helper is just its specialization to the local CndG gap sequence. -/
private theorem paper_cndg_shifted_min_wolfeGap_bound_of_weighted_sum
    (S : Setup E) (G u : E) {T : ℕ}
    (hT : 1 ≤ T)
    (hsum :
      Finset.sum (Finset.Icc 1 T)
          (fun j => (j : ℝ) *
            cndGGapValue S G u S.gamma⁻¹
              (cndGInnerIterateOneBased S G u S.gamma⁻¹ S.eta (j + 1))) ≤
        3 * (T : ℝ) *
          (S.gamma⁻¹ *
            (Classical.choose
              (SOptLib.compactNormDiameter S.X ⟨S.x₁, S.hx₁_mem⟩ S.hX_compact)) ^ 2)) :
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ T ∧
      cndGGapValue S G u S.gamma⁻¹
      (cndGInnerIterateOneBased S G u S.gamma⁻¹ S.eta (j + 1)) ≤
        6 * S.gamma⁻¹ *
            (Classical.choose
              (SOptLib.compactNormDiameter S.X ⟨S.x₁, S.hx₁_mem⟩ S.hX_compact)) ^ 2 /
          (((T + 1 : ℕ) : ℝ)) := by
  simpa [mul_assoc] using
    (SOptLib.exists_le_of_weighted_sum_Icc_one_le
      (T := T)
      (A := S.gamma⁻¹ *
        (Classical.choose
          (SOptLib.compactNormDiameter S.X ⟨S.x₁, S.hx₁_mem⟩ S.hX_compact)) ^ 2)
      (u := fun j =>
        cndGGapValue S G u S.gamma⁻¹
      (cndGInnerIterateOneBased S G u S.gamma⁻¹ S.eta (j + 1)))
      hT hsum)

/-- Extract the small shifted Wolfe gap from the raw CndG triangular sum.

Search audit: `SOptLib.exists_le_of_weighted_sum_Icc_one_le` exactly matches
the scalar weighted-min extraction in Lan Eq. (7.2.26); this helper specializes
it to the raw, non-stopping sequence required by the source proof. -/
private theorem paper_cndg_raw_shifted_min_wolfeGap_bound_of_weighted_sum
    (S : Setup E) (G u : E) {T : ℕ}
    (hT : 1 ≤ T)
    (hsum :
      Finset.sum (Finset.Icc 1 T)
          (fun j => (j : ℝ) *
            cndGGapValue S G u S.gamma⁻¹
              (cndGRawInnerIterateOneBased S G u S.gamma⁻¹ (j + 1))) ≤
        3 * (T : ℝ) *
          (S.gamma⁻¹ *
            (Classical.choose
              (SOptLib.compactNormDiameter S.X ⟨S.x₁, S.hx₁_mem⟩ S.hX_compact)) ^ 2)) :
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ T ∧
      cndGGapValue S G u S.gamma⁻¹
          (cndGRawInnerIterateOneBased S G u S.gamma⁻¹ (j + 1)) ≤
        6 * S.gamma⁻¹ *
            (Classical.choose
              (SOptLib.compactNormDiameter S.X ⟨S.x₁, S.hx₁_mem⟩ S.hX_compact)) ^ 2 /
          (((T + 1 : ℕ) : ℝ)) := by
  simpa [mul_assoc] using
    (SOptLib.exists_le_of_weighted_sum_Icc_one_le
      (T := T)
      (A := S.gamma⁻¹ *
        (Classical.choose
          (SOptLib.compactNormDiameter S.X ⟨S.x₁, S.hx₁_mem⟩ S.hX_compact)) ^ 2)
      (u := fun j =>
        cndGGapValue S G u S.gamma⁻¹
          (cndGRawInnerIterateOneBased S G u S.gamma⁻¹ (j + 1)))
      hT hsum)

/-- Local Theorem 7.9(c) shifted minimum Wolfe-gap estimate for the literal CndG
implementation.

Search audit: `SOptLib.shifted_weighted_wolfeGap_sum_le_of_normalized_step` is
the aligned Layer1 telescope theorem and is the intended aggregation endpoint;
`SOptLib.cndG_terminates_of_shifted_min_wolfeGap_bound` is only the downstream
stopping bridge, not this analytic premise.  The remaining work is the
source-derived bridge from this file's line-search formula and compact oracle to
the normalized Wolfe-step hypotheses of the SOptLib telescope theorem, matching
Lan Theorem 7.9(c) / Eq. (7.2.26). -/
private theorem paper_cndg_shifted_min_wolfeGap_bound (S : Setup E) (G u : E)
    (hu : u ∈ S.X) :
    ∀ {T : ℕ}, 1 ≤ T →
      ∃ j : ℕ, 1 ≤ j ∧ j ≤ T ∧
        cndGGapValue S G u S.gamma⁻¹
            (cndGRawInnerIterateOneBased S G u S.gamma⁻¹ (j + 1)) ≤
          6 * S.gamma⁻¹ *
              (Classical.choose
                (SOptLib.compactNormDiameter S.X ⟨S.x₁, S.hx₁_mem⟩ S.hX_compact)) ^ 2 /
            (((T + 1 : ℕ) : ℝ)) := by
  intro T hT
  have hmem : ∀ n : ℕ, (fun n => (cndGRawInnerMove S G u S.gamma⁻¹)^[n] u) n ∈ S.X :=
    cndG_raw_inner_iterate_mem_of_start_mem S G u hu
  have hbeta_pos : 0 < S.gamma⁻¹ := by
    rw [S.hgamma_eq_inv_L]
    simpa using averageSmoothness_pos S
  have hsum :
      Finset.sum (Finset.Icc 1 T)
          (fun j => (j : ℝ) *
            cndGGapValue S G u S.gamma⁻¹
              (cndGRawInnerIterateOneBased S G u S.gamma⁻¹ (j + 1))) ≤
        3 * (T : ℝ) *
          (S.gamma⁻¹ *
            (Classical.choose
              (SOptLib.compactNormDiameter S.X ⟨S.x₁, S.hx₁_mem⟩ S.hX_compact)) ^ 2) := by
    have hgapQuadratic :=
      cndg_raw_line_search_gap_quadratic
        (S := S) (G := G) (u := u) (beta := S.gamma⁻¹) hmem hbeta_pos
    classical
    let beta : ℝ := S.gamma⁻¹
    let D : ℝ :=
      Classical.choose
        (SOptLib.compactNormDiameter S.X ⟨S.x₁, S.hx₁_mem⟩ S.hX_compact)
    let A : ℝ := beta * D ^ 2
    let phi : E → ℝ := fun x => ⟪G, x⟫_ℝ + beta / 2 * ‖x - u‖ ^ 2
    let iterate : ℕ → E := fun n => cndGRawInnerIterateOneBased S G u beta n
    let wolfeGap : E → ℝ := fun x => cndGGapValue S G u beta x
    rcases cndg_quadratic_model_minimizer_exists S G u beta with
      ⟨xMin, hxMin_mem, hxMin_min⟩
    have hD_bound : ∀ a ∈ S.X, ∀ b ∈ S.X, ‖a - b‖ ≤ D := by
      have hDspec :=
        Classical.choose_spec
          (SOptLib.compactNormDiameter S.X ⟨S.x₁, S.hx₁_mem⟩ S.hX_compact)
      rcases hDspec with ⟨xD, hxD, yD, hyD, hD_eq, hbound⟩
      simpa [D] using hbound
    have hA_nonneg : 0 ≤ A := by
      exact mul_nonneg (le_of_lt hbeta_pos) (sq_nonneg D)
    have hterminal :
        0 ≤ phi (iterate (T + 2)) - phi xMin := by
      have hit_mem : iterate (T + 2) ∈ S.X := by
        simpa [iterate, cndGRawInnerIterateOneBased, beta] using hmem (T + 1)
      have hmin := hxMin_min (iterate (T + 2)) hit_mem
      simpa [phi] using sub_nonneg.mpr hmin
    have hcurvature_le_A_half :
        ∀ j : ℕ,
          let ut := (fun n => (cndGRawInnerMove S G u beta)^[n] u) j
          let vt := cndGLinearOraclePoint S ut (G + beta • (ut - u))
          beta * ‖vt - ut‖ ^ 2 / 2 ≤ A / 2 := by
      intro j
      let ut := (fun n => (cndGRawInnerMove S G u beta)^[n] u) j
      let vt := cndGLinearOraclePoint S ut (G + beta • (ut - u))
      have hut : ut ∈ S.X := by
        simpa [ut, beta] using hmem j
      have hvt : vt ∈ S.X := by
        simpa [vt, ut, cndGLinearOraclePoint] using
          SOptLib.compactLinearModelMaximizer_mem S.hX_compact
            ⟨S.x₁, S.hx₁_mem⟩ ut (G + beta • (ut - u))
      have hnorm_le : ‖vt - ut‖ ≤ D := hD_bound vt hvt ut hut
      have hnorm_sq_le : ‖vt - ut‖ ^ 2 ≤ D ^ 2 := by
        have hnorm_nonneg : 0 ≤ ‖vt - ut‖ := norm_nonneg _
        nlinarith
      have hscaled : beta * ‖vt - ut‖ ^ 2 ≤ beta * D ^ 2 := by
        exact mul_le_mul_of_nonneg_left hnorm_sq_le (le_of_lt hbeta_pos)
      dsimp [A]
      nlinarith
    have hDelta_bound : ∀ j, j ∈ Finset.Icc 1 T →
        phi (iterate (j + 1)) - phi xMin ≤ 2 * A / (((j + 1 : ℕ) : ℝ)) := by
      let Delta : ℕ → ℝ := fun n => phi (iterate n) - phi xMin
      have hrec : ∀ t, 1 ≤ t →
          let lam : ℝ := (2 : ℝ) / (((t + 1 : ℕ) : ℝ))
          Delta (t + 1) ≤ (1 - lam) * Delta t + (A / 2) * lam ^ 2 := by
        intro t ht
        let lam : ℝ := (2 : ℝ) / (((t + 1 : ℕ) : ℝ))
        let n : ℕ := t - 1
        let ut := (fun n => (cndGRawInnerMove S G u beta)^[n] u) n
        let vt := cndGLinearOraclePoint S ut (G + beta • (ut - u))
        let curv : ℝ := beta * ‖vt - ut‖ ^ 2 / 2
        have ha : lam ∈ Set.Icc (0 : ℝ) 1 := by
          simpa [lam] using SOptLib.two_div_nat_succ_cast_mem_Icc t ht
        have hn_succ : n + 1 = t := by
          exact Nat.sub_add_cancel ht
        have hquad := hgapQuadratic n lam ha
        have hquad_phi :
            phi (iterate (t + 1)) ≤
              phi (iterate t) + curv * lam ^ 2 - wolfeGap (iterate t) * lam := by
          simpa [phi, iterate, cndGRawInnerIterateOneBased, wolfeGap,
            beta, n, ut, vt, curv, hn_succ, lam] using hquad
        have hgap_lower :
            phi (iterate t) - phi xMin ≤ wolfeGap (iterate t) := by
          have hgap_res :=
            cndg_gap_ge_quadratic_residual
              (S := S) (G := G) (u := u) (beta := beta)
              (ut := iterate t) (x := xMin)
              (le_of_lt hbeta_pos) hxMin_mem
          simpa [phi, wolfeGap, beta] using hgap_res
        have hgap_mul :
            (phi (iterate t) - phi xMin) * lam ≤ wolfeGap (iterate t) * lam := by
          exact mul_le_mul_of_nonneg_right hgap_lower ha.1
        have hcurv_le : curv ≤ A / 2 := by
          simpa [curv, ut, vt] using hcurvature_le_A_half n
        have hcurv_mul : curv * lam ^ 2 ≤ (A / 2) * lam ^ 2 := by
          exact mul_le_mul_of_nonneg_right hcurv_le (sq_nonneg lam)
        dsimp [Delta]
        nlinarith
      intro j hj
      have hj_ge_one : 1 ≤ j := (Finset.mem_Icc.mp hj).1
      exact SOptLib.two_div_succ_residual_bound_of_recursion
        Delta A hA_nonneg hrec hj_ge_one
    have hstep : ∀ j, j ∈ Finset.Icc 1 T →
        (2 / (((j + 2 : ℕ) : ℝ))) * wolfeGap (iterate (j + 1)) ≤
          (phi (iterate (j + 1)) - phi xMin) -
            (phi (iterate (j + 2)) - phi xMin) +
              (A / 2) * (2 / (((j + 2 : ℕ) : ℝ))) ^ 2 := by
      intro j hj
      let a : ℝ := 2 / (((j + 2 : ℕ) : ℝ))
      let ut := (fun n => (cndGRawInnerMove S G u beta)^[n] u) j
      let vt := cndGLinearOraclePoint S ut (G + beta • (ut - u))
      have ha : a ∈ Set.Icc (0 : ℝ) 1 := by
        have ha' := SOptLib.two_div_nat_succ_cast_mem_Icc (j + 1)
          (Nat.succ_pos j)
        convert ha' using 1
      have hquad := hgapQuadratic j a ha
      have hquad_phi :
          phi ((fun n => (cndGRawInnerMove S G u beta)^[n] u) (j + 1)) ≤
            phi ut + (beta * ‖vt - ut‖ ^ 2 / 2) * a ^ 2 -
              wolfeGap ut * a := by
        simpa [phi, wolfeGap, beta, ut, vt, a] using hquad
      have hcurv : (beta * ‖vt - ut‖ ^ 2 / 2) * a ^ 2 ≤ (A / 2) * a ^ 2 := by
        exact mul_le_mul_of_nonneg_right (by
          simpa [ut, vt] using hcurvature_le_A_half j) (sq_nonneg a)
      have hdrop :
          a * wolfeGap ut ≤
            phi ut - phi ((fun n => (cndGRawInnerMove S G u beta)^[n] u) (j + 1)) +
              (A / 2) * a ^ 2 := by
        nlinarith
      have hit_cur :
          iterate (j + 1) = ut := by
        simp [iterate, cndGRawInnerIterateOneBased, beta, ut]
      have hit_next :
          iterate (j + 2) = (fun n => (cndGRawInnerMove S G u beta)^[n] u) (j + 1) := by
        simp [iterate, cndGRawInnerIterateOneBased, beta]
      calc
        (2 / (((j + 2 : ℕ) : ℝ))) * wolfeGap (iterate (j + 1))
            = a * wolfeGap ut := by simp [a, hit_cur]
        _ ≤ phi ut - phi ((fun n => (cndGRawInnerMove S G u beta)^[n] u) (j + 1)) +
              (A / 2) * a ^ 2 := hdrop
        _ =
            (phi (iterate (j + 1)) - phi xMin) -
              (phi (iterate (j + 2)) - phi xMin) +
                (A / 2) * (2 / (((j + 2 : ℕ) : ℝ))) ^ 2 := by
          rw [hit_cur, hit_next]
          ring
    simpa [iterate, wolfeGap, A, D, beta, mul_assoc] using
      SOptLib.shifted_weighted_wolfeGap_sum_le_of_normalized_step
        iterate phi wolfeGap xMin A T hA_nonneg hterminal hDelta_bound hstep
  exact paper_cndg_raw_shifted_min_wolfeGap_bound_of_weighted_sum S G u hT hsum

/-- Convert any one-based stopping witness into the first such witness.

Search audit: `SOptLib.firstGapStoppingOutputRel_exists_index` and
`SOptLib.firstGapStoppingOutputRel_def` expose minimality after a
`firstGapStoppingOutputRel` is already packaged; no existing helper found in
the reverse direction, so this local `Nat.find` bridge supplies the missing
bookkeeping. -/
private theorem exists_gap_stop_to_first {gap : ℕ → ℝ} {eta : ℝ}
    (hstop : ∃ t : ℕ, 1 ≤ t ∧ gap t ≤ eta) :
    ∃ t : ℕ, (1 ≤ t ∧ gap t ≤ eta) ∧
      ∀ s : ℕ, 1 ≤ s → s < t → ¬ (1 ≤ s ∧ gap s ≤ eta) := by
  exact SOptLib.exists_first_gap_stop_of_exists_gap_stop (gap := gap) (eta := eta) hstop

/-- Positive-tolerance termination obligation for the paper CndG call.

The PDF states `eta >= 0` after Eq. (7.5.7), while Theorem 7.9(c)'s finite
inner-iteration ceiling contains `eta` in the denominator.  This theorem is
therefore the source-backed positive-tolerance bridge used internally; no
unconditional finite termination is exported for the `eta = 0` boundary case. -/
theorem paperCndGTerminates_of_eta_pos (S : Setup E) (G u : E)
    (hu : u ∈ S.X) (hη : 0 < S.eta) :
    paperCndGTerminates S G u := by
  classical
  let gap : ℕ → ℝ := fun t =>
    cndGGapValue S G u S.gamma⁻¹
      (cndGInnerIterateOneBased S G u S.gamma⁻¹ S.eta t)
  let D : ℝ :=
    Classical.choose
      (SOptLib.compactNormDiameter S.X ⟨S.x₁, S.hx₁_mem⟩ S.hX_compact)
  let T : ℕ := max 1 (Nat.ceil ((6 * S.gamma⁻¹ * D ^ 2) / S.eta))
  have hT : 1 ≤ T := by
    exact le_max_left 1 (Nat.ceil ((6 * S.gamma⁻¹ * D ^ 2) / S.eta))
  have hraw_shifted :
      ∃ j : ℕ, 1 ≤ j ∧ j ≤ T ∧
        cndGGapValue S G u S.gamma⁻¹
            (cndGRawInnerIterateOneBased S G u S.gamma⁻¹ (j + 1)) ≤
          6 * S.gamma⁻¹ * D ^ 2 / (((T + 1 : ℕ) : ℝ)) := by
    simpa [D] using
      paper_cndg_shifted_min_wolfeGap_bound S G u hu hT
  have hceil :
      6 * S.gamma⁻¹ * D ^ 2 / (((T + 1 : ℕ) : ℝ)) ≤ S.eta := by
    simpa [T] using
      div_nat_succ_positiveCeil_le (6 * S.gamma⁻¹ * D ^ 2) S.eta hη
  have hstop : ∃ t : ℕ, 1 ≤ t ∧ gap t ≤ S.eta := by
    rcases hraw_shifted with ⟨j, _hj1, _hjT, hgap_bound⟩
    have hraw_gap :
        cndGGapValue S G u S.gamma⁻¹
          ((fun n => (cndGRawInnerMove S G u S.gamma⁻¹)^[n] u) j) ≤ S.eta := by
      have hgap_eta :
          cndGGapValue S G u S.gamma⁻¹
              (cndGRawInnerIterateOneBased S G u S.gamma⁻¹ (j + 1)) ≤ S.eta :=
        le_trans hgap_bound hceil
      simpa [cndGRawInnerIterateOneBased] using hgap_eta
    simpa [gap] using
      cndG_raw_gap_witness_to_stopped_gap_witness S G u ⟨j, hraw_gap⟩
  simpa [paperCndGTerminates, gap] using
    exists_gap_stop_to_first (gap := gap) (eta := S.eta) hstop

/-- First stopping index for the paper's Algorithm 7.6 CndG call inside
Eq. (7.5.5), defined only from an actual stopping witness.

This removes the previous totalized fallback index.  Since Eq. (7.5.7) allows
`eta = 0` while Theorem 7.9(c)'s ceiling uses `eta` in a denominator, finite
termination at the source boundary is kept as a proof obligation rather than
silently built into the object layer. -/
def paperCndGStopIndex (S : Setup E) (G u : E)
    (hterm : paperCndGTerminates S G u) : ℕ :=
  Classical.choose hterm

/-- Canonical CndG procedure output `u+` from Algorithm 7.6 for the paper
parameters `beta = 1/gamma` and the source tolerance `eta >= 0`, conditional on
the printed stopping test actually terminating. -/
def cndGProcedureOutput (S : Setup E) (G u : E)
    (hterm : paperCndGTerminates S G u) : E :=
  cndGInnerIterateOneBased S G u S.gamma⁻¹ S.eta
    (paperCndGStopIndex S G u hterm)

/-- The canonical CndG output is the first inner iterate satisfying the printed
Step 3 gap test. -/
theorem cndGProcedureOutput_firstGap (S : Setup E) (G u : E)
    (hterm : paperCndGTerminates S G u) :
    SOptLib.firstGapStoppingOutputRel
      (fun z => cndGGapValue S G u S.gamma⁻¹ z)
      (cndGInnerIterateOneBased S G u S.gamma⁻¹ S.eta)
      S.eta
      (cndGProcedureOutput S G u hterm) := by
  refine ⟨paperCndGStopIndex S G u hterm, ?_⟩
  rcases Classical.choose_spec hterm with
    ⟨hstop, hfirst⟩
  exact ⟨by simpa [paperCndGStopIndex] using hstop,
    by simpa [paperCndGStopIndex] using hfirst, by
      simp [cndGProcedureOutput, paperCndGStopIndex]⟩

/-- Canonical outer CndG update
`x_{k+1} = CndG(G_k, x_k, 1/gamma, eta)`, Eq. (7.5.5), now defined by the
Algorithm 7.6 inner loop rather than by choosing any point satisfying
Eq. (7.5.7). -/
def cndGUpdate (S : Setup E) (G x : E)
    (hterm : paperCndGTerminates S G x) : E :=
  cndGProcedureOutput S G x hterm

/-- The canonical CndG update satisfies the paper stopping inequality.

The proof must bridge Algorithm 7.6's Wolfe-gap stopping condition to the
variational inequality in Eq. (7.5.7). -/
theorem cndGUpdate_spec (S : Setup E) (G x : E)
    (hx : x ∈ S.X) (hterm : paperCndGTerminates S G x) :
    cndGUpdateSpec S G x S.gamma S.eta (cndGUpdate S G x hterm) := by
  unfold cndGUpdateSpec
  exact SOptLib.firstGapOutput_isApproxConditionalGradientUpdate
    (X := S.X) (G := G) (x := x) (y := cndGUpdate S G x hterm)
    (beta := S.gamma⁻¹) (eta := S.eta)
    (gap := fun z => cndGGapValue S G x S.gamma⁻¹ z)
    (iterate := cndGInnerIterateOneBased S G x S.gamma⁻¹ S.eta)
    (by simpa [cndGUpdate] using cndGProcedureOutput_firstGap S G x hterm)
    (by
      intro n
      simpa [cndGInnerIterateOneBased] using
        cndG_inner_iterate_mem_of_start_mem S G x hx (n - 1))
    (by
      intro z hz
      simpa [cndGGapValue, cndGLinearOraclePoint] using
        SOptLib.compactLinearModelMaximizer_isMax S.hX_compact
          ⟨S.x₁, S.hx₁_mem⟩
          (cndGUpdate S G x hterm)
          (G + S.gamma⁻¹ • (cndGUpdate S G x hterm - x)) z hz)

/-- State for the paper recursion: previous iterate, current iterate, and current
gradient estimator.

This is data, not a spec bundle; feasibility and estimator identities are proved
as theorems about the generated process. -/
structure RunState (E : Type*) where
  previous : E
  current : E
  estimator : E

/-- Initial state with `x_1` and a full-gradient estimator at `x_1`. -/
def initialState (S : Setup E) : RunState E where
  previous := S.x₁
  current := S.x₁
  estimator := SOptLib.finiteUniformAverage S.componentGradient S.x₁

/-- One canonical outer step relation: build `G_k` by Algorithm 7.12 and then
apply the CndG replacement Eq. (7.5.5) using an actual Algorithm 7.6 stopping
witness.

This relation is the paper-facing step object.  It does not totalize CndG when
finite stopping is not established at `eta = 0`. -/
def outerStepRel (S : Setup E) (k : ℕ) (batch : Fin S.b → Fin S.componentCount)
    (state next : RunState E) : Prop :=
  let Gk := gradientEstimatorUpdate S k state.previous state.current state.estimator batch
  ∃ _ : state.current ∈ S.X,
    ∃ hterm : paperCndGTerminates S Gk state.current,
      next =
        { previous := state.current
          current := cndGUpdate S Gk state.current hterm
          estimator := Gk }

/-- Functional outer step for Algorithm 7.12 with the Eq. (7.5.5) CndG
replacement, parameterized by an already-derived termination selector.

The paper states only `eta >= 0`; since finite termination at `eta = 0` was not
found in the source, the termination selector is not exported as a source-facing
setup field or paper theorem hypothesis.  Positive-eta runs are built below from
`paperCndGTerminates_of_eta_pos`. -/
def outerStepOfTerm (S : Setup E)
    (term : ∀ G x : E, x ∈ S.X → paperCndGTerminates S G x)
    (k : ℕ) (batch : Fin S.b → Fin S.componentCount)
    (state : RunState E) (hx : state.current ∈ S.X) : RunState E :=
  let Gk := gradientEstimatorUpdate S k state.previous state.current state.estimator batch
  { previous := state.current
    current := cndGUpdate S Gk state.current (term Gk state.current hx)
    estimator := Gk }

/-- The termination-parameterized step function realizes the relational step
specification. -/
theorem outerStepOfTerm_spec (S : Setup E)
    (term : ∀ G x : E, x ∈ S.X → paperCndGTerminates S G x) (k : ℕ)
    (batch : Fin S.b → Fin S.componentCount) (state : RunState E)
    (hx : state.current ∈ S.X) :
    outerStepRel S k batch state (outerStepOfTerm S term k batch state hx) := by
  classical
  dsimp [outerStepRel, outerStepOfTerm]
  exact ⟨hx, term
    (gradientEstimatorUpdate S k state.previous state.current state.estimator batch)
    state.current hx, rfl⟩

/-- Feasibility-carrying generated Algorithm 7.12 state process.

The recursion keeps the source invariant `x_k ∈ X` as part of the generated
state so the CndG termination selector is never invoked on an arbitrary ambient
point. -/
def generatedFeasibleRunStateOfTerm (S : Setup E)
    (term : ∀ G x : E, x ∈ S.X → paperCndGTerminates S G x) {Ω : Type*}
    (batch : ℕ → Fin S.b → Ω → Fin S.componentCount) :
    ℕ → Ω → {state : RunState E // state.current ∈ S.X}
  | 0, _ => ⟨initialState S, by simpa [initialState] using S.hx₁_mem⟩
  | k + 1, ω =>
      let prev := generatedFeasibleRunStateOfTerm S term batch k ω
      let Gk := gradientEstimatorUpdate S (k + 1) prev.1.previous prev.1.current prev.1.estimator
        (fun r => batch (k + 1) r ω)
      let hterm := term Gk prev.1.current prev.2
      ⟨{ previous := prev.1.current
         current := cndGUpdate S Gk prev.1.current hterm
         estimator := Gk },
        by
          exact (cndGUpdate_spec S Gk prev.1.current prev.2 hterm).1⟩

/-- Generated Algorithm 7.12 state process from the termination-parameterized
outer step.

Candidates considered: `SOptLib.recursiveIterateProcess` is the abstract
recursive-process primitive.  The paper needs the literal one-based update
`k = 1, ..., N` with the mini-batch stream read at the same paper index, so this
local definition specializes that primitive shape to Algorithm 7.12's state and
batch convention. -/
def generatedRunStateOfTerm (S : Setup E)
    (term : ∀ G x : E, x ∈ S.X → paperCndGTerminates S G x) {Ω : Type*}
    (batch : ℕ → Fin S.b → Ω → Fin S.componentCount) : ℕ → Ω → RunState E
  | k, ω => (generatedFeasibleRunStateOfTerm S term batch k ω).1

/-- Source-facing generated-run specification driven by the omega-indexed finite
mini-batch stream.

The run is characterized by the canonical initial state and `outerStepRel`.
Existence is a proof obligation because the source does not justify
unconditional finite CndG termination at `eta = 0`. -/
def runStateSpec (S : Setup E) {Ω : Type*}
    (batch : ℕ → Fin S.b → Ω → Fin S.componentCount)
    (run : ℕ → Ω → RunState E) : Prop :=
  (∀ ω : Ω, run 0 ω = initialState S) ∧
    ∀ k : ℕ, ∀ ω : Ω,
      outerStepRel S (k + 1) (fun r => batch (k + 1) r ω)
        (run k ω) (run (k + 1) ω)

/-- The termination-parameterized recursively generated state process satisfies
the source run specification. -/
theorem generatedRunStateOfTerm_spec (S : Setup E)
    (term : ∀ G x : E, x ∈ S.X → paperCndGTerminates S G x) {Ω : Type*}
    (batch : ℕ → Fin S.b → Ω → Fin S.componentCount) :
    runStateSpec S batch (generatedRunStateOfTerm S term batch) := by
  constructor
  · intro ω
    rfl
  · intro k ω
    simpa [generatedRunStateOfTerm] using
      outerStepOfTerm_spec S term (k + 1) (fun r => batch (k + 1) r ω)
        (generatedFeasibleRunStateOfTerm S term batch k ω).1
        (generatedFeasibleRunStateOfTerm S term batch k ω).2

/-- Existence of a generated run when the paper CndG tolerance is strictly
positive.

The PDF states only `eta >= 0` after Eq. (7.5.7), while the finite CndG
termination bound used later has `eta` in the denominator.  This positive-eta
construction is therefore kept as an internal theorem obligation and is not used
to manufacture an unconditional Algorithm 7.12 run at the source boundary. -/
theorem exists_runState_of_eta_pos (S : Setup E) {Ω : Type*}
    (batch : ℕ → Fin S.b → Ω → Fin S.componentCount) (hη : 0 < S.eta) :
    ∃ run : ℕ → Ω → RunState E, runStateSpec S batch run := by
  refine ⟨generatedRunStateOfTerm S
    (fun G x hx => paperCndGTerminates_of_eta_pos S G x hx hη)
    batch, ?_⟩
  exact generatedRunStateOfTerm_spec S
    (fun G x hx => paperCndGTerminates_of_eta_pos S G x hx hη) batch

/-- Positive-eta generated run, for internal uses where termination has been
derived from the paper parameters.

This replaces the previous unconditional `Classical.choose` run; the eta-zero
case remains exposed as a source-boundary obligation rather than hidden inside
the generated process. -/
def runStateOfEtaPos (S : Setup E) {Ω : Type*}
    (batch : ℕ → Fin S.b → Ω → Fin S.componentCount) (hη : 0 < S.eta) :
    ℕ → Ω → RunState E :=
  Classical.choose (exists_runState_of_eta_pos S batch hη)

/-- The positive-eta selected generated run satisfies the source-level recursion
specification. -/
theorem runStateOfEtaPos_spec (S : Setup E) {Ω : Type*}
    (batch : ℕ → Fin S.b → Ω → Fin S.componentCount) (hη : 0 < S.eta) :
    runStateSpec S batch (runStateOfEtaPos S batch hη) := by
  exact Classical.choose_spec (exists_runState_of_eta_pos S batch hη)

/-- Positive-eta Algorithm 7.12 run over the source sample paths.

This is deliberately an internal positive-tolerance realization, not the
paper-facing unconditional run.  The PDF states only `eta >= 0` after
Eq. (7.5.7), while the finite CndG stopping bound has `eta` in the denominator;
therefore the eta-zero source boundary is not hidden behind an unconditional
`Classical.choose` run. -/
def algorithmRunOfEtaPos (S : Setup E) (hη : 0 < S.eta) :
    ℕ → AlgorithmSamplePath S → RunState E :=
  runStateOfEtaPos S (algorithmBatchStream S) hη

/-- The positive-eta Algorithm 7.12 run satisfies the source recursion. -/
theorem algorithmRunOfEtaPos_spec (S : Setup E) (hη : 0 < S.eta) :
    runStateSpec S (algorithmBatchStream S) (algorithmRunOfEtaPos S hη) := by
  exact runStateOfEtaPos_spec S (algorithmBatchStream S) hη

/-- Zero-based current iterate read from an explicit run satisfying
`runStateSpec`.

The generated run is no longer chosen unconditionally; consumers either carry a
run satisfying the canonical recursion relation or derive a positive-eta run
internally. -/
def iterate (_S : Setup E) {Ω : Type*}
    (run : ℕ → Ω → RunState E) (k : ℕ) (ω : Ω) : E :=
  (run k ω).current

/-- Zero-based gradient estimator read from an explicit generated run. -/
def estimator (_S : Setup E) {Ω : Type*}
    (run : ℕ → Ω → RunState E) (k : ℕ) (ω : Ω) : E :=
  (run k ω).estimator

/-- Zero-based current iterate for an explicit Algorithm 7.12 run over the
source sample law. -/
def algorithmIterate (S : Setup E)
    (run : ℕ → AlgorithmSamplePath S → RunState E) (k : ℕ)
    (ω : AlgorithmSamplePath S) : E :=
  iterate S run k ω

/-- Zero-based gradient estimator for an explicit Algorithm 7.12 run over the
source sample law. -/
def algorithmEstimator (S : Setup E)
    (run : ℕ → AlgorithmSamplePath S → RunState E) (k : ℕ)
    (ω : AlgorithmSamplePath S) : E :=
  estimator S run k ω

/-- The generated recursion starts at the paper initial point `x_1`. -/
theorem iterate_zero (S : Setup E) {Ω : Type*}
    (batch : ℕ → Fin S.b → Ω → Fin S.componentCount)
    (run : ℕ → Ω → RunState E) (hrun : runStateSpec S batch run) (ω : Ω) :
    iterate S run 0 ω = S.x₁ := by
  have h := hrun.1 ω
  simpa [iterate, initialState] using congrArg RunState.current h

/-- The generated estimator starts as the full gradient at `x_1`. -/
theorem estimator_zero (S : Setup E) {Ω : Type*}
    (batch : ℕ → Fin S.b → Ω → Fin S.componentCount)
    (run : ℕ → Ω → RunState E) (hrun : runStateSpec S batch run) (ω : Ω) :
    estimator S run 0 ω = SOptLib.finiteUniformAverage S.componentGradient S.x₁ := by
  have h := hrun.1 ω
  simpa [estimator, initialState] using congrArg RunState.estimator h

/-- Successor relation for the canonical state recursion. -/
theorem runState_succ (S : Setup E) {Ω : Type*}
    (batch : ℕ → Fin S.b → Ω → Fin S.componentCount)
    (run : ℕ → Ω → RunState E) (hrun : runStateSpec S batch run) (k : ℕ) (ω : Ω) :
    outerStepRel S (k + 1) (fun r => batch (k + 1) r ω)
      (run k ω) (run (k + 1) ω) := by
  exact hrun.2 k ω

/-- A `runStateSpec` trajectory is determined by the finite prefix of driving
mini-batch samples used up to that time.

Search audit: SOptLib's `recursive_process_eq_of_driver_prefix_eq` handles a
functional recursion, but Algorithm 7.12 is currently exposed through the
relational `outerStepRel`; this helper proves the same finite-prefix
determinism by unfolding that relation and using proof irrelevance for the CndG
termination witness. -/
private theorem runState_eq_of_batch_prefix_eq (S : Setup E) {Ω : Type*}
    (batch : ℕ → Fin S.b → Ω → Fin S.componentCount)
    (run : ℕ → Ω → RunState E) (hrun : runStateSpec S batch run) :
    ∀ n : ℕ, ∀ ω ω' : Ω,
      (∀ j : ℕ, j ≤ n → ∀ r : Fin S.b, batch j r ω = batch j r ω') →
        run n ω = run n ω' := by
  intro n ω ω' hprefix
  exact SOptLib.relational_recursive_process_eq_of_driver_prefix_eq
    (initial := initialState S)
    (driver := fun j (ω : Ω) => fun r : Fin S.b => batch j r ω)
    (rel := fun k sample state next => outerStepRel S k sample state next)
    (run := run)
    hrun.1 hrun.2
    (fun _k _sample _state _next _next' hstep hstep' => by
      dsimp [outerStepRel] at hstep hstep'
      rcases hstep with ⟨_hx, hterm, hnext⟩
      rcases hstep' with ⟨_hx', hterm', hnext'⟩
      have hterm_eq : hterm = hterm' := Subsingleton.elim hterm hterm'
      cases hterm_eq
      exact hnext.trans hnext'.symm)
    n ω ω' (fun j hj => by
      funext r
      exact hprefix j hj r)

/-- Real observables determined by a finite Algorithm 7.12 mini-batch prefix are
integrable under the canonical product sample law.

Search audit: `integrable_of_finiteSampleWindow_factor` handles one-index
windows and `integrable_of_finiteRange_factor` handles arbitrary finite keys.
The latter matches the two-index mini-batch prefix used by Algorithm 7.12, so
this helper specializes it to the key
`Fin (n + 1) -> Fin b -> Fin componentCount`. -/
private theorem integrable_algorithmSampleLaw_of_prefix_const (S : Setup E)
    (n : ℕ) {Z : AlgorithmSamplePath S → ℝ}
    (hconst :
      ∀ ⦃ω ω' : AlgorithmSamplePath S⦄,
        (∀ j : ℕ, j ≤ n → ∀ r : Fin S.b, ω j r = ω' j r) →
          Z ω = Z ω') :
    Integrable Z (algorithmSampleLaw S) := by
  classical
  haveI : IsProbabilityMeasure (algorithmSampleLaw S) :=
    (algorithmSampleLaw_spec S).1
  let Y : AlgorithmSamplePath S →
      (Fin (n + 1) → Fin S.b → Fin S.componentCount) :=
    fun ω j r => ω j.1 r
  have hY : Measurable Y := by
    dsimp [Y]
    refine measurable_pi_lambda _ ?_
    intro j
    refine measurable_pi_lambda _ ?_
    intro r
    exact (measurable_pi_apply r).comp (measurable_pi_apply j.1)
  have hfin : (Set.range Y).Finite := Set.toFinite _
  refine integrable_of_finiteRange_factor (μ := algorithmSampleLaw S)
    (Y := Y) (Z := Z) hY hfin ?_
  intro ω ω' hYeq
  refine hconst ?_
  intro j hj r
  have hjlt : j < n + 1 := Nat.lt_succ_of_le hj
  exact congrFun (congrFun hYeq ⟨j, hjlt⟩) r

/-- Hilbert-valued observables determined by a finite Algorithm 7.12 mini-batch
prefix are a.e.-strongly measurable under the canonical product sample law.

Search audit: `measurable_of_finite_range_fiber_const`,
`integrable_of_finiteRange_factor`, and
`integrable_algorithmSampleLaw_of_prefix_const` were considered.  The first two
require a target `MeasurableSpace E`, while this Lemma 7.4 route deliberately
avoids adding source-facing measurability assumptions on `E`; the proof instead
factors through a finite prefix key and uses
`StronglyMeasurable.of_discrete`. -/
private theorem aestronglyMeasurable_algorithmSampleLaw_of_prefix_const
    (S : Setup E) (n : ℕ) {Z : AlgorithmSamplePath S → E}
    (hconst :
      ∀ ⦃ω ω' : AlgorithmSamplePath S⦄,
        (∀ j : ℕ, j ≤ n → ∀ r : Fin S.b, ω j r = ω' j r) →
          Z ω = Z ω') :
    AEStronglyMeasurable Z (algorithmSampleLaw S) := by
  classical
  let Y : AlgorithmSamplePath S →
      (Fin (n + 1) → Fin S.b → Fin S.componentCount) :=
    fun ω j r => ω j.1 r
  let defaultComponent : Fin S.componentCount := ⟨0, S.hcomponentCount_pos⟩
  let extend : (Fin (n + 1) → Fin S.b → Fin S.componentCount) →
      AlgorithmSamplePath S :=
    fun y k r => if hk : k < n + 1 then y ⟨k, hk⟩ r else defaultComponent
  refine aestronglyMeasurable_of_countable_key_reconstruction
    (μ := algorithmSampleLaw S) (Y := Y) (Z := Z) ?_ (fun y => Z (extend y)) ?_
  · apply Measurable.aemeasurable
    dsimp [Y]
    refine measurable_pi_lambda _ ?_
    intro j
    refine measurable_pi_lambda _ ?_
    intro r
    exact (measurable_pi_apply r).comp (measurable_pi_apply j.1)
  · filter_upwards with ω
    exact hconst (ω := extend (Y ω)) (ω' := ω) (by
      intro j hj r
      have hjlt : j < n + 1 := Nat.lt_succ_of_le hj
      simp only [Y, extend, dif_pos hjlt])

/-- Transfer a fixed-fiber scalar integral bound with a random-prefix-dependent
right side through an independent random parameter.

Search audit: `integral_comp_le_of_indep_fixed_integral_bound` and
`integrable_comp_of_indep_fixed_integral_bound` were checked.  They cover the
uniform-bound case, but Lemma 7.4's diagonal estimator transfer needs the bound
`B w` depending on the finite strict-prefix key `w`; this helper is the
corresponding scalar product-law bridge. -/
private theorem integral_comp_le_integral_bound_of_indep_fixed_integral_bound
    {Ω W Smp : Type*} [MeasurableSpace Ω] [MeasurableSpace W] [MeasurableSpace Smp]
    {P : Measure Ω} {ν : Measure Smp} [IsProbabilityMeasure P] [IsProbabilityMeasure ν]
    {φ : W → Smp → ℝ} {B : W → ℝ} {X : Ω → W} {Y : Ω → Smp}
    (hφ : Measurable (Function.uncurry φ))
    (hB : Measurable B) (hX : Measurable X) (hY : Measurable Y)
    (h_indep : IndepFun X Y P)
    (h_dist : Measure.map Y P = ν)
    (h_int : Integrable (fun ω => φ (X ω) (Y ω)) P)
    (hB_int : Integrable (fun ω => B (X ω)) P)
    (hfixed_bound : ∀ w, ∫ s, φ w s ∂ν ≤ B w) :
    ∫ ω, φ (X ω) (Y ω) ∂P ≤ ∫ ω, B (X ω) ∂P := by
  exact
    _root_.integral_comp_le_integral_comp_bound_of_indep_fixed_integral_bound
      (P := P) (ν := ν) (φ := φ) (B := B) (X := X) (Y := Y)
      hφ hB hX hY h_indep h_dist h_int hB_int hfixed_bound

/-- Positive paper-time view of the generated iterates: `x_k` is the zero-based
state after `k - 1` completed outer steps.

This reuses `SOptLib.positiveTimeIterateView`, the canonical positive-time view
for zero-based generated processes. -/
def paperIterate (S : Setup E) {Ω : Type*}
    (run : ℕ → Ω → RunState E)
    (k : {k : ℕ // 1 ≤ k}) (ω : Ω) : E :=
  SOptLib.positiveTimeIterateView (iterate S run) k ω

/-- Positive paper-time estimator `G_k`, stored after the `k`th Algorithm 7.12
estimator update. -/
def paperEstimator (S : Setup E) {Ω : Type*}
    (run : ℕ → Ω → RunState E)
    (k : {k : ℕ // 1 ≤ k}) (ω : Ω) : E :=
  estimator S run k.1 ω

/-- The generated estimator refreshes exactly on the paper's one-based epoch
start condition. -/
theorem paperEstimator_refresh (S : Setup E) {Ω : Type*}
    (batch : ℕ → Fin S.b → Ω → Fin S.componentCount)
    (run : ℕ → Ω → RunState E) (hrun : runStateSpec S batch run)
    (k : {k : ℕ // 1 ≤ k}) (ω : Ω)
    (hk : SOptLib.stepOfIndex S.T k.1 = 1) :
    paperEstimator S run k ω = SOptLib.finiteUniformAverage S.componentGradient (paperIterate S run k ω) := by
  classical
  exact SOptLib.positiveTime_estimator_eq_target_of_refresh_step
    (run := run) (iterOf := RunState.current) (estOf := RunState.estimator)
    (target := SOptLib.finiteUniformAverage S.componentGradient)
    (paperIter := paperIterate S run) (paperEst := paperEstimator S run)
    (refreshStep := fun k => SOptLib.stepOfIndex S.T k = 1)
    (by
      intro k ω
      simp [paperIterate, iterate])
    (by
      intro k ω
      simp [paperEstimator, estimator])
    (by
      intro n ω hn
      have hstep := hrun.2 n ω
      dsimp [outerStepRel] at hstep
      rcases hstep with ⟨_hx, _hterm, hnext⟩
      have hest := congrArg RunState.estimator hnext
      have hn_zero : n % S.T = 0 := by
        simpa [SOptLib.stepOfIndex_eq_mod_add_one] using hn
      simpa [gradientEstimatorUpdate, SOptLib.stepOfIndex_eq_mod_add_one, hn_zero] using hest)
    k ω hk

/-- The first coordinate in a source epoch decodes to the one-based refresh
step under the canonical fixed-length epoch decoder. -/
private theorem refresh_predicate_holds_at_global_index_start
    {T s : ℕ} (hT : 0 < T) :
    SOptLib.stepOfIndex T (SOptLib.global_index T s 1) = 1 := by
  exact SOptLib.nat_stepOf_globalIndex_eq (T := T) (s := s) (j := 1)
    (by omega) (by omega)

/-- Feasibility of the one-based paper iterate induced by any run satisfying
`runStateSpec`.

Search audit: SOptLib's `iterateProcess_mem` applies to subtype-valued abstract
processes, while this file's public `runStateSpec` stores feasibility in the
outer-step relation. This route-local bridge unfolds that relation and reuses
`cndGUpdate_spec`, aligning with Algorithm 7.12's generated feasible iterates. -/
private theorem paperIterate_mem_of_runStateSpec (S : Setup E) {Ω : Type*}
    (batch : ℕ → Fin S.b → Ω → Fin S.componentCount)
    (run : ℕ → Ω → RunState E) (hrun : runStateSpec S batch run)
    (k : {k : ℕ // 1 ≤ k}) (ω : Ω) :
    paperIterate S run k ω ∈ S.X := by
  classical
  have hprocess :
      SOptLib.IsRelationalRecursiveProcess (initialState S)
        (fun n prev next omega =>
          outerStepRel S (n + 1) (fun r => batch (n + 1) r omega) prev next)
        run := by
    constructor
    · exact hrun.1
    · exact hrun.2
  have hmem : ∀ n : ℕ, iterate S run n ω ∈ S.X := by
    intro n
    simpa [iterate] using
      SOptLib.IsRelationalRecursiveProcess.invariant_mem
        (X := S.X) (value := RunState.current) hprocess
        (by simpa [initialState] using S.hx₁_mem)
        (by
          intro _k prev _next _omega hstep hx
          dsimp [outerStepRel] at hstep
          rcases hstep with ⟨_hprev, hterm, hnext⟩
          have hc := congrArg RunState.current hnext
          have hcg := (cndGUpdate_spec S _ _ hx hterm).1
          simpa using hc.symm ▸ hcg)
        n ω
  simpa [paperIterate, SOptLib.positiveTimeIterateView_eq] using hmem (k.1 - 1)

/-- A positive paper-time outer step is exactly the CndG update driven by the
paper estimator `G_k` at the paper iterate `x_k`.

Search audit: `runState_succ` exposes the raw outer-step relation and
`cndGUpdate_spec` exposes the variational inequality after the update; no
existing helper specialized the one-based `paperIterate`/`paperEstimator` view,
so this bridge performs only the indexing rewrite needed for Theorem 7.18's
one-step descent route. -/
private theorem paper_iterate_next_eq_cndGUpdate (S : Setup E)
    (run : ℕ → AlgorithmSamplePath S → RunState E)
    (hrun : runStateSpec S (algorithmBatchStream S) run)
    (k : ℕ) (hk : 1 ≤ k) (ω : AlgorithmSamplePath S) :
    ∃ hterm :
        paperCndGTerminates S
          (paperEstimator S run ⟨k, hk⟩ ω)
          (paperIterate S run ⟨k, hk⟩ ω),
      iterate S run k ω =
        cndGUpdate S
          (paperEstimator S run ⟨k, hk⟩ ω)
          (paperIterate S run ⟨k, hk⟩ ω) hterm := by
  classical
  have hidx : (k - 1) + 1 = k := Nat.sub_add_cancel hk
  have hstep := hrun.2 (k - 1) ω
  rw [hidx] at hstep
  dsimp [outerStepRel, algorithmBatchStream] at hstep
  rcases hstep with ⟨_hx, hterm, hnext⟩
  have hcurrent := congrArg RunState.current hnext
  have hestimator := congrArg RunState.estimator hnext
  have hpaper :
      paperIterate S run ⟨k, hk⟩ ω = (run (k - 1) ω).current := by
    simp [paperIterate, iterate, SOptLib.positiveTimeIterateView_eq]
  have hG :
      paperEstimator S run ⟨k, hk⟩ ω =
        gradientEstimatorUpdate S k (run (k - 1) ω).previous
          (run (k - 1) ω).current (run (k - 1) ω).estimator
          (fun r => ω k r) := by
    simpa [paperEstimator, estimator] using hestimator
  refine ⟨by simpa [hG, hpaper] using hterm, ?_⟩
  simpa [iterate, hG, hpaper] using hcurrent

/-- The paper-time CndG output satisfies the variational inequality (7.5.7).

This consumes the `hrun` step identity and `cndGUpdate_spec`; it is the
one-based form needed by Theorem 7.18's descent and projected-gradient
comparison steps. -/
private theorem paper_cndGUpdateSpec_at_step (S : Setup E)
    (run : ℕ → AlgorithmSamplePath S → RunState E)
    (hrun : runStateSpec S (algorithmBatchStream S) run)
    (k : ℕ) (hk : 1 ≤ k) (ω : AlgorithmSamplePath S) :
    cndGUpdateSpec S
      (paperEstimator S run ⟨k, hk⟩ ω)
      (paperIterate S run ⟨k, hk⟩ ω)
      S.gamma S.eta
      (iterate S run k ω) := by
  classical
  rcases paper_iterate_next_eq_cndGUpdate S run hrun k hk ω with ⟨hterm, hnext⟩
  have hx :
      paperIterate S run ⟨k, hk⟩ ω ∈ S.X :=
    paperIterate_mem_of_runStateSpec S (algorithmBatchStream S) run hrun ⟨k, hk⟩ ω
  have hspec :=
    cndGUpdate_spec S
      (paperEstimator S run ⟨k, hk⟩ ω)
      (paperIterate S run ⟨k, hk⟩ ω) hx hterm
  simpa [hnext] using hspec

/-- Estimator error `delta_k = G_k - nabla f(x_k)`. -/
def estimatorError (S : Setup E) {Ω : Type*}
    (run : ℕ → Ω → RunState E) (k : ℕ) (ω : Ω) : E :=
  estimator S run k ω - SOptLib.finiteUniformAverage S.componentGradient (iterate S run k ω)

/-- Exact projected-gradient certificate at a generated iterate. -/
def iterateProjectedGradient (S : Setup E) {Ω : Type*}
    (run : ℕ → Ω → RunState E) (k : ℕ) (ω : Ω) : E :=
  exactProjectedGradient S (iterate S run k ω)

/-- Expected squared projected-gradient certificate at generated iterate `k`. -/
def expectedSquaredProjectedGradient (S : Setup E) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (run : ℕ → Ω → RunState E) (k : ℕ) : ℝ :=
  ∫ ω, ‖iterateProjectedGradient S run k ω‖ ^ 2 ∂P

/-- Theorem 7.18 projected-gradient certificate at one-based paper time `k`, so
`k = 1` evaluates the initial iterate `x_1`.

The source proof of Theorem 7.18 defines
`g_X,k = (x_k - xhat_{k+1}) / gamma`, where `xhat` is the Euclidean quadratic
projected point.  The general Bregman certificate remains available as
`exactProjectedGradient`; this paper-time aggregate follows the Euclidean route
used in Eqs. (7.5.11)--(7.5.13). -/
def paperProjectedGradient (S : Setup E) {Ω : Type*}
    (run : ℕ → Ω → RunState E) (k : ℕ) (ω : Ω) : E :=
  euclideanProjectedGradient S (iterate S run (k - 1) ω)

/-- Expected squared projected-gradient certificate at one-based paper time `k`. -/
def expectedSquaredPaperProjectedGradient (S : Setup E) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (run : ℕ → Ω → RunState E) (k : ℕ) : ℝ :=
  ∫ ω, ‖paperProjectedGradient S run k ω‖ ^ 2 ∂P

/-- Expected squared projected-gradient certificate for the canonical Algorithm
7.12 sample law, at one-based paper time `k`. -/
def algorithmExpectedSquaredPaperProjectedGradient (S : Setup E)
    (run : ℕ → AlgorithmSamplePath S → RunState E) (k : ℕ) : ℝ :=
  expectedSquaredPaperProjectedGradient S
    (algorithmSampleLaw S) run k

/-- Diameter value `Dbar_X = max_{x,y in X} ||x-y||`, Eq. (7.1.18).

This reuses `SOptLib.compactNormDiameter`, whose signature exactly supplies an
attained scalar norm diameter from a nonempty compact feasible set; this replaces
the earlier `sSup` encoding that did not expose maximum attainment. -/
def DbarX (S : Setup E) : ℝ :=
  Classical.choose (SOptLib.compactNormDiameter S.X ⟨S.x₁, S.hx₁_mem⟩ S.hX_compact)

/-- The selected diameter is attained by feasible points and bounds every
feasible pair. -/
theorem DbarX_spec (S : Setup E) :
    ∃ x ∈ S.X, ∃ y ∈ S.X,
      DbarX S = ‖x - y‖ ∧ ∀ a ∈ S.X, ∀ b ∈ S.X, ‖a - b‖ ≤ DbarX S := by
  simpa [DbarX] using
    Classical.choose_spec (SOptLib.compactNormDiameter S.X ⟨S.x₁, S.hx₁_mem⟩ S.hX_compact)

/-- Output window `{1, ..., N}` from Algorithm 7.12. -/
def outputWindow (S : Setup E) : Finset ℕ :=
  Finset.Icc 1 S.N

/-- Output denominator `sum_{k=1}^N alpha_k`, reused from SOptLib's finite
output-weight denominator. -/
def outputDenominator (S : Setup E) : ℝ :=
  SOptLib.outputWeightDenominator (outputWindow S) S.alpha

/-- Randomized output mass `Prob{R=k}=alpha_k/sum_{j=1}^N alpha_j` from
Algorithm 7.12.

This reuses `SOptLib.normalizedOutputMass`, which is exactly the finite
weight-normalization primitive for randomized output. -/
def outputMass (S : Setup E) (k : ℕ) : ℝ :=
  SOptLib.normalizedOutputMass S.alpha (outputDenominator S) k

/-- The output mass unfolds to the paper's displayed ratio. -/
theorem outputMass_eq (S : Setup E) (k : ℕ) :
    outputMass S k = S.alpha k / Finset.sum (Finset.Icc 1 S.N) S.alpha := by
  rfl

/-- Positivity of the output denominator is a proof obligation from the
paper's positive output weights, not a setup field in this file. -/
theorem outputDenominator_pos (S : Setup E)
    (halpha_pos : ∀ k ∈ outputWindow S, 0 < S.alpha k) :
    0 < outputDenominator S := by
  have hnonempty : (outputWindow S).Nonempty := by
    refine ⟨1, ?_⟩
    simp [outputWindow, Nat.succ_le_iff, S.hN_pos]
  simpa [outputDenominator, outputWindow] using
    SOptLib.outputWeightDenominator_pos (Finset.Icc 1 S.N) S.alpha
      (by simpa [outputWindow] using halpha_pos) hnonempty

/-- If the output denominator is nonzero, the output masses sum to one. -/
theorem outputMass_sum_one (S : Setup E) (hdenom_ne : outputDenominator S ≠ 0) :
    Finset.sum (outputWindow S) (outputMass S) = 1 := by
  simpa [outputMass, outputDenominator] using
    SOptLib.normalizedOutputMass_sum_one
      (times := outputWindow S) (weight := S.alpha) (denom := outputDenominator S)
      rfl hdenom_ne

/-- Source specification for Algorithm 7.12's random index `R`.

The paper output line states an actual probability law
`Prob{R = k} = alpha_k / sum alpha_k`; this Prop records the pointwise PMF mass
for internal realizations when the displayed weights have already been proved
admissible. -/
def outputIndexLawSpec (S : Setup E) (p : PMF {k : ℕ // k ∈ outputWindow S}) : Prop :=
  SOptLib.FiniteWindowPMFSpec (outputWindow S) S.alpha p

/-- Admissibility of Algorithm 7.12's displayed output probabilities, useful for
internal bridges to reusable normalized-weight APIs.

The PDF prints the ratio `alpha_k / sum alpha_k` as a probability law but does
not separately state these well-definedness conditions.  They therefore remain
an internal bridge, not a field on `Setup` and not a hypothesis of the
paper-named Theorem 7.18 below. -/
def outputWeightsAdmissible (S : Setup E) : Prop :=
  SOptLib.FiniteWindowWeightsAdmissible (outputWindow S) S.alpha

/-- Internal bridge: under the usual positivity side conditions, Algorithm 7.12's
displayed masses are nonnegative and normalized, hence can be realized as a
probability law.

The PDF prints `Prob{R=k}=alpha_k/sum alpha_k`, but does not restate the
positivity/denominator side conditions in the Algorithm 7.12 output line.  This
bridge is therefore kept separate from Theorem 7.18 rather than smuggled into its
theorem head. -/
theorem algorithmOutputMasses_probability_bridge (S : Setup E)
    (halpha_nonneg : ∀ k ∈ outputWindow S, 0 ≤ S.alpha k)
    (hdenom_pos : 0 < outputDenominator S) :
    (∀ k ∈ outputWindow S, 0 ≤ outputMass S k) ∧
      Finset.sum (outputWindow S) (outputMass S) = 1 := by
  refine ⟨?_, outputMass_sum_one S (ne_of_gt hdenom_pos)⟩
  intro k hk
  exact SOptLib.normalizedOutputMass_nonneg (outputWindow S) S.alpha
    (outputDenominator S) k hk halpha_nonneg (le_of_lt hdenom_pos)

/-- Internal normalized-weight realization of Algorithm 7.12's output law.

This reuses `SOptLib.normalizedFiniteWindowPMF`, the canonical finite-window PMF
constructor for normalized real weights, when the displayed alpha weights have
already been proved admissible. -/
def outputIndexPMFOfAdmissible (S : Setup E) (hα : outputWeightsAdmissible S) :
    PMF {k : ℕ // k ∈ outputWindow S} :=
  SOptLib.normalizedFiniteWindowPMF
    (outputWindow S) S.alpha hα.1 hα.2

/-- The output PMF assigns the paper's displayed normalized mass to each
one-based output index under an explicit admissibility proof. -/
theorem outputIndexPMFOfAdmissible_apply
    (S : Setup E) (hα : outputWeightsAdmissible S)
    (R : {k : ℕ // k ∈ outputWindow S}) :
    outputIndexPMFOfAdmissible S hα R =
      ENNReal.ofReal (S.alpha R.1 / Finset.sum (outputWindow S) S.alpha) := by
  simp [outputIndexPMFOfAdmissible]

/-- The admissible-weight PMF realizes Algorithm 7.12's displayed output-index
law. -/
theorem outputIndexLawSpec_of_admissible
    (S : Setup E) (hα : outputWeightsAdmissible S) :
    outputIndexLawSpec S (outputIndexPMFOfAdmissible S hα) := by
  exact SOptLib.finiteWindowPMFSpec_of_normalizedFiniteWindowPMF
    (times := outputWindow S) (weight := S.alpha) hα

/-- Coerce an output-window index to the positive paper-time index expected by
`paperIterate`. -/
def outputIndexPositive (S : Setup E) (R : {k : ℕ // k ∈ outputWindow S}) :
    {k : ℕ // 1 ≤ k} :=
  ⟨R.1, (Finset.mem_Icc.mp
    (show R.1 ∈ Finset.Icc 1 S.N from by
      simpa only [outputWindow] using R.2)).1⟩

/-- Canonical B-track uniform selected-output law over the full paper window
`S = {1, ..., N}`.

This is the corrected release law used with the proof-supported unweighted
Theorem 7.18 aggregate.  It keeps the full one-based `outputWindow S` and gives
each selected index mass `1 / N`. -/
def uniformOutputIndexPMF (S : Setup E) : PMF {k : ℕ // k ∈ outputWindow S} :=
  SOptLib.normalizedFiniteWindowPMF
    (outputWindow S) (fun _ : ℕ => (1 : ℝ))
    (by intro k hk; norm_num)
    (by
      have hNpos : 0 < (S.N : ℝ) := Nat.cast_pos.mpr S.hN_pos
      simpa [outputWindow, Nat.succ_le_iff, S.hN_pos] using hNpos)

/-- The canonical uniform output PMF has constant atom mass `1 / N` over the
full one-based output window. -/
theorem uniformOutputIndexPMF_apply
    (S : Setup E) (R : {k : ℕ // k ∈ outputWindow S}) :
    uniformOutputIndexPMF S R = ENNReal.ofReal (1 / (S.N : ℝ)) := by
  have hsum :
      Finset.sum (outputWindow S) (fun _ : ℕ => (1 : ℝ)) = (S.N : ℝ) := by
    simp [outputWindow, Nat.succ_le_iff, S.hN_pos]
  simp [uniformOutputIndexPMF, hsum]

/-- Joint law of the randomized output index and the Algorithm 7.12 sample path,
under an explicit proof that the displayed alpha weights are admissible.

The paper prints `Prob{R=k}=alpha_k/sum alpha_k` but does not state
nonnegativity or positive-denominator conditions for arbitrary `{alpha_k}`.
Accordingly this is an admissible-weight realization, not an unconditional
source-facing PMF selected by existence. -/
def randomOutputLawOfAdmissible (S : Setup E) (hα : outputWeightsAdmissible S) :
    Measure ({k : ℕ // k ∈ outputWindow S} × AlgorithmSamplePath S) :=
  SOptLib.selected_joint_measure (outputIndexPMFOfAdmissible S hα) (algorithmSampleLaw S)

/-- Joint law of the corrected uniform selected output and the Algorithm 7.12
sample path. -/
def uniformRandomOutputLaw (S : Setup E) :
    Measure ({k : ℕ // k ∈ outputWindow S} × AlgorithmSamplePath S) :=
  SOptLib.selected_joint_measure (uniformOutputIndexPMF S) (algorithmSampleLaw S)

/-- Joint law of a realization of Algorithm 7.12's random output index and the
canonical sample path.

The output-index PMF is supplied as an object satisfying `outputIndexLawSpec`,
which is the same interface used by admissible-weight internal realizations. -/
def randomOutputLaw (S : Setup E) (p : PMF {k : ℕ // k ∈ outputWindow S}) :
    Measure ({k : ℕ // k ∈ outputWindow S} × AlgorithmSamplePath S) :=
  SOptLib.selected_joint_measure p (algorithmSampleLaw S)

/-- The actual random output `x_R` from Algorithm 7.12. -/
def randomOutput (S : Setup E)
    (run : ℕ → AlgorithmSamplePath S → RunState E)
    (q : {k : ℕ // k ∈ outputWindow S} × AlgorithmSamplePath S) : E :=
  paperIterate S run (outputIndexPositive S q.1) q.2

/-- Projected-gradient certificate evaluated at the genuine random output. -/
def randomOutputProjectedGradient (S : Setup E)
    (run : ℕ → AlgorithmSamplePath S → RunState E)
    (q : {k : ℕ // k ∈ outputWindow S} × AlgorithmSamplePath S) : E :=
  exactProjectedGradient S (randomOutput S run q)

/-- Expected squared projected-gradient certificate of the actual Algorithm 7.12
random output `x_R`.

Candidates considered: `SOptLib.finiteWindowSelectedOutputExpectation_eq_weighted_sum`
and `SOptLib.expectedSelectedOutput_eq_inv_mul_Icc_weighted_sum` are expansion
theorems for an already-constructed selected-output law.  The paper object here
is the selected-output expectation itself, so this definition uses the canonical
Algorithm 7.12 run and a PMF satisfying `outputIndexLawSpec`.  The PMF is
supplied explicitly because the source prints the ratio
`alpha_k / sum alpha_k` but does not state arbitrary-alpha admissibility. -/
private def paperExpectedRandomOutputSquaredProjectedGradient (S : Setup E)
    (run : ℕ → AlgorithmSamplePath S → RunState E)
    (p : PMF {k : ℕ // k ∈ outputWindow S}) : ℝ :=
  ∫ q, ‖randomOutputProjectedGradient S run q‖ ^ 2 ∂randomOutputLaw S p

/-- Expected projected-gradient norm of the actual Algorithm 7.12 random output
`x_R`, matching Corollary 7.13's solution criterion. -/
private def paperExpectedRandomOutputProjectedGradientNorm (S : Setup E)
    (run : ℕ → AlgorithmSamplePath S → RunState E)
    (p : PMF {k : ℕ // k ∈ outputWindow S}) : ℝ :=
  ∫ q, ‖randomOutputProjectedGradient S run q‖ ∂randomOutputLaw S p

/-- Feasibility of a realized Algorithm 7.12 random output.

The paper's corollary asks for `xbar in X`; for the random-output realization,
this is derived from feasibility of the generated CndG iterates, not assumed as
a setup field. -/
theorem randomOutput_mem_of_runStateSpec (S : Setup E)
    (run : ℕ → AlgorithmSamplePath S → RunState E)
    (hrun : runStateSpec S (algorithmBatchStream S) run) :
    ∀ q : {k : ℕ // k ∈ outputWindow S} × AlgorithmSamplePath S,
      randomOutput S run q ∈ S.X := by
  classical
  have hmem : ∀ k ω, iterate S run k ω ∈ S.X := by
    intro k
    induction k with
    | zero =>
        intro ω
        have h0 := hrun.1 ω
        have hc := congrArg RunState.current h0
        simpa [iterate, initialState] using hc.symm ▸ S.hx₁_mem
    | succ k ih =>
        intro ω
        have hstep := hrun.2 k ω
        dsimp [outerStepRel] at hstep
        rcases hstep with ⟨hx, hterm, hnext⟩
        have hc := congrArg RunState.current hnext
        have hcg := (cndGUpdate_spec S _ _ hx hterm).1
        simpa [iterate] using hc.symm ▸ hcg
  intro q
  simpa [randomOutput, paperIterate, SOptLib.positiveTimeIterateView_eq] using
    hmem ((outputIndexPositive S q.1).1 - 1) q.2

/-- Expected squared projected-gradient certificate of Algorithm 7.12's random
output `x_R` under an admissible realization of the displayed output-index
law. -/
private def expectedRandomOutputSquaredProjectedGradientOfAdmissible (S : Setup E)
    (hα : outputWeightsAdmissible S)
    (run : ℕ → AlgorithmSamplePath S → RunState E) : ℝ :=
  ∫ q, ‖randomOutputProjectedGradient S run q‖ ^ 2 ∂randomOutputLawOfAdmissible S hα

/-- Expected projected-gradient norm of Algorithm 7.12's random output under the
displayed output-index law, realized only after alpha admissibility is proved. -/
private def expectedRandomOutputProjectedGradientNormOfAdmissible (S : Setup E)
    (hα : outputWeightsAdmissible S)
    (run : ℕ → AlgorithmSamplePath S → RunState E) : ℝ :=
  ∫ q, ‖randomOutputProjectedGradient S run q‖ ∂randomOutputLawOfAdmissible S hα

/-- Expected squared projected-gradient certificate of Algorithm 7.12's random
output `x_R` under admissible alpha weights and positive CndG tolerance.

This is an internal realization of the displayed random output law.  It is not
used as the paper-facing Theorem 7.18 object because the source does not state
arbitrary-alpha nonnegativity or a positive denominator, and the proof derives
an unweighted sum before invoking `R`. -/
private def expectedAlgorithmRandomOutputSquaredProjectedGradientOfAdmissibleEtaPos
    (S : Setup E) (hα : outputWeightsAdmissible S) (hη : 0 < S.eta) : ℝ :=
  ∫ q, ‖randomOutputProjectedGradient S (algorithmRunOfEtaPos S hη) q‖ ^ 2
    ∂randomOutputLawOfAdmissible S hα

/-- Expected projected-gradient norm of Algorithm 7.12's random output under an
admissible alpha-law realization and positive CndG tolerance. -/
private def expectedAlgorithmRandomOutputProjectedGradientNormOfAdmissibleEtaPos
    (S : Setup E) (hα : outputWeightsAdmissible S) (hη : 0 < S.eta) : ℝ :=
  ∫ q, ‖randomOutputProjectedGradient S (algorithmRunOfEtaPos S hη) q‖
    ∂randomOutputLawOfAdmissible S hα

/-- Corrected B-track selected-output certificate for the generated Algorithm
7.12 run under the canonical uniform selected-output law.

The integrand is the squared `paperProjectedGradient` certificate, not the
`randomOutputProjectedGradient`/`exactProjectedGradient` certificate. -/
def expectedUniformRandomOutputSquaredPaperProjectedGradient
    (S : Setup E) (hη : 0 < S.eta) : ℝ :=
  ∫ q : {k : ℕ // k ∈ outputWindow S} × AlgorithmSamplePath S,
    ‖paperProjectedGradient S (algorithmRunOfEtaPos S hη) q.1.1 q.2‖ ^ 2
      ∂uniformRandomOutputLaw S

/-- Expected squared projected-gradient certificate at a realized paper random
output `x_R` from Algorithm 7.12.

Candidates considered: `SOptLib.normalizedWeightedExpectedCertificate` and
`expectedSelectedOutput_eq_inv_mul_Icc_weighted_sum` are expansion theorems for a
supplied law.  This realization-parameterized form is retained as an internal
expansion object; the source-boundary record below uses
`paperExpectedRandomOutputSquaredProjectedGradient` over a realized run and a
PMF satisfying `outputIndexLawSpec`. -/
private def expectedAlgorithmRandomOutputSquaredProjectedGradient (S : Setup E)
    (run : ℕ → AlgorithmSamplePath S → RunState E)
    (p : PMF {k : ℕ // k ∈ outputWindow S}) : ℝ :=
  ∫ q, ‖randomOutputProjectedGradient S run q‖ ^ 2 ∂randomOutputLaw S p

/-- Expected projected-gradient norm at a realized paper random output `x_R`,
matching Corollary 7.13's criterion `E[g_X(xbar)] <= epsilon`.

This realization-parameterized form is an internal expansion object; the
paper-facing corollary criterion below is stated over
`paperExpectedRandomOutputProjectedGradientNorm`, not over a hidden selected run
or arbitrary-alpha PMF. -/
private def expectedAlgorithmRandomOutputProjectedGradientNorm (S : Setup E)
    (run : ℕ → AlgorithmSamplePath S → RunState E)
    (p : PMF {k : ℕ // k ∈ outputWindow S}) : ℝ :=
  ∫ q, ‖randomOutputProjectedGradient S run q‖ ∂randomOutputLaw S p

/-- Expected squared projected-gradient certificate at the randomized output
distribution displayed in Algorithm 7.12, written as the raw normalized finite
sum.

The PMF expectation is
`expectedRandomOutputSquaredProjectedGradientOfAdmissible`; this scalar
expression is kept as an internal algebraic expansion target for admissible
weights and is no longer used as the paper-facing random-output criterion. -/
private def expectedOutputSquaredProjectedGradient (S : Setup E) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (run : ℕ → Ω → RunState E) : ℝ :=
  Finset.sum (outputWindow S)
    (fun k => outputMass S k * expectedSquaredPaperProjectedGradient S P run k)

/-- Expected projected-gradient norm at the randomized output distribution in the
Corollary 7.13 criterion `E[g_X(xbar)] <= epsilon`. -/
private def expectedOutputProjectedGradientNorm (S : Setup E) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (run : ℕ → Ω → RunState E) : ℝ :=
  Finset.sum (outputWindow S)
    (fun k =>
      outputMass S k *
        ∫ ω, ‖paperProjectedGradient S run k ω‖ ∂P)

/-- Algorithm 7.12 alpha-weighted randomized-output squared certificate for the
canonical sample law.

This is the actual PMF expectation over the random output `x_R`, but only after
the alpha weights have been shown to define the printed probability law. -/
private def algorithm712RandomOutputSquaredProjectedGradientOfAdmissible (S : Setup E)
    (hα : outputWeightsAdmissible S)
    (run : ℕ → AlgorithmSamplePath S → RunState E) : ℝ :=
  expectedRandomOutputSquaredProjectedGradientOfAdmissible S hα run

/-- Unweighted average of the first `N` one-based projected-gradient certificates.

Candidates considered: `SOptLib.finiteUniformAverage` averages over `Finset.univ`
of a `Fintype`, while Theorem 7.18's proof uses the literal one-based
`(1/N) sum_{k=1}^N` expression from Eq. (7.5.13).  This local definition keeps
that interval average visible and avoids replacing the theorem by the
Algorithm 7.12 alpha-weighted output law. -/
def theorem718AverageSquaredProjectedGradient (S : Setup E)
    (run : ℕ → AlgorithmSamplePath S → RunState E) : ℝ :=
  (S.N : ℝ)⁻¹ *
    Finset.sum (outputWindow S)
      (fun k => algorithmExpectedSquaredPaperProjectedGradient S run k)

/-- Internal unweighted average projected-gradient norm over the first `N` paper
iterates.

Candidates considered: the selected-output expectation lemmas in
`SOptLib.Model.Selection` expand a supplied PMF law, but the source proof of
Theorem 7.18 sums the first `N` inequalities and does not derive the
arbitrary-alpha bridge.  This local definition keeps the unweighted
proof-supported aggregate explicit without replacing the paper random-output
criterion. -/
def theorem718AverageProjectedGradientNorm (S : Setup E)
    (run : ℕ → AlgorithmSamplePath S → RunState E) : ℝ :=
  (S.N : ℝ)⁻¹ *
    Finset.sum (outputWindow S)
      (fun k =>
        ∫ ω, ‖paperProjectedGradient S run k ω‖ ∂algorithmSampleLaw S)

/-- One-step smooth descent after the CndG approximate optimality step and
Young absorption of the estimator error.

This is Lan Theorem 7.18 proof steps 2--6 / Eq. (7.5.10) in local notation.
Candidates considered: `paper_cndGUpdateSpec_at_step` supplies the source
Eq. (7.5.7) CndG inequality and
`finiteUniformAverage_smooth_quadratic_upper_bound` supplies the source
smoothness step; no SOptLib descent theorem packages this file's
`runStateSpec` indexing, paper-time estimator, and CndG update together. -/
private theorem theorem718_cndg_smooth_descent_with_estimator_error (S : Setup E)
    (run : ℕ → AlgorithmSamplePath S → RunState E)
    (hrun : runStateSpec S (algorithmBatchStream S) run)
    {k : ℕ} (hk : 1 ≤ k) (ω : AlgorithmSamplePath S) {q : ℝ} (hq : 0 < q) :
    SOptLib.finiteUniformAverage S.componentObjective (iterate S run k ω) ≤
      SOptLib.finiteUniformAverage S.componentObjective (paperIterate S run ⟨k, hk⟩ ω) -
        (S.gamma⁻¹ - S.L / 2 - q / 2) *
          ‖iterate S run k ω - paperIterate S run ⟨k, hk⟩ ω‖ ^ 2 +
        (1 / (2 * q)) *
          ‖paperEstimator S run ⟨k, hk⟩ ω -
            SOptLib.finiteUniformAverage S.componentGradient (paperIterate S run ⟨k, hk⟩ ω)‖ ^ 2 +
        S.eta := by
  classical
  let x : E := paperIterate S run ⟨k, hk⟩ ω
  let y : E := iterate S run k ω
  let G : E := paperEstimator S run ⟨k, hk⟩ ω
  have hx : x ∈ S.X := by
    simpa [x] using
      paperIterate_mem_of_runStateSpec S (algorithmBatchStream S) run hrun ⟨k, hk⟩ ω
  have hspec : cndGUpdateSpec S G x S.gamma S.eta y := by
    simpa [x, y, G] using paper_cndGUpdateSpec_at_step S run hrun k hk ω
  have hy : y ∈ S.X := hspec.1
  have hsmooth :
      SOptLib.finiteUniformAverage S.componentObjective y ≤
        SOptLib.finiteUniformAverage S.componentObjective x + ⟪SOptLib.finiteUniformAverage S.componentGradient x, y - x⟫_ℝ +
          (S.L / 2) * ‖y - x‖ ^ 2 :=
    finiteUniformAverage_smooth_quadratic_upper_bound S hx hy
  have hproj_raw := hspec.2 x hx
  have hproj :
      ⟪G, y - x⟫_ℝ ≤ S.eta - S.gamma⁻¹ * ‖y - x‖ ^ 2 := by
    have hsplit :
        ⟪G + S.gamma⁻¹ • (y - x), y - x⟫_ℝ =
          ⟪G, y - x⟫_ℝ + S.gamma⁻¹ * ‖y - x‖ ^ 2 := by
      simp [inner_add_left, inner_smul_left]
    nlinarith [hproj_raw, hsplit]
  simpa [x, y, G, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    (smooth_descent_of_approx_variational_step_with_estimator_error
      (SOptLib.finiteUniformAverage S.componentObjective)
      (SOptLib.finiteUniformAverage S.componentGradient)
      x y G S.gamma S.eta S.L q hq hsmooth hproj)

/-- The distance-generating assumption gives one-strong monotonicity of the
selected prox gradient on the feasible set.

This is the reusable Bregman-side premise needed for Lan Theorem 7.18's
post-(7.5.11) projected-gradient comparison. Candidates considered:
`SOptLib.sq_norm_le_inner_gradient_sub_of_strong_distance_generator` assumes an
already packaged strong-monotonicity hypothesis, while the staged
`SOptLib.sq_norm_le_inner_gradient_sub_of_dgf_half_sq_bregman` derives that
premise directly from `S.hprox_dgf`. -/
private theorem theorem718_proxGradient_strong_monotone_on_X (S : Setup E)
    {u v : E} (hu : u ∈ S.X) (hv : v ∈ S.X) :
    ‖u - v‖ ^ 2 ≤ ⟪u - v, S.proxGradient u - S.proxGradient v⟫_ℝ := by
  exact SOptLib.sq_norm_le_inner_gradient_sub_of_dgf_half_sq_bregman
    S.hprox_dgf hu hv

/-- Eq. (7.5.11): the approximate CndG output is close to the exact minimizer
of the stochastic Euclidean quadratic model.

This is Lan Theorem 7.18 proof step 8. Candidates considered:
`cndg_gap_ge_quadratic_residual` controls the same quadratic residual through a
selected Wolfe gap, while the present source step uses the already available
paper-time variational inequality `cndGUpdateSpec` at the exact model minimizer;
therefore the proof below specializes the local quadratic minimizer certificate
directly. -/
private theorem theorem718_cndg_output_to_model_minimizer_distance (S : Setup E)
    {G x y zbar : E} {gamma eta : ℝ}
    (hgamma_pos : 0 < gamma)
    (hspec : cndGUpdateSpec S G x gamma eta y)
    (hzbar_mem : zbar ∈ S.X)
    (hzbar_min : ∀ z : E, z ∈ S.X →
      ⟪G, zbar⟫_ℝ + gamma⁻¹ / 2 * ‖zbar - x‖ ^ 2 ≤
        ⟪G, z⟫_ℝ + gamma⁻¹ / 2 * ‖z - x‖ ^ 2) :
    (1 / (2 * gamma)) * ‖y - zbar‖ ^ 2 ≤ eta := by
  exact
    SOptLib.conditional_gradient_output_dist_model_minimizer_le_of_variational
      (X := S.X) (G := G) (x := x) (y := y) (zbar := zbar)
      (gamma := gamma) (eta := eta) hgamma_pos hspec.1 hzbar_mem
      hspec.2 hzbar_min

/-- Variational inequality for the Bregman projected point in Eq. (7.5.2).

This is the source-facing optimality bridge needed before Lan Theorem 7.18's
projected-gradient comparison. It aligns the local `projectedPoint_spec` with
the SOptLib segment-derivative prox VI route; candidates considered:
`prox_variational_inequality_of_isMinOn_linear_bregman` is the canonical subtype
form but asks for a `fderivWithin` identity on `X`, while
`bregman_segment_difference_hasDerivWithinAt_zero`,
`prox_majorant_hasDerivWithinAt_zero`, and
`prox_scaled_variational_inequality_of_argmin` exactly use the ambient
`HasGradientAt` supplied by `S.hprox_dgf` along feasible segments. -/
private theorem projectedPoint_variational_inequality_on_X (S : Setup E)
    {x g v : E} {gamma : ℝ} (hgamma : 0 < gamma)
    (hx : x ∈ S.X) (hv : v ∈ S.X) :
    let p : E := projectedPoint S x g gamma
    0 ≤ ⟪g + gamma⁻¹ • (S.proxGradient p - S.proxGradient x), v - p⟫_ℝ := by
  classical
  let p : E := projectedPoint S x g gamma
  have hp : p ∈ S.X := by
    simpa [p] using (projectedPoint_spec S x g gamma).1
  let d : E := v - p
  let beta : ℝ → ℝ := fun t =>
    if _ht : t ∈ Set.Icc (0 : ℝ) 1 then
      carrierBregmanFormula S.proxFunction id S.proxGradient x
          (AffineMap.lineMap p v t) -
        carrierBregmanFormula S.proxFunction id S.proxGradient x p
    else 0
  let phi : ℝ → ℝ := fun t =>
    gamma * t * ⟪g, d⟫_ℝ + beta t + gamma * t * 0
  have hbeta_deriv :
      HasDerivWithinAt beta
        ⟪S.proxGradient p - S.proxGradient x, d⟫_ℝ
        (Set.Icc (0 : ℝ) 1) 0 := by
    have hgrad_p : HasGradientAt S.proxFunction (S.proxGradient p) p :=
      S.hprox_dgf.2.1 p hp
    simpa [beta, d] using
      (bregman_segment_difference_hasDerivWithinAt_zero
        S.proxFunction S.proxGradient (x := x) (xp := p) (u := v) hgrad_p)
  have hphi_deriv :
      HasDerivWithinAt phi
        (gamma * ⟪g, v - p⟫_ℝ +
          ⟪S.proxGradient p - S.proxGradient x, v - p⟫_ℝ +
          gamma * ((fun _ : E => (0 : ℝ)) v - (fun _ : E => (0 : ℝ)) p))
        (Set.Icc (0 : ℝ) 1) 0 := by
    simpa [phi, d] using
      (prox_majorant_hasDerivWithinAt_zero beta g d
        (S.proxGradient p - S.proxGradient x) gamma 0 hbeta_deriv)
  have hphi_zero : phi 0 = 0 := by
    simp [phi, beta]
  have hphi_nonneg : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ phi t := by
    intro t ht
    have hline_mem : AffineMap.lineMap p v t ∈ S.X :=
      S.hX_convex.lineMap_mem hp hv ht
    have hmin :
        projectedPointModelValue S x g gamma p ≤
          projectedPointModelValue S x g gamma (AffineMap.lineMap p v t) := by
      simpa [p] using
        (projectedPoint_spec S x g gamma).2 (AffineMap.lineMap p v t) hline_mem
    have hscaled :
        0 ≤ gamma *
          (projectedPointModelValue S x g gamma (AffineMap.lineMap p v t) -
            projectedPointModelValue S x g gamma p) := by
      exact mul_nonneg (le_of_lt hgamma) (sub_nonneg.mpr hmin)
    have hline_sub : AffineMap.lineMap p v t - p = t • d := by
      simp [d, AffineMap.lineMap_apply_module']
    have hinner_line :
        ⟪g, AffineMap.lineMap p v t⟫_ℝ - ⟪g, p⟫_ℝ =
          t * ⟪g, d⟫_ℝ := by
      calc
        ⟪g, AffineMap.lineMap p v t⟫_ℝ - ⟪g, p⟫_ℝ =
            ⟪g, AffineMap.lineMap p v t - p⟫_ℝ := by
          rw [← inner_sub_right]
        _ = ⟪g, t • d⟫_ℝ := by rw [hline_sub]
        _ = t * ⟪g, d⟫_ℝ := by simp [inner_smul_right]
    have hphi_eq :
        phi t =
          gamma *
            (projectedPointModelValue S x g gamma (AffineMap.lineMap p v t) -
              projectedPointModelValue S x g gamma p) := by
      have hgamma_ne : gamma ≠ 0 := ne_of_gt hgamma
      simp only [phi, beta]
      rw [dif_pos ht]
      unfold projectedPointModelValue proxDistance
      field_simp [hgamma_ne]
      ring_nf
      nlinarith [hinner_line]
    rw [hphi_eq]
    exact hscaled
  have hscaled_vi :
      0 ≤
        gamma * ⟪g, v - p⟫_ℝ +
          ⟪S.proxGradient p - S.proxGradient x, v - p⟫_ℝ +
          gamma * ((fun _ : E => (0 : ℝ)) v - (fun _ : E => (0 : ℝ)) p) :=
    prox_scaled_variational_inequality_of_argmin
      (fun z : E => z) S.proxGradient (fun _ : E => (0 : ℝ))
      x p v g gamma phi hphi_zero hphi_nonneg hphi_deriv
  have hunscaled :
      0 ≤
        ⟪g, v - p⟫_ℝ +
          gamma⁻¹ * ⟪S.proxGradient p - S.proxGradient x, v - p⟫_ℝ +
          ((fun _ : E => (0 : ℝ)) v - (fun _ : E => (0 : ℝ)) p) :=
    prox_variational_inequality_of_argmin
      (fun z : E => z) S.proxGradient (fun _ : E => (0 : ℝ))
      x p v g gamma hgamma hscaled_vi
  have hinner :
      ⟪g + gamma⁻¹ • (S.proxGradient p - S.proxGradient x), v - p⟫_ℝ =
        ⟪g, v - p⟫_ℝ +
          gamma⁻¹ * ⟪S.proxGradient p - S.proxGradient x, v - p⟫_ℝ := by
    simp [inner_add_left, inner_smul_left]
  simpa [p, hinner] using hunscaled

/-- Same-base Bregman projected points are Lipschitz in the oracle vector.

This specializes Lan Lemma 6.5 / Eq. (6.2.11) to the paper's local
`projectedPoint`. Candidates considered: `prox_points_scaled_dist_le_oracle_dist_of_variational`
is the exact SOptLib stability lemma once the preceding helper supplies the
two projected-point variational inequalities; `projectedGradient_lipschitz_oracle_of_prox_scaled_dist`
is the follow-on algebraic mapping bound, not the prox-point distance itself. -/
private theorem projectedPoint_scaled_dist_le_oracle_dist_on_X (S : Setup E)
    {x g₁ g₂ : E} {gamma : ℝ} (hgamma : 0 < gamma) (hx : x ∈ S.X) :
    gamma⁻¹ * ‖projectedPoint S x g₁ gamma - projectedPoint S x g₂ gamma‖ ≤
      ‖g₁ - g₂‖ := by
  classical
  let p₁ : E := projectedPoint S x g₁ gamma
  let p₂ : E := projectedPoint S x g₂ gamma
  have hp₁ : p₁ ∈ S.X := by
    simpa [p₁] using (projectedPoint_spec S x g₁ gamma).1
  have hp₂ : p₂ ∈ S.X := by
    simpa [p₂] using (projectedPoint_spec S x g₂ gamma).1
  have hvi₁_raw :
      0 ≤ ⟪g₁ + gamma⁻¹ • (S.proxGradient p₁ - S.proxGradient x), p₂ - p₁⟫_ℝ := by
    simpa [p₁, p₂] using
      (projectedPoint_variational_inequality_on_X
        S (x := x) (g := g₁) (v := p₂) (gamma := gamma) hgamma hx hp₂)
  have hvi₂_raw :
      0 ≤ ⟪g₂ + gamma⁻¹ • (S.proxGradient p₂ - S.proxGradient x), p₁ - p₂⟫_ℝ := by
    simpa [p₁, p₂] using
      (projectedPoint_variational_inequality_on_X
        S (x := x) (g := g₂) (v := p₁) (gamma := gamma) hgamma hx hp₁)
  have hvi₁ :
      0 ≤
        ⟪g₁, p₂ - p₁⟫_ℝ +
          gamma⁻¹ * ⟪S.proxGradient p₁ - S.proxGradient x, p₂ - p₁⟫_ℝ +
          ((fun _ : E => (0 : ℝ)) p₂ - (fun _ : E => (0 : ℝ)) p₁) := by
    simpa [inner_add_left, inner_smul_left] using hvi₁_raw
  have hvi₂ :
      0 ≤
        ⟪g₂, p₁ - p₂⟫_ℝ +
          gamma⁻¹ * ⟪S.proxGradient p₂ - S.proxGradient x, p₁ - p₂⟫_ℝ +
          ((fun _ : E => (0 : ℝ)) p₁ - (fun _ : E => (0 : ℝ)) p₂) := by
    simpa [inner_add_left, inner_smul_left] using hvi₂_raw
  have hstrong :
      ‖p₁ - p₂‖ ^ 2 ≤ ⟪p₁ - p₂, S.proxGradient p₁ - S.proxGradient p₂⟫_ℝ :=
    theorem718_proxGradient_strong_monotone_on_X S hp₁ hp₂
  simpa [p₁, p₂] using
    (prox_points_scaled_dist_le_oracle_dist_of_variational
      (fun z : E => z) S.proxGradient (fun _ : E => (0 : ℝ))
      x p₁ p₂ g₁ g₂ gamma hgamma hvi₁ hvi₂ hstrong)

/-- The exact projected-gradient displacement is one-Lipschitz in the oracle
argument at a fixed base point.

This is the direct Eq. (6.2.11) mapping form used in Lan Theorem 7.18 proof
step 11. It consumes the previous prox-point distance helper and the SOptLib
algebraic projected-gradient Lipschitz lemma. -/
private theorem projectedGradient_oracle_lipschitz_on_X (S : Setup E)
    {x g₁ g₂ : E} {gamma : ℝ} (hgamma : 0 < gamma) (hx : x ∈ S.X) :
    ‖gamma⁻¹ • (x - projectedPoint S x g₁ gamma) -
        gamma⁻¹ • (x - projectedPoint S x g₂ gamma)‖ ≤ ‖g₁ - g₂‖ := by
  exact
    projectedGradient_lipschitz_oracle_of_prox_scaled_dist
      (fun z : E => z) (fun x g gamma => projectedPoint S x g gamma)
      x g₁ g₂ gamma hgamma
      (projectedPoint_scaled_dist_le_oracle_dist_on_X S hgamma hx)

/-- Split the exact Bregman projected-gradient norm into a stochastic-oracle
projected-gradient norm and the oracle error.

This is the proved same-state portion of Lan Theorem 7.18 proof step 11. The
remaining source bridge is to compare the `G`-based Bregman projected-point
displacement with the Euclidean CndG model residual. -/
private theorem exactProjectedGradient_sq_le_oracle_projectedGradient_sq_add_error
    (S : Setup E) {x G : E} (hgamma : 0 < S.gamma) (hx : x ∈ S.X) :
    ‖exactProjectedGradient S x‖ ^ 2 ≤
      2 * ‖S.gamma⁻¹ • (x - projectedPoint S x G S.gamma)‖ ^ 2 +
        2 * ‖G - SOptLib.finiteUniformAverage S.componentGradient x‖ ^ 2 := by
  simpa [exactProjectedGradient, SOptLib.projectedGradient] using
    (exact_projectedGradient_sq_le_oracle_projectedGradient_sq_add_residual
      (eval := fun y : E => y)
      (prox := fun x g gamma => projectedPoint S x g gamma)
      (grad := fun x => SOptLib.finiteUniformAverage S.componentGradient x)
      (x := x) (G := G) (gamma := S.gamma)
      (by
        simpa [SOptLib.projectedGradient] using
          (projectedGradient_oracle_lipschitz_on_X
            S (x := x) (g₁ := SOptLib.finiteUniformAverage S.componentGradient x) (g₂ := G)
            (gamma := S.gamma) hgamma hx)))

/-- First-order optimality for the Euclidean projected point used in Theorem
7.18.

This is the local Euclidean counterpart of `projectedPoint_variational_inequality_on_X`.
It is the remaining source-proof leaf for the new object: restrict the argmin
inequality for `euclideanProjectedPoint` to feasible line segments and
differentiate the one-dimensional quadratic model at the left endpoint. -/
private theorem euclideanProjectedPoint_variational_inequality_on_X (S : Setup E)
    {x g v : E} {gamma : ℝ} (hgamma : 0 < gamma)
    (hx : x ∈ S.X) (hv : v ∈ S.X) :
    let p : E := euclideanProjectedPoint S x g gamma
    0 ≤ ⟪g + gamma⁻¹ • (p - x), v - p⟫_ℝ := by
  classical
  have _hgamma_ne : gamma ≠ 0 := ne_of_gt hgamma
  have _hx_mem : x ∈ S.X := hx
  let p : E := euclideanProjectedPoint S x g gamma
  have hp : p ∈ S.X := by
    simpa [p] using (euclideanProjectedPoint_spec S x g gamma).1
  let phi : ℝ → ℝ := fun t =>
    euclideanProjectedPointModelValue S x g gamma (AffineMap.lineMap p v t)
  have hphi_min : ∀ t ∈ Set.Icc (0 : ℝ) 1, phi 0 ≤ phi t := by
    intro t ht
    have hline_mem : AffineMap.lineMap p v t ∈ S.X :=
      S.hX_convex.lineMap_mem hp hv ht
    have hmin :=
      (euclideanProjectedPoint_spec S x g gamma).2
        (AffineMap.lineMap p v t) hline_mem
    simpa [phi, p] using hmin
  have hmodel_deriv :
      HasFDerivAt (fun u : E => euclideanProjectedPointModelValue S x g gamma u)
        (InnerProductSpace.toDual ℝ E (g + gamma⁻¹ • (p - x))) p := by
    have hlinF : HasFDerivAt (fun u : E => ⟪g, u⟫_ℝ) (innerSL ℝ g) p := by
      simpa using (innerSL ℝ g).hasFDerivAt
    have hquadF :
        HasFDerivAt (fun u : E => (gamma⁻¹ / 2) * ‖u - x‖ ^ 2)
          (InnerProductSpace.toDual ℝ E (gamma⁻¹ • (p - x))) p := by
      exact
        (hasGradientAt_const_mul_norm_sub_sq_centered
          (E := E) gamma⁻¹ x p).hasFDerivAt
    have hsum := hlinF.add hquadF
    convert hsum using 1
    ext y
    simp [ContinuousLinearMap.add_apply, InnerProductSpace.toDual_apply_apply,
      real_inner_comm]
  have hline_deriv :
      HasDerivWithinAt (fun t : ℝ => AffineMap.lineMap p v t) (v - p)
        (Set.Icc (0 : ℝ) 1) 0 := by
    simpa using
      (AffineMap.hasDerivWithinAt_lineMap (a := p) (b := v)
        (s := Set.Icc (0 : ℝ) 1) (x := (0 : ℝ)))
  have hphi_deriv :
      HasDerivWithinAt phi ⟪g + gamma⁻¹ • (p - x), v - p⟫_ℝ
        (Set.Icc (0 : ℝ) 1) 0 := by
    have hcomp :=
      hmodel_deriv.comp_hasDerivWithinAt_of_eq
        (x := (0 : ℝ)) hline_deriv (by simp)
    simpa [phi, InnerProductSpace.toDual_apply_apply, inner_add_left,
      inner_smul_left, inner_sub_left, sub_eq_add_neg, mul_add, mul_comm,
      mul_left_comm, mul_assoc] using hcomp
  have hnonneg : 0 ≤ ⟪g + gamma⁻¹ • (p - x), v - p⟫_ℝ :=
    right_derivative_nonneg_of_min_on_Icc hphi_deriv hphi_min
  simpa [p] using hnonneg

/-- Same-base Euclidean projected points are Lipschitz in the oracle vector.

This is Lan's prox-map Lipschitz step (6.2.11) specialized to the Euclidean
quadratic `xhat` objects actually used in Theorem 7.18 proof steps 9--11. -/
private theorem euclideanProjectedPoint_scaled_dist_le_oracle_dist_on_X
    (S : Setup E) {x g₁ g₂ : E} {gamma : ℝ} (hgamma : 0 < gamma)
    (hx : x ∈ S.X) :
    gamma⁻¹ * ‖euclideanProjectedPoint S x g₁ gamma -
        euclideanProjectedPoint S x g₂ gamma‖ ≤
      ‖g₁ - g₂‖ := by
  classical
  let p₁ : E := euclideanProjectedPoint S x g₁ gamma
  let p₂ : E := euclideanProjectedPoint S x g₂ gamma
  have hp₁ : p₁ ∈ S.X := by
    simpa [p₁] using (euclideanProjectedPoint_spec S x g₁ gamma).1
  have hp₂ : p₂ ∈ S.X := by
    simpa [p₂] using (euclideanProjectedPoint_spec S x g₂ gamma).1
  have hvi₁_raw :
      0 ≤ ⟪g₁ + gamma⁻¹ • (p₁ - x), p₂ - p₁⟫_ℝ := by
    simpa [p₁, p₂] using
      (euclideanProjectedPoint_variational_inequality_on_X
        S (x := x) (g := g₁) (v := p₂) (gamma := gamma) hgamma hx hp₂)
  have hvi₂_raw :
      0 ≤ ⟪g₂ + gamma⁻¹ • (p₂ - x), p₁ - p₂⟫_ℝ := by
    simpa [p₁, p₂] using
      (euclideanProjectedPoint_variational_inequality_on_X
        S (x := x) (g := g₂) (v := p₁) (gamma := gamma) hgamma hx hp₁)
  have hvi₁ :
      0 ≤
        ⟪g₁, p₂ - p₁⟫_ℝ +
          gamma⁻¹ * ⟪p₁ - x, p₂ - p₁⟫_ℝ +
          ((fun _ : E => (0 : ℝ)) p₂ - (fun _ : E => (0 : ℝ)) p₁) := by
    simpa [inner_add_left, inner_smul_left] using hvi₁_raw
  have hvi₂ :
      0 ≤
        ⟪g₂, p₁ - p₂⟫_ℝ +
          gamma⁻¹ * ⟪p₂ - x, p₁ - p₂⟫_ℝ +
          ((fun _ : E => (0 : ℝ)) p₁ - (fun _ : E => (0 : ℝ)) p₂) := by
    simpa [inner_add_left, inner_smul_left] using hvi₂_raw
  have hstrong :
      ‖p₁ - p₂‖ ^ 2 ≤ ⟪p₁ - p₂, p₁ - p₂⟫_ℝ := by
    rw [real_inner_self_eq_norm_sq]
  simpa [p₁, p₂] using
    (prox_points_scaled_dist_le_oracle_dist_of_variational
      (fun z : E => z) (fun z : E => z) (fun _ : E => (0 : ℝ))
      x p₁ p₂ g₁ g₂ gamma hgamma hvi₁ hvi₂ hstrong)

/-- The Euclidean projected-gradient displacement is one-Lipschitz in the
oracle argument at a fixed base point. -/
private theorem euclideanProjectedGradient_oracle_lipschitz_on_X (S : Setup E)
    {x g₁ g₂ : E} {gamma : ℝ} (hgamma : 0 < gamma) (hx : x ∈ S.X) :
    ‖gamma⁻¹ • (x - euclideanProjectedPoint S x g₁ gamma) -
        gamma⁻¹ • (x - euclideanProjectedPoint S x g₂ gamma)‖ ≤ ‖g₁ - g₂‖ := by
  exact
    projectedGradient_lipschitz_oracle_of_prox_scaled_dist
      (fun z : E => z) (fun x g gamma => euclideanProjectedPoint S x g gamma)
      x g₁ g₂ gamma hgamma
      (euclideanProjectedPoint_scaled_dist_le_oracle_dist_on_X S hgamma hx)

/-- Split the Theorem 7.18 Euclidean projected-gradient norm into a stochastic
Euclidean projected-gradient norm and the oracle error. -/
private theorem euclideanProjectedGradient_sq_le_oracle_projectedGradient_sq_add_error
    (S : Setup E) {x G : E} (hgamma : 0 < S.gamma) (hx : x ∈ S.X) :
    ‖euclideanProjectedGradient S x‖ ^ 2 ≤
      2 * ‖S.gamma⁻¹ • (x - euclideanProjectedPoint S x G S.gamma)‖ ^ 2 +
        2 * ‖G - SOptLib.finiteUniformAverage S.componentGradient x‖ ^ 2 := by
  classical
  let pgFull : E := S.gamma⁻¹ •
    (x - euclideanProjectedPoint S x (SOptLib.finiteUniformAverage S.componentGradient x) S.gamma)
  let pgG : E := S.gamma⁻¹ • (x - euclideanProjectedPoint S x G S.gamma)
  have hdiff_le : ‖pgFull - pgG‖ ≤ ‖SOptLib.finiteUniformAverage S.componentGradient x - G‖ := by
    simpa [pgFull, pgG] using
      (euclideanProjectedGradient_oracle_lipschitz_on_X
        S (x := x) (g₁ := SOptLib.finiteUniformAverage S.componentGradient x) (g₂ := G)
        (gamma := S.gamma) hgamma hx)
  have hdiff_sq : ‖pgFull - pgG‖ ^ 2 ≤ ‖G - SOptLib.finiteUniformAverage S.componentGradient x‖ ^ 2 := by
    have hnonneg₁ : 0 ≤ ‖pgFull - pgG‖ := norm_nonneg _
    have hnonneg₂ : 0 ≤ ‖SOptLib.finiteUniformAverage S.componentGradient x - G‖ := norm_nonneg _
    have hsq : ‖pgFull - pgG‖ ^ 2 ≤ ‖SOptLib.finiteUniformAverage S.componentGradient x - G‖ ^ 2 :=
      by nlinarith [hdiff_le, hnonneg₁, hnonneg₂,
        sq_nonneg (‖SOptLib.finiteUniformAverage S.componentGradient x - G‖ - ‖pgFull - pgG‖)]
    simpa [norm_sub_rev] using hsq
  have hdecomp : euclideanProjectedGradient S x = pgG + (pgFull - pgG) := by
    rw [euclideanProjectedGradient_eq]
    simp [pgFull, pgG]
  calc
    ‖euclideanProjectedGradient S x‖ ^ 2 = ‖pgG + (pgFull - pgG)‖ ^ 2 := by rw [hdecomp]
    _ ≤ 2 * ‖pgG‖ ^ 2 + 2 * ‖pgFull - pgG‖ ^ 2 :=
      SOptLib.norm_add_sq_le_two_mul_norm_sq_add_two_mul_norm_sq pgG (pgFull - pgG)
    _ ≤ 2 * ‖pgG‖ ^ 2 + 2 * ‖G - SOptLib.finiteUniformAverage S.componentGradient x‖ ^ 2 := by
      nlinarith

/-- Eq. (7.5.11) projected-gradient comparison in the three-term form needed
before the stochastic estimator variance telescope.

This aligns with Lan Theorem 7.18 proof step 11: decompose the Euclidean
projected-gradient displacement through the approximate CndG output and the
stochastic Euclidean model minimizer. Candidates considered:
`euclideanProjectedGradient_sq_le_oracle_projectedGradient_sq_add_error` gives
only a two-term split and loses the residual descent coefficient required by
Eq. (7.5.12), while `projectedGradient_lipschitz_oracle_of_prox_scaled_dist`
and `SOptLib.norm_add_sq_le_two_mul_norm_sq_add_two_mul_norm_sq` supply the
oracle-Lipschitz and norm-square algebra used below. -/
private theorem theorem718_projected_gradient_three_term_bound (S : Setup E)
    (run : ℕ → AlgorithmSamplePath S → RunState E)
    (hrun : runStateSpec S (algorithmBatchStream S) run)
    (hgamma_pos : 0 < S.gamma)
    (hmodel_distance :
      ∀ k, (hk : k ∈ outputWindow S) → ∀ ω : AlgorithmSamplePath S,
        (1 / (2 * S.gamma)) *
          ‖iterate S run k ω -
            euclideanProjectedPoint S
              (paperIterate S run
                ⟨k, (Finset.mem_Icc.mp (by simpa [outputWindow] using hk)).1⟩ ω)
              (paperEstimator S run
                ⟨k, (Finset.mem_Icc.mp (by simpa [outputWindow] using hk)).1⟩ ω)
              S.gamma‖ ^ 2 ≤ S.eta) :
    ∀ k, (hk : k ∈ outputWindow S) → ∀ ω : AlgorithmSamplePath S,
      ‖paperProjectedGradient S run k ω‖ ^ 2 ≤
        2 *
          ‖S.gamma⁻¹ •
            (paperIterate S run
                ⟨k, (Finset.mem_Icc.mp (by simpa [outputWindow] using hk)).1⟩ ω -
              iterate S run k ω)‖ ^ 2 +
          8 * S.eta / S.gamma +
          4 *
            ‖paperEstimator S run
                ⟨k, (Finset.mem_Icc.mp (by simpa [outputWindow] using hk)).1⟩ ω -
              SOptLib.finiteUniformAverage S.componentGradient
                (paperIterate S run
                  ⟨k, (Finset.mem_Icc.mp (by simpa [outputWindow] using hk)).1⟩ ω)‖ ^ 2 := by
  classical
  intro k hk ω
  have hkIcc : k ∈ Finset.Icc 1 S.N := by
    simpa [outputWindow] using hk
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hkIcc).1
  let x : E := paperIterate S run ⟨k, hk1⟩ ω
  let y : E := iterate S run k ω
  let G : E := paperEstimator S run ⟨k, hk1⟩ ω
  let grad : E := SOptLib.finiteUniformAverage S.componentGradient x
  let zbar : E := euclideanProjectedPoint S x G S.gamma
  let xhat : E := euclideanProjectedPoint S x grad S.gamma
  have hx : x ∈ S.X := by
    simpa [x] using
      paperIterate_mem_of_runStateSpec S (algorithmBatchStream S) run hrun ⟨k, hk1⟩ ω
  have hmodel :
      (1 / (2 * S.gamma)) * ‖y - zbar‖ ^ 2 ≤ S.eta := by
    simpa [x, y, G, zbar, hkIcc, hk1] using hmodel_distance k hk ω
  have horacle_error : ‖S.gamma⁻¹ • (zbar - xhat)‖ ≤ ‖G - grad‖ := by
    have hlip :=
      euclideanProjectedGradient_oracle_lipschitz_on_X
        S (x := x) (g₁ := grad) (g₂ := G)
        (gamma := S.gamma) hgamma_pos hx
    have hlip' : ‖S.gamma⁻¹ • (zbar - xhat)‖ ≤ ‖grad - G‖ := by
      simpa [zbar, xhat, sub_eq_add_neg, add_comm, add_left_comm,
        add_assoc, smul_add, smul_neg] using hlip
    simpa [norm_sub_rev] using hlip'
  simpa [paperProjectedGradient, paperIterate, SOptLib.positiveTimeIterateView_eq,
    euclideanProjectedGradient_eq, x, y, G, grad, zbar, xhat, hkIcc, hk1] using
    (projectedGradient_sq_le_three_term_of_model_distance_and_oracle_error
      (x := x) (y := y) (zbar := zbar) (xhat := xhat) (grad := grad) (G := G)
      (gamma := S.gamma) (eta := S.eta) hgamma_pos hmodel horacle_error)

/-- Finite-prefix integrability for the scalar observables in Theorem 7.18's
summed Eq. (7.5.13) route.

This aligns with Lan Theorem 7.18 proof steps 13--16: projected-gradient
squares, estimator residual squares, scaled step squares, and objective drops
are all finite-time observables of Algorithm 7.12. The SOptLib candidates
`integrable_of_finiteSampleWindow_factor` and `integrable_of_finiteRange_factor`
were considered; the helper above specializes the latter to this two-index
mini-batch sample path, and `runState_eq_of_batch_prefix_eq` supplies the
relational-run finite-prefix dependence. -/
private theorem theorem718_finite_prefix_observable_integrability (S : Setup E)
    (run : ℕ → AlgorithmSamplePath S → RunState E)
    (hrun : runStateSpec S (algorithmBatchStream S) run) :
    ∀ k, (hk : k ∈ outputWindow S) →
      Integrable (fun ω : AlgorithmSamplePath S =>
        ‖paperProjectedGradient S run k ω‖ ^ 2) (algorithmSampleLaw S) ∧
      Integrable (fun ω : AlgorithmSamplePath S =>
        ‖paperEstimator S run
            ⟨k, (Finset.mem_Icc.mp (by simpa [outputWindow] using hk)).1⟩ ω -
          SOptLib.finiteUniformAverage S.componentGradient
            (paperIterate S run
              ⟨k, (Finset.mem_Icc.mp (by simpa [outputWindow] using hk)).1⟩ ω)‖ ^ 2)
        (algorithmSampleLaw S) ∧
      Integrable (fun ω : AlgorithmSamplePath S =>
        ‖S.gamma⁻¹ •
          (paperIterate S run
              ⟨k, (Finset.mem_Icc.mp (by simpa [outputWindow] using hk)).1⟩ ω -
            iterate S run k ω)‖ ^ 2) (algorithmSampleLaw S) ∧
      Integrable (fun ω : AlgorithmSamplePath S =>
        SOptLib.finiteUniformAverage S.componentObjective
            (paperIterate S run
              ⟨k, (Finset.mem_Icc.mp (by simpa [outputWindow] using hk)).1⟩ ω) -
          SOptLib.finiteUniformAverage S.componentObjective (iterate S run k ω)) (algorithmSampleLaw S) := by
  classical
  intro k hk
  have hkIcc : k ∈ Finset.Icc 1 S.N := by
    simpa [outputWindow] using hk
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hkIcc).1
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine integrable_algorithmSampleLaw_of_prefix_const S k ?_
    intro ω ω' hprefix
    have hprev : run (k - 1) ω = run (k - 1) ω' :=
      runState_eq_of_batch_prefix_eq S (algorithmBatchStream S) run hrun
        (k - 1) ω ω' (fun j hj r => by
          exact hprefix j (by omega) r)
    simpa [paperProjectedGradient, iterate, hprev]
  · refine integrable_algorithmSampleLaw_of_prefix_const S k ?_
    intro ω ω' hprefix
    have hk_run : run k ω = run k ω' :=
      runState_eq_of_batch_prefix_eq S (algorithmBatchStream S) run hrun
        k ω ω' (fun j hj r => by
          exact hprefix j hj r)
    have hprev : run (k - 1) ω = run (k - 1) ω' :=
      runState_eq_of_batch_prefix_eq S (algorithmBatchStream S) run hrun
        (k - 1) ω ω' (fun j hj r => by
          exact hprefix j (by omega) r)
    simpa [paperEstimator, estimator, paperIterate, iterate,
      SOptLib.positiveTimeIterateView_eq, hk_run, hprev]
  · refine integrable_algorithmSampleLaw_of_prefix_const S k ?_
    intro ω ω' hprefix
    have hk_run : run k ω = run k ω' :=
      runState_eq_of_batch_prefix_eq S (algorithmBatchStream S) run hrun
        k ω ω' (fun j hj r => by
          exact hprefix j hj r)
    have hprev : run (k - 1) ω = run (k - 1) ω' :=
      runState_eq_of_batch_prefix_eq S (algorithmBatchStream S) run hrun
        (k - 1) ω ω' (fun j hj r => by
          exact hprefix j (by omega) r)
    simpa [paperIterate, iterate, SOptLib.positiveTimeIterateView_eq, hk_run, hprev]
  · refine integrable_algorithmSampleLaw_of_prefix_const S k ?_
    intro ω ω' hprefix
    have hk_run : run k ω = run k ω' :=
      runState_eq_of_batch_prefix_eq S (algorithmBatchStream S) run hrun
        k ω ω' (fun j hj r => by
          exact hprefix j hj r)
    have hprev : run (k - 1) ω = run (k - 1) ω' :=
      runState_eq_of_batch_prefix_eq S (algorithmBatchStream S) run hrun
        (k - 1) ω ω' (fun j hj r => by
          exact hprefix j (by omega) r)
    simpa [paperIterate, iterate, SOptLib.positiveTimeIterateView_eq, hk_run, hprev]

/-- Expected one-step projected-gradient descent with the negative tilde-square
term retained.

This is the expectation lift of the pointwise inequality immediately preceding
Lan Eq. (7.5.13). It reuses SOptLib's
`integral_one_step_gap_source_form_of_pointwise`; the route-local contribution
is supplying the finite-prefix integrability facts from
`theorem718_finite_prefix_observable_integrability` and rearranging the
pointwise CndG descent into objective-drop source form. -/
private theorem theorem718_integrated_one_step_projected_gradient_descent
    (S : Setup E)
    (run : ℕ → AlgorithmSamplePath S → RunState E)
    (hrun : runStateSpec S (algorithmBatchStream S) run)
    (hdescent :
      ∀ k, (hk : k ∈ outputWindow S) → ∀ ω : AlgorithmSamplePath S,
        SOptLib.finiteUniformAverage S.componentObjective (iterate S run k ω) +
            (1 / (16 * S.L)) * ‖paperProjectedGradient S run k ω‖ ^ 2 ≤
          SOptLib.finiteUniformAverage S.componentObjective
              (paperIterate S run
                ⟨k, (Finset.mem_Icc.mp (by simpa [outputWindow] using hk)).1⟩ ω) -
            (1 / (8 * S.L)) *
              ‖S.gamma⁻¹ •
                (paperIterate S run
                    ⟨k, (Finset.mem_Icc.mp (by simpa [outputWindow] using hk)).1⟩ ω -
                  iterate S run k ω)‖ ^ 2 +
            (5 / (4 * S.L)) *
              ‖paperEstimator S run
                  ⟨k, (Finset.mem_Icc.mp (by simpa [outputWindow] using hk)).1⟩ ω -
                SOptLib.finiteUniformAverage S.componentGradient
                  (paperIterate S run
                    ⟨k, (Finset.mem_Icc.mp (by simpa [outputWindow] using hk)).1⟩ ω)‖ ^ 2 +
            (3 / 2) * S.eta) :
    ∀ k, (hk : k ∈ outputWindow S) →
      (1 / (16 * S.L)) * algorithmExpectedSquaredPaperProjectedGradient S run k ≤
        ((∫ ω : AlgorithmSamplePath S,
            SOptLib.finiteUniformAverage S.componentObjective
                (paperIterate S run
                  ⟨k, (Finset.mem_Icc.mp (by simpa [outputWindow] using hk)).1⟩ ω) -
              SOptLib.finiteUniformAverage S.componentObjective (iterate S run k ω) ∂algorithmSampleLaw S) +
          (-(1 / (8 * S.L))) *
            ∫ ω : AlgorithmSamplePath S,
              ‖S.gamma⁻¹ •
                (paperIterate S run
                    ⟨k, (Finset.mem_Icc.mp (by simpa [outputWindow] using hk)).1⟩ ω -
                  iterate S run k ω)‖ ^ 2 ∂algorithmSampleLaw S) +
          (3 / 2) * S.eta +
          (5 / (4 * S.L)) *
            ∫ ω : AlgorithmSamplePath S,
              ‖paperEstimator S run
                  ⟨k, (Finset.mem_Icc.mp (by simpa [outputWindow] using hk)).1⟩ ω -
                SOptLib.finiteUniformAverage S.componentGradient
                  (paperIterate S run
                    ⟨k, (Finset.mem_Icc.mp (by simpa [outputWindow] using hk)).1⟩ ω)‖ ^ 2
              ∂algorithmSampleLaw S := by
  classical
  intro k hk
  have hreg := theorem718_finite_prefix_observable_integrability S run hrun k hk
  let gap : AlgorithmSamplePath S → ℝ :=
    fun ω => ‖paperProjectedGradient S run k ω‖ ^ 2
  let drop : AlgorithmSamplePath S → ℝ :=
    fun ω =>
      SOptLib.finiteUniformAverage S.componentObjective
          (paperIterate S run
            ⟨k, (Finset.mem_Icc.mp (by simpa [outputWindow] using hk)).1⟩ ω) -
        SOptLib.finiteUniformAverage S.componentObjective (iterate S run k ω)
  let tilde : AlgorithmSamplePath S → ℝ :=
    fun ω =>
      ‖S.gamma⁻¹ •
        (paperIterate S run
            ⟨k, (Finset.mem_Icc.mp (by simpa [outputWindow] using hk)).1⟩ ω -
          iterate S run k ω)‖ ^ 2
  let delta : AlgorithmSamplePath S → ℝ :=
    fun ω =>
      ‖paperEstimator S run
          ⟨k, (Finset.mem_Icc.mp (by simpa [outputWindow] using hk)).1⟩ ω -
        SOptLib.finiteUniformAverage S.componentGradient
          (paperIterate S run
            ⟨k, (Finset.mem_Icc.mp (by simpa [outputWindow] using hk)).1⟩ ω)‖ ^ 2
  have hpoint :
      ∀ ω : AlgorithmSamplePath S,
        (1 / (16 * S.L)) * gap ω ≤
          ((drop ω + (-(1 / (8 * S.L))) * tilde ω) + (3 / 2) * S.eta) +
            (5 / (4 * S.L)) * delta ω := by
    intro ω
    have h := hdescent k hk ω
    simp only [gap, drop, tilde, delta]
    nlinarith
  haveI : IsProbabilityMeasure (algorithmSampleLaw S) :=
    (algorithmSampleLaw_spec S).1
  have hraw :=
    integral_one_step_gap_source_form_of_pointwise
      (P := algorithmSampleLaw S)
      gap drop tilde delta
      (1 / (16 * S.L)) (-(1 / (8 * S.L))) ((3 / 2) * S.eta)
      (5 / (4 * S.L))
      hreg.1 hreg.2.2.2 hreg.2.2.1 hreg.2.1 hpoint
  simpa [algorithmExpectedSquaredPaperProjectedGradient,
    expectedSquaredPaperProjectedGradient, gap, drop, tilde, delta]
    using hraw

/-- Expected objective-drop telescope for the summed Theorem 7.18 route.

This aligns with Lan Theorem 7.18 proof step 16: summing the consecutive
objective drops leaves the initial objective minus a terminal objective, and
`finiteSumMinimizer_spec` lower-bounds the terminal feasible iterate by `f^*`.
The SOptLib candidate `integral_sum_telescope_bound_of_pointwise_lower_bound`
matches this expected-telescope shape and is specialized here to the paper's
one-based `paperIterate` view. -/
private theorem theorem718_expected_objective_drop_telescope (S : Setup E)
    (run : ℕ → AlgorithmSamplePath S → RunState E)
    (hrun : runStateSpec S (algorithmBatchStream S) run) :
    Finset.sum (outputWindow S) (fun k =>
        ∫ ω : AlgorithmSamplePath S,
          if hk : k ∈ outputWindow S then
            SOptLib.finiteUniformAverage S.componentObjective
                (paperIterate S run
                  ⟨k, (Finset.mem_Icc.mp (by simpa [outputWindow] using hk)).1⟩ ω) -
              SOptLib.finiteUniformAverage S.componentObjective (iterate S run k ω)
          else 0 ∂algorithmSampleLaw S) ≤
      SOptLib.finiteUniformAverage S.componentObjective S.x₁ - fStar S := by
  classical
  haveI : IsProbabilityMeasure (algorithmSampleLaw S) :=
    (algorithmSampleLaw_spec S).1
  let drop : ℕ → AlgorithmSamplePath S → ℝ := fun k ω =>
    if hk : k ∈ outputWindow S then
      SOptLib.finiteUniformAverage S.componentObjective
          (paperIterate S run
            ⟨k, (Finset.mem_Icc.mp (by simpa [outputWindow] using hk)).1⟩ ω) -
        SOptLib.finiteUniformAverage S.componentObjective (iterate S run k ω)
    else 0
  let terminal : AlgorithmSamplePath S → ℝ := fun ω =>
    SOptLib.finiteUniformAverage S.componentObjective
      (paperIterate S run
        ⟨S.N + 1, Nat.succ_le_succ (Nat.zero_le S.N)⟩ ω)
  have hdrop_int :
      ∀ k ∈ outputWindow S, Integrable (drop k) (algorithmSampleLaw S) := by
    intro k hk
    have hreg := theorem718_finite_prefix_observable_integrability S run hrun k hk
    simpa [drop, hk] using hreg.2.2.2
  have hpoint :
      ∀ ω : AlgorithmSamplePath S,
        Finset.sum (outputWindow S) (fun k => drop k ω) =
          SOptLib.finiteUniformAverage S.componentObjective S.x₁ - terminal ω := by
    intro ω
    let a : ℕ → ℝ := fun n =>
      if hn : 1 ≤ n then
        SOptLib.finiteUniformAverage S.componentObjective (paperIterate S run ⟨n, hn⟩ ω)
      else 0
    have htelescope :
        Finset.sum (Finset.Icc 1 S.N) (fun n => a n - a (n + 1)) =
          a 1 - a (S.N + 1) := by
      exact sum_Icc_sub_succ a 1 S.N S.hN_pos
    calc
      Finset.sum (outputWindow S) (fun k => drop k ω)
          = Finset.sum (Finset.Icc 1 S.N) (fun n => a n - a (n + 1)) := by
            refine Finset.sum_congr ?_ ?_
            · simp [outputWindow]
            · intro n hn
              have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
              have hnsucc : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
              have hn_window : n ∈ outputWindow S := by
                simpa [outputWindow] using hn
              have hpaper_succ :
                  paperIterate S run ⟨n + 1, hnsucc⟩ ω =
                    iterate S run n ω := by
                simp [paperIterate, SOptLib.positiveTimeIterateView_eq]
              simp [drop, hn_window, a, hn1, hnsucc, hpaper_succ]
      _ = a 1 - a (S.N + 1) := htelescope
      _ = SOptLib.finiteUniformAverage S.componentObjective S.x₁ - terminal ω := by
        have hpaper_one :
            paperIterate S run ⟨1, le_rfl⟩ ω = S.x₁ := by
          simpa [paperIterate, SOptLib.positiveTimeIterateView_eq] using
            iterate_zero S (algorithmBatchStream S) run hrun ω
        simp [a, terminal, hpaper_one]
  have hlower :
      ∀ ω : AlgorithmSamplePath S, fStar S ≤ terminal ω := by
    intro ω
    have hterm_mem :
        paperIterate S run
            ⟨S.N + 1, Nat.succ_le_succ (Nat.zero_le S.N)⟩ ω ∈ S.X :=
      paperIterate_mem_of_runStateSpec S (algorithmBatchStream S) run hrun
        ⟨S.N + 1, Nat.succ_le_succ (Nat.zero_le S.N)⟩ ω
    simpa [terminal, fStar] using (finiteSumMinimizer_spec S).2
      (paperIterate S run
        ⟨S.N + 1, Nat.succ_le_succ (Nat.zero_le S.N)⟩ ω) hterm_mem
  have hbound :=
    integral_sum_telescope_bound_of_pointwise_lower_bound
      (P := algorithmSampleLaw S) (times := outputWindow S)
      (drop := drop) (terminal := terminal)
      (initial := SOptLib.finiteUniformAverage S.componentObjective S.x₁) (lower := fStar S)
      hdrop_int hpoint hlower
  simpa [drop] using hbound

/-- Active-epoch summation form of the Lemma 7.4 estimator budget.

This helper aligns with Lan Eq. (7.4.4) as used in the proof of Theorem 7.18:
once the per-active-step estimator residual is bounded by the predecessor
triangle with coefficient `1 / b`, the SOptLib active-window partition and
triangular predecessor bound convert it to the global `1/10` absorption under
`b = 10T`. Candidates considered: `SOptLib.sum_output_window_eq_sum_active_epoch_steps`
and `SOptLib.active_triangular_predecessor_sum_le_batch_mul_global_sum` exactly
match the reindexing/counting part, while `SOptLib.epoch_recursive_estimator_second_moment_le_difference_sum`
is the lower-level stochastic induction needed to prove the pointwise premise,
not this summation step. -/
private theorem theorem718_sum_deltaTerm_le_tenth_sum_tildeTerm_from_epoch
    (S : Setup E) (tildeTerm deltaTerm : ℕ → ℝ)
    (hb_choice : S.b = 10 * S.T)
    (hdelta_epoch :
      ∀ s j, s ∈ Finset.Icc 0 S.N →
        j ∈ SOptLib.activeEpochSteps S.T S.N (SOptLib.global_index S.T) s →
          deltaTerm (SOptLib.global_index S.T s j) ≤
            (S.b : ℝ)⁻¹ *
              Finset.sum (Finset.Icc 2 j)
                (fun i => tildeTerm (SOptLib.global_index S.T s (i - 1))))
    (htilde_nonneg : ∀ k ∈ outputWindow S, 0 ≤ tildeTerm k) :
    Finset.sum (outputWindow S) deltaTerm ≤
      (1 / 10) * Finset.sum (outputWindow S) tildeTerm := by
  simpa [outputWindow] using
    SOptLib.sum_delta_le_ratio_sum_tilde_of_active_epoch_predecessor_bound
      (T := S.T) (N := S.N) (b := S.b)
      (tilde := tildeTerm) (delta := deltaTerm)
      S.hT_pos hb_choice hdelta_epoch
      (by simpa [outputWindow] using htilde_nonneg)


/-- Variance-term absorption from the active-epoch Lemma 7.4 budget.

This packages the already-proved active-window summation helper with the scalar
calculation, so the main Theorem 7.18 proof only has to supply the source-bound
pointwise estimator budget. -/
private theorem theorem718_varianceTerm_sum_nonpos_from_delta_epoch
    (S : Setup E) (tildeTerm deltaTerm varianceTerm : ℕ → ℝ)
    (hvariance_def :
      varianceTerm = fun k =>
        (-(1 / (8 * S.L))) * tildeTerm k + (5 / (4 * S.L)) * deltaTerm k)
    (hb_choice : S.b = 10 * S.T)
    (hLpos : 0 < S.L)
    (hdelta_epoch :
      ∀ s j, s ∈ Finset.Icc 0 S.N →
        j ∈ SOptLib.activeEpochSteps S.T S.N (SOptLib.global_index S.T) s →
          deltaTerm (SOptLib.global_index S.T s j) ≤
            (S.b : ℝ)⁻¹ *
              Finset.sum (Finset.Icc 2 j)
                (fun i => tildeTerm (SOptLib.global_index S.T s (i - 1))))
    (htilde_nonneg : ∀ k ∈ outputWindow S, 0 ≤ tildeTerm k) :
    Finset.sum (outputWindow S) varianceTerm ≤ 0 := by
  have hdelta_absorb :
      Finset.sum (outputWindow S) deltaTerm ≤
        (1 / 10) * Finset.sum (outputWindow S) tildeTerm :=
    theorem718_sum_deltaTerm_le_tenth_sum_tildeTerm_from_epoch
      S tildeTerm deltaTerm hb_choice hdelta_epoch htilde_nonneg
  have hsum_eq :
      Finset.sum (outputWindow S) varianceTerm =
        (-(1 / (8 * S.L))) * Finset.sum (outputWindow S) tildeTerm +
          (5 / (4 * S.L)) * Finset.sum (outputWindow S) deltaTerm := by
    rw [hvariance_def]
    rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  calc
    Finset.sum (outputWindow S) varianceTerm
        = (-(1 / (8 * S.L))) * Finset.sum (outputWindow S) tildeTerm +
            (5 / (4 * S.L)) * Finset.sum (outputWindow S) deltaTerm := hsum_eq
    _ ≤ 0 :=
        by
          have hcoef_nonneg : 0 ≤ 5 / (4 * S.L) := by
            have hden_pos : 0 < 4 * S.L := by nlinarith
            exact le_of_lt (div_pos (by norm_num) hden_pos)
          have hscaled :=
            mul_le_mul_of_nonneg_left hdelta_absorb hcoef_nonneg
          have hprod :
              (5 / (4 * S.L)) * Finset.sum (outputWindow S) deltaTerm ≤
                (1 / (8 * S.L)) * Finset.sum (outputWindow S) tildeTerm := by
            calc
              (5 / (4 * S.L)) * Finset.sum (outputWindow S) deltaTerm
                  ≤ (5 / (4 * S.L)) *
                      ((1 / 10) * Finset.sum (outputWindow S) tildeTerm) := hscaled
              _ = (1 / (8 * S.L)) * Finset.sum (outputWindow S) tildeTerm := by
                  field_simp [ne_of_gt hLpos]
                  ring
          simpa [neg_mul] using (neg_add_nonpos_iff.mpr hprod)

/-- Deterministic diagonal budget for the importance-weighted sampled correction.

This is the component-smoothness and `q_i = L_i/(mL)` simplification in Lan
Lemma 6.10, Eq. (6.5.6), reused by Lemma 7.4. Candidates considered:
`norm_inv_smoothness_importance_smul_le` exactly handles the inverse
smoothness-importance scaling, and
`finset_weighted_second_moment_le_of_pointwise_norm_bound` exactly handles the
normalized finite weighted second moment, so this helper only specializes those
SOptLib facts to the paper-local `sampledGradientCorrection` notation. -/
private theorem sampledGradientCorrection_weighted_second_moment_le
    (S : Setup E) {x y : E} (hx : x ∈ S.X) (hy : y ∈ S.X) :
    Finset.sum Finset.univ
        (fun i : Fin S.componentCount =>
          componentSamplingProbability S i *
            ‖sampledGradientCorrection S x y i‖ ^ 2) ≤
      S.L ^ 2 * ‖x - y‖ ^ 2 := by
  classical
  have hcount_pos : 0 < (S.componentCount : ℝ) :=
    Nat.cast_pos.mpr S.hcomponentCount_pos
  have hLpos : 0 < S.L := averageSmoothness_pos S
  have hpoint :
      ∀ i ∈ (Finset.univ : Finset (Fin S.componentCount)),
        ‖sampledGradientCorrection S x y i‖ ≤ S.L * ‖x - y‖ := by
    intro i _hi
    have hcomponent :
        ‖S.componentGradient i x - S.componentGradient i y‖ ≤
          S.componentL i * ‖x - y‖ :=
      S.hcomponent_smooth i x y hx hy
    have hscale :=
      norm_inv_smoothness_importance_smul_le
        (Lcomp := S.componentL) (n := (S.componentCount : ℝ))
        (L := S.L) (r := ‖x - y‖) i
        (S.componentGradient i x - S.componentGradient i y)
        hcount_pos hLpos (S.hcomponentL_pos i) hcomponent
    simpa [sampledGradientCorrection, componentSamplingProbability,
      SOptLib.normalizedOutputMass] using hscale
  have hweighted :
      Finset.sum Finset.univ
          (fun i : Fin S.componentCount =>
            componentSamplingProbability S i *
              ‖sampledGradientCorrection S x y i‖ ^ 2) ≤
        (S.L * ‖x - y‖) ^ 2 :=
    finset_weighted_second_moment_le_of_pointwise_norm_bound
      (s := (Finset.univ : Finset (Fin S.componentCount)))
      (q := componentSamplingProbability S)
      (A := fun i : Fin S.componentCount => sampledGradientCorrection S x y i)
      (C := S.L * ‖x - y‖)
      (by intro i _hi; exact componentSamplingProbability_nonneg S i)
      (componentSamplingProbability_sum_one S)
      hpoint
  calc
    Finset.sum Finset.univ
        (fun i : Fin S.componentCount =>
          componentSamplingProbability S i *
            ‖sampledGradientCorrection S x y i‖ ^ 2)
        ≤ (S.L * ‖x - y‖) ^ 2 := hweighted
    _ = S.L ^ 2 * ‖x - y‖ ^ 2 := by ring

/-- Mean identity for the importance-weighted sampled correction.

This is Lan Lemma 6.10's `E[ζ_i] = ∇f(x_t)-∇f(x_{t-1})` identity in
deterministic finite-index form. Candidates considered:
`finset_importance_weighted_diff_mean_eq_uniform_mean` exactly proves the
inverse-probability weighted mean cancellation, so this helper only rewrites it
to the paper-local finite-average-gradient and `sampledGradientCorrection` notation. -/
private theorem sampledGradientCorrection_weighted_mean_eq_finiteAverageGradient_sub
    (S : Setup E) (x y : E) :
    Finset.sum Finset.univ
        (fun i : Fin S.componentCount =>
          componentSamplingProbability S i • sampledGradientCorrection S x y i) =
      SOptLib.finiteUniformAverage S.componentGradient x - SOptLib.finiteUniformAverage S.componentGradient y := by
  classical
  have hcount_pos : 0 < (S.componentCount : ℝ) :=
    Nat.cast_pos.mpr S.hcomponentCount_pos
  have hcount_ne : (S.componentCount : ℝ) ≠ 0 := ne_of_gt hcount_pos
  have hq_ne :
      ∀ i ∈ (Finset.univ : Finset (Fin S.componentCount)),
        componentSamplingProbability S i ≠ 0 := by
    intro i _hi
    have hLpos : 0 < S.L := averageSmoothness_pos S
    have hden_pos : 0 < (S.componentCount : ℝ) * S.L :=
      mul_pos hcount_pos hLpos
    have hq_pos : 0 < componentSamplingProbability S i := by
      unfold componentSamplingProbability
      exact div_pos (S.hcomponentL_pos i) hden_pos
    exact ne_of_gt hq_pos
  have hmean :=
    finset_importance_weighted_diff_mean_eq_uniform_mean
      (s := (Finset.univ : Finset (Fin S.componentCount)))
      (q := componentSamplingProbability S)
      (n := (S.componentCount : ℝ))
      (a := fun i : Fin S.componentCount => S.componentGradient i x)
      (b := fun i : Fin S.componentCount => S.componentGradient i y)
      hq_ne hcount_ne
  simpa [sampledGradientCorrection, SOptLib.finiteUniformAverage, Finset.sum_sub_distrib]
    using hmean

/-- The sampled correction has the finite-average gradient difference as its
Bochner mean under the component PMF. -/
private theorem sampledGradientCorrection_integral_eq_finiteAverageGradient_sub
    (S : Setup E) (x y : E) :
    ∫ i : Fin S.componentCount, sampledGradientCorrection S x y i
        ∂(componentSamplingPMF S).toMeasure =
      SOptLib.finiteUniformAverage S.componentGradient x -
        SOptLib.finiteUniformAverage S.componentGradient y := by
  classical
  rw [PMF.integral_eq_sum]
  trans
      Finset.sum Finset.univ
        (fun i : Fin S.componentCount =>
          componentSamplingProbability S i • sampledGradientCorrection S x y i)
  · refine Finset.sum_congr rfl ?_
    intro i _hi
    have hpmf_apply :
        componentSamplingPMF S i =
          ENNReal.ofReal (componentSamplingProbability S i) := by
      simp [componentSamplingPMF, componentSamplingProbability,
        SOptLib.smoothnessImportanceWeight]
    have hmass :
        (componentSamplingPMF S i).toReal = componentSamplingProbability S i := by
      rw [hpmf_apply]
      exact ENNReal.toReal_ofReal (componentSamplingProbability_nonneg S i)
    simp [hmass]
  · exact sampledGradientCorrection_weighted_mean_eq_finiteAverageGradient_sub S x y

/-- Centered finite-index variance budget for one importance-sampled correction.

This is the deterministic finite-index form of the centered sample fluctuation
in Lan Lemma 6.10, Eq. (6.5.6). Candidates considered:
`finset_weighted_residual_second_moment_le_of_second_moment` exactly converts
the uncentered diagonal budget plus the weighted-mean identity into the
centered residual budget, so this helper specializes it to
`sampledGradientCorrection`, the finite-average gradient, and the paper probabilities. -/
private theorem sampledGradientCorrection_centered_weighted_second_moment_le
    (S : Setup E) {x y : E} (hx : x ∈ S.X) (hy : y ∈ S.X) :
    Finset.sum Finset.univ
        (fun i : Fin S.componentCount =>
          componentSamplingProbability S i *
            ‖sampledGradientCorrection S x y i -
              (SOptLib.finiteUniformAverage S.componentGradient x - SOptLib.finiteUniformAverage S.componentGradient y)‖ ^ 2) ≤
      S.L ^ 2 * ‖x - y‖ ^ 2 := by
  exact
    finset_weighted_residual_second_moment_le_of_second_moment
      (s := (Finset.univ : Finset (Fin S.componentCount)))
      (q := componentSamplingProbability S)
      (a := fun i : Fin S.componentCount => sampledGradientCorrection S x y i)
      (μ := SOptLib.finiteUniformAverage S.componentGradient x - SOptLib.finiteUniformAverage S.componentGradient y)
      (C := S.L ^ 2 * ‖x - y‖ ^ 2)
      (componentSamplingProbability_sum_one S)
      (sampledGradientCorrection_weighted_mean_eq_finiteAverageGradient_sub S x y)
      (sampledGradientCorrection_weighted_second_moment_le S hx hy)

/-- Lan Lemma 7.4 specialized to the concrete Algorithm 7.12 run objects.

This is the remaining source-derived finite-sum recursive-estimator bridge:
it aligns with Lan Eq. (7.4.4), using the canonical iid law, `runStateSpec`,
the refresh identity, smoothness-proportional probabilities, and
`gamma = 1/L` to convert the residual second moment into the predecessor
tilde-square triangle. Candidates considered: `SOptLib.epoch_recursive_estimator_second_moment_le_difference_sum`
matches the epoch induction skeleton, and
`SOptLib.randomQuery_centeredMiniBatchGradientDiff_secondMoment_le` /
`SOptLib.recursive_estimator_residual_global_index_eq_prev_add_centered_batch_diff`
match lower-level stochastic and recursive pieces, but the current file has
not yet assembled their hypotheses from `runStateSpec` and `algorithmSampleLawSpec`. -/
private theorem theorem718_deltaTerm_le_epoch_predecessor_tilde_sum
    (S : Setup E) (run : ℕ → AlgorithmSamplePath S → RunState E)
    (hLaw : algorithmSampleLawSpec S (algorithmSampleLaw S))
    (hrun : runStateSpec S (algorithmBatchStream S) run)
    (hb_choice : S.b = 10 * S.T)
    (hgamma_choice : S.gamma = S.L⁻¹)
    (hLpos : 0 < S.L)
    (tildeTerm deltaTerm : ℕ → ℝ)
    (htilde_def : tildeTerm = fun k =>
      ∫ ω : AlgorithmSamplePath S,
        if hk : k ∈ outputWindow S then
          ‖S.gamma⁻¹ •
            (paperIterate S run
                ⟨k, (Finset.mem_Icc.mp (by simpa [outputWindow] using hk)).1⟩ ω -
              iterate S run k ω)‖ ^ 2
        else 0 ∂algorithmSampleLaw S)
    (hdelta_def : deltaTerm = fun k =>
      ∫ ω : AlgorithmSamplePath S,
        if hk : k ∈ outputWindow S then
          ‖paperEstimator S run
              ⟨k, (Finset.mem_Icc.mp (by simpa [outputWindow] using hk)).1⟩ ω -
            SOptLib.finiteUniformAverage S.componentGradient
              (paperIterate S run
                ⟨k, (Finset.mem_Icc.mp (by simpa [outputWindow] using hk)).1⟩ ω)‖ ^ 2
        else 0 ∂algorithmSampleLaw S)
    (s j : ℕ) (hs : s ∈ Finset.Icc 0 S.N)
    (hj : j ∈ SOptLib.activeEpochSteps S.T S.N (SOptLib.global_index S.T) s) :
    deltaTerm (SOptLib.global_index S.T s j) ≤
      (S.b : ℝ)⁻¹ *
        Finset.sum (Finset.Icc 2 j)
          (fun i => tildeTerm (SOptLib.global_index S.T s (i - 1))) := by
  classical
  have hj_epoch :
      1 ≤ j ∧ j ≤ S.T := by
    exact SOptLib.activeEpochSteps_mem_epoch (T := S.T) (N := S.N)
      (globalIndex := SOptLib.global_index S.T) (s := s) (j := j) hj
  have hidx_pos : 1 ≤ SOptLib.global_index S.T s j := by
    simp [SOptLib.global_index_def]
    omega
  have hidx_window : SOptLib.global_index S.T s j ∈ outputWindow S := by
    simpa [outputWindow] using
      SOptLib.global_index_mem_output_window_of_active_epoch_step
        (T := S.T) (N := S.N) (globalIndex := SOptLib.global_index S.T)
        (s := s) (j := j) hidx_pos hj
  have h_epoch_start_step :
      SOptLib.stepOfIndex S.T (SOptLib.global_index S.T s 1) = 1 :=
    refresh_predicate_holds_at_global_index_start (T := S.T) (s := s) S.hT_pos
  have h_epoch_start_pos : 1 ≤ SOptLib.global_index S.T s 1 := by
    simp [SOptLib.global_index_def]
  have h_epoch_start_estimator_eq :
      ∀ ω : AlgorithmSamplePath S,
        paperEstimator S run ⟨SOptLib.global_index S.T s 1, h_epoch_start_pos⟩ ω =
          SOptLib.finiteUniformAverage S.componentGradient
            (paperIterate S run
              ⟨SOptLib.global_index S.T s 1, h_epoch_start_pos⟩ ω) := by
    intro ω
    exact paperEstimator_refresh S (algorithmBatchStream S) run hrun
      ⟨SOptLib.global_index S.T s 1, h_epoch_start_pos⟩ ω h_epoch_start_step
  let μ := algorithmSampleLaw S
  let index : ℕ → ℕ → ℕ := SOptLib.global_index S.T
  let deltaProc : ℕ → AlgorithmSamplePath S → E := fun k ω =>
    if hk : 1 ≤ k then
      paperEstimator S run ⟨k, hk⟩ ω -
        SOptLib.finiteUniformAverage S.componentGradient (paperIterate S run ⟨k, hk⟩ ω)
    else 0
  let xProc : ℕ → AlgorithmSamplePath S → E := fun k ω =>
    if hk : 1 ≤ k then paperIterate S run ⟨k, hk⟩ ω else iterate S run k ω
  have h_epoch_start_active :
      1 ∈ SOptLib.activeEpochSteps S.T S.N (SOptLib.global_index S.T) s := by
    have hjN :
        SOptLib.global_index S.T s j ≤ S.N :=
      SOptLib.activeEpochSteps_globalIndex_le (T := S.T) (N := S.N)
        (globalIndex := SOptLib.global_index S.T) (s := s) (j := j) hj
    have hstartN :
        SOptLib.global_index S.T s 1 ≤ S.N := by
      have hjN' : s * S.T + j ≤ S.N := by
        simpa [SOptLib.global_index_def] using hjN
      simpa [SOptLib.global_index_def] using
        (show s * S.T + 1 ≤ S.N by omega)
    rw [SOptLib.mem_activeEpochSteps]
    exact ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hstartN⟩
  have h_epoch_start_window :
      SOptLib.global_index S.T s 1 ∈ outputWindow S := by
    simpa [outputWindow] using
      SOptLib.global_index_mem_output_window_of_active_epoch_step
        (T := S.T) (N := S.N) (globalIndex := SOptLib.global_index S.T)
        (s := s) (j := 1) h_epoch_start_pos h_epoch_start_active
  have h_deltaProc_epoch_start_pointwise :
      ∀ ω : AlgorithmSamplePath S, deltaProc (index s 1) ω = 0 := by
    intro ω
    dsimp [deltaProc, index]
    by_cases hk : 1 ≤ SOptLib.global_index S.T s 1
    · have hres :
          paperEstimator S run ⟨SOptLib.global_index S.T s 1, hk⟩ ω =
            SOptLib.finiteUniformAverage S.componentGradient
              (paperIterate S run ⟨SOptLib.global_index S.T s 1, hk⟩ ω) := by
        simpa using h_epoch_start_estimator_eq ω
      simpa [SOptLib.global_index_def] using (sub_eq_zero.mpr hres)
    · exact (hk h_epoch_start_pos).elim
  have h_deltaProc_epoch_start_integral_zero :
      ∫ ω : AlgorithmSamplePath S, ‖deltaProc (index s 1) ω‖ ^ 2 ∂μ = 0 := by
    have hfun :
        (fun ω : AlgorithmSamplePath S => ‖deltaProc (index s 1) ω‖ ^ 2) =
          fun _ => (0 : ℝ) := by
      funext ω
      simp [h_deltaProc_epoch_start_pointwise ω]
    rw [hfun]
    simp [μ]
  have hbase_epoch_start :
      ∫ ω : AlgorithmSamplePath S, ‖deltaProc (index s 1) ω‖ ^ 2 ∂μ ≤
        (S.L ^ 2 / S.b) *
          ∫ ω : AlgorithmSamplePath S,
            SOptLib.epochSquaredDifferenceSum xProc index s 1 ω ∂μ + 0 := by
    rw [h_deltaProc_epoch_start_integral_zero]
    simp [SOptLib.epochSquaredDifferenceSum]
  have hdeltaTerm_epoch_start_zero :
      deltaTerm (SOptLib.global_index S.T s 1) = 0 := by
    rw [hdelta_def]
    have hfun :
        (fun ω : AlgorithmSamplePath S =>
            if hk : SOptLib.global_index S.T s 1 ∈ outputWindow S then
              ‖paperEstimator S run
                  ⟨SOptLib.global_index S.T s 1,
                    (Finset.mem_Icc.mp (by simpa [outputWindow] using hk)).1⟩ ω -
                SOptLib.finiteUniformAverage S.componentGradient
                  (paperIterate S run
                    ⟨SOptLib.global_index S.T s 1,
                      (Finset.mem_Icc.mp (by simpa [outputWindow] using hk)).1⟩ ω)‖ ^ 2
            else 0) = fun _ => (0 : ℝ) := by
      funext ω
      by_cases hk : SOptLib.global_index S.T s 1 ∈ outputWindow S
      · have hres :
            paperEstimator S run
                ⟨SOptLib.global_index S.T s 1,
                  (Finset.mem_Icc.mp (by simpa [outputWindow] using hk)).1⟩ ω =
              SOptLib.finiteUniformAverage S.componentGradient
                (paperIterate S run
                  ⟨SOptLib.global_index S.T s 1,
                    (Finset.mem_Icc.mp (by simpa [outputWindow] using hk)).1⟩ ω) := by
          simpa using h_epoch_start_estimator_eq ω
        rw [dif_pos hk]
        simpa using (sub_eq_zero.mpr hres)
      · exact (hk h_epoch_start_window).elim
    change
      (∫ ω : AlgorithmSamplePath S,
        (if hk : SOptLib.global_index S.T s 1 ∈ outputWindow S then
          ‖paperEstimator S run
              ⟨SOptLib.global_index S.T s 1,
                (Finset.mem_Icc.mp (by simpa [outputWindow] using hk)).1⟩ ω -
            SOptLib.finiteUniformAverage S.componentGradient
              (paperIterate S run
                ⟨SOptLib.global_index S.T s 1,
                  (Finset.mem_Icc.mp (by simpa [outputWindow] using hk)).1⟩ ω)‖ ^ 2
        else 0) ∂algorithmSampleLaw S) = 0
    rw [hfun]
    simp
  -- Direct proof route after the schedule reconstruction: instantiate Lan
  -- Lemma 7.4 through
  -- `SOptLib.epoch_recursive_estimator_second_moment_le_difference_sum`.
  -- The base-case gate now has the source-faithful refresh fact
  -- `h_epoch_start_estimator_eq` and the compiled base facts
  -- `h_deltaProc_epoch_start_integral_zero`, `hbase_epoch_start`, and
  -- `hdeltaTerm_epoch_start_zero`; the remaining work is the stochastic
  -- recursive-estimator second-moment adapter.
  by_cases hj_one : j = 1
  · subst j
    rw [hdeltaTerm_epoch_start_zero]
    simp
  have hj_two : 2 ≤ j := by omega
  have h_current_step :
      SOptLib.stepOfIndex S.T (index s j) = j := by
    dsimp [index]
    exact SOptLib.nat_stepOf_globalIndex_eq (T := S.T) (s := s) (j := j)
      hj_epoch.1 hj_epoch.2
  have h_current_nonrefresh :
      SOptLib.stepOfIndex S.T (index s j) ≠ 1 := by
    rw [h_current_step]
    omega
  have hidx_pred_eq :
      index s j - 1 = index s (j - 1) := by
    dsimp [index]
    simp [SOptLib.global_index_def]
    omega
  have hidx_pos' : 1 ≤ index s j := by
    dsimp [index]
    exact hidx_pos
  have hidx_pred_pos : 1 ≤ index s (j - 1) := by
    dsimp [index]
    simp [SOptLib.global_index_def]
    omega
  have hpaperEstimator_nonrefresh_raw :
      ∀ ω : AlgorithmSamplePath S,
        paperEstimator S run ⟨index s j, hidx_pos'⟩ ω =
          recursiveMiniBatchGradient S
            (run (index s j - 1) ω).current
            (run (index s j - 1) ω).previous
            (run (index s j - 1) ω).estimator
            (fun r => ω (index s j) r) := by
    intro ω
    have hidx_succ : (index s j - 1) + 1 = index s j :=
      Nat.sub_add_cancel hidx_pos'
    have hstep := hrun.2 (index s j - 1) ω
    rw [hidx_succ] at hstep
    dsimp only [outerStepRel, algorithmBatchStream] at hstep
    rcases hstep with ⟨_hx, _hterm, hnext⟩
    have hest := congrArg RunState.estimator hnext
    have hG :
        paperEstimator S run ⟨index s j, hidx_pos'⟩ ω =
          gradientEstimatorUpdate S (index s j)
            (run (index s j - 1) ω).previous
            (run (index s j - 1) ω).current
            (run (index s j - 1) ω).estimator
            (fun r => ω (index s j) r) := by
      simpa [paperEstimator, estimator] using hest
    rw [hG]
    rw [gradientEstimatorUpdate]
    exact if_neg h_current_nonrefresh
  have hrun_current_eq_paper :
      ∀ ω : AlgorithmSamplePath S,
        (run (index s j - 1) ω).current =
          paperIterate S run ⟨index s j, hidx_pos'⟩ ω := by
    intro ω
    simp [paperIterate, iterate, SOptLib.positiveTimeIterateView_eq]
  have hrun_previous_eq_paper_pred :
      ∀ ω : AlgorithmSamplePath S,
        (run (index s j - 1) ω).previous =
          paperIterate S run ⟨index s (j - 1), hidx_pred_pos⟩ ω := by
    intro ω
    have hpred_succ : (index s (j - 1) - 1) + 1 = index s (j - 1) :=
      Nat.sub_add_cancel hidx_pred_pos
    have hstep := hrun.2 (index s (j - 1) - 1) ω
    rw [hpred_succ] at hstep
    dsimp [outerStepRel, algorithmBatchStream] at hstep
    rcases hstep with ⟨_hx, _hterm, hnext⟩
    have hprev := congrArg RunState.previous hnext
    simpa [paperIterate, iterate, SOptLib.positiveTimeIterateView_eq,
      hidx_pred_eq] using hprev
  have hrun_estimator_eq_paper_pred :
      ∀ ω : AlgorithmSamplePath S,
        (run (index s j - 1) ω).estimator =
          paperEstimator S run ⟨index s (j - 1), hidx_pred_pos⟩ ω := by
    intro ω
    simp [paperEstimator, estimator, hidx_pred_eq]
  have hpaperEstimator_nonrefresh :
      ∀ ω : AlgorithmSamplePath S,
        paperEstimator S run ⟨index s j, hidx_pos'⟩ ω =
          recursiveMiniBatchGradient S
            (paperIterate S run ⟨index s j, hidx_pos'⟩ ω)
            (paperIterate S run ⟨index s (j - 1), hidx_pred_pos⟩ ω)
            (paperEstimator S run ⟨index s (j - 1), hidx_pred_pos⟩ ω)
            (fun r => ω (index s j) r) := by
    intro ω
    rw [hpaperEstimator_nonrefresh_raw ω]
    rw [hrun_current_eq_paper ω, hrun_previous_eq_paper_pred ω,
      hrun_estimator_eq_paper_pred ω]
  let centeredMiniBatchIncrement : AlgorithmSamplePath S → E := fun ω =>
    miniBatchCorrection S
      (paperIterate S run ⟨index s j, hidx_pos'⟩ ω)
      (paperIterate S run ⟨index s (j - 1), hidx_pred_pos⟩ ω)
      (fun r => ω (index s j) r) -
    (SOptLib.finiteUniformAverage S.componentGradient (paperIterate S run ⟨index s j, hidx_pos'⟩ ω) -
      SOptLib.finiteUniformAverage S.componentGradient (paperIterate S run ⟨index s (j - 1), hidx_pred_pos⟩ ω))
  have hdeltaProc_nonrefresh_recurrence :
      ∀ ω : AlgorithmSamplePath S,
        deltaProc (index s j) ω =
          deltaProc (index s (j - 1)) ω + centeredMiniBatchIncrement ω := by
    intro ω
    dsimp [deltaProc, centeredMiniBatchIncrement]
    rw [dif_pos hidx_pos', dif_pos hidx_pred_pos]
    rw [hpaperEstimator_nonrefresh ω]
    dsimp [recursiveMiniBatchGradient]
    abel
  have hcenteredMiniBatchIncrement_unfold :
      ∀ ω : AlgorithmSamplePath S,
        centeredMiniBatchIncrement ω =
          (S.b : ℝ)⁻¹ •
              Finset.sum Finset.univ
                (fun r : Fin S.b =>
                  sampledGradientCorrection S
                    (paperIterate S run ⟨index s j, hidx_pos'⟩ ω)
                    (paperIterate S run ⟨index s (j - 1), hidx_pred_pos⟩ ω)
                    (ω (index s j) r)) -
            (SOptLib.finiteUniformAverage S.componentGradient (paperIterate S run ⟨index s j, hidx_pos'⟩ ω) -
              SOptLib.finiteUniformAverage S.componentGradient
                (paperIterate S run ⟨index s (j - 1), hidx_pred_pos⟩ ω)) := by
    intro ω
    simp [centeredMiniBatchIncrement, miniBatchCorrection]
  have hcentered_component_budget :
      ∀ ω : AlgorithmSamplePath S,
        Finset.sum Finset.univ
            (fun i : Fin S.componentCount =>
              componentSamplingProbability S i *
                ‖sampledGradientCorrection S
                    (paperIterate S run ⟨index s j, hidx_pos'⟩ ω)
                    (paperIterate S run ⟨index s (j - 1), hidx_pred_pos⟩ ω) i -
                  (SOptLib.finiteUniformAverage S.componentGradient (paperIterate S run ⟨index s j, hidx_pos'⟩ ω) -
                    SOptLib.finiteUniformAverage S.componentGradient
                      (paperIterate S run ⟨index s (j - 1), hidx_pred_pos⟩ ω))‖ ^ 2) ≤
          S.L ^ 2 *
            ‖paperIterate S run ⟨index s j, hidx_pos'⟩ ω -
              paperIterate S run ⟨index s (j - 1), hidx_pred_pos⟩ ω‖ ^ 2 := by
    intro ω
    exact
      sampledGradientCorrection_centered_weighted_second_moment_le
        S
        (paperIterate_mem_of_runStateSpec S (algorithmBatchStream S) run hrun
          ⟨index s j, hidx_pos'⟩ ω)
        (paperIterate_mem_of_runStateSpec S (algorithmBatchStream S) run hrun
          ⟨index s (j - 1), hidx_pred_pos⟩ ω)
  have hcurrent_coordinate_law :
      ∀ r : Fin S.b,
        Measure.map (fun ω : AlgorithmSamplePath S => ω (index s j) r) μ =
          (componentSamplingPMF S).toMeasure := by
    intro r
    simpa [μ] using hLaw.2.2 (index s j) r
  have hcurrent_coordinate_identDistrib :
      ∀ r : Fin S.b,
        IdentDistrib (fun ω : AlgorithmSamplePath S => ω (index s j) r)
          (fun i : Fin S.componentCount => i) μ
          (componentSamplingPMF S).toMeasure := by
    intro r
    have hmeas :
        Measurable (fun ω : AlgorithmSamplePath S => ω (index s j) r) :=
      (measurable_pi_apply r).comp (measurable_pi_apply (index s j))
    refine ⟨hmeas.aemeasurable, measurable_id.aemeasurable, ?_⟩
    simpa using hcurrent_coordinate_law r
  let eps : Fin S.b → AlgorithmSamplePath S → E := fun r ω =>
    sampledGradientCorrection S
      (paperIterate S run ⟨index s j, hidx_pos'⟩ ω)
      (paperIterate S run ⟨index s (j - 1), hidx_pred_pos⟩ ω)
      (ω (index s j) r) -
    (SOptLib.finiteUniformAverage S.componentGradient (paperIterate S run ⟨index s j, hidx_pos'⟩ ω) -
      SOptLib.finiteUniformAverage S.componentGradient
        (paperIterate S run ⟨index s (j - 1), hidx_pred_pos⟩ ω))
  have hcenteredMiniBatchIncrement_as_average :
      ∀ ω : AlgorithmSamplePath S,
        centeredMiniBatchIncrement ω =
          (S.b : ℝ)⁻¹ • Finset.sum Finset.univ (fun r : Fin S.b => eps r ω) := by
    intro ω
    rw [hcenteredMiniBatchIncrement_unfold ω]
    have hcenter :=
      inv_card_smul_sum_sub_const_eq
        (s := (Finset.univ : Finset (Fin S.b)))
        (z := fun r : Fin S.b =>
          sampledGradientCorrection S
            (paperIterate S run ⟨index s j, hidx_pos'⟩ ω)
            (paperIterate S run ⟨index s (j - 1), hidx_pred_pos⟩ ω)
            (ω (index s j) r))
        (c := SOptLib.finiteUniformAverage S.componentGradient (paperIterate S run ⟨index s j, hidx_pos'⟩ ω) -
          SOptLib.finiteUniformAverage S.componentGradient
            (paperIterate S run ⟨index s (j - 1), hidx_pred_pos⟩ ω))
        (by simp [S.hb_pos])
    simpa [eps, Finset.card_univ] using hcenter.symm
  have hprev_active :
      j - 1 ∈ SOptLib.activeEpochSteps S.T S.N index s := by
    have hjN :
        index s j ≤ S.N :=
      SOptLib.activeEpochSteps_globalIndex_le (T := S.T) (N := S.N)
        (globalIndex := index) (s := s) (j := j) hj
    rw [SOptLib.mem_activeEpochSteps]
    refine ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    dsimp [index] at hjN ⊢
    simp [SOptLib.global_index_def] at hjN ⊢
    omega
  have hidx_pred_window : index s (j - 1) ∈ outputWindow S := by
    simpa [index, outputWindow] using
      SOptLib.global_index_mem_output_window_of_active_epoch_step
        (T := S.T) (N := S.N) (globalIndex := index)
        (s := s) (j := j - 1) hidx_pred_pos hprev_active
  have hdeltaProc_current_sq_int :
      Integrable (fun ω : AlgorithmSamplePath S =>
        ‖deltaProc (index s j) ω‖ ^ 2) μ := by
    have hreg :=
      theorem718_finite_prefix_observable_integrability S run hrun
        (index s j) (by simpa [index] using hidx_window)
    simpa [deltaProc, μ, dif_pos hidx_pos'] using hreg.2.1
  have hdeltaProc_prev_sq_int :
      Integrable (fun ω : AlgorithmSamplePath S =>
        ‖deltaProc (index s (j - 1)) ω‖ ^ 2) μ := by
    have hreg :=
      theorem718_finite_prefix_observable_integrability S run hrun
        (index s (j - 1)) (by simpa [index] using hidx_pred_window)
    simpa [deltaProc, μ, dif_pos hidx_pred_pos] using hreg.2.1
  have heps_sq_int :
      ∀ r : Fin S.b,
        Integrable (fun ω : AlgorithmSamplePath S => ‖eps r ω‖ ^ 2) μ := by
    intro r
    refine integrable_algorithmSampleLaw_of_prefix_const S (index s j) ?_
    intro ω ω' hprefix
    have hrun_current :
        run (index s j - 1) ω = run (index s j - 1) ω' :=
      runState_eq_of_batch_prefix_eq S (algorithmBatchStream S) run hrun
        (index s j - 1) ω ω' (fun q hq a => by
          exact hprefix q (by omega) a)
    have hrun_pred :
        run (index s (j - 1) - 1) ω = run (index s (j - 1) - 1) ω' :=
      runState_eq_of_batch_prefix_eq S (algorithmBatchStream S) run hrun
        (index s (j - 1) - 1) ω ω' (fun q hq a => by
          exact hprefix q (by
            dsimp [index] at hq ⊢
            simp [SOptLib.global_index_def] at hq ⊢
            omega) a)
    have hsample : ω (index s j) r = ω' (index s j) r :=
      hprefix (index s j) (le_rfl) r
    have heq : eps r ω = eps r ω' := by
      dsimp [eps]
      simpa [paperIterate, iterate, SOptLib.positiveTimeIterateView_eq,
        hrun_current, hrun_pred, hsample]
    simpa [heq]
  have heps_meas :
      ∀ r : Fin S.b, AEStronglyMeasurable (eps r) μ := by
    intro r
    change AEStronglyMeasurable (eps r) (algorithmSampleLaw S)
    refine aestronglyMeasurable_algorithmSampleLaw_of_prefix_const S (index s j) ?_
    intro ω ω' hprefix
    have hrun_current :
        run (index s j - 1) ω = run (index s j - 1) ω' :=
      runState_eq_of_batch_prefix_eq S (algorithmBatchStream S) run hrun
        (index s j - 1) ω ω' (fun q hq a => by
          exact hprefix q (by omega) a)
    have hrun_pred :
        run (index s (j - 1) - 1) ω = run (index s (j - 1) - 1) ω' :=
      runState_eq_of_batch_prefix_eq S (algorithmBatchStream S) run hrun
        (index s (j - 1) - 1) ω ω' (fun q hq a => by
          exact hprefix q (by
            dsimp [index] at hq ⊢
            simp [SOptLib.global_index_def] at hq ⊢
            omega) a)
    have hsample : ω (index s j) r = ω' (index s j) r :=
      hprefix (index s j) (le_rfl) r
    dsimp [eps]
    simpa [paperIterate, iterate, SOptLib.positiveTimeIterateView_eq,
      hrun_current, hrun_pred, hsample]
  let sampleCoord : ℕ × Fin S.b → AlgorithmSamplePath S → Fin S.componentCount :=
    fun kr ω => ω kr.1 kr.2
  have hsampleCoord_meas : ∀ q, Measurable (sampleCoord q) := by
    intro q
    dsimp [sampleCoord]
    exact (measurable_pi_apply q.2).comp (measurable_pi_apply q.1)
  have hsampleCoord_iIndep : iIndepFun sampleCoord μ := by
    simpa [sampleCoord, μ] using hLaw.2.1
  let strictPrefixKey : AlgorithmSamplePath S →
      (Fin (index s j) → Fin S.b → Fin S.componentCount) :=
    fun ω q r => ω q.1 r
  have hstrictPrefixKey_meas : Measurable strictPrefixKey := by
    dsimp [strictPrefixKey]
    refine measurable_pi_lambda _ ?_
    intro q
    refine measurable_pi_lambda _ ?_
    intro r
    exact (measurable_pi_apply r).comp (measurable_pi_apply q.1)
  have hdeltaTerm_current_eq :
      deltaTerm (index s j) =
        ∫ ω : AlgorithmSamplePath S, ‖deltaProc (index s j) ω‖ ^ 2 ∂μ := by
    rw [hdelta_def]
    refine integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro ω
    have hwin : s * S.T + j ∈ outputWindow S := by
      simpa [index, SOptLib.global_index_def] using hidx_window
    have hpos : 1 ≤ s * S.T + j := by
      simpa [index, SOptLib.global_index_def] using hidx_pos'
    simp [deltaProc, μ, index, SOptLib.global_index_def, hwin, hpos]
  have hcenteredMiniBatchIncrement_secondMoment_of_eps :
      (∀ r : Fin S.b, AEStronglyMeasurable (eps r) μ) →
      (∀ r : Fin S.b,
        Integrable (fun ω : AlgorithmSamplePath S => ‖eps r ω‖ ^ 2) μ ∧
          ∫ ω : AlgorithmSamplePath S, ‖eps r ω‖ ^ 2 ∂μ ≤
            S.L ^ 2 *
              ∫ ω : AlgorithmSamplePath S,
                ‖xProc (index s j) ω - xProc (index s (j - 1)) ω‖ ^ 2 ∂μ) →
      (∀ r ∈ (Finset.univ : Finset (Fin S.b)),
        ∀ q ∈ (Finset.univ : Finset (Fin S.b)), r ≠ q →
          ∫ ω : AlgorithmSamplePath S, ⟪eps r ω, eps q ω⟫_ℝ ∂μ = 0) →
      ∫ ω : AlgorithmSamplePath S, ‖centeredMiniBatchIncrement ω‖ ^ 2 ∂μ ≤
        (S.L ^ 2 *
          ∫ ω : AlgorithmSamplePath S,
            ‖xProc (index s j) ω - xProc (index s (j - 1)) ω‖ ^ 2 ∂μ) /
          (S.b : ℝ) := by
    intro heps_meas heps_diag heps_cross
    have hbatch :=
      centeredMiniBatchAverage_secondMoment_le_variance_div_card_of_cross_zero
        (P := μ) (I := (Finset.univ : Finset (Fin S.b))) (m := S.b)
        (eps := eps)
        (varianceBudget :=
          S.L ^ 2 *
            ∫ ω : AlgorithmSamplePath S,
              ‖xProc (index s j) ω - xProc (index s (j - 1)) ω‖ ^ 2 ∂μ)
        S.hb_pos (by simp [Finset.card_univ])
        (fun r _hr => heps_meas r)
        (fun r _hr => heps_diag r)
        heps_cross
    calc
      ∫ ω : AlgorithmSamplePath S, ‖centeredMiniBatchIncrement ω‖ ^ 2 ∂μ =
          ∫ ω : AlgorithmSamplePath S,
            ‖(S.b : ℝ)⁻¹ • Finset.sum Finset.univ (fun r : Fin S.b => eps r ω)‖ ^ 2 ∂μ := by
            refine integral_congr_ae (Filter.Eventually.of_forall ?_)
            intro ω
            change
              ‖centeredMiniBatchIncrement ω‖ ^ 2 =
                ‖(S.b : ℝ)⁻¹ • Finset.sum Finset.univ
                  (fun r : Fin S.b => eps r ω)‖ ^ 2
            exact
              congrArg (fun z : E => ‖z‖ ^ 2)
                (hcenteredMiniBatchIncrement_as_average ω)
      _ ≤
          (S.L ^ 2 *
            ∫ ω : AlgorithmSamplePath S,
              ‖xProc (index s j) ω - xProc (index s (j - 1)) ω‖ ^ 2 ∂μ) /
            (S.b : ℝ) := hbatch
  let sampleMS : MeasurableSpace (Fin S.componentCount) :=
    Fin.instMeasurableSpace S.componentCount
  let pathMS : MeasurableSpace (AlgorithmSamplePath S) := inferInstance
  let pastSet : Set (ℕ × Fin S.b) := {kr | kr.1 < index s j}
  let strictPast : MeasurableSpace (AlgorithmSamplePath S) :=
    ⨆ q ∈ pastSet, MeasurableSpace.comap (sampleCoord q) sampleMS
  have hstrict_le :
      strictPast ≤
        (⨆ q ∈ pastSet,
          MeasurableSpace.comap (sampleCoord q) sampleMS) := by
    rfl
  have hstrictPrefix_coord_meas :
      ∀ q : Fin (index s j), ∀ r : Fin S.b,
        Measurable[strictPast]
          (fun ω : AlgorithmSamplePath S => sampleCoord (q.1, r) ω) := by
    intro q r
    have hqmem : (q.1, r) ∈ pastSet := by
      dsimp [pastSet]
      exact q.2
    exact measurable_iff_comap_le.mpr
      (le_iSup_of_le (q.1, r) (le_iSup_of_le hqmem le_rfl))
  have hstrictPrefixKey_meas_strictPast :
      Measurable[strictPast] strictPrefixKey := by
    dsimp [strictPrefixKey]
    refine measurable_pi_lambda _ ?_
    intro q
    refine measurable_pi_lambda _ ?_
    intro r
    simpa [sampleCoord] using hstrictPrefix_coord_meas q r
  let mPair : ℕ × Fin S.b → MeasurableSpace (AlgorithmSamplePath S) :=
    fun q => MeasurableSpace.comap (sampleCoord q) sampleMS
  have hiPair : ProbabilityTheory.iIndep mPair μ := by
    simpa [mPair, sampleMS] using hsampleCoord_iIndep.iIndep
  have h_mPair_le : ∀ q, mPair q ≤ pathMS := by
    intro q
    simpa [mPair, sampleMS, pathMS] using (hsampleCoord_meas q).comap_le
  have hstrictPast_current_sigma_indep :
      ∀ r : Fin S.b,
        ProbabilityTheory.Indep strictPast
          (MeasurableSpace.comap (sampleCoord (index s j, r)) sampleMS) μ := by
    intro r
    have hpast_disj :
        Disjoint pastSet ({(index s j, r)} : Set (ℕ × Fin S.b)) := by
      refine Set.disjoint_left.2 ?_
      intro x hxpast hxcur
      rcases hxcur with rfl
      exact (Nat.lt_irrefl (index s j)) (by simpa [pastSet] using hxpast)
    have hpast_iSup_indep_current_iSup :
        ProbabilityTheory.Indep
          (⨆ q ∈ pastSet, mPair q)
          (⨆ q ∈ ({(index s j, r)} : Set (ℕ × Fin S.b)), mPair q) μ :=
      ProbabilityTheory.indep_iSup_of_disjoint
        (Ω := AlgorithmSamplePath S) (ι := ℕ × Fin S.b)
        (m := mPair) (_mΩ := pathMS) (μ := μ)
        h_mPair_le hiPair hpast_disj
    have hpast_indep_current :
        ProbabilityTheory.Indep
          (⨆ q ∈ pastSet, MeasurableSpace.comap (sampleCoord q) sampleMS)
          (MeasurableSpace.comap (sampleCoord (index s j, r)) sampleMS) μ := by
      simpa [mPair] using hpast_iSup_indep_current_iSup
    exact ProbabilityTheory.indep_of_indep_of_le_left
      hpast_indep_current hstrict_le
  have hstrictPrefix_current_indep :
      ∀ r : Fin S.b,
        IndepFun strictPrefixKey
          (fun ω : AlgorithmSamplePath S => ω (index s j) r) μ := by
    intro r
    rw [IndepFun_iff_Indep]
    exact ProbabilityTheory.indep_of_indep_of_le_left
      (by simpa [sampleCoord, sampleMS] using hstrictPast_current_sigma_indep r)
      hstrictPrefixKey_meas_strictPast.comap_le
  have hstrictPast_peer_current_sigma_indep :
      ∀ r q : Fin S.b, r ≠ q →
        ProbabilityTheory.Indep
          (strictPast ⊔
            MeasurableSpace.comap (sampleCoord (index s j, r)) sampleMS)
          (MeasurableSpace.comap (sampleCoord (index s j, q)) sampleMS) μ := by
    intro r q hrq
    have hleft_disj :
        Disjoint
          (pastSet ∪ ({(index s j, r)} : Set (ℕ × Fin S.b)))
          ({(index s j, q)} : Set (ℕ × Fin S.b)) := by
      refine Set.disjoint_left.2 ?_
      intro x hxleft hxcur
      rcases hxcur with rfl
      rcases hxleft with hxpast | hxpeer
      · exact (Nat.lt_irrefl (index s j)) (by simpa [pastSet] using hxpast)
      · have hpair_eq : (index s j, q) = (index s j, r) := by
          simpa using hxpeer
        exact hrq (by simpa using congrArg Prod.snd hpair_eq.symm)
    have henlarged_iSup_indep_current_iSup :
        ProbabilityTheory.Indep
          (⨆ u ∈ pastSet ∪ ({(index s j, r)} : Set (ℕ × Fin S.b)), mPair u)
          (⨆ u ∈ ({(index s j, q)} : Set (ℕ × Fin S.b)), mPair u) μ :=
      ProbabilityTheory.indep_iSup_of_disjoint
        (Ω := AlgorithmSamplePath S) (ι := ℕ × Fin S.b)
        (m := mPair) (_mΩ := pathMS) (μ := μ)
        h_mPair_le hiPair hleft_disj
    have henlarged_indep_current :
        ProbabilityTheory.Indep
          (⨆ u ∈ pastSet ∪ ({(index s j, r)} : Set (ℕ × Fin S.b)),
            MeasurableSpace.comap (sampleCoord u) sampleMS)
          (MeasurableSpace.comap (sampleCoord (index s j, q)) sampleMS) μ := by
      simpa [mPair] using henlarged_iSup_indep_current_iSup
    have hleft_le :
        strictPast ⊔
            MeasurableSpace.comap (sampleCoord (index s j, r)) sampleMS ≤
          (⨆ u ∈ pastSet ∪ ({(index s j, r)} : Set (ℕ × Fin S.b)),
            MeasurableSpace.comap (sampleCoord u) sampleMS) := by
      refine sup_le ?_ ?_
      · exact le_trans hstrict_le <| by
          refine iSup_le ?_
          intro u
          refine iSup_le ?_
          intro hu
          exact le_iSup_of_le u (le_iSup_of_le (Or.inl hu) le_rfl)
      · exact le_iSup_of_le (index s j, r)
          (le_iSup_of_le (Or.inr rfl) le_rfl)
    exact ProbabilityTheory.indep_of_indep_of_le_left
      henlarged_indep_current hleft_le
  have hstrictPrefix_peer_current_indep :
      ∀ r q : Fin S.b, r ≠ q →
        IndepFun
          (fun ω : AlgorithmSamplePath S =>
            (strictPrefixKey ω, ω (index s j) r))
          (fun ω : AlgorithmSamplePath S => ω (index s j) q) μ := by
    intro r q hrq
    have hleft_meas :
        Measurable[
            strictPast ⊔
              MeasurableSpace.comap (sampleCoord (index s j, r)) sampleMS]
          (fun ω : AlgorithmSamplePath S =>
            (strictPrefixKey ω, sampleCoord (index s j, r) ω)) := by
      have hX :
          Measurable[
              strictPast ⊔
                MeasurableSpace.comap (sampleCoord (index s j, r)) sampleMS]
            strictPrefixKey :=
        hstrictPrefixKey_meas_strictPast.mono le_sup_left le_rfl
      have hY :
          Measurable[
              strictPast ⊔
                MeasurableSpace.comap (sampleCoord (index s j, r)) sampleMS]
            (sampleCoord (index s j, r)) := by
        exact measurable_iff_comap_le.mpr le_sup_right
      exact hX.prodMk hY
    rw [IndepFun_iff_Indep]
    exact ProbabilityTheory.indep_of_indep_of_le_left
      (by
        simpa [sampleCoord, sampleMS] using
          hstrictPast_peer_current_sigma_indep r q hrq)
      (by simpa [sampleCoord] using hleft_meas.comap_le)
  have heps_diag :
      ∀ r : Fin S.b,
        Integrable (fun ω : AlgorithmSamplePath S => ‖eps r ω‖ ^ 2) μ ∧
          ∫ ω : AlgorithmSamplePath S, ‖eps r ω‖ ^ 2 ∂μ ≤
            S.L ^ 2 *
              ∫ ω : AlgorithmSamplePath S,
                ‖xProc (index s j) ω - xProc (index s (j - 1)) ω‖ ^ 2 ∂μ := by
    intro r
    haveI : IsProbabilityMeasure μ := by
      simpa [μ] using hLaw.1
    refine ⟨heps_sq_int r, ?_⟩
    let Prefix := Fin (index s j) → Fin S.b → Fin S.componentCount
    let defaultComponent : Fin S.componentCount := ⟨0, S.hcomponentCount_pos⟩
    let pathOfPrefix : Prefix → AlgorithmSamplePath S :=
      fun w k a => if hk : k < index s j then w ⟨k, hk⟩ a else defaultComponent
    let currentFromPrefix : Prefix → E :=
      fun w => paperIterate S run ⟨index s j, hidx_pos'⟩ (pathOfPrefix w)
    let previousFromPrefix : Prefix → E :=
      fun w => paperIterate S run ⟨index s (j - 1), hidx_pred_pos⟩ (pathOfPrefix w)
    let φ : Prefix → Fin S.componentCount → ℝ :=
      fun w i =>
        ‖sampledGradientCorrection S (currentFromPrefix w) (previousFromPrefix w) i -
          (SOptLib.finiteUniformAverage S.componentGradient (currentFromPrefix w) -
            SOptLib.finiteUniformAverage S.componentGradient (previousFromPrefix w))‖ ^ 2
    let B : Prefix → ℝ :=
      fun w => S.L ^ 2 * ‖currentFromPrefix w - previousFromPrefix w‖ ^ 2
    have hcurrent_reconstruct :
        ∀ ω : AlgorithmSamplePath S,
          currentFromPrefix (strictPrefixKey ω) =
            paperIterate S run ⟨index s j, hidx_pos'⟩ ω := by
      intro ω
      have hrun_current :
          run (index s j - 1) (pathOfPrefix (strictPrefixKey ω)) =
            run (index s j - 1) ω :=
        runState_eq_of_batch_prefix_eq S (algorithmBatchStream S) run hrun
          (index s j - 1) (pathOfPrefix (strictPrefixKey ω)) ω
          (fun q hq a => by
            have hqlt : q < index s j := by omega
            dsimp [pathOfPrefix, strictPrefixKey]
            simp [algorithmBatchStream, hqlt])
      dsimp [currentFromPrefix]
      simpa [paperIterate, iterate, SOptLib.positiveTimeIterateView_eq,
        hrun_current]
    have hprevious_reconstruct :
        ∀ ω : AlgorithmSamplePath S,
          previousFromPrefix (strictPrefixKey ω) =
            paperIterate S run ⟨index s (j - 1), hidx_pred_pos⟩ ω := by
      intro ω
      have hrun_previous :
          run (index s (j - 1) - 1) (pathOfPrefix (strictPrefixKey ω)) =
            run (index s (j - 1) - 1) ω :=
        runState_eq_of_batch_prefix_eq S (algorithmBatchStream S) run hrun
          (index s (j - 1) - 1) (pathOfPrefix (strictPrefixKey ω)) ω
          (fun q hq a => by
            have hqlt : q < index s j := by
              dsimp [index] at hq ⊢
              simp [SOptLib.global_index_def] at hq ⊢
              omega
            dsimp [pathOfPrefix, strictPrefixKey]
            simp [algorithmBatchStream, hqlt])
      dsimp [previousFromPrefix]
      simpa [paperIterate, iterate, SOptLib.positiveTimeIterateView_eq,
        hrun_previous]
    have hxProc_current :
        ∀ ω : AlgorithmSamplePath S,
          xProc (index s j) ω = currentFromPrefix (strictPrefixKey ω) := by
      intro ω
      simpa [xProc, hidx_pos'] using (hcurrent_reconstruct ω).symm
    have hxProc_previous :
        ∀ ω : AlgorithmSamplePath S,
          xProc (index s (j - 1)) ω = previousFromPrefix (strictPrefixKey ω) := by
      intro ω
      simpa [xProc, hidx_pred_pos] using (hprevious_reconstruct ω).symm
    have hφ_meas : Measurable (Function.uncurry φ) := by
      exact measurable_of_finite _
    have hB_meas : Measurable B := by
      exact measurable_of_finite _
    have hX_meas :
        @Measurable (AlgorithmSamplePath S) Prefix pathMS inferInstance strictPrefixKey := by
      simpa [Prefix, pathMS] using hstrictPrefixKey_meas
    have hY_meas :
        @Measurable (AlgorithmSamplePath S) (Fin S.componentCount) pathMS sampleMS
          (fun ω : AlgorithmSamplePath S => ω (index s j) r) := by
      simpa [sampleCoord, pathMS, sampleMS] using hsampleCoord_meas (index s j, r)
    have hφ_comp_eq :
        (fun ω : AlgorithmSamplePath S =>
            φ (strictPrefixKey ω) (ω (index s j) r)) =
          fun ω : AlgorithmSamplePath S => ‖eps r ω‖ ^ 2 := by
      funext ω
      dsimp [φ, eps]
      simp [hcurrent_reconstruct ω, hprevious_reconstruct ω]
    have hφ_comp_int :
        Integrable[pathMS]
          (fun ω : AlgorithmSamplePath S =>
            φ (strictPrefixKey ω) (ω (index s j) r)) μ := by
      simpa [hφ_comp_eq, pathMS] using heps_sq_int r
    have hB_comp_int :
        Integrable[pathMS] (fun ω : AlgorithmSamplePath S => B (strictPrefixKey ω)) μ := by
      have hB_comp_meas :
          AEStronglyMeasurable[pathMS]
            (fun ω : AlgorithmSamplePath S => B (strictPrefixKey ω)) μ :=
        (hB_meas.comp hX_meas).aestronglyMeasurable
      have hfin :
          (Set.range (fun ω : AlgorithmSamplePath S => B (strictPrefixKey ω))).Finite := by
        refine (Set.finite_range B).subset ?_
        intro z hz
        rcases hz with ⟨ω, rfl⟩
        exact ⟨strictPrefixKey ω, rfl⟩
      letI : MeasurableSpace (AlgorithmSamplePath S) := pathMS
      exact integrable_of_finite_range hB_comp_meas hfin
    have hpmf_atom :
        ∀ i : Fin S.componentCount,
          ((componentSamplingPMF S) i).toReal = componentSamplingProbability S i := by
      intro i
      calc
        ((componentSamplingPMF S) i).toReal =
            (ENNReal.ofReal (SOptLib.smoothnessImportanceWeight
              (fun i : Fin S.componentCount => S.componentL i)
              (S.componentCount : ℝ) S.L i)).toReal := by
          rw [componentSamplingPMF, SOptLib.smoothnessImportancePMF_apply]
        _ = SOptLib.smoothnessImportanceWeight
              (fun i : Fin S.componentCount => S.componentL i)
              (S.componentCount : ℝ) S.L i := by
          rw [ENNReal.toReal_ofReal]
          simpa [componentSamplingProbability, SOptLib.smoothnessImportanceWeight] using
            componentSamplingProbability_nonneg S i
        _ = componentSamplingProbability S i := by
          simp [componentSamplingProbability, SOptLib.smoothnessImportanceWeight]
    have hfixed_bound :
        ∀ w : Prefix, ∫ i, φ w i ∂(componentSamplingPMF S).toMeasure ≤ B w := by
      intro w
      have hid :
          IdentDistrib (fun i : Fin S.componentCount => i)
            (fun i : Fin S.componentCount => i)
            (componentSamplingPMF S).toMeasure
            (componentSamplingPMF S).toMeasure := by
        exact IdentDistrib.refl measurable_id.aemeasurable
      have htransport :=
        identDistrib_finite_pmf_integrable_integral_le_weighted_sum_bound
          (P := (componentSamplingPMF S).toMeasure)
          (sample := fun i : Fin S.componentCount => i)
          (pmf := componentSamplingPMF S)
          (q := componentSamplingProbability S)
          (phi := φ w)
          (C := B w)
          hid hpmf_atom
          (by
            dsimp [φ, B]
            simpa using hcentered_component_budget (pathOfPrefix w))
      exact htransport.2
    have htransport :
        ∫ ω : AlgorithmSamplePath S,
            φ (strictPrefixKey ω) (ω (index s j) r) ∂μ ≤
          ∫ ω : AlgorithmSamplePath S, B (strictPrefixKey ω) ∂μ :=
      by
        letI : MeasurableSpace (AlgorithmSamplePath S) := pathMS
        exact
          integral_comp_le_integral_bound_of_indep_fixed_integral_bound
            (P := μ) (ν := (componentSamplingPMF S).toMeasure)
            (φ := φ) (B := B) (X := strictPrefixKey)
            (Y := fun ω : AlgorithmSamplePath S => ω (index s j) r)
            hφ_meas hB_meas hX_meas hY_meas
            (hstrictPrefix_current_indep r) (hcurrent_coordinate_law r)
            hφ_comp_int hB_comp_int hfixed_bound
    have hB_comp_eq :
        (fun ω : AlgorithmSamplePath S => B (strictPrefixKey ω)) =
          fun ω : AlgorithmSamplePath S =>
            S.L ^ 2 *
              ‖xProc (index s j) ω - xProc (index s (j - 1)) ω‖ ^ 2 := by
      funext ω
      dsimp [B]
      simp [hxProc_current ω, hxProc_previous ω]
    calc
      ∫ ω : AlgorithmSamplePath S, ‖eps r ω‖ ^ 2 ∂μ =
          ∫ ω : AlgorithmSamplePath S,
            φ (strictPrefixKey ω) (ω (index s j) r) ∂μ := by
            rw [hφ_comp_eq]
      _ ≤ ∫ ω : AlgorithmSamplePath S, B (strictPrefixKey ω) ∂μ := htransport
      _ =
          ∫ ω : AlgorithmSamplePath S,
            S.L ^ 2 *
              ‖xProc (index s j) ω - xProc (index s (j - 1)) ω‖ ^ 2 ∂μ := by
            rw [hB_comp_eq]
      _ =
          S.L ^ 2 *
            ∫ ω : AlgorithmSamplePath S,
              ‖xProc (index s j) ω - xProc (index s (j - 1)) ω‖ ^ 2 ∂μ := by
            rw [integral_const_mul]
  have hbatch_from_cross :
      (∀ r ∈ (Finset.univ : Finset (Fin S.b)),
        ∀ q ∈ (Finset.univ : Finset (Fin S.b)), r ≠ q →
          ∫ ω : AlgorithmSamplePath S, ⟪eps r ω, eps q ω⟫_ℝ ∂μ = 0) →
      ∫ ω : AlgorithmSamplePath S, ‖centeredMiniBatchIncrement ω‖ ^ 2 ∂μ ≤
        (S.L ^ 2 *
          ∫ ω : AlgorithmSamplePath S,
            ‖xProc (index s j) ω - xProc (index s (j - 1)) ω‖ ^ 2 ∂μ) /
          (S.b : ℝ) :=
    hcenteredMiniBatchIncrement_secondMoment_of_eps heps_meas heps_diag
  have heps_cross :
      ∀ r ∈ (Finset.univ : Finset (Fin S.b)),
        ∀ q ∈ (Finset.univ : Finset (Fin S.b)), r ≠ q →
          ∫ ω : AlgorithmSamplePath S, ⟪eps r ω, eps q ω⟫_ℝ ∂μ = 0 := by
    intro r _hr q _hq hrq
    haveI : IsProbabilityMeasure μ := by
      simpa [μ] using hLaw.1
    let Prefix := Fin (index s j) → Fin S.b → Fin S.componentCount
    let defaultComponent : Fin S.componentCount := ⟨0, S.hcomponentCount_pos⟩
    let pathOfPrefix : Prefix → AlgorithmSamplePath S :=
      fun w k a => if hk : k < index s j then w ⟨k, hk⟩ a else defaultComponent
    let currentFromPrefix : Prefix → E :=
      fun w => paperIterate S run ⟨index s j, hidx_pos'⟩ (pathOfPrefix w)
    let previousFromPrefix : Prefix → E :=
      fun w => paperIterate S run ⟨index s (j - 1), hidx_pred_pos⟩ (pathOfPrefix w)
    let centeredCorrection : Prefix → Fin S.componentCount → E :=
      fun w i =>
        sampledGradientCorrection S (currentFromPrefix w) (previousFromPrefix w) i -
          (SOptLib.finiteUniformAverage S.componentGradient (currentFromPrefix w) -
            SOptLib.finiteUniformAverage S.componentGradient (previousFromPrefix w))
    let leftResidual : Prefix × Fin S.componentCount → E :=
      fun wi => centeredCorrection wi.1 wi.2
    let φ : Prefix × Fin S.componentCount → Fin S.componentCount → ℝ :=
      fun wi i => ⟪leftResidual wi, centeredCorrection wi.1 i⟫_ℝ
    have hcurrent_reconstruct :
        ∀ ω : AlgorithmSamplePath S,
          currentFromPrefix (strictPrefixKey ω) =
            paperIterate S run ⟨index s j, hidx_pos'⟩ ω := by
      intro ω
      have hrun_current :
          run (index s j - 1) (pathOfPrefix (strictPrefixKey ω)) =
            run (index s j - 1) ω :=
        runState_eq_of_batch_prefix_eq S (algorithmBatchStream S) run hrun
          (index s j - 1) (pathOfPrefix (strictPrefixKey ω)) ω
          (fun q hq a => by
            have hqlt : q < index s j := by omega
            dsimp [pathOfPrefix, strictPrefixKey]
            simp [algorithmBatchStream, hqlt])
      dsimp [currentFromPrefix]
      simpa [paperIterate, iterate, SOptLib.positiveTimeIterateView_eq,
        hrun_current]
    have hprevious_reconstruct :
        ∀ ω : AlgorithmSamplePath S,
          previousFromPrefix (strictPrefixKey ω) =
            paperIterate S run ⟨index s (j - 1), hidx_pred_pos⟩ ω := by
      intro ω
      have hrun_previous :
          run (index s (j - 1) - 1) (pathOfPrefix (strictPrefixKey ω)) =
            run (index s (j - 1) - 1) ω :=
        runState_eq_of_batch_prefix_eq S (algorithmBatchStream S) run hrun
          (index s (j - 1) - 1) (pathOfPrefix (strictPrefixKey ω)) ω
          (fun q hq a => by
            have hqlt : q < index s j := by
              dsimp [index] at hq ⊢
              simp [SOptLib.global_index_def] at hq ⊢
              omega
            dsimp [pathOfPrefix, strictPrefixKey]
            simp [algorithmBatchStream, hqlt])
      dsimp [previousFromPrefix]
      simpa [paperIterate, iterate, SOptLib.positiveTimeIterateView_eq,
        hrun_previous]
    have hφ_meas : Measurable (Function.uncurry φ) := by
      exact measurable_of_finite _
    have hX_meas :
        @Measurable (AlgorithmSamplePath S)
          (Prefix × Fin S.componentCount) pathMS inferInstance
          (fun ω : AlgorithmSamplePath S =>
            (strictPrefixKey ω, ω (index s j) r)) := by
      have hprefix_meas :
          @Measurable (AlgorithmSamplePath S) Prefix pathMS inferInstance strictPrefixKey := by
        simpa [Prefix, pathMS] using hstrictPrefixKey_meas
      have hr_meas :
          @Measurable (AlgorithmSamplePath S) (Fin S.componentCount) pathMS sampleMS
            (fun ω : AlgorithmSamplePath S => ω (index s j) r) := by
        simpa [sampleCoord] using hsampleCoord_meas (index s j, r)
      exact hprefix_meas.prodMk hr_meas
    have hY_meas :
        @Measurable (AlgorithmSamplePath S) (Fin S.componentCount) pathMS sampleMS
          (fun ω : AlgorithmSamplePath S => ω (index s j) q) := by
      simpa [sampleCoord] using hsampleCoord_meas (index s j, q)
    have hcomp_eq :
        (fun ω : AlgorithmSamplePath S =>
            φ (strictPrefixKey ω, ω (index s j) r) (ω (index s j) q)) =
          fun ω : AlgorithmSamplePath S => ⟪eps r ω, eps q ω⟫_ℝ := by
      funext ω
      dsimp [φ, leftResidual, centeredCorrection, eps]
      simp [hcurrent_reconstruct ω, hprevious_reconstruct ω]
    have hcomp_int :
        Integrable[pathMS]
          (fun ω : AlgorithmSamplePath S =>
            φ (strictPrefixKey ω, ω (index s j) r) (ω (index s j) q)) μ := by
      rw [hcomp_eq]
      letI : MeasurableSpace (AlgorithmSamplePath S) := pathMS
      simpa [pathMS] using integrable_inner_of_integrable_sq_norm
        (heps_meas r) (heps_meas q) (heps_sq_int r) (heps_sq_int q)
    have hfixed_zero :
        ∀ wi : Prefix × Fin S.componentCount,
          ∫ i : Fin S.componentCount, φ wi i ∂(componentSamplingPMF S).toMeasure = 0 := by
      intro wi
      dsimp [φ, leftResidual, centeredCorrection]
      have hzero :=
        (integral_inner_sub_mean_eq_zero_of_integral_eq
          (μ := (componentSamplingPMF S).toMeasure)
          (F := sampledGradientCorrection S (currentFromPrefix wi.1) (previousFromPrefix wi.1))
          (mean := SOptLib.finiteUniformAverage S.componentGradient (currentFromPrefix wi.1) -
            SOptLib.finiteUniformAverage S.componentGradient (previousFromPrefix wi.1))
          (direction := centeredCorrection wi.1 wi.2)
          (Integrable.of_finite
            (f := sampledGradientCorrection S (currentFromPrefix wi.1) (previousFromPrefix wi.1))
            (μ := (componentSamplingPMF S).toMeasure))
          (sampledGradientCorrection_integral_eq_finiteAverageGradient_sub
            S (currentFromPrefix wi.1) (previousFromPrefix wi.1))).2
      rw [← hzero]
      refine integral_congr_ae ?_
      filter_upwards with i
      exact real_inner_comm _ _
    have htransport :
        ∫ ω : AlgorithmSamplePath S,
            φ (strictPrefixKey ω, ω (index s j) r) (ω (index s j) q) ∂μ = 0 := by
      letI : MeasurableSpace (AlgorithmSamplePath S) := pathMS
      exact
        integral_comp_eq_zero_of_indep_fixed_integral_zero
          (P := μ) (ν := (componentSamplingPMF S).toMeasure)
          (φ := φ)
          (X := fun ω : AlgorithmSamplePath S =>
            (strictPrefixKey ω, ω (index s j) r))
          (Y := fun ω : AlgorithmSamplePath S => ω (index s j) q)
          hφ_meas hX_meas hY_meas
          (hstrictPrefix_peer_current_indep r q hrq)
          (hcurrent_coordinate_law q)
          hcomp_int hfixed_zero
    rwa [hcomp_eq] at htransport
  have hbatch_bound :
      ∫ ω : AlgorithmSamplePath S, ‖centeredMiniBatchIncrement ω‖ ^ 2 ∂μ ≤
        (S.L ^ 2 *
          ∫ ω : AlgorithmSamplePath S,
            ‖xProc (index s j) ω - xProc (index s (j - 1)) ω‖ ^ 2 ∂μ) /
          (S.b : ℝ) :=
    hbatch_from_cross heps_cross
  have hdeltaProc_prev_meas :
      AEStronglyMeasurable[pathMS] (deltaProc (index s (j - 1))) μ := by
    change AEStronglyMeasurable[pathMS] (deltaProc (index s (j - 1))) (algorithmSampleLaw S)
    refine aestronglyMeasurable_algorithmSampleLaw_of_prefix_const S (index s (j - 1)) ?_
    intro ω ω' hprefix
    have hrun_estimator :
        run (index s (j - 1)) ω = run (index s (j - 1)) ω' :=
      runState_eq_of_batch_prefix_eq S (algorithmBatchStream S) run hrun
        (index s (j - 1)) ω ω' (fun q hq a => by
          exact hprefix q (by omega) a)
    have hrun_iterate :
        run (index s (j - 1) - 1) ω = run (index s (j - 1) - 1) ω' :=
      runState_eq_of_batch_prefix_eq S (algorithmBatchStream S) run hrun
        (index s (j - 1) - 1) ω ω' (fun q hq a => by
          exact hprefix q (by omega) a)
    dsimp [deltaProc]
    simp [hidx_pred_pos, paperEstimator, paperIterate, estimator, iterate,
      SOptLib.positiveTimeIterateView_eq, hrun_estimator, hrun_iterate]
  have hprev_eps_cross :
      ∀ r : Fin S.b,
        ∫ ω : AlgorithmSamplePath S,
          ⟪deltaProc (index s (j - 1)) ω, eps r ω⟫_ℝ ∂μ = 0 := by
    intro r
    haveI : IsProbabilityMeasure μ := by
      simpa [μ] using hLaw.1
    let Prefix := Fin (index s j) → Fin S.b → Fin S.componentCount
    let defaultComponent : Fin S.componentCount := ⟨0, S.hcomponentCount_pos⟩
    let pathOfPrefix : Prefix → AlgorithmSamplePath S :=
      fun w k a => if hk : k < index s j then w ⟨k, hk⟩ a else defaultComponent
    let currentFromPrefix : Prefix → E :=
      fun w => paperIterate S run ⟨index s j, hidx_pos'⟩ (pathOfPrefix w)
    let previousFromPrefix : Prefix → E :=
      fun w => paperIterate S run ⟨index s (j - 1), hidx_pred_pos⟩ (pathOfPrefix w)
    let deltaPrevFromPrefix : Prefix → E :=
      fun w => deltaProc (index s (j - 1)) (pathOfPrefix w)
    let centeredCorrection : Prefix → Fin S.componentCount → E :=
      fun w i =>
        sampledGradientCorrection S (currentFromPrefix w) (previousFromPrefix w) i -
          (SOptLib.finiteUniformAverage S.componentGradient (currentFromPrefix w) -
            SOptLib.finiteUniformAverage S.componentGradient (previousFromPrefix w))
    let φ : Prefix → Fin S.componentCount → ℝ :=
      fun w i => ⟪deltaPrevFromPrefix w, centeredCorrection w i⟫_ℝ
    have hcurrent_reconstruct :
        ∀ ω : AlgorithmSamplePath S,
          currentFromPrefix (strictPrefixKey ω) =
            paperIterate S run ⟨index s j, hidx_pos'⟩ ω := by
      intro ω
      have hrun_current :
          run (index s j - 1) (pathOfPrefix (strictPrefixKey ω)) =
            run (index s j - 1) ω :=
        runState_eq_of_batch_prefix_eq S (algorithmBatchStream S) run hrun
          (index s j - 1) (pathOfPrefix (strictPrefixKey ω)) ω
          (fun q hq a => by
            have hqlt : q < index s j := by omega
            dsimp [pathOfPrefix, strictPrefixKey]
            simp [algorithmBatchStream, hqlt])
      dsimp [currentFromPrefix]
      simpa [paperIterate, iterate, SOptLib.positiveTimeIterateView_eq,
        hrun_current]
    have hprevious_reconstruct :
        ∀ ω : AlgorithmSamplePath S,
          previousFromPrefix (strictPrefixKey ω) =
            paperIterate S run ⟨index s (j - 1), hidx_pred_pos⟩ ω := by
      intro ω
      have hrun_previous :
          run (index s (j - 1) - 1) (pathOfPrefix (strictPrefixKey ω)) =
            run (index s (j - 1) - 1) ω :=
        runState_eq_of_batch_prefix_eq S (algorithmBatchStream S) run hrun
          (index s (j - 1) - 1) (pathOfPrefix (strictPrefixKey ω)) ω
          (fun q hq a => by
            have hqlt : q < index s j := by
              dsimp [index] at hq ⊢
              simp [SOptLib.global_index_def] at hq ⊢
              omega
            dsimp [pathOfPrefix, strictPrefixKey]
            simp [algorithmBatchStream, hqlt])
      dsimp [previousFromPrefix]
      simpa [paperIterate, iterate, SOptLib.positiveTimeIterateView_eq,
        hrun_previous]
    have hdeltaPrev_reconstruct :
        ∀ ω : AlgorithmSamplePath S,
          deltaPrevFromPrefix (strictPrefixKey ω) =
            deltaProc (index s (j - 1)) ω := by
      intro ω
      have hrun_estimator :
          run (index s (j - 1)) (pathOfPrefix (strictPrefixKey ω)) =
            run (index s (j - 1)) ω :=
        runState_eq_of_batch_prefix_eq S (algorithmBatchStream S) run hrun
          (index s (j - 1)) (pathOfPrefix (strictPrefixKey ω)) ω
          (fun q hq a => by
            have hqlt : q < index s j := by
              dsimp [index] at hq ⊢
              simp [SOptLib.global_index_def] at hq ⊢
              omega
            dsimp [pathOfPrefix, strictPrefixKey]
            simp [algorithmBatchStream, hqlt])
      have hrun_iterate :
          run (index s (j - 1) - 1) (pathOfPrefix (strictPrefixKey ω)) =
            run (index s (j - 1) - 1) ω :=
        runState_eq_of_batch_prefix_eq S (algorithmBatchStream S) run hrun
          (index s (j - 1) - 1) (pathOfPrefix (strictPrefixKey ω)) ω
          (fun q hq a => by
            have hqlt : q < index s j := by
              dsimp [index] at hq ⊢
              simp [SOptLib.global_index_def] at hq ⊢
              omega
            dsimp [pathOfPrefix, strictPrefixKey]
            simp [algorithmBatchStream, hqlt])
      dsimp [deltaPrevFromPrefix, deltaProc]
      simp [hidx_pred_pos, paperEstimator, paperIterate, estimator, iterate,
        SOptLib.positiveTimeIterateView_eq, hrun_estimator, hrun_iterate]
    have hφ_meas : Measurable (Function.uncurry φ) := by
      exact measurable_of_finite _
    have hX_meas :
        @Measurable (AlgorithmSamplePath S) Prefix pathMS inferInstance strictPrefixKey := by
      simpa [Prefix, pathMS] using hstrictPrefixKey_meas
    have hY_meas :
        @Measurable (AlgorithmSamplePath S) (Fin S.componentCount) pathMS sampleMS
          (fun ω : AlgorithmSamplePath S => ω (index s j) r) := by
      simpa [sampleCoord] using hsampleCoord_meas (index s j, r)
    have hcomp_eq :
        (fun ω : AlgorithmSamplePath S =>
            φ (strictPrefixKey ω) (ω (index s j) r)) =
          fun ω : AlgorithmSamplePath S =>
            ⟪deltaProc (index s (j - 1)) ω, eps r ω⟫_ℝ := by
      funext ω
      dsimp [φ, centeredCorrection, eps]
      simp [hcurrent_reconstruct ω, hprevious_reconstruct ω,
        hdeltaPrev_reconstruct ω]
    have hcomp_int :
        Integrable[pathMS]
          (fun ω : AlgorithmSamplePath S =>
            φ (strictPrefixKey ω) (ω (index s j) r)) μ := by
      rw [hcomp_eq]
      letI : MeasurableSpace (AlgorithmSamplePath S) := pathMS
      simpa [pathMS] using integrable_inner_of_integrable_sq_norm
        (hdeltaProc_prev_meas) (heps_meas r)
        (hdeltaProc_prev_sq_int) (heps_sq_int r)
    have hfixed_zero :
        ∀ w : Prefix,
          ∫ i : Fin S.componentCount, φ w i ∂(componentSamplingPMF S).toMeasure = 0 := by
      intro w
      dsimp [φ, deltaPrevFromPrefix, centeredCorrection]
      have hzero :=
        (integral_inner_sub_mean_eq_zero_of_integral_eq
          (μ := (componentSamplingPMF S).toMeasure)
          (F := sampledGradientCorrection S (currentFromPrefix w) (previousFromPrefix w))
          (mean := SOptLib.finiteUniformAverage S.componentGradient (currentFromPrefix w) -
            SOptLib.finiteUniformAverage S.componentGradient (previousFromPrefix w))
          (direction := deltaPrevFromPrefix w)
          (Integrable.of_finite
            (f := sampledGradientCorrection S (currentFromPrefix w) (previousFromPrefix w))
            (μ := (componentSamplingPMF S).toMeasure))
          (sampledGradientCorrection_integral_eq_finiteAverageGradient_sub
            S (currentFromPrefix w) (previousFromPrefix w))).2
      rw [← hzero]
      refine integral_congr_ae ?_
      filter_upwards with i
      exact real_inner_comm _ _
    have htransport :
        ∫ ω : AlgorithmSamplePath S,
            φ (strictPrefixKey ω) (ω (index s j) r) ∂μ = 0 := by
      letI : MeasurableSpace (AlgorithmSamplePath S) := pathMS
      exact
        integral_comp_eq_zero_of_indep_fixed_integral_zero
          (P := μ) (ν := (componentSamplingPMF S).toMeasure)
          (φ := φ) (X := strictPrefixKey)
          (Y := fun ω : AlgorithmSamplePath S => ω (index s j) r)
          hφ_meas hX_meas hY_meas
          (hstrictPrefix_current_indep r)
          (hcurrent_coordinate_law r)
          hcomp_int hfixed_zero
    rwa [hcomp_eq] at htransport
  have hprev_increment_cross :
      ∫ ω : AlgorithmSamplePath S,
        ⟪deltaProc (index s (j - 1)) ω, centeredMiniBatchIncrement ω⟫_ℝ ∂μ = 0 := by
    letI : MeasurableSpace (AlgorithmSamplePath S) := pathMS
    have havg_cross :
        ∫ ω : AlgorithmSamplePath S,
          ⟪deltaProc (index s (j - 1)) ω,
            ((S.b : ℝ)⁻¹) • Finset.sum Finset.univ (fun r : Fin S.b => eps r ω)⟫_ℝ ∂μ = 0 :=
      pastResidual_inner_centeredMiniBatchAverage_integral_eq_zero
        (P := μ) (I := (Finset.univ : Finset (Fin S.b))) (m := S.b)
        (d := deltaProc (index s (j - 1))) (eps := eps)
        hdeltaProc_prev_meas
        (fun r _hr => heps_meas r)
        hdeltaProc_prev_sq_int
        (fun r _hr => heps_sq_int r)
        (fun r _hr => hprev_eps_cross r)
    calc
      ∫ ω : AlgorithmSamplePath S,
          ⟪deltaProc (index s (j - 1)) ω, centeredMiniBatchIncrement ω⟫_ℝ ∂μ =
          ∫ ω : AlgorithmSamplePath S,
            ⟪deltaProc (index s (j - 1)) ω,
              ((S.b : ℝ)⁻¹) • Finset.sum Finset.univ (fun r : Fin S.b => eps r ω)⟫_ℝ ∂μ := by
            refine integral_congr_ae (Filter.Eventually.of_forall ?_)
            intro ω
            simp [hcenteredMiniBatchIncrement_as_average ω]
      _ = 0 := havg_cross
  have hinc_meas :
      AEStronglyMeasurable[pathMS] centeredMiniBatchIncrement μ := by
    have havg_meas :
        AEStronglyMeasurable[pathMS]
          (((S.b : ℝ)⁻¹) • Finset.sum Finset.univ (fun r : Fin S.b => eps r)) μ := by
      simpa [pathMS] using
        (Finset.aestronglyMeasurable_sum (s := (Finset.univ : Finset (Fin S.b)))
          (fun r _hr => heps_meas r)).const_smul ((S.b : ℝ)⁻¹)
    refine havg_meas.congr ?_
    filter_upwards [] with ω
    rw [Pi.smul_apply]
    simpa [Finset.sum_apply] using (hcenteredMiniBatchIncrement_as_average ω).symm
  have hinc_sq :
      Integrable[pathMS] (fun ω : AlgorithmSamplePath S =>
        ‖centeredMiniBatchIncrement ω‖ ^ 2) μ := by
    letI : MeasurableSpace (AlgorithmSamplePath S) := pathMS
    exact
      integrable_sq_norm_centeredMiniBatchAverage
        (μ := μ) (I := (Finset.univ : Finset (Fin S.b))) (m := S.b)
        (δ := eps) (avg := centeredMiniBatchIncrement)
        (fun r _hr => heps_meas r)
        (fun r _hr => heps_sq_int r)
        (by
          funext ω
          exact hcenteredMiniBatchIncrement_as_average ω)
  have hstep_current :
      ∫ ω : AlgorithmSamplePath S, ‖deltaProc (index s j) ω‖ ^ 2 ∂μ ≤
        ∫ ω : AlgorithmSamplePath S, ‖deltaProc (index s (j - 1)) ω‖ ^ 2 ∂μ +
          (S.L ^ 2 / (S.b : ℝ)) *
            ∫ ω : AlgorithmSamplePath S,
              ‖xProc (index s j) ω - xProc (index s (j - 1)) ω‖ ^ 2 ∂μ := by
    letI : MeasurableSpace (AlgorithmSamplePath S) := pathMS
    have hrec_ae :
        Filter.EventuallyEq (ae μ) (deltaProc (index s j))
          (fun ω : AlgorithmSamplePath S =>
            deltaProc (index s (j - 1)) ω + centeredMiniBatchIncrement ω) :=
      Filter.Eventually.of_forall hdeltaProc_nonrefresh_recurrence
    have hinc_bound :
        ∫ ω : AlgorithmSamplePath S, ‖centeredMiniBatchIncrement ω‖ ^ 2 ∂μ ≤
          (S.L ^ 2 / (S.b : ℝ)) *
            ∫ ω : AlgorithmSamplePath S,
              ‖xProc (index s j) ω - xProc (index s (j - 1)) ω‖ ^ 2 ∂μ := by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hbatch_bound
    exact
      (second_moment_add_recurrence_le_of_cross_zero
        (μ := μ)
        (deltaPrev := deltaProc (index s (j - 1)))
        (deltaNext := deltaProc (index s j))
        (inc := centeredMiniBatchIncrement)
        (B := (S.L ^ 2 / (S.b : ℝ)) *
          ∫ ω : AlgorithmSamplePath S,
            ‖xProc (index s j) ω - xProc (index s (j - 1)) ω‖ ^ 2 ∂μ)
        hdeltaProc_prev_meas hinc_meas hdeltaProc_prev_sq_int hinc_sq
        hrec_ae hprev_increment_cross hinc_bound).2
  let Valid : ℕ → ℕ → Prop := fun s0 t =>
    s0 = s ∧ t ≤ S.T ∧ index s0 t ≤ S.N
  have hvalid_prefix :
      ∀ {s0 i t : ℕ}, i ≤ t → Valid s0 t → Valid s0 i := by
    intro s0 i t hit hvalid
    rcases hvalid with ⟨hs_eq, htT, htN⟩
    refine ⟨hs_eq, by omega, ?_⟩
    subst s0
    exact SOptLib.global_index_le_of_step_le (T := S.T) (N := S.N)
      (s := s) hit htN
  have hvalid_current : Valid s j := by
    refine ⟨rfl, hj_epoch.2, ?_⟩
    exact SOptLib.activeEpochSteps_globalIndex_le (T := S.T) (N := S.N)
      (globalIndex := index) (s := s) (j := j) hj
  have hbase_all :
      ∀ s0 : ℕ, Valid s0 1 →
        ∫ ω : AlgorithmSamplePath S, ‖deltaProc (index s0 1) ω‖ ^ 2 ∂μ ≤
          (S.L ^ 2 / (S.b : ℝ)) *
            ∫ ω : AlgorithmSamplePath S,
              SOptLib.epochSquaredDifferenceSum xProc index s0 1 ω ∂μ + 0 := by
    intro s0 hvalid
    rcases hvalid with ⟨hs_eq, _hT, _hN⟩
    subst s0
    exact hbase_epoch_start
  letI : MeasurableSpace (AlgorithmSamplePath S) := pathMS
  have hdelta_sq_int_all :
      ∀ s0 t : ℕ, 1 ≤ t → t ≤ S.T → Valid s0 t →
        Integrable (fun ω : AlgorithmSamplePath S =>
          ‖deltaProc (index s0 t) ω‖ ^ 2) μ := by
    intro s0 t ht_pos _htT hvalid
    rcases hvalid with ⟨_hs_eq, _htT', htN⟩
    have hidx_pos_t : 1 ≤ index s0 t := by
      change 1 ≤ SOptLib.global_index S.T s0 t
      rw [SOptLib.global_index_def]
      omega
    have hwin : index s0 t ∈ outputWindow S := by
      simpa [outputWindow] using (Finset.mem_Icc.mpr ⟨hidx_pos_t, htN⟩)
    have hreg := theorem718_finite_prefix_observable_integrability S run hrun
      (index s0 t) hwin
    simpa [deltaProc, μ, pathMS, dif_pos hidx_pos_t] using hreg.2.1
  have hdiff_sq_int_all :
      ∀ s0 t : ℕ, 2 ≤ t → t ≤ S.T → Valid s0 t →
        Integrable
          (fun ω : AlgorithmSamplePath S =>
            ‖xProc (index s0 t) ω - xProc (index s0 (t - 1)) ω‖ ^ 2) μ := by
    intro s0 t ht_two htT hvalid
    refine integrable_algorithmSampleLaw_of_prefix_const S (index s0 t) ?_
    intro ω ω' hprefix
    have hidx_pos_t : 1 ≤ index s0 t := by
      change 1 ≤ SOptLib.global_index S.T s0 t
      rw [SOptLib.global_index_def]
      omega
    have hidx_pos_prev : 1 ≤ index s0 (t - 1) := by
      change 1 ≤ SOptLib.global_index S.T s0 (t - 1)
      rw [SOptLib.global_index_def]
      omega
    have hmono_prev : index s0 (t - 1) ≤ index s0 t := by
      exact SOptLib.global_index_mono_step (T := S.T) (s := s0)
        (i := t - 1) (t := t) (by omega)
    have hrun_t : run (index s0 t - 1) ω = run (index s0 t - 1) ω' :=
      runState_eq_of_batch_prefix_eq S (algorithmBatchStream S) run hrun
        (index s0 t - 1) ω ω' (fun q hq a => by
          exact hprefix q (by omega) a)
    have hrun_prev :
        run (index s0 (t - 1) - 1) ω =
          run (index s0 (t - 1) - 1) ω' :=
      runState_eq_of_batch_prefix_eq S (algorithmBatchStream S) run hrun
        (index s0 (t - 1) - 1) ω ω' (fun q hq a => by
          have hq_prev : q ≤ index s0 (t - 1) := by omega
          exact hprefix q (le_trans hq_prev hmono_prev) a)
    dsimp [xProc]
    simp [hidx_pos_t, hidx_pos_prev, paperIterate, iterate,
      SOptLib.positiveTimeIterateView_eq, hrun_t, hrun_prev]
  have hstep_all :
      ∀ s0 t : ℕ, 2 ≤ t → t ≤ S.T → Valid s0 t →
        Integrable (fun ω : AlgorithmSamplePath S =>
          ‖deltaProc (index s0 (t - 1)) ω‖ ^ 2) μ →
        ∫ ω : AlgorithmSamplePath S, ‖deltaProc (index s0 t) ω‖ ^ 2 ∂μ ≤
          ∫ ω : AlgorithmSamplePath S,
            ‖deltaProc (index s0 (t - 1)) ω‖ ^ 2 ∂μ +
            (S.L ^ 2 / (S.b : ℝ)) *
              ∫ ω : AlgorithmSamplePath S,
                ‖xProc (index s0 t) ω - xProc (index s0 (t - 1)) ω‖ ^ 2 ∂μ := by
    intro s0 t ht_two htT hvalid hprev_int
    rcases hvalid with ⟨hs0_eq, htT_valid, htN⟩
    rw [hs0_eq] at htN hprev_int ⊢
    have hj : t ∈ SOptLib.activeEpochSteps S.T S.N index s := by
      rw [SOptLib.mem_activeEpochSteps]
      refine ⟨Finset.mem_Icc.mpr ⟨by omega, htT⟩, ?_⟩
      simpa [index, SOptLib.global_index_def] using htN
    have hj_epoch : 1 ≤ t ∧ t ≤ S.T := ⟨by omega, htT⟩
    have hidx_pos : 1 ≤ index s t := by
      dsimp [index]
      rw [SOptLib.global_index_def]
      omega
    have hidx_window : index s t ∈ outputWindow S := by
      simpa [outputWindow] using (Finset.mem_Icc.mpr ⟨hidx_pos, htN⟩)
    have h_current_step :
        SOptLib.stepOfIndex S.T (index s t) = t := by
      dsimp [index]
      exact SOptLib.nat_stepOf_globalIndex_eq (T := S.T) (s := s) (j := t)
        hj_epoch.1 hj_epoch.2
    have h_current_nonrefresh :
        SOptLib.stepOfIndex S.T (index s t) ≠ 1 := by
      rw [h_current_step]
      omega
    have hidx_pred_eq :
        index s t - 1 = index s (t - 1) := by
      dsimp [index]
      simp [SOptLib.global_index_def]
      omega
    have hidx_pos' : 1 ≤ index s t := by
      dsimp [index]
      exact hidx_pos
    have hidx_pred_pos : 1 ≤ index s (t - 1) := by
      dsimp [index]
      simp [SOptLib.global_index_def]
      omega
    have hpaperEstimator_nonrefresh_raw :
        ∀ ω : AlgorithmSamplePath S,
          paperEstimator S run ⟨index s t, hidx_pos'⟩ ω =
            recursiveMiniBatchGradient S
              (run (index s t - 1) ω).current
              (run (index s t - 1) ω).previous
              (run (index s t - 1) ω).estimator
              (fun r => ω (index s t) r) := by
      intro ω
      have hidx_succ : (index s t - 1) + 1 = index s t :=
        Nat.sub_add_cancel hidx_pos'
      have hstep := hrun.2 (index s t - 1) ω
      rw [hidx_succ] at hstep
      dsimp only [outerStepRel, algorithmBatchStream] at hstep
      rcases hstep with ⟨_hx, _hterm, hnext⟩
      have hest := congrArg RunState.estimator hnext
      have hG :
          paperEstimator S run ⟨index s t, hidx_pos'⟩ ω =
            gradientEstimatorUpdate S (index s t)
              (run (index s t - 1) ω).previous
              (run (index s t - 1) ω).current
              (run (index s t - 1) ω).estimator
              (fun r => ω (index s t) r) := by
        simpa [paperEstimator, estimator] using hest
      rw [hG]
      rw [gradientEstimatorUpdate]
      exact if_neg h_current_nonrefresh
    have hrun_current_eq_paper :
        ∀ ω : AlgorithmSamplePath S,
          (run (index s t - 1) ω).current =
            paperIterate S run ⟨index s t, hidx_pos'⟩ ω := by
      intro ω
      simp [paperIterate, iterate, SOptLib.positiveTimeIterateView_eq]
    have hrun_previous_eq_paper_pred :
        ∀ ω : AlgorithmSamplePath S,
          (run (index s t - 1) ω).previous =
            paperIterate S run ⟨index s (t - 1), hidx_pred_pos⟩ ω := by
      intro ω
      have hpred_succ : (index s (t - 1) - 1) + 1 = index s (t - 1) :=
        Nat.sub_add_cancel hidx_pred_pos
      have hstep := hrun.2 (index s (t - 1) - 1) ω
      rw [hpred_succ] at hstep
      dsimp [outerStepRel, algorithmBatchStream] at hstep
      rcases hstep with ⟨_hx, _hterm, hnext⟩
      have hprev := congrArg RunState.previous hnext
      simpa [paperIterate, iterate, SOptLib.positiveTimeIterateView_eq,
        hidx_pred_eq] using hprev
    have hrun_estimator_eq_paper_pred :
        ∀ ω : AlgorithmSamplePath S,
          (run (index s t - 1) ω).estimator =
            paperEstimator S run ⟨index s (t - 1), hidx_pred_pos⟩ ω := by
      intro ω
      simp [paperEstimator, estimator, hidx_pred_eq]
    have hpaperEstimator_nonrefresh :
        ∀ ω : AlgorithmSamplePath S,
          paperEstimator S run ⟨index s t, hidx_pos'⟩ ω =
            recursiveMiniBatchGradient S
              (paperIterate S run ⟨index s t, hidx_pos'⟩ ω)
              (paperIterate S run ⟨index s (t - 1), hidx_pred_pos⟩ ω)
              (paperEstimator S run ⟨index s (t - 1), hidx_pred_pos⟩ ω)
              (fun r => ω (index s t) r) := by
      intro ω
      rw [hpaperEstimator_nonrefresh_raw ω]
      rw [hrun_current_eq_paper ω, hrun_previous_eq_paper_pred ω,
        hrun_estimator_eq_paper_pred ω]
    let centeredMiniBatchIncrement : AlgorithmSamplePath S → E := fun ω =>
      miniBatchCorrection S
        (paperIterate S run ⟨index s t, hidx_pos'⟩ ω)
        (paperIterate S run ⟨index s (t - 1), hidx_pred_pos⟩ ω)
        (fun r => ω (index s t) r) -
      (SOptLib.finiteUniformAverage S.componentGradient (paperIterate S run ⟨index s t, hidx_pos'⟩ ω) -
        SOptLib.finiteUniformAverage S.componentGradient (paperIterate S run ⟨index s (t - 1), hidx_pred_pos⟩ ω))
    have hdeltaProc_nonrefresh_recurrence :
        ∀ ω : AlgorithmSamplePath S,
          deltaProc (index s t) ω =
            deltaProc (index s (t - 1)) ω + centeredMiniBatchIncrement ω := by
      intro ω
      dsimp [deltaProc, centeredMiniBatchIncrement]
      rw [dif_pos hidx_pos', dif_pos hidx_pred_pos]
      rw [hpaperEstimator_nonrefresh ω]
      dsimp [recursiveMiniBatchGradient]
      abel
    have hcenteredMiniBatchIncrement_unfold :
        ∀ ω : AlgorithmSamplePath S,
          centeredMiniBatchIncrement ω =
            (S.b : ℝ)⁻¹ •
                Finset.sum Finset.univ
                  (fun r : Fin S.b =>
                    sampledGradientCorrection S
                      (paperIterate S run ⟨index s t, hidx_pos'⟩ ω)
                      (paperIterate S run ⟨index s (t - 1), hidx_pred_pos⟩ ω)
                      (ω (index s t) r)) -
              (SOptLib.finiteUniformAverage S.componentGradient (paperIterate S run ⟨index s t, hidx_pos'⟩ ω) -
                SOptLib.finiteUniformAverage S.componentGradient
                  (paperIterate S run ⟨index s (t - 1), hidx_pred_pos⟩ ω)) := by
      intro ω
      simp [centeredMiniBatchIncrement, miniBatchCorrection]
    have hcentered_component_budget :
        ∀ ω : AlgorithmSamplePath S,
          Finset.sum Finset.univ
              (fun i : Fin S.componentCount =>
                componentSamplingProbability S i *
                  ‖sampledGradientCorrection S
                      (paperIterate S run ⟨index s t, hidx_pos'⟩ ω)
                      (paperIterate S run ⟨index s (t - 1), hidx_pred_pos⟩ ω) i -
                    (SOptLib.finiteUniformAverage S.componentGradient (paperIterate S run ⟨index s t, hidx_pos'⟩ ω) -
                      SOptLib.finiteUniformAverage S.componentGradient
                        (paperIterate S run ⟨index s (t - 1), hidx_pred_pos⟩ ω))‖ ^ 2) ≤
            S.L ^ 2 *
              ‖paperIterate S run ⟨index s t, hidx_pos'⟩ ω -
                paperIterate S run ⟨index s (t - 1), hidx_pred_pos⟩ ω‖ ^ 2 := by
      intro ω
      exact
        sampledGradientCorrection_centered_weighted_second_moment_le
          S
          (paperIterate_mem_of_runStateSpec S (algorithmBatchStream S) run hrun
            ⟨index s t, hidx_pos'⟩ ω)
          (paperIterate_mem_of_runStateSpec S (algorithmBatchStream S) run hrun
            ⟨index s (t - 1), hidx_pred_pos⟩ ω)
    have hcurrent_coordinate_law :
        ∀ r : Fin S.b,
          Measure.map (fun ω : AlgorithmSamplePath S => ω (index s t) r) μ =
            (componentSamplingPMF S).toMeasure := by
      intro r
      simpa [μ] using hLaw.2.2 (index s t) r
    have hcurrent_coordinate_identDistrib :
        ∀ r : Fin S.b,
          IdentDistrib (fun ω : AlgorithmSamplePath S => ω (index s t) r)
            (fun i : Fin S.componentCount => i) μ
            (componentSamplingPMF S).toMeasure := by
      intro r
      have hmeas :
          Measurable (fun ω : AlgorithmSamplePath S => ω (index s t) r) :=
        (measurable_pi_apply r).comp (measurable_pi_apply (index s t))
      refine ⟨hmeas.aemeasurable, measurable_id.aemeasurable, ?_⟩
      simpa using hcurrent_coordinate_law r
    let eps : Fin S.b → AlgorithmSamplePath S → E := fun r ω =>
      sampledGradientCorrection S
        (paperIterate S run ⟨index s t, hidx_pos'⟩ ω)
        (paperIterate S run ⟨index s (t - 1), hidx_pred_pos⟩ ω)
        (ω (index s t) r) -
      (SOptLib.finiteUniformAverage S.componentGradient (paperIterate S run ⟨index s t, hidx_pos'⟩ ω) -
        SOptLib.finiteUniformAverage S.componentGradient
          (paperIterate S run ⟨index s (t - 1), hidx_pred_pos⟩ ω))
    have hcenteredMiniBatchIncrement_as_average :
        ∀ ω : AlgorithmSamplePath S,
          centeredMiniBatchIncrement ω =
            (S.b : ℝ)⁻¹ • Finset.sum Finset.univ (fun r : Fin S.b => eps r ω) := by
      intro ω
      rw [hcenteredMiniBatchIncrement_unfold ω]
      have hcenter :=
        inv_card_smul_sum_sub_const_eq
          (s := (Finset.univ : Finset (Fin S.b)))
          (z := fun r : Fin S.b =>
            sampledGradientCorrection S
              (paperIterate S run ⟨index s t, hidx_pos'⟩ ω)
              (paperIterate S run ⟨index s (t - 1), hidx_pred_pos⟩ ω)
              (ω (index s t) r))
          (c := SOptLib.finiteUniformAverage S.componentGradient (paperIterate S run ⟨index s t, hidx_pos'⟩ ω) -
            SOptLib.finiteUniformAverage S.componentGradient
              (paperIterate S run ⟨index s (t - 1), hidx_pred_pos⟩ ω))
          (by simp [S.hb_pos])
      simpa [eps, Finset.card_univ] using hcenter.symm
    have hprev_active :
        t - 1 ∈ SOptLib.activeEpochSteps S.T S.N index s := by
      have hjN :
          index s t ≤ S.N :=
        SOptLib.activeEpochSteps_globalIndex_le (T := S.T) (N := S.N)
          (globalIndex := index) (s := s) (j := t) hj
      rw [SOptLib.mem_activeEpochSteps]
      refine ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
      dsimp [index] at hjN ⊢
      simp [SOptLib.global_index_def] at hjN ⊢
      omega
    have hidx_pred_window : index s (t - 1) ∈ outputWindow S := by
      simpa [index, outputWindow] using
        SOptLib.global_index_mem_output_window_of_active_epoch_step
          (T := S.T) (N := S.N) (globalIndex := index)
          (s := s) (j := t - 1) hidx_pred_pos hprev_active
    have hdeltaProc_current_sq_int :
        Integrable (fun ω : AlgorithmSamplePath S =>
          ‖deltaProc (index s t) ω‖ ^ 2) μ := by
      have hreg :=
        theorem718_finite_prefix_observable_integrability S run hrun
          (index s t) (by simpa [index] using hidx_window)
      simpa [deltaProc, μ, dif_pos hidx_pos'] using hreg.2.1
    have hdeltaProc_prev_sq_int :
        Integrable (fun ω : AlgorithmSamplePath S =>
          ‖deltaProc (index s (t - 1)) ω‖ ^ 2) μ := by
      have hreg :=
        theorem718_finite_prefix_observable_integrability S run hrun
          (index s (t - 1)) (by simpa [index] using hidx_pred_window)
      simpa [deltaProc, μ, dif_pos hidx_pred_pos] using hreg.2.1
    have heps_sq_int :
        ∀ r : Fin S.b,
          Integrable (fun ω : AlgorithmSamplePath S => ‖eps r ω‖ ^ 2) μ := by
      intro r
      refine integrable_algorithmSampleLaw_of_prefix_const S (index s t) ?_
      intro ω ω' hprefix
      have hrun_current :
          run (index s t - 1) ω = run (index s t - 1) ω' :=
        runState_eq_of_batch_prefix_eq S (algorithmBatchStream S) run hrun
          (index s t - 1) ω ω' (fun q hq a => by
            exact hprefix q (by omega) a)
      have hrun_pred :
          run (index s (t - 1) - 1) ω = run (index s (t - 1) - 1) ω' :=
        runState_eq_of_batch_prefix_eq S (algorithmBatchStream S) run hrun
          (index s (t - 1) - 1) ω ω' (fun q hq a => by
            exact hprefix q (by
              dsimp [index] at hq ⊢
              simp [SOptLib.global_index_def] at hq ⊢
              omega) a)
      have hsample : ω (index s t) r = ω' (index s t) r :=
        hprefix (index s t) (le_rfl) r
      have heq : eps r ω = eps r ω' := by
        dsimp [eps]
        simpa [paperIterate, iterate, SOptLib.positiveTimeIterateView_eq,
          hrun_current, hrun_pred, hsample]
      simpa [heq]
    have heps_meas :
        ∀ r : Fin S.b, AEStronglyMeasurable (eps r) μ := by
      intro r
      change AEStronglyMeasurable (eps r) (algorithmSampleLaw S)
      refine aestronglyMeasurable_algorithmSampleLaw_of_prefix_const S (index s t) ?_
      intro ω ω' hprefix
      have hrun_current :
          run (index s t - 1) ω = run (index s t - 1) ω' :=
        runState_eq_of_batch_prefix_eq S (algorithmBatchStream S) run hrun
          (index s t - 1) ω ω' (fun q hq a => by
            exact hprefix q (by omega) a)
      have hrun_pred :
          run (index s (t - 1) - 1) ω = run (index s (t - 1) - 1) ω' :=
        runState_eq_of_batch_prefix_eq S (algorithmBatchStream S) run hrun
          (index s (t - 1) - 1) ω ω' (fun q hq a => by
            exact hprefix q (by
              dsimp [index] at hq ⊢
              simp [SOptLib.global_index_def] at hq ⊢
              omega) a)
      have hsample : ω (index s t) r = ω' (index s t) r :=
        hprefix (index s t) (le_rfl) r
      dsimp [eps]
      simpa [paperIterate, iterate, SOptLib.positiveTimeIterateView_eq,
        hrun_current, hrun_pred, hsample]
    let sampleCoord : ℕ × Fin S.b → AlgorithmSamplePath S → Fin S.componentCount :=
      fun kr ω => ω kr.1 kr.2
    have hsampleCoord_meas : ∀ q, Measurable (sampleCoord q) := by
      intro q
      dsimp [sampleCoord]
      exact (measurable_pi_apply q.2).comp (measurable_pi_apply q.1)
    have hsampleCoord_iIndep : iIndepFun sampleCoord μ := by
      simpa [sampleCoord, μ] using hLaw.2.1
    let strictPrefixKey : AlgorithmSamplePath S →
        (Fin (index s t) → Fin S.b → Fin S.componentCount) :=
      fun ω q r => ω q.1 r
    have hstrictPrefixKey_meas : Measurable strictPrefixKey := by
      dsimp [strictPrefixKey]
      refine measurable_pi_lambda _ ?_
      intro q
      refine measurable_pi_lambda _ ?_
      intro r
      exact (measurable_pi_apply r).comp (measurable_pi_apply q.1)
    have hdeltaTerm_current_eq :
        deltaTerm (index s t) =
          ∫ ω : AlgorithmSamplePath S, ‖deltaProc (index s t) ω‖ ^ 2 ∂μ := by
      rw [hdelta_def]
      refine integral_congr_ae (Filter.Eventually.of_forall ?_)
      intro ω
      have hwin : s * S.T + t ∈ outputWindow S := by
        simpa [index, SOptLib.global_index_def] using hidx_window
      have hpos : 1 ≤ s * S.T + t := by
        simpa [index, SOptLib.global_index_def] using hidx_pos'
      simp [deltaProc, μ, index, SOptLib.global_index_def, hwin, hpos]
    have hcenteredMiniBatchIncrement_secondMoment_of_eps :
        (∀ r : Fin S.b, AEStronglyMeasurable (eps r) μ) →
        (∀ r : Fin S.b,
          Integrable (fun ω : AlgorithmSamplePath S => ‖eps r ω‖ ^ 2) μ ∧
            ∫ ω : AlgorithmSamplePath S, ‖eps r ω‖ ^ 2 ∂μ ≤
              S.L ^ 2 *
                ∫ ω : AlgorithmSamplePath S,
                  ‖xProc (index s t) ω - xProc (index s (t - 1)) ω‖ ^ 2 ∂μ) →
        (∀ r ∈ (Finset.univ : Finset (Fin S.b)),
          ∀ q ∈ (Finset.univ : Finset (Fin S.b)), r ≠ q →
            ∫ ω : AlgorithmSamplePath S, ⟪eps r ω, eps q ω⟫_ℝ ∂μ = 0) →
        ∫ ω : AlgorithmSamplePath S, ‖centeredMiniBatchIncrement ω‖ ^ 2 ∂μ ≤
          (S.L ^ 2 *
            ∫ ω : AlgorithmSamplePath S,
              ‖xProc (index s t) ω - xProc (index s (t - 1)) ω‖ ^ 2 ∂μ) /
            (S.b : ℝ) := by
      intro heps_meas heps_diag heps_cross
      have hbatch :=
        centeredMiniBatchAverage_secondMoment_le_variance_div_card_of_cross_zero
          (P := μ) (I := (Finset.univ : Finset (Fin S.b))) (m := S.b)
          (eps := eps)
          (varianceBudget :=
            S.L ^ 2 *
              ∫ ω : AlgorithmSamplePath S,
                ‖xProc (index s t) ω - xProc (index s (t - 1)) ω‖ ^ 2 ∂μ)
          S.hb_pos (by simp [Finset.card_univ])
          (fun r _hr => heps_meas r)
          (fun r _hr => heps_diag r)
          heps_cross
      calc
        ∫ ω : AlgorithmSamplePath S, ‖centeredMiniBatchIncrement ω‖ ^ 2 ∂μ =
            ∫ ω : AlgorithmSamplePath S,
              ‖(S.b : ℝ)⁻¹ • Finset.sum Finset.univ (fun r : Fin S.b => eps r ω)‖ ^ 2 ∂μ := by
              refine integral_congr_ae (Filter.Eventually.of_forall ?_)
              intro ω
              change
                ‖centeredMiniBatchIncrement ω‖ ^ 2 =
                  ‖(S.b : ℝ)⁻¹ • Finset.sum Finset.univ
                    (fun r : Fin S.b => eps r ω)‖ ^ 2
              exact
                congrArg (fun z : E => ‖z‖ ^ 2)
                  (hcenteredMiniBatchIncrement_as_average ω)
        _ ≤
            (S.L ^ 2 *
              ∫ ω : AlgorithmSamplePath S,
                ‖xProc (index s t) ω - xProc (index s (t - 1)) ω‖ ^ 2 ∂μ) /
              (S.b : ℝ) := hbatch
    let sampleMS : MeasurableSpace (Fin S.componentCount) :=
      Fin.instMeasurableSpace S.componentCount
    let pathMS : MeasurableSpace (AlgorithmSamplePath S) := inferInstance
    let pastSet : Set (ℕ × Fin S.b) := {kr | kr.1 < index s t}
    let strictPast : MeasurableSpace (AlgorithmSamplePath S) :=
      ⨆ q ∈ pastSet, MeasurableSpace.comap (sampleCoord q) sampleMS
    have hstrict_le :
        strictPast ≤
          (⨆ q ∈ pastSet,
            MeasurableSpace.comap (sampleCoord q) sampleMS) := by
      rfl
    have hstrictPrefix_coord_meas :
        ∀ q : Fin (index s t), ∀ r : Fin S.b,
          Measurable[strictPast]
            (fun ω : AlgorithmSamplePath S => sampleCoord (q.1, r) ω) := by
      intro q r
      have hqmem : (q.1, r) ∈ pastSet := by
        dsimp [pastSet]
        exact q.2
      exact measurable_iff_comap_le.mpr
        (le_iSup_of_le (q.1, r) (le_iSup_of_le hqmem le_rfl))
    have hstrictPrefixKey_meas_strictPast :
        Measurable[strictPast] strictPrefixKey := by
      dsimp [strictPrefixKey]
      refine measurable_pi_lambda _ ?_
      intro q
      refine measurable_pi_lambda _ ?_
      intro r
      simpa [sampleCoord] using hstrictPrefix_coord_meas q r
    have hstrictPrefix_current_indep :
        ∀ r : Fin S.b,
          IndepFun strictPrefixKey
            (fun ω : AlgorithmSamplePath S => ω (index s t) r) μ := by
      intro r
      have hpast_disj :
          Disjoint pastSet ({(index s t, r)} : Set (ℕ × Fin S.b)) := by
        refine Set.disjoint_left.2 ?_
        intro x hxpast hxcur
        rcases hxcur with rfl
        exact (Nat.lt_irrefl (index s t)) (by simpa [pastSet] using hxpast)
      simpa [sampleCoord] using
        (indepFun_prefixKey_current_of_iIndepFun
          (mΩ := pathMS) (mSample := sampleMS)
          (μ := μ) (sampleCoord := sampleCoord)
          (pastSet := pastSet) (strictPast := strictPast)
          (prefixKey := strictPrefixKey) (current := (index s t, r))
          hsampleCoord_meas hsampleCoord_iIndep
          hstrictPrefixKey_meas_strictPast hstrict_le hpast_disj).1
    have hstrictPrefix_peer_current_indep :
        ∀ r q : Fin S.b, r ≠ q →
          IndepFun
            (fun ω : AlgorithmSamplePath S =>
              (strictPrefixKey ω, ω (index s t) r))
            (fun ω : AlgorithmSamplePath S => ω (index s t) q) μ := by
      intro r q hrq
      have hpast_disj :
          Disjoint pastSet ({(index s t, q)} : Set (ℕ × Fin S.b)) := by
        refine Set.disjoint_left.2 ?_
        intro x hxpast hxcur
        rcases hxcur with rfl
        exact (Nat.lt_irrefl (index s t)) (by simpa [pastSet] using hxpast)
      have hleft_disj :
          Disjoint
            (pastSet ∪ ({(index s t, r)} : Set (ℕ × Fin S.b)))
            ({(index s t, q)} : Set (ℕ × Fin S.b)) := by
        refine Set.disjoint_left.2 ?_
        intro x hxleft hxcur
        rcases hxcur with rfl
        rcases hxleft with hxpast | hxpeer
        · exact (Nat.lt_irrefl (index s t)) (by simpa [pastSet] using hxpast)
        · have hpair_eq : (index s t, q) = (index s t, r) := by
            simpa using hxpeer
          exact hrq (by simpa using congrArg Prod.snd hpair_eq.symm)
      simpa [sampleCoord] using
        ((indepFun_prefixKey_current_of_iIndepFun
          (mΩ := pathMS) (mSample := sampleMS)
          (μ := μ) (sampleCoord := sampleCoord)
          (pastSet := pastSet) (strictPast := strictPast)
          (prefixKey := strictPrefixKey) (current := (index s t, q))
          hsampleCoord_meas hsampleCoord_iIndep
          hstrictPrefixKey_meas_strictPast hstrict_le hpast_disj).2
          (index s t, r) hleft_disj)
    have heps_diag :
        ∀ r : Fin S.b,
          Integrable (fun ω : AlgorithmSamplePath S => ‖eps r ω‖ ^ 2) μ ∧
            ∫ ω : AlgorithmSamplePath S, ‖eps r ω‖ ^ 2 ∂μ ≤
              S.L ^ 2 *
                ∫ ω : AlgorithmSamplePath S,
                  ‖xProc (index s t) ω - xProc (index s (t - 1)) ω‖ ^ 2 ∂μ := by
      intro r
      haveI : IsProbabilityMeasure μ := by
        simpa [μ] using hLaw.1
      refine ⟨heps_sq_int r, ?_⟩
      let Prefix := Fin (index s t) → Fin S.b → Fin S.componentCount
      let defaultComponent : Fin S.componentCount := ⟨0, S.hcomponentCount_pos⟩
      let pathOfPrefix : Prefix → AlgorithmSamplePath S :=
        fun w k a => if hk : k < index s t then w ⟨k, hk⟩ a else defaultComponent
      let currentFromPrefix : Prefix → E :=
        fun w => paperIterate S run ⟨index s t, hidx_pos'⟩ (pathOfPrefix w)
      let previousFromPrefix : Prefix → E :=
        fun w => paperIterate S run ⟨index s (t - 1), hidx_pred_pos⟩ (pathOfPrefix w)
      let φ : Prefix → Fin S.componentCount → ℝ :=
        fun w i =>
          ‖sampledGradientCorrection S (currentFromPrefix w) (previousFromPrefix w) i -
            (SOptLib.finiteUniformAverage S.componentGradient (currentFromPrefix w) -
              SOptLib.finiteUniformAverage S.componentGradient (previousFromPrefix w))‖ ^ 2
      let B : Prefix → ℝ :=
        fun w => S.L ^ 2 * ‖currentFromPrefix w - previousFromPrefix w‖ ^ 2
      have hcurrent_reconstruct :
          ∀ ω : AlgorithmSamplePath S,
            currentFromPrefix (strictPrefixKey ω) =
              paperIterate S run ⟨index s t, hidx_pos'⟩ ω := by
        intro ω
        have hrun_current :
            run (index s t - 1) (pathOfPrefix (strictPrefixKey ω)) =
              run (index s t - 1) ω :=
          runState_eq_of_batch_prefix_eq S (algorithmBatchStream S) run hrun
            (index s t - 1) (pathOfPrefix (strictPrefixKey ω)) ω
            (fun q hq a => by
              have hqlt : q < index s t := by omega
              dsimp [pathOfPrefix, strictPrefixKey]
              simp [algorithmBatchStream, hqlt])
        dsimp [currentFromPrefix]
        simpa [paperIterate, iterate, SOptLib.positiveTimeIterateView_eq,
          hrun_current]
      have hprevious_reconstruct :
          ∀ ω : AlgorithmSamplePath S,
            previousFromPrefix (strictPrefixKey ω) =
              paperIterate S run ⟨index s (t - 1), hidx_pred_pos⟩ ω := by
        intro ω
        have hrun_previous :
            run (index s (t - 1) - 1) (pathOfPrefix (strictPrefixKey ω)) =
              run (index s (t - 1) - 1) ω :=
          runState_eq_of_batch_prefix_eq S (algorithmBatchStream S) run hrun
            (index s (t - 1) - 1) (pathOfPrefix (strictPrefixKey ω)) ω
            (fun q hq a => by
              have hqlt : q < index s t := by
                dsimp [index] at hq ⊢
                simp [SOptLib.global_index_def] at hq ⊢
                omega
              dsimp [pathOfPrefix, strictPrefixKey]
              simp [algorithmBatchStream, hqlt])
        dsimp [previousFromPrefix]
        simpa [paperIterate, iterate, SOptLib.positiveTimeIterateView_eq,
          hrun_previous]
      have hxProc_current :
          ∀ ω : AlgorithmSamplePath S,
            xProc (index s t) ω = currentFromPrefix (strictPrefixKey ω) := by
        intro ω
        simpa [xProc, hidx_pos'] using (hcurrent_reconstruct ω).symm
      have hxProc_previous :
          ∀ ω : AlgorithmSamplePath S,
            xProc (index s (t - 1)) ω = previousFromPrefix (strictPrefixKey ω) := by
        intro ω
        simpa [xProc, hidx_pred_pos] using (hprevious_reconstruct ω).symm
      have hφ_meas : Measurable (Function.uncurry φ) := by
        exact measurable_of_finite _
      have hB_meas : Measurable B := by
        exact measurable_of_finite _
      have hX_meas :
          @Measurable (AlgorithmSamplePath S) Prefix pathMS inferInstance strictPrefixKey := by
        simpa [Prefix, pathMS] using hstrictPrefixKey_meas
      have hY_meas :
          @Measurable (AlgorithmSamplePath S) (Fin S.componentCount) pathMS sampleMS
            (fun ω : AlgorithmSamplePath S => ω (index s t) r) := by
        simpa [sampleCoord, pathMS, sampleMS] using hsampleCoord_meas (index s t, r)
      have hφ_comp_eq :
          (fun ω : AlgorithmSamplePath S =>
              φ (strictPrefixKey ω) (ω (index s t) r)) =
            fun ω : AlgorithmSamplePath S => ‖eps r ω‖ ^ 2 := by
        funext ω
        dsimp [φ, eps]
        simp [hcurrent_reconstruct ω, hprevious_reconstruct ω]
      have hφ_comp_int :
          Integrable[pathMS]
            (fun ω : AlgorithmSamplePath S =>
              φ (strictPrefixKey ω) (ω (index s t) r)) μ := by
        simpa [hφ_comp_eq, pathMS] using heps_sq_int r
      have hB_comp_int :
          Integrable[pathMS] (fun ω : AlgorithmSamplePath S => B (strictPrefixKey ω)) μ := by
        have hB_comp_meas :
            AEStronglyMeasurable[pathMS]
              (fun ω : AlgorithmSamplePath S => B (strictPrefixKey ω)) μ :=
          (hB_meas.comp hX_meas).aestronglyMeasurable
        have hfin :
            (Set.range (fun ω : AlgorithmSamplePath S => B (strictPrefixKey ω))).Finite := by
          refine (Set.finite_range B).subset ?_
          intro z hz
          rcases hz with ⟨ω, rfl⟩
          exact ⟨strictPrefixKey ω, rfl⟩
        letI : MeasurableSpace (AlgorithmSamplePath S) := pathMS
        exact integrable_of_finite_range hB_comp_meas hfin
      have hpmf_atom :
          ∀ i : Fin S.componentCount,
            ((componentSamplingPMF S) i).toReal = componentSamplingProbability S i := by
        intro i
        calc
          ((componentSamplingPMF S) i).toReal =
              (ENNReal.ofReal (SOptLib.smoothnessImportanceWeight
                (fun i : Fin S.componentCount => S.componentL i)
                (S.componentCount : ℝ) S.L i)).toReal := by
            rw [componentSamplingPMF, SOptLib.smoothnessImportancePMF_apply]
          _ = SOptLib.smoothnessImportanceWeight
                (fun i : Fin S.componentCount => S.componentL i)
                (S.componentCount : ℝ) S.L i := by
            rw [ENNReal.toReal_ofReal]
            simpa [componentSamplingProbability, SOptLib.smoothnessImportanceWeight] using
              componentSamplingProbability_nonneg S i
          _ = componentSamplingProbability S i := by
            simp [componentSamplingProbability, SOptLib.smoothnessImportanceWeight]
      have hfixed_bound :
          ∀ w : Prefix, ∫ i, φ w i ∂(componentSamplingPMF S).toMeasure ≤ B w := by
        intro w
        have hid :
            IdentDistrib (fun i : Fin S.componentCount => i)
              (fun i : Fin S.componentCount => i)
              (componentSamplingPMF S).toMeasure
              (componentSamplingPMF S).toMeasure := by
          exact IdentDistrib.refl measurable_id.aemeasurable
        have htransport :=
          identDistrib_finite_pmf_integrable_integral_le_weighted_sum_bound
            (P := (componentSamplingPMF S).toMeasure)
            (sample := fun i : Fin S.componentCount => i)
            (pmf := componentSamplingPMF S)
            (q := componentSamplingProbability S)
            (phi := φ w)
            (C := B w)
            hid hpmf_atom
            (by
              dsimp [φ, B]
              simpa using hcentered_component_budget (pathOfPrefix w))
        exact htransport.2
      have htransport :
          ∫ ω : AlgorithmSamplePath S,
              φ (strictPrefixKey ω) (ω (index s t) r) ∂μ ≤
            ∫ ω : AlgorithmSamplePath S, B (strictPrefixKey ω) ∂μ :=
        by
          letI : MeasurableSpace (AlgorithmSamplePath S) := pathMS
          exact
            integral_comp_le_integral_bound_of_indep_fixed_integral_bound
              (P := μ) (ν := (componentSamplingPMF S).toMeasure)
              (φ := φ) (B := B) (X := strictPrefixKey)
              (Y := fun ω : AlgorithmSamplePath S => ω (index s t) r)
              hφ_meas hB_meas hX_meas hY_meas
              (hstrictPrefix_current_indep r) (hcurrent_coordinate_law r)
              hφ_comp_int hB_comp_int hfixed_bound
      have hB_comp_eq :
          (fun ω : AlgorithmSamplePath S => B (strictPrefixKey ω)) =
            fun ω : AlgorithmSamplePath S =>
              S.L ^ 2 *
                ‖xProc (index s t) ω - xProc (index s (t - 1)) ω‖ ^ 2 := by
        funext ω
        dsimp [B]
        simp [hxProc_current ω, hxProc_previous ω]
      calc
        ∫ ω : AlgorithmSamplePath S, ‖eps r ω‖ ^ 2 ∂μ =
            ∫ ω : AlgorithmSamplePath S,
              φ (strictPrefixKey ω) (ω (index s t) r) ∂μ := by
              rw [hφ_comp_eq]
        _ ≤ ∫ ω : AlgorithmSamplePath S, B (strictPrefixKey ω) ∂μ := htransport
        _ =
            ∫ ω : AlgorithmSamplePath S,
              S.L ^ 2 *
                ‖xProc (index s t) ω - xProc (index s (t - 1)) ω‖ ^ 2 ∂μ := by
              rw [hB_comp_eq]
        _ =
            S.L ^ 2 *
              ∫ ω : AlgorithmSamplePath S,
                ‖xProc (index s t) ω - xProc (index s (t - 1)) ω‖ ^ 2 ∂μ := by
              rw [integral_const_mul]
    have hbatch_from_cross :
        (∀ r ∈ (Finset.univ : Finset (Fin S.b)),
          ∀ q ∈ (Finset.univ : Finset (Fin S.b)), r ≠ q →
            ∫ ω : AlgorithmSamplePath S, ⟪eps r ω, eps q ω⟫_ℝ ∂μ = 0) →
        ∫ ω : AlgorithmSamplePath S, ‖centeredMiniBatchIncrement ω‖ ^ 2 ∂μ ≤
          (S.L ^ 2 *
            ∫ ω : AlgorithmSamplePath S,
              ‖xProc (index s t) ω - xProc (index s (t - 1)) ω‖ ^ 2 ∂μ) /
            (S.b : ℝ) :=
      hcenteredMiniBatchIncrement_secondMoment_of_eps heps_meas heps_diag
    have heps_cross :
        ∀ r ∈ (Finset.univ : Finset (Fin S.b)),
          ∀ q ∈ (Finset.univ : Finset (Fin S.b)), r ≠ q →
            ∫ ω : AlgorithmSamplePath S, ⟪eps r ω, eps q ω⟫_ℝ ∂μ = 0 := by
      intro r _hr q _hq hrq
      haveI : IsProbabilityMeasure μ := by
        simpa [μ] using hLaw.1
      let Prefix := Fin (index s t) → Fin S.b → Fin S.componentCount
      let defaultComponent : Fin S.componentCount := ⟨0, S.hcomponentCount_pos⟩
      let pathOfPrefix : Prefix → AlgorithmSamplePath S :=
        fun w k a => if hk : k < index s t then w ⟨k, hk⟩ a else defaultComponent
      let currentFromPrefix : Prefix → E :=
        fun w => paperIterate S run ⟨index s t, hidx_pos'⟩ (pathOfPrefix w)
      let previousFromPrefix : Prefix → E :=
        fun w => paperIterate S run ⟨index s (t - 1), hidx_pred_pos⟩ (pathOfPrefix w)
      let centeredCorrection : Prefix → Fin S.componentCount → E :=
        fun w i =>
          sampledGradientCorrection S (currentFromPrefix w) (previousFromPrefix w) i -
            (SOptLib.finiteUniformAverage S.componentGradient (currentFromPrefix w) -
              SOptLib.finiteUniformAverage S.componentGradient (previousFromPrefix w))
      let leftResidual : Prefix × Fin S.componentCount → E :=
        fun wi => centeredCorrection wi.1 wi.2
      let φ : Prefix × Fin S.componentCount → Fin S.componentCount → ℝ :=
        fun wi i => ⟪leftResidual wi, centeredCorrection wi.1 i⟫_ℝ
      have hcurrent_reconstruct :
          ∀ ω : AlgorithmSamplePath S,
            currentFromPrefix (strictPrefixKey ω) =
              paperIterate S run ⟨index s t, hidx_pos'⟩ ω := by
        intro ω
        have hrun_current :
            run (index s t - 1) (pathOfPrefix (strictPrefixKey ω)) =
              run (index s t - 1) ω :=
          runState_eq_of_batch_prefix_eq S (algorithmBatchStream S) run hrun
            (index s t - 1) (pathOfPrefix (strictPrefixKey ω)) ω
            (fun q hq a => by
              have hqlt : q < index s t := by omega
              dsimp [pathOfPrefix, strictPrefixKey]
              simp [algorithmBatchStream, hqlt])
        dsimp [currentFromPrefix]
        simpa [paperIterate, iterate, SOptLib.positiveTimeIterateView_eq,
          hrun_current]
      have hprevious_reconstruct :
          ∀ ω : AlgorithmSamplePath S,
            previousFromPrefix (strictPrefixKey ω) =
              paperIterate S run ⟨index s (t - 1), hidx_pred_pos⟩ ω := by
        intro ω
        have hrun_previous :
            run (index s (t - 1) - 1) (pathOfPrefix (strictPrefixKey ω)) =
              run (index s (t - 1) - 1) ω :=
          runState_eq_of_batch_prefix_eq S (algorithmBatchStream S) run hrun
            (index s (t - 1) - 1) (pathOfPrefix (strictPrefixKey ω)) ω
            (fun q hq a => by
              have hqlt : q < index s t := by
                dsimp [index] at hq ⊢
                simp [SOptLib.global_index_def] at hq ⊢
                omega
              dsimp [pathOfPrefix, strictPrefixKey]
              simp [algorithmBatchStream, hqlt])
        dsimp [previousFromPrefix]
        simpa [paperIterate, iterate, SOptLib.positiveTimeIterateView_eq,
          hrun_previous]
      have hφ_meas : Measurable (Function.uncurry φ) := by
        exact measurable_of_finite _
      have hX_meas :
          @Measurable (AlgorithmSamplePath S)
            (Prefix × Fin S.componentCount) pathMS inferInstance
            (fun ω : AlgorithmSamplePath S =>
              (strictPrefixKey ω, ω (index s t) r)) := by
        have hprefix_meas :
            @Measurable (AlgorithmSamplePath S) Prefix pathMS inferInstance strictPrefixKey := by
          simpa [Prefix, pathMS] using hstrictPrefixKey_meas
        have hr_meas :
            @Measurable (AlgorithmSamplePath S) (Fin S.componentCount) pathMS sampleMS
              (fun ω : AlgorithmSamplePath S => ω (index s t) r) := by
          simpa [sampleCoord] using hsampleCoord_meas (index s t, r)
        exact hprefix_meas.prodMk hr_meas
      have hY_meas :
          @Measurable (AlgorithmSamplePath S) (Fin S.componentCount) pathMS sampleMS
            (fun ω : AlgorithmSamplePath S => ω (index s t) q) := by
        simpa [sampleCoord] using hsampleCoord_meas (index s t, q)
      have hcomp_eq :
          (fun ω : AlgorithmSamplePath S =>
              φ (strictPrefixKey ω, ω (index s t) r) (ω (index s t) q)) =
            fun ω : AlgorithmSamplePath S => ⟪eps r ω, eps q ω⟫_ℝ := by
        funext ω
        dsimp [φ, leftResidual, centeredCorrection, eps]
        simp [hcurrent_reconstruct ω, hprevious_reconstruct ω]
      have hcomp_int :
          Integrable[pathMS]
            (fun ω : AlgorithmSamplePath S =>
              φ (strictPrefixKey ω, ω (index s t) r) (ω (index s t) q)) μ := by
        rw [hcomp_eq]
        letI : MeasurableSpace (AlgorithmSamplePath S) := pathMS
        simpa [pathMS] using integrable_inner_of_integrable_sq_norm
          (heps_meas r) (heps_meas q) (heps_sq_int r) (heps_sq_int q)
      have hfixed_zero :
          ∀ wi : Prefix × Fin S.componentCount,
            ∫ i : Fin S.componentCount, φ wi i ∂(componentSamplingPMF S).toMeasure = 0 := by
        intro wi
        dsimp [φ, leftResidual, centeredCorrection]
        have hzero :=
          (integral_inner_sub_mean_eq_zero_of_integral_eq
            (μ := (componentSamplingPMF S).toMeasure)
            (F := sampledGradientCorrection S (currentFromPrefix wi.1) (previousFromPrefix wi.1))
            (mean := SOptLib.finiteUniformAverage S.componentGradient (currentFromPrefix wi.1) -
              SOptLib.finiteUniformAverage S.componentGradient (previousFromPrefix wi.1))
            (direction := centeredCorrection wi.1 wi.2)
            (Integrable.of_finite
              (f := sampledGradientCorrection S (currentFromPrefix wi.1) (previousFromPrefix wi.1))
              (μ := (componentSamplingPMF S).toMeasure))
            (sampledGradientCorrection_integral_eq_finiteAverageGradient_sub
              S (currentFromPrefix wi.1) (previousFromPrefix wi.1))).2
        rw [← hzero]
        refine integral_congr_ae ?_
        filter_upwards with i
        exact real_inner_comm _ _
      have htransport :
          ∫ ω : AlgorithmSamplePath S,
              φ (strictPrefixKey ω, ω (index s t) r) (ω (index s t) q) ∂μ = 0 := by
        letI : MeasurableSpace (AlgorithmSamplePath S) := pathMS
        exact
          integral_comp_eq_zero_of_indep_fixed_integral_zero
            (P := μ) (ν := (componentSamplingPMF S).toMeasure)
            (φ := φ)
            (X := fun ω : AlgorithmSamplePath S =>
              (strictPrefixKey ω, ω (index s t) r))
            (Y := fun ω : AlgorithmSamplePath S => ω (index s t) q)
            hφ_meas hX_meas hY_meas
            (hstrictPrefix_peer_current_indep r q hrq)
            (hcurrent_coordinate_law q)
            hcomp_int hfixed_zero
      rwa [hcomp_eq] at htransport
    have hbatch_bound :
        ∫ ω : AlgorithmSamplePath S, ‖centeredMiniBatchIncrement ω‖ ^ 2 ∂μ ≤
          (S.L ^ 2 *
            ∫ ω : AlgorithmSamplePath S,
              ‖xProc (index s t) ω - xProc (index s (t - 1)) ω‖ ^ 2 ∂μ) /
            (S.b : ℝ) :=
      hbatch_from_cross heps_cross
    have hdeltaProc_prev_meas :
        AEStronglyMeasurable[pathMS] (deltaProc (index s (t - 1))) μ := by
      change AEStronglyMeasurable[pathMS] (deltaProc (index s (t - 1))) (algorithmSampleLaw S)
      refine aestronglyMeasurable_algorithmSampleLaw_of_prefix_const S (index s (t - 1)) ?_
      intro ω ω' hprefix
      have hrun_estimator :
          run (index s (t - 1)) ω = run (index s (t - 1)) ω' :=
        runState_eq_of_batch_prefix_eq S (algorithmBatchStream S) run hrun
          (index s (t - 1)) ω ω' (fun q hq a => by
            exact hprefix q (by omega) a)
      have hrun_iterate :
          run (index s (t - 1) - 1) ω = run (index s (t - 1) - 1) ω' :=
        runState_eq_of_batch_prefix_eq S (algorithmBatchStream S) run hrun
          (index s (t - 1) - 1) ω ω' (fun q hq a => by
            exact hprefix q (by omega) a)
      dsimp [deltaProc]
      simp [hidx_pred_pos, paperEstimator, paperIterate, estimator, iterate,
        SOptLib.positiveTimeIterateView_eq, hrun_estimator, hrun_iterate]
    have hprev_eps_cross :
        ∀ r : Fin S.b,
          ∫ ω : AlgorithmSamplePath S,
            ⟪deltaProc (index s (t - 1)) ω, eps r ω⟫_ℝ ∂μ = 0 := by
      intro r
      haveI : IsProbabilityMeasure μ := by
        simpa [μ] using hLaw.1
      let Prefix := Fin (index s t) → Fin S.b → Fin S.componentCount
      let defaultComponent : Fin S.componentCount := ⟨0, S.hcomponentCount_pos⟩
      let pathOfPrefix : Prefix → AlgorithmSamplePath S :=
        fun w k a => if hk : k < index s t then w ⟨k, hk⟩ a else defaultComponent
      let currentFromPrefix : Prefix → E :=
        fun w => paperIterate S run ⟨index s t, hidx_pos'⟩ (pathOfPrefix w)
      let previousFromPrefix : Prefix → E :=
        fun w => paperIterate S run ⟨index s (t - 1), hidx_pred_pos⟩ (pathOfPrefix w)
      let deltaPrevFromPrefix : Prefix → E :=
        fun w => deltaProc (index s (t - 1)) (pathOfPrefix w)
      let centeredCorrection : Prefix → Fin S.componentCount → E :=
        fun w i =>
          sampledGradientCorrection S (currentFromPrefix w) (previousFromPrefix w) i -
            (SOptLib.finiteUniformAverage S.componentGradient (currentFromPrefix w) -
              SOptLib.finiteUniformAverage S.componentGradient (previousFromPrefix w))
      let φ : Prefix → Fin S.componentCount → ℝ :=
        fun w i => ⟪deltaPrevFromPrefix w, centeredCorrection w i⟫_ℝ
      have hcurrent_reconstruct :
          ∀ ω : AlgorithmSamplePath S,
            currentFromPrefix (strictPrefixKey ω) =
              paperIterate S run ⟨index s t, hidx_pos'⟩ ω := by
        intro ω
        have hrun_current :
            run (index s t - 1) (pathOfPrefix (strictPrefixKey ω)) =
              run (index s t - 1) ω :=
          runState_eq_of_batch_prefix_eq S (algorithmBatchStream S) run hrun
            (index s t - 1) (pathOfPrefix (strictPrefixKey ω)) ω
            (fun q hq a => by
              have hqlt : q < index s t := by omega
              dsimp [pathOfPrefix, strictPrefixKey]
              simp [algorithmBatchStream, hqlt])
        dsimp [currentFromPrefix]
        simpa [paperIterate, iterate, SOptLib.positiveTimeIterateView_eq,
          hrun_current]
      have hprevious_reconstruct :
          ∀ ω : AlgorithmSamplePath S,
            previousFromPrefix (strictPrefixKey ω) =
              paperIterate S run ⟨index s (t - 1), hidx_pred_pos⟩ ω := by
        intro ω
        have hrun_previous :
            run (index s (t - 1) - 1) (pathOfPrefix (strictPrefixKey ω)) =
              run (index s (t - 1) - 1) ω :=
          runState_eq_of_batch_prefix_eq S (algorithmBatchStream S) run hrun
            (index s (t - 1) - 1) (pathOfPrefix (strictPrefixKey ω)) ω
            (fun q hq a => by
              have hqlt : q < index s t := by
                dsimp [index] at hq ⊢
                simp [SOptLib.global_index_def] at hq ⊢
                omega
              dsimp [pathOfPrefix, strictPrefixKey]
              simp [algorithmBatchStream, hqlt])
        dsimp [previousFromPrefix]
        simpa [paperIterate, iterate, SOptLib.positiveTimeIterateView_eq,
          hrun_previous]
      have hdeltaPrev_reconstruct :
          ∀ ω : AlgorithmSamplePath S,
            deltaPrevFromPrefix (strictPrefixKey ω) =
              deltaProc (index s (t - 1)) ω := by
        intro ω
        have hrun_estimator :
            run (index s (t - 1)) (pathOfPrefix (strictPrefixKey ω)) =
              run (index s (t - 1)) ω :=
          runState_eq_of_batch_prefix_eq S (algorithmBatchStream S) run hrun
            (index s (t - 1)) (pathOfPrefix (strictPrefixKey ω)) ω
            (fun q hq a => by
              have hqlt : q < index s t := by
                dsimp [index] at hq ⊢
                simp [SOptLib.global_index_def] at hq ⊢
                omega
              dsimp [pathOfPrefix, strictPrefixKey]
              simp [algorithmBatchStream, hqlt])
        have hrun_iterate :
            run (index s (t - 1) - 1) (pathOfPrefix (strictPrefixKey ω)) =
              run (index s (t - 1) - 1) ω :=
          runState_eq_of_batch_prefix_eq S (algorithmBatchStream S) run hrun
            (index s (t - 1) - 1) (pathOfPrefix (strictPrefixKey ω)) ω
            (fun q hq a => by
              have hqlt : q < index s t := by
                dsimp [index] at hq ⊢
                simp [SOptLib.global_index_def] at hq ⊢
                omega
              dsimp [pathOfPrefix, strictPrefixKey]
              simp [algorithmBatchStream, hqlt])
        dsimp [deltaPrevFromPrefix, deltaProc]
        simp [hidx_pred_pos, paperEstimator, paperIterate, estimator, iterate,
          SOptLib.positiveTimeIterateView_eq, hrun_estimator, hrun_iterate]
      have hφ_meas : Measurable (Function.uncurry φ) := by
        exact measurable_of_finite _
      have hX_meas :
          @Measurable (AlgorithmSamplePath S) Prefix pathMS inferInstance strictPrefixKey := by
        simpa [Prefix, pathMS] using hstrictPrefixKey_meas
      have hY_meas :
          @Measurable (AlgorithmSamplePath S) (Fin S.componentCount) pathMS sampleMS
            (fun ω : AlgorithmSamplePath S => ω (index s t) r) := by
        simpa [sampleCoord] using hsampleCoord_meas (index s t, r)
      have hcomp_eq :
          (fun ω : AlgorithmSamplePath S =>
              φ (strictPrefixKey ω) (ω (index s t) r)) =
            fun ω : AlgorithmSamplePath S =>
              ⟪deltaProc (index s (t - 1)) ω, eps r ω⟫_ℝ := by
        funext ω
        dsimp [φ, centeredCorrection, eps]
        simp [hcurrent_reconstruct ω, hprevious_reconstruct ω,
          hdeltaPrev_reconstruct ω]
      have hcomp_int :
          Integrable[pathMS]
            (fun ω : AlgorithmSamplePath S =>
              φ (strictPrefixKey ω) (ω (index s t) r)) μ := by
        rw [hcomp_eq]
        letI : MeasurableSpace (AlgorithmSamplePath S) := pathMS
        simpa [pathMS] using integrable_inner_of_integrable_sq_norm
          (hdeltaProc_prev_meas) (heps_meas r)
          (hdeltaProc_prev_sq_int) (heps_sq_int r)
      have hfixed_zero :
          ∀ w : Prefix,
            ∫ i : Fin S.componentCount, φ w i ∂(componentSamplingPMF S).toMeasure = 0 := by
        intro w
        dsimp [φ, deltaPrevFromPrefix, centeredCorrection]
        have hzero :=
          (integral_inner_sub_mean_eq_zero_of_integral_eq
            (μ := (componentSamplingPMF S).toMeasure)
            (F := sampledGradientCorrection S (currentFromPrefix w) (previousFromPrefix w))
            (mean := SOptLib.finiteUniformAverage S.componentGradient (currentFromPrefix w) -
              SOptLib.finiteUniformAverage S.componentGradient (previousFromPrefix w))
            (direction := deltaPrevFromPrefix w)
            (Integrable.of_finite
              (f := sampledGradientCorrection S (currentFromPrefix w) (previousFromPrefix w))
              (μ := (componentSamplingPMF S).toMeasure))
            (sampledGradientCorrection_integral_eq_finiteAverageGradient_sub
              S (currentFromPrefix w) (previousFromPrefix w))).2
        rw [← hzero]
        refine integral_congr_ae ?_
        filter_upwards with i
        exact real_inner_comm _ _
      have htransport :
          ∫ ω : AlgorithmSamplePath S,
              φ (strictPrefixKey ω) (ω (index s t) r) ∂μ = 0 := by
        letI : MeasurableSpace (AlgorithmSamplePath S) := pathMS
        exact
          integral_comp_eq_zero_of_indep_fixed_integral_zero
            (P := μ) (ν := (componentSamplingPMF S).toMeasure)
            (φ := φ) (X := strictPrefixKey)
            (Y := fun ω : AlgorithmSamplePath S => ω (index s t) r)
            hφ_meas hX_meas hY_meas
            (hstrictPrefix_current_indep r)
            (hcurrent_coordinate_law r)
            hcomp_int hfixed_zero
      rwa [hcomp_eq] at htransport
    have hprev_increment_cross :
        ∫ ω : AlgorithmSamplePath S,
          ⟪deltaProc (index s (t - 1)) ω, centeredMiniBatchIncrement ω⟫_ℝ ∂μ = 0 := by
      letI : MeasurableSpace (AlgorithmSamplePath S) := pathMS
      have havg_cross :
          ∫ ω : AlgorithmSamplePath S,
            ⟪deltaProc (index s (t - 1)) ω,
              ((S.b : ℝ)⁻¹) • Finset.sum Finset.univ (fun r : Fin S.b => eps r ω)⟫_ℝ ∂μ = 0 :=
        pastResidual_inner_centeredMiniBatchAverage_integral_eq_zero
          (P := μ) (I := (Finset.univ : Finset (Fin S.b))) (m := S.b)
          (d := deltaProc (index s (t - 1))) (eps := eps)
          hdeltaProc_prev_meas
          (fun r _hr => heps_meas r)
          hdeltaProc_prev_sq_int
          (fun r _hr => heps_sq_int r)
          (fun r _hr => hprev_eps_cross r)
      calc
        ∫ ω : AlgorithmSamplePath S,
            ⟪deltaProc (index s (t - 1)) ω, centeredMiniBatchIncrement ω⟫_ℝ ∂μ =
            ∫ ω : AlgorithmSamplePath S,
              ⟪deltaProc (index s (t - 1)) ω,
                ((S.b : ℝ)⁻¹) • Finset.sum Finset.univ (fun r : Fin S.b => eps r ω)⟫_ℝ ∂μ := by
              refine integral_congr_ae (Filter.Eventually.of_forall ?_)
              intro ω
              simp [hcenteredMiniBatchIncrement_as_average ω]
        _ = 0 := havg_cross
    have hinc_meas :
        AEStronglyMeasurable[pathMS] centeredMiniBatchIncrement μ := by
      have havg_meas :
          AEStronglyMeasurable[pathMS]
            (((S.b : ℝ)⁻¹) • Finset.sum Finset.univ (fun r : Fin S.b => eps r)) μ := by
        simpa [pathMS] using
          (Finset.aestronglyMeasurable_sum (s := (Finset.univ : Finset (Fin S.b)))
            (fun r _hr => heps_meas r)).const_smul ((S.b : ℝ)⁻¹)
      refine havg_meas.congr ?_
      filter_upwards [] with ω
      rw [Pi.smul_apply]
      simpa [Finset.sum_apply] using (hcenteredMiniBatchIncrement_as_average ω).symm
    have hinc_sq :
        Integrable[pathMS] (fun ω : AlgorithmSamplePath S =>
          ‖centeredMiniBatchIncrement ω‖ ^ 2) μ := by
      letI : MeasurableSpace (AlgorithmSamplePath S) := pathMS
      exact
        integrable_sq_norm_centeredMiniBatchAverage
          (μ := μ) (I := (Finset.univ : Finset (Fin S.b))) (m := S.b)
          (δ := eps) (avg := centeredMiniBatchIncrement)
          (fun r _hr => heps_meas r)
          (fun r _hr => heps_sq_int r)
          (by
            funext ω
            exact hcenteredMiniBatchIncrement_as_average ω)
    have hstep_current :
        ∫ ω : AlgorithmSamplePath S, ‖deltaProc (index s t) ω‖ ^ 2 ∂μ ≤
          ∫ ω : AlgorithmSamplePath S, ‖deltaProc (index s (t - 1)) ω‖ ^ 2 ∂μ +
            (S.L ^ 2 / (S.b : ℝ)) *
              ∫ ω : AlgorithmSamplePath S,
                ‖xProc (index s t) ω - xProc (index s (t - 1)) ω‖ ^ 2 ∂μ := by
      letI : MeasurableSpace (AlgorithmSamplePath S) := pathMS
      exact
        recursiveEstimatorResidual_secondMoment_step_le_of_centered_minibatch
          (μ := μ) (I := (Finset.univ : Finset (Fin S.b))) (b := S.b)
          (deltaPrev := deltaProc (index s (t - 1)))
          (deltaNext := deltaProc (index s t))
          (inc := centeredMiniBatchIncrement)
          (eps := eps)
          (xPrev := xProc (index s (t - 1)))
          (xCurr := xProc (index s t))
          (L := S.L)
          S.hb_pos (by simp)
          hdeltaProc_prev_meas
          (fun r _hr => heps_meas r)
          hdeltaProc_prev_sq_int
          (fun r _hr => heps_diag r)
          (by
            funext ω
            exact hcenteredMiniBatchIncrement_as_average ω)
          (Filter.Eventually.of_forall hdeltaProc_nonrefresh_recurrence)
          heps_cross
          hprev_increment_cross
    exact hstep_current
  have hrec :
      ∫ ω : AlgorithmSamplePath S, ‖deltaProc (index s j) ω‖ ^ 2 ∂μ ≤
        (S.L ^ 2 / (S.b : ℝ)) *
          ∫ ω : AlgorithmSamplePath S,
            SOptLib.epochSquaredDifferenceSum xProc index s j ω ∂μ + 0 :=
    epoch_second_moment_le_difference_sum_add_const_of_one_step_recurrence
      μ deltaProc xProc index Valid S.T (S.L ^ 2 / (S.b : ℝ)) 0
      hvalid_prefix hbase_all hdelta_sq_int_all hdiff_sq_int_all hstep_all
      s j hj_epoch.1 hj_epoch.2 hvalid_current
  have htilde_epoch :
      (S.L ^ 2 / (S.b : ℝ)) *
          ∫ ω : AlgorithmSamplePath S,
            SOptLib.epochSquaredDifferenceSum xProc index s j ω ∂μ + 0 ≤
        (S.b : ℝ)⁻¹ *
          Finset.sum (Finset.Icc 2 j)
            (fun i => tildeTerm (SOptLib.global_index S.T s (i - 1))) := by
    have hterm :
        ∀ i ∈ Finset.Icc 2 j,
          tildeTerm (SOptLib.global_index S.T s (i - 1)) =
            S.L ^ 2 *
              ∫ ω : AlgorithmSamplePath S,
                ‖xProc (index s i) ω - xProc (index s (i - 1)) ω‖ ^ 2 ∂μ := by
      intro i hi
      have hiIcc := Finset.mem_Icc.mp hi
      have hprev_valid : Valid s (i - 1) :=
        hvalid_prefix (by omega) hvalid_current
      have hidx_prev_pos : 1 ≤ index s (i - 1) := by
        change 1 ≤ SOptLib.global_index S.T s (i - 1)
        rw [SOptLib.global_index_def]
        omega
      have hidx_i_pos : 1 ≤ index s i := by
        change 1 ≤ SOptLib.global_index S.T s i
        rw [SOptLib.global_index_def]
        omega
      have hidx_i_pred : index s i - 1 = index s (i - 1) := by
        dsimp [index]
        simp [SOptLib.global_index_def]
        omega
      have hwin_prev : index s (i - 1) ∈ outputWindow S := by
        simpa [outputWindow] using
          (Finset.mem_Icc.mpr ⟨hidx_prev_pos, hprev_valid.2.2⟩)
      have hgamma_inv_eq : S.gamma⁻¹ = S.L := by
        rw [hgamma_choice]
        exact inv_inv S.L
      rw [htilde_def]
      have hfun :
          (fun ω : AlgorithmSamplePath S =>
            if hk : SOptLib.global_index S.T s (i - 1) ∈ outputWindow S then
              ‖S.gamma⁻¹ •
                (paperIterate S run
                    ⟨SOptLib.global_index S.T s (i - 1),
                      (Finset.mem_Icc.mp (by simpa [outputWindow] using hk)).1⟩ ω -
                  iterate S run (SOptLib.global_index S.T s (i - 1)) ω)‖ ^ 2
            else 0) =
          (fun ω : AlgorithmSamplePath S =>
            S.L ^ 2 * ‖xProc (index s i) ω - xProc (index s (i - 1)) ω‖ ^ 2) := by
        funext ω
        have hx_i :
            xProc (index s i) ω = iterate S run (index s (i - 1)) ω := by
          simp [xProc, hidx_i_pos, paperIterate, iterate,
            SOptLib.positiveTimeIterateView_eq, hidx_i_pred]
        have hx_prev :
            xProc (index s (i - 1)) ω =
              paperIterate S run ⟨index s (i - 1), hidx_prev_pos⟩ ω := by
          simp [xProc, hidx_prev_pos]
        rw [dif_pos]
        · change
            ‖S.gamma⁻¹ •
              (paperIterate S run ⟨index s (i - 1), hidx_prev_pos⟩ ω -
                iterate S run (index s (i - 1)) ω)‖ ^ 2 =
              S.L ^ 2 * ‖xProc (index s i) ω - xProc (index s (i - 1)) ω‖ ^ 2
          rw [hgamma_inv_eq, hx_i, hx_prev]
          simp only [norm_smul, Real.norm_of_nonneg (le_of_lt hLpos)]
          rw [norm_sub_rev]
          ring
        · simpa [index] using hwin_prev
      change
        (∫ ω : AlgorithmSamplePath S,
          (if hk : SOptLib.global_index S.T s (i - 1) ∈ outputWindow S then
            ‖S.gamma⁻¹ •
              (paperIterate S run
                  ⟨SOptLib.global_index S.T s (i - 1),
                    (Finset.mem_Icc.mp (by simpa [outputWindow] using hk)).1⟩ ω -
                iterate S run (SOptLib.global_index S.T s (i - 1)) ω)‖ ^ 2
          else 0) ∂algorithmSampleLaw S) =
          S.L ^ 2 *
            ∫ ω : AlgorithmSamplePath S,
              ‖xProc (index s i) ω - xProc (index s (i - 1)) ω‖ ^ 2 ∂μ
      rw [hfun]
      change
        (∫ ω : AlgorithmSamplePath S,
          S.L ^ 2 * ‖xProc (index s i) ω - xProc (index s (i - 1)) ω‖ ^ 2 ∂μ) =
          S.L ^ 2 *
            ∫ ω : AlgorithmSamplePath S,
              ‖xProc (index s i) ω - xProc (index s (i - 1)) ω‖ ^ 2 ∂μ
      rw [integral_const_mul]
    have hsum_int :
        ∫ ω : AlgorithmSamplePath S,
            SOptLib.epochSquaredDifferenceSum xProc index s j ω ∂μ =
          Finset.sum (Finset.Icc 2 j)
            (fun i => ∫ ω : AlgorithmSamplePath S,
              ‖xProc (index s i) ω - xProc (index s (i - 1)) ω‖ ^ 2 ∂μ) := by
      change
        ∫ ω : AlgorithmSamplePath S,
          Finset.sum (Finset.Icc 2 j)
            (fun i => ‖xProc (index s i) ω - xProc (index s (i - 1)) ω‖ ^ 2) ∂μ =
        Finset.sum (Finset.Icc 2 j)
          (fun i => ∫ ω : AlgorithmSamplePath S,
            ‖xProc (index s i) ω - xProc (index s (i - 1)) ω‖ ^ 2 ∂μ)
      exact MeasureTheory.integral_finset_sum
        (μ := μ) (s := Finset.Icc 2 j)
        (f := fun i ω =>
          ‖xProc (index s i) ω - xProc (index s (i - 1)) ω‖ ^ 2)
        (fun i hi => by
          have hiIcc := Finset.mem_Icc.mp hi
          exact hdiff_sq_int_all s i hiIcc.1 (le_trans hiIcc.2 hj_epoch.2)
            (hvalid_prefix hiIcc.2 hvalid_current))
    have hsum_tilde :
        Finset.sum (Finset.Icc 2 j)
            (fun i => tildeTerm (SOptLib.global_index S.T s (i - 1))) =
          S.L ^ 2 * Finset.sum (Finset.Icc 2 j)
            (fun i => ∫ ω : AlgorithmSamplePath S,
              ‖xProc (index s i) ω - xProc (index s (i - 1)) ω‖ ^ 2 ∂μ) := by
      calc
        Finset.sum (Finset.Icc 2 j)
            (fun i => tildeTerm (SOptLib.global_index S.T s (i - 1))) =
          Finset.sum (Finset.Icc 2 j)
            (fun i => S.L ^ 2 *
              ∫ ω : AlgorithmSamplePath S,
                ‖xProc (index s i) ω - xProc (index s (i - 1)) ω‖ ^ 2 ∂μ) := by
            exact Finset.sum_congr rfl (fun i hi => by rw [hterm i hi])
        _ = S.L ^ 2 * Finset.sum (Finset.Icc 2 j)
            (fun i => ∫ ω : AlgorithmSamplePath S,
              ‖xProc (index s i) ω - xProc (index s (i - 1)) ω‖ ^ 2 ∂μ) := by
            rw [← Finset.mul_sum]
    calc
      (S.L ^ 2 / (S.b : ℝ)) *
          ∫ ω : AlgorithmSamplePath S,
            SOptLib.epochSquaredDifferenceSum xProc index s j ω ∂μ + 0
          = (S.b : ℝ)⁻¹ *
              (S.L ^ 2 * Finset.sum (Finset.Icc 2 j)
                (fun i => ∫ ω : AlgorithmSamplePath S,
                  ‖xProc (index s i) ω - xProc (index s (i - 1)) ω‖ ^ 2 ∂μ)) := by
            rw [hsum_int]
            ring
      _ ≤ (S.b : ℝ)⁻¹ *
          Finset.sum (Finset.Icc 2 j)
            (fun i => tildeTerm (SOptLib.global_index S.T s (i - 1))) := by
            rw [hsum_tilde]
  calc
    deltaTerm (SOptLib.global_index S.T s j) =
        ∫ ω : AlgorithmSamplePath S, ‖deltaProc (index s j) ω‖ ^ 2 ∂μ := by
          simpa [index] using hdeltaTerm_current_eq
    _ ≤ (S.L ^ 2 / (S.b : ℝ)) *
          ∫ ω : AlgorithmSamplePath S,
            SOptLib.epochSquaredDifferenceSum xProc index s j ω ∂μ + 0 := hrec
    _ ≤ (S.b : ℝ)⁻¹ *
          Finset.sum (Finset.Icc 2 j)
            (fun i => tildeTerm (SOptLib.global_index S.T s (i - 1))) :=
          htilde_epoch

/-- Summed Eq. (7.5.13) after replacing the terminal objective by `f^*`.

This is the source-level stochastic descent and epoch-summation bridge that
Theorem 7.18 needs before multiplying by `16L`: it aligns with the PDF sentence
"by summing up the first `N` inequalities" after Eq. (7.5.13). Candidates
considered: the SOptLib variance identities
`finset_weighted_variance_eq_second_moment_sub_norm_mean_sq` and
`Finset.weighted_variance_le_second_moment`, the nested residual aggregator
`sum_scaled_l2_error_le_epoch_budget_add_variance_floor`, and the scalar
telescope lemmas in `SOptLib.Glue.Algebra`; these supply reusable sub-algebra
but none packages the `runStateSpec`-driven CndG step, finite-sum estimator
recursion, and expected projected-gradient comparison for this source theorem. -/
private theorem theorem718_global_summed_7513_lowered (S : Setup E)
    (run : ℕ → AlgorithmSamplePath S → RunState E)
    (hrun : runStateSpec S (algorithmBatchStream S) run) :
    (1 / (16 * S.L)) *
        Finset.sum (outputWindow S)
          (fun k => algorithmExpectedSquaredPaperProjectedGradient S run k) ≤
      SOptLib.finiteUniformAverage S.componentObjective S.x₁ - fStar S +
        (3 / 2) * (S.N : ℝ) * S.eta := by
  classical
  have hLaw : algorithmSampleLawSpec S (algorithmSampleLaw S) :=
    algorithmSampleLaw_spec S
  have hLpos : 0 < S.L := averageSmoothness_pos S
  have hb_choice : S.b = 10 * S.T := S.hb_eq_ten_mul_T
  have hgamma_choice : S.gamma = S.L⁻¹ := S.hgamma_eq_inv_L
  have hgamma_pos : 0 < S.gamma := by
    rw [hgamma_choice]
    exact inv_pos.mpr hLpos
  have hmin := finiteSumMinimizer_spec S
  have hrun_spec := hrun
  have hstep_descent :
      ∀ k, (hk : k ∈ outputWindow S) → ∀ ω : AlgorithmSamplePath S,
        SOptLib.finiteUniformAverage S.componentObjective (iterate S run k ω) ≤
          SOptLib.finiteUniformAverage S.componentObjective (paperIterate S run
            ⟨k, (Finset.mem_Icc.mp (by simpa [outputWindow] using hk)).1⟩ ω) -
            (S.gamma⁻¹ - S.L / 2 - (S.L / 2) / 2) *
              ‖iterate S run k ω -
                paperIterate S run
                  ⟨k, (Finset.mem_Icc.mp (by simpa [outputWindow] using hk)).1⟩ ω‖ ^ 2 +
            (1 / (2 * (S.L / 2))) *
              ‖paperEstimator S run
                  ⟨k, (Finset.mem_Icc.mp (by simpa [outputWindow] using hk)).1⟩ ω -
                SOptLib.finiteUniformAverage S.componentGradient
                  (paperIterate S run
                    ⟨k, (Finset.mem_Icc.mp (by simpa [outputWindow] using hk)).1⟩ ω)‖ ^ 2 +
            S.eta := by
    intro k hk ω
    have hkIcc : k ∈ Finset.Icc 1 S.N := by
      simpa [outputWindow] using hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hkIcc).1
    have hq : 0 < S.L / 2 := by nlinarith
    simpa [hkIcc, hk1] using
      theorem718_cndg_smooth_descent_with_estimator_error
        S run hrun_spec hk1 ω hq
  have hmodel_distance :
      ∀ k, (hk : k ∈ outputWindow S) → ∀ ω : AlgorithmSamplePath S,
        ∃ zbar : E,
          zbar ∈ S.X ∧
          (∀ z : E, z ∈ S.X →
            ⟪paperEstimator S run
                ⟨k, (Finset.mem_Icc.mp (by simpa [outputWindow] using hk)).1⟩ ω,
              zbar⟫_ℝ +
                S.gamma⁻¹ / 2 *
                  ‖zbar -
                    paperIterate S run
                      ⟨k, (Finset.mem_Icc.mp (by simpa [outputWindow] using hk)).1⟩ ω‖ ^ 2 ≤
              ⟪paperEstimator S run
                  ⟨k, (Finset.mem_Icc.mp (by simpa [outputWindow] using hk)).1⟩ ω,
                z⟫_ℝ +
                S.gamma⁻¹ / 2 *
                  ‖z -
                    paperIterate S run
                      ⟨k, (Finset.mem_Icc.mp (by simpa [outputWindow] using hk)).1⟩ ω‖ ^ 2) ∧
          (1 / (2 * S.gamma)) *
              ‖iterate S run k ω - zbar‖ ^ 2 ≤ S.eta := by
    intro k hk ω
    have hkIcc : k ∈ Finset.Icc 1 S.N := by
      simpa [outputWindow] using hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hkIcc).1
    have hgamma_pos : 0 < S.gamma := by
      rw [hgamma_choice]
      exact inv_pos.mpr hLpos
    let x : E := paperIterate S run ⟨k, hk1⟩ ω
    let G : E := paperEstimator S run ⟨k, hk1⟩ ω
    let y : E := iterate S run k ω
    have hspec : cndGUpdateSpec S G x S.gamma S.eta y := by
      simpa [x, y, G] using paper_cndGUpdateSpec_at_step S run hrun_spec k hk1 ω
    let zbar : E := euclideanProjectedPoint S x G S.gamma
    have hzbar_spec : euclideanProjectedPointSpec S x G S.gamma zbar := by
      simpa [zbar] using euclideanProjectedPoint_spec S x G S.gamma
    have hzbar_mem : zbar ∈ S.X := hzbar_spec.1
    have hzbar_min :
        ∀ z : E, z ∈ S.X →
          ⟪G, zbar⟫_ℝ +
              S.gamma⁻¹ / 2 *
                ‖zbar - x‖ ^ 2 ≤
            ⟪G, z⟫_ℝ +
              S.gamma⁻¹ / 2 *
                ‖z - x‖ ^ 2 := by
      exact hzbar_spec.2
    have hdist :
        (1 / (2 * S.gamma)) * ‖y - zbar‖ ^ 2 ≤ S.eta := by
      exact theorem718_cndg_output_to_model_minimizer_distance
        S hgamma_pos hspec hzbar_mem hzbar_min
    refine ⟨zbar, hzbar_mem, ?_, ?_⟩
    · intro z hz
      simpa [x, G] using hzbar_min z hz
    · simpa [y] using hdist
  have hmodel_distance_canonical :
      ∀ k, (hk : k ∈ outputWindow S) → ∀ ω : AlgorithmSamplePath S,
        (1 / (2 * S.gamma)) *
          ‖iterate S run k ω -
            euclideanProjectedPoint S
              (paperIterate S run
                ⟨k, (Finset.mem_Icc.mp (by simpa [outputWindow] using hk)).1⟩ ω)
              (paperEstimator S run
                ⟨k, (Finset.mem_Icc.mp (by simpa [outputWindow] using hk)).1⟩ ω)
              S.gamma‖ ^ 2 ≤ S.eta := by
    intro k hk ω
    have hkIcc : k ∈ Finset.Icc 1 S.N := by
      simpa [outputWindow] using hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hkIcc).1
    let x : E := paperIterate S run ⟨k, hk1⟩ ω
    let G : E := paperEstimator S run ⟨k, hk1⟩ ω
    let y : E := iterate S run k ω
    have hspec : cndGUpdateSpec S G x S.gamma S.eta y := by
      simpa [x, y, G] using paper_cndGUpdateSpec_at_step S run hrun_spec k hk1 ω
    let zbar : E := euclideanProjectedPoint S x G S.gamma
    have hzbar_spec : euclideanProjectedPointSpec S x G S.gamma zbar := by
      simpa [zbar] using euclideanProjectedPoint_spec S x G S.gamma
    have hdist :
        (1 / (2 * S.gamma)) * ‖y - zbar‖ ^ 2 ≤ S.eta := by
      exact theorem718_cndg_output_to_model_minimizer_distance
        S hgamma_pos hspec hzbar_spec.1 hzbar_spec.2
    simpa [x, y, G, zbar, hkIcc, hk1] using hdist
  have hprojectedGradient_three_term :=
    theorem718_projected_gradient_three_term_bound
      S run hrun_spec hgamma_pos hmodel_distance_canonical
  have hprojectedGradient_split :
      ∀ k, (hk : k ∈ outputWindow S) → ∀ ω : AlgorithmSamplePath S,
        ‖paperProjectedGradient S run k ω‖ ^ 2 ≤
          2 *
            ‖S.gamma⁻¹ •
              (paperIterate S run
                  ⟨k, (Finset.mem_Icc.mp (by simpa [outputWindow] using hk)).1⟩ ω -
                euclideanProjectedPoint S
                  (paperIterate S run
                    ⟨k, (Finset.mem_Icc.mp (by simpa [outputWindow] using hk)).1⟩ ω)
                  (paperEstimator S run
                    ⟨k, (Finset.mem_Icc.mp (by simpa [outputWindow] using hk)).1⟩ ω)
                  S.gamma)‖ ^ 2 +
            2 *
              ‖paperEstimator S run
                  ⟨k, (Finset.mem_Icc.mp (by simpa [outputWindow] using hk)).1⟩ ω -
                SOptLib.finiteUniformAverage S.componentGradient
                  (paperIterate S run
                    ⟨k, (Finset.mem_Icc.mp (by simpa [outputWindow] using hk)).1⟩ ω)‖ ^ 2 := by
    intro k hk ω
    have hkIcc : k ∈ Finset.Icc 1 S.N := by
      simpa [outputWindow] using hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hkIcc).1
    let x : E := paperIterate S run ⟨k, hk1⟩ ω
    let G : E := paperEstimator S run ⟨k, hk1⟩ ω
    have hx : x ∈ S.X := by
      simpa [x] using
        paperIterate_mem_of_runStateSpec S (algorithmBatchStream S) run hrun_spec ⟨k, hk1⟩ ω
    have hsplit :=
      euclideanProjectedGradient_sq_le_oracle_projectedGradient_sq_add_error
        S (x := x) (G := G) hgamma_pos hx
    simpa [paperProjectedGradient, paperIterate, SOptLib.positiveTimeIterateView_eq, x, G, hkIcc,
      hk1] using hsplit
  have hdescent_projected_gradient :
      ∀ k, (hk : k ∈ outputWindow S) → ∀ ω : AlgorithmSamplePath S,
        SOptLib.finiteUniformAverage S.componentObjective (iterate S run k ω) +
            (1 / (16 * S.L)) * ‖paperProjectedGradient S run k ω‖ ^ 2 ≤
          SOptLib.finiteUniformAverage S.componentObjective
              (paperIterate S run
                ⟨k, (Finset.mem_Icc.mp (by simpa [outputWindow] using hk)).1⟩ ω) -
            (1 / (8 * S.L)) *
              ‖S.gamma⁻¹ •
                (paperIterate S run
                    ⟨k, (Finset.mem_Icc.mp (by simpa [outputWindow] using hk)).1⟩ ω -
                  iterate S run k ω)‖ ^ 2 +
            (5 / (4 * S.L)) *
              ‖paperEstimator S run
                  ⟨k, (Finset.mem_Icc.mp (by simpa [outputWindow] using hk)).1⟩ ω -
                SOptLib.finiteUniformAverage S.componentGradient
                  (paperIterate S run
                    ⟨k, (Finset.mem_Icc.mp (by simpa [outputWindow] using hk)).1⟩ ω)‖ ^ 2 +
            (3 / 2) * S.eta := by
    intro k hk ω
    have hkIcc : k ∈ Finset.Icc 1 S.N := by
      simpa [outputWindow] using hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hkIcc).1
    let x : E := paperIterate S run ⟨k, hk1⟩ ω
    let y : E := iterate S run k ω
    let delta : E := paperEstimator S run ⟨k, hk1⟩ ω - SOptLib.finiteUniformAverage S.componentGradient x
    let tildeSq : ℝ := ‖S.gamma⁻¹ • (x - y)‖ ^ 2
    let distSq : ℝ := ‖y - x‖ ^ 2
    let deltaSq : ℝ := ‖delta‖ ^ 2
    let pgSq : ℝ := ‖paperProjectedGradient S run k ω‖ ^ 2
    let p : ℝ := 1 / (16 * S.L)
    have hL_ne : S.L ≠ 0 := ne_of_gt hLpos
    have hgamma_inv_eq : S.gamma⁻¹ = S.L := by
      rw [hgamma_choice]
      exact inv_inv S.L
    have hdescent_coef :
        S.gamma⁻¹ - S.L / 2 - (S.L / 2) / 2 = S.L / 4 := by
      rw [hgamma_inv_eq]
      ring
    have hvariance_coef :
        1 / (2 * (S.L / 2)) = 1 / S.L := by
      field_simp [hL_ne]
    have htilde_dist :
        tildeSq = S.L ^ 2 * distSq := by
      simp [tildeSq, distSq, hgamma_inv_eq, norm_smul,
        Real.norm_of_nonneg (le_of_lt hLpos), norm_sub_rev]
      ring
    have hdescent_tilde :
        S.L / 4 * distSq = (1 / (4 * S.L)) * tildeSq := by
      rw [htilde_dist]
      field_simp [hL_ne]
    have hp_nonneg : 0 ≤ p := by
      simp [p]
      positivity
    have hstep_raw := hstep_descent k hk ω
    have hstep :
        SOptLib.finiteUniformAverage S.componentObjective y ≤
          SOptLib.finiteUniformAverage S.componentObjective x -
            S.L / 4 * distSq +
            (1 / S.L) * deltaSq +
            S.eta := by
      simpa [x, y, delta, deltaSq, distSq, hkIcc, hk1, hdescent_coef,
        hvariance_coef] using hstep_raw
    have hpg_raw := hprojectedGradient_three_term k hk ω
    have hpg :
        pgSq ≤ 2 * tildeSq + 8 * S.eta / S.gamma + 4 * deltaSq := by
      simpa [pgSq, tildeSq, delta, deltaSq, x, y, hkIcc, hk1] using hpg_raw
    have hpg_scaled :
        p * pgSq ≤
          p * (2 * tildeSq + 8 * S.eta / S.gamma + 4 * deltaSq) :=
      mul_le_mul_of_nonneg_left hpg hp_nonneg
    have hp_two :
        p * (2 * tildeSq) = (1 / (8 * S.L)) * tildeSq := by
      simp [p]
      ring
    have hp_eta :
        p * (8 * S.eta / S.gamma) = (1 / 2) * S.eta := by
      simp [p, hgamma_choice]
      field_simp [hL_ne]
      ring
    have hp_delta :
        p * (4 * deltaSq) = (1 / (4 * S.L)) * deltaSq := by
      simp [p]
      ring
    have hpg_scaled' :
        p * pgSq ≤
          (1 / (8 * S.L)) * tildeSq + (1 / 2) * S.eta +
            (1 / (4 * S.L)) * deltaSq := by
      calc
        p * pgSq ≤
            p * (2 * tildeSq + 8 * S.eta / S.gamma + 4 * deltaSq) := hpg_scaled
        _ =
            (1 / (8 * S.L)) * tildeSq + (1 / 2) * S.eta +
              (1 / (4 * S.L)) * deltaSq := by
          rw [mul_add, mul_add, hp_two, hp_eta, hp_delta]
    have hsum :
        SOptLib.finiteUniformAverage S.componentObjective y + p * pgSq ≤
          SOptLib.finiteUniformAverage S.componentObjective x -
            (1 / (8 * S.L)) * tildeSq +
            (5 / (4 * S.L)) * deltaSq +
            (3 / 2) * S.eta := by
      have hstep_tilde :
          SOptLib.finiteUniformAverage S.componentObjective y ≤
            SOptLib.finiteUniformAverage S.componentObjective x -
              (1 / (4 * S.L)) * tildeSq +
              (1 / S.L) * deltaSq +
              S.eta := by
        calc
          SOptLib.finiteUniformAverage S.componentObjective y ≤
              SOptLib.finiteUniformAverage S.componentObjective x -
                S.L / 4 * distSq +
                (1 / S.L) * deltaSq +
                S.eta := hstep
          _ =
              SOptLib.finiteUniformAverage S.componentObjective x -
                (1 / (4 * S.L)) * tildeSq +
                (1 / S.L) * deltaSq +
                S.eta := by
            rw [hdescent_tilde]
      have hsum_raw := add_le_add hstep_tilde hpg_scaled'
      calc
        SOptLib.finiteUniformAverage S.componentObjective y + p * pgSq
            ≤
          (SOptLib.finiteUniformAverage S.componentObjective x -
              (1 / (4 * S.L)) * tildeSq +
              (1 / S.L) * deltaSq +
              S.eta) +
            ((1 / (8 * S.L)) * tildeSq + (1 / 2) * S.eta +
              (1 / (4 * S.L)) * deltaSq) := hsum_raw
        _ =
          SOptLib.finiteUniformAverage S.componentObjective x -
            (1 / (8 * S.L)) * tildeSq +
            (5 / (4 * S.L)) * deltaSq +
            (3 / 2) * S.eta := by
          field_simp [hL_ne]
          ring
    simpa [x, y, delta, tildeSq, deltaSq, pgSq, p, hkIcc, hk1] using hsum
  have hstep_expected :=
    theorem718_integrated_one_step_projected_gradient_descent
      S run hrun_spec hdescent_projected_gradient
  let dropTerm : ℕ → ℝ := fun k =>
    ∫ ω : AlgorithmSamplePath S,
      if hk : k ∈ outputWindow S then
        SOptLib.finiteUniformAverage S.componentObjective
            (paperIterate S run
              ⟨k, (Finset.mem_Icc.mp (by simpa [outputWindow] using hk)).1⟩ ω) -
          SOptLib.finiteUniformAverage S.componentObjective (iterate S run k ω)
      else 0 ∂algorithmSampleLaw S
  let tildeTerm : ℕ → ℝ := fun k =>
    ∫ ω : AlgorithmSamplePath S,
      if hk : k ∈ outputWindow S then
        ‖S.gamma⁻¹ •
          (paperIterate S run
              ⟨k, (Finset.mem_Icc.mp (by simpa [outputWindow] using hk)).1⟩ ω -
            iterate S run k ω)‖ ^ 2
      else 0 ∂algorithmSampleLaw S
  let deltaTerm : ℕ → ℝ := fun k =>
    ∫ ω : AlgorithmSamplePath S,
      if hk : k ∈ outputWindow S then
        ‖paperEstimator S run
            ⟨k, (Finset.mem_Icc.mp (by simpa [outputWindow] using hk)).1⟩ ω -
          SOptLib.finiteUniformAverage S.componentGradient
            (paperIterate S run
              ⟨k, (Finset.mem_Icc.mp (by simpa [outputWindow] using hk)).1⟩ ω)‖ ^ 2
      else 0 ∂algorithmSampleLaw S
  let varianceTerm : ℕ → ℝ := fun k =>
    (-(1 / (8 * S.L))) * tildeTerm k + (5 / (4 * S.L)) * deltaTerm k
  let etaTerm : ℝ := (3 / 2) * S.eta
  let stepRhs : ℕ → ℝ := fun k =>
    dropTerm k + (-(1 / (8 * S.L))) * tildeTerm k + etaTerm +
      (5 / (4 * S.L)) * deltaTerm k
  have hdrop_telescope :
      Finset.sum (outputWindow S) dropTerm ≤ SOptLib.finiteUniformAverage S.componentObjective S.x₁ - fStar S := by
    simpa [dropTerm] using theorem718_expected_objective_drop_telescope S run hrun_spec
  have hvariance_absorb :
      Finset.sum (outputWindow S) varianceTerm ≤ 0 := by
    have htilde_nonneg : ∀ k ∈ outputWindow S, 0 ≤ tildeTerm k := by
      intro k hk
      dsimp [tildeTerm]
      simp [hk]
      exact integral_nonneg (fun ω => sq_nonneg _)
    have hdelta_epoch :
        ∀ s j, s ∈ Finset.Icc 0 S.N →
          j ∈ SOptLib.activeEpochSteps S.T S.N (SOptLib.global_index S.T) s →
            deltaTerm (SOptLib.global_index S.T s j) ≤
              (S.b : ℝ)⁻¹ *
                Finset.sum (Finset.Icc 2 j)
                  (fun i => tildeTerm (SOptLib.global_index S.T s (i - 1))) := by
      intro s j hs hj
      have h :=
        theorem718_deltaTerm_le_epoch_predecessor_tilde_sum
          S run hLaw hrun_spec hb_choice hgamma_choice hLpos
          tildeTerm deltaTerm rfl rfl s j hs hj
      exact h
    exact theorem718_varianceTerm_sum_nonpos_from_delta_epoch
      S tildeTerm deltaTerm varianceTerm rfl hb_choice hLpos hdelta_epoch htilde_nonneg
  have hsummed :
      Finset.sum (outputWindow S)
          (fun k => (1 / (16 * S.L)) *
            algorithmExpectedSquaredPaperProjectedGradient S run k) ≤
        Finset.sum (outputWindow S) stepRhs := by
    refine Finset.sum_le_sum ?_
    intro k hk
    have h := hstep_expected k hk
    simpa [dropTerm, tildeTerm, deltaTerm, varianceTerm, etaTerm, stepRhs, hk,
      add_assoc] using h
  have hsplit :
      Finset.sum (outputWindow S) stepRhs =
        Finset.sum (outputWindow S) dropTerm +
          Finset.sum (outputWindow S) varianceTerm +
          Finset.sum (outputWindow S) (fun _k => etaTerm) := by
    have hstepRhs_eq :
        stepRhs = fun k => dropTerm k + varianceTerm k + etaTerm := by
      funext k
      dsimp [stepRhs, varianceTerm]
      ring
    rw [hstepRhs_eq]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have heta_sum :
      Finset.sum (outputWindow S) (fun _k => etaTerm) =
        (S.N : ℝ) * etaTerm := by
    simp [outputWindow, etaTerm]
  have hscaled_sum :
      Finset.sum (outputWindow S)
          (fun k => (1 / (16 * S.L)) *
            algorithmExpectedSquaredPaperProjectedGradient S run k) ≤
        SOptLib.finiteUniformAverage S.componentObjective S.x₁ - fStar S + (S.N : ℝ) * etaTerm := by
    calc
      Finset.sum (outputWindow S)
          (fun k => (1 / (16 * S.L)) *
            algorithmExpectedSquaredPaperProjectedGradient S run k)
          ≤ Finset.sum (outputWindow S) stepRhs := hsummed
      _ =
          Finset.sum (outputWindow S) dropTerm +
            Finset.sum (outputWindow S) varianceTerm +
            Finset.sum (outputWindow S) (fun _k => etaTerm) := hsplit
      _ ≤
          (SOptLib.finiteUniformAverage S.componentObjective S.x₁ - fStar S) + 0 +
            Finset.sum (outputWindow S) (fun _k => etaTerm) := by
        exact add_le_add (add_le_add hdrop_telescope hvariance_absorb) le_rfl
      _ = SOptLib.finiteUniformAverage S.componentObjective S.x₁ - fStar S + (S.N : ℝ) * etaTerm := by
        rw [heta_sum]
        ring
  calc
    (1 / (16 * S.L)) *
        Finset.sum (outputWindow S)
          (fun k => algorithmExpectedSquaredPaperProjectedGradient S run k)
        =
      Finset.sum (outputWindow S)
        (fun k => (1 / (16 * S.L)) *
          algorithmExpectedSquaredPaperProjectedGradient S run k) := by
      rw [Finset.mul_sum]
    _ ≤ SOptLib.finiteUniformAverage S.componentObjective S.x₁ - fStar S + (S.N : ℝ) * etaTerm := hscaled_sum
    _ = SOptLib.finiteUniformAverage S.componentObjective S.x₁ - fStar S +
        (3 / 2) * (S.N : ℝ) * S.eta := by
      simp [etaTerm]
      ring

/-- Raw unweighted summed projected-gradient bound from Theorem 7.18 before
division by `N`.

This is the source bridge for the printed summation after Eq. (7.5.13): it
aligns with Lan Theorem 7.18 proof lines deriving
`E[f(x_{N+1})] + (16L)^{-1} sum E[||g_X,k||^2] <= f(x_1) + 3/2 sum eta_k`.
Candidates considered: `finset_weighted_variance_eq_second_moment_sub_norm_mean_sq`
and `Finset.weighted_variance_le_second_moment` match the component variance
algebra, `sum_scaled_l2_error_le_epoch_budget_add_variance_floor` matches a
related nested residual aggregation, and
`finite_window_weighted_recurrence_telescope_with_tail_sums` /
`sum_Icc_two_coeff_telescope_le` match scalar telescoping patterns; none by
itself carries this file's `runStateSpec`, CndG projected-gradient comparison,
and Algorithm 7.12 iid estimator recursion needed for the literal Eq. (7.5.13)
global projected-gradient sum. -/
private theorem theorem718_specialized_global_sum_bound (S : Setup E)
    (run : ℕ → AlgorithmSamplePath S → RunState E)
    (hrun : runStateSpec S (algorithmBatchStream S) run) :
    Finset.sum (outputWindow S)
        (fun k => algorithmExpectedSquaredPaperProjectedGradient S run k) ≤
      16 * S.L * (SOptLib.finiteUniformAverage S.componentObjective S.x₁ - fStar S) +
        24 * S.L * (S.N : ℝ) * S.eta := by
  classical
  have hLpos : 0 < S.L := averageSmoothness_pos S
  have hcoef_pos : 0 < 16 * S.L := by nlinarith
  have hcoef_ne : 16 * S.L ≠ 0 := ne_of_gt hcoef_pos
  have h7513 := theorem718_global_summed_7513_lowered S run hrun
  have hscaled := mul_le_mul_of_nonneg_left h7513 (le_of_lt hcoef_pos)
  calc
    Finset.sum (outputWindow S)
        (fun k => algorithmExpectedSquaredPaperProjectedGradient S run k)
        =
      (16 * S.L) *
        ((1 / (16 * S.L)) *
          Finset.sum (outputWindow S)
            (fun k => algorithmExpectedSquaredPaperProjectedGradient S run k)) := by
      field_simp [hcoef_ne]
    _ ≤
      (16 * S.L) *
        (SOptLib.finiteUniformAverage S.componentObjective S.x₁ - fStar S +
          (3 / 2) * (S.N : ℝ) * S.eta) := hscaled
    _ =
      16 * S.L * (SOptLib.finiteUniformAverage S.componentObjective S.x₁ - fStar S) +
        24 * S.L * (S.N : ℝ) * S.eta := by
      ring

/-- Source-proof aggregate obtained by summing Eq. (7.5.13).

This is the unweighted average appearing directly after the summation step in
the printed proof, kept separate from the alpha-weighted Algorithm 7.12 random
output object. -/
theorem theorem718AverageSquaredProjectedGradient_bound (S : Setup E)
    (run : ℕ → AlgorithmSamplePath S → RunState E)
    (hrun : runStateSpec S (algorithmBatchStream S) run) :
    theorem718AverageSquaredProjectedGradient S run ≤
      (16 * S.L / (S.N : ℝ)) * (SOptLib.finiteUniformAverage S.componentObjective S.x₁ - fStar S) +
        24 * S.L * S.eta := by
  classical
  have hNposR : 0 < (S.N : ℝ) := Nat.cast_pos.mpr S.hN_pos
  have hN_ne : (S.N : ℝ) ≠ 0 := ne_of_gt hNposR
  have hsum :
      Finset.sum (outputWindow S)
          (fun k => algorithmExpectedSquaredPaperProjectedGradient S run k) ≤
        16 * S.L * (SOptLib.finiteUniformAverage S.componentObjective S.x₁ - fStar S) +
          24 * S.L * (S.N : ℝ) * S.eta :=
    theorem718_specialized_global_sum_bound S run hrun
  unfold theorem718AverageSquaredProjectedGradient
  have hscaled := mul_le_mul_of_nonneg_left hsum (le_of_lt (inv_pos.mpr hNposR))
  calc
    (S.N : ℝ)⁻¹ *
        Finset.sum (outputWindow S)
          (fun k => algorithmExpectedSquaredPaperProjectedGradient S run k)
        ≤
      (S.N : ℝ)⁻¹ *
        (16 * S.L * (SOptLib.finiteUniformAverage S.componentObjective S.x₁ - fStar S) +
          24 * S.L * (S.N : ℝ) * S.eta) := hscaled
    _ =
      (16 * S.L / (S.N : ℝ)) * (SOptLib.finiteUniformAverage S.componentObjective S.x₁ - fStar S) +
        24 * S.L * S.eta := by
      field_simp [hN_ne]

/-- Internal proof-supported unweighted aggregate from the Theorem 7.18 proof,
Eq. (7.5.13) summed over `k = 1, ..., N`.

This helper records the summed inequality that the proof uses before invoking
`R`.  It remains the corrected/source-boundary object for the printed proof
aggregate; the alpha-weighted random-output bridge is kept as separate proof
debt and is not exported under the original paper theorem name. -/
theorem theorem718UnweightedProjectedGradientBound (S : Setup E)
    (run : ℕ → AlgorithmSamplePath S → RunState E)
    (hrun : runStateSpec S (algorithmBatchStream S) run) :
    theorem718AverageSquaredProjectedGradient S run ≤
      (16 * S.L / (S.N : ℝ)) * (SOptLib.finiteUniformAverage S.componentObjective S.x₁ - fStar S) +
        24 * S.L * S.eta := by
  exact theorem718AverageSquaredProjectedGradient_bound S run hrun

/-- Expansion of the corrected uniform selected-output expectation into the
proof-supported unweighted Theorem 7.18 aggregate. -/
private theorem expectedUniformRandomOutputSquaredPaperProjectedGradient_eq_average
    (S : Setup E) (hη : 0 < S.eta) :
    expectedUniformRandomOutputSquaredPaperProjectedGradient S hη =
      theorem718AverageSquaredProjectedGradient S (algorithmRunOfEtaPos S hη) := by
  classical
  let run : ℕ → AlgorithmSamplePath S → RunState E := algorithmRunOfEtaPos S hη
  have hrun : runStateSpec S (algorithmBatchStream S) run := by
    simpa [run] using algorithmRunOfEtaPos_spec S hη
  have hden :
      0 < Finset.sum (outputWindow S) (fun _ : ℕ => (1 : ℝ)) := by
    have hNpos : 0 < (S.N : ℝ) := Nat.cast_pos.mpr S.hN_pos
    simpa [outputWindow, Nat.succ_le_iff, S.hN_pos] using hNpos
  have hsum :
      Finset.sum (outputWindow S) (fun _ : ℕ => (1 : ℝ)) = (S.N : ℝ) := by
    simp [outputWindow, Nat.succ_le_iff, S.hN_pos]
  have hgap_int :
      ∀ R : {k : ℕ // k ∈ outputWindow S},
        Integrable
          (fun ω : AlgorithmSamplePath S =>
            (fun g : E => ‖g‖ ^ 2) (paperProjectedGradient S run R.1 ω))
          (algorithmSampleLaw S) := by
    intro R
    exact (theorem718_finite_prefix_observable_integrability S run hrun R.1 R.2).1
  haveI : IsProbabilityMeasure (algorithmSampleLaw S) :=
    (algorithmSampleLaw_spec S).1
  haveI : SFinite (algorithmSampleLaw S) := inferInstance
  have hexpand :=
    SOptLib.finiteWindowSelectedOutputExpectation_eq_weighted_sum
      (times := outputWindow S) (α := fun _ : ℕ => (1 : ℝ))
      (P := algorithmSampleLaw S)
      (x := fun k (ω : AlgorithmSamplePath S) => paperProjectedGradient S run k ω)
      (gap := fun g : E => ‖g‖ ^ 2)
      (by intro k hk; norm_num) hden hgap_int
  calc
    expectedUniformRandomOutputSquaredPaperProjectedGradient S hη
        =
      (S.N : ℝ)⁻¹ *
        Finset.sum (outputWindow S)
          (fun k => algorithmExpectedSquaredPaperProjectedGradient S run k) := by
        simpa [expectedUniformRandomOutputSquaredPaperProjectedGradient,
          uniformRandomOutputLaw, uniformOutputIndexPMF, SOptLib.selected_joint_measure,
          algorithmExpectedSquaredPaperProjectedGradient,
          expectedSquaredPaperProjectedGradient, run, hsum] using hexpand
    _ = theorem718AverageSquaredProjectedGradient S run := by
        rfl

/-- Corrected B-track Theorem 7.18 endpoint for the generated Algorithm 7.12
run under the canonical uniform selected-output law. -/
theorem theorem718UniformRandomOutputSquaredProjectedGradient_bound
    (S : Setup E) (hη : 0 < S.eta) :
    expectedUniformRandomOutputSquaredPaperProjectedGradient S hη ≤
      (16 * S.L / (S.N : ℝ)) * (SOptLib.finiteUniformAverage S.componentObjective S.x₁ - fStar S) +
        24 * S.L * S.eta := by
  have hrun : runStateSpec S (algorithmBatchStream S) (algorithmRunOfEtaPos S hη) :=
    algorithmRunOfEtaPos_spec S hη
  rw [expectedUniformRandomOutputSquaredPaperProjectedGradient_eq_average S hη]
  exact theorem718AverageSquaredProjectedGradient_bound S (algorithmRunOfEtaPos S hη) hrun

/-- Source-boundary obligation for connecting the proof's unweighted aggregate
to Algorithm 7.12's alpha-randomized output.

The PDF proof invokes the definition of `R`, but the displayed output law uses
`alpha_k / sum alpha_k`, while the preceding proof aggregate is unweighted.
This declaration is deliberately a `Prop`, not a theorem: the bridge is not
available as an established fact until Phase 2 proves it from source-backed
objects or records the corrected boundary. -/
private def theorem718RandomOutputBridgeObligation
    (S : Setup E) (run : ℕ → AlgorithmSamplePath S → RunState E)
    (p : PMF {k : ℕ // k ∈ outputWindow S}) : Prop :=
  runStateSpec S (algorithmBatchStream S) run →
    outputIndexLawSpec S p →
      theorem718AverageSquaredProjectedGradient S run ≤
        (16 * S.L / (S.N : ℝ)) * (SOptLib.finiteUniformAverage S.componentObjective S.x₁ - fStar S) +
          24 * S.L * S.eta →
      paperExpectedRandomOutputSquaredProjectedGradient S run p ≤
        (16 * S.L / (S.N : ℝ)) * (SOptLib.finiteUniformAverage S.componentObjective S.x₁ - fStar S) +
          24 * S.L * S.eta

/-- The accuracy target for Corollary 7.13's proof choice `eta = epsilon/(48L)`. -/
def corollaryAccuracy (S : Setup E) (epsilon : ℝ) : ℝ :=
  epsilon / (48 * S.L)

/-- The Corollary 7.13 accuracy choice is strictly positive when `epsilon > 0`.

This is derived from the source-backed positivity of `L` and the displayed
choice `eta = epsilon/(48L)`, not assumed in the corollary theorem head. -/
theorem corollaryAccuracy_pos (S : Setup E) {epsilon : ℝ}
    (hε : 0 < epsilon) (hη : S.eta = corollaryAccuracy S epsilon) :
    0 < S.eta := by
  rw [hη, corollaryAccuracy]
  have hL_pos : 0 < S.L := averageSmoothness_pos S
  have hden_pos : 0 < 48 * S.L := by
    exact mul_pos (by norm_num) hL_pos
  exact div_pos hε hden_pos

/-- Corollary 7.13's epoch choice `T = sqrt(m)`.

No SOptLib match: searched the precomputed CorollaryTChoice candidates and
scanned `SOptLib/Model/Complexity.lean` / `SOptLib/Layer1/Complexity.lean`;
those primitives cover two-phase call accounting, while Corollary 7.13 uses this
literal one-run finite-sum epoch choice. -/
def corollaryEpochChoice (S : Setup E) : Prop :=
  (S.T : ℝ) = Real.sqrt (S.componentCount : ℝ)

/-- Corollary 7.13's iteration budget from the proof:
`N = ceil(32 L [f(x_1)-f^*] / epsilon)`.

No SOptLib match: searched the precomputed main-theorem complexity candidates
and scanned `SOptLib/Model/Complexity.lean` / `SOptLib/Layer1/Complexity.lean`;
available selectors are for two-phase stochastic schemes, not this displayed
single-run Theorem 7.18 budget. -/
def corollaryIterationBudget (S : Setup E) (epsilon : ℝ) : ℕ :=
  Nat.ceil ((32 * S.L * (SOptLib.finiteUniformAverage S.componentObjective S.x₁ - fStar S)) / epsilon)

/-- Source-facing statement that the run uses the Corollary 7.13 iteration
budget. -/
def usesCorollaryIterationBudget (S : Setup E) (epsilon : ℝ) : Prop :=
  S.N = corollaryIterationBudget S epsilon

/-- The paper epsilon criterion from Corollary 7.13.

The paper states a solution `xbar in X` with expected projected-gradient norm at
most `epsilon`.  The conclusion therefore exhibits a generated run and an output
law satisfying the displayed Algorithm 7.12 distribution, rather than using an
unconditional run or arbitrary-alpha PMF. -/
private def findsEpsilonProjectedGradientSolution (S : Setup E) (epsilon : ℝ) : Prop :=
  ∃ run : ℕ → AlgorithmSamplePath S → RunState E,
    runStateSpec S (algorithmBatchStream S) run ∧
      ∃ p : PMF {k : ℕ // k ∈ outputWindow S},
        outputIndexLawSpec S p ∧
          (∀ q : {k : ℕ // k ∈ outputWindow S} × AlgorithmSamplePath S,
            randomOutput S run q ∈ S.X) ∧
          paperExpectedRandomOutputProjectedGradientNorm S run p ≤ epsilon

/-- Number of stochastic-gradient evaluations counted in Corollary 7.13:
`(m + bT) ceil(N/T)`.

This specializes the staged single-phase epoch call-count primitive to the
paper's finite-sum refresh and recursive mini-batch schedule. -/
def stochasticGradientCallCount (S : Setup E) : ℕ :=
  SOptLib.singlePhaseEpochCallCount S.componentCount S.b S.T S.N

/-- Per-iteration linear-optimization oracle call ceiling from the proof of
Corollary 7.13, `ceil(6 Dbar_X^2/(gamma eta))`.

This specializes SOptLib's conditional-gradient inner-loop ceiling-budget
concept to the paper's `beta = 1/gamma` CndG call in Eq. (7.5.5). -/
def linearOracleCallsPerIteration (S : Setup E) : ℕ :=
  Nat.ceil ((6 * DbarX S ^ 2) / (S.gamma * S.eta))

/-- Total linear-optimization oracle calls from Corollary 7.13:
`N ceil(6 Dbar_X^2/(gamma eta))`. -/
def linearOracleCallCount (S : Setup E) : ℕ :=
  S.N * linearOracleCallsPerIteration S

/-- Concrete stochastic-gradient call budget used in Corollary 7.13's proof:
`11m(N/sqrt(m)+1)` with `N` specialized to the displayed iteration budget.

No SOptLib match: `SOptLib.Model.Complexity` and `SOptLib.Layer1.Complexity`
provide two-phase and logarithmic-rate accounting helpers, but not the finite-sum
epoch count `(m+bT) ceil(N/T) <= 11m(N/sqrt(m)+1)` from this corollary. -/
def corollaryStochasticGradientCallBudget (S : Setup E) (epsilon : ℝ) : ℝ :=
  11 * (S.componentCount : ℝ) *
    ((corollaryIterationBudget S epsilon : ℝ) /
      Real.sqrt (S.componentCount : ℝ) + 1)

/-- Concrete linear-oracle call budget used in Corollary 7.13's proof:
`N ceil(6 Dbar_X^2/(gamma eta))`, with `N` specialized to the displayed
iteration budget.

No SOptLib match: `SOptLib.Model.ConditionalGradient` has the inner-loop ceiling
shape, but the corollary's total one-run product with the Theorem 7.18 iteration
budget is paper-local. -/
def corollaryLinearOracleCallBudget (S : Setup E) (epsilon : ℝ) : ℝ :=
  (corollaryIterationBudget S epsilon : ℝ) *
    (Nat.ceil ((6 * DbarX S ^ 2) / (S.gamma * S.eta)) : ℝ)

/-- Displayed stochastic-gradient rate from Eq. (7.5.14), without hiding it
behind a per-instance existential big-O envelope. -/
def corollaryStochasticGradientDisplayedRate (S : Setup E) (epsilon : ℝ) : ℝ :=
  (S.componentCount : ℝ) +
    Real.sqrt (S.componentCount : ℝ) *
      S.L * (SOptLib.finiteUniformAverage S.componentObjective S.x₁ - fStar S) / epsilon

/-- Displayed linear-oracle rate from Eq. (7.5.15), without hiding it behind a
per-instance existential big-O envelope. -/
def corollaryLinearOracleDisplayedRate (S : Setup E) (epsilon : ℝ) : ℝ :=
  S.L ^ 3 * DbarX S ^ 2 *
    (SOptLib.finiteUniformAverage S.componentObjective S.x₁ - fStar S) / epsilon ^ 2

/-- Corollary 7.13's proof-supported concrete complexity claim.

The paper advertises the final call-count rates with big-O notation in
Eqs. (7.5.14)-(7.5.15).  This source-boundary proposition records the concrete
raw budgets derived immediately before that asymptotic conversion, avoiding
false pointwise constants for the big-O display. -/
private def corollaryDisplayedComplexityStatement (S : Setup E) (epsilon : ℝ) : Prop :=
  findsEpsilonProjectedGradientSolution S epsilon ∧
    (stochasticGradientCallCount S : ℝ) ≤
      corollaryStochasticGradientCallBudget S epsilon ∧
    (linearOracleCallCount S : ℝ) ≤
      corollaryLinearOracleCallBudget S epsilon

/-- The call-count part of Corollary 7.13, separated from the random-output
solution criterion.

The PDF proof contains explicit arithmetic for the SFO and LO counts after
invoking Theorem 7.18.  This statement records only those count inequalities and
does not assert either the alpha-randomized output criterion or a pointwise
constant for the final big-O display. -/
def corollaryDisplayedCallCountStatement (S : Setup E) (epsilon : ℝ) : Prop :=
  (stochasticGradientCallCount S : ℝ) ≤
    corollaryStochasticGradientCallBudget S epsilon ∧
  (linearOracleCallCount S : ℝ) ≤
    corollaryLinearOracleCallBudget S epsilon

/-- Internal call-count theorem for Corollary 7.13's raw proof budgets.

This is not the original paper corollary: the solution-existence/random-output
part remains blocked by the Theorem 7.18 alpha-output boundary. -/
theorem corollary713CallCounts_internal
    (S : Setup E) (epsilon : ℝ)
    (_hε : 0 < epsilon)
    (_hT : corollaryEpochChoice S)
    (_hη : S.eta = corollaryAccuracy S epsilon)
    (_hN : usesCorollaryIterationBudget S epsilon) :
    corollaryDisplayedCallCountStatement S epsilon := by
  constructor
  · unfold stochasticGradientCallCount
    unfold corollaryStochasticGradientCallBudget
    unfold usesCorollaryIterationBudget at _hN
    unfold corollaryEpochChoice at _hT
    rw [_hN, S.hb_eq_ten_mul_T]
    have hT_sq : (S.T : ℝ) ^ 2 = (S.componentCount : ℝ) := by
      calc
        (S.T : ℝ) ^ 2 = (Real.sqrt (S.componentCount : ℝ)) ^ 2 := by rw [_hT]
        _ = (S.componentCount : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
    have hbound :=
      SOptLib.epoch_call_count_le_sqrt_bound_of_epoch_sq_eq_refresh
        (corollaryIterationBudget S epsilon) S.componentCount S.T 10 hT_sq
    norm_num at hbound
    simpa using hbound
  · unfold linearOracleCallCount
    unfold corollaryLinearOracleCallBudget linearOracleCallsPerIteration
    unfold usesCorollaryIterationBudget at _hN
    rw [_hN, Nat.cast_mul]

/-- Corrected B-track Corollary 7.13 endpoint.

This combines the proof-supported uniform selected-output squared
`paperProjectedGradient` certificate for the generated positive-eta Algorithm
7.12 run with the established raw call-count theorem. -/
theorem corollary713UniformOutputComplexity
    (S : Setup E) (epsilon : ℝ)
    (hε : 0 < epsilon)
    (hη : S.eta = corollaryAccuracy S epsilon)
    (hT : corollaryEpochChoice S)
    (hN : usesCorollaryIterationBudget S epsilon) :
    expectedUniformRandomOutputSquaredPaperProjectedGradient S
        (corollaryAccuracy_pos S hε hη) ≤ epsilon ∧
      corollaryDisplayedCallCountStatement S epsilon := by
  classical
  let A : ℝ := SOptLib.finiteUniformAverage S.componentObjective S.x₁ - fStar S
  have hLpos : 0 < S.L := averageSmoothness_pos S
  have hNpos : 0 < (S.N : ℝ) := Nat.cast_pos.mpr S.hN_pos
  have hA_nonneg : 0 ≤ A := by
    have hmin := (finiteSumMinimizer_spec S).2 S.x₁ S.hx₁_mem
    exact sub_nonneg.mpr hmin
  have hceil :
      (32 * S.L * A) / epsilon ≤ (S.N : ℝ) := by
    unfold usesCorollaryIterationBudget at hN
    rw [hN, corollaryIterationBudget]
    exact Nat.le_ceil ((32 * S.L * A) / epsilon)
  have hbudget : 32 * S.L * A ≤ (S.N : ℝ) * epsilon := by
    have hmul := mul_le_mul_of_nonneg_right hceil (le_of_lt hε)
    have hleft : ((32 * S.L * A) / epsilon) * epsilon = 32 * S.L * A := by
      field_simp [ne_of_gt hε]
    nlinarith
  have hfirst :
      (16 * S.L / (S.N : ℝ)) * A ≤ epsilon / 2 := by
    have hdiv : (16 * S.L * A) / (S.N : ℝ) ≤ epsilon / 2 := by
      rw [div_le_iff₀ hNpos]
      nlinarith
    have heq : (16 * S.L / (S.N : ℝ)) * A =
        (16 * S.L * A) / (S.N : ℝ) := by
      ring
    simpa [heq]
  have hsecond :
      24 * S.L * S.eta = epsilon / 2 := by
    rw [hη, corollaryAccuracy]
    field_simp [ne_of_gt hLpos]
    ring
  have huniform :=
    theorem718UniformRandomOutputSquaredProjectedGradient_bound
      S (corollaryAccuracy_pos S hε hη)
  have hrhs :
      (16 * S.L / (S.N : ℝ)) * A + 24 * S.L * S.eta ≤ epsilon := by
    rw [hsecond]
    nlinarith
  refine ⟨?_, corollary713CallCounts_internal S epsilon hε hT hη hN⟩
  exact le_trans (by simpa [A] using huniform) hrhs

/-- Source-boundary obligation for the full Corollary 7.13 solution claim.

The displayed corollary asks for a randomized output solution satisfying the
expected projected-gradient criterion.  Because the source proof relies on
Theorem 7.18's unresolved alpha-random-output bridge, this full statement is
kept as an obligation rather than an asserted internal theorem. -/
private def corollary713FullComplexityBoundaryObligation
    (S : Setup E) (epsilon : ℝ) : Prop :=
  corollaryDisplayedComplexityStatement S epsilon

end

end Algorithms.Unverified.StochasticNonconvexCGSliding
