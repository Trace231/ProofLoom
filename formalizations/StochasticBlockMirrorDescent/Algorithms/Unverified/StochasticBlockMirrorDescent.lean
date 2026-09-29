import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Process.Adapted
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import SOptLib.Model.Bregman
import SOptLib.Model.BlockSampling
import SOptLib.Model.Carrier
import SOptLib.Model.Filtration
import SOptLib.Model.Iterates
import SOptLib.Model.Norms
import SOptLib.Model.Objective
import SOptLib.Model.Prox
import SOptLib.Model.StochasticOracle
import SOptLib.Model.Subdifferential
import SOptLib.Glue.Algebra
import SOptLib.Glue.Analysis
import SOptLib.Glue.Calculus
import SOptLib.Glue.Probability
import SOptLib.Layer0.ConvexFOC
import SOptLib.Layer0.Oracle
import SOptLib.Layer0.Subgradient
import SOptLib.Layer1.Descent
import SOptLib.Layer1.Proximal
import SOptLib.Layer1.Telescope

/-!
# Stochastic Block Mirror Descent

Statement-only formalization of stochastic block mirror descent for nonsmooth
convex stochastic optimization, following Section 4.6 of Lan's
*First-Order and Stochastic Optimization Methods for Machine Learning*.

The file packages the stochastic objective, block decomposition, blockwise
Bregman geometry, sampling law, oracle assumptions, and the canonical one-block
prox update into `StochasticBlockMirrorDescentSetup`. It then defines the
recursive stochastic process together with the full lemma chain and the final
expected convergence theorem from the JSON specification.
-/

open MeasureTheory ProbabilityTheory SOptLib
open scoped InnerProductSpace
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι]
variable {S : Type*} [MeasurableSpace S]
variable {Ω : Type*} [MeasurableSpace Ω]



/-- Canonical sample path for Algorithm 4.5: at each time the product stream
returns the stochastic-oracle sample and sampled block index.

No SOptLib match: searched "sample prefix filtration independent current iid
sample process" and checked `SOptLib.filtration`; SOptLib supplies the
generated-filtration reused below, but not this paper's same-time `(ξ_k, i_k)`
product-coordinate stream. -/
abbrev StochasticBlockSamplePath (S ι : Type*) :=
  blockSamplePath S ι

/-- Finite block-sampling PMF from the probabilities `p_i` in Eq. (4.6.12).

Mathlib `PMF.ofFintype` was selected after checking finite probability-measure
candidates: it is the canonical finite distribution constructor for the paper's
law `Prob {i_k = i} = p_i`; the proof that `∑ᵢ ENNReal.ofReal (p_i) = 1` is
left to the prover from `p_i ≥ 0` and `∑ᵢ p_i = 1`. -/
noncomputable def finiteBlockSamplingPMF
    {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (hp_nonneg : ∀ i, 0 ≤ p i) (hp_sum : Finset.sum Finset.univ p = 1) : PMF ι :=
  PMF.ofFintypeOfReal p hp_nonneg hp_sum

/-- Finite block-index sampling law induced by Eq. (4.6.12). -/
noncomputable def finiteBlockSamplingLaw
    {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] (p : ι → ℝ)
    (hp_nonneg : ∀ i, 0 ≤ p i) (hp_sum : Finset.sum Finset.univ p = 1) : Measure ι :=
  (finiteBlockSamplingPMF p hp_nonneg hp_sum).toMeasure

/-- Singleton probability form of the finite block-index law in Eq. (4.6.12). -/
theorem finiteBlockSamplingLaw_singleton
    {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (p : ι → ℝ) (hp_nonneg : ∀ i, 0 ≤ p i)
    (hp_sum : Finset.sum Finset.univ p = 1) (i : ι) :
    finiteBlockSamplingLaw p hp_nonneg hp_sum ({i} : Set ι) = ENNReal.ofReal (p i) := by
  simpa [finiteBlockSamplingLaw, finiteBlockSamplingPMF] using
    (PMF.toMeasure_apply_singleton
      (finiteBlockSamplingPMF p hp_nonneg hp_sum) i (measurableSet_singleton i))

/-- State of the stochastic block mirror-descent recursion. -/
abbrev StochasticBlockMirrorDescentState (ι : Type*) (E : Type*) (Block : ι → Type*) : Type _ :=
  BlockIterateState ι E Block

/-- Strong convexity with respect to an explicitly supplied norm.

No SOptLib match: searched "seminorm norm dual norm strong convex", checked the
top hits `SOptLib.bregman_lower_bound_of_strongConvexOn_hasFDerivWithinAt` and
Mathlib `StrongConvexOn`; these use the ambient typeclass norm, while Lan
Eq. (4.6.7) states strong convexity with respect to the paper object
`‖·‖_i`. -/
def StrongConvexOnWithNorm
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (s : Set B) (μ : ℝ) (norm : B → ℝ) (f : B → ℝ) : Prop :=
  StrongConvexOnWithGauge s μ norm f

/-- Separation property turning a Mathlib seminorm into the paper's genuine
norm object.

No SOptLib match: searched "dual norm seminorm support function" and
"Seminorm dual", checked `SOptLib/Model/Norms.lean`,
`SOptLib/Model/Iterates.lean`, and `SOptLib/Layer0/Oracle.lean`; SOptLib only
has abstract `normDual : E → ℝ` parameters or a placeholder Norms file, while
Lan Eq. (4.6.7) requires an actual block norm `‖·‖_i` whose unit ball defines
the dual norm. -/
def IsPaperNorm {B : Type*} [AddCommGroup B] [Module ℝ B] (p : Seminorm ℝ B) : Prop :=
  Seminorm.IsSeparating p

/-- Canonical dual norm `‖ζ‖_* = sup { |⟪ζ,d⟫| : ‖d‖ ≤ 1 }` associated with
the primal norm in Lemma 4.3 and Eq. (4.6.4).

No SOptLib match: searched "dual norm seminorm support function", "Seminorm
dual", and "support function norm inner product", checked
`SOptLib/Model/Norms.lean`, `SOptLib/Model/Iterates.lean`, and
`SOptLib/Layer0/Oracle.lean`; existing candidates expose abstract
`normDual : E → ℝ` witnesses rather than deriving the dual from the primal
unit ball required by the paper's `‖·‖_{i,*}` notation. -/
noncomputable def canonicalDualNormFromPrimal
    {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℝ B]
    (p : Seminorm ℝ B) (ζ : B) : ℝ :=
  SOptLib.canonicalDualNorm p ζ


/-- Finite-dimensional seminorms are bounded above by the ambient norm.

This is the coordinate bridge for Lan's finite Euclidean block spaces: after
checking the pre-searched candidates `dualNorm`, `weightedExpectedExactStationarity`,
`validation_query_variance_bound`, and `integrable_map_measure_of_integrable_comp`,
none matched this finite-coordinate seminorm-continuity obligation, while
`LinearMap.continuous_of_finiteDimensional` and coordinate bounds give the
needed local Mathlib route. -/
private theorem seminorm_upper_bound_by_ambient_norm_of_finite_dimensional
    {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℝ B]
    [FiniteDimensional ℝ B]
    (p : Seminorm ℝ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : B, p x ≤ K * ‖x‖ := by
  classical
  let b := Module.finBasis ℝ B
  have hcoord :
      ∀ i, ∃ C : ℝ, 0 < C ∧ ∀ x : B, |b.equivFun x i| ≤ C * ‖x‖ := by
    intro i
    rcases Module.Basis.exists_norm_coord_le_mul_norm_of_finiteDimensional b i with
      ⟨C, hCpos, hC⟩
    refine ⟨C, hCpos, ?_⟩
    intro x
    simpa [Real.norm_eq_abs] using hC x
  choose C hCpos hCbound using hcoord
  refine ⟨∑ i, C i * p (b i), ?_, ?_⟩
  · exact Finset.sum_nonneg (fun i _ =>
      mul_nonneg (le_of_lt (hCpos i)) (apply_nonneg p (b i)))
  · intro x
    have hsum :
        p (∑ i, b.equivFun x i • b i) ≤
          ∑ i, p (b.equivFun x i • b i) := by
      refine Finset.induction_on Finset.univ ?_ ?_
      · simp
      · intro a s ha ih
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        exact (map_add_le_add p _ _).trans (add_le_add le_rfl ih)
    have hterms :
        (∑ i, p (b.equivFun x i • b i)) ≤
          ∑ i, (C i * ‖x‖) * p (b i) := by
      refine Finset.sum_le_sum ?_
      intro i _
      have hi := hCbound i x
      have hmul := mul_le_mul_of_nonneg_right hi (apply_nonneg p (b i))
      simpa [map_smul_eq_mul, mul_assoc] using hmul
    calc
      p x = p (∑ i, b.equivFun x i • b i) := by rw [b.sum_equivFun x]
      _ ≤ ∑ i, p (b.equivFun x i • b i) := hsum
      _ ≤ ∑ i, (C i * ‖x‖) * p (b i) := hterms
      _ = (∑ i, C i * p (b i)) * ‖x‖ := by
        simp_rw [mul_assoc, mul_comm ‖x‖, ← mul_assoc]
        rw [Finset.sum_mul]

/-- A separating paper seminorm has a positive minimum on the ambient unit sphere.

This aligns with Lan Eq. (4.6.4)/(4.6.7): on a finite-dimensional Euclidean
block, continuity of the paper seminorm and separation rule out zero on the
compact unit sphere. SOptLib's compact continuous-bound helper was considered,
but the needed conclusion is a strictly positive minimum, not merely an
absolute upper bound. -/
private theorem paper_norm_positive_on_unit_sphere
    {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℝ B]
    [FiniteDimensional ℝ B]
    (p : Seminorm ℝ B) (hp : IsPaperNorm p) (hcont : Continuous p)
    [Nontrivial B] :
    ∃ c : ℝ, 0 < c ∧ ∀ y : B, ‖y‖ = 1 → c ≤ p y := by
  classical
  haveI : ProperSpace B := FiniteDimensional.proper ℝ B
  exact Seminorm.exists_pos_le_on_unit_sphere_of_separating p hp hcont.continuousOn

/-- A separating paper seminorm controls the ambient finite-dimensional norm.

This is the finite-dimensional norm-equivalence bridge needed to make the
paper dual unit-ball support function a real supremum. SOptLib candidates
`dualNorm`, `dualNorm_eq_norm`, `exists_nonneg_norm_bound_of_isCompact_of_continuousOn`,
and the pre-searched mirror-descent update lemmas were considered; none match,
because they either use the ambient Riesz norm, give only upper bounds for
continuous functions on already compact sets, or concern prox updates rather
than deriving ambient norm control from the literal separating seminorm in
Lan Eq. (4.6.4). -/
private theorem paper_norm_controls_ambient_norm
    {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℝ B]
    [FiniteDimensional ℝ B]
    (p : Seminorm ℝ B) (hp : IsPaperNorm p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : B, ‖x‖ ≤ C * p x := by
  exact Seminorm.exists_norm_le_mul_self_of_finiteDimensional_separating p hp

/-- The support set defining the canonical paper dual norm is bounded above.

This aligns with Lan Eq. (4.6.4): after the local finite-dimensional norm
control above, the primal unit ball is ambient-bounded, so Cauchy-Schwarz
bounds all support values. SOptLib's compact continuous-bound helper was
considered, but the set here is a seminorm unit ball rather than a pre-existing
compact carrier; the required compactness is supplied through
`paper_norm_controls_ambient_norm`. -/
private theorem canonical_dual_support_set_bddAbove
    {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℝ B]
    [FiniteDimensional ℝ B]
    (p : Seminorm ℝ B) (hp : IsPaperNorm p) (ζ : B) :
    BddAbove {r : ℝ | ∃ u : B, p u ≤ 1 ∧ r = |⟪ζ, u⟫_ℝ|} := by
  rcases paper_norm_controls_ambient_norm p hp with ⟨C, hC0, hC⟩
  refine SOptLib.canonicalDualNorm_supportSet_bddAbove p ζ ⟨C, ?_⟩
  intro x hx
  calc
    ‖x‖ ≤ C * p x := hC x
    _ ≤ C * 1 := mul_le_mul_of_nonneg_left hx hC0
    _ = C := by simp

/-- Cauchy support inequality derived from the canonical primal/dual norm pair.

This is the object-layer bridge used by Lemma 4.3: the dual norm is not an
independent hypothesis but the support function of the primal unit ball. The
finite-dimensional hypothesis is part of the source block model
`X_i ⊆ ℝ^{n_i}` in Eq. (4.6.2); it supplies the boundedness/compactness bridge
needed for the real-valued support supremum. -/
theorem abs_inner_le_canonicalDualNorm_mul_primal
    {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℝ B]
    [FiniteDimensional ℝ B]
    (p : Seminorm ℝ B) (hp : IsPaperNorm p) (ζ d : B) :
    |⟪ζ, d⟫_ℝ| ≤ canonicalDualNormFromPrimal p ζ * p d := by
  simpa [canonicalDualNormFromPrimal] using
    (SOptLib.abs_inner_le_canonicalDualNorm_mul (p := p) (hp := by simpa [IsPaperNorm] using hp)
      (zeta := ζ) (d := d) (h_bdd := canonical_dual_support_set_bddAbove p hp ζ))

/-- The canonical paper dual norm is bounded by the ambient norm.

Candidate audit: no SOptLib norm primitive matches this source-derived support
function; `canonical_dual_support_set_bddAbove` gives the same geometric bound
as a `BddAbove` witness, while the measurability route for Eq. (4.6.22) needs
the explicit inequality. -/
private theorem canonicalDualNormFromPrimal_le_norm_mul_control
    {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℝ B]
    [FiniteDimensional ℝ B]
    (p : Seminorm ℝ B) (hp : IsPaperNorm p)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x : B, ‖x‖ ≤ C * p x) (ζ : B) :
    canonicalDualNormFromPrimal p ζ ≤ ‖ζ‖ * C := by
  have hC_unit : ∀ x : B, p x ≤ 1 → ‖x‖ ≤ C := by
    intro x hx
    exact (hC x).trans (by simpa using mul_le_mul_of_nonneg_left hx hC0)
  simpa [canonicalDualNormFromPrimal] using (SOptLib.canonicalDualNorm_le_norm_mul_control p hC_unit ζ)

/-- Subadditivity of the canonical paper dual norm as a support function. -/
private theorem canonicalDualNormFromPrimal_add_le
    {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℝ B]
    [FiniteDimensional ℝ B]
    (p : Seminorm ℝ B) (hp : IsPaperNorm p) (ζ η : B) :
    canonicalDualNormFromPrimal p (ζ + η) ≤
      canonicalDualNormFromPrimal p ζ + canonicalDualNormFromPrimal p η := by
  simpa [canonicalDualNormFromPrimal] using
    SOptLib.canonicalDualNorm_add_le (p := p) (zeta := ζ) (eta := η)
      (canonical_dual_support_set_bddAbove p hp ζ)
      (canonical_dual_support_set_bddAbove p hp η)

/-- Lipschitz control of the canonical paper dual norm. -/
private theorem canonicalDualNormFromPrimal_lipschitz_control
    {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℝ B]
    [FiniteDimensional ℝ B]
    (p : Seminorm ℝ B) (hp : IsPaperNorm p)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x : B, ‖x‖ ≤ C * p x) (ζ η : B) :
    |canonicalDualNormFromPrimal p ζ - canonicalDualNormFromPrimal p η| ≤
      C * ‖ζ - η‖ := by
  have hC_unit : ∀ x : B, p x ≤ 1 → ‖x‖ ≤ C := by
    intro x hx
    exact (hC x).trans (by simpa using mul_le_mul_of_nonneg_left hx hC0)
  simpa [canonicalDualNormFromPrimal] using
    (SOptLib.canonicalDualNorm_lipschitz_control (p := p) (C := C) hC_unit ζ η)

/-- Continuity of the canonical paper dual norm.

This is the measurability bridge needed for the uncentered quadratic kernel in
Lan Eq. (4.6.22); it follows from finite-dimensional control of the primal
unit ball and support-function subadditivity, not from a new setup field. -/
private theorem canonicalDualNormFromPrimal_continuous
    {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℝ B]
    [FiniteDimensional ℝ B]
    (p : Seminorm ℝ B) (hp : IsPaperNorm p) :
    Continuous (fun ζ : B => canonicalDualNormFromPrimal p ζ) := by
  classical
  rcases paper_norm_controls_ambient_norm p hp with ⟨C, hC0, hC⟩
  have hC_unit : ∀ x : B, p x ≤ 1 → ‖x‖ ≤ C := by
    intro x hx
    exact (hC x).trans (by simpa using mul_le_mul_of_nonneg_left hx hC0)
  simpa [canonicalDualNormFromPrimal] using
    (SOptLib.canonicalDualNorm_continuous (p := p) (C := C) hC_unit)

/-- Complete setup for stochastic block mirror descent.

The structure collects the product block model `X = Πᵢ Xᵢ`, stochastic
objective/oracle data, blockwise Bregman geometry, the sampling distribution,
and the stated Section 4.6 assumptions. The full feasible set, block oracle
values, one-block prox step, and recursive process are derived below as
canonical objects rather than setup witnesses. -/
structure StochasticBlockMirrorDescentSetup
    (ι : Type*) [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι]
    (S : Type*) [MeasurableSpace S] where
  blockDim : ι → ℕ
  XBlock : ∀ i, Set (EuclideanSpace ℝ (Fin (blockDim i)))
  w₀ : PiLp 2 (fun i : ι => EuclideanSpace ℝ (Fin (blockDim i)))
  η : ℕ → ℝ
  θ : ℕ → ℝ
  p : ι → ℝ
  F : PiLp 2 (fun i : ι => EuclideanSpace ℝ (Fin (blockDim i))) → S → ℝ
  gradL : PiLp 2 (fun i : ι => EuclideanSpace ℝ (Fin (blockDim i))) → S → PiLp 2 (fun i : ι => EuclideanSpace ℝ (Fin (blockDim i)))
  g : PiLp 2 (fun i : ι => EuclideanSpace ℝ (Fin (blockDim i))) → PiLp 2 (fun i : ι => EuclideanSpace ℝ (Fin (blockDim i)))
  /-- book/FOML/StochasticBlockMirrorDescent.json#/setup/problem/math:
  "`f(x) := E[F(x, ξ)]`". The law of the stochastic source `ξ` is encoded as
  Mathlib probability-measure data rather than as a separate setup Prop. -/
  sampleLaw : ProbabilityMeasure S
  /-- book/FOML/StochasticBlockMirrorDescent.json#/assumptions/3/math:
  "`v_i : X_i → ℝ`". This is the paper-facing restricted distance generating
  function; outside-carrier values are not part of the source mathematical
  object. -/
  blockDGF : ∀ i, {u : EuclideanSpace ℝ (Fin (blockDim i)) // u ∈ XBlock i} → ℝ
  /-- Internal ambient realization of the restricted source DGF `v_i`.

  This field is not a paper object. It exists only to express Mathlib's
  `ContDiffOn` and ambient strong-convexity assumptions on `X_i`; the bridge
  `hblockDGF_eq_ambient` below states that all paper-facing values are the
  restricted `blockDGF` values, and no outside-`X_i` value enters `V_i`. -/
  blockDGFAmbient : ∀ i, EuclideanSpace ℝ (Fin (blockDim i)) → ℝ
  /-- Internal realization bridge for Eq. (4.6.7):
  paper-facing `v_i` agrees with its ambient differentiability realization on
  `X_i`. Outside-carrier values of `blockDGFAmbient` have no paper semantics. -/
  hblockDGF_eq_ambient :
    ∀ i (u : {u : EuclideanSpace ℝ (Fin (blockDim i)) // u ∈ XBlock i}),
      blockDGF i u = blockDGFAmbient i u.1
  /-- book/FOML/StochasticBlockMirrorDescent.json#/assumptions/3/math:
  "`v_i` is `1`-strongly convex w.r.t. `‖·‖_i`". This is the paper's block
  primal norm family, not an ambient Hilbert specialization. The separation
  law below makes the seminorm representation a genuine paper norm. -/
  blockPrimalNorm : ∀ i, Seminorm ℝ (EuclideanSpace ℝ (Fin (blockDim i)))
  /-- book/FOML/StochasticBlockMirrorDescent.json#/assumptions/2/math:
  "`E[‖G_i(x, ξ)‖_{i,*}^2] ≤ M_i^2`", together with
  book/FOML/StochasticBlockMirrorDescent.json#/assumptions/3/math:
  "`v_i` is `1`-strongly convex w.r.t. `‖·‖_i`". The `*` norm is now derived
  from this primal norm, so the setup records only the primal norm's
  nondegeneracy as part of saying `‖·‖_i` is a norm. -/
  hblockPrimalNorm_norm : ∀ i, IsPaperNorm (blockPrimalNorm i)
  M : ι → ℝ
  /-- book/FOML/StochasticBlockMirrorDescent.json#/setup/variable_space:
  "each `X_i ⊆ ℝ^{n_i}` closed convex". -/
  hXBlock_closed :
    ∀ i, IsClosed (XBlock i)
  /-- Lan, §4.6.1.1, immediately before Eq. (4.6.8):
  "Suppose that the set `X_i` is bounded". Together with the preceding closed
  carrier assumption and finite-dimensional block realization, this is the
  compactness datum used by the canonical compact prox selector below. -/
  hXBlock_bounded :
    ∀ i, Bornology.IsBounded (XBlock i)
  /-- book/FOML/StochasticBlockMirrorDescent.json#/setup/variable_space:
  "each `X_i ⊆ ℝ^{n_i}` closed convex". -/
  hXBlock_convex :
    ∀ i, Convex ℝ (XBlock i)
  /-- book/FOML/StochasticBlockMirrorDescent.json#/assumptions/0/math:
  "`f(·)` is convex on `X`", where
  book/FOML/StochasticBlockMirrorDescent.json#/setup/problem/math defines
  "`f(x) := E[F(x, ξ)]`". This records the well-definedness part of the
  displayed expectation on feasible points, using SOptLib's objective
  integrability predicate rather than relying on Mathlib's totalized integral. -/
  hobjective_wellDefined :
    ∀ x, x ∈ {x : PiLp 2 (fun i : ι => EuclideanSpace ℝ (Fin (blockDim i))) | ∀ i, x i ∈ XBlock i} →
      SOptLib.objectiveWellDefined (sampleLaw : Measure S) F (fun s : S => s) x
  /-- book/FOML/StochasticBlockMirrorDescent.json#/assumptions/0/math:
  "`f(·)` is convex on `X`". -/
  hf_convex :
    ConvexOn ℝ {x : PiLp 2 (fun i : ι => EuclideanSpace ℝ (Fin (blockDim i))) | ∀ i, x i ∈ XBlock i}
      (fun x => SOptLib.objectiveExpectation (sampleLaw : Measure S) F (fun s : S => s) x)
  /-- book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec/initialization:
  "`x_1 ∈ X`". -/
  hw₀_mem : ∀ i, w₀ i ∈ XBlock i
  /-- book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec/parameters/0/math:
  "`γ_k > 0` (positive stepsizes)". -/
  hη_pos : ∀ k, 0 < η k
  /-- book/FOML/StochasticBlockMirrorDescent.json#/assumptions/5/math:
  "`θ_k = γ_k`". -/
  hθ_eq_η : ∀ k, θ k = η k
  /-- book/FOML/StochasticBlockMirrorDescent.json#/assumptions/4/parameters:
  "`p_i ∈ (0, 1]`". -/
  hp_pos : ∀ i, 0 < p i
  /-- book/FOML/StochasticBlockMirrorDescent.json#/assumptions/4/math:
  "`∑_{i=1}^{b} p_i = 1`". -/
  hp_sum : Finset.sum Finset.univ p = 1
  /-- book/FOML/StochasticBlockMirrorDescent.json#/assumptions/1/math:
  "`E[G(x, ξ)] = g(x)`". This is the well-definedness part of the source
  expectation notation for feasible `x`, specialized from SOptLib's oracle
  integrability predicate. -/
  horacle_wellDefined :
    ∀ x, x ∈ {x : PiLp 2 (fun i : ι => EuclideanSpace ℝ (Fin (blockDim i))) | ∀ i, x i ∈ XBlock i} →
      SOptLib.oracleWellDefined (sampleLaw : Measure S) gradL (fun s : S => s) x
  /-- book/FOML/StochasticBlockMirrorDescent.json#/assumptions/1/math:
  "`E[G(x, ξ)] = g(x)`". -/
  hunbiased :
    ∀ x, x ∈ {x : PiLp 2 (fun i : ι => EuclideanSpace ℝ (Fin (blockDim i))) | ∀ i, x i ∈ XBlock i} →
      ∫ s, gradL x s ∂(sampleLaw : Measure S) = g x
  /-- book/FOML/StochasticBlockMirrorDescent.json#/assumptions/1/math:
  "`g(x) ∈ ∂ f(x)`, for all `x ∈ X`". -/
  hsubgradient :
    ∀ x (hx : x ∈ {x : PiLp 2 (fun i : ι => EuclideanSpace ℝ (Fin (blockDim i))) | ∀ i, x i ∈ XBlock i}),
      g x ∈ SOptLib.carrierSubdifferential
        (fun y : {y : PiLp 2 (fun i : ι => EuclideanSpace ℝ (Fin (blockDim i))) //
            y ∈ {x : PiLp 2 (fun i : ι => EuclideanSpace ℝ (Fin (blockDim i))) | ∀ i, x i ∈ XBlock i}} =>
          SOptLib.objectiveExpectation (sampleLaw : Measure S) F (fun s : S => s) y.1)
        ⟨x, hx⟩
  /-- book/FOML/StochasticBlockMirrorDescent.json#/assumptions/2/math:
  "`E[‖G_i(x, ξ)‖_{i,*}^2] ≤ M_i^2`". This records the square-integrability
  required for the displayed second moment to be a genuine expectation; no
  reusable SOptLib primitive matches the uncentered block-dual moment exactly,
  so the source assumption is stated directly as `Integrable`. -/
  hblock_second_moment_wellDefined :
    ∀ i x, x ∈ {x : PiLp 2 (fun i : ι => EuclideanSpace ℝ (Fin (blockDim i))) | ∀ i, x i ∈ XBlock i} →
      Integrable
        (fun s =>
          canonicalDualNormFromPrimal (blockPrimalNorm i) ((gradL x s) i) ^ 2)
        (sampleLaw : Measure S)
  /-- book/FOML/StochasticBlockMirrorDescent.json#/assumptions/2/math:
  "`E[‖G_i(x, ξ)‖_{i,*}^2] ≤ M_i^2`". -/
  hblock_second_moment :
    ∀ i x, x ∈ {x : PiLp 2 (fun i : ι => EuclideanSpace ℝ (Fin (blockDim i))) | ∀ i, x i ∈ XBlock i} →
      ∫ s,
        canonicalDualNormFromPrimal (blockPrimalNorm i) ((gradL x s) i) ^ 2 ∂(sampleLaw : Measure S)
        ≤ (M i) ^ 2
  /-- book/FOML/StochasticBlockMirrorDescent.json#/assumptions/2/parameters:
  "`M_i > 0`". -/
  hM_pos : ∀ i, 0 < M i
  /-- book/FOML/StochasticBlockMirrorDescent.json#/assumptions/3/math:
  "`v_i : X_i → ℝ` is continuously differentiable". -/
  hblockDGFAmbient_contDiffOn :
    ∀ i, ContDiffOn ℝ 1 (blockDGFAmbient i) (XBlock i)
  /-- book/FOML/StochasticBlockMirrorDescent.json#/assumptions/3/math:
  "`v_i` is `1`-strongly convex w.r.t. `‖·‖_i`". -/
  hblockDGFAmbient_strongly_convex :
    ∀ i, StrongConvexOnWithNorm (XBlock i) 1 (blockPrimalNorm i) (blockDGFAmbient i)
  /-- Measurable stochastic-oracle kernel for the random update map.

  This is the Lean regularity realization of the source stochastic oracle:
  Lan §4.1 states that one may use "a measurable selection `G(x, ξ)`" as the
  stochastic subgradient, and §6.1 refers explicitly to "Borel functions
  `G(x_k, ξ_k)`". The SBMD section then uses the same stochastic-oracle object
  in Eq. (4.6.3) and at random iterates in Theorem 4.12. -/
  hgradL_measurable :
    Measurable (fun p : PiLp 2 (fun i : ι => EuclideanSpace ℝ (Fin (blockDim i))) × S => gradL p.1 p.2)

namespace StochasticBlockMirrorDescentSetup

variable (setup : StochasticBlockMirrorDescentSetup ι S)

/-- Canonical ambient state space `Πᵢ ℝ^{n_i}` from Eq. (4.6.2). -/
abbrev StateSpace : Type _ :=
  PiLp 2 (fun i : ι => EuclideanSpace ℝ (Fin (setup.blockDim i)))

/-- Canonical path space of iid same-time product samples `(ξ_k, i_k)`. -/
abbrev SamplePath : Type _ :=
  StochasticBlockSamplePath S ι

/-- The canonical block type `ℝ^{n_i}` from Eq. (4.6.2). -/
abbrev Block (i : ι) : Type :=
  EuclideanSpace ℝ (Fin (setup.blockDim i))

noncomputable instance instBlockNormed (i : ι) : NormedAddCommGroup (setup.Block i) :=
  inferInstance

noncomputable instance instBlockInner (i : ι) : InnerProductSpace ℝ (setup.Block i) :=
  inferInstance

noncomputable instance instBlockComplete (i : ι) : CompleteSpace (setup.Block i) :=
  inferInstance

/-- Product-feasible set `X = X_1 × ... × X_b` from Eq. (4.6.2).

No SOptLib match: searched "block coordinate product replacement projection",
scanned `SOptLib/Model/Carrier.lean` and `SOptLib/Model/Prox.lean`; none align
with Lan Eq. (4.6.2) because this paper needs a dependent block product whose
coordinates may live in different spaces `ℝ^{n_i}`. -/
def X : Set setup.StateSpace :=
  {x | ∀ i, x i ∈ setup.XBlock i}

/-- Full product-feasible subtype for the feasible carrier `X`. -/
abbrev FeasibleState : Type _ :=
  Set.Elem setup.X


/-- The finite Euclidean block space `ℝ^{n_i}` from Eq. (4.6.2). -/
abbrev blockEuclideanSpace (i : ι) : Type :=
  EuclideanSpace ℝ (Fin (setup.blockDim i))

/-- Nonnegativity of the block sampling probabilities, derived from the paper
assumption `p_i ∈ (0, 1]` rather than stored as setup data. -/
theorem hp_nonneg : ∀ i, 0 ≤ setup.p i :=
  fun i => le_of_lt (setup.hp_pos i)

/-- The paper's dimension identity `n = ∑ᵢ n_i` from Eq. (4.6.2). -/
theorem ambientDim_eq_sum_blockDim :
    Finset.sum Finset.univ setup.blockDim = Finset.sum Finset.univ setup.blockDim := by
  exact le_antisymm
    (Finset.sum_le_sum fun i _ => le_rfl)
    (Finset.sum_le_sum fun i _ => le_rfl)

/-- Canonical block coordinate map `U_i^T x = x^{(i)}` on the product space. -/
noncomputable def blockCoord (i : ι) : setup.StateSpace →L[ℝ] setup.Block i :=
  PiLp.proj 2 (fun i : ι => EuclideanSpace ℝ (Fin (setup.blockDim i))) i


/-- Coordinate-after-assembly is definitional for the product model. -/
theorem blockCoord_assemble (y : ∀ i, setup.Block i) (i : ι) :
    setup.blockCoord i (WithLp.toLp 2 y) = y i := by
  simpa [blockCoord] using
    (PiLp.proj_toLp (𝕜 := ℝ) (p := 2)
      (fun i : ι => EuclideanSpace ℝ (Fin (setup.blockDim i))) y i)

/-- Assembly-after-coordinate projection is definitional for the product model. -/
theorem assemble_blockCoord (x : setup.StateSpace) :
    WithLp.toLp 2 (fun i => setup.blockCoord i x) = x := by
  simpa [blockCoord] using
    (PiLp.toLp_proj (𝕜 := ℝ) (p := 2)
      (fun i : ι => EuclideanSpace ℝ (Fin (setup.blockDim i))) x)

/-- The object-layer block type is a finite Euclidean block `ℝ^{n_i}` up to
linear isometry, not an unconstrained Hilbert witness. -/
noncomputable def blockEuclideanRealization (i : ι) :
    setup.Block i ≃L[ℝ] setup.blockEuclideanSpace i := by
  exact ContinuousLinearEquiv.refl ℝ (setup.blockEuclideanSpace i)

/-- Canonical sample law of the stochastic oracle draw `ξ` in Eq. (4.6.1). -/
noncomputable def oracleSampleLaw : Measure S :=
  setup.sampleLaw

/-- The source law of `ξ` is a probability measure by its Mathlib
`ProbabilityMeasure` data, not by an extra paper-facing setup hypothesis. -/
theorem oracleSampleLaw_probability : IsProbabilityMeasure setup.oracleSampleLaw := by
  unfold oracleSampleLaw
  infer_instance

/-- Finite block-index law from `Prob {i_k = i} = p_i`, Eq. (4.6.12). -/
noncomputable def blockIndexLaw : Measure ι :=
  finiteBlockIndexLaw setup.p setup.hp_nonneg setup.hp_sum

/-- Singleton form of the finite block-index law from Eq. (4.6.12). -/
theorem blockIndexLaw_singleton (i : ι) :
    setup.blockIndexLaw ({i} : Set ι) = ENNReal.ofReal (setup.p i) := by
  simpa [StochasticBlockMirrorDescentSetup.blockIndexLaw] using
    finiteBlockIndexLaw_singleton setup.p setup.hp_nonneg setup.hp_sum i

/-- Product law for the generated same-time oracle/block pair `(ξ_k, i_k)`.

This is the canonical source-layer sampling distribution used by Algorithm 4.5:
the oracle draw has law `sampleLaw` and the block draw has the finite PMF
specified by `p`. -/
noncomputable def samplePairLaw : Measure (S × ι) :=
  setup.oracleSampleLaw.prod setup.blockIndexLaw

/-- The same-time oracle/block product law is a probability measure, derived
from the source sample law and the finite PMF block law. -/
theorem samplePairLaw_probability : IsProbabilityMeasure setup.samplePairLaw := by
  classical
  letI : IsProbabilityMeasure setup.oracleSampleLaw := setup.oracleSampleLaw_probability
  unfold samplePairLaw blockIndexLaw finiteBlockIndexLaw
  infer_instance

/-- Canonical iid product-stream law for Algorithm 4.5.

This replaces the previous setup witness `P` and its iid/product-law property
fields. Mathlib's `Measure.infinitePi` is the canonical product measure for an
arbitrary family of probability measures, and the one-time marginal is the
paper's product law `sampleLaw × finiteBlockSamplingLaw p` from Eq. (4.6.12). -/
noncomputable def P : Measure (StochasticBlockSamplePath S ι) := by
  exact iidStreamLaw setup.samplePairLaw

/-- The canonical iid product-stream law is a probability measure. -/
theorem P_probability : IsProbabilityMeasure setup.P := by
  classical
  letI : IsProbabilityMeasure setup.oracleSampleLaw := setup.oracleSampleLaw_probability
  letI : IsProbabilityMeasure setup.samplePairLaw := setup.samplePairLaw_probability
  unfold P
  exact iidStreamLaw_isProbabilityMeasure setup.samplePairLaw

/-- Paper objective `f(x) := E[F(x, ξ)]` from Eq. (4.6.1).

This specializes SOptLib's `objectiveExpectation` to the sample law induced by
the stochastic loss kernel; the previous primitive setup field `f` and equality
field `hobjective_expectation` have been removed so Eq. (4.6.1) is a definition
rather than witness data. -/
noncomputable def objective (x : setup.StateSpace) : ℝ :=
  SOptLib.objectiveExpectation setup.oracleSampleLaw setup.F (fun s : S => s) x

/-- Well-definedness of the paper objective expectation on feasible points in
Eq. (4.6.1), specialized from SOptLib's objective integrability predicate. -/
theorem objective_wellDefined (x : setup.StateSpace) (hx : x ∈ setup.X) :
    SOptLib.objectiveWellDefined setup.oracleSampleLaw setup.F (fun s : S => s) x := by
  exact SOptLib.stochasticObjective_wellDefined_of_mem setup.oracleSampleLaw setup.F
    (fun s : S => s) setup.X
    (by
      intro y hy
      simpa [X, oracleSampleLaw] using setup.hobjective_wellDefined y hy)
    hx

/-- Defining formula for the paper objective in Eq. (4.6.1), stated with the
well-definedness hypothesis that makes the integral a genuine expectation
rather than only Mathlib's totalized Bochner integral. -/
theorem objective_eq_integral (x : setup.StateSpace) (hx : x ∈ setup.X) :
    setup.objective x = ∫ s, setup.F x s ∂setup.oracleSampleLaw := by
  simpa [StochasticBlockMirrorDescentSetup.objective, SOptLib.objectiveExpectation_def]

/-- Feasible-carrier objective for the setup problem in Eq. (4.6.1).

This specializes SOptLib's objective-minimizer layer to the paper's carrier
`X`: the candidates `objectiveExpectation`, `IsMinimizer`, and
`optimizerValueOfMinimum` were checked, and the latter two exactly model the
attained minimum value `f^* := min_{x in X} f(x)` once the expected objective
above is restricted to feasible points. -/
noncomputable def feasibleObjective (x : setup.FeasibleState) : ℝ :=
  setup.objective x.1

/-- Carrier minimizer predicate for the setup problem
`f^* := min_{x in X} { f(x) := E[F(x, ξ)] }`, Eq. (4.6.1). -/
def isObjectiveMinimizer (xStar : setup.FeasibleState) : Prop :=
  SOptLib.IsMinimizer setup.feasibleObjective xStar

/-- Attained-minimum carrier object for the paper's setup problem in Eq. (4.6.1). -/
abbrev ObjectiveMinimum : Type _ :=
  SOptLib.ObjectiveMinimum setup.feasibleObjective

/-- Paper optimum value `f^* := min_{x in X} f(x)` from Eq. (4.6.1).

This is SOptLib's `optimizerValueOfMinimum` applied to the carrier-restricted
expected objective, so the optimum value is a named object-layer value rather
than an implicit theorem-local optimizer hypothesis. -/
noncomputable def fStar (minimum : setup.ObjectiveMinimum) : ℝ :=
  SOptLib.optimizerValueOfMinimum setup.feasibleObjective
    ⟨minimum.1, by
      simpa [isObjectiveMinimizer, SOptLib.IsMinimizer] using minimum.2⟩

/-- Selected optimizer `x_*` associated with an attained setup minimum. -/
noncomputable def optimalPoint (minimum : setup.ObjectiveMinimum) : setup.StateSpace :=
  minimum.1.1

/-- The selected optimizer is feasible. -/
theorem optimalPoint_mem (minimum : setup.ObjectiveMinimum) :
    setup.optimalPoint minimum ∈ setup.X :=
  minimum.1.2

/-- Defining relation between `f^*` and the selected optimizer. -/
theorem fStar_eq_objective_optimalPoint (minimum : setup.ObjectiveMinimum) :
    setup.fStar minimum = setup.objective (setup.optimalPoint minimum) := by
  simp [fStar, feasibleObjective, optimalPoint, SOptLib.optimizerValueOfMinimum]

/-- The optimum value lower-bounds the objective at every feasible point. -/
theorem fStar_le_objective (minimum : setup.ObjectiveMinimum)
    (z : setup.StateSpace) (hz : z ∈ setup.X) :
    setup.fStar minimum ≤ setup.objective z := by
  simpa [fStar, feasibleObjective, SOptLib.objectiveMinimumValue,
    SOptLib.optimizerValueOfMinimum, isObjectiveMinimizer, SOptLib.IsMinimizer] using
    (SOptLib.objectiveMinimumValue_le setup.feasibleObjective minimum ⟨z, hz⟩)

/-- Bridge from the former theorem-local optimizer data to the canonical
attained-minimum carrier object for Eq. (4.6.1). -/
noncomputable def objectiveMinimumOfOptimizer
    (xStar : setup.StateSpace) (hxStar : xStar ∈ setup.X)
    (h_opt : ∀ z, z ∈ setup.X → setup.objective xStar ≤ setup.objective z) :
    setup.ObjectiveMinimum :=
  by
    simpa [feasibleObjective] using
      (SOptLib.objectiveMinimumOfFeasibleOptimizer setup.X setup.objective xStar hxStar h_opt)

/-- The source-backed optimizer bridge has optimum value `f(x_*)`. -/
theorem fStar_objectiveMinimumOfOptimizer
    (xStar : setup.StateSpace) (hxStar : xStar ∈ setup.X)
    (h_opt : ∀ z, z ∈ setup.X → setup.objective xStar ≤ setup.objective z) :
    setup.fStar (setup.objectiveMinimumOfOptimizer xStar hxStar h_opt) =
      setup.objective xStar := by
  simpa [fStar, objectiveMinimumOfOptimizer, feasibleObjective,
    SOptLib.optimizerValueOfMinimum] using
    (SOptLib.objectiveMinimumOfFeasibleOptimizer_value setup.X setup.objective xStar hxStar h_opt)

/-- Joint sample `(ξ_k, i_k)` generated at iteration `k` of Algorithm 4.5.

The product stream is the primitive stochastic source; its coordinate
projections below are the paper's `ξ_k` and `i_k`. -/
def samplePair (_setup : StochasticBlockMirrorDescentSetup ι S)
    (t : ℕ) (ω : StochasticBlockSamplePath S ι) : S × ι :=
  ω t

/-- Stochastic-oracle sample projection `ξ_k` from the canonical product stream. -/
def ξ (setup : StochasticBlockMirrorDescentSetup ι S)
    (t : ℕ) (ω : StochasticBlockSamplePath S ι) : S :=
  (setup.samplePair t ω).1

/-- Sampled block-index projection `i_k` from the canonical product stream. -/
def block (setup : StochasticBlockMirrorDescentSetup ι S)
    (t : ℕ) (ω : StochasticBlockSamplePath S ι) : ι :=
  (setup.samplePair t ω).2

/-- Measurability of the generated stochastic sample/block pair. -/
theorem samplePair_measurable (t : ℕ) : Measurable (setup.samplePair t) := by
  simpa [samplePair] using measurable_pi_apply t

/-- Measurability of the oracle-sample projection. -/
theorem ξ_measurable (t : ℕ) : Measurable (setup.ξ t) := by
  simpa [ξ] using (setup.samplePair_measurable t).fst

/-- Measurability of the block-index projection. -/
theorem block_measurable (t : ℕ) : Measurable (setup.block t) := by
  simpa [block] using (setup.samplePair_measurable t).snd

/-- The canonical product stream has independent same-time coordinates across
iteration index; this is derived from `Measure.infinitePi`, not stored in the
paper-facing setup. -/
theorem samplePair_iIndep :
    iIndepFun (fun t (ω : StochasticBlockSamplePath S ι) => setup.samplePair t ω) setup.P := by
  classical
  letI : IsProbabilityMeasure setup.oracleSampleLaw := setup.oracleSampleLaw_probability
  letI : IsProbabilityMeasure setup.samplePairLaw := setup.samplePairLaw_probability
  unfold P samplePair
  exact ProbabilityTheory.iIndepFun_infinitePi (fun _ : ℕ => measurable_id)

/-- Every coordinate of the canonical product stream has the one-step product
law `sampleLaw × finiteBlockSamplingLaw p`. -/
theorem samplePair_law (t : ℕ) :
    Measure.map (setup.samplePair t) setup.P = setup.samplePairLaw := by
  classical
  letI : IsProbabilityMeasure setup.oracleSampleLaw := setup.oracleSampleLaw_probability
  letI : IsProbabilityMeasure setup.samplePairLaw := setup.samplePairLaw_probability
  unfold P samplePair
  simpa using (MeasureTheory.Measure.infinitePi_map_eval
    (μ := fun _ : ℕ => setup.samplePairLaw) t)

/-- Every algorithmic oracle sample `ξ_t` has the paper source law of `ξ`.

This is derived from the same-time product law of the canonical pair stream. -/
theorem stream_sample_law (t : ℕ) :
    Measure.map (setup.ξ t) setup.P = setup.oracleSampleLaw := by
  classical
  letI : IsProbabilityMeasure setup.blockIndexLaw := by
    unfold StochasticBlockMirrorDescentSetup.blockIndexLaw finiteBlockIndexLaw
    infer_instance
  simpa [StochasticBlockMirrorDescentSetup.ξ,
    StochasticBlockMirrorDescentSetup.samplePairLaw] using
    (map_fst_eq_of_map_prod_eq
      (P := setup.P) (Y := setup.samplePair t)
      (μ := setup.oracleSampleLaw) (ν := setup.blockIndexLaw)
      (setup.samplePair_measurable t).aemeasurable (setup.samplePair_law t))

/-- The generated block index has the finite law specified by `p_i`, Eq. (4.6.12). -/
theorem stream_block_law (t : ℕ) :
    Measure.map (setup.block t) setup.P = setup.blockIndexLaw := by
  classical
  letI : IsProbabilityMeasure setup.oracleSampleLaw := setup.oracleSampleLaw_probability
  letI : IsProbabilityMeasure setup.blockIndexLaw := by
    unfold StochasticBlockMirrorDescentSetup.blockIndexLaw finiteBlockIndexLaw
    infer_instance
  simpa [StochasticBlockMirrorDescentSetup.block,
    StochasticBlockMirrorDescentSetup.samplePairLaw] using
    (map_snd_eq_of_map_prod_eq
      (P := setup.P) (Y := setup.samplePair t)
      (μ := setup.oracleSampleLaw) (ν := setup.blockIndexLaw)
      (setup.samplePair_measurable t).aemeasurable (setup.samplePair_law t))

/-- Singleton form of the block sampling distribution in Eq. (4.6.12). -/
theorem block_prob (t : ℕ) (i : ι) :
    setup.P (setup.block t ⁻¹' ({i} : Set ι)) = ENNReal.ofReal (setup.p i) := by
  exact (measure_preimage_singleton_eq_of_map_eq (P := setup.P) (Y := setup.block t)
    (mu := setup.blockIndexLaw) i (setup.block_measurable t).aemeasurable
    (setup.stream_block_law t)).trans
    (setup.blockIndexLaw_singleton i)

/-- Algorithmic samples give the same objective value at every time because
their law is the paper source law of `ξ`. -/
theorem objective_eq_integral_of_stream
    (x : setup.StateSpace) (hx : x ∈ setup.X) (t : ℕ) :
    ∫ ω, setup.F x (setup.ξ t ω) ∂setup.P = setup.objective x := by
  simpa [StochasticBlockMirrorDescentSetup.objective] using
    SOptLib.objectiveExpectation_eq_integral_of_map_eq setup.P setup.oracleSampleLaw setup.F
      (setup.ξ t) x (setup.ξ_measurable t).aemeasurable
      (by
        simpa [SOptLib.objectiveWellDefined, SOptLib.objectiveKernel] using
          (setup.objective_wellDefined x hx).aestronglyMeasurable)
      (setup.stream_sample_law t)

/-- Stream form of the unbiased stochastic subgradient assumption (4.6.3). -/
theorem unbiased_stream
    (x : setup.StateSpace) (hx : x ∈ setup.X) (t : ℕ) :
    ∫ ω, setup.gradL x (setup.ξ t ω) ∂setup.P = setup.g x := by
  exact oracleMean_stream_eq_of_map_eq
    (P := setup.P) (nu := setup.oracleSampleLaw) (G := setup.gradL) (target := setup.g)
    (Y := setup.ξ t) (x := x) (setup.ξ_measurable t).aemeasurable
    (by
      have hwell : Integrable (fun s => setup.gradL x s) setup.oracleSampleLaw := by
        simpa [StochasticBlockMirrorDescentSetup.oracleSampleLaw,
          StochasticBlockMirrorDescentSetup.X, SOptLib.oracleWellDefined,
          SOptLib.oracleKernel] using setup.horacle_wellDefined x hx
      exact hwell.aestronglyMeasurable)
    (setup.stream_sample_law t)
    (oracleMean_eq_of_integral_eq
      (mu := setup.oracleSampleLaw) (G := setup.gradL) (target := setup.g) (x := x)
      (by
        simpa [StochasticBlockMirrorDescentSetup.oracleSampleLaw,
          StochasticBlockMirrorDescentSetup.X] using setup.hunbiased x hx))

/-- The initial point belongs to the product-feasible set in Algorithm 4.5. -/
theorem w₀_mem : setup.w₀ ∈ setup.X := by
  intro i
  exact setup.hw₀_mem i

/-- The averaging weights are nonnegative because Algorithm 4.5 assumes
positive stepsizes `γ_k > 0` and Eq. (4.6.16) states `θ_k = γ_k`.
This is derived data, not a setup assumption. -/
theorem theta_nonneg (k : ℕ) : 0 ≤ setup.θ k := by
  rw [setup.hθ_eq_η k]
  exact le_of_lt (setup.hη_pos k)

/-- The second-moment constants satisfy the nonnegative bound needed by later
algebra because Eq. (4.6.4) states `M_i > 0`. -/
theorem M_nonneg (i : ι) : 0 ≤ setup.M i := by
  exact le_of_lt (setup.hM_pos i)

/-- Closedness of the product-feasible set induced by the closed block sets in Eq. (4.6.2). -/
theorem X_closed : IsClosed setup.X := by
  simpa [StochasticBlockMirrorDescentSetup.X] using
    (PiLp.isClosed_set_pi (p := 2)
      (E := fun i : ι => EuclideanSpace ℝ (Fin (setup.blockDim i)))
      setup.XBlock setup.hXBlock_closed)

/-- Convexity of the product-feasible set induced by the convex block sets in Eq. (4.6.2). -/
theorem X_convex : Convex ℝ setup.X := by
  simpa [StochasticBlockMirrorDescentSetup.X] using
    (PiLp.convex_set_pi (p := 2) (X := setup.XBlock) setup.hXBlock_convex)

/-- Convexity assumption stated against the canonical expected objective from
Eq. (4.6.1), not a primitive objective field. -/
theorem objective_convex : ConvexOn ℝ setup.X setup.objective := by
  simpa [X, objective] using setup.hf_convex

/-- Well-definedness of the stochastic subgradient expectation in Eq. (4.6.3)
on feasible points, using SOptLib's oracle integrability predicate. -/
theorem oracle_wellDefined (x : setup.StateSpace) (hx : x ∈ setup.X) :
    SOptLib.oracleWellDefined setup.oracleSampleLaw setup.gradL (fun s : S => s) x := by
  simpa [X, oracleSampleLaw] using setup.horacle_wellDefined x hx

/-- Eq. (4.6.3) as an equality of the canonical SOptLib oracle mean with the
paper subgradient `g(x)`, backed by `oracle_wellDefined`. -/
theorem unbiased_oracleMean (x : setup.StateSpace) (hx : x ∈ setup.X) :
    SOptLib.oracleMean setup.oracleSampleLaw setup.gradL (fun s : S => s) x = setup.g x := by
  exact oracleMean_eq_of_integral_eq
    (mu := setup.oracleSampleLaw) (G := setup.gradL) (target := setup.g) (x := x)
    (by
      simpa [StochasticBlockMirrorDescentSetup.oracleSampleLaw,
        StochasticBlockMirrorDescentSetup.X] using setup.hunbiased x hx)


/-- The mean block subgradient `g_i(x) = U_i^T g(x)` derived from Eq. (4.6.3). -/
noncomputable def gBlock (i : ι) (x : setup.StateSpace) : setup.Block i :=
  setup.blockCoord i (setup.g x)

/-- The paper-facing block primal norm `‖·‖_i` is the setup norm datum from
Eq. (4.6.7), not a Hilbert-norm alias. -/
theorem blockPrimalNorm_eq_source (i : ι) (v : setup.Block i) :
    setup.blockPrimalNorm i v = setup.blockPrimalNorm i v := rfl

/-- The paper-facing block primal norm is nondegenerate, as required by the
source phrase `‖·‖_i` in Eq. (4.6.7). -/
theorem blockPrimalNorm_isPaperNorm (i : ι) :
    IsPaperNorm (setup.blockPrimalNorm i) :=
  setup.hblockPrimalNorm_norm i



/-- Source-facing Cauchy/support inequality for the canonical block
primal-dual norm pair. -/
theorem blockDualNorm_support_bound (i : ι) (ζ d : setup.Block i) :
    |⟪ζ, d⟫_ℝ| ≤ SOptLib.canonicalDualNorm (setup.blockPrimalNorm i) ζ * setup.blockPrimalNorm i d := by
  simpa [canonicalDualNormFromPrimal] using
    abs_inner_le_canonicalDualNorm_mul_primal
      (setup.blockPrimalNorm i) (setup.blockPrimalNorm_isPaperNorm i) ζ d

/-- The restricted paper DGF agrees with its internal ambient realization on `X_i`.

This is the only bridge from the paper object `v_i : X_i → ℝ` to the Mathlib
`ContDiffOn`/strong-convexity realization; values of `blockDGFAmbient` outside
`X_i` are intentionally absent from paper-facing formulas. -/
theorem blockDGF_eq_ambient (i : ι) (u : {u : setup.Block i // u ∈ setup.XBlock i}) :
    setup.blockDGF i u = setup.blockDGFAmbient i u.1 :=
  setup.hblockDGF_eq_ambient i u

/-- Source identity for the paper distance generator
`v_i : X_i → ℝ` in Eq. (4.6.7).

This deliberately exposes the restricted carrier object as the source-facing
DGF; the ambient realization bridge is separate and only supports Mathlib
differentiability predicates. -/
theorem blockDGF_eq_source (i : ι) (u : {u : setup.Block i // u ∈ setup.XBlock i}) :
    setup.blockDGF i u = setup.blockDGF i u := rfl

/-- The internal ambient realization of the restricted DGF is continuously
differentiable on `X_i`, expressing the smoothness part of Eq. (4.6.7). -/
theorem blockDGFAmbient_contDiffOn (i : ι) :
    ContDiffOn ℝ 1 (setup.blockDGFAmbient i) (setup.XBlock i) := by
  exact setup.hblockDGFAmbient_contDiffOn i

/-- The internal ambient realization of the restricted DGF is strongly convex on
`X_i` with respect to the paper-facing block norm, matching Eq. (4.6.7). -/
theorem blockDGFAmbient_strongly_convex_wrt_blockPrimalNorm (i : ι) :
    StrongConvexOnWithNorm (setup.XBlock i) 1 (setup.blockPrimalNorm i)
      (setup.blockDGFAmbient i) := by
  exact setup.hblockDGFAmbient_strongly_convex i

/-- Source-facing restricted form of the `1`-strong convexity assumption for
`v_i : X_i → ℝ` in Eq. (4.6.7).

The theorem is stated entirely on the feasible carrier. Its proof is deferred
to the prover from `blockDGFAmbient_strongly_convex_wrt_blockPrimalNorm`,
`blockDGF_eq_ambient`, and convexity of `X_i`. -/
theorem blockDGF_strongly_convex_wrt_blockPrimalNorm (i : ι) :
    ∀ ⦃x : {u : setup.Block i // u ∈ setup.XBlock i}⦄,
      ∀ ⦃y : {u : setup.Block i // u ∈ setup.XBlock i}⦄,
      ∀ ⦃a b : ℝ⦄, (ha : 0 ≤ a) → (hb : 0 ≤ b) → (hab : a + b = 1) →
        setup.blockDGF i
          ⟨a • x.1 + b • y.1,
            setup.hXBlock_convex i x.2 y.2 ha hb hab⟩ ≤
          a * setup.blockDGF i x + b * setup.blockDGF i y -
            (1 : ℝ) / 2 * a * b * (setup.blockPrimalNorm i (x.1 - y.1)) ^ 2 := by
  exact
    strongConvexOnWithGauge_subtype_restrict_of_eqOn
      (X := setup.XBlock i) (mu := (1 : ℝ)) (rho := setup.blockPrimalNorm i)
      (f := setup.blockDGFAmbient i) (fc := setup.blockDGF i)
      (setup.hXBlock_convex i)
      (by
        simpa [StrongConvexOnWithNorm] using
          setup.blockDGFAmbient_strongly_convex_wrt_blockPrimalNorm i)
      (setup.blockDGF_eq_ambient i)

/-- Well-definedness of the uncentered block second moment in Eq. (4.6.4).

The SOptLib variance predicates were considered, but they encode centered
variance kernels. Lan's displayed assumption is the uncentered block moment
`E[‖G_i(x, ξ)‖_{i,*}^2]`, so this theorem exposes the exact integrability
recorded in the setup. -/
theorem block_second_moment_wellDefined
    (i : ι) (x : setup.StateSpace) (hx : x ∈ setup.X) :
    Integrable
      (fun s => SOptLib.canonicalDualNorm (setup.blockPrimalNorm i) (setup.blockCoord i (setup.gradL x s)) ^ 2)
      setup.oracleSampleLaw := by
  exact blockOracleSecondMomentWellDefined
    (μ := setup.oracleSampleLaw)
    (Gblock := fun z s => setup.blockCoord i (setup.gradL z s))
    (dualNorm := SOptLib.canonicalDualNorm (setup.blockPrimalNorm i))
    (feasible := setup.X)
    (x := x)
    (hx := hx)
    (h_wellDefined := by
      intro z hz
      simpa [X, canonicalDualNormFromPrimal, oracleSampleLaw] using
        setup.hblock_second_moment_wellDefined i z hz)

/-- Eq. (4.6.4) stated with the paper-facing block dual norm. -/
theorem block_second_moment_dualNorm
    (i : ι) (x : setup.StateSpace) (hx : x ∈ setup.X) :
    ∫ s, SOptLib.canonicalDualNorm (setup.blockPrimalNorm i) (setup.blockCoord i (setup.gradL x s)) ^ 2 ∂setup.oracleSampleLaw
      ≤ (setup.M i) ^ 2 := by
  exact blockOracleSecondMoment_le_sq
    (μ := setup.oracleSampleLaw)
    (Gblock := fun z s => setup.blockCoord i (setup.gradL z s))
    (dualNorm := SOptLib.canonicalDualNorm (setup.blockPrimalNorm i))
    (feasible := setup.X)
    (M := setup.M i)
    (x := x)
    (hx := hx)
    (h_second_moment := by
      intro z hz
      simpa [X, oracleSampleLaw] using setup.hblock_second_moment i z hz)

/-- Eq. (4.6.4) packaged as a genuine well-defined moment assumption: the
uncentered block dual squared norm is integrable and its expectation is bounded
by `M_i^2`. -/
theorem block_second_moment_expectation
    (i : ι) (x : setup.StateSpace) (hx : x ∈ setup.X) :
    Integrable
        (fun s => SOptLib.canonicalDualNorm (setup.blockPrimalNorm i) (setup.blockCoord i (setup.gradL x s)) ^ 2)
        setup.oracleSampleLaw ∧
      ∫ s, SOptLib.canonicalDualNorm (setup.blockPrimalNorm i) (setup.blockCoord i (setup.gradL x s)) ^ 2 ∂setup.oracleSampleLaw
        ≤ (setup.M i) ^ 2 :=
  blockOracleSecondMomentExpectation
    (μ := setup.oracleSampleLaw)
    (Gblock := fun z s => setup.blockCoord i (setup.gradL z s))
    (dualNorm := SOptLib.canonicalDualNorm (setup.blockPrimalNorm i))
    (feasible := setup.X)
    (M := setup.M i)
    (x := x)
    (hx := hx)
    (h_wellDefined := fun z hz => setup.block_second_moment_wellDefined i z hz)
    (h_second_moment := fun z hz => setup.block_second_moment_dualNorm i z hz)

/-- Algorithmic-stream form of the block second-moment bound (4.6.4), derived
from the source sample law and the stream-law bridge. -/
theorem block_second_moment_stream
    (i : ι) (x : setup.StateSpace) (hx : x ∈ setup.X) (t : ℕ) :
    ∫ ω, SOptLib.canonicalDualNorm (setup.blockPrimalNorm i) (setup.blockCoord i (setup.gradL x (setup.ξ t ω))) ^ 2 ∂setup.P
      ≤ (setup.M i) ^ 2 := by
  exact blockOracleSecondMoment_stream_le_sq_of_map_eq
    (P := setup.P) (mu := setup.oracleSampleLaw) (Y := setup.ξ)
    (Gblock := fun z s => setup.blockCoord i (setup.gradL z s))
    (dualNorm := SOptLib.canonicalDualNorm (setup.blockPrimalNorm i))
    (M := setup.M i) (x := x) (t := t)
    (hY := (setup.ξ_measurable t).aemeasurable)
    (hmap := setup.stream_sample_law t)
    (h_moment_aesm := (setup.block_second_moment_wellDefined i x hx).aestronglyMeasurable)
    (h_bound := setup.block_second_moment_dualNorm i x hx)

/-- Natural strict-prefix filtration generated by the realized pairs
`(ξ_j, i_j)` for `j < k`.

This specializes SOptLib's `filtration` to Algorithm 4.5, replacing
the previous theorem-local filtration and independence hypotheses by a
canonical generated filtration object for
`book/FOML/StochasticBlockMirrorDescent.json#/main_theorem/proof/2`. -/
noncomputable def sampleFiltration :
    Filtration ℕ (by infer_instance : MeasurableSpace (StochasticBlockSamplePath S ι)) :=
  SOptLib.filtration setup.samplePair setup.samplePair_measurable

/-- The current generated sample/block pair is independent of the strict past
filtration. This is derived stochastic-process scaffolding used in the proof of
Eq. (4.6.21), not a primitive paper assumption. -/
theorem currentSample_independent_past (k : ℕ) :
  Indep (setup.sampleFiltration k)
      (MeasurableSpace.comap (setup.samplePair k) (by infer_instance : MeasurableSpace (S × ι)))
      setup.P := by
  simpa [sampleFiltration] using
    (samplePrefixFiltration_indep_current
      (ξ := setup.samplePair)
      (hξ_measurable := setup.samplePair_measurable)
      (hξ_iIndep := setup.samplePair_iIndep)
      (t := k))

/-- Same-time independence of the oracle draw `ξ_k` and sampled block `i_k`.

This exposes the stochastic law cited in
`book/FOML/StochasticBlockMirrorDescent.json#/main_theorem/proof/2`:
`E[δ_k | ζ_[k-1]] = 0` follows from same-time independence together with
the unbiased oracle condition (4.6.3). -/
theorem currentSample_components_independent (k : ℕ) :
    IndepFun (setup.ξ k) (setup.block k) setup.P := by
  classical
  letI : IsProbabilityMeasure setup.oracleSampleLaw := setup.oracleSampleLaw_probability
  letI : IsProbabilityMeasure setup.blockIndexLaw := by
    unfold StochasticBlockMirrorDescentSetup.blockIndexLaw finiteBlockIndexLaw
    infer_instance
  have hpair :
      Measure.map (setup.samplePair k) setup.P =
        setup.oracleSampleLaw.prod setup.blockIndexLaw := by
    simpa [StochasticBlockMirrorDescentSetup.samplePairLaw] using setup.samplePair_law k
  simpa [StochasticBlockMirrorDescentSetup.ξ, StochasticBlockMirrorDescentSetup.block] using
    (indepFun_of_map_prod_eq_prod_laws
      (P := setup.P) (Z := setup.samplePair k)
      (mu := setup.oracleSampleLaw) (nu := setup.blockIndexLaw)
      (setup.samplePair_measurable k).aemeasurable hpair)


/-- Defining pairing law for the paper maps `U_i^T` and `U_i`. -/
theorem blockDualLift_pairing (i : ι) (v : setup.StateSpace) (u : setup.Block i) :
    ⟪setup.blockCoord i v, u⟫_ℝ = ⟪v, PiLp.single 2 i u⟫_ℝ := by
  simpa [blockCoord] using
    (SOptLib.piLp_inner_coord_single (𝕜 := ℝ) (Block := setup.Block) i v u)

/-- Paper coordinate-insertion reconstruction law
`∑ᵢ Uᵢ Uᵢᵀ v = v` for the block product `X = Πᵢ Xᵢ`.

This is the source-facing bridge missing from the earlier object layer: the
ambient lift used in `δ_k` is tied to the same block coordinates that define
`G_i(x, ξ) = U_i^T G(x, ξ)`, so finite block averaging can reconstruct the full
ambient vector. -/
theorem blockDualLift_sum_blockCoord (v : setup.StateSpace) :
    Finset.sum Finset.univ (fun i => PiLp.single 2 i (setup.blockCoord i v)) = v := by
  simpa [blockCoord] using
    (SOptLib.finset_sum_piLp_single_apply_self (Block := setup.Block) (p := 2) v)

/-- The sampled block oracle components reconstruct the ambient stochastic
subgradient: `∑ᵢ Uᵢ G_i(x, ξ) = G(x, ξ)`. -/
theorem gradBlock_reconstruction (x : setup.StateSpace) (s : S) :
    Finset.sum Finset.univ (fun i => PiLp.single 2 i (setup.blockCoord i (setup.gradL x s))) =
      setup.gradL x s := by
  simpa using setup.blockDualLift_sum_blockCoord (setup.gradL x s)

/-- The weighted lifted sampled block oracle has mean `g(x)`, the concrete
one-step form of Eq. (4.6.3) combined with the block law
`Prob {i_k = i} = p_i` and the same-time independence of `i_k` and `ξ_k`
cited in Theorem 4.12 proof step 3.

The proof is intentionally left to the prover: it expands over the finite block
law, uses `currentSample_components_independent`, applies `∑ᵢ Uᵢ Uᵢᵀ`, and
then uses the unbiased stochastic oracle assumption. -/
theorem weighted_lifted_gradBlock_unbiased
    (x : setup.StateSpace) (hx : x ∈ setup.X) (t : ℕ) :
    ∫ ω, (setup.p (setup.block t ω))⁻¹ •
        PiLp.single 2 (setup.block t ω)
          (setup.blockCoord (setup.block t ω) (setup.gradL x (setup.ξ t ω))) ∂setup.P =
      setup.g x := by
  classical
  letI : IsProbabilityMeasure setup.oracleSampleLaw := setup.oracleSampleLaw_probability
  letI : IsProbabilityMeasure setup.blockIndexLaw := by
    unfold StochasticBlockMirrorDescentSetup.blockIndexLaw finiteBlockIndexLaw
    infer_instance
  exact integral_weighted_lifted_block_oracle_eq_mean
    (P := setup.P) (muS := setup.oracleSampleLaw) (muI := setup.blockIndexLaw)
    (samplePair := setup.samplePair t) (p := setup.p) (G := fun s => setup.gradL x s)
    (target := setup.g x) (coord := fun i y => setup.blockCoord i y)
    (lift := fun i u => PiLp.single 2 i u)
    (hsamplePair_meas := (setup.samplePair_measurable t).aemeasurable)
    (hsamplePair_law := by
      simpa [StochasticBlockMirrorDescentSetup.samplePairLaw] using setup.samplePair_law t)
    (hlift_int := by
      have hwell : Integrable (fun s => setup.gradL x s) setup.oracleSampleLaw := by
        simpa [StochasticBlockMirrorDescentSetup.oracleSampleLaw,
          StochasticBlockMirrorDescentSetup.X, SOptLib.oracleWellDefined,
          SOptLib.oracleKernel] using setup.horacle_wellDefined x hx
      intro i
      have hcont_lift : Continuous (fun u : setup.Block i => PiLp.single 2 i u) := by
        rw [Metric.continuous_iff]
        intro u ε hε
        refine ⟨ε, hε, ?_⟩
        intro v hv
        have hnorm : ‖PiLp.single 2 i v - PiLp.single 2 i u‖ = ‖v - u‖ := by
          simp [← PiLp.single_sub, PiLp.norm_single]
        simpa [dist_eq_norm, hnorm] using hv
      have hmeas :
          AEStronglyMeasurable
            (fun s => PiLp.single 2 i (setup.blockCoord i (setup.gradL x s)))
            setup.oracleSampleLaw := by
        exact hcont_lift.comp_aestronglyMeasurable
          ((setup.blockCoord i).continuous.comp_aestronglyMeasurable hwell.aestronglyMeasurable)
      refine hwell.mono hmeas ?_
      filter_upwards with s
      calc
        ‖PiLp.single 2 i (setup.blockCoord i (setup.gradL x s))‖ =
            ‖setup.blockCoord i (setup.gradL x s)‖ := by
              simp [PiLp.norm_single]
        _ ≤ ‖setup.gradL x s‖ := by
              simpa [StochasticBlockMirrorDescentSetup.blockCoord] using
                PiLp.norm_apply_le (setup.gradL x s) i)
    (hmuI_singleton := fun i => setup.blockIndexLaw_singleton i)
    (hp_pos := setup.hp_pos)
    (hreconstruct := fun v => setup.blockDualLift_sum_blockCoord v)
    (hmean := by
      simpa [StochasticBlockMirrorDescentSetup.oracleSampleLaw,
        StochasticBlockMirrorDescentSetup.X] using setup.hunbiased x hx)

/-- Pairing law for the sampled block oracle `G_i(x, ξ) = U_i^T G(x, ξ)`. -/
theorem gradBlock_pairing (i : ι) (x : setup.StateSpace) (s : S) (u : setup.Block i) :
    ⟪setup.blockCoord i (setup.gradL x s), u⟫_ℝ =
      ⟪setup.gradL x s, PiLp.single 2 i u⟫_ℝ := by
  simpa using setup.blockDualLift_pairing i (setup.gradL x s) u


/-- Canonical within-carrier gradient of the block distance generator `v_i`
on the feasible block `X_i`.

SOptLib `carrierGradientFrom` was checked but rejected for this source-facing
formula because it computes an affine-span chart gradient of the restricted
carrier function, while Lan Eq. (4.6.7) writes the ambient gradient
`∇v_i(z)` of the continuously differentiable realization on `X_i`. This
definition therefore uses Mathlib's `gradientWithin` of `blockDGFAmbient`
directly on `X_i`, avoiding outside-carrier totalization of `blockDGF`. -/
private noncomputable def blockFeasibleGradDGF (i : ι) (z : Set.Elem (setup.XBlock i)) :
    setup.Block i := by
  letI := setup.instBlockNormed i
  letI := setup.instBlockInner i
  letI := setup.instBlockComplete i
  exact gradientWithin (setup.blockDGFAmbient i) (setup.XBlock i) z.1

/-- Bridge theorem identifying the gradient used in `V_i` with the ambient
within-gradient of the differentiable realization of `v_i` on `X_i`. -/
private theorem blockFeasibleGradDGF_eq_ambientGradient
    (i : ι) (z : Set.Elem (setup.XBlock i)) :
    setup.blockFeasibleGradDGF i z =
      (by
        letI := setup.instBlockNormed i
        letI := setup.instBlockInner i
        letI := setup.instBlockComplete i
        exact gradientWithin (setup.blockDGFAmbient i) (setup.XBlock i) z.1) := by
  rfl

/-- Continuity of the restricted block distance generator on the feasible subtype.

This is the direct topological consequence of Lan Eq. (4.6.7)'s `C¹`
ambient realization on `X_i`: `ContDiffOn.continuousOn` gives continuity on
the carrier, and `hblockDGF_eq_ambient` transports it back to the
paper-facing subtype DGF. SOptLib candidates considered:
`carrierBregmanDivergence_continuous` needs this as an input rather than
proving it, while `ContDiffOnCarrier` bundles an additional gradient
continuity field not present in the current setup. -/
private theorem blockDGF_subtype_continuous
    (i : ι) :
    Continuous (fun u : Set.Elem (setup.XBlock i) => setup.blockDGF i u) := by
  classical
  have hamb : ContinuousOn (setup.blockDGFAmbient i) (setup.XBlock i) := by
    exact (setup.hblockDGFAmbient_contDiffOn i).continuousOn
  have hvamb : Continuous (fun u : Set.Elem (setup.XBlock i) =>
      setup.blockDGFAmbient i u.1) := by
    exact hamb.comp_continuous continuous_subtype_val (fun u => u.2)
  have h_eq :
      (fun u : Set.Elem (setup.XBlock i) => setup.blockDGF i u) =
        fun u : Set.Elem (setup.XBlock i) => setup.blockDGFAmbient i u.1 := by
    funext u
    exact setup.blockDGF_eq_ambient i u
  simpa [h_eq] using hvamb

/-- If the ambient carrier is uniquely differentiable, the selected
`gradientWithin` used by the source-facing block DGF is continuous.

This is the direct Mathlib route: `ContDiffOn.continuousOn_fderivWithin`
supplies continuous within-derivatives under `UniqueDiffOn`, and the Riesz
equivalence transports them to `gradientWithin`. It aligns with the direct
Eq. (4.6.7) formula; the later helper isolates that the current setup has
convexity and a feasible anchor, but not ordinary full-dimensional
`UniqueDiffOn` for `X_i`. -/
private theorem blockFeasibleGradDGF_continuous_of_uniqueDiffOn
    (i : ι) (huniq : UniqueDiffOn ℝ (setup.XBlock i)) :
    Continuous (fun z : Set.Elem (setup.XBlock i) => setup.blockFeasibleGradDGF i z) := by
  classical
  letI := setup.instBlockNormed i
  letI := setup.instBlockInner i
  letI := setup.instBlockComplete i
  simpa [StochasticBlockMirrorDescentSetup.blockFeasibleGradDGF] using
    (continuous_gradientWithin_subtype_of_contDiffOn_uniqueDiffOn
      (X := setup.XBlock i) (ν := setup.blockDGFAmbient i)
      (setup.hblockDGFAmbient_contDiffOn i) huniq)

/-- Continuity of the affine-span carrier-gradient realization for the block DGF.

This is the SOptLib carrier-chart fallback for Eq. (4.6.7). It uses the source
feasible anchor `w₀ᵢ ∈ X_i`, convexity of `X_i`, the ambient `C¹` realization,
and `hblockDGF_eq_ambient` to feed `SOptLib.carrierGradientFrom_continuous`.
The remaining bridge to the literal block divergence is the pointwise
identification of the Bregman linearization term based on Mathlib's
`gradientWithin` with this affine-span carrier gradient. -/
private theorem blockCarrierGradientFrom_continuous
    (i : ι) :
    Continuous (fun z : Set.Elem (setup.XBlock i) =>
      SOptLib.carrierGradientFrom (setup.XBlock i)
        (fun u : Set.Elem (setup.XBlock i) => setup.blockDGF i u)
        (⟨setup.w₀ i, setup.hw₀_mem i⟩ : Set.Elem (setup.XBlock i)) z) := by
  classical
  letI := setup.instBlockNormed i
  letI := setup.instBlockInner i
  have hv_total : ContDiffOn ℝ 1
      (SOptLib.totalizeOn (setup.XBlock i)
        (fun u : Set.Elem (setup.XBlock i) => setup.blockDGF i u))
      (setup.XBlock i) := by
    exact (setup.hblockDGFAmbient_contDiffOn i).congr (by
      intro x hx
      rw [SOptLib.totalizeOn_of_mem (setup.XBlock i)
        (fun u : Set.Elem (setup.XBlock i) => setup.blockDGF i u) hx]
      exact setup.blockDGF_eq_ambient i ⟨x, hx⟩)
  exact SOptLib.carrierGradientFrom_continuous
    (setup.XBlock i) (fun u : Set.Elem (setup.XBlock i) => setup.blockDGF i u)
    (⟨setup.w₀ i, setup.hw₀_mem i⟩ : Set.Elem (setup.XBlock i))
    (setup.hXBlock_convex i) hv_total

/-- Carrier-chart gradients pair with feasible displacements like the ambient
`gradientWithin` over the same carrier.

This is the boundary-safe scalar bridge needed for Lan Eq. (4.6.7). Candidate
audit: `SOptLib.carrierGradientFrom_inner_eq_gradientWithin_intrinsicInterior`
only applies at intrinsic-interior base points, while
`SOptLib.carrierGradientFrom_continuous` gives the continuous chart gradient but
not the scalar equality with the source-facing `gradientWithin`; this local
variant proves the feasible-direction equality directly from chart composition
on `X`. -/
private theorem carrierGradientFrom_inner_eq_gradientWithin_on_feasible_direction
    {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℝ B]
    [FiniteDimensional ℝ B] [CompleteSpace B]
    {X : Set B} (v : {x : B // x ∈ X} → ℝ) (ν : B → ℝ)
    (anchor z x : {x : B // x ∈ X}) (hX : Convex ℝ X)
    (hνdiff : ContDiffOn ℝ 1 ν X)
    (hv_eq : ∀ y : {x : B // x ∈ X}, v y = ν y.1) :
    ⟪SOptLib.carrierGradientFrom X v anchor z, x.1 - z.1⟫_ℝ =
      ⟪gradientWithin ν X z.1, x.1 - z.1⟫_ℝ := by
  exact _root_.carrierGradientFrom_inner_eq_gradientWithin_on_feasible_direction
    (v := v) (ν := ν) (anchor := anchor) (z := z) (x := x) hX
    (hνdiff.differentiableOn_one z.1 z.2) hv_eq

/-- Block-specialized scalar bridge between the continuous carrier gradient and
the source-facing within-gradient in Eq. (4.6.7). -/
private theorem block_carrierGradientFrom_inner_eq_blockFeasibleGradDGF_inner
    (i : ι) (z x : Set.Elem (setup.XBlock i)) :
    ⟪SOptLib.carrierGradientFrom (setup.XBlock i)
        (fun u : Set.Elem (setup.XBlock i) => setup.blockDGF i u)
        (⟨setup.w₀ i, setup.hw₀_mem i⟩ : Set.Elem (setup.XBlock i)) z,
      x.1 - z.1⟫_ℝ =
      ⟪setup.blockFeasibleGradDGF i z, x.1 - z.1⟫_ℝ := by
  classical
  letI := setup.instBlockNormed i
  letI := setup.instBlockInner i
  letI := setup.instBlockComplete i
  rw [setup.blockFeasibleGradDGF_eq_ambientGradient i z]
  exact carrierGradientFrom_inner_eq_gradientWithin_on_feasible_direction
    (v := fun u : Set.Elem (setup.XBlock i) => setup.blockDGF i u)
    (ν := setup.blockDGFAmbient i)
    (anchor := (⟨setup.w₀ i, setup.hw₀_mem i⟩ : Set.Elem (setup.XBlock i)))
    (z := z) (x := x) (hX := setup.hXBlock_convex i)
    (hνdiff := setup.hblockDGFAmbient_contDiffOn i)
    (hv_eq := fun u => setup.blockDGF_eq_ambient i u)

/-- Block Bregman divergence `V_i(z, x)` from Eq. (4.6.7).

This is the restricted paper object on `X_i`. It uses SOptLib's canonical
carrier Bregman divergence with the ambient within-gradient bridge above,
aligning with `book/FOML/StochasticBlockMirrorDescent.json#/assumptions/3`:
`V_i(z,x)` is defined for `z, x ∈ X_i` by the literal formula using
`∇v_i(z)`. -/
noncomputable def blockDivergence (i : ι)
    (z x : Set.Elem (setup.XBlock i)) : ℝ := by
  letI := setup.instBlockNormed i
  letI := setup.instBlockInner i
  exact SOptLib.carrierBregmanDivergence
    (fun u : Set.Elem (setup.XBlock i) => setup.blockDGF i u)
    (setup.blockFeasibleGradDGF i) z x

/-- Pointwise equality between the source-facing block divergence and the
boundary-safe carrier-gradient Bregman kernel. -/
private theorem blockDivergence_eq_carrierGradientFrom_kernel
    (i : ι) (z x : Set.Elem (setup.XBlock i)) :
    setup.blockDivergence i z x =
      SOptLib.carrierBregmanDivergence
        (fun u : Set.Elem (setup.XBlock i) => setup.blockDGF i u)
        (fun u : Set.Elem (setup.XBlock i) =>
          SOptLib.carrierGradientFrom (setup.XBlock i)
            (fun y : Set.Elem (setup.XBlock i) => setup.blockDGF i y)
            (⟨setup.w₀ i, setup.hw₀_mem i⟩ : Set.Elem (setup.XBlock i)) u)
        z x := by
  classical
  letI := setup.instBlockNormed i
  letI := setup.instBlockInner i
  exact carrierBregmanDivergence_eq_of_gradient_pairing
    (v := fun u : Set.Elem (setup.XBlock i) => setup.blockDGF i u)
    (grad := setup.blockFeasibleGradDGF i)
    (grad' := fun u : Set.Elem (setup.XBlock i) =>
      SOptLib.carrierGradientFrom (setup.XBlock i)
        (fun y : Set.Elem (setup.XBlock i) => setup.blockDGF i y)
        (⟨setup.w₀ i, setup.hw₀_mem i⟩ : Set.Elem (setup.XBlock i)) u)
    z x (setup.block_carrierGradientFrom_inner_eq_blockFeasibleGradDGF_inner i z x).symm

/-- Defining formula for the block Bregman divergence in Eq. (4.6.7).

The public formula is stated with Mathlib's `gradientWithin` of the ambient
realization of the source DGF, so consumers see the literal differentiable
Bregman object rather than the route-local feasible-gradient helper used in the
implementation. -/
theorem blockDivergence_eq (i : ι) (z x : Set.Elem (setup.XBlock i)) :
    setup.blockDivergence i z x =
      setup.blockDGFAmbient i x.1 -
        (setup.blockDGFAmbient i z.1 +
          ⟪gradientWithin (setup.blockDGFAmbient i) (setup.XBlock i) z.1,
            x.1 - z.1⟫_ℝ) := by
  simpa [blockDivergence, blockFeasibleGradDGF] using
    blockBregmanDivergence_eq_gradientWithin_formula
      (X := setup.XBlock i)
      (v := fun u : Set.Elem (setup.XBlock i) => setup.blockDGF i u)
      (ν := setup.blockDGFAmbient i) z x
      (fun y => setup.blockDGF_eq_ambient i y)

/-- Segment lower-bound bridge for Lan Eq. (4.6.7).

SOptLib candidates `bregman_lower_bound_of_strongConvexOn_intrinsicInterior` and
`carrierBregmanDivergence_lower_bound_of_strongConvexOn_intrinsicInterior` were
checked and used as proof templates, but they lower-bound by the ambient Hilbert
norm on an intrinsic interior. The block theorem needs the literal paper
seminorm from `StrongConvexOnWithNorm` on `X_i`, so this helper is the
setup-independent specialization of the same first-order argument to the
explicit norm in Eq. (4.6.7). -/
private theorem bregman_lower_bound_of_strongConvexOnWithNorm_contDiffOn
    {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℝ B] [CompleteSpace B]
    {X : Set B} {ν : B → ℝ} {p : Seminorm ℝ B} {z x : B}
    (hX : Convex ℝ X) (hνdiff : ContDiffOn ℝ 1 ν X)
    (hstrong : StrongConvexOnWithNorm X 1 p ν) (hz : z ∈ X) (hx : x ∈ X) :
    (1 / 2 : ℝ) * p (x - z) ^ 2 ≤
      ν x - (ν z + ⟪gradientWithin ν X z, x - z⟫_ℝ) := by
  exact bregman_lower_bound_of_strongConvexOnWithSeminorm_differentiableWithinAt
    (X := X) (ν := ν) (p := p) (z := z) (x := x)
    hX
    (hνdiff.differentiableOn_one z hz)
    (by
      intro y hy w hw a b ha hb hab
      simpa [StrongConvexOnWithNorm] using
        hstrong (x := y) hy (y := w) hw (a := a) (b := b) ha hb hab)
    hz hx

/-- Backwards-compatible alias for the public Eq. (4.6.7) formula. -/
theorem blockDivergence_eq_ambient_formula
    (i : ι) (z x : Set.Elem (setup.XBlock i)) :
    setup.blockDivergence i z x =
      setup.blockDGFAmbient i x.1 -
        (setup.blockDGFAmbient i z.1 +
          ⟪gradientWithin (setup.blockDGFAmbient i) (setup.XBlock i) z.1,
            x.1 - z.1⟫_ℝ) := by
  exact setup.blockDivergence_eq i z x

/-- The paper's `1`-strong convexity assumption implies the Eq. (4.6.7)
Bregman lower bound used in block prox estimates. -/
theorem blockDivergence_lower_bound
    (i : ι) (z x : Set.Elem (setup.XBlock i)) :
    (1 / 2 : ℝ) * setup.blockPrimalNorm i (x.1 - z.1) ^ 2 ≤
      setup.blockDivergence i z x := by
  have hcore :=
    bregman_lower_bound_of_strongConvexOnWithNorm_contDiffOn
      (X := setup.XBlock i) (ν := setup.blockDGFAmbient i)
      (p := setup.blockPrimalNorm i)
      (setup.hXBlock_convex i) (setup.hblockDGFAmbient_contDiffOn i)
      (setup.hblockDGFAmbient_strongly_convex i) z.2 x.2
  rw [setup.blockDivergence_eq i z x]
  exact hcore

/-- Nonnegativity of the canonical block Bregman divergence from 1-strong convexity. -/
theorem blockDivergence_nonneg
    (i : ι) (z x : Set.Elem (setup.XBlock i)) :
    0 ≤ setup.blockDivergence i z x := by
  exact blockBregmanDivergence_nonneg_of_lower_bound
    (setup.blockDivergence i)
    (fun z x : Set.Elem (setup.XBlock i) => setup.blockPrimalNorm i (x.1 - z.1))
    z x (setup.blockDivergence_lower_bound i z x)

/-- Objective minimized by the sampled block mirror step in Eq. (4.6.14).

This specializes SOptLib's `proxObjective` to the sampled block carrier `X_i`,
with zero composite term and subtype evaluation. This aligns the
paper's one-block objective with the reusable mirror-prox objective while
keeping Eq. (4.6.14)'s sampled-block domain source-facing:
`book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec/steps/2/math`. -/
noncomputable def blockProxObjective (i : ι) :
    Set.Elem (setup.XBlock i) → setup.Block i → ℝ → Set.Elem (setup.XBlock i) → ℝ :=
  fun z g γ u => by
    letI := setup.instBlockNormed i
    letI := setup.instBlockInner i
    exact SOptLib.proxObjective
      (setup.blockDivergence i) (fun _ : Set.Elem (setup.XBlock i) => 0)
      (fun y : Set.Elem (setup.XBlock i) => y.1) z g γ u

/-- Expanded Eq. (4.6.14) formula for the sampled block prox objective. -/
theorem blockProxObjective_eq
    (i : ι) (z u : Set.Elem (setup.XBlock i)) (g : setup.Block i) (γ : ℝ) :
    setup.blockProxObjective i z g γ u =
      (by
        letI := setup.instBlockNormed i
        letI := setup.instBlockInner i
        exact ⟪g, u.1⟫_ℝ + γ⁻¹ * setup.blockDivergence i z u) := by
  letI := setup.instBlockNormed i
  letI := setup.instBlockInner i
  simpa [blockProxObjective] using
    proxObjective_zero_eq (V := setup.blockDivergence i)
      (eval := fun y : Set.Elem (setup.XBlock i) => y.1) z g γ u

/-- Compactness of the source block carrier `X_i`, viewed as the feasible subtype.

This is derived from Lan's bounded block-carrier assumption in §4.6.1.1, the
closedness of `X_i`, and finite-dimensional Euclidean block geometry. The proof is
left as infrastructure work, but the prox selector below consumes this compactness
through SOptLib's canonical compact argmin construction rather than a paper-local
choice witness. -/
theorem blockFeasible_compact (i : ι) :
    IsCompact (Set.univ : Set (Set.Elem (setup.XBlock i))) := by
  exact isCompact_univ_subtype_of_isClosed_isBounded
    (X := setup.XBlock i) (setup.hXBlock_closed i) (setup.hXBlock_bounded i)

/-- Joint continuity of the block Bregman kernel on the compact feasible carrier.

This is the continuity input required by `SOptLib.proxStep`; it follows from the
`ContDiffOn` DGF realization and the scalar feasible-displacement bridge from
the source-facing `gradientWithin` formula to the boundary-safe carrier
gradient. -/
theorem blockDivergence_continuous (i : ι) :
    Continuous (fun p : Set.Elem (setup.XBlock i) × Set.Elem (setup.XBlock i) =>
      setup.blockDivergence i p.1 p.2) := by
  classical
  letI := setup.instBlockNormed i
  letI := setup.instBlockInner i
  let carrierGrad : Set.Elem (setup.XBlock i) → setup.Block i := fun u =>
    SOptLib.carrierGradientFrom (setup.XBlock i)
      (fun y : Set.Elem (setup.XBlock i) => setup.blockDGF i y)
      (⟨setup.w₀ i, setup.hw₀_mem i⟩ : Set.Elem (setup.XBlock i)) u
  exact (evaluatedCarrierBregmanDivergence_continuous
    (nu := fun u : Set.Elem (setup.XBlock i) => setup.blockDGF i u)
    (grad := carrierGrad)
    (eval := fun u : Set.Elem (setup.XBlock i) => u.1)
    (setup.blockDGF_subtype_continuous i)
    (setup.blockCarrierGradientFrom_continuous i)
    continuous_subtype_val).congr (by
      intro p
      simpa [SOptLib.carrierBregmanDivergence, carrierGrad] using
        (setup.blockDivergence_eq_carrierGradientFrom_kernel i p.1 p.2).symm)

/-- Existence of a minimizer for the sampled block prox subproblem in Eq. (4.6.14).

This is a derived theorem, not setup data: later proof work must obtain it from
the block distance-generator assumptions and feasible-set geometry. -/
theorem exists_blockMirrorProx
    (i : ι) (z : Set.Elem (setup.XBlock i)) (g : setup.Block i) (γ : ℝ)
    (hγ : 0 < γ) :
    ∃ y : Set.Elem (setup.XBlock i),
      IsMinOn (setup.blockProxObjective i z g γ) Set.univ y := by
  classical
  letI := setup.instBlockNormed i
  letI := setup.instBlockInner i
  simpa [blockProxObjective] using
    (proxObjective_exists_isMinOn_compact
      (V := setup.blockDivergence i)
      (eval := fun y : Set.Elem (setup.XBlock i) => y.1)
      (setup.blockFeasible_compact i)
      continuous_subtype_val z
      ((setup.blockDivergence_continuous i).comp (continuous_const.prodMk continuous_id))
      g γ)

/-- Canonical block argmin selected by the one-block mirror step in Eq. (4.6.14).

The terminal construction is `SOptLib.proxStep`, whose implementation chooses the
argmin supplied by SOptLib's compact extreme-value theorem
`SOptLib.mirrorStep_exists_compact`. This replaces the former paper-local selector
field with a reusable Mathlib/SOptLib compact-argmin realization. -/
noncomputable def blockMirrorProxBlockRaw
    (i : ι) (z : Set.Elem (setup.XBlock i)) (g : setup.Block i) (γ : ℝ) :
    Set.Elem (setup.XBlock i) := by
  letI := setup.instBlockNormed i
  letI := setup.instBlockInner i
  exact SOptLib.proxStep
    (V := setup.blockDivergence i)
    (eval := fun y : Set.Elem (setup.XBlock i) => y.1)
    (setup.blockFeasible_compact i)
    (setup.blockDivergence_continuous i)
    continuous_subtype_val
    z g γ

/-- First-order variational inequality for the block prox subproblem, placed
before selector measurability so the unique-argmin proof can consume it.

SOptLib candidates considered: `mirrorObjective_argmin_variational` is a
general charted FOC, while `prox_scaled_variational_inequality_of_argmin` and
`carrierBregman_segment_difference_hasDerivWithinAt_zero` expose the same
segment-derivative route; this block-local statement keeps the exact
`gradientWithin` object used by `setup.blockDivergence_eq`. -/
private theorem block_prox_variational_from_isMinOn_core
    (setup : StochasticBlockMirrorDescentSetup ι S) (i : ι)
    (z y x : Set.Elem (setup.XBlock i)) (ζ : setup.Block i)
    (hmin :
      IsMinOn
        (fun u : Set.Elem (setup.XBlock i) =>
          ⟪ζ, u.1⟫_ℝ + setup.blockDivergence i z u)
        Set.univ y) :
    0 ≤
      ⟪ζ +
          gradientWithin (setup.blockDGFAmbient i) (setup.XBlock i) y.1 -
            gradientWithin (setup.blockDGFAmbient i) (setup.XBlock i) z.1,
        x.1 - y.1⟫_ℝ := by
  classical
  simpa using
    prox_variational_inequality_of_isMinOn_linear_bregman
        (hX_convex := setup.hXBlock_convex i)
        (nu := fun u : Set.Elem (setup.XBlock i) => setup.blockDGF i u)
        (nuAmbient := setup.blockDGFAmbient i)
        (grad := fun u : Set.Elem (setup.XBlock i) =>
          gradientWithin (setup.blockDGFAmbient i) (setup.XBlock i) u.1)
        z y x ζ
        (hnu_eq_segment := fun t ht => setup.blockDGF_eq_ambient i _)
        (hnu_diff := (setup.hblockDGFAmbient_contDiffOn i).differentiableOn_one y.1 y.2)
        (hgrad_apply := by
          simp [gradientWithin, InnerProductSpace.toDual_symm_apply])
        (by
          simpa [carrierBregmanDivergence_def, setup.blockDivergence_eq,
            setup.blockDGF_eq_ambient, sub_eq_add_neg, add_assoc, add_comm,
            add_left_comm] using hmin)

/-- Uniqueness of minimizers for the block paper mirror objective.

SOptLib candidates considered: `paperMirrorObjective_argmin_unique_of_strict_bregman`
matches the symmetric-variational route but uses an ambient-norm lower bound;
this block-local helper keeps Lan Eq. (4.6.7)'s paper norm via
`setup.blockDivergence_lower_bound` and `setup.blockPrimalNorm_isPaperNorm`. -/
private theorem block_paper_mirror_objective_argmin_unique
    (setup : StochasticBlockMirrorDescentSetup ι S) (i : ι)
    (x : Set.Elem (setup.XBlock i)) (g : setup.Block i) (γ : ℝ)
    (z z' : Set.Elem (setup.XBlock i))
    (hzmin :
      ∀ y : Set.Elem (setup.XBlock i),
        SOptLib.paperMirrorObjective (setup.blockDivergence i)
          (fun y : Set.Elem (setup.XBlock i) => y.1) x g γ z ≤
        SOptLib.paperMirrorObjective (setup.blockDivergence i)
          (fun y : Set.Elem (setup.XBlock i) => y.1) x g γ y)
    (hz'min :
      ∀ y : Set.Elem (setup.XBlock i),
        SOptLib.paperMirrorObjective (setup.blockDivergence i)
          (fun y : Set.Elem (setup.XBlock i) => y.1) x g γ z' ≤
        SOptLib.paperMirrorObjective (setup.blockDivergence i)
          (fun y : Set.Elem (setup.XBlock i) => y.1) x g γ y) :
    z = z' := by
  exact
    mirrorObjective_argmin_unique_of_bregman_seminorm_lower_bound
      (V := setup.blockDivergence i)
      (eval := fun y : Set.Elem (setup.XBlock i) => y.1)
      (grad := fun u : Set.Elem (setup.XBlock i) =>
        gradientWithin (setup.blockDGFAmbient i) (setup.XBlock i) u.1)
      (p := setup.blockPrimalNorm i)
      (heval_inj := by
        intro a b h
        exact Subtype.ext h)
      (x := x) (g := g) (γ := γ) (z := z) (z' := z')
      (hvariational := by
        intro a b hmin
        have hmin' :
            IsMinOn
              (fun u : Set.Elem (setup.XBlock i) =>
                ⟪γ • g, u.1⟫_ℝ + setup.blockDivergence i x u)
              Set.univ a := by
          rw [isMinOn_univ_iff]
          intro y
          have h := hmin y
          simpa [SOptLib.paperMirrorObjective, inner_smul_left] using h
        simpa using
          block_prox_variational_from_isMinOn_core setup i x a b (γ • g) hmin')
      (hsymm := by
        intro a b
        have hV :
            ∀ c d : Set.Elem (setup.XBlock i),
              setup.blockDivergence i c d =
                setup.blockDGFAmbient i d.1 - setup.blockDGFAmbient i c.1 -
                  ⟪gradientWithin (setup.blockDGFAmbient i) (setup.XBlock i) c.1,
                    d.1 - c.1⟫_ℝ := by
          intro c d
          rw [setup.blockDivergence_eq i c d]
          ring
        rw [hV a b, hV b a]
        have hrev : a.1 - b.1 = -(b.1 - a.1) := by
          abel
        rw [hrev, inner_neg_right, inner_sub_left]
        ring)
      (hlower := by
        intro a b
        exact setup.blockDivergence_lower_bound i a b)
      (hp_zero := by
        intro u hu
        exact (setup.blockPrimalNorm_isPaperNorm i u).1 hu)
      hzmin hz'min

/-- Measurability of the canonical compact-argmin block prox selector.

FILL should prove this from `proxStep_measurable_of_joint_continuous_unique`,
`blockDivergence_continuous`, compactness of `Set.Elem (setup.XBlock i)`, and strict
convexity/uniqueness of the one-block prox objective. -/
theorem blockMirrorProxBlockRaw_measurable (i : ι) :
    Measurable
      (fun p : Set.Elem (setup.XBlock i) × setup.Block i × ℝ =>
        setup.blockMirrorProxBlockRaw i p.1 p.2.1 p.2.2) := by
  classical
  letI := setup.instBlockNormed i
  letI := setup.instBlockInner i
  simpa [blockMirrorProxBlockRaw] using
    (SOptLib.mirrorObjective_argmin_selector_measurable_of_continuous_unique
      (V := setup.blockDivergence i)
      (eval := fun y : Set.Elem (setup.XBlock i) => y.1)
      (hcompact := setup.blockFeasible_compact i)
      (hV := setup.blockDivergence_continuous i)
      (heval := continuous_subtype_val)
      (hunique := block_paper_mirror_objective_argmin_unique setup i))

/-- The raw selected block prox point satisfies its defining argmin property. -/
theorem blockMirrorProxBlockRaw_isMinOn
    (i : ι) (z : Set.Elem (setup.XBlock i)) (g : setup.Block i) (γ : ℝ)
    (hγ : 0 < γ) :
    IsMinOn (setup.blockProxObjective i z g γ) Set.univ
      (setup.blockMirrorProxBlockRaw i z g γ) := by
  classical
  letI := setup.instBlockNormed i
  letI := setup.instBlockInner i
  simpa [blockProxObjective, SOptLib.positiveStepsizeMirrorProxBlock] using
    SOptLib.positiveStepsizeMirrorProxBlock_isMinOn_unscaled
      (V := setup.blockDivergence i)
      (eval := fun y : Set.Elem (setup.XBlock i) => y.1)
      (raw := setup.blockMirrorProxBlockRaw i)
      (by
        intro x g γ y
        simpa [blockMirrorProxBlockRaw] using
          SOptLib.proxStep_minimizes
            (V := setup.blockDivergence i)
            (eval := fun y : Set.Elem (setup.XBlock i) => y.1)
            (setup.blockFeasible_compact i)
            (setup.blockDivergence_continuous i)
            continuous_subtype_val x g γ y)
      z g γ hγ

/-- Replace a single block coordinate and reconstruct the full state.

No SOptLib match: searched "block coordinate product replacement projection",
scanned `SOptLib/Model/Iterates.lean`; none provides the paper-specific splice
operator required by Eq. (4.6.14), where non-sampled coordinates remain
definitionally unchanged. -/
noncomputable def blockReplacement
    (x : setup.StateSpace) (i : ι) (u : setup.Block i) : setup.StateSpace :=
  dependentProductCoordinateReplacement
    (ι := ι) (X := setup.StateSpace) (B := setup.Block)
    (fun y => WithLp.toLp 2 y) (fun j (z : setup.StateSpace) => z j) x i u

/-- The replaced coordinate is exactly the inserted block. -/
theorem blockReplacement_selected (x : setup.StateSpace) (i : ι) (u : setup.Block i) :
    setup.blockCoord i (setup.blockReplacement x i u) = u := by
  simpa [blockReplacement, blockCoord] using
    (dependentProductCoordinateReplacement_selected
      (assemble := fun y : ∀ j, setup.Block j => WithLp.toLp 2 y)
      (coord := fun j (z : setup.StateSpace) => z j)
      (hcoord_assemble := by
        intro y j
        simpa [blockCoord] using setup.blockCoord_assemble y j)
      (x := x) (i := i) (u := u))

/-- Coordinates other than the sampled block remain unchanged. -/
theorem blockReplacement_other
    (x : setup.StateSpace) (i j : ι) (u : setup.Block i) (hji : j ≠ i) :
    setup.blockCoord j (setup.blockReplacement x i u) = setup.blockCoord j x := by
  simpa [blockReplacement, blockCoord] using
    (dependentProductCoordinateReplacement_other
      (assemble := fun y : ∀ j, setup.Block j => WithLp.toLp 2 y)
      (coord := fun j (z : setup.StateSpace) => z j)
      (hcoord_assemble := by
        intro y j
        simpa [blockCoord] using setup.blockCoord_assemble y j)
      (x := x) (i := i) (j := j) (u := u) hji)

/-- Single-block replacement preserves product feasibility. -/
theorem blockReplacement_mem
    (x : setup.StateSpace) (i : ι) (u : setup.Block i)
    (hx : x ∈ setup.X) (hu : u ∈ setup.XBlock i) :
    setup.blockReplacement x i u ∈ setup.X := by
  simpa [blockReplacement, X] using
    (dependentProductCoordinateReplacement_mem
      (assemble := fun y : ∀ j, setup.Block j => WithLp.toLp 2 y)
      (coord := fun j (z : setup.StateSpace) => z j)
      (hcoord_assemble := by
        intro y j
        simpa [blockCoord] using setup.blockCoord_assemble y j)
      (XBlock := setup.XBlock) (x := x) (i := i) (u := u) hx hu)


/-- Full-state mirror-descent update obtained by splicing the selected block argmin
into the sampled coordinate and leaving all other coordinates unchanged. -/
noncomputable def blockMirrorProx
    (i : ι) (x : setup.FeasibleState) (g : setup.Block i) (γ : ℝ) (hγ : 0 < γ) :
    setup.FeasibleState :=
  blockMirrorUpdate
    (X := setup.X) (XBlock := setup.XBlock)
    (coord := fun i y => setup.blockCoord i y)
    (replace := fun i y u => setup.blockReplacement y i u)
    (replace_mem := by
      intro i y u hy hu
      exact setup.blockReplacement_mem y i u hy hu)
    (coord_mem := by
      intro i y hy
      simpa [blockCoord] using hy i)
    (blockProx := setup.blockMirrorProxBlockRaw)
    i x g γ


/-- The updated sampled coordinate is the block argmin from Eq. (4.6.14). -/
theorem blockMirrorProx_selected
    (i : ι) (x : setup.FeasibleState) (g : setup.Block i) (γ : ℝ) (hγ : 0 < γ) :
    setup.blockCoord i (setup.blockMirrorProx i x g γ hγ).1 =
      (setup.blockMirrorProxBlockRaw i
        ⟨setup.blockCoord i x.1, by simpa [blockCoord] using x.2 i⟩ g γ).1 := by
  simpa [blockMirrorProx] using
    (blockMirrorUpdate_selected
      (X := setup.X) (XBlock := setup.XBlock)
      (coord := fun i y => setup.blockCoord i y)
      (replace := fun i y u => setup.blockReplacement y i u)
      (replace_mem := by
        intro i y u hy hu
        exact setup.blockReplacement_mem y i u hy hu)
      (coord_mem := by
        intro i y hy
        simpa [blockCoord] using hy i)
      (replace_selected := by
        intro i y u
        exact setup.blockReplacement_selected y i u)
      (blockProx := setup.blockMirrorProxBlockRaw)
      i x g γ)

/-- Non-sampled coordinates are definitionally unchanged in Eq. (4.6.14). -/
theorem blockMirrorProx_other
    (i j : ι) (x : setup.FeasibleState) (g : setup.Block i) (γ : ℝ)
    (hγ : 0 < γ) (hji : j ≠ i) :
    setup.blockCoord j (setup.blockMirrorProx i x g γ hγ).1 = setup.blockCoord j x.1 := by
  simpa [blockMirrorProx] using
    (blockMirrorUpdate_other
      (X := setup.X) (XBlock := setup.XBlock)
      (coord := fun i y => setup.blockCoord i y)
      (replace := fun i y u => setup.blockReplacement y i u)
      (replace_mem := by
        intro i y u hy hu
        exact setup.blockReplacement_mem y i u hy hu)
      (coord_mem := by
        intro i y hy
        simpa [blockCoord] using hy i)
      (replace_other := by
        intro i j y u hji
        exact setup.blockReplacement_other y i j u hji)
      (blockProx := setup.blockMirrorProxBlockRaw)
      i j x g γ hji)

/-- The sampled coordinate of the full update satisfies the block argmin property. -/
theorem blockMirrorProx_selected_isMinOn
    (i : ι) (x : setup.FeasibleState) (g : setup.Block i) (γ : ℝ) (hγ : 0 < γ) :
    IsMinOn
      (setup.blockProxObjective i
        ⟨setup.blockCoord i x.1, by simpa [blockCoord] using x.2 i⟩ g γ)
      Set.univ
      ⟨setup.blockCoord i (setup.blockMirrorProx i x g γ hγ).1,
        by
          rw [setup.blockMirrorProx_selected i x g γ hγ]
          exact (setup.blockMirrorProxBlockRaw i
            ⟨setup.blockCoord i x.1, by simpa [blockCoord] using x.2 i⟩ g γ).2⟩ := by
  simpa [blockMirrorProx] using
    (blockMirrorUpdate_selected_isMinOn
      (X := setup.X) (XBlock := setup.XBlock)
      (coord := fun i y => setup.blockCoord i y)
      (replace := fun i y u => setup.blockReplacement y i u)
      (replace_mem := by
        intro i y u hy hu
        exact setup.blockReplacement_mem y i u hy hu)
      (coord_mem := by
        intro i y hy
        simpa [blockCoord] using hy i)
      (replace_selected := by
        intro i y u
        exact setup.blockReplacement_selected y i u)
      (blockProx := setup.blockMirrorProxBlockRaw)
      (blockObjective := setup.blockProxObjective)
      i x g γ
      (setup.blockMirrorProxBlockRaw_isMinOn i
        ⟨setup.blockCoord i x.1, by simpa [blockCoord] using x.2 i⟩ g γ hγ))

set_option maxHeartbeats 800000

/-- Feasible block coordinate of a feasible product state.

This is a route-local naming helper for the repeated carrier proof in the
Eq. (4.6.14) splice; SOptLib has coordinate projection primitives, but not this
paper-specific feasible block subtype packaging. -/
private noncomputable def feasibleBlockCoord
    (setup : StochasticBlockMirrorDescentSetup ι S) (i : ι)
    (x : setup.FeasibleState) : Set.Elem (setup.XBlock i) :=
  ⟨setup.blockCoord i x.1, by simpa [blockCoord] using x.2 i⟩

/-- Finite singleton-fiber dispatch preserves measurability.

Mathlib/SOptLib candidates considered: `Measurable.piecewise` handles one
binary split and `exists_measurable_piecewise` handles countable measurable
covers; no existing SOptLib lemma packages the finite selector dispatch needed
for the sampled block in Lan Eq. (4.6.14), so this helper specializes the
countable-cover API to finite singleton fibers. -/
private theorem finite_dispatch_measurable
    {α β δ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace δ]
    [Fintype δ] [MeasurableSingletonClass δ] [Nonempty δ]
    {idx : α → δ} {f : δ → α → β}
    (hidx : Measurable idx) (hf : ∀ i, Measurable (f i)) :
    Measurable (fun a => f (idx a) a) := by
  exact measurable_countable_dispatch hidx hf

/-- Fixed-block feasible coordinate replacement is measurable.

SOptLib candidates considered: `measurable_pi_subtype_restrict_of_mem_map`
packages finite coordinate restriction, while this paper needs the literal
Eq. (4.6.14) one-coordinate splice into `setup.FeasibleState`; the proof uses
`measurable_pi_lambda` with `blockReplacement_selected`/`other` behavior
encoded by `Function.update`. -/
private theorem block_replacement_feasible_measurable_fixed
    (setup : StochasticBlockMirrorDescentSetup ι S) (i : ι) :
    Measurable
      (fun p : setup.FeasibleState × Set.Elem (setup.XBlock i) =>
        (fun (x : setup.FeasibleState) (i : ι) (u : Set.Elem (setup.XBlock i)) =>
  Subtype.map
    (fun y : setup.StateSpace => setup.blockReplacement y i u.1)
    (fun y hy => setup.blockReplacement_mem y i u.1 hy u.2)
    x) p.1 i p.2) := by
  classical
  simpa [blockReplacement] using
    (feasible_coordinate_replacement_measurable
      (assemble := fun y : ∀ j, setup.Block j => WithLp.toLp 2 y)
      (coord := fun j => setup.blockCoord j)
      (X := setup.X) (i := i) (X_i := setup.XBlock i)
      (hassemble :=
        WithLp.measurable_toLp 2
          (∀ j : ι, EuclideanSpace ℝ (Fin (setup.blockDim j))))
      (hcoord := by
        intro j
        exact (setup.blockCoord j).measurable.comp measurable_subtype_coe)
      (replace_mem := by
        intro y u hy hu
        simpa [blockReplacement, blockCoord] using setup.blockReplacement_mem y i u hy hu))

/-- Fixed-block center coordinate as a feasible block is measurable.

This is the coordinate-projection component of the fixed-block form of
Eq. (4.6.14), separated so the full update proof does not repeatedly normalize
the feasible subtype construction. -/
private theorem block_center_measurable_fixed
    (setup : StochasticBlockMirrorDescentSetup ι S) (i : ι) :
    Measurable
      (fun p : setup.FeasibleState × S =>
        setup.feasibleBlockCoord i p.1) := by
  refine Measurable.subtype_mk ?_
  change Measurable (fun p : setup.FeasibleState × S => setup.blockCoord i p.1.1)
  exact (setup.blockCoord i).measurable.comp
    (measurable_subtype_coe.comp measurable_fst)

/-- Fixed-block stochastic oracle coordinate is measurable.

This applies the setup's jointly measurable stochastic oracle kernel
`hgradL_measurable` and then the continuous linear block coordinate projection;
it is the block version of the sampled-oracle measurability bridge. -/
private theorem gradBlock_measurable_fixed
    (setup : StochasticBlockMirrorDescentSetup ι S) (i : ι) :
    Measurable
      (fun p : setup.FeasibleState × S => setup.blockCoord i (setup.gradL p.1.1 p.2)) := by
  exact oracle_postcomp_measurable_of_joint_measurable
    (m := (by infer_instance : MeasurableSpace (setup.FeasibleState × S)))
    (oracle := setup.gradL)
    (coord := setup.blockCoord i)
    (x := fun p : setup.FeasibleState × S => p.1.1)
    (ξ := fun p : setup.FeasibleState × S => p.2)
    setup.hgradL_measurable
    (setup.blockCoord i).measurable
    (measurable_subtype_coe.comp measurable_fst)
    measurable_snd

/-- Fixed-block prox selector is measurable before splicing into the full state.

This is the direct use of the previously proved raw compact selector
measurability, aligned with Lan Eq. (4.6.14)'s one-block prox subproblem. -/
private theorem blockMirrorProxBlockRaw_measurable_fixed
    (setup : StochasticBlockMirrorDescentSetup ι S) (t : ℕ) (i : ι) :
    Measurable
      (fun p : setup.FeasibleState × S =>
        setup.blockMirrorProxBlockRaw i
          (setup.feasibleBlockCoord i p.1)
          (setup.blockCoord i (setup.gradL p.1.1 p.2)) (setup.η t)) := by
  have hraw := setup.blockMirrorProxBlockRaw_measurable i
  have hcomp :=
    Measurable.proxStep_comp (prox := setup.blockMirrorProxBlockRaw i)
      hraw (block_center_measurable_fixed setup i)
      (gradBlock_measurable_fixed setup i)
      (measurable_const : Measurable (fun _ : setup.FeasibleState × S => setup.η t))
  simpa using hcomp

/-- Fixed-block full mirror update remains measurable after replacing the
sample input by the first component of the same-time `(sample, block)` pair.

This is the direct projection form consumed by the finite dispatch over the
sampled block in Eq. (4.6.14); it combines the fixed-block prox selector with
the feasible coordinate splice, not a new source-facing assumption. -/
private theorem fixed_block_mirror_update_sample_pair_measurable
    (setup : StochasticBlockMirrorDescentSetup ι S) (t : ℕ) (i : ι) :
    Measurable
      (fun p : setup.FeasibleState × (S × ι) =>
        (fun (x : setup.FeasibleState) (i : ι) (u : Set.Elem (setup.XBlock i)) =>
  Subtype.map
    (fun y : setup.StateSpace => setup.blockReplacement y i u.1)
    (fun y hy => setup.blockReplacement_mem y i u.1 hy u.2)
    x) p.1 i
          (setup.blockMirrorProxBlockRaw i
            (setup.feasibleBlockCoord i p.1)
            (setup.blockCoord i (setup.gradL p.1.1 p.2.1)) (setup.η t))) := by
  exact
    fixed_coordinate_prox_update_measurable_of_components
      (center := setup.feasibleBlockCoord i)
      (oracle := fun x : setup.FeasibleState => fun s : S => setup.gradL x.1 s)
      (coord := setup.blockCoord i)
      (prox := setup.blockMirrorProxBlockRaw i)
      (replace := fun x u =>
        (fun (x : setup.FeasibleState) (i : ι) (u : Set.Elem (setup.XBlock i)) =>
  Subtype.map
    (fun y : setup.StateSpace => setup.blockReplacement y i u.1)
    (fun y hy => setup.blockReplacement_mem y i u.1 hy u.2)
    x) x i u)
      (query := fun p : setup.FeasibleState × (S × ι) => p.1)
      (sample := fun p : setup.FeasibleState × (S × ι) => p.2.1)
      (step := fun _ : setup.FeasibleState × (S × ι) => setup.η t)
      (by
        refine Measurable.subtype_mk ?_
        change Measurable (fun x : setup.FeasibleState => setup.blockCoord i x.1)
        exact (setup.blockCoord i).measurable.comp measurable_subtype_coe)
      (by
        exact setup.hgradL_measurable.comp
          ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd))
      (setup.blockCoord i).measurable
      (setup.blockMirrorProxBlockRaw_measurable i)
      (block_replacement_feasible_measurable_fixed setup i)
      measurable_fst measurable_snd.fst measurable_const

/-- Block mirror-descent state recursion.

At time `t + 1`, the method samples one block, applies the abstract one-block
prox update through `blockMirrorProx`, and updates the incremental averaging
state only on the sampled block. -/
noncomputable def process :
    ℕ → StochasticBlockSamplePath S ι → StochasticBlockMirrorDescentState ι setup.FeasibleState setup.Block
  :=
    stochasticBlockMirrorDescentProcess
      (instAdd := fun i => by
        letI := setup.instBlockNormed i
        infer_instance)
      (instSMul := fun i => by
        letI := setup.instBlockNormed i
        letI := setup.instBlockInner i
        infer_instance)
      (init := ⟨setup.w₀, setup.w₀_mem⟩)
      (zeroBlock := fun i => by
        letI := setup.instBlockNormed i
        exact 0)
      (sampleBlock := setup.block)
      (oracle := fun i t x ω => setup.blockCoord i (setup.gradL x.1 (setup.ξ t ω)))
      (blockCoord := fun i x => setup.blockCoord i x.1)
      (blockUpdate := fun i t x g _ => setup.blockMirrorProx i x g (setup.η t) (setup.hη_pos t))
      (η := setup.η)
      (θ := setup.θ)


/-- Iterates generated by Algorithm 4.5 remain in the product feasible set `X`. -/
theorem xIter_mem (t : ℕ) (ω : StochasticBlockSamplePath S ι) : (SOptLib.iterateProcessView (fun t ω => (setup.process t ω).x.1)) t ω ∈ setup.X := by
  exact (setup.process t ω).x.2

/-! Adaptedness staging for Eq. (4.6.21).

The recursive measurability part aligns with Lan's strict-past conditioning
`ζ_[k-1]`; after reconstruction the remaining hard leaf is the finite
dependent-coordinate measurability bridge for splicing the measurable
Eq. (4.6.14) selector into the sampled block. -/

/-- The full sampled block update map is measurable once the selected block
argmin is known to be a measurable selector.

This is the exact selector regularity subgoal needed for adaptedness of
`xIter`. SOptLib candidates considered: `Measurable.proxStep_comp`,
`proxStep_measurable_of_joint_continuous_unique`, and
`measurable_proxStep_of_continuous_state_oracle`; the selected block is now
`setup.blockMirrorProxBlockRaw`, a `SOptLib.proxStep` specialization, so FILL
should combine `setup.blockMirrorProxBlockRaw_measurable`,
`setup.hgradL_measurable`, and finite case analysis on the sampled block. -/
private theorem blockMirrorProx_sample_update_measurable
    (setup : StochasticBlockMirrorDescentSetup ι S) (t : ℕ) :
    Measurable (fun p : setup.FeasibleState × (S × ι) =>
      setup.blockMirrorProx p.2.2 p.1
        (setup.blockCoord p.2.2 (setup.gradL p.1.1 p.2.1))
        (setup.η t) (setup.hη_pos t)) := by
  classical
  haveI : Nonempty ι := by
    by_cases h : Nonempty ι
    · exact h
    · exfalso
      haveI : IsEmpty ι := ⟨fun i => h ⟨i⟩⟩
      have hsum0 : Finset.sum Finset.univ setup.p = 0 := by simp
      linarith [setup.hp_sum, hsum0]
  change Measurable
    (fun p : setup.FeasibleState × (S × ι) =>
      (fun (x : setup.FeasibleState) (i : ι) (u : Set.Elem (setup.XBlock i)) =>
  Subtype.map
    (fun y : setup.StateSpace => setup.blockReplacement y i u.1)
    (fun y hy => setup.blockReplacement_mem y i u.1 hy u.2)
    x) p.1 p.2.2
        (setup.blockMirrorProxBlockRaw p.2.2
          (setup.feasibleBlockCoord p.2.2 p.1)
          (setup.blockCoord p.2.2 (setup.gradL p.1.1 p.2.1)) (setup.η t)))
  refine finite_dispatch_measurable
    (idx := fun p : setup.FeasibleState × (S × ι) => p.2.2)
    (f := fun i p =>
      (fun (x : setup.FeasibleState) (i : ι) (u : Set.Elem (setup.XBlock i)) =>
  Subtype.map
    (fun y : setup.StateSpace => setup.blockReplacement y i u.1)
    (fun y hy => setup.blockReplacement_mem y i u.1 hy u.2)
    x) p.1 i
        (setup.blockMirrorProxBlockRaw i
          (setup.feasibleBlockCoord i p.1)
          (setup.blockCoord i (setup.gradL p.1.1 p.2.1)) (setup.η t)))
    ?hidx ?hf
  · exact measurable_snd.snd
  · intro i
    exact fixed_block_mirror_update_sample_pair_measurable setup t i

/-- The feasible iterate process is adapted to the strict-prefix sample
filtration, modulo the concrete prox-selector measurability leaf above.

This specializes `SOptLib.recursiveProcess_measurable_wrt_strictPast` to the
Algorithm 4.5 recursion and consumes the canonical strict-prefix filtration
generated by the sample-pair stream. -/
theorem xFeasibleIter_measurable_sampleFiltration
    (setup : StochasticBlockMirrorDescentSetup ι S) (k : ℕ) :
    Measurable[setup.sampleFiltration k] (fun ω => (setup.process k ω).x) := by
  classical
  let step : ℕ → setup.FeasibleState → (S × ι) → setup.FeasibleState :=
    fun t x q =>
      setup.blockMirrorProx q.2 x
        (setup.blockCoord q.2 (setup.gradL x.1 q.1))
        (setup.η t) (setup.hη_pos t)
  have hrec :
      ∀ n, n ≤ k →
        Measurable[setup.sampleFiltration k] (fun ω => (setup.process n ω).x) := by
    refine SOptLib.recursiveProcess_measurable_wrt_strictPast
      (past := fun k : ℕ =>
        (setup.sampleFiltration k :
          MeasurableSpace (StochasticBlockSamplePath S ι)))
      (process := fun n ω => (setup.process n ω).x)
      (driver := setup.samplePair)
      (step := step)
      (k := k) (N := k) ?_ ?_ ?_ ?_
    · simp [StochasticBlockMirrorDescentSetup.process, stochasticBlockMirrorDescentProcess]
    · intro n hn _hproc
      refine Measurable.of_comap_le ?_
      change
        MeasurableSpace.comap (setup.samplePair n)
            (by infer_instance : MeasurableSpace (S × ι)) ≤
          (setup.sampleFiltration k :
            MeasurableSpace (StochasticBlockSamplePath S ι))
      rw [StochasticBlockMirrorDescentSetup.sampleFiltration, SOptLib.filtration_seq]
      exact le_iSup_of_le n
        (le_iSup_of_le (Nat.lt_of_succ_le hn) le_rfl)
    · intro n _hn
      simpa [step] using setup.blockMirrorProx_sample_update_measurable n
    · intro n _hn
      funext ω
      rfl
  exact hrec k le_rfl

/-- The primal iterate `x_k` is measurable with respect to the strict-past
sample filtration, once the feasible-state adaptedness bridge is available. -/
theorem xIter_measurable_sampleFiltration
    (setup : StochasticBlockMirrorDescentSetup ι S) (k : ℕ) :
    Measurable[setup.sampleFiltration k] (fun ω => (SOptLib.iterateProcessView (fun t ω => (setup.process t ω).x.1)) k ω) := by
  simpa [SOptLib.iterateProcessView] using
    (measurable_subtype_coe.comp
      (xFeasibleIter_measurable_sampleFiltration setup k))

/-- Paper-facing averaging counter `u_i`.

The recursive state stores the zero-based realization used to index Lean
arrays; Algorithm 4.5 initializes `u_i = 1` and then sets `u_{i_k} = k + 1`.
This definition exposes the one-based paper counter by adding one to the
internal state counter. -/
noncomputable def uPaper (t : ℕ) (ω : StochasticBlockSamplePath S ι) (i : ι) : ℕ :=
  SOptLib.oneBasedCounter (fun t ω i => (setup.process t ω).u i) t ω i

/-- Algorithm 4.5 initialization: `u_i = 1`. -/
theorem uPaper_init (ω : StochasticBlockSamplePath S ι) (i : ι) :
    setup.uPaper 0 ω i = 1 := by
  exact SOptLib.oneBasedCounter_init (fun t ω i => (setup.process t ω).u i)
    ω i (by simp [process, stochasticBlockMirrorDescentProcess])

/-- Algorithm 4.5 counter update on the sampled block: after zero-based step
`t`, the one-based counter is `t + 2`, i.e. paper `k + 1`. -/
theorem uPaper_update_selected (t : ℕ) (ω : StochasticBlockSamplePath S ι) :
    setup.uPaper (t + 1) ω (setup.block t ω) = t + 2 := by
  simpa [uPaper] using
    (SOptLib.oneBasedCounter_update_selected
      (fun t ω i => (setup.process t ω).u i) setup.block
      (next := fun t => t + 1) (t := t) (ω := ω)
      (updatedValue := t + 1)
      (by
        ext i
        simp [process, stochasticBlockMirrorDescentProcess]))

/-- Algorithm 4.5 leaves the non-sampled block counters unchanged. -/
theorem uPaper_update_other (t : ℕ) (ω : StochasticBlockSamplePath S ι) {j : ι}
    (hji : j ≠ setup.block t ω) :
    setup.uPaper (t + 1) ω j = setup.uPaper t ω j := by
  exact SOptLib.oneBasedCounter_update_other
    (fun t ω i => (setup.process t ω).u i) setup.block
    (next := fun t => t + 1) (t := t) (ω := ω) (j := j)
    (updatedValue := t + 1)
    (by
      ext i
      simp [process, stochasticBlockMirrorDescentProcess])
    hji

/-- Positive paper time indices `k ≥ 1` for Algorithm 4.5.

This uses SOptLib's lower-bounded natural-time subtype so the paper's
`k = 1, ..., N` output window is explicit rather than hidden behind a
zero-based `Finset.range` convention. -/
abbrev PositiveTime : Type :=
  {k : ℕ // 1 ≤ k}

/-- Convert a paper index `k ≥ 1` to the zero-based recursive-process index. -/
def zeroBasedIndex (k : PositiveTime) : ℕ :=
  k.1 - 1

/-- Paper-facing iterate `x_k`, with `x_1` realized by the initial process state. -/
noncomputable def xPaper (k : PositiveTime) (ω : StochasticBlockSamplePath S ι) : setup.StateSpace :=
  (SOptLib.iterateProcessView (fun t ω => (setup.process t ω).x.1)) (zeroBasedIndex k) ω

/-- Paper-facing stepsize `γ_k` over positive time. -/
def paperEta (k : PositiveTime) : ℝ :=
  SOptLib.positiveTimeStepSize setup.η k

/-- Paper-facing averaging weight `θ_k` over positive time. -/
def paperTheta (k : PositiveTime) : ℝ :=
  setup.θ (zeroBasedIndex k)

/-- Positive-time form of the paper condition `θ_k = γ_k`, Eq. (4.6.16). -/
theorem paperTheta_eq_paperEta (k : PositiveTime) :
    setup.paperTheta k = setup.paperEta k := by
  exact SOptLib.positiveTimeWeight_eq_stepSize setup.η setup.θ setup.hθ_eq_η k

/-- Positive-time averaging weights are nonnegative, derived from `γ_k > 0`
and `θ_k = γ_k` rather than carried as a setup assumption. -/
theorem paperTheta_nonneg (k : PositiveTime) : 0 ≤ setup.paperTheta k :=
  by
    simpa [StochasticBlockMirrorDescentSetup.paperTheta,
      StochasticBlockMirrorDescentSetup.zeroBasedIndex] using
      SOptLib.positiveTimeWeight_nonneg setup.θ setup.theta_nonneg k

/-- Positive-time output window `{1, ..., N}` from Eq. (4.6.15), realized by
SOptLib's reusable positive-time output-window constructor. -/
def outputTimes (N : ℕ) : Finset PositiveTime :=
  SOptLib.positiveTimeOutputWindowTimes 1 N (le_refl 1)

/-- Paper denominator `∑_{k=1}^N θ_k` for the weighted average. -/
def outputThetaSum (N : ℕ) : ℝ :=
  Finset.sum (outputTimes N) setup.paperTheta

/-- Paper denominator `∑_{k=1}^N γ_k` used in Theorem 4.12. -/
def outputEtaSum (N : ℕ) : ℝ :=
  Finset.sum (outputTimes N) setup.paperEta

/-- Aggregate weighted block-Bregman potential
`V(z, x) = ∑ᵢ pᵢ⁻¹ Vᵢ(z^{(i)}, x^{(i)})` on feasible product states.

No SOptLib match: searched "weighted block Bregman aggregate potential",
scanned `SOptLib/Model/Bregman.lean` and `SOptLib/Layer1/Telescope.lean`;
SOptLib provides the carrier Bregman kernel and telescope bridges, but not
Lan's block-sampling weighted product potential from
`book/FOML/StochasticBlockMirrorDescent.json#/main_theorem/proof/0`. -/
noncomputable def aggregatePotential (z x : setup.FeasibleState) : ℝ :=
  weightedBlockBregmanPotential
    (fun i => Set.Elem (setup.XBlock i))
    setup.p
    (fun i y => ⟨setup.blockCoord i y.1, by simpa [blockCoord] using y.2 i⟩)
    setup.blockDivergence
    z x

/-- Weighted average output `x̄_N` as SOptLib's finite normalized weighted sum.

This aligns Algorithm 4.5 Eq. (4.6.15) with the reusable
`weightedOutputAverage` object. The ambient-valued wrapper is kept because this
file's theorem statements are stated in `setup.StateSpace`; membership in `X`
is exposed by the SOptLib subtype construction once iterate feasibility is
available. -/
noncomputable def weightedAverageSubtype
    (N : ℕ)
    (hx_mem : ∀ t, t ∈ outputTimes N → ∀ ω, setup.xPaper t ω ∈ setup.X)
    (hweightSum_pos : 0 < setup.outputThetaSum N) :
    StochasticBlockSamplePath S ι → {y : setup.StateSpace // y ∈ setup.X} :=
  SOptLib.weightedOutputAverage setup.X (fun _ : Unit => outputTimes N) setup.paperTheta
    setup.xPaper (fun _ : Unit => setup.outputThetaSum N)
    setup.X_convex
    (fun _ t _ => setup.paperTheta_nonneg t)
    (fun _ t ht ω => hx_mem t ht ω)
    (fun _ => hweightSum_pos)
    (fun _ => rfl)
    ()

/-- Weighted average output `x̄_N` from Eq. (4.6.15), indexed over `k = 1, ..., N`. -/
noncomputable def weightedAverage (N : ℕ) (ω : StochasticBlockSamplePath S ι) : setup.StateSpace :=
  SOptLib.weightedAverageOutputValue (fun _ : Unit => outputTimes N) setup.paperTheta
    setup.xPaper (fun _ : Unit => setup.outputThetaSum N) () ω

/-- Noise term `δ_k` from Eq. (4.6.19). -/
noncomputable def delta (x : setup.StateSpace) (k : ℕ) (ω : StochasticBlockSamplePath S ι) : ℝ :=
  blockOracleResidualInner setup.block setup.ξ (SOptLib.iterateProcessView (fun t ω => (setup.process t ω).x.1))
    (fun i x s => PiLp.single 2 i (setup.blockCoord i (setup.gradL x s))) setup.g setup.p x k ω

/-- Quadratic stochastic term `δ̄_k` from Eq. (4.6.19). -/
noncomputable def deltaBar (k : ℕ) (ω : StochasticBlockSamplePath S ι) : ℝ :=
  blockOracleQuadraticTerm setup.block setup.ξ (SOptLib.iterateProcessView (fun t ω => (setup.process t ω).x.1))
    (fun i x s => setup.blockCoord i (setup.gradL x s))
    (fun i => SOptLib.canonicalDualNorm (setup.blockPrimalNorm i)) setup.p k ω

end StochasticBlockMirrorDescentSetup

/-! Source-derived deterministic block-dual infrastructure. -/

/-- The canonical support-form dual norm is nonnegative.

Candidate audit: `canonicalDualNorm_eq_sSup`,
`canonical_dual_support_set_bddAbove`, and
`abs_inner_le_canonicalDualNorm_mul_primal` were checked; none states
nonnegativity directly, while this is the support-set `0 ∈ unit ball` fact
needed for the Jensen/L2 route to Lan Eq. (4.6.4). -/
private theorem canonicalDualNormFromPrimal_nonneg
    {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℝ B]
    [FiniteDimensional ℝ B]
    (p : Seminorm ℝ B) (hp : IsPaperNorm p) (ζ : B) :
    0 ≤ canonicalDualNormFromPrimal p ζ := by
  simpa [canonicalDualNormFromPrimal] using SOptLib.canonicalDualNorm_nonneg p ζ

/-- Jensen bridge for the canonical paper dual norm, proved from its support
function representation.

Candidate audit: the pre-searched probability-transfer and martingale lemmas
(`integral_comp_le_of_indep_fixed_integral_bound`,
`integral_finset_sum_const_mul_eq_zero`, oracle measurability helpers) concern
independent random-query transport or centered sums. Search for "canonical dual
norm integral Jensen support" found only the local support formula and Cauchy
bound, so this route-local helper proves the literal support-function Jensen
step used to derive Lan Eq. (4.6.4)'s deterministic mean bound. -/
private theorem canonical_dual_norm_integral_le_integral
    {Ω B : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup B] [InnerProductSpace ℝ B] [CompleteSpace B]
    [FiniteDimensional ℝ B]
    {μ : Measure Ω} (p : Seminorm ℝ B) (hp : IsPaperNorm p)
    {Y : Ω → B}
    (hY : Integrable Y μ)
    (hdual : Integrable (fun ω => canonicalDualNormFromPrimal p (Y ω)) μ) :
    canonicalDualNormFromPrimal p (∫ ω, Y ω ∂μ) ≤
      ∫ ω, canonicalDualNormFromPrimal p (Y ω) ∂μ := by
  have hdual' : Integrable (fun ω => SOptLib.canonicalDualNorm p (Y ω)) μ := by
    simpa [canonicalDualNormFromPrimal] using hdual
  simpa [canonicalDualNormFromPrimal] using
    (SOptLib.canonicalDualNorm_integral_le_integral (p := p) (Y := Y)
      (fun ω => canonical_dual_support_set_bddAbove p hp (Y ω)) hY hdual')

/-- A nonnegative scalar random variable with integrable square is a.e.
strongly measurable.

Candidate audit: `integrable_of_integrable_norm_sq` gives L2-to-L1 only after
measurability is known, and `memLp_two_iff_integrable_sq` also requires
`AEStronglyMeasurable Z μ`; this helper extracts that measurability from the
integrable square using `Z = sqrt (Z^2)` for nonnegative `Z`. -/
private theorem aestronglyMeasurable_of_integrable_sq_of_nonneg
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {Z : Ω → ℝ}
    (hZ2 : Integrable (fun ω => Z ω ^ 2) μ) (hZ_nonneg : ∀ ω, 0 ≤ Z ω) :
    AEStronglyMeasurable Z μ := by
  exact AEStronglyMeasurable.of_integrable_sq_of_nonneg hZ2
    (Filter.Eventually.of_forall hZ_nonneg)

/-- Scalar probability Jensen/Cauchy step: `(E Z)^2 ≤ E[Z^2]`.

Candidate audit: SOptLib search for "probability integral square Jensen
Cauchy Schwarz" did not expose a direct scalar lemma; Mathlib's variance API
(`ProbabilityTheory.variance_eq_sub`, `ProbabilityTheory.variance_nonneg`,
`MeasureTheory.memLp_two_iff_integrable_sq`) exactly supplies the contraction
once the square integrability and measurability of `Z` are available. -/
private theorem integral_nonnegative_sq_le_integral_sq
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Z : Ω → ℝ}
    (hZ_meas : AEStronglyMeasurable Z μ)
    (hZ2 : Integrable (fun ω => Z ω ^ 2) μ) :
    (∫ ω, Z ω ∂μ) ^ 2 ≤ ∫ ω, Z ω ^ 2 ∂μ := by
  exact sq_integral_le_integral_sq hZ_meas hZ2

/-! Source-derived deterministic block-dual bound from the unbiased block
oracle and the blockwise second-moment control in Eq. (4.6.4).

The source proof of Eq. (4.6.22) uses only the block quantities
`‖G_i(x, ξ)‖_{i,*}^2` and their bounds by `M_i^2`; it does not assert a
unit-constant ambient Hilbert-norm bound on `g x`. -/
theorem derived_block_norm_bounds
    (setup : StochasticBlockMirrorDescentSetup ι S)
    (x : setup.StateSpace) (hx : x ∈ setup.X) :
    ∀ i, SOptLib.canonicalDualNorm (setup.blockPrimalNorm i) (setup.gBlock i x) ^ 2 ≤ (setup.M i) ^ 2 := by
  intro i
  classical
  letI : IsProbabilityMeasure setup.oracleSampleLaw := setup.oracleSampleLaw_probability
  refine dualNorm_mean_sq_le_second_moment_bound
    (μ := setup.oracleSampleLaw) (p := setup.blockPrimalNorm i)
    (Y := fun s => setup.blockCoord i (setup.gradL x s))
    (target := setup.gBlock i x) (M := setup.M i)
    (fun s => canonical_dual_support_set_bddAbove
      (setup.blockPrimalNorm i) (setup.blockPrimalNorm_isPaperNorm i)
      (setup.blockCoord i (setup.gradL x s))) ?_ ?_ ?_ ?_
  · have hGradInt : Integrable (fun s => setup.gradL x s) setup.oracleSampleLaw := by
      simpa [StochasticBlockMirrorDescentSetup.oracleSampleLaw, StochasticBlockMirrorDescentSetup.X,
        SOptLib.oracleWellDefined, SOptLib.oracleKernel] using setup.horacle_wellDefined x hx
    simpa using (setup.blockCoord i).integrable_comp hGradInt
  · have hGradInt : Integrable (fun s => setup.gradL x s) setup.oracleSampleLaw := by
      simpa [StochasticBlockMirrorDescentSetup.oracleSampleLaw, StochasticBlockMirrorDescentSetup.X,
        SOptLib.oracleWellDefined, SOptLib.oracleKernel] using setup.horacle_wellDefined x hx
    unfold StochasticBlockMirrorDescentSetup.gBlock
    rw [← setup.hunbiased x hx]
    simpa [StochasticBlockMirrorDescentSetup.oracleSampleLaw] using
      (ContinuousLinearMap.integral_comp_comm (setup.blockCoord i) hGradInt).symm
  · simpa using setup.block_second_moment_wellDefined i x hx
  · simpa using setup.block_second_moment_dualNorm i x hx

/-! ### Retired false ambient-norm scaffold

The following certificate ties the deleted ambient Hilbert-norm conjunct to the
current paper-norm realization rather than to an arbitrary abstract dual norm:
the block dual norm below is exactly `canonicalDualNormFromPrimal` for the
scaled primal paper norm `p(d) = 100 * |d|` on one real block. -/

private noncomputable def scaledHundredPaperNorm : Seminorm ℝ ℝ :=
  ((100 : NNReal) • (normSeminorm ℝ ℝ) : Seminorm ℝ ℝ)

private theorem scaledHundredPaperNorm_apply (x : ℝ) :
    scaledHundredPaperNorm x = 100 * |x| := by
  simp [scaledHundredPaperNorm, NNReal.smul_def, Real.norm_eq_abs]

private theorem scaledHundredPaperNorm_isPaperNorm :
    IsPaperNorm scaledHundredPaperNorm := by
  intro x
  rw [scaledHundredPaperNorm_apply]
  constructor
  · intro h
    have hnorm : |x| = 0 := by nlinarith
    exact abs_eq_zero.mp hnorm
  · intro h
    simp [h]

private theorem scaledHundredPaperNorm_dual_at_hundred :
    canonicalDualNormFromPrimal scaledHundredPaperNorm (100 : ℝ) = 1 := by
  classical
  let A : Set ℝ :=
    {r : ℝ | ∃ d : ℝ,
      scaledHundredPaperNorm d ≤ 1 ∧ r = |⟪(100 : ℝ), d⟫_ℝ|}
  have hA_nonempty : A.Nonempty := by
    refine ⟨0, ?_⟩
    refine ⟨0, ?_, ?_⟩
    · simp [scaledHundredPaperNorm_apply]
    · simp
  have hupper : ∀ r ∈ A, r ≤ 1 := by
    intro r hr
    rcases hr with ⟨d, hd, rfl⟩
    rw [scaledHundredPaperNorm_apply] at hd
    rw [show ⟪(100 : ℝ), d⟫_ℝ = d * (100 : ℝ) by
      exact RCLike.inner_apply (100 : ℝ) d]
    norm_num at hd ⊢
    rwa [mul_comm]
  have hA_bdd : BddAbove A := ⟨1, hupper⟩
  have h_one_mem : (1 : ℝ) ∈ A := by
    refine ⟨(1 / 100 : ℝ), ?_, ?_⟩
    · rw [scaledHundredPaperNorm_apply]
      norm_num [abs_of_pos]
    · rw [show ⟪(100 : ℝ), (1 / 100 : ℝ)⟫_ℝ =
          (1 / 100 : ℝ) * (100 : ℝ) by
        exact RCLike.inner_apply (100 : ℝ) (1 / 100 : ℝ)]
      norm_num
  have hle : sSup A ≤ 1 := csSup_le hA_nonempty hupper
  have hge : (1 : ℝ) ≤ sSup A := le_csSup hA_bdd h_one_mem
  change sSup A = 1
  exact le_antisymm hle hge

/-- Formal counterexample certificate for the deleted ambient Hilbert-norm
conjunct from the old `derived_block_norm_bounds` scaffold.

The witness uses the actual canonical paper dual norm generated by
`canonicalDualNormFromPrimal` from the genuine scaled paper norm
`p(d) = 100 * |d|`. Taking `gBlock = g = 100` and `M = 1` satisfies the
source-style block-dual bound because the canonical dual value is `1`, while
the unguarded ambient conclusion `‖g‖^2 ≤ ∑ᵢ M_i^2` is false. -/
theorem old_derived_block_norm_bounds_ambient_counterexample :
    ∃ (p : Seminorm ℝ ℝ) (_hp : IsPaperNorm p)
      (gBlock : Unit → ℝ) (M : Unit → ℝ) (g : ℝ),
      canonicalDualNormFromPrimal p (gBlock ()) = 1 ∧
        (∀ i, canonicalDualNormFromPrimal p (gBlock i) ^ 2 ≤ M i ^ 2) ∧
        (∀ i, gBlock i = g) ∧
        ¬ (‖g‖ ^ 2 ≤ Finset.sum Finset.univ (fun i => M i ^ 2)) := by
  refine ⟨scaledHundredPaperNorm, scaledHundredPaperNorm_isPaperNorm,
    (fun _ => 100), (fun _ => 1), 100, ?_, ?_, ?_, ?_⟩
  · exact scaledHundredPaperNorm_dual_at_hundred
  · intro i
    fin_cases i
    rw [scaledHundredPaperNorm_dual_at_hundred]
  · intro i
    fin_cases i
    rfl
  · norm_num

/-- Retired audit bridge for the old, non-source conjunction.

An earlier scaffold bundled `derived_block_norm_bounds` with the ambient claim
`‖g x‖^2 ≤ ∑ᵢ M_i^2`. Eq. (4.6.22) only controls the block-dual quadratic
term. The ambient conclusion can be recovered only after explicitly providing
a comparison from the Hilbert norm of `g x` to the sum of squared block dual
norms; this comparison is not a source assumption and is therefore kept out of
the source-facing helper above. -/
theorem retired_derived_block_norm_bounds_with_ambient_comparison
    (setup : StochasticBlockMirrorDescentSetup ι S)
    (x : setup.StateSpace) (hx : x ∈ setup.X)
    (hambient_from_block_dual :
      ‖setup.g x‖ ^ 2 ≤
        Finset.sum Finset.univ
          (fun i => SOptLib.canonicalDualNorm (setup.blockPrimalNorm i) (setup.gBlock i x) ^ 2)) :
    (∀ i, SOptLib.canonicalDualNorm (setup.blockPrimalNorm i) (setup.gBlock i x) ^ 2 ≤ (setup.M i) ^ 2) ∧
      ‖setup.g x‖ ^ 2 ≤ Finset.sum Finset.univ (fun i => (setup.M i) ^ 2) := by
  constructor
  · exact derived_block_norm_bounds setup x hx
  · exact le_trans hambient_from_block_dual
      (Finset.sum_le_sum (fun i _ => derived_block_norm_bounds setup x hx i))

/-- DGF-derived lower bound used internally in Lemma 4.3.

This is the proof-step consequence of the paper's differentiable
distance-generating-function context, not a public hypothesis of Lemma 4.3. The
statement follows Eq. (4.6.7): `V` is the formula with `gradientWithin` for the
continuously differentiable, 1-strongly-convex generator on the carrier. -/
theorem lemma_4_3_dgf_lower_bound
    (X : Set E) (ν : E → ℝ) (V : E → E → ℝ) (p : Seminorm ℝ E)
    (hX_convex : Convex ℝ X)
    (hν_contDiffOn : ContDiffOn ℝ 1 ν X)
    (hν_strongly_convex : StrongConvexOnWithNorm X 1 p ν)
    (hV_eq : ∀ z x, z ∈ X → x ∈ X →
      V z x = ν x - (ν z + ⟪gradientWithin ν X z, x - z⟫_ℝ)) :
    ∀ z x, z ∈ X → x ∈ X →
      (1 / 2 : ℝ) * p (x - z) ^ 2 ≤ V z x := by
  intro z x hz hx
  rw [hV_eq z x hz hx]
  exact
    StochasticBlockMirrorDescentSetup.bregman_lower_bound_of_strongConvexOnWithNorm_contDiffOn
      (X := X) (ν := ν) (p := p) (z := z) (x := x)
      hX_convex hν_contDiffOn hν_strongly_convex hz hx

/-- Lemma 4.3's Cauchy/strong-convexity scalar estimate.

This is the proof step in Lan Lemma 4.3 after the prox three-point inequality:
`blockDualNorm_support_bound` supplies the block Cauchy bound and
`blockDivergence_lower_bound` supplies the `1/2‖·‖_i^2` Bregman lower bound.
SOptLib candidates considered: `prox_descent_inner_bound_of_variational` targets
projected-gradient descent from variational inequalities, while this helper is
the later scalar Young estimate with the paper's block primal/dual norms. -/
private theorem block_dual_young_minus_bregman
    (setup : StochasticBlockMirrorDescentSetup ι S) (i : ι)
    (ζ : setup.Block i) (z y : Set.Elem (setup.XBlock i)) :
    ⟪ζ, z.1 - y.1⟫_ℝ - setup.blockDivergence i z y ≤
      (1 / 2 : ℝ) * SOptLib.canonicalDualNorm (setup.blockPrimalNorm i) ζ ^ 2 := by
  refine inner_sub_sub_bregman_le_half_dual_sq
    (fun w : Set.Elem (setup.XBlock i) => w.1) (setup.blockDivergence i)
    (setup.blockPrimalNorm i) (SOptLib.canonicalDualNorm (setup.blockPrimalNorm i))
    ζ z y ?_ ?_
  · exact le_trans (le_abs_self _)
      (setup.blockDualNorm_support_bound i ζ (z.1 - y.1))
  · have hnorm :
        setup.blockPrimalNorm i (y.1 - z.1) =
          setup.blockPrimalNorm i (z.1 - y.1) := by
      have hsub : y.1 - z.1 = -(z.1 - y.1) := by
        abel
      rw [hsub, map_neg_eq_map]
    simpa [hnorm] using setup.blockDivergence_lower_bound i z y

/-- Finite-range telescope for the second half of Lan Lemma 4.3.

SOptLib candidate `sum_Icc_sub_succ` was considered; this helper specializes
the same closed-interval telescope to the zero-based `Finset.range j` used by
the paper-facing Lean statement and immediately drops the nonnegative tail. -/
private theorem range_bregman_telescope_nonneg_tail
    (A : ℕ → ℝ) (j : ℕ) (hterm : 0 ≤ A j) :
    Finset.sum (Finset.range j) (fun t => A t - A (t + 1)) ≤ A 0 := by
  exact sum_range_sub_succ_le_first_of_last_nonneg A j hterm

/-- First-order variational inequality for the block prox subproblem.

This is the source step behind Lan Lemma 4.3, obtained by differentiating the
prox objective along the feasible segment from the minimizer `y` to the
comparison point `x`. SOptLib candidates considered: `mirrorObjective_argmin_variational`
is a general charted FOC, while `prox_scaled_variational_inequality_of_argmin`
and `carrierBregman_segment_difference_hasDerivWithinAt_zero` expose the same
segment-derivative route; this block-local statement keeps the exact
`gradientWithin` object used by `setup.blockDivergence_eq`. -/
private theorem block_prox_variational_from_isMinOn
    (setup : StochasticBlockMirrorDescentSetup ι S) (i : ι)
    (z y x : Set.Elem (setup.XBlock i)) (ζ : setup.Block i)
    (hmin :
      IsMinOn
        (fun u : Set.Elem (setup.XBlock i) =>
          ⟪ζ, u.1⟫_ℝ + setup.blockDivergence i z u)
        Set.univ y) :
    0 ≤
      ⟪ζ +
          gradientWithin (setup.blockDGFAmbient i) (setup.XBlock i) y.1 -
            gradientWithin (setup.blockDGFAmbient i) (setup.XBlock i) z.1,
        x.1 - y.1⟫_ℝ := by
  classical
  let objective : Set.Elem (setup.XBlock i) → ℝ := fun u =>
    ⟪ζ, u.1⟫_ℝ + setup.blockDivergence i z u
  have hmin_all : ∀ u : Set.Elem (setup.XBlock i), objective y ≤ objective u := by
    simpa [objective, isMinOn_univ_iff] using hmin
  let segment : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → Set.Elem (setup.XBlock i) :=
    fun t ht =>
      ⟨AffineMap.lineMap y.1 x.1 t,
        (setup.hXBlock_convex i).lineMap_mem y.2 x.2 ht⟩
  have hsegment_min :
      ∀ t (ht : t ∈ Set.Icc (0 : ℝ) 1), objective y ≤ objective (segment t ht) := by
    intro t ht
    exact hmin_all (segment t ht)
  let grad : Set.Elem (setup.XBlock i) → setup.Block i := fun u =>
    gradientWithin (setup.blockDGFAmbient i) (setup.XBlock i) u.1
  let d : setup.Block i := x.1 - y.1
  let β : ℝ → ℝ := fun t =>
    if ht : t ∈ Set.Icc (0 : ℝ) 1 then
      setup.blockDivergence i z (segment t ht) - setup.blockDivergence i z y
    else 0
  have hV :
      ∀ a b : Set.Elem (setup.XBlock i),
        setup.blockDivergence i a b =
          setup.blockDGF i b - setup.blockDGF i a - ⟪grad a, b.1 - a.1⟫_ℝ := by
    intro a b
    rw [setup.blockDivergence_eq i a b]
    rw [setup.blockDGF_eq_ambient i b, setup.blockDGF_eq_ambient i a]
    simp [grad]
    ring
  have hgrad_apply :
      ∀ (u : Set.Elem (setup.XBlock i)) (w : setup.Block i),
        (fderivWithin ℝ (setup.blockDGFAmbient i) (setup.XBlock i) u.1) w =
          ⟪grad u, w⟫_ℝ := by
    intro u w
    simp [grad, gradientWithin, InnerProductSpace.toDual_symm_apply]
  have hβderiv :
      HasDerivWithinAt β ⟪grad y - grad z, d⟫_ℝ (Set.Icc (0 : ℝ) 1) 0 := by
    have hcore :=
      carrierBregman_segment_difference_hasDerivWithinAt_zero
        (hX_convex := setup.hXBlock_convex i)
        (nu := fun u : Set.Elem (setup.XBlock i) => setup.blockDGF i u)
        (nuAmbient := setup.blockDGFAmbient i)
        (grad := grad)
        (V := setup.blockDivergence i)
        (hnu_eq := fun u => setup.blockDGF_eq_ambient i u)
        (hnu_diff := (setup.hblockDGFAmbient_contDiffOn i).differentiableOn_one)
        (hgrad_apply := hgrad_apply)
        (hV := hV)
        z y x
    simpa [β, segment, d] using hcore
  let φ : ℝ → ℝ := fun t => (1 : ℝ) * t * ⟪ζ, d⟫_ℝ + β t + (1 : ℝ) * t * 0
  have hφmin : ∀ t ∈ Set.Icc (0 : ℝ) 1, φ 0 ≤ φ t := by
    intro t ht
    have hseg := hsegment_min t ht
    have hline_sub : (segment t ht).1 - y.1 = t • d := by
      simp [segment, d, AffineMap.lineMap_apply_module']
    have hinner :
        ⟪ζ, (segment t ht).1⟫_ℝ - ⟪ζ, y.1⟫_ℝ =
          t * ⟪ζ, d⟫_ℝ := by
      calc
        ⟪ζ, (segment t ht).1⟫_ℝ - ⟪ζ, y.1⟫_ℝ =
            ⟪ζ, (segment t ht).1 - y.1⟫_ℝ := by
              rw [inner_sub_right]
        _ = t * ⟪ζ, d⟫_ℝ := by
              rw [hline_sub, inner_smul_right]
    have hβ_eval :
        β t = setup.blockDivergence i z (segment t ht) -
          setup.blockDivergence i z y := by
      dsimp [β]
      rw [dif_pos ht]
    have hφ0 : φ 0 = 0 := by
      have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
      have hseg0 : segment 0 h0 = y := by
        apply Subtype.ext
        simp [segment, AffineMap.lineMap_apply_module']
      have hβ0 : β 0 = 0 := by
        dsimp [β]
        rw [dif_pos h0, hseg0]
        ring
      simp [φ, hβ0]
    rw [hφ0]
    dsimp [objective] at hseg
    dsimp [φ]
    rw [hβ_eval]
    nlinarith
  have hφderiv :
      HasDerivWithinAt φ
        ((1 : ℝ) * ⟪ζ, d⟫_ℝ + ⟪grad y - grad z, d⟫_ℝ + (1 : ℝ) * 0)
        (Set.Icc (0 : ℝ) 1) 0 := by
    simpa [φ] using
      prox_majorant_hasDerivWithinAt_zero β ζ d (grad y - grad z) (1 : ℝ) 0 hβderiv
  have hnonneg :
      0 ≤ (1 : ℝ) * ⟪ζ, d⟫_ℝ + ⟪grad y - grad z, d⟫_ℝ + (1 : ℝ) * 0 :=
    right_derivative_nonneg_of_min_on_Icc hφderiv hφmin
  simpa [d, grad, inner_add_left, inner_sub_left, add_assoc, sub_eq_add_neg] using hnonneg

/-- Three-point prox inequality for the block Bregman prox update.

This aligns with Lan Lemma 4.3 proof step 1. The bridge consumes the
argmin-derived variational inequality above and SOptLib's
`carrierBregmanDivergence_three_point_identity`; measurability/selector
candidates such as `Measurable.proxStep_comp`,
`proxStep_measurable_of_joint_continuous_unique`,
`projectedGradient_lipschitz_oracle_of_prox_scaled_dist`,
`proxPoint_continuous_of_lipschitzWith_oracle`,
`continuous_argmin_of_compact_unique`, and `argminSelectorOfSource` were
checked from the digest but rejected because they address selector existence or
regularity, not the deterministic three-point inequality. -/
private theorem block_prox_three_point_from_isMinOn
    (setup : StochasticBlockMirrorDescentSetup ι S) (i : ι)
    (z y x : Set.Elem (setup.XBlock i)) (ζ : setup.Block i)
    (hmin :
      IsMinOn
        (fun u : Set.Elem (setup.XBlock i) =>
          ⟪ζ, u.1⟫_ℝ + setup.blockDivergence i z u)
        Set.univ y) :
    ⟪ζ, y.1 - x.1⟫_ℝ + setup.blockDivergence i z y ≤
      setup.blockDivergence i z x - setup.blockDivergence i y x := by
  classical
  simpa [carrierBregmanDivergence_def, setup.blockDivergence_eq,
    setup.blockDGF_eq_ambient, sub_eq_add_neg, add_assoc, add_comm,
    add_left_comm] using
      prox_three_point_of_isMinOn_linear_bregman
        (hX_convex := setup.hXBlock_convex i)
        (nu := fun u : Set.Elem (setup.XBlock i) => setup.blockDGF i u)
        (nuAmbient := setup.blockDGFAmbient i)
        (grad := fun u : Set.Elem (setup.XBlock i) =>
          gradientWithin (setup.blockDGFAmbient i) (setup.XBlock i) u.1)
        z y x ζ
        (hnu_eq_segment := fun t ht => setup.blockDGF_eq_ambient i _)
        (hnu_diff := (setup.hblockDGFAmbient_contDiffOn i).differentiableOn_one y.1 y.2)
        (hgrad_apply := by
          simp [gradientWithin, InnerProductSpace.toDual_symm_apply])
        (by
          simpa [carrierBregmanDivergence_def, setup.blockDivergence_eq,
            setup.blockDGF_eq_ambient, sub_eq_add_neg, add_assoc, add_comm,
            add_left_comm] using hmin)

/-- Lemma 4.3 in the paper-facing block-DGF Bregman prox-recursion form.

The zero-based Lean sequence `v 0, v 1, ...` represents the paper's
`v_1, v_2, ...`. The feasible carrier, distance generator, Bregman divergence
`V_i`, and `1`-strong convexity context are the canonical block objects in
`setup`, not theorem-local arbitrary witnesses. Book citation:
`book/FOML/StochasticBlockMirrorDescent.json#/key_lemmas/0/statement_math`. -/
theorem lemma_4_3
    (setup : StochasticBlockMirrorDescentSetup ι S) (i : ι)
    (ζ : ℕ → setup.Block i) (v : ℕ → Set.Elem (setup.XBlock i)) (j : ℕ)
    (hv_init : (v 0).1 ∈ interior (setup.XBlock i))
    (hprox_rec :
      ∀ t, t < j →
        IsMinOn
          (fun u : Set.Elem (setup.XBlock i) =>
            ⟪ζ t, u.1⟫_ℝ + setup.blockDivergence i (v t) u)
          Set.univ (v (t + 1))) :
    (∀ t x, t < j →
      ⟪ζ t, (v t).1 - x.1⟫_ℝ ≤
        setup.blockDivergence i (v t) x -
          setup.blockDivergence i (v (t + 1)) x +
            (1 / 2 : ℝ) * SOptLib.canonicalDualNorm (setup.blockPrimalNorm i) (ζ t) ^ 2) ∧
    ∀ x,
      Finset.sum (Finset.range j) (fun t => ⟪ζ t, (v t).1 - x.1⟫_ℝ) ≤
        setup.blockDivergence i (v 0) x + (1 / 2 : ℝ) *
          Finset.sum (Finset.range j) (fun t => SOptLib.canonicalDualNorm (setup.blockPrimalNorm i) (ζ t) ^ 2) := by
  exact
    mirror_descent_sum_bound_of_three_point_and_young
      (V := setup.blockDivergence i) (eval := fun x : Set.Elem (setup.XBlock i) => x.1)
      (dualNorm := SOptLib.canonicalDualNorm (setup.blockPrimalNorm i)) ζ v j
      (fun t x ht =>
        block_prox_three_point_from_isMinOn setup i (v t) (v (t + 1)) x (ζ t)
          (hprox_rec t ht))
      (fun t ht =>
        block_dual_young_minus_bregman setup i (ζ t) (v t) (v (t + 1)))
      (fun x => setup.blockDivergence_nonneg i (v j) x)

/-- γ-scaled one-block descent estimate for the sampled update in Eq. (4.6.14).

This aligns with Lan Theorem 4.12 proof step 1, before lifting the sampled
block inequality into the aggregate potential. SOptLib/target candidates
considered: `block_prox_three_point_from_isMinOn` supplies the unscaled
three-point inequality and is used here; `block_dual_young_minus_bregman`
would require a homogeneity theorem for the paper-derived dual norm
`blockDualNorm`, so the scaled Young estimate is proved directly from
`blockDualNorm_support_bound` and `blockDivergence_lower_bound`. -/
private theorem block_prox_gamma_step_bound
    (setup : StochasticBlockMirrorDescentSetup ι S) (i : ι)
    (z y x : Set.Elem (setup.XBlock i)) (g : setup.Block i) (γ : ℝ)
    (hγ : 0 < γ)
    (hmin :
      IsMinOn (setup.blockProxObjective i z g γ) Set.univ y) :
    γ * ⟪g, z.1 - x.1⟫_ℝ ≤
      setup.blockDivergence i z x - setup.blockDivergence i y x +
        (1 / 2 : ℝ) * γ ^ 2 * SOptLib.canonicalDualNorm (setup.blockPrimalNorm i) g ^ 2 := by
  classical
  refine
    prox_gamma_step_bound_of_three_point_and_dual_support
      (V := setup.blockDivergence i)
      (eval := fun u : Set.Elem (setup.XBlock i) => u.1)
      (primalNorm := setup.blockPrimalNorm i)
      (dualNorm := SOptLib.canonicalDualNorm (setup.blockPrimalNorm i))
      (z := z) (y := y) (x := x) (g := g) (γ := γ)
      (le_of_lt hγ) ?_ ?_ ?_
  · have hγ_nonneg : 0 ≤ γ := le_of_lt hγ
    have hγ_ne : γ ≠ 0 := ne_of_gt hγ
    have hscaled_min :
        IsMinOn
          (fun u : Set.Elem (setup.XBlock i) =>
            ⟪γ • g, u.1⟫_ℝ + setup.blockDivergence i z u)
          Set.univ y := by
      rw [isMinOn_univ_iff]
      intro u
      have hmin_all :
          ∀ u : Set.Elem (setup.XBlock i),
            setup.blockProxObjective i z g γ y ≤
              setup.blockProxObjective i z g γ u := by
        simpa [isMinOn_univ_iff] using hmin
      have hbase := hmin_all u
      rw [setup.blockProxObjective_eq i z y g γ,
        setup.blockProxObjective_eq i z u g γ] at hbase
      have hmul := mul_le_mul_of_nonneg_left hbase hγ_nonneg
      convert hmul using 1
      · rw [real_inner_smul_left]
        field_simp [hγ_ne]
      · rw [real_inner_smul_left]
        field_simp [hγ_ne]
    simpa [real_inner_smul_left] using
      block_prox_three_point_from_isMinOn setup i z y x (γ • g) hscaled_min
  · exact le_trans (le_abs_self _)
      (setup.blockDualNorm_support_bound i g (z.1 - y.1))
  · have hnorm :
        setup.blockPrimalNorm i (y.1 - z.1) =
          setup.blockPrimalNorm i (z.1 - y.1) := by
      have hsub : y.1 - z.1 = -(z.1 - y.1) := by
        abel
      rw [hsub, map_neg_eq_map]
    simpa [hnorm] using setup.blockDivergence_lower_bound i z y

/-- Lift the sampled one-block prox descent estimate into the weighted aggregate
potential sum.

This is the finite-sum part of Lan Theorem 4.12 proof step 1. No SOptLib
match: searched "aggregate potential block replacement finite sum" and the
target-file/SOptLib hits around `aggregatePotential`, `blockMirrorProx_other`,
and `Finset.sum_eq_single`; SOptLib has generic finite-sum and weighted-output
tools, but not this paper's coordinate-splice aggregate Bregman potential. -/
private theorem aggregatePotential_blockMirrorProx_bound
    (setup : StochasticBlockMirrorDescentSetup ι S) (i : ι)
    (x0 x : setup.FeasibleState) (g : setup.Block i) (γ : ℝ) (hγ : 0 < γ) :
    setup.aggregatePotential (setup.blockMirrorProx i x0 g γ hγ) x ≤
      setup.aggregatePotential x0 x +
        (setup.p i)⁻¹ * γ * ⟪g, setup.blockCoord i x.1 - setup.blockCoord i x0.1⟫_ℝ +
          (1 / 2 : ℝ) * γ ^ 2 * (setup.p i)⁻¹ * SOptLib.canonicalDualNorm (setup.blockPrimalNorm i) g ^ 2 := by
  classical
  let z : Set.Elem (setup.XBlock i) :=
    ⟨setup.blockCoord i x0.1,
      by simpa [StochasticBlockMirrorDescentSetup.blockCoord] using x0.2 i⟩
  let y : Set.Elem (setup.XBlock i) :=
    ⟨setup.blockCoord i (setup.blockMirrorProx i x0 g γ hγ).1,
      by
        rw [setup.blockMirrorProx_selected i x0 g γ hγ]
        exact (setup.blockMirrorProxBlockRaw i
          ⟨setup.blockCoord i x0.1,
            by simpa [StochasticBlockMirrorDescentSetup.blockCoord] using x0.2 i⟩ g γ).2⟩
  let xcmp : Set.Elem (setup.XBlock i) :=
    ⟨setup.blockCoord i x.1,
      by simpa [StochasticBlockMirrorDescentSetup.blockCoord] using x.2 i⟩
  have hlift :=
    weighted_block_bregman_potential_single_block_bound
      (B := fun i => Set.Elem (setup.XBlock i))
      (p := setup.p)
      (coord := fun i y =>
        ⟨setup.blockCoord i y.1,
          by simpa [StochasticBlockMirrorDescentSetup.blockCoord] using y.2 i⟩)
      (V := setup.blockDivergence)
      (i := i) (z := x0) (y := setup.blockMirrorProx i x0 g γ hγ) (x := x)
      (delta :=
        γ * ⟪g, setup.blockCoord i x.1 - setup.blockCoord i x0.1⟫_ℝ +
          (1 / 2 : ℝ) * γ ^ 2 * SOptLib.canonicalDualNorm (setup.blockPrimalNorm i) g ^ 2)
      (inv_nonneg.mpr (le_of_lt (setup.hp_pos i)))
      (by
        have hmin : IsMinOn (setup.blockProxObjective i z g γ) Set.univ y := by
          simpa [z, y] using setup.blockMirrorProx_selected_isMinOn i x0 g γ hγ
        have hblock_raw :
            γ * ⟪g, z.1 - xcmp.1⟫_ℝ ≤
              setup.blockDivergence i z xcmp - setup.blockDivergence i y xcmp +
                (1 / 2 : ℝ) * γ ^ 2 * SOptLib.canonicalDualNorm (setup.blockPrimalNorm i) g ^ 2 := by
          exact block_prox_gamma_step_bound setup i z y xcmp g γ hγ hmin
        have hinner : ⟪g, xcmp.1 - z.1⟫_ℝ = -⟪g, z.1 - xcmp.1⟫_ℝ := by
          have hsub : xcmp.1 - z.1 = -(z.1 - xcmp.1) := by
            abel
          rw [hsub, inner_neg_right]
        change
          setup.blockDivergence i y xcmp ≤
            setup.blockDivergence i z xcmp +
              (γ * ⟪g, xcmp.1 - z.1⟫_ℝ +
                (1 / 2 : ℝ) * γ ^ 2 *
                  SOptLib.canonicalDualNorm (setup.blockPrimalNorm i) g ^ 2)
        rw [hinner]
        nlinarith)
      (by
        intro j hji
        have hcoord :
            setup.blockCoord j (setup.blockMirrorProx i x0 g γ hγ).1 =
              setup.blockCoord j x0.1 := by
          exact setup.blockMirrorProx_other i j x0 g γ hγ hji
        simp [hcoord])
  calc
    setup.aggregatePotential (setup.blockMirrorProx i x0 g γ hγ) x
        ≤ setup.aggregatePotential x0 x +
            (setup.p i)⁻¹ *
              (γ * ⟪g, setup.blockCoord i x.1 - setup.blockCoord i x0.1⟫_ℝ +
                (1 / 2 : ℝ) * γ ^ 2 *
                  SOptLib.canonicalDualNorm (setup.blockPrimalNorm i) g ^ 2) := by
          simpa [StochasticBlockMirrorDescentSetup.aggregatePotential] using hlift
    _ = setup.aggregatePotential x0 x +
        (setup.p i)⁻¹ * γ * ⟪g, setup.blockCoord i x.1 - setup.blockCoord i x0.1⟫_ℝ +
          (1 / 2 : ℝ) * γ ^ 2 * (setup.p i)⁻¹ *
            SOptLib.canonicalDualNorm (setup.blockPrimalNorm i) g ^ 2 := by
        ring

/-! Used in: `step_4_6_20` and `theorem_4_12` as the one-step aggregate
potential recursion from Eq. (4.6.18). -/
theorem step_4_6_18
    (setup : StochasticBlockMirrorDescentSetup ι S)
    (k : ℕ) (ω : StochasticBlockSamplePath S ι) (x : setup.StateSpace) (hx : x ∈ setup.X) :
    setup.aggregatePotential ⟨(SOptLib.iterateProcessView (fun t ω => (setup.process t ω).x.1)) (k + 1) ω, setup.xIter_mem (k + 1) ω⟩ ⟨x, hx⟩ ≤
      setup.aggregatePotential ⟨(SOptLib.iterateProcessView (fun t ω => (setup.process t ω).x.1)) k ω, setup.xIter_mem k ω⟩ ⟨x, hx⟩ +
        setup.η k * ⟪setup.g ((SOptLib.iterateProcessView (fun t ω => (setup.process t ω).x.1)) k ω), x - (SOptLib.iterateProcessView (fun t ω => (setup.process t ω).x.1)) k ω⟫_ℝ +
        setup.η k * setup.delta x k ω +
        (1 / 2 : ℝ) * (setup.η k) ^ 2 * setup.deltaBar k ω := by
  classical
  let i := setup.block k ω
  let xkF : setup.FeasibleState :=
    ⟨(SOptLib.iterateProcessView (fun t ω => (setup.process t ω).x.1)) k ω,
      setup.xIter_mem k ω⟩
  let xNextF : setup.FeasibleState :=
    ⟨(SOptLib.iterateProcessView (fun t ω => (setup.process t ω).x.1)) (k + 1) ω,
      setup.xIter_mem (k + 1) ω⟩
  let gk : setup.Block i := setup.blockCoord i (setup.gradL ((SOptLib.iterateProcessView (fun t ω => (setup.process t ω).x.1)) k ω) (setup.ξ k ω))
  let yF : setup.FeasibleState := setup.blockMirrorProx i xkF gk (setup.η k) (setup.hη_pos k)
  have hnext : (SOptLib.iterateProcessView (fun t ω => (setup.process t ω).x.1)) (k + 1) ω = yF.1 := by
    simp [SOptLib.iterateProcessView, StochasticBlockMirrorDescentSetup.process,
      stochasticBlockMirrorDescentProcess, i, xkF, gk, yF]
  have hstate :
      xNextF = yF := by
    apply Subtype.ext
    exact hnext
  have hstep :
      setup.aggregatePotential xNextF ⟨x, hx⟩ ≤
        setup.aggregatePotential xkF ⟨x, hx⟩ +
          setup.η k *
            ((setup.p i)⁻¹ *
              ⟪gk, setup.blockCoord i x - setup.blockCoord i xkF.1⟫_ℝ) +
          (1 / 2 : ℝ) * (setup.η k) ^ 2 *
            ((setup.p i)⁻¹ * SOptLib.canonicalDualNorm (setup.blockPrimalNorm i) gk ^ 2) := by
    have hagg :
        setup.aggregatePotential xNextF ⟨x, hx⟩ ≤
          setup.aggregatePotential xkF ⟨x, hx⟩ +
            (setup.p i)⁻¹ * setup.η k *
              ⟪gk, setup.blockCoord i x - setup.blockCoord i xkF.1⟫_ℝ +
            (1 / 2 : ℝ) * (setup.η k) ^ 2 * (setup.p i)⁻¹ *
              SOptLib.canonicalDualNorm (setup.blockPrimalNorm i) gk ^ 2 := by
      rw [hstate]
      simpa [yF, xkF, gk] using
        aggregatePotential_blockMirrorProx_bound setup i xkF ⟨x, hx⟩ gk (setup.η k)
          (setup.hη_pos k)
    nlinarith
  let d : setup.StateSpace := x - xkF.1
  have hcoord_diff :
      setup.blockCoord i d = setup.blockCoord i x - setup.blockCoord i xkF.1 := by
    simp [d]
  have hpair_lift :
      ⟪gk, setup.blockCoord i x - setup.blockCoord i xkF.1⟫_ℝ =
        ⟪PiLp.single 2 i gk, x - xkF.1⟫_ℝ := by
    calc
      ⟪gk, setup.blockCoord i x - setup.blockCoord i xkF.1⟫_ℝ =
          ⟪gk, setup.blockCoord i d⟫_ℝ := by rw [hcoord_diff]
      _ = ⟪setup.blockCoord i d, gk⟫_ℝ := by rw [real_inner_comm]
      _ = ⟪d, PiLp.single 2 i gk⟫_ℝ := by
          exact setup.blockDualLift_pairing i d gk
      _ = ⟪PiLp.single 2 i gk, d⟫_ℝ := by rw [real_inner_comm]
      _ = ⟪PiLp.single 2 i gk, x - xkF.1⟫_ℝ := by simp [d]
  have hpair :
      (setup.p i)⁻¹ * ⟪gk, setup.blockCoord i x - setup.blockCoord i xkF.1⟫_ℝ =
        ⟪(setup.p i)⁻¹ • PiLp.single 2 i gk, x - xkF.1⟫_ℝ := by
    rw [hpair_lift, real_inner_smul_left]
  have hdelta :
      setup.delta x k ω =
        ⟪(setup.p i)⁻¹ • PiLp.single 2 i gk - setup.g xkF.1, x - xkF.1⟫_ℝ := by
    simp [StochasticBlockMirrorDescentSetup.delta, i, gk, xkF]
  have hdeltaBar :
      setup.deltaBar k ω =
        (setup.p i)⁻¹ * SOptLib.canonicalDualNorm (setup.blockPrimalNorm i) gk ^ 2 := by
    simp [StochasticBlockMirrorDescentSetup.deltaBar, i, gk]
  simpa [xkF, xNextF] using
    block_mirror_descent_one_step_aggregate_recursion
      (point := fun z : setup.FeasibleState => z.1)
      (V := setup.aggregatePotential)
      (x := xkF)
      (xNext := xNextF)
      (xRef := ⟨x, hx⟩)
      (sampledLift := (setup.p i)⁻¹ • PiLp.single 2 i gk)
      (meanGrad := setup.g xkF.1)
      (sampledPair :=
        (setup.p i)⁻¹ * ⟪gk, setup.blockCoord i x - setup.blockCoord i xkF.1⟫_ℝ)
      (eta := setup.η k)
      (delta := setup.delta x k ω)
      (deltaBar := setup.deltaBar k ω)
      (quad := (setup.p i)⁻¹ * SOptLib.canonicalDualNorm (setup.blockPrimalNorm i) gk ^ 2)
      hstep hpair hdelta hdeltaBar

/-! Used in: `theorem_4_12` as the telescoped suboptimality inequality leading
from Eq. (4.6.18) to Eq. (4.6.20). -/
theorem step_4_6_20
    (setup : StochasticBlockMirrorDescentSetup ι S)
    (N : ℕ) (hN : 0 < N) (x : setup.StateSpace) (hx : x ∈ setup.X)
    (ω : StochasticBlockSamplePath S ι) :
    setup.objective (setup.weightedAverage N ω) - setup.objective x ≤
      (setup.outputEtaSum N)⁻¹ *
        (setup.aggregatePotential ⟨setup.w₀, setup.w₀_mem⟩ ⟨x, hx⟩ +
          Finset.sum (StochasticBlockMirrorDescentSetup.outputTimes N) (fun k =>
            setup.paperEta k *
              setup.delta x (StochasticBlockMirrorDescentSetup.zeroBasedIndex k) ω +
              (1 / 2 : ℝ) * (setup.paperEta k) ^ 2 *
                setup.deltaBar (StochasticBlockMirrorDescentSetup.zeroBasedIndex k) ω)) := by
  classical
  letI : IsProbabilityMeasure setup.P := setup.P_probability
  let times := StochasticBlockMirrorDescentSetup.outputTimes N
  let t0 := StochasticBlockMirrorDescentSetup.zeroBasedIndex
  let V : ℕ → ℝ := fun n =>
    setup.aggregatePotential ⟨(SOptLib.iterateProcessView (fun t ω => (setup.process t ω).x.1)) n ω, setup.xIter_mem n ω⟩ ⟨x, hx⟩
  let noise : StochasticBlockMirrorDescentSetup.PositiveTime → ℝ := fun k =>
    setup.paperEta k * setup.delta x (t0 k) ω +
      (1 / 2 : ℝ) * setup.paperEta k ^ 2 * setup.deltaBar (t0 k) ω
  have hWpos : 0 < setup.outputEtaSum N := by
    unfold StochasticBlockMirrorDescentSetup.outputEtaSum
      StochasticBlockMirrorDescentSetup.outputTimes
    exact SOptLib.positiveTimeOutputWindow setup.paperEta
      (fun k => setup.hη_pos (StochasticBlockMirrorDescentSetup.zeroBasedIndex k))
      (le_refl 1) hN
  have htheta_eta : setup.outputThetaSum N = setup.outputEtaSum N := by
    unfold StochasticBlockMirrorDescentSetup.outputThetaSum
      StochasticBlockMirrorDescentSetup.outputEtaSum
    exact Finset.sum_congr rfl (fun k _hk => setup.paperTheta_eq_paperEta k)
  have havg_eta :
      setup.weightedAverage N ω =
        (setup.outputEtaSum N)⁻¹ •
          Finset.sum times (fun k => setup.paperEta k • setup.xPaper k ω) := by
    unfold StochasticBlockMirrorDescentSetup.weightedAverage
    simp [SOptLib.weightedAverageOutputValue, times, htheta_eta,
      setup.paperTheta_eq_paperEta]
  have hpoint :
      ∀ k ∈ times,
        setup.paperEta k * (setup.objective (setup.xPaper k ω) - setup.objective x) ≤
          V (t0 k) - V (t0 k + 1) + noise k := by
    intro k _hk
    let t := StochasticBlockMirrorDescentSetup.zeroBasedIndex k
    have hsubmem := setup.hsubgradient (setup.xPaper k ω) (setup.xIter_mem t ω)
    have hsupport0 := (SOptLib.mem_carrierSubdifferential_iff.mp hsubmem) ⟨x, hx⟩
    have hsupport :
        setup.objective x ≥
          setup.objective (setup.xPaper k ω) +
            ⟪setup.g (setup.xPaper k ω), x - setup.xPaper k ω⟫_ℝ := by
      simpa [StochasticBlockMirrorDescentSetup.objective,
        StochasticBlockMirrorDescentSetup.xPaper, t] using hsupport0
    have hgap :
        setup.objective (setup.xPaper k ω) - setup.objective x ≤
          ⟪setup.g (setup.xPaper k ω), setup.xPaper k ω - x⟫_ℝ := by
      have hneg :
          -⟪setup.g (setup.xPaper k ω), x - setup.xPaper k ω⟫_ℝ =
            ⟪setup.g (setup.xPaper k ω), setup.xPaper k ω - x⟫_ℝ := by
        have hd : -(x - setup.xPaper k ω) = setup.xPaper k ω - x := by
          abel
        rw [← inner_neg_right, hd]
      nlinarith
    have hmul := mul_le_mul_of_nonneg_left hgap (le_of_lt (setup.hη_pos t))
    have hstep := step_4_6_18 setup t ω x hx
    have hstep_rearr :
        setup.paperEta k *
            ⟪setup.g (setup.xPaper k ω), setup.xPaper k ω - x⟫_ℝ ≤
          V t - V (t + 1) + noise k := by
      dsimp [V, noise, t, t0]
      dsimp [StochasticBlockMirrorDescentSetup.xPaper,
        StochasticBlockMirrorDescentSetup.paperEta,
        SOptLib.positiveTimeStepSize, t,
        StochasticBlockMirrorDescentSetup.zeroBasedIndex] at hstep ⊢
      have hinner :
          ⟪setup.g ((SOptLib.iterateProcessView (fun t ω => (setup.process t ω).x.1)) t ω), (SOptLib.iterateProcessView (fun t ω => (setup.process t ω).x.1)) t ω - x⟫_ℝ =
            -⟪setup.g ((SOptLib.iterateProcessView (fun t ω => (setup.process t ω).x.1)) t ω), x - (SOptLib.iterateProcessView (fun t ω => (setup.process t ω).x.1)) t ω⟫_ℝ := by
        have hd : (SOptLib.iterateProcessView (fun t ω => (setup.process t ω).x.1)) t ω - x = -(x - (SOptLib.iterateProcessView (fun t ω => (setup.process t ω).x.1)) t ω) := by
          abel
        rw [hd, inner_neg_right]
      dsimp [t, StochasticBlockMirrorDescentSetup.zeroBasedIndex] at hinner
      rw [hinner]
      nlinarith
    exact le_trans hmul hstep_rearr
  have htel :
      Finset.sum times (fun k => V (t0 k) - V (t0 k + 1)) ≤ V 0 := by
    have hVN_nonneg : 0 ≤ V N := by
      dsimp [V]
      unfold StochasticBlockMirrorDescentSetup.aggregatePotential
      apply Finset.sum_nonneg
      intro i _hi
      exact mul_nonneg (inv_nonneg.mpr (le_of_lt (setup.hp_pos i)))
        (setup.blockDivergence_nonneg i _ _)
    have htel0 := outputWindow_sum_sub_succ_le_first_of_last_nonneg
      (times := StochasticBlockMirrorDescentSetup.outputTimes N)
      (a := fun k : StochasticBlockMirrorDescentSetup.PositiveTime => V (k.1 - 1))
      (hstart := le_refl 1) (hle := hN)
      (htimes_sum_eq_Icc := fun φ =>
        SOptLib.sum_positiveTimeOutputWindowTimes_eq_Icc 1 N (le_refl 1) hN φ)
      (by simpa using hVN_nonneg)
    have htel_window :
        Finset.sum (StochasticBlockMirrorDescentSetup.outputTimes N)
            (fun k => V (k.1 - 1) - V k.1) ≤ V 0 := by
      simpa [StochasticBlockMirrorDescentSetup.outputTimes] using htel0
    calc
      Finset.sum times (fun k => V (t0 k) - V (t0 k + 1))
          = Finset.sum (StochasticBlockMirrorDescentSetup.outputTimes N)
              (fun k => V (k.1 - 1) - V k.1) := by
            dsimp [times, t0]
            refine Finset.sum_congr rfl ?_
            intro k _hk
            dsimp [StochasticBlockMirrorDescentSetup.zeroBasedIndex]
            rw [Nat.sub_add_cancel k.2]
      _ ≤ V 0 := htel_window
  have hmain :
      setup.objective (setup.weightedAverage N ω) - setup.objective x ≤
        (setup.outputEtaSum N)⁻¹ * (V 0 + Finset.sum times noise) := by
    exact weighted_output_gap_le_initial_potential_add_noise
      (hobjective_convex := setup.objective_convex)
      (times := times) (weight := setup.paperEta) (W := setup.outputEtaSum N)
      (xbar := setup.weightedAverage N ω) (xRef := x)
      (xAt := fun k => setup.xPaper k ω)
      (index := t0) (V := V) (noise := noise)
      (fun k _hk =>
        le_of_lt (setup.hη_pos (StochasticBlockMirrorDescentSetup.zeroBasedIndex k)))
      (fun k _hk => setup.xIter_mem (StochasticBlockMirrorDescentSetup.zeroBasedIndex k) ω)
      hWpos (by rfl) havg_eta hpoint htel
  simpa [times, noise, t0, V, SOptLib.iterateProcessView,
    StochasticBlockMirrorDescentSetup.process] using hmain

/-! Fixed-fiber centering for Eq. (4.6.21). -/

/-- The weighted lifted block oracle is integrable under the fixed same-time
sample-pair law.

Candidate audit: `weighted_lifted_gradBlock_unbiased` proves the matching
stream mean identity, but it does not expose the fixed-fiber integrability
needed by the scalar conditional-expectation route; SOptLib's
`integrable_prod_of_fiber_integrable` was considered, but the local product
law has the oracle law on the first coordinate and the finite block law on the
second, so this helper reuses the same finite-dispatch construction aligned
with Lan Eq. (4.6.3)/(4.6.12). -/
private theorem fixed_pair_lifted_gradBlock_integrable
    (setup : StochasticBlockMirrorDescentSetup ι S)
    (z : setup.StateSpace) (hz : z ∈ setup.X) :
    Integrable
      (fun q : S × ι =>
        (setup.p q.2)⁻¹ •
          PiLp.single 2 q.2 (setup.blockCoord q.2 (setup.gradL z q.1)))
      setup.samplePairLaw := by
  classical
  letI : IsProbabilityMeasure setup.oracleSampleLaw := setup.oracleSampleLaw_probability
  letI : IsProbabilityMeasure setup.blockIndexLaw := by
    unfold StochasticBlockMirrorDescentSetup.blockIndexLaw finiteBlockIndexLaw
    infer_instance
  simpa [StochasticBlockMirrorDescentSetup.samplePairLaw] using
    (integrable_inverse_probability_lifted_block_oracle_prod
      (muS := setup.oracleSampleLaw) (muI := setup.blockIndexLaw)
      (p := setup.p) (G := fun s => setup.gradL z s)
      (coord := fun i y => setup.blockCoord i y)
      (lift := fun i u => PiLp.single 2 i u)
      (hG := by
        simpa [StochasticBlockMirrorDescentSetup.oracleSampleLaw,
          StochasticBlockMirrorDescentSetup.X, SOptLib.oracleWellDefined,
          SOptLib.oracleKernel] using
          setup.horacle_wellDefined z hz)
      (hmeas := by
        intro i
        have hwell : Integrable (fun s => setup.gradL z s) setup.oracleSampleLaw := by
          simpa [StochasticBlockMirrorDescentSetup.oracleSampleLaw,
            StochasticBlockMirrorDescentSetup.X, SOptLib.oracleWellDefined,
            SOptLib.oracleKernel] using
            setup.horacle_wellDefined z hz
        have hcont_lift : Continuous (fun u : setup.Block i => PiLp.single 2 i u) := by
          rw [Metric.continuous_iff]
          intro u ε hε
          refine ⟨ε, hε, ?_⟩
          intro v hv
          have hnorm : ‖PiLp.single 2 i v - PiLp.single 2 i u‖ = ‖v - u‖ := by
            simp [← PiLp.single_sub, PiLp.norm_single]
          simpa [dist_eq_norm, hnorm] using hv
        exact hcont_lift.comp_aestronglyMeasurable
          ((setup.blockCoord i).continuous.comp_aestronglyMeasurable hwell.aestronglyMeasurable))
      (hnorm := by
        intro i s
        calc
          ‖PiLp.single 2 i (setup.blockCoord i (setup.gradL z s))‖ =
              ‖setup.blockCoord i (setup.gradL z s)‖ := by
                simp [PiLp.norm_single]
          _ ≤ ‖setup.gradL z s‖ := by
                simpa [StochasticBlockMirrorDescentSetup.blockCoord] using
                  PiLp.norm_apply_le (setup.gradL z s) i))

/-- Fixed sample-pair form of the weighted lifted block-oracle unbiasedness.

This aligns the stream lemma `weighted_lifted_gradBlock_unbiased` with the
fixed law required by `condExp_oracle_noise_eq_zero_of_iid_adapted` for
Lan Theorem 4.12 proof step 3. -/
private theorem fixed_pair_lifted_gradBlock_unbiased
    (setup : StochasticBlockMirrorDescentSetup ι S)
    (z : setup.StateSpace) (hz : z ∈ setup.X) :
    ∫ q : S × ι,
        (setup.p q.2)⁻¹ •
          PiLp.single 2 q.2 (setup.blockCoord q.2 (setup.gradL z q.1))
        ∂setup.samplePairLaw =
      setup.g z := by
  classical
  let Fpair : S × ι → setup.StateSpace :=
    fun q => (setup.p q.2)⁻¹ •
      PiLp.single 2 q.2 (setup.blockCoord q.2 (setup.gradL z q.1))
  have hprod : Integrable Fpair setup.samplePairLaw :=
    fixed_pair_lifted_gradBlock_integrable setup z hz
  have hfm :
      AEStronglyMeasurable Fpair (Measure.map (setup.samplePair 0) setup.P) := by
    rw [setup.samplePair_law 0]
    exact hprod.aestronglyMeasurable
  have hmap_eq := MeasureTheory.integral_map
    (setup.samplePair_measurable 0).aemeasurable hfm
  rw [setup.samplePair_law 0] at hmap_eq
  have hstream := setup.weighted_lifted_gradBlock_unbiased z hz 0
  calc
    ∫ q : S × ι, Fpair q ∂setup.samplePairLaw
        = ∫ ω, Fpair (setup.samplePair 0 ω) ∂setup.P := hmap_eq
    _ = ∫ ω, (setup.p (setup.block 0 ω))⁻¹ •
          PiLp.single 2 (setup.block 0 ω)
            (setup.blockCoord (setup.block 0 ω) (setup.gradL z (setup.ξ 0 ω))) ∂setup.P := by
          rfl
    _ = setup.g z := hstream

/-- Fixed-pair scalar centering for the delta integrand in Eq. (4.6.21).

Candidate audit: `integral_inner_fixedOracleDeviation_eq_zero` was checked and
matches the scalarization principle, while `weighted_lifted_gradBlock_unbiased`
provides the paper-specific centered vector mean only over the stream law. The
two fixed-pair helpers above bridge that gap for the exact Lan Eq. (4.6.3) and
Eq. (4.6.12) sample-pair law used by the conditional-expectation cancellation. -/
private theorem fixed_pair_scalar_delta_centered
    (setup : StochasticBlockMirrorDescentSetup ι S)
    (x z : setup.StateSpace) (hz : z ∈ setup.X) :
    Integrable
      (fun q : S × ι =>
        ⟪(setup.p q.2)⁻¹ •
            PiLp.single 2 q.2 (setup.blockCoord q.2 (setup.gradL z q.1)) - setup.g z,
          x - z⟫_ℝ)
      setup.samplePairLaw ∧
    ∫ q : S × ι,
        ⟪(setup.p q.2)⁻¹ •
            PiLp.single 2 q.2 (setup.blockCoord q.2 (setup.gradL z q.1)) - setup.g z,
          x - z⟫_ℝ ∂setup.samplePairLaw = 0 := by
  classical
  letI : IsProbabilityMeasure setup.samplePairLaw := setup.samplePairLaw_probability
  simpa using
    (integral_inner_sub_mean_eq_zero_of_integral_eq
      (μ := setup.samplePairLaw)
      (F := fun q : S × ι =>
        (setup.p q.2)⁻¹ •
          PiLp.single 2 q.2 (setup.blockCoord q.2 (setup.gradL z q.1)))
      (mean := setup.g z) (direction := x - z)
      (by simpa using fixed_pair_lifted_gradBlock_integrable setup z hz)
      (by simpa using fixed_pair_lifted_gradBlock_unbiased setup z hz))

/-- The deterministic mean oracle `g` is measurable on the feasible carrier.

Candidate audit: no setup field states measurability of `g`; SOptLib's
`oracleMean_measurable_of_joint_measurable` applies because on feasible points
`setup.hunbiased` identifies `g z` with the Bochner mean of the jointly
measurable stochastic oracle in Lan Eq. (4.6.3). -/
private theorem feasible_g_measurable
    (setup : StochasticBlockMirrorDescentSetup ι S) :
    Measurable (fun z : setup.FeasibleState => setup.g z.1) := by
  letI : IsProbabilityMeasure setup.oracleSampleLaw := setup.oracleSampleLaw_probability
  exact oracleMean_measurable_of_eq_integral
    (μ := setup.oracleSampleLaw)
    (G := fun z : setup.FeasibleState => fun s : S => setup.gradL z.1 s)
    (g := fun z : setup.FeasibleState => setup.g z.1)
    (by
      exact setup.hgradL_measurable.comp
        ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd))
    (by
      intro z
      simpa [StochasticBlockMirrorDescentSetup.oracleSampleLaw] using
        (setup.hunbiased z.1 z.2).symm)

/-- Local finite dispatch measurability outside the setup namespace.

Candidate audit: the target file has an earlier private `finite_dispatch_measurable`
inside `StochasticBlockMirrorDescentSetup`; it is not accessible after the
namespace boundary where the martingale helpers live. This copy keeps the same
Mathlib piecewise-cover proof and serves only the scalar kernel measurability
side condition for Eq. (4.6.21). -/
private theorem finite_dispatch_measurable_kernel
    {α β δ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace δ]
    [Fintype δ] [MeasurableSingletonClass δ] [Nonempty δ]
    {idx : α → δ} {f : δ → α → β}
    (hidx : Measurable idx) (hf : ∀ i, Measurable (f i)) :
    Measurable (fun a => f (idx a) a) := by
  classical
  let fiber : δ → Set α := fun i => idx ⁻¹' ({i} : Set δ)
  have hfiber : ∀ i, MeasurableSet (fiber i) := by
    intro i
    exact (measurableSet_singleton i).preimage hidx
  have hpair :
      Pairwise fun i j => Set.EqOn (f i) (f j) (fiber i ∩ fiber j) := by
    intro i j hij a ha
    have hi : idx a = i := by simpa [fiber] using ha.1
    have hj : idx a = j := by simpa [fiber] using ha.2
    exact False.elim (hij (hi.symm.trans hj))
  obtain ⟨g, hg, hgon⟩ := exists_measurable_piecewise fiber hfiber f hf hpair
  have hfg : (fun a => f (idx a) a) = g := by
    funext a
    have ha : a ∈ fiber (idx a) := by simp [fiber]
    exact (hgon (idx a) ha).symm
  rw [hfg]
  exact hg

/-- Joint measurability of the scalar fixed-pair delta kernel.

This is the `hGg_meas` side condition for
`condExp_oracle_noise_eq_zero_of_iid_adapted`; it combines the jointly
measurable stochastic oracle, finite block dispatch, and the feasible-carrier
measurability of `g` derived above from Eq. (4.6.3). -/
private theorem scalar_delta_kernel_measurable
    (setup : StochasticBlockMirrorDescentSetup ι S)
    (x : setup.StateSpace) :
    Measurable
      (fun p : setup.FeasibleState × (S × ι) =>
        ⟪(setup.p p.2.2)⁻¹ •
            PiLp.single 2 p.2.2 (setup.blockCoord p.2.2 (setup.gradL p.1.1 p.2.1)) -
            setup.g p.1.1,
          x - p.1.1⟫_ℝ) := by
  simpa [StochasticBlockMirrorDescentSetup.blockCoord] using
    (oracle_scalar_deviation_kernel_measurable_of_finite_dispatch
      (X := setup.FeasibleState) (S := S)
      (Block := fun i : ι => setup.Block i)
      (grad := fun z s => setup.gradL z.1 s)
      (mean := fun z => setup.g z.1)
      (eval := fun z => z.1)
      (weight := fun i => (setup.p i)⁻¹)
      (target := x)
      (by
        exact setup.hgradL_measurable.comp
          ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd))
      (feasible_g_measurable setup)
      measurable_subtype_coe)

/-- Uniform blockwise primal-norm displacement bound against a fixed comparison
point.

Candidate audit: `Bornology.IsBounded.exists_norm_le` gives the ambient bound
from the bounded block carrier, while the target-file
`seminorm_upper_bound_by_ambient_norm_of_finite_dimensional` is the required
paper-norm bridge; SOptLib compact/Lipschitz bound helpers were considered but
do not expose the literal block seminorm `‖·‖_i` needed for Lan Eq. (4.6.7). -/
private theorem block_primal_displacement_bound
    (setup : StochasticBlockMirrorDescentSetup ι S)
    (x : setup.StateSpace) :
    ∃ R : ι → ℝ, (∀ i, 0 ≤ R i) ∧
      ∀ z : setup.FeasibleState, ∀ i,
        setup.blockPrimalNorm i (x i - z.1 i) ≤ R i := by
  simpa [StochasticBlockMirrorDescentSetup.X, StochasticBlockMirrorDescentSetup.StateSpace,
    StochasticBlockMirrorDescentSetup.Block] using
      exists_uniform_seminorm_sub_bound_of_bounded_sets
        (X := setup.XBlock) (p := setup.blockPrimalNorm) (x := fun i => x i)
        (coord := fun z : setup.FeasibleState => fun i => z.1 i)
        (hcoord := fun z i => by
          simpa [StochasticBlockMirrorDescentSetup.X] using z.2 i)
        setup.hXBlock_bounded

/-- Fixed-fiber `L¹` control of each sampled block dual norm from the source
second-moment assumption.

Candidate audit: `integrable_of_integrable_norm_sq` and the local
`aestronglyMeasurable_of_integrable_sq_of_nonneg` exactly match the L²-to-L¹
part, while `block_second_moment_expectation` supplies Lan Eq. (4.6.4);
SOptLib oracle residual lemmas were considered but are vector-noise wrappers,
not this scalar block-dual-norm fiber estimate. -/
private theorem block_dual_norm_gradBlock_l1_bound
    (setup : StochasticBlockMirrorDescentSetup ι S)
    (i : ι) (z : setup.StateSpace) (hz : z ∈ setup.X) :
    Integrable
        (fun s => SOptLib.canonicalDualNorm (setup.blockPrimalNorm i) (setup.blockCoord i (setup.gradL z s)))
        setup.oracleSampleLaw ∧
      ∫ s, SOptLib.canonicalDualNorm (setup.blockPrimalNorm i) (setup.blockCoord i (setup.gradL z s)) ∂setup.oracleSampleLaw
        ≤ setup.M i ^ 2 + 1 := by
  letI : IsProbabilityMeasure setup.oracleSampleLaw := setup.oracleSampleLaw_probability
  exact integrable_of_nonneg_sq_integrable_integral_le_sq_bound_add_one
    (μ := setup.oracleSampleLaw)
    (Z := fun s => SOptLib.canonicalDualNorm (setup.blockPrimalNorm i)
      (setup.blockCoord i (setup.gradL z s)))
    (C := setup.M i ^ 2)
    (by simpa using (setup.block_second_moment_expectation i z hz).1)
    (Filter.Eventually.of_forall (by
      intro s
      simpa [canonicalDualNormFromPrimal] using
        canonicalDualNormFromPrimal_nonneg (setup.blockPrimalNorm i)
          (setup.blockPrimalNorm_isPaperNorm i) (setup.blockCoord i (setup.gradL z s))))
    (by simpa using (setup.block_second_moment_expectation i z hz).2)

/-- Deterministic block mean dual norm bound derived from Eq. (4.6.4).

Candidate audit: `derived_block_norm_bounds` is the exact source-derived
squared block bound for `g_i`; this helper only extracts its nonnegative square
root form using `setup.M_nonneg`, rather than appealing to the retired ambient
norm comparison scaffold. -/
private theorem gBlock_dual_norm_le_M
    (setup : StochasticBlockMirrorDescentSetup ι S)
    (i : ι) (z : setup.StateSpace) (hz : z ∈ setup.X) :
    SOptLib.canonicalDualNorm (setup.blockPrimalNorm i) (setup.gBlock i z) ≤ setup.M i := by
  have hsq := derived_block_norm_bounds setup z hz i
  have hleft_nonneg : 0 ≤ SOptLib.canonicalDualNorm (setup.blockPrimalNorm i) (setup.gBlock i z) := by
    simpa [canonicalDualNormFromPrimal] using
      canonicalDualNormFromPrimal_nonneg (setup.blockPrimalNorm i)
        (setup.blockPrimalNorm_isPaperNorm i) (setup.gBlock i z)
  have hM_nonneg := setup.M_nonneg i
  nlinarith

/-- Pointwise scalar bound for the sampled lifted block oracle term.

Candidate audit: `setup.blockDualNorm_support_bound` is the exact Lan
Eq. (4.6.4) primal/dual support inequality, and
`block_primal_displacement_bound` supplies the required paper primal displacement
budget; SOptLib inner-product boundedness lemmas were considered but use ambient
Hilbert norms instead of the block primal norm. -/
private theorem sampled_lifted_block_inner_abs_le
    (setup : StochasticBlockMirrorDescentSetup ι S)
    (x : setup.StateSpace) (R : ι → ℝ)
    (hR_nonneg : ∀ i, 0 ≤ R i)
    (hR : ∀ z : setup.FeasibleState, ∀ i,
      setup.blockPrimalNorm i (x i - z.1 i) ≤ R i)
    (z : setup.FeasibleState) (i : ι) (ζ : setup.Block i) :
    |⟪(setup.p i)⁻¹ • PiLp.single 2 i ζ, x - z.1⟫_ℝ| ≤
      (setup.p i)⁻¹ * SOptLib.canonicalDualNorm (setup.blockPrimalNorm i) ζ * R i := by
  exact
    abs_inner_smul_lift_le_dual_norm_mul_block_radius
      (c := (setup.p i)⁻¹)
      (lift := fun j η => PiLp.single 2 j η)
      (coord := fun j (v : setup.StateSpace) => setup.blockCoord j v)
      (dualNorm := fun j η => SOptLib.canonicalDualNorm (setup.blockPrimalNorm j) η)
      (primalNorm := fun j η => setup.blockPrimalNorm j η)
      (R := R) (i := i) (ζ := ζ) (d := x - z.1)
      (inv_nonneg.mpr (le_of_lt (setup.hp_pos i)))
      (setup.blockDualLift_pairing i (x - z.1) ζ)
      (setup.blockDualNorm_support_bound i ζ (setup.blockCoord i (x - z.1)))
      (by
        simpa [canonicalDualNormFromPrimal] using
          canonicalDualNormFromPrimal_nonneg (setup.blockPrimalNorm i)
            (setup.blockPrimalNorm_isPaperNorm i) ζ)
      (by
        simpa [StochasticBlockMirrorDescentSetup.blockCoord, Pi.sub_apply] using hR z i)

/-- Pointwise scalar bound for the deterministic mean oracle term.

Candidate audit: the only source-faithful deterministic oracle-size fact is
`derived_block_norm_bounds`, extracted above as `gBlock_dual_norm_le_M`; the
retired ambient comparison theorem was deliberately rejected because it is
documented false for the canonical paper dual norm. -/
private theorem g_inner_abs_le_sum_M_mul_R
    (setup : StochasticBlockMirrorDescentSetup ι S)
    (x : setup.StateSpace) (R : ι → ℝ)
    (hR_nonneg : ∀ i, 0 ≤ R i)
    (hR : ∀ z : setup.FeasibleState, ∀ i,
      setup.blockPrimalNorm i (x i - z.1 i) ≤ R i)
    (z : setup.FeasibleState) :
    |⟪setup.g z.1, x - z.1⟫_ℝ| ≤
      Finset.sum Finset.univ (fun i => setup.M i * R i) := by
  classical
  refine abs_inner_block_sum_le_sum_dual_bound_mul_radius
    (lift := fun i ζ => PiLp.single 2 i ζ)
    (coord := fun i y => setup.blockCoord i y)
    (g := setup.g z.1)
    (gBlock := fun i => setup.gBlock i z.1)
    (d := x - z.1)
    (dual := fun i => SOptLib.canonicalDualNorm (setup.blockPrimalNorm i) (setup.gBlock i z.1))
    (radius := fun i => setup.blockPrimalNorm i (setup.blockCoord i (x - z.1)))
    (M := setup.M) (R := R) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · symm
    simpa [StochasticBlockMirrorDescentSetup.gBlock] using
      setup.blockDualLift_sum_blockCoord (setup.g z.1)
  · intro i ζ v
    have hbase := setup.blockDualLift_pairing i v ζ
    rw [real_inner_comm]
    rw [← hbase]
    rw [real_inner_comm]
  · intro i
    exact setup.blockDualNorm_support_bound i (setup.gBlock i z.1)
      (setup.blockCoord i (x - z.1))
  · intro i
    exact gBlock_dual_norm_le_M setup i z.1 z.2
  · intro i
    exact apply_nonneg (setup.blockPrimalNorm i) (setup.blockCoord i (x - z.1))
  · intro i
    simpa [StochasticBlockMirrorDescentSetup.blockCoord, Pi.sub_apply] using hR z i
  · exact setup.M_nonneg

/-- Pointwise domination of the fixed-fiber scalar delta kernel.

Candidate audit: this combines the two route-local pointwise estimates above;
SOptLib's `Integrable.inner_sub_const_of_bounded` was considered, but its
ambient bounded-displacement hypothesis does not match the paper block
primal/dual norm budget required for Lan Eq. (4.6.21). -/
private theorem scalar_delta_abs_pointwise_le
    (setup : StochasticBlockMirrorDescentSetup ι S)
    (x : setup.StateSpace) (R : ι → ℝ)
    (hR_nonneg : ∀ i, 0 ≤ R i)
    (hR : ∀ z : setup.FeasibleState, ∀ i,
      setup.blockPrimalNorm i (x i - z.1 i) ≤ R i)
    (z : setup.FeasibleState) (q : S × ι) :
    ‖⟪(setup.p q.2)⁻¹ •
          PiLp.single 2 q.2 (setup.blockCoord q.2 (setup.gradL z.1 q.1)) - setup.g z.1,
        x - z.1⟫_ℝ - (0 : ℝ)‖ ≤
      (setup.p q.2)⁻¹ *
          SOptLib.canonicalDualNorm (setup.blockPrimalNorm q.2) (setup.blockCoord q.2 (setup.gradL z.1 q.1)) * R q.2 +
        Finset.sum Finset.univ (fun i => setup.M i * R i) := by
  exact
    abs_scalar_block_oracle_noise_le_sample_majorant_add_mean_bound
      (sample := fun q : S × ι =>
        (setup.p q.2)⁻¹ •
          PiLp.single 2 q.2 (setup.blockCoord q.2 (setup.gradL z.1 q.1)))
      (mean := fun _ : S × ι => setup.g z.1)
      (displacement := fun _ : S × ι => x - z.1)
      (sampleMajorant := fun q : S × ι =>
        (setup.p q.2)⁻¹ *
          SOptLib.canonicalDualNorm (setup.blockPrimalNorm q.2)
            (setup.blockCoord q.2 (setup.gradL z.1 q.1)) * R q.2)
      (meanMajorant := fun _ : S × ι =>
        Finset.sum Finset.univ (fun i => setup.M i * R i))
      (by
        intro q
        simpa using
          sampled_lifted_block_inner_abs_le setup x R hR_nonneg hR z q.2
            (setup.blockCoord q.2 (setup.gradL z.1 q.1)))
      (by
        intro q
        simpa using g_inner_abs_le_sum_M_mul_R setup x R hR_nonneg hR z)
      q

/-- Fixed-fiber `L¹` bound for the sampled scalar majorant.

Candidate audit: this is the finite-block/product-law part of Lan
Eq. (4.6.21)'s integrability side condition. Existing SOptLib transfer lemmas
handle random-parameter composition after a uniform fixed-fiber bound, but they
do not build this paper-specific block majorant from `p_i`, `M_i`, and the
paper primal displacement budget. -/
private theorem sampled_scalar_majorant_l1_bound
    (setup : StochasticBlockMirrorDescentSetup ι S)
    (R : ι → ℝ) (hR_nonneg : ∀ i, 0 ≤ R i)
    (z : setup.FeasibleState) :
    Integrable
        (fun q : S × ι =>
          (setup.p q.2)⁻¹ *
            SOptLib.canonicalDualNorm (setup.blockPrimalNorm q.2) (setup.blockCoord q.2 (setup.gradL z.1 q.1)) * R q.2)
        setup.samplePairLaw ∧
      ∫ q : S × ι,
          (setup.p q.2)⁻¹ *
            SOptLib.canonicalDualNorm (setup.blockPrimalNorm q.2) (setup.blockCoord q.2 (setup.gradL z.1 q.1)) * R q.2
          ∂setup.samplePairLaw ≤
        Finset.sum Finset.univ
          (fun i => (setup.p i)⁻¹ * R i * (setup.M i ^ 2 + 1)) := by
  classical
  letI : IsProbabilityMeasure setup.oracleSampleLaw := setup.oracleSampleLaw_probability
  letI : IsProbabilityMeasure setup.blockIndexLaw := by
    unfold StochasticBlockMirrorDescentSetup.blockIndexLaw finiteBlockIndexLaw
    infer_instance
  simpa [StochasticBlockMirrorDescentSetup.samplePairLaw] using
    (selected_block_majorant_integral_le_sum_inv_prob_bound
      (μ := setup.oracleSampleLaw) (ν := setup.blockIndexLaw)
      (p := setup.p)
      (Z := fun i s =>
        SOptLib.canonicalDualNorm (setup.blockPrimalNorm i) (setup.blockCoord i (setup.gradL z.1 s)))
      (R := R) (B := fun i => setup.M i ^ 2 + 1)
      setup.hp_pos hR_nonneg
      (fun i s => by
        simpa [canonicalDualNormFromPrimal] using
          canonicalDualNormFromPrimal_nonneg (setup.blockPrimalNorm i)
            (setup.blockPrimalNorm_isPaperNorm i) (setup.blockCoord i (setup.gradL z.1 s)))
      (fun i => (block_dual_norm_gradBlock_l1_bound setup i z.1 z.2).1)
      (fun i => (block_dual_norm_gradBlock_l1_bound setup i z.1 z.2).2))

set_option maxHeartbeats 2000000

/-- Uniform fixed-fiber `L¹` bound for the scalar delta kernel in Eq. (4.6.21).

Candidate audit: `integrable_comp_of_indep_fixed_integral_bound` is the planned
consumer of this fixed-fiber estimate, not a provider of the estimate itself;
the bound here is built from the paper-specific block displacement helper,
`blockDualNorm_support_bound`, `block_second_moment_expectation`, and
`derived_block_norm_bounds`. -/
private theorem fixed_pair_scalar_delta_abs_uniform_bound
    (setup : StochasticBlockMirrorDescentSetup ι S)
    (x : setup.StateSpace) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ z : setup.FeasibleState,
        Integrable
          (fun q : S × ι =>
            ‖⟪(setup.p q.2)⁻¹ •
                PiLp.single 2 q.2 (setup.blockCoord q.2 (setup.gradL z.1 q.1)) - setup.g z.1,
              x - z.1⟫_ℝ - (0 : ℝ)‖)
          setup.samplePairLaw ∧
        ∫ q : S × ι,
            ‖⟪(setup.p q.2)⁻¹ •
                PiLp.single 2 q.2 (setup.blockCoord q.2 (setup.gradL z.1 q.1)) - setup.g z.1,
              x - z.1⟫_ℝ - (0 : ℝ)‖ ∂setup.samplePairLaw ≤ C := by
  classical
  letI : IsProbabilityMeasure setup.samplePairLaw := setup.samplePairLaw_probability
  obtain ⟨R, hR_nonneg, hR⟩ := block_primal_displacement_bound setup x
  let Csample : ℝ :=
    Finset.sum Finset.univ
      (fun i => (setup.p i)⁻¹ * R i * (setup.M i ^ 2 + 1))
  let Cg : ℝ := Finset.sum Finset.univ (fun i => setup.M i * R i)
  let noise : setup.FeasibleState → S × ι → ℝ := fun z q =>
    ⟪(setup.p q.2)⁻¹ •
        PiLp.single 2 q.2 (setup.blockCoord q.2 (setup.gradL z.1 q.1)) - setup.g z.1,
      x - z.1⟫_ℝ - (0 : ℝ)
  let majorant : setup.FeasibleState → S × ι → ℝ := fun z q =>
    (setup.p q.2)⁻¹ *
      SOptLib.canonicalDualNorm (setup.blockPrimalNorm q.2)
        (setup.blockCoord q.2 (setup.gradL z.1 q.1)) * R q.2
  have hCsample_nonneg : 0 ≤ Csample := by
    dsimp [Csample]
    exact Finset.sum_nonneg (fun i _hi =>
      mul_nonneg
        (mul_nonneg (inv_nonneg.mpr (le_of_lt (setup.hp_pos i))) (hR_nonneg i))
        (by nlinarith [sq_nonneg (setup.M i)]))
  have hCg_nonneg : 0 ≤ Cg := by
    dsimp [Cg]
    exact Finset.sum_nonneg (fun i _hi =>
      mul_nonneg (setup.M_nonneg i) (hR_nonneg i))
  have hnoise_int : ∀ z, Integrable (noise z) setup.samplePairLaw := by
    intro z
    have hscalar :
        Integrable
          (fun q : S × ι =>
            ⟪(setup.p q.2)⁻¹ •
                PiLp.single 2 q.2 (setup.blockCoord q.2 (setup.gradL z.1 q.1)) -
            setup.g z.1,
          x - z.1⟫_ℝ)
        setup.samplePairLaw :=
      (fixed_pair_scalar_delta_centered setup x z.1 z.2).1
    simpa [noise] using hscalar
  have hmajorant_int : ∀ z, Integrable (majorant z) setup.samplePairLaw := by
    intro z
    simpa [majorant] using (sampled_scalar_majorant_l1_bound setup R hR_nonneg z).1
  have hmajorant_bound :
      ∀ z, ∫ q, majorant z q ∂setup.samplePairLaw ≤ Csample := by
    intro z
    simpa [majorant, Csample] using
      (sampled_scalar_majorant_l1_bound setup R hR_nonneg z).2
  have hpoint : ∀ z q, ‖noise z q‖ ≤ majorant z q + Cg := by
    intro z q
    simpa [noise, majorant, Cg] using
      scalar_delta_abs_pointwise_le setup x R hR_nonneg hR z q
  change ∃ C : ℝ, 0 ≤ C ∧
    ∀ z : setup.FeasibleState,
      Integrable (fun q : S × ι => ‖noise z q‖) setup.samplePairLaw ∧
        ∫ q : S × ι, ‖noise z q‖ ∂setup.samplePairLaw ≤ C
  exact
    exists_uniform_l1_bound_scalar_block_oracle_noise
      (ν := setup.samplePairLaw)
      (noise := noise)
      (majorant := majorant)
      (C := Csample) (D := Cg)
      hCsample_nonneg hCg_nonneg hnoise_int hmajorant_int hmajorant_bound hpoint

/-- The adapted feasible iterate is independent of the fresh current sample.

This aligns Lan Theorem 4.12 proof step 3 with SOptLib's
`indepFun_of_past_measurable_current_iid_sample`: the iterate is measurable
with respect to the strict-prefix filtration, while the current sample-pair is
independent of that filtration. -/
private theorem current_sample_indep_feasible_state
    (setup : StochasticBlockMirrorDescentSetup ι S)
    (k : ℕ) :
    IndepFun
      (fun ω : StochasticBlockSamplePath S ι => (setup.process k ω).x)
      (setup.samplePair k) setup.P := by
  exact
    indepFun_of_past_measurable_current_iid_sample
      (μ := setup.P)
      (past := setup.sampleFiltration k)
      (X := fun ω : StochasticBlockSamplePath S ι => (setup.process k ω).x)
      (Y := setup.samplePair k)
      (setup.xFeasibleIter_measurable_sampleFiltration k)
      (setup.currentSample_independent_past k)

/-- Integrability of the random-iterate scalar delta kernel in Eq. (4.6.21).

This consumes the paper-specific fixed-fiber bound
`fixed_pair_scalar_delta_abs_uniform_bound` through SOptLib's
`integrable_comp_of_indep_fixed_integral_bound`, using the current-sample law
`setup.samplePair_law k`. -/
private theorem scalar_delta_process_integrable
    (setup : StochasticBlockMirrorDescentSetup ι S)
    (x : setup.StateSpace) (k : ℕ) :
    Integrable
      (fun ω : StochasticBlockSamplePath S ι =>
        ⟪(setup.p (setup.samplePair k ω).2)⁻¹ •
            PiLp.single 2 (setup.samplePair k ω).2
              (setup.blockCoord (setup.samplePair k ω).2
                (setup.gradL ((setup.process k ω).x).1 (setup.samplePair k ω).1)) -
            setup.g ((setup.process k ω).x).1,
          x - ((setup.process k ω).x).1⟫_ℝ - (0 : ℝ))
      setup.P := by
  classical
  letI : IsProbabilityMeasure setup.P := setup.P_probability
  let X : StochasticBlockSamplePath S ι → setup.FeasibleState :=
    fun ω => (setup.process k ω).x
  have hX_meas : Measurable X := by
    have hx_adapted := setup.xFeasibleIter_measurable_sampleFiltration k
    have hm_le : setup.sampleFiltration k ≤ MeasurableSpace.pi := by
      simpa using setup.sampleFiltration.le k
    simpa [X] using hx_adapted.mono hm_le le_rfl
  obtain ⟨C, hC_nonneg, hC⟩ := fixed_pair_scalar_delta_abs_uniform_bound setup x
  simpa [X] using
    integrable_scalar_oracle_noise_of_indep_uniform_l1_bound
      (P := setup.P) (ν := setup.samplePairLaw)
      (X := X)
      (Y := setup.samplePair k)
      (noise := fun z q =>
        ⟪(setup.p q.2)⁻¹ • PiLp.single 2 q.2
            (setup.blockCoord q.2 (setup.gradL z.1 q.1)) - setup.g z.1,
          x - z.1⟫_ℝ)
      (C := C)
      (by simpa [Function.uncurry] using scalar_delta_kernel_measurable setup x)
      hX_meas
      (by simpa using setup.samplePair_measurable k)
      (by simpa using current_sample_indep_feasible_state setup k)
      (by simpa using setup.samplePair_law k)
      hC_nonneg
      (fun z => by simpa using (hC z).1)
      (fun z => by simpa using (hC z).2)

/-! Used in: `theorem_4_12` to remove the martingale-difference term by the
conditional-expectation cancellation in Eq. (4.6.21). -/
theorem step_4_6_21
    (setup : StochasticBlockMirrorDescentSetup ι S)
    (x : setup.StateSpace) (k : ℕ) :
    setup.P[setup.delta x k|setup.sampleFiltration k] =ᵐ[setup.P] fun _ => (0 : ℝ) := by
  letI : IsProbabilityMeasure setup.P := setup.P_probability
  have hpast : Indep (setup.sampleFiltration k)
      (MeasurableSpace.comap (setup.samplePair k) (by infer_instance : MeasurableSpace (S × ι)))
      setup.P :=
    setup.currentSample_independent_past k
  let Φ : setup.FeasibleState → S × ι → ℝ := fun z q =>
    ⟪(setup.p q.2)⁻¹ •
        PiLp.single 2 q.2 (setup.blockCoord q.2 (setup.gradL z.1 q.1)) - setup.g z.1,
      x - z.1⟫_ℝ
  have hx_feas_adapted :
      Measurable[setup.sampleFiltration k] (fun ω => (setup.process k ω).x) := by
    simpa using setup.xFeasibleIter_measurable_sampleFiltration k
  have hm_le : setup.sampleFiltration k ≤ MeasurableSpace.pi := by
    simpa using setup.sampleFiltration.le k
  have hx_feas_full :
      @Measurable (StochasticBlockSamplePath S ι) setup.FeasibleState
        MeasurableSpace.pi Subtype.instMeasurableSpace
        (fun ω => (setup.process k ω).x) :=
    hx_feas_adapted.mono hm_le le_rfl
  have hΦ_meas :
      Measurable (fun p : setup.FeasibleState × (S × ι) => Φ p.1 p.2 - (0 : ℝ)) := by
    simpa [Φ] using scalar_delta_kernel_measurable setup x
  have h_indep :
      ∀ A : Set (StochasticBlockSamplePath S ι), MeasurableSet[setup.sampleFiltration k] A →
        IndepFun (fun ω => (A.indicator (fun _ => (1 : ℝ)) ω, (setup.process k ω).x))
          (setup.samplePair k) setup.P := by
    intro A hA
    have hleft :
        Measurable[setup.sampleFiltration k]
          (fun ω => (A.indicator (fun _ => (1 : ℝ)) ω, (setup.process k ω).x)) :=
      (measurable_const.indicator hA).prodMk hx_feas_adapted
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le_left hpast hleft.comap_le
  have hΦ_fixed :
      ∀ z : setup.FeasibleState,
        Integrable (Φ z) setup.samplePairLaw ∧
          ∫ q : S × ι, Φ z q ∂setup.samplePairLaw = 0 := by
    intro z
    simpa [Φ] using fixed_pair_scalar_delta_centered setup x z.1 z.2
  have hfixed_zero :
      ∀ z : setup.FeasibleState,
        ∫ q : S × ι, Φ z q - (0 : ℝ) ∂setup.samplePairLaw = 0 := by
    intro z
    simpa using (hΦ_fixed z).2
  have h_int :
      Integrable
        (fun ω : StochasticBlockSamplePath S ι =>
          Φ ((setup.process k ω).x) (setup.samplePair k ω) - (0 : ℝ))
        setup.P := by
    simpa [Φ] using scalar_delta_process_integrable setup x k
  have hfixed_zero_map :
      ∀ z : setup.FeasibleState,
        ∫ q : S × ι, Φ z q - (0 : ℝ) ∂Measure.map (setup.samplePair k) setup.P = 0 := by
    intro z
    rw [setup.samplePair_law k]
    exact hfixed_zero z
  have hce :
      setup.P[(fun ω : StochasticBlockSamplePath S ι =>
          Φ ((setup.process k ω).x) (setup.samplePair k ω) - (0 : ℝ))|
          setup.sampleFiltration k] =ᵐ[setup.P] fun _ => (0 : ℝ) := by
    exact condExp_oracle_noise_eq_zero_of_iid_adapted
      (μ := setup.P) (m := setup.sampleFiltration k) (hm := hm_le)
      (G := Φ) (g := fun _ : setup.FeasibleState => (0 : ℝ))
      (x := fun ω : StochasticBlockSamplePath S ι => (setup.process k ω).x)
      (Y := setup.samplePair k)
      hΦ_meas hx_feas_adapted hx_feas_full (setup.samplePair_measurable k)
      h_indep h_int hfixed_zero_map
  simpa [Φ, StochasticBlockMirrorDescentSetup.delta, SOptLib.iterateProcessView,
    StochasticBlockMirrorDescentSetup.ξ, StochasticBlockMirrorDescentSetup.block] using hce

/-! Fixed-pair expansion for Eq. (4.6.22). -/

/-- Fixed sample-pair expansion of the quadratic selected-block term.

Candidate audit: `samplePairLaw`, `blockIndexLaw_singleton`, and
`block_second_moment_expectation` are the exact local paper objects; SOptLib's
variance-transfer candidates (`randomIterate_variance_bound_of_fixed_variance`,
`oracleRandomIterateVarianceBound_of_fixedVariance`) are centered vector-noise
wrappers, while this helper needs the literal uncentered Lan Eq. (4.6.4) scalar
kernel and the finite block law from Eq. (4.6.12). -/
private theorem fixed_pair_deltaBar_integral_expansion
    (setup : StochasticBlockMirrorDescentSetup ι S)
    (z : setup.FeasibleState) :
    ∫ q : S × ι,
        (setup.p q.2)⁻¹ *
          SOptLib.canonicalDualNorm (setup.blockPrimalNorm q.2) (setup.blockCoord q.2 (setup.gradL z.1 q.1)) ^ 2
        ∂setup.samplePairLaw =
      Finset.sum Finset.univ (fun i =>
        setup.p i * (setup.p i)⁻¹ *
          ∫ s, SOptLib.canonicalDualNorm (setup.blockPrimalNorm i) (setup.blockCoord i (setup.gradL z.1 s)) ^ 2
            ∂setup.oracleSampleLaw) := by
  classical
  letI : IsProbabilityMeasure setup.oracleSampleLaw := setup.oracleSampleLaw_probability
  letI : IsProbabilityMeasure setup.blockIndexLaw := by
    unfold StochasticBlockMirrorDescentSetup.blockIndexLaw finiteBlockIndexLaw
    infer_instance
  rw [StochasticBlockMirrorDescentSetup.samplePairLaw]
  calc
    ∫ q : S × ι,
        (setup.p q.2)⁻¹ *
          SOptLib.canonicalDualNorm (setup.blockPrimalNorm q.2) (setup.blockCoord q.2 (setup.gradL z.1 q.1)) ^ 2
        ∂setup.oracleSampleLaw.prod setup.blockIndexLaw =
      Finset.sum Finset.univ (fun i =>
        setup.p i *
          ∫ s, (setup.p i)⁻¹ *
            SOptLib.canonicalDualNorm (setup.blockPrimalNorm i) (setup.blockCoord i (setup.gradL z.1 s)) ^ 2
            ∂setup.oracleSampleLaw) := by
        exact integral_selected_finite_index_prod_eq_sum_weights
          (μ := setup.oracleSampleLaw) (ν := setup.blockIndexLaw) (p := setup.p)
          (F := fun i s =>
            (setup.p i)⁻¹ *
              SOptLib.canonicalDualNorm (setup.blockPrimalNorm i) (setup.blockCoord i (setup.gradL z.1 s)) ^ 2)
          (fun i => by
            rw [Measure.real, setup.blockIndexLaw_singleton i]
            simp [le_of_lt (setup.hp_pos i)])
          (fun i => by
            simpa [mul_assoc, mul_comm, mul_left_comm] using
              (setup.block_second_moment_expectation i z.1 z.2).1.const_mul ((setup.p i)⁻¹))
    _ = Finset.sum Finset.univ (fun i =>
        setup.p i * (setup.p i)⁻¹ *
          ∫ s, SOptLib.canonicalDualNorm (setup.blockPrimalNorm i) (setup.blockCoord i (setup.gradL z.1 s)) ^ 2
            ∂setup.oracleSampleLaw) := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [integral_const_mul, mul_assoc]

/-- Fixed sample-pair bound for the quadratic selected-block term.

This consumes `fixed_pair_deltaBar_integral_expansion` and applies Lan
Eq. (4.6.4) block by block; the remaining random-iterate theorem needs to
transport this fixed-fiber estimate through current-sample independence. -/
private theorem fixed_pair_deltaBar_integral_bound
    (setup : StochasticBlockMirrorDescentSetup ι S)
    (z : setup.FeasibleState) :
    ∫ q : S × ι,
        (setup.p q.2)⁻¹ *
          SOptLib.canonicalDualNorm (setup.blockPrimalNorm q.2) (setup.blockCoord q.2 (setup.gradL z.1 q.1)) ^ 2
        ∂setup.samplePairLaw ≤
      Finset.sum Finset.univ (fun i => (setup.M i) ^ 2) := by
  classical
  letI : IsProbabilityMeasure setup.oracleSampleLaw := setup.oracleSampleLaw_probability
  letI : IsProbabilityMeasure setup.blockIndexLaw := by
    unfold StochasticBlockMirrorDescentSetup.blockIndexLaw finiteBlockIndexLaw
    infer_instance
  rw [StochasticBlockMirrorDescentSetup.samplePairLaw]
  exact selected_block_second_moment_integral_le_sum_bounds
    (μ := setup.oracleSampleLaw) (ν := setup.blockIndexLaw)
    (p := setup.p) (M := setup.M)
    (Z := fun i s =>
      SOptLib.canonicalDualNorm (setup.blockPrimalNorm i) (setup.blockCoord i (setup.gradL z.1 s)) ^ 2)
    setup.hp_pos
    (fun i => by
      rw [Measure.real, setup.blockIndexLaw_singleton i]
      simp [le_of_lt (setup.hp_pos i)])
    (fun i => (setup.block_second_moment_expectation i z.1 z.2).1)
    (fun i => (setup.block_second_moment_expectation i z.1 z.2).2)

/-- Fixed sample-pair integrability of the quadratic selected-block term. -/
private theorem fixed_pair_deltaBar_integrable
    (setup : StochasticBlockMirrorDescentSetup ι S)
    (z : setup.FeasibleState) :
    Integrable
      (fun q : S × ι =>
        (setup.p q.2)⁻¹ *
          SOptLib.canonicalDualNorm (setup.blockPrimalNorm q.2) (setup.blockCoord q.2 (setup.gradL z.1 q.1)) ^ 2)
      setup.samplePairLaw := by
  classical
  letI : IsProbabilityMeasure setup.oracleSampleLaw := setup.oracleSampleLaw_probability
  letI : IsProbabilityMeasure setup.blockIndexLaw := by
    unfold StochasticBlockMirrorDescentSetup.blockIndexLaw finiteBlockIndexLaw
    infer_instance
  let G : ι → S × ι → ℝ := fun i q =>
    ({r : S × ι | r.2 = i}.indicator
      (fun q => (setup.p i)⁻¹ *
        SOptLib.canonicalDualNorm (setup.blockPrimalNorm i) (setup.blockCoord i (setup.gradL z.1 q.1)) ^ 2) q)
  have hGint : ∀ i ∈ Finset.univ, Integrable (G i) setup.samplePairLaw := by
    intro i _hi
    have hbaseS :
        Integrable
          (fun s => (setup.p i)⁻¹ *
            SOptLib.canonicalDualNorm (setup.blockPrimalNorm i) (setup.blockCoord i (setup.gradL z.1 s)) ^ 2)
          setup.oracleSampleLaw := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using
        (setup.block_second_moment_expectation i z.1 z.2).1.const_mul ((setup.p i)⁻¹)
    have hbaseProd :
        Integrable
          (fun q : S × ι => (setup.p i)⁻¹ *
            SOptLib.canonicalDualNorm (setup.blockPrimalNorm i) (setup.blockCoord i (setup.gradL z.1 q.1)) ^ 2)
          setup.samplePairLaw := by
      rw [StochasticBlockMirrorDescentSetup.samplePairLaw]
      simpa using hbaseS.comp_fst setup.blockIndexLaw
    have hset : MeasurableSet ({r : S × ι | r.2 = i} : Set (S × ι)) := by
      exact measurable_snd (measurableSet_singleton i)
    exact hbaseProd.indicator hset
  have hsum : Integrable (fun q => Finset.sum Finset.univ (fun i => G i q))
      setup.samplePairLaw :=
    MeasureTheory.integrable_finset_sum (s := Finset.univ) (μ := setup.samplePairLaw) hGint
  refine hsum.congr ?_
  filter_upwards with q
  dsimp [G]
  symm
  rw [Finset.sum_eq_single q.2]
  · simp
  · intro j _hj hji
    have hq : q.2 ≠ j := fun h => hji h.symm
    simp [hq]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ q.2))

/-- Random-iterate bound for the selected quadratic `deltaBar` kernel. -/
private theorem random_deltaBar_integral_bound
    (setup : StochasticBlockMirrorDescentSetup ι S)
    (k : ℕ) :
    ∫ ω, setup.deltaBar k ω ∂setup.P ≤
      Finset.sum Finset.univ (fun i => (setup.M i) ^ 2) := by
  classical
  letI : IsProbabilityMeasure setup.P := setup.P_probability
  letI : IsProbabilityMeasure setup.samplePairLaw := setup.samplePairLaw_probability
  let X : StochasticBlockSamplePath S ι → setup.FeasibleState :=
    fun ω => (setup.process k ω).x
  let Y : StochasticBlockSamplePath S ι → S × ι := setup.samplePair k
  let φ : setup.FeasibleState → S × ι → ℝ := fun z q =>
    (setup.p q.2)⁻¹ *
      SOptLib.canonicalDualNorm (setup.blockPrimalNorm q.2) (setup.blockCoord q.2 (setup.gradL z.1 q.1)) ^ 2
  have hφ_meas : Measurable (Function.uncurry φ) := by
    haveI : Nonempty ι := by
      by_cases h : Nonempty ι
      · exact h
      · exfalso
        haveI : IsEmpty ι := ⟨fun i => h ⟨i⟩⟩
        have hsum0 : Finset.sum Finset.univ setup.p = 0 := by simp
        linarith [setup.hp_sum, hsum0]
    refine finite_dispatch_measurable_kernel
      (idx := fun p : setup.FeasibleState × (S × ι) => p.2.2)
      (f := fun j p =>
        (setup.p j)⁻¹ *
          SOptLib.canonicalDualNorm (setup.blockPrimalNorm j) (setup.blockCoord j (setup.gradL p.1.1 p.2.1)) ^ 2)
      ?hidx ?hf
    · exact measurable_snd.snd
    · intro j
      have hgrad :
          Measurable
            (fun p : setup.FeasibleState × (S × ι) =>
              setup.blockCoord j (setup.gradL p.1.1 p.2.1)) := by
        have hgraw :
            Measurable
              (fun p : setup.FeasibleState × (S × ι) =>
                setup.gradL p.1.1 p.2.1) := by
          exact setup.hgradL_measurable.comp
            ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd.fst)
        simpa using
          (setup.blockCoord j).measurable.comp hgraw
      have hdual :
          Measurable
            (fun p : setup.FeasibleState × (S × ι) =>
              SOptLib.canonicalDualNorm (setup.blockPrimalNorm j) (setup.blockCoord j (setup.gradL p.1.1 p.2.1))) :=
        ((canonicalDualNormFromPrimal_continuous (setup.blockPrimalNorm j)
          (setup.blockPrimalNorm_isPaperNorm j)).measurable.comp hgrad)
      have hsq := hdual.mul hdual
      simpa [pow_two] using (measurable_const.mul hsq)
  have hX_meas : Measurable X := by
    have hx_adapted := setup.xFeasibleIter_measurable_sampleFiltration k
    have hm_le : setup.sampleFiltration k ≤ MeasurableSpace.pi := by
      simpa using setup.sampleFiltration.le k
    simpa [X] using hx_adapted.mono hm_le le_rfl
  have hY_meas : Measurable Y := by
    simpa [Y] using setup.samplePair_measurable k
  have h_indep : IndepFun X Y setup.P := by
    simpa [X, Y] using current_sample_indep_feasible_state setup k
  have hC_nonneg :
      0 ≤ Finset.sum Finset.univ (fun i => (setup.M i) ^ 2) :=
    Finset.sum_nonneg (fun i _hi => sq_nonneg (setup.M i))
  have h_int : Integrable (fun ω => φ (X ω) (Y ω)) setup.P := by
    exact integrable_comp_of_indep_fixed_integral_bound
      (P := setup.P) (ν := setup.samplePairLaw) (φ := φ)
      (X := X) (Y := Y)
      (C := Finset.sum Finset.univ (fun i => (setup.M i) ^ 2))
      hφ_meas hX_meas hY_meas h_indep
      (by simpa [Y] using setup.samplePair_law k)
      (by
        intro z q
        exact mul_nonneg (inv_nonneg.mpr (le_of_lt (setup.hp_pos q.2))) (sq_nonneg _))
      hC_nonneg
      (fun z => by simpa [φ] using fixed_pair_deltaBar_integrable setup z)
      (fun z => by simpa [φ] using fixed_pair_deltaBar_integral_bound setup z)
  have h_le :
      ∫ ω, φ (X ω) (Y ω) ∂setup.P ≤
        Finset.sum Finset.univ (fun i => (setup.M i) ^ 2) := by
    exact integral_comp_le_of_indep_fixed_integral_bound
      (P := setup.P) (ν := setup.samplePairLaw) (φ := φ)
      (X := X) (Y := Y)
      (C := Finset.sum Finset.univ (fun i => (setup.M i) ^ 2))
      hφ_meas hX_meas hY_meas h_indep
      (by simpa [Y] using setup.samplePair_law k)
      h_int
      (fun z => by simpa [φ] using fixed_pair_deltaBar_integral_bound setup z)
  simpa [φ, X, Y, StochasticBlockMirrorDescentSetup.deltaBar,
    SOptLib.iterateProcessView, StochasticBlockMirrorDescentSetup.ξ,
    StochasticBlockMirrorDescentSetup.block, StochasticBlockMirrorDescentSetup.samplePair] using h_le

/-- Random-iterate transfer of the block second-moment bound in Lan Eq. (4.6.4).

Candidate audit: SOptLib's `integrable_comp_of_indep_fixed_integral_bound` and
`integral_comp_le_of_indep_fixed_integral_bound` exactly provide the
random-parameter transport; centered variance wrappers were rejected because
Lan Eq. (4.6.22) uses the uncentered block dual squared norm. -/
private theorem random_iterate_block_second_moment_bound
    (setup : StochasticBlockMirrorDescentSetup ι S)
    (i : ι) (k : ℕ) :
    Integrable
        (fun ω : StochasticBlockSamplePath S ι =>
          SOptLib.canonicalDualNorm (setup.blockPrimalNorm i)
            (setup.blockCoord i (setup.gradL ((SOptLib.iterateProcessView (fun t ω => (setup.process t ω).x.1)) k ω) (setup.ξ k ω))) ^ 2)
        setup.P ∧
      ∫ ω, SOptLib.canonicalDualNorm (setup.blockPrimalNorm i)
          (setup.blockCoord i (setup.gradL ((SOptLib.iterateProcessView (fun t ω => (setup.process t ω).x.1)) k ω) (setup.ξ k ω))) ^ 2 ∂setup.P
        ≤ setup.M i ^ 2 := by
  classical
  letI : IsProbabilityMeasure setup.P := setup.P_probability
  letI : IsProbabilityMeasure setup.oracleSampleLaw := setup.oracleSampleLaw_probability
  letI : IsProbabilityMeasure setup.blockIndexLaw := by
    unfold StochasticBlockMirrorDescentSetup.blockIndexLaw finiteBlockIndexLaw
    infer_instance
  letI : IsProbabilityMeasure setup.samplePairLaw := setup.samplePairLaw_probability
  simpa [SOptLib.iterateProcessView, StochasticBlockMirrorDescentSetup.ξ,
      StochasticBlockMirrorDescentSetup.samplePair] using
    (random_iterate_uncentered_oracle_moment_bound_of_fixed
      (P := setup.P) (ν := setup.samplePairLaw)
      (X := fun ω : StochasticBlockSamplePath S ι => (setup.process k ω).x)
      (Y := setup.samplePair k)
      (moment := fun z q =>
        SOptLib.canonicalDualNorm (setup.blockPrimalNorm i) (setup.blockCoord i (setup.gradL z.1 q.1)) ^ 2)
      (C := setup.M i ^ 2)
      (by
        have hgrad :
            Measurable
              (fun p : setup.FeasibleState × (S × ι) =>
                setup.blockCoord i (setup.gradL p.1.1 p.2.1)) := by
          have hgraw :
              Measurable
                (fun p : setup.FeasibleState × (S × ι) =>
                  setup.gradL p.1.1 p.2.1) := by
            exact setup.hgradL_measurable.comp
              ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd.fst)
          simpa using
            (setup.blockCoord i).measurable.comp hgraw
        have hdual :
            Measurable
              (fun p : setup.FeasibleState × (S × ι) =>
                SOptLib.canonicalDualNorm (setup.blockPrimalNorm i)
                  (setup.blockCoord i (setup.gradL p.1.1 p.2.1))) := by
          exact
            ((canonicalDualNormFromPrimal_continuous (setup.blockPrimalNorm i)
              (setup.blockPrimalNorm_isPaperNorm i)).measurable.comp hgrad)
        have hsq := hdual.mul hdual
        simpa [Function.uncurry, pow_two] using hsq)
      (by
        have hx_adapted := setup.xFeasibleIter_measurable_sampleFiltration k
        have hm_le : setup.sampleFiltration k ≤ MeasurableSpace.pi := by
          simpa using setup.sampleFiltration.le k
        simpa using hx_adapted.mono hm_le le_rfl)
      (by simpa using setup.samplePair_measurable k)
      (by simpa using current_sample_indep_feasible_state setup k)
      (by simpa using setup.samplePair_law k)
      (by intro z q; exact sq_nonneg _)
      (sq_nonneg (setup.M i))
      (by
        intro z
        have hbaseS :
            Integrable
              (fun s => SOptLib.canonicalDualNorm (setup.blockPrimalNorm i)
                  (setup.blockCoord i (setup.gradL z.1 s)) ^ 2)
              setup.oracleSampleLaw :=
          (setup.block_second_moment_expectation i z.1 z.2).1
        rw [StochasticBlockMirrorDescentSetup.samplePairLaw]
        simpa using hbaseS.comp_fst setup.blockIndexLaw)
      (by
        intro z
        calc
          ∫ q : S × ι,
              SOptLib.canonicalDualNorm (setup.blockPrimalNorm i)
                  (setup.blockCoord i (setup.gradL z.1 q.1)) ^ 2 ∂setup.samplePairLaw
              = ∫ s : S, SOptLib.canonicalDualNorm (setup.blockPrimalNorm i)
                  (setup.blockCoord i (setup.gradL z.1 s)) ^ 2 ∂setup.oracleSampleLaw := by
                  rw [StochasticBlockMirrorDescentSetup.samplePairLaw]
                  rw [MeasureTheory.integral_fun_fst (μ := setup.oracleSampleLaw)
                    (ν := setup.blockIndexLaw)
                    (f := fun s : S =>
                      SOptLib.canonicalDualNorm (setup.blockPrimalNorm i)
                        (setup.blockCoord i (setup.gradL z.1 s)) ^ 2)]
                  simp
          _ ≤ setup.M i ^ 2 := (setup.block_second_moment_expectation i z.1 z.2).2))

/-! Route-local infrastructure for the equality part of Eq. (4.6.22). -/

/-- Joint measurability of the selected quadratic `deltaBar` kernel.

Candidate audit: this is the same finite-dispatch measurable kernel used in
`random_deltaBar_integral_bound`; SOptLib's transfer lemmas require a named
`Measurable (Function.uncurry φ)` side condition, while no existing local helper
exposed this paper-specific selected-block scalar kernel. -/
private theorem selected_deltaBar_kernel_measurable
    (setup : StochasticBlockMirrorDescentSetup ι S) :
    Measurable
      (fun p : setup.FeasibleState × (S × ι) =>
        (setup.p p.2.2)⁻¹ *
          SOptLib.canonicalDualNorm (setup.blockPrimalNorm p.2.2) (setup.blockCoord p.2.2 (setup.gradL p.1.1 p.2.1)) ^ 2) := by
  classical
  haveI : Nonempty ι := by
    by_cases h : Nonempty ι
    · exact h
    · exfalso
      haveI : IsEmpty ι := ⟨fun i => h ⟨i⟩⟩
      have hsum0 : Finset.sum Finset.univ setup.p = 0 := by simp
      linarith [setup.hp_sum, hsum0]
  refine finite_dispatch_measurable_kernel
    (idx := fun p : setup.FeasibleState × (S × ι) => p.2.2)
    (f := fun j p =>
      (setup.p j)⁻¹ *
        SOptLib.canonicalDualNorm (setup.blockPrimalNorm j) (setup.blockCoord j (setup.gradL p.1.1 p.2.1)) ^ 2)
    ?hidx ?hf
  · exact measurable_snd.snd
  · intro j
    have hgrad :
        Measurable
          (fun p : setup.FeasibleState × (S × ι) =>
            setup.blockCoord j (setup.gradL p.1.1 p.2.1)) := by
      have hgraw :
          Measurable
            (fun p : setup.FeasibleState × (S × ι) =>
              setup.gradL p.1.1 p.2.1) := by
        exact setup.hgradL_measurable.comp
          ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd.fst)
      simpa using
        (setup.blockCoord j).measurable.comp hgraw
    have hdual :
        Measurable
          (fun p : setup.FeasibleState × (S × ι) =>
            SOptLib.canonicalDualNorm (setup.blockPrimalNorm j) (setup.blockCoord j (setup.gradL p.1.1 p.2.1))) :=
      ((canonicalDualNormFromPrimal_continuous (setup.blockPrimalNorm j)
        (setup.blockPrimalNorm_isPaperNorm j)).measurable.comp hgrad)
    have hsq := hdual.mul hdual
    simpa [pow_two] using (measurable_const.mul hsq)

/-- Joint measurability of the weighted all-block quadratic kernel.

Candidate audit: `Finset.measurable_sum` and the block dual-norm continuity
helpers match this finite all-block scalar kernel; SOptLib's probabilistic
transfer lemmas are downstream consumers, not replacements for this local
Lan Eq. (4.6.22) measurability side condition. -/
private theorem weighted_deltaBar_kernel_measurable
    (setup : StochasticBlockMirrorDescentSetup ι S) :
    Measurable
      (fun p : setup.FeasibleState × (S × ι) =>
        Finset.sum Finset.univ (fun i =>
          setup.p i * (setup.p i)⁻¹ *
            SOptLib.canonicalDualNorm (setup.blockPrimalNorm i) (setup.blockCoord i (setup.gradL p.1.1 p.2.1)) ^ 2)) := by
  classical
  refine Finset.measurable_sum Finset.univ (fun i _hi => ?_)
  have hgrad :
      Measurable
        (fun p : setup.FeasibleState × (S × ι) =>
          setup.blockCoord i (setup.gradL p.1.1 p.2.1)) := by
    have hgraw :
        Measurable
          (fun p : setup.FeasibleState × (S × ι) =>
            setup.gradL p.1.1 p.2.1) := by
      exact setup.hgradL_measurable.comp
        ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd.fst)
    simpa using
      (setup.blockCoord i).measurable.comp hgraw
  have hdual :
      Measurable
        (fun p : setup.FeasibleState × (S × ι) =>
          SOptLib.canonicalDualNorm (setup.blockPrimalNorm i) (setup.blockCoord i (setup.gradL p.1.1 p.2.1))) :=
    ((canonicalDualNormFromPrimal_continuous (setup.blockPrimalNorm i)
      (setup.blockPrimalNorm_isPaperNorm i)).measurable.comp hgrad)
  have hsq := hdual.mul hdual
  simpa [pow_two] using
    (measurable_const.mul hsq)

/-- Fixed-pair integrability of the weighted all-block quadratic kernel.

Candidate audit: `fixed_pair_deltaBar_integrable` covers only the sampled
selected block, and `MeasureTheory.integrable_finset_sum` is the exact Mathlib
finite-sum API needed for the all-block weighted Lan Eq. (4.6.22) kernel. -/
private theorem fixed_pair_weighted_block_sum_integrable
    (setup : StochasticBlockMirrorDescentSetup ι S)
    (z : setup.FeasibleState) :
    Integrable
      (fun q : S × ι =>
        Finset.sum Finset.univ (fun i =>
          setup.p i * (setup.p i)⁻¹ *
            SOptLib.canonicalDualNorm (setup.blockPrimalNorm i) (setup.blockCoord i (setup.gradL z.1 q.1)) ^ 2))
      setup.samplePairLaw := by
  classical
  letI : IsProbabilityMeasure setup.oracleSampleLaw := setup.oracleSampleLaw_probability
  letI : IsProbabilityMeasure setup.blockIndexLaw := by
    unfold StochasticBlockMirrorDescentSetup.blockIndexLaw finiteBlockIndexLaw
    infer_instance
  rw [StochasticBlockMirrorDescentSetup.samplePairLaw]
  refine MeasureTheory.integrable_finset_sum (s := Finset.univ)
    (μ := setup.oracleSampleLaw.prod setup.blockIndexLaw) ?_
  intro i _hi
  have hbaseS :
      Integrable
        (fun s : S =>
          setup.p i * (setup.p i)⁻¹ *
            SOptLib.canonicalDualNorm (setup.blockPrimalNorm i) (setup.blockCoord i (setup.gradL z.1 s)) ^ 2)
        setup.oracleSampleLaw :=
    (setup.block_second_moment_expectation i z.1 z.2).1.const_mul
      (setup.p i * (setup.p i)⁻¹)
  simpa using hbaseS.comp_fst setup.blockIndexLaw

/-- Fixed-pair expansion of the weighted all-block quadratic kernel.

Candidate audit: `fixed_pair_deltaBar_integral_expansion` expands the selected
sampled block. This helper is its all-block companion, using
`MeasureTheory.integral_fun_fst`, `integral_finset_sum`, and
`integral_const_mul` to expose the weighted RHS in Lan Theorem 4.12 step 4. -/
private theorem fixed_pair_weighted_block_sum_integral_expansion
    (setup : StochasticBlockMirrorDescentSetup ι S)
    (z : setup.FeasibleState) :
    ∫ q : S × ι,
        Finset.sum Finset.univ (fun i =>
          setup.p i * (setup.p i)⁻¹ *
            SOptLib.canonicalDualNorm (setup.blockPrimalNorm i) (setup.blockCoord i (setup.gradL z.1 q.1)) ^ 2)
        ∂setup.samplePairLaw =
      Finset.sum Finset.univ (fun i =>
        setup.p i * (setup.p i)⁻¹ *
          ∫ s, SOptLib.canonicalDualNorm (setup.blockPrimalNorm i) (setup.blockCoord i (setup.gradL z.1 s)) ^ 2
            ∂setup.oracleSampleLaw) := by
  classical
  letI : IsProbabilityMeasure setup.oracleSampleLaw := setup.oracleSampleLaw_probability
  letI : IsProbabilityMeasure setup.blockIndexLaw := by
    unfold StochasticBlockMirrorDescentSetup.blockIndexLaw finiteBlockIndexLaw
    infer_instance
  rw [StochasticBlockMirrorDescentSetup.samplePairLaw]
  simpa [smul_eq_mul] using
    integral_fst_finset_sum_smul_eq_sum_smul_integrals
      (μ := setup.oracleSampleLaw) (ν := setup.blockIndexLaw)
      (s := Finset.univ) (c := fun i => setup.p i * (setup.p i)⁻¹)
      (F := fun i s =>
        SOptLib.canonicalDualNorm (setup.blockPrimalNorm i) (setup.blockCoord i (setup.gradL z.1 s)) ^ 2)
      (by
        intro i _hi
        exact (setup.block_second_moment_expectation i z.1 z.2).1)

/-- Fixed-fiber cancellation between selected and weighted quadratic kernels.

Candidate audit: this consumes `fixed_pair_deltaBar_integral_expansion` and
the weighted companion above. No SOptLib primitive states this paper-specific
Lan Eq. (4.6.22) selected-minus-weighted cancellation; SOptLib provides the
independence-transfer consumer used downstream. -/
private theorem fixed_pair_deltaBar_difference_integral_zero
    (setup : StochasticBlockMirrorDescentSetup ι S)
    (z : setup.FeasibleState) :
    ∫ q : S × ι,
        ((setup.p q.2)⁻¹ *
          SOptLib.canonicalDualNorm (setup.blockPrimalNorm q.2) (setup.blockCoord q.2 (setup.gradL z.1 q.1)) ^ 2 -
        Finset.sum Finset.univ (fun i =>
          setup.p i * (setup.p i)⁻¹ *
            SOptLib.canonicalDualNorm (setup.blockPrimalNorm i) (setup.blockCoord i (setup.gradL z.1 q.1)) ^ 2))
        ∂setup.samplePairLaw = 0 := by
  classical
  exact selected_block_estimator_minus_weighted_sum_integral_eq_zero
    (ν := setup.samplePairLaw)
    (selected := fun q : S × ι =>
      (setup.p q.2)⁻¹ *
        SOptLib.canonicalDualNorm (setup.blockPrimalNorm q.2) (setup.blockCoord q.2 (setup.gradL z.1 q.1)) ^ 2)
    (weighted := fun q : S × ι =>
      Finset.sum Finset.univ (fun i =>
        setup.p i * (setup.p i)⁻¹ *
          SOptLib.canonicalDualNorm (setup.blockPrimalNorm i) (setup.blockCoord i (setup.gradL z.1 q.1)) ^ 2))
    (fixed_pair_deltaBar_integrable setup z)
    (fixed_pair_weighted_block_sum_integrable setup z)
    (by
      rw [fixed_pair_deltaBar_integral_expansion setup z,
        fixed_pair_weighted_block_sum_integral_expansion setup z])

/-- Random-iterate integrability of the weighted all-block quadratic kernel.

Candidate audit: this specializes `MeasureTheory.integrable_finset_sum` to the
already proved `random_iterate_block_second_moment_bound`; SOptLib transfer
lemmas are unnecessary here because every summand is already on the random
iterate law needed by Lan Eq. (4.6.22). -/
private theorem random_weighted_block_sum_integrable
    (setup : StochasticBlockMirrorDescentSetup ι S)
    (k : ℕ) :
    Integrable
      (fun ω : StochasticBlockSamplePath S ι =>
        Finset.sum Finset.univ (fun i =>
          setup.p i * (setup.p i)⁻¹ *
            SOptLib.canonicalDualNorm (setup.blockPrimalNorm i)
              (setup.blockCoord i (setup.gradL ((SOptLib.iterateProcessView (fun t ω => (setup.process t ω).x.1)) k ω) (setup.ξ k ω))) ^ 2))
      setup.P := by
  classical
  refine MeasureTheory.integrable_finset_sum (s := Finset.univ) (μ := setup.P) ?_
  intro i _hi
  exact (random_iterate_block_second_moment_bound setup i k).1.const_mul
    (setup.p i * (setup.p i)⁻¹)

/-- Random-iterate expansion of the weighted all-block quadratic integral.

Candidate audit: this is the random-law analogue of the weighted fixed-pair
helper and uses `integral_finset_sum` plus `integral_const_mul`; no existing
SOptLib lemma exposes this exact finite scalar expansion. -/
private theorem random_weighted_block_sum_integral_expansion
    (setup : StochasticBlockMirrorDescentSetup ι S)
    (k : ℕ) :
    ∫ ω : StochasticBlockSamplePath S ι,
        Finset.sum Finset.univ (fun i =>
          setup.p i * (setup.p i)⁻¹ *
            SOptLib.canonicalDualNorm (setup.blockPrimalNorm i)
              (setup.blockCoord i (setup.gradL ((SOptLib.iterateProcessView (fun t ω => (setup.process t ω).x.1)) k ω) (setup.ξ k ω))) ^ 2)
        ∂setup.P =
      Finset.sum Finset.univ (fun i =>
        setup.p i * (setup.p i)⁻¹ *
          ∫ ω : StochasticBlockSamplePath S ι,
            SOptLib.canonicalDualNorm (setup.blockPrimalNorm i)
              (setup.blockCoord i (setup.gradL ((SOptLib.iterateProcessView (fun t ω => (setup.process t ω).x.1)) k ω) (setup.ξ k ω))) ^ 2
            ∂setup.P) := by
  classical
  calc
    ∫ ω : StochasticBlockSamplePath S ι,
        Finset.sum Finset.univ (fun i =>
          setup.p i * (setup.p i)⁻¹ *
            SOptLib.canonicalDualNorm (setup.blockPrimalNorm i)
              (setup.blockCoord i (setup.gradL ((SOptLib.iterateProcessView (fun t ω => (setup.process t ω).x.1)) k ω) (setup.ξ k ω))) ^ 2)
        ∂setup.P
        = Finset.sum Finset.univ (fun i =>
            ∫ ω : StochasticBlockSamplePath S ι,
              setup.p i * (setup.p i)⁻¹ *
                SOptLib.canonicalDualNorm (setup.blockPrimalNorm i)
                  (setup.blockCoord i (setup.gradL ((SOptLib.iterateProcessView (fun t ω => (setup.process t ω).x.1)) k ω) (setup.ξ k ω))) ^ 2
              ∂setup.P) := by
            rw [integral_finset_sum]
            intro i _hi
            exact (random_iterate_block_second_moment_bound setup i k).1.const_mul
              (setup.p i * (setup.p i)⁻¹)
    _ = Finset.sum Finset.univ (fun i =>
          setup.p i * (setup.p i)⁻¹ *
            ∫ ω : StochasticBlockSamplePath S ι,
              SOptLib.canonicalDualNorm (setup.blockPrimalNorm i)
                (setup.blockCoord i (setup.gradL ((SOptLib.iterateProcessView (fun t ω => (setup.process t ω).x.1)) k ω) (setup.ξ k ω))) ^ 2
              ∂setup.P) := by
          apply Finset.sum_congr rfl
          intro i _hi
          rw [integral_const_mul]

/-- Random-iterate integrability of the selected quadratic `deltaBar` term.

Candidate audit: symbol search returned the already proved
`random_deltaBar_integral_bound`, `selected_deltaBar_kernel_measurable`, and
`fixed_pair_deltaBar_integrable`; none exposes the standalone integrability
side condition needed for `integral_add`/`integral_finset_sum`, so this helper
specializes SOptLib's `integrable_comp_of_indep_fixed_integral_bound` to Lan
Eq. (4.6.22). -/
private theorem deltaBar_process_integrable
    (setup : StochasticBlockMirrorDescentSetup ι S)
    (k : ℕ) :
    Integrable (fun ω : StochasticBlockSamplePath S ι => setup.deltaBar k ω) setup.P := by
  classical
  letI : IsProbabilityMeasure setup.P := setup.P_probability
  letI : IsProbabilityMeasure setup.samplePairLaw := setup.samplePairLaw_probability
  let X : StochasticBlockSamplePath S ι → setup.FeasibleState :=
    fun ω => (setup.process k ω).x
  let Y : StochasticBlockSamplePath S ι → S × ι := setup.samplePair k
  let φ : setup.FeasibleState → S × ι → ℝ := fun z q =>
    (setup.p q.2)⁻¹ *
      SOptLib.canonicalDualNorm (setup.blockPrimalNorm q.2) (setup.blockCoord q.2 (setup.gradL z.1 q.1)) ^ 2
  have hφ_meas : Measurable (Function.uncurry φ) := by
    simpa [φ, Function.uncurry] using selected_deltaBar_kernel_measurable setup
  have hX_meas : Measurable X := by
    have hx_adapted := setup.xFeasibleIter_measurable_sampleFiltration k
    have hm_le : setup.sampleFiltration k ≤ MeasurableSpace.pi := by
      simpa using setup.sampleFiltration.le k
    simpa [X] using hx_adapted.mono hm_le le_rfl
  have hY_meas : Measurable Y := by
    simpa [Y] using setup.samplePair_measurable k
  have h_indep : IndepFun X Y setup.P := by
    simpa [X, Y] using current_sample_indep_feasible_state setup k
  have hC_nonneg :
      0 ≤ Finset.sum Finset.univ (fun i => (setup.M i) ^ 2) :=
    Finset.sum_nonneg (fun i _hi => sq_nonneg (setup.M i))
  have h_int : Integrable (fun ω => φ (X ω) (Y ω)) setup.P := by
    exact integrable_comp_of_indep_fixed_integral_bound
      (P := setup.P) (ν := setup.samplePairLaw) (φ := φ)
      (X := X) (Y := Y)
      (C := Finset.sum Finset.univ (fun i => (setup.M i) ^ 2))
      hφ_meas hX_meas hY_meas h_indep
      (by simpa [Y] using setup.samplePair_law k)
      (by
        intro z q
        exact mul_nonneg (inv_nonneg.mpr (le_of_lt (setup.hp_pos q.2))) (sq_nonneg _))
      hC_nonneg
      (fun z => by simpa [φ] using fixed_pair_deltaBar_integrable setup z)
      (fun z => by simpa [φ] using fixed_pair_deltaBar_integral_bound setup z)
  simpa [φ, X, Y, StochasticBlockMirrorDescentSetup.deltaBar,
    SOptLib.iterateProcessView, StochasticBlockMirrorDescentSetup.ξ,
    StochasticBlockMirrorDescentSetup.block, StochasticBlockMirrorDescentSetup.samplePair] using h_int

/-! Used in: `theorem_4_12` to bound the quadratic stochastic term through the
sampling probabilities and the blockwise second-moment estimate in Eq. (4.6.22). -/
theorem step_4_6_22
    (setup : StochasticBlockMirrorDescentSetup ι S)
    (k : ℕ) :
    (∫ ω, setup.deltaBar k ω ∂setup.P =
      Finset.sum Finset.univ (fun i =>
        setup.p i * (setup.p i)⁻¹ *
          (∫ ω, SOptLib.canonicalDualNorm (setup.blockPrimalNorm i)
            (setup.blockCoord i (setup.gradL ((SOptLib.iterateProcessView (fun t ω => (setup.process t ω).x.1)) k ω) (setup.ξ k ω))) ^ 2 ∂setup.P))) ∧
    (∫ ω, setup.deltaBar k ω ∂setup.P ≤
      Finset.sum Finset.univ (fun i => (setup.M i) ^ 2)) := by
  classical
  letI : IsProbabilityMeasure setup.P := setup.P_probability
  letI : IsProbabilityMeasure setup.samplePairLaw := setup.samplePairLaw_probability
  let X : StochasticBlockSamplePath S ι → setup.FeasibleState :=
    fun ω => (setup.process k ω).x
  let Y : StochasticBlockSamplePath S ι → S × ι := setup.samplePair k
  let selected : setup.FeasibleState → S × ι → ℝ := fun z q =>
    (setup.p q.2)⁻¹ *
      SOptLib.canonicalDualNorm (setup.blockPrimalNorm q.2) (setup.blockCoord q.2 (setup.gradL z.1 q.1)) ^ 2
  let weighted : setup.FeasibleState → S × ι → ℝ := fun z q =>
    Finset.sum Finset.univ (fun i =>
      setup.p i * (setup.p i)⁻¹ *
        SOptLib.canonicalDualNorm (setup.blockPrimalNorm i) (setup.blockCoord i (setup.gradL z.1 q.1)) ^ 2)
  let A : ι → ℝ := fun i =>
    setup.p i * (setup.p i)⁻¹ *
      ∫ ω, SOptLib.canonicalDualNorm (setup.blockPrimalNorm i)
        (setup.blockCoord i
          (setup.gradL
            ((SOptLib.iterateProcessView (fun t ω => (setup.process t ω).x.1)) k ω)
            (setup.ξ k ω))) ^ 2 ∂setup.P
  have hselected_meas : Measurable (Function.uncurry selected) := by
    simpa [selected, Function.uncurry] using selected_deltaBar_kernel_measurable setup
  have hweighted_meas : Measurable (Function.uncurry weighted) := by
    simpa [weighted, Function.uncurry] using weighted_deltaBar_kernel_measurable setup
  have hX_meas : Measurable X := by
    have hx_adapted := setup.xFeasibleIter_measurable_sampleFiltration k
    have hm_le : setup.sampleFiltration k ≤ MeasurableSpace.pi := by
      simpa using setup.sampleFiltration.le k
    simpa [X] using hx_adapted.mono hm_le le_rfl
  have hY_meas : Measurable Y := by
    simpa [Y] using setup.samplePair_measurable k
  have h_indep : IndepFun X Y setup.P := by
    simpa [X, Y] using current_sample_indep_feasible_state setup k
  have hselected_int : Integrable (fun ω => selected (X ω) (Y ω)) setup.P := by
    exact integrable_comp_of_indep_fixed_integral_bound
      (P := setup.P) (ν := setup.samplePairLaw) (φ := selected)
      (X := X) (Y := Y)
      (C := Finset.sum Finset.univ (fun i => (setup.M i) ^ 2))
      hselected_meas hX_meas hY_meas h_indep
      (by simpa [Y] using setup.samplePair_law k)
      (by
        intro z q
        exact mul_nonneg (inv_nonneg.mpr (le_of_lt (setup.hp_pos q.2))) (sq_nonneg _))
      (Finset.sum_nonneg (fun i _hi => sq_nonneg (setup.M i)))
      (fun z => by simpa [selected] using fixed_pair_deltaBar_integrable setup z)
      (fun z => by simpa [selected] using fixed_pair_deltaBar_integral_bound setup z)
  have hweighted_int : Integrable (fun ω => weighted (X ω) (Y ω)) setup.P := by
    simpa [weighted, X, Y, SOptLib.iterateProcessView,
      StochasticBlockMirrorDescentSetup.ξ, StochasticBlockMirrorDescentSetup.samplePair]
      using random_weighted_block_sum_integrable setup k
  have hfixed_zero :
      ∀ z : setup.FeasibleState, ∫ q : S × ι, selected z q - weighted z q ∂setup.samplePairLaw = 0 := by
    intro z
    simpa [selected, weighted] using fixed_pair_deltaBar_difference_integral_zero setup z
  have hweighted_eval :
      ∫ ω, weighted (X ω) (Y ω) ∂setup.P = Finset.sum Finset.univ A := by
    simpa [A, weighted, X, Y, SOptLib.iterateProcessView,
      StochasticBlockMirrorDescentSetup.ξ, StochasticBlockMirrorDescentSetup.samplePair]
      using random_weighted_block_sum_integral_expansion setup k
  have hselected_bound :
      ∫ ω, selected (X ω) (Y ω) ∂setup.P ≤
        Finset.sum Finset.univ (fun i => setup.M i ^ 2) := by
    calc
      ∫ ω, selected (X ω) (Y ω) ∂setup.P =
          ∫ ω, setup.deltaBar k ω ∂setup.P := by
            apply integral_congr_ae
            filter_upwards with ω
            rfl
      _ ≤ Finset.sum Finset.univ (fun i => setup.M i ^ 2) :=
        random_deltaBar_integral_bound setup k
  have hmain :=
    selected_block_quadratic_expectation_eq_weighted_sum_and_le
      (P := setup.P) (ν := setup.samplePairLaw)
      (X := X) (Y := Y) (selected := selected) (weighted := weighted)
      (A := A) (M := setup.M)
      hselected_meas hweighted_meas hX_meas hY_meas h_indep
      (by simpa [Y] using setup.samplePair_law k)
      hselected_int hweighted_int hfixed_zero hweighted_eval hselected_bound
  constructor
  · calc
      ∫ ω, setup.deltaBar k ω ∂setup.P =
          ∫ ω, selected (X ω) (Y ω) ∂setup.P := by
            apply integral_congr_ae
            filter_upwards with ω
            rfl
      _ = Finset.sum Finset.univ (fun i =>
          setup.p i * (setup.p i)⁻¹ *
            (∫ ω, SOptLib.canonicalDualNorm (setup.blockPrimalNorm i)
              (setup.blockCoord i
                (setup.gradL
                  ((SOptLib.iterateProcessView (fun t ω => (setup.process t ω).x.1)) k ω)
                  (setup.ξ k ω))) ^ 2 ∂setup.P)) := by
          simpa [A] using hmain.1
  · calc
      ∫ ω, setup.deltaBar k ω ∂setup.P =
          ∫ ω, selected (X ω) (Y ω) ∂setup.P := by
            apply integral_congr_ae
            filter_upwards with ω
            rfl
      _ ≤ Finset.sum Finset.univ (fun i => setup.M i ^ 2) := hmain.2

/-- Finite-window expectation bound for the stochastic terms in Theorem 4.12.

Candidate audit: SOptLib's `integral_finset_sum_const_mul_eq_zero` handles the
martingale part only, while the local `random_deltaBar_integral_bound` handles
one quadratic term only; the paper step needs their finite-window affine
combination, so this helper combines `step_4_6_21`, `step_4_6_22`, and the
standalone integrability helper for Lan Theorem 4.12 proof step 5. -/
private theorem finite_window_noise_integral_bound
    (setup : StochasticBlockMirrorDescentSetup ι S)
    (N : ℕ) (x : setup.StateSpace) :
    ∫ ω : StochasticBlockSamplePath S ι,
        Finset.sum (StochasticBlockMirrorDescentSetup.outputTimes N) (fun k =>
          setup.paperEta k *
            setup.delta x (StochasticBlockMirrorDescentSetup.zeroBasedIndex k) ω +
            (1 / 2 : ℝ) * (setup.paperEta k) ^ 2 *
              setup.deltaBar (StochasticBlockMirrorDescentSetup.zeroBasedIndex k) ω)
        ∂setup.P ≤
      (1 / 2 : ℝ) *
        Finset.sum (StochasticBlockMirrorDescentSetup.outputTimes N) (fun k =>
          (setup.paperEta k) ^ 2 *
            Finset.sum Finset.univ (fun i => (setup.M i) ^ 2)) := by
  classical
  letI : IsProbabilityMeasure setup.P := setup.P_probability
  exact finite_window_zero_mean_plus_quadratic_noise_integral_bound
    (P := setup.P)
    (times := StochasticBlockMirrorDescentSetup.outputTimes N)
    (η := setup.paperEta)
    (δ := fun k ω => setup.delta x (StochasticBlockMirrorDescentSetup.zeroBasedIndex k) ω)
    (δbar := fun k ω => setup.deltaBar (StochasticBlockMirrorDescentSetup.zeroBasedIndex k) ω)
    (B := fun _ => Finset.sum Finset.univ (fun i => (setup.M i) ^ 2))
    (by
      intro k _hk
      simpa [StochasticBlockMirrorDescentSetup.delta, SOptLib.iterateProcessView,
        StochasticBlockMirrorDescentSetup.ξ, StochasticBlockMirrorDescentSetup.block] using
        (scalar_delta_process_integrable setup x
          (StochasticBlockMirrorDescentSetup.zeroBasedIndex k)))
    (by
      intro k _hk
      exact deltaBar_process_integrable setup (StochasticBlockMirrorDescentSetup.zeroBasedIndex k))
    (by
      intro k _hk
      exact integral_eq_zero_of_condExp_ae_eq_zero
        (P := setup.P)
        (m := setup.sampleFiltration (StochasticBlockMirrorDescentSetup.zeroBasedIndex k))
        (hm := setup.sampleFiltration.le (StochasticBlockMirrorDescentSetup.zeroBasedIndex k))
        (step_4_6_21 setup x (StochasticBlockMirrorDescentSetup.zeroBasedIndex k)))
    (by
      intro k _hk
      exact (step_4_6_22 setup (StochasticBlockMirrorDescentSetup.zeroBasedIndex k)).2)

/-! Output measurability and objective-gap well-posedness infrastructure for
Theorem 4.12. -/

/-- The weighted output `x̄_N` is feasible and measurable.

Candidate audit: `SOptLib.weightedAverageOutput_measurable`,
`SOptLib.weightedAverageOutput_mem`, and `SOptLib.weightedOutputAverage_val`
match the reusable finite weighted-output construction for Eq. (4.6.15).  This
helper specializes that construction to the SBMD `weightedAverage`, transporting
`setup.xIter_measurable_sampleFiltration` to ordinary measurability and using
`θ_k = γ_k` plus positive stepsizes for the output normalizer. -/
private theorem weighted_average_output_mem_measurable
    (setup : StochasticBlockMirrorDescentSetup ι S)
    (N : ℕ) (hN : 0 < N) :
    (∀ ω : StochasticBlockSamplePath S ι, setup.weightedAverage N ω ∈ setup.X) ∧
      Measurable (fun ω : StochasticBlockSamplePath S ι => setup.weightedAverage N ω) := by
  classical
  have htheta_pos : 0 < setup.outputThetaSum N := by
    unfold StochasticBlockMirrorDescentSetup.outputThetaSum
      StochasticBlockMirrorDescentSetup.outputTimes
    exact SOptLib.positiveTimeOutputWindow setup.paperTheta
      (fun k => by
        rw [setup.paperTheta_eq_paperEta k]
        exact setup.hη_pos (StochasticBlockMirrorDescentSetup.zeroBasedIndex k))
      (le_refl 1) hN
  have hx_mem :
      ∀ t, t ∈ StochasticBlockMirrorDescentSetup.outputTimes N →
        ∀ ω : StochasticBlockSamplePath S ι, setup.xPaper t ω ∈ setup.X := by
    intro t _ht ω
    simpa [StochasticBlockMirrorDescentSetup.xPaper] using
      setup.xIter_mem (StochasticBlockMirrorDescentSetup.zeroBasedIndex t) ω
  let xbarSub :=
    setup.weightedAverageSubtype N hx_mem htheta_pos
  have hval :
      ∀ ω : StochasticBlockSamplePath S ι,
        (xbarSub ω).1 = setup.weightedAverage N ω := by
    intro ω
    rfl
  have hmem :
      ∀ ω : StochasticBlockSamplePath S ι, setup.weightedAverage N ω ∈ setup.X := by
    intro ω
    rw [← hval ω]
    exact (xbarSub ω).2
  have hx_measurable :
      ∀ t : StochasticBlockMirrorDescentSetup.PositiveTime,
        Measurable (setup.xPaper t) := by
    intro t
    have hfil :
        Measurable[setup.sampleFiltration
            (StochasticBlockMirrorDescentSetup.zeroBasedIndex t)]
          (fun ω : StochasticBlockSamplePath S ι =>
            (SOptLib.iterateProcessView (fun t ω => (setup.process t ω).x.1)) (StochasticBlockMirrorDescentSetup.zeroBasedIndex t) ω) :=
      setup.xIter_measurable_sampleFiltration
        (StochasticBlockMirrorDescentSetup.zeroBasedIndex t)
    have hamb :
        Measurable
          (fun ω : StochasticBlockSamplePath S ι =>
            (SOptLib.iterateProcessView (fun t ω => (setup.process t ω).x.1)) (StochasticBlockMirrorDescentSetup.zeroBasedIndex t) ω) :=
      Measurable.of_measurableSpace_le hfil
        (by
          simpa using
            (setup.sampleFiltration.le
              (StochasticBlockMirrorDescentSetup.zeroBasedIndex t)))
    change Measurable
      (fun ω : StochasticBlockSamplePath S ι =>
        setup.xPaper t ω)
    simpa [StochasticBlockMirrorDescentSetup.xPaper] using hamb
  have hxbarSub_meas : Measurable xbarSub := by
    simpa [xbarSub] using
      SOptLib.weightedAverageOutput_measurable setup.X
        (fun _ : Unit => StochasticBlockMirrorDescentSetup.outputTimes N)
        setup.paperTheta setup.xPaper
        (fun _ : Unit => setup.outputThetaSum N)
        setup.X_convex
        (fun _ t _ => setup.paperTheta_nonneg t)
        (fun _ t ht ω => hx_mem t ht ω)
        (fun _ => htheta_pos)
        (fun _ => rfl)
        hx_measurable
        ()
  have hmeas :
      Measurable (fun ω : StochasticBlockSamplePath S ι => setup.weightedAverage N ω) := by
    have hproj : Measurable (fun ω : StochasticBlockSamplePath S ι => (xbarSub ω).1) :=
      measurable_subtype_coe.comp hxbarSub_meas
    convert hproj using 1
  exact ⟨hmem, hmeas⟩

/-- Carrier support inequality for the feasible objective.

Candidate audit: `SOptLib.mem_carrierSubdifferential_iff` exactly exposes the
paper subgradient condition `g(x) ∈ ∂f(x)` as the carrier-restricted supporting
hyperplane inequality; the weighted-output/telescope candidates listed for the
current goal concern output averaging rather than objective regularity. -/
private theorem feasible_objective_supporting_inequality
    (setup : StochasticBlockMirrorDescentSetup ι S)
    (z y : setup.FeasibleState) :
    setup.objective z.1 + ⟪setup.g z.1, y.1 - z.1⟫_ℝ ≤
      setup.objective y.1 := by
  have hsubmem := setup.hsubgradient z.1 z.2
  have hsupport := (SOptLib.mem_carrierSubdifferential_iff.mp hsubmem) y
  simpa [StochasticBlockMirrorDescentSetup.objective] using hsupport

/-- Block-dual control of the deterministic mean subgradient against feasible
displacements.

Candidate audit: `gBlock_dual_norm_le_M`, `setup.blockDualNorm_support_bound`,
and `seminorm_upper_bound_by_ambient_norm_of_finite_dimensional` exactly match
Lan Eq. (4.6.5)--(4.6.6)'s finite block argument; the SOptLib ambient
subgradient Lipschitz lemma was rejected here because it requires a direct
Hilbert-norm bound on `setup.g`, which the local counterexample shows is not
source-derived. -/
private theorem g_inner_abs_le_feasible_dist
    (setup : StochasticBlockMirrorDescentSetup ι S) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ z y : setup.FeasibleState,
        |⟪setup.g z.1, y.1 - z.1⟫_ℝ| ≤ C * dist z y := by
  classical
  exact abs_inner_le_dist_of_block_dual_bounds
    (eval := fun z : setup.FeasibleState => (z.1 : setup.StateSpace))
    (coord := setup.blockCoord)
    (lift := fun i ζ => PiLp.single 2 i ζ)
    (g := fun z : setup.FeasibleState => setup.g z.1)
    (gBlock := fun i z => setup.gBlock i z.1)
    (p := setup.blockPrimalNorm)
    (dual := fun i z => SOptLib.canonicalDualNorm (setup.blockPrimalNorm i) (setup.gBlock i z.1))
    (M := setup.M)
    setup.M_nonneg
    (by
      intro i
      exact seminorm_upper_bound_by_ambient_norm_of_finite_dimensional
        (setup.blockPrimalNorm i))
    (by
      intro z
      symm
      simpa [StochasticBlockMirrorDescentSetup.gBlock] using
        setup.blockDualLift_sum_blockCoord (setup.g z.1))
    (by
      intro i ζ d
      have hbase := setup.blockDualLift_pairing i d ζ
      rw [real_inner_comm]
      rw [← hbase]
      rw [real_inner_comm])
    (by
      intro i z d
      exact setup.blockDualNorm_support_bound i (setup.gBlock i z.1)
        (setup.blockCoord i d))
    (by
      intro i z
      exact gBlock_dual_norm_le_M setup i z.1 z.2)
    (by
      intro z y
      rw [Subtype.dist_eq, dist_eq_norm]
      simp [norm_sub_rev])

/-- The feasible objective is measurable on the feasible carrier.

Candidate audit: `SOptLib.LipschitzWith.measurable` and
`SOptLib.lipschitzWith_of_norm_sub_le_mul` exactly package the final
metric-to-measurable step.  The needed pointwise Lipschitz estimate is supplied
locally by the preceding block-dual argument rather than by the ambient
subgradient-norm lemma, whose hypothesis is not source-derived in this model. -/
private theorem feasibleObjective_measurable
    (setup : StochasticBlockMirrorDescentSetup ι S) :
    Measurable setup.feasibleObjective := by
  rcases g_inner_abs_le_feasible_dist setup with ⟨C, _hC_nonneg, hinner⟩
  exact measurable_of_supporting_inequality_and_abs_inner_bound
    (f := setup.feasibleObjective)
    (g := fun z : setup.FeasibleState => setup.g z.1)
    (eval := fun z : setup.FeasibleState => (z.1 : setup.StateSpace))
    (C := C)
    (by
      intro z y
      simpa [StochasticBlockMirrorDescentSetup.feasibleObjective] using
        feasible_objective_supporting_inequality setup z y)
    hinner

/-- The objective gap at the measurable weighted output is a.e. strongly
measurable.

Candidate audit: `SOptLib.weightedAverageOutput_measurable` supplies the output
map, while `SOptLib.lipschitzOn_of_forall_subgradient_norm_le` and
`SOptLib.LipschitzWith.measurable` were considered for the missing objective
regularity bridge.  The remaining Lean obligation is the analytic step from the
paper's finite-dimensional bounded-subgradient data
(`setup.hsubgradient`, `derived_block_norm_bounds`, and the block norm control)
to measurability of `setup.objective` on the feasible carrier, which is exactly
the implicit well-posedness condition behind Lan Theorem 4.12's expectation. -/
private theorem objective_output_gap_aestronglyMeasurable
    (setup : StochasticBlockMirrorDescentSetup ι S)
    (N : ℕ) (hN : 0 < N)
    (minimum : setup.ObjectiveMinimum) :
    AEStronglyMeasurable
      (fun ω : StochasticBlockSamplePath S ι =>
        setup.objective (setup.weightedAverage N ω) - setup.fStar minimum)
  setup.P := by
  classical
  rcases weighted_average_output_mem_measurable setup N hN with ⟨_hmem, _hmeas⟩
  let xbarF : StochasticBlockSamplePath S ι → setup.FeasibleState :=
    fun ω => ⟨setup.weightedAverage N ω, _hmem ω⟩
  have hxbarF_meas : Measurable xbarF := by
    refine Measurable.subtype_mk ?_
    exact _hmeas
  have hobj_meas :
      Measurable (fun ω : StochasticBlockSamplePath S ι =>
        setup.objective (setup.weightedAverage N ω)) := by
    have hcomp := (feasibleObjective_measurable setup).comp hxbarF_meas
    simpa [xbarF, StochasticBlockMirrorDescentSetup.feasibleObjective] using hcomp
  exact (hobj_meas.sub measurable_const).aestronglyMeasurable

/-! Used in: the main expected convergence statement for stochastic block
mirror descent, corresponding to Theorem 4.12 and Eq. (4.6.17). -/
theorem theorem_4_12_output_gap_integrable
    (setup : StochasticBlockMirrorDescentSetup ι S)
    (N : ℕ) (hN : 0 < N)
    (minimum : setup.ObjectiveMinimum) :
    Integrable
      (fun ω : StochasticBlockSamplePath S ι =>
        setup.objective (setup.weightedAverage N ω) - setup.fStar minimum)
      setup.P := by
  /- Source-faithfulness obligation for the expectation in Theorem 4.12.

  The book writes `E[f(xbar_N) - f(x_*)]`; in Lean this cannot be discharged
  by the totalized Bochner integral's non-integrable fallback.  This leaf should
  be proved from the existing output feasibility, finite-dimensional continuity
  on the compact product domain, and the fixed-feasible-point objective
  well-definedness already present in the setup. -/
  classical
  letI : IsProbabilityMeasure setup.P := setup.P_probability
  let xStar : setup.StateSpace := setup.optimalPoint minimum
  have hxStar : xStar ∈ setup.X := by
    simpa [xStar] using setup.optimalPoint_mem minimum
  let times := StochasticBlockMirrorDescentSetup.outputTimes N
  let t0 := StochasticBlockMirrorDescentSetup.zeroBasedIndex
  let noise : StochasticBlockMirrorDescentSetup.PositiveTime →
      StochasticBlockSamplePath S ι → ℝ := fun k ω =>
    setup.paperEta k * setup.delta xStar (t0 k) ω +
      (1 / 2 : ℝ) * setup.paperEta k ^ 2 * setup.deltaBar (t0 k) ω
  let A : StochasticBlockSamplePath S ι → ℝ := fun ω =>
    setup.objective (setup.weightedAverage N ω) - setup.fStar minimum
  let B : StochasticBlockSamplePath S ι → ℝ := fun ω =>
    (setup.outputEtaSum N)⁻¹ *
      (setup.aggregatePotential ⟨setup.w₀, setup.w₀_mem⟩ minimum.1 +
        Finset.sum times (fun k => noise k ω))
  have hdelta_int :
      ∀ k ∈ times, Integrable (fun ω : StochasticBlockSamplePath S ι =>
        setup.delta xStar (t0 k) ω) setup.P := by
    intro k _hk
    simpa [t0, StochasticBlockMirrorDescentSetup.delta,
      SOptLib.iterateProcessView, StochasticBlockMirrorDescentSetup.ξ,
      StochasticBlockMirrorDescentSetup.block] using
      (scalar_delta_process_integrable setup xStar (t0 k))
  have hbar_int :
      ∀ k ∈ times, Integrable (fun ω : StochasticBlockSamplePath S ι =>
        setup.deltaBar (t0 k) ω) setup.P := by
    intro k _hk
    exact deltaBar_process_integrable setup (t0 k)
  have hnoise_int :
      ∀ k ∈ times, Integrable (fun ω : StochasticBlockSamplePath S ι =>
        noise k ω) setup.P := by
    intro k hk
    have hd := (hdelta_int k hk).const_mul (setup.paperEta k)
    have hb := (hbar_int k hk).const_mul ((1 / 2 : ℝ) * setup.paperEta k ^ 2)
    simpa [noise, mul_assoc] using hd.add hb
  have hsumNoiseInt : Integrable
      (fun ω : StochasticBlockSamplePath S ι => Finset.sum times (fun k => noise k ω))
      setup.P := by
    exact MeasureTheory.integrable_finset_sum (s := times) (μ := setup.P) hnoise_int
  have hBint : Integrable B setup.P := by
    have hconst : Integrable
        (fun _ : StochasticBlockSamplePath S ι =>
          setup.aggregatePotential ⟨setup.w₀, setup.w₀_mem⟩ minimum.1) setup.P :=
      integrable_const _
    have hadd := hconst.add hsumNoiseInt
    simpa [B] using hadd.const_mul (setup.outputEtaSum N)⁻¹
  rcases weighted_average_output_mem_measurable setup N hN with ⟨havg_mem, _havg_meas⟩
  have hA_aemeas : AEStronglyMeasurable A setup.P := by
    simpa [A] using objective_output_gap_aestronglyMeasurable setup N hN minimum
  have hA_nonneg : ∀ ω : StochasticBlockSamplePath S ι, 0 ≤ A ω := by
    intro ω
    have hle := setup.fStar_le_objective minimum (setup.weightedAverage N ω)
      (havg_mem ω)
    dsimp [A]
    linarith
  have hA_le_B : ∀ ω : StochasticBlockSamplePath S ι, A ω ≤ B ω := by
    intro ω
    have h := step_4_6_20 setup N hN xStar hxStar ω
    simpa [A, B, xStar, noise, times, t0, setup.fStar_eq_objective_optimalPoint minimum]
      using h
  have hnorm : ∀ᵐ ω ∂setup.P, ‖A ω‖ ≤ B ω := by
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hA_nonneg ω)]
    exact hA_le_B ω
  have hAint : Integrable A setup.P :=
    Integrable.mono' hBint hA_aemeas hnorm
  simpa [A] using hAint

theorem theorem_4_12
    (setup : StochasticBlockMirrorDescentSetup ι S)
    (N : ℕ) (hN : 0 < N)
    (minimum : setup.ObjectiveMinimum) :
    ∫ ω, (setup.objective (setup.weightedAverage N ω) - setup.fStar minimum) ∂setup.P ≤
      (setup.outputEtaSum N)⁻¹ *
        (setup.aggregatePotential ⟨setup.w₀, setup.w₀_mem⟩ minimum.1 +
          (1 / 2 : ℝ) *
            Finset.sum (StochasticBlockMirrorDescentSetup.outputTimes N) (fun k =>
              (setup.paperEta k) ^ 2 *
                (Finset.sum Finset.univ (fun i => (setup.M i) ^ 2)))) := by
  classical
  letI : IsProbabilityMeasure setup.P := setup.P_probability
  let xStar : setup.StateSpace := setup.optimalPoint minimum
  have hxStar : xStar ∈ setup.X := by
    simpa [xStar] using setup.optimalPoint_mem minimum
  let times := StochasticBlockMirrorDescentSetup.outputTimes N
  let t0 := StochasticBlockMirrorDescentSetup.zeroBasedIndex
  let sumM : ℝ := Finset.sum Finset.univ (fun i => (setup.M i) ^ 2)
  let noise : StochasticBlockMirrorDescentSetup.PositiveTime →
      StochasticBlockSamplePath S ι → ℝ := fun k ω =>
    setup.paperEta k * setup.delta xStar (t0 k) ω +
      (1 / 2 : ℝ) * setup.paperEta k ^ 2 * setup.deltaBar (t0 k) ω
  let A : StochasticBlockSamplePath S ι → ℝ := fun ω =>
    setup.objective (setup.weightedAverage N ω) - setup.fStar minimum
  let B : StochasticBlockSamplePath S ι → ℝ := fun ω =>
    (setup.outputEtaSum N)⁻¹ *
      (setup.aggregatePotential ⟨setup.w₀, setup.w₀_mem⟩ minimum.1 +
        Finset.sum times (fun k => noise k ω))
  have hWpos : 0 < setup.outputEtaSum N := by
    unfold StochasticBlockMirrorDescentSetup.outputEtaSum
      StochasticBlockMirrorDescentSetup.outputTimes
    exact SOptLib.positiveTimeOutputWindow setup.paperEta
      (fun k => setup.hη_pos (StochasticBlockMirrorDescentSetup.zeroBasedIndex k))
      (le_refl 1) hN
  have hNoiseBound :
      ∫ ω : StochasticBlockSamplePath S ι, Finset.sum times (fun k => noise k ω) ∂setup.P ≤
        (1 / 2 : ℝ) * Finset.sum times (fun k => setup.paperEta k ^ 2 * sumM) := by
    simpa [times, t0, noise, sumM] using finite_window_noise_integral_bound setup N xStar
  have hpoint : ∀ ω : StochasticBlockSamplePath S ι, A ω ≤ B ω := by
    intro ω
    have h := step_4_6_20 setup N hN xStar hxStar ω
    simpa [A, B, xStar, noise, times, t0, setup.fStar_eq_objective_optimalPoint minimum]
      using h
  have hdelta_int :
      ∀ k ∈ times, Integrable (fun ω : StochasticBlockSamplePath S ι =>
        setup.delta xStar (t0 k) ω) setup.P := by
    intro k _hk
    simpa [t0, StochasticBlockMirrorDescentSetup.delta,
      SOptLib.iterateProcessView, StochasticBlockMirrorDescentSetup.ξ,
      StochasticBlockMirrorDescentSetup.block] using
      (scalar_delta_process_integrable setup xStar (t0 k))
  have hbar_int :
      ∀ k ∈ times, Integrable (fun ω : StochasticBlockSamplePath S ι =>
        setup.deltaBar (t0 k) ω) setup.P := by
    intro k _hk
    exact deltaBar_process_integrable setup (t0 k)
  have hnoise_int :
      ∀ k ∈ times, Integrable (fun ω : StochasticBlockSamplePath S ι => noise k ω) setup.P := by
    intro k hk
    have hd := (hdelta_int k hk).const_mul (setup.paperEta k)
    have hb := (hbar_int k hk).const_mul ((1 / 2 : ℝ) * setup.paperEta k ^ 2)
    simpa [noise, mul_assoc] using hd.add hb
  have hsumNoiseInt : Integrable
      (fun ω : StochasticBlockSamplePath S ι => Finset.sum times (fun k => noise k ω)) setup.P := by
    exact MeasureTheory.integrable_finset_sum (s := times) (μ := setup.P) hnoise_int
  have hAint : Integrable A setup.P := by
    simpa [A] using theorem_4_12_output_gap_integrable setup N hN minimum
  have hBint : Integrable B setup.P := by
    have hconst : Integrable
        (fun _ : StochasticBlockSamplePath S ι =>
          setup.aggregatePotential ⟨setup.w₀, setup.w₀_mem⟩ minimum.1) setup.P :=
      integrable_const _
    have hadd := hconst.add hsumNoiseInt
    simpa [B] using hadd.const_mul (setup.outputEtaSum N)⁻¹
  have hmono : ∫ ω : StochasticBlockSamplePath S ι, A ω ∂setup.P ≤
      ∫ ω : StochasticBlockSamplePath S ι, B ω ∂setup.P := by
    exact MeasureTheory.integral_mono hAint hBint hpoint
  have hBeval : ∫ ω : StochasticBlockSamplePath S ι, B ω ∂setup.P =
      (setup.outputEtaSum N)⁻¹ *
        (setup.aggregatePotential ⟨setup.w₀, setup.w₀_mem⟩ minimum.1 +
          ∫ ω : StochasticBlockSamplePath S ι, Finset.sum times (fun k => noise k ω) ∂setup.P) := by
    rw [show (∫ ω : StochasticBlockSamplePath S ι, B ω ∂setup.P) =
        ∫ ω : StochasticBlockSamplePath S ι,
          (setup.outputEtaSum N)⁻¹ *
            (setup.aggregatePotential ⟨setup.w₀, setup.w₀_mem⟩ minimum.1 +
              Finset.sum times (fun k => noise k ω)) ∂setup.P by rfl]
    rw [integral_const_mul]
    congr 1
    rw [integral_add (integrable_const _) hsumNoiseInt]
    simp
  calc
    ∫ ω : StochasticBlockSamplePath S ι, A ω ∂setup.P
        ≤ ∫ ω : StochasticBlockSamplePath S ι, B ω ∂setup.P := hmono
    _ = (setup.outputEtaSum N)⁻¹ *
        (setup.aggregatePotential ⟨setup.w₀, setup.w₀_mem⟩ minimum.1 +
          ∫ ω : StochasticBlockSamplePath S ι, Finset.sum times (fun k => noise k ω) ∂setup.P) := hBeval
    _ ≤ (setup.outputEtaSum N)⁻¹ *
        (setup.aggregatePotential ⟨setup.w₀, setup.w₀_mem⟩ minimum.1 +
          (1 / 2 : ℝ) * Finset.sum times (fun k => setup.paperEta k ^ 2 * sumM)) := by
          have hadd :
              setup.aggregatePotential ⟨setup.w₀, setup.w₀_mem⟩ minimum.1 +
                  (∫ ω : StochasticBlockSamplePath S ι,
                    Finset.sum times (fun k => noise k ω) ∂setup.P) ≤
                setup.aggregatePotential ⟨setup.w₀, setup.w₀_mem⟩ minimum.1 +
                  (1 / 2 : ℝ) * Finset.sum times
                    (fun k => setup.paperEta k ^ 2 * sumM) := by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_left hNoiseBound
                (setup.aggregatePotential ⟨setup.w₀, setup.w₀_mem⟩ minimum.1)
          exact mul_le_mul_of_nonneg_left hadd (inv_nonneg.mpr (le_of_lt hWpos))
    _ = (setup.outputEtaSum N)⁻¹ *
      (setup.aggregatePotential ⟨setup.w₀, setup.w₀_mem⟩ minimum.1 +
        (1 / 2 : ℝ) *
          Finset.sum (StochasticBlockMirrorDescentSetup.outputTimes N) (fun k =>
            (setup.paperEta k) ^ 2 *
              (Finset.sum Finset.univ (fun i => (setup.M i) ^ 2)))) := by
          simp [times, sumM]
