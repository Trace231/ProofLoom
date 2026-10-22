import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Data.Real.StarOrdered
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Independence.Basic
import SOptLib.Model.BlockSampling
import SOptLib.Model.Bregman
import SOptLib.Model.Iterates
import SOptLib.Model.NetworkMatrix
import SOptLib.Model.Norms
import SOptLib.Model.Prox
import SOptLib.Model.Saddle
import SOptLib.Glue.Algebra
import SOptLib.Glue.Analysis
import SOptLib.Glue.Probability
import SOptLib.Layer0.Oracle
import SOptLib.Layer1.Proximal
import SOptLib.Layer1.Telescope

namespace SDCS

open scoped BigOperators
open MeasureTheory

noncomputable section

/-- The stacked primal/dual space with one local copy per network agent. -/
abbrev Stacked (ι E : Type _) := ι → E

section Model

variable {ι E Ξ Ω : Type _}
variable [Fintype ι]
variable [MeasurableSpace E] [MeasurableSpace Ξ] [MeasurableSpace Ω]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [BorelSpace E] [SecondCountableTopology E]

/-- The stacked inner product on the product space, written as the source's Euclidean
pairing on `ℝ^{md}`.

Source: `book/research/Source.json setup.variable_space`: `y=(y_1,\ldots,y_m)
\in \mathbb{R}^{md}` and `setup.saddle_point_problem`: `\langle \mathcal{L}x,y\rangle`.
-/
def stackedInner (x y : Stacked ι E) : ℝ :=
  SOptLib.dependentProductInner x y

/-- Agreement subspace: all local copies are equal.

Source: `book/research/Source.json setup.problem`: `The constraint \mathcal{L}x=0`
encodes consensus among local copies.
-/
def AgreementSubspace (x : Stacked ι E) : Prop :=
  FiniteNetwork.IsAgreementState x

/-- Source-level semantic contract for the lifted connected-graph Laplacian
`\mathcal{L}=L\otimes I_d`.

Source: `source/FOML_complete.txt` lines 31788-31794: by construction the lifted
operator is symmetric positive semidefinite and its nullspace is the agreement
subspace; `book/research/Source.json assumptions[ConnectedGraph]`: `The graph G
is connected.`
-/
def IsConnectedLiftedLaplacian (Lop : Stacked ι E →L[ℝ] Stacked ι E) : Prop :=
  FiniteNetwork.IsConnectedLaplacian stackedInner Lop

/--
Source-facing data and primitive assumptions for stochastic decentralized communication
sliding.  The generated iterates are not fields: they are defined below from the oracle,
network operator, parameters, and initial state.
-/
structure Setup (ι E Ξ : Type _) [Fintype ι] [MeasurableSpace E] [MeasurableSpace Ξ]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  /-- The source network has at least one agent.

  Source: `book/research/Source.json setup.variable_space`: `x=(x_1,\ldots,x_m)
  \in X_1\times\cdots\times X_m`; `setup.problem`: constraints are indexed by
  `i=1,\ldots,m`; `assumptions[ConnectedGraph]`: `The graph G is connected.` -/
  agent_count_pos : 0 < Fintype.card ι
  /-- Local feasible sets `X_i`.

  Source: `book/research/Source.json setup.variable_space`: `x=(x_1,\ldots,x_m)\in
  X_1\times\cdots\times X_m`. -/
  feasible : ι → Set E
  /-- The local constraint sets are closed.

  Source: `source/FOML_complete.txt` lines 31902-31905: `X_i ⊆ R^d is a closed
  convex constraint set of agent i`. -/
  feasible_closed : ∀ i, IsClosed (feasible i)
  /-- The local constraint sets are convex.

  Source: `source/FOML_complete.txt` lines 31902-31905: `X_i ⊆ R^d is a closed
  convex constraint set of agent i`. -/
  feasible_convex : ∀ i, Convex ℝ (feasible i)
  /-- Local objectives `f_i`.

  Source: `book/research/Source.json setup.problem`: `F(x) := \sum_{i=1}^m
  f_i(x_i)`. -/
  localObjective : ι → E → ℝ
  /-- Chosen source subgradient `f_i'`.

  Source: `book/research/Source.json assumptions[StochasticOracleUnbiased]`:
  `E[G_i(u_t,\xi_it)]=f_i'(u_t)\in\partial f_i(u_t)`. -/
  subgradient : ι → E → E
  /-- Local Bregman/prox distance `V_i`.

  Source: `book/research/Source.json assumptions[StackedProxFunction]`:
  `V(x,u):=\sum_i V_i(x_i,u_i)`. -/
  localProx : ι → E → E → ℝ
  /-- Local distance-generating potential `ω_i` whose associated Bregman distance is
  `V_i`.

  Source: `source/FOML_complete.txt` lines 31874-31876: the local constraint sets
  are equipped with prox-functions associated with the distance-generating
  functions `ω_i`; lines 3336-3339 define the associated Bregman formula. -/
  localProxPotential : ι → E → ℝ
  /-- Selected gradient of the local distance-generating potential. -/
  localProxGradient : ι → E → E
  /-- Each local potential is a distance-generating function on the corresponding
  feasible set.

  Source: `source/FOML_complete.txt` lines 3323-3332 define distance-generating
  functions with differentiability and strong convexity, and lines 31874-31880
  specialize this prox-function setup to each `X_i`. -/
  localProx_isDistanceGenerating :
    ∀ i, IsDistanceGeneratingFunctionOn (feasible i) (localProxPotential i)
      (localProxGradient i)
  /-- `localProx` is the Bregman formula associated with the selected
  distance-generating potential.

  The book defines `V_i` on the source feasible domain.  The Lean model uses a total
  ambient function, so this field is the canonical ambient totalization of the same
  formula.

  Source: `source/FOML_complete.txt` lines 3336-3339:
  `V(x,z)=ν(z)-[ν(x)+<∇ν(x),z-x>]`. -/
  localProx_eq_bregmanFormula :
    ∀ i x u, localProx i x u =
      carrierBregmanFormula (localProxPotential i) (fun z : E => z)
        (localProxGradient i) x u
  /-- Lifted network operator `\mathcal{L}=L\otimes I_d`.

  Source: `book/research/Source.json setup.problem`: `the network consensus
  constraint encoded by the lifted Laplacian \mathcal{L}=L\otimes I_d`. -/
  networkOperator : Stacked ι E →L[ℝ] Stacked ι E
  /-- Primitive stochastic first-order oracle kernel `G_i(u, ξ)`.

  Source: `book/research/Source.json assumptions[StochasticOracleUnbiased]`:
  `E[G_i(u_t,\xi_it)]=f_i'(u_t)`. -/
  oracle : ι → E → Ξ → E
  /-- Distribution of a fresh oracle sample.

  Source: `source/FOML_complete.txt` lines 32533-32535: `the distribution P(ξ_i)
  is not known in advance`. -/
  oracleMeasure : Measure Ξ
  /-- The fresh oracle sample law is a probability distribution.

  Source: `source/FOML_complete.txt` lines 32533-32535 calls this object the
  distribution `P(ξ_i)`; the expectation assumptions (8.3.61)-(8.3.62) are taken
  with respect to this law. -/
  oracleMeasure_isProbability : IsProbabilityMeasure oracleMeasure
  /-- Diameter/growth constant `M` from (8.3.16).

  Source: `book/research/Source.json assumptions[ObjectiveGrowthCondition]`:
  `... <= M||x-y||`. -/
  M : ℝ
  /-- Oracle variance constant `σ`.

  Source: `book/research/Source.json assumptions[StochasticOracleVariance]`:
  `E[||G_i(u_t,\xi_it)-f_i'(u_t)||_*^2] <= \sigma^2`. -/
  sigma : ℝ
  /-- Assumption 18 plus the source's lifted-Laplacian semantics.

  Source: `book/research/Source.json assumptions[ConnectedGraph]`: `The graph G
  is connected`; `source/FOML_complete.txt` lines 31788-31794: the lifted
  Laplacian is symmetric positive semidefinite and has agreement nullspace. -/
  networkIsConnectedLaplacian : IsConnectedLiftedLaplacian networkOperator
  /-- Source saddle-point existence assumption, stated with the primal optimality and
  saddle inequalities rather than as an opaque proposition.

  Source: `book/research/Source.json assumptions[SaddlePointExistence]`: `there
  exists an optimal solution x^*\in X of (8.3.6) and there exists y^*\in
  \mathbb{R}^{md} such that (x^*,y^*) is a saddle point of (8.3.7)`. -/
  saddlePointExistsSource :
    ∃ xStar yStar,
      ((∀ i, xStar i ∈ feasible i) ∧ networkOperator xStar = 0 ∧
        (∀ x, (∀ i, x i ∈ feasible i) → networkOperator x = 0 →
          (∑ i, localObjective i (xStar i)) ≤ (∑ i, localObjective i (x i)))) ∧
      (∀ x y, (∀ i, x i ∈ feasible i) →
        ((∑ i, localObjective i (xStar i)) + stackedInner (networkOperator xStar) y -
            ((∑ i, localObjective i (x i)) + stackedInner (networkOperator x) yStar) ≤ 0) ∧
          (0 ≤ (∑ i, localObjective i (x i)) + stackedInner (networkOperator x) yStar -
            ((∑ i, localObjective i (xStar i)) + stackedInner (networkOperator xStar) y)))
  /-- Local prox strong-convexity lower bound (8.3.12).

  Source: `book/research/Source.json assumptions[ProxStrongConvexityModulusOne]`:
  `V_i(x_i,u_i) >= 1/2 ||x_i-u_i||^2`. -/
  proxStrongConvexity :
    ∀ i x u, i ∈ (Finset.univ : Finset ι) →
      x ∈ feasible i → u ∈ feasible i →
        (1 / 2 : ℝ) * ‖x - u‖ ^ 2 ≤ localProx i x u
  /-- Objective growth/subgradient condition (8.3.16), specialized to `μ = 0`.

  Source: `book/research/Source.json assumptions[ObjectiveGrowthCondition]`:
  `μ V_i(y,x) <= f_i(x)-f_i(y)-<f_i'(y),x-y> <= M||x-y||`. -/
  objectiveGrowth :
    ∀ i x y, x ∈ feasible i → y ∈ feasible i →
      0 ≤ localObjective i x - localObjective i y - inner ℝ (subgradient i y) (x - y) ∧
        localObjective i x - localObjective i y - inner ℝ (subgradient i y) (x - y)
          ≤ M * ‖x - y‖
  /-- General nonsmooth convex case constant.

  Source: `book/research/Source.json assumptions[GeneralConvexCase]`: `μ=0 and
  M>0`. -/
  M_pos : 0 < M
  /-- Oracle unbiasedness assumption (8.3.61).

  Source: `book/research/Source.json assumptions[StochasticOracleUnbiased]`:
  `E[G_i(u_t,\xi_it)]=f_i'(u_t)`. -/
  oracleIntegrable :
    ∀ i u, Integrable (fun ξ => oracle i u ξ) oracleMeasure
  /-- Oracle unbiasedness assumption (8.3.61), with the well-formed expectation
  exposed separately by `oracleIntegrable`.

  Source: `book/research/Source.json assumptions[StochasticOracleUnbiased]`:
  `E[G_i(u_t,\xi_it)]=f_i'(u_t)`. -/
  oracleUnbiased :
    ∀ i u, ∫ ξ, oracle i u ξ ∂oracleMeasure = subgradient i u
  /-- Joint measurability of the centered oracle residual kernel.

  Source: `book/research/Source.json assumptions[StochasticOracleUnbiased]` and
  `assumptions[StochasticOracleVariance]` state expectations of
  `G_i(u_t,\xi_it)` and `G_i(u_t,\xi_it)-f_i'(u_t)` for generated query points.
  This field records the random-kernel well-formedness implicit in those
  expectation statements; centering itself is still derived from
  `oracleUnbiased`, not assumed here. -/
  oracleErrorKernelMeasurable :
    ∀ i, Measurable (fun p : E × Ξ => subgradient i p.1 - oracle i p.1 p.2)
  /-- Oracle variance bound (8.3.62).

  Source: `book/research/Source.json assumptions[StochasticOracleVariance]`:
  `E[||G_i(u_t,\xi_it)-f_i'(u_t)||_*^2] <= \sigma^2`.  This is the
  well-formedness half of that stated expectation, separated from the numerical
  bound below. -/
  oracleVarianceIntegrable :
    ∀ i u, Integrable (fun ξ => ‖oracle i u ξ - subgradient i u‖ ^ 2) oracleMeasure
  /-- Oracle variance bound (8.3.62).

  Source: `book/research/Source.json assumptions[StochasticOracleVariance]`:
  `E[||G_i(u_t,\xi_it)-f_i'(u_t)||_*^2] <= \sigma^2`. -/
  oracleVariance :
    ∀ i u, ∫ ξ, ‖oracle i u ξ - subgradient i u‖ ^ 2 ∂oracleMeasure ≤ sigma ^ 2

namespace Setup

variable (S : Setup ι E Ξ)

/-- The global objective `F(x) = ∑_i f_i(x_i)` from (8.3.6).

Source: `book/research/Source.json setup.problem`: `F(x) := \sum_{i=1}^m
f_i(x_i)`.
-/
def objective (x : Stacked ι E) : ℝ :=
  ∑ i, S.localObjective i (x i)

/-- The stacked prox function `V(x,u) = ∑_i V_i(x_i,u_i)` from (8.3.14).

Source: `book/research/Source.json assumptions[StackedProxFunction]`:
`V(x,u):=\sum_i V_i(x_i,u_i)`.
-/
def stackedProx (x u : Stacked ι E) : ℝ :=
  ∑ i, S.localProx i (x i) (u i)

/-- Bregman diagonal zero for the local prox-functions.

Source: `source/FOML_complete.txt` lines 3336-3339 define
`V(x,z)=ν(z)-[ν(x)+<∇ν(x),z-x>]`, hence `V(x,x)=0`.
-/
theorem localProx_self_eq_zero (i : ι) (x : E) (hx : x ∈ S.feasible i) :
    S.localProx i x x = 0 := by
  rw [S.localProx_eq_bregmanFormula]
  simp [carrierBregmanFormula]

/-- Lemma 3.5 projection inequality for the local source prox-functions.

This is derived from the Bregman realization of `localProx`, not assumed as a
primitive endpoint.  It is the projection step used in Proposition 8.7 and the
proof of Lemma 8.5.

Source: `book/research/Source.json key_lemmas[ProjectionLemma35]` and
`source/FOML_complete.txt` lines 3548-3574.
-/
theorem localProx_sourceProjectionInequality
    (i : ι) (p : E → ℝ) (xTilde yTilde uHat u : E) (mu1 mu2 : ℝ)
    (hp : ConvexOn ℝ (S.feasible i) p)
    (hmu1 : 0 ≤ mu1) (hmu2 : 0 ≤ mu2)
    (hxTilde : xTilde ∈ S.feasible i) (hyTilde : yTilde ∈ S.feasible i)
    (huHat : uHat ∈ S.feasible i) (hu : u ∈ S.feasible i)
    (hMin :
      IsMinOn
        (fun v =>
          p v + mu1 * S.localProx i xTilde v + mu2 * S.localProx i yTilde v)
        (S.feasible i) uHat) :
    p uHat + mu1 * S.localProx i xTilde uHat +
        mu2 * S.localProx i yTilde uHat ≤
      p u + mu1 * S.localProx i xTilde u + mu2 * S.localProx i yTilde u -
        (mu1 + mu2) * S.localProx i uHat u := by
  classical
  have hSegment :
      ∀ (a z u : E), z ∈ S.feasible i →
        let d : E := u - z;
        let β : ℝ → ℝ := fun t =>
          if _ht : t ∈ Set.Icc (0 : ℝ) 1 then
            S.localProx i a (AffineMap.lineMap z u t) - S.localProx i a z
          else 0;
        HasDerivWithinAt β
          (inner ℝ (S.localProxGradient i z - S.localProxGradient i a) d)
          (Set.Icc (0 : ℝ) 1) 0 := by
    intro a z u hz
    have hbase :
        let d : E := u - z;
        let β : ℝ → ℝ := fun t =>
          if _ht : t ∈ Set.Icc (0 : ℝ) 1 then
            carrierBregmanFormula (S.localProxPotential i) (fun q : E => q)
              (S.localProxGradient i) a (AffineMap.lineMap z u t) -
              carrierBregmanFormula (S.localProxPotential i) (fun q : E => q)
                (S.localProxGradient i) a z
          else 0;
        HasDerivWithinAt β
          (inner ℝ (S.localProxGradient i z - S.localProxGradient i a) d)
          (Set.Icc (0 : ℝ) 1) 0 := by
      exact
        bregman_segment_difference_hasDerivWithinAt_zero
          (v := S.localProxPotential i) (grad := S.localProxGradient i)
          (x := a) (xp := z) (u := u)
          ((S.localProx_isDistanceGenerating i).2.1 z hz)
    simpa [S.localProx_eq_bregmanFormula i] using hbase
  have hThree :
      ∀ a b c : E,
        S.localProx i a c =
          S.localProx i a b +
            inner ℝ (S.localProxGradient i b - S.localProxGradient i a) (c - b) +
              S.localProx i b c := by
    intro a b c
    simpa [S.localProx_eq_bregmanFormula i] using
      (carrierBregmanDivergence_three_point_identity
        (v := S.localProxPotential i) (eval := fun q : E => q)
        (grad := S.localProxGradient i)
        (V := fun x z =>
          carrierBregmanFormula (S.localProxPotential i) (fun q : E => q)
            (S.localProxGradient i) x z)
        (by
          intro x z
          rfl)
        a b c)
  have hOpt :
      ∀ v, v ∈ S.feasible i →
        p uHat + mu1 * S.localProx i xTilde uHat +
            mu2 * S.localProx i yTilde uHat ≤
          p v + mu1 * S.localProx i xTilde v + mu2 * S.localProx i yTilde v := by
    intro v hv
    exact (isMinOn_iff.mp hMin) v hv
  exact
    SOptLib.two_bregman_argmin_descent (X := S.feasible i) (p := p)
      (V := S.localProx i) (grad := S.localProxGradient i) hp
      (xTilde := xTilde) (yTilde := yTilde) (uHat := uHat)
      (mu1 := mu1) (mu2 := mu2) huHat hmu1 hmu2 hSegment hThree hOpt u hu

/-- The squared stacked norm `∑_i ‖x_i‖^2` from (8.3.13).

Source: `book/research/Source.json assumptions[StackedPrimalNorm]`:
`\|x\|^2 := \sum_i \|x_i\|_{X_i}^2`.
-/
def stackedNormSq (_S : Setup ι E Ξ) (x : Stacked ι E) : ℝ :=
  ∑ i, ‖x i‖ ^ 2


/-- The source stacked distance induced by the squared-sum norm. -/
def stackedDist (S : Setup ι E Ξ) (x y : Stacked ι E) : ℝ :=
  (fun x => ‖WithLp.toLp 2 x‖) (x - y)

/-- Nonnegativity of the source stacked squared norm. -/
theorem stackedNormSq_nonneg (S : Setup ι E Ξ) (x : Stacked ι E) :
    0 ≤ S.stackedNormSq x := by
  dsimp [stackedNormSq]
  exact Finset.sum_nonneg (fun i _hi => sq_nonneg (‖x i‖))

/-- Nonnegativity of the source stacked norm. -/
theorem stackedNorm_nonneg (S : Setup ι E Ξ) (x : Stacked ι E) :
    0 ≤ (fun x => ‖WithLp.toLp 2 x‖) x := by
  exact norm_nonneg _

/-- The induced operator norm of the lifted network operator for the source stacked
Euclidean product norm.

This is the source-facing meaning of `‖\mathcal{L}‖` in (8.3.32), (8.3.33), and
Theorem 8.11, rather than Lean's default operator norm between Pi-normed function
spaces.

Source: `book/research/Source.json algorithm_spec.parameters.theorem_811_schedule`:
`η_k=2||L||`, `τ_k=||L||`, and
`T_k=ceil(m(M^2+sigma^2)N/(||L||^2 Dtilde))`.
-/
def networkOperatorNorm (S : Setup ι E Ξ) : ℝ :=
  SOptLib.inducedSeminormOperatorNorm
    ((normSeminorm ℝ (WithLp 2 (Stacked ι E))).comp
      (WithLp.linearEquiv 2 ℝ (Stacked ι E)).symm.toLinearMap)
    ((normSeminorm ℝ (WithLp 2 (Stacked ι E))).comp
      (WithLp.linearEquiv 2 ℝ (Stacked ι E)).symm.toLinearMap)
    S.networkOperator

/-- Nonnegativity of the induced source operator norm. -/
theorem networkOperatorNorm_nonneg (S : Setup ι E Ξ) : 0 ≤ S.networkOperatorNorm := by
  unfold networkOperatorNorm
  let A : Set ℝ := { c : ℝ | ∃ x : Stacked ι E,
    (fun x => ‖WithLp.toLp 2 x‖) x ≤ 1 ∧ c = (fun x => ‖WithLp.toLp 2 x‖) (S.networkOperator x) }
  have hmem : (0 : ℝ) ∈ A := by
    refine ⟨0, ?_, ?_⟩
    · simp [A]
    · simp [A]
  change 0 ≤ sSup A
  by_cases hA : BddAbove A
  · exact le_csSup hA hmem
  · rw [Real.sSup_of_not_bddAbove hA]

/-- Squaring the explicit source stacked norm recovers the source squared norm. -/
private theorem stackedNorm_sq_eq (S : Setup ι E Ξ) (x : Stacked ι E) :
    (fun x => ‖WithLp.toLp 2 x‖) x ^ 2 = S.stackedNormSq x := by
  simpa [stackedNormSq] using
    (PiLp.norm_sq_eq_of_L2 (fun _ : ι => E) (WithLp.toLp 2 x))

/-- The source squared stacked norm is homogeneous under real scaling. -/
private theorem stackedNormSq_smul (S : Setup ι E Ξ) (a : ℝ) (x : Stacked ι E) :
    S.stackedNormSq (a • x) = a ^ 2 * S.stackedNormSq x := by
  dsimp [stackedNormSq]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  simp [Pi.smul_apply, norm_smul, mul_pow]

/-- The source squared stacked norm is invariant under negation. -/
private theorem stackedNormSq_neg (S : Setup ι E Ξ) (x : Stacked ι E) :
    S.stackedNormSq (-x) = S.stackedNormSq x := by
  simpa using (stackedNormSq_smul S (-1 : ℝ) x)

/-- The source squared stacked distance is symmetric. -/
private theorem stackedNormSq_sub_comm (S : Setup ι E Ξ) (x y : Stacked ι E) :
    S.stackedNormSq (x - y) = S.stackedNormSq (y - x) := by
  have h := stackedNormSq_neg S (x - y)
  simpa [neg_sub] using h.symm

/-- Polarization identity for the dual endpoint terms in Lemma 8.5. -/
private theorem stackedNormSq_endpoint_dual_identity (S : Setup ι E Ξ)
    (c : ℝ) (y y0 yN : Stacked ι E) :
    (c / 2) * S.stackedNormSq yN +
        (c / 2) * (S.stackedNormSq (y - y0) - S.stackedNormSq (y - yN)) =
      (c / 2) * S.stackedNormSq y0 +
        c * stackedInner (yN - y0) y := by
  simpa only [← stackedNorm_sq_eq S, stackedInner,
    SOptLib.dependentProductInner_eq_piLp_inner, WithLp.toLp_sub] using
      (half_mul_norm_sq_add_half_mul_sq_dist_drop_eq c
        (WithLp.toLp 2 y) (WithLp.toLp 2 y0) (WithLp.toLp 2 yN))

/-- Scalar assembly of the non-primal Lemma 8.5 terms after Young absorption. -/
private theorem sdcs_nonprimal_assembly_algebra
    {term lagged prox dual linY primal terminalDual laggedPrimal dualTailA
      dualTailB endpointDual initDual perturbTail perturb : ℝ}
    (hTerm : term ≤ linY + primal + terminalDual)
    (hLagged : -lagged ≤ laggedPrimal + dualTailA)
    (hProx : primal + laggedPrimal ≤ prox)
    (hDual : dual ≤ endpointDual - dualTailB)
    (hDualTail : dualTailA = dualTailB)
    (hEndpoint : terminalDual + endpointDual = initDual + perturbTail)
    (hPerturb : linY + perturbTail = perturb) :
    term - lagged - prox + dual ≤ initDual + perturb := by
  nlinarith

/-- Scalar assembly for the retained post-(c) Lemma 8.5 aggregate.

This is the same non-primal bookkeeping as `sdcs_nonprimal_assembly_algebra`,
but it keeps the terminal primal prox term on the left rather than replacing the
terminal pairing by a Young split.
-/
private theorem sdcs_retained_nonprimal_assembly_algebra
    {term lagged prox dual terminalProx terminalDual laggedPrimal dualTailA
      dualTailB endpointDual initDual : ℝ}
    (hLagged : -lagged ≤ laggedPrimal + dualTailA)
    (hProx : terminalProx + laggedPrimal ≤ prox)
    (hDual : dual ≤ endpointDual - dualTailB)
    (hDualTail : dualTailA = dualTailB)
    (hEndpoint : terminalDual + endpointDual = initDual) :
    term - lagged - prox + dual + terminalProx + terminalDual ≤
      term + initDual := by
  nlinarith

/-- Split a one-based range sum into its terminal term plus a lagged predecessor
window, allowing pointwise lower bounds only on the lagged part. -/
private theorem terminal_add_lagged_le_range_sum_of_lagged_le
    (A B : ℕ → ℝ) (N : ℕ) (hN : 1 ≤ N)
    (hLagged : ∀ t ∈ Finset.Icc 2 N, A (t - 1) ≤ B (t - 1)) :
    B N + ∑ t ∈ Finset.Icc 2 N, A (t - 1) ≤
      ∑ k ∈ Finset.range N, B (k + 1) := by
  exact terminal_add_sum_Icc_lagged_le_sum_range_succ_of_lagged_le A B N hN hLagged

/-- The source stacked norm is homogeneous under real scaling. -/
private theorem stackedNorm_smul (S : Setup ι E Ξ) (a : ℝ) (x : Stacked ι E) :
    (fun x => ‖WithLp.toLp 2 x‖) (a • x) = |a| * (fun x => ‖WithLp.toLp 2 x‖) x := by
  change ‖WithLp.toLp 2 (a • x)‖ = |a| * ‖WithLp.toLp 2 x‖
  rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
  change Real.sqrt (S.stackedNormSq (a • x)) =
    |a| * Real.sqrt (S.stackedNormSq x)
  rw [stackedNormSq_smul]
  rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs]


/-- Zero source stacked norm is equivalent to the zero stacked vector. -/
private theorem stackedNorm_eq_zero_iff (S : Setup ι E Ξ) (x : Stacked ι E) :
    (fun x => ‖WithLp.toLp 2 x‖) x = 0 ↔ x = 0 := by
  exact SOptLib.dependentProductL2Seminorm_eq_zero_iff x

/-- A unit source-stacked vector is bounded by the source induced network norm.

The only nontrivial infrastructure obligation is boundedness of the `sSup` set:
the proof should compare the source finite square-sum norm with Lean's finite Pi
norm and then use the continuous linear-map operator norm. -/
private theorem stacked_network_operator_norm_unit_le
    (S : Setup ι E Ξ) (x : Stacked ι E) (hx : (fun x => ‖WithLp.toLp 2 x‖) x ≤ 1) :
    (fun x => ‖WithLp.toLp 2 x‖) (S.networkOperator x) ≤ S.networkOperatorNorm := by
  exact SOptLib.map_le_inducedSeminormOperatorNorm_of_le_one
    ((normSeminorm ℝ (WithLp 2 (Stacked ι E))).comp
      (WithLp.linearEquiv 2 ℝ (Stacked ι E)).symm.toLinearMap)
    ((normSeminorm ℝ (WithLp 2 (Stacked ι E))).comp
      (WithLp.linearEquiv 2 ℝ (Stacked ι E)).symm.toLinearMap)
    S.networkOperator
    (by simpa using
      (SOptLib.bddAbove_dependentProductL2Seminorm_image_unitBall
        (A := S.networkOperator))) x hx

/-- The source induced network norm bounds the source stacked norm of every image. -/
private theorem stacked_network_operator_norm_le
    (S : Setup ι E Ξ) (d : Stacked ι E) :
    (fun x => ‖WithLp.toLp 2 x‖) (S.networkOperator d) ≤ S.networkOperatorNorm * (fun x => ‖WithLp.toLp 2 x‖) d := by
  exact SOptLib.map_le_inducedSeminormOperatorNorm_mul
    ((normSeminorm ℝ (WithLp 2 (Stacked ι E))).comp
      (WithLp.linearEquiv 2 ℝ (Stacked ι E)).symm.toLinearMap)
    ((normSeminorm ℝ (WithLp 2 (Stacked ι E))).comp
      (WithLp.linearEquiv 2 ℝ (Stacked ι E)).symm.toLinearMap)
    S.networkOperator
    (by
      intro z
      change ‖WithLp.toLp 2 z‖ = 0 ↔ z = 0
      rw [norm_eq_zero, WithLp.toLp_eq_zero])
    (by simpa using
      (SOptLib.bddAbove_dependentProductL2Seminorm_image_unitBall
        (A := S.networkOperator))) d

/-- Source-stacked squared norm image bound for the lifted network operator. -/
private theorem stacked_network_operator_norm_sq_le
    (S : Setup ι E Ξ) (d : Stacked ι E) :
    S.stackedNormSq (S.networkOperator d) ≤
      S.networkOperatorNorm ^ 2 * S.stackedNormSq d := by
  have hbound :=
    SOptLib.map_sq_le_inducedSeminormOperatorNorm_sq_mul
      ((normSeminorm ℝ (WithLp 2 (Stacked ι E))).comp
        (WithLp.linearEquiv 2 ℝ (Stacked ι E)).symm.toLinearMap)
      ((normSeminorm ℝ (WithLp 2 (Stacked ι E))).comp
        (WithLp.linearEquiv 2 ℝ (Stacked ι E)).symm.toLinearMap)
      S.networkOperator
      (by simpa using
        (SOptLib.bddAbove_dependentProductL2Seminorm_image_unitBall
          (A := S.networkOperator))) d
  change (fun x => ‖WithLp.toLp 2 x‖) (S.networkOperator d) ^ 2 ≤
    S.networkOperatorNorm ^ 2 * (fun x => ‖WithLp.toLp 2 x‖) d ^ 2 at hbound
  simpa only [stackedNorm_sq_eq S] using hbound

/-- Cauchy-Schwarz for the source stacked inner product and source stacked norm. -/
private theorem stackedInner_le_stackedNorm_mul
    (S : Setup ι E Ξ) (x y : Stacked ι E) :
    stackedInner x y ≤ (fun x => ‖WithLp.toLp 2 x‖) x * (fun x => ‖WithLp.toLp 2 x‖) y := by
  simpa [stackedInner, SOptLib.dependentProductInner,
    SOptLib.dependentProductNormSq_def, PiLp.norm_eq_of_L2] using
      (SOptLib.dependentProductInner_le_l2Seminorm_mul x y)

/-- Triangle inequality for the source finite-product stacked norm. -/
private theorem stackedNorm_add_le (S : Setup ι E Ξ) (x y : Stacked ι E) :
    (fun x => ‖WithLp.toLp 2 x‖) (x + y) ≤ (fun x => ‖WithLp.toLp 2 x‖) x + (fun x => ‖WithLp.toLp 2 x‖) y := by
  exact SOptLib.dependentProductL2Seminorm_add_le x y

/-- Young absorption for a source-stacked cross term using a squared-norm budget.

This is the local algebraic shape needed in Lemma 8.5 steps (b)-(e): once a
network residual squared norm has been bounded by a scalar multiple of a primal
squared step, a coefficient condition absorbs the cross term into the primal and
dual quadratic budgets. -/
private theorem stacked_inner_young_absorption_of_sq_bound
    (S : Setup ι E Ξ) {A B c K q : ℝ} {g v : Stacked ι E}
    (hA : 0 < A) (hB : 0 < B) (hc : 0 ≤ c) (hK : 0 ≤ K) (hq : 0 ≤ q)
    (hcoef : c ^ 2 * K ≤ 4 * A * B)
    (hg : S.stackedNormSq g ≤ K * q) :
    c * stackedInner g v ≤ A * q + B * S.stackedNormSq v := by
  have hG_nonneg : 0 ≤ (fun x => ‖WithLp.toLp 2 x‖) g := S.stackedNorm_nonneg g
  have hV_nonneg : 0 ≤ (fun x => ‖WithLp.toLp 2 x‖) v := S.stackedNorm_nonneg v
  have hbudget_norm :
      (fun x => ‖WithLp.toLp 2 x‖) g ^ 2 ≤ K * q := by
    rw [stackedNorm_sq_eq S]
    exact hg
  have hinner :
      c * stackedInner g v ≤ c * ((fun x => ‖WithLp.toLp 2 x‖) g * (fun x => ‖WithLp.toLp 2 x‖) v) :=
    mul_le_mul_of_nonneg_left (stackedInner_le_stackedNorm_mul S g v) hc
  have hprod_sq :
      (c * ((fun x => ‖WithLp.toLp 2 x‖) g * (fun x => ‖WithLp.toLp 2 x‖) v)) ^ 2 ≤
        (A * q + B * (fun x => ‖WithLp.toLp 2 x‖) v ^ 2) ^ 2 := by
    have hYsq_nonneg : 0 ≤ (fun x => ‖WithLp.toLp 2 x‖) v ^ 2 := sq_nonneg _
    have hAB_nonneg : 0 ≤ A * B := mul_nonneg (le_of_lt hA) (le_of_lt hB)
    have hcoef_q :
        c ^ 2 * K * q ≤ 4 * A * B * q :=
      mul_le_mul_of_nonneg_right hcoef hq
    have hcg :
        c ^ 2 * (fun x => ‖WithLp.toLp 2 x‖) g ^ 2 ≤ c ^ 2 * (K * q) :=
      mul_le_mul_of_nonneg_left hbudget_norm (sq_nonneg c)
    have hcg' :
        c ^ 2 * (fun x => ‖WithLp.toLp 2 x‖) g ^ 2 ≤ 4 * A * B * q := by
      nlinarith [hcoef_q, hcg]
    have hleft_bound :
        c ^ 2 * (fun x => ‖WithLp.toLp 2 x‖) g ^ 2 * (fun x => ‖WithLp.toLp 2 x‖) v ^ 2 ≤
          4 * A * B * q * (fun x => ‖WithLp.toLp 2 x‖) v ^ 2 :=
      mul_le_mul_of_nonneg_right hcg' hYsq_nonneg
    have hyoung_sq :
        4 * A * B * q * (fun x => ‖WithLp.toLp 2 x‖) v ^ 2 ≤
          (A * q + B * (fun x => ‖WithLp.toLp 2 x‖) v ^ 2) ^ 2 := by
      have hsquare : 0 ≤ (A * q - B * (fun x => ‖WithLp.toLp 2 x‖) v ^ 2) ^ 2 := sq_nonneg _
      nlinarith [hsquare]
    calc
      (c * ((fun x => ‖WithLp.toLp 2 x‖) g * (fun x => ‖WithLp.toLp 2 x‖) v)) ^ 2
          = c ^ 2 * (fun x => ‖WithLp.toLp 2 x‖) g ^ 2 * (fun x => ‖WithLp.toLp 2 x‖) v ^ 2 := by ring
      _ ≤ 4 * A * B * q * (fun x => ‖WithLp.toLp 2 x‖) v ^ 2 := hleft_bound
      _ ≤ (A * q + B * (fun x => ‖WithLp.toLp 2 x‖) v ^ 2) ^ 2 := hyoung_sq
  have hright_nonneg :
      0 ≤ A * q + B * (fun x => ‖WithLp.toLp 2 x‖) v ^ 2 :=
    add_nonneg (mul_nonneg (le_of_lt hA) hq)
      (mul_nonneg (le_of_lt hB) (sq_nonneg _))
  have hprod_nonneg :
      0 ≤ c * ((fun x => ‖WithLp.toLp 2 x‖) g * (fun x => ‖WithLp.toLp 2 x‖) v) :=
    mul_nonneg hc (mul_nonneg hG_nonneg hV_nonneg)
  have hprod_le :
      c * ((fun x => ‖WithLp.toLp 2 x‖) g * (fun x => ‖WithLp.toLp 2 x‖) v) ≤
        A * q + B * (fun x => ‖WithLp.toLp 2 x‖) v ^ 2 :=
    (sq_le_sq₀ hprod_nonneg hright_nonneg).mp hprod_sq
  calc
    c * stackedInner g v ≤ c * ((fun x => ‖WithLp.toLp 2 x‖) g * (fun x => ‖WithLp.toLp 2 x‖) v) := hinner
    _ ≤ A * q + B * (fun x => ‖WithLp.toLp 2 x‖) v ^ 2 := hprod_le
    _ = A * q + B * S.stackedNormSq v := by
          rw [stackedNorm_sq_eq S]

/-- Degenerate-safe version of `stacked_inner_young_absorption_of_sq_bound`.

The current source-boundary bridge assumes nonnegative parameters, not strict
positivity of every weighted budget.  When a budget coefficient vanishes, the
same coefficient condition forces either a zero cross coefficient or a zero
source residual budget, and the inequality still follows. -/
private theorem stacked_inner_young_absorption_of_sq_bound_nonneg
    (S : Setup ι E Ξ) {A B c K q : ℝ} {g v : Stacked ι E}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hc : 0 ≤ c) (hK : 0 ≤ K) (hq : 0 ≤ q)
    (hcoef : c ^ 2 * K ≤ 4 * A * B)
    (hg : S.stackedNormSq g ≤ K * q) :
    c * stackedInner g v ≤ A * q + B * S.stackedNormSq v := by
  have hright : 0 ≤ A * q + B * S.stackedNormSq v :=
    add_nonneg (mul_nonneg hA hq)
      (mul_nonneg hB (S.stackedNormSq_nonneg v))
  simpa only [stackedInner, SOptLib.dependentProductInner_eq_piLp_inner,
    stackedNorm_sq_eq S] using
      (mul_inner_le_quadratic_sum_of_norm_sq_le_mul
        (g := WithLp.toLp 2 g) (v := WithLp.toLp 2 v)
        hA hB hc hq hcoef
        (by simpa only [stackedNorm_sq_eq S] using hg))

/-- Terminal SDCS specialization of the source-stacked Young absorption. -/
private theorem sdcs_terminal_young_absorption
    (S : Setup ι E Ξ) {thetaN theta1 tau1 etaN : ℝ}
    {g dx v : Stacked ι E}
    (hthetaN : 0 ≤ thetaN) (htheta1 : 0 ≤ theta1) (htau1 : 0 ≤ tau1)
    (hetaN : 0 ≤ etaN)
    (hcond : thetaN * S.networkOperatorNorm ^ 2 ≤ theta1 * tau1 * etaN)
    (hg : S.stackedNormSq g ≤ S.networkOperatorNorm ^ 2 * S.stackedNormSq dx) :
    thetaN * stackedInner g v ≤
      (thetaN * etaN / 2) * S.stackedNormSq dx +
        (theta1 * tau1 / 2) * S.stackedNormSq v := by
  have hA : 0 ≤ thetaN * etaN / 2 := by positivity
  have hB : 0 ≤ theta1 * tau1 / 2 := by positivity
  have hK : 0 ≤ S.networkOperatorNorm ^ 2 := sq_nonneg _
  have hq : 0 ≤ S.stackedNormSq dx := S.stackedNormSq_nonneg dx
  have hcoef :
      thetaN ^ 2 * S.networkOperatorNorm ^ 2 ≤
        4 * (thetaN * etaN / 2) * (theta1 * tau1 / 2) := by
    nlinarith [hcond, hthetaN]
  exact
    stacked_inner_young_absorption_of_sq_bound_nonneg S
      (A := thetaN * etaN / 2) (B := theta1 * tau1 / 2)
      (c := thetaN) (K := S.networkOperatorNorm ^ 2)
      (q := S.stackedNormSq dx) (g := g) (v := v)
      hA hB hthetaN hK hq hcoef hg

/-- Lagged-tail SDCS specialization of the source-stacked Young absorption. -/
private theorem sdcs_lagged_young_absorption
    (S : Setup ι E Ξ) {thetaPrev theta alpha etaPrev tau : ℝ}
    {g dx dy : Stacked ι E}
    (hthetaPrev : 0 ≤ thetaPrev) (htheta : 0 ≤ theta) (halpha : 0 ≤ alpha)
    (hetaPrev : 0 ≤ etaPrev) (htau : 0 ≤ tau)
    (hlink : alpha * theta = thetaPrev)
    (hcond : alpha * S.networkOperatorNorm ^ 2 ≤ etaPrev * tau)
    (hg : S.stackedNormSq g ≤ S.networkOperatorNorm ^ 2 * S.stackedNormSq dx) :
    theta * alpha * stackedInner g dy ≤
      (thetaPrev * etaPrev / 2) * S.stackedNormSq dx +
        (theta * tau / 2) * S.stackedNormSq dy := by
  have hA : 0 ≤ thetaPrev * etaPrev / 2 := by positivity
  have hB : 0 ≤ theta * tau / 2 := by positivity
  have hc : 0 ≤ theta * alpha := mul_nonneg htheta halpha
  have hK : 0 ≤ S.networkOperatorNorm ^ 2 := sq_nonneg _
  have hq : 0 ≤ S.stackedNormSq dx := S.stackedNormSq_nonneg dx
  have hscale_nonneg : 0 ≤ alpha * theta ^ 2 :=
    mul_nonneg halpha (sq_nonneg _)
  have hscaled :
      alpha * theta ^ 2 * (alpha * S.networkOperatorNorm ^ 2) ≤
        alpha * theta ^ 2 * (etaPrev * tau) :=
    mul_le_mul_of_nonneg_left hcond hscale_nonneg
  have hcoef :
      (theta * alpha) ^ 2 * S.networkOperatorNorm ^ 2 ≤
        4 * (thetaPrev * etaPrev / 2) * (theta * tau / 2) := by
    calc
      (theta * alpha) ^ 2 * S.networkOperatorNorm ^ 2
          = alpha * theta ^ 2 * (alpha * S.networkOperatorNorm ^ 2) := by
            ring
      _ ≤ alpha * theta ^ 2 * (etaPrev * tau) := hscaled
      _ = 4 * (thetaPrev * etaPrev / 2) * (theta * tau / 2) := by
            rw [← hlink]
            ring
  exact
    stacked_inner_young_absorption_of_sq_bound_nonneg S
      (A := thetaPrev * etaPrev / 2) (B := theta * tau / 2)
      (c := theta * alpha) (K := S.networkOperatorNorm ^ 2)
      (q := S.stackedNormSq dx) (g := g) (v := dy)
      hA hB hc hK hq hcoef hg

/-- Residual branch extraction from the retained terminal inequality in Lemma 8.5.

This is the algebra after Source.json Lemma 8.5 step 16: the retained terminal
bound gives the primal prox drop and the terminal dual square before the final
Young split.  The helper keeps the retained aggregate as an explicit hypothesis
so the remaining proof obligation is exactly the source step-16 estimate, not
the later scalar residual manipulation.
-/
private theorem sdcs_residual_branches_of_retained_terminal_bound
    (S : Setup ι E Ξ) {theta eta tau theta1 tau1 R prox : ℝ}
    {dx g v : Stacked ι E}
    (htheta : 0 ≤ theta) (heta_pos : 0 < eta) (htau_pos : 0 < tau)
    (htheta_ge_one : 1 ≤ theta)
    (htheta_tau : theta * tau = theta1 * tau1)
    (hcond : theta * S.networkOperatorNorm ^ 2 ≤ theta1 * tau1 * eta)
    (hprox : (1 / 2 : ℝ) * S.stackedNormSq dx ≤ prox)
    (hg : S.stackedNormSq g ≤ S.networkOperatorNorm ^ 2 * S.stackedNormSq dx)
    (hretained :
      theta * eta * prox + (theta1 * tau1 / 2) * S.stackedNormSq v ≤
        theta * stackedInner g v + R) :
    let coeff : ℝ := (theta / 2) *
      (1 - theta * S.networkOperatorNorm ^ 2 / (eta * tau))
    coeff * (eta * S.stackedNormSq dx) ≤ R ∧
      coeff * (tau * S.stackedNormSq v) ≤ R := by
  classical
  intro coeff
  have htau_nonneg : 0 ≤ tau := le_of_lt htau_pos
  have heta_nonneg : 0 ≤ eta := le_of_lt heta_pos
  have hB_nonneg : 0 ≤ theta1 * tau1 / 2 := by
    rw [← htheta_tau]
    positivity
  have hdx_nonneg : 0 ≤ S.stackedNormSq dx := S.stackedNormSq_nonneg dx
  have hv_nonneg : 0 ≤ S.stackedNormSq v := S.stackedNormSq_nonneg v
  have hK_nonneg : 0 ≤ S.networkOperatorNorm ^ 2 := sq_nonneg _
  have hcoeff_eta_expand :
      coeff * eta =
        theta * eta / 2 -
          (theta ^ 2 * S.networkOperatorNorm ^ 2) / (2 * tau) := by
    dsimp [coeff]
    field_simp [heta_pos.ne', htau_pos.ne']
  have hcoeff_tau_expand :
      coeff * tau =
        theta * tau / 2 -
          (theta ^ 2 * S.networkOperatorNorm ^ 2) / (2 * eta) := by
    dsimp [coeff]
    field_simp [heta_pos.ne', htau_pos.ne']
  have hA_primal_nonneg :
      0 ≤ (theta ^ 2 * S.networkOperatorNorm ^ 2) / (2 * tau) := by
    positivity
  have hA_dual_nonneg :
      0 ≤ (theta ^ 2 * S.networkOperatorNorm ^ 2) / (2 * eta) := by
    positivity
  have hYoungPrimal :
      theta * stackedInner g v ≤
        ((theta ^ 2 * S.networkOperatorNorm ^ 2) / (2 * tau)) *
            S.stackedNormSq dx +
          (theta1 * tau1 / 2) * S.stackedNormSq v := by
    have hcoef :
        theta ^ 2 * S.networkOperatorNorm ^ 2 ≤
          4 * ((theta ^ 2 * S.networkOperatorNorm ^ 2) / (2 * tau)) *
            (theta1 * tau1 / 2) := by
      rw [← htheta_tau]
      field_simp [htau_pos.ne']
      nlinarith [
        mul_nonneg (sub_nonneg.mpr htheta_ge_one)
          (mul_nonneg (sq_nonneg theta) hK_nonneg)]
    exact
      stacked_inner_young_absorption_of_sq_bound_nonneg S
        (A := (theta ^ 2 * S.networkOperatorNorm ^ 2) / (2 * tau))
        (B := theta1 * tau1 / 2)
        (c := theta) (K := S.networkOperatorNorm ^ 2)
        (q := S.stackedNormSq dx) (g := g) (v := v)
        hA_primal_nonneg hB_nonneg htheta hK_nonneg hdx_nonneg hcoef hg
  have hYoungDual :
      theta * stackedInner g v ≤
        (theta * eta / 2) * S.stackedNormSq dx +
          ((theta ^ 2 * S.networkOperatorNorm ^ 2) / (2 * eta)) *
            S.stackedNormSq v := by
    have hcoef :
        theta ^ 2 * S.networkOperatorNorm ^ 2 ≤
          4 * (theta * eta / 2) *
            ((theta ^ 2 * S.networkOperatorNorm ^ 2) / (2 * eta)) := by
      field_simp [heta_pos.ne']
      nlinarith [
        mul_nonneg (sub_nonneg.mpr htheta_ge_one)
          (mul_nonneg (sq_nonneg theta) hK_nonneg)]
    have hA : 0 ≤ theta * eta / 2 := by positivity
    exact
      stacked_inner_young_absorption_of_sq_bound_nonneg S
        (A := theta * eta / 2)
        (B := (theta ^ 2 * S.networkOperatorNorm ^ 2) / (2 * eta))
        (c := theta) (K := S.networkOperatorNorm ^ 2)
        (q := S.stackedNormSq dx) (g := g) (v := v)
        hA hA_dual_nonneg htheta hK_nonneg hdx_nonneg hcoef hg
  have hprox_scaled :
      (theta * eta / 2) * S.stackedNormSq dx ≤ theta * eta * prox := by
    have hscale : 0 ≤ theta * eta := mul_nonneg htheta heta_nonneg
    have h := mul_le_mul_of_nonneg_left hprox hscale
    nlinarith
  constructor
  · calc
      coeff * (eta * S.stackedNormSq dx)
          = (theta * eta / 2) * S.stackedNormSq dx -
              ((theta ^ 2 * S.networkOperatorNorm ^ 2) / (2 * tau)) *
                S.stackedNormSq dx := by
              calc
                coeff * (eta * S.stackedNormSq dx) =
                    (coeff * eta) * S.stackedNormSq dx := by ring
                _ = (theta * eta / 2 -
                      theta ^ 2 * S.networkOperatorNorm ^ 2 / (2 * tau)) *
                    S.stackedNormSq dx := by rw [hcoeff_eta_expand]
                _ = (theta * eta / 2) * S.stackedNormSq dx -
                    (theta ^ 2 * S.networkOperatorNorm ^ 2 / (2 * tau)) *
                      S.stackedNormSq dx := by ring
      _ ≤ theta * eta * prox +
            (theta1 * tau1 / 2) * S.stackedNormSq v -
            theta * stackedInner g v := by
              linarith [hprox_scaled, hYoungPrimal]
      _ ≤ R := by
              linarith
  · calc
      coeff * (tau * S.stackedNormSq v)
          = (theta * tau / 2) * S.stackedNormSq v -
              ((theta ^ 2 * S.networkOperatorNorm ^ 2) / (2 * eta)) *
                S.stackedNormSq v := by
              calc
                coeff * (tau * S.stackedNormSq v) =
                    (coeff * tau) * S.stackedNormSq v := by ring
                _ = (theta * tau / 2 -
                      theta ^ 2 * S.networkOperatorNorm ^ 2 / (2 * eta)) *
                    S.stackedNormSq v := by rw [hcoeff_tau_expand]
                _ = (theta * tau / 2) * S.stackedNormSq v -
                    (theta ^ 2 * S.networkOperatorNorm ^ 2 / (2 * eta)) *
                      S.stackedNormSq v := by ring
      _ = (theta1 * tau1 / 2) * S.stackedNormSq v -
              ((theta ^ 2 * S.networkOperatorNorm ^ 2) / (2 * eta)) *
                S.stackedNormSq v := by
              rw [← htheta_tau]
      _ ≤ theta * eta * prox +
            (theta1 * tau1 / 2) * S.stackedNormSq v -
            theta * stackedInner g v := by
              linarith [hprox_scaled, hYoungDual]
      _ ≤ R := by
              linarith

/-- Degenerate-safe residual branch extraction from the retained terminal
inequality in Lemma 8.5.

This is the same scalar step as
`sdcs_residual_branches_of_retained_terminal_bound`, but it accepts the
source-facing nonnegativity hypothesis on `tau`.  If `tau = 0`, the parameter
condition forces the network residual budget to vanish, so the retained
terminal inequality directly bounds the primal branch while the dual branch is
zero. -/
private theorem sdcs_residual_branches_of_retained_terminal_bound_nonneg_tau
    (S : Setup ι E Ξ) {theta eta tau theta1 tau1 R prox : ℝ}
    {dx g v : Stacked ι E}
    (htheta : 0 ≤ theta) (heta_pos : 0 < eta) (htau : 0 ≤ tau)
    (htheta_ge_one : 1 ≤ theta)
    (htheta_tau : theta * tau = theta1 * tau1)
    (hcond : theta * S.networkOperatorNorm ^ 2 ≤ theta1 * tau1 * eta)
    (hprox : (1 / 2 : ℝ) * S.stackedNormSq dx ≤ prox)
    (hg : S.stackedNormSq g ≤ S.networkOperatorNorm ^ 2 * S.stackedNormSq dx)
    (hretained :
      theta * eta * prox + (theta1 * tau1 / 2) * S.stackedNormSq v ≤
        theta * stackedInner g v + R) :
    let coeff : ℝ := (theta / 2) *
      (1 - theta * S.networkOperatorNorm ^ 2 / (eta * tau))
    coeff * (eta * S.stackedNormSq dx) ≤ R ∧
      coeff * (tau * S.stackedNormSq v) ≤ R := by
  simpa only [stackedNorm_sq_eq S] using
    (residual_branches_of_retained_quadratic_bound_nonneg
      (theta := theta) (eta := eta) (tau := tau) (weight := theta1 * tau1)
      (K := S.networkOperatorNorm ^ 2) (R := R) (energy := prox)
      (dx := WithLp.toLp 2 dx) (g := WithLp.toLp 2 g) (v := WithLp.toLp 2 v)
      heta_pos htau htheta_ge_one htheta_tau (sq_nonneg _)
      (by
        intro htau_zero
        have htheta_pos : 0 < theta := lt_of_lt_of_le zero_lt_one htheta_ge_one
        have hweight_zero : theta1 * tau1 = 0 := by
          rw [← htheta_tau, htau_zero, mul_zero]
        have hupper : theta * S.networkOperatorNorm ^ 2 ≤ 0 := by
          simpa [hweight_zero] using hcond
        nlinarith [sq_nonneg S.networkOperatorNorm])
      (by simpa only [stackedNorm_sq_eq S] using hprox)
      (by simpa only [stackedNorm_sq_eq S] using hg)
      (by simpa only [stackedInner, SOptLib.dependentProductInner_eq_piLp_inner,
        stackedNorm_sq_eq S] using hretained))

/-- If both branches are bounded after multiplication by the same scalar, then
the multiplied maximum is bounded.  This avoids any sign assumption on the
scalar by splitting on which branch realizes the maximum. -/
private theorem mul_max_le_of_mul_le_left_right {a x y C : ℝ}
    (hx : a * x ≤ C) (hy : a * y ≤ C) :
    a * max x y ≤ C := by
  by_cases hxy : x ≤ y
  · rw [max_eq_right hxy]
    exact hy
  · have hyx : y ≤ x := le_of_lt (lt_of_not_ge hxy)
    rw [max_eq_left hyx]
    exact hx

/-- Scalar dual-drop telescope used in Lemma 8.5 step (d).

The first dual-step square is nonpositive in the source display and can be
dropped; the remaining tail squares are kept so that the lagged Young budgets
cancel them. -/
private theorem sdcs_dual_drop_sum_le_endpoint_sub_tail
    (theta tau D E : ℕ → ℝ) (N : ℕ) (hN : 1 ≤ N)
    (hc_nonneg : 0 ≤ theta 1 * tau 1)
    (hcoeff : ∀ t, 2 ≤ t → t ≤ N → theta t * tau t = theta 1 * tau 1)
    (hE_nonneg : ∀ t, 1 ≤ t → t ≤ N → 0 ≤ E t) :
    (∑ k ∈ Finset.range N,
      theta (k + 1) * (tau (k + 1) / 2) *
        (D k - D (k + 1) - E (k + 1))) ≤
      (theta 1 * tau 1 / 2) * (D 0 - D N) -
        ∑ t ∈ Finset.Icc 2 N, theta t * (tau t / 2) * E t := by
  exact sum_range_constant_weight_drop_sub_le_endpoint_sub_Icc_tail
    theta tau D E N hN hc_nonneg hcoeff (hE_nonneg 1 (by norm_num) hN)

/-- The primal-dual gap expression `Q(z; zbar)` from (8.3.8).

Source: `book/research/Source.json setup.saddle_point_problem`: `min_x {F(x)+
max_y <\mathcal{L}x,y>}`; `main_theorem.proof[2]` references the perturbed gap
definition and Lemma 8.5 conversion through `Q`.
-/
def primalDualGap (x : Stacked ι E) (y : Stacked ι E)
    (xbar : Stacked ι E) (ybar : Stacked ι E) : ℝ :=
  S.objective x + stackedInner (S.networkOperator x) ybar -
    (S.objective xbar + stackedInner (S.networkOperator xbar) y)

/-- The real support set underlying the full-space perturbed gap `g(s,z)`.

The source definition is an extended-valued supremum over the whole dual space
`Y = R^{md}`.  Keeping the support set explicit lets Proposition 8.6 state the
missing finiteness boundary instead of relying on Lean's real `sSup` fallback
for unbounded sets.

Source: `book/research/Source.json#/key_lemmas/0/statement_math`:
`g_Y(s,z):=sup_{\bar y \in Y} Q(z;x^*,\bar y)-<s,\bar y>`.
-/
def perturbedGapSupport (x : Stacked ι E) (y : Stacked ι E)
    (xStar : Stacked ι E) (s : Stacked ι E) : Set ℝ :=
  { q : ℝ | ∃ ybar : Stacked ι E,
    q = S.primalDualGap x y xStar ybar - stackedInner s ybar }

/-- Source finiteness predicate for the full-space perturbed gap.

Proposition 8.6 uses the fact that `g(s,z) < ∞`; in Lean this must be recorded
separately from the real-valued `sSup`, whose unbounded fallback is not the
paper's extended-valued `∞`.
-/
def PerturbedGapFinite (x : Stacked ι E) (y : Stacked ι E)
    (xStar : Stacked ι E) (s : Stacked ι E) : Prop :=
  BddAbove (S.perturbedGapSupport x y xStar s)

/-- The real value of the perturbed gap when the full-space support is finite.

Consumers that use Proposition 8.6 must also carry `PerturbedGapFinite`; this
definition alone deliberately does not encode the source's `∞` case.
-/
def perturbedGap (x : Stacked ι E) (y : Stacked ι E)
    (xStar : Stacked ι E) (s : Stacked ι E) : ℝ :=
  sSup (S.perturbedGapSupport x y xStar s)

/-- The objective residual of Definition 8.1 / (8.3.11).

Source: `book/research/Source.json key_lemmas[EpsilonDeltaSolutionDefinition]`:
`F(x)-F(x^*) <= epsilon`. -/
def objectiveResidual (x xStar : Stacked ι E) : ℝ :=
  S.objective x - S.objective xStar

/-- The consensus residual `‖L x‖` of Definition 8.1 / (8.3.11).

Source: `book/research/Source.json key_lemmas[EpsilonDeltaSolutionDefinition]`:
`||mathcal{L}x|| <= delta`. -/
def consensusResidual (x : Stacked ι E) : ℝ :=
  (fun x => ‖WithLp.toLp 2 x‖) (S.networkOperator x)

/-- Product feasibility `x ∈ X_1 × ... × X_m`.

Source: `book/research/Source.json setup.variable_space`: `x=(x_1,\ldots,x_m)\in
X_1\times\cdots\times X_m`. -/
def FeasiblePoint (x : Stacked ι E) : Prop :=
  ∀ i, x i ∈ S.feasible i

/-- Primal optimal solution of the network-constrained problem (8.3.6).

Source: `book/research/Source.json assumptions[SaddlePointExistence]`: `there
exists an optimal solution x^*\in X of (8.3.6)`. -/
def PrimalOptimalSolution (xStar : Stacked ι E) : Prop :=
  S.FeasiblePoint xStar ∧ S.networkOperator xStar = 0 ∧
    ∀ x, S.FeasiblePoint x → S.networkOperator x = 0 →
      S.objective xStar ≤ S.objective x

/-- Saddle point predicate for (8.3.7).

Source: `book/research/Source.json setup.saddle_point_problem`: `min_x {F(x)+
max_y <\mathcal{L}x,y>}` and assumptions[SaddlePointExistence]: `(x^*,y^*) is a
saddle point of (8.3.7)`. -/
def SaddlePoint (xStar yStar : Stacked ι E) : Prop :=
  S.PrimalOptimalSolution xStar ∧
    ∀ x y, S.FeasiblePoint x →
      S.primalDualGap xStar yStar x y ≤ 0 ∧
        0 ≤ S.primalDualGap x y xStar yStar

/-- Dual optimal solution paired with the selected source optimal point.

Source: `book/research/Source.json main_theorem.statement_math`: `y^* is an
arbitrary dual optimal solution`. -/
def DualOptimalSolution (xStar yStar : Stacked ι E) : Prop :=
  S.SaddlePoint xStar yStar

private theorem primalDualGap_to_objectiveResidual_add_network_pairing
    (x yHat xStar y : Stacked ι E)
    (hxStar : S.PrimalOptimalSolution xStar) :
    S.primalDualGap x yHat xStar y =
      S.objectiveResidual x xStar + stackedInner (S.networkOperator x) y := by
  simpa [primalDualGap, objectiveResidual, stackedInner,
    SOptLib.dependentProductInner_eq_piLp_inner] using
      (SOptLib.saddleGap_linearCoupled_eq_objectiveGap_add_pairing_of_reference_eq_zero
        S.objective (fun z => WithLp.toLp 2 (S.networkOperator z))
        (fun z => WithLp.toLp 2 z) x xStar yHat y (by simp [hxStar.2.1]))

/-- Proposition 8.6 full-space consequence, stated as a source bridge.

For `Y = R^{md}`, the source proof expands the perturbed gap as
`F(x)-F(x*) + sup_y <-y, Lx-s>`.  Finiteness of that full-space supremum forces
`s = Lx`, and then the finite perturbed gap equals the objective residual.  The
separate `PerturbedGapFinite` premise is the Lean replacement for the source's
extended-valued condition `g(s,z) < ∞`; it prevents the real `sSup` fallback from
standing in for `∞`.

Source: `source/FOML_complete.txt` lines 31859-31870 and
`book/research/Source.json#/main_theorem/proof/15-18`.
-/
structure PerturbedGapToResidualsProposition86Bridge
    (x y xStar s : Stacked ι E) : Prop where
  scaled_eq_network : s = S.networkOperator x
  perturbedGap_eq_objectiveResidual :
    S.perturbedGap x y xStar s = S.objectiveResidual x xStar
  objectiveResidual_le_of_perturbedGap_le :
    ∀ ε : ℝ, S.perturbedGap x y xStar s ≤ ε →
      S.objectiveResidual x xStar ≤ ε
  consensusResidual_eq :
    S.consensusResidual x = (fun x => ‖WithLp.toLp 2 x‖) s

/-- Proposition 8.6 for the full dual space, with the finiteness condition made
explicit.

This is a shared source-boundary theorem for the Theorem 8.11 objective and
consensus routes.  It must not be replaced by an endpoint-local wrapper: both
routes consume the same bridge so the source's finite-gap identification
`s = Lx` remains visible.
-/
theorem perturbedGap_fullSpace_to_residuals_sourceBoundaryCorrected
    (x y xStar s : Stacked ι E)
    (hxStar : S.PrimalOptimalSolution xStar)
    (hfinite : S.PerturbedGapFinite x y xStar s) :
    S.PerturbedGapToResidualsProposition86Bridge x y xStar s := by
  classical
  let d : WithLp 2 (Stacked ι E) :=
    WithLp.toLp 2 (S.networkOperator x - s)
  have hsupport_affine :
      S.perturbedGapSupport x y xStar s =
        {q : ℝ | ∃ ybar : WithLp 2 (Stacked ι E),
          q = S.objectiveResidual x xStar + inner ℝ d ybar} := by
    ext q
    constructor
    · intro hq
      rcases hq with ⟨ybar, hq_eq⟩
      have hgap := primalDualGap_to_objectiveResidual_add_network_pairing
        (S := S) x y xStar ybar hxStar
      refine ⟨WithLp.toLp 2 ybar, ?_⟩
      calc
        q = S.primalDualGap x y xStar ybar - stackedInner s ybar := hq_eq
        _ = S.objectiveResidual x xStar +
            stackedInner (S.networkOperator x - s) ybar := by
          rw [hgap]
          dsimp [stackedInner]
          simp [inner_sub_left, Finset.sum_sub_distrib]
          ring
        _ = S.objectiveResidual x xStar +
            inner ℝ d (WithLp.toLp 2 ybar) := by
          dsimp [d, stackedInner]
          rw [SOptLib.dependentProductInner_eq_piLp_inner]
          simp
    · intro hq
      rcases hq with ⟨ybar, hq_eq⟩
      refine ⟨WithLp.ofLp ybar, ?_⟩
      have hgap := primalDualGap_to_objectiveResidual_add_network_pairing
        (S := S) x y xStar (WithLp.ofLp ybar) hxStar
      calc
        q = S.objectiveResidual x xStar + inner ℝ d ybar := hq_eq
        _ = S.objectiveResidual x xStar +
            stackedInner (S.networkOperator x - s) (WithLp.ofLp ybar) := by
          dsimp [d, stackedInner]
          rw [SOptLib.dependentProductInner_eq_piLp_inner]
          simp
        _ = S.primalDualGap x y xStar (WithLp.ofLp ybar) -
            stackedInner s (WithLp.ofLp ybar) := by
          rw [hgap]
          dsimp [stackedInner]
          simp [inner_sub_left, Finset.sum_sub_distrib]
          ring
  have h_bdd_affine :
      BddAbove {q : ℝ | ∃ ybar : WithLp 2 (Stacked ι E),
        q = S.objectiveResidual x xStar + inner ℝ d ybar} := by
    rw [← hsupport_affine]
    exact hfinite
  have hd_and_sup :=
    eq_zero_and_sSup_affine_inner_support_eq_of_bddAbove
      (S.objectiveResidual x xStar) d h_bdd_affine
  have hs : s = S.networkOperator x := by
    have hdiff : S.networkOperator x - s = 0 := by
      have hdiff_lp := congrArg WithLp.ofLp hd_and_sup.1
      simpa [d] using hdiff_lp
    exact (sub_eq_zero.mp hdiff).symm
  have hgap_eq :
      S.perturbedGap x y xStar s = S.objectiveResidual x xStar := by
    rw [perturbedGap, hsupport_affine]
    exact hd_and_sup.2
  refine ⟨hs, hgap_eq, ?_, ?_⟩
  · intro ε hε
    simpa [hgap_eq] using hε
  · rw [consensusResidual, hs]

/-- Source assumption that a primal-dual saddle point exists, now tied to the
paper-level optimality predicates instead of an opaque `Prop`.

Source: `book/research/Source.json assumptions[SaddlePointExistence]`: `there
exists an optimal solution x^* ... and there exists y^* ... such that (x^*,y^*) is
a saddle point of (8.3.7)`. -/
theorem saddlePointExists : ∃ xStar yStar, S.SaddlePoint xStar yStar := by
  simpa [SaddlePoint, PrimalOptimalSolution, FeasiblePoint, primalDualGap, objective]
    using S.saddlePointExistsSource

theorem stackedProx_lower_bound (x u : Stacked ι E)
    (hx : ∀ i, x i ∈ S.feasible i) (hu : ∀ i, u i ∈ S.feasible i) :
    (1 / 2 : ℝ) * S.stackedNormSq (x - u) ≤ S.stackedProx x u := by
  simpa [stackedNormSq, stackedProx] using
    (SOptLib.half_dependentProductNormSq_le_blockBregmanSum_of_pointwise
      (ι := ι) (Block := fun _ => E) S.localProx x u fun i =>
        S.proxStrongConvexity i (x i) (u i) (by simp) (hx i) (hu i))

/-- Parameter families used by Algorithms 8.7/8.8.  The Theorem 8.11 schedule is
computed by `theorem811Parameters` once its printed denominator boundary is supplied. -/
structure Parameters where
  alpha : ℕ → ℝ
  theta : ℕ → ℝ
  eta : ℕ → ℝ
  tau : ℕ → ℝ
  innerSteps : ℕ → ℕ

/-- Source-facing nonnegative parameter domain for Algorithms 8.7/8.8.

Source: `book/research/Source.json algorithm_spec.initialization`: `the
nonnegative parameters {alpha_k}, {tau_k}, {eta_k}, and {T_k} be given`.  The
inner-loop counts are encoded as natural numbers, so their nonnegativity is
intrinsic to `innerSteps`.
-/
def ValidParameters (P : Parameters) : Prop :=
  (∀ k, 0 ≤ P.alpha k) ∧ (∀ k, 0 ≤ P.tau k) ∧ (∀ k, 0 ≤ P.eta k)

theorem ValidParameters.alpha_nonneg {P : Parameters} (hP : ValidParameters P) (k : ℕ) :
    0 ≤ P.alpha k :=
  hP.1 k

theorem ValidParameters.tau_nonneg {P : Parameters} (hP : ValidParameters P) (k : ℕ) :
    0 ≤ P.tau k :=
  hP.2.1 k

theorem ValidParameters.eta_nonneg {P : Parameters} (hP : ValidParameters P) (k : ℕ) :
    0 ≤ P.eta k :=
  hP.2.2 k

/-- The CS weights (8.3.34): `λ_t = t + 1`. -/
def csLambda (t : ℕ) : ℝ :=
  (t : ℝ) + 1

/-- The CS weights (8.3.34), verified on printed p. 542: `β_t = t/2`. -/
def csBeta (t : ℕ) : ℝ :=
  (t : ℝ) / 2

/-- The denominator `∑_{t=1}^T λ_t` in the CS weighted average. -/
def csLambdaSum (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.range T, csLambda (t + 1)

private theorem weighted_average_sub_target_eq_average_residual
    {κ V : Type _} [AddCommGroup V] [Module ℝ V]
    (s : Finset κ) (γ : κ → ℝ) (W : ℝ) (hW : W = ∑ i ∈ s, γ i)
    (hW_ne : W ≠ 0) (p : κ → V) (z : V) :
    W⁻¹ • (∑ i ∈ s, γ i • p i) - z =
      W⁻¹ • (∑ i ∈ s, γ i • (p i - z)) := by
  exact inv_smul_weighted_sum_sub_eq_inv_smul_sum_weighted_sub
    s γ W hW hW_ne p z

/-- Explicit source-boundary correction for the printed Theorem 8.11 schedule.

The source states `Dtilde > 0` but does not explicitly state `0 < ‖L‖`; without
that fact the denominator in (8.3.67) is not mathematically defined, although Lean
totalizes division.  The corrected endpoint below carries this boundary openly
rather than presenting totalized division as the paper theorem.  The norm here is
the source stacked-norm induced operator norm, not Lean's default Pi operator norm.
-/
def Theorem811ScheduleWellDefined (_N : ℕ) (Dtilde : ℝ) : Prop :=
  0 < Dtilde ∧ 0 < S.networkOperatorNorm

/-- Internal raw quotient for the printed `T_k` expression.

This helper is intentionally not the paper-facing schedule object: it is evaluated
only through the guarded `theorem811InnerSteps`, so Lean's total division cannot
silently stand for the source expression outside its denominator boundary.
-/
private def theorem811InnerStepsRaw (N : ℕ) (Dtilde : ℝ) : ℕ :=
  Nat.ceil ((Fintype.card ι : ℝ) * (S.M ^ 2 + S.sigma ^ 2) * (N : ℝ) /
    (S.networkOperatorNorm ^ 2 * Dtilde))

/-- The guarded inner-loop count expression printed in Theorem 8.11 / (8.3.67).

Source: `book/research/Source.json algorithm_spec.parameters.theorem_811_schedule`:
`T_k=ceil(m(M^2+sigma^2)N/(||L||^2 Dtilde))`.
-/
def theorem811InnerSteps (N : ℕ) (Dtilde : ℝ)
    (_hSchedule : S.Theorem811ScheduleWellDefined N Dtilde) : ℕ :=
  S.theorem811InnerStepsRaw N Dtilde

/-- The constant schedule of Theorem 8.11 / (8.3.67), available only with the
well-definedness boundary needed by the printed denominator.

Source: `book/research/Source.json algorithm_spec.parameters.theorem_811_schedule`:
`alpha_k=theta_k=1`, `eta_k=2||L||`, `tau_k=||L||`, and
`T_k=ceil(m(M^2+sigma^2)N/(||L||^2 Dtilde))`.
-/
def theorem811Parameters (N : ℕ) (Dtilde : ℝ)
    (_hSchedule : S.Theorem811ScheduleWellDefined N Dtilde) : Parameters where
  alpha := fun _ => 1
  theta := fun _ => 1
  eta := fun _ => 2 * S.networkOperatorNorm
  tau := fun _ => S.networkOperatorNorm
  innerSteps := fun _ => S.theorem811InnerSteps N Dtilde _hSchedule

theorem theorem811Parameters_valid (N : ℕ) (Dtilde : ℝ)
    (hSchedule : S.Theorem811ScheduleWellDefined N Dtilde) :
    ValidParameters (S.theorem811Parameters N Dtilde hSchedule) := by
  refine ⟨?_, ?_, ?_⟩
  · intro k
    dsimp [theorem811Parameters]
    norm_num
  · intro k
    exact le_of_lt hSchedule.2
  · intro k
    dsimp [theorem811Parameters]
    exact mul_nonneg (by norm_num) (le_of_lt hSchedule.2)

/-- Initial data `x_i^0 = x_i^{-1} = xhat_i^0 ∈ X_i`, `y_i^0`.

Source: `book/research/Source.json algorithm_spec.initialization`: `Let
x_i^0=x_i^{-1}=\hat{x}_i^0\in X_i, y_i^0\in\mathbb{R}^d`. -/
structure InitialState (S : Setup ι E Ξ) where
  x0 : Stacked ι E
  y0 : Stacked ι E
  x0_mem : S.FeasiblePoint x0

/-- Outer loop state just before the next iteration.  The current primal iterate
keeps its feasibility proof so the next stochastic CS argmin is never fed by an
unjustified fallback value.
-/
structure OuterState (S : Setup ι E Ξ) where
  xPrev : Stacked ι E
  xLag : Stacked ι E
  xHatPrev : Stacked ι E
  yPrev : Stacked ι E
  xPrev_mem : S.FeasiblePoint xPrev

/-- The canonical initial outer state from Algorithm 8.8 initialization. -/
def initialOuterState (init : InitialState S) : OuterState S where
  xPrev := init.x0
  xLag := init.x0
  xHatPrev := init.x0
  yPrev := init.y0
  xPrev_mem := init.x0_mem

/-- Outer extrapolation (8.3.17)/(8.3.20). -/
def outerExtrapolation (P : Parameters) (k : ℕ) (st : OuterState S) :
    Stacked ι E :=
  P.alpha k • (st.xHatPrev - st.xLag) + st.xPrev

/-- Primal neighbor disagreement `v_i^k`, encoded by the lifted operator (8.3.21). -/
def primalNeighborDisagreement (xTilde : Stacked ι E) : Stacked ι E :=
  S.networkOperator xTilde

/-- Guarded closed form for the dual update `y^k = y^{k-1} + τ_k^{-1} v^k`.

The paper formula (8.3.22) contains `1 / τ_k`; the proof-facing value therefore
requires an explicit positive-`τ_k` bridge rather than using Lean's total inverse as
the source semantics at `τ_k = 0`.
-/
def dualUpdate (P : Parameters) (k : ℕ) (_hTau : 0 < P.tau k)
    (st : OuterState S) (xTilde : Stacked ι E) : Stacked ι E :=
  st.yPrev + (P.tau k)⁻¹ • S.primalNeighborDisagreement xTilde

/-- Relational dual update from (8.3.22).

This is the paper-facing outer-step object: it states the required positive denominator
and the printed closed form, without assigning a fallback meaning to `τ_k = 0`.
-/
def IsDualUpdate (P : Parameters) (k : ℕ)
    (st : OuterState S) (xTilde yNext : Stacked ι E) : Prop :=
  SOptLib.IsCheckedInverseScaleAddUpdate
    (P.tau k) st.yPrev (S.primalNeighborDisagreement xTilde) yNext

/-- Dual neighbor disagreement `w_i^k`, encoded by the lifted operator (8.3.23). -/
def dualNeighborDisagreement (y : Stacked ι E) : Stacked ι E :=
  S.networkOperator y

/-- The scalar objective minimized in the stochastic CS projection (8.3.64).

Source: `book/research/Source.json algorithm_spec.steps[7]`: `u_t=argmin_{u in U}
{<w+h_{t-1},u>+eta V(x,u)+eta beta_t V(u_{t-1},u)}`. -/
def stochasticCSProjectionObjective (i : ι) (w xCenter uPrev h : E) (eta beta : ℝ)
    (u : E) : ℝ :=
  SOptLib.twoBregmanProxObjective
    (fun z => inner ℝ (w + h) z) (S.localProx i)
    xCenter uPrev eta (eta * beta) u

/-- Relational semantics of the stochastic CS projection step (8.3.64).

This is the source-facing object: the paper states an `argmin`, while existence and
measurable selection are proof obligations rather than primitive Setup fields.
-/
def IsStochasticCSProjection (i : ι) (w xCenter uPrev h : E) (eta beta : ℝ)
    (u : E) : Prop :=
  u ∈ S.feasible i ∧
    IsMinOn (S.stochasticCSProjectionObjective i w xCenter uPrev h eta beta)
      (S.feasible i) u

/-- Nonnegativity of the CS weight `β_t=t/2`.

Source: `book/research/Source.json algorithm_spec.parameters.general_cs_weights`:
`beta_t=t/2`.
-/
theorem csBeta_nonneg (t : ℕ) : 0 ≤ csBeta t := by
  unfold csBeta
  exact div_nonneg (Nat.cast_nonneg t) (by norm_num)

private theorem csLambdaSum_eq (T : ℕ) :
    csLambdaSum T = (T : ℝ) * ((T : ℝ) + 3) / 2 := by
  induction T with
  | zero =>
      simp [csLambdaSum]
  | succ T ih =>
      unfold csLambdaSum at ih ⊢
      rw [Finset.sum_range_succ, ih]
      simp [csLambda]
      ring

private theorem csLambdaSum_pos_of_pos {T : ℕ} (hT : 0 < T) :
    0 < csLambdaSum T := by
  rw [csLambdaSum_eq]
  have hT_real : 0 < (T : ℝ) := by exact_mod_cast hT
  have hT3 : 0 < (T : ℝ) + 3 := by positivity
  positivity

private theorem cs_coeff_mul_weighted_const_eq {T : ℕ} (hT : 0 < T) (c : ℝ) :
    (2 / ((T : ℝ) * ((T : ℝ) + 3))) *
        (∑ t ∈ Finset.range T, csLambda (t + 1) * c) = c := by
  have hT_ne : (T : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hT)
  have hT3_ne : (T : ℝ) + 3 ≠ 0 := by positivity
  have hsum :
      (∑ t ∈ Finset.range T, csLambda (t + 1) * c) =
        (((T : ℝ) * ((T : ℝ) + 3)) / 2) * c := by
    rw [← Finset.sum_mul, ← csLambdaSum, csLambdaSum_eq]
  rw [hsum]
  field_simp [hT_ne, hT3_ne]

private theorem coeff_mul_weighted_time_agent_sum_comm
    (T : ℕ) (c : ℝ) (φ : ι → ℕ → ℝ) :
    c * (∑ t ∈ Finset.range T, csLambda (t + 1) * (∑ i, φ i t)) =
      ∑ i, c * (∑ t ∈ Finset.range T, csLambda (t + 1) * φ i t) := by
  classical
  calc
    c * (∑ t ∈ Finset.range T, csLambda (t + 1) * (∑ i, φ i t))
        = ∑ t ∈ Finset.range T, ∑ i, c * (csLambda (t + 1) * φ i t) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro t ht
          calc
            c * (csLambda (t + 1) * (∑ i, φ i t))
                = c * (∑ i, csLambda (t + 1) * φ i t) := by
                  rw [Finset.mul_sum]
            _ = ∑ i, c * (csLambda (t + 1) * φ i t) := by
                  rw [Finset.mul_sum]
    _ = ∑ i, ∑ t ∈ Finset.range T, c * (csLambda (t + 1) * φ i t) := by
          rw [Finset.sum_comm]
    _ = ∑ i, c * (∑ t ∈ Finset.range T, csLambda (t + 1) * φ i t) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [Finset.mul_sum]

private theorem cs_coeff_agent_weighted_three_term_decomp {T : ℕ} (hT : 0 < T)
    (C : ι → ℝ) (B O : ι → ℕ → ℝ) :
    let coeff := 2 / ((T : ℝ) * ((T : ℝ) + 3))
    (∑ i,
      coeff * (∑ t ∈ Finset.range T, csLambda (t + 1) * (C i + B i t + O i t))) =
      (∑ i, C i) +
        (∑ i, coeff * (∑ t ∈ Finset.range T, csLambda (t + 1) * B i t)) +
          (∑ i, coeff * (∑ t ∈ Finset.range T, csLambda (t + 1) * O i t)) := by
  classical
  intro coeff
  calc
    (∑ i,
      coeff * (∑ t ∈ Finset.range T, csLambda (t + 1) * (C i + B i t + O i t))) =
        ∑ i,
          (coeff * (∑ t ∈ Finset.range T, csLambda (t + 1) * C i) +
            coeff * (∑ t ∈ Finset.range T, csLambda (t + 1) * B i t) +
              coeff * (∑ t ∈ Finset.range T, csLambda (t + 1) * O i t)) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          simp [mul_add, Finset.sum_add_distrib, add_assoc]
    _ =
        ∑ i,
          (C i +
            coeff * (∑ t ∈ Finset.range T, csLambda (t + 1) * B i t) +
              coeff * (∑ t ∈ Finset.range T, csLambda (t + 1) * O i t)) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          rw [cs_coeff_mul_weighted_const_eq hT]
    _ =
      (∑ i, C i) +
        (∑ i, coeff * (∑ t ∈ Finset.range T, csLambda (t + 1) * B i t)) +
          (∑ i, coeff * (∑ t ∈ Finset.range T, csLambda (t + 1) * O i t)) := by
          simp [Finset.sum_add_distrib, add_assoc]

private theorem cs_weighted_oracle_square_budget_pointwise_le
    {eta M d : ℝ} (t : ℕ)
    (hEta : 0 < eta) (_hM : 0 ≤ M) (_hd : 0 ≤ d) :
    csLambda (t + 1) * ((M + d) ^ 2 / (2 * (eta * csBeta (t + 1)))) ≤
      4 * (M ^ 2 + d ^ 2) / eta := by
  convert add_one_mul_add_sq_div_mul_le_four_mul_sq_add_sq_div_of_one_le
    ((t + 1 : ℕ) : ℝ) eta M d hEta (by exact_mod_cast Nat.succ_pos t) using 1 <;>
    simp [csLambda, csBeta] <;> ring

private theorem cs_weighted_oracle_square_budget_sum_le
    {eta M d : ℝ} (T : ℕ)
    (hEta : 0 < eta) (hM : 0 ≤ M) (hd : 0 ≤ d) :
    (∑ t ∈ Finset.range T,
      csLambda (t + 1) * ((M + d) ^ 2 / (2 * (eta * csBeta (t + 1)))) ) ≤
      ∑ t ∈ Finset.range T, 4 * (M ^ 2 + d ^ 2) / eta := by
  exact Finset.sum_le_sum (fun t _ht =>
    cs_weighted_oracle_square_budget_pointwise_le t hEta hM hd)

private theorem cs_weighted_bregman_raw_terminal_coeff_source_le
    {eta : ℝ} {T : ℕ} (hEta : 0 ≤ eta) (hT : 0 < T) (V : ℕ → ℝ)
    (hV : ∀ n, 0 ≤ V n) :
    let coeff := 2 / ((T : ℝ) * ((T : ℝ) + 3))
    coeff *
        (∑ t ∈ Finset.range T, csLambda (t + 1) *
          ((eta * csBeta (t + 1)) * V t -
            (eta + eta * csBeta (t + 1)) * V (t + 1))) ≤
      (2 * eta / ((T : ℝ) * ((T : ℝ) + 3))) * V 0 -
        ((((T : ℝ) + 1) * ((T : ℝ) + 2) * eta) /
          ((T : ℝ) * ((T : ℝ) + 3))) * V T := by
  intro coeff
  have hT_one : 1 ≤ T := hT
  have hunscaled :
      (∑ t ∈ Finset.range T, csLambda (t + 1) *
        ((eta * csBeta (t + 1)) * V t -
          (eta + eta * csBeta (t + 1)) * V (t + 1))) ≤
        eta * V 0 - ((((T : ℝ) + 1) * ((T : ℝ) + 2) * eta) / 2) * V T := by
    let c : ℕ → ℝ := fun r => eta * (r : ℝ) * ((r : ℝ) + 1) / 2
    let betaTail : ℕ → ℝ := fun r => ((r : ℝ) + 2) / (r : ℝ)
    have htel :=
      sum_weighted_sub_mul_le_first_sub_tail (c := c) (beta := betaTail) (V := V)
        T hT_one (fun n _ _ => hV n) ?_
    · have hsum_eq :
          (∑ t ∈ Finset.range T, csLambda (t + 1) *
            ((eta * csBeta (t + 1)) * V t -
              (eta + eta * csBeta (t + 1)) * V (t + 1))) =
            ∑ r ∈ Finset.Icc 1 T, c r * (V (r - 1) - betaTail r * V r) := by
        rw [sum_Icc_one_eq_sum_range_succ]
        refine Finset.sum_congr rfl ?_
        intro t _ht
        dsimp [c, betaTail, csLambda, csBeta]
        have hden : (t : ℝ) + 1 ≠ 0 := by positivity
        field_simp [hden]
        ring
      calc
        (∑ t ∈ Finset.range T, csLambda (t + 1) *
          ((eta * csBeta (t + 1)) * V t -
            (eta + eta * csBeta (t + 1)) * V (t + 1)))
            = ∑ r ∈ Finset.Icc 1 T, c r * (V (r - 1) - betaTail r * V r) := hsum_eq
        _ ≤ c 1 * V 0 - c T * betaTail T * V T := htel
        _ = eta * V 0 - ((((T : ℝ) + 1) * ((T : ℝ) + 2) * eta) / 2) * V T := by
              dsimp [c, betaTail]
              have hT_ne : (T : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hT)
              field_simp [hT_ne]
              ring
    · intro n hn_one _hn_lt
      dsimp [c, betaTail]
      have hn_pos : (0 : ℝ) < n := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn_one)
      have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
      field_simp [hn_ne]
      norm_num [Nat.cast_add, Nat.cast_one]
      nlinarith
  have hden_pos : 0 < (T : ℝ) * ((T : ℝ) + 3) := by
    have hT_real : 0 < (T : ℝ) := by exact_mod_cast hT
    positivity
  have hcoeff_nonneg : 0 ≤ coeff := by
    dsimp [coeff]
    positivity
  have hmul := mul_le_mul_of_nonneg_left hunscaled hcoeff_nonneg
  calc
    coeff *
        (∑ t ∈ Finset.range T, csLambda (t + 1) *
          ((eta * csBeta (t + 1)) * V t -
            (eta + eta * csBeta (t + 1)) * V (t + 1)))
      ≤ coeff * (eta * V 0 - ((((T : ℝ) + 1) * ((T : ℝ) + 2) * eta) / 2) * V T) := hmul
    _ = (2 * eta / ((T : ℝ) * ((T : ℝ) + 3))) * V 0 -
        ((((T : ℝ) + 1) * ((T : ℝ) + 2) * eta) /
          ((T : ℝ) * ((T : ℝ) + 3))) * V T := by
          dsimp [coeff]
          field_simp [ne_of_gt hden_pos]

/-- A feasible inner CS iterate packaged with its feasibility proof. -/
structure InnerState (i : ι) where
  u : E
  mem : u ∈ S.feasible i

/-- Relational trace of the stochastic CS inner loop from (8.3.63)-(8.3.64).

The paper states the next inner iterate by an `argmin`; the source does not provide
an all-input argmin existence theorem.  Therefore the generated inner loop is a
trace satisfying the printed relation, not a `Classical.choose` selector.
-/
structure InnerTrace (i : ι) (w xCenter : E) (eta : ℝ) (sample : ℕ → Ξ)
    (hxCenter : xCenter ∈ S.feasible i) where
  state : ℕ → InnerState S i
  initial_value : (state 0).u = xCenter
  step_spec : ∀ t,
    let uPrev := (state t).u
    let h := S.oracle i uPrev (sample t)
    S.IsStochasticCSProjection i w xCenter uPrev h eta (csBeta (t + 1))
      (state (t + 1)).u

/-- The actual inner CS iterate `u_t` from a relational generated trace. -/
def csIterate (i : ι) (w xCenter : E) (eta : ℝ) (sample : ℕ → Ξ)
    (hxCenter : xCenter ∈ S.feasible i)
    (trace : S.InnerTrace i w xCenter eta sample hxCenter) (t : ℕ) : E :=
  (trace.state t).u

theorem csIterate_mem (i : ι) (w xCenter : E) (eta : ℝ) (sample : ℕ → Ξ)
    (hxCenter : xCenter ∈ S.feasible i)
    (trace : S.InnerTrace i w xCenter eta sample hxCenter) (t : ℕ) :
    S.csIterate i w xCenter eta sample hxCenter trace t ∈ S.feasible i :=
  (trace.state t).mem

/-- The weighted inner average `û_T` from (8.3.27), over the actual generated inner
trace. -/
def csWeightedAverage (i : ι) (w xCenter : E) (eta : ℝ) (sample : ℕ → Ξ)
    (hxCenter : xCenter ∈ S.feasible i)
    (trace : S.InnerTrace i w xCenter eta sample hxCenter) (T : ℕ) : E :=
  (csLambdaSum T)⁻¹ •
    (∑ t ∈ Finset.range T, csLambda (t + 1) •
      S.csIterate i w xCenter eta sample hxCenter trace (t + 1))

private theorem csWeightedAverage_mem (i : ι) (w xCenter : E) (eta : ℝ)
    (sample : ℕ → Ξ) (hxCenter : xCenter ∈ S.feasible i)
    (trace : S.InnerTrace i w xCenter eta sample hxCenter) {T : ℕ} (hT : 0 < T) :
    S.csWeightedAverage i w xCenter eta sample hxCenter trace T ∈ S.feasible i := by
  classical
  unfold csWeightedAverage
  exact
    (S.feasible_convex i).normalized_weighted_sum_mem
      (s := Finset.range T) (w := fun t => csLambda (t + 1))
      (x := fun t => S.csIterate i w xCenter eta sample hxCenter trace (t + 1))
      (by simpa [csLambdaSum] using csLambdaSum_pos_of_pos hT)
      (by
        intro t _ht
        unfold csLambda
        positivity)
      (by
        intro t _ht
        exact S.csIterate_mem i w xCenter eta sample hxCenter trace (t + 1))

/-- Relational stochastic CS call returning `(x_i^k, xhat_i^k)` in Algorithm 8.8. -/
def IsStochasticCSCall (P : Parameters) (k : ℕ) (i : ι)
    (w xCenter : E) (hxCenter : xCenter ∈ S.feasible i) (sample : ℕ → Ξ)
    (trace : S.InnerTrace i w xCenter (P.eta k) sample hxCenter)
    (xOut xHatOut : E) : Prop :=
  xOut = S.csIterate i w xCenter (P.eta k) sample hxCenter trace (P.innerSteps k) ∧
    xHatOut =
      S.csWeightedAverage i w xCenter (P.eta k) sample hxCenter trace (P.innerSteps k)

/-- The guarded dual value that precedes the local CS calls in one outer iteration. -/
def outerStepDual (P : Parameters) (k : ℕ) (hTau : 0 < P.tau k)
    (st : OuterState S) : Stacked ι E :=
  S.dualUpdate P k hTau st (S.outerExtrapolation P k st)

/-- Relational outer SDCS update, combining (8.3.20)-(8.3.24) and
(8.3.63)-(8.3.64). -/
def IsOuterStep (P : Parameters) (samples : ℕ → ι → ℕ → Ξ) (k : ℕ)
    (st next : OuterState S)
    (inner : ∀ i,
      S.InnerTrace i ((S.dualNeighborDisagreement next.yPrev) i)
        (st.xPrev i) (P.eta k) (samples k i) (st.xPrev_mem i)) : Prop :=
  next.xLag = st.xPrev ∧
    S.IsDualUpdate P k st (S.outerExtrapolation P k st) next.yPrev ∧
    ∀ i,
      S.IsStochasticCSCall P k i ((S.dualNeighborDisagreement next.yPrev) i)
        (st.xPrev i) (st.xPrev_mem i) (samples k i) (inner i)
        (next.xPrev i) (next.xHatPrev i)

/-- The actual generated outer and inner traces of Algorithm 8.8 on the
source-facing nonnegative parameter domain.

Source: `book/research/Source.json algorithm_spec.initialization`: `the
nonnegative parameters {alpha_k}, {tau_k}, {eta_k}, and {T_k} be given`.
-/
structure GeneratedTrace (P : Parameters) (_hP : ValidParameters P) (init : InitialState S)
    (samples : ℕ → ι → ℕ → Ξ) where
  state : ℕ → OuterState S
  initial_state : state 0 = S.initialOuterState init
  inner : ∀ k i,
    S.InnerTrace i
      ((S.dualNeighborDisagreement ((state k).yPrev)) i)
      ((state (k - 1)).xPrev i) (P.eta k) (samples k i)
      ((state (k - 1)).xPrev_mem i)
  step_spec : ∀ k, 1 ≤ k →
    S.IsOuterStep P samples k (state (k - 1)) (state k) (inner k)

/-- The actual generated outer state `k` from a relational SDCS trace. -/
def generatedState (P : Parameters) (hP : ValidParameters P) (init : InitialState S)
    (samples : ℕ → ι → ℕ → Ξ)
    (trace : S.GeneratedTrace P hP init samples) (k : ℕ) : OuterState S :=
  trace.state k

/-- The actual generated primal iterate `x_k`. -/
def generatedX (P : Parameters) (hP : ValidParameters P) (init : InitialState S)
    (samples : ℕ → ι → ℕ → Ξ) (trace : S.GeneratedTrace P hP init samples)
    (k : ℕ) : Stacked ι E :=
  (S.generatedState P hP init samples trace k).xPrev

/-- The actual generated averaged local iterate `xhat_k`. -/
def generatedXHat (P : Parameters) (hP : ValidParameters P) (init : InitialState S)
    (samples : ℕ → ι → ℕ → Ξ) (trace : S.GeneratedTrace P hP init samples)
    (k : ℕ) : Stacked ι E :=
  (S.generatedState P hP init samples trace k).xHatPrev

/-- The actual generated dual iterate `y_k`. -/
def generatedY (P : Parameters) (hP : ValidParameters P) (init : InitialState S)
    (samples : ℕ → ι → ℕ → Ξ) (trace : S.GeneratedTrace P hP init samples)
    (k : ℕ) : Stacked ι E :=
  (S.generatedState P hP init samples trace k).yPrev

/-- The actual generated inner search point queried before the fresh stochastic sample
`ξ_i^{t,k}` is consumed.

Source: `book/research/Source.json algorithm_spec.steps[6]`: `h_{t-1}=H(u_{t-1},
ξ^{t-1})`; `assumptions[StochasticQueryIndependence]`: `ξ_it is independent of the
search point u_t`.
-/
def generatedInnerQuery (P : Parameters) (hP : ValidParameters P) (init : InitialState S)
    (samples : ℕ → ι → ℕ → Ξ) (trace : S.GeneratedTrace P hP init samples)
    (i : ι) (k t : ℕ) : E :=
  (trace.inner k i).state t |>.u

/-- The generated Algorithm 8.8 inner update satisfies the printed argmin relation
at the next inner iterate.  This is the paper-facing generated-call property replacing
the old fallback/existence-only encoding.

Source: `book/research/Source.json algorithm_spec.steps[6]`: `h_{t-1}=H(u_{t-1},
ξ^{t-1})`; `algorithm_spec.steps[7]`: `u_t=argmin_{u\in U}{<w+h_{t-1},u>+eta
V(x,u)+eta beta_t V(u_{t-1},u)}`.
-/
theorem generated_stochasticCSProjection_spec
    (P : Parameters) (hP : ValidParameters P) (init : InitialState S)
    (samples : ℕ → ι → ℕ → Ξ)
    (trace : S.GeneratedTrace P hP init samples)
    (i : ι) (k t : ℕ) :
    let centerState := S.generatedState P hP init samples trace (k - 1)
    let nextState := S.generatedState P hP init samples trace k
    let w := (S.dualNeighborDisagreement nextState.yPrev) i
    let xCenter := centerState.xPrev i
    let uPrev := S.generatedInnerQuery P hP init samples trace i k t
    let h := S.oracle i uPrev (samples k i t)
    S.IsStochasticCSProjection i w xCenter uPrev h (P.eta k) (csBeta (t + 1))
      (S.generatedInnerQuery P hP init samples trace i k (t + 1)) := by
  dsimp [generatedInnerQuery, generatedState]
  exact (trace.inner k i).step_spec t

/-- The generated Algorithm 8.8 outer dual value satisfies the guarded printed dual
update (8.3.22), rather than a totalized inverse fallback.
-/
theorem generated_dualUpdate_spec
    (P : Parameters) (hP : ValidParameters P) (init : InitialState S)
    (samples : ℕ → ι → ℕ → Ξ)
    (trace : S.GeneratedTrace P hP init samples)
    (k : ℕ) (hk : 1 ≤ k) :
    S.IsDualUpdate P k (S.generatedState P hP init samples trace (k - 1))
      (S.outerExtrapolation P k (S.generatedState P hP init samples trace (k - 1)))
      (S.generatedY P hP init samples trace k) := by
  dsimp [generatedState, generatedY]
  exact (trace.step_spec k hk).2.1

private theorem generated_x_eq_inner_terminal
    (P : Parameters) (hP : ValidParameters P) (init : InitialState S)
    (samples : ℕ → ι → ℕ → Ξ)
    (trace : S.GeneratedTrace P hP init samples)
    (k : ℕ) (hk : 1 ≤ k) (i : ι) :
    let centerState := S.generatedState P hP init samples trace (k - 1)
    let nextState := S.generatedState P hP init samples trace k
    S.generatedX P hP init samples trace k i =
      S.csIterate i ((S.dualNeighborDisagreement nextState.yPrev) i)
        (centerState.xPrev i) (P.eta k) (samples k i) (centerState.xPrev_mem i)
        (trace.inner k i) (P.innerSteps k) := by
  intro centerState nextState
  have hcall := (trace.step_spec k hk).2.2 i
  simpa [generatedX, generatedState, centerState, nextState, IsStochasticCSCall]
    using hcall.1

private theorem generated_xhat_eq_inner_weightedAverage
    (P : Parameters) (hP : ValidParameters P) (init : InitialState S)
    (samples : ℕ → ι → ℕ → Ξ)
    (trace : S.GeneratedTrace P hP init samples)
    (k : ℕ) (hk : 1 ≤ k) (i : ι) :
    let centerState := S.generatedState P hP init samples trace (k - 1)
    let nextState := S.generatedState P hP init samples trace k
    S.generatedXHat P hP init samples trace k i =
      S.csWeightedAverage i ((S.dualNeighborDisagreement nextState.yPrev) i)
        (centerState.xPrev i) (P.eta k) (samples k i) (centerState.xPrev_mem i)
        (trace.inner k i) (P.innerSteps k) := by
  intro centerState nextState
  have hcall := (trace.step_spec k hk).2.2 i
  simpa [generatedXHat, generatedState, centerState, nextState, IsStochasticCSCall]
    using hcall.2

private theorem generatedXHat_mem
    (P : Parameters) (hP : ValidParameters P) (init : InitialState S)
    (samples : ℕ → ι → ℕ → Ξ)
    (trace : S.GeneratedTrace P hP init samples)
    (k : ℕ) (hk : 1 ≤ k) (hT : 0 < P.innerSteps k) :
    S.FeasiblePoint (S.generatedXHat P hP init samples trace k) := by
  intro i
  let centerState := S.generatedState P hP init samples trace (k - 1)
  let nextState := S.generatedState P hP init samples trace k
  have hxhat :=
    S.generated_xhat_eq_inner_weightedAverage P hP init samples trace k hk i
  rw [hxhat]
  exact
    S.csWeightedAverage_mem i ((S.dualNeighborDisagreement nextState.yPrev) i)
      (centerState.xPrev i) (P.eta k) (samples k i) (centerState.xPrev_mem i)
      (trace.inner k i) hT

private theorem convexOn_inner_const (X : Set E) (hX : Convex ℝ X) (a : E) :
    ConvexOn ℝ X (fun z : E => inner ℝ a z) := by
  refine ⟨hX, ?_⟩
  intro x _hx y _hy α β _hα _hβ hsum
  simp [inner_add_right, inner_smul_right, hsum]

private theorem localObjective_convexOn_feasible_of_objectiveGrowth (i : ι) :
    ConvexOn ℝ (S.feasible i) (S.localObjective i) := by
  classical
  refine
    ConvexOn.of_first_order_lower_support
      (X := S.feasible i) (phi := S.localObjective i)
      (support := fun z => (innerSL ℝ (S.subgradient i z)).toLinearMap)
      (S.feasible_convex i) ?_
  intro x z hx hz
  have hgrowth := (S.objectiveGrowth i x z hx hz).1
  change
    S.localObjective i z + inner ℝ (S.subgradient i z) (x - z) ≤
      S.localObjective i x
  linarith

private theorem localObjective_continuousOn_feasible_of_objectiveGrowth (i : ι) :
    ContinuousOn (S.localObjective i) (S.feasible i) := by
  intro z hz
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  let C : ℝ := ‖S.subgradient i z‖ + S.M
  have hC_nonneg : 0 ≤ C := by
    exact add_nonneg (norm_nonneg _) (le_of_lt S.M_pos)
  refine ⟨ε / (C + 1), by positivity, ?_⟩
  intro x hx hdist
  have habs_bound :
      |S.localObjective i x - S.localObjective i z| ≤ C * ‖x - z‖ := by
    have hbound :=
      (abs_sub_le_and_continuousOn_of_first_order_remainder_le_norm
        (S.feasible i) (S.localObjective i) (S.subgradient i) S.M
        (le_of_lt S.M_pos) (fun u hu v hv => S.objectiveGrowth i u v hu hv)).1
        x hx z hz
    simpa [C, add_comm] using hbound
  have hdist_norm : ‖x - z‖ < ε / (C + 1) := by
    simpa [dist_eq_norm] using hdist
  have hC_lt : C * ‖x - z‖ < ε := by
    have hscaled :
        (C + 1) * ‖x - z‖ < ε := by
      have hpos : 0 < C + 1 := by positivity
      calc
        (C + 1) * ‖x - z‖ < (C + 1) * (ε / (C + 1)) :=
          mul_lt_mul_of_pos_left hdist_norm hpos
        _ = ε := by
          field_simp [ne_of_gt hpos]
    have hC_le : C * ‖x - z‖ ≤ (C + 1) * ‖x - z‖ := by
      exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    exact lt_of_le_of_lt hC_le hscaled
  simpa [Real.dist_eq] using lt_of_le_of_lt habs_bound hC_lt

private theorem localProx_convexOn_second_arg_of_distanceGenerating
    (i : ι) (xCenter : E) :
    ConvexOn ℝ (S.feasible i) (fun z : E => S.localProx i xCenter z) := by
  refine convexOn_second_of_three_point_identity_and_nonneg
    (S.feasible i) (S.localProx i) (S.localProxGradient i) xCenter
    (S.feasible_convex i) ?_ ?_
  · intro x _hx z _hz
    simpa [S.localProx_eq_bregmanFormula i] using
      (carrierBregmanDivergence_three_point_identity
        (v := S.localProxPotential i) (eval := fun q : E => q)
        (grad := S.localProxGradient i)
        (V := fun x z =>
          carrierBregmanFormula (S.localProxPotential i) (fun q : E => q)
            (S.localProxGradient i) x z)
        (by intro x z; rfl) xCenter z x)
  · intro x hx z hz
    exact le_trans (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) * ‖z - x‖ ^ 2)
      (S.proxStrongConvexity i z x (by simp) hz hx)

private theorem local_phi_convexOn_feasible
    (i : ι) (w xCenter : E) {eta : ℝ} (heta_nonneg : 0 ≤ eta) :
    ConvexOn ℝ (S.feasible i)
      (fun z : E => inner ℝ w z + S.localObjective i z +
        eta * S.localProx i xCenter z) := by
  classical
  refine
    ConvexOn.of_first_order_lower_support
      (X := S.feasible i)
      (phi := fun z : E => inner ℝ w z + S.localObjective i z +
        eta * S.localProx i xCenter z)
      (support := fun z =>
        (innerSL ℝ (w + S.subgradient i z +
          eta • (S.localProxGradient i z - S.localProxGradient i xCenter))).toLinearMap)
      (S.feasible_convex i) ?_
  intro x z hx hz
  have hObj := (S.objectiveGrowth i x z hx hz).1
  have hObjSupport :
      S.localObjective i z + inner ℝ (S.subgradient i z) (x - z) ≤
        S.localObjective i x := by
    linarith
  have hThree :
      S.localProx i xCenter x =
        S.localProx i xCenter z +
          inner ℝ (S.localProxGradient i z - S.localProxGradient i xCenter) (x - z) +
            S.localProx i z x := by
    simpa [S.localProx_eq_bregmanFormula i] using
      (carrierBregmanDivergence_three_point_identity
        (v := S.localProxPotential i) (eval := fun q : E => q)
        (grad := S.localProxGradient i)
        (V := fun x z =>
          carrierBregmanFormula (S.localProxPotential i) (fun q : E => q)
            (S.localProxGradient i) x z)
        (by
          intro x z
          rfl)
        xCenter z x)
  have hprox_nonneg : 0 ≤ S.localProx i z x := by
    have hhalf : (0 : ℝ) ≤ (1 / 2 : ℝ) * ‖z - x‖ ^ 2 := by positivity
    have hbound := S.proxStrongConvexity i z x (by simp) hz hx
    exact le_trans hhalf hbound
  have hProxSupport :
      eta * (S.localProx i xCenter z +
          inner ℝ (S.localProxGradient i z - S.localProxGradient i xCenter) (x - z)) ≤
        eta * S.localProx i xCenter x := by
    have hbase :
        S.localProx i xCenter z +
            inner ℝ (S.localProxGradient i z - S.localProxGradient i xCenter) (x - z) ≤
          S.localProx i xCenter x := by
      rw [hThree]
      linarith
    exact mul_le_mul_of_nonneg_left hbase heta_nonneg
  change
    inner ℝ w z + S.localObjective i z + eta * S.localProx i xCenter z +
        inner ℝ (w + S.subgradient i z +
          eta • (S.localProxGradient i z - S.localProxGradient i xCenter)) (x - z) ≤
      inner ℝ w x + S.localObjective i x + eta * S.localProx i xCenter x
  have hinnerW : inner ℝ w z + inner ℝ w (x - z) = inner ℝ w x := by
    rw [inner_sub_right]
    abel
  have hinnerExpand :
      inner ℝ (w + S.subgradient i z +
          eta • (S.localProxGradient i z - S.localProxGradient i xCenter)) (x - z) =
        inner ℝ w (x - z) + inner ℝ (S.subgradient i z) (x - z) +
          eta * inner ℝ (S.localProxGradient i z - S.localProxGradient i xCenter) (x - z) := by
    simp [inner_add_left, inner_smul_left]
  rw [hinnerExpand]
  nlinarith [hinnerW, hObjSupport, hProxSupport]

private theorem generated_sdcs_inner_projection_descent
    (P : Parameters) (hP : ValidParameters P) (init : InitialState S)
    (samples : ℕ → ι → ℕ → Ξ)
    (trace : S.GeneratedTrace P hP init samples)
    (i : ι) (k t : ℕ) (u : E) (hu : u ∈ S.feasible i) :
    let centerState := S.generatedState P hP init samples trace (k - 1)
    let nextState := S.generatedState P hP init samples trace k
    let w := (S.dualNeighborDisagreement nextState.yPrev) i
    let xCenter := centerState.xPrev i
    let uPrev := S.generatedInnerQuery P hP init samples trace i k t
    let h := S.oracle i uPrev (samples k i t)
    let uNext := S.generatedInnerQuery P hP init samples trace i k (t + 1)
    inner ℝ (w + h) uNext + P.eta k * S.localProx i xCenter uNext +
        (P.eta k * csBeta (t + 1)) * S.localProx i uPrev uNext ≤
      inner ℝ (w + h) u + P.eta k * S.localProx i xCenter u +
          (P.eta k * csBeta (t + 1)) * S.localProx i uPrev u -
        (P.eta k + P.eta k * csBeta (t + 1)) * S.localProx i uNext u := by
  classical
  intro centerState nextState w xCenter uPrev h uNext
  have hproj :=
    S.generated_stochasticCSProjection_spec P hP init samples trace i k t
  have hxCenter : xCenter ∈ S.feasible i := by
    simpa [centerState, xCenter, generatedState] using
      (S.generatedState P hP init samples trace (k - 1)).xPrev_mem i
  have huPrev : uPrev ∈ S.feasible i := by
    simpa [uPrev, generatedInnerQuery] using
      ((trace.inner k i).state t).mem
  have huNext : uNext ∈ S.feasible i := by
    simpa [uNext, generatedInnerQuery] using
      ((trace.inner k i).state (t + 1)).mem
  have hmin :
      IsMinOn
        (S.stochasticCSProjectionObjective i w xCenter uPrev h (P.eta k) (csBeta (t + 1)))
        (S.feasible i) uNext := by
    simpa [centerState, nextState, w, xCenter, uPrev, h, uNext] using hproj.2
  have hconv :
      ConvexOn ℝ (S.feasible i) (fun z : E => inner ℝ (w + h) z) :=
    convexOn_inner_const (X := S.feasible i) (S.feasible_convex i) (w + h)
  have hineq :=
    S.localProx_sourceProjectionInequality i
      (fun z : E => inner ℝ (w + h) z)
      xCenter uPrev uNext u (P.eta k) (P.eta k * csBeta (t + 1))
      hconv (ValidParameters.eta_nonneg hP k)
      (mul_nonneg (ValidParameters.eta_nonneg hP k) (csBeta_nonneg (t + 1)))
      hxCenter huPrev huNext hu
      (by simpa [stochasticCSProjectionObjective] using hmin)
  simpa using hineq

private theorem generated_sdcs_inner_phi_raw_inequality
    (P : Parameters) (hP : ValidParameters P) (init : InitialState S)
    (samples : ℕ → ι → ℕ → Ξ)
    (trace : S.GeneratedTrace P hP init samples)
    (i : ι) (k t : ℕ) (u : E) (hu : u ∈ S.feasible i) :
    let centerState := S.generatedState P hP init samples trace (k - 1)
    let nextState := S.generatedState P hP init samples trace k
    let w := (S.dualNeighborDisagreement nextState.yPrev) i
    let xCenter := centerState.xPrev i
    let uPrev := S.generatedInnerQuery P hP init samples trace i k t
    let h := S.oracle i uPrev (samples k i t)
    let uNext := S.generatedInnerQuery P hP init samples trace i k (t + 1)
    let δ := S.subgradient i uPrev - S.oracle i uPrev (samples k i t)
    inner ℝ w (uNext - u) + S.localObjective i uNext - S.localObjective i u +
        inner ℝ δ (u - uPrev) +
        P.eta k * S.localProx i xCenter uNext -
          P.eta k * S.localProx i xCenter u ≤
      (P.eta k * csBeta (t + 1)) * S.localProx i uPrev u -
        (P.eta k + P.eta k * csBeta (t + 1)) * S.localProx i uNext u +
        inner ℝ δ (uNext - uPrev) + S.M * ‖uNext - uPrev‖ -
        (P.eta k * csBeta (t + 1)) * S.localProx i uPrev uNext := by
  classical
  intro centerState nextState w xCenter uPrev h uNext δ
  have huPrev : uPrev ∈ S.feasible i := by
    simpa [uPrev, generatedInnerQuery] using
      ((trace.inner k i).state t).mem
  have huNext : uNext ∈ S.feasible i := by
    simpa [uNext, generatedInnerQuery] using
      ((trace.inner k i).state (t + 1)).mem
  have hObjUpper :=
    (S.objectiveGrowth i uNext uPrev huNext huPrev).2
  have hObjLower :=
    (S.objectiveGrowth i u uPrev hu huPrev).1
  have hObj :
      S.localObjective i uNext - S.localObjective i u ≤
        inner ℝ (S.subgradient i uPrev) (uNext - u) +
          S.M * ‖uNext - uPrev‖ := by
    have hUpper' :
        S.localObjective i uNext ≤
          S.localObjective i uPrev +
            inner ℝ (S.subgradient i uPrev) (uNext - uPrev) +
            S.M * ‖uNext - uPrev‖ := by
      linarith
    have hLower' :
        S.localObjective i uPrev +
            inner ℝ (S.subgradient i uPrev) (u - uPrev) ≤
          S.localObjective i u := by
      linarith
    have hinner :
        inner ℝ (S.subgradient i uPrev) (uNext - uPrev) -
            inner ℝ (S.subgradient i uPrev) (u - uPrev) =
          inner ℝ (S.subgradient i uPrev) (uNext - u) := by
      rw [← inner_sub_right]
      congr 1
      abel
    nlinarith
  have hProj :=
    S.generated_sdcs_inner_projection_descent P hP init samples trace i k t u hu
  have hProjMove :
      inner ℝ (w + h) (uNext - u) +
          P.eta k * S.localProx i xCenter uNext -
            P.eta k * S.localProx i xCenter u ≤
        (P.eta k * csBeta (t + 1)) * S.localProx i uPrev u -
          (P.eta k + P.eta k * csBeta (t + 1)) * S.localProx i uNext u -
          (P.eta k * csBeta (t + 1)) * S.localProx i uPrev uNext := by
    have hProj' :
        inner ℝ (w + h) uNext + P.eta k * S.localProx i xCenter uNext +
            (P.eta k * csBeta (t + 1)) * S.localProx i uPrev uNext ≤
          inner ℝ (w + h) u + P.eta k * S.localProx i xCenter u +
              (P.eta k * csBeta (t + 1)) * S.localProx i uPrev u -
            (P.eta k + P.eta k * csBeta (t + 1)) *
              S.localProx i uNext u := by
      simpa [centerState, nextState, w, xCenter, uPrev, h, uNext] using hProj
    have hinner :
        inner ℝ (w + h) (uNext - u) =
          inner ℝ (w + h) uNext - inner ℝ (w + h) u := by
      rw [inner_sub_right]
    nlinarith
  have hsubgrad_eq : S.subgradient i uPrev = h + δ := by
    simp [δ, h]
  have hnoise :
      inner ℝ w (uNext - u) +
          inner ℝ (S.subgradient i uPrev) (uNext - u) +
          inner ℝ δ (u - uPrev) =
        inner ℝ (w + h) (uNext - u) +
          inner ℝ δ (uNext - uPrev) := by
    rw [hsubgrad_eq]
    have hstep : (uNext - u) + (u - uPrev) = uNext - uPrev := by
      abel
    calc
      inner ℝ w (uNext - u) + inner ℝ (h + δ) (uNext - u) +
          inner ℝ δ (u - uPrev)
          =
        inner ℝ (w + h) (uNext - u) +
          (inner ℝ δ (uNext - u) + inner ℝ δ (u - uPrev)) := by
          simp [inner_add_left]
          ring
      _ = inner ℝ (w + h) (uNext - u) +
          inner ℝ δ ((uNext - u) + (u - uPrev)) := by
          rw [inner_add_right]
      _ = inner ℝ (w + h) (uNext - u) +
          inner ℝ δ (uNext - uPrev) := by
          rw [hstep]
  calc
    inner ℝ w (uNext - u) + S.localObjective i uNext - S.localObjective i u +
          inner ℝ δ (u - uPrev) +
          P.eta k * S.localProx i xCenter uNext -
            P.eta k * S.localProx i xCenter u
        ≤ inner ℝ w (uNext - u) +
            inner ℝ (S.subgradient i uPrev) (uNext - u) +
            inner ℝ δ (u - uPrev) +
            P.eta k * S.localProx i xCenter uNext -
              P.eta k * S.localProx i xCenter u +
            S.M * ‖uNext - uPrev‖ := by
          nlinarith
    _ = inner ℝ (w + h) (uNext - u) +
          P.eta k * S.localProx i xCenter uNext -
            P.eta k * S.localProx i xCenter u +
          inner ℝ δ (uNext - uPrev) +
          S.M * ‖uNext - uPrev‖ := by
          rw [hnoise]
          ring
    _ ≤ (P.eta k * csBeta (t + 1)) * S.localProx i uPrev u -
          (P.eta k + P.eta k * csBeta (t + 1)) * S.localProx i uNext u +
          inner ℝ δ (uNext - uPrev) + S.M * ‖uNext - uPrev‖ -
          (P.eta k * csBeta (t + 1)) * S.localProx i uPrev uNext := by
          nlinarith

/-- The recursion-local form of the stochastic CS projection inequality.

Choosing the previous inner iterate itself as the comparator makes the first
prox term a consecutive difference.  Thus these terms telescope over any
finite inner window, while strong convexity of the *backward* prox term already
controls the squared increment.  This avoids the retired route that tried to
deduce upper integrability of forward Bregman slices from their coercive lower
bound. -/
private theorem generated_sdcs_inner_increment_energy_inequality
    (P : Parameters) (hP : ValidParameters P) (init : InitialState S)
    (samples : ℕ → ι → ℕ → Ξ)
    (trace : S.GeneratedTrace P hP init samples)
    (i : ι) (k t : ℕ) :
    let centerState := S.generatedState P hP init samples trace (k - 1)
    let nextState := S.generatedState P hP init samples trace k
    let w := (S.dualNeighborDisagreement nextState.yPrev) i
    let xCenter := centerState.xPrev i
    let uPrev := S.generatedInnerQuery P hP init samples trace i k t
    let uNext := S.generatedInnerQuery P hP init samples trace i k (t + 1)
    let δ := S.subgradient i uPrev - S.oracle i uPrev (samples k i t)
    (P.eta k / 2) * ‖uNext - uPrev‖ ^ 2 +
        inner ℝ w (uNext - uPrev) +
        S.localObjective i uNext - S.localObjective i uPrev +
        P.eta k * S.localProx i xCenter uNext -
          P.eta k * S.localProx i xCenter uPrev ≤
      inner ℝ δ (uNext - uPrev) + S.M * ‖uNext - uPrev‖ := by
  classical
  intro centerState nextState w xCenter uPrev uNext δ
  have huPrev : uPrev ∈ S.feasible i := by
    simpa [uPrev, generatedInnerQuery] using
      ((trace.inner k i).state t).mem
  have huNext : uNext ∈ S.feasible i := by
    simpa [uNext, generatedInnerQuery] using
      ((trace.inner k i).state (t + 1)).mem
  have hbeta_nonneg : 0 ≤ P.eta k * csBeta (t + 1) :=
    mul_nonneg (ValidParameters.eta_nonneg hP k) (csBeta_nonneg (t + 1))
  exact
    inner_step_increment_energy_of_two_bregman_descent
      (f := S.localObjective i) (V := S.localProx i)
      (w := w) (center := xCenter) (uPrev := uPrev) (uNext := uNext)
      (delta := δ) (eta := P.eta k) (beta := P.eta k * csBeta (t + 1))
      (M := S.M)
      (heta_nonneg := ValidParameters.eta_nonneg hP k)
      (hbeta_nonneg := hbeta_nonneg)
      (hself := S.localProx_self_eq_zero i uPrev huPrev)
      (hbackward :=
        S.proxStrongConvexity i uNext uPrev (by simp) huNext huPrev)
      (hforward_nonneg :=
        le_trans (mul_nonneg (by norm_num) (sq_nonneg _))
          (S.proxStrongConvexity i uPrev uNext (by simp) huPrev huNext))
      (hdescent := by
        simpa [centerState, nextState, w, xCenter, uPrev, uNext, δ] using
          S.generated_sdcs_inner_phi_raw_inequality
            P hP init samples trace i k t uPrev huPrev)

/-- A finite path whose one-step energy has a telescoping potential has an
explicit square-increment bound.  This is the scalar summation used below for
the direct finite-horizon moment proof; unlike the retired forward-Bregman
route, it needs only nonnegativity of the terminal potential. -/
private theorem finite_path_sq_increment_le_of_telescope
    (u delta : ℕ → E) (w xRef : E) (f V : E → ℝ)
    (eta M C : ℝ) (n : ℕ)
    (heta : 0 < eta) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hV0 : V (u 0) = 0) (hVn : 0 ≤ V (u n))
    (hf0 : |f (u 0) - f xRef| ≤ C * ‖u 0 - xRef‖)
    (hfn : |f (u n) - f xRef| ≤ C * ‖u n - xRef‖)
    (hstep : ∀ r ∈ Finset.range n,
      (eta / 2) * ‖u (r + 1) - u r‖ ^ 2 +
          inner ℝ w (u (r + 1) - u r) +
          f (u (r + 1)) - f (u r) +
          eta * V (u (r + 1)) - eta * V (u r) ≤
        inner ℝ (delta r) (u (r + 1) - u r) +
          M * ‖u (r + 1) - u r‖) :
    (∑ r ∈ Finset.range n, ‖u (r + 1) - u r‖ ^ 2) ≤
      (4 / eta ^ 2) *
          (∑ r ∈ Finset.range n,
            (‖delta r‖ + M + ‖w‖ + C) ^ 2) +
        (8 * C / eta) * ‖u 0 - xRef‖ := by
  exact sum_sq_increment_le_of_telescoping_energy
    u delta w xRef f V eta M C n heta hC hV0 hVn hf0 hfn hstep

/-- The objective growth assumption controls objective differences from a fixed
feasible reference point by a deterministic linear modulus. -/
private theorem localObjective_sub_abs_le_ref
    (i : ι) (z xRef : E) (hz : z ∈ S.feasible i) (hxRef : xRef ∈ S.feasible i) :
    |S.localObjective i z - S.localObjective i xRef| ≤
      (S.M + ‖S.subgradient i xRef‖) * ‖z - xRef‖ := by
  let R : ℝ :=
    S.localObjective i z - S.localObjective i xRef -
      inner ℝ (S.subgradient i xRef) (z - xRef)
  have hgrowth := S.objectiveGrowth i z xRef hz hxRef
  have hR_nonneg : 0 ≤ R := by simpa [R] using hgrowth.1
  have hR_le : R ≤ S.M * ‖z - xRef‖ := by simpa [R] using hgrowth.2
  have heq :
      S.localObjective i z - S.localObjective i xRef =
        R + inner ℝ (S.subgradient i xRef) (z - xRef) := by
    dsimp [R]
    ring
  calc
    |S.localObjective i z - S.localObjective i xRef| =
        |R + inner ℝ (S.subgradient i xRef) (z - xRef)| := by rw [heq]
    _ ≤ |R| + |inner ℝ (S.subgradient i xRef) (z - xRef)| := abs_add_le _ _
    _ ≤ S.M * ‖z - xRef‖ +
          ‖S.subgradient i xRef‖ * ‖z - xRef‖ := by
      exact add_le_add (by simpa [abs_of_nonneg hR_nonneg] using hR_le)
        (abs_real_inner_le_norm _ _)
    _ = (S.M + ‖S.subgradient i xRef‖) * ‖z - xRef‖ := by ring

/-- Direct finite-prefix square-increment estimate for the actual stochastic CS
trace.  Its right-hand side contains only oracle-error squares, the outer dual
disagreement square, and the previous outer primal distance; all are suitable
for the simultaneous finite-horizon L2 induction below. -/
private theorem generated_sdcs_inner_prefix_increment_sq_le
    (P : Parameters) (hP : ValidParameters P) (init : InitialState S)
    (samples : ℕ → ι → ℕ → Ξ)
    (trace : S.GeneratedTrace P hP init samples)
    (i : ι) (k n : ℕ) (xRef : E) (hxRef : xRef ∈ S.feasible i)
    (heta : 0 < P.eta k) :
    let u : ℕ → E := fun r => S.generatedInnerQuery P hP init samples trace i k r
    let delta : ℕ → E := fun r => S.subgradient i (u r) - S.oracle i (u r) (samples k i r)
    let w := (S.dualNeighborDisagreement
      (S.generatedState P hP init samples trace k).yPrev) i
    let C := S.M + ‖S.subgradient i xRef‖
    (∑ r ∈ Finset.range n, ‖u (r + 1) - u r‖ ^ 2) ≤
      (4 / (P.eta k) ^ 2) *
          (∑ r ∈ Finset.range n, (‖delta r‖ + S.M + ‖w‖ + C) ^ 2) +
        (8 * C / P.eta k) * ‖u 0 - xRef‖ := by
  classical
  intro u delta w C
  let centerState := S.generatedState P hP init samples trace (k - 1)
  let xCenter := centerState.xPrev i
  have hu0 : u 0 = xCenter := by
    have h0 := (trace.inner k i).initial_value
    simpa [u, xCenter, centerState, generatedInnerQuery, generatedState] using h0
  have hu_mem : ∀ r, u r ∈ S.feasible i := by
    intro r
    simpa [u, generatedInnerQuery] using ((trace.inner k i).state r).mem
  have hV0 : S.localProx i xCenter (u 0) = 0 := by
    rw [hu0]
    exact S.localProx_self_eq_zero i xCenter (by
      show centerState.xPrev i ∈ S.feasible i
      exact centerState.xPrev_mem i)
  have hVn : 0 ≤ S.localProx i xCenter (u n) := by
    have hprox := S.proxStrongConvexity i xCenter (u n) (by simp)
      (by
        show centerState.xPrev i ∈ S.feasible i
        exact centerState.xPrev_mem i) (hu_mem n)
    exact le_trans (mul_nonneg (by norm_num) (sq_nonneg _)) hprox
  have hC : 0 ≤ C := by
    dsimp [C]
    exact add_nonneg (le_of_lt S.M_pos) (norm_nonneg _)
  refine finite_path_sq_increment_le_of_telescope
    (u := u) (delta := delta) (w := w) (xRef := xRef)
    (f := S.localObjective i) (V := S.localProx i xCenter)
    (eta := P.eta k) (M := S.M) (C := C) (n := n)
    heta (le_of_lt S.M_pos) hC hV0 hVn
    (S.localObjective_sub_abs_le_ref i (u 0) xRef (hu_mem 0) hxRef)
    (S.localObjective_sub_abs_le_ref i (u n) xRef (hu_mem n) hxRef) ?_
  intro r hr
  simpa [u, delta, w, centerState, xCenter] using
    S.generated_sdcs_inner_increment_energy_inequality
      P hP init samples trace i k r

private theorem generated_sdcs_inner_phi_young_inequality
    (P : Parameters) (hP : ValidParameters P) (init : InitialState S)
    (samples : ℕ → ι → ℕ → Ξ)
    (trace : S.GeneratedTrace P hP init samples)
    (i : ι) (k t : ℕ) (u : E) (hu : u ∈ S.feasible i)
    (heta : 0 < P.eta k) :
    let centerState := S.generatedState P hP init samples trace (k - 1)
    let nextState := S.generatedState P hP init samples trace k
    let w := (S.dualNeighborDisagreement nextState.yPrev) i
    let xCenter := centerState.xPrev i
    let uPrev := S.generatedInnerQuery P hP init samples trace i k t
    let h := S.oracle i uPrev (samples k i t)
    let uNext := S.generatedInnerQuery P hP init samples trace i k (t + 1)
    let δ := S.subgradient i uPrev - S.oracle i uPrev (samples k i t)
    inner ℝ w (uNext - u) + S.localObjective i uNext - S.localObjective i u +
        inner ℝ δ (u - uPrev) +
        P.eta k * S.localProx i xCenter uNext -
          P.eta k * S.localProx i xCenter u ≤
      (P.eta k * csBeta (t + 1)) * S.localProx i uPrev u -
        (P.eta k + P.eta k * csBeta (t + 1)) * S.localProx i uNext u +
        (S.M + ‖δ‖) ^ 2 / (2 * (P.eta k * csBeta (t + 1))) := by
  classical
  intro centerState nextState w xCenter uPrev h uNext δ
  exact
    two_bregman_descent_le_of_linear_error_and_coercivity
      (f := S.localObjective i) (V := S.localProx i)
      (w := w) (center := xCenter) (uPrev := uPrev) (uNext := uNext)
      (u := u) (delta := δ) (eta := P.eta k)
      (D := P.eta k * csBeta (t + 1)) (M := S.M)
      (mul_pos heta (by unfold csBeta; positivity))
      (by
        simpa [norm_sub_rev] using
          S.proxStrongConvexity i uPrev uNext (by simp)
            (by
              simpa [uPrev, generatedInnerQuery] using
                ((trace.inner k i).state t).mem)
            (by
              simpa [uNext, generatedInnerQuery] using
                ((trace.inner k i).state (t + 1)).mem))
      (by
        simpa [centerState, nextState, w, xCenter, uPrev, h, uNext, δ] using
          S.generated_sdcs_inner_phi_raw_inequality
            P hP init samples trace i k t u hu)

private theorem generated_sdcs_inner_phi_young_phi_bound
    (P : Parameters) (hP : ValidParameters P) (init : InitialState S)
    (samples : ℕ → ι → ℕ → Ξ)
    (trace : S.GeneratedTrace P hP init samples)
    (i : ι) (k t : ℕ) (u : E) (hu : u ∈ S.feasible i)
    (heta : 0 < P.eta k) :
    let centerState := S.generatedState P hP init samples trace (k - 1)
    let nextState := S.generatedState P hP init samples trace k
    let w := (S.dualNeighborDisagreement nextState.yPrev) i
    let xCenter := centerState.xPrev i
    let uPrev := S.generatedInnerQuery P hP init samples trace i k t
    let uNext := S.generatedInnerQuery P hP init samples trace i k (t + 1)
    let δ := S.subgradient i uPrev - S.oracle i uPrev (samples k i t)
    inner ℝ w uNext + S.localObjective i uNext +
        P.eta k * S.localProx i xCenter uNext ≤
      inner ℝ w u + S.localObjective i u +
        P.eta k * S.localProx i xCenter u -
        inner ℝ δ (u - uPrev) +
        (P.eta k * csBeta (t + 1)) * S.localProx i uPrev u -
        (P.eta k + P.eta k * csBeta (t + 1)) * S.localProx i uNext u +
        (S.M + ‖δ‖) ^ 2 / (2 * (P.eta k * csBeta (t + 1))) := by
  classical
  intro centerState nextState w xCenter uPrev uNext δ
  have hYoung :=
    S.generated_sdcs_inner_phi_young_inequality P hP init samples trace
      i k t u hu heta
  have hYoung' :
      inner ℝ w (uNext - u) + S.localObjective i uNext - S.localObjective i u +
          inner ℝ δ (u - uPrev) +
          P.eta k * S.localProx i xCenter uNext -
            P.eta k * S.localProx i xCenter u ≤
        (P.eta k * csBeta (t + 1)) * S.localProx i uPrev u -
          (P.eta k + P.eta k * csBeta (t + 1)) * S.localProx i uNext u +
          (S.M + ‖δ‖) ^ 2 / (2 * (P.eta k * csBeta (t + 1))) := by
    simpa [centerState, nextState, w, xCenter, uPrev, uNext, δ] using hYoung
  have hinner :
      inner ℝ w (uNext - u) = inner ℝ w uNext - inner ℝ w u := by
    rw [inner_sub_right]
  nlinarith

private theorem generated_inner_phi_weighted_sum_bound
    (P : Parameters) (hP : ValidParameters P) (init : InitialState S)
    (samples : ℕ → ι → ℕ → Ξ)
    (trace : S.GeneratedTrace P hP init samples)
    (i : ι) (k : ℕ) (u : E) (hu : u ∈ S.feasible i)
    (hT : 0 < P.innerSteps k) (heta : 0 < P.eta k) :
    let centerState := S.generatedState P hP init samples trace (k - 1)
    let nextState := S.generatedState P hP init samples trace k
    let T := P.innerSteps k
    let W := csLambdaSum T
    let w := (S.dualNeighborDisagreement nextState.yPrev) i
    let xCenter := centerState.xPrev i
    W⁻¹ *
        (∑ t ∈ Finset.range T, csLambda (t + 1) *
          (let uNext := S.generatedInnerQuery P hP init samples trace i k (t + 1)
           inner ℝ w uNext + S.localObjective i uNext +
             P.eta k * S.localProx i xCenter uNext)) ≤
      W⁻¹ *
        (∑ t ∈ Finset.range T, csLambda (t + 1) *
          (let uPrev := S.generatedInnerQuery P hP init samples trace i k t
           let uNext := S.generatedInnerQuery P hP init samples trace i k (t + 1)
           let δ := S.subgradient i uPrev - S.oracle i uPrev (samples k i t)
           inner ℝ w u + S.localObjective i u + P.eta k * S.localProx i xCenter u -
             inner ℝ δ (u - uPrev) +
             (P.eta k * csBeta (t + 1)) * S.localProx i uPrev u -
             (P.eta k + P.eta k * csBeta (t + 1)) * S.localProx i uNext u +
             (S.M + ‖δ‖) ^ 2 / (2 * (P.eta k * csBeta (t + 1))))) := by
  classical
  intro centerState nextState T W w xCenter
  have hW_nonneg : 0 ≤ W⁻¹ := by
    exact inv_nonneg.mpr (le_of_lt (by simpa [W, T] using csLambdaSum_pos_of_pos hT))
  have hsum :
      (∑ t ∈ Finset.range T, csLambda (t + 1) *
          (let uNext := S.generatedInnerQuery P hP init samples trace i k (t + 1)
           inner ℝ w uNext + S.localObjective i uNext +
             P.eta k * S.localProx i xCenter uNext)) ≤
        (∑ t ∈ Finset.range T, csLambda (t + 1) *
          (let uPrev := S.generatedInnerQuery P hP init samples trace i k t
           let uNext := S.generatedInnerQuery P hP init samples trace i k (t + 1)
           let δ := S.subgradient i uPrev - S.oracle i uPrev (samples k i t)
           inner ℝ w u + S.localObjective i u + P.eta k * S.localProx i xCenter u -
             inner ℝ δ (u - uPrev) +
             (P.eta k * csBeta (t + 1)) * S.localProx i uPrev u -
             (P.eta k + P.eta k * csBeta (t + 1)) * S.localProx i uNext u +
             (S.M + ‖δ‖) ^ 2 / (2 * (P.eta k * csBeta (t + 1))))) := by
    refine Finset.sum_le_sum ?_
    intro t ht
    have hLambda_nonneg : 0 ≤ csLambda (t + 1) := by
      unfold csLambda
      positivity
    have hpoint :=
      S.generated_sdcs_inner_phi_young_phi_bound P hP init samples trace i k t u hu heta
    exact mul_le_mul_of_nonneg_left
      (by
        simpa [centerState, nextState, w, xCenter] using hpoint)
      hLambda_nonneg
  exact mul_le_mul_of_nonneg_left hsum hW_nonneg

private theorem generated_inner_phi_weighted_sum_bound_coeff
    (P : Parameters) (hP : ValidParameters P) (init : InitialState S)
    (samples : ℕ → ι → ℕ → Ξ)
    (trace : S.GeneratedTrace P hP init samples)
    (i : ι) (k : ℕ) (u : E) (hu : u ∈ S.feasible i)
    (hT : 0 < P.innerSteps k) (heta : 0 < P.eta k) :
    let centerState := S.generatedState P hP init samples trace (k - 1)
    let nextState := S.generatedState P hP init samples trace k
    let T := P.innerSteps k
    let coeff := 2 / ((T : ℝ) * ((T : ℝ) + 3))
    let w := (S.dualNeighborDisagreement nextState.yPrev) i
    let xCenter := centerState.xPrev i
    coeff *
        (∑ t ∈ Finset.range T, csLambda (t + 1) *
          (let uNext := S.generatedInnerQuery P hP init samples trace i k (t + 1)
           inner ℝ w uNext + S.localObjective i uNext +
             P.eta k * S.localProx i xCenter uNext)) ≤
      coeff *
        (∑ t ∈ Finset.range T, csLambda (t + 1) *
          (let uPrev := S.generatedInnerQuery P hP init samples trace i k t
           let uNext := S.generatedInnerQuery P hP init samples trace i k (t + 1)
           let δ := S.subgradient i uPrev - S.oracle i uPrev (samples k i t)
           inner ℝ w u + S.localObjective i u + P.eta k * S.localProx i xCenter u -
             inner ℝ δ (u - uPrev) +
             (P.eta k * csBeta (t + 1)) * S.localProx i uPrev u -
             (P.eta k + P.eta k * csBeta (t + 1)) * S.localProx i uNext u +
             (S.M + ‖δ‖) ^ 2 / (2 * (P.eta k * csBeta (t + 1))))) := by
  classical
  intro centerState nextState T coeff w xCenter
  have hbase :=
    S.generated_inner_phi_weighted_sum_bound P hP init samples trace i k u hu hT heta
  have hcoeff : (csLambdaSum T)⁻¹ = coeff := by
    have hT_ne : (T : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hT)
    have hT3_ne : (T : ℝ) + 3 ≠ 0 := by positivity
    dsimp [coeff]
    rw [csLambdaSum_eq]
    field_simp [hT_ne, hT3_ne]
  simpa [centerState, nextState, T, coeff, w, xCenter, hcoeff] using hbase

private theorem generated_outer_phi_jensen_inequality
    (P : Parameters) (hP : ValidParameters P) (init : InitialState S)
    (samples : ℕ → ι → ℕ → Ξ)
    (trace : S.GeneratedTrace P hP init samples)
    (k : ℕ) (hk : 1 ≤ k) (hT : 0 < P.innerSteps k) :
    let centerState := S.generatedState P hP init samples trace (k - 1)
    let nextState := S.generatedState P hP init samples trace k
    let T := P.innerSteps k
    let W := csLambdaSum T
    (∑ i,
      (inner ℝ ((S.dualNeighborDisagreement nextState.yPrev) i)
          (S.generatedXHat P hP init samples trace k i) +
        (S.localObjective i (S.generatedXHat P hP init samples trace k i) +
          P.eta k * S.localProx i (centerState.xPrev i)
            (S.generatedXHat P hP init samples trace k i)))) ≤
      W⁻¹ *
        ∑ t ∈ Finset.range T, csLambda (t + 1) *
          (∑ i,
            (inner ℝ ((S.dualNeighborDisagreement nextState.yPrev) i)
                (S.generatedInnerQuery P hP init samples trace i k (t + 1)) +
              (S.localObjective i
                  (S.generatedInnerQuery P hP init samples trace i k (t + 1)) +
                P.eta k * S.localProx i (centerState.xPrev i)
                  (S.generatedInnerQuery P hP init samples trace i k (t + 1))))) := by
  classical
  intro centerState nextState T W
  let X : ι → Set E := fun i => S.feasible i
  let f : ι → E → ℝ := fun i z =>
    inner ℝ ((S.dualNeighborDisagreement nextState.yPrev) i) z +
      S.localObjective i z + P.eta k * S.localProx i (centerState.xPrev i) z
  let p : ℕ → ι → E := fun t i =>
    S.generatedInnerQuery P hP init samples trace i k (t + 1)
  have hf : ∀ i, ConvexOn ℝ (X i) (f i) := by
    intro i
    simpa [X, f] using
      S.local_phi_convexOn_feasible i ((S.dualNeighborDisagreement nextState.yPrev) i)
        (centerState.xPrev i) (ValidParameters.eta_nonneg hP k)
  have hγ_nonneg : ∀ t ∈ Finset.range T, 0 ≤ csLambda (t + 1) := by
    intro t _ht
    unfold csLambda
    positivity
  have hp_mem : ∀ t ∈ Finset.range T, ∀ i, p t i ∈ X i := by
    intro t _ht i
    simpa [p, X, generatedInnerQuery] using
      ((trace.inner k i).state (t + 1)).mem
  have hW_pos : 0 < W := by
    simpa [W, T] using csLambdaSum_pos_of_pos hT
  have hW_eq : W = ∑ t ∈ Finset.range T, csLambda (t + 1) := by
    simp [W, T, csLambdaSum]
  have hxbar :
      ∀ i,
        S.generatedXHat P hP init samples trace k i =
          W⁻¹ • ∑ t ∈ Finset.range T, csLambda (t + 1) • p t i := by
    intro i
    have hxhat :=
      S.generated_xhat_eq_inner_weightedAverage P hP init samples trace k hk i
    simpa [W, T, p, centerState, nextState, csWeightedAverage, generatedInnerQuery]
      using hxhat
  have hJ :=
    sum_convexOn_weighted_average_le_weighted_sum
      (I := ι) (T := ℕ) (E := E)
      (s := Finset.range T) (γ := fun t => csLambda (t + 1))
      (X := X) (f := f) (p := p)
      (xbar := S.generatedXHat P hP init samples trace k) (W := W)
      hf hγ_nonneg hp_mem hW_pos hW_eq hxbar
  dsimp [f, p] at hJ ⊢
  simpa [add_assoc] using hJ

private theorem generated_outer_phi_jensen_coeff_inequality
    (P : Parameters) (hP : ValidParameters P) (init : InitialState S)
    (samples : ℕ → ι → ℕ → Ξ)
    (trace : S.GeneratedTrace P hP init samples)
    (k : ℕ) (hk : 1 ≤ k) (hT : 0 < P.innerSteps k) :
    let centerState := S.generatedState P hP init samples trace (k - 1)
    let nextState := S.generatedState P hP init samples trace k
    let T := P.innerSteps k
    let coeff := 2 / ((T : ℝ) * ((T : ℝ) + 3))
    (∑ i,
      (inner ℝ ((S.dualNeighborDisagreement nextState.yPrev) i)
          (S.generatedXHat P hP init samples trace k i) +
        (S.localObjective i (S.generatedXHat P hP init samples trace k i) +
          P.eta k * S.localProx i (centerState.xPrev i)
            (S.generatedXHat P hP init samples trace k i)))) ≤
      ∑ i,
        coeff *
          (∑ t ∈ Finset.range T, csLambda (t + 1) *
            (inner ℝ ((S.dualNeighborDisagreement nextState.yPrev) i)
                (S.generatedInnerQuery P hP init samples trace i k (t + 1)) +
              (S.localObjective i
                  (S.generatedInnerQuery P hP init samples trace i k (t + 1)) +
                P.eta k * S.localProx i (centerState.xPrev i)
                  (S.generatedInnerQuery P hP init samples trace i k (t + 1))))) := by
  classical
  intro centerState nextState T coeff
  have hJ :=
    S.generated_outer_phi_jensen_inequality P hP init samples trace k hk hT
  have hcoeff : (csLambdaSum T)⁻¹ = coeff := by
    have hT_ne : (T : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hT)
    have hT3_ne : (T : ℝ) + 3 ≠ 0 := by positivity
    dsimp [coeff]
    rw [csLambdaSum_eq]
    field_simp [hT_ne, hT3_ne]
  let φ : ι → ℕ → ℝ := fun i t =>
    inner ℝ ((S.dualNeighborDisagreement nextState.yPrev) i)
        (S.generatedInnerQuery P hP init samples trace i k (t + 1)) +
      (S.localObjective i (S.generatedInnerQuery P hP init samples trace i k (t + 1)) +
        P.eta k * S.localProx i (centerState.xPrev i)
          (S.generatedInnerQuery P hP init samples trace i k (t + 1)))
  have hcomm :=
    coeff_mul_weighted_time_agent_sum_comm (T := T) (c := coeff) (φ := φ)
  calc
    (∑ i,
      (inner ℝ ((S.dualNeighborDisagreement nextState.yPrev) i)
          (S.generatedXHat P hP init samples trace k i) +
        (S.localObjective i (S.generatedXHat P hP init samples trace k i) +
          P.eta k * S.localProx i (centerState.xPrev i)
            (S.generatedXHat P hP init samples trace k i))))
        ≤ (csLambdaSum T)⁻¹ *
            ∑ t ∈ Finset.range T, csLambda (t + 1) *
              (∑ i,
                (inner ℝ ((S.dualNeighborDisagreement nextState.yPrev) i)
                    (S.generatedInnerQuery P hP init samples trace i k (t + 1)) +
                  (S.localObjective i
                      (S.generatedInnerQuery P hP init samples trace i k (t + 1)) +
                    P.eta k * S.localProx i (centerState.xPrev i)
                      (S.generatedInnerQuery P hP init samples trace i k (t + 1))))) := by
          simpa [centerState, nextState, T] using hJ
    _ = coeff *
            ∑ t ∈ Finset.range T, csLambda (t + 1) *
              (∑ i,
                (inner ℝ ((S.dualNeighborDisagreement nextState.yPrev) i)
                    (S.generatedInnerQuery P hP init samples trace i k (t + 1)) +
                  (S.localObjective i
                      (S.generatedInnerQuery P hP init samples trace i k (t + 1)) +
                    P.eta k * S.localProx i (centerState.xPrev i)
                      (S.generatedInnerQuery P hP init samples trace i k (t + 1))))) := by
          rw [hcoeff]
    _ = ∑ i,
        coeff *
          (∑ t ∈ Finset.range T, csLambda (t + 1) *
            (inner ℝ ((S.dualNeighborDisagreement nextState.yPrev) i)
                (S.generatedInnerQuery P hP init samples trace i k (t + 1)) +
              (S.localObjective i
                  (S.generatedInnerQuery P hP init samples trace i k (t + 1)) +
                P.eta k * S.localProx i (centerState.xPrev i)
                  (S.generatedInnerQuery P hP init samples trace i k (t + 1))))) := by
          simpa [φ] using hcomm

private theorem dual_update_inner_eq_half_sq_dist_drop
    {τ : ℝ} (hτ : 0 < τ) (v yPrev yNext y : Stacked ι E)
    (hupdate : yNext = yPrev + τ⁻¹ • v) :
    stackedInner v (y - yNext) =
      (τ / 2) *
        (S.stackedNormSq (y - yPrev) - S.stackedNormSq (y - yNext) -
          S.stackedNormSq (yPrev - yNext)) := by
  classical
  have hτ_ne : τ ≠ 0 := ne_of_gt hτ
  have hpoint :
      ∀ i,
        inner ℝ (v i) (y i - yNext i) =
          (τ / 2) *
            (‖y i - yPrev i‖ ^ 2 - ‖y i - yNext i‖ ^ 2 -
              ‖yPrev i - yNext i‖ ^ 2) := by
    intro i
    have hcoord_update :
        yNext i = yPrev i + τ⁻¹ • v i := by
      simpa using congrFun hupdate i
    have hv :
        v i = τ • (yNext i - yPrev i) := by
      rw [hcoord_update]
      simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, hτ_ne]
    have hthree :
        inner ℝ (yNext i - yPrev i) (y i - yNext i) =
          (‖y i - yPrev i‖ ^ 2 - ‖y i - yNext i‖ ^ 2 -
              ‖yPrev i - yNext i‖ ^ 2) / 2 := by
      have hnorm := norm_sub_sq_real (yNext i - y i) (yNext i - yPrev i)
      have hsub : (yNext i - y i) - (yNext i - yPrev i) = yPrev i - y i := by
        abel
      have hnorm_yPrev :
          ‖yPrev i - y i‖ ^ 2 = ‖y i - yPrev i‖ ^ 2 := by
        rw [← norm_neg (yPrev i - y i)]
        congr 1
        abel
      have hnorm_yNext :
          ‖yNext i - y i‖ ^ 2 = ‖y i - yNext i‖ ^ 2 := by
        rw [← norm_neg (yNext i - y i)]
        congr 1
        abel
      have hnorm_step :
          ‖yNext i - yPrev i‖ ^ 2 = ‖yPrev i - yNext i‖ ^ 2 := by
        rw [← norm_neg (yNext i - yPrev i)]
        congr 1
        abel
      rw [hsub, hnorm_yPrev, hnorm_yNext, hnorm_step] at hnorm
      have hinner_comm :
          inner ℝ (yNext i - y i) (yNext i - yPrev i) =
            inner ℝ (yNext i - yPrev i) (yNext i - y i) := by
        rw [real_inner_comm]
      have hneg :
          inner ℝ (yNext i - yPrev i) (y i - yNext i) =
            -inner ℝ (yNext i - yPrev i) (yNext i - y i) := by
        have hyneg : y i - yNext i = -(yNext i - y i) := by
          abel
        rw [hyneg, inner_neg_right]
      rw [hinner_comm] at hnorm
      nlinarith
    calc
      inner ℝ (v i) (y i - yNext i) =
          inner ℝ (τ • (yNext i - yPrev i)) (y i - yNext i) := by
            rw [hv]
      _ = τ * inner ℝ (yNext i - yPrev i) (y i - yNext i) := by
            simp [inner_smul_left]
      _ = (τ / 2) *
            (‖y i - yPrev i‖ ^ 2 - ‖y i - yNext i‖ ^ 2 -
              ‖yPrev i - yNext i‖ ^ 2) := by
            rw [hthree]
            ring
  dsimp [stackedInner, stackedNormSq]
  calc
    (∑ i, inner ℝ (v i) ((y - yNext) i)) =
        ∑ i, (τ / 2) *
          (‖y i - yPrev i‖ ^ 2 - ‖y i - yNext i‖ ^ 2 -
            ‖yPrev i - yNext i‖ ^ 2) := by
          exact Finset.sum_congr rfl (fun i _hi => by simpa [Pi.sub_apply] using hpoint i)
    _ = (τ / 2) *
        (∑ i,
          (‖y i - yPrev i‖ ^ 2 - ‖y i - yNext i‖ ^ 2 -
            ‖yPrev i - yNext i‖ ^ 2)) := by
          rw [Finset.mul_sum]
    _ = (τ / 2) *
        ((∑ i, ‖(y - yPrev) i‖ ^ 2) - (∑ i, ‖(y - yNext) i‖ ^ 2) -
          (∑ i, ‖(yPrev - yNext) i‖ ^ 2)) := by
          simp [Pi.sub_apply, Finset.sum_sub_distrib]

private theorem generated_sdcs_dual_one_step_inequality
    (P : Parameters) (hP : ValidParameters P) (init : InitialState S)
    (samples : ℕ → ι → ℕ → Ξ)
    (trace : S.GeneratedTrace P hP init samples)
    (k : ℕ) (hk : 1 ≤ k) (y : Stacked ι E) :
    stackedInner
        (S.primalNeighborDisagreement
          (S.outerExtrapolation P k (S.generatedState P hP init samples trace (k - 1))))
        (y - S.generatedY P hP init samples trace k) ≤
      (P.tau k / 2) *
        (S.stackedNormSq (y - S.generatedY P hP init samples trace (k - 1)) -
          S.stackedNormSq (y - S.generatedY P hP init samples trace k) -
            S.stackedNormSq
              (S.generatedY P hP init samples trace (k - 1) -
                S.generatedY P hP init samples trace k)) := by
  classical
  let stPrev := S.generatedState P hP init samples trace (k - 1)
  let xTilde := S.outerExtrapolation P k stPrev
  let v := S.primalNeighborDisagreement xTilde
  let yPrev := S.generatedY P hP init samples trace (k - 1)
  let yNext := S.generatedY P hP init samples trace k
  have hdual :=
    S.generated_dualUpdate_spec P hP init samples trace k hk
  have hτ : 0 < P.tau k := hdual.1
  have hupdate : yNext = yPrev + (P.tau k)⁻¹ • v := by
    simpa [yNext, yPrev, v, xTilde, stPrev, IsDualUpdate, generatedY, generatedState]
      using hdual.2
  have hEq :=
    S.dual_update_inner_eq_half_sq_dist_drop hτ v yPrev yNext y hupdate
  exact le_of_eq (by
    simpa [v, xTilde, stPrev, yPrev, yNext] using hEq)

/-- The weighted output `zhat_N` from Algorithm 8.7.

Source: `book/research/Source.json algorithm_spec.output`: `zhat_N=(sum theta_k)^-1
sum theta_k (xhat_k,y_k)`.
-/
def weightedPrimalAverage (P : Parameters) (hP : ValidParameters P) (init : InitialState S)
    (samples : ℕ → ι → ℕ → Ξ) (trace : S.GeneratedTrace P hP init samples)
    (N : ℕ) : Stacked ι E :=
  (∑ k ∈ Finset.range N, P.theta (k + 1))⁻¹ •
    (∑ k ∈ Finset.range N, P.theta (k + 1) •
      S.generatedXHat P hP init samples trace (k + 1))

/-- The Theorem 8.11 average `xhat_N = N^{-1} ∑_{k=1}^N xhat_k`.

Source: `book/research/Source.json algorithm_spec.output`: `xhat_N=1/N
sum_{k=1}^N xhat_k under theta_k=1`; `main_theorem.statement_math`: `where
\hat{x}_N=1/N sum_{k=1}^N \hat{x}_k`.
-/
def theorem811PrimalAverage (P : Parameters) (hP : ValidParameters P) (init : InitialState S)
    (samples : ℕ → ι → ℕ → Ξ) (trace : S.GeneratedTrace P hP init samples)
    (N : ℕ) : Stacked ι E :=
  ((N : ℝ)⁻¹) •
    (∑ k ∈ Finset.range N, S.generatedXHat P hP init samples trace (k + 1))

/-- Lemma 8.5 perturbation vector `s_hat`.

Source: `book/research/Source.json algorithm_spec.parameters.lemma_85_residual_vector`:
`\hat{s}:=\theta_N\mathcal{L}(\hat{x}_N-x_{N-1})+\theta_1\tau_1(y_N-y_0)`.
-/
def perturbationVector (P : Parameters) (hP : ValidParameters P) (init : InitialState S)
    (samples : ℕ → ι → ℕ → Ξ) (trace : S.GeneratedTrace P hP init samples)
    (N : ℕ) : Stacked ι E :=
  P.theta N • S.networkOperator
      (S.generatedXHat P hP init samples trace N -
        S.generatedX P hP init samples trace (N - 1)) +
    (P.theta 1 * P.tau 1) • (S.generatedY P hP init samples trace N - init.y0)

/-- The scaled perturbation `s_hat_N = (∑ θ_k)^{-1} s_hat` used in Theorem 8.11. -/
def scaledPerturbation (P : Parameters) (hP : ValidParameters P) (init : InitialState S)
    (samples : ℕ → ι → ℕ → Ξ) (trace : S.GeneratedTrace P hP init samples)
    (N : ℕ) : Stacked ι E :=
  (∑ k ∈ Finset.range N, P.theta (k + 1))⁻¹ •
    S.perturbationVector P hP init samples trace N

/-- The stochastic oracle error `δ_i^{t-1,k}` derived from the primitive oracle kernel.

Source: `book/research/Source.json key_lemmas.StochasticOracleErrorMomentFacts.proof[0]`:
`delta_i^{t-1,k}=f_i'(u_i^{t-1})-G_i(u_i^{t-1},xi_i^{t-1,k})`.
-/
def oracleError (i : ι) (u : E) (ξ : Ξ) : E :=
  S.subgradient i u - S.oracle i u ξ

theorem oracleError_mean_zero (i : ι) (u : E) :
    ∫ ξ, S.oracleError i u ξ ∂S.oracleMeasure = 0 := by
  letI : IsProbabilityMeasure S.oracleMeasure := S.oracleMeasure_isProbability
  calc
    ∫ ξ, S.oracleError i u ξ ∂S.oracleMeasure =
        ∫ ξ, S.subgradient i u - S.oracle i u ξ ∂S.oracleMeasure := by
          rfl
    _ = (∫ _ξ : Ξ, S.subgradient i u ∂S.oracleMeasure) -
        ∫ ξ, S.oracle i u ξ ∂S.oracleMeasure := by
          exact integral_sub (integrable_const (c := S.subgradient i u))
            (S.oracleIntegrable i u)
    _ = S.subgradient i u - S.subgradient i u := by
          rw [integral_const]
          simp [S.oracleUnbiased i u]
    _ = 0 := sub_self _

theorem oracleError_second_moment_bound (i : ι) (u : E) :
    ∫ ξ, ‖S.oracleError i u ξ‖ ^ 2 ∂S.oracleMeasure ≤ S.sigma ^ 2 := by
  have hpoint :
      (fun ξ => ‖S.oracleError i u ξ‖ ^ 2) =
        fun ξ => ‖S.oracle i u ξ - S.subgradient i u‖ ^ 2 := by
    funext ξ
    rw [oracleError]
    have hneg : S.subgradient i u - S.oracle i u ξ =
        -(S.oracle i u ξ - S.subgradient i u) := by
      abel
    rw [hneg, norm_neg]
  simpa [hpoint] using S.oracleVariance i u

/-- A stochastic oracle sample path model for Algorithm 8.8.

Source: `book/research/Source.json assumptions[StochasticOracleUnbiased]`,
`assumptions[StochasticOracleVariance]`: the oracle samples have law `P(ξ_i)`;
unbiasedness and bounded variance live on the oracle kernel in `Setup`.
-/
abbrev OracleRun (S : Setup ι E Ξ) (Ω : Type _) [MeasurableSpace Ω] :=
  SOptLib.CommonMarginalSampleRun Ω ℕ ι ℕ Ξ S.oracleMeasure

/-- Source stochastic independence, specialized to the actual generated trace whose
fresh sample is queried.

Source: `book/research/Source.json assumptions[StochasticQueryIndependence]`:
`ξ_it is independent of the search point u_t`; `source/FOML_complete.txt` lines
32533-32535 repeats that `ξ_it` is independent of the search point `u_t`.
-/
def GeneratedQueryIndependentCore (P : Parameters) (hP : ValidParameters P)
    (init : InitialState S) (run : OracleRun S Ω)
    (trace : ∀ ω, S.GeneratedTrace P hP init (run.samples ω)) : Prop :=
  ∀ (i : ι) (k t : ℕ),
    let query := fun ω =>
      S.generatedInnerQuery P hP init (run.samples ω) (trace ω) i k t
    let sample := fun ω => run.samples ω k i t
    Measurable query ∧ Measurable sample ∧
      ProbabilityTheory.IndepFun query sample run.law

theorem generated_query_cancellation_soptlib
    (P : Parameters) (hP : ValidParameters P) (init : InitialState S) (run : OracleRun S Ω)
    (trace : ∀ ω, S.GeneratedTrace P hP init (run.samples ω))
    (hIndependent : S.GeneratedQueryIndependentCore P hP init run trace)
    (i : ι) (k t : ℕ) (xStar : Stacked ι E) :
    ∫ ω,
      inner ℝ
        (xStar i -
          S.generatedInnerQuery P hP init (run.samples ω) (trace ω) i k t)
        (S.oracleError i
          (S.generatedInnerQuery P hP init (run.samples ω) (trace ω) i k t)
          (run.samples ω k i t))
      ∂run.law = 0 := by
  classical
  letI : IsProbabilityMeasure run.law := run.law_isProbability
  letI : IsFiniteMeasure run.law := ⟨by simp⟩
  letI : IsProbabilityMeasure S.oracleMeasure := S.oracleMeasure_isProbability
  letI : IsFiniteMeasure S.oracleMeasure := ⟨by simp⟩
  letI : SFinite S.oracleMeasure := inferInstance
  let query : Ω → E := fun ω =>
    S.generatedInnerQuery P hP init (run.samples ω) (trace ω) i k t
  let sample : Ω → Ξ := fun ω => run.samples ω k i t
  let residual : E → Ξ → E := fun q ξ => S.oracleError i q ξ
  let direction : E → E := fun q => xStar i - q
  have hQI := hIndependent i k t
  have hquery : Measurable query := hQI.1
  have hsample : Measurable sample := hQI.2.1
  have hindep : ProbabilityTheory.IndepFun query sample run.law := hQI.2.2
  have hdist : Measure.map sample run.law = S.oracleMeasure := by
    simpa [sample] using run.sampleLaw k i t
  have hres_meas : Measurable (fun p : E × Ξ => residual p.1 p.2) := by
    simpa [residual, oracleError] using S.oracleErrorKernelMeasurable i
  have hdir_meas : Measurable direction := by
    simpa [direction] using (continuous_const.sub continuous_id).measurable
  have hfixed_int : ∀ q : E, Integrable (fun ξ => residual q ξ) S.oracleMeasure := by
    intro q
    simpa [residual, oracleError] using
      (integrable_const (c := S.subgradient i q)).sub (S.oracleIntegrable i q)
  have hfixed_zero : ∀ q : E, ∫ ξ, residual q ξ ∂S.oracleMeasure = 0 := by
    intro q
    simpa [residual] using S.oracleError_mean_zero i q
  have hzero :=
    randomQuery_inner_oracleResidual_integral_eq_zero_of_fixed_zero
      (P := run.law) (ν := S.oracleMeasure) (query := query) (sample := sample)
      (residual := residual) (d := direction)
      hres_meas hdir_meas hquery hsample hindep hdist hfixed_int hfixed_zero
  simpa [query, sample, residual, direction] using hzero

theorem generated_query_cancellation
    (P : Parameters) (hP : ValidParameters P) (init : InitialState S) (run : OracleRun S Ω)
    (trace : ∀ ω, S.GeneratedTrace P hP init (run.samples ω))
    (hIndependent : S.GeneratedQueryIndependentCore P hP init run trace)
    (i : ι) (k t : ℕ) (xStar : Stacked ι E) :
    ∫ ω,
      inner ℝ
        (S.oracleError i
          (S.generatedInnerQuery P hP init (run.samples ω) (trace ω) i k t)
          (run.samples ω k i t))
        (xStar i -
          S.generatedInnerQuery P hP init (run.samples ω) (trace ω) i k t)
      ∂run.law = 0 := by
  have hzero :=
    S.generated_query_cancellation_soptlib P hP init run trace hIndependent i k t xStar
  simpa [real_inner_comm] using hzero

private theorem generated_oracle_error_sq_integral_le
    (P : Parameters) (hP : ValidParameters P) (init : InitialState S) (run : OracleRun S Ω)
    (trace : ∀ ω, S.GeneratedTrace P hP init (run.samples ω))
    (hIndependent : S.GeneratedQueryIndependentCore P hP init run trace)
    (i : ι) (k t : ℕ) :
    ∫ ω,
      ‖S.oracleError i
        (S.generatedInnerQuery P hP init (run.samples ω) (trace ω) i k t)
        (run.samples ω k i t)‖ ^ 2 ∂run.law ≤ S.sigma ^ 2 := by
  classical
  letI : IsProbabilityMeasure run.law := run.law_isProbability
  letI : IsProbabilityMeasure S.oracleMeasure := S.oracleMeasure_isProbability
  let query : Ω → E := fun ω =>
    S.generatedInnerQuery P hP init (run.samples ω) (trace ω) i k t
  let sample : Ω → Ξ := fun ω => run.samples ω k i t
  have hQI := hIndependent i k t
  have hquery : Measurable query := hQI.1
  have hsample : Measurable sample := hQI.2.1
  have hindep : ProbabilityTheory.IndepFun query sample run.law := hQI.2.2
  have hdist : Measure.map sample run.law = S.oracleMeasure := by
    simpa [sample] using run.sampleLaw k i t
  have hres_meas :
      Measurable (fun p : E × Ξ => S.oracle i p.1 p.2 - S.subgradient i p.1) := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (S.oracleErrorKernelMeasurable i).neg
  have hsq :
      ∫ ω, ‖S.oracle i (query ω) (sample ω) - S.subgradient i (query ω)‖ ^ 2
          ∂run.law ≤ S.sigma ^ 2 := by
    exact
      integral_sq_oracleResidual_le_of_indep_fixed_variance
        (P := run.law) (ν := S.oracleMeasure) (query := query) (sample := sample)
        (G := fun q ξ => S.oracle i q ξ) (target := fun q => S.subgradient i q)
        (σ2 := S.sigma ^ 2) hres_meas hquery hsample hindep hdist
        (sq_nonneg S.sigma) (fun q => S.oracleVariance i q)
  have hpoint :
      (fun ω =>
        ‖S.oracleError i
          (S.generatedInnerQuery P hP init (run.samples ω) (trace ω) i k t)
          (run.samples ω k i t)‖ ^ 2) =
        fun ω => ‖S.oracle i (query ω) (sample ω) - S.subgradient i (query ω)‖ ^ 2 := by
    funext ω
    simp [query, sample, oracleError, norm_sub_rev]
  simpa [hpoint] using hsq

private theorem generated_oracle_error_sq_integrable
    (P : Parameters) (hP : ValidParameters P) (init : InitialState S) (run : OracleRun S Ω)
    (trace : ∀ ω, S.GeneratedTrace P hP init (run.samples ω))
    (hIndependent : S.GeneratedQueryIndependentCore P hP init run trace)
    (i : ι) (k t : ℕ) :
    Integrable
      (fun ω =>
        ‖S.oracleError i
          (S.generatedInnerQuery P hP init (run.samples ω) (trace ω) i k t)
          (run.samples ω k i t)‖ ^ 2) run.law := by
  classical
  letI : IsProbabilityMeasure run.law := run.law_isProbability
  letI : IsFiniteMeasure run.law := ⟨by simp⟩
  let query : Ω → E := fun ω =>
    S.generatedInnerQuery P hP init (run.samples ω) (trace ω) i k t
  let sample : Ω → Ξ := fun ω => run.samples ω k i t
  have hQI := hIndependent i k t
  have hquery : Measurable query := hQI.1
  have hsample : Measurable sample := hQI.2.1
  have hindep : ProbabilityTheory.IndepFun query sample run.law := hQI.2.2
  have hdist : Measure.map sample run.law = S.oracleMeasure := by
    simpa [sample] using run.sampleLaw k i t
  have hres_meas :
      Measurable (fun p : E × Ξ => S.oracle i p.1 p.2 - S.subgradient i p.1) := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (S.oracleErrorKernelMeasurable i).neg
  have hsq :
      Integrable
        (fun ω => ‖S.oracle i (query ω) (sample ω) - S.subgradient i (query ω)‖ ^ 2)
        run.law := by
    exact
      integrable_sq_oracleResidual_of_indep_fixed_variance_bound
        (P := run.law) (ν := S.oracleMeasure) (query := query) (sample := sample)
        (G := fun q ξ => S.oracle i q ξ) (target := fun q => S.subgradient i q)
        (σ2 := S.sigma ^ 2) hres_meas hquery hsample hindep hdist
        (sq_nonneg S.sigma) (fun q => S.oracleVarianceIntegrable i q)
        (fun q => S.oracleVariance i q)
  have hpoint :
      (fun ω =>
        ‖S.oracleError i
          (S.generatedInnerQuery P hP init (run.samples ω) (trace ω) i k t)
          (run.samples ω k i t)‖ ^ 2) =
        fun ω => ‖S.oracle i (query ω) (sample ω) - S.subgradient i (query ω)‖ ^ 2 := by
    funext ω
    simp [query, sample, oracleError, norm_sub_rev]
  simpa [hpoint] using hsq

/-- Finite-window integrability of the oracle-noise square term in the Young
majorant used by the generated inner CS recursion.

This closes the stochastic-oracle half of the current Young-window leaf.  The
remaining obstruction is not the finite sum or the oracle moment; it is the
prox/Bregman part of the same majorant. -/
private theorem generated_oracle_error_young_noise_window_integrable
    (P : Parameters) (hP : ValidParameters P) (init : InitialState S) (run : OracleRun S Ω)
    (trace : ∀ ω, S.GeneratedTrace P hP init (run.samples ω))
    (hIndependent : S.GeneratedQueryIndependentCore P hP init run trace)
    (i : ι) (k : ℕ) (s : Finset ℕ) (denom : ℕ → ℝ) :
    Integrable
      (fun ω =>
        Finset.sum s
          (fun r =>
            csLambda r *
              ((S.M +
                    ‖S.oracleError i
                      (S.generatedInnerQuery P hP init (run.samples ω) (trace ω)
                        i k (r - 1))
                      (run.samples ω k i (r - 1))‖) ^ 2 / denom r)))
      run.law := by
  classical
  letI : IsProbabilityMeasure run.law := run.law_isProbability
  letI : IsFiniteMeasure run.law := inferInstance
  refine MeasureTheory.integrable_finset_sum (μ := run.law) (s := s)
    (f := fun r ω =>
      csLambda r *
        ((S.M +
              ‖S.oracleError i
                (S.generatedInnerQuery P hP init (run.samples ω) (trace ω)
                  i k (r - 1))
                (run.samples ω k i (r - 1))‖) ^ 2 / denom r)) ?_
  intro r _hr
  let δ : Ω → E := fun ω =>
    S.oracleError i
      (S.generatedInnerQuery P hP init (run.samples ω) (trace ω) i k (r - 1))
      (run.samples ω k i (r - 1))
  have hδ_meas : Measurable δ := by
    let query : Ω → E := fun ω =>
      S.generatedInnerQuery P hP init (run.samples ω) (trace ω) i k (r - 1)
    let sample : Ω → Ξ := fun ω => run.samples ω k i (r - 1)
    have hQI := hIndependent i k (r - 1)
    have hquery : Measurable query := hQI.1
    have hsample : Measurable sample := hQI.2.1
    have hpair : Measurable (fun ω => (query ω, sample ω)) :=
      hquery.prodMk hsample
    simpa [δ, query, sample] using (S.oracleErrorKernelMeasurable i).comp hpair
  have hδ_sq :
      Integrable (fun ω => ‖δ ω‖ ^ 2) run.law := by
    simpa [δ] using
      S.generated_oracle_error_sq_integrable P hP init run trace hIndependent
        i k (r - 1)
  have hdom :
      Integrable (fun ω => 2 * S.M ^ 2 + 2 * ‖δ ω‖ ^ 2) run.law := by
    exact (integrable_const (2 * S.M ^ 2)).add (hδ_sq.const_mul 2)
  have htarget_aesm :
      AEStronglyMeasurable (fun ω => (S.M + ‖δ ω‖) ^ 2) run.law :=
    ((measurable_const.add hδ_meas.norm).pow_const 2).aestronglyMeasurable
  have hyoung :
      Integrable (fun ω => (S.M + ‖δ ω‖) ^ 2) run.law := by
    refine Integrable.mono' hdom htarget_aesm ?_
    refine Filter.Eventually.of_forall ?_
    intro ω
    have hle : (S.M + ‖δ ω‖) ^ 2 ≤ 2 * S.M ^ 2 + 2 * ‖δ ω‖ ^ 2 := by
      nlinarith [sq_nonneg (S.M - ‖δ ω‖)]
    simpa [Real.norm_of_nonneg (sq_nonneg _)] using hle
  simpa [δ, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    (hyoung.const_mul (csLambda r * (denom r)⁻¹))

/-- Integrability half of the generated stochastic-error linear term, reduced to
the exact finite-horizon query-direction L2 premise.

The oracle-error square integrability is already a consequence of the source
fresh-sample independence and variance assumptions.  What remains, and what
`GeneratedProcessCore` does not provide, is the L2 moment of
`x_i^* - u_i^{t-1,k}` for the generated inner query. -/
private theorem generated_oracle_error_inner_integrable_of_direction_l2
    (P : Parameters) (hP : ValidParameters P) (init : InitialState S) (run : OracleRun S Ω)
    (trace : ∀ ω, S.GeneratedTrace P hP init (run.samples ω))
    (hIndependent : S.GeneratedQueryIndependentCore P hP init run trace)
    (i : ι) (k t : ℕ) (xStar : Stacked ι E)
    (hDirectionSq :
      Integrable
        (fun ω =>
          ‖xStar i -
            S.generatedInnerQuery P hP init (run.samples ω) (trace ω) i k t‖ ^ 2)
        run.law) :
    Integrable
      (fun ω =>
        inner ℝ
          (S.oracleError i
            (S.generatedInnerQuery P hP init (run.samples ω) (trace ω) i k t)
            (run.samples ω k i t))
          (xStar i -
            S.generatedInnerQuery P hP init (run.samples ω) (trace ω) i k t))
      run.law := by
  classical
  let query : Ω → E := fun ω =>
    S.generatedInnerQuery P hP init (run.samples ω) (trace ω) i k t
  let sample : Ω → Ξ := fun ω => run.samples ω k i t
  have hQI := hIndependent i k t
  have hquery : Measurable query := hQI.1
  have hsample : Measurable sample := hQI.2.1
  have hres_meas :
      Measurable (fun ω => S.oracleError i (query ω) (sample ω)) := by
    have hpair : Measurable (fun ω => (query ω, sample ω)) :=
      hquery.prodMk hsample
    exact (S.oracleErrorKernelMeasurable i).comp hpair
  have hdir_meas :
      Measurable (fun ω => xStar i - query ω) :=
    measurable_const.sub hquery
  have hres_sq :
      Integrable
        (fun ω => ‖S.oracleError i (query ω) (sample ω)‖ ^ 2) run.law := by
    simpa [query, sample] using
      S.generated_oracle_error_sq_integrable P hP init run trace hIndependent i k t
  exact
    integrable_inner_of_integrable_sq_norm
      hres_meas.aestronglyMeasurable hdir_meas.aestronglyMeasurable
      hres_sq (by simpa [query] using hDirectionSq)

/-- Expected objective residual for the actual averaged generated iterate.

Source: `book/research/Source.json main_theorem.measure`: `Expected objective
residual E[F(xhat_N)-F(x*)]`; `main_theorem.statement_math`: (8.3.68) bounds
`E[F(\hat{x}_N)-F(x^*)]` for `\hat{x}_N=1/N sum_{k=1}^N \hat{x}_k`.
-/
def expectedObjectiveResidual (P : Parameters) (hP : ValidParameters P)
    (init : InitialState S) (run : OracleRun S Ω)
    (trace : ∀ ω, S.GeneratedTrace P hP init (run.samples ω))
    (xStar : Stacked ι E) (N : ℕ) : ℝ :=
  ∫ ω,
    S.objectiveResidual
      (S.theorem811PrimalAverage P hP init (run.samples ω) (trace ω) N) xStar
  ∂run.law

/-- Expected consensus residual for the actual averaged generated iterate.

Source: `book/research/Source.json main_theorem.measure`: `Expected consensus
residual E[||L xhat_N||]`; `main_theorem.statement_math`: (8.3.69) bounds
`E[||L \hat{x}_N||]` for `\hat{x}_N=1/N sum_{k=1}^N \hat{x}_k`.
-/
def expectedConsensusResidual (P : Parameters) (hP : ValidParameters P)
    (init : InitialState S) (run : OracleRun S Ω)
    (trace : ∀ ω, S.GeneratedTrace P hP init (run.samples ω))
    (N : ℕ) : ℝ :=
  ∫ ω,
    S.consensusResidual
      (S.theorem811PrimalAverage P hP init (run.samples ω) (trace ω) N) ∂run.law

/-- The exact general parameter conditions (8.3.29)-(8.3.33) used by Lemma 8.5.

Source: `book/research/Source.json algorithm_spec.parameters.general_parameter_condition_29`:
`\theta_k ((T_k+1)(T_k+2)\eta_k)/(T_k(T_k+3)) <= ...`; entries
`general_parameter_condition_30` through `general_parameter_condition_33` state
`\alpha_k\theta_k=\theta_{k-1}`, `\theta_k\tau_k=\theta_1\tau_1`,
`\alpha_k||L||^2 <= \eta_{k-1}\tau_k`, and
`\theta_N||L||^2 <= \theta_1\tau_1\eta_N`.
-/
def generalParameterConditions (P : Parameters) (N : ℕ) : Prop :=
  (∀ k, 2 ≤ k → k ≤ N →
    P.theta k * (((P.innerSteps k : ℝ) + 1) * ((P.innerSteps k : ℝ) + 2) * P.eta k /
      ((P.innerSteps k : ℝ) * ((P.innerSteps k : ℝ) + 3))) ≤
    P.theta (k - 1) *
      ((((P.innerSteps (k - 1) : ℝ) + 1) * ((P.innerSteps (k - 1) : ℝ) + 2) *
        P.eta (k - 1)) /
      ((P.innerSteps (k - 1) : ℝ) * ((P.innerSteps (k - 1) : ℝ) + 3)))) ∧
  (∀ k, 2 ≤ k → k ≤ N → P.alpha k * P.theta k = P.theta (k - 1)) ∧
  (∀ k, 2 ≤ k → k ≤ N → P.theta k * P.tau k = P.theta 1 * P.tau 1) ∧
  (∀ k, 2 ≤ k → k ≤ N → P.alpha k * S.networkOperatorNorm ^ 2 ≤
    P.eta (k - 1) * P.tau k) ∧
  (P.theta N * S.networkOperatorNorm ^ 2 ≤ P.theta 1 * P.tau 1 * P.eta N)

private theorem generalParameterConditions_negative_theta_sum_counterexample
    (N : ℕ) (hN : 1 ≤ N) :
    ∃ P : Parameters,
      ValidParameters P ∧
        S.generalParameterConditions P N ∧
        (∀ k, 1 ≤ k → k ≤ N → 0 < P.innerSteps k ∧ 0 < P.eta k) ∧
        (∑ k ∈ Finset.range N, P.theta (k + 1)) < 0 := by
  classical
  let P : Parameters :=
    { alpha := fun _ => 1
      theta := fun _ => -1
      eta := fun _ => 1
      tau := fun _ => S.networkOperatorNorm ^ 2
      innerSteps := fun _ => 1 }
  refine ⟨P, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro k
      simp [P]
    · intro k
      simp [P, sq_nonneg S.networkOperatorNorm]
    · intro k
      simp [P]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro k hk_two hk_le
      norm_num [P]
    · intro k hk_two hk_le
      simp [P]
    · intro k hk_two hk_le
      simp [P]
    · intro k hk_two hk_le
      simp [P]
    · simp [P]
  · intro k hk hkN
    simp [P]
  · have hNpos : (0 : ℝ) < N := by
      exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hN)
    simpa [P] using (neg_neg_of_pos hNpos)

/-- Internal denominator bridge for the printed `T_k` expression in (8.3.67).

The hypothesis `0 < S.networkOperatorNorm` is not asserted by the checked source as
a Theorem 8.11 assumption; endpoint theorems that rely on it are therefore named
as source-boundary corrected statements.
-/
theorem theorem811_innerSteps_denominator_positive_of_network_norm_pos
    (Dtilde : ℝ) (hDtilde : 0 < Dtilde)
    (hL : 0 < S.networkOperatorNorm) :
    0 < S.networkOperatorNorm ^ 2 * Dtilde := by
  positivity

private theorem theorem811_raw_inner_steps_arg_pos
    (N : ℕ) (Dtilde : ℝ)
    (hSchedule : S.Theorem811ScheduleWellDefined N Dtilde)
    (hN : 1 ≤ N) :
    0 <
      ((Fintype.card ι : ℝ) * (S.M ^ 2 + S.sigma ^ 2) * (N : ℝ) /
        (S.networkOperatorNorm ^ 2 * Dtilde)) := by
  have hCard : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast S.agent_count_pos
  have hM_sq : 0 < S.M ^ 2 := sq_pos_of_pos S.M_pos
  have hSigma_sq : 0 ≤ S.sigma ^ 2 := sq_nonneg S.sigma
  have hMoment : 0 < S.M ^ 2 + S.sigma ^ 2 :=
    add_pos_of_pos_of_nonneg hM_sq hSigma_sq
  have hN_real : 0 < (N : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hNum :
      0 < (Fintype.card ι : ℝ) * (S.M ^ 2 + S.sigma ^ 2) * (N : ℝ) :=
    mul_pos (mul_pos hCard hMoment) hN_real
  have hDen : 0 < S.networkOperatorNorm ^ 2 * Dtilde :=
    S.theorem811_innerSteps_denominator_positive_of_network_norm_pos Dtilde hSchedule.1 hSchedule.2
  exact div_pos hNum hDen

private theorem theorem811_innerSteps_lower_bound
    (N : ℕ) (Dtilde : ℝ)
    (hSchedule : S.Theorem811ScheduleWellDefined N Dtilde)
    (k : ℕ) :
    ((Fintype.card ι : ℝ) * (S.M ^ 2 + S.sigma ^ 2) * (N : ℝ) /
      (S.networkOperatorNorm ^ 2 * Dtilde)) ≤
      ((S.theorem811Parameters N Dtilde hSchedule).innerSteps k : ℝ) := by
  dsimp [theorem811Parameters, theorem811InnerSteps, theorem811InnerStepsRaw]
  exact Nat.le_ceil _

private theorem theorem811_innerSteps_add_three_lower_bound
    (N : ℕ) (Dtilde : ℝ)
    (hSchedule : S.Theorem811ScheduleWellDefined N Dtilde)
    (k : ℕ) :
    ((Fintype.card ι : ℝ) * (S.M ^ 2 + S.sigma ^ 2) * (N : ℝ) /
      (S.networkOperatorNorm ^ 2 * Dtilde)) ≤
      ((S.theorem811Parameters N Dtilde hSchedule).innerSteps k : ℝ) + 3 := by
  have hT := S.theorem811_innerSteps_lower_bound N Dtilde hSchedule k
  nlinarith

theorem theorem811_innerSteps_positive_of_schedule_wellDefined
    (N : ℕ) (Dtilde : ℝ)
    (hSchedule : S.Theorem811ScheduleWellDefined N Dtilde)
    (hN : 1 ≤ N)
    (k : ℕ) (hk_pos : 1 ≤ k) (hk_le : k ≤ N) :
    1 ≤ (S.theorem811Parameters N Dtilde hSchedule).innerSteps k := by
  have _hk_pos : 1 ≤ k := hk_pos
  have _hk_le : k ≤ N := hk_le
  dsimp [theorem811Parameters, theorem811InnerSteps, theorem811InnerStepsRaw]
  exact Nat.ceil_pos.2 (S.theorem811_raw_inner_steps_arg_pos N Dtilde hSchedule hN)

/-- The Theorem 8.11 schedule has positive `τ_k`, so its dual update denominator is
defined in the paper sense.

Source: `book/research/Source.json algorithm_spec.parameters.theorem_811_schedule`:
`τ_k=||L||`; the corrected schedule boundary records the missing denominator fact
`0 < ||L||`.
-/
theorem theorem811_tau_positive
    (N : ℕ) (Dtilde : ℝ)
    (hSchedule : S.Theorem811ScheduleWellDefined N Dtilde) (k : ℕ) :
    0 < (S.theorem811Parameters N Dtilde hSchedule).tau k := by
  simpa [theorem811Parameters] using hSchedule.2

/-- The Theorem 8.11 schedule supplies the denominator guards required by the
corrected raw-terminal Lemma 8.5 bridge.

The source formulas in Proposition 8.7 and Lemma 8.5 divide by `T_k` and
`eta_k`; this theorem derives those guards from the guarded schedule (8.3.67)
rather than storing them as hidden setup assumptions.
-/
theorem theorem811_general_parameter_denominators_pos
    (N : ℕ) (hN : 1 ≤ N) (Dtilde : ℝ)
    (hSchedule : S.Theorem811ScheduleWellDefined N Dtilde) :
    ∀ k, 1 ≤ k → k ≤ N →
      0 < (S.theorem811Parameters N Dtilde hSchedule).innerSteps k ∧
        0 < (S.theorem811Parameters N Dtilde hSchedule).eta k := by
  intro k hk_pos hk_le
  constructor
  · exact
      S.theorem811_innerSteps_positive_of_schedule_wellDefined
        N Dtilde hSchedule hN k hk_pos hk_le
  · simpa [theorem811Parameters] using
      mul_pos (by norm_num : (0 : ℝ) < 2) hSchedule.2

/-- The Theorem 8.11 schedule has nonnegative Lemma 8.5 output weights.

This discharges the Jensen/weighted-output side condition locally from
`theta_k = 1` in (8.3.67), instead of adding theta nonnegativity to the general
setup or pretending it follows from (8.3.29)-(8.3.33).
-/
theorem theorem811_theta_nonneg
    (N : ℕ) (Dtilde : ℝ)
    (hSchedule : S.Theorem811ScheduleWellDefined N Dtilde) :
    ∀ k, 1 ≤ k → k ≤ N →
      0 ≤ (S.theorem811Parameters N Dtilde hSchedule).theta k := by
  intro k _hk_pos _hk_le
  simp [theorem811Parameters]

/-- The Theorem 8.11 schedule has the extra residual-coefficient guard needed
by the corrected Lemma 8.5 residual bridge.

Source: (8.3.67) sets `theta_k = 1`.  This theorem is intentionally schedule
local; the general parameter conditions (8.3.29)-(8.3.33) do not imply
`1 <= theta_N`.
-/
theorem theorem811_theta_ge_one
    (N : ℕ) (Dtilde : ℝ)
    (hSchedule : S.Theorem811ScheduleWellDefined N Dtilde) :
    ∀ k, 1 ≤ k → k ≤ N →
      1 ≤ (S.theorem811Parameters N Dtilde hSchedule).theta k := by
  intro k _hk_pos _hk_le
  simp [theorem811Parameters]

/-- The Theorem 8.11 schedule has positive total Lemma 8.5 output weight.

Source: (8.3.67) sets `theta_k = 1`, so `∑_{k=1}^N theta_k = N > 0` under
the Theorem 8.11 horizon assumption.
-/
theorem theorem811_theta_sum_pos
    (N : ℕ) (hN : 1 ≤ N) (Dtilde : ℝ)
    (hSchedule : S.Theorem811ScheduleWellDefined N Dtilde) :
    0 < ∑ k ∈ Finset.range N,
      (S.theorem811Parameters N Dtilde hSchedule).theta (k + 1) := by
  have hNpos : (0 : ℝ) < N := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hN)
  simpa [theorem811Parameters] using hNpos

/-- Pointwise Theorem 8.11 perturbation expansion used in the consensus residual.

Under the constant schedule (8.3.67), the scaled Lemma 8.5 residual vector is
bounded by the network norm times the terminal primal and dual residuals.  This
is the pathwise triangle-inequality step immediately preceding the expectation
and Jensen estimates in the proof of Theorem 8.11.
-/
private theorem theorem811_scaledPerturbation_norm_le
    (init : InitialState S) (N : ℕ) (hN : 1 ≤ N) (Dtilde : ℝ)
    (hSchedule : S.Theorem811ScheduleWellDefined N Dtilde)
    (samples : ℕ → ι → ℕ → Ξ)
    (trace :
      S.GeneratedTrace (S.theorem811Parameters N Dtilde hSchedule)
        (S.theorem811Parameters_valid N Dtilde hSchedule) init samples)
    (yStar : Stacked ι E) :
    let P := S.theorem811Parameters N Dtilde hSchedule
    let hP := S.theorem811Parameters_valid N Dtilde hSchedule
    (fun x => ‖WithLp.toLp 2 x‖) (S.scaledPerturbation P hP init samples trace N) ≤
      (S.networkOperatorNorm / (N : ℝ)) *
        ((fun x => ‖WithLp.toLp 2 x‖)
            (S.generatedXHat P hP init samples trace N -
              S.generatedX P hP init samples trace (N - 1)) +
          (fun x => ‖WithLp.toLp 2 x‖) (yStar - S.generatedY P hP init samples trace N) +
          (fun x => ‖WithLp.toLp 2 x‖) (yStar - init.y0)) := by
  simpa [scaledPerturbation, perturbationVector, theorem811Parameters, div_eq_mul_inv,
    mul_comm, mul_left_comm, mul_assoc] using
      (SOptLib.seminorm_smul_map_add_endpoint_sub_le
        ((normSeminorm ℝ (WithLp 2 (Stacked ι E))).comp
          (WithLp.linearEquiv 2 ℝ (Stacked ι E)).symm.toLinearMap)
        ((normSeminorm ℝ (WithLp 2 (Stacked ι E))).comp
          (WithLp.linearEquiv 2 ℝ (Stacked ι E)).symm.toLinearMap)
        S.networkOperator ((N : ℝ)⁻¹) S.networkOperatorNorm
        (S.generatedXHat (S.theorem811Parameters N Dtilde hSchedule)
            (S.theorem811Parameters_valid N Dtilde hSchedule) init samples trace N -
          S.generatedX (S.theorem811Parameters N Dtilde hSchedule)
            (S.theorem811Parameters_valid N Dtilde hSchedule) init samples trace (N - 1))
        (S.generatedY (S.theorem811Parameters N Dtilde hSchedule)
          (S.theorem811Parameters_valid N Dtilde hSchedule) init samples trace N)
        init.y0 yStar
        (inv_nonneg.mpr (by positivity)) (le_of_lt hSchedule.2)
        (stacked_network_operator_norm_le S _))

theorem theorem811_schedule_satisfies_general_conditions_sourceBoundaryCorrected
    (N : ℕ) (hN : 1 ≤ N) (Dtilde : ℝ)
    (hSchedule : S.Theorem811ScheduleWellDefined N Dtilde) :
    S.generalParameterConditions (S.theorem811Parameters N Dtilde hSchedule) N := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k hk_two hk_le
    simp [generalParameterConditions, theorem811Parameters]
  · intro k hk_two hk_le
    simp [theorem811Parameters]
  · intro k hk_two hk_le
    simp [theorem811Parameters]
  · intro k hk_two hk_le
    dsimp [theorem811Parameters]
    nlinarith [sq_nonneg S.networkOperatorNorm]
  · dsimp [theorem811Parameters]
    nlinarith [sq_nonneg S.networkOperatorNorm]

private theorem theorem811_variance_budget_scalar_le
    (N : ℕ) (hN : 1 ≤ N) (Dtilde : ℝ)
    (hSchedule : S.Theorem811ScheduleWellDefined N Dtilde)
    (k : ℕ) :
    (8 * (Fintype.card ι : ℝ) * (S.M ^ 2 + S.sigma ^ 2) /
      ((((S.theorem811Parameters N Dtilde hSchedule).innerSteps k : ℝ) + 3) *
        (2 * S.networkOperatorNorm))) ≤
      (S.networkOperatorNorm / (N : ℝ)) * (4 * Dtilde) := by
  simpa [mul_assoc] using
    (eight_mul_div_two_mul_le_four_mul_of_scaled_denominator_lower_bound
      (A := (Fintype.card ι : ℝ) * (S.M ^ 2 + S.sigma ^ 2))
      (N := (N : ℝ)) (L := S.networkOperatorNorm) (D := Dtilde)
      (T := ((S.theorem811Parameters N Dtilde hSchedule).innerSteps k : ℝ) + 3)
      (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN))
      hSchedule.2 hSchedule.1 (by positivity)
      (by simpa [mul_assoc] using
        S.theorem811_innerSteps_add_three_lower_bound N Dtilde hSchedule k))

private theorem theorem811_initial_prox_coefficient_le
    (N : ℕ) (hN : 1 ≤ N) (Dtilde : ℝ)
    (hSchedule : S.Theorem811ScheduleWellDefined N Dtilde) :
    let P := S.theorem811Parameters N Dtilde hSchedule
    ((((P.innerSteps 1 : ℝ) + 1) * ((P.innerSteps 1 : ℝ) + 2) *
      P.theta 1 * P.eta 1) /
      ((P.innerSteps 1 : ℝ) * ((P.innerSteps 1 : ℝ) + 3))) ≤
      3 * S.networkOperatorNorm := by
  dsimp [theorem811Parameters]
  let T : ℝ := (S.theorem811InnerSteps N Dtilde hSchedule : ℝ)
  let L : ℝ := S.networkOperatorNorm
  have hT_ge_one : 1 ≤ T := by
    dsimp [T]
    exact_mod_cast
      S.theorem811_innerSteps_positive_of_schedule_wellDefined N Dtilde hSchedule hN
        1 (by norm_num) hN
  have hRatio : ((T + 1) * (T + 2)) / (T * (T + 3)) ≤ 3 / 2 :=
    (add_one_mul_add_two_div_mul_add_three_eq_and_le_three_halves T hT_ge_one).2
  have hL_pos : 0 < L := by
    simpa [L] using hSchedule.2
  change ((T + 1) * (T + 2) * 1 * (2 * L)) / (T * (T + 3)) ≤ 3 * L
  calc
    ((T + 1) * (T + 2) * 1 * (2 * L)) / (T * (T + 3)) =
        (2 * L) * (((T + 1) * (T + 2)) / (T * (T + 3))) := by ring
    _ ≤ (2 * L) * (3 / 2) :=
      mul_le_mul_of_nonneg_left hRatio (mul_nonneg (by norm_num) hL_pos.le)
    _ = 3 * L := by ring

/-- Initial Bregman coefficient produced by the raw CS telescope alone. -/
def generalSDCSRawPrimalTelescopeInitialCoeff (P : Parameters) (k : ℕ) : ℝ :=
  (2 * P.eta k) /
    ((P.innerSteps k : ℝ) * ((P.innerSteps k : ℝ) + 3))

/-- Initial Bregman coefficient after expanding `Φ^k` in Lemma 8.5.
With the source weights `β_t=t/2`, this is
`η_k + 2η_k/(T_k(T_k+3))`, equal for positive `T_k` to
`((T_k+1)(T_k+2)η_k)/(T_k(T_k+3))` on printed p. 560.
-/
def generalSDCSRawPrimalInitialCoeff (P : Parameters) (k : ℕ) : ℝ :=
  P.eta k + generalSDCSRawPrimalTelescopeInitialCoeff P k

private theorem generalSDCSRawPrimalInitialCoeff_mul_eq_phi_plus_telescope
    (P : Parameters) (k : ℕ) (v : ℝ) :
    generalSDCSRawPrimalInitialCoeff P k * v =
      P.eta k * v + generalSDCSRawPrimalTelescopeInitialCoeff P k * v := by
  unfold generalSDCSRawPrimalInitialCoeff
  ring

/-- Bregman coefficient multiplying the whole difference on printed p. 560:
`((T_k+1)(T_k+2)η_k)/(T_k(T_k+3))`.
-/
def generalSDCSRawPrimalTerminalCoeff (P : Parameters) (k : ℕ) : ℝ :=
  (((P.innerSteps k : ℝ) + 1) * ((P.innerSteps k : ℝ) + 2) * P.eta k) /
    ((P.innerSteps k : ℝ) * ((P.innerSteps k : ℝ) + 3))

private theorem generalSDCSRawPrimalInitialCoeff_eq_terminalCoeff_of_innerSteps_pos
    (P : Parameters) {k : ℕ} (hT : 0 < P.innerSteps k) :
    generalSDCSRawPrimalInitialCoeff P k = generalSDCSRawPrimalTerminalCoeff P k := by
  unfold generalSDCSRawPrimalInitialCoeff generalSDCSRawPrimalTelescopeInitialCoeff
    generalSDCSRawPrimalTerminalCoeff
  have hT_ne : ((P.innerSteps k : ℝ) ≠ 0) := by
    exact_mod_cast (ne_of_gt hT)
  have hT_three_ne : ((P.innerSteps k : ℝ) + 3 ≠ 0) := by
    have hT_pos : 0 < (P.innerSteps k : ℝ) := by
      exact_mod_cast hT
    nlinarith
  field_simp [hT_ne, hT_three_ne]
  ring

private theorem generalSDCSRawPrimalTelescope_with_phi_initial_le
    (P : Parameters) (k : ℕ) (lhs v0 vT : ℝ)
    (h :
      lhs ≤
        generalSDCSRawPrimalTelescopeInitialCoeff P k * v0 -
          generalSDCSRawPrimalTerminalCoeff P k * vT) :
    P.eta k * v0 + lhs ≤
      generalSDCSRawPrimalInitialCoeff P k * v0 -
        generalSDCSRawPrimalTerminalCoeff P k * vT := by
  rw [generalSDCSRawPrimalInitialCoeff_mul_eq_phi_plus_telescope]
  linarith

private theorem generated_inner_bregman_raw_terminal_bound
    (P : Parameters) (hP : ValidParameters P) (init : InitialState S)
    (samples : ℕ → ι → ℕ → Ξ)
    (trace : S.GeneratedTrace P hP init samples)
    (i : ι) (k : ℕ) (hk : 1 ≤ k) (u : E) (hu : u ∈ S.feasible i)
    (hT : 0 < P.innerSteps k) :
    let centerState := S.generatedState P hP init samples trace (k - 1)
    let T := P.innerSteps k
    let coeff := 2 / ((T : ℝ) * ((T : ℝ) + 3))
    coeff *
        (∑ t ∈ Finset.range T, csLambda (t + 1) *
          ((P.eta k * csBeta (t + 1)) *
              S.localProx i (S.generatedInnerQuery P hP init samples trace i k t) u -
            (P.eta k + P.eta k * csBeta (t + 1)) *
              S.localProx i (S.generatedInnerQuery P hP init samples trace i k (t + 1)) u)) ≤
      generalSDCSRawPrimalTelescopeInitialCoeff P k *
          S.localProx i (centerState.xPrev i) u -
        generalSDCSRawPrimalTerminalCoeff P k *
          S.localProx i (S.generatedX P hP init samples trace k i) u := by
  classical
  intro centerState T coeff
  let V : ℕ → ℝ := fun t =>
    S.localProx i (S.generatedInnerQuery P hP init samples trace i k t) u
  have hV_nonneg : ∀ n, 0 ≤ V n := by
    intro n
    have huQuery : S.generatedInnerQuery P hP init samples trace i k n ∈ S.feasible i := by
      simpa [generatedInnerQuery] using ((trace.inner k i).state n).mem
    have hprox :=
      S.proxStrongConvexity i
        (S.generatedInnerQuery P hP init samples trace i k n) u (by simp) huQuery hu
    have hsq : 0 ≤ (1 / 2 : ℝ) *
        ‖S.generatedInnerQuery P hP init samples trace i k n - u‖ ^ 2 := by
      positivity
    exact le_trans hsq hprox
  have hAudit :=
    cs_weighted_bregman_raw_terminal_coeff_source_le
      (ValidParameters.eta_nonneg hP k) hT V hV_nonneg
  have hInit :
      V 0 = S.localProx i (centerState.xPrev i) u := by
    dsimp [V]
    have h0 := (trace.inner k i).initial_value
    simpa [generatedInnerQuery, centerState, generatedState] using
      congrArg (fun z => S.localProx i z u) h0
  have hTerm :
      V T = S.localProx i (S.generatedX P hP init samples trace k i) u := by
    dsimp [V]
    have hx :=
      S.generated_x_eq_inner_terminal P hP init samples trace k hk i
    simpa [T, centerState, generatedInnerQuery] using
      congrArg (fun z => S.localProx i z u) hx.symm
  have hAudit' :
      coeff *
          (∑ t ∈ Finset.range T, csLambda (t + 1) *
            ((P.eta k * csBeta (t + 1)) * V t -
              (P.eta k + P.eta k * csBeta (t + 1)) * V (t + 1))) ≤
        generalSDCSRawPrimalTelescopeInitialCoeff P k *
            S.localProx i (centerState.xPrev i) u -
          generalSDCSRawPrimalTerminalCoeff P k *
            S.localProx i (S.generatedX P hP init samples trace k i) u := by
    simpa [coeff, generalSDCSRawPrimalTelescopeInitialCoeff,
      generalSDCSRawPrimalTerminalCoeff, hInit, hTerm, T] using hAudit
  calc
    coeff *
        (∑ t ∈ Finset.range T, csLambda (t + 1) *
          ((P.eta k * csBeta (t + 1)) *
              S.localProx i (S.generatedInnerQuery P hP init samples trace i k t) u -
            (P.eta k + P.eta k * csBeta (t + 1)) *
              S.localProx i (S.generatedInnerQuery P hP init samples trace i k (t + 1)) u))
      = coeff *
          (∑ t ∈ Finset.range T, csLambda (t + 1) *
            ((P.eta k * csBeta (t + 1)) * V t -
              (P.eta k + P.eta k * csBeta (t + 1)) * V (t + 1))) := by
          rfl
    _ ≤ generalSDCSRawPrimalTelescopeInitialCoeff P k *
          S.localProx i (centerState.xPrev i) u -
        generalSDCSRawPrimalTerminalCoeff P k *
          S.localProx i (S.generatedX P hP init samples trace k i) u := hAudit'

/-- Weighted Bregman differences in Lemma 8.5, printed p. 560.
The same coefficient multiplies both terms inside the source brackets.
-/
def generalSDCSRawTerminalPotential (P : Parameters) (hP : ValidParameters P)
    (init : InitialState S) (samples : ℕ → ι → ℕ → Ξ)
    (trace : S.GeneratedTrace P hP init samples) (x : Stacked ι E) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N,
    let kk := k + 1
    P.theta kk * generalSDCSRawPrimalTerminalCoeff P kk *
      (S.stackedProx (S.generatedX P hP init samples trace (kk - 1)) x -
        S.stackedProx (S.generatedX P hP init samples trace kk) x)

/-- The signed stochastic-error and exact Young-square part of Lemma 8.5.

Proposition 8.7 defines delta as subgradient minus oracle; moving its linear term
from the left side of the CS inequality to the right gives the negative sign
below.  The source's subsequent square-budget simplification is valid and is
represented by cs_weighted_oracle_square_budget_pointwise_le and its finite-sum
form.  Keeping the exact Young term here lets the expectation bridge combine
that estimate with generated-query cancellation and the oracle variance bound.
-/

def generalSDCSRawOracleErrorBudget (P : Parameters) (hP : ValidParameters P)
    (init : InitialState S) (samples : ℕ → ι → ℕ → Ξ)
    (trace : S.GeneratedTrace P hP init samples) (x : Stacked ι E) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N,
    let kk := k + 1
    let T := P.innerSteps kk
    ∑ t ∈ Finset.range T,
      ∑ i,
        let uPrev := S.generatedInnerQuery P hP init samples trace i kk t
        let δ := S.oracleError i uPrev (samples kk i t)
        (2 * P.theta kk / ((T : ℝ) * ((T : ℝ) + 3))) *
          (-(csLambda (t + 1) * inner ℝ δ (x i - uPrev)) +
            csLambda (t + 1) *
              ((S.M + ‖δ‖) ^ 2 / (2 * (P.eta kk * csBeta (t + 1)))))

/-- Raw-terminal right hand side of Lemma 8.5.

The authoritative source places one common coefficient on the complete terminal
Bregman difference.  This expression preserves that coefficient, the
perturbation vector, and the negative oracle-error term dictated by Proposition
8.7 with this file's definition of oracleError.
-/

def generalSDCSGapLemma85RawTerminalRHS (P : Parameters) (hP : ValidParameters P)
    (init : InitialState S) (samples : ℕ → ι → ℕ → Ξ)
    (trace : S.GeneratedTrace P hP init samples) (x y : Stacked ι E) (N : ℕ) : ℝ :=
  S.generalSDCSRawTerminalPotential P hP init samples trace x N +
    (P.theta 1 * P.tau 1 / 2) * S.stackedNormSq init.y0 +
    stackedInner (S.perturbationVector P hP init samples trace N) y +
    S.generalSDCSRawOracleErrorBudget P hP init samples trace x N

/-- The part of the corrected Lemma 8.5 RHS that remains after passing from
`Q(\hat z_N; x^*, y)` to the perturbed gap
`g(\hat s_N,\hat z_N)`.

This is `generalSDCSGapLemma85RawTerminalRHS` with the linear
`<\hat s,y>` term removed, because the source scaled perturbation
`\hat s_N=(∑θ_k)^{-1}\hat s` is subtracted in the definition of the
perturbed gap.  It still retains the signed stochastic oracle budget, whose
linear part is cancelled only after taking expectations.
-/
def generalSDCSGapLemma85RawPerturbedGapRHS (P : Parameters) (hP : ValidParameters P)
    (init : InitialState S) (samples : ℕ → ι → ℕ → Ξ)
    (trace : S.GeneratedTrace P hP init samples) (x : Stacked ι E) (N : ℕ) : ℝ :=
  S.generalSDCSRawTerminalPotential P hP init samples trace x N +
    (P.theta 1 * P.tau 1 / 2) * S.stackedNormSq init.y0 +
    S.generalSDCSRawOracleErrorBudget P hP init samples trace x N

/-- Raw-terminal residual RHS for Lemma 8.5, equation (8.3.66).

It preserves the common coefficient on the complete Bregman difference and the
squared dual distance.  The square is also the moment quantity needed by the
corrected Jensen step in the consensus proof.
-/

def generalSDCSGapLemma85RawResidualRHS (P : Parameters) (hP : ValidParameters P)
    (init : InitialState S) (samples : ℕ → ι → ℕ → Ξ)
    (trace : S.GeneratedTrace P hP init samples)
    (xStar yStar : Stacked ι E) (N : ℕ) : ℝ :=
  S.generalSDCSRawTerminalPotential P hP init samples trace xStar N +
    (P.theta 1 * P.tau 1 / 2) * S.stackedNormSq (yStar - init.y0) +
    S.generalSDCSRawOracleErrorBudget P hP init samples trace xStar N

/-- Left side of the residual inequality in Lemma 8.5 / (8.3.66). -/
def generalSDCSGapLemma85ResidualLHS (P : Parameters) (hP : ValidParameters P)
    (init : InitialState S) (samples : ℕ → ι → ℕ → Ξ)
    (trace : S.GeneratedTrace P hP init samples)
    (xStar yStar : Stacked ι E) (N : ℕ) : ℝ :=
  (P.theta N / 2) *
    (1 - P.theta N * S.networkOperatorNorm ^ 2 / (P.eta N * P.tau N)) *
      max
        (P.eta N *
          S.stackedNormSq
            (S.generatedXHat P hP init samples trace N -
              S.generatedX P hP init samples trace (N - 1)))
        (P.tau N *
          S.stackedNormSq (yStar - S.generatedY P hP init samples trace N))

/-- The weighted dual output component used by the source `zhat_N` expression in
Lemma 8.5. -/
def weightedDualAverage (P : Parameters) (hP : ValidParameters P) (init : InitialState S)
    (samples : ℕ → ι → ℕ → Ξ) (trace : S.GeneratedTrace P hP init samples)
    (N : ℕ) : Stacked ι E :=
  (∑ k ∈ Finset.range N, P.theta (k + 1))⁻¹ •
    (∑ k ∈ Finset.range N, P.theta (k + 1) •
      S.generatedY P hP init samples trace (k + 1))

/-- Source stochastic independence for the actual generated trace whose fresh
sample is queried.

This public predicate is intentionally only the source assumption that the fresh
sample is independent of the generated search point.  Endpoint Bochner
integrability for the Theorem 8.11 expectation step must be derived from a
generated-process regularity theorem, not bundled into this source assumption.
-/
def GeneratedQueryIndependent (P : Parameters) (hP : ValidParameters P)
    (init : InitialState S) (run : OracleRun S Ω)
    (trace : ∀ ω, S.GeneratedTrace P hP init (run.samples ω)) : Prop :=
  S.GeneratedQueryIndependentCore P hP init run trace

/-- The source-boundary core of the generated stochastic process.

This is the part of the process object that follows the book's generated
Algorithm 8.8 trace boundary: a random generated trace together with
measurability of generated states, generated query coordinates, and fresh sample
coordinates.  Moment and domination facts used for Bochner expectations are
kept out of this core so that every survivor can be audited separately.
-/
structure GeneratedProcessCore (P : Parameters) (hP : ValidParameters P)
    (init : InitialState S) (run : OracleRun S Ω) where
  trace : ∀ ω, S.GeneratedTrace P hP init (run.samples ω)
  generatedX_measurable :
    ∀ k i, Measurable (fun ω => S.generatedX P hP init (run.samples ω) (trace ω) k i)
  generatedXHat_measurable :
    ∀ k i, Measurable (fun ω => S.generatedXHat P hP init (run.samples ω) (trace ω) k i)
  generatedY_measurable :
    ∀ k i, Measurable (fun ω => S.generatedY P hP init (run.samples ω) (trace ω) k i)
  generatedInnerQuery_measurable :
    ∀ i k t, Measurable
      (fun ω => S.generatedInnerQuery P hP init (run.samples ω) (trace ω) i k t)
  sample_measurable :
    ∀ k i t, Measurable (fun ω => run.samples ω k i t)

/-- The direct finite-prefix estimate above gives every generated inner query a
second moment once the center and the current dual disagreement have second
moments.  This is the inner half of the finite-horizon outer/inner induction;
it uses no upper Bregman bound. -/
private theorem generated_sdcs_inner_query_direction_sq_integrable
    (P : Parameters) (hP : ValidParameters P) (init : InitialState S)
    (run : OracleRun S Ω)
    (core : S.GeneratedProcessCore P hP init run)
    (hIndependent : S.GeneratedQueryIndependentCore P hP init run core.trace)
    (i : ι) (k : ℕ) (xRef : E) (hxRef : xRef ∈ S.feasible i)
    (heta : 0 < P.eta k)
    (hzero : Integrable
      (fun ω =>
        ‖xRef - S.generatedInnerQuery P hP init (run.samples ω) (core.trace ω)
          i k 0‖ ^ 2) run.law)
    (hw : Integrable
      (fun ω =>
        ‖(S.dualNeighborDisagreement
          (S.generatedState P hP init (run.samples ω) (core.trace ω) k).yPrev) i‖ ^ 2)
      run.law) :
    ∀ t, Integrable
      (fun ω =>
        ‖xRef - S.generatedInnerQuery P hP init (run.samples ω) (core.trace ω)
          i k t‖ ^ 2) run.law := by
  classical
  letI : IsProbabilityMeasure run.law := run.law_isProbability
  letI : IsFiniteMeasure run.law := inferInstance
  let u : Ω → ℕ → E := fun ω r =>
    S.generatedInnerQuery P hP init (run.samples ω) (core.trace ω) i k r
  let delta : ℕ → Ω → E := fun r ω =>
    S.oracleError i (u ω r) (run.samples ω k i r)
  let w : Ω → E := fun ω =>
    (S.dualNeighborDisagreement
      (S.generatedState P hP init (run.samples ω) (core.trace ω) k).yPrev) i
  let C : ℝ := S.M + ‖S.subgradient i xRef‖
  apply finite_path_sq_distance_integrable_of_increment_energy_bound
    (μ := run.law) (u := u) (delta := delta) (w := w) (xRef := xRef)
    (eta := P.eta k) (M := S.M) (C := C)
  · exact fun r => (core.generatedInnerQuery_measurable i k r).aestronglyMeasurable
  · intro r
    have hpair : Measurable (fun ω => (u ω r, run.samples ω k i r)) :=
      (core.generatedInnerQuery_measurable i k r).prodMk (core.sample_measurable k i r)
    exact (by
      simpa [delta, u, oracleError] using
        ((S.oracleErrorKernelMeasurable i).comp hpair).aestronglyMeasurable)
  · have hy : Measurable (fun ω =>
        S.generatedY P hP init (run.samples ω) (core.trace ω) k) :=
      measurable_pi_iff.mpr (fun j => core.generatedY_measurable k j)
    exact ((continuous_apply i).measurable.comp
      (S.networkOperator.measurable.comp hy)).aestronglyMeasurable
  · intro r
    simpa [delta, u] using
      S.generated_oracle_error_sq_integrable
        P hP init run core.trace hIndependent i k r
  · simpa [w] using hw
  · simpa [u] using hzero
  · intro t
    filter_upwards with ω
    simpa [u, delta, w, C, oracleError] using
      S.generated_sdcs_inner_prefix_increment_sq_le
        P hP init (run.samples ω) (core.trace ω) i k t xRef hxRef heta

private theorem integrable_norm_sq_add_of_integrable_norm_sq
    {f g : Ω → E} (μ : Measure Ω)
    (hf_meas : AEStronglyMeasurable f μ) (hg_meas : AEStronglyMeasurable g μ)
    (hf : Integrable (fun ω => ‖f ω‖ ^ 2) μ)
    (hg : Integrable (fun ω => ‖g ω‖ ^ 2) μ) :
    Integrable (fun ω => ‖f ω + g ω‖ ^ 2) μ := by
  exact integrable_sq_norm_add hf_meas hg_meas hf hg

private theorem integrable_norm_sq_const_smul_of_integrable_norm_sq
    {f : Ω → E} (μ : Measure Ω) (c : ℝ)
    (hf_meas : AEStronglyMeasurable f μ)
    (hf : Integrable (fun ω => ‖f ω‖ ^ 2) μ) :
    Integrable (fun ω => ‖c • f ω‖ ^ 2) μ := by
  exact integrable_sq_norm_const_smul c hf

private theorem generated_network_coordinate_norm_sq_integrable
    (run : OracleRun S Ω) (z : Ω → Stacked ι E)
    (hz_meas : ∀ j, Measurable (fun ω => z ω j))
    (hz_sq : ∀ j, Integrable (fun ω => ‖z ω j‖ ^ 2) run.law)
    (i : ι) :
    Integrable (fun ω => ‖(S.networkOperator (z ω)) i‖ ^ 2) run.law := by
  exact integrable_sq_norm_apply_continuousLinearMap_of_coordinate_sq_integrable
    run.law S.networkOperator z (fun j => (hz_meas j).aestronglyMeasurable) hz_sq i

/-- Finite-horizon L2 regularity for the actual Algorithm 8.8 generated query.
The proof is a simultaneous strong induction over the three generated outer
states and invokes the direct inner-prefix estimate at each successor step. -/
private theorem theorem811_generated_inner_query_direction_sq_integrable
    (init : InitialState S) (run : OracleRun S Ω)
    (N : ℕ) (Dtilde : ℝ)
    (hSchedule : S.Theorem811ScheduleWellDefined N Dtilde)
    (core :
      S.GeneratedProcessCore (S.theorem811Parameters N Dtilde hSchedule)
        (S.theorem811Parameters_valid N Dtilde hSchedule) init run)
    (hIndependent :
      S.GeneratedQueryIndependentCore (S.theorem811Parameters N Dtilde hSchedule)
        (S.theorem811Parameters_valid N Dtilde hSchedule) init run core.trace)
    (xStar : Stacked ι E) (hxStar : S.PrimalOptimalSolution xStar) :
    let P := S.theorem811Parameters N Dtilde hSchedule
    let hP := S.theorem811Parameters_valid N Dtilde hSchedule
    ∀ i k t, Integrable
      (fun ω =>
        ‖xStar i -
          S.generatedInnerQuery P hP init (run.samples ω) (core.trace ω) i k t‖ ^ 2)
      run.law := by
  classical
  letI : IsProbabilityMeasure run.law := run.law_isProbability
  letI : IsFiniteMeasure run.law := inferInstance
  let P := S.theorem811Parameters N Dtilde hSchedule
  let hP := S.theorem811Parameters_valid N Dtilde hSchedule
  let X : ℕ → ι → Ω → E := fun k i ω =>
    S.generatedX P hP init (run.samples ω) (core.trace ω) k i
  let XHat : ℕ → ι → Ω → E := fun k i ω =>
    S.generatedXHat P hP init (run.samples ω) (core.trace ω) k i
  let Y : ℕ → ι → Ω → E := fun k i ω =>
    S.generatedY P hP init (run.samples ω) (core.trace ω) k i
  let Good : ℕ → Prop := fun k =>
    (∀ i, Integrable (fun ω => ‖X k i ω‖ ^ 2) run.law) ∧
    (∀ i, Integrable (fun ω => ‖XHat k i ω‖ ^ 2) run.law) ∧
    (∀ i, Integrable (fun ω => ‖Y k i ω‖ ^ 2) run.law)
  have hXmeas : ∀ k i, Measurable (X k i) := fun k i => core.generatedX_measurable k i
  have hXHatmeas : ∀ k i, Measurable (XHat k i) :=
    fun k i => core.generatedXHat_measurable k i
  have hYmeas : ∀ k i, Measurable (Y k i) := fun k i => core.generatedY_measurable k i
  have hGood : ∀ k, Good k := by
    intro q
    refine Nat.strong_induction_on q ?_
    intro k ih
    cases k with
    | zero =>
        refine ⟨?_, ?_, ?_⟩
        · intro i
          refine (integrable_const (c := ‖init.x0 i‖ ^ 2) (μ := run.law)).congr ?_
          filter_upwards with ω
          have h0 := (core.trace ω).initial_state
          simp [X, P, hP, generatedX, generatedState, initialOuterState, h0]
        · intro i
          refine (integrable_const (c := ‖init.x0 i‖ ^ 2) (μ := run.law)).congr ?_
          filter_upwards with ω
          have h0 := (core.trace ω).initial_state
          simp [XHat, P, hP, generatedXHat, generatedState, initialOuterState, h0]
        · intro i
          refine (integrable_const (c := ‖init.y0 i‖ ^ 2) (μ := run.law)).congr ?_
          filter_upwards with ω
          have h0 := (core.trace ω).initial_state
          simp [Y, P, hP, generatedY, generatedState, initialOuterState, h0]
    | succ n =>
        have hprev : Good n := ih n (Nat.lt_succ_self n)
        let xLag : ι → Ω → E := fun i ω =>
          (S.generatedState P hP init (run.samples ω) (core.trace ω) n).xLag i
        have hxLag_eq : ∀ i, xLag i =
            if n = 0 then (fun _ω => init.x0 i) else X (n - 1) i := by
          intro i
          funext ω
          by_cases hn : n = 0
          · subst n
            have h0 := (core.trace ω).initial_state
            simp [xLag, X, P, hP, generatedState, generatedX, initialOuterState, h0]
          · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
            have hs := ((core.trace ω).step_spec n hn1).1
            simp only [if_neg hn]
            simpa [xLag, X, generatedState, generatedX, Nat.sub_add_cancel hn1] using
              congrArg (fun z => z i) hs
        have hxLag_meas : ∀ i, Measurable (xLag i) := by
          intro i
          rw [hxLag_eq i]
          split_ifs with hn
          · exact measurable_const
          · exact hXmeas (n - 1) i
        have hxLag_sq : ∀ i, Integrable (fun ω => ‖xLag i ω‖ ^ 2) run.law := by
          intro i
          rw [hxLag_eq i]
          split_ifs with hn
          · exact integrable_const (c := ‖init.x0 i‖ ^ 2)
          · exact (ih (n - 1) (by omega)).1 i
        let xTilde : ι → Ω → E := fun i ω =>
          S.outerExtrapolation P (n + 1)
            (S.generatedState P hP init (run.samples ω) (core.trace ω) n) i
        have hxTilde_meas : ∀ i, Measurable (xTilde i) := by
          intro i
          simpa [xTilde, outerExtrapolation, xLag, X, XHat, Pi.smul_apply,
            Pi.sub_apply, Pi.add_apply] using
            (((hXHatmeas n i).sub (hxLag_meas i)).const_smul (P.alpha (n + 1))).add
              (hXmeas n i)
        have hxTilde_sq : ∀ i, Integrable (fun ω => ‖xTilde i ω‖ ^ 2) run.law := by
          intro i
          have hdiff : Integrable
              (fun ω => ‖XHat n i ω - xLag i ω‖ ^ 2) run.law := by
            simpa [sub_eq_add_neg] using
              integrable_norm_sq_add_of_integrable_norm_sq run.law
                (hXHatmeas n i).aestronglyMeasurable
                ((hxLag_meas i).neg.aestronglyMeasurable)
                (hprev.2.1 i) (by simpa using hxLag_sq i)
          have hscaled : Integrable
              (fun ω => ‖P.alpha (n + 1) • (XHat n i ω - xLag i ω)‖ ^ 2) run.law :=
            integrable_norm_sq_const_smul_of_integrable_norm_sq run.law
              (P.alpha (n + 1))
              ((hXHatmeas n i).sub (hxLag_meas i)).aestronglyMeasurable hdiff
          simpa [xTilde, outerExtrapolation, xLag, X, XHat, Pi.smul_apply,
            Pi.sub_apply, Pi.add_apply] using
            integrable_norm_sq_add_of_integrable_norm_sq run.law
              (((hXHatmeas n i).sub (hxLag_meas i)).const_smul
                (P.alpha (n + 1))).aestronglyMeasurable
              (hXmeas n i).aestronglyMeasurable hscaled (hprev.1 i)
        let v : ι → Ω → E := fun i ω =>
          (S.primalNeighborDisagreement (fun j => xTilde j ω)) i
        have hv_meas : ∀ i, Measurable (v i) := by
          intro i
          have hstack : Measurable (fun ω => (fun j => xTilde j ω)) :=
            measurable_pi_iff.mpr hxTilde_meas
          exact (continuous_apply i).measurable.comp
            (S.networkOperator.measurable.comp hstack)
        have hv_sq : ∀ i, Integrable (fun ω => ‖v i ω‖ ^ 2) run.law := by
          intro i
          simpa [v, primalNeighborDisagreement] using
            S.generated_network_coordinate_norm_sq_integrable run
              (fun ω j => xTilde j ω) hxTilde_meas hxTilde_sq i
        have hy_eq : ∀ i, Y (n + 1) i = fun ω =>
            Y n i ω + (P.tau (n + 1))⁻¹ • v i ω := by
          intro i
          funext ω
          have hs := S.generated_dualUpdate_spec P hP init (run.samples ω)
            (core.trace ω) (n + 1) (by omega)
          have heq := congrArg (fun z => z i) hs.2
          simpa only [Y, v, xTilde, generatedY, generatedState,
            Pi.add_apply, Pi.smul_apply]
            using heq
        have hySucc : ∀ i, Integrable (fun ω => ‖Y (n + 1) i ω‖ ^ 2) run.law := by
          intro i
          rw [hy_eq i]
          have hscaled := integrable_norm_sq_const_smul_of_integrable_norm_sq run.law
            (P.tau (n + 1))⁻¹ (hv_meas i).aestronglyMeasurable (hv_sq i)
          exact integrable_norm_sq_add_of_integrable_norm_sq run.law
            (hYmeas n i).aestronglyMeasurable
            ((hv_meas i).const_smul (P.tau (n + 1))⁻¹).aestronglyMeasurable
            (hprev.2.2 i) hscaled
        have hwSucc : ∀ i, Integrable
            (fun ω => ‖(S.dualNeighborDisagreement
              (S.generatedState P hP init (run.samples ω) (core.trace ω) (n + 1)).yPrev) i‖ ^ 2)
              run.law := by
          intro i
          simpa [dualNeighborDisagreement, generatedY, generatedState, Y] using
            S.generated_network_coordinate_norm_sq_integrable run
              (fun ω => S.generatedY P hP init (run.samples ω) (core.trace ω) (n + 1))
              (fun j => core.generatedY_measurable (n + 1) j)
              (by intro j; simpa [Y] using hySucc j) i
        have hu0_eq : ∀ i,
            (fun ω => S.generatedInnerQuery P hP init (run.samples ω) (core.trace ω)
              i (n + 1) 0) = X n i := by
          intro i
          funext ω
          have h0 := ((core.trace ω).inner (n + 1) i).initial_value
          simpa [generatedInnerQuery, X, generatedX, generatedState] using h0
        have hu0dir : ∀ i, Integrable
            (fun ω => ‖xStar i -
              S.generatedInnerQuery P hP init (run.samples ω) (core.trace ω)
                i (n + 1) 0‖ ^ 2) run.law := by
          intro i
          conv_lhs =>
            intro ω
            rw [congrFun (hu0_eq i) ω]
          simpa [sub_eq_add_neg] using
            integrable_norm_sq_add_of_integrable_norm_sq run.law
              (show AEStronglyMeasurable (fun _ω : Ω => xStar i) run.law from
                measurable_const.aestronglyMeasurable)
              ((hXmeas n i).neg.aestronglyMeasurable)
              (integrable_const (c := ‖xStar i‖ ^ 2))
              (by simpa using hprev.1 i)
        have hqueryDir : ∀ i t, Integrable
            (fun ω => ‖xStar i -
              S.generatedInnerQuery P hP init (run.samples ω) (core.trace ω)
                i (n + 1) t‖ ^ 2) run.law := by
          intro i t
          exact S.generated_sdcs_inner_query_direction_sq_integrable
            P hP init run core hIndependent i (n + 1) (xStar i) (hxStar.1 i)
              (by
                dsimp [P, theorem811Parameters]
                exact mul_pos (by norm_num) hSchedule.2)
              (hu0dir i) (hwSucc i) t
        have hqueryAbs : ∀ i t, Integrable
            (fun ω => ‖S.generatedInnerQuery P hP init (run.samples ω) (core.trace ω)
              i (n + 1) t‖ ^ 2) run.law := by
          intro i t
          let d : Ω → E := fun ω => xStar i -
            S.generatedInnerQuery P hP init (run.samples ω) (core.trace ω)
              i (n + 1) t
          have hdmeas : Measurable d :=
            measurable_const.sub (core.generatedInnerQuery_measurable i (n + 1) t)
          have hadd := integrable_norm_sq_add_of_integrable_norm_sq run.law
            (show AEStronglyMeasurable (fun _ω : Ω => xStar i) run.law from
              measurable_const.aestronglyMeasurable)
            hdmeas.neg.aestronglyMeasurable
            (integrable_const (c := ‖xStar i‖ ^ 2))
            (by simpa [d, norm_sub_rev] using hqueryDir i t)
          simpa [d, sub_eq_add_neg] using hadd
        have hxSucc : ∀ i, Integrable (fun ω => ‖X (n + 1) i ω‖ ^ 2) run.law := by
          intro i
          have heq : X (n + 1) i = fun ω =>
              S.generatedInnerQuery P hP init (run.samples ω) (core.trace ω)
                i (n + 1) (P.innerSteps (n + 1)) := by
            funext ω
            have hx := S.generated_x_eq_inner_terminal P hP init (run.samples ω)
              (core.trace ω) (n + 1) (by omega) i
            simpa [X, generatedInnerQuery, csIterate] using hx
          rw [heq]
          exact hqueryAbs i (P.innerSteps (n + 1))
        have hxhatSucc : ∀ i, Integrable (fun ω => ‖XHat (n + 1) i ω‖ ^ 2) run.law := by
          intro i
          let T := P.innerSteps (n + 1)
          let avg : Ω → E := fun ω => (csLambdaSum T)⁻¹ •
            ∑ t ∈ Finset.range T, csLambda (t + 1) •
              S.generatedInnerQuery P hP init (run.samples ω) (core.trace ω)
                i (n + 1) (t + 1)
          have hterm : ∀ t ∈ Finset.range T, MemLp
              (fun ω => csLambda (t + 1) •
                S.generatedInnerQuery P hP init (run.samples ω) (core.trace ω)
                  i (n + 1) (t + 1)) 2 run.law := by
            intro t ht
            have hqmeas := core.generatedInnerQuery_measurable i (n + 1) (t + 1)
            have hq2 : MemLp
                (fun ω => S.generatedInnerQuery P hP init (run.samples ω) (core.trace ω)
                  i (n + 1) (t + 1)) 2 run.law :=
              (memLp_two_iff_integrable_sq_norm hqmeas.aestronglyMeasurable).2
                (hqueryAbs i (t + 1))
            exact hq2.const_smul (csLambda (t + 1))
          have havg2 : MemLp avg 2 run.law := by
            dsimp [avg]
            exact (memLp_finset_sum (Finset.range T) hterm).const_smul (csLambdaSum T)⁻¹
          have havgMeas : Measurable avg := by
            dsimp [avg]
            exact (Finset.measurable_sum (Finset.range T)
              (fun t _ht => (core.generatedInnerQuery_measurable i (n + 1) (t + 1)).const_smul
                (csLambda (t + 1)))).const_smul (csLambdaSum T)⁻¹
          have havgSq : Integrable (fun ω => ‖avg ω‖ ^ 2) run.law :=
            (memLp_two_iff_integrable_sq_norm havgMeas.aestronglyMeasurable).1 havg2
          have heq : XHat (n + 1) i = avg := by
            funext ω
            have hxhat := S.generated_xhat_eq_inner_weightedAverage P hP init
              (run.samples ω) (core.trace ω) (n + 1) (by omega) i
            simpa [XHat, avg, T, csWeightedAverage, csIterate, generatedInnerQuery]
              using hxhat
          rw [heq]
          exact havgSq
        exact ⟨hxSucc, hxhatSucc, hySucc⟩
  dsimp only
  intro i k t
  have hkstates := hGood k
  have hw : Integrable
      (fun ω => ‖(S.dualNeighborDisagreement
        (S.generatedState P hP init (run.samples ω) (core.trace ω) k).yPrev) i‖ ^ 2)
      run.law := by
    simpa [dualNeighborDisagreement, generatedY, generatedState, Y] using
      S.generated_network_coordinate_norm_sq_integrable run
        (fun ω => S.generatedY P hP init (run.samples ω) (core.trace ω) k)
        (fun j => core.generatedY_measurable k j)
        (by intro j; simpa [Y] using hkstates.2.2 j) i
  have hu0eq : (fun ω =>
      S.generatedInnerQuery P hP init (run.samples ω) (core.trace ω) i k 0) =
      X (k - 1) i := by
    funext ω
    have h0 := ((core.trace ω).inner k i).initial_value
    simpa [generatedInnerQuery, X, generatedX, generatedState] using h0
  have hzero : Integrable
      (fun ω => ‖xStar i -
        S.generatedInnerQuery P hP init (run.samples ω) (core.trace ω) i k 0‖ ^ 2)
      run.law := by
    conv_lhs =>
      intro ω
      rw [congrFun hu0eq ω]
    simpa [sub_eq_add_neg] using
      integrable_norm_sq_add_of_integrable_norm_sq run.law
        (show AEStronglyMeasurable (fun _ω : Ω => xStar i) run.law from
          measurable_const.aestronglyMeasurable)
        ((hXmeas (k - 1) i).neg.aestronglyMeasurable)
        (integrable_const (c := ‖xStar i‖ ^ 2))
        (by simpa using (hGood (k - 1)).1 i)
  exact S.generated_sdcs_inner_query_direction_sq_integrable
    P hP init run core hIndependent i k (xStar i) (hxStar.1 i)
      (by
        dsimp [P, theorem811Parameters]
        exact mul_pos (by norm_num) hSchedule.2) hzero hw t

/-- A stronger legacy compatibility record carrying global L2 assumptions.

The source-boundary model is GeneratedProcessCore; the canonical Theorem 8.11
proof derives its finite-horizon moments directly from the generated recursion.
This private record is retained only to document the former stronger interface
and is not used by either public residual endpoint.
-/
private structure GeneratedProcess (P : Parameters) (hP : ValidParameters P)
    (init : InitialState S) (run : OracleRun S Ω)
    extends S.GeneratedProcessCore P hP init run where
  generatedX_sq_integrable :
    ∀ k x, Integrable
      (fun ω => S.stackedNormSq
        (S.generatedX P hP init (run.samples ω) (trace ω) k - x)) run.law
  generatedXHat_sq_integrable :
    ∀ k x, Integrable
      (fun ω => S.stackedNormSq
        (S.generatedXHat P hP init (run.samples ω) (trace ω) k - x)) run.law
  generatedY_sq_integrable :
    ∀ k y, Integrable
      (fun ω => S.stackedNormSq
        (y - S.generatedY P hP init (run.samples ω) (trace ω) k)) run.law
private theorem theorem811PrimalAverage_mem
    (P : Parameters) (hP : ValidParameters P) (init : InitialState S)
    (samples : ℕ → ι → ℕ → Ξ)
    (trace : S.GeneratedTrace P hP init samples)
    {N : ℕ} (hN : 1 ≤ N)
    (hDenom : ∀ k, 1 ≤ k → k ≤ N → 0 < P.innerSteps k ∧ 0 < P.eta k) :
    S.FeasiblePoint (S.theorem811PrimalAverage P hP init samples trace N) := by
  classical
  intro i
  have hsum_eq : (∑ _k ∈ Finset.range N, (1 : ℝ)) = (N : ℝ) := by
    simp
  have hsum_pos : 0 < ∑ _k ∈ Finset.range N, (1 : ℝ) := by
    rw [hsum_eq]
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hN)
  have hmem :
      ((∑ _k ∈ Finset.range N, (1 : ℝ))⁻¹) •
          (∑ k ∈ Finset.range N,
            (1 : ℝ) • S.generatedXHat P hP init samples trace (k + 1) i) ∈
        S.feasible i :=
    (S.feasible_convex i).normalized_weighted_sum_mem
      (s := Finset.range N) (w := fun _k => (1 : ℝ))
      (x := fun k => S.generatedXHat P hP init samples trace (k + 1) i)
      hsum_pos
      (by intro k _hk; positivity)
      (by
        intro k hk
        have hkk1 : 1 ≤ k + 1 := Nat.succ_pos k
        have hkkN : k + 1 ≤ N := Nat.succ_le_of_lt (Finset.mem_range.mp hk)
        exact S.generatedXHat_mem P hP init samples trace (k + 1) hkk1
          (hDenom (k + 1) hkk1 hkkN).1 i)
  simpa [theorem811PrimalAverage, hsum_eq] using hmem

private theorem sum_Icc_weighted_lagged_stackedInner_telescope_eq_terminal_sub
    (theta alpha : ℕ → ℝ) (m : ℝ)
    (x : Stacked ι E) (xseq delta : ℕ → Stacked ι E) {k : ℕ} (hk : 1 ≤ k)
    (hcoeff :
      ∀ t, 2 ≤ t → t ≤ k →
        theta t * alpha t / m = theta (t - 1))
    (hdelta_zero : delta 0 = 0) :
    Finset.sum (Finset.Icc 1 k)
        (fun t =>
          theta t *
            (stackedInner (xseq t - x) (delta t) -
              (alpha t / m) *
                stackedInner (xseq t - x) (delta (t - 1)))) =
      theta k * stackedInner (xseq k - x) (delta k) -
        Finset.sum (Finset.Icc 2 k)
          (fun t =>
            (theta t * alpha t / m) *
              stackedInner (xseq t - xseq (t - 1)) (delta (t - 1))) := by
  classical
  let A : ℕ → ℝ := fun t => stackedInner (xseq t - x) (delta t)
  let Lag : ℕ → ℝ := fun t => stackedInner (xseq t - x) (delta (t - 1))
  let Step : ℕ → ℝ := fun t => stackedInner (xseq t - xseq (t - 1)) (delta (t - 1))
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
      simp [Lag, stackedInner, hdelta_zero]
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
        ext i
        simp [Pi.sub_apply, Pi.add_apply]
      dsimp [Lag, A, Step]
      calc
        stackedInner (xseq (n + 1) - x) (delta n) =
            stackedInner ((xseq n - x) + (xseq (n + 1) - xseq n)) (delta n) := by
              rw [hvec]
        _ = stackedInner (xseq n - x) (delta n) +
              stackedInner (xseq (n + 1) - xseq n) (delta n) := by
              dsimp [stackedInner, SOptLib.dependentProductInner]
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl ?_
              intro i _hi
              rw [inner_add_left]
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

private theorem weighted_gap_sum_le_of_weighted_one_step_and_delta_budget
    (N : ℕ) (theta gap delta weightedOracle : ℕ → ℝ)
    (terminal oracleBudget : ℝ)
    (hstep :
      ∀ k ∈ Finset.range N,
        theta k * gap k ≤ theta k * delta k + weightedOracle k)
    (hdelta :
      (∑ k ∈ Finset.range N, theta k * delta k) ≤ terminal)
    (horacle :
      (∑ k ∈ Finset.range N, weightedOracle k) = oracleBudget) :
    (∑ k ∈ Finset.range N, theta k * gap k) ≤ terminal + oracleBudget := by
  classical
  have hsum :
      (∑ k ∈ Finset.range N, theta k * gap k) ≤
        ∑ k ∈ Finset.range N, (theta k * delta k + weightedOracle k) :=
    Finset.sum_le_sum hstep
  have hsplit :
      (∑ k ∈ Finset.range N, (theta k * delta k + weightedOracle k)) =
        (∑ k ∈ Finset.range N, theta k * delta k) +
          ∑ k ∈ Finset.range N, weightedOracle k := by
    simp [Finset.sum_add_distrib]
  calc
    (∑ k ∈ Finset.range N, theta k * gap k)
        ≤ ∑ k ∈ Finset.range N, (theta k * delta k + weightedOracle k) := hsum
    _ = (∑ k ∈ Finset.range N, theta k * delta k) +
          ∑ k ∈ Finset.range N, weightedOracle k := hsplit
    _ ≤ terminal + oracleBudget := by
          rw [horacle]
          linarith

private theorem weighted_gap_plus_retained_terms_le_of_step_and_delta_budget
    (N : ℕ) (theta gap delta weightedOracle : ℕ → ℝ)
    (terminal retained oracleBudget : ℝ)
    (hstep :
      ∀ k ∈ Finset.range N,
        theta k * gap k ≤ theta k * delta k + weightedOracle k)
    (hdelta :
      (∑ k ∈ Finset.range N, theta k * delta k) + retained ≤ terminal)
    (horacle :
      (∑ k ∈ Finset.range N, weightedOracle k) = oracleBudget) :
    (∑ k ∈ Finset.range N, theta k * gap k) + retained ≤
      terminal + oracleBudget := by
  classical
  have hsum :
      (∑ k ∈ Finset.range N, theta k * gap k) ≤
        ∑ k ∈ Finset.range N, (theta k * delta k + weightedOracle k) :=
    Finset.sum_le_sum hstep
  have hsplit :
      (∑ k ∈ Finset.range N, (theta k * delta k + weightedOracle k)) =
        (∑ k ∈ Finset.range N, theta k * delta k) +
          ∑ k ∈ Finset.range N, weightedOracle k := by
    simp [Finset.sum_add_distrib]
  calc
    (∑ k ∈ Finset.range N, theta k * gap k) + retained
        ≤ (∑ k ∈ Finset.range N, (theta k * delta k + weightedOracle k)) +
            retained := by
          simpa [add_comm] using add_le_add_right hsum retained
    _ = ((∑ k ∈ Finset.range N, theta k * delta k) + retained) +
          ∑ k ∈ Finset.range N, weightedOracle k := by
          rw [hsplit]
          ring
    _ ≤ terminal + oracleBudget := by
          rw [horacle]
          linarith

private theorem retained_delta_budget_le_of_expand_and_nonprimal
    {deltaSum potential mismatch prox dual terminal retained : ℝ}
    (hexpand : deltaSum = potential + mismatch - prox + dual)
    (hnonprimal : mismatch - prox + dual + retained ≤ terminal) :
    deltaSum + retained ≤ potential + terminal := by
  rw [hexpand]
  linarith

set_option maxHeartbeats 800000

/-- Lemma 8.5 raw-terminal aggregate weighted `Q` inequality before the final
weighted-output Jensen step.

This is the source step obtained by combining the outer primal CS inequality,
the dual update inequality, conditions (8.3.29)-(8.3.33), and the corrected raw
inner terminal Bregman telescope. -/
private theorem general_sdcs_weighted_gap_sum_raw_terminal_le
    (P : Parameters) (hP : ValidParameters P) (init : InitialState S)
    (samples : ℕ → ι → ℕ → Ξ) (trace : S.GeneratedTrace P hP init samples)
    (N : ℕ) (hN : 1 ≤ N) (hGeneral : S.generalParameterConditions P N)
    (hDenom : ∀ k, 1 ≤ k → k ≤ N → 0 < P.innerSteps k ∧ 0 < P.eta k)
    (hTheta_nonneg : ∀ k, 1 ≤ k → k ≤ N → 0 ≤ P.theta k)
    (hRawInnerTerminal :
      ∀ (i : ι) (k : ℕ), 1 ≤ k → k ≤ N → ∀ u : E, u ∈ S.feasible i →
          let centerState := S.generatedState P hP init samples trace (k - 1)
          let T := P.innerSteps k
          let coeff := 2 / ((T : ℝ) * ((T : ℝ) + 3))
          coeff *
              (∑ t ∈ Finset.range T, csLambda (t + 1) *
                ((P.eta k * csBeta (t + 1)) *
                    S.localProx i (S.generatedInnerQuery P hP init samples trace i k t) u -
                  (P.eta k + P.eta k * csBeta (t + 1)) *
                    S.localProx i
                      (S.generatedInnerQuery P hP init samples trace i k (t + 1)) u)) ≤
            generalSDCSRawPrimalTelescopeInitialCoeff P k *
                S.localProx i (centerState.xPrev i) u -
              generalSDCSRawPrimalTerminalCoeff P k *
                S.localProx i (S.generatedX P hP init samples trace k i) u) :
    ∀ x y : Stacked ι E,
      S.FeasiblePoint x →
        (∑ k ∈ Finset.range N,
          P.theta (k + 1) *
            S.primalDualGap
              (S.generatedXHat P hP init samples trace (k + 1))
              (S.generatedY P hP init samples trace (k + 1)) x y) ≤
          S.generalSDCSGapLemma85RawTerminalRHS P hP init samples trace x y N := by
  classical
  intro x y hx
  let gap : ℕ → ℝ := fun k =>
    S.primalDualGap
      (S.generatedXHat P hP init samples trace (k + 1))
      (S.generatedY P hP init samples trace (k + 1)) x y
  let deltaRaw : ℕ → ℝ := fun kk =>
    let stPrev := S.generatedState P hP init samples trace (kk - 1)
    let xTilde := S.outerExtrapolation P kk stPrev
    stackedInner
        (S.networkOperator (S.generatedXHat P hP init samples trace kk - xTilde))
        (y - S.generatedY P hP init samples trace kk) +
      generalSDCSRawPrimalInitialCoeff P kk *
          S.stackedProx (S.generatedX P hP init samples trace (kk - 1)) x -
        generalSDCSRawPrimalTerminalCoeff P kk *
          S.stackedProx (S.generatedX P hP init samples trace kk) x -
      P.eta kk *
          S.stackedProx (S.generatedX P hP init samples trace (kk - 1))
            (S.generatedXHat P hP init samples trace kk) +
      (P.tau kk / 2) *
        (S.stackedNormSq (y - S.generatedY P hP init samples trace (kk - 1)) -
          S.stackedNormSq (y - S.generatedY P hP init samples trace kk) -
            S.stackedNormSq
              (S.generatedY P hP init samples trace (kk - 1) -
                S.generatedY P hP init samples trace kk))
  let weightedOracle : ℕ → ℝ := fun k =>
    let kk := k + 1
    let T := P.innerSteps kk
    ∑ t ∈ Finset.range T,
      ∑ i,
        let uPrev := S.generatedInnerQuery P hP init samples trace i kk t
        let δ := S.oracleError i uPrev (samples kk i t)
        (2 * P.theta kk / ((T : ℝ) * ((T : ℝ) + 3))) *
          (-(csLambda (t + 1) * inner ℝ δ (x i - uPrev)) +
            csLambda (t + 1) *
              ((S.M + ‖δ‖) ^ 2 / (2 * (P.eta kk * csBeta (t + 1)))))
  have htheta_range : ∀ k ∈ Finset.range N, 0 ≤ P.theta (k + 1) := by
    intro k hk
    exact hTheta_nonneg (k + 1) (Nat.succ_pos k)
      (Nat.succ_le_of_lt (Finset.mem_range.mp hk))
  have hOneStep :
      ∀ k ∈ Finset.range N,
        gap k ≤ deltaRaw (k + 1) +
          (let kk := k + 1
           let T := P.innerSteps kk
           ∑ t ∈ Finset.range T,
             ∑ i,
               let uPrev := S.generatedInnerQuery P hP init samples trace i kk t
               let δ := S.oracleError i uPrev (samples kk i t)
               (2 / ((T : ℝ) * ((T : ℝ) + 3))) *
                 (-(csLambda (t + 1) * inner ℝ δ (x i - uPrev)) +
                   csLambda (t + 1) *
                     ((S.M + ‖δ‖) ^ 2 / (2 * (P.eta kk * csBeta (t + 1)))))) := by
    -- Source Lemma 8.5 steps 1-5: compose
    -- `generated_outer_phi_jensen_coeff_inequality`,
    -- `generated_inner_phi_weighted_sum_bound_coeff`, `hRawInnerTerminal`, and
    -- `generated_sdcs_dual_one_step_inequality`.
    intro k hk
    have hkk_pos : 1 ≤ k + 1 := Nat.succ_pos k
    have hkk_le : k + 1 ≤ N :=
      Nat.succ_le_of_lt (Finset.mem_range.mp hk)
    have hT : 0 < P.innerSteps (k + 1) :=
      (hDenom (k + 1) hkk_pos hkk_le).1
    have heta : 0 < P.eta (k + 1) :=
      (hDenom (k + 1) hkk_pos hkk_le).2
    have hOuter :=
      S.generated_outer_phi_jensen_coeff_inequality P hP init samples trace
        (k + 1) hkk_pos hT
    have hInner :
        ∀ i,
          let centerState := S.generatedState P hP init samples trace ((k + 1) - 1)
          let nextState := S.generatedState P hP init samples trace (k + 1)
          let T := P.innerSteps (k + 1)
          let coeff := 2 / ((T : ℝ) * ((T : ℝ) + 3))
          let w := (S.dualNeighborDisagreement nextState.yPrev) i
          let xCenter := centerState.xPrev i
          coeff *
              (∑ t ∈ Finset.range T, csLambda (t + 1) *
                (let uNext :=
                  S.generatedInnerQuery P hP init samples trace i (k + 1) (t + 1)
                 inner ℝ w uNext + S.localObjective i uNext +
                   P.eta (k + 1) * S.localProx i xCenter uNext)) ≤
            coeff *
              (∑ t ∈ Finset.range T, csLambda (t + 1) *
                (let uPrev := S.generatedInnerQuery P hP init samples trace i (k + 1) t
                 let uNext :=
                  S.generatedInnerQuery P hP init samples trace i (k + 1) (t + 1)
                 let δ := S.subgradient i uPrev - S.oracle i uPrev (samples (k + 1) i t)
                 inner ℝ w (x i) + S.localObjective i (x i) +
                   P.eta (k + 1) * S.localProx i xCenter (x i) -
                   inner ℝ δ (x i - uPrev) +
                   (P.eta (k + 1) * csBeta (t + 1)) * S.localProx i uPrev (x i) -
                   (P.eta (k + 1) + P.eta (k + 1) * csBeta (t + 1)) *
                     S.localProx i uNext (x i) +
                   (S.M + ‖δ‖) ^ 2 /
                     (2 * (P.eta (k + 1) * csBeta (t + 1))))) := by
      intro i
      simpa using
        S.generated_inner_phi_weighted_sum_bound_coeff P hP init samples trace
          i (k + 1) (x i) (hx i) hT heta
    have hRaw :
        ∀ i,
          let centerState := S.generatedState P hP init samples trace ((k + 1) - 1)
          let T := P.innerSteps (k + 1)
          let coeff := 2 / ((T : ℝ) * ((T : ℝ) + 3))
          coeff *
              (∑ t ∈ Finset.range T, csLambda (t + 1) *
                ((P.eta (k + 1) * csBeta (t + 1)) *
                    S.localProx i
                      (S.generatedInnerQuery P hP init samples trace i (k + 1) t)
                      (x i) -
                  (P.eta (k + 1) + P.eta (k + 1) * csBeta (t + 1)) *
                    S.localProx i
                      (S.generatedInnerQuery P hP init samples trace i (k + 1) (t + 1))
                      (x i))) ≤
            generalSDCSRawPrimalTelescopeInitialCoeff P (k + 1) *
                S.localProx i (centerState.xPrev i) (x i) -
              generalSDCSRawPrimalTerminalCoeff P (k + 1) *
                S.localProx i (S.generatedX P hP init samples trace (k + 1) i) (x i) := by
      intro i
      simpa using hRawInnerTerminal i (k + 1) hkk_pos hkk_le (x i) (hx i)
    have hDual :=
      S.generated_sdcs_dual_one_step_inequality P hP init samples trace
        (k + 1) hkk_pos y
    let kk := k + 1
    let centerState := S.generatedState P hP init samples trace (kk - 1)
    let nextState := S.generatedState P hP init samples trace kk
    let T := P.innerSteps kk
    let coeff := 2 / ((T : ℝ) * ((T : ℝ) + 3))
    have hInnerSum :
        (∑ i,
          coeff *
            (∑ t ∈ Finset.range T, csLambda (t + 1) *
              (let uNext := S.generatedInnerQuery P hP init samples trace i kk (t + 1)
               inner ℝ ((S.dualNeighborDisagreement nextState.yPrev) i) uNext +
                 S.localObjective i uNext +
                   P.eta kk * S.localProx i (centerState.xPrev i) uNext))) ≤
          ∑ i,
            coeff *
              (∑ t ∈ Finset.range T, csLambda (t + 1) *
                (let uPrev := S.generatedInnerQuery P hP init samples trace i kk t
                 let uNext := S.generatedInnerQuery P hP init samples trace i kk (t + 1)
                 let δ := S.subgradient i uPrev - S.oracle i uPrev (samples kk i t)
                 inner ℝ ((S.dualNeighborDisagreement nextState.yPrev) i) (x i) +
                   S.localObjective i (x i) +
                   P.eta kk * S.localProx i (centerState.xPrev i) (x i) -
                   inner ℝ δ (x i - uPrev) +
                   (P.eta kk * csBeta (t + 1)) * S.localProx i uPrev (x i) -
                   (P.eta kk + P.eta kk * csBeta (t + 1)) *
                     S.localProx i uNext (x i) +
                   (S.M + ‖δ‖) ^ 2 /
                     (2 * (P.eta kk * csBeta (t + 1))))) := by
      exact Finset.sum_le_sum (fun i _hi => by
        simpa [kk, centerState, nextState, T, coeff] using hInner i)
    have hOuterInner :
        (∑ i,
          (inner ℝ ((S.dualNeighborDisagreement nextState.yPrev) i)
              (S.generatedXHat P hP init samples trace kk i) +
            (S.localObjective i (S.generatedXHat P hP init samples trace kk i) +
              P.eta kk * S.localProx i (centerState.xPrev i)
                (S.generatedXHat P hP init samples trace kk i)))) ≤
          ∑ i,
            coeff *
              (∑ t ∈ Finset.range T, csLambda (t + 1) *
                (let uPrev := S.generatedInnerQuery P hP init samples trace i kk t
                 let uNext := S.generatedInnerQuery P hP init samples trace i kk (t + 1)
                 let δ := S.subgradient i uPrev - S.oracle i uPrev (samples kk i t)
                 inner ℝ ((S.dualNeighborDisagreement nextState.yPrev) i) (x i) +
                   S.localObjective i (x i) +
                   P.eta kk * S.localProx i (centerState.xPrev i) (x i) -
                   inner ℝ δ (x i - uPrev) +
                   (P.eta kk * csBeta (t + 1)) * S.localProx i uPrev (x i) -
                   (P.eta kk + P.eta kk * csBeta (t + 1)) *
                     S.localProx i uNext (x i) +
                   (S.M + ‖δ‖) ^ 2 /
                     (2 * (P.eta kk * csBeta (t + 1))))) :=
      le_trans (by simpa [kk, centerState, nextState, T, coeff, add_assoc] using hOuter)
        hInnerSum
    have hRawSum :
        (∑ i,
          coeff *
            (∑ t ∈ Finset.range T, csLambda (t + 1) *
              ((P.eta kk * csBeta (t + 1)) *
                  S.localProx i
                    (S.generatedInnerQuery P hP init samples trace i kk t)
                    (x i) -
                (P.eta kk + P.eta kk * csBeta (t + 1)) *
                  S.localProx i
                    (S.generatedInnerQuery P hP init samples trace i kk (t + 1))
                    (x i)))) ≤
          ∑ i,
            (generalSDCSRawPrimalTelescopeInitialCoeff P kk *
                S.localProx i (centerState.xPrev i) (x i) -
              generalSDCSRawPrimalTerminalCoeff P kk *
                S.localProx i (S.generatedX P hP init samples trace kk i) (x i)) := by
      exact Finset.sum_le_sum (fun i _hi => by
        simpa [kk, centerState, T, coeff] using hRaw i)
    let C : ι → ℝ := fun i =>
      inner ℝ ((S.dualNeighborDisagreement nextState.yPrev) i) (x i) +
        S.localObjective i (x i) +
          P.eta kk * S.localProx i (centerState.xPrev i) (x i)
    let B : ι → ℕ → ℝ := fun i t =>
      (P.eta kk * csBeta (t + 1)) *
          S.localProx i
            (S.generatedInnerQuery P hP init samples trace i kk t)
            (x i) -
        (P.eta kk + P.eta kk * csBeta (t + 1)) *
          S.localProx i
            (S.generatedInnerQuery P hP init samples trace i kk (t + 1))
            (x i)
    let O : ι → ℕ → ℝ := fun i t =>
      let uPrev := S.generatedInnerQuery P hP init samples trace i kk t;
      let δ := S.subgradient i uPrev - S.oracle i uPrev (samples kk i t);
      -inner ℝ δ (x i - uPrev) +
        (S.M + ‖δ‖) ^ 2 / (2 * (P.eta kk * csBeta (t + 1)))
    have hInnerRhs_decomp :
        (∑ i,
          coeff *
            (∑ t ∈ Finset.range T, csLambda (t + 1) *
              (C i + B i t + O i t))) =
          (∑ i, C i) +
            (∑ i, coeff * (∑ t ∈ Finset.range T, csLambda (t + 1) * B i t)) +
              (∑ i, coeff * (∑ t ∈ Finset.range T, csLambda (t + 1) * O i t)) := by
      exact cs_coeff_agent_weighted_three_term_decomp (ι := ι) (T := T) hT C B O
    let innerExpanded : ℝ :=
      ∑ i,
        coeff *
          (∑ t ∈ Finset.range T, csLambda (t + 1) *
            (let uPrev := S.generatedInnerQuery P hP init samples trace i kk t
             let uNext := S.generatedInnerQuery P hP init samples trace i kk (t + 1)
             let δ := S.subgradient i uPrev - S.oracle i uPrev (samples kk i t)
             inner ℝ ((S.dualNeighborDisagreement nextState.yPrev) i) (x i) +
               S.localObjective i (x i) +
                 P.eta kk * S.localProx i (centerState.xPrev i) (x i) -
                 inner ℝ δ (x i - uPrev) +
                 (P.eta kk * csBeta (t + 1)) * S.localProx i uPrev (x i) -
                 (P.eta kk + P.eta kk * csBeta (t + 1)) *
                   S.localProx i uNext (x i) +
                 (S.M + ‖δ‖) ^ 2 /
                   (2 * (P.eta kk * csBeta (t + 1)))))
    let innerCBO : ℝ :=
      ∑ i,
        coeff *
          (∑ t ∈ Finset.range T, csLambda (t + 1) *
            (C i + B i t + O i t))
    have hInnerRhs_as_CBO : innerExpanded = innerCBO := by
      dsimp [innerExpanded, innerCBO]
      refine Finset.sum_congr rfl ?_
      intro i _hi
      apply congrArg (fun z => coeff * z)
      refine Finset.sum_congr rfl ?_
      intro t _ht
      apply congrArg (fun z => csLambda (t + 1) * z)
      dsimp [C, B, O]
      ring
    have hOuterCBO :
        (∑ i,
          (inner ℝ ((S.dualNeighborDisagreement nextState.yPrev) i)
              (S.generatedXHat P hP init samples trace kk i) +
            (S.localObjective i (S.generatedXHat P hP init samples trace kk i) +
              P.eta kk * S.localProx i (centerState.xPrev i)
                (S.generatedXHat P hP init samples trace kk i)))) ≤
          ∑ i,
            coeff *
              (∑ t ∈ Finset.range T, csLambda (t + 1) *
                (C i + B i t + O i t)) := by
      exact le_trans hOuterInner (by
        simpa [innerExpanded, innerCBO] using le_of_eq hInnerRhs_as_CBO)
    let Csum : ℝ := ∑ i, C i
    let Bsum : ℝ :=
      ∑ i, coeff * (∑ t ∈ Finset.range T, csLambda (t + 1) * B i t)
    let Osum : ℝ :=
      ∑ i, coeff * (∑ t ∈ Finset.range T, csLambda (t + 1) * O i t)
    let rawBoundary : ℝ :=
      ∑ i,
        (generalSDCSRawPrimalTelescopeInitialCoeff P kk *
            S.localProx i (centerState.xPrev i) (x i) -
          generalSDCSRawPrimalTerminalCoeff P kk *
            S.localProx i (S.generatedX P hP init samples trace kk i) (x i))
    have hOuterSplit :
        (∑ i,
          (inner ℝ ((S.dualNeighborDisagreement nextState.yPrev) i)
              (S.generatedXHat P hP init samples trace kk i) +
            (S.localObjective i (S.generatedXHat P hP init samples trace kk i) +
              P.eta kk * S.localProx i (centerState.xPrev i)
                (S.generatedXHat P hP init samples trace kk i)))) ≤
          Csum + Bsum + Osum := by
      exact le_trans hOuterCBO (le_of_eq (by simpa [Csum, Bsum, Osum] using hInnerRhs_decomp))
    have hRawSum' : Bsum ≤ rawBoundary := by
      simpa [Bsum, rawBoundary, B] using hRawSum
    have hOuterRaw :
        (∑ i,
          (inner ℝ ((S.dualNeighborDisagreement nextState.yPrev) i)
              (S.generatedXHat P hP init samples trace kk i) +
            (S.localObjective i (S.generatedXHat P hP init samples trace kk i) +
              P.eta kk * S.localProx i (centerState.xPrev i)
                (S.generatedXHat P hP init samples trace kk i)))) ≤
          Csum + rawBoundary + Osum := by
      exact le_trans hOuterSplit (by
        have h := add_le_add_right (add_le_add_left hRawSum' Csum) Osum
        simpa [add_assoc] using h)
    have hOsum_oracle :
        Osum =
          ∑ t ∈ Finset.range T,
            ∑ i,
              let uPrev := S.generatedInnerQuery P hP init samples trace i kk t
              let δ := S.oracleError i uPrev (samples kk i t)
              coeff *
                (-(csLambda (t + 1) * inner ℝ δ (x i - uPrev)) +
                  csLambda (t + 1) *
                    ((S.M + ‖δ‖) ^ 2 / (2 * (P.eta kk * csBeta (t + 1))))) := by
      calc
        Osum =
            ∑ i, coeff * (∑ t ∈ Finset.range T, csLambda (t + 1) * O i t) := by
              rfl
        _ =
            coeff * (∑ t ∈ Finset.range T, csLambda (t + 1) * (∑ i, O i t)) := by
              exact (coeff_mul_weighted_time_agent_sum_comm (ι := ι) T coeff O).symm
        _ =
            ∑ t ∈ Finset.range T, ∑ i, coeff * (csLambda (t + 1) * O i t) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro t _ht
              calc
                coeff * (csLambda (t + 1) * ∑ i, O i t) =
                    coeff * (∑ i, csLambda (t + 1) * O i t) := by
                      rw [Finset.mul_sum]
                _ = ∑ i, coeff * (csLambda (t + 1) * O i t) := by
                      simpa using
                        (Finset.mul_sum (s := (Finset.univ : Finset ι))
                          (f := fun i => csLambda (t + 1) * O i t) coeff)
        _ =
          ∑ t ∈ Finset.range T,
            ∑ i,
              let uPrev := S.generatedInnerQuery P hP init samples trace i kk t
              let δ := S.oracleError i uPrev (samples kk i t)
              coeff *
                (-(csLambda (t + 1) * inner ℝ δ (x i - uPrev)) +
                  csLambda (t + 1) *
                    ((S.M + ‖δ‖) ^ 2 / (2 * (P.eta kk * csBeta (t + 1))))) := by
              refine Finset.sum_congr rfl ?_
              intro t _ht
              refine Finset.sum_congr rfl ?_
              intro i _hi
              dsimp [O, oracleError]
              ring
    have hStackedInner_comm :
        ∀ a b : Stacked ι E, stackedInner a b = stackedInner b a := by
      intro a b
      simp [stackedInner, real_inner_comm]
    have hNetworkPair_symm :
        ∀ a b : Stacked ι E,
          stackedInner (S.networkOperator a) b =
            stackedInner (S.networkOperator b) a := by
      intro a b
      calc
        stackedInner (S.networkOperator a) b =
            stackedInner a (S.networkOperator b) :=
              S.networkIsConnectedLaplacian.2.2 a b
        _ = stackedInner (S.networkOperator b) a := by
              rw [hStackedInner_comm]
    let xHat : Stacked ι E := S.generatedXHat P hP init samples trace kk
    let yNext : Stacked ι E := S.generatedY P hP init samples trace kk
    let xPrev : Stacked ι E := S.generatedX P hP init samples trace (kk - 1)
    let xNext : Stacked ι E := S.generatedX P hP init samples trace kk
    have hPairHat :
        (∑ i,
          inner ℝ ((S.dualNeighborDisagreement nextState.yPrev) i) (xHat i)) =
          stackedInner (S.networkOperator xHat) yNext := by
      calc
        (∑ i,
          inner ℝ ((S.dualNeighborDisagreement nextState.yPrev) i) (xHat i)) =
            stackedInner (S.networkOperator yNext) xHat := by
              simp [stackedInner, dualNeighborDisagreement, yNext, generatedY, nextState]
        _ = stackedInner (S.networkOperator xHat) yNext := hNetworkPair_symm yNext xHat
    have hPairX :
        (∑ i,
          inner ℝ ((S.dualNeighborDisagreement nextState.yPrev) i) (x i)) =
          stackedInner (S.networkOperator x) yNext := by
      calc
        (∑ i,
          inner ℝ ((S.dualNeighborDisagreement nextState.yPrev) i) (x i)) =
            stackedInner (S.networkOperator yNext) x := by
              simp [stackedInner, dualNeighborDisagreement, yNext, generatedY, nextState]
        _ = stackedInner (S.networkOperator x) yNext := hNetworkPair_symm yNext x
    let xTilde : Stacked ι E := S.outerExtrapolation P kk centerState
    have hOuterRaw_primal :
        S.objective xHat + stackedInner (S.networkOperator xHat) yNext +
            P.eta kk * S.stackedProx xPrev xHat ≤
          S.objective x + stackedInner (S.networkOperator x) yNext +
            generalSDCSRawPrimalInitialCoeff P kk * S.stackedProx xPrev x -
              generalSDCSRawPrimalTerminalCoeff P kk * S.stackedProx xNext x + Osum := by
      have hLhs :
          (∑ i,
            (inner ℝ ((S.dualNeighborDisagreement nextState.yPrev) i)
                (S.generatedXHat P hP init samples trace kk i) +
              (S.localObjective i (S.generatedXHat P hP init samples trace kk i) +
                P.eta kk * S.localProx i (centerState.xPrev i)
                  (S.generatedXHat P hP init samples trace kk i)))) =
            stackedInner (S.networkOperator xHat) yNext +
              (S.objective xHat + P.eta kk * S.stackedProx xPrev xHat) := by
        calc
          (∑ i,
            (inner ℝ ((S.dualNeighborDisagreement nextState.yPrev) i)
                (S.generatedXHat P hP init samples trace kk i) +
              (S.localObjective i (S.generatedXHat P hP init samples trace kk i) +
                P.eta kk * S.localProx i (centerState.xPrev i)
                  (S.generatedXHat P hP init samples trace kk i)))) =
              (∑ i, inner ℝ ((S.dualNeighborDisagreement nextState.yPrev) i) (xHat i)) +
                (∑ i, S.localObjective i (xHat i)) +
                  P.eta kk * (∑ i, S.localProx i (xPrev i) (xHat i)) := by
              dsimp [xHat, xPrev, centerState, generatedX, generatedXHat]
              simp [Finset.sum_add_distrib, Finset.mul_sum]
              ring
          _ = stackedInner (S.networkOperator xHat) yNext +
                (S.objective xHat + P.eta kk * S.stackedProx xPrev xHat) := by
              rw [hPairHat]
              dsimp [objective, stackedProx]
              ring
      have hRhs :
          Csum + rawBoundary + Osum =
            stackedInner (S.networkOperator x) yNext +
              (S.objective x + P.eta kk * S.stackedProx xPrev x) +
                (generalSDCSRawPrimalTelescopeInitialCoeff P kk * S.stackedProx xPrev x -
                  generalSDCSRawPrimalTerminalCoeff P kk * S.stackedProx xNext x) + Osum := by
        calc
          Csum + rawBoundary + Osum =
              (∑ i, inner ℝ ((S.dualNeighborDisagreement nextState.yPrev) i) (x i)) +
                (∑ i, S.localObjective i (x i)) +
                  P.eta kk * (∑ i, S.localProx i (xPrev i) (x i)) +
                (generalSDCSRawPrimalTelescopeInitialCoeff P kk *
                    (∑ i, S.localProx i (xPrev i) (x i)) -
                  generalSDCSRawPrimalTerminalCoeff P kk *
                    (∑ i, S.localProx i (xNext i) (x i))) + Osum := by
              dsimp [Csum, rawBoundary, C, xPrev, xNext, centerState, generatedX]
              simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
          _ = stackedInner (S.networkOperator x) yNext +
                (S.objective x + P.eta kk * S.stackedProx xPrev x) +
                  (generalSDCSRawPrimalTelescopeInitialCoeff P kk * S.stackedProx xPrev x -
                    generalSDCSRawPrimalTerminalCoeff P kk * S.stackedProx xNext x) + Osum := by
              rw [hPairX]
              dsimp [objective, stackedProx]
              ring
      have h := hOuterRaw
      rw [hLhs, hRhs] at h
      rw [generalSDCSRawPrimalInitialCoeff_mul_eq_phi_plus_telescope]
      linarith
    have hDualNet :
        stackedInner (S.networkOperator xTilde) (y - yNext) ≤
          P.tau kk / 2 *
            (S.stackedNormSq (y - S.generatedY P hP init samples trace (kk - 1)) -
              S.stackedNormSq (y - yNext) -
                S.stackedNormSq (S.generatedY P hP init samples trace (kk - 1) - yNext)) := by
      simpa [xTilde, kk, centerState, yNext, primalNeighborDisagreement] using hDual
    have hNetworkGapSplit :
        stackedInner (S.networkOperator xHat) y =
          stackedInner (S.networkOperator xHat) yNext +
            stackedInner (S.networkOperator (xHat - xTilde)) (y - yNext) +
              stackedInner (S.networkOperator xTilde) (y - yNext) := by
      dsimp [stackedInner, SOptLib.dependentProductInner]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro i _hi
      simp [ContinuousLinearMap.map_sub, Pi.sub_apply, inner_sub_left, inner_sub_right]
      ring
    have hGapSplit :
        gap k =
          (S.objective xHat + stackedInner (S.networkOperator xHat) yNext -
            (S.objective x + stackedInner (S.networkOperator x) yNext)) +
            stackedInner (S.networkOperator (xHat - xTilde)) (y - yNext) +
              stackedInner (S.networkOperator xTilde) (y - yNext) := by
      calc
        gap k =
            S.objective xHat + stackedInner (S.networkOperator xHat) y -
              (S.objective x + stackedInner (S.networkOperator x) yNext) := by
              dsimp [gap, primalDualGap, xHat, yNext, kk]
        _ =
          (S.objective xHat + stackedInner (S.networkOperator xHat) yNext -
            (S.objective x + stackedInner (S.networkOperator x) yNext)) +
            stackedInner (S.networkOperator (xHat - xTilde)) (y - yNext) +
              stackedInner (S.networkOperator xTilde) (y - yNext) := by
              rw [hNetworkGapSplit]
              ring
    have hDeltaO :
        gap k ≤ deltaRaw (k + 1) + Osum := by
      have hPrimalBracket :
          S.objective xHat + stackedInner (S.networkOperator xHat) yNext -
              (S.objective x + stackedInner (S.networkOperator x) yNext) ≤
            generalSDCSRawPrimalInitialCoeff P kk * S.stackedProx xPrev x -
              generalSDCSRawPrimalTerminalCoeff P kk * S.stackedProx xNext x -
                P.eta kk * S.stackedProx xPrev xHat + Osum := by
        linarith [hOuterRaw_primal]
      have hDeltaUnfold :
          deltaRaw (k + 1) =
            stackedInner (S.networkOperator (xHat - xTilde)) (y - yNext) +
              generalSDCSRawPrimalInitialCoeff P kk * S.stackedProx xPrev x -
                generalSDCSRawPrimalTerminalCoeff P kk * S.stackedProx xNext x -
              P.eta kk * S.stackedProx xPrev xHat +
              P.tau kk / 2 *
                (S.stackedNormSq (y - S.generatedY P hP init samples trace (kk - 1)) -
                  S.stackedNormSq (y - yNext) -
                    S.stackedNormSq
                      (S.generatedY P hP init samples trace (kk - 1) - yNext)) := by
        dsimp [deltaRaw, xHat, xTilde, xPrev, xNext, yNext, centerState, kk,
          generatedX, generatedXHat, generatedY]
      rw [hGapSplit, hDeltaUnfold]
      linarith [hPrimalBracket, hDualNet]
    calc
      gap k ≤ deltaRaw (k + 1) + Osum := hDeltaO
      _ = deltaRaw (k + 1) +
          (let kk := k + 1
           let T := P.innerSteps kk
           ∑ t ∈ Finset.range T,
             ∑ i,
               let uPrev := S.generatedInnerQuery P hP init samples trace i kk t
               let δ := S.oracleError i uPrev (samples kk i t)
               (2 / ((T : ℝ) * ((T : ℝ) + 3))) *
                 (-(csLambda (t + 1) * inner ℝ δ (x i - uPrev)) +
                   csLambda (t + 1) *
                     ((S.M + ‖δ‖) ^ 2 / (2 * (P.eta kk * csBeta (t + 1)))))) := by
            rw [hOsum_oracle]
  have hWeightedStep :
      ∀ k ∈ Finset.range N,
        P.theta (k + 1) * gap k ≤
          P.theta (k + 1) * deltaRaw (k + 1) + weightedOracle k := by
    intro k hk
    have hθ := htheta_range k hk
    let oracleBase : ℝ :=
      let kk := k + 1
      let T := P.innerSteps kk
      ∑ t ∈ Finset.range T,
        ∑ i,
          let uPrev := S.generatedInnerQuery P hP init samples trace i kk t
          let δ := S.oracleError i uPrev (samples kk i t)
          (2 / ((T : ℝ) * ((T : ℝ) + 3))) *
            (-(csLambda (t + 1) * inner ℝ δ (x i - uPrev)) +
              csLambda (t + 1) *
                ((S.M + ‖δ‖) ^ 2 / (2 * (P.eta kk * csBeta (t + 1)))))
    have hstep : gap k ≤ deltaRaw (k + 1) + oracleBase := by
      simpa [oracleBase] using hOneStep k hk
    have hmul :=
      mul_le_mul_of_nonneg_left hstep hθ
    have hscale :
        P.theta (k + 1) * (deltaRaw (k + 1) + oracleBase) =
          P.theta (k + 1) * deltaRaw (k + 1) + weightedOracle k := by
      rw [mul_add]
      congr 1
      dsimp [weightedOracle, oracleBase]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro t ht
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i hi
      ring
    exact le_trans hmul (le_of_eq hscale)
  have hDelta :
      (∑ k ∈ Finset.range N, P.theta (k + 1) * deltaRaw (k + 1)) ≤
        S.generalSDCSRawTerminalPotential P hP init samples trace x N +
          (P.theta 1 * P.tau 1 / 2) * S.stackedNormSq init.y0 +
            stackedInner (S.perturbationVector P hP init samples trace N) y := by
    let mismatchSum : ℝ :=
      ∑ k ∈ Finset.range N,
        let kk := k + 1
        let stPrev := S.generatedState P hP init samples trace (kk - 1)
        let xTilde := S.outerExtrapolation P kk stPrev
        P.theta kk *
          stackedInner
            (S.networkOperator (S.generatedXHat P hP init samples trace kk - xTilde))
            (y - S.generatedY P hP init samples trace kk)
    let proxDropSum : ℝ :=
      ∑ k ∈ Finset.range N,
        let kk := k + 1
        P.theta kk * P.eta kk *
          S.stackedProx (S.generatedX P hP init samples trace (kk - 1))
            (S.generatedXHat P hP init samples trace kk)
    let dualDropSum : ℝ :=
      ∑ k ∈ Finset.range N,
        let kk := k + 1
        P.theta kk * (P.tau kk / 2) *
          (S.stackedNormSq (y - S.generatedY P hP init samples trace (kk - 1)) -
            S.stackedNormSq (y - S.generatedY P hP init samples trace kk) -
              S.stackedNormSq
                (S.generatedY P hP init samples trace (kk - 1) -
                  S.generatedY P hP init samples trace kk))
    have hDeltaExpand :
        (∑ k ∈ Finset.range N, P.theta (k + 1) * deltaRaw (k + 1)) =
          S.generalSDCSRawTerminalPotential P hP init samples trace x N +
            mismatchSum - proxDropSum + dualDropSum := by
      dsimp [mismatchSum, proxDropSum, dualDropSum, deltaRaw,
        generalSDCSRawTerminalPotential]
      simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_add, mul_sub,
        add_assoc]
      have hCoeffSum :
          (∑ k ∈ Finset.range N,
              P.theta (k + 1) *
                (generalSDCSRawPrimalInitialCoeff P (k + 1) *
                  S.stackedProx (S.generatedX P hP init samples trace k) x)) =
            ∑ k ∈ Finset.range N,
              P.theta (k + 1) *
                (generalSDCSRawPrimalTerminalCoeff P (k + 1) *
                  S.stackedProx (S.generatedX P hP init samples trace k) x) := by
        refine Finset.sum_congr rfl ?_
        intro k hk
        have hk_lt : k < N := Finset.mem_range.mp hk
        have hTpos : 0 < P.innerSteps (k + 1) := by
          exact (hDenom (k + 1) (by omega) (by omega)).1
        rw [generalSDCSRawPrimalInitialCoeff_eq_terminalCoeff_of_innerSteps_pos P hTpos]
      rw [hCoeffSum]
      ring
    have h29 := hGeneral.1
    have h30 := hGeneral.2.1
    have h31 := hGeneral.2.2.1
    have h32 := hGeneral.2.2.2.1
    have h33 := hGeneral.2.2.2.2
    have hNonPrimalTelescope :
        mismatchSum - proxDropSum + dualDropSum ≤
          (P.theta 1 * P.tau 1 / 2) * S.stackedNormSq init.y0 +
            stackedInner (S.perturbationVector P hP init samples trace N) y := by
      have hPerturbationPairing :
          stackedInner (S.perturbationVector P hP init samples trace N) y =
            P.theta N *
              stackedInner
                (S.networkOperator
                  (S.generatedXHat P hP init samples trace N -
                    S.generatedX P hP init samples trace (N - 1))) y +
              (P.theta 1 * P.tau 1) *
                stackedInner (S.generatedY P hP init samples trace N - init.y0) y := by
        dsimp [perturbationVector, stackedInner]
        simp [ContinuousLinearMap.map_sub, Pi.sub_apply, inner_add_left, inner_smul_left,
          Finset.sum_add_distrib, Finset.mul_sum]
      -- Source Lemma 8.5 steps 7-14: use (8.3.30) for the lagged inner-product
      -- telescope, (8.3.31) for the dual-distance boundary, and
      -- (8.3.32)-(8.3.33) with `stackedProx_lower_bound` to absorb the
      -- operator-norm Young terms.
      have hStackedInner_sub_smul_left :
          ∀ (a b c : Stacked ι E) (r : ℝ),
            stackedInner (a - r • b) c =
              stackedInner c a - r * stackedInner c b := by
        intro a b c r
        dsimp [stackedInner]
        simp [inner_sub_left, inner_smul_left, real_inner_comm,
          Finset.sum_sub_distrib, Finset.mul_sum]
      have hLagState :
          ∀ t, 1 ≤ t →
            (S.generatedState P hP init samples trace (t - 1)).xLag =
              S.generatedX P hP init samples trace (t - 2) := by
        intro t ht
        by_cases ht2 : 2 ≤ t
        · have hj : 1 ≤ t - 1 := by omega
          have hstep := (trace.step_spec (t - 1) hj).1
          have hidx : (t - 1) - 1 = t - 2 := by omega
          simpa [generatedState, generatedX, hidx] using hstep
        · have ht_eq : t = 1 := by omega
          subst ht_eq
          simp [generatedState, generatedX, initialOuterState, trace.initial_state]
      let delta : ℕ → Stacked ι E := fun t =>
        S.networkOperator
          (S.generatedXHat P hP init samples trace t -
            S.generatedX P hP init samples trace (t - 1))
      let ydiff : ℕ → Stacked ι E := fun t =>
        y - S.generatedY P hP init samples trace t
      have hOuterDelta :
          ∀ t, 1 ≤ t →
            S.networkOperator
              (S.generatedXHat P hP init samples trace t -
                S.outerExtrapolation P t
                  (S.generatedState P hP init samples trace (t - 1))) =
              delta t - P.alpha t • delta (t - 1) := by
        intro t ht
        calc
          S.networkOperator
              (S.generatedXHat P hP init samples trace t -
                S.outerExtrapolation P t
                  (S.generatedState P hP init samples trace (t - 1))) =
              S.networkOperator
                ((S.generatedXHat P hP init samples trace t -
                    S.generatedX P hP init samples trace (t - 1)) -
                  P.alpha t •
                    (S.generatedXHat P hP init samples trace (t - 1) -
                      S.generatedX P hP init samples trace (t - 2))) := by
                congr 1
                ext i
                simp [outerExtrapolation, generatedX, generatedXHat,
                  hLagState t ht, Pi.sub_apply, Pi.add_apply]
                abel
          _ = delta t - P.alpha t • delta (t - 1) := by
                have hidx : t - 1 - 1 = t - 2 := by omega
                simp [delta, ContinuousLinearMap.map_sub, hidx]
      have hDeltaZero : delta 0 = 0 := by
        simp [delta, generatedXHat, generatedX, generatedState, initialOuterState,
          trace.initial_state]
      have hcoeff :
          ∀ t, 2 ≤ t → t ≤ N → P.theta t * P.alpha t / (1 : ℝ) =
            P.theta (t - 1) := by
        intro t ht2 htN
        rw [div_one, mul_comm, h30 t ht2 htN]
      have htel :=
        sum_Icc_weighted_lagged_stackedInner_telescope_eq_terminal_sub
          P.theta P.alpha (1 : ℝ) (0 : Stacked ι E) ydiff delta hN hcoeff hDeltaZero
      have hMismatchAsTelescopeLhs :
          mismatchSum =
            ∑ t ∈ Finset.Icc 1 N,
              P.theta t *
                (stackedInner (ydiff t - (0 : Stacked ι E)) (delta t) -
                  (P.alpha t / (1 : ℝ)) *
                    stackedInner (ydiff t - (0 : Stacked ι E)) (delta (t - 1))) := by
        dsimp [mismatchSum]
        rw [sum_Icc_one_eq_sum_range_succ N
          (fun t =>
            P.theta t *
              (stackedInner (ydiff t - (0 : Stacked ι E)) (delta t) -
                (P.alpha t / (1 : ℝ)) *
                  stackedInner (ydiff t - (0 : Stacked ι E)) (delta (t - 1))))]
        refine Finset.sum_congr rfl ?_
        intro k hk
        have hk1 : 1 ≤ k + 1 := Nat.succ_pos k
        have hOD :
            S.networkOperator
              (S.generatedXHat P hP init samples trace (k + 1) -
                S.outerExtrapolation P (k + 1)
                  (S.generatedState P hP init samples trace k)) =
              delta (k + 1) - P.alpha (k + 1) • delta (k + 1 - 1) := by
          simpa using hOuterDelta (k + 1) hk1
        rw [hOD, hStackedInner_sub_smul_left]
        simp [ydiff]
      have hMismatchTel :
          mismatchSum =
            P.theta N * stackedInner (delta N) (ydiff N) -
              ∑ t ∈ Finset.Icc 2 N,
                P.theta t * P.alpha t *
                  stackedInner (delta (t - 1))
                    (S.generatedY P hP init samples trace (t - 1) -
                      S.generatedY P hP init samples trace t) := by
        rw [hMismatchAsTelescopeLhs, htel]
        congr 1
        · dsimp [ydiff]
          dsimp [stackedInner]
          simp [real_inner_comm]
        · refine Finset.sum_congr rfl ?_
          intro t ht
          dsimp [ydiff]
          dsimp [stackedInner]
          simp [real_inner_comm]
      have hNonPrimalAfterMismatch :
          (P.theta N * stackedInner (delta N) (ydiff N) -
              ∑ t ∈ Finset.Icc 2 N,
                P.theta t * P.alpha t *
                  stackedInner (delta (t - 1))
                    (S.generatedY P hP init samples trace (t - 1) -
                      S.generatedY P hP init samples trace t)) -
              proxDropSum + dualDropSum ≤
            (P.theta 1 * P.tau 1 / 2) * S.stackedNormSq init.y0 +
              stackedInner (S.perturbationVector P hP init samples trace N) y := by
        have hDelta_network_norm_sq :
            ∀ t,
              S.stackedNormSq (delta t) ≤
                S.networkOperatorNorm ^ 2 *
                  S.stackedNormSq
                    (S.generatedXHat P hP init samples trace t -
                      S.generatedX P hP init samples trace (t - 1)) := by
          intro t
          simpa [delta] using
            stacked_network_operator_norm_sq_le S
              (S.generatedXHat P hP init samples trace t -
                S.generatedX P hP init samples trace (t - 1))
        let dx : ℕ → Stacked ι E := fun t =>
          S.generatedXHat P hP init samples trace t -
            S.generatedX P hP init samples trace (t - 1)
        let ystep : ℕ → Stacked ι E := fun t =>
          S.generatedY P hP init samples trace t -
            S.generatedY P hP init samples trace (t - 1)
        have hDelta_network_norm_sq_dx :
            ∀ t,
              S.stackedNormSq (delta t) ≤
                S.networkOperatorNorm ^ 2 * S.stackedNormSq (dx t) := by
          intro t
          simpa [dx] using hDelta_network_norm_sq t
        have hTerminalYoungYdiff :
            P.theta N * stackedInner (delta N) (ydiff N) ≤
              (P.theta N * P.eta N / 2) * S.stackedNormSq (dx N) +
                (P.theta 1 * P.tau 1 / 2) * S.stackedNormSq (ydiff N) := by
          have hthetaN : 0 ≤ P.theta N := hTheta_nonneg N hN le_rfl
          have hetaN : 0 ≤ P.eta N := ValidParameters.eta_nonneg hP N
          have htau1 : 0 ≤ P.tau 1 := ValidParameters.tau_nonneg hP 1
          have htheta1 : 0 ≤ P.theta 1 := hTheta_nonneg 1 (by omega) hN
          have hA : 0 ≤ P.theta N * P.eta N / 2 := by positivity
          have hB : 0 ≤ P.theta 1 * P.tau 1 / 2 := by positivity
          have hc : 0 ≤ P.theta N := hthetaN
          have hK : 0 ≤ S.networkOperatorNorm ^ 2 := sq_nonneg _
          have hq :
              0 ≤ S.stackedNormSq (dx N) :=
            S.stackedNormSq_nonneg _
          have hcoef :
              P.theta N ^ 2 * S.networkOperatorNorm ^ 2 ≤
                4 * (P.theta N * P.eta N / 2) *
                  (P.theta 1 * P.tau 1 / 2) := by
            nlinarith [h33, hthetaN]
          exact
            stacked_inner_young_absorption_of_sq_bound_nonneg S
              (A := P.theta N * P.eta N / 2)
              (B := P.theta 1 * P.tau 1 / 2)
              (c := P.theta N)
              (K := S.networkOperatorNorm ^ 2)
              (q := S.stackedNormSq (dx N))
              (g := delta N) (v := ydiff N)
              hA hB hc hK hq hcoef (hDelta_network_norm_sq_dx N)
        have hLaggedYoungPointwise :
            ∀ t ∈ Finset.Icc 2 N,
              P.theta t * P.alpha t *
                  stackedInner (delta (t - 1)) (ystep t) ≤
                (P.theta (t - 1) * P.eta (t - 1) / 2) *
                    S.stackedNormSq (dx (t - 1)) +
                  (P.theta t * P.tau t / 2) * S.stackedNormSq (ystep t) := by
          intro t ht
          have ht2 : 2 ≤ t := (Finset.mem_Icc.mp ht).1
          have htN : t ≤ N := (Finset.mem_Icc.mp ht).2
          have htPrev1 : 1 ≤ t - 1 := by omega
          have htPrevN : t - 1 ≤ N := by omega
          have hthetaPrev : 0 ≤ P.theta (t - 1) :=
            hTheta_nonneg (t - 1) htPrev1 htPrevN
          have htheta : 0 ≤ P.theta t :=
            hTheta_nonneg t (by omega) htN
          have halpha : 0 ≤ P.alpha t := ValidParameters.alpha_nonneg hP t
          have hetaPrev : 0 ≤ P.eta (t - 1) := ValidParameters.eta_nonneg hP (t - 1)
          have htau : 0 ≤ P.tau t := ValidParameters.tau_nonneg hP t
          have hlink : P.alpha t * P.theta t = P.theta (t - 1) :=
            h30 t ht2 htN
          have hcond :
              P.alpha t * S.networkOperatorNorm ^ 2 ≤
                P.eta (t - 1) * P.tau t :=
            h32 t ht2 htN
          exact
            sdcs_lagged_young_absorption S
              (thetaPrev := P.theta (t - 1)) (theta := P.theta t)
              (alpha := P.alpha t) (etaPrev := P.eta (t - 1))
              (tau := P.tau t) (g := delta (t - 1))
              (dx := dx (t - 1)) (dy := ystep t)
              hthetaPrev htheta halpha hetaPrev htau hlink hcond
              (hDelta_network_norm_sq_dx (t - 1))
        have hLaggedYoungSum :
            (∑ t ∈ Finset.Icc 2 N,
              P.theta t * P.alpha t *
                stackedInner (delta (t - 1)) (ystep t)) ≤
              ∑ t ∈ Finset.Icc 2 N,
                ((P.theta (t - 1) * P.eta (t - 1) / 2) *
                    S.stackedNormSq (dx (t - 1)) +
                  (P.theta t * P.tau t / 2) * S.stackedNormSq (ystep t)) := by
          exact Finset.sum_le_sum hLaggedYoungPointwise
        have hProxDropLower :
            (∑ k ∈ Finset.range N,
              (P.theta (k + 1) * P.eta (k + 1) / 2) *
                S.stackedNormSq (dx (k + 1))) ≤ proxDropSum := by
          dsimp [proxDropSum]
          refine Finset.sum_le_sum ?_
          intro k hk
          have hkk1 : 1 ≤ k + 1 := Nat.succ_pos k
          have hkkN : k + 1 ≤ N := Nat.succ_le_of_lt (Finset.mem_range.mp hk)
          have htheta : 0 ≤ P.theta (k + 1) :=
            hTheta_nonneg (k + 1) hkk1 hkkN
          have heta : 0 ≤ P.eta (k + 1) :=
            ValidParameters.eta_nonneg hP (k + 1)
          have hweight : 0 ≤ P.theta (k + 1) * P.eta (k + 1) :=
            mul_nonneg htheta heta
          have hxprev :
              S.FeasiblePoint (S.generatedX P hP init samples trace k) := by
            simpa [generatedX, generatedState] using
              (S.generatedState P hP init samples trace k).xPrev_mem
          have hxhat :
              S.FeasiblePoint
                (S.generatedXHat P hP init samples trace (k + 1)) :=
            S.generatedXHat_mem P hP init samples trace (k + 1) hkk1
              (hDenom (k + 1) hkk1 hkkN).1
          have hprox :=
            S.stackedProx_lower_bound
              (S.generatedX P hP init samples trace k)
              (S.generatedXHat P hP init samples trace (k + 1))
              hxprev hxhat
          have hprox_dx :
              (1 / 2 : ℝ) * S.stackedNormSq (dx (k + 1)) ≤
                S.stackedProx (S.generatedX P hP init samples trace k)
                  (S.generatedXHat P hP init samples trace (k + 1)) := by
            simpa [dx, stackedNormSq_sub_comm S
              (S.generatedXHat P hP init samples trace (k + 1))
              (S.generatedX P hP init samples trace k)] using hprox
          have hscaled :=
            mul_le_mul_of_nonneg_left hprox_dx hweight
          nlinarith
        have hTerminalYoungNegY :
            -(P.theta N * stackedInner (delta N)
                (S.generatedY P hP init samples trace N)) ≤
              (P.theta N * P.eta N / 2) * S.stackedNormSq (dx N) +
                (P.theta 1 * P.tau 1 / 2) *
                  S.stackedNormSq (S.generatedY P hP init samples trace N) := by
          have hthetaN : 0 ≤ P.theta N := hTheta_nonneg N hN le_rfl
          have hetaN : 0 ≤ P.eta N := ValidParameters.eta_nonneg hP N
          have htau1 : 0 ≤ P.tau 1 := ValidParameters.tau_nonneg hP 1
          have htheta1 : 0 ≤ P.theta 1 := hTheta_nonneg 1 (by omega) hN
          have hA : 0 ≤ P.theta N * P.eta N / 2 := by positivity
          have hB : 0 ≤ P.theta 1 * P.tau 1 / 2 := by positivity
          have hK : 0 ≤ S.networkOperatorNorm ^ 2 := sq_nonneg _
          have hq : 0 ≤ S.stackedNormSq (dx N) := S.stackedNormSq_nonneg _
          have hcoef :
              P.theta N ^ 2 * S.networkOperatorNorm ^ 2 ≤
                4 * (P.theta N * P.eta N / 2) *
                  (P.theta 1 * P.tau 1 / 2) := by
            nlinarith [h33, hthetaN]
          have hy :=
            stacked_inner_young_absorption_of_sq_bound_nonneg S
              (A := P.theta N * P.eta N / 2)
              (B := P.theta 1 * P.tau 1 / 2)
              (c := P.theta N)
              (K := S.networkOperatorNorm ^ 2)
              (q := S.stackedNormSq (dx N))
              (g := delta N)
              (v := -S.generatedY P hP init samples trace N)
              hA hB hthetaN hK hq hcoef (hDelta_network_norm_sq_dx N)
          simpa [stackedNormSq, stackedInner, Finset.mul_sum] using hy
        have hDualDropUpper :
            dualDropSum ≤
              (P.theta 1 * P.tau 1 / 2) *
                (S.stackedNormSq (y - init.y0) -
                  S.stackedNormSq
                    (y - S.generatedY P hP init samples trace N)) -
                ∑ t ∈ Finset.Icc 2 N,
                  P.theta t * (P.tau t / 2) * S.stackedNormSq (ystep t) := by
          have hY0 :
              S.generatedY P hP init samples trace 0 = init.y0 := by
            simp [generatedY, generatedState, initialOuterState, trace.initial_state]
          have hc_nonneg : 0 ≤ P.theta 1 * P.tau 1 := by
            exact mul_nonneg (hTheta_nonneg 1 (by omega) hN)
              (ValidParameters.tau_nonneg hP 1)
          have hE_nonneg :
              ∀ t, 1 ≤ t → t ≤ N →
                0 ≤ S.stackedNormSq
                  (S.generatedY P hP init samples trace (t - 1) -
                    S.generatedY P hP init samples trace t) := by
            intro t _ht1 _htN
            exact S.stackedNormSq_nonneg _
          have hdual :=
            sdcs_dual_drop_sum_le_endpoint_sub_tail
              P.theta P.tau
              (fun k => S.stackedNormSq
                (y - S.generatedY P hP init samples trace k))
              (fun t => S.stackedNormSq
                (S.generatedY P hP init samples trace (t - 1) -
                  S.generatedY P hP init samples trace t))
              N hN hc_nonneg h31 hE_nonneg
          simpa [dualDropSum, ystep, hY0, stackedNormSq_sub_comm S] using hdual
        let terminalPrimal : ℝ :=
          (P.theta N * P.eta N / 2) * S.stackedNormSq (dx N)
        let laggedPrimal : ℝ :=
          ∑ t ∈ Finset.Icc 2 N,
            (P.theta (t - 1) * P.eta (t - 1) / 2) *
              S.stackedNormSq (dx (t - 1))
        let dualTailA : ℝ :=
          ∑ t ∈ Finset.Icc 2 N,
            P.theta t * P.tau t / 2 * S.stackedNormSq (ystep t)
        let dualTailB : ℝ :=
          ∑ t ∈ Finset.Icc 2 N,
            P.theta t * (P.tau t / 2) * S.stackedNormSq (ystep t)
        let terminalDual : ℝ :=
          (P.theta 1 * P.tau 1 / 2) *
            S.stackedNormSq (S.generatedY P hP init samples trace N)
        let endpointDual : ℝ :=
          (P.theta 1 * P.tau 1 / 2) *
            (S.stackedNormSq (y - init.y0) -
              S.stackedNormSq
                (y - S.generatedY P hP init samples trace N))
        let perturbTail : ℝ :=
          P.theta 1 * P.tau 1 *
            stackedInner (S.generatedY P hP init samples trace N - init.y0) y
        have hTerminalSplit :
            P.theta N * stackedInner (delta N) (ydiff N) ≤
              P.theta N * stackedInner (delta N) y +
                terminalPrimal + terminalDual := by
          have hsplit :
              P.theta N * stackedInner (delta N) (ydiff N) =
                P.theta N * stackedInner (delta N) y +
                  -(P.theta N *
                    stackedInner (delta N)
                      (S.generatedY P hP init samples trace N)) := by
            dsimp [ydiff, stackedInner, SOptLib.dependentProductInner]
            rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
              ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl ?_
            intro i _hi
            simp [Pi.sub_apply, inner_sub_right]
            ring
          dsimp [terminalPrimal, terminalDual]
          linarith [hTerminalYoungNegY]
        have hLaggedOrientation :
            -(∑ t ∈ Finset.Icc 2 N,
                P.theta t * P.alpha t *
                  stackedInner (delta (t - 1))
                    (S.generatedY P hP init samples trace (t - 1) -
                      S.generatedY P hP init samples trace t)) ≤
              laggedPrimal + dualTailA := by
          have hsign :
              -(∑ t ∈ Finset.Icc 2 N,
                  P.theta t * P.alpha t *
                    stackedInner (delta (t - 1))
                      (S.generatedY P hP init samples trace (t - 1) -
                        S.generatedY P hP init samples trace t)) =
                ∑ t ∈ Finset.Icc 2 N,
                  P.theta t * P.alpha t *
                    stackedInner (delta (t - 1)) (ystep t) := by
            rw [← Finset.sum_neg_distrib]
            refine Finset.sum_congr rfl ?_
            intro t ht
            dsimp [ystep, stackedInner]
            simp [Pi.sub_apply, inner_sub_right, Finset.sum_sub_distrib,
              Finset.mul_sum]
            ring
          calc
            -(∑ t ∈ Finset.Icc 2 N,
                P.theta t * P.alpha t *
                  stackedInner (delta (t - 1))
                    (S.generatedY P hP init samples trace (t - 1) -
                      S.generatedY P hP init samples trace t))
                = ∑ t ∈ Finset.Icc 2 N,
                    P.theta t * P.alpha t *
                      stackedInner (delta (t - 1)) (ystep t) := hsign
            _ ≤ ∑ t ∈ Finset.Icc 2 N,
                ((P.theta (t - 1) * P.eta (t - 1) / 2) *
                    S.stackedNormSq (dx (t - 1)) +
                  (P.theta t * P.tau t / 2) * S.stackedNormSq (ystep t)) :=
                  hLaggedYoungSum
            _ = laggedPrimal + dualTailA := by
                  dsimp [laggedPrimal, dualTailA]
                  rw [Finset.sum_add_distrib]
        have hProxBudget :
            terminalPrimal + laggedPrimal ≤ proxDropSum := by
          let A : ℕ → ℝ := fun t =>
            (P.theta t * P.eta t / 2) * S.stackedNormSq (dx t)
          have hsum_eq :
              (∑ k ∈ Finset.range N,
                (P.theta (k + 1) * P.eta (k + 1) / 2) *
                  S.stackedNormSq (dx (k + 1))) =
                terminalPrimal + laggedPrimal := by
            calc
              (∑ k ∈ Finset.range N,
                (P.theta (k + 1) * P.eta (k + 1) / 2) *
                  S.stackedNormSq (dx (k + 1))) =
                  ∑ t ∈ Finset.Icc 1 N, A t := by
                    rw [sum_Icc_one_eq_sum_range_succ]
              _ = A N + ∑ t ∈ Finset.Icc 2 N, A (t - 1) := by
                    exact sum_Icc_one_eq_terminal_add_lagged A N hN
              _ = terminalPrimal + laggedPrimal := by
                    dsimp [A, terminalPrimal, laggedPrimal]
          simpa [hsum_eq] using hProxDropLower
        have hDualTailEq : dualTailA = dualTailB := by
          dsimp [dualTailA, dualTailB]
          refine Finset.sum_congr rfl ?_
          intro t ht
          ring
        have hDualEndpoint :
            terminalDual + endpointDual =
              (P.theta 1 * P.tau 1 / 2) * S.stackedNormSq init.y0 +
                perturbTail := by
          dsimp [terminalDual, endpointDual, perturbTail]
          simpa [mul_assoc] using
            (stackedNormSq_endpoint_dual_identity S
              (P.theta 1 * P.tau 1) y init.y0
              (S.generatedY P hP init samples trace N))
        have hPerturb :
            P.theta N * stackedInner (delta N) y + perturbTail =
              stackedInner (S.perturbationVector P hP init samples trace N) y := by
          simpa [delta, perturbTail] using hPerturbationPairing.symm
        exact
          sdcs_nonprimal_assembly_algebra
            (term := P.theta N * stackedInner (delta N) (ydiff N))
            (lagged :=
              ∑ t ∈ Finset.Icc 2 N,
                P.theta t * P.alpha t *
                  stackedInner (delta (t - 1))
                    (S.generatedY P hP init samples trace (t - 1) -
                      S.generatedY P hP init samples trace t))
            (prox := proxDropSum) (dual := dualDropSum)
            (linY := P.theta N * stackedInner (delta N) y)
            (primal := terminalPrimal) (terminalDual := terminalDual)
            (laggedPrimal := laggedPrimal) (dualTailA := dualTailA)
            (dualTailB := dualTailB) (endpointDual := endpointDual)
            (initDual := (P.theta 1 * P.tau 1 / 2) * S.stackedNormSq init.y0)
            (perturbTail := perturbTail)
            (perturb := stackedInner (S.perturbationVector P hP init samples trace N) y)
            hTerminalSplit hLaggedOrientation hProxBudget hDualDropUpper hDualTailEq
            hDualEndpoint hPerturb
      rw [hMismatchTel]
      exact hNonPrimalAfterMismatch
    rw [hDeltaExpand]
    linarith [hNonPrimalTelescope]
  have horacle :
      (∑ k ∈ Finset.range N, weightedOracle k) =
        S.generalSDCSRawOracleErrorBudget P hP init samples trace x N := by
    simp [weightedOracle, generalSDCSRawOracleErrorBudget]
  have hagg :=
    weighted_gap_sum_le_of_weighted_one_step_and_delta_budget
      N (fun k => P.theta (k + 1)) gap (fun k => deltaRaw (k + 1)) weightedOracle
      (S.generalSDCSRawTerminalPotential P hP init samples trace x N +
        (P.theta 1 * P.tau 1 / 2) * S.stackedNormSq init.y0 +
          stackedInner (S.perturbationVector P hP init samples trace N) y)
      (S.generalSDCSRawOracleErrorBudget P hP init samples trace x N)
      hWeightedStep hDelta horacle
  simpa [gap, generalSDCSGapLemma85RawTerminalRHS, add_assoc] using hagg

set_option maxHeartbeats 200000

/-- Convert the aggregate weighted `Q` inequality of Lemma 8.5 to the gap at the
weighted generated output. -/
private theorem general_sdcs_weighted_average_gap_bound_from_sum
    (P : Parameters) (hP : ValidParameters P) (init : InitialState S)
    (samples : ℕ → ι → ℕ → Ξ) (trace : S.GeneratedTrace P hP init samples)
    (N : ℕ)
    (hDenom : ∀ k, 1 ≤ k → k ≤ N → 0 < P.innerSteps k ∧ 0 < P.eta k)
    (hTheta_nonneg : ∀ k, 1 ≤ k → k ≤ N → 0 ≤ P.theta k)
    (hTheta_sum_pos : 0 < ∑ k ∈ Finset.range N, P.theta (k + 1))
    (hWeightedQ :
      ∀ x y : Stacked ι E,
        S.FeasiblePoint x →
          (∑ k ∈ Finset.range N,
            P.theta (k + 1) *
              S.primalDualGap
                (S.generatedXHat P hP init samples trace (k + 1))
                (S.generatedY P hP init samples trace (k + 1)) x y) ≤
            S.generalSDCSGapLemma85RawTerminalRHS P hP init samples trace x y N) :
    ∀ x y : Stacked ι E,
      S.FeasiblePoint x →
        S.primalDualGap
            (S.weightedPrimalAverage P hP init samples trace N)
            (S.weightedDualAverage P hP init samples trace N) x y ≤
          (∑ k ∈ Finset.range N, P.theta (k + 1))⁻¹ *
            S.generalSDCSGapLemma85RawTerminalRHS P hP init samples trace x y N := by
  classical
  intro x y hx
  let W : ℝ := ∑ k ∈ Finset.range N, P.theta (k + 1)
  have hW_pos : 0 < W := by
    simpa [W] using hTheta_sum_pos
  have hW_nonneg : 0 ≤ W⁻¹ := inv_nonneg.mpr hW_pos.le
  have htheta_range : ∀ k ∈ Finset.range N, 0 ≤ P.theta (k + 1) := by
    intro k hk
    exact hTheta_nonneg (k + 1) (Nat.succ_pos k) (Nat.succ_le_of_lt (Finset.mem_range.mp hk))
  have hObjJensen :
      S.objective (S.weightedPrimalAverage P hP init samples trace N) ≤
        W⁻¹ *
          (∑ k ∈ Finset.range N,
            P.theta (k + 1) *
              S.objective (S.generatedXHat P hP init samples trace (k + 1))) := by
    let X : ι → Set E := fun i => S.feasible i
    let f : ι → E → ℝ := fun i z => S.localObjective i z
    let p : ℕ → ι → E := fun k =>
      S.generatedXHat P hP init samples trace (k + 1)
    have hf : ∀ i, ConvexOn ℝ (X i) (f i) := by
      intro i
      simpa [X, f] using S.localObjective_convexOn_feasible_of_objectiveGrowth i
    have hp_mem : ∀ k ∈ Finset.range N, ∀ i, p k i ∈ X i := by
      intro k hk i
      have hkN : k + 1 ≤ N := Nat.succ_le_of_lt (Finset.mem_range.mp hk)
      have hT : 0 < P.innerSteps (k + 1) :=
        (hDenom (k + 1) (Nat.succ_pos k) hkN).1
      simpa [p, X] using
        S.generatedXHat_mem P hP init samples trace (k + 1) (Nat.succ_pos k) hT i
    have hW_eq : W = ∑ k ∈ Finset.range N, P.theta (k + 1) := by
      rfl
    have hxbar :
        ∀ i,
          S.weightedPrimalAverage P hP init samples trace N i =
            W⁻¹ • ∑ k ∈ Finset.range N, P.theta (k + 1) • p k i := by
      intro i
      simp [weightedPrimalAverage, W, p]
    have hraw :=
      sum_convexOn_weighted_average_le_weighted_sum
        (I := ι) (T := ℕ) (E := E)
        (s := Finset.range N) (γ := fun k => P.theta (k + 1))
        (X := X) (f := f) (p := p)
        (xbar := S.weightedPrimalAverage P hP init samples trace N) (W := W)
        hf htheta_range hp_mem hW_pos hW_eq hxbar
    simpa [objective, X, f, p, W] using hraw
  have hJensen :
      S.primalDualGap
          (S.weightedPrimalAverage P hP init samples trace N)
          (S.weightedDualAverage P hP init samples trace N) x y ≤
        W⁻¹ *
          (∑ k ∈ Finset.range N,
            P.theta (k + 1) *
              S.primalDualGap
                (S.generatedXHat P hP init samples trace (k + 1))
                (S.generatedY P hP init samples trace (k + 1)) x y) := by
    -- Weighted-output convexity of `Q`: Jensen for the primal objective plus
    -- affine finite-sum identities for the two network-pairing terms.
    have hWeightedLeft :
        ∀ (a : ℝ) (v : ℕ → Stacked ι E) (u : Stacked ι E),
          stackedInner (a • ∑ k ∈ Finset.range N, P.theta (k + 1) • v k) u =
            a * ∑ k ∈ Finset.range N, P.theta (k + 1) * stackedInner (v k) u := by
      intro a v u
      let s : Finset ℕ := Finset.range N
      change
        stackedInner (a • ∑ k ∈ s, P.theta (k + 1) • v k) u =
          a * ∑ k ∈ s, P.theta (k + 1) * stackedInner (v k) u
      induction s using Finset.induction_on with
      | empty =>
          simp [stackedInner]
      | insert k s hks ih =>
          rw [Finset.sum_insert hks, Finset.sum_insert hks]
          calc
            stackedInner
                (a • (P.theta (k + 1) • v k +
                  ∑ x ∈ s, P.theta (x + 1) • v x)) u =
                a * (P.theta (k + 1) * stackedInner (v k) u) +
                  stackedInner (a • ∑ x ∈ s, P.theta (x + 1) • v x) u := by
                  simp [stackedInner, smul_add, smul_smul, inner_add_left,
                    inner_smul_left, Finset.sum_add_distrib]
                  rw [← Finset.mul_sum]
                  ring
            _ =
                a * (P.theta (k + 1) * stackedInner (v k) u +
                  ∑ x ∈ s, P.theta (x + 1) * stackedInner (v x) u) := by
                  rw [ih]
                  ring
    have hWeightedRight :
        ∀ (a : ℝ) (u : Stacked ι E) (v : ℕ → Stacked ι E),
          stackedInner u (a • ∑ k ∈ Finset.range N, P.theta (k + 1) • v k) =
            a * ∑ k ∈ Finset.range N, P.theta (k + 1) * stackedInner u (v k) := by
      intro a u v
      let s : Finset ℕ := Finset.range N
      change
        stackedInner u (a • ∑ k ∈ s, P.theta (k + 1) • v k) =
          a * ∑ k ∈ s, P.theta (k + 1) * stackedInner u (v k)
      induction s using Finset.induction_on with
      | empty =>
          simp [stackedInner]
      | insert k s hks ih =>
          rw [Finset.sum_insert hks, Finset.sum_insert hks]
          calc
            stackedInner u
                (a • (P.theta (k + 1) • v k +
                  ∑ x ∈ s, P.theta (x + 1) • v x)) =
                a * (P.theta (k + 1) * stackedInner u (v k)) +
                  stackedInner u (a • ∑ x ∈ s, P.theta (x + 1) • v x) := by
                  simp [stackedInner, smul_add, smul_smul, inner_add_right,
                    inner_smul_right, Finset.sum_add_distrib]
                  rw [← Finset.mul_sum]
                  ring
            _ =
                a * (P.theta (k + 1) * stackedInner u (v k) +
                  ∑ x ∈ s, P.theta (x + 1) * stackedInner u (v x)) := by
                  rw [ih]
                  ring
    have hPairX :
        stackedInner (S.networkOperator (S.weightedPrimalAverage P hP init samples trace N)) y =
          W⁻¹ *
            (∑ k ∈ Finset.range N,
              P.theta (k + 1) *
                stackedInner
                  (S.networkOperator (S.generatedXHat P hP init samples trace (k + 1))) y) := by
      calc
        stackedInner (S.networkOperator (S.weightedPrimalAverage P hP init samples trace N)) y =
            stackedInner
              (W⁻¹ • ∑ k ∈ Finset.range N,
                P.theta (k + 1) •
                  S.networkOperator
                    (S.generatedXHat P hP init samples trace (k + 1))) y := by
              simp [weightedPrimalAverage, W, map_sum]
        _ =
            W⁻¹ *
              (∑ k ∈ Finset.range N,
                P.theta (k + 1) *
                  stackedInner
                    (S.networkOperator
                      (S.generatedXHat P hP init samples trace (k + 1))) y) := by
              exact hWeightedLeft W⁻¹
                (fun k => S.networkOperator
                  (S.generatedXHat P hP init samples trace (k + 1))) y
    have hPairY :
        stackedInner (S.networkOperator x) (S.weightedDualAverage P hP init samples trace N) =
          W⁻¹ *
            (∑ k ∈ Finset.range N,
              P.theta (k + 1) *
                stackedInner (S.networkOperator x)
                  (S.generatedY P hP init samples trace (k + 1))) := by
      calc
        stackedInner (S.networkOperator x) (S.weightedDualAverage P hP init samples trace N) =
            stackedInner (S.networkOperator x)
              (W⁻¹ • ∑ k ∈ Finset.range N,
                P.theta (k + 1) • S.generatedY P hP init samples trace (k + 1)) := by
              simp [weightedDualAverage, W]
        _ =
            W⁻¹ *
              (∑ k ∈ Finset.range N,
                P.theta (k + 1) *
                  stackedInner (S.networkOperator x)
                    (S.generatedY P hP init samples trace (k + 1))) := by
              exact hWeightedRight W⁻¹ (S.networkOperator x)
                (fun k => S.generatedY P hP init samples trace (k + 1))
    have hW_ne : W ≠ 0 := ne_of_gt hW_pos
    have hW_norm :
        W⁻¹ * (∑ k ∈ Finset.range N, P.theta (k + 1)) = 1 := by
      rw [show (∑ k ∈ Finset.range N, P.theta (k + 1)) = W by rfl]
      exact inv_mul_cancel₀ hW_ne
    have hConstObj :
        W⁻¹ * (∑ k ∈ Finset.range N, P.theta (k + 1) * S.objective x) =
          S.objective x := by
      calc
        W⁻¹ * (∑ k ∈ Finset.range N, P.theta (k + 1) * S.objective x) =
            W⁻¹ * ((∑ k ∈ Finset.range N, P.theta (k + 1)) * S.objective x) := by
              rw [Finset.sum_mul]
        _ =
            (W⁻¹ * (∑ k ∈ Finset.range N, P.theta (k + 1))) * S.objective x := by
              ring
        _ = S.objective x := by
              rw [hW_norm]
              ring
    have hLeft :
        S.primalDualGap
            (S.weightedPrimalAverage P hP init samples trace N)
            (S.weightedDualAverage P hP init samples trace N) x y =
          S.objective (S.weightedPrimalAverage P hP init samples trace N) +
            stackedInner
              (S.networkOperator (S.weightedPrimalAverage P hP init samples trace N)) y -
            S.objective x -
            stackedInner (S.networkOperator x)
              (S.weightedDualAverage P hP init samples trace N) := by
      simp [primalDualGap]
      ring
    have hGapEach : ∀ k,
        S.primalDualGap
            (S.generatedXHat P hP init samples trace (k + 1))
            (S.generatedY P hP init samples trace (k + 1)) x y =
          S.objective (S.generatedXHat P hP init samples trace (k + 1)) +
            stackedInner
              (S.networkOperator (S.generatedXHat P hP init samples trace (k + 1))) y -
            S.objective x -
            stackedInner (S.networkOperator x)
              (S.generatedY P hP init samples trace (k + 1)) := by
      intro k
      simp [primalDualGap]
      ring
    have hRight :
        W⁻¹ *
            (∑ k ∈ Finset.range N,
              P.theta (k + 1) *
                S.primalDualGap
                  (S.generatedXHat P hP init samples trace (k + 1))
                  (S.generatedY P hP init samples trace (k + 1)) x y) =
          W⁻¹ * (∑ k ∈ Finset.range N,
            P.theta (k + 1) *
              S.objective (S.generatedXHat P hP init samples trace (k + 1))) +
          W⁻¹ * (∑ k ∈ Finset.range N,
            P.theta (k + 1) * stackedInner
              (S.networkOperator (S.generatedXHat P hP init samples trace (k + 1))) y) -
          S.objective x -
          W⁻¹ * (∑ k ∈ Finset.range N,
            P.theta (k + 1) * stackedInner (S.networkOperator x)
              (S.generatedY P hP init samples trace (k + 1))) := by
      calc
        W⁻¹ *
            (∑ k ∈ Finset.range N,
              P.theta (k + 1) *
                S.primalDualGap
                  (S.generatedXHat P hP init samples trace (k + 1))
                  (S.generatedY P hP init samples trace (k + 1)) x y) =
          W⁻¹ *
            (∑ k ∈ Finset.range N,
              P.theta (k + 1) *
                (S.objective (S.generatedXHat P hP init samples trace (k + 1)) +
                  stackedInner
                    (S.networkOperator
                      (S.generatedXHat P hP init samples trace (k + 1))) y -
                  S.objective x -
                  stackedInner (S.networkOperator x)
                    (S.generatedY P hP init samples trace (k + 1)))) := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro k _hk
            rw [hGapEach k]
        _ =
          W⁻¹ * (∑ k ∈ Finset.range N,
            P.theta (k + 1) *
              S.objective (S.generatedXHat P hP init samples trace (k + 1))) +
          W⁻¹ * (∑ k ∈ Finset.range N,
            P.theta (k + 1) * stackedInner
              (S.networkOperator (S.generatedXHat P hP init samples trace (k + 1))) y) -
          S.objective x -
          W⁻¹ * (∑ k ∈ Finset.range N,
            P.theta (k + 1) * stackedInner (S.networkOperator x)
              (S.generatedY P hP init samples trace (k + 1))) := by
            let A : ℕ → ℝ := fun k =>
              S.objective (S.generatedXHat P hP init samples trace (k + 1))
            let B : ℕ → ℝ := fun k =>
              stackedInner
                (S.networkOperator (S.generatedXHat P hP init samples trace (k + 1))) y
            let C : ℕ → ℝ := fun k =>
              stackedInner (S.networkOperator x)
                (S.generatedY P hP init samples trace (k + 1))
            have hsum_expand :
                (∑ k ∈ Finset.range N,
                  P.theta (k + 1) * (A k + B k - S.objective x - C k)) =
                  (∑ k ∈ Finset.range N, P.theta (k + 1) * A k) +
                  (∑ k ∈ Finset.range N, P.theta (k + 1) * B k) -
                  (∑ k ∈ Finset.range N, P.theta (k + 1) * S.objective x) -
                  (∑ k ∈ Finset.range N, P.theta (k + 1) * C k) := by
              simp [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
            change
              W⁻¹ * (∑ k ∈ Finset.range N,
                P.theta (k + 1) * (A k + B k - S.objective x - C k)) =
                W⁻¹ * (∑ k ∈ Finset.range N, P.theta (k + 1) * A k) +
                W⁻¹ * (∑ k ∈ Finset.range N, P.theta (k + 1) * B k) -
                S.objective x -
                W⁻¹ * (∑ k ∈ Finset.range N, P.theta (k + 1) * C k)
            rw [hsum_expand]
            nlinarith [hConstObj]
    rw [hLeft, hRight, hPairX, hPairY]
    nlinarith [hObjJensen]
  have hScaled :
      W⁻¹ *
          (∑ k ∈ Finset.range N,
            P.theta (k + 1) *
              S.primalDualGap
                (S.generatedXHat P hP init samples trace (k + 1))
                (S.generatedY P hP init samples trace (k + 1)) x y) ≤
        W⁻¹ * S.generalSDCSGapLemma85RawTerminalRHS P hP init samples trace x y N := by
    exact mul_le_mul_of_nonneg_left (hWeightedQ x y hx) hW_nonneg
  exact le_trans hJensen (by simpa [W] using hScaled)

/-- Retained-primal version of the Lemma 8.5 prox-drop budget.

The terminal prox term is kept exactly, while `stackedProx_lower_bound` is used
only to absorb the lagged Young budgets.
-/
private theorem sdcs_terminal_prox_plus_lagged_primal_le_prox_drop_sum
    (P : Parameters) (hP : ValidParameters P) (init : InitialState S)
    (samples : ℕ → ι → ℕ → Ξ) (trace : S.GeneratedTrace P hP init samples)
    (N : ℕ) (hN : 1 ≤ N)
    (hDenom : ∀ k, 1 ≤ k → k ≤ N → 0 < P.innerSteps k ∧ 0 < P.eta k)
    (hTheta_nonneg : ∀ k, 1 ≤ k → k ≤ N → 0 ≤ P.theta k) :
    let dx : ℕ → Stacked ι E := fun t =>
      S.generatedXHat P hP init samples trace t -
        S.generatedX P hP init samples trace (t - 1)
    P.theta N * P.eta N *
        S.stackedProx
          (S.generatedX P hP init samples trace (N - 1))
          (S.generatedXHat P hP init samples trace N) +
      (∑ t ∈ Finset.Icc 2 N,
        (P.theta (t - 1) * P.eta (t - 1) / 2) *
          S.stackedNormSq (dx (t - 1))) ≤
      ∑ k ∈ Finset.range N,
        let kk := k + 1
        P.theta kk * P.eta kk *
          S.stackedProx
            (S.generatedX P hP init samples trace (kk - 1))
            (S.generatedXHat P hP init samples trace kk) := by
  classical
  let dx : ℕ → Stacked ι E := fun t =>
    S.generatedXHat P hP init samples trace t -
      S.generatedX P hP init samples trace (t - 1)
  let A : ℕ → ℝ := fun t =>
    (P.theta t * P.eta t / 2) * S.stackedNormSq (dx t)
  let B : ℕ → ℝ := fun t =>
    P.theta t * P.eta t *
      S.stackedProx
        (S.generatedX P hP init samples trace (t - 1))
        (S.generatedXHat P hP init samples trace t)
  have hLagged : ∀ t ∈ Finset.Icc 2 N, A (t - 1) ≤ B (t - 1) := by
    intro t ht
    have ht2 : 2 ≤ t := (Finset.mem_Icc.mp ht).1
    have htN : t ≤ N := (Finset.mem_Icc.mp ht).2
    have htPrev1 : 1 ≤ t - 1 := by omega
    have htPrevN : t - 1 ≤ N := by omega
    have htheta : 0 ≤ P.theta (t - 1) :=
      hTheta_nonneg (t - 1) htPrev1 htPrevN
    have heta : 0 ≤ P.eta (t - 1) :=
      ValidParameters.eta_nonneg hP (t - 1)
    have hweight : 0 ≤ P.theta (t - 1) * P.eta (t - 1) :=
      mul_nonneg htheta heta
    have hxprev :
        S.FeasiblePoint (S.generatedX P hP init samples trace ((t - 1) - 1)) := by
      simpa [generatedX, generatedState] using
        (S.generatedState P hP init samples trace ((t - 1) - 1)).xPrev_mem
    have hxhat :
        S.FeasiblePoint
          (S.generatedXHat P hP init samples trace (t - 1)) :=
      S.generatedXHat_mem P hP init samples trace (t - 1) htPrev1
        (hDenom (t - 1) htPrev1 htPrevN).1
    have hprox :=
      S.stackedProx_lower_bound
        (S.generatedX P hP init samples trace ((t - 1) - 1))
        (S.generatedXHat P hP init samples trace (t - 1))
        hxprev hxhat
    have hprox_dx :
        (1 / 2 : ℝ) * S.stackedNormSq (dx (t - 1)) ≤
          S.stackedProx
            (S.generatedX P hP init samples trace ((t - 1) - 1))
            (S.generatedXHat P hP init samples trace (t - 1)) := by
      simpa [dx, stackedNormSq_sub_comm S
        (S.generatedXHat P hP init samples trace (t - 1))
        (S.generatedX P hP init samples trace ((t - 1) - 1))] using hprox
    have hscaled := mul_le_mul_of_nonneg_left hprox_dx hweight
    dsimp [A, B]
    nlinarith
  have hsplit := terminal_add_lagged_le_range_sum_of_lagged_le A B N hN hLagged
  simpa [A, B, dx] using hsplit

/-- SDCS specialization of the dual-drop telescope used in Lemma 8.5 step 16. -/
private theorem sdcs_dual_drop_sum_le_endpoint_sub_tail_generated
    (P : Parameters) (hP : ValidParameters P) (init : InitialState S)
    (samples : ℕ → ι → ℕ → Ξ) (trace : S.GeneratedTrace P hP init samples)
    (N : ℕ) (hN : 1 ≤ N) (hGeneral : S.generalParameterConditions P N)
    (hTheta_nonneg : ∀ k, 1 ≤ k → k ≤ N → 0 ≤ P.theta k)
    (y : Stacked ι E) :
    (∑ k ∈ Finset.range N,
      let kk := k + 1
      P.theta kk * (P.tau kk / 2) *
        (S.stackedNormSq (y - S.generatedY P hP init samples trace (kk - 1)) -
          S.stackedNormSq (y - S.generatedY P hP init samples trace kk) -
            S.stackedNormSq
              (S.generatedY P hP init samples trace (kk - 1) -
                S.generatedY P hP init samples trace kk))) ≤
      (P.theta 1 * P.tau 1 / 2) *
        (S.stackedNormSq (y - init.y0) -
          S.stackedNormSq (y - S.generatedY P hP init samples trace N)) -
        ∑ t ∈ Finset.Icc 2 N,
          P.theta t * (P.tau t / 2) *
            S.stackedNormSq
              (S.generatedY P hP init samples trace (t - 1) -
                S.generatedY P hP init samples trace t) := by
  classical
  have h31 := hGeneral.2.2.1
  have hY0 :
      S.generatedY P hP init samples trace 0 = init.y0 := by
    simp [generatedY, generatedState, initialOuterState, trace.initial_state]
  have hc_nonneg : 0 ≤ P.theta 1 * P.tau 1 := by
    exact mul_nonneg (hTheta_nonneg 1 (by omega) hN)
      (ValidParameters.tau_nonneg hP 1)
  have hE_nonneg :
      ∀ t, 1 ≤ t → t ≤ N →
        0 ≤ S.stackedNormSq
          (S.generatedY P hP init samples trace (t - 1) -
            S.generatedY P hP init samples trace t) := by
    intro t _ht1 _htN
    exact S.stackedNormSq_nonneg _
  have hdual :=
    sdcs_dual_drop_sum_le_endpoint_sub_tail
      P.theta P.tau
      (fun k => S.stackedNormSq
        (y - S.generatedY P hP init samples trace k))
      (fun t => S.stackedNormSq
        (S.generatedY P hP init samples trace (t - 1) -
          S.generatedY P hP init samples trace t))
      N hN hc_nonneg h31 hE_nonneg
  simpa [hY0, stackedNormSq_sub_comm S] using hdual

/-- Lemma 8.5 source step 16 before applying saddle nonnegativity.

This is the retained post-(c) aggregate from the source proof.  Unlike
`general_sdcs_weighted_gap_sum_raw_terminal_le`, it has not passed through the
terminal Young/drop assembly, so the terminal primal prox and dual-square terms
remain on the left.
-/
private theorem general_sdcs_weighted_gap_sum_retained_terminal_le
    (P : Parameters) (hP : ValidParameters P) (init : InitialState S)
    (samples : ℕ → ι → ℕ → Ξ) (trace : S.GeneratedTrace P hP init samples)
    (N : ℕ) (hN : 1 ≤ N) (hGeneral : S.generalParameterConditions P N)
    (hDenom : ∀ k, 1 ≤ k → k ≤ N → 0 < P.innerSteps k ∧ 0 < P.eta k)
    (hTheta_nonneg : ∀ k, 1 ≤ k → k ≤ N → 0 ≤ P.theta k)
    (hRawInnerTerminal :
      ∀ (i : ι) (k : ℕ), 1 ≤ k → k ≤ N → ∀ u : E, u ∈ S.feasible i →
          let centerState := S.generatedState P hP init samples trace (k - 1)
          let T := P.innerSteps k
          let coeff := 2 / ((T : ℝ) * ((T : ℝ) + 3))
          coeff *
              (∑ t ∈ Finset.range T, csLambda (t + 1) *
                ((P.eta k * csBeta (t + 1)) *
                    S.localProx i (S.generatedInnerQuery P hP init samples trace i k t) u -
                  (P.eta k + P.eta k * csBeta (t + 1)) *
                    S.localProx i
                      (S.generatedInnerQuery P hP init samples trace i k (t + 1)) u)) ≤
            generalSDCSRawPrimalTelescopeInitialCoeff P k *
                S.localProx i (centerState.xPrev i) u -
              generalSDCSRawPrimalTerminalCoeff P k *
                S.localProx i (S.generatedX P hP init samples trace k i) u) :
    ∀ x y : Stacked ι E,
      S.FeasiblePoint x →
        (∑ k ∈ Finset.range N,
          P.theta (k + 1) *
            S.primalDualGap
              (S.generatedXHat P hP init samples trace (k + 1))
              (S.generatedY P hP init samples trace (k + 1)) x y) +
          P.theta N * P.eta N *
            S.stackedProx
              (S.generatedX P hP init samples trace (N - 1))
              (S.generatedXHat P hP init samples trace N) +
          (P.theta 1 * P.tau 1 / 2) *
            S.stackedNormSq
              (y - S.generatedY P hP init samples trace N) ≤
        P.theta N *
          stackedInner
            (S.networkOperator
              (S.generatedXHat P hP init samples trace N -
                S.generatedX P hP init samples trace (N - 1)))
            (y - S.generatedY P hP init samples trace N) +
          S.generalSDCSRawTerminalPotential P hP init samples trace x N +
          (P.theta 1 * P.tau 1 / 2) *
            S.stackedNormSq (y - init.y0) +
          S.generalSDCSRawOracleErrorBudget P hP init samples trace x N := by
  classical
  intro x y hx
  let dx : ℕ → Stacked ι E := fun t =>
    S.generatedXHat P hP init samples trace t -
      S.generatedX P hP init samples trace (t - 1)
  have hProxRetainedBudget :
      P.theta N * P.eta N *
          S.stackedProx
            (S.generatedX P hP init samples trace (N - 1))
            (S.generatedXHat P hP init samples trace N) +
        (∑ t ∈ Finset.Icc 2 N,
          (P.theta (t - 1) * P.eta (t - 1) / 2) *
            S.stackedNormSq (dx (t - 1))) ≤
        ∑ k ∈ Finset.range N,
          let kk := k + 1
          P.theta kk * P.eta kk *
            S.stackedProx
              (S.generatedX P hP init samples trace (kk - 1))
              (S.generatedXHat P hP init samples trace kk) := by
    simpa [dx] using
      sdcs_terminal_prox_plus_lagged_primal_le_prox_drop_sum S
        P hP init samples trace N hN hDenom hTheta_nonneg
  have hDualDropUpper :
      (∑ k ∈ Finset.range N,
        let kk := k + 1
        P.theta kk * (P.tau kk / 2) *
          (S.stackedNormSq (y - S.generatedY P hP init samples trace (kk - 1)) -
            S.stackedNormSq (y - S.generatedY P hP init samples trace kk) -
              S.stackedNormSq
                (S.generatedY P hP init samples trace (kk - 1) -
                  S.generatedY P hP init samples trace kk))) ≤
        (P.theta 1 * P.tau 1 / 2) *
          (S.stackedNormSq (y - init.y0) -
            S.stackedNormSq (y - S.generatedY P hP init samples trace N)) -
          ∑ t ∈ Finset.Icc 2 N,
            P.theta t * (P.tau t / 2) *
              S.stackedNormSq
                (S.generatedY P hP init samples trace (t - 1) -
                  S.generatedY P hP init samples trace t) := by
    exact
      sdcs_dual_drop_sum_le_endpoint_sub_tail_generated S
        P hP init samples trace N hN hGeneral hTheta_nonneg y
  let gap : ℕ → ℝ := fun k =>
    S.primalDualGap
      (S.generatedXHat P hP init samples trace (k + 1))
      (S.generatedY P hP init samples trace (k + 1)) x y
  let deltaRaw : ℕ → ℝ := fun kk =>
    let stPrev := S.generatedState P hP init samples trace (kk - 1)
    let xTilde := S.outerExtrapolation P kk stPrev
    stackedInner
        (S.networkOperator (S.generatedXHat P hP init samples trace kk - xTilde))
        (y - S.generatedY P hP init samples trace kk) +
      generalSDCSRawPrimalInitialCoeff P kk *
          S.stackedProx (S.generatedX P hP init samples trace (kk - 1)) x -
        generalSDCSRawPrimalTerminalCoeff P kk *
          S.stackedProx (S.generatedX P hP init samples trace kk) x -
      P.eta kk *
          S.stackedProx (S.generatedX P hP init samples trace (kk - 1))
            (S.generatedXHat P hP init samples trace kk) +
      (P.tau kk / 2) *
        (S.stackedNormSq (y - S.generatedY P hP init samples trace (kk - 1)) -
          S.stackedNormSq (y - S.generatedY P hP init samples trace kk) -
            S.stackedNormSq
              (S.generatedY P hP init samples trace (kk - 1) -
                S.generatedY P hP init samples trace kk))
  let weightedOracle : ℕ → ℝ := fun k =>
    let kk := k + 1
    let T := P.innerSteps kk
    ∑ t ∈ Finset.range T,
      ∑ i,
        let uPrev := S.generatedInnerQuery P hP init samples trace i kk t
        let δ := S.oracleError i uPrev (samples kk i t)
        (2 * P.theta kk / ((T : ℝ) * ((T : ℝ) + 3))) *
          (-(csLambda (t + 1) * inner ℝ δ (x i - uPrev)) +
            csLambda (t + 1) *
              ((S.M + ‖δ‖) ^ 2 / (2 * (P.eta kk * csBeta (t + 1)))))
  have htheta_range : ∀ k ∈ Finset.range N, 0 ≤ P.theta (k + 1) := by
    intro k hk
    exact hTheta_nonneg (k + 1) (Nat.succ_pos k)
      (Nat.succ_le_of_lt (Finset.mem_range.mp hk))
  have hOneStep :
      ∀ k ∈ Finset.range N,
        gap k ≤ deltaRaw (k + 1) +
          (let kk := k + 1
           let T := P.innerSteps kk
           ∑ t ∈ Finset.range T,
             ∑ i,
               let uPrev := S.generatedInnerQuery P hP init samples trace i kk t
               let δ := S.oracleError i uPrev (samples kk i t)
               (2 / ((T : ℝ) * ((T : ℝ) + 3))) *
                 (-(csLambda (t + 1) * inner ℝ δ (x i - uPrev)) +
                   csLambda (t + 1) *
                     ((S.M + ‖δ‖) ^ 2 / (2 * (P.eta kk * csBeta (t + 1)))))) := by
    -- Source Lemma 8.5 steps 1-5: compose
    -- `generated_outer_phi_jensen_coeff_inequality`,
    -- `generated_inner_phi_weighted_sum_bound_coeff`, `hRawInnerTerminal`, and
    -- `generated_sdcs_dual_one_step_inequality`.
    intro k hk
    have hkk_pos : 1 ≤ k + 1 := Nat.succ_pos k
    have hkk_le : k + 1 ≤ N :=
      Nat.succ_le_of_lt (Finset.mem_range.mp hk)
    have hT : 0 < P.innerSteps (k + 1) :=
      (hDenom (k + 1) hkk_pos hkk_le).1
    have heta : 0 < P.eta (k + 1) :=
      (hDenom (k + 1) hkk_pos hkk_le).2
    have hOuter :=
      S.generated_outer_phi_jensen_coeff_inequality P hP init samples trace
        (k + 1) hkk_pos hT
    have hInner :
        ∀ i,
          let centerState := S.generatedState P hP init samples trace ((k + 1) - 1)
          let nextState := S.generatedState P hP init samples trace (k + 1)
          let T := P.innerSteps (k + 1)
          let coeff := 2 / ((T : ℝ) * ((T : ℝ) + 3))
          let w := (S.dualNeighborDisagreement nextState.yPrev) i
          let xCenter := centerState.xPrev i
          coeff *
              (∑ t ∈ Finset.range T, csLambda (t + 1) *
                (let uNext :=
                  S.generatedInnerQuery P hP init samples trace i (k + 1) (t + 1)
                 inner ℝ w uNext + S.localObjective i uNext +
                   P.eta (k + 1) * S.localProx i xCenter uNext)) ≤
            coeff *
              (∑ t ∈ Finset.range T, csLambda (t + 1) *
                (let uPrev := S.generatedInnerQuery P hP init samples trace i (k + 1) t
                 let uNext :=
                  S.generatedInnerQuery P hP init samples trace i (k + 1) (t + 1)
                 let δ := S.subgradient i uPrev - S.oracle i uPrev (samples (k + 1) i t)
                 inner ℝ w (x i) + S.localObjective i (x i) +
                   P.eta (k + 1) * S.localProx i xCenter (x i) -
                   inner ℝ δ (x i - uPrev) +
                   (P.eta (k + 1) * csBeta (t + 1)) * S.localProx i uPrev (x i) -
                   (P.eta (k + 1) + P.eta (k + 1) * csBeta (t + 1)) *
                     S.localProx i uNext (x i) +
                   (S.M + ‖δ‖) ^ 2 /
                     (2 * (P.eta (k + 1) * csBeta (t + 1))))) := by
      intro i
      simpa using
        S.generated_inner_phi_weighted_sum_bound_coeff P hP init samples trace
          i (k + 1) (x i) (hx i) hT heta
    have hRaw :
        ∀ i,
          let centerState := S.generatedState P hP init samples trace ((k + 1) - 1)
          let T := P.innerSteps (k + 1)
          let coeff := 2 / ((T : ℝ) * ((T : ℝ) + 3))
          coeff *
              (∑ t ∈ Finset.range T, csLambda (t + 1) *
                ((P.eta (k + 1) * csBeta (t + 1)) *
                    S.localProx i
                      (S.generatedInnerQuery P hP init samples trace i (k + 1) t)
                      (x i) -
                  (P.eta (k + 1) + P.eta (k + 1) * csBeta (t + 1)) *
                    S.localProx i
                      (S.generatedInnerQuery P hP init samples trace i (k + 1) (t + 1))
                      (x i))) ≤
            generalSDCSRawPrimalTelescopeInitialCoeff P (k + 1) *
                S.localProx i (centerState.xPrev i) (x i) -
              generalSDCSRawPrimalTerminalCoeff P (k + 1) *
                S.localProx i (S.generatedX P hP init samples trace (k + 1) i) (x i) := by
      intro i
      simpa using hRawInnerTerminal i (k + 1) hkk_pos hkk_le (x i) (hx i)
    have hDual :=
      S.generated_sdcs_dual_one_step_inequality P hP init samples trace
        (k + 1) hkk_pos y
    let kk := k + 1
    let centerState := S.generatedState P hP init samples trace (kk - 1)
    let nextState := S.generatedState P hP init samples trace kk
    let T := P.innerSteps kk
    let coeff := 2 / ((T : ℝ) * ((T : ℝ) + 3))
    have hInnerSum :
        (∑ i,
          coeff *
            (∑ t ∈ Finset.range T, csLambda (t + 1) *
              (let uNext := S.generatedInnerQuery P hP init samples trace i kk (t + 1)
               inner ℝ ((S.dualNeighborDisagreement nextState.yPrev) i) uNext +
                 S.localObjective i uNext +
                   P.eta kk * S.localProx i (centerState.xPrev i) uNext))) ≤
          ∑ i,
            coeff *
              (∑ t ∈ Finset.range T, csLambda (t + 1) *
                (let uPrev := S.generatedInnerQuery P hP init samples trace i kk t
                 let uNext := S.generatedInnerQuery P hP init samples trace i kk (t + 1)
                 let δ := S.subgradient i uPrev - S.oracle i uPrev (samples kk i t)
                 inner ℝ ((S.dualNeighborDisagreement nextState.yPrev) i) (x i) +
                   S.localObjective i (x i) +
                   P.eta kk * S.localProx i (centerState.xPrev i) (x i) -
                   inner ℝ δ (x i - uPrev) +
                   (P.eta kk * csBeta (t + 1)) * S.localProx i uPrev (x i) -
                   (P.eta kk + P.eta kk * csBeta (t + 1)) *
                     S.localProx i uNext (x i) +
                   (S.M + ‖δ‖) ^ 2 /
                     (2 * (P.eta kk * csBeta (t + 1))))) := by
      exact Finset.sum_le_sum (fun i _hi => by
        simpa [kk, centerState, nextState, T, coeff] using hInner i)
    have hOuterInner :
        (∑ i,
          (inner ℝ ((S.dualNeighborDisagreement nextState.yPrev) i)
              (S.generatedXHat P hP init samples trace kk i) +
            (S.localObjective i (S.generatedXHat P hP init samples trace kk i) +
              P.eta kk * S.localProx i (centerState.xPrev i)
                (S.generatedXHat P hP init samples trace kk i)))) ≤
          ∑ i,
            coeff *
              (∑ t ∈ Finset.range T, csLambda (t + 1) *
                (let uPrev := S.generatedInnerQuery P hP init samples trace i kk t
                 let uNext := S.generatedInnerQuery P hP init samples trace i kk (t + 1)
                 let δ := S.subgradient i uPrev - S.oracle i uPrev (samples kk i t)
                 inner ℝ ((S.dualNeighborDisagreement nextState.yPrev) i) (x i) +
                   S.localObjective i (x i) +
                   P.eta kk * S.localProx i (centerState.xPrev i) (x i) -
                   inner ℝ δ (x i - uPrev) +
                   (P.eta kk * csBeta (t + 1)) * S.localProx i uPrev (x i) -
                   (P.eta kk + P.eta kk * csBeta (t + 1)) *
                     S.localProx i uNext (x i) +
                   (S.M + ‖δ‖) ^ 2 /
                     (2 * (P.eta kk * csBeta (t + 1))))) :=
      le_trans (by simpa [kk, centerState, nextState, T, coeff, add_assoc] using hOuter)
        hInnerSum
    have hRawSum :
        (∑ i,
          coeff *
            (∑ t ∈ Finset.range T, csLambda (t + 1) *
              ((P.eta kk * csBeta (t + 1)) *
                  S.localProx i
                    (S.generatedInnerQuery P hP init samples trace i kk t)
                    (x i) -
                (P.eta kk + P.eta kk * csBeta (t + 1)) *
                  S.localProx i
                    (S.generatedInnerQuery P hP init samples trace i kk (t + 1))
                    (x i)))) ≤
          ∑ i,
            (generalSDCSRawPrimalTelescopeInitialCoeff P kk *
                S.localProx i (centerState.xPrev i) (x i) -
              generalSDCSRawPrimalTerminalCoeff P kk *
                S.localProx i (S.generatedX P hP init samples trace kk i) (x i)) := by
      exact Finset.sum_le_sum (fun i _hi => by
        simpa [kk, centerState, T, coeff] using hRaw i)
    let C : ι → ℝ := fun i =>
      inner ℝ ((S.dualNeighborDisagreement nextState.yPrev) i) (x i) +
        S.localObjective i (x i) +
          P.eta kk * S.localProx i (centerState.xPrev i) (x i)
    let B : ι → ℕ → ℝ := fun i t =>
      (P.eta kk * csBeta (t + 1)) *
          S.localProx i
            (S.generatedInnerQuery P hP init samples trace i kk t)
            (x i) -
        (P.eta kk + P.eta kk * csBeta (t + 1)) *
          S.localProx i
            (S.generatedInnerQuery P hP init samples trace i kk (t + 1))
            (x i)
    let O : ι → ℕ → ℝ := fun i t =>
      let uPrev := S.generatedInnerQuery P hP init samples trace i kk t;
      let δ := S.subgradient i uPrev - S.oracle i uPrev (samples kk i t);
      -inner ℝ δ (x i - uPrev) +
        (S.M + ‖δ‖) ^ 2 / (2 * (P.eta kk * csBeta (t + 1)))
    have hInnerRhs_decomp :
        (∑ i,
          coeff *
            (∑ t ∈ Finset.range T, csLambda (t + 1) *
              (C i + B i t + O i t))) =
          (∑ i, C i) +
            (∑ i, coeff * (∑ t ∈ Finset.range T, csLambda (t + 1) * B i t)) +
              (∑ i, coeff * (∑ t ∈ Finset.range T, csLambda (t + 1) * O i t)) := by
      exact cs_coeff_agent_weighted_three_term_decomp (ι := ι) (T := T) hT C B O
    let innerExpanded : ℝ :=
      ∑ i,
        coeff *
          (∑ t ∈ Finset.range T, csLambda (t + 1) *
            (let uPrev := S.generatedInnerQuery P hP init samples trace i kk t
             let uNext := S.generatedInnerQuery P hP init samples trace i kk (t + 1)
             let δ := S.subgradient i uPrev - S.oracle i uPrev (samples kk i t)
             inner ℝ ((S.dualNeighborDisagreement nextState.yPrev) i) (x i) +
               S.localObjective i (x i) +
                 P.eta kk * S.localProx i (centerState.xPrev i) (x i) -
                 inner ℝ δ (x i - uPrev) +
                 (P.eta kk * csBeta (t + 1)) * S.localProx i uPrev (x i) -
                 (P.eta kk + P.eta kk * csBeta (t + 1)) *
                   S.localProx i uNext (x i) +
                 (S.M + ‖δ‖) ^ 2 /
                   (2 * (P.eta kk * csBeta (t + 1)))))
    let innerCBO : ℝ :=
      ∑ i,
        coeff *
          (∑ t ∈ Finset.range T, csLambda (t + 1) *
            (C i + B i t + O i t))
    have hInnerRhs_as_CBO : innerExpanded = innerCBO := by
      dsimp [innerExpanded, innerCBO]
      refine Finset.sum_congr rfl ?_
      intro i _hi
      apply congrArg (fun z => coeff * z)
      refine Finset.sum_congr rfl ?_
      intro t _ht
      apply congrArg (fun z => csLambda (t + 1) * z)
      dsimp [C, B, O]
      ring
    have hOuterCBO :
        (∑ i,
          (inner ℝ ((S.dualNeighborDisagreement nextState.yPrev) i)
              (S.generatedXHat P hP init samples trace kk i) +
            (S.localObjective i (S.generatedXHat P hP init samples trace kk i) +
              P.eta kk * S.localProx i (centerState.xPrev i)
                (S.generatedXHat P hP init samples trace kk i)))) ≤
          ∑ i,
            coeff *
              (∑ t ∈ Finset.range T, csLambda (t + 1) *
                (C i + B i t + O i t)) := by
      exact le_trans hOuterInner (by
        simpa [innerExpanded, innerCBO] using le_of_eq hInnerRhs_as_CBO)
    let Csum : ℝ := ∑ i, C i
    let Bsum : ℝ :=
      ∑ i, coeff * (∑ t ∈ Finset.range T, csLambda (t + 1) * B i t)
    let Osum : ℝ :=
      ∑ i, coeff * (∑ t ∈ Finset.range T, csLambda (t + 1) * O i t)
    let rawBoundary : ℝ :=
      ∑ i,
        (generalSDCSRawPrimalTelescopeInitialCoeff P kk *
            S.localProx i (centerState.xPrev i) (x i) -
          generalSDCSRawPrimalTerminalCoeff P kk *
            S.localProx i (S.generatedX P hP init samples trace kk i) (x i))
    have hOuterSplit :
        (∑ i,
          (inner ℝ ((S.dualNeighborDisagreement nextState.yPrev) i)
              (S.generatedXHat P hP init samples trace kk i) +
            (S.localObjective i (S.generatedXHat P hP init samples trace kk i) +
              P.eta kk * S.localProx i (centerState.xPrev i)
                (S.generatedXHat P hP init samples trace kk i)))) ≤
          Csum + Bsum + Osum := by
      exact le_trans hOuterCBO (le_of_eq (by simpa [Csum, Bsum, Osum] using hInnerRhs_decomp))
    have hRawSum' : Bsum ≤ rawBoundary := by
      simpa [Bsum, rawBoundary, B] using hRawSum
    have hOuterRaw :
        (∑ i,
          (inner ℝ ((S.dualNeighborDisagreement nextState.yPrev) i)
              (S.generatedXHat P hP init samples trace kk i) +
            (S.localObjective i (S.generatedXHat P hP init samples trace kk i) +
              P.eta kk * S.localProx i (centerState.xPrev i)
                (S.generatedXHat P hP init samples trace kk i)))) ≤
          Csum + rawBoundary + Osum := by
      exact le_trans hOuterSplit (by
        have h := add_le_add_right (add_le_add_left hRawSum' Csum) Osum
        simpa [add_assoc] using h)
    have hOsum_oracle :
        Osum =
          ∑ t ∈ Finset.range T,
            ∑ i,
              let uPrev := S.generatedInnerQuery P hP init samples trace i kk t
              let δ := S.oracleError i uPrev (samples kk i t)
              coeff *
                (-(csLambda (t + 1) * inner ℝ δ (x i - uPrev)) +
                  csLambda (t + 1) *
                    ((S.M + ‖δ‖) ^ 2 / (2 * (P.eta kk * csBeta (t + 1))))) := by
      calc
        Osum =
            ∑ i, coeff * (∑ t ∈ Finset.range T, csLambda (t + 1) * O i t) := by
              rfl
        _ =
            coeff * (∑ t ∈ Finset.range T, csLambda (t + 1) * (∑ i, O i t)) := by
              exact (coeff_mul_weighted_time_agent_sum_comm (ι := ι) T coeff O).symm
        _ =
            ∑ t ∈ Finset.range T, ∑ i, coeff * (csLambda (t + 1) * O i t) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro t _ht
              calc
                coeff * (csLambda (t + 1) * ∑ i, O i t) =
                    coeff * (∑ i, csLambda (t + 1) * O i t) := by
                      rw [Finset.mul_sum]
                _ = ∑ i, coeff * (csLambda (t + 1) * O i t) := by
                      simpa using
                        (Finset.mul_sum (s := (Finset.univ : Finset ι))
                          (f := fun i => csLambda (t + 1) * O i t) coeff)
        _ =
          ∑ t ∈ Finset.range T,
            ∑ i,
              let uPrev := S.generatedInnerQuery P hP init samples trace i kk t
              let δ := S.oracleError i uPrev (samples kk i t)
              coeff *
                (-(csLambda (t + 1) * inner ℝ δ (x i - uPrev)) +
                  csLambda (t + 1) *
                    ((S.M + ‖δ‖) ^ 2 / (2 * (P.eta kk * csBeta (t + 1))))) := by
              refine Finset.sum_congr rfl ?_
              intro t _ht
              refine Finset.sum_congr rfl ?_
              intro i _hi
              dsimp [O, oracleError]
              ring
    have hStackedInner_comm :
        ∀ a b : Stacked ι E, stackedInner a b = stackedInner b a := by
      intro a b
      simp [stackedInner, real_inner_comm]
    have hNetworkPair_symm :
        ∀ a b : Stacked ι E,
          stackedInner (S.networkOperator a) b =
            stackedInner (S.networkOperator b) a := by
      intro a b
      calc
        stackedInner (S.networkOperator a) b =
            stackedInner a (S.networkOperator b) :=
              S.networkIsConnectedLaplacian.2.2 a b
        _ = stackedInner (S.networkOperator b) a := by
              rw [hStackedInner_comm]
    let xHat : Stacked ι E := S.generatedXHat P hP init samples trace kk
    let yNext : Stacked ι E := S.generatedY P hP init samples trace kk
    let xPrev : Stacked ι E := S.generatedX P hP init samples trace (kk - 1)
    let xNext : Stacked ι E := S.generatedX P hP init samples trace kk
    have hPairHat :
        (∑ i,
          inner ℝ ((S.dualNeighborDisagreement nextState.yPrev) i) (xHat i)) =
          stackedInner (S.networkOperator xHat) yNext := by
      calc
        (∑ i,
          inner ℝ ((S.dualNeighborDisagreement nextState.yPrev) i) (xHat i)) =
            stackedInner (S.networkOperator yNext) xHat := by
              simp [stackedInner, dualNeighborDisagreement, yNext, generatedY, nextState]
        _ = stackedInner (S.networkOperator xHat) yNext := hNetworkPair_symm yNext xHat
    have hPairX :
        (∑ i,
          inner ℝ ((S.dualNeighborDisagreement nextState.yPrev) i) (x i)) =
          stackedInner (S.networkOperator x) yNext := by
      calc
        (∑ i,
          inner ℝ ((S.dualNeighborDisagreement nextState.yPrev) i) (x i)) =
            stackedInner (S.networkOperator yNext) x := by
              simp [stackedInner, dualNeighborDisagreement, yNext, generatedY, nextState]
        _ = stackedInner (S.networkOperator x) yNext := hNetworkPair_symm yNext x
    let xTilde : Stacked ι E := S.outerExtrapolation P kk centerState
    have hOuterRaw_primal :
        S.objective xHat + stackedInner (S.networkOperator xHat) yNext +
            P.eta kk * S.stackedProx xPrev xHat ≤
          S.objective x + stackedInner (S.networkOperator x) yNext +
            generalSDCSRawPrimalInitialCoeff P kk * S.stackedProx xPrev x -
              generalSDCSRawPrimalTerminalCoeff P kk * S.stackedProx xNext x + Osum := by
      have hLhs :
          (∑ i,
            (inner ℝ ((S.dualNeighborDisagreement nextState.yPrev) i)
                (S.generatedXHat P hP init samples trace kk i) +
              (S.localObjective i (S.generatedXHat P hP init samples trace kk i) +
                P.eta kk * S.localProx i (centerState.xPrev i)
                  (S.generatedXHat P hP init samples trace kk i)))) =
            stackedInner (S.networkOperator xHat) yNext +
              (S.objective xHat + P.eta kk * S.stackedProx xPrev xHat) := by
        calc
          (∑ i,
            (inner ℝ ((S.dualNeighborDisagreement nextState.yPrev) i)
                (S.generatedXHat P hP init samples trace kk i) +
              (S.localObjective i (S.generatedXHat P hP init samples trace kk i) +
                P.eta kk * S.localProx i (centerState.xPrev i)
                  (S.generatedXHat P hP init samples trace kk i)))) =
              (∑ i, inner ℝ ((S.dualNeighborDisagreement nextState.yPrev) i) (xHat i)) +
                (∑ i, S.localObjective i (xHat i)) +
                  P.eta kk * (∑ i, S.localProx i (xPrev i) (xHat i)) := by
              dsimp [xHat, xPrev, centerState, generatedX, generatedXHat]
              simp [Finset.sum_add_distrib, Finset.mul_sum]
              ring
          _ = stackedInner (S.networkOperator xHat) yNext +
                (S.objective xHat + P.eta kk * S.stackedProx xPrev xHat) := by
              rw [hPairHat]
              dsimp [objective, stackedProx]
              ring
      have hRhs :
          Csum + rawBoundary + Osum =
            stackedInner (S.networkOperator x) yNext +
              (S.objective x + P.eta kk * S.stackedProx xPrev x) +
                (generalSDCSRawPrimalTelescopeInitialCoeff P kk * S.stackedProx xPrev x -
                  generalSDCSRawPrimalTerminalCoeff P kk * S.stackedProx xNext x) + Osum := by
        calc
          Csum + rawBoundary + Osum =
              (∑ i, inner ℝ ((S.dualNeighborDisagreement nextState.yPrev) i) (x i)) +
                (∑ i, S.localObjective i (x i)) +
                  P.eta kk * (∑ i, S.localProx i (xPrev i) (x i)) +
                (generalSDCSRawPrimalTelescopeInitialCoeff P kk *
                    (∑ i, S.localProx i (xPrev i) (x i)) -
                  generalSDCSRawPrimalTerminalCoeff P kk *
                    (∑ i, S.localProx i (xNext i) (x i))) + Osum := by
              dsimp [Csum, rawBoundary, C, xPrev, xNext, centerState, generatedX]
              simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
          _ = stackedInner (S.networkOperator x) yNext +
                (S.objective x + P.eta kk * S.stackedProx xPrev x) +
                  (generalSDCSRawPrimalTelescopeInitialCoeff P kk * S.stackedProx xPrev x -
                    generalSDCSRawPrimalTerminalCoeff P kk * S.stackedProx xNext x) + Osum := by
              rw [hPairX]
              dsimp [objective, stackedProx]
              ring
      have h := hOuterRaw
      rw [hLhs, hRhs] at h
      rw [generalSDCSRawPrimalInitialCoeff_mul_eq_phi_plus_telescope]
      linarith
    have hDualNet :
        stackedInner (S.networkOperator xTilde) (y - yNext) ≤
          P.tau kk / 2 *
            (S.stackedNormSq (y - S.generatedY P hP init samples trace (kk - 1)) -
              S.stackedNormSq (y - yNext) -
                S.stackedNormSq (S.generatedY P hP init samples trace (kk - 1) - yNext)) := by
      simpa [xTilde, kk, centerState, yNext, primalNeighborDisagreement] using hDual
    have hNetworkGapSplit :
        stackedInner (S.networkOperator xHat) y =
          stackedInner (S.networkOperator xHat) yNext +
            stackedInner (S.networkOperator (xHat - xTilde)) (y - yNext) +
              stackedInner (S.networkOperator xTilde) (y - yNext) := by
      dsimp [stackedInner, SOptLib.dependentProductInner]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro i _hi
      simp [ContinuousLinearMap.map_sub, Pi.sub_apply, inner_sub_left, inner_sub_right]
      ring
    have hGapSplit :
        gap k =
          (S.objective xHat + stackedInner (S.networkOperator xHat) yNext -
            (S.objective x + stackedInner (S.networkOperator x) yNext)) +
            stackedInner (S.networkOperator (xHat - xTilde)) (y - yNext) +
              stackedInner (S.networkOperator xTilde) (y - yNext) := by
      calc
        gap k =
            S.objective xHat + stackedInner (S.networkOperator xHat) y -
              (S.objective x + stackedInner (S.networkOperator x) yNext) := by
              dsimp [gap, primalDualGap, xHat, yNext, kk]
        _ =
          (S.objective xHat + stackedInner (S.networkOperator xHat) yNext -
            (S.objective x + stackedInner (S.networkOperator x) yNext)) +
            stackedInner (S.networkOperator (xHat - xTilde)) (y - yNext) +
              stackedInner (S.networkOperator xTilde) (y - yNext) := by
              rw [hNetworkGapSplit]
              ring
    have hDeltaO :
        gap k ≤ deltaRaw (k + 1) + Osum := by
      have hPrimalBracket :
          S.objective xHat + stackedInner (S.networkOperator xHat) yNext -
              (S.objective x + stackedInner (S.networkOperator x) yNext) ≤
            generalSDCSRawPrimalInitialCoeff P kk * S.stackedProx xPrev x -
              generalSDCSRawPrimalTerminalCoeff P kk * S.stackedProx xNext x -
                P.eta kk * S.stackedProx xPrev xHat + Osum := by
        linarith [hOuterRaw_primal]
      have hDeltaUnfold :
          deltaRaw (k + 1) =
            stackedInner (S.networkOperator (xHat - xTilde)) (y - yNext) +
              generalSDCSRawPrimalInitialCoeff P kk * S.stackedProx xPrev x -
                generalSDCSRawPrimalTerminalCoeff P kk * S.stackedProx xNext x -
              P.eta kk * S.stackedProx xPrev xHat +
              P.tau kk / 2 *
                (S.stackedNormSq (y - S.generatedY P hP init samples trace (kk - 1)) -
                  S.stackedNormSq (y - yNext) -
                    S.stackedNormSq
                      (S.generatedY P hP init samples trace (kk - 1) - yNext)) := by
        dsimp [deltaRaw, xHat, xTilde, xPrev, xNext, yNext, centerState, kk,
          generatedX, generatedXHat, generatedY]
      rw [hGapSplit, hDeltaUnfold]
      linarith [hPrimalBracket, hDualNet]
    calc
      gap k ≤ deltaRaw (k + 1) + Osum := hDeltaO
      _ = deltaRaw (k + 1) +
          (let kk := k + 1
           let T := P.innerSteps kk
           ∑ t ∈ Finset.range T,
             ∑ i,
               let uPrev := S.generatedInnerQuery P hP init samples trace i kk t
               let δ := S.oracleError i uPrev (samples kk i t)
               (2 / ((T : ℝ) * ((T : ℝ) + 3))) *
                 (-(csLambda (t + 1) * inner ℝ δ (x i - uPrev)) +
                   csLambda (t + 1) *
                     ((S.M + ‖δ‖) ^ 2 / (2 * (P.eta kk * csBeta (t + 1)))))) := by
            rw [hOsum_oracle]
  have hWeightedStep :
      ∀ k ∈ Finset.range N,
        P.theta (k + 1) * gap k ≤
          P.theta (k + 1) * deltaRaw (k + 1) + weightedOracle k := by
    intro k hk
    have hθ := htheta_range k hk
    let oracleBase : ℝ :=
      let kk := k + 1
      let T := P.innerSteps kk
      ∑ t ∈ Finset.range T,
        ∑ i,
          let uPrev := S.generatedInnerQuery P hP init samples trace i kk t
          let δ := S.oracleError i uPrev (samples kk i t)
          (2 / ((T : ℝ) * ((T : ℝ) + 3))) *
            (-(csLambda (t + 1) * inner ℝ δ (x i - uPrev)) +
              csLambda (t + 1) *
                ((S.M + ‖δ‖) ^ 2 / (2 * (P.eta kk * csBeta (t + 1)))))
    have hstep : gap k ≤ deltaRaw (k + 1) + oracleBase := by
      simpa [oracleBase] using hOneStep k hk
    have hmul :=
      mul_le_mul_of_nonneg_left hstep hθ
    have hscale :
        P.theta (k + 1) * (deltaRaw (k + 1) + oracleBase) =
          P.theta (k + 1) * deltaRaw (k + 1) + weightedOracle k := by
      rw [mul_add]
      congr 1
      dsimp [weightedOracle, oracleBase]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro t ht
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i hi
      ring
    exact le_trans hmul (le_of_eq hscale)
  have hRetainedDelta :
      (∑ k ∈ Finset.range N, P.theta (k + 1) * deltaRaw (k + 1)) +
          (P.theta N * P.eta N *
            S.stackedProx
              (S.generatedX P hP init samples trace (N - 1))
              (S.generatedXHat P hP init samples trace N) +
            (P.theta 1 * P.tau 1 / 2) *
              S.stackedNormSq
                (y - S.generatedY P hP init samples trace N)) ≤
        P.theta N *
            stackedInner
              (S.networkOperator
                (S.generatedXHat P hP init samples trace N -
                  S.generatedX P hP init samples trace (N - 1)))
              (y - S.generatedY P hP init samples trace N) +
          S.generalSDCSRawTerminalPotential P hP init samples trace x N +
            (P.theta 1 * P.tau 1 / 2) *
              S.stackedNormSq (y - init.y0) := by
    -- Source Lemma 8.5 step 16: mismatch telescope plus retained prox and
    -- generated dual-drop assembly, before terminal Young projection.
    let mismatchSum : ℝ :=
      ∑ k ∈ Finset.range N,
        let kk := k + 1
        let stPrev := S.generatedState P hP init samples trace (kk - 1)
        let xTilde := S.outerExtrapolation P kk stPrev
        P.theta kk *
          stackedInner
            (S.networkOperator (S.generatedXHat P hP init samples trace kk - xTilde))
            (y - S.generatedY P hP init samples trace kk)
    let proxDropSum : ℝ :=
      ∑ k ∈ Finset.range N,
        let kk := k + 1
        P.theta kk * P.eta kk *
          S.stackedProx (S.generatedX P hP init samples trace (kk - 1))
            (S.generatedXHat P hP init samples trace kk)
    let dualDropSum : ℝ :=
      ∑ k ∈ Finset.range N,
        let kk := k + 1
        P.theta kk * (P.tau kk / 2) *
          (S.stackedNormSq (y - S.generatedY P hP init samples trace (kk - 1)) -
            S.stackedNormSq (y - S.generatedY P hP init samples trace kk) -
              S.stackedNormSq
                (S.generatedY P hP init samples trace (kk - 1) -
                  S.generatedY P hP init samples trace kk))
    let terminalProx : ℝ :=
      P.theta N * P.eta N *
        S.stackedProx
          (S.generatedX P hP init samples trace (N - 1))
          (S.generatedXHat P hP init samples trace N)
    let terminalDual : ℝ :=
      (P.theta 1 * P.tau 1 / 2) *
        S.stackedNormSq (y - S.generatedY P hP init samples trace N)
    let terminalPair : ℝ :=
      P.theta N *
        stackedInner
          (S.networkOperator
            (S.generatedXHat P hP init samples trace N -
              S.generatedX P hP init samples trace (N - 1)))
          (y - S.generatedY P hP init samples trace N)
    let initDual : ℝ :=
      (P.theta 1 * P.tau 1 / 2) * S.stackedNormSq (y - init.y0)
    have hDeltaExpand :
        (∑ k ∈ Finset.range N, P.theta (k + 1) * deltaRaw (k + 1)) =
          S.generalSDCSRawTerminalPotential P hP init samples trace x N +
            mismatchSum - proxDropSum + dualDropSum := by
      dsimp [mismatchSum, proxDropSum, dualDropSum, deltaRaw,
        generalSDCSRawTerminalPotential]
      simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_add, mul_sub,
        add_assoc]
      have hCoeffSum :
          (∑ k ∈ Finset.range N,
              P.theta (k + 1) *
                (generalSDCSRawPrimalInitialCoeff P (k + 1) *
                  S.stackedProx (S.generatedX P hP init samples trace k) x)) =
            ∑ k ∈ Finset.range N,
              P.theta (k + 1) *
                (generalSDCSRawPrimalTerminalCoeff P (k + 1) *
                  S.stackedProx (S.generatedX P hP init samples trace k) x) := by
        refine Finset.sum_congr rfl ?_
        intro k hk
        have hk_lt : k < N := Finset.mem_range.mp hk
        have hTpos : 0 < P.innerSteps (k + 1) := by
          exact (hDenom (k + 1) (by omega) (by omega)).1
        rw [generalSDCSRawPrimalInitialCoeff_eq_terminalCoeff_of_innerSteps_pos P hTpos]
      rw [hCoeffSum]
      ring
    have h30 := hGeneral.2.1
    have h32 := hGeneral.2.2.2.1
    have hNonPrimalTelescope :
        mismatchSum - proxDropSum + dualDropSum +
            (terminalProx + terminalDual) ≤
          terminalPair + initDual := by
      have hStackedInner_sub_smul_left :
          ∀ (a b c : Stacked ι E) (r : ℝ),
            stackedInner (a - r • b) c =
              stackedInner c a - r * stackedInner c b := by
        intro a b c r
        dsimp [stackedInner]
        simp [inner_sub_left, inner_smul_left, real_inner_comm,
          Finset.sum_sub_distrib, Finset.mul_sum]
      have hLagState :
          ∀ t, 1 ≤ t →
            (S.generatedState P hP init samples trace (t - 1)).xLag =
              S.generatedX P hP init samples trace (t - 2) := by
        intro t ht
        by_cases ht2 : 2 ≤ t
        · have hj : 1 ≤ t - 1 := by omega
          have hstep := (trace.step_spec (t - 1) hj).1
          have hidx : (t - 1) - 1 = t - 2 := by omega
          simpa [generatedState, generatedX, hidx] using hstep
        · have ht_eq : t = 1 := by omega
          subst ht_eq
          simp [generatedState, generatedX, initialOuterState, trace.initial_state]
      let delta : ℕ → Stacked ι E := fun t =>
        S.networkOperator
          (S.generatedXHat P hP init samples trace t -
            S.generatedX P hP init samples trace (t - 1))
      let ydiff : ℕ → Stacked ι E := fun t =>
        y - S.generatedY P hP init samples trace t
      have hOuterDelta :
          ∀ t, 1 ≤ t →
            S.networkOperator
              (S.generatedXHat P hP init samples trace t -
                S.outerExtrapolation P t
                  (S.generatedState P hP init samples trace (t - 1))) =
              delta t - P.alpha t • delta (t - 1) := by
        intro t ht
        calc
          S.networkOperator
              (S.generatedXHat P hP init samples trace t -
                S.outerExtrapolation P t
                  (S.generatedState P hP init samples trace (t - 1))) =
              S.networkOperator
                ((S.generatedXHat P hP init samples trace t -
                    S.generatedX P hP init samples trace (t - 1)) -
                  P.alpha t •
                    (S.generatedXHat P hP init samples trace (t - 1) -
                      S.generatedX P hP init samples trace (t - 2))) := by
                congr 1
                ext i
                simp [outerExtrapolation, generatedX, generatedXHat,
                  hLagState t ht, Pi.sub_apply, Pi.add_apply]
                abel
          _ = delta t - P.alpha t • delta (t - 1) := by
                have hidx : t - 1 - 1 = t - 2 := by omega
                simp [delta, ContinuousLinearMap.map_sub, hidx]
      have hDeltaZero : delta 0 = 0 := by
        simp [delta, generatedXHat, generatedX, generatedState, initialOuterState,
          trace.initial_state]
      have hcoeff :
          ∀ t, 2 ≤ t → t ≤ N → P.theta t * P.alpha t / (1 : ℝ) =
            P.theta (t - 1) := by
        intro t ht2 htN
        rw [div_one, mul_comm, h30 t ht2 htN]
      have htel :=
        sum_Icc_weighted_lagged_stackedInner_telescope_eq_terminal_sub
          P.theta P.alpha (1 : ℝ) (0 : Stacked ι E) ydiff delta hN hcoeff hDeltaZero
      have hMismatchAsTelescopeLhs :
          mismatchSum =
            ∑ t ∈ Finset.Icc 1 N,
              P.theta t *
                (stackedInner (ydiff t - (0 : Stacked ι E)) (delta t) -
                  (P.alpha t / (1 : ℝ)) *
                    stackedInner (ydiff t - (0 : Stacked ι E)) (delta (t - 1))) := by
        dsimp [mismatchSum]
        rw [sum_Icc_one_eq_sum_range_succ N
          (fun t =>
            P.theta t *
              (stackedInner (ydiff t - (0 : Stacked ι E)) (delta t) -
                (P.alpha t / (1 : ℝ)) *
                  stackedInner (ydiff t - (0 : Stacked ι E)) (delta (t - 1))))]
        refine Finset.sum_congr rfl ?_
        intro k hk
        have hk1 : 1 ≤ k + 1 := Nat.succ_pos k
        have hOD :
            S.networkOperator
              (S.generatedXHat P hP init samples trace (k + 1) -
                S.outerExtrapolation P (k + 1)
                  (S.generatedState P hP init samples trace k)) =
              delta (k + 1) - P.alpha (k + 1) • delta (k + 1 - 1) := by
          simpa using hOuterDelta (k + 1) hk1
        rw [hOD, hStackedInner_sub_smul_left]
        simp [ydiff]
      have hMismatchTel :
          mismatchSum =
            P.theta N * stackedInner (delta N) (ydiff N) -
              ∑ t ∈ Finset.Icc 2 N,
                P.theta t * P.alpha t *
                  stackedInner (delta (t - 1))
                    (S.generatedY P hP init samples trace (t - 1) -
                      S.generatedY P hP init samples trace t) := by
        rw [hMismatchAsTelescopeLhs, htel]
        congr 1
        · dsimp [ydiff]
          dsimp [stackedInner]
          simp [real_inner_comm]
        · refine Finset.sum_congr rfl ?_
          intro t ht
          dsimp [ydiff]
          dsimp [stackedInner]
          simp [real_inner_comm]
      have hNonPrimalAfterMismatch :
          (P.theta N * stackedInner (delta N) (ydiff N) -
              ∑ t ∈ Finset.Icc 2 N,
                P.theta t * P.alpha t *
                  stackedInner (delta (t - 1))
                    (S.generatedY P hP init samples trace (t - 1) -
                      S.generatedY P hP init samples trace t)) -
              proxDropSum + dualDropSum + (terminalProx + terminalDual) ≤
            terminalPair + initDual := by
        have hDelta_network_norm_sq_dx :
            ∀ t,
              S.stackedNormSq (delta t) ≤
                S.networkOperatorNorm ^ 2 * S.stackedNormSq (dx t) := by
          intro t
          simpa [delta, dx] using
            stacked_network_operator_norm_sq_le S
              (S.generatedXHat P hP init samples trace t -
                S.generatedX P hP init samples trace (t - 1))
        let ystep : ℕ → Stacked ι E := fun t =>
          S.generatedY P hP init samples trace t -
            S.generatedY P hP init samples trace (t - 1)
        have hLaggedYoungPointwise :
            ∀ t ∈ Finset.Icc 2 N,
              P.theta t * P.alpha t *
                  stackedInner (delta (t - 1)) (ystep t) ≤
                (P.theta (t - 1) * P.eta (t - 1) / 2) *
                    S.stackedNormSq (dx (t - 1)) +
                  (P.theta t * P.tau t / 2) * S.stackedNormSq (ystep t) := by
          intro t ht
          have ht2 : 2 ≤ t := (Finset.mem_Icc.mp ht).1
          have htN : t ≤ N := (Finset.mem_Icc.mp ht).2
          have htPrev1 : 1 ≤ t - 1 := by omega
          have htPrevN : t - 1 ≤ N := by omega
          have hthetaPrev : 0 ≤ P.theta (t - 1) :=
            hTheta_nonneg (t - 1) htPrev1 htPrevN
          have htheta : 0 ≤ P.theta t :=
            hTheta_nonneg t (by omega) htN
          have halpha : 0 ≤ P.alpha t := ValidParameters.alpha_nonneg hP t
          have hetaPrev : 0 ≤ P.eta (t - 1) := ValidParameters.eta_nonneg hP (t - 1)
          have htau : 0 ≤ P.tau t := ValidParameters.tau_nonneg hP t
          have hlink : P.alpha t * P.theta t = P.theta (t - 1) :=
            h30 t ht2 htN
          have hcond :
              P.alpha t * S.networkOperatorNorm ^ 2 ≤
                P.eta (t - 1) * P.tau t :=
            h32 t ht2 htN
          exact
            sdcs_lagged_young_absorption S
              (thetaPrev := P.theta (t - 1)) (theta := P.theta t)
              (alpha := P.alpha t) (etaPrev := P.eta (t - 1))
              (tau := P.tau t) (g := delta (t - 1))
              (dx := dx (t - 1)) (dy := ystep t)
              hthetaPrev htheta halpha hetaPrev htau hlink hcond
              (hDelta_network_norm_sq_dx (t - 1))
        have hLaggedYoungSum :
            (∑ t ∈ Finset.Icc 2 N,
              P.theta t * P.alpha t *
                stackedInner (delta (t - 1)) (ystep t)) ≤
              ∑ t ∈ Finset.Icc 2 N,
                ((P.theta (t - 1) * P.eta (t - 1) / 2) *
                    S.stackedNormSq (dx (t - 1)) +
                  (P.theta t * P.tau t / 2) * S.stackedNormSq (ystep t)) := by
          exact Finset.sum_le_sum hLaggedYoungPointwise
        let laggedPrimal : ℝ :=
          ∑ t ∈ Finset.Icc 2 N,
            (P.theta (t - 1) * P.eta (t - 1) / 2) *
              S.stackedNormSq (dx (t - 1))
        let dualTailA : ℝ :=
          ∑ t ∈ Finset.Icc 2 N,
            P.theta t * P.tau t / 2 * S.stackedNormSq (ystep t)
        let dualTailB : ℝ :=
          ∑ t ∈ Finset.Icc 2 N,
            P.theta t * (P.tau t / 2) * S.stackedNormSq (ystep t)
        let endpointDual : ℝ :=
          (P.theta 1 * P.tau 1 / 2) *
            (S.stackedNormSq (y - init.y0) -
              S.stackedNormSq
                (y - S.generatedY P hP init samples trace N))
        have hLaggedOrientation :
            -(∑ t ∈ Finset.Icc 2 N,
                P.theta t * P.alpha t *
                  stackedInner (delta (t - 1))
                    (S.generatedY P hP init samples trace (t - 1) -
                      S.generatedY P hP init samples trace t)) ≤
              laggedPrimal + dualTailA := by
          have hsign :
              -(∑ t ∈ Finset.Icc 2 N,
                  P.theta t * P.alpha t *
                    stackedInner (delta (t - 1))
                      (S.generatedY P hP init samples trace (t - 1) -
                        S.generatedY P hP init samples trace t)) =
                ∑ t ∈ Finset.Icc 2 N,
                  P.theta t * P.alpha t *
                    stackedInner (delta (t - 1)) (ystep t) := by
            rw [← Finset.sum_neg_distrib]
            refine Finset.sum_congr rfl ?_
            intro t ht
            dsimp [ystep, stackedInner]
            simp [Pi.sub_apply, inner_sub_right, Finset.sum_sub_distrib,
              Finset.mul_sum]
            ring
          calc
            -(∑ t ∈ Finset.Icc 2 N,
                P.theta t * P.alpha t *
                  stackedInner (delta (t - 1))
                    (S.generatedY P hP init samples trace (t - 1) -
                      S.generatedY P hP init samples trace t))
                = ∑ t ∈ Finset.Icc 2 N,
                    P.theta t * P.alpha t *
                      stackedInner (delta (t - 1)) (ystep t) := hsign
            _ ≤ ∑ t ∈ Finset.Icc 2 N,
                ((P.theta (t - 1) * P.eta (t - 1) / 2) *
                    S.stackedNormSq (dx (t - 1)) +
                  (P.theta t * P.tau t / 2) * S.stackedNormSq (ystep t)) :=
                  hLaggedYoungSum
            _ = laggedPrimal + dualTailA := by
                  dsimp [laggedPrimal, dualTailA]
                  rw [Finset.sum_add_distrib]
        have hProxBudget :
            terminalProx + laggedPrimal ≤ proxDropSum := by
          simpa [terminalProx, laggedPrimal, proxDropSum] using hProxRetainedBudget
        have hDualBudget :
            dualDropSum ≤ endpointDual - dualTailB := by
          simpa [dualDropSum, endpointDual, dualTailB, ystep, stackedNormSq_sub_comm S]
            using hDualDropUpper
        have hDualTailEq : dualTailA = dualTailB := by
          dsimp [dualTailA, dualTailB]
          refine Finset.sum_congr rfl ?_
          intro t ht
          ring
        have hEndpoint :
            terminalDual + endpointDual = initDual := by
          dsimp [terminalDual, endpointDual, initDual]
          ring
        have hAssembly :=
          sdcs_retained_nonprimal_assembly_algebra
            (term := P.theta N * stackedInner (delta N) (ydiff N))
            (lagged :=
              ∑ t ∈ Finset.Icc 2 N,
                P.theta t * P.alpha t *
                  stackedInner (delta (t - 1))
                    (S.generatedY P hP init samples trace (t - 1) -
                      S.generatedY P hP init samples trace t))
            (prox := proxDropSum) (dual := dualDropSum)
            (terminalProx := terminalProx) (terminalDual := terminalDual)
            (laggedPrimal := laggedPrimal) (dualTailA := dualTailA)
            (dualTailB := dualTailB) (endpointDual := endpointDual)
            (initDual := initDual)
            hLaggedOrientation hProxBudget hDualBudget hDualTailEq hEndpoint
        dsimp [terminalPair, delta, ydiff, terminalProx, terminalDual, initDual] at hAssembly ⊢
        linarith
      rw [hMismatchTel]
      linarith
    have hDeltaBudget :=
      retained_delta_budget_le_of_expand_and_nonprimal
        (deltaSum := ∑ k ∈ Finset.range N, P.theta (k + 1) * deltaRaw (k + 1))
        (potential := S.generalSDCSRawTerminalPotential P hP init samples trace x N)
        (mismatch := mismatchSum) (prox := proxDropSum) (dual := dualDropSum)
        (terminal := terminalPair + initDual)
        (retained := terminalProx + terminalDual)
        hDeltaExpand hNonPrimalTelescope
    dsimp [terminalProx, terminalDual, terminalPair, initDual] at hDeltaBudget
    linarith
  have horacle :
      (∑ k ∈ Finset.range N, weightedOracle k) =
        S.generalSDCSRawOracleErrorBudget P hP init samples trace x N := by
    simp [weightedOracle, generalSDCSRawOracleErrorBudget]
  have hagg :=
    weighted_gap_plus_retained_terms_le_of_step_and_delta_budget
      N (fun k => P.theta (k + 1)) gap (fun k => deltaRaw (k + 1)) weightedOracle
      (P.theta N *
          stackedInner
            (S.networkOperator
              (S.generatedXHat P hP init samples trace N -
                S.generatedX P hP init samples trace (N - 1)))
            (y - S.generatedY P hP init samples trace N) +
        S.generalSDCSRawTerminalPotential P hP init samples trace x N +
          (P.theta 1 * P.tau 1 / 2) *
            S.stackedNormSq (y - init.y0))
      (P.theta N * P.eta N *
        S.stackedProx
          (S.generatedX P hP init samples trace (N - 1))
          (S.generatedXHat P hP init samples trace N) +
        (P.theta 1 * P.tau 1 / 2) *
          S.stackedNormSq
            (y - S.generatedY P hP init samples trace N))
      (S.generalSDCSRawOracleErrorBudget P hP init samples trace x N)
      hWeightedStep hRetainedDelta horacle
  simpa [gap, add_assoc] using hagg

/-- Lemma 8.5 retained terminal residual aggregate.

This is Source.json `GeneralSDCSGapLemma85` proof step 16 specialized to a
saddle point.  It reuses the raw weighted one-step/delta telescope route but
stops before the terminal prox and dual-square terms are dropped in the
`general_sdcs_weighted_gap_sum_raw_terminal_le` projection.
-/
private theorem general_sdcs_retained_terminal_residual_bound
    (P : Parameters) (hP : ValidParameters P) (init : InitialState S)
    (samples : ℕ → ι → ℕ → Ξ) (trace : S.GeneratedTrace P hP init samples)
    (N : ℕ) (hN : 1 ≤ N) (hGeneral : S.generalParameterConditions P N)
    (hDenom : ∀ k, 1 ≤ k → k ≤ N → 0 < P.innerSteps k ∧ 0 < P.eta k)
    (hTheta_nonneg : ∀ k, 1 ≤ k → k ≤ N → 0 ≤ P.theta k)
    (hRawInnerTerminal :
      ∀ (i : ι) (k : ℕ), 1 ≤ k → k ≤ N → ∀ u : E, u ∈ S.feasible i →
          let centerState := S.generatedState P hP init samples trace (k - 1)
          let T := P.innerSteps k
          let coeff := 2 / ((T : ℝ) * ((T : ℝ) + 3))
          coeff *
              (∑ t ∈ Finset.range T, csLambda (t + 1) *
                ((P.eta k * csBeta (t + 1)) *
                    S.localProx i (S.generatedInnerQuery P hP init samples trace i k t) u -
                  (P.eta k + P.eta k * csBeta (t + 1)) *
                    S.localProx i
                      (S.generatedInnerQuery P hP init samples trace i k (t + 1)) u)) ≤
            generalSDCSRawPrimalTelescopeInitialCoeff P k *
                S.localProx i (centerState.xPrev i) u -
              generalSDCSRawPrimalTerminalCoeff P k *
                S.localProx i (S.generatedX P hP init samples trace k i) u)
    (xStar yStar : Stacked ι E)
    (hxStar : S.PrimalOptimalSolution xStar)
    (hyStar : S.DualOptimalSolution xStar yStar)
    (hSaddleWeightedNonneg :
      0 ≤ ∑ k ∈ Finset.range N,
        P.theta (k + 1) *
          S.primalDualGap
            (S.generatedXHat P hP init samples trace (k + 1))
            (S.generatedY P hP init samples trace (k + 1)) xStar yStar) :
    P.theta N * P.eta N *
        S.stackedProx
          (S.generatedX P hP init samples trace (N - 1))
          (S.generatedXHat P hP init samples trace N) +
      (P.theta 1 * P.tau 1 / 2) *
        S.stackedNormSq
          (yStar - S.generatedY P hP init samples trace N) ≤
      P.theta N *
        stackedInner
          (S.networkOperator
            (S.generatedXHat P hP init samples trace N -
              S.generatedX P hP init samples trace (N - 1)))
          (yStar - S.generatedY P hP init samples trace N) +
        S.generalSDCSGapLemma85RawResidualRHS P hP init samples trace xStar yStar N := by
  classical
  have hRetained :=
    S.general_sdcs_weighted_gap_sum_retained_terminal_le
      P hP init samples trace N hN hGeneral hDenom hTheta_nonneg
      hRawInnerTerminal xStar yStar hxStar.1
  dsimp [generalSDCSGapLemma85RawResidualRHS] at hRetained ⊢
  linarith [hRetained, hSaddleWeightedNonneg]

/-- Lemma 8.5 source-boundary package.

It preserves the authoritative source's common coefficient on the complete
Bregman difference and exposes all three consequences used by Theorem 8.11:
the `Q` gap inequality, the perturbed-gap inequality used with Proposition 8.6,
and the residual inequality (8.3.66) used for the consensus second moments.
-/
structure GeneralSDCSGapLemma85RawTerminalBridge
    (P : Parameters) (hP : ValidParameters P) (init : InitialState S)
    (samples : ℕ → ι → ℕ → Ξ) (trace : S.GeneratedTrace P hP init samples)
    (N : ℕ) : Prop where
  gap_bound :
    ∀ x y : Stacked ι E,
      S.FeasiblePoint x →
      S.primalDualGap
          (S.weightedPrimalAverage P hP init samples trace N)
          (S.weightedDualAverage P hP init samples trace N) x y ≤
        (∑ k ∈ Finset.range N, P.theta (k + 1))⁻¹ *
          S.generalSDCSGapLemma85RawTerminalRHS P hP init samples trace x y N
  perturbed_gap_bound :
    ∀ xStar : Stacked ι E,
      S.PrimalOptimalSolution xStar →
      S.perturbedGap
          (S.weightedPrimalAverage P hP init samples trace N)
          (S.weightedDualAverage P hP init samples trace N)
          xStar
          (S.scaledPerturbation P hP init samples trace N) ≤
        (∑ k ∈ Finset.range N, P.theta (k + 1))⁻¹ *
          S.generalSDCSGapLemma85RawPerturbedGapRHS P hP init samples trace xStar N
  perturbed_gap_finite :
    ∀ xStar : Stacked ι E,
      S.PrimalOptimalSolution xStar →
      S.PerturbedGapFinite
          (S.weightedPrimalAverage P hP init samples trace N)
          (S.weightedDualAverage P hP init samples trace N)
          xStar
          (S.scaledPerturbation P hP init samples trace N)
  residual_bound :
    ∀ xStar yStar : Stacked ι E,
      S.PrimalOptimalSolution xStar → S.DualOptimalSolution xStar yStar →
        1 ≤ P.theta N →
        S.generalSDCSGapLemma85ResidualLHS P hP init samples trace xStar yStar N ≤
          S.generalSDCSGapLemma85RawResidualRHS P hP init samples trace xStar yStar N

/-- Lemma 8.5 raw-terminal source boundary.

The bridge retains the source's common coefficient on the complete Bregman
difference.  Its explicit source correction is the negative oracle-error linear
term forced by Proposition 8.7 under oracleError = subgradient - oracle.

The weighted-output step also uses nonnegative theta_k and a positive
normalizer.  The residual consequence exposes 1 <= theta_N; the Theorem 8.11
schedule has theta_k = 1 and discharges it without adding a Setup assumption.
-/

theorem generalSDCSGapLemma85_rawTerminal_bridge_sourceBoundaryCorrected
    (P : Parameters) (hP : ValidParameters P) (init : InitialState S)
    (samples : ℕ → ι → ℕ → Ξ) (trace : S.GeneratedTrace P hP init samples)
    (N : ℕ) (hN : 1 ≤ N) (hGeneral : S.generalParameterConditions P N)
    (hDenom : ∀ k, 1 ≤ k → k ≤ N → 0 < P.innerSteps k ∧ 0 < P.eta k)
    (hTheta_nonneg : ∀ k, 1 ≤ k → k ≤ N → 0 ≤ P.theta k)
    (hTheta_sum_pos : 0 < ∑ k ∈ Finset.range N, P.theta (k + 1)) :
    S.GeneralSDCSGapLemma85RawTerminalBridge P hP init samples trace N := by
  classical
  have hInnerSteps_pos :
      ∀ k, 1 ≤ k → k ≤ N → 0 < P.innerSteps k :=
    fun k hk hkN => (hDenom k hk hkN).1
  have heta_pos :
      ∀ k, 1 ≤ k → k ≤ N → 0 < P.eta k :=
    fun k hk hkN => (hDenom k hk hkN).2
  have hTheta_nonneg' :
      ∀ k, 1 ≤ k → k ≤ N → 0 ≤ P.theta k := hTheta_nonneg
  have hTheta_sum_pos' :
      0 < ∑ k ∈ Finset.range N, P.theta (k + 1) := hTheta_sum_pos
  have hRawInnerTerminal :
      ∀ (i : ι) (k : ℕ), 1 ≤ k → k ≤ N → ∀ u : E, u ∈ S.feasible i →
          let centerState := S.generatedState P hP init samples trace (k - 1)
          let T := P.innerSteps k
          let coeff := 2 / ((T : ℝ) * ((T : ℝ) + 3))
          coeff *
              (∑ t ∈ Finset.range T, csLambda (t + 1) *
                ((P.eta k * csBeta (t + 1)) *
                    S.localProx i (S.generatedInnerQuery P hP init samples trace i k t) u -
                  (P.eta k + P.eta k * csBeta (t + 1)) *
                    S.localProx i
                      (S.generatedInnerQuery P hP init samples trace i k (t + 1)) u)) ≤
            generalSDCSRawPrimalTelescopeInitialCoeff P k *
                S.localProx i (centerState.xPrev i) u -
              generalSDCSRawPrimalTerminalCoeff P k *
                S.localProx i (S.generatedX P hP init samples trace k i) u := by
    intro i k hk hkN u hu
    have hT : 0 < P.innerSteps k := hInnerSteps_pos k hk hkN
    exact
      S.generated_inner_bregman_raw_terminal_bound P hP init samples trace
        i k hk u hu hT
  have hWeightedQ :
      ∀ x y : Stacked ι E,
        S.FeasiblePoint x →
          (∑ k ∈ Finset.range N,
            P.theta (k + 1) *
              S.primalDualGap
                (S.generatedXHat P hP init samples trace (k + 1))
                (S.generatedY P hP init samples trace (k + 1)) x y) ≤
            S.generalSDCSGapLemma85RawTerminalRHS P hP init samples trace x y N :=
    S.general_sdcs_weighted_gap_sum_raw_terminal_le
      P hP init samples trace N hN hGeneral hDenom hTheta_nonneg hRawInnerTerminal
  have hGapAvg :
      ∀ x y : Stacked ι E,
        S.FeasiblePoint x →
          S.primalDualGap
              (S.weightedPrimalAverage P hP init samples trace N)
              (S.weightedDualAverage P hP init samples trace N) x y ≤
            (∑ k ∈ Finset.range N, P.theta (k + 1))⁻¹ *
              S.generalSDCSGapLemma85RawTerminalRHS P hP init samples trace x y N :=
    S.general_sdcs_weighted_average_gap_bound_from_sum
      P hP init samples trace N hDenom hTheta_nonneg hTheta_sum_pos hWeightedQ
  have hPerturbedGapBoundAndFinite :
      ∀ xStar : Stacked ι E,
        S.PrimalOptimalSolution xStar →
          S.perturbedGap
              (S.weightedPrimalAverage P hP init samples trace N)
              (S.weightedDualAverage P hP init samples trace N)
              xStar
              (S.scaledPerturbation P hP init samples trace N) ≤
            (∑ k ∈ Finset.range N, P.theta (k + 1))⁻¹ *
              S.generalSDCSGapLemma85RawPerturbedGapRHS P hP init samples trace xStar N ∧
          S.PerturbedGapFinite
              (S.weightedPrimalAverage P hP init samples trace N)
              (S.weightedDualAverage P hP init samples trace N)
              xStar
              (S.scaledPerturbation P hP init samples trace N) := by
    intro xStar hxStar
    let W : ℝ := ∑ k ∈ Finset.range N, P.theta (k + 1)
    let bound : ℝ :=
      W⁻¹ * S.generalSDCSGapLemma85RawPerturbedGapRHS P hP init samples trace xStar N
    have hSupportUpper :
        ∀ q ∈ S.perturbedGapSupport
            (S.weightedPrimalAverage P hP init samples trace N)
            (S.weightedDualAverage P hP init samples trace N)
            xStar
            (S.scaledPerturbation P hP init samples trace N), q ≤ bound := by
      intro q hq
      rcases hq with ⟨ybar, rfl⟩
      have hgap := hGapAvg xStar ybar hxStar.1
      have hscaledPairing :
          stackedInner (S.scaledPerturbation P hP init samples trace N) ybar =
            W⁻¹ * stackedInner (S.perturbationVector P hP init samples trace N) ybar := by
        dsimp [W, scaledPerturbation, stackedInner, SOptLib.dependentProductInner]
        rw [Finset.mul_sum]
        simp [inner_smul_left]
      have hcancel :
          (∑ k ∈ Finset.range N, P.theta (k + 1))⁻¹ *
              S.generalSDCSGapLemma85RawTerminalRHS P hP init samples trace xStar ybar N -
            stackedInner (S.scaledPerturbation P hP init samples trace N) ybar = bound := by
        dsimp [bound, W, generalSDCSGapLemma85RawTerminalRHS,
          generalSDCSGapLemma85RawPerturbedGapRHS]
        rw [hscaledPairing]
        ring
      calc
        S.primalDualGap
            (S.weightedPrimalAverage P hP init samples trace N)
            (S.weightedDualAverage P hP init samples trace N) xStar ybar -
            stackedInner (S.scaledPerturbation P hP init samples trace N) ybar
            ≤ (∑ k ∈ Finset.range N, P.theta (k + 1))⁻¹ *
                S.generalSDCSGapLemma85RawTerminalRHS P hP init samples trace xStar ybar N -
              stackedInner (S.scaledPerturbation P hP init samples trace N) ybar := by
              linarith
        _ = bound := hcancel
    have hBdd :
        BddAbove (S.perturbedGapSupport
            (S.weightedPrimalAverage P hP init samples trace N)
            (S.weightedDualAverage P hP init samples trace N)
            xStar
            (S.scaledPerturbation P hP init samples trace N)) :=
      ⟨bound, hSupportUpper⟩
    refine ⟨?_, hBdd⟩
    have hNonempty :
        (S.perturbedGapSupport
            (S.weightedPrimalAverage P hP init samples trace N)
            (S.weightedDualAverage P hP init samples trace N)
            xStar
            (S.scaledPerturbation P hP init samples trace N)).Nonempty := by
      refine ⟨S.primalDualGap
          (S.weightedPrimalAverage P hP init samples trace N)
          (S.weightedDualAverage P hP init samples trace N) xStar 0 -
          stackedInner (S.scaledPerturbation P hP init samples trace N) 0, ?_⟩
      exact ⟨0, rfl⟩
    dsimp [perturbedGap]
    exact csSup_le hNonempty hSupportUpper
  refine
    { gap_bound := ?_
      perturbed_gap_bound := ?_
      perturbed_gap_finite := ?_
      residual_bound := ?_ }
  · intro x y hx
    exact hGapAvg x y hx
  · intro xStar hxStar
    exact (hPerturbedGapBoundAndFinite xStar hxStar).1
  · intro xStar hxStar
    exact (hPerturbedGapBoundAndFinite xStar hxStar).2
  · intro xStar yStar hxStar hyStar hThetaN_ge_one
    let coeff : ℝ :=
      (P.theta N / 2) *
        (1 - P.theta N * S.networkOperatorNorm ^ 2 / (P.eta N * P.tau N))
    have hSaddleWeightedNonneg :
        0 ≤ ∑ k ∈ Finset.range N,
          P.theta (k + 1) *
            S.primalDualGap
              (S.generatedXHat P hP init samples trace (k + 1))
              (S.generatedY P hP init samples trace (k + 1)) xStar yStar := by
      refine Finset.sum_nonneg ?_
      intro k hk
      have hkk1 : 1 ≤ k + 1 := Nat.succ_pos k
      have hkkN : k + 1 ≤ N := Nat.succ_le_of_lt (Finset.mem_range.mp hk)
      have htheta : 0 ≤ P.theta (k + 1) :=
        hTheta_nonneg (k + 1) hkk1 hkkN
      have hxhat :
          S.FeasiblePoint (S.generatedXHat P hP init samples trace (k + 1)) :=
        S.generatedXHat_mem P hP init samples trace (k + 1) hkk1
          (hDenom (k + 1) hkk1 hkkN).1
      have hgap_nonneg :
          0 ≤ S.primalDualGap
            (S.generatedXHat P hP init samples trace (k + 1))
            (S.generatedY P hP init samples trace (k + 1)) xStar yStar :=
        (hyStar.2
          (S.generatedXHat P hP init samples trace (k + 1))
          (S.generatedY P hP init samples trace (k + 1)) hxhat).2
      exact mul_nonneg htheta hgap_nonneg
    let dxN : Stacked ι E :=
      S.generatedXHat P hP init samples trace N -
        S.generatedX P hP init samples trace (N - 1)
    let gN : Stacked ι E := S.networkOperator dxN
    let vN : Stacked ι E := yStar - S.generatedY P hP init samples trace N
    let proxN : ℝ :=
      S.stackedProx
        (S.generatedX P hP init samples trace (N - 1))
        (S.generatedXHat P hP init samples trace N)
    let R : ℝ :=
      S.generalSDCSGapLemma85RawResidualRHS P hP init samples trace xStar yStar N
    have hRetained :
        P.theta N * P.eta N * proxN +
          (P.theta 1 * P.tau 1 / 2) * S.stackedNormSq vN ≤
        P.theta N * stackedInner gN vN + R := by
      simpa [dxN, gN, vN, proxN, R] using
        S.general_sdcs_retained_terminal_residual_bound
          P hP init samples trace N hN hGeneral hDenom hTheta_nonneg
          hRawInnerTerminal xStar yStar hxStar hyStar hSaddleWeightedNonneg
    have hThetaTauN : P.theta N * P.tau N = P.theta 1 * P.tau 1 := by
      by_cases hN_one : N = 1
      · subst hN_one
        rfl
      · have hN_two : 2 ≤ N := by omega
        exact hGeneral.2.2.1 N hN_two le_rfl
    have hProxN_lower :
        (1 / 2 : ℝ) * S.stackedNormSq dxN ≤ proxN := by
      have hxprev :
          S.FeasiblePoint (S.generatedX P hP init samples trace (N - 1)) := by
        simpa [generatedX, generatedState] using
          (S.generatedState P hP init samples trace (N - 1)).xPrev_mem
      have hxhat :
          S.FeasiblePoint (S.generatedXHat P hP init samples trace N) :=
        S.generatedXHat_mem P hP init samples trace N hN
          (hDenom N hN le_rfl).1
      have hprox :=
        S.stackedProx_lower_bound
          (S.generatedX P hP init samples trace (N - 1))
          (S.generatedXHat P hP init samples trace N)
          hxprev hxhat
      simpa [dxN, proxN, stackedNormSq_sub_comm S
        (S.generatedXHat P hP init samples trace N)
        (S.generatedX P hP init samples trace (N - 1))] using hprox
    have hNetworkN :
        S.stackedNormSq gN ≤ S.networkOperatorNorm ^ 2 * S.stackedNormSq dxN := by
      simpa [dxN, gN] using stacked_network_operator_norm_sq_le S dxN
    have hBranches :
        coeff * (P.eta N * S.stackedNormSq dxN) ≤ R ∧
          coeff * (P.tau N * S.stackedNormSq vN) ≤ R := by
      simpa [coeff, dxN, gN, vN, proxN, R] using
        sdcs_residual_branches_of_retained_terminal_bound_nonneg_tau S
          (theta := P.theta N) (eta := P.eta N) (tau := P.tau N)
          (theta1 := P.theta 1) (tau1 := P.tau 1)
          (R := R) (prox := proxN) (dx := dxN) (g := gN) (v := vN)
          (hTheta_nonneg N hN le_rfl) (hDenom N hN le_rfl).2
          (ValidParameters.tau_nonneg hP N) hThetaN_ge_one hThetaTauN
          hGeneral.2.2.2.2 hProxN_lower hNetworkN hRetained
    have hPrimalTerminalBranch :
        coeff *
            (P.eta N *
              S.stackedNormSq
                (S.generatedXHat P hP init samples trace N -
                  S.generatedX P hP init samples trace (N - 1))) ≤
          S.generalSDCSGapLemma85RawResidualRHS P hP init samples trace xStar yStar N := by
      simpa [dxN, R] using hBranches.1
    have hDualTerminalBranch :
        coeff *
            (P.tau N *
              S.stackedNormSq
                (yStar - S.generatedY P hP init samples trace N)) ≤
          S.generalSDCSGapLemma85RawResidualRHS P hP init samples trace xStar yStar N := by
      simpa [vN, R] using hBranches.2
    dsimp [generalSDCSGapLemma85ResidualLHS, coeff]
    exact mul_max_le_of_mul_le_left_right hPrimalTerminalBranch hDualTerminalBranch

/-- Corrected Lemma 8.5 raw-terminal `Q`-gap projection.

Consumers that need the Theorem 8.11 route should prefer the bridge package
`generalSDCSGapLemma85_rawTerminal_bridge_sourceBoundaryCorrected`, because it
also carries the perturbed-gap and residual consequences.
-/
theorem generalSDCSGapLemma85_rawTerminal_sourceBoundaryCorrected
    (P : Parameters) (hP : ValidParameters P) (init : InitialState S)
    (samples : ℕ → ι → ℕ → Ξ) (trace : S.GeneratedTrace P hP init samples)
    (N : ℕ) (hN : 1 ≤ N) (hGeneral : S.generalParameterConditions P N)
    (hDenom : ∀ k, 1 ≤ k → k ≤ N → 0 < P.innerSteps k ∧ 0 < P.eta k)
    (hTheta_nonneg : ∀ k, 1 ≤ k → k ≤ N → 0 ≤ P.theta k)
    (hTheta_sum_pos : 0 < ∑ k ∈ Finset.range N, P.theta (k + 1))
    (x y : Stacked ι E) (hx : S.FeasiblePoint x) :
    S.primalDualGap
        (S.weightedPrimalAverage P hP init samples trace N)
        (S.weightedDualAverage P hP init samples trace N) x y ≤
      (∑ k ∈ Finset.range N, P.theta (k + 1))⁻¹ *
        S.generalSDCSGapLemma85RawTerminalRHS P hP init samples trace x y N := by
  exact
    (S.generalSDCSGapLemma85_rawTerminal_bridge_sourceBoundaryCorrected
      P hP init samples trace N hN hGeneral hDenom hTheta_nonneg hTheta_sum_pos).gap_bound
        x y hx

/-- Expected raw primal Bregman boundary for the Theorem 8.11 schedule. -/
def theorem811ExpectedRawTerminalPotential
    (init : InitialState S) (run : OracleRun S Ω)
    (N : ℕ) (hN : 1 ≤ N) (Dtilde : ℝ)
    (hSchedule : S.Theorem811ScheduleWellDefined N Dtilde)
    (trace : ∀ ω,
      S.GeneratedTrace (S.theorem811Parameters N Dtilde hSchedule)
        (S.theorem811Parameters_valid N Dtilde hSchedule) init (run.samples ω))
    (xStar : Stacked ι E) : ℝ :=
  let P := S.theorem811Parameters N Dtilde hSchedule
  let hP := S.theorem811Parameters_valid N Dtilde hSchedule
  ∫ ω, S.generalSDCSRawTerminalPotential P hP init (run.samples ω) (trace ω) xStar N
    ∂run.law

/-- Expected exact raw perturbed-gap RHS from the Lemma 8.5 route.

This expression keeps the complete coefficient-weighted terminal Bregman
difference and exact Young-square oracle budget.  The direct expectation bridge
then applies the valid square estimate, fresh-query cancellation, and variance
control to obtain the published Theorem 8.11 constant.
-/

def theorem811ExpectedRawPerturbedGapRHS
    (init : InitialState S) (run : OracleRun S Ω)
    (N : ℕ) (hN : 1 ≤ N) (Dtilde : ℝ)
    (hSchedule : S.Theorem811ScheduleWellDefined N Dtilde)
    (trace : ∀ ω,
      S.GeneratedTrace (S.theorem811Parameters N Dtilde hSchedule)
        (S.theorem811Parameters_valid N Dtilde hSchedule) init (run.samples ω))
    (xStar : Stacked ι E) : ℝ :=
  let P := S.theorem811Parameters N Dtilde hSchedule
  let hP := S.theorem811Parameters_valid N Dtilde hSchedule
  ∫ ω,
    S.generalSDCSGapLemma85RawPerturbedGapRHS P hP init (run.samples ω) (trace ω)
      xStar N ∂run.law

/-- Expected corrected raw residual RHS from Lemma 8.5 / (8.3.66). -/
def theorem811ExpectedRawResidualRHS
    (init : InitialState S) (run : OracleRun S Ω)
    (N : ℕ) (hN : 1 ≤ N) (Dtilde : ℝ)
    (hSchedule : S.Theorem811ScheduleWellDefined N Dtilde)
    (trace : ∀ ω,
      S.GeneratedTrace (S.theorem811Parameters N Dtilde hSchedule)
        (S.theorem811Parameters_valid N Dtilde hSchedule) init (run.samples ω))
    (xStar yStar : Stacked ι E) : ℝ :=
  let P := S.theorem811Parameters N Dtilde hSchedule
  let hP := S.theorem811Parameters_valid N Dtilde hSchedule
  ∫ ω,
    S.generalSDCSGapLemma85RawResidualRHS P hP init (run.samples ω) (trace ω)
      xStar yStar N ∂run.law

/-- Under the Theorem 8.11 schedule, the Lemma 8.5 weighted primal output is the
actual averaged generated iterate `N⁻¹ ∑_{k=1}^N xhat_k`.

Source: `book/research/Source.json#/main_theorem/statement_math` sets
`theta_k = 1` and defines `\hat{x}_N = N^{-1}\sum_{k=1}^N\hat{x}_k`.
-/
private theorem theorem811_weightedPrimalAverage_eq_theorem811PrimalAverage
    (init : InitialState S) (N : ℕ) (Dtilde : ℝ)
    (hSchedule : S.Theorem811ScheduleWellDefined N Dtilde)
    (samples : ℕ → ι → ℕ → Ξ)
    (trace :
      S.GeneratedTrace (S.theorem811Parameters N Dtilde hSchedule)
        (S.theorem811Parameters_valid N Dtilde hSchedule) init samples) :
    let P := S.theorem811Parameters N Dtilde hSchedule
    let hP := S.theorem811Parameters_valid N Dtilde hSchedule
    S.weightedPrimalAverage P hP init samples trace N =
      S.theorem811PrimalAverage P hP init samples trace N := by
  classical
  dsimp [weightedPrimalAverage, theorem811PrimalAverage, theorem811Parameters]
  simp

/-- Raw-terminal objective-residual expression for Theorem 8.11.

It measures the exact expected Lemma 8.5 perturbed-gap budget at the actual
generated average.  The completed direct finite-horizon expectation bridge
bounds this expression by the published objective constant.
-/

def theorem811ObjectiveResidualRawTerminalBound
    (init : InitialState S) (run : OracleRun S Ω)
    (N : ℕ) (hN : 1 ≤ N) (Dtilde : ℝ)
    (hSchedule : S.Theorem811ScheduleWellDefined N Dtilde)
    (trace : ∀ ω,
      S.GeneratedTrace (S.theorem811Parameters N Dtilde hSchedule)
        (S.theorem811Parameters_valid N Dtilde hSchedule) init (run.samples ω))
    (xStar : Stacked ι E) : ℝ :=
  (1 / (N : ℝ)) *
    S.theorem811ExpectedRawPerturbedGapRHS init run N hN Dtilde hSchedule trace xStar

/-- Real-valued expectation lift used at the Theorem 8.11 source boundary.

This is intentionally only the Mathlib/Bochner-integral part of the source
expectation step: pointwise Lemma 8.5 inequalities can be integrated once the
two generated real-valued integrands are known integrable.  The stochastic
cancellation and variance estimates remain in the source-stage theorem bodies
where the exact SDCS oracle budget is assembled.
-/
private theorem integral_le_of_forall_le_of_integrable
    {f g : Ω → ℝ} {μ : Measure Ω}
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hpoint : ∀ ω, f ω ≤ g ω) :
    (∫ ω, f ω ∂μ) ≤ ∫ ω, g ω ∂μ := by
  exact MeasureTheory.integral_mono_ae hf hg (Filter.Eventually.of_forall hpoint)



/-- Printed (8.3.71) budget for the expected perturbed gap of the actual
Theorem 8.11 averaged generated iterate. -/
def theorem811ExpectedPerturbedGapBudget
    (init : InitialState S) (N : ℕ) (Dtilde : ℝ)
    (xStar : Stacked ι E) : ℝ :=
  (S.networkOperatorNorm / (N : ℝ)) *
    (3 * S.stackedProx init.x0 xStar +
      (1 / 2 : ℝ) * S.stackedNormSq init.y0 + 4 * Dtilde)

/-- Source-sized expectation budget obtained by applying the Theorem 8.11
schedule to the residual inequality (8.3.66).  Under the schedule this is the
common budget whose two branches give the squared-distance estimates used in
the proof of (8.3.69). -/
def theorem811ExpectedResidualLHSBudget
    (init : InitialState S) (Dtilde : ℝ)
    (xStar yStar : Stacked ι E) : ℝ :=
  S.networkOperatorNorm *
    (3 * S.stackedProx init.x0 xStar +
      (1 / 2 : ℝ) * S.stackedNormSq (yStar - init.y0) + 4 * Dtilde)

/-- Formula-level expectation-and-budget interface for Theorem 8.11.

This is the active replacement for the retired generated-component regularity
route.  Its two inequalities are exactly the source transition obtained by
taking expectations in corrected (8.3.70) and (8.3.66), cancelling the fresh
generated-query linear errors, bounding the quadratic oracle errors, and
substituting the constant schedule.  Residual-LHS integrability is included as
the internally derived analytic fact needed by the subsequent Jensen step; it
is not an additional theorem-level assumption. -/
structure Theorem811ExpectedBudgetBridge
    (init : InitialState S) (run : OracleRun S Ω)
    (N : ℕ) (hN : 1 ≤ N) (Dtilde : ℝ)
    (hSchedule : S.Theorem811ScheduleWellDefined N Dtilde)
    (core :
      S.GeneratedProcessCore (S.theorem811Parameters N Dtilde hSchedule)
        (S.theorem811Parameters_valid N Dtilde hSchedule) init run)
    (xStar yStar : Stacked ι E) : Prop where
  perturbed_gap_bound :
    let P := S.theorem811Parameters N Dtilde hSchedule
    let hP := S.theorem811Parameters_valid N Dtilde hSchedule
    ∫ ω,
      S.perturbedGap
        (S.theorem811PrimalAverage P hP init (run.samples ω) (core.trace ω) N)
        (S.weightedDualAverage P hP init (run.samples ω) (core.trace ω) N)
        xStar
        (S.scaledPerturbation P hP init (run.samples ω) (core.trace ω) N) ∂run.law ≤
      S.theorem811ExpectedPerturbedGapBudget init N Dtilde xStar
  residualLHS_integrable :
    let P := S.theorem811Parameters N Dtilde hSchedule
    let hP := S.theorem811Parameters_valid N Dtilde hSchedule
    Integrable
      (fun ω =>
        S.generalSDCSGapLemma85ResidualLHS P hP init (run.samples ω) (core.trace ω)
          xStar yStar N)
      run.law
  residual_lhs_bound :
    let P := S.theorem811Parameters N Dtilde hSchedule
    let hP := S.theorem811Parameters_valid N Dtilde hSchedule
    ∫ ω,
      S.generalSDCSGapLemma85ResidualLHS P hP init (run.samples ω) (core.trace ω)
        xStar yStar N ∂run.law ≤
      S.theorem811ExpectedResidualLHSBudget init Dtilde xStar yStar

/-- Exact analytic obstruction reached by the direct Theorem 8.11
expectation-and-budget proof.

This is deliberately a private formula-level target, not a process field or a
premise of a source-facing theorem.  The source assumptions prove that the
integral of each displayed generated-query term is zero and that the oracle
error has an integrable square.  Mathlib's finite-sum integral rule additionally
requires the displayed scalar product itself to be integrable; that does not
follow from those two facts without a moment bound for the generated direction.
-/
private def theorem811GeneratedLinearErrorIntegrable
    (init : InitialState S) (run : OracleRun S Ω)
    (N : ℕ) (Dtilde : ℝ)
    (hSchedule : S.Theorem811ScheduleWellDefined N Dtilde)
    (core :
      S.GeneratedProcessCore (S.theorem811Parameters N Dtilde hSchedule)
        (S.theorem811Parameters_valid N Dtilde hSchedule) init run)
    (xStar : Stacked ι E) : Prop :=
  let P := S.theorem811Parameters N Dtilde hSchedule
  let hP := S.theorem811Parameters_valid N Dtilde hSchedule
  ∀ (i : ι) (k : ℕ), k ∈ Finset.range N →
    let kk := k + 1
    ∀ (t : ℕ), t ∈ Finset.range (P.innerSteps kk) →
      Integrable
        (fun ω =>
          inner ℝ
            (S.oracleError i
              (S.generatedInnerQuery P hP init (run.samples ω) (core.trace ω) i kk t)
              (run.samples ω kk i t))
            (xStar i -
              S.generatedInnerQuery P hP init (run.samples ω) (core.trace ω) i kk t))
        run.law

private theorem theorem811_rawTerminalPotential_le_initial
    (init : InitialState S) (N : ℕ) (hN : 1 ≤ N) (Dtilde : ℝ)
    (hSchedule : S.Theorem811ScheduleWellDefined N Dtilde)
    (samples : ℕ → ι → ℕ → Ξ)
    (trace :
      S.GeneratedTrace (S.theorem811Parameters N Dtilde hSchedule)
        (S.theorem811Parameters_valid N Dtilde hSchedule) init samples)
    (xStar : Stacked ι E) (hxStar : S.PrimalOptimalSolution xStar) :
    let P := S.theorem811Parameters N Dtilde hSchedule
    let hP := S.theorem811Parameters_valid N Dtilde hSchedule
    S.generalSDCSRawTerminalPotential P hP init samples trace xStar N ≤
      3 * S.networkOperatorNorm * S.stackedProx init.x0 xStar := by
  classical
  let P := S.theorem811Parameters N Dtilde hSchedule
  let hP := S.theorem811Parameters_valid N Dtilde hSchedule
  have hTpos : 0 < P.innerSteps 1 := by
    simpa [P] using
      S.theorem811_innerSteps_positive_of_schedule_wellDefined
        N Dtilde hSchedule hN 1 (by omega) hN
  have hcoeff_nonneg :
      0 ≤ generalSDCSRawPrimalTerminalCoeff P 1 := by
    have hLpos : 0 < S.networkOperatorNorm := hSchedule.2
    dsimp [generalSDCSRawPrimalTerminalCoeff, P, theorem811Parameters]
    positivity
  have hxN : S.FeasiblePoint (S.generatedX P hP init samples trace N) := by
    simpa [generatedX, generatedState] using
      (S.generatedState P hP init samples trace N).xPrev_mem
  have hproxN_nonneg :
      0 ≤ S.stackedProx (S.generatedX P hP init samples trace N) xStar := by
    exact le_trans
      (mul_nonneg (by norm_num) (S.stackedNormSq_nonneg _))
      (S.stackedProx_lower_bound
        (S.generatedX P hP init samples trace N) xStar hxN hxStar.1)
  have hcoeff_le :=
    S.theorem811_initial_prox_coefficient_le N hN Dtilde hSchedule
  have hcoeff_bound :
      generalSDCSRawPrimalTerminalCoeff P 1 ≤ 3 * S.networkOperatorNorm := by
    rw [← generalSDCSRawPrimalInitialCoeff_eq_terminalCoeff_of_innerSteps_pos P hTpos]
    calc
      generalSDCSRawPrimalInitialCoeff P 1 =
          ((((P.innerSteps 1 : ℝ) + 1) * ((P.innerSteps 1 : ℝ) + 2) *
            P.theta 1 * P.eta 1) /
            ((P.innerSteps 1 : ℝ) * ((P.innerSteps 1 : ℝ) + 3))) := by
        have hTne : (P.innerSteps 1 : ℝ) ≠ 0 := by
          exact_mod_cast (ne_of_gt hTpos)
        have hT3ne : (P.innerSteps 1 : ℝ) + 3 ≠ 0 := by positivity
        unfold generalSDCSRawPrimalInitialCoeff generalSDCSRawPrimalTelescopeInitialCoeff
        change
          2 * S.networkOperatorNorm +
              2 * (2 * S.networkOperatorNorm) /
                ((P.innerSteps 1 : ℝ) * ((P.innerSteps 1 : ℝ) + 3)) = _
        field_simp [hTne, hT3ne]
        simp [P, theorem811Parameters]
        ring
      _ ≤ 3 * S.networkOperatorNorm := hcoeff_le
  let A : ℕ → ℝ := fun k =>
    S.stackedProx (S.generatedX P hP init samples trace k) xStar
  have htel :
      (∑ k ∈ Finset.range N, (A k - A (k + 1))) ≤ A 0 :=
    sum_range_sub_succ_le_first_of_last_nonneg A N (by simpa [A] using hproxN_nonneg)
  have hA0 : A 0 = S.stackedProx init.x0 xStar := by
    dsimp [A]
    simp [P, hP, generatedX, generatedState, initialOuterState, trace.initial_state]
  have hA0_nonneg : 0 ≤ A 0 := by
    rw [hA0]
    exact le_trans
      (mul_nonneg (by norm_num) (S.stackedNormSq_nonneg _))
      (S.stackedProx_lower_bound init.x0 xStar init.x0_mem hxStar.1)
  calc
    S.generalSDCSRawTerminalPotential P hP init samples trace xStar N =
        generalSDCSRawPrimalTerminalCoeff P 1 *
          (∑ k ∈ Finset.range N, (A k - A (k + 1))) := by
      dsimp [generalSDCSRawTerminalPotential, A]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro k hk
      dsimp [P, theorem811Parameters, generalSDCSRawPrimalTerminalCoeff]
      ring
    _ ≤ generalSDCSRawPrimalTerminalCoeff P 1 * A 0 :=
      mul_le_mul_of_nonneg_left htel hcoeff_nonneg
    _ ≤ (3 * S.networkOperatorNorm) * A 0 :=
      mul_le_mul_of_nonneg_right hcoeff_bound hA0_nonneg
    _ = 3 * S.networkOperatorNorm * S.stackedProx init.x0 xStar := by rw [hA0]

private theorem theorem811_rawOracleErrorBudget_integrable_integral_le
    (init : InitialState S) (run : OracleRun S Ω)
    (N : ℕ) (hN : 1 ≤ N) (Dtilde : ℝ)
    (hSchedule : S.Theorem811ScheduleWellDefined N Dtilde)
    (core :
      S.GeneratedProcessCore (S.theorem811Parameters N Dtilde hSchedule)
        (S.theorem811Parameters_valid N Dtilde hSchedule) init run)
    (hQueryIndependent :
      S.GeneratedQueryIndependent (S.theorem811Parameters N Dtilde hSchedule)
        (S.theorem811Parameters_valid N Dtilde hSchedule) init run core.trace)
    (xStar : Stacked ι E)
    (hLinear :
      S.theorem811GeneratedLinearErrorIntegrable
        init run N Dtilde hSchedule core xStar) :
    let P := S.theorem811Parameters N Dtilde hSchedule
    let hP := S.theorem811Parameters_valid N Dtilde hSchedule
    Integrable
        (fun ω =>
          S.generalSDCSRawOracleErrorBudget P hP init
            (run.samples ω) (core.trace ω) xStar N)
        run.law ∧
      (∫ ω,
        S.generalSDCSRawOracleErrorBudget P hP init
          (run.samples ω) (core.trace ω) xStar N ∂run.law) ≤
        S.networkOperatorNorm * (4 * Dtilde) := by
  classical
  letI : IsProbabilityMeasure run.law := run.law_isProbability
  let P := S.theorem811Parameters N Dtilde hSchedule
  let hP := S.theorem811Parameters_valid N Dtilde hSchedule
  let trace := core.trace
  let term : ℕ → ℕ → ι → Ω → ℝ := fun k t i ω =>
    let kk := k + 1
    let T := P.innerSteps kk
    let uPrev := S.generatedInnerQuery P hP init (run.samples ω) (trace ω) i kk t
    let δ := S.oracleError i uPrev (run.samples ω kk i t)
    (2 * P.theta kk / ((T : ℝ) * ((T : ℝ) + 3))) *
      (-(csLambda (t + 1) * inner ℝ δ (xStar i - uPrev)) +
        csLambda (t + 1) *
          ((S.M + ‖δ‖) ^ 2 / (2 * (P.eta kk * csBeta (t + 1)))))
  have hQueryCore : S.GeneratedQueryIndependentCore P hP init run trace := by
    simpa [P, hP, trace, GeneratedQueryIndependent] using hQueryIndependent
  have hTerm :
      ∀ k ∈ Finset.range N, ∀ t ∈ Finset.range (P.innerSteps (k + 1)), ∀ i,
        Integrable (term k t i) run.law ∧
          (∫ ω, term k t i ω ∂run.law) ≤
            (2 * P.theta (k + 1) /
                (((P.innerSteps (k + 1) : ℝ)) *
                  ((P.innerSteps (k + 1) : ℝ) + 3))) *
              (4 * (S.M ^ 2 + S.sigma ^ 2) / P.eta (k + 1)) := by
    intro k hk t ht i
    let kk := k + 1
    let T := P.innerSteps kk
    let innerTerm : Ω → ℝ := fun ω =>
      inner ℝ
        (S.oracleError i
          (S.generatedInnerQuery P hP init (run.samples ω) (trace ω) i kk t)
          (run.samples ω kk i t))
        (xStar i -
          S.generatedInnerQuery P hP init (run.samples ω) (trace ω) i kk t)
    let noiseSq : Ω → ℝ := fun ω =>
      ‖S.oracleError i
        (S.generatedInnerQuery P hP init (run.samples ω) (trace ω) i kk t)
        (run.samples ω kk i t)‖ ^ 2
    let shiftedSq : Ω → ℝ := fun ω =>
      (S.M + ‖S.oracleError i
        (S.generatedInnerQuery P hP init (run.samples ω) (trace ω) i kk t)
        (run.samples ω kk i t)‖) ^ 2
    let q : ℝ := 2 * P.theta kk / ((T : ℝ) * ((T : ℝ) + 3))
    have hkkN : kk ≤ N := by
      dsimp [kk]
      have hklt := Finset.mem_range.mp hk
      omega
    have hTpos : 0 < T := by
      dsimp [T]
      exact
        (S.theorem811_general_parameter_denominators_pos
          N hN Dtilde hSchedule kk (by simp [kk]) hkkN).1
    have hEtaPos : 0 < P.eta kk :=
      (S.theorem811_general_parameter_denominators_pos
        N hN Dtilde hSchedule kk (by simp [kk]) hkkN).2
    have hq_nonneg : 0 ≤ q := by
      dsimp [q, T, kk, P, theorem811Parameters]
      positivity
    have hInnerInt : Integrable innerTerm run.law := by
      simpa [theorem811GeneratedLinearErrorIntegrable, P, hP, trace,
        kk, innerTerm] using hLinear i k hk t (by simpa [T, kk] using ht)
    have hInnerZero : ∫ ω, innerTerm ω ∂run.law = 0 := by
      dsimp [innerTerm]
      exact
        S.generated_query_cancellation P hP init run trace hQueryIndependent
          i kk t xStar
    have hNoiseSqInt : Integrable noiseSq run.law := by
      simpa [noiseSq] using
        S.generated_oracle_error_sq_integrable
          P hP init run trace hQueryCore i kk t
    have hNoiseSqBound : ∫ ω, noiseSq ω ∂run.law ≤ S.sigma ^ 2 := by
      simpa [noiseSq] using
        S.generated_oracle_error_sq_integral_le
          P hP init run trace hQueryIndependent i kk t
    have hShiftedInt : Integrable shiftedSq run.law := by
      exact
        (integrable_sq_add_nonneg_of_integrable_sq_bound
          (Z := fun ω =>
            ‖S.oracleError i
              (S.generatedInnerQuery P hP init (run.samples ω) (trace ω) i kk t)
              (run.samples ω kk i t)‖)
          (M := S.M) (sigma := S.sigma)
          (by simpa [noiseSq] using hNoiseSqInt)
          (Filter.Eventually.of_forall (fun ω => norm_nonneg _))
          (by simpa [noiseSq] using hNoiseSqBound)).1
    let loose : Ω → ℝ := fun ω =>
      q * (-(csLambda (t + 1) * innerTerm ω) +
        4 * (S.M ^ 2 + noiseSq ω) / P.eta kk)
    have hTermInt : Integrable (term k t i) run.law := by
      have hSecond :
          Integrable
            (fun ω =>
              csLambda (t + 1) *
                (shiftedSq ω / (2 * (P.eta kk * csBeta (t + 1)))))
            run.law :=
        by
          simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
            (hShiftedInt.const_mul (1 / (2 * (P.eta kk * csBeta (t + 1)))))
              |>.const_mul (csLambda (t + 1))
      have hFirst :
          Integrable (fun ω => -(csLambda (t + 1) * innerTerm ω)) run.law :=
        (hInnerInt.const_mul (csLambda (t + 1))).neg
      simpa [term, kk, T, q, innerTerm, shiftedSq, div_eq_mul_inv,
        mul_assoc] using (hFirst.add hSecond).const_mul q
    have hLooseInt : Integrable loose run.law := by
      have hFirst :
          Integrable (fun ω => -(csLambda (t + 1) * innerTerm ω)) run.law :=
        (hInnerInt.const_mul (csLambda (t + 1))).neg
      have hSecond :
          Integrable (fun ω => 4 * (S.M ^ 2 + noiseSq ω) / P.eta kk) run.law :=
        by
          simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
            (((integrable_const (c := S.M ^ 2)).add hNoiseSqInt).const_mul 4).const_mul
              (1 / P.eta kk)
      simpa [loose, div_eq_mul_inv, mul_assoc] using
        (hFirst.add hSecond).const_mul q
    have hPoint : ∀ ω, term k t i ω ≤ loose ω := by
      intro ω
      have hsquare :=
        cs_weighted_oracle_square_budget_pointwise_le t hEtaPos
          (le_of_lt S.M_pos)
          (norm_nonneg
            (S.oracleError i
              (S.generatedInnerQuery P hP init (run.samples ω) (trace ω) i kk t)
              (run.samples ω kk i t)))
      dsimp [term, loose, innerTerm, noiseSq, shiftedSq, q, T, kk]
      exact mul_le_mul_of_nonneg_left (add_le_add (le_refl _) hsquare) hq_nonneg
    have hMono :
        (∫ ω, term k t i ω ∂run.law) ≤ ∫ ω, loose ω ∂run.law :=
      integral_mono hTermInt hLooseInt hPoint
    have hLooseIntegral :
        (∫ ω, loose ω ∂run.law) =
          q * (4 * (S.M ^ 2 + ∫ ω, noiseSq ω ∂run.law) / P.eta kk) := by
      dsimp [loose]
      rw [integral_const_mul]
      have hFirstInt :
          Integrable (fun ω => -(csLambda (t + 1) * innerTerm ω)) run.law :=
        (hInnerInt.const_mul (csLambda (t + 1))).neg
      have hSecondInt :
          Integrable (fun ω => 4 * (S.M ^ 2 + noiseSq ω) / P.eta kk) run.law := by
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
          (((integrable_const (c := S.M ^ 2)).add hNoiseSqInt).const_mul 4).const_mul
            (1 / P.eta kk)
      rw [integral_add hFirstInt hSecondInt]
      rw [integral_neg, integral_const_mul, hInnerZero]
      rw [integral_div, integral_const_mul]
      rw [integral_add (integrable_const (c := S.M ^ 2)) hNoiseSqInt]
      simp
    refine ⟨hTermInt, hMono.trans ?_⟩
    rw [hLooseIntegral]
    have hinside :
        4 * (S.M ^ 2 + ∫ ω, noiseSq ω ∂run.law) / P.eta kk ≤
          4 * (S.M ^ 2 + S.sigma ^ 2) / P.eta kk := by
      exact div_le_div_of_nonneg_right (by nlinarith) (le_of_lt hEtaPos)
    simpa [q, T, kk] using mul_le_mul_of_nonneg_left hinside hq_nonneg
  have hBudgetInt :
      Integrable
        (fun ω =>
          S.generalSDCSRawOracleErrorBudget P hP init
            (run.samples ω) (trace ω) xStar N)
        run.law := by
    simpa [generalSDCSRawOracleErrorBudget, term] using
      MeasureTheory.integrable_finset_sum (s := Finset.range N) (fun k hk =>
        MeasureTheory.integrable_finset_sum (s := Finset.range (P.innerSteps (k + 1)))
          (fun t ht =>
            MeasureTheory.integrable_finset_sum (s := (Finset.univ : Finset ι))
              (fun i _hi => (hTerm k hk t ht i).1)))
  refine ⟨hBudgetInt, ?_⟩
  have hOuterInt :
      ∀ k ∈ Finset.range N,
        Integrable
          (fun ω =>
            ∑ t ∈ Finset.range (P.innerSteps (k + 1)), ∑ i, term k t i ω)
          run.law := by
    intro k hk
    exact MeasureTheory.integrable_finset_sum (s := Finset.range (P.innerSteps (k + 1)))
      (fun t ht => MeasureTheory.integrable_finset_sum (s := (Finset.univ : Finset ι))
        (fun i _hi => (hTerm k hk t ht i).1))
  have hIntegralExpand :
      (∫ ω,
        S.generalSDCSRawOracleErrorBudget P hP init
          (run.samples ω) (trace ω) xStar N ∂run.law) =
        ∑ k ∈ Finset.range N,
          ∑ t ∈ Finset.range (P.innerSteps (k + 1)),
            ∑ i, ∫ ω, term k t i ω ∂run.law := by
    simp_rw [generalSDCSRawOracleErrorBudget, term]
    rw [MeasureTheory.integral_finset_sum (s := Finset.range N) hOuterInt]
    refine Finset.sum_congr rfl ?_
    intro k hk
    rw [MeasureTheory.integral_finset_sum
      (s := Finset.range (P.innerSteps (k + 1))) (fun t ht =>
        MeasureTheory.integrable_finset_sum (s := (Finset.univ : Finset ι))
          (fun i _hi => (hTerm k hk t ht i).1))]
    refine Finset.sum_congr rfl ?_
    intro t ht
    rw [MeasureTheory.integral_finset_sum (s := (Finset.univ : Finset ι))
      (fun i _hi => (hTerm k hk t ht i).1)]
  rw [hIntegralExpand]
  have hTermSum :
      (∑ k ∈ Finset.range N,
        ∑ t ∈ Finset.range (P.innerSteps (k + 1)),
          ∑ i, ∫ ω, term k t i ω ∂run.law) ≤
        ∑ k ∈ Finset.range N,
          ∑ t ∈ Finset.range (P.innerSteps (k + 1)),
            ∑ _i : ι,
              (2 * P.theta (k + 1) /
                  (((P.innerSteps (k + 1) : ℝ)) *
                    ((P.innerSteps (k + 1) : ℝ) + 3))) *
                (4 * (S.M ^ 2 + S.sigma ^ 2) / P.eta (k + 1)) := by
    refine Finset.sum_le_sum ?_
    intro k hk
    refine Finset.sum_le_sum ?_
    intro t ht
    exact Finset.sum_le_sum (fun i _hi => (hTerm k hk t ht i).2)
  calc
    (∑ k ∈ Finset.range N,
      ∑ t ∈ Finset.range (P.innerSteps (k + 1)),
        ∑ i, ∫ ω, term k t i ω ∂run.law) ≤
        ∑ k ∈ Finset.range N,
          ∑ t ∈ Finset.range (P.innerSteps (k + 1)),
            ∑ _i : ι,
              (2 * P.theta (k + 1) /
                  (((P.innerSteps (k + 1) : ℝ)) *
                    ((P.innerSteps (k + 1) : ℝ) + 3))) *
                (4 * (S.M ^ 2 + S.sigma ^ 2) / P.eta (k + 1)) := hTermSum
    _ = ∑ k ∈ Finset.range N,
          (8 * (Fintype.card ι : ℝ) * (S.M ^ 2 + S.sigma ^ 2) /
            ((((S.theorem811Parameters N Dtilde hSchedule).innerSteps (k + 1) : ℝ) + 3) *
              (2 * S.networkOperatorNorm))) := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      have hTpos : 0 < P.innerSteps (k + 1) :=
        (S.theorem811_general_parameter_denominators_pos
          N hN Dtilde hSchedule (k + 1) (by omega)
          (Nat.succ_le_of_lt (Finset.mem_range.mp hk))).1
      have hTne : (P.innerSteps (k + 1) : ℝ) ≠ 0 := by
        exact_mod_cast (ne_of_gt hTpos)
      have hLne : S.networkOperatorNorm ≠ 0 := ne_of_gt hSchedule.2
      simp only [Finset.sum_const, Finset.card_univ, Finset.card_range, nsmul_eq_mul]
      dsimp [P, theorem811Parameters] at hTne ⊢
      field_simp [hTne, hLne]
      ring
    _ ≤ ∑ _k ∈ Finset.range N,
          (S.networkOperatorNorm / (N : ℝ)) * (4 * Dtilde) := by
      exact Finset.sum_le_sum (fun k _hk =>
        S.theorem811_variance_budget_scalar_le N hN Dtilde hSchedule (k + 1))
    _ = S.networkOperatorNorm * (4 * Dtilde) := by
      have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hN))
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp [hNne]

private theorem integrable_of_measurable_nonneg_le_integrable
    {f g : Ω → ℝ} {μ : Measure Ω}
    (hf : Measurable f) (hfnn : ∀ ω, 0 ≤ f ω)
    (hg : Integrable g μ) (hfg : ∀ ω, f ω ≤ g ω) :
    Integrable f μ := by
  refine Integrable.mono' hg hf.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ω => ?_))
  have hgnn : 0 ≤ g ω := (hfnn ω).trans (hfg ω)
  simpa [Real.norm_eq_abs, abs_of_nonneg (hfnn ω), abs_of_nonneg hgnn] using hfg ω

private theorem integrable_of_measurable_between_integrable
    {f lower upper : Ω → ℝ} {μ : Measure Ω}
    (hf : Measurable f) (hlower : Integrable lower μ) (hupper : Integrable upper μ)
    (hlf : ∀ ω, lower ω ≤ f ω) (hfu : ∀ ω, f ω ≤ upper ω) :
    Integrable f μ := by
  exact integrable_of_le_of_le hf.aestronglyMeasurable
    (Filter.Eventually.of_forall hlf) (Filter.Eventually.of_forall hfu) hlower hupper

/-- The complete source expectation aggregation under the exact finite-window
product-integrability condition omitted by the printed "take expectations"
step.  This is private infrastructure: it changes neither `Setup` nor either
paper-facing endpoint. -/
private theorem theorem811_expected_budget_bridge_of_generatedLinearErrorIntegrable
    (init : InitialState S) (run : OracleRun S Ω)
    (N : ℕ) (hN : 1 ≤ N) (Dtilde : ℝ)
    (hSchedule : S.Theorem811ScheduleWellDefined N Dtilde)
    (core :
      S.GeneratedProcessCore (S.theorem811Parameters N Dtilde hSchedule)
        (S.theorem811Parameters_valid N Dtilde hSchedule) init run)
    (hQueryIndependent :
      S.GeneratedQueryIndependent (S.theorem811Parameters N Dtilde hSchedule)
        (S.theorem811Parameters_valid N Dtilde hSchedule) init run core.trace)
    (xStar yStar : Stacked ι E)
    (hxStar : S.PrimalOptimalSolution xStar) (hyStar : S.DualOptimalSolution xStar yStar)
    (hLinear :
      S.theorem811GeneratedLinearErrorIntegrable
        init run N Dtilde hSchedule core xStar) :
    S.Theorem811ExpectedBudgetBridge init run N hN Dtilde hSchedule core xStar yStar := by
  classical
  letI : IsProbabilityMeasure run.law := run.law_isProbability
  let P := S.theorem811Parameters N Dtilde hSchedule
  let hP := S.theorem811Parameters_valid N Dtilde hSchedule
  let trace := core.trace
  have hGeneral : S.generalParameterConditions P N :=
    S.theorem811_schedule_satisfies_general_conditions_sourceBoundaryCorrected
      N hN Dtilde hSchedule
  have hDenom :
      ∀ k, 1 ≤ k → k ≤ N → 0 < P.innerSteps k ∧ 0 < P.eta k := by
    simpa [P] using
      S.theorem811_general_parameter_denominators_pos N hN Dtilde hSchedule
  have hTheta_nonneg :
      ∀ k, 1 ≤ k → k ≤ N → 0 ≤ P.theta k := by
    simpa [P] using S.theorem811_theta_nonneg N Dtilde hSchedule
  have hTheta_sum_pos :
      0 < ∑ k ∈ Finset.range N, P.theta (k + 1) := by
    simpa [P] using S.theorem811_theta_sum_pos N hN Dtilde hSchedule
  have hThetaN_ge_one : 1 ≤ P.theta N := by
    simpa [P] using S.theorem811_theta_ge_one N Dtilde hSchedule N hN le_rfl
  have hLemma85 :
      ∀ ω,
        S.GeneralSDCSGapLemma85RawTerminalBridge P hP init (run.samples ω) (trace ω) N :=
    fun ω =>
      S.generalSDCSGapLemma85_rawTerminal_bridge_sourceBoundaryCorrected
        P hP init (run.samples ω) (trace ω) N hN hGeneral hDenom
        hTheta_nonneg hTheta_sum_pos
  have hAvg :
      ∀ ω,
        S.weightedPrimalAverage P hP init (run.samples ω) (trace ω) N =
          S.theorem811PrimalAverage P hP init (run.samples ω) (trace ω) N :=
    fun ω => by
      simpa [P, hP] using
        S.theorem811_weightedPrimalAverage_eq_theorem811PrimalAverage
          init N Dtilde hSchedule (run.samples ω) (trace ω)
  let oracleBudget : Ω → ℝ := fun ω =>
    S.generalSDCSRawOracleErrorBudget P hP init (run.samples ω) (trace ω) xStar N
  have hOracle :=
    S.theorem811_rawOracleErrorBudget_integrable_integral_le
      init run N hN Dtilde hSchedule core hQueryIndependent xStar hLinear
  have hOracleInt : Integrable oracleBudget run.law := by
    simpa [P, hP, trace, oracleBudget] using hOracle.1
  have hOracleBound :
      ∫ ω, oracleBudget ω ∂run.law ≤ S.networkOperatorNorm * (4 * Dtilde) := by
    simpa [P, hP, trace, oracleBudget] using hOracle.2
  have hPotential :
      ∀ ω,
        S.generalSDCSRawTerminalPotential P hP init (run.samples ω) (trace ω) xStar N ≤
          3 * S.networkOperatorNorm * S.stackedProx init.x0 xStar := by
    intro ω
    simpa [P, hP] using
      S.theorem811_rawTerminalPotential_le_initial
        init N hN Dtilde hSchedule (run.samples ω) (trace ω) xStar hxStar
  have hAvgMem :
      ∀ ω, S.FeasiblePoint
        (S.theorem811PrimalAverage P hP init (run.samples ω) (trace ω) N) := by
    intro ω
    exact theorem811PrimalAverage_mem S P hP init (run.samples ω) (trace ω)
      hN hDenom
  have hAvgCoordMeas :
      ∀ i, Measurable
        (fun ω =>
          S.theorem811PrimalAverage P hP init (run.samples ω) (trace ω) N i) := by
    intro i
    dsimp [theorem811PrimalAverage]
    simpa [Pi.smul_apply] using
      (Finset.measurable_sum (Finset.range N)
        (fun k _hk => core.generatedXHat_measurable (k + 1) i)).const_smul ((N : ℝ)⁻¹)
  have hObjectiveMeas :
      Measurable
        (fun ω =>
          S.objectiveResidual
            (S.theorem811PrimalAverage P hP init (run.samples ω) (trace ω) N) xStar) := by
    dsimp [objectiveResidual, objective]
    apply Measurable.sub
    · refine Finset.measurable_sum (Finset.univ : Finset ι) ?_
      intro i _hi
      have hi :=
        measurable_sub_const_of_continuousOn_comp_measurable_mem
          (X := S.feasible i) (f := S.localObjective i)
          (y := fun ω =>
            S.theorem811PrimalAverage P hP init (run.samples ω) (trace ω) N i)
          (c := (0 : ℝ))
          (S.localObjective_continuousOn_feasible_of_objectiveGrowth i)
          (hAvgCoordMeas i) (fun ω => hAvgMem ω i)
      simpa using hi
    · exact measurable_const
  have hGapFinite :
      ∀ ω,
        S.PerturbedGapFinite
          (S.theorem811PrimalAverage P hP init (run.samples ω) (trace ω) N)
          (S.weightedDualAverage P hP init (run.samples ω) (trace ω) N)
          xStar (S.scaledPerturbation P hP init (run.samples ω) (trace ω) N) := by
    intro ω
    simpa [hAvg ω] using (hLemma85 ω).perturbed_gap_finite xStar hxStar
  have hProp86 : ∀ ω,
      S.PerturbedGapToResidualsProposition86Bridge
        (S.theorem811PrimalAverage P hP init (run.samples ω) (trace ω) N)
        (S.weightedDualAverage P hP init (run.samples ω) (trace ω) N)
        xStar (S.scaledPerturbation P hP init (run.samples ω) (trace ω) N) :=
    fun ω => S.perturbedGap_fullSpace_to_residuals_sourceBoundaryCorrected
      _ _ _ _ hxStar (hGapFinite ω)
  let gap : Ω → ℝ := fun ω =>
    S.perturbedGap
      (S.theorem811PrimalAverage P hP init (run.samples ω) (trace ω) N)
      (S.weightedDualAverage P hP init (run.samples ω) (trace ω) N)
      xStar (S.scaledPerturbation P hP init (run.samples ω) (trace ω) N)
  have hGapMeas : Measurable gap := by
    have heq : gap = fun ω =>
        S.objectiveResidual
          (S.theorem811PrimalAverage P hP init (run.samples ω) (trace ω) N) xStar := by
      funext ω
      exact (hProp86 ω).perturbedGap_eq_objectiveResidual
    rw [heq]
    exact hObjectiveMeas
  let gapUpper : Ω → ℝ := fun ω =>
    (1 / (N : ℝ)) *
      (3 * S.networkOperatorNorm * S.stackedProx init.x0 xStar +
        (S.networkOperatorNorm / 2) * S.stackedNormSq init.y0 + oracleBudget ω)
  have hGapUpperInt : Integrable gapUpper run.law := by
    exact (((integrable_const
      (c := 3 * S.networkOperatorNorm * S.stackedProx init.x0 xStar +
        (S.networkOperatorNorm / 2) * S.stackedNormSq init.y0)).add hOracleInt).const_mul
          (1 / (N : ℝ)))
  have hGapLe : ∀ ω, gap ω ≤ gapUpper ω := by
    intro ω
    have hp := (hLemma85 ω).perturbed_gap_bound xStar hxStar
    rw [hAvg ω] at hp
    have hsum : (∑ k ∈ Finset.range N, P.theta (k + 1))⁻¹ = 1 / (N : ℝ) := by
      simp [P, theorem811Parameters]
    rw [hsum] at hp
    dsimp [gap, gapUpper, generalSDCSGapLemma85RawPerturbedGapRHS] at hp ⊢
    have hNinv : 0 ≤ 1 / (N : ℝ) := by positivity
    calc
      gap ω ≤ (1 / (N : ℝ)) *
          (S.generalSDCSRawTerminalPotential P hP init (run.samples ω) (trace ω)
              xStar N +
            (P.theta 1 * P.tau 1 / 2) * S.stackedNormSq init.y0 +
            oracleBudget ω) := by simpa [oracleBudget] using hp
      _ ≤ (1 / (N : ℝ)) *
          (3 * S.networkOperatorNorm * S.stackedProx init.x0 xStar +
            (P.theta 1 * P.tau 1 / 2) * S.stackedNormSq init.y0 +
            oracleBudget ω) := by
        gcongr
        exact hPotential ω
      _ = gapUpper ω := by
        dsimp [gapUpper]
        simp [P, theorem811Parameters]
  let residual : Ω → ℝ := fun ω =>
    S.generalSDCSGapLemma85ResidualLHS P hP init (run.samples ω) (trace ω)
      xStar yStar N
  have hResidualMeas : Measurable residual := by
    dsimp [residual, generalSDCSGapLemma85ResidualLHS, stackedNormSq]
    apply Measurable.const_mul
    apply Measurable.max
    · apply Measurable.const_mul
      refine Finset.measurable_sum (Finset.univ : Finset ι) ?_
      intro i _hi
      exact ((core.generatedXHat_measurable N i).sub
        (core.generatedX_measurable (N - 1) i)).norm.pow_const 2
    · apply Measurable.const_mul
      refine Finset.measurable_sum (Finset.univ : Finset ι) ?_
      intro i _hi
      exact (measurable_const.sub (core.generatedY_measurable N i)).norm.pow_const 2
  have hResidualNonneg : ∀ ω, 0 ≤ residual ω := by
    intro ω
    dsimp [residual, generalSDCSGapLemma85ResidualLHS, P, theorem811Parameters]
    have hLne : S.networkOperatorNorm ≠ 0 := ne_of_gt hSchedule.2
    have hc :
        (1 / 2 : ℝ) *
            (1 - S.networkOperatorNorm ^ 2 /
              (2 * S.networkOperatorNorm * S.networkOperatorNorm)) = 1 / 4 := by
      field_simp [hLne]
      ring
    simp only [one_mul]
    rw [hc]
    apply mul_nonneg (by norm_num)
    exact (mul_nonneg
      (mul_nonneg (by norm_num) (le_of_lt hSchedule.2))
      (S.stackedNormSq_nonneg _)).trans
      (le_max_left _ _)
  let residualUpper : Ω → ℝ := fun ω =>
    3 * S.networkOperatorNorm * S.stackedProx init.x0 xStar +
      (S.networkOperatorNorm / 2) * S.stackedNormSq (yStar - init.y0) +
        oracleBudget ω
  have hResidualUpperInt : Integrable residualUpper run.law :=
    (integrable_const
      (c := 3 * S.networkOperatorNorm * S.stackedProx init.x0 xStar +
        (S.networkOperatorNorm / 2) * S.stackedNormSq (yStar - init.y0))).add hOracleInt
  have hResidualLe : ∀ ω, residual ω ≤ residualUpper ω := by
    intro ω
    have hr := (hLemma85 ω).residual_bound xStar yStar hxStar hyStar hThetaN_ge_one
    calc
      residual ω ≤
          S.generalSDCSRawTerminalPotential P hP init (run.samples ω) (trace ω)
              xStar N +
            (P.theta 1 * P.tau 1 / 2) * S.stackedNormSq (yStar - init.y0) +
            oracleBudget ω := by simpa [residual, oracleBudget] using hr
      _ ≤ 3 * S.networkOperatorNorm * S.stackedProx init.x0 xStar +
            (P.theta 1 * P.tau 1 / 2) * S.stackedNormSq (yStar - init.y0) +
            oracleBudget ω := by
        gcongr
        exact hPotential ω
      _ = residualUpper ω := by
        dsimp [residualUpper]
        simp [P, theorem811Parameters]
  have hResidualInt : Integrable residual run.law :=
    integrable_of_measurable_nonneg_le_integrable
      hResidualMeas hResidualNonneg hResidualUpperInt hResidualLe
  have hResidualBudget :
      (∫ ω, residual ω ∂run.law) ≤
        S.theorem811ExpectedResidualLHSBudget init Dtilde xStar yStar := by
    calc
      (∫ ω, residual ω ∂run.law) ≤ ∫ ω, residualUpper ω ∂run.law :=
        integral_le_of_forall_le_of_integrable
          hResidualInt hResidualUpperInt hResidualLe
      _ = 3 * S.networkOperatorNorm * S.stackedProx init.x0 xStar +
          (S.networkOperatorNorm / 2) * S.stackedNormSq (yStar - init.y0) +
            ∫ ω, oracleBudget ω ∂run.law := by
        dsimp [residualUpper]
        rw [integral_add (integrable_const
          (c := 3 * S.networkOperatorNorm * S.stackedProx init.x0 xStar +
            (S.networkOperatorNorm / 2) * S.stackedNormSq (yStar - init.y0))) hOracleInt]
        simp
      _ ≤ 3 * S.networkOperatorNorm * S.stackedProx init.x0 xStar +
          (S.networkOperatorNorm / 2) * S.stackedNormSq (yStar - init.y0) +
            S.networkOperatorNorm * (4 * Dtilde) := by gcongr
      _ = S.theorem811ExpectedResidualLHSBudget init Dtilde xStar yStar := by
        dsimp [theorem811ExpectedResidualLHSBudget]
        ring
  let dxSq : Ω → ℝ := fun ω =>
    S.stackedNormSq
      (S.generatedXHat P hP init (run.samples ω) (trace ω) N -
        S.generatedX P hP init (run.samples ω) (trace ω) (N - 1))
  let vSq : Ω → ℝ := fun ω =>
    S.stackedNormSq (yStar - S.generatedY P hP init (run.samples ω) (trace ω) N)
  have hDxSqMeas : Measurable dxSq := by
    dsimp [dxSq, stackedNormSq]
    refine Finset.measurable_sum (Finset.univ : Finset ι) ?_
    intro i _hi
    exact ((core.generatedXHat_measurable N i).sub
      (core.generatedX_measurable (N - 1) i)).norm.pow_const 2
  have hVSqMeas : Measurable vSq := by
    dsimp [vSq, stackedNormSq]
    refine Finset.measurable_sum (Finset.univ : Finset ι) ?_
    intro i _hi
    exact (measurable_const.sub (core.generatedY_measurable N i)).norm.pow_const 2
  have hBranch : ∀ ω,
      2 * S.networkOperatorNorm * dxSq ω ≤ 4 * residual ω ∧
        S.networkOperatorNorm * vSq ω ≤ 4 * residual ω := by
    intro ω
    have hLne : S.networkOperatorNorm ≠ 0 := ne_of_gt hSchedule.2
    have heq : residual ω =
        (1 / 4 : ℝ) * max
          (2 * S.networkOperatorNorm * dxSq ω)
          (S.networkOperatorNorm * vSq ω) := by
      dsimp [residual, dxSq, vSq, generalSDCSGapLemma85ResidualLHS,
        P, theorem811Parameters]
      have hc :
          (1 / 2 : ℝ) *
              (1 - S.networkOperatorNorm ^ 2 /
                (2 * S.networkOperatorNorm * S.networkOperatorNorm)) = 1 / 4 := by
        field_simp [hLne]
        ring
      simp only [one_mul]
      rw [hc]
    rw [heq]
    constructor
    · nlinarith [le_max_left
        (2 * S.networkOperatorNorm * dxSq ω) (S.networkOperatorNorm * vSq ω)]
    · nlinarith [le_max_right
        (2 * S.networkOperatorNorm * dxSq ω) (S.networkOperatorNorm * vSq ω)]
  have hDxLe : ∀ ω, dxSq ω ≤ (2 / S.networkOperatorNorm) * residual ω := by
    intro ω
    have h := (hBranch ω).1
    have hLpos := hSchedule.2
    have hden : 0 < 2 * S.networkOperatorNorm := by positivity
    calc
      dxSq ω = (2 * S.networkOperatorNorm * dxSq ω) / (2 * S.networkOperatorNorm) := by
        field_simp [ne_of_gt hden]
      _ ≤ (4 * residual ω) / (2 * S.networkOperatorNorm) :=
        div_le_div_of_nonneg_right h (le_of_lt hden)
      _ = (2 / S.networkOperatorNorm) * residual ω := by
        field_simp [ne_of_gt hLpos]
        ring
  have hVLe : ∀ ω, vSq ω ≤ (4 / S.networkOperatorNorm) * residual ω := by
    intro ω
    have h := (hBranch ω).2
    have hLpos := hSchedule.2
    calc
      vSq ω = (S.networkOperatorNorm * vSq ω) / S.networkOperatorNorm := by
        field_simp [ne_of_gt hLpos]
      _ ≤ (4 * residual ω) / S.networkOperatorNorm :=
        div_le_div_of_nonneg_right h (le_of_lt hLpos)
      _ = (4 / S.networkOperatorNorm) * residual ω := by ring
  have hDxSqInt : Integrable dxSq run.law :=
    integrable_of_measurable_nonneg_le_integrable hDxSqMeas
      (fun ω => S.stackedNormSq_nonneg _)
      (hResidualInt.const_mul (2 / S.networkOperatorNorm)) hDxLe
  have hVSqInt : Integrable vSq run.law :=
    integrable_of_measurable_nonneg_le_integrable hVSqMeas
      (fun ω => S.stackedNormSq_nonneg _)
      (hResidualInt.const_mul (4 / S.networkOperatorNorm)) hVLe
  let dxNorm : Ω → ℝ := fun ω =>
    (fun x => ‖WithLp.toLp 2 x‖)
      (S.generatedXHat P hP init (run.samples ω) (trace ω) N -
        S.generatedX P hP init (run.samples ω) (trace ω) (N - 1))
  let vNorm : Ω → ℝ := fun ω =>
    (fun x => ‖WithLp.toLp 2 x‖) (yStar - S.generatedY P hP init (run.samples ω) (trace ω) N)
  have hDxNormMeas : Measurable dxNorm := by
    simpa [dxNorm, PiLp.norm_eq_of_L2,
      dxSq, stackedNormSq] using hDxSqMeas.sqrt
  have hVNormMeas : Measurable vNorm := by
    simpa [vNorm, PiLp.norm_eq_of_L2,
      vSq, stackedNormSq] using hVSqMeas.sqrt
  have hDxNormSqInt : Integrable (fun ω => dxNorm ω ^ 2) run.law := by
    refine hDxSqInt.congr (Filter.Eventually.of_forall (fun ω => ?_))
    symm
    exact stackedNorm_sq_eq S _
  have hVNormSqInt : Integrable (fun ω => vNorm ω ^ 2) run.law := by
    refine hVSqInt.congr (Filter.Eventually.of_forall (fun ω => ?_))
    symm
    exact stackedNorm_sq_eq S _
  have hDxNormInt : Integrable dxNorm run.law :=
    integrable_of_integrable_norm_sq hDxNormMeas.aestronglyMeasurable (by
      simpa [Real.norm_of_nonneg (S.stackedNorm_nonneg _)] using hDxNormSqInt)
  have hVNormInt : Integrable vNorm run.law :=
    integrable_of_integrable_norm_sq hVNormMeas.aestronglyMeasurable (by
      simpa [Real.norm_of_nonneg (S.stackedNorm_nonneg _)] using hVNormSqInt)
  let scaledRhs : Ω → ℝ := fun ω =>
    (S.networkOperatorNorm / (N : ℝ)) *
      (dxNorm ω + vNorm ω + (fun x => ‖WithLp.toLp 2 x‖) (yStar - init.y0))
  have hScaledRhsInt : Integrable scaledRhs run.law := by
    exact ((hDxNormInt.add hVNormInt).add
      (integrable_const (c := (fun x => ‖WithLp.toLp 2 x‖) (yStar - init.y0)))).const_mul
        (S.networkOperatorNorm / (N : ℝ))
  have hScaledNormLe : ∀ ω,
      (fun x => ‖WithLp.toLp 2 x‖)
        (S.scaledPerturbation P hP init (run.samples ω) (trace ω) N) ≤
        scaledRhs ω := by
    intro ω
    simpa [P, hP, trace, scaledRhs, dxNorm, vNorm] using
      S.theorem811_scaledPerturbation_norm_le
        init N hN Dtilde hSchedule (run.samples ω) (trace ω) yStar
  let gapLower : Ω → ℝ := fun ω => -(scaledRhs ω * (fun x => ‖WithLp.toLp 2 x‖) yStar)
  have hGapLowerInt : Integrable gapLower run.law := by
    simpa [gapLower, mul_comm] using
      (hScaledRhsInt.const_mul ((fun x => ‖WithLp.toLp 2 x‖) yStar)).neg
  have hGapLower : ∀ ω, gapLower ω ≤ gap ω := by
    intro ω
    let xbar := S.theorem811PrimalAverage P hP init (run.samples ω) (trace ω) N
    let ybar := S.weightedDualAverage P hP init (run.samples ω) (trace ω) N
    let sbar := S.scaledPerturbation P hP init (run.samples ω) (trace ω) N
    have hsaddle : 0 ≤ S.primalDualGap xbar ybar xStar yStar :=
      (hyStar.2 xbar ybar (hAvgMem ω)).2
    have hgapform :
        S.primalDualGap xbar ybar xStar yStar =
          S.objectiveResidual xbar xStar + stackedInner (S.networkOperator xbar) yStar :=
      primalDualGap_to_objectiveResidual_add_network_pairing S xbar ybar xStar yStar hxStar
    have hs : sbar = S.networkOperator xbar := (hProp86 ω).scaled_eq_network
    have hobj : gap ω = S.objectiveResidual xbar xStar := by
      simpa [gap, xbar, ybar, sbar] using (hProp86 ω).perturbedGap_eq_objectiveResidual
    have hpair : stackedInner sbar yStar ≤ (fun x => ‖WithLp.toLp 2 x‖) sbar * (fun x => ‖WithLp.toLp 2 x‖) yStar :=
      stackedInner_le_stackedNorm_mul S sbar yStar
    have hnormmul :
        (fun x => ‖WithLp.toLp 2 x‖) sbar * (fun x => ‖WithLp.toLp 2 x‖) yStar ≤
          scaledRhs ω * (fun x => ‖WithLp.toLp 2 x‖) yStar :=
      mul_le_mul_of_nonneg_right (hScaledNormLe ω) (S.stackedNorm_nonneg _)
    dsimp [gapLower]
    rw [hobj]
    rw [hgapform, ← hs] at hsaddle
    linarith
  have hGapInt : Integrable gap run.law :=
    integrable_of_measurable_between_integrable
      hGapMeas hGapLowerInt hGapUpperInt hGapLower hGapLe
  have hGapBudget :
      (∫ ω, gap ω ∂run.law) ≤
        S.theorem811ExpectedPerturbedGapBudget init N Dtilde xStar := by
    calc
      (∫ ω, gap ω ∂run.law) ≤ ∫ ω, gapUpper ω ∂run.law :=
        integral_le_of_forall_le_of_integrable hGapInt hGapUpperInt hGapLe
      _ = (1 / (N : ℝ)) *
          (3 * S.networkOperatorNorm * S.stackedProx init.x0 xStar +
            (S.networkOperatorNorm / 2) * S.stackedNormSq init.y0 +
              ∫ ω, oracleBudget ω ∂run.law) := by
        dsimp [gapUpper]
        rw [integral_const_mul]
        rw [integral_add (integrable_const
          (c := 3 * S.networkOperatorNorm * S.stackedProx init.x0 xStar +
            (S.networkOperatorNorm / 2) * S.stackedNormSq init.y0)) hOracleInt]
        simp
      _ ≤ (1 / (N : ℝ)) *
          (3 * S.networkOperatorNorm * S.stackedProx init.x0 xStar +
            (S.networkOperatorNorm / 2) * S.stackedNormSq init.y0 +
              S.networkOperatorNorm * (4 * Dtilde)) := by
        gcongr
      _ = S.theorem811ExpectedPerturbedGapBudget init N Dtilde xStar := by
        dsimp [theorem811ExpectedPerturbedGapBudget]
        ring
  refine
    { perturbed_gap_bound := ?_
      residualLHS_integrable := ?_
      residual_lhs_bound := ?_ }
  · simpa [P, hP, trace, gap] using hGapBudget
  · simpa [P, hP, trace, residual] using hResidualInt
  · simpa [P, hP, trace, residual] using hResidualBudget

/-- Source/coarser supplier for the paired Theorem 8.11 expectation budgets.

The proof is deliberately staged at the printed formula boundary.  It
consumes corrected Lemma 8.5, generated-query cancellation, oracle second
moments, the initial coefficient estimate, and the schedule variance estimate
directly.  The generated-direction moment needed for the formula-level
expectation aggregation is derived by a finite-horizon induction over the
unchanged Algorithm 8.8 updates; no tombstoned forward-Bregman/window helper is
used. -/
theorem theorem811_expected_budget_bridge_sourceBoundaryCorrected
    (init : InitialState S) (run : OracleRun S Ω)
    (N : ℕ) (hN : 1 ≤ N) (Dtilde : ℝ)
    (hSchedule : S.Theorem811ScheduleWellDefined N Dtilde)
    (core :
      S.GeneratedProcessCore (S.theorem811Parameters N Dtilde hSchedule)
        (S.theorem811Parameters_valid N Dtilde hSchedule) init run)
    (hQueryIndependent :
      S.GeneratedQueryIndependent (S.theorem811Parameters N Dtilde hSchedule)
        (S.theorem811Parameters_valid N Dtilde hSchedule) init run core.trace)
    (xStar yStar : Stacked ι E)
    (hxStar : S.PrimalOptimalSolution xStar) (hyStar : S.DualOptimalSolution xStar yStar) :
    S.Theorem811ExpectedBudgetBridge init run N hN Dtilde hSchedule core xStar yStar := by
  have hLinear :
      S.theorem811GeneratedLinearErrorIntegrable
        init run N Dtilde hSchedule core xStar := by
    classical
    let P := S.theorem811Parameters N Dtilde hSchedule
    let hP := S.theorem811Parameters_valid N Dtilde hSchedule
    have hQueryCore :
        S.GeneratedQueryIndependentCore P hP init run core.trace := by
      simpa [P, hP, GeneratedQueryIndependent] using hQueryIndependent
    dsimp [theorem811GeneratedLinearErrorIntegrable]
    intro i k hk t ht
    refine
      S.generated_oracle_error_inner_integrable_of_direction_l2
        P hP init run core.trace hQueryCore i (k + 1) t xStar ?_
    exact
      S.theorem811_generated_inner_query_direction_sq_integrable
        init run N Dtilde hSchedule core hQueryCore xStar hxStar i (k + 1) t
  exact
    S.theorem811_expected_budget_bridge_of_generatedLinearErrorIntegrable
      init run N hN Dtilde hSchedule core hQueryIndependent
      xStar yStar hxStar hyStar hLinear

/-- Expectation bridge for Theorem 8.11's objective route.

For the actual average of generated xhat_k, the direct finite-horizon moment
derivation makes every oracle-error pairing integrable.  Fresh-query
cancellation, the variance bound, the valid square estimate, and the
coefficient-weighted terminal Bregman formula then prove the stated expected
perturbed-gap budget.
-/

theorem theorem811_expected_gap_stage_actual_average_sourceBoundaryCorrected
    (init : InitialState S) (run : OracleRun S Ω)
    (N : ℕ) (hN : 1 ≤ N) (Dtilde : ℝ)
    (hSchedule : S.Theorem811ScheduleWellDefined N Dtilde)
    (core :
      S.GeneratedProcessCore (S.theorem811Parameters N Dtilde hSchedule)
        (S.theorem811Parameters_valid N Dtilde hSchedule) init run)
    (hQueryIndependent :
      S.GeneratedQueryIndependent (S.theorem811Parameters N Dtilde hSchedule)
        (S.theorem811Parameters_valid N Dtilde hSchedule) init run core.trace)
    (xStar yStar : Stacked ι E)
    (hxStar : S.PrimalOptimalSolution xStar) (hyStar : S.DualOptimalSolution xStar yStar) :
    let P := S.theorem811Parameters N Dtilde hSchedule
    let hP := S.theorem811Parameters_valid N Dtilde hSchedule
    ∫ ω,
      S.perturbedGap
        (S.theorem811PrimalAverage P hP init (run.samples ω) (core.trace ω) N)
        (S.weightedDualAverage P hP init (run.samples ω) (core.trace ω) N)
        xStar
        (S.scaledPerturbation P hP init (run.samples ω) (core.trace ω) N) ∂run.law ≤
      S.theorem811ExpectedPerturbedGapBudget init N Dtilde xStar := by
  exact
    (S.theorem811_expected_budget_bridge_sourceBoundaryCorrected
      init run N hN Dtilde hSchedule core hQueryIndependent
      xStar yStar hxStar hyStar).perturbed_gap_bound


/-- Expected residual second-moment stage for the consensus proof.

The completed direct finite-horizon bridge integrates the Lemma 8.5 residual
inequality and proves the source-sized squared-moment budget.  These squared
moments are the quantities required by Jensen in the next stage.
-/

theorem theorem811_expected_residual_second_moment_stage_sourceBoundaryCorrected
    (init : InitialState S) (run : OracleRun S Ω)
    (N : ℕ) (hN : 1 ≤ N) (Dtilde : ℝ)
    (hSchedule : S.Theorem811ScheduleWellDefined N Dtilde)
    (core :
      S.GeneratedProcessCore (S.theorem811Parameters N Dtilde hSchedule)
        (S.theorem811Parameters_valid N Dtilde hSchedule) init run)
    (hQueryIndependent :
      S.GeneratedQueryIndependent (S.theorem811Parameters N Dtilde hSchedule)
        (S.theorem811Parameters_valid N Dtilde hSchedule) init run core.trace)
    (xStar yStar : Stacked ι E)
    (hxStar : S.PrimalOptimalSolution xStar) (hyStar : S.DualOptimalSolution xStar yStar) :
    let P := S.theorem811Parameters N Dtilde hSchedule
    let hP := S.theorem811Parameters_valid N Dtilde hSchedule
    ∫ ω,
      S.generalSDCSGapLemma85ResidualLHS P hP init (run.samples ω) (core.trace ω)
        xStar yStar N ∂run.law ≤
      S.theorem811ExpectedResidualLHSBudget init Dtilde xStar yStar := by
  exact
    (S.theorem811_expected_budget_bridge_sourceBoundaryCorrected
      init run N hN Dtilde hSchedule core hQueryIndependent
      xStar yStar hxStar hyStar).residual_lhs_bound


/-- The Theorem 8.11 schedule exposes the residual side of Lemma 8.5 as the
quarter-scaled maximum of the primal and dual terminal second-moment branches.

This is the source-derived algebra behind the Jensen step in the consensus
bound: `theta_N = 1`, `eta_N = 2‖L‖`, and `tau_N = ‖L‖`, so the Lemma 8.5
coefficient becomes `1 / 4`.
-/
private theorem theorem811_residualLHS_eq_quarter_max
    (init : InitialState S) (N : ℕ) (Dtilde : ℝ)
    (hSchedule : S.Theorem811ScheduleWellDefined N Dtilde)
    (samples : ℕ → ι → ℕ → Ξ)
    (trace :
      S.GeneratedTrace (S.theorem811Parameters N Dtilde hSchedule)
        (S.theorem811Parameters_valid N Dtilde hSchedule) init samples)
    (xStar yStar : Stacked ι E) :
    let P := S.theorem811Parameters N Dtilde hSchedule
    let hP := S.theorem811Parameters_valid N Dtilde hSchedule
    S.generalSDCSGapLemma85ResidualLHS P hP init samples trace xStar yStar N =
      (1 / 4 : ℝ) *
        max
          (2 * S.networkOperatorNorm *
            S.stackedNormSq
              (S.generatedXHat P hP init samples trace N -
                S.generatedX P hP init samples trace (N - 1)))
          (S.networkOperatorNorm *
            S.stackedNormSq (yStar - S.generatedY P hP init samples trace N)) := by
  classical
  let P := S.theorem811Parameters N Dtilde hSchedule
  let hP := S.theorem811Parameters_valid N Dtilde hSchedule
  have hL_ne : S.networkOperatorNorm ≠ 0 := ne_of_gt hSchedule.2
  have hCoeff :
      ((1 : ℝ) / 2) *
          (1 - 1 * S.networkOperatorNorm ^ 2 /
            ((2 * S.networkOperatorNorm) * S.networkOperatorNorm)) =
        (1 / 4 : ℝ) := by
    field_simp [hL_ne]
    ring
  dsimp [P, hP, generalSDCSGapLemma85ResidualLHS, theorem811Parameters]
  rw [hCoeff]

/-- Pointwise branch extraction from the Theorem 8.11 residual LHS.

After the schedule specialization, each terminal second-moment branch is bounded
by four times the Lemma 8.5 residual left side.  This is the pointwise ingredient
for integrating the primal and dual second-moment estimates.
-/
private theorem theorem811_residualLHS_branch_bounds
    (init : InitialState S) (N : ℕ) (Dtilde : ℝ)
    (hSchedule : S.Theorem811ScheduleWellDefined N Dtilde)
    (samples : ℕ → ι → ℕ → Ξ)
    (trace :
      S.GeneratedTrace (S.theorem811Parameters N Dtilde hSchedule)
        (S.theorem811Parameters_valid N Dtilde hSchedule) init samples)
    (xStar yStar : Stacked ι E) :
    let P := S.theorem811Parameters N Dtilde hSchedule
    let hP := S.theorem811Parameters_valid N Dtilde hSchedule
    (2 * S.networkOperatorNorm *
        S.stackedNormSq
          (S.generatedXHat P hP init samples trace N -
            S.generatedX P hP init samples trace (N - 1)) ≤
      4 * S.generalSDCSGapLemma85ResidualLHS P hP init samples trace xStar yStar N) ∧
    (S.networkOperatorNorm *
        S.stackedNormSq (yStar - S.generatedY P hP init samples trace N) ≤
      4 * S.generalSDCSGapLemma85ResidualLHS P hP init samples trace xStar yStar N) := by
  classical
  let P := S.theorem811Parameters N Dtilde hSchedule
  let hP := S.theorem811Parameters_valid N Dtilde hSchedule
  let A : ℝ :=
    2 * S.networkOperatorNorm *
      S.stackedNormSq
        (S.generatedXHat P hP init samples trace N -
          S.generatedX P hP init samples trace (N - 1))
  let B : ℝ :=
    S.networkOperatorNorm *
      S.stackedNormSq (yStar - S.generatedY P hP init samples trace N)
  have hEq :
      S.generalSDCSGapLemma85ResidualLHS P hP init samples trace xStar yStar N =
        (1 / 4 : ℝ) * max A B := by
    simpa [P, hP, A, B] using
      S.theorem811_residualLHS_eq_quarter_max
        init N Dtilde hSchedule samples trace xStar yStar
  have hFour :
      4 * S.generalSDCSGapLemma85ResidualLHS P hP init samples trace xStar yStar N =
        max A B := by
    rw [hEq]
    ring
  constructor
  · calc
      A ≤ max A B := le_max_left A B
      _ = 4 * S.generalSDCSGapLemma85ResidualLHS P hP init samples trace xStar yStar N :=
        hFour.symm
  · calc
      B ≤ max A B := le_max_right A B
      _ = 4 * S.generalSDCSGapLemma85ResidualLHS P hP init samples trace xStar yStar N :=
        hFour.symm

/-- Expected primal and dual terminal second-moment branches extracted from the
corrected residual-moment estimate.

This is the Lean form of the source step "from (8.3.66)" before Jensen: the
residual LHS controls both terminal squared distances after the Theorem 8.11
schedule is substituted.
-/
private theorem theorem811_expected_residual_branch_moment_bounds
    (init : InitialState S) (run : OracleRun S Ω)
    (N : ℕ) (hN : 1 ≤ N) (Dtilde : ℝ)
    (hSchedule : S.Theorem811ScheduleWellDefined N Dtilde)
    (core :
      S.GeneratedProcessCore (S.theorem811Parameters N Dtilde hSchedule)
        (S.theorem811Parameters_valid N Dtilde hSchedule) init run)
    (xStar yStar : Stacked ι E) (R : ℝ)
    (hResidualInt :
      let P := S.theorem811Parameters N Dtilde hSchedule
      let hP := S.theorem811Parameters_valid N Dtilde hSchedule
      Integrable
        (fun ω =>
          S.generalSDCSGapLemma85ResidualLHS P hP init (run.samples ω) (core.trace ω)
            xStar yStar N)
        run.law)
    (hResidualMoment :
      let P := S.theorem811Parameters N Dtilde hSchedule
      let hP := S.theorem811Parameters_valid N Dtilde hSchedule
      ∫ ω,
        S.generalSDCSGapLemma85ResidualLHS P hP init (run.samples ω) (core.trace ω)
          xStar yStar N ∂run.law ≤
        R) :
    let P := S.theorem811Parameters N Dtilde hSchedule
    let hP := S.theorem811Parameters_valid N Dtilde hSchedule
    (Integrable
        (fun ω =>
          S.stackedNormSq
            (S.generatedXHat P hP init (run.samples ω) (core.trace ω) N -
              S.generatedX P hP init (run.samples ω) (core.trace ω) (N - 1)))
        run.law ∧
      ∫ ω,
        S.stackedNormSq
          (S.generatedXHat P hP init (run.samples ω) (core.trace ω) N -
            S.generatedX P hP init (run.samples ω) (core.trace ω) (N - 1)) ∂run.law ≤
        2 * R / S.networkOperatorNorm) ∧
    (Integrable
        (fun ω =>
          S.stackedNormSq (yStar - S.generatedY P hP init (run.samples ω) (core.trace ω) N))
        run.law ∧
      ∫ ω,
        S.stackedNormSq (yStar - S.generatedY P hP init (run.samples ω) (core.trace ω) N)
          ∂run.law ≤
        4 * R / S.networkOperatorNorm) := by
  classical
  letI : IsProbabilityMeasure run.law := run.law_isProbability
  let P := S.theorem811Parameters N Dtilde hSchedule
  let hP := S.theorem811Parameters_valid N Dtilde hSchedule
  let residual : Ω → ℝ := fun ω =>
    S.generalSDCSGapLemma85ResidualLHS P hP init (run.samples ω) (core.trace ω)
      xStar yStar N
  let dxSq : Ω → ℝ := fun ω =>
    S.stackedNormSq
      (S.generatedXHat P hP init (run.samples ω) (core.trace ω) N -
        S.generatedX P hP init (run.samples ω) (core.trace ω) (N - 1))
  let vSq : Ω → ℝ := fun ω =>
    S.stackedNormSq (yStar - S.generatedY P hP init (run.samples ω) (core.trace ω) N)
  have hResidualInt' : Integrable residual run.law := by
    simpa [P, hP, residual] using hResidualInt
  have hResidualMoment' :
      ∫ ω, residual ω ∂run.law ≤ R := by
    simpa [P, hP, residual] using hResidualMoment
  have hL_pos : 0 < S.networkOperatorNorm := hSchedule.2
  have hdx_meas : Measurable dxSq := by
    dsimp [dxSq, stackedNormSq]
    refine Finset.measurable_sum (Finset.univ : Finset ι) ?_
    intro i _hi
    have hxhat :
        Measurable
          (fun ω =>
            S.generatedXHat P hP init (run.samples ω) (core.trace ω) N i) := by
      simpa [P, hP] using core.generatedXHat_measurable N i
    have hx :
        Measurable
          (fun ω =>
            S.generatedX P hP init (run.samples ω) (core.trace ω) (N - 1) i) := by
      simpa [P, hP] using core.generatedX_measurable (N - 1) i
    exact ((hxhat.sub hx).norm.pow_const 2)
  have hv_meas : Measurable vSq := by
    dsimp [vSq, stackedNormSq]
    refine Finset.measurable_sum (Finset.univ : Finset ι) ?_
    intro i _hi
    have hy :
        Measurable
          (fun ω =>
            S.generatedY P hP init (run.samples ω) (core.trace ω) N i) := by
      simpa [P, hP] using core.generatedY_measurable N i
    exact ((measurable_const.sub hy).norm.pow_const 2)
  have hBranch :
      ∀ ω,
        (2 * S.networkOperatorNorm * dxSq ω ≤ 4 * residual ω) ∧
        (S.networkOperatorNorm * vSq ω ≤ 4 * residual ω) := by
    intro ω
    simpa [P, hP, residual, dxSq, vSq] using
      S.theorem811_residualLHS_branch_bounds
        init N Dtilde hSchedule (run.samples ω) (core.trace ω) xStar yStar
  have hdx_nonneg : ∀ ω, 0 ≤ dxSq ω := by
    intro ω
    exact S.stackedNormSq_nonneg _
  have hv_nonneg : ∀ ω, 0 ≤ vSq ω := by
    intro ω
    exact S.stackedNormSq_nonneg _
  have hdx_le : ∀ ω, dxSq ω ≤ (2 / S.networkOperatorNorm) * residual ω := by
    intro ω
    have h := (hBranch ω).1
    have hden : 0 < 2 * S.networkOperatorNorm := by positivity
    calc
      dxSq ω = (2 * S.networkOperatorNorm * dxSq ω) / (2 * S.networkOperatorNorm) := by
        field_simp [hden.ne']
      _ ≤ (4 * residual ω) / (2 * S.networkOperatorNorm) :=
        div_le_div_of_nonneg_right h (le_of_lt hden)
      _ = (2 / S.networkOperatorNorm) * residual ω := by
        field_simp [hL_pos.ne']
        ring
  have hv_le : ∀ ω, vSq ω ≤ (4 / S.networkOperatorNorm) * residual ω := by
    intro ω
    have h := (hBranch ω).2
    calc
      vSq ω = (S.networkOperatorNorm * vSq ω) / S.networkOperatorNorm := by
        field_simp [hL_pos.ne']
      _ ≤ (4 * residual ω) / S.networkOperatorNorm :=
        div_le_div_of_nonneg_right h (le_of_lt hL_pos)
      _ = (4 / S.networkOperatorNorm) * residual ω := by
        ring
  simpa only [P, hP, dxSq, vSq, div_eq_mul_inv, mul_assoc, mul_left_comm,
    mul_comm] using
    (two_nonnegative_integrable_integral_le_of_scaled_residual_bounds
      run.law residual dxSq vSq (2 / S.networkOperatorNorm)
      (4 / S.networkOperatorNorm) R hdx_meas.aestronglyMeasurable
      hv_meas.aestronglyMeasurable hResidualInt'
      (Filter.Eventually.of_forall hdx_nonneg)
      (Filter.Eventually.of_forall hv_nonneg) (by positivity) (by positivity)
      (Filter.Eventually.of_forall hdx_le) (Filter.Eventually.of_forall hv_le)
      hResidualMoment')

/-- The Jensen/triangle part of the consensus estimate, parameterized by the
already aggregated residual budget.  Nonnegativity of the norm lets us use
`integral_mono_of_nonneg`; no independent integrability assumption for the
scaled perturbation is needed. -/
private theorem theorem811_expected_scaledPerturbation_norm_le_of_residual_budget
    (init : InitialState S) (run : OracleRun S Ω)
    (N : ℕ) (hN : 1 ≤ N) (Dtilde : ℝ)
    (hSchedule : S.Theorem811ScheduleWellDefined N Dtilde)
    (core :
      S.GeneratedProcessCore (S.theorem811Parameters N Dtilde hSchedule)
        (S.theorem811Parameters_valid N Dtilde hSchedule) init run)
    (xStar yStar : Stacked ι E) (R : ℝ)
    (hResidualInt :
      let P := S.theorem811Parameters N Dtilde hSchedule
      let hP := S.theorem811Parameters_valid N Dtilde hSchedule
      Integrable
        (fun ω =>
          S.generalSDCSGapLemma85ResidualLHS P hP init (run.samples ω) (core.trace ω)
            xStar yStar N)
        run.law)
    (hResidualMoment :
      let P := S.theorem811Parameters N Dtilde hSchedule
      let hP := S.theorem811Parameters_valid N Dtilde hSchedule
      ∫ ω,
        S.generalSDCSGapLemma85ResidualLHS P hP init (run.samples ω) (core.trace ω)
          xStar yStar N ∂run.law ≤ R) :
    let P := S.theorem811Parameters N Dtilde hSchedule
    let hP := S.theorem811Parameters_valid N Dtilde hSchedule
    (∫ ω,
      (fun x => ‖WithLp.toLp 2 x‖) (S.scaledPerturbation P hP init (run.samples ω) (core.trace ω) N)
        ∂run.law) ≤
      (S.networkOperatorNorm / (N : ℝ)) *
        (Real.sqrt (2 * R / S.networkOperatorNorm) +
          Real.sqrt (4 * R / S.networkOperatorNorm) +
          (fun x => ‖WithLp.toLp 2 x‖) (yStar - init.y0)) := by
  classical
  letI : IsProbabilityMeasure run.law := run.law_isProbability
  let P := S.theorem811Parameters N Dtilde hSchedule
  let hP := S.theorem811Parameters_valid N Dtilde hSchedule
  let target : Ω → ℝ := fun ω =>
    (fun x => ‖WithLp.toLp 2 x‖)
      (S.scaledPerturbation P hP init (run.samples ω) (core.trace ω) N)
  let first : Ω → ℝ := fun ω =>
    (fun x => ‖WithLp.toLp 2 x‖)
      (S.generatedXHat P hP init (run.samples ω) (core.trace ω) N -
        S.generatedX P hP init (run.samples ω) (core.trace ω) (N - 1))
  let second : Ω → ℝ := fun ω =>
    (fun x => ‖WithLp.toLp 2 x‖)
      (yStar - S.generatedY P hP init (run.samples ω) (core.trace ω) N)
  let offset : ℝ := (fun x => ‖WithLp.toLp 2 x‖) (yStar - init.y0)
  have hBranchMoments :=
    S.theorem811_expected_residual_branch_moment_bounds
      init run N hN Dtilde hSchedule core xStar yStar R hResidualInt hResidualMoment
  exact
    integral_nonnegative_le_scale_mul_sqrt_second_moments_add_const
      run.law target first second (S.networkOperatorNorm / (N : ℝ)) offset
      (2 * R / S.networkOperatorNorm) (4 * R / S.networkOperatorNorm)
      (by
        refine hBranchMoments.1.1.congr
          (Filter.Eventually.of_forall (fun ω => ?_))
        change
          S.stackedNormSq
              (S.generatedXHat P hP init (run.samples ω) (core.trace ω) N -
                S.generatedX P hP init (run.samples ω) (core.trace ω) (N - 1)) =
            first ω ^ 2
        simp only [first, stackedNorm_sq_eq S])
      (by
        refine hBranchMoments.2.1.congr
          (Filter.Eventually.of_forall (fun ω => ?_))
        change
          S.stackedNormSq
              (yStar - S.generatedY P hP init (run.samples ω) (core.trace ω) N) =
            second ω ^ 2
        simp only [second, stackedNorm_sq_eq S])
      (Filter.Eventually.of_forall (fun ω => by
        exact S.stackedNorm_nonneg
          (S.scaledPerturbation P hP init (run.samples ω) (core.trace ω) N)))
      (Filter.Eventually.of_forall (fun ω => by
        exact S.stackedNorm_nonneg
          (S.generatedXHat P hP init (run.samples ω) (core.trace ω) N -
            S.generatedX P hP init (run.samples ω) (core.trace ω) (N - 1))))
      (Filter.Eventually.of_forall (fun ω => by
        exact S.stackedNorm_nonneg
          (yStar - S.generatedY P hP init (run.samples ω) (core.trace ω) N)))
      (by
        have hN_pos_real : 0 < (N : ℝ) := by
          exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hN)
        exact div_nonneg (le_of_lt hSchedule.2) (le_of_lt hN_pos_real))
      (by simpa only [first, stackedNorm_sq_eq S] using hBranchMoments.1.2)
      (by simpa only [second, stackedNorm_sq_eq S] using hBranchMoments.2.2)
      (Filter.Eventually.of_forall (fun ω => by
        simpa only [target, first, second, offset, P, hP] using
          S.theorem811_scaledPerturbation_norm_le
            init N hN Dtilde hSchedule (run.samples ω) (core.trace ω) yStar))

/-- Raw-terminal consensus-residual expression for Theorem 8.11.

It is the direct Jensen/triangle expression obtained from the squared residual
moments in Lemma 8.5.  The completed expectation bridge controls its exact
Young-square budget with the valid source square estimate and oracle moments.
-/

def theorem811ConsensusResidualRawTerminalBound
    (init : InitialState S) (run : OracleRun S Ω)
    (N : ℕ) (hN : 1 ≤ N) (Dtilde : ℝ)
    (hSchedule : S.Theorem811ScheduleWellDefined N Dtilde)
    (trace : ∀ ω,
      S.GeneratedTrace (S.theorem811Parameters N Dtilde hSchedule)
        (S.theorem811Parameters_valid N Dtilde hSchedule) init (run.samples ω))
    (xStar yStar : Stacked ι E) : ℝ :=
  let R := S.theorem811ExpectedRawResidualRHS init run N hN Dtilde hSchedule trace
    xStar yStar
  (S.networkOperatorNorm / (N : ℝ)) *
    (Real.sqrt (2 * R / S.networkOperatorNorm) +
      Real.sqrt (4 * R / S.networkOperatorNorm) +
      (fun x => ‖WithLp.toLp 2 x‖) (yStar - init.y0))

/-- Corrected raw-terminal objective residual endpoint for Theorem 8.11. -/
theorem theorem811_expected_objective_residual_from_rawTerminalGap_sourceBoundaryCorrected
    (init : InitialState S) (run : OracleRun S Ω)
    (N : ℕ) (hN : 1 ≤ N) (Dtilde : ℝ)
    (hSchedule : S.Theorem811ScheduleWellDefined N Dtilde)
    (core :
      S.GeneratedProcessCore (S.theorem811Parameters N Dtilde hSchedule)
        (S.theorem811Parameters_valid N Dtilde hSchedule) init run)
    (hQueryIndependent :
      S.GeneratedQueryIndependent (S.theorem811Parameters N Dtilde hSchedule)
        (S.theorem811Parameters_valid N Dtilde hSchedule) init run core.trace)
    (xStar yStar : Stacked ι E)
    (hxStar : S.PrimalOptimalSolution xStar) (hyStar : S.DualOptimalSolution xStar yStar) :
    let P := S.theorem811Parameters N Dtilde hSchedule
    S.expectedObjectiveResidual P (S.theorem811Parameters_valid N Dtilde hSchedule) init run
      core.trace xStar N ≤
      S.theorem811ExpectedPerturbedGapBudget init N Dtilde xStar := by
  classical
  let P := S.theorem811Parameters N Dtilde hSchedule
  let hP := S.theorem811Parameters_valid N Dtilde hSchedule
  let trace := core.trace
  have hExpectedPerturbedGap :=
    S.theorem811_expected_gap_stage_actual_average_sourceBoundaryCorrected
      init run N hN Dtilde hSchedule core hQueryIndependent xStar yStar hxStar hyStar
  have hGeneral :
      S.generalParameterConditions P N :=
    S.theorem811_schedule_satisfies_general_conditions_sourceBoundaryCorrected
      N hN Dtilde hSchedule
  have hDenom :
      ∀ k, 1 ≤ k → k ≤ N → 0 < P.innerSteps k ∧ 0 < P.eta k := by
    simpa [P] using
      S.theorem811_general_parameter_denominators_pos N hN Dtilde hSchedule
  have hTheta_nonneg :
      ∀ k, 1 ≤ k → k ≤ N → 0 ≤ P.theta k := by
    simpa [P] using S.theorem811_theta_nonneg N Dtilde hSchedule
  have hTheta_sum_pos :
      0 < ∑ k ∈ Finset.range N, P.theta (k + 1) := by
    simpa [P] using S.theorem811_theta_sum_pos N hN Dtilde hSchedule
  have hObjectiveEq :
      S.expectedObjectiveResidual P hP init run trace xStar N =
        ∫ ω,
          S.perturbedGap
            (S.theorem811PrimalAverage P hP init (run.samples ω) (trace ω) N)
            (S.weightedDualAverage P hP init (run.samples ω) (trace ω) N)
            xStar
            (S.scaledPerturbation P hP init (run.samples ω) (trace ω) N) ∂run.law := by
    dsimp [expectedObjectiveResidual]
    exact MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall (fun ω => by
        have hLemma85 :
            S.GeneralSDCSGapLemma85RawTerminalBridge
              P hP init (run.samples ω) (trace ω) N :=
          S.generalSDCSGapLemma85_rawTerminal_bridge_sourceBoundaryCorrected
            P hP init (run.samples ω) (trace ω) N hN hGeneral hDenom
            hTheta_nonneg hTheta_sum_pos
        have hAvg :=
          S.theorem811_weightedPrimalAverage_eq_theorem811PrimalAverage
            init N Dtilde hSchedule (run.samples ω) (trace ω)
        have hFinite :
            S.PerturbedGapFinite
              (S.theorem811PrimalAverage P hP init (run.samples ω) (trace ω) N)
              (S.weightedDualAverage P hP init (run.samples ω) (trace ω) N)
              xStar
              (S.scaledPerturbation P hP init (run.samples ω) (trace ω) N) := by
          simpa [P, hP, hAvg] using hLemma85.perturbed_gap_finite xStar hxStar
        have hProp86 :=
          S.perturbedGap_fullSpace_to_residuals_sourceBoundaryCorrected
            (S.theorem811PrimalAverage P hP init (run.samples ω) (trace ω) N)
            (S.weightedDualAverage P hP init (run.samples ω) (trace ω) N)
            xStar
            (S.scaledPerturbation P hP init (run.samples ω) (trace ω) N)
            hxStar hFinite
        exact hProp86.perturbedGap_eq_objectiveResidual.symm))
  change S.expectedObjectiveResidual P hP init run trace xStar N ≤
    S.theorem811ExpectedPerturbedGapBudget init N Dtilde xStar
  rw [hObjectiveEq]
  simpa [P, hP, trace] using hExpectedPerturbedGap


/-- Public objective-residual conclusion (8.3.68) for the actual generated average.

The schedule well-definedness boundary is explicit.  The direct finite-horizon
expectation bridge and objective-residual proof are complete, with no endpoint
integrability assumption added.
-/

theorem theorem811_expected_objective_residual_sourceBoundaryCorrected
    (init : InitialState S) (run : OracleRun S Ω)
    (N : ℕ) (hN : 1 ≤ N) (Dtilde : ℝ)
    (hSchedule : S.Theorem811ScheduleWellDefined N Dtilde)
    (core :
      S.GeneratedProcessCore (S.theorem811Parameters N Dtilde hSchedule)
        (S.theorem811Parameters_valid N Dtilde hSchedule) init run)
    (hQueryIndependent :
      S.GeneratedQueryIndependent (S.theorem811Parameters N Dtilde hSchedule)
        (S.theorem811Parameters_valid N Dtilde hSchedule) init run core.trace)
    (xStar yStar : Stacked ι E)
    (hxStar : S.PrimalOptimalSolution xStar) (hyStar : S.DualOptimalSolution xStar yStar) :
    let P := S.theorem811Parameters N Dtilde hSchedule
    S.expectedObjectiveResidual P (S.theorem811Parameters_valid N Dtilde hSchedule) init run
      core.trace xStar N ≤
      (S.networkOperatorNorm / (N : ℝ)) *
        (3 * S.stackedProx init.x0 xStar + (1 / 2 : ℝ) * S.stackedNormSq init.y0 +
          4 * Dtilde) := by
  simpa [theorem811ExpectedPerturbedGapBudget] using
    S.theorem811_expected_objective_residual_from_rawTerminalGap_sourceBoundaryCorrected
      init run N hN Dtilde hSchedule core hQueryIndependent
      xStar yStar hxStar hyStar

/-- Downstream Jensen/triangle step from the source-sized residual expectation
budget to the printed consensus residual.  This is intentionally separate from
`Theorem811ExpectedBudgetBridge`: it is ordinary formula algebra after the new
source route, and has no dependency on the retired expectation-regularity
family. -/
private theorem sqrt_two_budget_sum_le {A d : ℝ} (hA : 0 ≤ A) (hd : 0 ≤ d) :
    Real.sqrt (A + d ^ 2) + Real.sqrt (2 * A + 2 * d ^ 2) + d ≤
      3 * Real.sqrt A + 4 * d := by
  exact sqrt_add_sq_add_sqrt_two_mul_add_sq_le_three_sqrt_add_four_mul hA hd

private theorem theorem811_expected_consensus_residual_of_expected_residual_budget
    (init : InitialState S) (run : OracleRun S Ω)
    (N : ℕ) (hN : 1 ≤ N) (Dtilde : ℝ)
    (hSchedule : S.Theorem811ScheduleWellDefined N Dtilde)
    (core :
      S.GeneratedProcessCore (S.theorem811Parameters N Dtilde hSchedule)
        (S.theorem811Parameters_valid N Dtilde hSchedule) init run)
    (xStar yStar : Stacked ι E) (hxStar : S.PrimalOptimalSolution xStar)
    (hResidualInt :
      let P := S.theorem811Parameters N Dtilde hSchedule
      let hP := S.theorem811Parameters_valid N Dtilde hSchedule
      Integrable
        (fun ω =>
          S.generalSDCSGapLemma85ResidualLHS P hP init (run.samples ω) (core.trace ω)
            xStar yStar N)
        run.law)
    (hResidualMoment :
      let P := S.theorem811Parameters N Dtilde hSchedule
      let hP := S.theorem811Parameters_valid N Dtilde hSchedule
      ∫ ω,
        S.generalSDCSGapLemma85ResidualLHS P hP init (run.samples ω) (core.trace ω)
          xStar yStar N ∂run.law ≤
        S.theorem811ExpectedResidualLHSBudget init Dtilde xStar yStar) :
    let P := S.theorem811Parameters N Dtilde hSchedule
    S.expectedConsensusResidual P (S.theorem811Parameters_valid N Dtilde hSchedule) init run
      core.trace N ≤
      (S.networkOperatorNorm / (N : ℝ)) *
        (3 * Real.sqrt (6 * S.stackedProx init.x0 xStar + 8 * Dtilde) +
          4 * (fun x => ‖WithLp.toLp 2 x‖) (yStar - init.y0)) := by
  classical
  let P := S.theorem811Parameters N Dtilde hSchedule
  let hP := S.theorem811Parameters_valid N Dtilde hSchedule
  let trace := core.trace
  let R := S.theorem811ExpectedResidualLHSBudget init Dtilde xStar yStar
  have hGeneral : S.generalParameterConditions P N :=
    S.theorem811_schedule_satisfies_general_conditions_sourceBoundaryCorrected
      N hN Dtilde hSchedule
  have hDenom :
      ∀ k, 1 ≤ k → k ≤ N → 0 < P.innerSteps k ∧ 0 < P.eta k := by
    simpa [P] using
      S.theorem811_general_parameter_denominators_pos N hN Dtilde hSchedule
  have hTheta_nonneg :
      ∀ k, 1 ≤ k → k ≤ N → 0 ≤ P.theta k := by
    simpa [P] using S.theorem811_theta_nonneg N Dtilde hSchedule
  have hTheta_sum_pos :
      0 < ∑ k ∈ Finset.range N, P.theta (k + 1) := by
    simpa [P] using S.theorem811_theta_sum_pos N hN Dtilde hSchedule
  have hConsensusPathwise : ∀ ω,
      S.consensusResidual
          (S.theorem811PrimalAverage P hP init (run.samples ω) (trace ω) N) =
        (fun x => ‖WithLp.toLp 2 x‖)
          (S.scaledPerturbation P hP init (run.samples ω) (trace ω) N) := by
    intro ω
    have hLemma85 :
        S.GeneralSDCSGapLemma85RawTerminalBridge
          P hP init (run.samples ω) (trace ω) N :=
      S.generalSDCSGapLemma85_rawTerminal_bridge_sourceBoundaryCorrected
        P hP init (run.samples ω) (trace ω) N hN hGeneral hDenom
        hTheta_nonneg hTheta_sum_pos
    have hAvg :=
      S.theorem811_weightedPrimalAverage_eq_theorem811PrimalAverage
        init N Dtilde hSchedule (run.samples ω) (trace ω)
    have hFinite :
        S.PerturbedGapFinite
          (S.theorem811PrimalAverage P hP init (run.samples ω) (trace ω) N)
          (S.weightedDualAverage P hP init (run.samples ω) (trace ω) N)
          xStar
          (S.scaledPerturbation P hP init (run.samples ω) (trace ω) N) := by
      simpa [P, hP, hAvg] using hLemma85.perturbed_gap_finite xStar hxStar
    exact
      (S.perturbedGap_fullSpace_to_residuals_sourceBoundaryCorrected
        (S.theorem811PrimalAverage P hP init (run.samples ω) (trace ω) N)
        (S.weightedDualAverage P hP init (run.samples ω) (trace ω) N)
        xStar
        (S.scaledPerturbation P hP init (run.samples ω) (trace ω) N)
        hxStar hFinite).consensusResidual_eq
  have hConsensusEqScaled :
      S.expectedConsensusResidual P hP init run trace N =
        ∫ ω,
          (fun x => ‖WithLp.toLp 2 x‖)
            (S.scaledPerturbation P hP init (run.samples ω) (trace ω) N) ∂run.law := by
    dsimp [expectedConsensusResidual]
    exact MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall hConsensusPathwise)
  have hScaledBound :=
    S.theorem811_expected_scaledPerturbation_norm_le_of_residual_budget
      init run N hN Dtilde hSchedule core xStar yStar R
      (by simpa [P, hP, trace, R] using hResidualInt)
      (by simpa [P, hP, trace, R] using hResidualMoment)
  have hV : 0 ≤ S.stackedProx init.x0 xStar := by
    have hLower :=
      S.stackedProx_lower_bound init.x0 xStar init.x0_mem hxStar.1
    exact le_trans
      (mul_nonneg (by norm_num) (S.stackedNormSq_nonneg (init.x0 - xStar))) hLower
  have hD : 0 ≤ Dtilde := le_of_lt hSchedule.1
  let A : ℝ := 6 * S.stackedProx init.x0 xStar + 8 * Dtilde
  let d : ℝ := (fun x => ‖WithLp.toLp 2 x‖) (yStar - init.y0)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hd : 0 ≤ d := by exact S.stackedNorm_nonneg _
  have hd_sq :
      ‖WithLp.toLp 2 yStar - WithLp.toLp 2 init.y0‖ ^ 2 =
        S.stackedNormSq (yStar - init.y0) := by
    rw [← WithLp.toLp_sub]
    exact stackedNorm_sq_eq S _
  have hRdx : 2 * R / S.networkOperatorNorm = A + d ^ 2 := by
    dsimp [R, theorem811ExpectedResidualLHSBudget, A, d]
    rw [hd_sq]
    field_simp [ne_of_gt hSchedule.2]
    ring
  have hRy : 4 * R / S.networkOperatorNorm = 2 * A + 2 * d ^ 2 := by
    dsimp [R, theorem811ExpectedResidualLHSBudget, A, d]
    rw [hd_sq]
    field_simp [ne_of_gt hSchedule.2]
    ring
  have hInner :
      Real.sqrt (2 * R / S.networkOperatorNorm) +
          Real.sqrt (4 * R / S.networkOperatorNorm) + d ≤
        3 * Real.sqrt A + 4 * d := by
    rw [hRdx, hRy]
    exact sqrt_two_budget_sum_le hA hd
  have hScale_nonneg : 0 ≤ S.networkOperatorNorm / (N : ℝ) := by
    have hNreal : 0 < (N : ℝ) := by
      exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hN)
    exact div_nonneg (le_of_lt hSchedule.2) (le_of_lt hNreal)
  change S.expectedConsensusResidual P hP init run trace N ≤
    (S.networkOperatorNorm / (N : ℝ)) * (3 * Real.sqrt A + 4 * d)
  rw [hConsensusEqScaled]
  exact le_trans hScaledBound (mul_le_mul_of_nonneg_left hInner hScale_nonneg)

/-- Corrected raw-terminal consensus residual endpoint for Theorem 8.11. -/
theorem theorem811_expected_consensus_residual_from_rawTerminalGap_sourceBoundaryCorrected
    (init : InitialState S) (run : OracleRun S Ω)
    (N : ℕ) (hN : 1 ≤ N) (Dtilde : ℝ)
    (hSchedule : S.Theorem811ScheduleWellDefined N Dtilde)
    (core :
      S.GeneratedProcessCore (S.theorem811Parameters N Dtilde hSchedule)
        (S.theorem811Parameters_valid N Dtilde hSchedule) init run)
    (hQueryIndependent :
      S.GeneratedQueryIndependent (S.theorem811Parameters N Dtilde hSchedule)
        (S.theorem811Parameters_valid N Dtilde hSchedule) init run core.trace)
    (xStar yStar : Stacked ι E)
    (hxStar : S.PrimalOptimalSolution xStar) (hyStar : S.DualOptimalSolution xStar yStar) :
    let P := S.theorem811Parameters N Dtilde hSchedule
    S.expectedConsensusResidual P (S.theorem811Parameters_valid N Dtilde hSchedule) init run
      core.trace N ≤
      (S.networkOperatorNorm / (N : ℝ)) *
        (3 * Real.sqrt (6 * S.stackedProx init.x0 xStar + 8 * Dtilde) +
          4 * (fun x => ‖WithLp.toLp 2 x‖) (yStar - init.y0)) := by
  have hBudgetBridge :=
    S.theorem811_expected_budget_bridge_sourceBoundaryCorrected
      init run N hN Dtilde hSchedule core hQueryIndependent
      xStar yStar hxStar hyStar
  have hResidualMoment :=
    S.theorem811_expected_residual_second_moment_stage_sourceBoundaryCorrected
      init run N hN Dtilde hSchedule core hQueryIndependent
      xStar yStar hxStar hyStar
  exact
    S.theorem811_expected_consensus_residual_of_expected_residual_budget
      init run N hN Dtilde hSchedule core xStar yStar hxStar
      hBudgetBridge.residualLHS_integrable hResidualMoment


/-- Public consensus-residual conclusion (8.3.69) for the same generated average.

The schedule well-definedness boundary is explicit.  The direct finite-horizon
moment bridge, corrected squared Jensen step, and consensus-residual proof are
complete, with no endpoint moment assumption added.
-/

theorem theorem811_expected_consensus_residual_sourceBoundaryCorrected
    (init : InitialState S) (run : OracleRun S Ω)
    (N : ℕ) (hN : 1 ≤ N) (Dtilde : ℝ)
    (hSchedule : S.Theorem811ScheduleWellDefined N Dtilde)
    (core :
      S.GeneratedProcessCore (S.theorem811Parameters N Dtilde hSchedule)
        (S.theorem811Parameters_valid N Dtilde hSchedule) init run)
    (hQueryIndependent :
      S.GeneratedQueryIndependent (S.theorem811Parameters N Dtilde hSchedule)
        (S.theorem811Parameters_valid N Dtilde hSchedule) init run core.trace)
    (xStar yStar : Stacked ι E)
    (hxStar : S.PrimalOptimalSolution xStar) (hyStar : S.DualOptimalSolution xStar yStar) :
    let P := S.theorem811Parameters N Dtilde hSchedule
    S.expectedConsensusResidual P (S.theorem811Parameters_valid N Dtilde hSchedule) init run
      core.trace N ≤
      (S.networkOperatorNorm / (N : ℝ)) *
        (3 * Real.sqrt (6 * S.stackedProx init.x0 xStar + 8 * Dtilde) +
          4 * (fun x => ‖WithLp.toLp 2 x‖) (yStar - init.y0)) := by
  exact
    S.theorem811_expected_consensus_residual_from_rawTerminalGap_sourceBoundaryCorrected
      init run N hN Dtilde hSchedule core hQueryIndependent
      xStar yStar hxStar hyStar

end Setup

end Model

end

end SDCS
