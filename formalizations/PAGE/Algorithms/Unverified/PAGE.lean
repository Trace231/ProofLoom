import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import SOptLib.Glue.Martingale
import SOptLib.Model.BlockSampling
import SOptLib.Model.Iterates
import SOptLib.Model.Objective
import SOptLib.Model.StochasticOracle
import Staging.FiniteAverageSquaredGradientSmoothness
import Staging.PositiveRealParameter
import Staging.infinitePi_prefix_current_map_eq_prod
import Staging.iidMiniBatchSampleLaw_row_reindex_map_eq_pi
import Staging.iidMiniBatchSampleLaw_prefix_row_map_eq_prod
import Staging.ProbabilityScheduleDomain

/-!
Object-layer model for PAGE (ProbAbilistic Gradient Estimator).

The file intentionally names the algorithmic objects from Algorithm 1:
the finite-sum objective/full gradient, the initial and recursive gradient
estimators, the primal update, the generated state process, and the uniform
output iterate.
-/

open scoped BigOperators
open scoped Gradient

namespace Algorithms
namespace Unverified
namespace PAGE

variable {ι E Ω B B' : Type*}
variable [Fintype ι] [Fintype B] [Fintype B']
variable [DecidableEq B] [DecidableEq B']
variable [Nonempty ι] [Nonempty B] [Nonempty B']
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [FiniteDimensional ℝ E]

/-- Source data for PAGE's finite-sum problem over the paper's finite-dimensional
Euclidean domain and random mini-batch draws.

Book citations:
* `book/research/PAGE.json#/setup/problem`: `\min_{x\in\mathbb{R}^d} f(x)`.
* `book/research/PAGE.json#/setup/variable_space`: `f(x) := (1/n)\sum_i f_i(x)`.

The Prop-valued assumptions from the convergence theorem are kept outside this
data record as named predicates/theorems below. The stochastic estimator values
are not fields: they are constructed from the component-gradient oracle and the
sample streams. -/
structure Setup (ι E Ω B B' : Type*) [Fintype ι] [Fintype B] [Fintype B']
    [DecidableEq B] [DecidableEq B']
    [Nonempty ι] [Nonempty B] [Nonempty B']
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E] where
  /-- Component functions `f_i` in the finite-sum objective.

  Book citation: `book/research/PAGE.json#/setup/variable_space`: `f(x) :=
  (1/n)\sum_i f_i(x)`. -/
  componentObjective : ι → E → ℝ
  /-- Initial point `x^0` from Algorithm 1 input.

  Book citation: `book/research/PAGE.json#/assumptions/3`: `initial point
  x^0, stepsize η, minibatch size b, b'<b, probability {p_t}∈(0,1]`. -/
  x0 : E
  /-- Constant stepsize `η` from Algorithm 1 input.

  Book citation: `book/research/PAGE.json#/assumptions/3`: `initial point
  x^0, stepsize η, minibatch size b, b'<b, probability {p_t}∈(0,1]`. -/
  η : ℝ
  /-- Time-dependent PAGE refresh probabilities `p_t`.

  Book citation: `book/research/PAGE.json#/assumptions/3`: `probability
  {p_t}∈(0,1]`. -/
  refreshProbability : ℕ → ℝ
  /-- Refresh-branch minibatch samples `I` in Algorithm 1.

  Book citation: `book/research/PAGE.json#/assumptions/4`: `I denotes random
  minibatch samples with |I|=b`. -/
  refreshSample : ℕ → B → Ω → ι
  /-- Recursive-branch minibatch samples `I'` in Algorithm 1 Line 4.

  Book citation: `book/research/PAGE.json#/assumptions/6`: `g^{t+1}=...+
  (1/b')\sum_{i\in I'}(∇f_i(x^{t+1})-∇f_i(x^t)) with probability 1-p_t`. -/
  recursiveSample : ℕ → B' → Ω → ι
  /-- Bernoulli branch selecting the two cases of Algorithm 1 Line 4.

  Book citation: `book/research/PAGE.json#/assumptions/6`: the two estimator
  cases occur `with probability p_t` and `with probability 1-p_t`. -/
  refreshBranch : ℕ → Ω → Bool
  /-- Lower-boundedness of the finite-sum objective range, making the paper's
  notation `f^* := min_x f(x)` usable through the infimum-valued Lean
  realization.

  Book citation: `book/research/PAGE.json#/definitions/1`: `f^* :=
  \min_{x\in\mathbb{R}^d} f(x)`. The Theorem 1 proof later uses
  `f(x)-f^* >= 0`, recorded in
  `book/research/PAGE.json#/main_theorem/proof/10`. -/
  h_objective_bddBelow :
    BddBelow
      ((fun x : E =>
          SOptLib.finiteUniformAverage
            (fun i : ι => componentObjective i x)) '' (Set.univ : Set E))

/-- Reindexing a finite uniform average along an equivalence preserves the
average. -/
theorem finiteUniformAverage_comp_equiv
    {α β V : Type*} [Fintype α] [Fintype β]
    [AddCommMonoid V] [Module ℝ V] (e : α ≃ β) (g : β → V) :
    SOptLib.finiteUniformAverage (fun a : α => g (e a)) =
      SOptLib.finiteUniformAverage g := by
  rw [SOptLib.finiteUniformAverage_def, SOptLib.finiteUniformAverage_def]
  have hsum :
      Finset.sum Finset.univ (fun a : α => g (e a)) =
        Finset.sum Finset.univ g := by
    refine Finset.sum_bij (fun a _ha => e a) ?_ ?_ ?_ ?_
    · intro a _ha
      simp
    · intro a₁ _ha₁ a₂ _ha₂ h
      exact e.injective h
    · intro b _hb
      refine ⟨e.symm b, ?_, ?_⟩
      · simp
      · simp
    · intro a _ha
      rfl
  have hcard : Fintype.card α = Fintype.card β := Fintype.card_congr e
  rw [hsum, hcard]

namespace Setup

variable (S : Setup ι E Ω B B')

/-- The paper's finite-sum objective `f(x) = (1/n) ∑ᵢ fᵢ(x)`.

Book citation: `book/research/PAGE.json#/setup/variable_space`: `f(x) :=
(1/n)\sum_i f_i(x)`. -/
noncomputable def objective (x : E) : ℝ :=
  SOptLib.finiteUniformAverage (fun i : ι => S.componentObjective i x)

/-- The component gradient selector `∇fᵢ(x)`, derived from the component
objective rather than supplied as an independent oracle.

Book citation: `book/research/PAGE.json#/assumptions/4`: Line 1 uses
`∇f_i(x^0)` inside the minibatch estimator. -/
noncomputable def componentGradient (i : ι) (x : E) : E :=
  ∇ (S.componentObjective i) x

/-- The finite average of component gradients `(1/n) ∑ᵢ ∇fᵢ(x)`.

Book citation: `book/research/PAGE.json#/assumptions/0`: bounded variance is
stated around `∇f_i(x)-∇f(x)`, tying component gradients to the full gradient. -/
noncomputable def componentAverageGradient (x : E) : E :=
  SOptLib.finiteUniformAverage (fun i : ι => S.componentGradient i x)

/-- The paper's full finite-sum gradient `∇f(x)`, attached to the named
finite-sum objective rather than to an independently supplied vector field.

Book citation: `book/research/PAGE.json#/main_theorem/measure`: the theorem
measures `E[||nabla f(xhat_T)||]`. -/
noncomputable def fullGradient (x : E) : E :=
  ∇ S.objective x

/-- The paper's lower reference value `f^* = min_x f(x)`.

Book citation: `book/research/PAGE.json#/definitions/1`: `f^* :=
\min_{x\in\mathbb{R}^d} f(x)`.

The value is constructed as the infimum of the objective range. Attainment is
not setup data: the paper names an optimal value, but does not provide an
optimizer certificate in the source-facing setup. -/
noncomputable def fStar : ℝ :=
  SOptLib.objectiveInfimumValue Set.univ S.objective


/-- The refresh estimator. In the finite-sum theorem regime `b = n`, the
paper's full-refresh branch is the full gradient, not a uniform sample vector
that happens to have the same cardinality.

Book citation: `book/research/PAGE.json#/assumptions/6`: the refresh branch is
`(1/b)\sum_{i∈I}∇f_i(x^{t+1}) with probability p_t`; Theorem 1 additionally
sets `b=n` via `book/research/PAGE.json#/algorithm_spec/parameters/1`. -/
noncomputable def refreshEstimator (t : ℕ) (ω : Ω) (x : E) : E :=
  if Fintype.card B = Fintype.card ι then
    S.fullGradient x
  else
    SOptLib.finiteUniformAverage (fun j : B => S.componentGradient (S.refreshSample t j ω) x)

/-- The initial estimator `g⁰ = (1/b) ∑_{i∈I} ∇fᵢ(x⁰)`.

Book citation: `book/research/PAGE.json#/algorithm_spec/initialization`:
`g^0=(1/b)\sum_{i∈I}∇f_i(x^0)`. -/
noncomputable def initialEstimator (ω : Ω) : E :=
  refreshEstimator S 0 ω S.x0

/-- PAGE's primal update `x⁺ = x - η g`.

Book citation: `book/research/PAGE.json#/algorithm_spec/steps/0`: `x^{t+1}
=x^t-η g^t`. -/
def primalUpdate (x g : E) : E :=
  x - S.η • g

/-- The recursive low-cost PAGE estimator branch.

Book citation: `book/research/PAGE.json#/algorithm_spec/steps/1`: the
recursive branch is `g^t+(1/b')\sum_{i∈I'}(∇f_i(x^{t+1})-∇f_i(x^t))`. -/
noncomputable def recursiveEstimatorUpdate
    (t : ℕ) (ω : Ω) (gPrev xPrev xCurr : E) : E :=
  SOptLib.recursiveGradientDifferenceAverage
    (fun x i => S.componentGradient i x)
    gPrev xPrev xCurr
    (fun j : B' => S.recursiveSample t j ω)

/-- PAGE's two-branch estimator update from Algorithm 1, Line 4.

Book citation: `book/research/PAGE.json#/algorithm_spec/steps/1`: `g^{t+1}`
is the refresh minibatch estimator `with probability p_t` and the recursive
difference estimator `with probability 1-p_t`. -/
noncomputable def estimatorUpdate
    (t : ℕ) (ω : Ω) (gPrev xPrev xCurr : E) : E :=
  if S.refreshBranch t ω then
    refreshEstimator S (t + 1) ω xCurr
  else
    recursiveEstimatorUpdate S t ω gPrev xPrev xCurr

/-- PAGE state at one time: primal iterate and gradient estimator.

Book citation: `book/research/PAGE.json#/algorithm_spec/steps`: Algorithm 1
recursively updates `x^{t+1}` and `g^{t+1}`. -/
structure State where
  x : E
  g : E

/-- Initial PAGE state.

Book citation: `book/research/PAGE.json#/algorithm_spec/initialization`:
Line 1 defines `g^0`, and `book/research/PAGE.json#/assumptions/3` gives the
input `initial point x^0`. -/
noncomputable def initialState (ω : Ω) : State (E := E) :=
  { x := S.x0
    g := initialEstimator S ω }

@[simp]
theorem initialState_x (ω : Ω) :
    (S.initialState ω).x = S.x0 := by
  rfl

@[simp]
theorem initialState_g (ω : Ω) :
    (S.initialState ω).g = initialEstimator S ω := by
  rfl

/-- One PAGE transition from `(xᵗ, gᵗ)` to `(xᵗ⁺¹, gᵗ⁺¹)`.

Book citation: `book/research/PAGE.json#/algorithm_spec/steps`: Lines 3-4 give
the primal update and probabilistic gradient-estimator update. -/
noncomputable def stateUpdate (t : ℕ) (ω : Ω)
    (state : State (E := E)) : State (E := E) :=
  let xNext := primalUpdate S state.x state.g
  { x := xNext
    g := estimatorUpdate S t ω state.g state.x xNext }

@[simp]
theorem stateUpdate_x (t : ℕ) (ω : Ω) (state : State (E := E)) :
    (S.stateUpdate t ω state).x =
      primalUpdate S state.x state.g := by
  rfl

@[simp]
theorem stateUpdate_g (t : ℕ) (ω : Ω) (state : State (E := E)) :
    (S.stateUpdate t ω state).g =
      estimatorUpdate S t ω state.g state.x
        (primalUpdate S state.x state.g) := by
  rfl

/-- The generated PAGE process, not a witness field.

Book citation: `book/research/PAGE.json#/algorithm_spec/steps`: Algorithm 1
iterates `for t = 0,1,2,...` with Lines 3-4 defining the next state.

The process is the canonical recursive process over `State`; its transition
already receives the sample path, so no lifted path-valued recursion is needed.
-/
noncomputable def process : ℕ → Ω → State (E := E) :=
  SOptLib.recursive_process_from_random_initial
    (initialState S) (fun t state ω => stateUpdate S t ω state)

/-- The generated primal iterates `xᵗ`.

Book citation: `book/research/PAGE.json#/algorithm_spec/steps/0`: Line 3
defines `x^{t+1}=x^t-ηg^t`. -/
noncomputable def iterate (t : ℕ) (ω : Ω) : E :=
  (S.process t ω).x

/-- The generated gradient estimators `gᵗ`.

Book citation: `book/research/PAGE.json#/algorithm_spec/steps/1`: Line 4
defines `g^{t+1}` by the two PAGE estimator branches. -/
noncomputable def estimator (t : ℕ) (ω : Ω) : E :=
  (S.process t ω).g

/-- Uniformly selected PAGE output from the first `T` iterates.

Book citation: `book/research/PAGE.json#/algorithm_spec/output`: `xhat_T
chosen uniformly from {x^t}_{t∈[T]}`. -/
noncomputable def uniformOutput (T : ℕ) (k : Fin T) (ω : Ω) : E :=
  S.iterate k.val ω

/-- Canonical uniform output-index law for the PAGE output rule.

Book citation: `book/research/PAGE.json#/algorithm_spec/output`: `xhat_T
chosen uniformly from {x^t}_{t∈[T]}`. -/
noncomputable def outputIndexLaw (T : ℕ) [NeZero T] : PMF (Fin T) :=
  PMF.uniformOfFintype (Fin T)

/-- Joint law of the uniformly selected PAGE output index and sample path.

Book citation: `book/research/PAGE.json#/algorithm_spec/output`: the output is
the random iterate `xhat_T chosen uniformly from {x^t}_{t∈[T]}`. -/
noncomputable def outputJointLaw [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) (T : ℕ) [NeZero T] :
    MeasureTheory.Measure (Fin T × Ω) :=
  SOptLib.selected_joint_measure (outputIndexLaw T) P

/-- Integrand for the gradient norm at PAGE's uniformly selected output.

Book citation: `book/research/PAGE.json#/main_theorem/measure`, which names the
quantity `E[||nabla f(xhat_T)||]` for the random output iterate. -/
noncomputable def selectedGradientNormIntegrand [MeasurableSpace Ω]
    (T : ℕ) [NeZero T] (q : Fin T × Ω) : ℝ :=
  ‖S.fullGradient (S.uniformOutput T q.1 q.2)‖

/-- Well-definedness predicate for the paper expectation
`E[||nabla f(xhat_T)||]`. This is a theorem obligation under Theorem 1's
source assumptions, not a primitive setup or theorem-head assumption.

Book citation: `book/research/PAGE.json#/main_theorem/measure`: `Expected
gradient norm E[||nabla f(xhat_T)||] for the random output iterate`. -/
def SelectedGradientNormIntegrable [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) (T : ℕ) [NeZero T] : Prop :=
  MeasureTheory.Integrable (S.selectedGradientNormIntegrand T) (outputJointLaw P T)

/-- Expected norm of the full gradient at PAGE's uniformly selected output.

The definition is guarded by `SelectedGradientNormIntegrable` so Lean's
totalized Bochner integral is not silently used as the paper expectation
outside its well-definedness domain.

Book citation: `book/research/PAGE.json#/main_theorem/statement_math`: the
paper guarantee is `E[||nabla f(xhat_T)||] <= epsilon`. -/
noncomputable def expectedSelectedGradientNorm [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) (T : ℕ) [NeZero T] : ℝ := by
  classical
  exact
    if h : S.SelectedGradientNormIntegrable P T then
      ∫ q : Fin T × Ω, S.selectedGradientNormIntegrand T q ∂ outputJointLaw P T
    else
      0

/-- Reindex the refresh minibatch stream by `Fin (card B)` so it can be
compared with SOptLib's canonical iid minibatch path law.

Book citation: `book/research/PAGE.json#/algorithm_spec/initialization`:
`I denotes random minibatch samples with |I|=b`. -/
noncomputable def refreshFinSample
    (t : ℕ) (j : Fin (Fintype.card B)) (ω : Ω) : ι :=
  S.refreshSample t ((Fintype.equivFin B).symm j) ω

/-- Reindex the recursive minibatch stream by `Fin (card B')` so it can be
compared with SOptLib's canonical iid minibatch path law.

Book citation: `book/research/PAGE.json#/algorithm_spec/steps/1`: the
recursive branch averages over minibatch `I'` with denominator `b'`. -/
noncomputable def recursiveFinSample
    (t : ℕ) (j : Fin (Fintype.card B')) (ω : Ω) : ι :=
  S.recursiveSample t ((Fintype.equivFin B').symm j) ω

/-- The refresh minibatch sample path used in PAGE's full-refresh branch.

Book citation: `book/research/PAGE.json#/algorithm_spec/initialization`:
`I denotes random minibatch samples with |I|=b`. -/
noncomputable def refreshSamplePath (ω : Ω) :
    SOptLib.miniBatchSamplePath (Fintype.card B) ι :=
  fun t j => S.refreshFinSample t j ω

/-- The recursive minibatch sample path used in PAGE's low-cost branch.

Book citation: `book/research/PAGE.json#/algorithm_spec/steps/1`: the
recursive PAGE branch uses samples `i∈I'`. -/
noncomputable def recursiveSamplePath (ω : Ω) :
    SOptLib.miniBatchSamplePath (Fintype.card B') ι :=
  fun t j => S.recursiveFinSample t j ω

/-- Canonical path space for Algorithm 1's random source: a Bernoulli branch
stream, a refresh-minibatch stream, and a recursive-minibatch stream.

Book citation: `book/research/PAGE.json#/algorithm_spec/initialization`
introduces random minibatches `I`, while
`book/research/PAGE.json#/algorithm_spec/steps/1` introduces the Line 4
Bernoulli branch and recursive minibatch `I'`. -/
abbrev RandomSource : Type _ :=
  (ℕ → Bool) ×
    (SOptLib.miniBatchSamplePath (Fintype.card B) ι ×
      SOptLib.miniBatchSamplePath (Fintype.card B') ι)

/-- Algorithm 1's branch-probability domain.

Book citation: `book/research/PAGE.json#/assumptions/3`: `probability
{p_t}∈(0,1]`. -/
def RefreshProbabilityDomain : Prop :=
  SOptLib.ProbabilityScheduleDomain S.refreshProbability

/-- The Bernoulli PMF for Algorithm 1's Line 4 branch at time `t`.

Book citation: `book/research/PAGE.json#/algorithm_spec/steps/1`: the refresh
branch occurs `with probability p_t`; the recursive branch occurs `with
probability 1-p_t`. -/
noncomputable def branchPMF (hp : S.RefreshProbabilityDomain) (t : ℕ) : PMF Bool :=
  PMF.bernoulli ⟨S.refreshProbability t, (hp t).1.le⟩ (by
    change (S.refreshProbability t) ≤ (1 : ℝ)
    exact (hp t).2)

/-- Canonical product law for the full branch stream in Algorithm 1. -/
noncomputable def branchPathLaw (hp : S.RefreshProbabilityDomain) :
    MeasureTheory.Measure (ℕ → Bool) :=
  MeasureTheory.Measure.infinitePi (fun t : ℕ => (S.branchPMF hp t).toMeasure)

/-- Uniform component-index law for finite-sum minibatch draws. -/
noncomputable def componentUniformMeasure [MeasurableSpace ι] :
    MeasureTheory.Measure ι :=
  PMF.toMeasure (PMF.uniformOfFintype (α := ι))

/-- Canonical iid law for the refresh minibatch stream. -/
noncomputable def refreshMiniBatchSourceLaw [MeasurableSpace ι] :
    MeasureTheory.Measure (SOptLib.miniBatchSamplePath (Fintype.card B) ι) :=
  SOptLib.iidMiniBatchSampleLaw (Fintype.card B) (componentUniformMeasure (ι := ι))

/-- Canonical iid law for the recursive minibatch stream. -/
noncomputable def recursiveMiniBatchSourceLaw [MeasurableSpace ι] :
    MeasureTheory.Measure (SOptLib.miniBatchSamplePath (Fintype.card B') ι) :=
  SOptLib.iidMiniBatchSampleLaw (Fintype.card B') (componentUniformMeasure (ι := ι))

/-- Canonical product law for Algorithm 1's entire random source.

This is the object-layer repair for the stochastic spine: downstream freshness
facts are derived from a single joint product law for the branch stream and both
mini-batch streams, rather than asserted as theorem-head hypotheses.

Book/PDF citation: Algorithm 1 specifies fresh random minibatches and Line 4
branch probabilities; Lemma 3 expands expectations using that random-source
model around Eq. (16)-(18). -/
noncomputable def randomSourceLaw [MeasurableSpace ι]
    (hp : S.RefreshProbabilityDomain) :
    MeasureTheory.Measure (RandomSource (ι := ι) (B := B) (B' := B')) :=
  (S.branchPathLaw hp).prod
    ((refreshMiniBatchSourceLaw (ι := ι) (B := B)).prod
      (recursiveMiniBatchSourceLaw (ι := ι) (B' := B')))

/-- The actual Algorithm 1 random source generated on the ambient probability
space: branch path, refresh minibatches, and recursive minibatches. -/
noncomputable def randomSourcePath (ω : Ω) :
    RandomSource (ι := ι) (B := B) (B' := B') :=
  (fun t : ℕ => S.refreshBranch t ω,
    (S.refreshSamplePath ω, S.recursiveSamplePath ω))

@[simp]
theorem randomSourcePath_branch (ω : Ω) :
    (S.randomSourcePath ω).1 = fun t : ℕ => S.refreshBranch t ω := by
  rfl

@[simp]
theorem randomSourcePath_refresh (ω : Ω) :
    (S.randomSourcePath ω).2.1 = S.refreshSamplePath ω := by
  rfl

@[simp]
theorem randomSourcePath_recursive (ω : Ω) :
    (S.randomSourcePath ω).2.2 = S.recursiveSamplePath ω := by
  rfl

/-- Source-facing law for the probabilistic refresh branch in Algorithm 1.

Book citation: `book/research/PAGE.json#/algorithm_spec/steps/1`: the refresh
branch occurs `with probability p_t`; the recursive branch occurs `with
probability 1-p_t`. -/
def RefreshBranchLaw [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) : Prop :=
  ∀ t : ℕ,
    P {ω : Ω | S.refreshBranch t ω = true} =
      ENNReal.ofReal (S.refreshProbability t)

/-- Source-facing iid law for the fresh full-refresh minibatch stream.

Book citation: `book/research/PAGE.json#/algorithm_spec/initialization`:
`I denotes random minibatch samples with |I|=b`; PDF `paper/PAGE.pdf`,
Algorithm 1, Line 1 repeats `random minibatch samples with |I| = b`. -/
noncomputable def RefreshMiniBatchFreshLaw [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) : Prop :=
  letI : MeasurableSpace ι := ⊤
  SOptLib.miniBatchIidLawSpec (Fintype.card B)
    (PMF.toMeasure (PMF.uniformOfFintype (α := ι)))
    (MeasureTheory.Measure.map S.refreshSamplePath P)

/-- Source-facing iid law for the fresh recursive minibatch stream.

Book citation: `book/research/PAGE.json#/algorithm_spec/steps/1`: the
recursive branch averages over samples `i∈I'` and occurs `with probability
1-p_t`. -/
noncomputable def RecursiveMiniBatchFreshLaw [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) : Prop :=
  letI : MeasurableSpace ι := ⊤
  SOptLib.miniBatchIidLawSpec (Fintype.card B')
    (PMF.toMeasure (PMF.uniformOfFintype (α := ι)))
    (MeasureTheory.Measure.map S.recursiveSamplePath P)

/-- Joint Line 4 law for the PAGE estimator update: the branch choice and the
mini-batch used by the active branch have the probabilities stated in
Algorithm 1.

Book citation: `book/research/PAGE.json#/algorithm_spec/steps/1`: the estimator
has the refresh minibatch branch `with probability p_t` and the recursive
minibatch branch `with probability 1-p_t`. -/
def Line4EstimatorLaw [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) : Prop :=
  ∀ (t : ℕ) (useRefresh : Bool)
      (refreshVector : B → ι) (recursiveVector : B' → ι),
    P {ω : Ω |
        S.refreshBranch t ω = useRefresh ∧
          (if useRefresh then
            Fintype.card B = Fintype.card ι ∨
              ∀ j : B, S.refreshSample (t + 1) j ω = refreshVector j
          else
            ∀ j : B', S.recursiveSample t j ω = recursiveVector j)} =
      ENNReal.ofReal
        (if useRefresh then
          if Fintype.card B = Fintype.card ι then
            S.refreshProbability t
          else
            S.refreshProbability t * ((Fintype.card (B → ι) : ℝ)⁻¹)
        else
          (1 - S.refreshProbability t) * ((Fintype.card (B' → ι) : ℝ)⁻¹))

/-- Internal proof obligation: conditional freshness of the Bernoulli Line 4
branch relative to the state already generated before the branch is drawn.

Source boundary: `book/research/PAGE.json#/algorithm_spec/steps/1` states only
the Line 4 branch probabilities. The conditioning-on-past form is not part of
the paper-facing stochastic-law contract; it is derived below as a proof
obligation from the Algorithm 1 random-source law. -/
def Line4BranchFreshGivenState [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) : Prop :=
  ∀ (t : ℕ) (pastEvent : Set (State (E := E))),
    P {ω : Ω | S.process t ω ∈ pastEvent ∧ S.refreshBranch t ω = true} =
      ENNReal.ofReal (S.refreshProbability t) *
        P {ω : Ω | S.process t ω ∈ pastEvent}

/-- Conditional freshness of the low-cost minibatch `I'` in Line 4 relative to
the generated state and the branch event. This is the object-layer law consumed
by Lemma 3's centered fresh-minibatch calculation.

Source boundary: `book/research/PAGE.json#/algorithm_spec/steps/1` gives the
recursive branch mini-batch `I'` and probability `1-p_t`. The conditional
freshness formulation is kept out of `StochasticLaws` and exposed only as a
derived proof obligation for Lemma 3. -/
def RecursiveSampleFreshGivenLine4Past [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) : Prop :=
  ∀ (t : ℕ) (pastEvent : Set (State (E := E))) (recursiveVector : B' → ι),
    P {ω : Ω |
        S.process t ω ∈ pastEvent ∧
          S.refreshBranch t ω = false ∧
          ∀ j : B', S.recursiveSample t j ω = recursiveVector j} =
      ENNReal.ofReal ((Fintype.card (B' → ι) : ℝ)⁻¹) *
        P {ω : Ω |
          S.process t ω ∈ pastEvent ∧ S.refreshBranch t ω = false}

/-- The stochastic laws stated by Algorithm 1, encoded as one canonical product
law over the full branch/minibatch random-source path.

Book/PDF citation: `book/research/PAGE.json#/algorithm_spec/initialization`
states `I denotes random minibatch samples with |I|=b`;
`book/research/PAGE.json#/algorithm_spec/steps/1` states the Line 4 branches
`with probability p_t` and `with probability 1-p_t`; PDF `paper/PAGE.pdf`,
Algorithm 1, Lines 1 and 4 have the same random-minibatch and branch-probability
phrasing. Conditional-on-past freshness facts are derived theorem obligations
below, not assumptions in this paper-facing law. -/
noncomputable def StochasticLaws [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) : Prop :=
  letI : MeasurableSpace ι := ⊤
  ∃ hp : S.RefreshProbabilityDomain,
    MeasureTheory.Measure.map S.randomSourcePath P = S.randomSourceLaw hp

/-- The product random-source law projects to the marginal branch law.

This remains a proof obligation because later proof phases must unpack the
Mathlib product/infinite-product measure APIs. It is not a primitive
paper-facing assumption. -/
theorem refreshBranchLaw_of_stochasticLaws [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) (h_laws : S.StochasticLaws P) :
    S.RefreshBranchLaw P := by
  classical
  unfold RefreshBranchLaw
  unfold StochasticLaws at h_laws
  letI : MeasurableSpace ι := ⊤
  rcases h_laws with ⟨hp, hmap⟩
  haveI hbranchProb : MeasureTheory.IsProbabilityMeasure (S.branchPathLaw hp) := by
    unfold branchPathLaw
    infer_instance
  haveI hrefProb :
      MeasureTheory.IsProbabilityMeasure (refreshMiniBatchSourceLaw (ι := ι) (B := B)) := by
    unfold refreshMiniBatchSourceLaw componentUniformMeasure
    infer_instance
  haveI hrecProb :
      MeasureTheory.IsProbabilityMeasure (recursiveMiniBatchSourceLaw (ι := ι) (B' := B')) := by
    unfold recursiveMiniBatchSourceLaw componentUniformMeasure
    infer_instance
  haveI hpairProb : MeasureTheory.IsProbabilityMeasure
      ((refreshMiniBatchSourceLaw (ι := ι) (B := B)).prod
        (recursiveMiniBatchSourceLaw (ι := ι) (B' := B'))) := by
    infer_instance
  have hY : AEMeasurable S.randomSourcePath P := by
    by_contra hnot
    have hzero : MeasureTheory.Measure.map S.randomSourcePath P = 0 := by
      simpa using (MeasureTheory.Measure.map_of_not_aemeasurable hnot)
    have hru : S.randomSourceLaw hp Set.univ = (0 : ENNReal) := by
      rw [← hmap, hzero]
      simp
    have hprob : S.randomSourceLaw hp Set.univ = (1 : ENNReal) := by
      unfold randomSourceLaw
      simp
    rw [hprob] at hru
    norm_num at hru
  have hbranchPath :
      MeasureTheory.Measure.map (fun ω => (S.randomSourcePath ω).1) P = S.branchPathLaw hp := by
    exact
      map_fst_eq_of_map_prod_eq (P := P) (Y := S.randomSourcePath)
        (μ := S.branchPathLaw hp)
        (ν := (refreshMiniBatchSourceLaw (ι := ι) (B := B)).prod
          (recursiveMiniBatchSourceLaw (ι := ι) (B' := B')))
        hY (by simpa [randomSourceLaw] using hmap)
  intro t
  have heval :
      MeasureTheory.Measure.map (fun x : ℕ → Bool => x t) (S.branchPathLaw hp) =
        (S.branchPMF hp t).toMeasure := by
    unfold branchPathLaw
    simpa using
      (MeasureTheory.Measure.infinitePi_map_eval
        (μ := fun t : ℕ => (S.branchPMF hp t).toMeasure) t)
  have hbranchAEM : AEMeasurable (fun ω => (S.randomSourcePath ω).1) P :=
    measurable_fst.aemeasurable.comp_aemeasurable hY
  have hcoordAEM : AEMeasurable (fun ω => ((S.randomSourcePath ω).1) t) P :=
    (measurable_pi_apply t).aemeasurable.comp_aemeasurable hbranchAEM
  have hcoordMap :
      MeasureTheory.Measure.map (fun ω => ((S.randomSourcePath ω).1) t) P =
        (S.branchPMF hp t).toMeasure := by
    calc
      MeasureTheory.Measure.map (fun ω => ((S.randomSourcePath ω).1) t) P =
          MeasureTheory.Measure.map (fun x : ℕ → Bool => x t)
            (MeasureTheory.Measure.map (fun ω => (S.randomSourcePath ω).1) P) := by
            exact
              (AEMeasurable.map_map_of_aemeasurable
                (measurable_pi_apply t).aemeasurable hbranchAEM).symm
      _ = MeasureTheory.Measure.map (fun x : ℕ → Bool => x t) (S.branchPathLaw hp) := by
            rw [hbranchPath]
      _ = (S.branchPMF hp t).toMeasure := heval
  have hmass :=
    measure_preimage_singleton_eq_of_map_eq (P := P)
      (Y := fun ω => ((S.randomSourcePath ω).1) t)
      (mu := (S.branchPMF hp t).toMeasure) true hcoordAEM hcoordMap
  simpa [randomSourcePath, branchPMF, ENNReal.coe_nnreal_eq] using hmass

/-- The product random-source law projects to the iid refresh-minibatch stream
law. This is derived from `StochasticLaws`, not assumed separately. -/
theorem refreshMiniBatchFreshLaw_of_stochasticLaws [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) (h_laws : S.StochasticLaws P) :
    S.RefreshMiniBatchFreshLaw P := by
  classical
  unfold StochasticLaws at h_laws
  letI : MeasurableSpace ι := ⊤
  rcases h_laws with ⟨hp, hmap⟩
  haveI hbranchProb : MeasureTheory.IsProbabilityMeasure (S.branchPathLaw hp) := by
    unfold branchPathLaw
    infer_instance
  haveI hrefProb :
      MeasureTheory.IsProbabilityMeasure (refreshMiniBatchSourceLaw (ι := ι) (B := B)) := by
    unfold refreshMiniBatchSourceLaw componentUniformMeasure
    infer_instance
  haveI hrecProb :
      MeasureTheory.IsProbabilityMeasure (recursiveMiniBatchSourceLaw (ι := ι) (B' := B')) := by
    unfold recursiveMiniBatchSourceLaw componentUniformMeasure
    infer_instance
  haveI hpairProb : MeasureTheory.IsProbabilityMeasure
      ((refreshMiniBatchSourceLaw (ι := ι) (B := B)).prod
        (recursiveMiniBatchSourceLaw (ι := ι) (B' := B'))) := by
    infer_instance
  haveI hpairSFinite : MeasureTheory.SFinite
      ((refreshMiniBatchSourceLaw (ι := ι) (B := B)).prod
        (recursiveMiniBatchSourceLaw (ι := ι) (B' := B'))) := by
    infer_instance
  have hY : AEMeasurable S.randomSourcePath P := by
    by_contra hnot
    have hzero : MeasureTheory.Measure.map S.randomSourcePath P = 0 := by
      simpa using (MeasureTheory.Measure.map_of_not_aemeasurable hnot)
    have hru : S.randomSourceLaw hp Set.univ = (0 : ENNReal) := by
      rw [← hmap, hzero]
      simp
    have hprob : S.randomSourceLaw hp Set.univ = (1 : ENNReal) := by
      unfold randomSourceLaw
      simp
    rw [hprob] at hru
    norm_num at hru
  have hpairAEM : AEMeasurable (fun ω => (S.randomSourcePath ω).2) P :=
    measurable_snd.aemeasurable.comp_aemeasurable hY
  have hpair :
      MeasureTheory.Measure.map (fun ω => (S.randomSourcePath ω).2) P =
        (refreshMiniBatchSourceLaw (ι := ι) (B := B)).prod
          (recursiveMiniBatchSourceLaw (ι := ι) (B' := B')) := by
    exact
      map_snd_eq_of_map_prod_eq (P := P) (Y := S.randomSourcePath)
        (μ := S.branchPathLaw hp)
        (ν := (refreshMiniBatchSourceLaw (ι := ι) (B := B)).prod
          (recursiveMiniBatchSourceLaw (ι := ι) (B' := B')))
        hY (by simpa [randomSourceLaw] using hmap)
  have hrefreshRaw :
      MeasureTheory.Measure.map (fun ω => ((S.randomSourcePath ω).2).1) P =
        refreshMiniBatchSourceLaw (ι := ι) (B := B) := by
    exact
      map_fst_eq_of_map_prod_eq (P := P) (Y := fun ω => (S.randomSourcePath ω).2)
        (μ := refreshMiniBatchSourceLaw (ι := ι) (B := B))
        (ν := recursiveMiniBatchSourceLaw (ι := ι) (B' := B')) hpairAEM hpair
  have hrefresh :
      MeasureTheory.Measure.map S.refreshSamplePath P =
        refreshMiniBatchSourceLaw (ι := ι) (B := B) := by
    simpa [randomSourcePath] using hrefreshRaw
  unfold RefreshMiniBatchFreshLaw
  rw [hrefresh]
  simpa [refreshMiniBatchSourceLaw, componentUniformMeasure] using
    (SOptLib.iidMiniBatchSampleLaw_spec (Fintype.card B)
      (PMF.toMeasure (PMF.uniformOfFintype (α := ι))))

/-- The product random-source law projects to the iid recursive-minibatch stream
law. This is derived from `StochasticLaws`, not assumed separately. -/
theorem recursiveMiniBatchFreshLaw_of_stochasticLaws [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) (h_laws : S.StochasticLaws P) :
    S.RecursiveMiniBatchFreshLaw P := by
  classical
  unfold StochasticLaws at h_laws
  letI : MeasurableSpace ι := ⊤
  rcases h_laws with ⟨hp, hmap⟩
  haveI hbranchProb : MeasureTheory.IsProbabilityMeasure (S.branchPathLaw hp) := by
    unfold branchPathLaw
    infer_instance
  haveI hrefProb :
      MeasureTheory.IsProbabilityMeasure (refreshMiniBatchSourceLaw (ι := ι) (B := B)) := by
    unfold refreshMiniBatchSourceLaw componentUniformMeasure
    infer_instance
  haveI hrecProb :
      MeasureTheory.IsProbabilityMeasure (recursiveMiniBatchSourceLaw (ι := ι) (B' := B')) := by
    unfold recursiveMiniBatchSourceLaw componentUniformMeasure
    infer_instance
  haveI hpairProb : MeasureTheory.IsProbabilityMeasure
      ((refreshMiniBatchSourceLaw (ι := ι) (B := B)).prod
        (recursiveMiniBatchSourceLaw (ι := ι) (B' := B'))) := by
    infer_instance
  haveI hpairSFinite : MeasureTheory.SFinite
      ((refreshMiniBatchSourceLaw (ι := ι) (B := B)).prod
        (recursiveMiniBatchSourceLaw (ι := ι) (B' := B'))) := by
    infer_instance
  have hY : AEMeasurable S.randomSourcePath P := by
    by_contra hnot
    have hzero : MeasureTheory.Measure.map S.randomSourcePath P = 0 := by
      simpa using (MeasureTheory.Measure.map_of_not_aemeasurable hnot)
    have hru : S.randomSourceLaw hp Set.univ = (0 : ENNReal) := by
      rw [← hmap, hzero]
      simp
    have hprob : S.randomSourceLaw hp Set.univ = (1 : ENNReal) := by
      unfold randomSourceLaw
      simp
    rw [hprob] at hru
    norm_num at hru
  have hpairAEM : AEMeasurable (fun ω => (S.randomSourcePath ω).2) P :=
    measurable_snd.aemeasurable.comp_aemeasurable hY
  have hpair :
      MeasureTheory.Measure.map (fun ω => (S.randomSourcePath ω).2) P =
        (refreshMiniBatchSourceLaw (ι := ι) (B := B)).prod
          (recursiveMiniBatchSourceLaw (ι := ι) (B' := B')) := by
    exact
      map_snd_eq_of_map_prod_eq (P := P) (Y := S.randomSourcePath)
        (μ := S.branchPathLaw hp)
        (ν := (refreshMiniBatchSourceLaw (ι := ι) (B := B)).prod
          (recursiveMiniBatchSourceLaw (ι := ι) (B' := B')))
        hY (by simpa [randomSourceLaw] using hmap)
  have hrecRaw :
      MeasureTheory.Measure.map (fun ω => ((S.randomSourcePath ω).2).2) P =
        recursiveMiniBatchSourceLaw (ι := ι) (B' := B') := by
    exact
      map_snd_eq_of_map_prod_eq (P := P) (Y := fun ω => (S.randomSourcePath ω).2)
        (μ := refreshMiniBatchSourceLaw (ι := ι) (B := B))
        (ν := recursiveMiniBatchSourceLaw (ι := ι) (B' := B')) hpairAEM hpair
  have hrec :
      MeasureTheory.Measure.map S.recursiveSamplePath P =
        recursiveMiniBatchSourceLaw (ι := ι) (B' := B') := by
    simpa [randomSourcePath] using hrecRaw
  unfold RecursiveMiniBatchFreshLaw
  rw [hrec]
  simpa [recursiveMiniBatchSourceLaw, componentUniformMeasure] using
    (SOptLib.iidMiniBatchSampleLaw_spec (Fintype.card B')
      (PMF.toMeasure (PMF.uniformOfFintype (α := ι))))

/-- A fixed row of the canonical iid mini-batch path law is the finite product
uniform law after reindexing from `Fin (card C)` back to the paper's batch
index type `C`. -/
private theorem iidMiniBatchSampleLaw_row_map_eq_uniform_pi
    {A C : Type*} [Fintype A] [Fintype C] [DecidableEq C]
    [Nonempty A] [Nonempty C] (k : ℕ) :
    letI : MeasurableSpace A := ⊤
    MeasureTheory.Measure.map
        (fun omega : SOptLib.miniBatchSamplePath (Fintype.card C) A =>
          fun j : C => omega k (Fintype.equivFin C j))
        (SOptLib.iidMiniBatchSampleLaw (Fintype.card C)
          (PMF.toMeasure (PMF.uniformOfFintype (α := A)))) =
      MeasureTheory.Measure.pi
        (fun _ : C => PMF.toMeasure (PMF.uniformOfFintype (α := A))) := by
  classical
  letI : MeasurableSpace A := ⊤
  exact
    iid_mini_batch_sample_law_row_reindex_map_eq_pi
      (A := A) (C := C)
      (PMF.toMeasure (PMF.uniformOfFintype (α := A))) k

/-- Under the canonical iid mini-batch path law, the strict prefix before `t`
and the current row `t` have product law after reindexing each row by the
paper's batch index type. -/
private theorem iidMiniBatchSampleLaw_prefix_current_row_map_eq_prod
    {A C : Type*} [Fintype A] [Fintype C] [DecidableEq C]
    [Nonempty A] [Nonempty C] (t : ℕ) :
    letI : MeasurableSpace A := ⊤
    MeasureTheory.Measure.map
        (fun omega : SOptLib.miniBatchSamplePath (Fintype.card C) A =>
          (fun k : Fin t => fun j : C => omega k.1 (Fintype.equivFin C j),
            fun j : C => omega t (Fintype.equivFin C j)))
        (SOptLib.iidMiniBatchSampleLaw (Fintype.card C)
          (PMF.toMeasure (PMF.uniformOfFintype (α := A)))) =
      (MeasureTheory.Measure.map
        (fun omega : SOptLib.miniBatchSamplePath (Fintype.card C) A =>
          fun k : Fin t => fun j : C => omega k.1 (Fintype.equivFin C j))
        (SOptLib.iidMiniBatchSampleLaw (Fintype.card C)
          (PMF.toMeasure (PMF.uniformOfFintype (α := A))))).prod
        (MeasureTheory.Measure.pi
          (fun _ : C => PMF.toMeasure (PMF.uniformOfFintype (α := A)))) := by
  classical
  letI : MeasurableSpace A := ⊤
  simpa using
    (_root_.iidMiniBatchSampleLaw_prefix_current_row_map_eq_prod
      (A := A) (C := C)
      (PMF.toMeasure (PMF.uniformOfFintype (α := A))) t)

/-- Reverse product associativity as a pushforward by the canonical reassociation
map. -/
private theorem map_prod_assoc_reverse_eq_prod
    {A β C : Type*} [MeasurableSpace A] [MeasurableSpace β] [MeasurableSpace C]
    (μ : MeasureTheory.Measure A) (ν : MeasureTheory.Measure β)
    (κ : MeasureTheory.Measure C)
    [MeasureTheory.SFinite μ] [MeasureTheory.SFinite ν] [MeasureTheory.SFinite κ] :
    MeasureTheory.Measure.map
        (fun z : A × (β × C) => ((z.1, z.2.1), z.2.2))
        (μ.prod (ν.prod κ)) =
      (μ.prod ν).prod κ := by
  classical
  let splitRight : A × (β × C) → (A × β) × C :=
    fun z => ((z.1, z.2.1), z.2.2)
  have hsplitMeas : Measurable splitRight := by
    simpa [splitRight] using
      ((measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
        (measurable_snd.comp measurable_snd))
  have hforward :
      MeasureTheory.Measure.map
          (MeasurableEquiv.prodAssoc : (A × β) × C ≃ᵐ A × β × C)
          ((μ.prod ν).prod κ) =
        μ.prod (ν.prod κ) := by
    exact MeasureTheory.Measure.prodAssoc_prod (μ := μ) (ν := ν) (τ := κ)
  calc
    MeasureTheory.Measure.map splitRight (μ.prod (ν.prod κ)) =
        MeasureTheory.Measure.map splitRight
          (MeasureTheory.Measure.map
            (MeasurableEquiv.prodAssoc : (A × β) × C ≃ᵐ A × β × C)
            ((μ.prod ν).prod κ)) := by
          rw [hforward]
    _ = (μ.prod ν).prod κ := by
        rw [MeasureTheory.Measure.map_map]
        · trans MeasureTheory.Measure.map id ((μ.prod ν).prod κ)
          · apply MeasureTheory.Measure.map_congr
            filter_upwards with x
            rcases x with ⟨⟨a, b⟩, c⟩
            rfl
          · simp
        · exact hsplitMeas
        · exact
            (MeasurableEquiv.prodAssoc : (A × β) × C ≃ᵐ A × β × C).measurable

/-- The refresh stream coordinates used in the Line 4 past key and the
recursive strict-prefix rows are independent of the current recursive row under
the canonical minibatch product law. -/
private theorem refresh_recursive_line4_key_current_row_map_eq_prod
    (t : ℕ) :
    letI : MeasurableSpace ι := ⊤
    MeasureTheory.Measure.map
        (fun z :
            SOptLib.miniBatchSamplePath (Fintype.card B) ι ×
              SOptLib.miniBatchSamplePath (Fintype.card B') ι =>
          ((fun k : Fin (t + 1) => fun j : B =>
              z.1 k.1 (Fintype.equivFin B j),
            fun k : Fin t => fun j : B' =>
              z.2 k.1 (Fintype.equivFin B' j)),
            fun j : B' => z.2 t (Fintype.equivFin B' j)))
        ((refreshMiniBatchSourceLaw (ι := ι) (B := B)).prod
          (recursiveMiniBatchSourceLaw (ι := ι) (B' := B'))) =
      (MeasureTheory.Measure.map
        (fun z :
            SOptLib.miniBatchSamplePath (Fintype.card B) ι ×
              SOptLib.miniBatchSamplePath (Fintype.card B') ι =>
          (fun k : Fin (t + 1) => fun j : B =>
              z.1 k.1 (Fintype.equivFin B j),
            fun k : Fin t => fun j : B' =>
              z.2 k.1 (Fintype.equivFin B' j)))
        ((refreshMiniBatchSourceLaw (ι := ι) (B := B)).prod
          (recursiveMiniBatchSourceLaw (ι := ι) (B' := B')))).prod
        (MeasureTheory.Measure.pi
          (fun _ : B' => PMF.toMeasure (PMF.uniformOfFintype (α := ι)))) := by
  classical
  letI : MeasurableSpace ι := ⊤
  let refreshKey :
      SOptLib.miniBatchSamplePath (Fintype.card B) ι →
        Fin (t + 1) → B → ι :=
    fun omega k j => omega k.1 (Fintype.equivFin B j)
  let recPrefix :
      SOptLib.miniBatchSamplePath (Fintype.card B') ι →
        Fin t → B' → ι :=
    fun omega k j => omega k.1 (Fintype.equivFin B' j)
  let recRow :
      SOptLib.miniBatchSamplePath (Fintype.card B') ι → B' → ι :=
    fun omega j => omega t (Fintype.equivFin B' j)
  let recPair :
      SOptLib.miniBatchSamplePath (Fintype.card B') ι →
        (Fin t → B' → ι) × (B' → ι) :=
    fun omega => (recPrefix omega, recRow omega)
  haveI hrefSFinite :
      MeasureTheory.SFinite (refreshMiniBatchSourceLaw (ι := ι) (B := B)) := by
    unfold refreshMiniBatchSourceLaw componentUniformMeasure
    infer_instance
  haveI hrecSFinite :
      MeasureTheory.SFinite (recursiveMiniBatchSourceLaw (ι := ι) (B' := B')) := by
    unfold recursiveMiniBatchSourceLaw componentUniformMeasure
    infer_instance
  have hrefreshMeas : Measurable refreshKey := by
    refine measurable_pi_lambda _ ?_
    intro k
    refine measurable_pi_lambda _ ?_
    intro j
    exact (measurable_pi_apply (Fintype.equivFin B j)).comp
      (measurable_pi_apply k.1)
  have hrecPrefixMeas : Measurable recPrefix := by
    refine measurable_pi_lambda _ ?_
    intro k
    refine measurable_pi_lambda _ ?_
    intro j
    exact (measurable_pi_apply (Fintype.equivFin B' j)).comp
      (measurable_pi_apply k.1)
  have hrecRowMeas : Measurable recRow := by
    refine measurable_pi_lambda _ ?_
    intro j
    exact (measurable_pi_apply (Fintype.equivFin B' j)).comp
      (measurable_pi_apply t)
  have hrecPairMeas : Measurable recPair :=
    hrecPrefixMeas.prodMk hrecRowMeas
  have hrecPairLaw :
      MeasureTheory.Measure.map recPair
          (recursiveMiniBatchSourceLaw (ι := ι) (B' := B')) =
        (MeasureTheory.Measure.map recPrefix
          (recursiveMiniBatchSourceLaw (ι := ι) (B' := B'))).prod
          (MeasureTheory.Measure.pi
            (fun _ : B' => PMF.toMeasure (PMF.uniformOfFintype (α := ι)))) := by
    simpa [recursiveMiniBatchSourceLaw, componentUniformMeasure, recPair,
      recPrefix, recRow] using
      (iidMiniBatchSampleLaw_prefix_current_row_map_eq_prod
        (A := ι) (C := B') (t := t))
  have hraw :
      MeasureTheory.Measure.map (Prod.map refreshKey recPair)
          ((refreshMiniBatchSourceLaw (ι := ι) (B := B)).prod
            (recursiveMiniBatchSourceLaw (ι := ι) (B' := B'))) =
        (MeasureTheory.Measure.map refreshKey
          (refreshMiniBatchSourceLaw (ι := ι) (B := B))).prod
          (MeasureTheory.Measure.map recPair
            (recursiveMiniBatchSourceLaw (ι := ι) (B' := B'))) := by
    exact (MeasureTheory.Measure.map_prod_map
      (refreshMiniBatchSourceLaw (ι := ι) (B := B))
      (recursiveMiniBatchSourceLaw (ι := ι) (B' := B'))
      hrefreshMeas hrecPairMeas).symm
  let splitRight :
      (Fin (t + 1) → B → ι) × ((Fin t → B' → ι) × (B' → ι)) →
        ((Fin (t + 1) → B → ι) × (Fin t → B' → ι)) × (B' → ι) :=
    fun z => ((z.1, z.2.1), z.2.2)
  have hsplitMeas : Measurable splitRight := by
    simpa [splitRight] using
      ((measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
        (measurable_snd.comp measurable_snd))
  have htargetAsSplit :
      MeasureTheory.Measure.map
          (fun z :
              SOptLib.miniBatchSamplePath (Fintype.card B) ι ×
                SOptLib.miniBatchSamplePath (Fintype.card B') ι =>
            ((refreshKey z.1, recPrefix z.2), recRow z.2))
          ((refreshMiniBatchSourceLaw (ι := ι) (B := B)).prod
            (recursiveMiniBatchSourceLaw (ι := ι) (B' := B'))) =
        MeasureTheory.Measure.map splitRight
          (MeasureTheory.Measure.map (Prod.map refreshKey recPair)
            ((refreshMiniBatchSourceLaw (ι := ι) (B := B)).prod
              (recursiveMiniBatchSourceLaw (ι := ι) (B' := B')))) := by
    simpa [splitRight, recPair] using
      (AEMeasurable.map_map_of_aemeasurable
        hsplitMeas.aemeasurable
        (hrefreshMeas.prodMap hrecPairMeas).aemeasurable).symm
  have hminiKey :
      MeasureTheory.Measure.map
          (fun z :
              SOptLib.miniBatchSamplePath (Fintype.card B) ι ×
                SOptLib.miniBatchSamplePath (Fintype.card B') ι =>
            (refreshKey z.1, recPrefix z.2))
          ((refreshMiniBatchSourceLaw (ι := ι) (B := B)).prod
            (recursiveMiniBatchSourceLaw (ι := ι) (B' := B'))) =
        (MeasureTheory.Measure.map refreshKey
          (refreshMiniBatchSourceLaw (ι := ι) (B := B))).prod
          (MeasureTheory.Measure.map recPrefix
            (recursiveMiniBatchSourceLaw (ι := ι) (B' := B'))) := by
    exact (MeasureTheory.Measure.map_prod_map
      (refreshMiniBatchSourceLaw (ι := ι) (B := B))
      (recursiveMiniBatchSourceLaw (ι := ι) (B' := B'))
      hrefreshMeas hrecPrefixMeas).symm
  calc
    MeasureTheory.Measure.map
        (fun z :
            SOptLib.miniBatchSamplePath (Fintype.card B) ι ×
              SOptLib.miniBatchSamplePath (Fintype.card B') ι =>
          ((fun k : Fin (t + 1) => fun j : B =>
              z.1 k.1 (Fintype.equivFin B j),
            fun k : Fin t => fun j : B' =>
              z.2 k.1 (Fintype.equivFin B' j)),
            fun j : B' => z.2 t (Fintype.equivFin B' j)))
        ((refreshMiniBatchSourceLaw (ι := ι) (B := B)).prod
          (recursiveMiniBatchSourceLaw (ι := ι) (B' := B'))) =
      MeasureTheory.Measure.map
          (fun z :
              SOptLib.miniBatchSamplePath (Fintype.card B) ι ×
                SOptLib.miniBatchSamplePath (Fintype.card B') ι =>
            ((refreshKey z.1, recPrefix z.2), recRow z.2))
          ((refreshMiniBatchSourceLaw (ι := ι) (B := B)).prod
            (recursiveMiniBatchSourceLaw (ι := ι) (B' := B'))) := by
        rfl
    _ = MeasureTheory.Measure.map splitRight
          ((MeasureTheory.Measure.map refreshKey
            (refreshMiniBatchSourceLaw (ι := ι) (B := B))).prod
            ((MeasureTheory.Measure.map recPrefix
              (recursiveMiniBatchSourceLaw (ι := ι) (B' := B'))).prod
              (MeasureTheory.Measure.pi
                (fun _ : B' => PMF.toMeasure (PMF.uniformOfFintype (α := ι)))))) := by
        rw [htargetAsSplit, hraw, hrecPairLaw]
    _ = ((MeasureTheory.Measure.map refreshKey
            (refreshMiniBatchSourceLaw (ι := ι) (B := B))).prod
          (MeasureTheory.Measure.map recPrefix
            (recursiveMiniBatchSourceLaw (ι := ι) (B' := B')))).prod
          (MeasureTheory.Measure.pi
            (fun _ : B' => PMF.toMeasure (PMF.uniformOfFintype (α := ι)))) := by
        exact map_prod_assoc_reverse_eq_prod
          (μ := MeasureTheory.Measure.map refreshKey
            (refreshMiniBatchSourceLaw (ι := ι) (B := B)))
          (ν := MeasureTheory.Measure.map recPrefix
            (recursiveMiniBatchSourceLaw (ι := ι) (B' := B')))
          (κ := MeasureTheory.Measure.pi
            (fun _ : B' => PMF.toMeasure (PMF.uniformOfFintype (α := ι))))
    _ =
      (MeasureTheory.Measure.map
        (fun z :
            SOptLib.miniBatchSamplePath (Fintype.card B) ι ×
              SOptLib.miniBatchSamplePath (Fintype.card B') ι =>
          (fun k : Fin (t + 1) => fun j : B =>
              z.1 k.1 (Fintype.equivFin B j),
            fun k : Fin t => fun j : B' =>
              z.2 k.1 (Fintype.equivFin B' j)))
        ((refreshMiniBatchSourceLaw (ι := ι) (B := B)).prod
          (recursiveMiniBatchSourceLaw (ι := ι) (B' := B')))).prod
        (MeasureTheory.Measure.pi
          (fun _ : B' => PMF.toMeasure (PMF.uniformOfFintype (α := ι)))) := by
        rw [hminiKey]

/-- The random-source product law gives the joint law of the refresh branch
indicator and the refresh mini-batch row used by Algorithm 1 Line 4. -/
private theorem refresh_branch_active_vector_map_eq_prod [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) (hp : S.RefreshProbabilityDomain)
    (hmap :
      letI : MeasurableSpace ι := ⊤
      MeasureTheory.Measure.map S.randomSourcePath P = S.randomSourceLaw hp)
    (t : ℕ) :
    letI : MeasurableSpace ι := ⊤
    MeasureTheory.Measure.map
        (fun ω : Ω =>
          (S.refreshBranch t ω, fun j : B => S.refreshSample (t + 1) j ω)) P =
      (S.branchPMF hp t).toMeasure.prod
        (MeasureTheory.Measure.pi
          (fun _ : B => PMF.toMeasure (PMF.uniformOfFintype (α := ι)))) := by
  classical
  letI : MeasurableSpace ι := ⊤
  haveI hbranchProb : MeasureTheory.IsProbabilityMeasure (S.branchPathLaw hp) := by
    unfold branchPathLaw
    infer_instance
  haveI hrefProb :
      MeasureTheory.IsProbabilityMeasure (refreshMiniBatchSourceLaw (ι := ι) (B := B)) := by
    unfold refreshMiniBatchSourceLaw componentUniformMeasure
    infer_instance
  haveI hrecProb :
      MeasureTheory.IsProbabilityMeasure (recursiveMiniBatchSourceLaw (ι := ι) (B' := B')) := by
    unfold recursiveMiniBatchSourceLaw componentUniformMeasure
    infer_instance
  haveI hpairProb : MeasureTheory.IsProbabilityMeasure
      ((refreshMiniBatchSourceLaw (ι := ι) (B := B)).prod
        (recursiveMiniBatchSourceLaw (ι := ι) (B' := B'))) := by
    infer_instance
  haveI hpairSFinite : MeasureTheory.SFinite
      ((refreshMiniBatchSourceLaw (ι := ι) (B := B)).prod
        (recursiveMiniBatchSourceLaw (ι := ι) (B' := B'))) := by
    infer_instance
  have hY : AEMeasurable S.randomSourcePath P := by
    by_contra hnot
    have hzero : MeasureTheory.Measure.map S.randomSourcePath P = 0 := by
      simpa using (MeasureTheory.Measure.map_of_not_aemeasurable hnot)
    have hru : S.randomSourceLaw hp Set.univ = (0 : ENNReal) := by
      rw [← hmap, hzero]
      simp
    have hprob : S.randomSourceLaw hp Set.univ = (1 : ENNReal) := by
      unfold randomSourceLaw
      simp
    rw [hprob] at hru
    norm_num at hru
  have hbranchEval :
      MeasureTheory.Measure.map (fun x : ℕ → Bool => x t) (S.branchPathLaw hp) =
        (S.branchPMF hp t).toMeasure := by
    unfold branchPathLaw
    simpa using
      (MeasureTheory.Measure.infinitePi_map_eval
        (μ := fun t : ℕ => (S.branchPMF hp t).toMeasure) t)
  have hrow :
      MeasureTheory.Measure.map
          (fun omega : SOptLib.miniBatchSamplePath (Fintype.card B) ι =>
            fun j : B => omega (t + 1) (Fintype.equivFin B j))
          (refreshMiniBatchSourceLaw (ι := ι) (B := B)) =
        MeasureTheory.Measure.pi
          (fun _ : B => PMF.toMeasure (PMF.uniformOfFintype (α := ι))) := by
    simpa [refreshMiniBatchSourceLaw, componentUniformMeasure] using
      (iidMiniBatchSampleLaw_row_map_eq_uniform_pi (A := ι) (C := B) (k := t + 1))
  have hrowMeas : Measurable
      (fun omega : SOptLib.miniBatchSamplePath (Fintype.card B) ι =>
        fun j : B => omega (t + 1) (Fintype.equivFin B j)) := by
    refine measurable_pi_lambda _ ?_
    intro j
    exact (measurable_pi_apply (Fintype.equivFin B j)).comp
      (measurable_pi_apply (t + 1))
  have hrowPair :
      MeasureTheory.Measure.map
          (fun z : SOptLib.miniBatchSamplePath (Fintype.card B) ι ×
              SOptLib.miniBatchSamplePath (Fintype.card B') ι =>
            fun j : B => z.1 (t + 1) (Fintype.equivFin B j))
          ((refreshMiniBatchSourceLaw (ι := ι) (B := B)).prod
            (recursiveMiniBatchSourceLaw (ι := ι) (B' := B'))) =
        MeasureTheory.Measure.pi
          (fun _ : B => PMF.toMeasure (PMF.uniformOfFintype (α := ι))) := by
    calc
      MeasureTheory.Measure.map
          (fun z : SOptLib.miniBatchSamplePath (Fintype.card B) ι ×
              SOptLib.miniBatchSamplePath (Fintype.card B') ι =>
            fun j : B => z.1 (t + 1) (Fintype.equivFin B j))
          ((refreshMiniBatchSourceLaw (ι := ι) (B := B)).prod
            (recursiveMiniBatchSourceLaw (ι := ι) (B' := B'))) =
        MeasureTheory.Measure.map
          (fun omega : SOptLib.miniBatchSamplePath (Fintype.card B) ι =>
            fun j : B => omega (t + 1) (Fintype.equivFin B j))
          (MeasureTheory.Measure.map Prod.fst
            ((refreshMiniBatchSourceLaw (ι := ι) (B := B)).prod
              (recursiveMiniBatchSourceLaw (ι := ι) (B' := B')))) := by
          exact (AEMeasurable.map_map_of_aemeasurable
            hrowMeas.aemeasurable measurable_fst.aemeasurable).symm
      _ = MeasureTheory.Measure.map
          (fun omega : SOptLib.miniBatchSamplePath (Fintype.card B) ι =>
            fun j : B => omega (t + 1) (Fintype.equivFin B j))
          (refreshMiniBatchSourceLaw (ι := ι) (B := B)) := by
          rw [MeasureTheory.Measure.map_fst_prod]
          simp
      _ = _ := hrow
  have hprodLaw :
      MeasureTheory.Measure.map
          (Prod.map (fun x : ℕ → Bool => x t)
            (fun z : SOptLib.miniBatchSamplePath (Fintype.card B) ι ×
                SOptLib.miniBatchSamplePath (Fintype.card B') ι =>
              fun j : B => z.1 (t + 1) (Fintype.equivFin B j)))
          (S.randomSourceLaw hp) =
        (S.branchPMF hp t).toMeasure.prod
          (MeasureTheory.Measure.pi
            (fun _ : B => PMF.toMeasure (PMF.uniformOfFintype (α := ι)))) := by
    unfold randomSourceLaw
    rw [← MeasureTheory.Measure.map_prod_map]
    · rw [hbranchEval, hrowPair]
    · exact measurable_pi_apply t
    · exact hrowMeas.comp measurable_fst
  have hG : AEMeasurable
      (fun y : RandomSource (ι := ι) (B := B) (B' := B') =>
        (y.1 t, fun j : B => y.2.1 (t + 1) (Fintype.equivFin B j)))
      (MeasureTheory.Measure.map S.randomSourcePath P) := by
    fun_prop
  have hraw :
      MeasureTheory.Measure.map
          (fun ω : Ω =>
            (((S.randomSourcePath ω).1) t,
              fun j : B => ((S.randomSourcePath ω).2).1 (t + 1) (Fintype.equivFin B j)))
          P =
        (S.branchPMF hp t).toMeasure.prod
          (MeasureTheory.Measure.pi
            (fun _ : B => PMF.toMeasure (PMF.uniformOfFintype (α := ι)))) := by
    calc
      MeasureTheory.Measure.map
          (fun ω : Ω =>
            (((S.randomSourcePath ω).1) t,
              fun j : B => ((S.randomSourcePath ω).2).1 (t + 1) (Fintype.equivFin B j)))
          P =
        MeasureTheory.Measure.map
          (fun y : RandomSource (ι := ι) (B := B) (B' := B') =>
            (y.1 t, fun j : B => y.2.1 (t + 1) (Fintype.equivFin B j)))
          (MeasureTheory.Measure.map S.randomSourcePath P) := by
          exact (AEMeasurable.map_map_of_aemeasurable hG hY).symm
      _ = MeasureTheory.Measure.map
          (fun y : RandomSource (ι := ι) (B := B) (B' := B') =>
            (y.1 t, fun j : B => y.2.1 (t + 1) (Fintype.equivFin B j)))
          (S.randomSourceLaw hp) := by
          rw [hmap]
      _ = MeasureTheory.Measure.map
          (Prod.map (fun x : ℕ → Bool => x t)
            (fun z : SOptLib.miniBatchSamplePath (Fintype.card B) ι ×
                SOptLib.miniBatchSamplePath (Fintype.card B') ι =>
              fun j : B => z.1 (t + 1) (Fintype.equivFin B j)))
          (S.randomSourceLaw hp) := by
          rfl
      _ = _ := hprodLaw
  simpa [randomSourcePath, refreshSamplePath, refreshFinSample] using hraw

/-- The random-source product law gives the joint law of the branch indicator
and the recursive mini-batch row used by Algorithm 1 Line 4. -/
private theorem recursive_branch_active_vector_map_eq_prod [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) (hp : S.RefreshProbabilityDomain)
    (hmap :
      letI : MeasurableSpace ι := ⊤
      MeasureTheory.Measure.map S.randomSourcePath P = S.randomSourceLaw hp)
    (t : ℕ) :
    letI : MeasurableSpace ι := ⊤
    MeasureTheory.Measure.map
        (fun ω : Ω =>
          (S.refreshBranch t ω, fun j : B' => S.recursiveSample t j ω)) P =
      (S.branchPMF hp t).toMeasure.prod
        (MeasureTheory.Measure.pi
          (fun _ : B' => PMF.toMeasure (PMF.uniformOfFintype (α := ι)))) := by
  classical
  letI : MeasurableSpace ι := ⊤
  haveI hbranchProb : MeasureTheory.IsProbabilityMeasure (S.branchPathLaw hp) := by
    unfold branchPathLaw
    infer_instance
  haveI hrefProb :
      MeasureTheory.IsProbabilityMeasure (refreshMiniBatchSourceLaw (ι := ι) (B := B)) := by
    unfold refreshMiniBatchSourceLaw componentUniformMeasure
    infer_instance
  haveI hrecProb :
      MeasureTheory.IsProbabilityMeasure (recursiveMiniBatchSourceLaw (ι := ι) (B' := B')) := by
    unfold recursiveMiniBatchSourceLaw componentUniformMeasure
    infer_instance
  haveI hpairProb : MeasureTheory.IsProbabilityMeasure
      ((refreshMiniBatchSourceLaw (ι := ι) (B := B)).prod
        (recursiveMiniBatchSourceLaw (ι := ι) (B' := B'))) := by
    infer_instance
  haveI hpairSFinite : MeasureTheory.SFinite
      ((refreshMiniBatchSourceLaw (ι := ι) (B := B)).prod
        (recursiveMiniBatchSourceLaw (ι := ι) (B' := B'))) := by
    infer_instance
  have hY : AEMeasurable S.randomSourcePath P := by
    by_contra hnot
    have hzero : MeasureTheory.Measure.map S.randomSourcePath P = 0 := by
      simpa using (MeasureTheory.Measure.map_of_not_aemeasurable hnot)
    have hru : S.randomSourceLaw hp Set.univ = (0 : ENNReal) := by
      rw [← hmap, hzero]
      simp
    have hprob : S.randomSourceLaw hp Set.univ = (1 : ENNReal) := by
      unfold randomSourceLaw
      simp
    rw [hprob] at hru
    norm_num at hru
  have hbranchEval :
      MeasureTheory.Measure.map (fun x : ℕ → Bool => x t) (S.branchPathLaw hp) =
        (S.branchPMF hp t).toMeasure := by
    unfold branchPathLaw
    simpa using
      (MeasureTheory.Measure.infinitePi_map_eval
        (μ := fun t : ℕ => (S.branchPMF hp t).toMeasure) t)
  have hrow :
      MeasureTheory.Measure.map
          (fun omega : SOptLib.miniBatchSamplePath (Fintype.card B') ι =>
            fun j : B' => omega t (Fintype.equivFin B' j))
          (recursiveMiniBatchSourceLaw (ι := ι) (B' := B')) =
        MeasureTheory.Measure.pi
          (fun _ : B' => PMF.toMeasure (PMF.uniformOfFintype (α := ι))) := by
    simpa [recursiveMiniBatchSourceLaw, componentUniformMeasure] using
      (iidMiniBatchSampleLaw_row_map_eq_uniform_pi (A := ι) (C := B') (k := t))
  have hrowMeas : Measurable
      (fun omega : SOptLib.miniBatchSamplePath (Fintype.card B') ι =>
        fun j : B' => omega t (Fintype.equivFin B' j)) := by
    refine measurable_pi_lambda _ ?_
    intro j
    exact (measurable_pi_apply (Fintype.equivFin B' j)).comp
      (measurable_pi_apply t)
  have hrowPair :
      MeasureTheory.Measure.map
          (fun z : SOptLib.miniBatchSamplePath (Fintype.card B) ι ×
              SOptLib.miniBatchSamplePath (Fintype.card B') ι =>
            fun j : B' => z.2 t (Fintype.equivFin B' j))
          ((refreshMiniBatchSourceLaw (ι := ι) (B := B)).prod
            (recursiveMiniBatchSourceLaw (ι := ι) (B' := B'))) =
        MeasureTheory.Measure.pi
          (fun _ : B' => PMF.toMeasure (PMF.uniformOfFintype (α := ι))) := by
    calc
      MeasureTheory.Measure.map
          (fun z : SOptLib.miniBatchSamplePath (Fintype.card B) ι ×
              SOptLib.miniBatchSamplePath (Fintype.card B') ι =>
            fun j : B' => z.2 t (Fintype.equivFin B' j))
          ((refreshMiniBatchSourceLaw (ι := ι) (B := B)).prod
            (recursiveMiniBatchSourceLaw (ι := ι) (B' := B'))) =
        MeasureTheory.Measure.map
          (fun omega : SOptLib.miniBatchSamplePath (Fintype.card B') ι =>
            fun j : B' => omega t (Fintype.equivFin B' j))
          (MeasureTheory.Measure.map Prod.snd
            ((refreshMiniBatchSourceLaw (ι := ι) (B := B)).prod
              (recursiveMiniBatchSourceLaw (ι := ι) (B' := B')))) := by
          exact (AEMeasurable.map_map_of_aemeasurable
            hrowMeas.aemeasurable measurable_snd.aemeasurable).symm
      _ = MeasureTheory.Measure.map
          (fun omega : SOptLib.miniBatchSamplePath (Fintype.card B') ι =>
            fun j : B' => omega t (Fintype.equivFin B' j))
          (recursiveMiniBatchSourceLaw (ι := ι) (B' := B')) := by
          rw [MeasureTheory.Measure.map_snd_prod]
          simp
      _ = _ := hrow
  have hprodLaw :
      MeasureTheory.Measure.map
          (Prod.map (fun x : ℕ → Bool => x t)
            (fun z : SOptLib.miniBatchSamplePath (Fintype.card B) ι ×
                SOptLib.miniBatchSamplePath (Fintype.card B') ι =>
              fun j : B' => z.2 t (Fintype.equivFin B' j)))
          (S.randomSourceLaw hp) =
        (S.branchPMF hp t).toMeasure.prod
          (MeasureTheory.Measure.pi
            (fun _ : B' => PMF.toMeasure (PMF.uniformOfFintype (α := ι)))) := by
    unfold randomSourceLaw
    rw [← MeasureTheory.Measure.map_prod_map]
    · rw [hbranchEval, hrowPair]
    · exact measurable_pi_apply t
    · exact hrowMeas.comp measurable_snd
  have hG : AEMeasurable
      (fun y : RandomSource (ι := ι) (B := B) (B' := B') =>
        (y.1 t, fun j : B' => y.2.2 t (Fintype.equivFin B' j)))
      (MeasureTheory.Measure.map S.randomSourcePath P) := by
    fun_prop
  have hraw :
      MeasureTheory.Measure.map
          (fun ω : Ω =>
            (((S.randomSourcePath ω).1) t,
              fun j : B' => ((S.randomSourcePath ω).2).2 t (Fintype.equivFin B' j)))
          P =
        (S.branchPMF hp t).toMeasure.prod
          (MeasureTheory.Measure.pi
            (fun _ : B' => PMF.toMeasure (PMF.uniformOfFintype (α := ι)))) := by
    calc
      MeasureTheory.Measure.map
          (fun ω : Ω =>
            (((S.randomSourcePath ω).1) t,
              fun j : B' => ((S.randomSourcePath ω).2).2 t (Fintype.equivFin B' j)))
          P =
        MeasureTheory.Measure.map
          (fun y : RandomSource (ι := ι) (B := B) (B' := B') =>
            (y.1 t, fun j : B' => y.2.2 t (Fintype.equivFin B' j)))
          (MeasureTheory.Measure.map S.randomSourcePath P) := by
          exact (AEMeasurable.map_map_of_aemeasurable hG hY).symm
      _ = MeasureTheory.Measure.map
          (fun y : RandomSource (ι := ι) (B := B) (B' := B') =>
            (y.1 t, fun j : B' => y.2.2 t (Fintype.equivFin B' j)))
          (S.randomSourceLaw hp) := by
          rw [hmap]
      _ = MeasureTheory.Measure.map
          (Prod.map (fun x : ℕ → Bool => x t)
            (fun z : SOptLib.miniBatchSamplePath (Fintype.card B) ι ×
                SOptLib.miniBatchSamplePath (Fintype.card B') ι =>
              fun j : B' => z.2 t (Fintype.equivFin B' j)))
          (S.randomSourceLaw hp) := by
          rfl
      _ = _ := hprodLaw
  simpa [randomSourcePath, recursiveSamplePath, recursiveFinSample] using hraw

/-- A finite product of uniform component-index laws assigns each sample vector
the inverse cardinality of the function space. -/
private theorem uniform_pi_singleton_mass
    {A C : Type*} [Fintype A] [Fintype C] [DecidableEq C] [Nonempty A] (v : C → A) :
    letI : MeasurableSpace A := ⊤
    (MeasureTheory.Measure.pi
      (fun _ : C => PMF.toMeasure (PMF.uniformOfFintype (α := A))))
        ({v} : Set (C → A)) =
      ENNReal.ofReal ((Fintype.card (C → A) : ℝ)⁻¹) := by
  classical
  letI : MeasurableSpace A := ⊤
  rw [MeasureTheory.Measure.pi_singleton]
  simp [PMF.uniformOfFintype_apply]
  rw [ENNReal.ofReal_inv_of_pos (pow_pos (Nat.cast_pos.mpr Fintype.card_pos) _)]
  rw [ENNReal.ofReal_pow (Nat.cast_nonneg (Fintype.card A))]
  simpa using
    (ENNReal.inv_pow (a := (Fintype.card A : ENNReal)) (n := Fintype.card C)).symm

/-- If a random variable has a named probability pushforward law, then it is
a.e. measurable under the source measure. -/
private theorem aemeasurable_of_map_eq_probability_law
    {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    {P : MeasureTheory.Measure Ω} {Y : Ω → A} {μ : MeasureTheory.Measure A}
    [MeasureTheory.IsProbabilityMeasure μ]
    (hmap : MeasureTheory.Measure.map Y P = μ) :
    AEMeasurable Y P := by
  by_contra hnot
  have hzero : MeasureTheory.Measure.map Y P = 0 := by
    simpa using (MeasureTheory.Measure.map_of_not_aemeasurable hnot)
  have hμ_zero : μ Set.univ = (0 : ENNReal) := by
    rw [← hmap, hzero]
    simp
  have hμ_one : μ Set.univ = (1 : ENNReal) := by
    simp
  rw [hμ_one] at hμ_zero
  norm_num at hμ_zero

/-- Finite random-source coordinates that determine the PAGE state before the
Line 4 branch at time `t`: branch bits before `t`, refresh rows through `t`,
and recursive rows before `t`. -/
private abbrev Line4PastKey (S : Setup ι E Ω B B') (t : ℕ) : Type _ :=
  (Fin t → Bool) × ((Fin (t + 1) → B → ι) × (Fin t → B' → ι))

private noncomputable def line4PastKey
    (S : Setup ι E Ω B B') (t : ℕ) (ω : Ω) : Line4PastKey S t :=
  (fun k : Fin t => S.refreshBranch k.1 ω,
    (fun k : Fin (t + 1) => fun j : B => S.refreshSample k.1 j ω,
      fun k : Fin t => fun j : B' => S.recursiveSample k.1 j ω))

private noncomputable def randomSourceLine4PastKey
    (S : Setup ι E Ω B B') (t : ℕ)
    (y : RandomSource (ι := ι) (B := B) (B' := B')) : Line4PastKey S t :=
  (fun k : Fin t => y.1 k.1,
    (fun k : Fin (t + 1) => fun j : B => y.2.1 k.1 (Fintype.equivFin B j),
      fun k : Fin t => fun j : B' => y.2.2 k.1 (Fintype.equivFin B' j)))

private theorem randomSourceLine4PastKey_measurable
    (S : Setup ι E Ω B B') (t : ℕ) :
    letI : MeasurableSpace ι := ⊤
    Measurable
      (fun y : RandomSource (ι := ι) (B := B) (B' := B') =>
        randomSourceLine4PastKey S t y) := by
  classical
  letI : MeasurableSpace ι := ⊤
  have hbranch :
      Measurable
        (fun y : RandomSource (ι := ι) (B := B) (B' := B') =>
          fun k : Fin t => y.1 k.1) := by
    refine measurable_pi_lambda _ ?_
    intro k
    exact (measurable_pi_apply k.1).comp measurable_fst
  have hrefresh :
      Measurable
        (fun y : RandomSource (ι := ι) (B := B) (B' := B') =>
          fun k : Fin (t + 1) => fun j : B =>
            y.2.1 k.1 (Fintype.equivFin B j)) := by
    refine measurable_pi_lambda _ ?_
    intro k
    refine measurable_pi_lambda _ ?_
    intro j
    have hcoord :
        Measurable
          (fun omega : SOptLib.miniBatchSamplePath (Fintype.card B) ι =>
            omega k.1 (Fintype.equivFin B j)) := by
      exact (measurable_pi_apply (Fintype.equivFin B j)).comp
        (measurable_pi_apply k.1)
    exact hcoord.comp (measurable_fst.comp measurable_snd)
  have hrecursive :
      Measurable
        (fun y : RandomSource (ι := ι) (B := B) (B' := B') =>
          fun k : Fin t => fun j : B' =>
            y.2.2 k.1 (Fintype.equivFin B' j)) := by
    refine measurable_pi_lambda _ ?_
    intro k
    refine measurable_pi_lambda _ ?_
    intro j
    have hcoord :
        Measurable
          (fun omega : SOptLib.miniBatchSamplePath (Fintype.card B') ι =>
            omega k.1 (Fintype.equivFin B' j)) := by
      exact (measurable_pi_apply (Fintype.equivFin B' j)).comp
        (measurable_pi_apply k.1)
    exact hcoord.comp (measurable_snd.comp measurable_snd)
  simpa [randomSourceLine4PastKey, Line4PastKey] using
    hbranch.prodMk (hrefresh.prodMk hrecursive)

private theorem measurableSet_line4PastKey_of_fintype
    (S : Setup ι E Ω B B') (t : ℕ) (K : Set (Line4PastKey S t)) :
    letI : MeasurableSpace ι := ⊤
    MeasurableSet K := by
  classical
  letI : MeasurableSpace ι := ⊤
  exact (Set.toFinite K).measurableSet

/-- Under the Bernoulli product branch law, the strict prefix before `t` and
the current branch bit at `t` have product law. -/
private theorem branch_prefix_current_map_eq_prod
    (hp : S.RefreshProbabilityDomain) (t : ℕ) :
    MeasureTheory.Measure.map
        (fun x : ℕ → Bool => (fun k : Fin t => x k.1, x t))
        (S.branchPathLaw hp) =
      (MeasureTheory.Measure.map (fun x : ℕ → Bool => fun k : Fin t => x k.1)
        (S.branchPathLaw hp)).prod (S.branchPMF hp t).toMeasure := by
  simpa [branchPathLaw] using
    (infinitePi_prefix_current_map_eq_prod
      (fun n : ℕ => (S.branchPMF hp n).toMeasure) t)

/-- Reassociate a triple product law and move the middle coordinate to the end. -/
private theorem map_prod_prod_shuffle_eq_prod
    {A β C : Type*} [MeasurableSpace A] [MeasurableSpace β] [MeasurableSpace C]
    (μ : MeasureTheory.Measure A) (ν : MeasureTheory.Measure β)
    (κ : MeasureTheory.Measure C)
    [MeasureTheory.SFinite μ] [MeasureTheory.SFinite ν] [MeasureTheory.SFinite κ] :
    MeasureTheory.Measure.map
        (fun z : (A × β) × C => ((z.1.1, z.2), z.1.2))
        ((μ.prod ν).prod κ) =
      (μ.prod κ).prod ν := by
  classical
  let assoc₁ : ((A × β) × C) → A × β × C :=
    fun z => (z.1.1, z.1.2, z.2)
  let swap₂ : A × β × C → A × C × β :=
    fun z => (z.1, z.2.2, z.2.1)
  let assoc₂ : A × C × β → (A × C) × β :=
    fun z => ((z.1, z.2.1), z.2.2)
  have hassoc₁_meas : Measurable assoc₁ := by
    simpa [assoc₁] using
      ((measurable_fst.comp measurable_fst).prodMk
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  have hswap₂_meas : Measurable swap₂ := by
    simpa [swap₂] using
      (measurable_fst.prodMk (measurable_swap.comp measurable_snd))
  have hassoc₂_meas : Measurable assoc₂ := by
    simpa [assoc₂] using
      ((measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
        (measurable_snd.comp measurable_snd))
  have h_assoc₁ :
      MeasureTheory.Measure.map assoc₁ ((μ.prod ν).prod κ) =
        μ.prod (ν.prod κ) := by
    simpa [assoc₁] using
      (MeasureTheory.Measure.prodAssoc_prod (μ := μ) (ν := ν) (τ := κ))
  have h_swap :
      MeasureTheory.Measure.map swap₂ (μ.prod (ν.prod κ)) =
        μ.prod (κ.prod ν) := by
    calc
      MeasureTheory.Measure.map swap₂ (μ.prod (ν.prod κ)) =
          (MeasureTheory.Measure.map id μ).prod
            (MeasureTheory.Measure.map Prod.swap (ν.prod κ)) := by
            simpa [swap₂] using
              (MeasureTheory.Measure.map_prod_map μ (ν.prod κ)
                measurable_id measurable_swap).symm
      _ = μ.prod (κ.prod ν) := by
          simp [MeasureTheory.Measure.prod_swap]
  have h_assoc₂ :
      MeasureTheory.Measure.map assoc₂ (μ.prod (κ.prod ν)) =
        (μ.prod κ).prod ν := by
    have hforward :
        MeasureTheory.Measure.map
            (MeasurableEquiv.prodAssoc : (A × C) × β ≃ᵐ A × C × β)
            ((μ.prod κ).prod ν) =
          μ.prod (κ.prod ν) := by
      exact MeasureTheory.Measure.prodAssoc_prod (μ := μ) (ν := κ) (τ := ν)
    calc
      MeasureTheory.Measure.map assoc₂ (μ.prod (κ.prod ν)) =
          MeasureTheory.Measure.map assoc₂
            (MeasureTheory.Measure.map
              (MeasurableEquiv.prodAssoc : (A × C) × β ≃ᵐ A × C × β)
              ((μ.prod κ).prod ν)) := by
            rw [hforward]
      _ = (μ.prod κ).prod ν := by
          rw [MeasureTheory.Measure.map_map]
          · trans MeasureTheory.Measure.map id ((μ.prod κ).prod ν)
            · apply MeasureTheory.Measure.map_congr
              filter_upwards with x
              rcases x with ⟨⟨a, c⟩, b⟩
              rfl
            · simp
          · exact hassoc₂_meas
          · exact
              (MeasurableEquiv.prodAssoc : (A × C) × β ≃ᵐ A × C × β).measurable
  have h_nested :
      MeasureTheory.Measure.map assoc₂
          (MeasureTheory.Measure.map swap₂
            (MeasureTheory.Measure.map assoc₁ ((μ.prod ν).prod κ))) =
        MeasureTheory.Measure.map
          (fun z : (A × β) × C => ((z.1.1, z.2), z.1.2))
          ((μ.prod ν).prod κ) := by
    calc
      MeasureTheory.Measure.map assoc₂
          (MeasureTheory.Measure.map swap₂
            (MeasureTheory.Measure.map assoc₁ ((μ.prod ν).prod κ))) =
          MeasureTheory.Measure.map ((assoc₂ ∘ swap₂) ∘ assoc₁)
            ((μ.prod ν).prod κ) := by
          rw [MeasureTheory.Measure.map_map]
          · rw [MeasureTheory.Measure.map_map]
            · exact hassoc₂_meas.comp hswap₂_meas
            · exact hassoc₁_meas
          · exact hassoc₂_meas
          · exact hswap₂_meas
      _ = MeasureTheory.Measure.map
          (fun z : (A × β) × C => ((z.1.1, z.2), z.1.2))
          ((μ.prod ν).prod κ) := by
          apply MeasureTheory.Measure.map_congr
          filter_upwards with z
          rcases z with ⟨⟨a, b⟩, c⟩
          rfl
  calc
    MeasureTheory.Measure.map
        (fun z : (A × β) × C => ((z.1.1, z.2), z.1.2))
        ((μ.prod ν).prod κ) =
        MeasureTheory.Measure.map assoc₂
          (MeasureTheory.Measure.map swap₂
            (MeasureTheory.Measure.map assoc₁ ((μ.prod ν).prod κ))) := by
          exact h_nested.symm
    _ = (μ.prod κ).prod ν := by
        rw [h_assoc₁, h_swap, h_assoc₂]

/-- Reassociate a four-coordinate product law and move the second coordinate
behind the third, leaving the fourth coordinate last. -/
private theorem map_prod_prod_prod_shuffle_eq_prod
    {A β C D : Type*} [MeasurableSpace A] [MeasurableSpace β]
    [MeasurableSpace C] [MeasurableSpace D]
    (μ : MeasureTheory.Measure A) (ν : MeasureTheory.Measure β)
    (κ : MeasureTheory.Measure C) (τ : MeasureTheory.Measure D)
    [MeasureTheory.SFinite μ] [MeasureTheory.SFinite ν]
    [MeasureTheory.SFinite κ] [MeasureTheory.SFinite τ] :
    MeasureTheory.Measure.map
        (fun z : (A × β) × (C × D) =>
          (((z.1.1, z.2.1), z.1.2), z.2.2))
        ((μ.prod ν).prod (κ.prod τ)) =
      ((μ.prod κ).prod ν).prod τ := by
  classical
  let splitRight : (A × β) × (C × D) → ((A × β) × C) × D :=
    fun z => ((z.1, z.2.1), z.2.2)
  let shuffleLeft : ((A × β) × C) → (A × C) × β :=
    fun z => ((z.1.1, z.2), z.1.2)
  have hsplitMeas : Measurable splitRight := by
    simpa [splitRight] using
      ((measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
        (measurable_snd.comp measurable_snd))
  have hshuffleMeas : Measurable shuffleLeft := by
    simpa [shuffleLeft] using
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd).prodMk
        (measurable_snd.comp measurable_fst)
  have hsplit :
      MeasureTheory.Measure.map splitRight ((μ.prod ν).prod (κ.prod τ)) =
        ((μ.prod ν).prod κ).prod τ := by
    have hforward :
        MeasureTheory.Measure.map
            (MeasurableEquiv.prodAssoc : ((A × β) × C) × D ≃ᵐ
              (A × β) × C × D)
            (((μ.prod ν).prod κ).prod τ) =
          (μ.prod ν).prod (κ.prod τ) := by
      exact MeasureTheory.Measure.prodAssoc_prod
        (μ := μ.prod ν) (ν := κ) (τ := τ)
    calc
      MeasureTheory.Measure.map splitRight ((μ.prod ν).prod (κ.prod τ)) =
          MeasureTheory.Measure.map splitRight
            (MeasureTheory.Measure.map
              (MeasurableEquiv.prodAssoc : ((A × β) × C) × D ≃ᵐ
                (A × β) × C × D)
              (((μ.prod ν).prod κ).prod τ)) := by
            rw [hforward]
      _ = ((μ.prod ν).prod κ).prod τ := by
          rw [MeasureTheory.Measure.map_map]
          · trans MeasureTheory.Measure.map id (((μ.prod ν).prod κ).prod τ)
            · apply MeasureTheory.Measure.map_congr
              filter_upwards with x
              rcases x with ⟨⟨⟨a, b⟩, c⟩, d⟩
              rfl
            · simp
          · exact hsplitMeas
          · exact
              (MeasurableEquiv.prodAssoc : ((A × β) × C) × D ≃ᵐ
                (A × β) × C × D).measurable
  have hshuffleProd :
      MeasureTheory.Measure.map (Prod.map shuffleLeft id)
          (((μ.prod ν).prod κ).prod τ) =
        ((μ.prod κ).prod ν).prod τ := by
    calc
      MeasureTheory.Measure.map (Prod.map shuffleLeft id)
          (((μ.prod ν).prod κ).prod τ) =
        (MeasureTheory.Measure.map shuffleLeft ((μ.prod ν).prod κ)).prod
          (MeasureTheory.Measure.map id τ) := by
          exact (MeasureTheory.Measure.map_prod_map
            ((μ.prod ν).prod κ) τ hshuffleMeas measurable_id).symm
      _ = ((μ.prod κ).prod ν).prod τ := by
          rw [map_prod_prod_shuffle_eq_prod (μ := μ) (ν := ν) (κ := κ)]
          simp
  have hmap :
      MeasureTheory.Measure.map
          (fun z : (A × β) × (C × D) =>
            (((z.1.1, z.2.1), z.1.2), z.2.2))
          ((μ.prod ν).prod (κ.prod τ)) =
        MeasureTheory.Measure.map (Prod.map shuffleLeft id)
          (MeasureTheory.Measure.map splitRight ((μ.prod ν).prod (κ.prod τ))) := by
    symm
    calc
      MeasureTheory.Measure.map (Prod.map shuffleLeft id)
          (MeasureTheory.Measure.map splitRight ((μ.prod ν).prod (κ.prod τ))) =
        MeasureTheory.Measure.map ((Prod.map shuffleLeft id) ∘ splitRight)
          ((μ.prod ν).prod (κ.prod τ)) := by
          rw [MeasureTheory.Measure.map_map]
          · exact (hshuffleMeas.prodMap measurable_id)
          · exact hsplitMeas
      _ = MeasureTheory.Measure.map
          (fun z : (A × β) × (C × D) =>
            (((z.1.1, z.2.1), z.1.2), z.2.2))
          ((μ.prod ν).prod (κ.prod τ)) := by
          apply MeasureTheory.Measure.map_congr
          filter_upwards with z
          rcases z with ⟨⟨a, b⟩, ⟨c, d⟩⟩
          rfl
  rw [hmap, hsplit, hshuffleProd]

/-- Source-space finite-key/current-branch product law for the PAGE random
source. -/
private theorem random_source_line4_past_key_branch_map_eq_prod
    (hp : S.RefreshProbabilityDomain) (t : ℕ) :
    letI : MeasurableSpace ι := ⊤
    AEMeasurable
        (fun y : RandomSource (ι := ι) (B := B) (B' := B') =>
          (randomSourceLine4PastKey S t y, y.1 t))
        (S.randomSourceLaw hp) ∧
      AEMeasurable
        (fun y : RandomSource (ι := ι) (B := B) (B' := B') =>
          randomSourceLine4PastKey S t y)
        (S.randomSourceLaw hp) ∧
      MeasureTheory.Measure.map
          (fun y : RandomSource (ι := ι) (B := B) (B' := B') =>
            (randomSourceLine4PastKey S t y, y.1 t))
          (S.randomSourceLaw hp) =
        (MeasureTheory.Measure.map
            (fun y : RandomSource (ι := ι) (B := B) (B' := B') =>
              randomSourceLine4PastKey S t y)
            (S.randomSourceLaw hp)).prod (S.branchPMF hp t).toMeasure := by
  classical
  letI : MeasurableSpace ι := ⊤
  have hkeyMeas :=
    randomSourceLine4PastKey_measurable (S := S) t
  have hcurrentMeas :
      Measurable
        (fun y : RandomSource (ι := ι) (B := B) (B' := B') => y.1 t) :=
    (measurable_pi_apply t).comp measurable_fst
  have hpairMeas :
      Measurable
        (fun y : RandomSource (ι := ι) (B := B) (B' := B') =>
          (randomSourceLine4PastKey S t y, y.1 t)) :=
    hkeyMeas.prodMk hcurrentMeas
  -- This is the remaining source-law projection: the branch stream prefix
  -- before `t`, the mini-batch streams, and the current branch coordinate.
  have hbranchPrefixCurrent :=
    branch_prefix_current_map_eq_prod (S := S) hp t
  let branchPair : (ℕ → Bool) → (Fin t → Bool) × Bool :=
    fun x => (fun k : Fin t => x k.1, x t)
  let miniKey :
      SOptLib.miniBatchSamplePath (Fintype.card B) ι ×
        SOptLib.miniBatchSamplePath (Fintype.card B') ι →
        (Fin (t + 1) → B → ι) × (Fin t → B' → ι) :=
    fun z =>
      (fun k : Fin (t + 1) => fun j : B => z.1 k.1 (Fintype.equivFin B j),
        fun k : Fin t => fun j : B' => z.2 k.1 (Fintype.equivFin B' j))
  have hbranchPrefixMeas :
      Measurable (fun x : ℕ → Bool => fun k : Fin t => x k.1) := by
    refine measurable_pi_lambda _ ?_
    intro k
    exact measurable_pi_apply k.1
  have hbranchPairMeas : Measurable branchPair := by
    dsimp [branchPair]
    exact hbranchPrefixMeas.prodMk (measurable_pi_apply t)
  have hminiKeyMeas : Measurable miniKey := by
    dsimp [miniKey]
    have hrefresh : Measurable
        (fun z : SOptLib.miniBatchSamplePath (Fintype.card B) ι ×
            SOptLib.miniBatchSamplePath (Fintype.card B') ι =>
          fun k : Fin (t + 1) => fun j : B => z.1 k.1 (Fintype.equivFin B j)) := by
      refine measurable_pi_lambda _ ?_
      intro k
      refine measurable_pi_lambda _ ?_
      intro j
      have hcoord : Measurable
          (fun omega : SOptLib.miniBatchSamplePath (Fintype.card B) ι =>
            omega k.1 (Fintype.equivFin B j)) := by
        exact (measurable_pi_apply (Fintype.equivFin B j)).comp
          (measurable_pi_apply k.1)
      exact hcoord.comp measurable_fst
    have hrecursive : Measurable
        (fun z : SOptLib.miniBatchSamplePath (Fintype.card B) ι ×
            SOptLib.miniBatchSamplePath (Fintype.card B') ι =>
          fun k : Fin t => fun j : B' => z.2 k.1 (Fintype.equivFin B' j)) := by
      refine measurable_pi_lambda _ ?_
      intro k
      refine measurable_pi_lambda _ ?_
      intro j
      have hcoord : Measurable
          (fun omega : SOptLib.miniBatchSamplePath (Fintype.card B') ι =>
            omega k.1 (Fintype.equivFin B' j)) := by
        exact (measurable_pi_apply (Fintype.equivFin B' j)).comp
          (measurable_pi_apply k.1)
      exact hcoord.comp measurable_snd
    exact hrefresh.prodMk hrecursive
  haveI hbranchProb : MeasureTheory.IsProbabilityMeasure (S.branchPathLaw hp) := by
    unfold branchPathLaw
    infer_instance
  haveI hrefProb :
      MeasureTheory.IsProbabilityMeasure (refreshMiniBatchSourceLaw (ι := ι) (B := B)) := by
    unfold refreshMiniBatchSourceLaw componentUniformMeasure
    infer_instance
  haveI hrecProb :
      MeasureTheory.IsProbabilityMeasure (recursiveMiniBatchSourceLaw (ι := ι) (B' := B')) := by
    unfold recursiveMiniBatchSourceLaw componentUniformMeasure
    infer_instance
  haveI hminiPairProb : MeasureTheory.IsProbabilityMeasure
      ((refreshMiniBatchSourceLaw (ι := ι) (B := B)).prod
        (recursiveMiniBatchSourceLaw (ι := ι) (B' := B'))) := by
    infer_instance
  haveI hminiPairSFinite : MeasureTheory.SFinite
      ((refreshMiniBatchSourceLaw (ι := ι) (B := B)).prod
        (recursiveMiniBatchSourceLaw (ι := ι) (B' := B'))) := by
    infer_instance
  have hraw :
      MeasureTheory.Measure.map (Prod.map branchPair miniKey) (S.randomSourceLaw hp) =
        (MeasureTheory.Measure.map branchPair (S.branchPathLaw hp)).prod
          (MeasureTheory.Measure.map miniKey
            ((refreshMiniBatchSourceLaw (ι := ι) (B := B)).prod
              (recursiveMiniBatchSourceLaw (ι := ι) (B' := B')))) := by
    unfold randomSourceLaw
    exact (MeasureTheory.Measure.map_prod_map (S.branchPathLaw hp)
      ((refreshMiniBatchSourceLaw (ι := ι) (B := B)).prod
        (recursiveMiniBatchSourceLaw (ι := ι) (B' := B')))
      hbranchPairMeas hminiKeyMeas).symm
  have hrawProduct :
      MeasureTheory.Measure.map (Prod.map branchPair miniKey) (S.randomSourceLaw hp) =
        ((MeasureTheory.Measure.map (fun x : ℕ → Bool => fun k : Fin t => x k.1)
          (S.branchPathLaw hp)).prod (S.branchPMF hp t).toMeasure).prod
          (MeasureTheory.Measure.map miniKey
            ((refreshMiniBatchSourceLaw (ι := ι) (B := B)).prod
              (recursiveMiniBatchSourceLaw (ι := ι) (B' := B')))) := by
    rw [hraw]
    dsimp [branchPair]
    rw [hbranchPrefixCurrent]
  have hkeyRaw :
      MeasureTheory.Measure.map
          (fun y : RandomSource (ι := ι) (B := B) (B' := B') =>
            randomSourceLine4PastKey S t y)
          (S.randomSourceLaw hp) =
        (MeasureTheory.Measure.map (fun x : ℕ → Bool => fun k : Fin t => x k.1)
          (S.branchPathLaw hp)).prod
          (MeasureTheory.Measure.map miniKey
            ((refreshMiniBatchSourceLaw (ι := ι) (B := B)).prod
              (recursiveMiniBatchSourceLaw (ι := ι) (B' := B')))) := by
    unfold randomSourceLaw
    calc
      MeasureTheory.Measure.map
          (fun y : RandomSource (ι := ι) (B := B) (B' := B') =>
            randomSourceLine4PastKey S t y)
          ((S.branchPathLaw hp).prod
            ((refreshMiniBatchSourceLaw (ι := ι) (B := B)).prod
              (recursiveMiniBatchSourceLaw (ι := ι) (B' := B')))) =
        MeasureTheory.Measure.map
          (Prod.map (fun x : ℕ → Bool => fun k : Fin t => x k.1) miniKey)
          ((S.branchPathLaw hp).prod
            ((refreshMiniBatchSourceLaw (ι := ι) (B := B)).prod
              (recursiveMiniBatchSourceLaw (ι := ι) (B' := B')))) := by
          rfl
      _ = _ := by
          exact (MeasureTheory.Measure.map_prod_map (S.branchPathLaw hp)
            ((refreshMiniBatchSourceLaw (ι := ι) (B := B)).prod
              (recursiveMiniBatchSourceLaw (ι := ι) (B' := B')))
            hbranchPrefixMeas hminiKeyMeas).symm
  let shuffle :
      ((Fin t → Bool) × Bool) ×
        ((Fin (t + 1) → B → ι) × (Fin t → B' → ι)) →
        Line4PastKey S t × Bool :=
    fun z => ((z.1.1, z.2), z.1.2)
  have hshuffleMeas : Measurable shuffle := by
    dsimp [shuffle, Line4PastKey]
    exact (((measurable_fst.comp measurable_fst).prodMk measurable_snd).prodMk
      (measurable_snd.comp measurable_fst))
  have hrawMapMeas : Measurable (Prod.map branchPair miniKey) :=
    hbranchPairMeas.prodMap hminiKeyMeas
  have hpairAsShuffle :
      MeasureTheory.Measure.map
          (fun y : RandomSource (ι := ι) (B := B) (B' := B') =>
            (randomSourceLine4PastKey S t y, y.1 t))
          (S.randomSourceLaw hp) =
        MeasureTheory.Measure.map shuffle
          (MeasureTheory.Measure.map (Prod.map branchPair miniKey) (S.randomSourceLaw hp)) := by
    simpa [shuffle, branchPair, miniKey, randomSourceLine4PastKey, Line4PastKey]
      using (AEMeasurable.map_map_of_aemeasurable
        hshuffleMeas.aemeasurable hrawMapMeas.aemeasurable).symm
  exact ⟨hpairMeas.aemeasurable, hkeyMeas.aemeasurable, by
    rw [hpairAsShuffle, hrawProduct, hkeyRaw]
    simpa [shuffle, Line4PastKey] using
      (map_prod_prod_shuffle_eq_prod
        (μ := MeasureTheory.Measure.map (fun x : ℕ → Bool => fun k : Fin t => x k.1)
          (S.branchPathLaw hp))
        (ν := (S.branchPMF hp t).toMeasure)
        (κ := MeasureTheory.Measure.map miniKey
          ((refreshMiniBatchSourceLaw (ι := ι) (B := B)).prod
            (recursiveMiniBatchSourceLaw (ι := ι) (B' := B')))))⟩

/-- Source-space finite-key/current-branch/current-recursive-row product law
for the PAGE random source. -/
private theorem random_source_line4_past_key_branch_recursive_row_map_eq_prod
    (hp : S.RefreshProbabilityDomain) (t : ℕ) :
    letI : MeasurableSpace ι := ⊤
    AEMeasurable
        (fun y : RandomSource (ι := ι) (B := B) (B' := B') =>
          ((randomSourceLine4PastKey S t y, y.1 t),
            fun j : B' => y.2.2 t (Fintype.equivFin B' j)))
        (S.randomSourceLaw hp) ∧
      AEMeasurable
        (fun y : RandomSource (ι := ι) (B := B) (B' := B') =>
          (randomSourceLine4PastKey S t y, y.1 t))
        (S.randomSourceLaw hp) ∧
      MeasureTheory.Measure.map
          (fun y : RandomSource (ι := ι) (B := B) (B' := B') =>
            ((randomSourceLine4PastKey S t y, y.1 t),
              fun j : B' => y.2.2 t (Fintype.equivFin B' j)))
          (S.randomSourceLaw hp) =
        (MeasureTheory.Measure.map
          (fun y : RandomSource (ι := ι) (B := B) (B' := B') =>
            (randomSourceLine4PastKey S t y, y.1 t))
          (S.randomSourceLaw hp)).prod
          (MeasureTheory.Measure.pi
            (fun _ : B' => PMF.toMeasure (PMF.uniformOfFintype (α := ι)))) := by
  classical
  letI : MeasurableSpace ι := ⊤
  have hkeyMeas := randomSourceLine4PastKey_measurable (S := S) t
  have hbranchMeas :
      Measurable
        (fun y : RandomSource (ι := ι) (B := B) (B' := B') => y.1 t) :=
    (measurable_pi_apply t).comp measurable_fst
  have hleftMeas :
      Measurable
        (fun y : RandomSource (ι := ι) (B := B) (B' := B') =>
          (randomSourceLine4PastKey S t y, y.1 t)) :=
    hkeyMeas.prodMk hbranchMeas
  have hrowMeas :
      Measurable
        (fun y : RandomSource (ι := ι) (B := B) (B' := B') =>
          fun j : B' => y.2.2 t (Fintype.equivFin B' j)) := by
    refine measurable_pi_lambda _ ?_
    intro j
    have hcoord :
        Measurable
          (fun omega : SOptLib.miniBatchSamplePath (Fintype.card B') ι =>
            omega t (Fintype.equivFin B' j)) := by
      exact (measurable_pi_apply (Fintype.equivFin B' j)).comp
        (measurable_pi_apply t)
    exact hcoord.comp (measurable_snd.comp measurable_snd)
  have hpairMeas :
      Measurable
        (fun y : RandomSource (ι := ι) (B := B) (B' := B') =>
          ((randomSourceLine4PastKey S t y, y.1 t),
            fun j : B' => y.2.2 t (Fintype.equivFin B' j))) :=
    hleftMeas.prodMk hrowMeas
  let branchPair : (ℕ → Bool) → (Fin t → Bool) × Bool :=
    fun x => (fun k : Fin t => x k.1, x t)
  let miniKey :
      SOptLib.miniBatchSamplePath (Fintype.card B) ι ×
        SOptLib.miniBatchSamplePath (Fintype.card B') ι →
        (Fin (t + 1) → B → ι) × (Fin t → B' → ι) :=
    fun z =>
      (fun k : Fin (t + 1) => fun j : B => z.1 k.1 (Fintype.equivFin B j),
        fun k : Fin t => fun j : B' => z.2 k.1 (Fintype.equivFin B' j))
  let miniKeyRow :
      SOptLib.miniBatchSamplePath (Fintype.card B) ι ×
        SOptLib.miniBatchSamplePath (Fintype.card B') ι →
        ((Fin (t + 1) → B → ι) × (Fin t → B' → ι)) × (B' → ι) :=
    fun z => (miniKey z, fun j : B' => z.2 t (Fintype.equivFin B' j))
  have hbranchPrefixMeas :
      Measurable (fun x : ℕ → Bool => fun k : Fin t => x k.1) := by
    refine measurable_pi_lambda _ ?_
    intro k
    exact measurable_pi_apply k.1
  have hbranchPairMeas : Measurable branchPair := by
    dsimp [branchPair]
    exact hbranchPrefixMeas.prodMk (measurable_pi_apply t)
  have hminiKeyMeas : Measurable miniKey := by
    dsimp [miniKey]
    have hrefresh : Measurable
        (fun z : SOptLib.miniBatchSamplePath (Fintype.card B) ι ×
            SOptLib.miniBatchSamplePath (Fintype.card B') ι =>
          fun k : Fin (t + 1) => fun j : B => z.1 k.1 (Fintype.equivFin B j)) := by
      refine measurable_pi_lambda _ ?_
      intro k
      refine measurable_pi_lambda _ ?_
      intro j
      have hcoord : Measurable
          (fun omega : SOptLib.miniBatchSamplePath (Fintype.card B) ι =>
            omega k.1 (Fintype.equivFin B j)) := by
        exact (measurable_pi_apply (Fintype.equivFin B j)).comp
          (measurable_pi_apply k.1)
      exact hcoord.comp measurable_fst
    have hrecursive : Measurable
        (fun z : SOptLib.miniBatchSamplePath (Fintype.card B) ι ×
            SOptLib.miniBatchSamplePath (Fintype.card B') ι =>
          fun k : Fin t => fun j : B' => z.2 k.1 (Fintype.equivFin B' j)) := by
      refine measurable_pi_lambda _ ?_
      intro k
      refine measurable_pi_lambda _ ?_
      intro j
      have hcoord : Measurable
          (fun omega : SOptLib.miniBatchSamplePath (Fintype.card B') ι =>
            omega k.1 (Fintype.equivFin B' j)) := by
        exact (measurable_pi_apply (Fintype.equivFin B' j)).comp
          (measurable_pi_apply k.1)
      exact hcoord.comp measurable_snd
    exact hrefresh.prodMk hrecursive
  have hminiKeyRowMeas : Measurable miniKeyRow := by
    dsimp [miniKeyRow]
    have hrow : Measurable
        (fun z : SOptLib.miniBatchSamplePath (Fintype.card B) ι ×
            SOptLib.miniBatchSamplePath (Fintype.card B') ι =>
          fun j : B' => z.2 t (Fintype.equivFin B' j)) := by
      refine measurable_pi_lambda _ ?_
      intro j
      have hcoord : Measurable
          (fun omega : SOptLib.miniBatchSamplePath (Fintype.card B') ι =>
            omega t (Fintype.equivFin B' j)) := by
        exact (measurable_pi_apply (Fintype.equivFin B' j)).comp
          (measurable_pi_apply t)
      exact hcoord.comp measurable_snd
    exact hminiKeyMeas.prodMk hrow
  haveI hbranchSFinite : MeasureTheory.SFinite (S.branchPathLaw hp) := by
    unfold branchPathLaw
    infer_instance
  haveI hminiPairSFinite : MeasureTheory.SFinite
      ((refreshMiniBatchSourceLaw (ι := ι) (B := B)).prod
        (recursiveMiniBatchSourceLaw (ι := ι) (B' := B'))) := by
    unfold refreshMiniBatchSourceLaw recursiveMiniBatchSourceLaw componentUniformMeasure
    infer_instance
  have hbranchLaw := branch_prefix_current_map_eq_prod (S := S) hp t
  have hminiLaw := refresh_recursive_line4_key_current_row_map_eq_prod
    (ι := ι) (B := B) (B' := B') t
  have hraw :
      MeasureTheory.Measure.map (Prod.map branchPair miniKeyRow) (S.randomSourceLaw hp) =
        (MeasureTheory.Measure.map branchPair (S.branchPathLaw hp)).prod
          (MeasureTheory.Measure.map miniKeyRow
            ((refreshMiniBatchSourceLaw (ι := ι) (B := B)).prod
              (recursiveMiniBatchSourceLaw (ι := ι) (B' := B')))) := by
    unfold randomSourceLaw
    exact (MeasureTheory.Measure.map_prod_map (S.branchPathLaw hp)
      ((refreshMiniBatchSourceLaw (ι := ι) (B := B)).prod
        (recursiveMiniBatchSourceLaw (ι := ι) (B' := B')))
      hbranchPairMeas hminiKeyRowMeas).symm
  have hkeyRaw :
      MeasureTheory.Measure.map
          (fun y : RandomSource (ι := ι) (B := B) (B' := B') =>
            randomSourceLine4PastKey S t y)
          (S.randomSourceLaw hp) =
        (MeasureTheory.Measure.map (fun x : ℕ → Bool => fun k : Fin t => x k.1)
          (S.branchPathLaw hp)).prod
          (MeasureTheory.Measure.map miniKey
            ((refreshMiniBatchSourceLaw (ι := ι) (B := B)).prod
              (recursiveMiniBatchSourceLaw (ι := ι) (B' := B')))) := by
    unfold randomSourceLaw
    simpa [randomSourceLine4PastKey, Line4PastKey, miniKey] using
      (MeasureTheory.Measure.map_prod_map (S.branchPathLaw hp)
        ((refreshMiniBatchSourceLaw (ι := ι) (B := B)).prod
          (recursiveMiniBatchSourceLaw (ι := ι) (B' := B')))
        hbranchPrefixMeas hminiKeyMeas).symm
  have hleftLaw := random_source_line4_past_key_branch_map_eq_prod (S := S) hp t
  let shuffle :
      ((Fin t → Bool) × Bool) ×
        (((Fin (t + 1) → B → ι) × (Fin t → B' → ι)) × (B' → ι)) →
        (Line4PastKey S t × Bool) × (B' → ι) :=
    fun z => ((((z.1.1, z.2.1), z.1.2), z.2.2))
  have hshuffleMeas : Measurable shuffle := by
    dsimp [shuffle, Line4PastKey]
    exact ((((measurable_fst.comp measurable_fst).prodMk
      (measurable_fst.comp measurable_snd)).prodMk
      (measurable_snd.comp measurable_fst)).prodMk
      (measurable_snd.comp measurable_snd))
  have hrawMapMeas : Measurable (Prod.map branchPair miniKeyRow) :=
    hbranchPairMeas.prodMap hminiKeyRowMeas
  have hpairAsShuffle :
      MeasureTheory.Measure.map
          (fun y : RandomSource (ι := ι) (B := B) (B' := B') =>
            ((randomSourceLine4PastKey S t y, y.1 t),
              fun j : B' => y.2.2 t (Fintype.equivFin B' j)))
          (S.randomSourceLaw hp) =
        MeasureTheory.Measure.map shuffle
          (MeasureTheory.Measure.map (Prod.map branchPair miniKeyRow)
            (S.randomSourceLaw hp)) := by
    simpa [shuffle, branchPair, miniKey, miniKeyRow, randomSourceLine4PastKey,
      Line4PastKey]
      using (AEMeasurable.map_map_of_aemeasurable
        hshuffleMeas.aemeasurable hrawMapMeas.aemeasurable).symm
  refine ⟨hpairMeas.aemeasurable, hleftMeas.aemeasurable, ?_⟩
  rw [hpairAsShuffle, hraw, hbranchLaw, hminiLaw]
  rw [hkeyRaw] at hleftLaw
  calc
    MeasureTheory.Measure.map shuffle
        (((MeasureTheory.Measure.map (fun x : ℕ → Bool => fun k : Fin t => x k.1)
              (S.branchPathLaw hp)).prod (S.branchPMF hp t).toMeasure).prod
          ((MeasureTheory.Measure.map miniKey
              ((refreshMiniBatchSourceLaw (ι := ι) (B := B)).prod
                (recursiveMiniBatchSourceLaw (ι := ι) (B' := B')))).prod
            (MeasureTheory.Measure.pi
              (fun _ : B' => PMF.toMeasure (PMF.uniformOfFintype (α := ι)))))) =
      (((MeasureTheory.Measure.map (fun x : ℕ → Bool => fun k : Fin t => x k.1)
            (S.branchPathLaw hp)).prod
          (MeasureTheory.Measure.map miniKey
            ((refreshMiniBatchSourceLaw (ι := ι) (B := B)).prod
              (recursiveMiniBatchSourceLaw (ι := ι) (B' := B'))))).prod
        (S.branchPMF hp t).toMeasure).prod
        (MeasureTheory.Measure.pi
          (fun _ : B' => PMF.toMeasure (PMF.uniformOfFintype (α := ι)))) := by
        simpa [shuffle, Line4PastKey] using
          (map_prod_prod_prod_shuffle_eq_prod
            (μ := MeasureTheory.Measure.map
              (fun x : ℕ → Bool => fun k : Fin t => x k.1) (S.branchPathLaw hp))
            (ν := (S.branchPMF hp t).toMeasure)
            (κ := MeasureTheory.Measure.map miniKey
              ((refreshMiniBatchSourceLaw (ι := ι) (B := B)).prod
                (recursiveMiniBatchSourceLaw (ι := ι) (B' := B'))))
            (τ := MeasureTheory.Measure.pi
              (fun _ : B' => PMF.toMeasure (PMF.uniformOfFintype (α := ι)))))
    _ = (MeasureTheory.Measure.map
          (fun y : RandomSource (ι := ι) (B := B) (B' := B') =>
            (randomSourceLine4PastKey S t y, y.1 t))
          (S.randomSourceLaw hp)).prod
        (MeasureTheory.Measure.pi
          (fun _ : B' => PMF.toMeasure (PMF.uniformOfFintype (α := ι)))) := by
        exact congrArg
          (fun μ : MeasureTheory.Measure (Line4PastKey S t × Bool) =>
            μ.prod (MeasureTheory.Measure.pi
              (fun _ : B' => PMF.toMeasure (PMF.uniformOfFintype (α := ι)))))
          hleftLaw.2.2.symm

/-- Transport the source-space finite-key/current-branch product law through
the ambient random-source map. -/
private theorem line4_past_key_branch_pair_bridge [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) (hp : S.RefreshProbabilityDomain)
    (hmap :
      letI : MeasurableSpace ι := ⊤
      MeasureTheory.Measure.map S.randomSourcePath P = S.randomSourceLaw hp)
    (t : ℕ) :
    letI : MeasurableSpace ι := ⊤
    AEMeasurable
        (fun ω : Ω => (line4PastKey S t ω, S.refreshBranch t ω)) P ∧
      MeasureTheory.Measure.map
          (fun ω : Ω => (line4PastKey S t ω, S.refreshBranch t ω)) P =
        (MeasureTheory.Measure.map (fun ω : Ω => line4PastKey S t ω) P).prod
          (S.branchPMF hp t).toMeasure := by
  classical
  letI : MeasurableSpace ι := ⊤
  haveI hsourceProb : MeasureTheory.IsProbabilityMeasure (S.randomSourceLaw hp) := by
    unfold randomSourceLaw branchPathLaw refreshMiniBatchSourceLaw
      recursiveMiniBatchSourceLaw componentUniformMeasure
    infer_instance
  have hY : AEMeasurable S.randomSourcePath P :=
    aemeasurable_of_map_eq_probability_law (P := P) (Y := S.randomSourcePath)
      (μ := S.randomSourceLaw hp) hmap
  have hsourceBridge :=
    random_source_line4_past_key_branch_map_eq_prod (S := S) hp t
  have hpairSourceAEM :
      AEMeasurable
        (fun y : RandomSource (ι := ι) (B := B) (B' := B') =>
          (randomSourceLine4PastKey S t y, y.1 t))
        (MeasureTheory.Measure.map S.randomSourcePath P) := by
    rw [hmap]
    exact hsourceBridge.1
  have hkeySourceAEM :
      AEMeasurable
        (fun y : RandomSource (ι := ι) (B := B) (B' := B') =>
          randomSourceLine4PastKey S t y)
        (MeasureTheory.Measure.map S.randomSourcePath P) := by
    rw [hmap]
    exact hsourceBridge.2.1
  have hpairAEM :
      AEMeasurable
        (fun ω : Ω => (line4PastKey S t ω, S.refreshBranch t ω)) P := by
    simpa [randomSourcePath, line4PastKey, randomSourceLine4PastKey,
      refreshSamplePath, recursiveSamplePath, refreshFinSample, recursiveFinSample,
      Function.comp_def, Equiv.symm_apply_apply]
      using (hpairSourceAEM.comp_aemeasurable hY)
  have hkeyMap :
      MeasureTheory.Measure.map (fun ω : Ω => line4PastKey S t ω) P =
        MeasureTheory.Measure.map
          (fun y : RandomSource (ι := ι) (B := B) (B' := B') =>
            randomSourceLine4PastKey S t y)
          (S.randomSourceLaw hp) := by
    calc
      MeasureTheory.Measure.map (fun ω : Ω => line4PastKey S t ω) P =
          MeasureTheory.Measure.map
            (fun y : RandomSource (ι := ι) (B := B) (B' := B') =>
              randomSourceLine4PastKey S t y)
            (MeasureTheory.Measure.map S.randomSourcePath P) := by
            simpa [randomSourcePath, line4PastKey, randomSourceLine4PastKey,
              refreshSamplePath, recursiveSamplePath, refreshFinSample, recursiveFinSample,
              Function.comp_def, Equiv.symm_apply_apply]
              using (AEMeasurable.map_map_of_aemeasurable hkeySourceAEM hY).symm
      _ = MeasureTheory.Measure.map
            (fun y : RandomSource (ι := ι) (B := B) (B' := B') =>
              randomSourceLine4PastKey S t y)
            (S.randomSourceLaw hp) := by
            rw [hmap]
  have hpairMap :
      MeasureTheory.Measure.map
          (fun ω : Ω => (line4PastKey S t ω, S.refreshBranch t ω)) P =
        MeasureTheory.Measure.map
          (fun y : RandomSource (ι := ι) (B := B) (B' := B') =>
            (randomSourceLine4PastKey S t y, y.1 t))
          (S.randomSourceLaw hp) := by
    calc
      MeasureTheory.Measure.map
          (fun ω : Ω => (line4PastKey S t ω, S.refreshBranch t ω)) P =
        MeasureTheory.Measure.map
          (fun y : RandomSource (ι := ι) (B := B) (B' := B') =>
            (randomSourceLine4PastKey S t y, y.1 t))
          (MeasureTheory.Measure.map S.randomSourcePath P) := by
          simpa [randomSourcePath, line4PastKey, randomSourceLine4PastKey,
            refreshSamplePath, recursiveSamplePath, refreshFinSample, recursiveFinSample,
            Function.comp_def, Equiv.symm_apply_apply]
            using (AEMeasurable.map_map_of_aemeasurable hpairSourceAEM hY).symm
      _ = MeasureTheory.Measure.map
          (fun y : RandomSource (ι := ι) (B := B) (B' := B') =>
            (randomSourceLine4PastKey S t y, y.1 t))
          (S.randomSourceLaw hp) := by
          rw [hmap]
  refine ⟨hpairAEM, ?_⟩
  rw [hpairMap, hkeyMap]
  exact hsourceBridge.2.2

/-- Transport the source-space finite-key/current-branch/current-recursive-row
product law through the ambient random-source map. -/
private theorem line4_past_key_branch_recursive_row_bridge [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) (hp : S.RefreshProbabilityDomain)
    (hmap :
      letI : MeasurableSpace ι := ⊤
      MeasureTheory.Measure.map S.randomSourcePath P = S.randomSourceLaw hp)
    (t : ℕ) :
    letI : MeasurableSpace ι := ⊤
    AEMeasurable
        (fun ω : Ω =>
          ((line4PastKey S t ω, S.refreshBranch t ω),
            fun j : B' => S.recursiveSample t j ω)) P ∧
      AEMeasurable
        (fun ω : Ω => (line4PastKey S t ω, S.refreshBranch t ω)) P ∧
      MeasureTheory.Measure.map
          (fun ω : Ω =>
            ((line4PastKey S t ω, S.refreshBranch t ω),
              fun j : B' => S.recursiveSample t j ω)) P =
        (MeasureTheory.Measure.map
          (fun ω : Ω => (line4PastKey S t ω, S.refreshBranch t ω)) P).prod
          (MeasureTheory.Measure.pi
            (fun _ : B' => PMF.toMeasure (PMF.uniformOfFintype (α := ι)))) := by
  classical
  letI : MeasurableSpace ι := ⊤
  haveI hsourceProb : MeasureTheory.IsProbabilityMeasure (S.randomSourceLaw hp) := by
    unfold randomSourceLaw branchPathLaw refreshMiniBatchSourceLaw
      recursiveMiniBatchSourceLaw componentUniformMeasure
    infer_instance
  have hY : AEMeasurable S.randomSourcePath P :=
    aemeasurable_of_map_eq_probability_law (P := P) (Y := S.randomSourcePath)
      (μ := S.randomSourceLaw hp) hmap
  have hsourceBridge :=
    random_source_line4_past_key_branch_recursive_row_map_eq_prod (S := S) hp t
  have hpairSourceAEM :
      AEMeasurable
        (fun y : RandomSource (ι := ι) (B := B) (B' := B') =>
          ((randomSourceLine4PastKey S t y, y.1 t),
            fun j : B' => y.2.2 t (Fintype.equivFin B' j)))
        (MeasureTheory.Measure.map S.randomSourcePath P) := by
    rw [hmap]
    exact hsourceBridge.1
  have hleftSourceAEM :
      AEMeasurable
        (fun y : RandomSource (ι := ι) (B := B) (B' := B') =>
          (randomSourceLine4PastKey S t y, y.1 t))
        (MeasureTheory.Measure.map S.randomSourcePath P) := by
    rw [hmap]
    exact hsourceBridge.2.1
  have hpairAEM :
      AEMeasurable
        (fun ω : Ω =>
          ((line4PastKey S t ω, S.refreshBranch t ω),
            fun j : B' => S.recursiveSample t j ω)) P := by
    simpa [randomSourcePath, line4PastKey, randomSourceLine4PastKey,
      refreshSamplePath, recursiveSamplePath, refreshFinSample, recursiveFinSample,
      Function.comp_def, Equiv.symm_apply_apply]
      using (hpairSourceAEM.comp_aemeasurable hY)
  have hleftAEM :
      AEMeasurable
        (fun ω : Ω => (line4PastKey S t ω, S.refreshBranch t ω)) P := by
    simpa [randomSourcePath, line4PastKey, randomSourceLine4PastKey,
      refreshSamplePath, recursiveSamplePath, refreshFinSample, recursiveFinSample,
      Function.comp_def, Equiv.symm_apply_apply]
      using (hleftSourceAEM.comp_aemeasurable hY)
  have hleftMap :
      MeasureTheory.Measure.map
          (fun ω : Ω => (line4PastKey S t ω, S.refreshBranch t ω)) P =
        MeasureTheory.Measure.map
          (fun y : RandomSource (ι := ι) (B := B) (B' := B') =>
            (randomSourceLine4PastKey S t y, y.1 t))
          (S.randomSourceLaw hp) := by
    calc
      MeasureTheory.Measure.map
          (fun ω : Ω => (line4PastKey S t ω, S.refreshBranch t ω)) P =
        MeasureTheory.Measure.map
          (fun y : RandomSource (ι := ι) (B := B) (B' := B') =>
            (randomSourceLine4PastKey S t y, y.1 t))
          (MeasureTheory.Measure.map S.randomSourcePath P) := by
          simpa [randomSourcePath, line4PastKey, randomSourceLine4PastKey,
            refreshSamplePath, recursiveSamplePath, refreshFinSample, recursiveFinSample,
            Function.comp_def, Equiv.symm_apply_apply]
            using (AEMeasurable.map_map_of_aemeasurable hleftSourceAEM hY).symm
      _ = MeasureTheory.Measure.map
          (fun y : RandomSource (ι := ι) (B := B) (B' := B') =>
            (randomSourceLine4PastKey S t y, y.1 t))
          (S.randomSourceLaw hp) := by
          rw [hmap]
  have hpairMap :
      MeasureTheory.Measure.map
          (fun ω : Ω =>
            ((line4PastKey S t ω, S.refreshBranch t ω),
              fun j : B' => S.recursiveSample t j ω)) P =
        MeasureTheory.Measure.map
          (fun y : RandomSource (ι := ι) (B := B) (B' := B') =>
            ((randomSourceLine4PastKey S t y, y.1 t),
              fun j : B' => y.2.2 t (Fintype.equivFin B' j)))
          (S.randomSourceLaw hp) := by
    calc
      MeasureTheory.Measure.map
          (fun ω : Ω =>
            ((line4PastKey S t ω, S.refreshBranch t ω),
              fun j : B' => S.recursiveSample t j ω)) P =
        MeasureTheory.Measure.map
          (fun y : RandomSource (ι := ι) (B := B) (B' := B') =>
            ((randomSourceLine4PastKey S t y, y.1 t),
              fun j : B' => y.2.2 t (Fintype.equivFin B' j)))
          (MeasureTheory.Measure.map S.randomSourcePath P) := by
          simpa [randomSourcePath, line4PastKey, randomSourceLine4PastKey,
            refreshSamplePath, recursiveSamplePath, refreshFinSample, recursiveFinSample,
            Function.comp_def, Equiv.symm_apply_apply]
            using (AEMeasurable.map_map_of_aemeasurable hpairSourceAEM hY).symm
      _ = MeasureTheory.Measure.map
          (fun y : RandomSource (ι := ι) (B := B) (B' := B') =>
            ((randomSourceLine4PastKey S t y, y.1 t),
              fun j : B' => y.2.2 t (Fintype.equivFin B' j)))
          (S.randomSourceLaw hp) := by
          rw [hmap]
  refine ⟨hpairAEM, hleftAEM, ?_⟩
  rw [hpairMap, hleftMap]
  exact hsourceBridge.2.2

private theorem process_eq_of_line4_past_key_eq
    (t : ℕ) {ω ω' : Ω}
    (hkey : line4PastKey S t ω = line4PastKey S t ω') :
    S.process t ω = S.process t ω' := by
  classical
  induction t with
  | zero =>
      have hrefresh :
          (fun j : B => S.refreshSample 0 j ω) =
            (fun j : B => S.refreshSample 0 j ω') := by
        have h :=
          congrFun (congrArg (fun k : Line4PastKey S 0 => k.2.1) hkey)
            (⟨0, Nat.zero_lt_one⟩ : Fin 1)
        simpa using h
      by_cases hfull : Fintype.card B = Fintype.card ι
      · change initialState S ω = initialState S ω'
        simp [initialState, initialEstimator, refreshEstimator, hfull]
      · have hg : initialEstimator S ω = initialEstimator S ω' := by
          unfold initialEstimator refreshEstimator
          simp [SOptLib.finiteUniformAverage, hfull]
          have hsum :
              (∑ j : B, S.componentGradient (S.refreshSample 0 j ω) S.x0) =
                ∑ j : B, S.componentGradient (S.refreshSample 0 j ω') S.x0 := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [congrFun hrefresh j]
          exact hsum
        simpa [process, SOptLib.recursive_process_from_random_initial,
          initialState, hg]
  | succ t ih =>
      have hprevKey : line4PastKey S t ω = line4PastKey S t ω' := by
        apply Prod.ext
        · funext k
          have hbranch :=
            congrFun (congrArg (fun k : Line4PastKey S (t + 1) => k.1) hkey)
              (⟨k.1, Nat.lt_trans k.2 (Nat.lt_succ_self t)⟩ : Fin (t + 1))
          simpa [line4PastKey] using hbranch
        · apply Prod.ext
          · funext k j
            have hrefresh :=
              congrFun (congrArg (fun k : Line4PastKey S (t + 1) => k.2.1) hkey)
                (⟨k.1, Nat.lt_trans k.2 (Nat.lt_succ_self (t + 1))⟩ : Fin (t + 2))
            exact congrFun hrefresh j
          · funext k j
            have hrec :=
              congrFun (congrArg (fun k : Line4PastKey S (t + 1) => k.2.2) hkey)
                (⟨k.1, Nat.lt_trans k.2 (Nat.lt_succ_self t)⟩ : Fin (t + 1))
            exact congrFun hrec j
      have hprev : S.process t ω = S.process t ω' := ih hprevKey
      have hbranch :
          S.refreshBranch t ω = S.refreshBranch t ω' := by
        have h :=
          congrFun (congrArg (fun k : Line4PastKey S (t + 1) => k.1) hkey)
            (⟨t, Nat.lt_succ_self t⟩ : Fin (t + 1))
        simpa [line4PastKey] using h
      have hrefresh :
          (fun j : B => S.refreshSample (t + 1) j ω) =
            (fun j : B => S.refreshSample (t + 1) j ω') := by
        have h :=
          congrFun (congrArg (fun k : Line4PastKey S (t + 1) => k.2.1) hkey)
            (⟨t + 1, Nat.lt_succ_self (t + 1)⟩ : Fin (t + 2))
        simpa [line4PastKey] using h
      have hrecursive :
          (fun j : B' => S.recursiveSample t j ω) =
            (fun j : B' => S.recursiveSample t j ω') := by
        have h :=
          congrFun (congrArg (fun k : Line4PastKey S (t + 1) => k.2.2) hkey)
            (⟨t, Nat.lt_succ_self t⟩ : Fin (t + 1))
        simpa [line4PastKey] using h
      have hsucc (ξ : Ω) :
          S.process (t + 1) ξ =
            S.stateUpdate t ξ (S.process t ξ) := by
        simp [process, SOptLib.recursive_process_from_random_initial]
      rw [hsucc ω, hsucc ω']
      rw [hprev]
      simp only [stateUpdate]
      by_cases hbr : S.refreshBranch t ω
      · have hbr' : S.refreshBranch t ω' = true := by simpa [hbr] using hbranch.symm
        by_cases hfull : Fintype.card B = Fintype.card ι
        · simp [estimatorUpdate, hbr, hbr', refreshEstimator, hfull]
        · simp [estimatorUpdate, hbr, hbr', refreshEstimator, SOptLib.finiteUniformAverage, hfull]
          exact Finset.sum_congr rfl (fun j _ => by rw [congrFun hrefresh j])
      · have hbr' : S.refreshBranch t ω' = false := by simpa [hbr] using hbranch.symm
        simp [estimatorUpdate, hbr, hbr', recursiveEstimatorUpdate, hrecursive]

/-- The product random-source law makes the current Line 4 branch independent
of every finite random-source coordinate that can influence `process t`. -/
private theorem line4_past_key_branch_true_measure [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) (h_laws : S.StochasticLaws P)
    (t : ℕ) (K : Set (Line4PastKey S t)) :
    P {ω : Ω | line4PastKey S t ω ∈ K ∧ S.refreshBranch t ω = true} =
      ENNReal.ofReal (S.refreshProbability t) *
        P {ω : Ω | line4PastKey S t ω ∈ K} := by
  classical
  unfold StochasticLaws at h_laws
  letI : MeasurableSpace ι := ⊤
  rcases h_laws with ⟨hp, hmap⟩
  have hpairBridge :
      AEMeasurable
        (fun ω : Ω => (line4PastKey S t ω, S.refreshBranch t ω)) P ∧
      MeasureTheory.Measure.map
          (fun ω : Ω => (line4PastKey S t ω, S.refreshBranch t ω)) P =
        (MeasureTheory.Measure.map (fun ω : Ω => line4PastKey S t ω) P).prod
          (S.branchPMF hp t).toMeasure := by
    exact line4_past_key_branch_pair_bridge (S := S) P hp hmap t
  have hpairAEM :
      AEMeasurable
        (fun ω : Ω => (line4PastKey S t ω, S.refreshBranch t ω)) P :=
    hpairBridge.1
  have hkeyAEM :
      AEMeasurable (fun ω : Ω => line4PastKey S t ω) P := hpairAEM.fst
  have hpairMap :
      MeasureTheory.Measure.map
          (fun ω : Ω => (line4PastKey S t ω, S.refreshBranch t ω)) P =
        (MeasureTheory.Measure.map (fun ω : Ω => line4PastKey S t ω) P).prod
          (S.branchPMF hp t).toMeasure := by
    exact hpairBridge.2
  have hK : MeasurableSet K := by
    exact measurableSet_line4PastKey_of_fintype (S := S) t K
  have hrect : MeasurableSet (K ×ˢ ({true} : Set Bool)) :=
    hK.prod (measurableSet_singleton true)
  calc
    P {ω : Ω | line4PastKey S t ω ∈ K ∧ S.refreshBranch t ω = true}
        = MeasureTheory.Measure.map
            (fun ω : Ω => (line4PastKey S t ω, S.refreshBranch t ω)) P
            (K ×ˢ ({true} : Set Bool)) := by
          rw [MeasureTheory.Measure.map_apply_of_aemeasurable hpairAEM hrect]
          rfl
    _ = ((MeasureTheory.Measure.map (fun ω : Ω => line4PastKey S t ω) P).prod
          (S.branchPMF hp t).toMeasure) (K ×ˢ ({true} : Set Bool)) := by
          rw [hpairMap]
    _ = MeasureTheory.Measure.map (fun ω : Ω => line4PastKey S t ω) P K *
          (S.branchPMF hp t).toMeasure ({true} : Set Bool) := by
          rw [MeasureTheory.Measure.prod_prod]
    _ = P {ω : Ω | line4PastKey S t ω ∈ K} *
          ENNReal.ofReal (S.refreshProbability t) := by
          rw [MeasureTheory.Measure.map_apply_of_aemeasurable hkeyAEM hK]
          rw [PMF.toMeasure_apply_singleton (S.branchPMF hp t) true
            (measurableSet_singleton true)]
          simp [Set.preimage, branchPMF, ENNReal.coe_nnreal_eq]
    _ = ENNReal.ofReal (S.refreshProbability t) *
          P {ω : Ω | line4PastKey S t ω ∈ K} := by
          rw [mul_comm]

/-- The current recursive row is uniform even after conditioning on a finite
Line 4 past key and the recursive branch event. -/
private theorem line4_past_key_branch_recursive_vector_measure [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) (h_laws : S.StochasticLaws P)
    (t : ℕ) (K : Set (Line4PastKey S t)) (recursiveVector : B' → ι) :
    P {ω : Ω |
        line4PastKey S t ω ∈ K ∧
          S.refreshBranch t ω = false ∧
          ∀ j : B', S.recursiveSample t j ω = recursiveVector j} =
      ENNReal.ofReal ((Fintype.card (B' → ι) : ℝ)⁻¹) *
        P {ω : Ω |
          line4PastKey S t ω ∈ K ∧ S.refreshBranch t ω = false} := by
  classical
  unfold StochasticLaws at h_laws
  letI : MeasurableSpace ι := ⊤
  rcases h_laws with ⟨hp, hmap⟩
  have hbridge :=
    line4_past_key_branch_recursive_row_bridge (S := S) P hp hmap t
  have hpairAEM :
      AEMeasurable
        (fun ω : Ω =>
          ((line4PastKey S t ω, S.refreshBranch t ω),
            fun j : B' => S.recursiveSample t j ω)) P :=
    hbridge.1
  have hleftAEM :
      AEMeasurable
        (fun ω : Ω => (line4PastKey S t ω, S.refreshBranch t ω)) P :=
    hbridge.2.1
  have hpairMap :
      MeasureTheory.Measure.map
          (fun ω : Ω =>
            ((line4PastKey S t ω, S.refreshBranch t ω),
              fun j : B' => S.recursiveSample t j ω)) P =
        (MeasureTheory.Measure.map
          (fun ω : Ω => (line4PastKey S t ω, S.refreshBranch t ω)) P).prod
          (MeasureTheory.Measure.pi
            (fun _ : B' => PMF.toMeasure (PMF.uniformOfFintype (α := ι)))) :=
    hbridge.2.2
  have hK : MeasurableSet K := by
    exact measurableSet_line4PastKey_of_fintype (S := S) t K
  have hleftSet : MeasurableSet (K ×ˢ ({false} : Set Bool)) :=
    hK.prod (measurableSet_singleton false)
  have hrect :
      MeasurableSet
        ((K ×ˢ ({false} : Set Bool)) ×ˢ
          ({recursiveVector} : Set (B' → ι))) :=
    hleftSet.prod (measurableSet_singleton recursiveVector)
  calc
    P {ω : Ω |
        line4PastKey S t ω ∈ K ∧
          S.refreshBranch t ω = false ∧
          ∀ j : B', S.recursiveSample t j ω = recursiveVector j}
        =
      MeasureTheory.Measure.map
          (fun ω : Ω =>
            ((line4PastKey S t ω, S.refreshBranch t ω),
              fun j : B' => S.recursiveSample t j ω)) P
          ((K ×ˢ ({false} : Set Bool)) ×ˢ
            ({recursiveVector} : Set (B' → ι))) := by
          rw [MeasureTheory.Measure.map_apply_of_aemeasurable hpairAEM hrect]
          simp [Set.preimage, funext_iff, and_assoc]
    _ = ((MeasureTheory.Measure.map
          (fun ω : Ω => (line4PastKey S t ω, S.refreshBranch t ω)) P).prod
          (MeasureTheory.Measure.pi
            (fun _ : B' => PMF.toMeasure (PMF.uniformOfFintype (α := ι)))))
          ((K ×ˢ ({false} : Set Bool)) ×ˢ
            ({recursiveVector} : Set (B' → ι))) := by
          rw [hpairMap]
    _ = MeasureTheory.Measure.map
          (fun ω : Ω => (line4PastKey S t ω, S.refreshBranch t ω)) P
          (K ×ˢ ({false} : Set Bool)) *
        (MeasureTheory.Measure.pi
          (fun _ : B' => PMF.toMeasure (PMF.uniformOfFintype (α := ι))))
          ({recursiveVector} : Set (B' → ι)) := by
          rw [MeasureTheory.Measure.prod_prod]
    _ = MeasureTheory.Measure.map
          (fun ω : Ω => (line4PastKey S t ω, S.refreshBranch t ω)) P
          (K ×ˢ ({false} : Set Bool)) *
        ENNReal.ofReal ((Fintype.card (B' → ι) : ℝ)⁻¹) := by
          rw [uniform_pi_singleton_mass (A := ι) (C := B') recursiveVector]
    _ = ENNReal.ofReal ((Fintype.card (B' → ι) : ℝ)⁻¹) *
        P {ω : Ω |
          line4PastKey S t ω ∈ K ∧ S.refreshBranch t ω = false} := by
          rw [MeasureTheory.Measure.map_apply_of_aemeasurable hleftAEM hleftSet]
          simp [Set.preimage, mul_comm]

/-- The product random-source law gives the one-step Line 4 branch/minibatch law
used to expand the estimator distribution. This is derived from the canonical
Algorithm 1 random-source law, not listed as a primitive stochastic contract. -/
theorem line4EstimatorLaw_of_stochasticLaws [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) (h_laws : S.StochasticLaws P) :
    S.Line4EstimatorLaw P := by
  classical
  have hbranchLaw := S.refreshBranchLaw_of_stochasticLaws P h_laws
  unfold StochasticLaws at h_laws
  letI : MeasurableSpace ι := ⊤
  rcases h_laws with ⟨hp, hmap⟩
  have hrefreshBranchVector :=
    refresh_branch_active_vector_map_eq_prod (S := S) P hp hmap
  have hrecursiveBranchVector :=
    recursive_branch_active_vector_map_eq_prod (S := S) P hp hmap
  unfold Line4EstimatorLaw
  intro t useRefresh refreshVector recursiveVector
  cases useRefresh with
  | false =>
      simp
      have hpairAEM : AEMeasurable
          (fun ω : Ω => (S.refreshBranch t ω, fun j : B' => S.recursiveSample t j ω)) P := by
        exact aemeasurable_of_map_eq_probability_law (P := P)
          (Y := fun ω : Ω => (S.refreshBranch t ω, fun j : B' => S.recursiveSample t j ω))
          (μ := (S.branchPMF hp t).toMeasure.prod
            (MeasureTheory.Measure.pi fun _ : B' =>
              (PMF.uniformOfFintype (α := ι)).toMeasure))
          (hrecursiveBranchVector t)
      have hmass :=
        measure_preimage_singleton_eq_of_map_eq (P := P)
          (Y := fun ω : Ω => (S.refreshBranch t ω, fun j : B' => S.recursiveSample t j ω))
          (mu := (S.branchPMF hp t).toMeasure.prod
            (MeasureTheory.Measure.pi fun _ : B' =>
              (PMF.uniformOfFintype (α := ι)).toMeasure))
          (false, recursiveVector) hpairAEM (hrecursiveBranchVector t)
      have hprod :
          ((S.branchPMF hp t).toMeasure.prod
            (MeasureTheory.Measure.pi fun _ : B' =>
              (PMF.uniformOfFintype (α := ι)).toMeasure))
              ({(false, recursiveVector)} : Set (Bool × (B' → ι))) =
            ENNReal.ofReal ((1 - S.refreshProbability t) *
              ((Fintype.card (B' → ι) : ℝ)⁻¹)) := by
        have hset : ({(false, recursiveVector)} : Set (Bool × (B' → ι))) =
            ({false} : Set Bool) ×ˢ ({recursiveVector} : Set (B' → ι)) := by
          ext x
          cases x
          simp
        rw [hset, MeasureTheory.Measure.prod_prod]
        rw [PMF.toMeasure_apply_singleton (S.branchPMF hp t) false
          (measurableSet_singleton false)]
        rw [uniform_pi_singleton_mass (A := ι) (C := B') recursiveVector]
        simp only [branchPMF, PMF.bernoulli_apply, Bool.cond_false]
        rw [ENNReal.ofReal_mul (sub_nonneg.mpr (hp t).2)]
        congr 1
      rw [hprod] at hmass
      simpa [Set.preimage, funext_iff] using hmass
  | true =>
      simp
      by_cases hfull : Fintype.card B = Fintype.card ι
      · simpa [hfull] using hbranchLaw t
      · have hpairAEM : AEMeasurable
            (fun ω : Ω => (S.refreshBranch t ω, fun j : B =>
              S.refreshSample (t + 1) j ω)) P := by
          exact aemeasurable_of_map_eq_probability_law (P := P)
            (Y := fun ω : Ω => (S.refreshBranch t ω, fun j : B =>
              S.refreshSample (t + 1) j ω))
            (μ := (S.branchPMF hp t).toMeasure.prod
              (MeasureTheory.Measure.pi fun _ : B =>
                (PMF.uniformOfFintype (α := ι)).toMeasure))
            (hrefreshBranchVector t)
        have hmass :=
          measure_preimage_singleton_eq_of_map_eq (P := P)
            (Y := fun ω : Ω => (S.refreshBranch t ω, fun j : B =>
              S.refreshSample (t + 1) j ω))
            (mu := (S.branchPMF hp t).toMeasure.prod
              (MeasureTheory.Measure.pi fun _ : B =>
                (PMF.uniformOfFintype (α := ι)).toMeasure))
            (true, refreshVector) hpairAEM (hrefreshBranchVector t)
        have hprod :
            ((S.branchPMF hp t).toMeasure.prod
              (MeasureTheory.Measure.pi fun _ : B =>
                (PMF.uniformOfFintype (α := ι)).toMeasure))
                ({(true, refreshVector)} : Set (Bool × (B → ι))) =
              ENNReal.ofReal (S.refreshProbability t *
                ((Fintype.card (B → ι) : ℝ)⁻¹)) := by
          have hset : ({(true, refreshVector)} : Set (Bool × (B → ι))) =
              ({true} : Set Bool) ×ˢ ({refreshVector} : Set (B → ι)) := by
            ext x
            cases x
            simp
          rw [hset, MeasureTheory.Measure.prod_prod]
          rw [PMF.toMeasure_apply_singleton (S.branchPMF hp t) true
            (measurableSet_singleton true)]
          rw [uniform_pi_singleton_mass (A := ι) (C := B) refreshVector]
          simp [branchPMF, ENNReal.coe_nnreal_eq, ENNReal.ofReal_mul, (hp t).1.le]
        rw [hprod] at hmass
        simpa [Set.preimage, hfull, funext_iff] using hmass

/-- Derived Line 4 branch-freshness obligation used by the variance-recursion
proof. It is intentionally not a field of `StochasticLaws` and therefore not a
paper-facing Theorem 1 hypothesis.

Book/PDF citation: Algorithm 1 states Line 4 branch probabilities; Lemma 3's
proof uses the resulting branch expansion in Eq. (16)-(17). The PDF does not
state this conditional event law as an assumption. -/
theorem line4BranchFreshGivenState_of_stochasticLaws [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) (h_laws : S.StochasticLaws P) :
    S.Line4BranchFreshGivenState P := by
  classical
  unfold Line4BranchFreshGivenState
  intro t pastEvent
  let K : Set (Line4PastKey S t) :=
    {k | ∃ ω : Ω, line4PastKey S t ω = k ∧ S.process t ω ∈ pastEvent}
  have hfactor :
      {ω : Ω | S.process t ω ∈ pastEvent} =
        {ω : Ω | line4PastKey S t ω ∈ K} := by
    ext ω
    constructor
    · intro hpast
      exact ⟨ω, rfl, hpast⟩
    · rintro ⟨ω', hkey, hpast⟩
      have hproc :
          S.process t ω = S.process t ω' :=
        process_eq_of_line4_past_key_eq (S := S) t hkey.symm
      simpa [hproc] using hpast
  have hfactor_branch :
      {ω : Ω | S.process t ω ∈ pastEvent ∧ S.refreshBranch t ω = true} =
        {ω : Ω | line4PastKey S t ω ∈ K ∧ S.refreshBranch t ω = true} := by
    ext ω
    have hmem :
        S.process t ω ∈ pastEvent ↔ line4PastKey S t ω ∈ K := by
      simpa using congrArg (fun s : Set Ω => ω ∈ s) hfactor
    constructor
    · intro h
      exact ⟨hmem.mp h.1, h.2⟩
    · intro h
      exact ⟨hmem.mpr h.1, h.2⟩
  calc
    P {ω : Ω | S.process t ω ∈ pastEvent ∧ S.refreshBranch t ω = true}
        = P {ω : Ω | line4PastKey S t ω ∈ K ∧ S.refreshBranch t ω = true} := by
          rw [hfactor_branch]
    _ = ENNReal.ofReal (S.refreshProbability t) *
          P {ω : Ω | line4PastKey S t ω ∈ K} := by
          exact line4_past_key_branch_true_measure (S := S) P h_laws t K
    _ = ENNReal.ofReal (S.refreshProbability t) *
          P {ω : Ω | S.process t ω ∈ pastEvent} := by
          rw [hfactor]

/-- Derived recursive-minibatch freshness obligation used by Lemma 3's centered
mini-batch calculation. It is kept out of the source-facing stochastic-law
contract because Algorithm 1 only states random mini-batches and branch
probabilities.

Book/PDF citation: Algorithm 1 Line 4 gives the recursive mini-batch `I'`;
Lemma 3 uses it in the expectation calculation around Eq. (16)-(18), but the
PDF does not list this conditional event law as a theorem assumption. -/
theorem recursiveSampleFreshGivenLine4Past_of_stochasticLaws [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) (h_laws : S.StochasticLaws P) :
    S.RecursiveSampleFreshGivenLine4Past P := by
  classical
  unfold RecursiveSampleFreshGivenLine4Past
  intro t pastEvent recursiveVector
  let K : Set (Line4PastKey S t) :=
    {k | ∃ ω : Ω, line4PastKey S t ω = k ∧ S.process t ω ∈ pastEvent}
  have hfactor :
      {ω : Ω | S.process t ω ∈ pastEvent} =
        {ω : Ω | line4PastKey S t ω ∈ K} := by
    ext ω
    constructor
    · intro hpast
      exact ⟨ω, rfl, hpast⟩
    · rintro ⟨ω', hkey, hpast⟩
      have hproc :
          S.process t ω = S.process t ω' :=
        process_eq_of_line4_past_key_eq (S := S) t hkey.symm
      simpa [hproc] using hpast
  have hfactor_false :
      {ω : Ω | S.process t ω ∈ pastEvent ∧ S.refreshBranch t ω = false} =
        {ω : Ω | line4PastKey S t ω ∈ K ∧ S.refreshBranch t ω = false} := by
    ext ω
    have hmem :
        S.process t ω ∈ pastEvent ↔ line4PastKey S t ω ∈ K := by
      simpa using congrArg (fun s : Set Ω => ω ∈ s) hfactor
    constructor
    · intro h
      exact ⟨hmem.mp h.1, h.2⟩
    · intro h
      exact ⟨hmem.mpr h.1, h.2⟩
  have hfactor_vector :
      {ω : Ω |
        S.process t ω ∈ pastEvent ∧
          S.refreshBranch t ω = false ∧
          ∀ j : B', S.recursiveSample t j ω = recursiveVector j} =
        {ω : Ω |
          line4PastKey S t ω ∈ K ∧
            S.refreshBranch t ω = false ∧
            ∀ j : B', S.recursiveSample t j ω = recursiveVector j} := by
    ext ω
    have hmem :
        S.process t ω ∈ pastEvent ↔ line4PastKey S t ω ∈ K := by
      simpa using congrArg (fun s : Set Ω => ω ∈ s) hfactor
    constructor
    · intro h
      exact ⟨hmem.mp h.1, h.2⟩
    · intro h
      exact ⟨hmem.mpr h.1, h.2⟩
  calc
    P {ω : Ω |
        S.process t ω ∈ pastEvent ∧
          S.refreshBranch t ω = false ∧
          ∀ j : B', S.recursiveSample t j ω = recursiveVector j}
        =
      P {ω : Ω |
        line4PastKey S t ω ∈ K ∧
          S.refreshBranch t ω = false ∧
          ∀ j : B', S.recursiveSample t j ω = recursiveVector j} := by
        rw [hfactor_vector]
    _ = ENNReal.ofReal ((Fintype.card (B' → ι) : ℝ)⁻¹) *
          P {ω : Ω |
            line4PastKey S t ω ∈ K ∧ S.refreshBranch t ω = false} := by
        exact line4_past_key_branch_recursive_vector_measure
          (S := S) P h_laws t K recursiveVector
    _ = ENNReal.ofReal ((Fintype.card (B' → ι) : ℝ)⁻¹) *
          P {ω : Ω |
            S.process t ω ∈ pastEvent ∧ S.refreshBranch t ω = false} := by
        rw [hfactor_false]

@[simp]
theorem objective_def (x : E) :
    S.objective x =
      SOptLib.finiteUniformAverage (fun i : ι => S.componentObjective i x) := by
  rfl

@[simp]
theorem componentGradient_def (i : ι) (x : E) :
    S.componentGradient i x = ∇ (S.componentObjective i) x := by
  rfl

@[simp]
theorem fullGradient_def (x : E) :
    S.fullGradient x = ∇ S.objective x := by
  rfl

@[simp]
theorem componentAverageGradient_def (x : E) :
    S.componentAverageGradient x =
      SOptLib.finiteUniformAverage (fun i : ι => S.componentGradient i x) := by
  rfl

/-- The named full gradient is definitionally Mathlib's gradient of the named
finite-sum objective. -/
theorem gradient_objective_eq_fullGradient (x : E) :
    ∇ S.objective x = S.fullGradient x := by
  rfl

/-- The average of component gradients agrees with the full objective gradient
when the component gradient selectors are justified by component
`HasGradientAt` facts. -/
theorem fullGradient_eq_componentAverageGradient (x : E)
    (h_components :
      ∀ i : ι, HasGradientAt (S.componentObjective i) (S.componentGradient i x) x) :
    S.fullGradient x = S.componentAverageGradient x := by
  rw [fullGradient, componentAverageGradient]
  rw [show S.objective = SOptLib.finiteUniformAverage S.componentObjective by
    funext y
    simp [objective, SOptLib.finiteUniformAverage]]
  exact
    SOptLib.gradient_finiteUniformAverage_eq_finiteUniformAverage_gradient
      S.componentObjective S.componentGradient x h_components

@[simp]
theorem fStar_def :
    S.fStar =
      SOptLib.objectiveInfimumValue Set.univ S.objective := by
  rfl

/-- The setup-level realization of the paper's `f^* := min_x f(x)` boundary. -/
theorem objective_bddBelow :
    BddBelow (S.objective '' (Set.univ : Set E)) := by
  simpa [objective] using S.h_objective_bddBelow

/-- Infimum lower-bound projection for the paper notation `f^*`, conditional
on the explicit setup/source lower-bound contract. -/
theorem fStar_le_objective_of_bddBelow
    (h_boundary : BddBelow (S.objective '' (Set.univ : Set E))) (x : E) :
    S.fStar ≤ S.objective x := by
  rw [fStar]
  exact
    SOptLib.objectiveInfimumValue_le
      h_boundary (Set.mem_univ x)

/-- Public lower-bound projection from the source/setup minimum-value
contract. -/
theorem fStar_le_objective (x : E) :
    S.fStar ≤ S.objective x :=
  S.fStar_le_objective_of_bddBelow S.objective_bddBelow x

theorem refreshEstimator_fullBatch
    {t : ℕ} {ω : Ω} {x : E} (h_full : Fintype.card B = Fintype.card ι) :
    S.refreshEstimator t ω x = S.fullGradient x := by
  simp [refreshEstimator, h_full]

theorem refreshEstimator_minibatch
    {t : ℕ} {ω : Ω} {x : E} (h_not_full : Fintype.card B ≠ Fintype.card ι) :
    S.refreshEstimator t ω x = SOptLib.finiteUniformAverage (fun j : B => S.componentGradient (S.refreshSample t j ω) x) := by
  simp [refreshEstimator, h_not_full]

@[simp]
theorem initialEstimator_def (ω : Ω) :
    initialEstimator S ω = refreshEstimator S 0 ω S.x0 := by
  rfl

theorem initialEstimator_fullBatch
    {ω : Ω} (h_full : Fintype.card B = Fintype.card ι) :
    initialEstimator S ω = S.fullGradient S.x0 := by
  simp [initialEstimator, refreshEstimator, h_full]

@[simp]
theorem primalUpdate_def (x g : E) :
    S.primalUpdate x g = x - S.η • g := by
  rfl

@[simp]
theorem recursiveEstimatorUpdate_def
    (t : ℕ) (ω : Ω) (gPrev xPrev xCurr : E) :
    recursiveEstimatorUpdate S t ω gPrev xPrev xCurr =
      SOptLib.recursiveGradientDifferenceAverage
        (fun x i => S.componentGradient i x)
        gPrev xPrev xCurr
        (fun j : B' => S.recursiveSample t j ω) := by
  rfl

theorem estimatorUpdate_refresh
    {t : ℕ} {ω : Ω} (h : S.refreshBranch t ω = true)
    (gPrev xPrev xCurr : E) :
    estimatorUpdate S t ω gPrev xPrev xCurr =
      refreshEstimator S (t + 1) ω xCurr := by
  simp [estimatorUpdate, h]

theorem estimatorUpdate_recursive
    {t : ℕ} {ω : Ω} (h : S.refreshBranch t ω = false)
    (gPrev xPrev xCurr : E) :
    estimatorUpdate S t ω gPrev xPrev xCurr =
      recursiveEstimatorUpdate S t ω gPrev xPrev xCurr := by
  simp [estimatorUpdate, h]

@[simp]
theorem process_zero :
    S.process 0 = fun ω => initialState S ω := by
  rfl

@[simp]
theorem process_succ (t : ℕ) :
    S.process (t + 1) = fun ω => stateUpdate S t ω (S.process t ω) := by
  simp [process, SOptLib.recursive_process_from_random_initial]

@[simp]
theorem iterate_zero (ω : Ω) :
    S.iterate 0 ω = S.x0 := by
  rfl

@[simp]
theorem estimator_zero (ω : Ω) :
    S.estimator 0 ω = initialEstimator S ω := by
  rfl

theorem iterate_succ (t : ℕ) (ω : Ω) :
    S.iterate (t + 1) ω =
      primalUpdate S (S.iterate t ω) (S.estimator t ω) := by
  simp [iterate, estimator, stateUpdate]

theorem estimator_succ (t : ℕ) (ω : Ω) :
    S.estimator (t + 1) ω =
      estimatorUpdate S t ω
        (S.estimator t ω) (S.iterate t ω) (S.iterate (t + 1) ω) := by
  simp [iterate, estimator, stateUpdate]

theorem iterate_succ_eq_sub_eta_smul (t : ℕ) (ω : Ω) :
    S.iterate (t + 1) ω = S.iterate t ω - S.η • S.estimator t ω := by
  simpa [primalUpdate] using S.iterate_succ t ω

@[simp]
theorem uniformOutput_def (T : ℕ) (k : Fin T) (ω : Ω) :
    S.uniformOutput T k ω = S.iterate k.val ω := by
  rfl

@[simp]
theorem outputIndexLaw_def (T : ℕ) [NeZero T] :
    outputIndexLaw (T := T) = PMF.uniformOfFintype (Fin T) := by
  rfl

@[simp]
theorem outputJointLaw_def [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) (T : ℕ) [NeZero T] :
    outputJointLaw P T =
      SOptLib.selected_joint_measure (outputIndexLaw T) P := by
  rfl

@[simp]
theorem selectedGradientNormIntegrand_def [MeasurableSpace Ω]
    (T : ℕ) [NeZero T] (q : Fin T × Ω) :
    S.selectedGradientNormIntegrand T q =
      ‖S.fullGradient (S.uniformOutput T q.1 q.2)‖ := by
  rfl

theorem expectedSelectedGradientNorm_of_integrable [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) (T : ℕ) [NeZero T]
    (h_int : S.SelectedGradientNormIntegrable P T) :
    S.expectedSelectedGradientNorm P T =
      ∫ q : Fin T × Ω, S.selectedGradientNormIntegrand T q ∂ outputJointLaw P T := by
  rw [expectedSelectedGradientNorm]
  simp [h_int]

/-- Assumption 2: average `L`-smoothness of component gradients.

Book citation: `book/research/PAGE.json#/assumptions/1`: `E_i[||∇f_i(x)-
∇f_i(y)||^2] <= L^2||x-y||^2, for all x,y∈R^d`. -/
def AverageLSmooth (L : ℝ) : Prop :=
  SOptLib.FiniteAverageSquaredGradientSmoothness
    S.componentObjective S.componentGradient L

theorem averageLSmooth_fullGradient_eq_componentAverageGradient
    {L : ℝ} (hL : S.AverageLSmooth L) (x : E) :
    S.fullGradient x = S.componentAverageGradient x :=
  S.fullGradient_eq_componentAverageGradient x (fun i => hL.2.1 i x)

                                                                         
         

                                                                        
                                     
def BoundedVariance (σ : ℝ) : Prop :=
  0 < σ ∧
    ∀ x : E,
      SOptLib.finiteUniformAverage
          (fun i : ι => ‖S.componentGradient i x - S.fullGradient x‖ ^ 2) ≤ σ ^ 2

                                               

                                                                        
                                

                                                                             

                                                              
                                                       
/-- Literal reading of Theorem 1 / Eq. (20): the stepsize is only upper-bounded.

This predicate is kept separate from `TheoremOneSchedule` because the displayed
iteration count in Eq. (24) uses the stronger identity
`T = 2 * Delta0 / (epsilon^2 * eta) = ...`, which is not implied by the
upper-bound-only schedule for smaller positive `eta`. -/
def TheoremOneUpperBoundSchedule (L p : ℝ) : Prop :=
  0 < S.η ∧
    S.η ≤ (L * (1 + Real.sqrt ((1 - p) / (p * (Fintype.card B' : ℝ)))))⁻¹ ∧
    Fintype.card B = Fintype.card ι ∧
    Fintype.card B' < Fintype.card B ∧
    (∀ t : ℕ, S.refreshProbability t = p) ∧
    0 < p ∧ p ≤ 1

/-- Corrected maximal-stepsize regime used by the displayed Theorem 1 count.

Source boundary note: `book/research/PAGE.json#/assumptions/7` and the theorem
statement record Eq. (20) as `eta <= ...`, while
`book/research/PAGE.json#/main_theorem/proof/12` and `paper/PAGE.pdf` Eq. (24)
use the equality `T = 2 Delta0 / (epsilon^2 eta) = ...`. The public theorem
uses this maximal-step regime so the displayed L-based count is the
eta-dependent horizon required by Eq. (23). -/
def TheoremOneMaximalStepsizeSchedule (L p : ℝ) : Prop :=
  0 < S.η ∧
    S.η = (L * (1 + Real.sqrt ((1 - p) / (p * (Fintype.card B' : ℝ)))))⁻¹ ∧
    Fintype.card B = Fintype.card ι ∧
    Fintype.card B' < Fintype.card B ∧
    (∀ t : ℕ, S.refreshProbability t = p) ∧
    0 < p ∧ p ≤ 1

/-- The part of Theorem 1's maximal schedule used by the Lyapunov/output
estimate.

This keeps the strict `b' < b` condition out of the reusable proof machinery:
the strict branch still supplies `TheoremOneSchedule`, while the Corollary 2
unit boundary can replay the same Eq. (14)--(24) output route from the
maximal stepsize, full-batch, and probability identities that the algebra
actually consumes. -/
def TheoremOneOutputSchedule (L p : ℝ) : Prop :=
  0 < S.η ∧
    S.η = (L * (1 + Real.sqrt ((1 - p) / (p * (Fintype.card B' : ℝ)))))⁻¹ ∧
    Fintype.card B = Fintype.card ι ∧
    (∀ t : ℕ, S.refreshProbability t = p) ∧
    0 < p ∧ p ≤ 1

/-- Theorem 1's compiled schedule interface: the corrected maximal-stepsize
regime needed for the paper's displayed iteration-count formula. -/
def TheoremOneSchedule (L p : ℝ) : Prop :=
  S.TheoremOneMaximalStepsizeSchedule L p

theorem theoremOneSchedule_outputSchedule {L p : ℝ}
    (h_schedule : S.TheoremOneSchedule L p) :
    S.TheoremOneOutputSchedule L p := by
  refine ⟨h_schedule.1, h_schedule.2.1, h_schedule.2.2.1, ?_, ?_, ?_⟩
  · exact h_schedule.2.2.2.2.1
  · exact h_schedule.2.2.2.2.2.1
  · exact h_schedule.2.2.2.2.2.2

theorem theoremOneMaximalStepsizeSchedule_upperBound {L p : ℝ}
    (h_schedule : S.TheoremOneMaximalStepsizeSchedule L p) :
    S.TheoremOneUpperBoundSchedule L p := by
  refine ⟨h_schedule.1, le_of_eq h_schedule.2.1, ?_, ?_, ?_, ?_, ?_⟩
  · exact h_schedule.2.2.1
  · exact h_schedule.2.2.2.1
  · exact h_schedule.2.2.2.2.1
  · exact h_schedule.2.2.2.2.2.1
  · exact h_schedule.2.2.2.2.2.2

theorem theoremOneSchedule_stepsize_le {L p : ℝ}
    (h_schedule : S.TheoremOneSchedule L p) :
    S.η ≤ (L * (1 + Real.sqrt ((1 - p) / (p * (Fintype.card B' : ℝ)))))⁻¹ := by
  exact (S.theoremOneMaximalStepsizeSchedule_upperBound h_schedule).2.1

/-- Scalar obstruction for the literal Eq. (20) schedule.

The concrete values below satisfy a positive upper-bound-only stepsize rule and
the displayed L-based iteration count, but fail the eta-dependent condition
needed to turn Eq. (23) into an `epsilon` bound. This is the formal correction
artifact justifying why `TheoremOneSchedule` above is the maximal-step regime
rather than the literal upper-bound-only predicate. -/
theorem theoremOne_upperBoundSchedule_scalar_obstruction :
    ∃ η Δ L p b ε T : ℝ,
      0 < η ∧
        η ≤ (L * (1 + Real.sqrt ((1 - p) / (p * b))))⁻¹ ∧
        0 < Δ ∧ 0 < L ∧ 0 < p ∧ p ≤ 1 ∧ 0 < b ∧ 0 < ε ∧
        2 * Δ * L / ε ^ 2 * (1 + Real.sqrt ((1 - p) / (p * b))) ≤ T ∧
        ¬ 2 * Δ / (η * T) ≤ ε ^ 2 := by
  refine ⟨(1 : ℝ) / 1000, (1 : ℝ) / 2, 1, 1, 1, (1 : ℝ) / 10, 100, ?_⟩
  norm_num [Real.sqrt_zero]

                                        

                                                                    
               
noncomputable def initialGap : ℝ :=
  S.objective S.x0 - S.fStar

private theorem initialGap_nonneg
    (h_boundary : BddBelow (S.objective '' (Set.univ : Set E))) :
    0 ≤ S.initialGap := by
  dsimp [initialGap]
  exact sub_nonneg.mpr
    (S.fStar_le_objective_of_bddBelow h_boundary S.x0)

                                                                      

                                                                           
                                                      
noncomputable def theoremOneIterationCount (L p ε : ℝ) : ℝ :=
  2 * S.initialGap * L / ε ^ 2 *
    (1 + Real.sqrt ((1 - p) / (p * (Fintype.card B' : ℝ))))

                                                                            

                                                                      
                               
noncomputable def theoremOneGradientComplexity (L p ε : ℝ) : ℝ :=
  (Fintype.card B : ℝ) +
    S.theoremOneIterationCount L p ε *
      (p * (Fintype.card B : ℝ) + (1 - p) * (Fintype.card B' : ℝ))

                                                                    
                                                                    

                                                                            
                                                                             
                      
theorem estimatorUpdate_line4 (t : ℕ) (ω : Ω) (gPrev xPrev xCurr : E) :
    estimatorUpdate S t ω gPrev xPrev xCurr =
      if S.refreshBranch t ω then
        refreshEstimator S (t + 1) ω xCurr
      else
        recursiveEstimatorUpdate S t ω gPrev xPrev xCurr := by
  rfl

theorem finite_uniform_average_norm_sq_le_average_sq_norm
    (v : ι → E) :
    ‖SOptLib.finiteUniformAverage v‖ ^ 2 ≤
      SOptLib.finiteUniformAverage (fun i : ι => ‖v i‖ ^ 2) := by
  classical
  have hcard_pos_nat : 0 < Fintype.card ι := Fintype.card_pos
  have hcard_pos : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast hcard_pos_nat
  have hJ :=
    norm_sq_weighted_average_sub_le_inv_mul_sum
      (s := (Finset.univ : Finset ι))
      (γ := fun _ : ι => (1 : ℝ))
      (p := v)
      (xbar := SOptLib.finiteUniformAverage v)
      (z := (0 : E))
      (W := (Fintype.card ι : ℝ))
      (by intro i hi; norm_num)
      hcard_pos
      (by simp)
      (by simp [SOptLib.finiteUniformAverage_def])
  simpa [SOptLib.finiteUniformAverage_def] using hJ

/-- Lemma 1 obligation: average smoothness implies ordinary smoothness of the
finite-sum objective. The proof is source-derived and belongs after the object
layer, not as a setup field.

Book citation: `book/research/PAGE.json#/key_lemmas/0`: if Assumption 2 holds,
then `f is also L-smooth`, including `||∇f(x)-∇f(y)|| <= L||x-y||`. -/
theorem averageLSmooth_implies_fullGradient_lipschitz
    {L : ℝ} (hL : S.AverageLSmooth L) :
    ∀ x y : E, ‖S.fullGradient x - S.fullGradient y‖ ≤ L * ‖x - y‖ := by
  intro x y
  have hdiff :
      S.fullGradient x - S.fullGradient y =
        SOptLib.finiteUniformAverage
          (fun i : ι => S.componentGradient i x - S.componentGradient i y) := by
    calc
      S.fullGradient x - S.fullGradient y =
          S.componentAverageGradient x - S.componentAverageGradient y := by
            rw [S.averageLSmooth_fullGradient_eq_componentAverageGradient hL x,
              S.averageLSmooth_fullGradient_eq_componentAverageGradient hL y]
      _ = SOptLib.finiteUniformAverage
          (fun i : ι => S.componentGradient i x - S.componentGradient i y) := by
            simp [componentAverageGradient, SOptLib.finiteUniformAverage_def,
              Finset.sum_sub_distrib, smul_sub]
  have hsquare : ‖S.fullGradient x - S.fullGradient y‖ ^ 2 ≤ L ^ 2 * ‖x - y‖ ^ 2 := by
    calc
      ‖S.fullGradient x - S.fullGradient y‖ ^ 2 =
          ‖SOptLib.finiteUniformAverage
            (fun i : ι => S.componentGradient i x - S.componentGradient i y)‖ ^ 2 := by
            rw [hdiff]
      _ ≤ SOptLib.finiteUniformAverage
            (fun i : ι => ‖S.componentGradient i x - S.componentGradient i y‖ ^ 2) :=
            finite_uniform_average_norm_sq_le_average_sq_norm
              (fun i : ι => S.componentGradient i x - S.componentGradient i y)
      _ ≤ L ^ 2 * ‖x - y‖ ^ 2 := hL.2.2 x y
  have hR_nonneg : 0 ≤ L * ‖x - y‖ :=
    mul_nonneg hL.1.le (norm_nonneg (x - y))
  have hLhs_nonneg : 0 ≤ ‖S.fullGradient x - S.fullGradient y‖ :=
    norm_nonneg _
  nlinarith [sq_nonneg (‖S.fullGradient x - S.fullGradient y‖ - L * ‖x - y‖)]

private theorem objective_hasGradientAt_of_averageLSmooth
    {L : ℝ} (hL : S.AverageLSmooth L) (z : E) :
    HasGradientAt S.objective (S.fullGradient z) z := by
  have hRaw :=
    SOptLib.finiteAverageObjective_hasGradientAt
      S.componentObjective S.componentGradient z (fun i : ι => hL.2.1 i z)
  have hAvg : HasGradientAt S.objective (S.componentAverageGradient z) z := by
    simpa [objective, componentAverageGradient, SOptLib.finiteUniformAverage_def] using hRaw
  rw [S.averageLSmooth_fullGradient_eq_componentAverageGradient hL z]
  exact hAvg

/-- Lemma 1 obligation, quadratic smoothness conclusion. This is source-derived
from Assumption 2 and the finite-sum objective, not a setup field.

Book citation: `book/research/PAGE.json#/key_lemmas/0`: the derived smoothness
bound is `f(y) <= f(x)+<∇f(x),y-x>+(L/2)||y-x||^2`. -/
theorem averageLSmooth_implies_quadratic_upper_bound
    {L : ℝ} (hL : S.AverageLSmooth L) :
    ∀ x y : E,
      S.objective y ≤
        S.objective x + inner ℝ (S.fullGradient x) (y - x) + (L / 2) * ‖y - x‖ ^ 2 := by
  intro x y
  have hgrad : ∀ z : E, HasGradientAt S.objective (S.fullGradient z) z :=
    S.objective_hasGradientAt_of_averageLSmooth hL
  have hLip := S.averageLSmooth_implies_fullGradient_lipschitz hL
  have hquad :=
    Convex.carrier_smooth_quadratic_upper_bound_of_hasGradientWithinAt_lipschitz
      (f := fun z : {z : E // z ∈ (Set.univ : Set E)} => S.objective z.1)
      (F := S.objective)
      (grad := fun z : {z : E // z ∈ (Set.univ : Set E)} => S.fullGradient z.1)
      (L := L)
      (by simpa using (convex_univ : Convex ℝ (Set.univ : Set E)))
      (by intro z hz; rfl)
      (by
        intro z
        rw [hasGradientWithinAt_univ]
        exact hgrad z.1)
      (by
        intro u v
        simpa using hLip v.1 u.1)
      (⟨y, trivial⟩ : {z : E // z ∈ (Set.univ : Set E)})
      (⟨x, trivial⟩ : {z : E // z ∈ (Set.univ : Set E)})
  dsimp at hquad
  linarith

private theorem inexact_gradient_step_inner_identity
    {V : Type*} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]
    {η : ℝ} (hη : 0 < η) (a g : V) :
    inner ℝ a (-η • g) =
      -(η / 2) * ‖a‖ ^ 2 -
        (2 * η)⁻¹ * ‖-η • g‖ ^ 2 +
        (η / 2) * ‖g - a‖ ^ 2 := by
  have hη_ne : η ≠ 0 := ne_of_gt hη
  rw [norm_sub_sq_real, norm_smul, norm_neg, Real.norm_of_nonneg hη.le]
  simp [inner_smul_right, real_inner_comm]
  field_simp [hη_ne]
  ring

/-- Lemma 2 obligation: descent under the PAGE primal update with an inexact
gradient. The smoothness hypothesis is Lemma 1's derived conclusion.

Book citation: `book/research/PAGE.json#/key_lemmas/1`: Lemma 2 assumes
`x^{t+1}:=x^t-eta g^t` and concludes the displayed inexact-gradient descent
inequality. -/
theorem descent_with_inexact_gradient
    {L : ℝ}
    (h_smooth :
      ∀ x y : E,
        S.objective y ≤
          S.objective x + inner ℝ (S.fullGradient x) (y - x) + (L / 2) * ‖y - x‖ ^ 2)
    {η : ℝ} (hη : 0 < η) (x g : E) :
    S.objective (x - η • g) ≤
      S.objective x -
        (η / 2) * ‖S.fullGradient x‖ ^ 2 -
        ((2 * η)⁻¹ - L / 2) * ‖(x - η • g) - x‖ ^ 2 +
        (η / 2) * ‖g - S.fullGradient x‖ ^ 2 := by
  have hs := h_smooth x (x - η • g)
  have hdisp : (x - η • g) - x = -η • g := by
    simp [sub_eq_add_neg, add_comm, add_left_comm, neg_smul]
  have hinner :
      inner ℝ (S.fullGradient x) (-η • g) =
        -(η / 2) * ‖S.fullGradient x‖ ^ 2 -
          (2 * η)⁻¹ * ‖-η • g‖ ^ 2 +
          (η / 2) * ‖g - S.fullGradient x‖ ^ 2 :=
    inexact_gradient_step_inner_identity hη (S.fullGradient x) g
  calc
    S.objective (x - η • g) ≤
        S.objective x + inner ℝ (S.fullGradient x) (-η • g) +
          (L / 2) * ‖-η • g‖ ^ 2 := by
          simpa [hdisp] using hs
    _ = S.objective x -
        (η / 2) * ‖S.fullGradient x‖ ^ 2 -
        ((2 * η)⁻¹ - L / 2) * ‖(x - η • g) - x‖ ^ 2 +
        (η / 2) * ‖g - S.fullGradient x‖ ^ 2 := by
          rw [hinner, hdisp]
          ring

private theorem line4_refresh_branch_error_zero
    {t : ℕ} {ω : Ω} (h_full : Fintype.card B = Fintype.card ι)
    (h_branch : S.refreshBranch t ω = true) :
    S.estimator (t + 1) ω - S.fullGradient (S.iterate (t + 1) ω) = 0 := by
  rw [S.estimator_succ t ω]
  rw [S.estimatorUpdate_refresh h_branch]
  rw [S.refreshEstimator_fullBatch h_full]
  simp

private theorem line4_residual_branch_decomposition
    {L : ℝ} (hL : S.AverageLSmooth L)
    (h_full : Fintype.card B = Fintype.card ι) (t : ℕ) (ω : Ω) :
    S.estimator (t + 1) ω - S.fullGradient (S.iterate (t + 1) ω) =
      if S.refreshBranch t ω then
        0
      else
        (S.estimator t ω - S.fullGradient (S.iterate t ω)) +
          ((Fintype.card B' : ℝ)⁻¹) •
            Finset.sum Finset.univ
              (fun j : B' =>
                (S.componentGradient (S.recursiveSample t j ω)
                    (S.iterate (t + 1) ω) -
                  S.componentGradient (S.recursiveSample t j ω)
                    (S.iterate t ω)) -
                (S.componentAverageGradient (S.iterate (t + 1) ω) -
                  S.componentAverageGradient (S.iterate t ω))) := by
  classical
  by_cases hbranch : S.refreshBranch t ω = true
  · rw [if_pos hbranch]
    exact line4_refresh_branch_error_zero (S := S) h_full hbranch
  · have hfalse : S.refreshBranch t ω = false := by
      cases hb : S.refreshBranch t ω with
      | false => rfl
      | true => exact False.elim (hbranch hb)
    simp only [hfalse, Bool.false_eq_true, ↓reduceIte]
    have htarget :
        S.fullGradient (S.iterate (t + 1) ω) - S.fullGradient (S.iterate t ω) =
          S.componentAverageGradient (S.iterate (t + 1) ω) -
            S.componentAverageGradient (S.iterate t ω) := by
      rw [S.averageLSmooth_fullGradient_eq_componentAverageGradient hL
            (S.iterate (t + 1) ω),
          S.averageLSmooth_fullGradient_eq_componentAverageGradient hL
            (S.iterate t ω)]
    have hcenter :
        ((Fintype.card B' : ℝ)⁻¹) •
            Finset.sum Finset.univ
              (fun j : B' =>
                (S.componentGradient (S.recursiveSample t j ω)
                    (S.iterate (t + 1) ω) -
                  S.componentGradient (S.recursiveSample t j ω)
                    (S.iterate t ω)) -
                (S.componentAverageGradient (S.iterate (t + 1) ω) -
                  S.componentAverageGradient (S.iterate t ω))) =
          ((Fintype.card B' : ℝ)⁻¹) •
            Finset.sum Finset.univ
              (fun j : B' =>
                S.componentGradient (S.recursiveSample t j ω)
                    (S.iterate (t + 1) ω) -
                  S.componentGradient (S.recursiveSample t j ω)
                    (S.iterate t ω)) -
            (S.componentAverageGradient (S.iterate (t + 1) ω) -
              S.componentAverageGradient (S.iterate t ω)) := by
      simpa using
        inv_card_smul_sum_sub_const_eq
          (s := (Finset.univ : Finset B'))
          (z := fun j : B' =>
            S.componentGradient (S.recursiveSample t j ω)
                (S.iterate (t + 1) ω) -
              S.componentGradient (S.recursiveSample t j ω)
                (S.iterate t ω))
          (c := S.componentAverageGradient (S.iterate (t + 1) ω) -
            S.componentAverageGradient (S.iterate t ω))
          (by simpa using (Fintype.card_pos : 0 < Fintype.card B'))
    rw [S.estimator_succ t ω, S.estimatorUpdate_recursive hfalse,
      S.recursiveEstimatorUpdate_def, SOptLib.recursiveGradientDifferenceAverage_def]
    calc
      (((Fintype.card B' : ℝ)⁻¹) •
              Finset.sum Finset.univ
                (fun i : B' =>
                  S.componentGradient (S.recursiveSample t i ω)
                      (S.iterate (t + 1) ω) -
                    S.componentGradient (S.recursiveSample t i ω)
                      (S.iterate t ω)) +
            S.estimator t ω) -
          S.fullGradient (S.iterate (t + 1) ω)
          =
        (S.estimator t ω - S.fullGradient (S.iterate t ω)) +
          (((Fintype.card B' : ℝ)⁻¹) •
              Finset.sum Finset.univ
                (fun i : B' =>
                  S.componentGradient (S.recursiveSample t i ω)
                      (S.iterate (t + 1) ω) -
                    S.componentGradient (S.recursiveSample t i ω)
                      (S.iterate t ω)) -
            (S.fullGradient (S.iterate (t + 1) ω) -
              S.fullGradient (S.iterate t ω))) := by
            abel
      _ =
        (S.estimator t ω - S.fullGradient (S.iterate t ω)) +
          (((Fintype.card B' : ℝ)⁻¹) •
              Finset.sum Finset.univ
                (fun i : B' =>
                  S.componentGradient (S.recursiveSample t i ω)
                      (S.iterate (t + 1) ω) -
                    S.componentGradient (S.recursiveSample t i ω)
                      (S.iterate t ω)) -
            (S.componentAverageGradient (S.iterate (t + 1) ω) -
              S.componentAverageGradient (S.iterate t ω))) := by
            rw [htarget]
      _ =
        (S.estimator t ω - S.fullGradient (S.iterate t ω)) +
          ((Fintype.card B' : ℝ)⁻¹) •
            Finset.sum Finset.univ
              (fun j : B' =>
                (S.componentGradient (S.recursiveSample t j ω)
                    (S.iterate (t + 1) ω) -
                  S.componentGradient (S.recursiveSample t j ω)
                    (S.iterate t ω)) -
                (S.componentAverageGradient (S.iterate (t + 1) ω) -
                  S.componentAverageGradient (S.iterate t ω))) := by
            rw [← hcenter]

private theorem line4_centered_componentGradientDiff_average_zero
    {L : ℝ} (hL : S.AverageLSmooth L) (x y : E) :
    SOptLib.finiteUniformAverage
        (fun i : ι =>
          (S.componentGradient i x - S.componentGradient i y) -
            (S.fullGradient x - S.fullGradient y)) = 0 := by
  classical
  have htarget :
      S.fullGradient x - S.fullGradient y =
        S.componentAverageGradient x - S.componentAverageGradient y := by
    rw [S.averageLSmooth_fullGradient_eq_componentAverageGradient hL x,
      S.averageLSmooth_fullGradient_eq_componentAverageGradient hL y]
  rw [htarget]
  have hcenter :
      ((Fintype.card ι : ℝ)⁻¹) •
          Finset.sum Finset.univ
            (fun i : ι =>
              (S.componentGradient i x - S.componentGradient i y) -
                (S.componentAverageGradient x - S.componentAverageGradient y)) =
        ((Fintype.card ι : ℝ)⁻¹) •
          Finset.sum Finset.univ
            (fun i : ι => S.componentGradient i x - S.componentGradient i y) -
          (S.componentAverageGradient x - S.componentAverageGradient y) := by
    simpa using
      inv_card_smul_sum_sub_const_eq
        (s := (Finset.univ : Finset ι))
        (z := fun i : ι => S.componentGradient i x - S.componentGradient i y)
        (c := S.componentAverageGradient x - S.componentAverageGradient y)
        (by simpa using (Fintype.card_pos : 0 < Fintype.card ι))
  rw [SOptLib.finiteUniformAverage_def, hcenter]
  simp [componentAverageGradient, SOptLib.finiteUniformAverage_def,
    Finset.sum_sub_distrib, smul_sub]

private theorem finiteUniformAverage_function_eval_eq_zero_of_average_zero
    {α β V : Type*} [Fintype α] [Fintype β] [DecidableEq α] [Nonempty β]
    [AddCommGroup V] [Module ℝ V]
    (j : α) (f : β → V)
    (hmean : SOptLib.finiteUniformAverage f = 0) :
    SOptLib.finiteUniformAverage (fun r : α → β => f (r j)) = 0 := by
  classical
  let e : (α → β) ≃ β × ({i : α // i ≠ j} → β) := by
    refine
      { toFun := fun r : α → β =>
          (r j, fun i : {i : α // i ≠ j} => r i.1)
        invFun := fun p : β × ({i : α // i ≠ j} → β) => fun i : α =>
          if h : i = j then p.1 else p.2 ⟨i, h⟩
        left_inv := ?_
        right_inv := ?_ }
    · intro r
      funext i
      by_cases h : i = j
      · simp [h]
      · simp [h]
    · intro p
      ext i
      · simp
      · simp [i.2]
  have hsum_reindex :
      (Finset.univ.sum (fun r : α → β => f (r j))) =
        Finset.univ.sum (fun p : β × ({i : α // i ≠ j} → β) => f p.1) := by
    refine Fintype.sum_equiv e (fun r : α → β => f (r j))
      (fun p : β × ({i : α // i ≠ j} → β) => f p.1) ?_
    ·
      intro r
      rfl
  have hsum_prod :
      (Finset.univ.sum (fun p : β × ({i : α // i ≠ j} → β) => f p.1)) =
        Finset.univ.sum (fun b : β =>
          Finset.univ.sum (fun _ : {i : α // i ≠ j} → β => f b)) := by
    rw [Fintype.sum_prod_type]
  have hsum_const :
      (Finset.univ.sum (fun b : β =>
          Finset.univ.sum (fun _ : {i : α // i ≠ j} → β => f b))) =
        Finset.univ.sum (fun b : β =>
          Fintype.card ({i : α // i ≠ j} → β) • f b) := by
    simp
  have hsum_f_zero : Finset.univ.sum f = 0 := by
    have hcard_ne : (Fintype.card β : ℝ)⁻¹ ≠ 0 := by
      exact inv_ne_zero (by exact_mod_cast (Fintype.card_ne_zero : Fintype.card β ≠ 0))
    rw [SOptLib.finiteUniformAverage_def] at hmean
    exact (smul_eq_zero.mp hmean).resolve_left hcard_ne
  rw [SOptLib.finiteUniformAverage_def, hsum_reindex, hsum_prod, hsum_const]
  rw [← Finset.smul_sum, hsum_f_zero]
  simp

private theorem finiteUniformAverage_function_eval_eq
    {α β V : Type*} [Fintype α] [Fintype β] [DecidableEq α] [Nonempty β]
    [AddCommGroup V] [Module ℝ V]
    (j : α) (f : β → V) :
    SOptLib.finiteUniformAverage (fun r : α → β => f (r j)) =
      SOptLib.finiteUniformAverage f := by
  classical
  let c : V := SOptLib.finiteUniformAverage f
  have hcenter_pop :
      SOptLib.finiteUniformAverage (fun b : β => f b - c) = 0 := by
    have hcard_pos : 0 < Fintype.card β := Fintype.card_pos
    have hcenter :=
      inv_card_smul_sum_sub_const_eq
        (s := (Finset.univ : Finset β)) (z := f) (c := c)
        (by simpa using hcard_pos)
    calc
      SOptLib.finiteUniformAverage (fun b : β => f b - c)
          = SOptLib.finiteUniformAverage f - c := by
              simpa [SOptLib.finiteUniformAverage_def] using hcenter
      _ = 0 := by
              simp [c]
  have hcenter_row :
      SOptLib.finiteUniformAverage (fun r : α → β => f (r j) - c) = 0 :=
    finiteUniformAverage_function_eval_eq_zero_of_average_zero
      (α := α) (β := β) (V := V) j (fun b : β => f b - c) hcenter_pop
  have hrow_center_expand :
      SOptLib.finiteUniformAverage (fun r : α → β => f (r j) - c) =
        SOptLib.finiteUniformAverage (fun r : α → β => f (r j)) - c := by
    have hcard_pos : 0 < Fintype.card (α → β) := Fintype.card_pos
    have hcenter :=
      inv_card_smul_sum_sub_const_eq
        (s := (Finset.univ : Finset (α → β)))
        (z := fun r : α → β => f (r j)) (c := c)
        (by simpa using hcard_pos)
    simpa [SOptLib.finiteUniformAverage_def] using hcenter
  rw [hrow_center_expand] at hcenter_row
  exact sub_eq_zero.mp hcenter_row

private theorem finiteUniformAverage_function_eval_inner_eval_eq_zero_of_average_zero
    {α β V : Type*} [Fintype α] [Fintype β] [DecidableEq α] [Nonempty β]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {j l : α} (hjl : j ≠ l) (f : β → V)
    (hmean : SOptLib.finiteUniformAverage f = 0) :
    SOptLib.finiteUniformAverage
      (fun r : α → β => inner ℝ (f (r j)) (f (r l))) = 0 := by
  classical
  let rest := {i : α // i ≠ j ∧ i ≠ l}
  let e : (α → β) ≃ β × β × (rest → β) := by
    refine
      { toFun := fun r : α → β =>
          (r j, r l, fun i : rest => r i.1)
        invFun := fun p : β × β × (rest → β) => fun i : α =>
          if hij : i = j then
            p.1
          else if hil : i = l then
            p.2.1
          else
            p.2.2 ⟨i, hij, hil⟩
        left_inv := ?_
        right_inv := ?_ }
    · intro r
      funext i
      by_cases hij : i = j
      · simp [hij]
      · by_cases hil : i = l
        · have hlj : l ≠ j := by
            intro h
            exact hij (hil.trans h)
          simp [hij, hil, hlj]
        · simp [hij, hil]
    · intro p
      ext i
      · simp
      · simp [hjl.symm]
      · simp [i.2.1, i.2.2]
  have hsum_reindex :
      (Finset.univ.sum
          (fun r : α → β => inner ℝ (f (r j)) (f (r l)))) =
        Finset.univ.sum
          (fun p : β × β × (rest → β) => inner ℝ (f p.1) (f p.2.1)) := by
    refine Fintype.sum_equiv e
      (fun r : α → β => inner ℝ (f (r j)) (f (r l)))
      (fun p : β × β × (rest → β) => inner ℝ (f p.1) (f p.2.1)) ?_
    intro r
    rfl
  have hsum_prod :
      (Finset.univ.sum
          (fun p : β × β × (rest → β) => inner ℝ (f p.1) (f p.2.1))) =
        Finset.univ.sum (fun b₁ : β =>
          Finset.univ.sum (fun b₂ : β =>
            Finset.univ.sum (fun _ : rest → β => inner ℝ (f b₁) (f b₂)))) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl ?_
    intro b₁ _hb₁
    rw [Fintype.sum_prod_type]
  have hsum_const :
      (Finset.univ.sum (fun b₁ : β =>
          Finset.univ.sum (fun b₂ : β =>
            Finset.univ.sum (fun _ : rest → β => inner ℝ (f b₁) (f b₂))))) =
        Finset.univ.sum (fun b₁ : β =>
          Finset.univ.sum (fun b₂ : β =>
            Fintype.card (rest → β) • inner ℝ (f b₁) (f b₂))) := by
    simp
  have hsum_f_zero : Finset.univ.sum f = 0 := by
    have hcard_ne : (Fintype.card β : ℝ)⁻¹ ≠ 0 := by
      exact inv_ne_zero (by exact_mod_cast (Fintype.card_ne_zero : Fintype.card β ≠ 0))
    rw [SOptLib.finiteUniformAverage_def] at hmean
    exact (smul_eq_zero.mp hmean).resolve_left hcard_ne
  have hinner_sum_zero :
      ∀ b₁ : β, Finset.univ.sum (fun b₂ : β => inner ℝ (f b₁) (f b₂)) = 0 := by
    intro b₁
    calc
      Finset.univ.sum (fun b₂ : β => inner ℝ (f b₁) (f b₂))
          = inner ℝ (f b₁) (Finset.univ.sum f) := by
              rw [inner_sum]
      _ = 0 := by
              rw [hsum_f_zero]
              simp
  have hscaled_inner_sum_zero :
      ∀ b₁ : β,
        Finset.univ.sum
          (fun b₂ : β =>
            ((Fintype.card β : ℝ) ^ Fintype.card rest) *
              inner ℝ (f b₁) (f b₂)) = 0 := by
    intro b₁
    rw [← Finset.mul_sum, hinner_sum_zero b₁]
    simp
  rw [SOptLib.finiteUniformAverage_def, hsum_reindex, hsum_prod, hsum_const]
  simp [hscaled_inner_sum_zero]

private theorem finite_function_row_sum_norm_sq_eq_sum_diagonal_of_average_zero
    {α β V : Type*} [Fintype α] [Fintype β] [DecidableEq α] [Nonempty β]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (f : β → V) (hmean : SOptLib.finiteUniformAverage f = 0) :
    Finset.univ.sum
        (fun r : α → β => ‖Finset.univ.sum (fun j : α => f (r j))‖ ^ 2) =
      Finset.univ.sum
        (fun j : α => Finset.univ.sum (fun r : α → β => ‖f (r j)‖ ^ 2)) := by
  classical
  letI : MeasurableSpace (α → β) := ⊤
  let μ : MeasureTheory.Measure (α → β) := MeasureTheory.Measure.count
  have hcov :=
    integral_norm_sq_finset_sum_eq_sum_integrals_of_cross_zero
      (μ := μ) (I := (Finset.univ : Finset α))
      (δ := fun j r => f (r j))
      (hmeas := by
        intro j hj
        exact
          aestronglyMeasurable_of_countable_key_reconstruction
            (μ := μ) (Y := fun r : α → β => r)
            (Z := fun r : α → β => f (r j))
            (by exact measurable_id.aemeasurable)
            (fun r : α → β => f (r j))
            (by exact Filter.EventuallyEq.rfl))
      (hL2 := by
        intro j hj
        exact integrable_of_finite_range
          ((measurable_of_finite
            (fun r : α → β => ‖f (r j)‖ ^ 2)).aestronglyMeasurable)
          (Set.toFinite (Set.range (fun r : α → β => ‖f (r j)‖ ^ 2))))
      (hcross := by
        intro j hj l hl hjl
        have hcross_avg :
            SOptLib.finiteUniformAverage
              (fun r : α → β => inner ℝ (f (r j)) (f (r l))) = 0 :=
          finiteUniformAverage_function_eval_inner_eval_eq_zero_of_average_zero
            (α := α) (β := β) (V := V) hjl f hmean
        have hsum_zero :
            Finset.univ.sum
              (fun r : α → β => inner ℝ (f (r j)) (f (r l))) = 0 := by
          have hcard_ne : (Fintype.card (α → β) : ℝ)⁻¹ ≠ 0 := by
            exact inv_ne_zero
              (by exact_mod_cast
                (Fintype.card_ne_zero : Fintype.card (α → β) ≠ 0))
          rw [SOptLib.finiteUniformAverage_def] at hcross_avg
          exact (smul_eq_zero.mp hcross_avg).resolve_left hcard_ne
        simpa [μ] using hsum_zero)
  simpa [μ] using hcov

private theorem finite_function_row_centered_average_secondMoment_le
    {α β V : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    [Nonempty α] [Nonempty β]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (f : β → V) (hmean : SOptLib.finiteUniformAverage f = 0) :
    (Fintype.card (α → β) : ℝ)⁻¹ *
        Finset.univ.sum
          (fun r : α → β =>
            ‖((Fintype.card α : ℝ)⁻¹) •
              Finset.univ.sum (fun j : α => f (r j))‖ ^ 2) ≤
      SOptLib.finiteUniformAverage (fun b : β => ‖f b‖ ^ 2) /
        (Fintype.card α : ℝ) := by
  classical
  let m : ℝ := Fintype.card α
  let rowCard : ℝ := Fintype.card (α → β)
  let diagAvg : ℝ := SOptLib.finiteUniformAverage (fun b : β => ‖f b‖ ^ 2)
  have hm_pos : 0 < m := by
    dsimp [m]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card α)
  have hm_ne : m ≠ 0 := ne_of_gt hm_pos
  have hrow_ne : rowCard ≠ 0 := by
    dsimp [rowCard]
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (α → β) ≠ 0)
  have hcov :
      Finset.univ.sum
          (fun r : α → β => ‖Finset.univ.sum (fun j : α => f (r j))‖ ^ 2) =
        Finset.univ.sum
          (fun j : α =>
            Finset.univ.sum (fun r : α → β => ‖f (r j)‖ ^ 2)) :=
    finite_function_row_sum_norm_sq_eq_sum_diagonal_of_average_zero
      (α := α) (β := β) (V := V) f hmean
  have hdiag :
      ∀ j : α,
        (Fintype.card (α → β) : ℝ)⁻¹ *
            Finset.univ.sum (fun r : α → β => ‖f (r j)‖ ^ 2) =
          diagAvg := by
    intro j
    have h :=
      finiteUniformAverage_function_eval_eq
        (α := α) (β := β) (V := ℝ) j (fun b : β => ‖f b‖ ^ 2)
    simpa [SOptLib.finiteUniformAverage_def, diagAvg] using h
  have hscaled :
      Finset.univ.sum
          (fun r : α → β =>
            ‖((Fintype.card α : ℝ)⁻¹) •
              Finset.univ.sum (fun j : α => f (r j))‖ ^ 2) =
        (m⁻¹) ^ 2 *
          Finset.univ.sum
            (fun r : α → β => ‖Finset.univ.sum (fun j : α => f (r j))‖ ^ 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro r _hr
    have hnonneg : 0 ≤ (Fintype.card α : ℝ)⁻¹ := by positivity
    simp [m, norm_smul, Real.norm_eq_abs, abs_of_nonneg hnonneg, sq]
    ring
  calc
    (Fintype.card (α → β) : ℝ)⁻¹ *
        Finset.univ.sum
          (fun r : α → β =>
            ‖((Fintype.card α : ℝ)⁻¹) •
              Finset.univ.sum (fun j : α => f (r j))‖ ^ 2)
        =
      (m⁻¹) ^ 2 *
        ((Fintype.card (α → β) : ℝ)⁻¹ *
          Finset.univ.sum
            (fun r : α → β => ‖Finset.univ.sum (fun j : α => f (r j))‖ ^ 2)) := by
        rw [hscaled]
        ring
    _ =
      (m⁻¹) ^ 2 *
        ((Fintype.card (α → β) : ℝ)⁻¹ *
          Finset.univ.sum
            (fun j : α =>
              Finset.univ.sum (fun r : α → β => ‖f (r j)‖ ^ 2))) := by
        rw [hcov]
    _ =
      (m⁻¹) ^ 2 *
        Finset.univ.sum (fun _j : α => diagAvg) := by
        congr 1
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro j _hj
        exact hdiag j
    _ = diagAvg / (Fintype.card α : ℝ) := by
        simp [m]
        field_simp [hm_ne]
    _ ≤ SOptLib.finiteUniformAverage (fun b : β => ‖f b‖ ^ 2) /
        (Fintype.card α : ℝ) := by
        rfl

private theorem line4_false_branch_key_integral_factor [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (h_laws : S.StochasticLaws P) (t : ℕ)
    (φ : Line4PastKey S t → ℝ) :
    (∫ ω : Ω,
        (if S.refreshBranch t ω = false then φ (line4PastKey S t ω) else 0) ∂P) =
      ∫ ω : Ω,
        (1 - S.refreshProbability t) * φ (line4PastKey S t ω) ∂P := by
  classical
  letI : MeasurableSpace ι := ⊤
  unfold StochasticLaws at h_laws
  rcases h_laws with ⟨hp, hmap⟩
  let pnn : {r : ℝ // 0 ≤ r} := ⟨S.refreshProbability t, (hp t).1.le⟩
  let W : Ω → Line4PastKey S t := fun ω => line4PastKey S t ω
  let Y : Ω → Bool := fun ω => S.refreshBranch t ω
  let ν : MeasureTheory.Measure Bool := (S.branchPMF hp t).toMeasure
  let w : Bool → ℝ := fun b => ν.real ({b} : Set Bool)
  let F : Line4PastKey S t → Bool → ℝ := fun k b =>
    if b = false then φ k else 0
  have hν_false : ν.real ({false} : Set Bool) = 1 - S.refreshProbability t := by
    dsimp [ν]
    rw [MeasureTheory.Measure.real,
      PMF.toMeasure_apply_singleton (S.branchPMF hp t) false
        (measurableSet_singleton false)]
    rw [branchPMF, PMF.bernoulli_apply]
    change ((1 - pnn : {r : ℝ // 0 ≤ r}) : ℝ) = 1 - S.refreshProbability t
    have hp_nn : pnn ≤ 1 := by
      exact_mod_cast (hp t).2
    calc
      ((1 - pnn : {r : ℝ // 0 ≤ r}) : ℝ) = (1 : ℝ) - (pnn : ℝ) :=
        NNReal.coe_sub hp_nn
      _ = 1 - S.refreshProbability t := by
        rfl
  have hbridge :=
    line4_past_key_branch_pair_bridge (S := S) P hp hmap t
  have htransport :
      (∫ ω : Ω, F (W ω) (Y ω) ∂P) =
        ∫ ω : Ω, Finset.univ.sum (fun b : Bool => w b • F (W ω) b) ∂P := by
    refine
      expectation_sample_eq_expectation_weighted_fiber_sum_of_joint_law
        (P := P) (W := W) (Y := Y) (nu := ν) (w := w) (F := F)
        ?_ ?_ ?_ ?_ ?_ ?_
    · exact hbridge.1.fst
    · exact hbridge.1.snd
    · simpa [W, Y] using hbridge.2
    · intro b
      rfl
    · exact
        integrable_prod_of_finite_left_map_fintype_right
          (mu := P) (W := W) (nu := ν) (F := F)
          (hW := hbridge.1.fst) (hfin := Set.toFinite (Set.range W))
    · exact (measurable_of_finite
        (fun k : Line4PastKey S t =>
          Finset.univ.sum (fun b : Bool => w b • F k b))).aestronglyMeasurable
  calc
    (∫ ω : Ω,
        (if S.refreshBranch t ω = false then φ (line4PastKey S t ω) else 0) ∂P)
        = ∫ ω : Ω, F (W ω) (Y ω) ∂P := by
          simp [F, W, Y]
    _ = ∫ ω : Ω, Finset.univ.sum (fun b : Bool => w b • F (W ω) b) ∂P :=
          htransport
    _ = ∫ ω : Ω,
          (1 - S.refreshProbability t) * φ (line4PastKey S t ω) ∂P := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards with ω
          simp [F, W, w, hν_false, smul_eq_mul]

private theorem line4_false_branch_recursive_row_integral [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (h_laws : S.StochasticLaws P) (t : ℕ)
    (F : Line4PastKey S t → (B' → ι) → ℝ) :
    (∫ ω : Ω,
        (if S.refreshBranch t ω = false then
          F (line4PastKey S t ω) (fun j : B' => S.recursiveSample t j ω)
        else
          0) ∂P) =
      ∫ ω : Ω,
        (1 - S.refreshProbability t) *
          ((Fintype.card (B' → ι) : ℝ)⁻¹ *
            Finset.univ.sum
              (fun r : B' → ι => F (line4PastKey S t ω) r)) ∂P := by
  classical
  letI : MeasurableSpace ι := ⊤
  unfold StochasticLaws at h_laws
  rcases h_laws with ⟨hp, hmap⟩
  let W : Ω → Line4PastKey S t × Bool :=
    fun ω => (line4PastKey S t ω, S.refreshBranch t ω)
  let Y : Ω → (B' → ι) := fun ω => fun j : B' => S.recursiveSample t j ω
  let ν : MeasureTheory.Measure (B' → ι) :=
    MeasureTheory.Measure.pi
      (fun _ : B' => PMF.toMeasure (PMF.uniformOfFintype (α := ι)))
  let w : (B' → ι) → ℝ := fun r => ν.real ({r} : Set (B' → ι))
  let G : Line4PastKey S t × Bool → (B' → ι) → ℝ := fun k r =>
    if k.2 = false then F k.1 r else 0
  let φ : Line4PastKey S t → ℝ := fun k =>
    (Fintype.card (B' → ι) : ℝ)⁻¹ *
      Finset.univ.sum (fun r : B' → ι => F k r)
  have hν_singleton :
      ∀ r : B' → ι,
        ν.real ({r} : Set (B' → ι)) =
          (Fintype.card (B' → ι) : ℝ)⁻¹ := by
    intro r
    dsimp [ν]
    rw [MeasureTheory.Measure.real,
      uniform_pi_singleton_mass (A := ι) (C := B') r]
    exact ENNReal.toReal_ofReal
      (inv_nonneg.mpr (Nat.cast_nonneg (Fintype.card (B' → ι))))
  have hbridge :=
    line4_past_key_branch_recursive_row_bridge (S := S) P hp hmap t
  have htransport :
      (∫ ω : Ω, G (W ω) (Y ω) ∂P) =
        ∫ ω : Ω, Finset.univ.sum (fun r : B' → ι => w r • G (W ω) r) ∂P := by
    refine
      expectation_sample_eq_expectation_weighted_fiber_sum_of_joint_law
        (P := P) (W := W) (Y := Y) (nu := ν) (w := w) (F := G)
        ?_ ?_ ?_ ?_ ?_ ?_
    · exact hbridge.2.1
    · exact hbridge.1.snd
    · simpa [W, Y] using hbridge.2.2
    · intro r
      rfl
    · exact
        integrable_prod_of_finite_left_map_fintype_right
          (mu := P) (W := W) (nu := ν) (F := G)
          (hW := hbridge.2.1) (hfin := Set.toFinite (Set.range W))
    · exact (measurable_of_finite
        (fun k : Line4PastKey S t × Bool =>
          Finset.univ.sum (fun r : B' → ι => w r • G k r))).aestronglyMeasurable
  calc
    (∫ ω : Ω,
        (if S.refreshBranch t ω = false then
          F (line4PastKey S t ω) (fun j : B' => S.recursiveSample t j ω)
        else
          0) ∂P)
        = ∫ ω : Ω, G (W ω) (Y ω) ∂P := by
          simp [G, W, Y]
    _ = ∫ ω : Ω, Finset.univ.sum (fun r : B' → ι => w r • G (W ω) r) ∂P :=
          htransport
    _ = ∫ ω : Ω,
          (if S.refreshBranch t ω = false then
            φ (line4PastKey S t ω)
          else
            0) ∂P := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards with ω
          by_cases hbranch : S.refreshBranch t ω = false
          · simp [G, W, w, hν_singleton, hbranch, Finset.mul_sum, mul_assoc,
              mul_left_comm, mul_comm, φ]
          · simp [G, W, w, hν_singleton, hbranch, φ]
    _ = ∫ ω : Ω,
          (1 - S.refreshProbability t) * φ (line4PastKey S t ω) ∂P :=
          line4_false_branch_key_integral_factor (S := S) P
            ⟨hp, hmap⟩ t φ
    _ = ∫ ω : Ω,
          (1 - S.refreshProbability t) *
            ((Fintype.card (B' → ι) : ℝ)⁻¹ *
              Finset.univ.sum
                (fun r : B' → ι => F (line4PastKey S t ω) r)) ∂P := by
          rfl

private theorem line4_false_branch_recursive_row_integral_le_key_bound
    [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (h_laws : S.StochasticLaws P) (t : ℕ)
    (F : Line4PastKey S t → (B' → ι) → ℝ)
    (G : Line4PastKey S t → ℝ)
    (h_bound :
      ∀ k : Line4PastKey S t,
        (Fintype.card (B' → ι) : ℝ)⁻¹ *
            Finset.univ.sum (fun r : B' → ι => F k r) ≤ G k) :
    (∫ ω : Ω,
        (if S.refreshBranch t ω = false then
          F (line4PastKey S t ω) (fun j : B' => S.recursiveSample t j ω)
        else
          0) ∂P) ≤
      ∫ ω : Ω,
        (1 - S.refreshProbability t) * G (line4PastKey S t ω) ∂P := by
  classical
  letI : MeasurableSpace ι := ⊤
  have htransport :=
    line4_false_branch_recursive_row_integral (S := S) P h_laws t F
  have h_laws' := h_laws
  unfold StochasticLaws at h_laws'
  rcases h_laws' with ⟨hp, hmap⟩
  have hbridge :=
    line4_past_key_branch_pair_bridge (S := S) P hp hmap t
  have hkey_aemeas :
      AEMeasurable (fun ω : Ω => line4PastKey S t ω) P :=
    hbridge.1.fst
  have hprob_nonneg : 0 ≤ 1 - S.refreshProbability t := by
    linarith [(hp t).2]
  let avgF : Line4PastKey S t → ℝ := fun k =>
    (1 - S.refreshProbability t) *
      ((Fintype.card (B' → ι) : ℝ)⁻¹ *
        Finset.univ.sum (fun r : B' → ι => F k r))
  let weightedG : Line4PastKey S t → ℝ := fun k =>
    (1 - S.refreshProbability t) * G k
  have hleft_int :
      MeasureTheory.Integrable
        (fun ω : Ω =>
          (1 - S.refreshProbability t) *
            ((Fintype.card (B' → ι) : ℝ)⁻¹ *
              Finset.univ.sum
                (fun r : B' → ι => F (line4PastKey S t ω) r))) P := by
    have haestrong :
        MeasureTheory.AEStronglyMeasurable
          (fun ω : Ω => avgF (line4PastKey S t ω)) P := by
      exact
        aestronglyMeasurable_of_countable_key_reconstruction
          (μ := P) (Y := fun ω : Ω => line4PastKey S t ω)
          (Z := fun ω : Ω => avgF (line4PastKey S t ω))
          hkey_aemeas avgF (Filter.Eventually.of_forall fun _ω => rfl)
    have hfin :
        (Set.range (fun ω : Ω => avgF (line4PastKey S t ω))).Finite := by
      have hsubset :
          Set.range (fun ω : Ω => avgF (line4PastKey S t ω)) ⊆
            avgF '' Set.range (fun ω : Ω => line4PastKey S t ω) := by
        rintro z ⟨ω, rfl⟩
        exact ⟨line4PastKey S t ω, ⟨ω, rfl⟩, rfl⟩
      exact ((Set.toFinite (Set.range (fun ω : Ω => line4PastKey S t ω))).image
        avgF).subset hsubset
    simpa [avgF] using integrable_of_finite_range haestrong hfin
  have hright_int :
      MeasureTheory.Integrable
        (fun ω : Ω =>
          (1 - S.refreshProbability t) * G (line4PastKey S t ω)) P := by
    have haestrong :
        MeasureTheory.AEStronglyMeasurable
          (fun ω : Ω => weightedG (line4PastKey S t ω)) P := by
      exact
        aestronglyMeasurable_of_countable_key_reconstruction
          (μ := P) (Y := fun ω : Ω => line4PastKey S t ω)
          (Z := fun ω : Ω => weightedG (line4PastKey S t ω))
          hkey_aemeas weightedG (Filter.Eventually.of_forall fun _ω => rfl)
    have hfin :
        (Set.range (fun ω : Ω => weightedG (line4PastKey S t ω))).Finite := by
      have hsubset :
          Set.range (fun ω : Ω => weightedG (line4PastKey S t ω)) ⊆
            weightedG '' Set.range (fun ω : Ω => line4PastKey S t ω) := by
        rintro z ⟨ω, rfl⟩
        exact ⟨line4PastKey S t ω, ⟨ω, rfl⟩, rfl⟩
      exact ((Set.toFinite (Set.range (fun ω : Ω => line4PastKey S t ω))).image
        weightedG).subset hsubset
    simpa [weightedG] using integrable_of_finite_range haestrong hfin
  have hmono :
      (∫ ω : Ω,
          (1 - S.refreshProbability t) *
            ((Fintype.card (B' → ι) : ℝ)⁻¹ *
              Finset.univ.sum
                (fun r : B' → ι => F (line4PastKey S t ω) r)) ∂P) ≤
        ∫ ω : Ω,
          (1 - S.refreshProbability t) * G (line4PastKey S t ω) ∂P := by
    refine MeasureTheory.integral_mono_ae hleft_int hright_int ?_
    filter_upwards with ω
    exact mul_le_mul_of_nonneg_left (h_bound (line4PastKey S t ω)) hprob_nonneg
  rw [htransport]
  exact hmono

/-- Formal retirement artifact for the old no-`b = n` Lemma 3 route.

If the refresh branch is only a minibatch average, its squared error against the
full finite average need not vanish. In the two-component, one-sample case below
the refresh sample always chooses the second component, giving refresh average
`1` while the full finite average is `1/2`. Thus the refresh-free recursion
used by the old `line4_variance_recursion` head cannot be justified without the
full-refresh premise.

Source context: `paper/PAGE.pdf`, Appendix A.1, justifies Eq. (17) by saying
`where (17) holds since we let b = n in this finite-sum case`. -/
theorem line4_variance_recursion_old_no_fullBatch_counterexample :
    ∃ (sample : PUnit → Fin 2) (componentGradientValues : Fin 2 → ℝ),
      Fintype.card PUnit ≠ Fintype.card (Fin 2) ∧
        ¬ (‖SOptLib.finiteUniformAverage
              (fun j : PUnit => componentGradientValues (sample j)) -
            SOptLib.finiteUniformAverage componentGradientValues‖ ^ 2 ≤
          (0 : ℝ)) := by
  refine ⟨fun _ => (1 : Fin 2), fun i => if i = 0 then (0 : ℝ) else 1, ?_, ?_⟩
  · norm_num
  · norm_num [SOptLib.finiteUniformAverage_def, Fin.sum_univ_two]

/-- Lemma 3 obligation: PAGE's Line 4 estimator law yields the finite-sum
variance recursion used by Theorem 1.

Book citation: `book/research/PAGE.json#/key_lemmas/2`: if Assumption 2 holds
and `g^{t+1}` is defined by Line 4, then the expected estimator-error recursion
is bounded by the old error and `(1-p_t)L^2/b'` times the step length. The
finite-sum proof removes the refresh-branch error using the Theorem 1 schedule
condition `b = n`; in this Lean model that condition is
`Fintype.card B = Fintype.card ι`. -/
theorem line4_variance_recursion [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    {L : ℝ} (hL : S.AverageLSmooth L)
    (h_laws : S.StochasticLaws P)
    (h_full : Fintype.card B = Fintype.card ι) (t : ℕ) :
    (∫ ω : Ω,
        ‖S.estimator (t + 1) ω - S.fullGradient (S.iterate (t + 1) ω)‖ ^ 2 ∂P) ≤
      ∫ ω : Ω,
        (1 - S.refreshProbability t) *
          ‖S.estimator t ω - S.fullGradient (S.iterate t ω)‖ ^ 2 +
        (((1 - S.refreshProbability t) * L ^ 2) / (Fintype.card B' : ℝ)) *
          ‖S.iterate (t + 1) ω - S.iterate t ω‖ ^ 2 ∂P := by
  classical
  let oldError : Ω → E :=
    fun ω => S.estimator t ω - S.fullGradient (S.iterate t ω)
  let centeredIncrement : Ω → E :=
    fun ω =>
      ((Fintype.card B' : ℝ)⁻¹) •
        Finset.sum Finset.univ
          (fun j : B' =>
            (S.componentGradient (S.recursiveSample t j ω)
                (S.iterate (t + 1) ω) -
              S.componentGradient (S.recursiveSample t j ω)
                (S.iterate t ω)) -
            (S.componentAverageGradient (S.iterate (t + 1) ω) -
              S.componentAverageGradient (S.iterate t ω)))
  have h_decomp :
      ∀ ω : Ω,
        S.estimator (t + 1) ω - S.fullGradient (S.iterate (t + 1) ω) =
          if S.refreshBranch t ω then
            0
          else
            oldError ω + centeredIncrement ω := by
    intro ω
    simpa [oldError, centeredIncrement] using
      line4_residual_branch_decomposition (S := S) hL h_full t ω
  have h_population_centered :
      ∀ x y : E,
        SOptLib.finiteUniformAverage
            (fun i : ι =>
              (S.componentGradient i x - S.componentGradient i y) -
                (S.fullGradient x - S.fullGradient y)) = 0 := by
    intro x y
    exact line4_centered_componentGradientDiff_average_zero (S := S) hL x y
  have h_recursive_fresh :
      S.RecursiveSampleFreshGivenLine4Past P :=
    S.recursiveSampleFreshGivenLine4Past_of_stochasticLaws P h_laws
  let repState : Line4PastKey S t → State (E := E) :=
    fun k =>
      if h : ∃ ω : Ω, line4PastKey S t ω = k then
        S.process t (Classical.choose h)
      else
        { x := 0, g := 0 }
  let oldErrorSqKey : Line4PastKey S t → ℝ :=
    fun k => ‖(repState k).g - S.fullGradient (repState k).x‖ ^ 2
  have h_oldError_key :
      ∀ ω : Ω, oldErrorSqKey (line4PastKey S t ω) = ‖oldError ω‖ ^ 2 := by
    intro ω
    have hrange : ∃ ω' : Ω, line4PastKey S t ω' = line4PastKey S t ω := ⟨ω, rfl⟩
    have hchosen :
        line4PastKey S t (Classical.choose hrange) = line4PastKey S t ω :=
      Classical.choose_spec hrange
    have hproc :
        S.process t (Classical.choose hrange) = S.process t ω :=
      process_eq_of_line4_past_key_eq (S := S) t hchosen
    simp [oldErrorSqKey, repState, hrange, oldError, iterate, estimator, hproc]
  have h_false_oldError_factor :
      (∫ ω : Ω,
          (if S.refreshBranch t ω = false then ‖oldError ω‖ ^ 2 else 0) ∂P) =
        ∫ ω : Ω,
          (1 - S.refreshProbability t) * ‖oldError ω‖ ^ 2 ∂P := by
    have hkey_factor :=
      line4_false_branch_key_integral_factor (S := S) P h_laws t oldErrorSqKey
    calc
      (∫ ω : Ω,
          (if S.refreshBranch t ω = false then ‖oldError ω‖ ^ 2 else 0) ∂P)
          =
        ∫ ω : Ω,
          (if S.refreshBranch t ω = false then
            oldErrorSqKey (line4PastKey S t ω)
          else
            0) ∂P := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards with ω
            by_cases hbranch : S.refreshBranch t ω = false
            · simp [hbranch, h_oldError_key ω]
            · simp [hbranch]
      _ = ∫ ω : Ω,
            (1 - S.refreshProbability t) * oldErrorSqKey (line4PastKey S t ω) ∂P :=
            hkey_factor
      _ = ∫ ω : Ω,
            (1 - S.refreshProbability t) * ‖oldError ω‖ ^ 2 ∂P := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards with ω
            rw [h_oldError_key ω]
  let xPrevKey : Line4PastKey S t → E := fun k => (repState k).x
  let gPrevKey : Line4PastKey S t → E := fun k => (repState k).g
  let xCurrKey : Line4PastKey S t → E :=
    fun k => S.primalUpdate (xPrevKey k) (gPrevKey k)
  let oldErrorKey : Line4PastKey S t → E :=
    fun k => gPrevKey k - S.fullGradient (xPrevKey k)
  let rowIncrementKey : Line4PastKey S t → (B' → ι) → E :=
    fun k r =>
      ((Fintype.card B' : ℝ)⁻¹) •
        Finset.sum Finset.univ
          (fun j : B' =>
            (S.componentGradient (r j) (xCurrKey k) -
              S.componentGradient (r j) (xPrevKey k)) -
            (S.componentAverageGradient (xCurrKey k) -
              S.componentAverageGradient (xPrevKey k)))
  have h_false_cross_row_transport :
      (∫ ω : Ω,
          (if S.refreshBranch t ω = false then
            inner ℝ (oldErrorKey (line4PastKey S t ω))
              (rowIncrementKey (line4PastKey S t ω)
                (fun j : B' => S.recursiveSample t j ω))
          else
            0) ∂P) =
        ∫ ω : Ω,
          (1 - S.refreshProbability t) *
            ((Fintype.card (B' → ι) : ℝ)⁻¹ *
              Finset.univ.sum
                (fun r : B' → ι =>
                  inner ℝ (oldErrorKey (line4PastKey S t ω))
                    (rowIncrementKey (line4PastKey S t ω) r))) ∂P := by
    exact
      line4_false_branch_recursive_row_integral (S := S) P h_laws t
        (fun k r => inner ℝ (oldErrorKey k) (rowIncrementKey k r))
  have h_rowIncrementKey_average_zero :
      ∀ k : Line4PastKey S t,
        SOptLib.finiteUniformAverage
          (fun r : B' → ι => rowIncrementKey k r) = 0 := by
    intro k
    let atom : B' → (B' → ι) → E := fun j r =>
      (S.componentGradient (r j) (xCurrKey k) -
        S.componentGradient (r j) (xPrevKey k)) -
      (S.componentAverageGradient (xCurrKey k) -
        S.componentAverageGradient (xPrevKey k))
    have hcoord_avg :
        ∀ j : B',
          SOptLib.finiteUniformAverage (fun r : B' → ι => atom j r) = 0 := by
      intro j
      have hbase :
          SOptLib.finiteUniformAverage
              (fun i : ι =>
                (S.componentGradient i (xCurrKey k) -
                  S.componentGradient i (xPrevKey k)) -
                (S.componentAverageGradient (xCurrKey k) -
                  S.componentAverageGradient (xPrevKey k))) = 0 := by
        have hpop := h_population_centered (xCurrKey k) (xPrevKey k)
        rw [S.averageLSmooth_fullGradient_eq_componentAverageGradient hL
            (xCurrKey k),
          S.averageLSmooth_fullGradient_eq_componentAverageGradient hL
            (xPrevKey k)] at hpop
        exact hpop
      simpa [atom] using
        finiteUniformAverage_function_eval_eq_zero_of_average_zero
          (α := B') (β := ι) (V := E) j
          (fun i : ι =>
            (S.componentGradient i (xCurrKey k) -
              S.componentGradient i (xPrevKey k)) -
            (S.componentAverageGradient (xCurrKey k) -
              S.componentAverageGradient (xPrevKey k)))
          hbase
    have hcoord_sum :
        ∀ j : B',
          Finset.univ.sum (fun r : B' → ι => atom j r) = 0 := by
      intro j
      have hcard_ne : (Fintype.card (B' → ι) : ℝ)⁻¹ ≠ 0 := by
        exact inv_ne_zero
          (by exact_mod_cast
            (Fintype.card_ne_zero : Fintype.card (B' → ι) ≠ 0))
      have hj := hcoord_avg j
      rw [SOptLib.finiteUniformAverage_def] at hj
      exact (smul_eq_zero.mp hj).resolve_left hcard_ne
    have hrow :
        ∀ r : B' → ι,
          rowIncrementKey k r =
            (Fintype.card B' : ℝ)⁻¹ • Finset.univ.sum (fun j : B' => atom j r) := by
      intro r
      rfl
    rw [SOptLib.finiteUniformAverage_def]
    simp only [hrow]
    rw [← Finset.smul_sum]
    rw [Finset.sum_comm]
    simp [hcoord_sum]
  have h_cross_row_fiber_zero :
      ∀ k : Line4PastKey S t,
        (Fintype.card (B' → ι) : ℝ)⁻¹ *
          Finset.univ.sum
            (fun r : B' → ι => inner ℝ (oldErrorKey k) (rowIncrementKey k r)) = 0 := by
    intro k
    have hmean := h_rowIncrementKey_average_zero k
    rw [SOptLib.finiteUniformAverage_def] at hmean
    calc
      (Fintype.card (B' → ι) : ℝ)⁻¹ *
          Finset.univ.sum
            (fun r : B' → ι => inner ℝ (oldErrorKey k) (rowIncrementKey k r))
          =
        inner ℝ (oldErrorKey k)
          ((Fintype.card (B' → ι) : ℝ)⁻¹ •
            Finset.univ.sum (fun r : B' → ι => rowIncrementKey k r)) := by
          rw [inner_smul_right, inner_sum]
      _ = 0 := by
          rw [hmean]
          simp
  have h_false_cross_zero_key :
      (∫ ω : Ω,
          (if S.refreshBranch t ω = false then
            inner ℝ (oldErrorKey (line4PastKey S t ω))
              (rowIncrementKey (line4PastKey S t ω)
                (fun j : B' => S.recursiveSample t j ω))
          else
            0) ∂P) = 0 := by
    rw [h_false_cross_row_transport]
    calc
      (∫ ω : Ω,
          (1 - S.refreshProbability t) *
            ((Fintype.card (B' → ι) : ℝ)⁻¹ *
              Finset.univ.sum
                (fun r : B' → ι =>
                  inner ℝ (oldErrorKey (line4PastKey S t ω))
                    (rowIncrementKey (line4PastKey S t ω) r))) ∂P)
          = ∫ ω : Ω, 0 ∂P := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards with ω
            rw [h_cross_row_fiber_zero (line4PastKey S t ω)]
            simp
      _ = 0 := by
            simp
  have h_oldError_vec_key :
      ∀ ω : Ω, oldErrorKey (line4PastKey S t ω) = oldError ω := by
    intro ω
    have hrange : ∃ ω' : Ω, line4PastKey S t ω' = line4PastKey S t ω := ⟨ω, rfl⟩
    have hchosen :
        line4PastKey S t (Classical.choose hrange) = line4PastKey S t ω :=
      Classical.choose_spec hrange
    have hproc :
        S.process t (Classical.choose hrange) = S.process t ω :=
      process_eq_of_line4_past_key_eq (S := S) t hchosen
    simp [oldErrorKey, xPrevKey, gPrevKey, repState, hrange, oldError,
      iterate, estimator, hproc]
  have h_rowIncrement_key :
      ∀ ω : Ω,
        rowIncrementKey (line4PastKey S t ω)
            (fun j : B' => S.recursiveSample t j ω) =
          centeredIncrement ω := by
    intro ω
    have hrange : ∃ ω' : Ω, line4PastKey S t ω' = line4PastKey S t ω := ⟨ω, rfl⟩
    have hchosen :
        line4PastKey S t (Classical.choose hrange) = line4PastKey S t ω :=
      Classical.choose_spec hrange
    have hproc :
        S.process t (Classical.choose hrange) = S.process t ω :=
      process_eq_of_line4_past_key_eq (S := S) t hchosen
    have hcurr :
        xCurrKey (line4PastKey S t ω) = S.iterate (t + 1) ω := by
      simp [xCurrKey, xPrevKey, gPrevKey, repState, hrange, iterate, estimator,
        hproc, S.iterate_succ t ω, stateUpdate, primalUpdate]
    simp [rowIncrementKey, xPrevKey, repState, hrange, centeredIncrement,
      iterate, hproc, hcurr]
  have h_false_cross_zero :
      (∫ ω : Ω,
          (if S.refreshBranch t ω = false then
            inner ℝ (oldError ω) (centeredIncrement ω)
          else
            0) ∂P) = 0 := by
    calc
      (∫ ω : Ω,
          (if S.refreshBranch t ω = false then
            inner ℝ (oldError ω) (centeredIncrement ω)
          else
            0) ∂P)
          =
        ∫ ω : Ω,
          (if S.refreshBranch t ω = false then
            inner ℝ (oldErrorKey (line4PastKey S t ω))
              (rowIncrementKey (line4PastKey S t ω)
                (fun j : B' => S.recursiveSample t j ω))
          else
            0) ∂P := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards with ω
            by_cases hbranch : S.refreshBranch t ω = false
            · simp [hbranch, h_oldError_vec_key ω, h_rowIncrement_key ω]
            · simp [hbranch]
      _ = 0 := h_false_cross_zero_key
  have h_rowIncrementKey_fiber_secondMoment_le :
      ∀ k : Line4PastKey S t,
        (Fintype.card (B' → ι) : ℝ)⁻¹ *
            Finset.univ.sum
              (fun r : B' → ι => ‖rowIncrementKey k r‖ ^ 2) ≤
          L ^ 2 / (Fintype.card B' : ℝ) *
            ‖xCurrKey k - xPrevKey k‖ ^ 2 := by
    intro k
    let raw : ι → E := fun i =>
      S.componentGradient i (xCurrKey k) -
        S.componentGradient i (xPrevKey k)
    let mean : E :=
      S.componentAverageGradient (xCurrKey k) -
        S.componentAverageGradient (xPrevKey k)
    let atom : ι → E := fun i => raw i - mean
    have hcenter : SOptLib.finiteUniformAverage atom = 0 := by
      have hpop := h_population_centered (xCurrKey k) (xPrevKey k)
      rw [S.averageLSmooth_fullGradient_eq_componentAverageGradient hL
          (xCurrKey k),
        S.averageLSmooth_fullGradient_eq_componentAverageGradient hL
          (xPrevKey k)] at hpop
      simpa [atom, raw, mean] using hpop
    have hrow :
        (Fintype.card (B' → ι) : ℝ)⁻¹ *
            Finset.univ.sum
              (fun r : B' → ι =>
                ‖((Fintype.card B' : ℝ)⁻¹) •
                  Finset.univ.sum (fun j : B' => atom (r j))‖ ^ 2) ≤
          SOptLib.finiteUniformAverage (fun i : ι => ‖atom i‖ ^ 2) /
            (Fintype.card B' : ℝ) :=
      finite_function_row_centered_average_secondMoment_le
        (α := B') (β := ι) (V := E) atom hcenter
    have hqsum :
        Finset.univ.sum (fun _i : ι => (Fintype.card ι : ℝ)⁻¹) = 1 := by
      have hcard : (Fintype.card ι : ℝ) ≠ 0 := by
        exact_mod_cast (Fintype.card_ne_zero : Fintype.card ι ≠ 0)
      simp [Finset.sum_const, hcard]
    have hmean_weighted :
        Finset.univ.sum
            (fun i : ι => (Fintype.card ι : ℝ)⁻¹ • raw i) = mean := by
      rw [← Finset.smul_sum]
      simp [raw, mean, componentAverageGradient, SOptLib.finiteUniformAverage_def,
        Finset.sum_sub_distrib, smul_sub]
    have hcenter_budget :
        SOptLib.finiteUniformAverage (fun i : ι => ‖atom i‖ ^ 2) ≤
          SOptLib.finiteUniformAverage (fun i : ι => ‖raw i‖ ^ 2) := by
      have hw :=
        Finset.weighted_variance_le_second_moment
          (s := (Finset.univ : Finset ι))
          (q := fun _i : ι => (Fintype.card ι : ℝ)⁻¹)
          (a := raw) (μ := mean) hqsum hmean_weighted
      simpa [SOptLib.finiteUniformAverage_def, atom, Finset.mul_sum] using hw
    have hsmooth :
        SOptLib.finiteUniformAverage (fun i : ι => ‖raw i‖ ^ 2) ≤
          L ^ 2 * ‖xCurrKey k - xPrevKey k‖ ^ 2 := by
      simpa [raw] using hL.2.2 (xCurrKey k) (xPrevKey k)
    have hcardB'_nonneg : 0 ≤ (Fintype.card B' : ℝ) := by positivity
    calc
      (Fintype.card (B' → ι) : ℝ)⁻¹ *
          Finset.univ.sum
            (fun r : B' → ι => ‖rowIncrementKey k r‖ ^ 2)
          ≤ SOptLib.finiteUniformAverage (fun i : ι => ‖atom i‖ ^ 2) /
              (Fintype.card B' : ℝ) := by
            simpa [rowIncrementKey, atom, raw, mean] using hrow
      _ ≤ SOptLib.finiteUniformAverage (fun i : ι => ‖raw i‖ ^ 2) /
              (Fintype.card B' : ℝ) := by
            exact div_le_div_of_nonneg_right hcenter_budget hcardB'_nonneg
      _ ≤ (L ^ 2 * ‖xCurrKey k - xPrevKey k‖ ^ 2) /
              (Fintype.card B' : ℝ) := by
            exact div_le_div_of_nonneg_right hsmooth hcardB'_nonneg
      _ = L ^ 2 / (Fintype.card B' : ℝ) *
              ‖xCurrKey k - xPrevKey k‖ ^ 2 := by
            ring
  have h_fiber_whole_square_le :
      ∀ k : Line4PastKey S t,
        (Fintype.card (B' → ι) : ℝ)⁻¹ *
            Finset.univ.sum
              (fun r : B' → ι =>
                ‖oldErrorKey k + rowIncrementKey k r‖ ^ 2) ≤
          ‖oldErrorKey k‖ ^ 2 +
            L ^ 2 / (Fintype.card B' : ℝ) *
              ‖xCurrKey k - xPrevKey k‖ ^ 2 := by
    intro k
    have hcard_row_ne : (Fintype.card (B' → ι) : ℝ) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card (B' → ι) ≠ 0)
    have hcard_i_ne : (Fintype.card ι : ℝ) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card ι ≠ 0)
    have hcard_i_pow_ne :
        (Fintype.card ι : ℝ) ^ Fintype.card B' ≠ 0 :=
      pow_ne_zero _ hcard_i_ne
    have hdecomp :
        (Fintype.card (B' → ι) : ℝ)⁻¹ *
            Finset.univ.sum
              (fun r : B' → ι =>
                ‖oldErrorKey k + rowIncrementKey k r‖ ^ 2) =
          ‖oldErrorKey k‖ ^ 2 +
            (Fintype.card (B' → ι) : ℝ)⁻¹ *
              Finset.univ.sum
                (fun r : B' → ι => ‖rowIncrementKey k r‖ ^ 2) := by
      calc
        (Fintype.card (B' → ι) : ℝ)⁻¹ *
            Finset.univ.sum
              (fun r : B' → ι =>
                ‖oldErrorKey k + rowIncrementKey k r‖ ^ 2)
            =
          (Fintype.card (B' → ι) : ℝ)⁻¹ *
            Finset.univ.sum
              (fun r : B' → ι =>
                ‖oldErrorKey k‖ ^ 2 +
                  2 * inner ℝ (oldErrorKey k) (rowIncrementKey k r) +
                  ‖rowIncrementKey k r‖ ^ 2) := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro r _hr
            rw [norm_add_sq_real]
        _ =
          ‖oldErrorKey k‖ ^ 2 +
            2 *
              ((Fintype.card (B' → ι) : ℝ)⁻¹ *
                Finset.univ.sum
                  (fun r : B' → ι =>
                    inner ℝ (oldErrorKey k) (rowIncrementKey k r))) +
            (Fintype.card (B' → ι) : ℝ)⁻¹ *
              Finset.univ.sum
                (fun r : B' → ι => ‖rowIncrementKey k r‖ ^ 2) := by
            simp [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const,
              hcard_row_ne]
            rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
              ← Finset.mul_sum]
            field_simp [hcard_row_ne, hcard_i_ne, hcard_i_pow_ne]
        _ =
          ‖oldErrorKey k‖ ^ 2 +
            (Fintype.card (B' → ι) : ℝ)⁻¹ *
              Finset.univ.sum
                (fun r : B' → ι => ‖rowIncrementKey k r‖ ^ 2) := by
            rw [h_cross_row_fiber_zero k]
            ring
    calc
      (Fintype.card (B' → ι) : ℝ)⁻¹ *
          Finset.univ.sum
            (fun r : B' → ι =>
              ‖oldErrorKey k + rowIncrementKey k r‖ ^ 2)
          =
        ‖oldErrorKey k‖ ^ 2 +
          (Fintype.card (B' → ι) : ℝ)⁻¹ *
            Finset.univ.sum
              (fun r : B' → ι => ‖rowIncrementKey k r‖ ^ 2) := hdecomp
      _ ≤ ‖oldErrorKey k‖ ^ 2 +
          L ^ 2 / (Fintype.card B' : ℝ) *
            ‖xCurrKey k - xPrevKey k‖ ^ 2 := by
          have h :=
            add_le_add_left (h_rowIncrementKey_fiber_secondMoment_le k)
              (‖oldErrorKey k‖ ^ 2)
          linarith
  have h_false_square_transport :
      (∫ ω : Ω,
          (if S.refreshBranch t ω = false then
            ‖oldErrorKey (line4PastKey S t ω) +
              rowIncrementKey (line4PastKey S t ω)
                (fun j : B' => S.recursiveSample t j ω)‖ ^ 2
          else
            0) ∂P) =
        ∫ ω : Ω,
          (1 - S.refreshProbability t) *
            ((Fintype.card (B' → ι) : ℝ)⁻¹ *
              Finset.univ.sum
                (fun r : B' → ι =>
                  ‖oldErrorKey (line4PastKey S t ω) +
                    rowIncrementKey (line4PastKey S t ω) r‖ ^ 2)) ∂P := by
    exact
      line4_false_branch_recursive_row_integral (S := S) P h_laws t
        (fun k r => ‖oldErrorKey k + rowIncrementKey k r‖ ^ 2)
  have h_xPrevKey :
      ∀ ω : Ω, xPrevKey (line4PastKey S t ω) = S.iterate t ω := by
    intro ω
    have hrange : ∃ ω' : Ω, line4PastKey S t ω' = line4PastKey S t ω := ⟨ω, rfl⟩
    have hchosen :
        line4PastKey S t (Classical.choose hrange) = line4PastKey S t ω :=
      Classical.choose_spec hrange
    have hproc :
        S.process t (Classical.choose hrange) = S.process t ω :=
      process_eq_of_line4_past_key_eq (S := S) t hchosen
    simp [xPrevKey, repState, hrange, iterate, hproc]
  have h_xCurrKey :
      ∀ ω : Ω, xCurrKey (line4PastKey S t ω) = S.iterate (t + 1) ω := by
    intro ω
    have hrange : ∃ ω' : Ω, line4PastKey S t ω' = line4PastKey S t ω := ⟨ω, rfl⟩
    have hchosen :
        line4PastKey S t (Classical.choose hrange) = line4PastKey S t ω :=
      Classical.choose_spec hrange
    have hproc :
        S.process t (Classical.choose hrange) = S.process t ω :=
      process_eq_of_line4_past_key_eq (S := S) t hchosen
    simp [xCurrKey, xPrevKey, gPrevKey, repState, hrange, iterate, estimator,
      hproc, S.iterate_succ t ω, stateUpdate, primalUpdate]
  have h_lhs_false_square :
      (∫ ω : Ω,
          ‖S.estimator (t + 1) ω -
            S.fullGradient (S.iterate (t + 1) ω)‖ ^ 2 ∂P) =
        ∫ ω : Ω,
          (if S.refreshBranch t ω = false then
            ‖oldErrorKey (line4PastKey S t ω) +
              rowIncrementKey (line4PastKey S t ω)
                (fun j : B' => S.recursiveSample t j ω)‖ ^ 2
          else
            0) ∂P := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with ω
    rw [h_decomp ω]
    by_cases hbranch : S.refreshBranch t ω
    · simp [hbranch]
    · have hfalse : S.refreshBranch t ω = false := by
        simpa using hbranch
      simp [hbranch, hfalse, h_oldError_vec_key ω, h_rowIncrement_key ω]
  have h_false_square_le :
      (∫ ω : Ω,
          (if S.refreshBranch t ω = false then
            ‖oldErrorKey (line4PastKey S t ω) +
              rowIncrementKey (line4PastKey S t ω)
                (fun j : B' => S.recursiveSample t j ω)‖ ^ 2
          else
            0) ∂P) ≤
        ∫ ω : Ω,
          (1 - S.refreshProbability t) *
            (‖oldErrorKey (line4PastKey S t ω)‖ ^ 2 +
              L ^ 2 / (Fintype.card B' : ℝ) *
                ‖xCurrKey (line4PastKey S t ω) -
                  xPrevKey (line4PastKey S t ω)‖ ^ 2) ∂P := by
    exact
      line4_false_branch_recursive_row_integral_le_key_bound (S := S) P h_laws t
        (fun k r => ‖oldErrorKey k + rowIncrementKey k r‖ ^ 2)
        (fun k =>
          ‖oldErrorKey k‖ ^ 2 +
            L ^ 2 / (Fintype.card B' : ℝ) *
              ‖xCurrKey k - xPrevKey k‖ ^ 2)
        h_fiber_whole_square_le
  have h_key_rhs :
      (∫ ω : Ω,
          (1 - S.refreshProbability t) *
            (‖oldErrorKey (line4PastKey S t ω)‖ ^ 2 +
              L ^ 2 / (Fintype.card B' : ℝ) *
                ‖xCurrKey (line4PastKey S t ω) -
                  xPrevKey (line4PastKey S t ω)‖ ^ 2) ∂P) =
        ∫ ω : Ω,
          (1 - S.refreshProbability t) *
            ‖S.estimator t ω - S.fullGradient (S.iterate t ω)‖ ^ 2 +
          (((1 - S.refreshProbability t) * L ^ 2) / (Fintype.card B' : ℝ)) *
            ‖S.iterate (t + 1) ω - S.iterate t ω‖ ^ 2 ∂P := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with ω
    rw [h_oldError_vec_key ω, h_xCurrKey ω, h_xPrevKey ω]
    ring
  calc
    (∫ ω : Ω,
        ‖S.estimator (t + 1) ω -
          S.fullGradient (S.iterate (t + 1) ω)‖ ^ 2 ∂P)
        =
      ∫ ω : Ω,
        (if S.refreshBranch t ω = false then
          ‖oldErrorKey (line4PastKey S t ω) +
            rowIncrementKey (line4PastKey S t ω)
              (fun j : B' => S.recursiveSample t j ω)‖ ^ 2
        else
          0) ∂P := h_lhs_false_square
    _ ≤
      ∫ ω : Ω,
        (1 - S.refreshProbability t) *
          (‖oldErrorKey (line4PastKey S t ω)‖ ^ 2 +
            L ^ 2 / (Fintype.card B' : ℝ) *
              ‖xCurrKey (line4PastKey S t ω) -
                xPrevKey (line4PastKey S t ω)‖ ^ 2) ∂P := h_false_square_le
    _ =
      ∫ ω : Ω,
        (1 - S.refreshProbability t) *
          ‖S.estimator t ω - S.fullGradient (S.iterate t ω)‖ ^ 2 +
        (((1 - S.refreshProbability t) * L ^ 2) / (Fintype.card B' : ℝ)) *
          ‖S.iterate (t + 1) ω - S.iterate t ω‖ ^ 2 ∂P := h_key_rhs

@[simp]
theorem theoremOneIterationCount_def (L p ε : ℝ) :
    S.theoremOneIterationCount L p ε =
      2 * S.initialGap * L / ε ^ 2 *
        (1 + Real.sqrt ((1 - p) / (p * (Fintype.card B' : ℝ)))) := by
  rfl

theorem theoremOneIterationCount_eq_eta_horizon_of_outputSchedule {L p ε : ℝ}
    (h_schedule : S.TheoremOneOutputSchedule L p) (hε : 0 < ε) :
    S.theoremOneIterationCount L p ε =
      2 * S.initialGap / (ε ^ 2 * S.η) := by
  let scale : ℝ :=
    L * (1 + Real.sqrt ((1 - p) / (p * (Fintype.card B' : ℝ))))
  have hη_eq : S.η = scale⁻¹ := by
    simpa [scale] using h_schedule.2.1
  have hscale_inv_pos : 0 < scale⁻¹ := by
    simpa [hη_eq] using h_schedule.1
  have hscale_pos : 0 < scale := inv_pos.mp hscale_inv_pos
  have hscale_ne : scale ≠ 0 := ne_of_gt hscale_pos
  have hε_ne : ε ≠ 0 := ne_of_gt hε
  simp [theoremOneIterationCount, scale, hη_eq]
  field_simp [hscale_ne, hε_ne]

theorem theoremOneIterationCount_eq_eta_horizon {L p ε : ℝ}
    (h_schedule : S.TheoremOneSchedule L p) (hε : 0 < ε) :
    S.theoremOneIterationCount L p ε =
      2 * S.initialGap / (ε ^ 2 * S.η) := by
  exact
    S.theoremOneIterationCount_eq_eta_horizon_of_outputSchedule
      (S.theoremOneSchedule_outputSchedule h_schedule) hε

theorem theoremOne_eta_horizon_bound_of_outputSchedule {L p ε : ℝ} {T : ℕ} [NeZero T]
    (h_schedule : S.TheoremOneOutputSchedule L p) (hε : 0 < ε)
    (hT : S.theoremOneIterationCount L p ε ≤ (T : ℝ)) :
    2 * S.initialGap / (S.η * (T : ℝ)) ≤ ε ^ 2 := by
  have hcount_eq := S.theoremOneIterationCount_eq_eta_horizon_of_outputSchedule h_schedule hε
  have hT_eta : 2 * S.initialGap / (ε ^ 2 * S.η) ≤ (T : ℝ) := by
    rwa [hcount_eq] at hT
  have hη_pos : 0 < S.η := h_schedule.1
  have hε_sq_pos : 0 < ε ^ 2 := sq_pos_of_ne_zero hε.ne'
  have hden_count_pos : 0 < ε ^ 2 * S.η := mul_pos hε_sq_pos hη_pos
  have hT_nat_pos : 0 < T := Nat.pos_of_neZero T
  have hT_pos : 0 < (T : ℝ) := by
    exact_mod_cast hT_nat_pos
  have hcleared :
      2 * S.initialGap ≤ (T : ℝ) * (ε ^ 2 * S.η) :=
    (div_le_iff₀ hden_count_pos).mp hT_eta
  rw [div_le_iff₀ (mul_pos hη_pos hT_pos)]
  convert hcleared using 1
  ring

theorem theoremOne_eta_horizon_bound {L p ε : ℝ} {T : ℕ} [NeZero T]
    (h_schedule : S.TheoremOneSchedule L p) (hε : 0 < ε)
    (hT : S.theoremOneIterationCount L p ε ≤ (T : ℝ)) :
    2 * S.initialGap / (S.η * (T : ℝ)) ≤ ε ^ 2 := by
  exact
    S.theoremOne_eta_horizon_bound_of_outputSchedule
      (S.theoremOneSchedule_outputSchedule h_schedule) hε hT

@[simp]
theorem theoremOneGradientComplexity_def (L p ε : ℝ) :
    S.theoremOneGradientComplexity L p ε =
      (Fintype.card B : ℝ) +
        S.theoremOneIterationCount L p ε *
          (p * (Fintype.card B : ℝ) + (1 - p) * (Fintype.card B' : ℝ)) := by
  rfl

private theorem selected_gradient_norm_fiber_integrable_of_stochastic_laws
    [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (h_laws : S.StochasticLaws P) (k : ℕ) :
    MeasureTheory.Integrable
      (fun ω : Ω => ‖S.fullGradient (S.iterate k ω)‖) P := by
  classical
  letI : MeasurableSpace ι := ⊤
  unfold StochasticLaws at h_laws
  rcases h_laws with ⟨hp, hmap⟩
  let gradNormKey : Line4PastKey S k → ℝ := fun key =>
    if hrange : ∃ ω : Ω, line4PastKey S k ω = key then
      ‖S.fullGradient (S.iterate k (Classical.choose hrange))‖
    else
      0
  have hbridge := line4_past_key_branch_pair_bridge (S := S) P hp hmap k
  have hkey_aemeas :
      AEMeasurable (fun ω : Ω => line4PastKey S k ω) P :=
    hbridge.1.fst
  have hpoint :
      ∀ ω : Ω,
        gradNormKey (line4PastKey S k ω) =
          ‖S.fullGradient (S.iterate k ω)‖ := by
    intro ω
    have hrange : ∃ ω' : Ω, line4PastKey S k ω' = line4PastKey S k ω :=
      ⟨ω, rfl⟩
    have hchosen :
        line4PastKey S k (Classical.choose hrange) = line4PastKey S k ω :=
      Classical.choose_spec hrange
    have hproc : S.process k (Classical.choose hrange) = S.process k ω :=
      process_eq_of_line4_past_key_eq (S := S) k hchosen
    simp [gradNormKey, hrange, iterate, hproc]
  have haestrong :
      MeasureTheory.AEStronglyMeasurable
        (fun ω : Ω => ‖S.fullGradient (S.iterate k ω)‖) P := by
    refine
      aestronglyMeasurable_of_countable_key_reconstruction
        (μ := P) (Y := fun ω : Ω => line4PastKey S k ω)
        (Z := fun ω : Ω => ‖S.fullGradient (S.iterate k ω)‖)
        hkey_aemeas gradNormKey ?_
    exact Filter.Eventually.of_forall hpoint
  have hfin :
      (Set.range (fun ω : Ω => ‖S.fullGradient (S.iterate k ω)‖)).Finite := by
    have hsubset :
        Set.range (fun ω : Ω => ‖S.fullGradient (S.iterate k ω)‖) ⊆
          gradNormKey '' Set.range (fun ω : Ω => line4PastKey S k ω) := by
      rintro z ⟨ω, rfl⟩
      exact ⟨line4PastKey S k ω, ⟨ω, rfl⟩, hpoint ω⟩
    exact ((Set.toFinite (Set.range (fun ω : Ω => line4PastKey S k ω))).image
      gradNormKey).subset hsubset
  exact integrable_of_finite_range haestrong hfin

private theorem selected_gradient_norm_integrable_of_fiber_integrable
    [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    {T : ℕ} [NeZero T]
    (hfiber :
      ∀ k : Fin T,
        MeasureTheory.Integrable
          (fun ω : Ω => ‖S.fullGradient (S.iterate k.val ω)‖) P) :
    S.SelectedGradientNormIntegrable P T := by
  simpa [SelectedGradientNormIntegrable, outputJointLaw, selectedGradientNormIntegrand,
    uniformOutput, SOptLib.selected_joint_measure] using
    (integrable_finite_index_first_prod_of_fiber_integrable
      (ν := (outputIndexLaw T).toMeasure) (μ := P)
      (F := fun k : Fin T => fun ω : Ω => ‖S.fullGradient (S.iterate k.val ω)‖)
      hfiber)

private theorem selected_gradient_norm_sq_fiber_integrable_of_stochastic_laws
    [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (h_laws : S.StochasticLaws P) (k : ℕ) :
    MeasureTheory.Integrable
      (fun ω : Ω => ‖S.fullGradient (S.iterate k ω)‖ ^ 2) P := by
  classical
  letI : MeasurableSpace ι := ⊤
  unfold StochasticLaws at h_laws
  rcases h_laws with ⟨hp, hmap⟩
  let gradNormSqKey : Line4PastKey S k → ℝ := fun key =>
    if hrange : ∃ ω : Ω, line4PastKey S k ω = key then
      ‖S.fullGradient (S.iterate k (Classical.choose hrange))‖ ^ 2
    else
      0
  have hbridge := line4_past_key_branch_pair_bridge (S := S) P hp hmap k
  have hkey_aemeas :
      AEMeasurable (fun ω : Ω => line4PastKey S k ω) P :=
    hbridge.1.fst
  have hpoint :
      ∀ ω : Ω,
        gradNormSqKey (line4PastKey S k ω) =
          ‖S.fullGradient (S.iterate k ω)‖ ^ 2 := by
    intro ω
    have hrange : ∃ ω' : Ω, line4PastKey S k ω' = line4PastKey S k ω :=
      ⟨ω, rfl⟩
    have hchosen :
        line4PastKey S k (Classical.choose hrange) = line4PastKey S k ω :=
      Classical.choose_spec hrange
    have hproc : S.process k (Classical.choose hrange) = S.process k ω :=
      process_eq_of_line4_past_key_eq (S := S) k hchosen
    simp [gradNormSqKey, hrange, iterate, hproc]
  have haestrong :
      MeasureTheory.AEStronglyMeasurable
        (fun ω : Ω => ‖S.fullGradient (S.iterate k ω)‖ ^ 2) P := by
    refine
      aestronglyMeasurable_of_countable_key_reconstruction
        (μ := P) (Y := fun ω : Ω => line4PastKey S k ω)
        (Z := fun ω : Ω => ‖S.fullGradient (S.iterate k ω)‖ ^ 2)
        hkey_aemeas gradNormSqKey ?_
    exact Filter.Eventually.of_forall hpoint
  have hfin :
      (Set.range (fun ω : Ω => ‖S.fullGradient (S.iterate k ω)‖ ^ 2)).Finite := by
    have hsubset :
        Set.range (fun ω : Ω => ‖S.fullGradient (S.iterate k ω)‖ ^ 2) ⊆
          gradNormSqKey '' Set.range (fun ω : Ω => line4PastKey S k ω) := by
      rintro z ⟨ω, rfl⟩
      exact ⟨line4PastKey S k ω, ⟨ω, rfl⟩, hpoint ω⟩
    exact ((Set.toFinite (Set.range (fun ω : Ω => line4PastKey S k ω))).image
      gradNormSqKey).subset hsubset
  exact integrable_of_finite_range haestrong hfin

/-- Every real observable of a fixed PAGE state is integrable under the
finite-valued random-source law.  This is the finite-past regularity bridge
used by the Lyapunov calculation below. -/
private theorem process_scalar_observable_integrable_of_stochastic_laws
    [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (h_laws : S.StochasticLaws P) (t : ℕ)
    (φ : State (E := E) → ℝ) :
    MeasureTheory.Integrable (fun ω : Ω => φ (S.process t ω)) P := by
  classical
  letI : MeasurableSpace ι := ⊤
  unfold StochasticLaws at h_laws
  rcases h_laws with ⟨hp, hmap⟩
  let scalarKey : Line4PastKey S t → ℝ := fun key =>
    if hrange : ∃ ω : Ω, line4PastKey S t ω = key then
      φ (S.process t (Classical.choose hrange))
    else
      0
  have hbridge := line4_past_key_branch_pair_bridge (S := S) P hp hmap t
  have hkey_aemeas :
      AEMeasurable (fun ω : Ω => line4PastKey S t ω) P :=
    hbridge.1.fst
  have hpoint :
      ∀ ω : Ω, scalarKey (line4PastKey S t ω) = φ (S.process t ω) := by
    intro ω
    have hrange : ∃ ω' : Ω, line4PastKey S t ω' = line4PastKey S t ω :=
      ⟨ω, rfl⟩
    have hchosen :
        line4PastKey S t (Classical.choose hrange) = line4PastKey S t ω :=
      Classical.choose_spec hrange
    have hproc :
        S.process t (Classical.choose hrange) = S.process t ω :=
      process_eq_of_line4_past_key_eq (S := S) t hchosen
    simp [scalarKey, hrange, hproc]
  have haestrong :
      MeasureTheory.AEStronglyMeasurable
        (fun ω : Ω => φ (S.process t ω)) P := by
    refine
      aestronglyMeasurable_of_countable_key_reconstruction
        (μ := P) (Y := fun ω : Ω => line4PastKey S t ω)
        (Z := fun ω : Ω => φ (S.process t ω))
        hkey_aemeas scalarKey ?_
    exact Filter.Eventually.of_forall hpoint
  have hfin :
      (Set.range (fun ω : Ω => φ (S.process t ω))).Finite := by
    have hsubset :
        Set.range (fun ω : Ω => φ (S.process t ω)) ⊆
          scalarKey '' Set.range (fun ω : Ω => line4PastKey S t ω) := by
      rintro z ⟨ω, rfl⟩
      exact ⟨line4PastKey S t ω, ⟨ω, rfl⟩, hpoint ω⟩
    exact ((Set.toFinite (Set.range (fun ω : Ω => line4PastKey S t ω))).image
      scalarKey).subset hsubset
  exact integrable_of_finite_range haestrong hfin

/-- The maximal PAGE stepsize makes the displacement coefficient in the
collected Lyapunov inequality nonnegative (Eq. (20)). -/
private theorem theoremOne_displacement_coefficient_nonneg
    {L p : ℝ} (h_average_smooth : S.AverageLSmooth L)
    (h_schedule : S.TheoremOneOutputSchedule L p) :
    0 ≤ (2 * S.η)⁻¹ - L / 2 -
      ((1 - p) * S.η * L ^ 2) /
        (2 * p * (Fintype.card B' : ℝ)) := by
  let b : ℝ := Fintype.card B'
  let r : ℝ := Real.sqrt ((1 - p) / (p * b))
  have hb_pos : 0 < b := by
    dsimp [b]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card B')
  have hp_pos : 0 < p := h_schedule.2.2.2.2.1
  have hp_le_one : p ≤ 1 := h_schedule.2.2.2.2.2
  have hratio_nonneg : 0 ≤ (1 - p) / (p * b) := by
    exact div_nonneg (sub_nonneg.mpr hp_le_one)
      (mul_nonneg hp_pos.le hb_pos.le)
  have hr_nonneg : 0 ≤ r := Real.sqrt_nonneg _
  have hrsq : r ^ 2 = (1 - p) / (p * b) := by
    simpa [r] using Real.sq_sqrt hratio_nonneg
  have hL_pos : 0 < L := h_average_smooth.1
  have hη_eq : S.η = (L * (1 + r))⁻¹ := by
    simpa [r, b] using h_schedule.2.1
  have hL_ne : L ≠ 0 := ne_of_gt hL_pos
  have hp_ne : p ≠ 0 := ne_of_gt hp_pos
  have hb_ne : b ≠ 0 := ne_of_gt hb_pos
  have hpb_ne : p * b ≠ 0 := mul_ne_zero hp_ne hb_ne
  have hrsq_clear : r ^ 2 * (p * b) = 1 - p :=
    (eq_div_iff hpb_ne).mp hrsq
  have hcore :
      0 ≤ L * ((1 + r) * r * p * b - (1 - p)) := by
    have hrpb_nonneg : 0 ≤ r * p * b :=
      mul_nonneg (mul_nonneg hr_nonneg hp_pos.le) hb_pos.le
    rw [← hrsq_clear]
    nlinarith [mul_nonneg hL_pos.le hrpb_nonneg]
  have h_one_add_r_pos : 0 < 1 + r := by linarith
  have h_one_add_r_ne : 1 + r ≠ 0 := ne_of_gt h_one_add_r_pos
  rw [hη_eq]
  dsimp [b] at hb_pos hcore ⊢
  field_simp [hL_ne, hp_ne, hb_ne, h_one_add_r_ne]
  nlinarith [hcore]

/-- Integrated PAGE Lyapunov step before the nonnegative displacement term is
dropped.  This is the Lean form of the collected inequality in Eq. (19). -/
private theorem page_integrated_lyapunov_step
    [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    {L p : ℝ} (h_average_smooth : S.AverageLSmooth L)
    (h_schedule : S.TheoremOneOutputSchedule L p)
    (h_laws : S.StochasticLaws P) (t : ℕ)
    (h_variance :
      (∫ ω : Ω,
          ‖S.estimator (t + 1) ω - S.fullGradient (S.iterate (t + 1) ω)‖ ^ 2 ∂P) ≤
        ∫ ω : Ω,
          (1 - S.refreshProbability t) *
              ‖S.estimator t ω - S.fullGradient (S.iterate t ω)‖ ^ 2 +
            (((1 - S.refreshProbability t) * L ^ 2) /
                (Fintype.card B' : ℝ)) *
              ‖S.iterate (t + 1) ω - S.iterate t ω‖ ^ 2 ∂P) :
    (∫ ω : Ω, S.objective (S.iterate (t + 1) ω) - S.fStar ∂P) +
          S.η / (2 * p) *
            (∫ ω : Ω,
              ‖S.estimator (t + 1) ω -
                S.fullGradient (S.iterate (t + 1) ω)‖ ^ 2 ∂P) ≤
      (∫ ω : Ω, S.objective (S.iterate t ω) - S.fStar ∂P) +
          S.η / (2 * p) *
            (∫ ω : Ω,
              ‖S.estimator t ω - S.fullGradient (S.iterate t ω)‖ ^ 2 ∂P) -
        (S.η / 2) *
          (∫ ω : Ω, ‖S.fullGradient (S.iterate t ω)‖ ^ 2 ∂P) -
        ((2 * S.η)⁻¹ - L / 2 -
            ((1 - p) * S.η * L ^ 2) /
              (2 * p * (Fintype.card B' : ℝ))) *
          (∫ ω : Ω,
            ‖S.iterate (t + 1) ω - S.iterate t ω‖ ^ 2 ∂P) := by
  classical
  let F : ℕ → ℝ := fun k =>
    ∫ ω : Ω, S.objective (S.iterate k ω) - S.fStar ∂P
  let R : ℕ → ℝ := fun k =>
    ∫ ω : Ω,
      ‖S.estimator k ω - S.fullGradient (S.iterate k ω)‖ ^ 2 ∂P
  let G : ℕ → ℝ := fun k =>
    ∫ ω : Ω, ‖S.fullGradient (S.iterate k ω)‖ ^ 2 ∂P
  let D : ℕ → ℝ := fun k =>
    ∫ ω : Ω, ‖S.iterate (k + 1) ω - S.iterate k ω‖ ^ 2 ∂P
  change
    F (t + 1) + S.η / (2 * p) * R (t + 1) ≤
      F t + S.η / (2 * p) * R t - (S.η / 2) * G t -
        ((2 * S.η)⁻¹ - L / 2 -
            ((1 - p) * S.η * L ^ 2) /
              (2 * p * (Fintype.card B' : ℝ))) * D t
  have hF_int : ∀ k : ℕ,
      MeasureTheory.Integrable
        (fun ω : Ω => S.objective (S.iterate k ω) - S.fStar) P := by
    intro k
    simpa [iterate] using
      (process_scalar_observable_integrable_of_stochastic_laws
        (S := S) P h_laws k
        (fun state : State (E := E) => S.objective state.x - S.fStar))
  have hR_int : ∀ k : ℕ,
      MeasureTheory.Integrable
        (fun ω : Ω =>
          ‖S.estimator k ω - S.fullGradient (S.iterate k ω)‖ ^ 2) P := by
    intro k
    simpa [iterate, estimator] using
      (process_scalar_observable_integrable_of_stochastic_laws
        (S := S) P h_laws k
        (fun state : State (E := E) =>
          ‖state.g - S.fullGradient state.x‖ ^ 2))
  have hG_int : ∀ k : ℕ,
      MeasureTheory.Integrable
        (fun ω : Ω => ‖S.fullGradient (S.iterate k ω)‖ ^ 2) P := by
    intro k
    simpa [iterate] using
      (process_scalar_observable_integrable_of_stochastic_laws
        (S := S) P h_laws k
        (fun state : State (E := E) => ‖S.fullGradient state.x‖ ^ 2))
  have hD_int : ∀ k : ℕ,
      MeasureTheory.Integrable
        (fun ω : Ω => ‖S.iterate (k + 1) ω - S.iterate k ω‖ ^ 2) P := by
    intro k
    have hraw :=
      process_scalar_observable_integrable_of_stochastic_laws
        (S := S) P h_laws k
        (fun state : State (E := E) => ‖-S.η • state.g‖ ^ 2)
    have hfun :
        (fun ω : Ω => ‖S.iterate (k + 1) ω - S.iterate k ω‖ ^ 2) =
          (fun ω : Ω => ‖-S.η • (S.process k ω).g‖ ^ 2) := by
      funext ω
      rw [S.iterate_succ_eq_sub_eta_smul]
      simp [iterate, estimator]
    rw [hfun]
    exact hraw
  let descentRhs : Ω → ℝ := fun ω =>
    (S.objective (S.iterate t ω) - S.fStar) -
        (S.η / 2) * ‖S.fullGradient (S.iterate t ω)‖ ^ 2 -
        ((2 * S.η)⁻¹ - L / 2) *
          ‖S.iterate (t + 1) ω - S.iterate t ω‖ ^ 2 +
      (S.η / 2) *
        ‖S.estimator t ω - S.fullGradient (S.iterate t ω)‖ ^ 2
  have hdescent_rhs_int : MeasureTheory.Integrable descentRhs P := by
    exact
      (((hF_int t).sub ((hG_int t).const_mul (S.η / 2))).sub
        ((hD_int t).const_mul ((2 * S.η)⁻¹ - L / 2))).add
          ((hR_int t).const_mul (S.η / 2))
  have hdescent_point : ∀ ω : Ω,
      S.objective (S.iterate (t + 1) ω) - S.fStar ≤ descentRhs ω := by
    intro ω
    have hdescent :=
      S.descent_with_inexact_gradient
        (S.averageLSmooth_implies_quadratic_upper_bound h_average_smooth)
        h_schedule.1 (S.iterate t ω) (S.estimator t ω)
    rw [← S.iterate_succ_eq_sub_eta_smul t ω] at hdescent
    dsimp [descentRhs]
    linarith
  have hdescent_mono :
      F (t + 1) ≤ ∫ ω : Ω, descentRhs ω ∂P := by
    exact MeasureTheory.integral_mono (hF_int (t + 1)) hdescent_rhs_int
      hdescent_point
  have hdescent_rhs_eq :
      (∫ ω : Ω, descentRhs ω ∂P) =
        F t - (S.η / 2) * G t -
            ((2 * S.η)⁻¹ - L / 2) * D t +
          (S.η / 2) * R t := by
    calc
      (∫ ω : Ω, descentRhs ω ∂P) =
          (∫ ω : Ω,
            (S.objective (S.iterate t ω) - S.fStar -
                (S.η / 2) * ‖S.fullGradient (S.iterate t ω)‖ ^ 2 -
              ((2 * S.η)⁻¹ - L / 2) *
                ‖S.iterate (t + 1) ω - S.iterate t ω‖ ^ 2) ∂P) +
            ∫ ω : Ω,
              (S.η / 2) *
                ‖S.estimator t ω - S.fullGradient (S.iterate t ω)‖ ^ 2 ∂P := by
            simpa only [descentRhs, Pi.add_apply] using
              (MeasureTheory.integral_add
                (((hF_int t).sub ((hG_int t).const_mul (S.η / 2))).sub
                  ((hD_int t).const_mul ((2 * S.η)⁻¹ - L / 2)))
                ((hR_int t).const_mul (S.η / 2)))
      _ =
          ((∫ ω : Ω,
              S.objective (S.iterate t ω) - S.fStar -
                (S.η / 2) * ‖S.fullGradient (S.iterate t ω)‖ ^ 2 ∂P) -
            ∫ ω : Ω,
              ((2 * S.η)⁻¹ - L / 2) *
                ‖S.iterate (t + 1) ω - S.iterate t ω‖ ^ 2 ∂P) +
            ∫ ω : Ω,
              (S.η / 2) *
                ‖S.estimator t ω - S.fullGradient (S.iterate t ω)‖ ^ 2 ∂P := by
            congr 1
            simpa only [Pi.sub_apply] using
              (MeasureTheory.integral_sub
                ((hF_int t).sub ((hG_int t).const_mul (S.η / 2)))
                ((hD_int t).const_mul ((2 * S.η)⁻¹ - L / 2)))
      _ =
          (((∫ ω : Ω, S.objective (S.iterate t ω) - S.fStar ∂P) -
              ∫ ω : Ω,
                (S.η / 2) * ‖S.fullGradient (S.iterate t ω)‖ ^ 2 ∂P) -
            ∫ ω : Ω,
              ((2 * S.η)⁻¹ - L / 2) *
                ‖S.iterate (t + 1) ω - S.iterate t ω‖ ^ 2 ∂P) +
            ∫ ω : Ω,
              (S.η / 2) *
                ‖S.estimator t ω - S.fullGradient (S.iterate t ω)‖ ^ 2 ∂P := by
            congr 2
            simpa only [Pi.sub_apply] using
              (MeasureTheory.integral_sub (hF_int t)
                ((hG_int t).const_mul (S.η / 2)))
      _ = F t - (S.η / 2) * G t -
            ((2 * S.η)⁻¹ - L / 2) * D t +
          (S.η / 2) * R t := by
            rw [MeasureTheory.integral_const_mul,
              MeasureTheory.integral_const_mul,
              MeasureTheory.integral_const_mul]
  have hdescent :
      F (t + 1) ≤
        F t - (S.η / 2) * G t -
            ((2 * S.η)⁻¹ - L / 2) * D t +
          (S.η / 2) * R t := by
    rw [hdescent_rhs_eq] at hdescent_mono
    exact hdescent_mono
  have hvar := h_variance
  rw [h_schedule.2.2.2.1 t] at hvar
  have hvar_rhs_eq :
      (∫ ω : Ω,
          (1 - p) *
              ‖S.estimator t ω - S.fullGradient (S.iterate t ω)‖ ^ 2 +
            (((1 - p) * L ^ 2) / (Fintype.card B' : ℝ)) *
              ‖S.iterate (t + 1) ω - S.iterate t ω‖ ^ 2 ∂P) =
        (1 - p) * R t +
          (((1 - p) * L ^ 2) / (Fintype.card B' : ℝ)) * D t := by
    rw [MeasureTheory.integral_add ((hR_int t).const_mul (1 - p))
      ((hD_int t).const_mul
        (((1 - p) * L ^ 2) / (Fintype.card B' : ℝ)))]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  rw [hvar_rhs_eq] at hvar
  change
    R (t + 1) ≤
      (1 - p) * R t +
        (((1 - p) * L ^ 2) / (Fintype.card B' : ℝ)) * D t at hvar
  have hp_pos : 0 < p := h_schedule.2.2.2.2.1
  have hbeta_nonneg : 0 ≤ S.η / (2 * p) := by
    exact div_nonneg h_schedule.1.le (mul_nonneg (by norm_num) hp_pos.le)
  have hvar_scaled :
      S.η / (2 * p) * R (t + 1) ≤
        S.η / (2 * p) *
          ((1 - p) * R t +
            (((1 - p) * L ^ 2) / (Fintype.card B' : ℝ)) * D t) :=
    mul_le_mul_of_nonneg_left hvar hbeta_nonneg
  have hp_ne : p ≠ 0 := ne_of_gt hp_pos
  calc
    F (t + 1) + S.η / (2 * p) * R (t + 1) ≤
        (F t - (S.η / 2) * G t -
              ((2 * S.η)⁻¹ - L / 2) * D t +
            (S.η / 2) * R t) +
          S.η / (2 * p) * R (t + 1) := by
            exact add_le_add hdescent (le_refl _)
    _ ≤
        (F t - (S.η / 2) * G t -
              ((2 * S.η)⁻¹ - L / 2) * D t +
            (S.η / 2) * R t) +
          S.η / (2 * p) *
            ((1 - p) * R t +
              (((1 - p) * L ^ 2) / (Fintype.card B' : ℝ)) * D t) := by
            exact add_le_add (le_refl _) hvar_scaled
    _ =
        F t + S.η / (2 * p) * R t - (S.η / 2) * G t -
          ((2 * S.η)⁻¹ - L / 2 -
              ((1 - p) * S.η * L ^ 2) /
                (2 * p * (Fintype.card B' : ℝ))) * D t := by
            field_simp [hp_ne]
            ring

private theorem selected_output_sq_integral_le_eta_horizon
    [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    {L p : ℝ} (h_schedule : S.TheoremOneOutputSchedule L p)
    (h_laws : S.StochasticLaws P)
    {T : ℕ} [NeZero T]
    (hsum :
      Finset.sum (Finset.range T)
        (fun t => ∫ ω : Ω, ‖S.fullGradient (S.iterate t ω)‖ ^ 2 ∂P) ≤
        2 * S.initialGap / S.η) :
    (∫ q : Fin T × Ω,
        ‖S.fullGradient (S.uniformOutput T q.1 q.2)‖ ^ 2 ∂outputJointLaw P T) ≤
      2 * S.initialGap / (S.η * (T : ℝ)) := by
  classical
  have hT_nat_pos : 0 < T := Nat.pos_of_neZero T
  have hT_pos : 0 < (T : ℝ) := by
    exact_mod_cast hT_nat_pos
  have hT_ne : (T : ℝ) ≠ 0 := ne_of_gt hT_pos
  have hη_pos : 0 < S.η := h_schedule.1
  have hη_ne : S.η ≠ 0 := ne_of_gt hη_pos
  have hfiber_sq :
      ∀ k : Fin T,
        MeasureTheory.Integrable
          (fun ω : Ω => ‖S.fullGradient (S.iterate k.val ω)‖ ^ 2) P := by
    intro k
    exact selected_gradient_norm_sq_fiber_integrable_of_stochastic_laws
      (S := S) P h_laws k.val
  have hsingleton :
      ∀ k : Fin T,
        (outputIndexLaw T).toMeasure.real ({k} : Set (Fin T)) = (T : ℝ)⁻¹ := by
    intro k
    rw [outputIndexLaw, MeasureTheory.Measure.real_def]
    rw [PMF.toMeasure_apply_singleton
      (PMF.uniformOfFintype (Fin T)) k (measurableSet_singleton k)]
    simp [PMF.uniformOfFintype_apply]
  have hexpand :
      (∫ q : Fin T × Ω,
          ‖S.fullGradient (S.uniformOutput T q.1 q.2)‖ ^ 2 ∂outputJointLaw P T) =
        Finset.sum Finset.univ
          (fun k : Fin T =>
            (T : ℝ)⁻¹ *
              ∫ ω : Ω, ‖S.fullGradient (S.iterate k.val ω)‖ ^ 2 ∂P) := by
    simpa [outputJointLaw, SOptLib.selected_joint_measure, uniformOutput] using
      (SOptLib.integral_finite_index_first_prod_eq_sum_weights
        (ν := (outputIndexLaw T).toMeasure) (μ := P)
        (p := fun _ : Fin T => (T : ℝ)⁻¹)
        (F := fun k : Fin T => fun ω : Ω =>
          ‖S.fullGradient (S.iterate k.val ω)‖ ^ 2)
        hsingleton hfiber_sq)
  have hsum_univ :
      Finset.sum Finset.univ
          (fun k : Fin T =>
            ∫ ω : Ω, ‖S.fullGradient (S.iterate k.val ω)‖ ^ 2 ∂P) =
        Finset.sum (Finset.range T)
          (fun t => ∫ ω : Ω, ‖S.fullGradient (S.iterate t ω)‖ ^ 2 ∂P) := by
    rw [Finset.sum_fin_eq_sum_range]
    refine Finset.sum_congr rfl ?_
    intro t ht
    simp [Finset.mem_range.mp ht]
  rw [hexpand]
  calc
    Finset.sum Finset.univ
        (fun k : Fin T =>
          (T : ℝ)⁻¹ *
            ∫ ω : Ω, ‖S.fullGradient (S.iterate k.val ω)‖ ^ 2 ∂P)
        =
      (T : ℝ)⁻¹ *
        Finset.sum Finset.univ
          (fun k : Fin T =>
            ∫ ω : Ω, ‖S.fullGradient (S.iterate k.val ω)‖ ^ 2 ∂P) := by
        rw [Finset.mul_sum]
    _ =
      (T : ℝ)⁻¹ *
        Finset.sum (Finset.range T)
          (fun t => ∫ ω : Ω, ‖S.fullGradient (S.iterate t ω)‖ ^ 2 ∂P) := by
        rw [hsum_univ]
    _ ≤ (T : ℝ)⁻¹ * (2 * S.initialGap / S.η) := by
        exact mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hT_pos.le)
    _ = 2 * S.initialGap / (S.η * (T : ℝ)) := by
        field_simp [hη_ne, hT_ne]

/-- Well-definedness obligation for the expected-gradient expression in the
paper-facing Theorem 1 regime.

Book/PDF citation: `book/research/PAGE.json#/main_theorem/measure` names
`E[||nabla f(xhat_T)||]`; `paper/PAGE.pdf`, Theorem 1 and Eq. (23)-(24),
derives the random-output bound before applying Jensen's inequality. This
regularity is therefore a derived obligation under the theorem assumptions, not
an unconditional theorem and not an extra theorem-head assumption. -/
theorem theoremOne_expectedSelectedGradientNorm_integrable [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    {L p ε : ℝ}
    (h_average_smooth : S.AverageLSmooth L)
    (h_schedule : S.TheoremOneSchedule L p)
    (h_laws : S.StochasticLaws P)
    (hε : 0 < ε)
    {T : ℕ} [NeZero T]
    (hT : S.theoremOneIterationCount L p ε ≤ (T : ℝ)) :
    S.SelectedGradientNormIntegrable P T := by
  exact
    selected_gradient_norm_integrable_of_fiber_integrable (S := S) P
      (fun k =>
        selected_gradient_norm_fiber_integrable_of_stochastic_laws
          (S := S) P h_laws k.val)

/-- The output half of Theorem 1 under exactly the schedule facts used by the
Lyapunov argument.  This is the route used by the Corollary 2 unit boundary,
where `b = b' = 1` makes the strict `TheoremOneSchedule` interface
unavailable but the paper's Eq. (14)--(24) output proof still uses the same
maximal-step, full-batch, and probability identities. -/
theorem theoremOne_output_of_outputSchedule [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    {L p ε : ℝ}
    (h_average_smooth : S.AverageLSmooth L)
    (h_schedule : S.TheoremOneOutputSchedule L p)
    (h_laws : S.StochasticLaws P)
    (hε : 0 < ε) :
    ∀ {T : ℕ} [NeZero T],
      S.theoremOneIterationCount L p ε ≤ (T : ℝ) →
        S.SelectedGradientNormIntegrable P T ∧
          S.expectedSelectedGradientNorm P T ≤ ε := by
  have h_variance_recursion :
      ∀ t : ℕ,
        (∫ ω : Ω,
            ‖S.estimator (t + 1) ω - S.fullGradient (S.iterate (t + 1) ω)‖ ^ 2 ∂P) ≤
          ∫ ω : Ω,
            (1 - S.refreshProbability t) *
              ‖S.estimator t ω - S.fullGradient (S.iterate t ω)‖ ^ 2 +
            (((1 - S.refreshProbability t) * L ^ 2) / (Fintype.card B' : ℝ)) *
              ‖S.iterate (t + 1) ω - S.iterate t ω‖ ^ 2 ∂P := by
    intro t
    exact S.line4_variance_recursion P h_average_smooth h_laws
      h_schedule.2.2.1 t
  intro T hne hT
  have h_int : S.SelectedGradientNormIntegrable P T :=
    selected_gradient_norm_integrable_of_fiber_integrable (S := S) P
      (fun k =>
        selected_gradient_norm_fiber_integrable_of_stochastic_laws
          (S := S) P h_laws k.val)
  refine ⟨h_int, ?_⟩
  rw [S.expectedSelectedGradientNorm_of_integrable P T h_int]
  have hsum_sq :
      Finset.sum (Finset.range T)
        (fun t => ∫ ω : Ω, ‖S.fullGradient (S.iterate t ω)‖ ^ 2 ∂P) ≤
        2 * S.initialGap / S.η := by
    let F : ℕ → ℝ := fun k =>
      ∫ ω : Ω, S.objective (S.iterate k ω) - S.fStar ∂P
    let R : ℕ → ℝ := fun k =>
      ∫ ω : Ω,
        ‖S.estimator k ω - S.fullGradient (S.iterate k ω)‖ ^ 2 ∂P
    let G : ℕ → ℝ := fun k =>
      ∫ ω : Ω, ‖S.fullGradient (S.iterate k ω)‖ ^ 2 ∂P
    let D : ℕ → ℝ := fun k =>
      ∫ ω : Ω, ‖S.iterate (k + 1) ω - S.iterate k ω‖ ^ 2 ∂P
    let Φ : ℕ → ℝ := fun k => F k + S.η / (2 * p) * R k
    have hcoeff :
        0 ≤ (2 * S.η)⁻¹ - L / 2 -
          ((1 - p) * S.η * L ^ 2) /
            (2 * p * (Fintype.card B' : ℝ)) :=
      theoremOne_displacement_coefficient_nonneg
        (S := S) h_average_smooth h_schedule
    have hD_nonneg : ∀ k : ℕ, 0 ≤ D k := by
      intro k
      exact MeasureTheory.integral_nonneg
        (fun ω : Ω => sq_nonneg ‖S.iterate (k + 1) ω - S.iterate k ω‖)
    have hstep : ∀ k : ℕ,
        Φ (k + 1) ≤ Φ k - (S.η / 2) * G k := by
      intro k
      have hstrong :=
        page_integrated_lyapunov_step
          (S := S) P h_average_smooth h_schedule h_laws k
          (h_variance_recursion k)
      change
        F (k + 1) + S.η / (2 * p) * R (k + 1) ≤
          F k + S.η / (2 * p) * R k - (S.η / 2) * G k -
            ((2 * S.η)⁻¹ - L / 2 -
              ((1 - p) * S.η * L ^ 2) /
                (2 * p * (Fintype.card B' : ℝ))) * D k at hstrong
      dsimp [Φ]
      nlinarith [mul_nonneg hcoeff (hD_nonneg k)]
    have htelescope : ∀ n : ℕ,
        Φ n + (S.η / 2) * Finset.sum (Finset.range n) G ≤ Φ 0 := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          rw [Finset.sum_range_succ]
          have hn := hstep n
          nlinarith
    have hF_zero : F 0 = S.initialGap := by
      simp [F, initialGap, MeasureTheory.integral_const,
        MeasureTheory.probReal_univ]
    have hR_zero : R 0 = 0 := by
      have hfun :
          (fun ω : Ω =>
            ‖S.estimator 0 ω - S.fullGradient (S.iterate 0 ω)‖ ^ 2) =
            (fun _ω : Ω => 0) := by
        funext ω
        rw [S.estimator_zero, S.iterate_zero,
          S.initialEstimator_fullBatch h_schedule.2.2.1]
        simp
      dsimp [R]
      rw [hfun]
      simp
    have hΦ_zero : Φ 0 = S.initialGap := by
      simp [Φ, hF_zero, hR_zero]
    have hF_terminal_nonneg : 0 ≤ F T := by
      exact MeasureTheory.integral_nonneg
        (fun ω : Ω =>
          sub_nonneg.mpr
            (S.fStar_le_objective (S.iterate T ω)))
    have hR_terminal_nonneg : 0 ≤ R T := by
      exact MeasureTheory.integral_nonneg
        (fun ω : Ω =>
          sq_nonneg ‖S.estimator T ω - S.fullGradient (S.iterate T ω)‖)
    have hp_pos : 0 < p := h_schedule.2.2.2.2.1
    have hbeta_nonneg : 0 ≤ S.η / (2 * p) := by
      exact div_nonneg h_schedule.1.le (mul_nonneg (by norm_num) hp_pos.le)
    have hΦ_terminal_nonneg : 0 ≤ Φ T := by
      dsimp [Φ]
      exact add_nonneg hF_terminal_nonneg
        (mul_nonneg hbeta_nonneg hR_terminal_nonneg)
    have hscaled_sum :
        (S.η / 2) * Finset.sum (Finset.range T) G ≤ S.initialGap := by
      have htel := htelescope T
      rw [hΦ_zero] at htel
      nlinarith
    have hη_pos : 0 < S.η := h_schedule.1
    have hraw_sum :
        Finset.sum (Finset.range T) G ≤ 2 * S.initialGap / S.η := by
      apply (le_div_iff₀ hη_pos).2
      nlinarith
    simpa [G] using hraw_sum
  have hsq_out :
      (∫ q : Fin T × Ω,
          ‖S.fullGradient (S.uniformOutput T q.1 q.2)‖ ^ 2 ∂outputJointLaw P T) ≤
        2 * S.initialGap / (S.η * (T : ℝ)) :=
    selected_output_sq_integral_le_eta_horizon (S := S) P h_schedule h_laws hsum_sq
  have heta_eps :
      2 * S.initialGap / (S.η * (T : ℝ)) ≤ ε ^ 2 :=
    S.theoremOne_eta_horizon_bound_of_outputSchedule h_schedule hε hT
  have hsq_eps :
      (∫ q : Fin T × Ω,
          (S.selectedGradientNormIntegrand T q) ^ 2 ∂outputJointLaw P T) ≤ ε ^ 2 := by
    exact le_trans (by simpa [selectedGradientNormIntegrand] using hsq_out) heta_eps
  have hsq_int :
      MeasureTheory.Integrable
        (fun q : Fin T × Ω => (S.selectedGradientNormIntegrand T q) ^ 2)
        (outputJointLaw P T) := by
    simpa [selectedGradientNormIntegrand, outputJointLaw, SOptLib.selected_joint_measure,
      uniformOutput] using
      (integrable_finite_index_first_prod_of_fiber_integrable
        (ν := (outputIndexLaw T).toMeasure) (μ := P)
        (F := fun k : Fin T => fun ω : Ω =>
          ‖S.fullGradient (S.iterate k.val ω)‖ ^ 2)
        (fun k =>
          selected_gradient_norm_sq_fiber_integrable_of_stochastic_laws
            (S := S) P h_laws k.val))
  haveI houtput_prob :
      MeasureTheory.IsProbabilityMeasure (outputJointLaw P T) := by
    unfold outputJointLaw
    unfold SOptLib.selected_joint_measure
    infer_instance
  exact
    integral_nonneg_le_of_integral_sq_le_sq
      (μ := outputJointLaw P T)
      (Z := S.selectedGradientNormIntegrand T)
      (C := ε)
      hsq_int
      (Filter.Eventually.of_forall (fun q => by
        simp [selectedGradientNormIntegrand]))
      hε.le
      hsq_eps

/-- Finite-dimensional helper form of Theorem 1. The paper-facing statement is
`theoremOne` below, specialized to `EuclideanSpace Real (Fin d)` for the source's
`\mathbb{R}^d`; this helper keeps the proof obligations reusable for
isomorphic finite-dimensional Euclidean models.

Book citation: `book/research/PAGE.json#/main_theorem/statement_math`:
Theorem 1 assumes Assumption 2, the schedule in Eq. (20), and returns
`E[||nabla f(xhat_T)||] <= epsilon` with the displayed `T` and `#grad`
formulas. -/
theorem theoremOne_finiteDimensional [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    {L p ε : ℝ}
    (h_average_smooth : S.AverageLSmooth L)
    (h_schedule : S.TheoremOneSchedule L p)
    (h_laws : S.StochasticLaws P)
    (hε : 0 < ε) :
    (∀ {T : ℕ} [NeZero T],
        S.theoremOneIterationCount L p ε ≤ (T : ℝ) →
          S.SelectedGradientNormIntegrable P T ∧
            S.expectedSelectedGradientNorm P T ≤ ε) ∧
      S.theoremOneIterationCount L p ε =
        2 * S.initialGap * L / ε ^ 2 *
          (1 + Real.sqrt ((1 - p) / (p * (Fintype.card B' : ℝ)))) ∧
      S.theoremOneGradientComplexity L p ε =
        (Fintype.card B : ℝ) +
          S.theoremOneIterationCount L p ε *
            (p * (Fintype.card B : ℝ) + (1 - p) * (Fintype.card B' : ℝ)) := by
  have h_output_schedule : S.TheoremOneOutputSchedule L p :=
    S.theoremOneSchedule_outputSchedule h_schedule
  have h_variance_recursion :
      ∀ t : ℕ,
        (∫ ω : Ω,
            ‖S.estimator (t + 1) ω - S.fullGradient (S.iterate (t + 1) ω)‖ ^ 2 ∂P) ≤
          ∫ ω : Ω,
            (1 - S.refreshProbability t) *
              ‖S.estimator t ω - S.fullGradient (S.iterate t ω)‖ ^ 2 +
            (((1 - S.refreshProbability t) * L ^ 2) / (Fintype.card B' : ℝ)) *
              ‖S.iterate (t + 1) ω - S.iterate t ω‖ ^ 2 ∂P := by
    intro t
    exact S.line4_variance_recursion P h_average_smooth h_laws
      h_output_schedule.2.2.1 t
  refine ⟨?_, ?_, ?_⟩
  · intro T hne hT
    have h_int : S.SelectedGradientNormIntegrable P T :=
      S.theoremOne_expectedSelectedGradientNorm_integrable P h_average_smooth
        h_schedule h_laws hε hT
    refine ⟨h_int, ?_⟩
    rw [S.expectedSelectedGradientNorm_of_integrable P T h_int]
    have hsum_sq :
        Finset.sum (Finset.range T)
          (fun t => ∫ ω : Ω, ‖S.fullGradient (S.iterate t ω)‖ ^ 2 ∂P) ≤
          2 * S.initialGap / S.η := by
      let F : ℕ → ℝ := fun k =>
        ∫ ω : Ω, S.objective (S.iterate k ω) - S.fStar ∂P
      let R : ℕ → ℝ := fun k =>
        ∫ ω : Ω,
          ‖S.estimator k ω - S.fullGradient (S.iterate k ω)‖ ^ 2 ∂P
      let G : ℕ → ℝ := fun k =>
        ∫ ω : Ω, ‖S.fullGradient (S.iterate k ω)‖ ^ 2 ∂P
      let D : ℕ → ℝ := fun k =>
        ∫ ω : Ω, ‖S.iterate (k + 1) ω - S.iterate k ω‖ ^ 2 ∂P
      let Φ : ℕ → ℝ := fun k => F k + S.η / (2 * p) * R k
      have hT_pos : 0 < T := @Nat.pos_of_neZero T hne
      have hcoeff :
          0 ≤ (2 * S.η)⁻¹ - L / 2 -
            ((1 - p) * S.η * L ^ 2) /
              (2 * p * (Fintype.card B' : ℝ)) :=
        theoremOne_displacement_coefficient_nonneg
          (S := S) h_average_smooth h_output_schedule
      have hD_nonneg : ∀ k : ℕ, 0 ≤ D k := by
        intro k
        exact MeasureTheory.integral_nonneg
          (fun ω : Ω => sq_nonneg ‖S.iterate (k + 1) ω - S.iterate k ω‖)
      have hstep : ∀ k : ℕ,
          Φ (k + 1) ≤ Φ k - (S.η / 2) * G k := by
        intro k
        have hstrong :=
          page_integrated_lyapunov_step
            (S := S) P h_average_smooth h_output_schedule h_laws k
            (h_variance_recursion k)
        change
          F (k + 1) + S.η / (2 * p) * R (k + 1) ≤
            F k + S.η / (2 * p) * R k - (S.η / 2) * G k -
              ((2 * S.η)⁻¹ - L / 2 -
                ((1 - p) * S.η * L ^ 2) /
                  (2 * p * (Fintype.card B' : ℝ))) * D k at hstrong
        dsimp [Φ]
        nlinarith [mul_nonneg hcoeff (hD_nonneg k)]
      have htelescope : ∀ n : ℕ,
          Φ n + (S.η / 2) * Finset.sum (Finset.range n) G ≤ Φ 0 := by
        intro n
        induction n with
        | zero => simp
        | succ n ih =>
            rw [Finset.sum_range_succ]
            have hn := hstep n
            nlinarith
      have hF_zero : F 0 = S.initialGap := by
        simp [F, initialGap, MeasureTheory.integral_const,
          MeasureTheory.probReal_univ]
      have hR_zero : R 0 = 0 := by
        have hfun :
            (fun ω : Ω =>
              ‖S.estimator 0 ω - S.fullGradient (S.iterate 0 ω)‖ ^ 2) =
              (fun _ω : Ω => 0) := by
          funext ω
          rw [S.estimator_zero, S.iterate_zero,
            S.initialEstimator_fullBatch h_output_schedule.2.2.1]
          simp
        dsimp [R]
        rw [hfun]
        simp
      have hΦ_zero : Φ 0 = S.initialGap := by
        simp [Φ, hF_zero, hR_zero]
      have hF_terminal_nonneg : 0 ≤ F T := by
        exact MeasureTheory.integral_nonneg
          (fun ω : Ω =>
            sub_nonneg.mpr
              (S.fStar_le_objective (S.iterate T ω)))
      have hR_terminal_nonneg : 0 ≤ R T := by
        exact MeasureTheory.integral_nonneg
          (fun ω : Ω =>
            sq_nonneg ‖S.estimator T ω - S.fullGradient (S.iterate T ω)‖)
      have hp_pos : 0 < p := h_output_schedule.2.2.2.2.1
      have hbeta_nonneg : 0 ≤ S.η / (2 * p) := by
        exact div_nonneg h_output_schedule.1.le (mul_nonneg (by norm_num) hp_pos.le)
      have hΦ_terminal_nonneg : 0 ≤ Φ T := by
        dsimp [Φ]
        exact add_nonneg hF_terminal_nonneg
          (mul_nonneg hbeta_nonneg hR_terminal_nonneg)
      have hscaled_sum :
          (S.η / 2) * Finset.sum (Finset.range T) G ≤ S.initialGap := by
        have htel := htelescope T
        rw [hΦ_zero] at htel
        nlinarith
      have hη_pos : 0 < S.η := h_output_schedule.1
      have hraw_sum :
          Finset.sum (Finset.range T) G ≤ 2 * S.initialGap / S.η := by
        apply (le_div_iff₀ hη_pos).2
        nlinarith
      simpa [G] using hraw_sum
    have hsq_out :
        (∫ q : Fin T × Ω,
            ‖S.fullGradient (S.uniformOutput T q.1 q.2)‖ ^ 2 ∂outputJointLaw P T) ≤
      2 * S.initialGap / (S.η * (T : ℝ)) :=
      selected_output_sq_integral_le_eta_horizon (S := S) P h_output_schedule h_laws hsum_sq
    have heta_eps :
        2 * S.initialGap / (S.η * (T : ℝ)) ≤ ε ^ 2 :=
      S.theoremOne_eta_horizon_bound_of_outputSchedule h_output_schedule hε hT
    have hsq_eps :
        (∫ q : Fin T × Ω,
            (S.selectedGradientNormIntegrand T q) ^ 2 ∂outputJointLaw P T) ≤ ε ^ 2 := by
      exact le_trans (by simpa [selectedGradientNormIntegrand] using hsq_out) heta_eps
    have hsq_int :
        MeasureTheory.Integrable
          (fun q : Fin T × Ω => (S.selectedGradientNormIntegrand T q) ^ 2)
          (outputJointLaw P T) := by
      simpa [selectedGradientNormIntegrand, outputJointLaw, SOptLib.selected_joint_measure,
        uniformOutput] using
        (integrable_finite_index_first_prod_of_fiber_integrable
          (ν := (outputIndexLaw T).toMeasure) (μ := P)
          (F := fun k : Fin T => fun ω : Ω =>
            ‖S.fullGradient (S.iterate k.val ω)‖ ^ 2)
          (fun k =>
            selected_gradient_norm_sq_fiber_integrable_of_stochastic_laws
              (S := S) P h_laws k.val))
    haveI houtput_prob :
        MeasureTheory.IsProbabilityMeasure (outputJointLaw P T) := by
      unfold outputJointLaw
      unfold SOptLib.selected_joint_measure
      infer_instance
    exact
      integral_nonneg_le_of_integral_sq_le_sq
        (μ := outputJointLaw P T)
        (Z := S.selectedGradientNormIntegrand T)
        (C := ε)
        hsq_int
        (Filter.Eventually.of_forall (fun q => by
          simp [selectedGradientNormIntegrand]))
        hε.le
        hsq_eps
  · simp [theoremOneIterationCount_def]
  · simp [theoremOneGradientComplexity_def]

/-- Theorem 1, paper-facing finite-sum PAGE guarantee over Mathlib's
coordinate Euclidean space `EuclideanSpace Real (Fin d)`, modeling
`\mathbb{R}^d`.

Book citations:
* `book/research/PAGE.json#/setup/problem`: `\min_{x\in\mathbb{R}^d} f(x)`.
* `book/research/PAGE.json#/main_theorem`: Theorem 1 gives the expected
  gradient-norm guarantee and gradient-complexity formula.

The stochastic run laws formalize Algorithm 1's branch and minibatch randomness;
regularity needed for the displayed expectation is returned as part of the
theorem-regime conclusion, not assumed. -/
theorem theoremOne {d : ℕ}
    (S : Setup ι (EuclideanSpace ℝ (Fin d)) Ω B B') [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    {L p ε : ℝ}
    (h_average_smooth : S.AverageLSmooth L)
    (h_schedule : S.TheoremOneSchedule L p)
    (h_laws : S.StochasticLaws P)
    (hε : 0 < ε) :
    (∀ {T : ℕ} [NeZero T],
        S.theoremOneIterationCount L p ε ≤ (T : ℝ) →
          S.SelectedGradientNormIntegrable P T ∧
            S.expectedSelectedGradientNorm P T ≤ ε) ∧
      S.theoremOneIterationCount L p ε =
        2 * S.initialGap * L / ε ^ 2 *
          (1 + Real.sqrt ((1 - p) / (p * (Fintype.card B' : ℝ)))) ∧
      S.theoremOneGradientComplexity L p ε =
        (Fintype.card B : ℝ) +
          S.theoremOneIterationCount L p ε *
            (p * (Fintype.card B : ℝ) + (1 - p) * (Fintype.card B' : ℝ)) :=
  S.theoremOne_finiteDimensional P h_average_smooth h_schedule h_laws hε

/-- Corrected-adapter realization of Corollary 2's fixed refresh probability
`p = b' / (b + b')`, using the finite batch-index cardinalities of the PAGE
setup.

Book citation: `book/research/PAGE.json#/extension/additions/assumptions/0`:
`p_t ≡ b'/(b+b')`. The source scalars are kept in
`CorollaryTwoSourceSchedule`; this cardinality realization belongs only to the
corrected adapter. PDF: `paper/PAGE.pdf`, Corollary 2, p. 5. -/
noncomputable def corollaryTwoProbability : ℝ :=
  (Fintype.card B' : ℝ) /
    ((Fintype.card B : ℝ) + (Fintype.card B' : ℝ))

/-- Formal endpoint adapter for the Corollary 2 stepsize expression.

Book citation: `book/research/PAGE.json#/extension/additions/assumptions/0`:
`eta <= 1/(L(1+sqrt(b)/b'))`. This equality is a corrected Lean adapter input
for the inherited eta-horizon identity, not a replacement for the source
upper bound. -/
noncomputable def corollaryTwoStepsizeEndpoint (L : ℝ) : ℝ :=
  (L *
      (1 + Real.sqrt (Fintype.card B : ℝ) /
        (Fintype.card B' : ℝ)))⁻¹

/-- The source-facing Corollary 2 batch-range condition `b' <= sqrt(b)`.

Book citation: `book/research/PAGE.json#/extension/additions/assumptions/1`:
`b' <= sqrt(b)`. -/
def CorollaryTwoBatchRange : Prop :=
  (Fintype.card B' : ℝ) ≤ Real.sqrt (Fintype.card B : ℝ)

/-- The corrected adapter's full-batch condition after source scalars have
been translated to the finite-index boundary of the generated PAGE model.

Book citation: `book/research/PAGE.json#/extension/additions/assumptions/0`:
`b = n`. This declaration is only the translated finite-index adapter. -/
def CorollaryTwoFiniteSumIndex : Prop :=
  Fintype.card B = Fintype.card ι

/-- Explicit corrected-adapter bridge from the paper's scalar batch
parameters to the finite index types used by this Lean realization. The
paper-facing declarations quantify over `b`, `b'`, and `n` directly and do not
carry this bridge. -/
def CorollaryTwoBatchSize : Type :=
  {b : ℕ // 0 < b}

def CorollaryTwoScalarCardinalityBridge
    (b b' n : CorollaryTwoBatchSize) : Prop :=
  b.1 = Fintype.card B ∧
    b'.1 = Fintype.card B' ∧
      n.1 = Fintype.card ι

/-- Canonical source-side finite-sum data for Corollary 2.

The paper's scalar `n` is represented by the component universe `Fin n`
itself.  Ambient finite-index realizations are converted into this object only
through an explicit equivalence in the corrected adapter.  This prevents an
independent ambient `ι` from silently disagreeing with the source component
count.

Book citation: `book/research/PAGE.json#/setup/variable_space`: `f(x) :=
(1/n) \sum_{i=1}^n f_i(x)`. -/
structure CorollaryTwoSourceModel (n : CorollaryTwoBatchSize) where
  componentObjective : Fin n.1 → E → ℝ
  x0 : E
  η : ℝ
  objective_bddBelow :
    BddBelow
      ((fun x : E =>
          SOptLib.finiteUniformAverage
            (fun i : Fin n.1 => componentObjective i x)) '' (Set.univ : Set E))

instance corollaryTwoSourceModel_index_nonempty
    (n : CorollaryTwoBatchSize) : Nonempty (Fin n.1) :=
  ⟨⟨0, n.2⟩⟩

/-- Explicit source-boundary convention for the paper's real-valued `T`.

The paper prints a real-valued iteration expression but selects the output
uniformly from a finite iterate window.  The canonical source realization
chooses the positive window `max 1 (Nat.ceil τ)` for a displayed real horizon
`τ`.  This is the single representation convention used by the source object;
the corrected adapter may still select and compare an arbitrary natural
horizon separately.

PDF citation: `paper/PAGE.pdf`, Algorithm 1 output clause, p. 4, says
`xhat_T` is chosen uniformly from `{x^t}_{t∈[T]}`; Corollary 2, p. 5, prints
the iteration budget as a real-valued expression. -/
abbrev CorollaryTwoSourceOutputWindow (T : ℕ) := Fin T

noncomputable def corollaryTwoSourceOutputWindow (τ : ℝ) : ℕ :=
  max 1 (Nat.ceil τ)

theorem corollaryTwoSourceOutputWindow_pos (τ : ℝ) :
    0 < corollaryTwoSourceOutputWindow τ := by
  exact Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 (Nat.ceil τ))

theorem corollaryTwoSourceOutputWindow_real_horizon_le (τ : ℝ) :
    τ ≤ (corollaryTwoSourceOutputWindow τ : ℝ) := by
  unfold corollaryTwoSourceOutputWindow
  exact
    (Nat.le_ceil τ).trans
      (by
        exact_mod_cast Nat.le_max_right 1 (Nat.ceil τ))

/-- Source-side PAGE setup with scalar batch sizes realized by `Fin b` and
component count realized by `Fin n`.

Book-JSON citations:
* `book/research/PAGE.json#/setup/variable_space`: `f(x) :=
  \frac{1}{n}\sum_{i=1}^n f_i(x)`;
* `book/research/PAGE.json#/algorithm_spec/initialization`:
  `g^0=\frac{1}{b}\sum_{i\in I}\nabla f_i(x^0)`;
* `book/research/PAGE.json#/algorithm_spec/steps/0`:
  `x^{t+1}=x^t-\eta g^t`;
* `book/research/PAGE.json#/algorithm_spec/steps/1`:
  `g^{t+1}=\begin{cases}\frac{1}{b}\sum_{i\in I}\nabla f_i(x^{t+1})
  &\text{with probability }p_t,\\
  g^t+\frac{1}{b'}\sum_{i\in I'}(\nabla f_i(x^{t+1})-\nabla f_i(x^t))
  &\text{with probability }1-p_t.\end{cases}`.
* `book/research/PAGE.json#/extension/additions/assumptions/0`:
  Corollary 2 parameter specialization
  `\eta\le\frac{1}{L(1+\frac{\sqrt{b}}{b'})}`, `b=n`,
  `b'\le\sqrt{b}`, and `p_t\equiv\frac{b'}{b+b'}`; the constructed
  refresh probability below is this canonical `p_t` specialization.

This definition realizes those paper objects over the canonical component
universe `Fin n` and the two finite sample supports; the corresponding
estimator and iterate operations are inherited from the constructed `Setup`
rather than supplied as extra witness fields. -/
noncomputable def corollaryTwoSourceSetup
    (M : CorollaryTwoSourceModel (E := E) n)
    (b b' : CorollaryTwoBatchSize) :
    Setup (Fin n.1) E
      (RandomSource (ι := Fin n.1) (B := Fin b.1) (B' := Fin b'.1))
      (Fin b.1) (Fin b'.1) :=
  letI : Nonempty (Fin n.1) := ⟨⟨0, n.2⟩⟩
  letI : Nonempty (Fin b.1) := ⟨⟨0, b.2⟩⟩
  letI : Nonempty (Fin b'.1) := ⟨⟨0, b'.2⟩⟩
  { componentObjective := M.componentObjective
    x0 := M.x0
    η := M.η
    refreshProbability := fun _ =>
      (b'.1 : ℝ) / ((b.1 : ℝ) + (b'.1 : ℝ))
    refreshSample := fun t j ξ =>
      ξ.2.1 t (Fintype.equivFin (Fin b.1) j)
    recursiveSample := fun t j ξ =>
      ξ.2.2 t (Fintype.equivFin (Fin b'.1) j)
    refreshBranch := fun t ξ => ξ.1 t
    h_objective_bddBelow := M.objective_bddBelow }

/-- Reindex an ambient PAGE setup into the canonical source universe `Fin n`.
The equivalence is an adapter datum; the source process itself only sees
`Fin n`. -/
noncomputable def corollaryTwoSourceModelOfAmbient
    (S : Setup ι E Ω B B') (n : CorollaryTwoBatchSize)
    (e : Fin n.1 ≃ ι) : CorollaryTwoSourceModel (E := E) n :=
  { componentObjective := fun i => S.componentObjective (e i)
    x0 := S.x0
    η := S.η
    objective_bddBelow := by
      have h_eq :
          (fun x : E =>
              SOptLib.finiteUniformAverage
                (fun i : Fin n.1 => S.componentObjective (e i) x)) =
            S.objective := by
        funext x
        exact finiteUniformAverage_comp_equiv e
          (fun i : ι => S.componentObjective i x)
      rw [h_eq]
      exact S.objective_bddBelow }

/-- The exact source upper-bound parameter specialization from Corollary 2.

Book citation: `book/research/PAGE.json#/extension/additions/assumptions/0`
and `book/research/PAGE.json#/extension/additions/main_theorem/statement_math`:
`"\\eta\\le \\frac{1}{L(1+\\frac{\\sqrt{b}}{b'})},\\quad b=n,\\quad
b'\\le \\sqrt{b},\\quad p_t\\equiv \\frac{b'}{b+b'}"`.
The source scalars are explicit here. Their identification with the finite
index cardinalities used by the inherited PAGE interface is an adapter
obligation and is deliberately not folded into this source predicate. -/
def CorollaryTwoSourceSchedule
    (M : CorollaryTwoSourceModel (E := E) n)
    (L : ℝ) (b b' : CorollaryTwoBatchSize) : Prop :=
  M.η ≤
      (L *
    (1 + Real.sqrt (b.1 : ℝ) / (b'.1 : ℝ)))⁻¹ ∧
    b.1 = n.1 ∧
    (b'.1 : ℝ) ≤ Real.sqrt (b.1 : ℝ)

/-- Formal adapter input selecting the endpoint needed by the inherited
Theorem 1 eta-horizon identity. -/
def CorollaryTwoMaximalEndpoint (L : ℝ) : Prop :=
  S.η = corollaryTwoStepsizeEndpoint (B := B) (B' := B') L

/-- Formal adapter input for the strict branch of the source condition
`b' <= sqrt(b)`. -/
def CorollaryTwoStrictBatch : Prop :=
  Fintype.card B' < Fintype.card B

/-- The only boundary left when the inherited Theorem 1 interface needs
`b' < b` but the source Corollary 2 prints `b' <= sqrt(b)`.

This is a formal cardinality case, not a replacement for the source
non-strict condition. -/
def CorollaryTwoUnitBatchBoundary : Prop :=
  Fintype.card B = 1 ∧ Fintype.card B' = 1

/-- Source-derived dispatch obligation for the non-strict Corollary 2 batch
range. The unit case is kept explicit because it cannot be silently fed to the
strict Theorem 1 schedule interface. -/
theorem corollaryTwo_batch_boundary_split
    (h_range : CorollaryTwoBatchRange (B := B) (B' := B'))
    (h_not_strict : ¬ CorollaryTwoStrictBatch (B := B) (B' := B')) :
    CorollaryTwoUnitBatchBoundary (B := B) (B' := B') := by
  have hB_nat : 0 < Fintype.card B := Fintype.card_pos
  have hB_le_B' : Fintype.card B ≤ Fintype.card B' := by
    exact Nat.le_of_not_lt h_not_strict
  have hB_le_B'_real : (Fintype.card B : ℝ) ≤ Fintype.card B' := by
    exact_mod_cast hB_le_B'
  have hsqrt_le_B :
      Real.sqrt (Fintype.card B : ℝ) ≤ Fintype.card B := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · have hB_ge_one_nat : 1 ≤ Fintype.card B := hB_nat
      have hB_ge_one : (1 : ℝ) ≤ Fintype.card B := by
        exact_mod_cast hB_ge_one_nat
      nlinarith
  have hB_eq_B'_real :
      (Fintype.card B : ℝ) = Fintype.card B' := by
    exact le_antisymm hB_le_B'_real
      (le_trans h_range hsqrt_le_B)
  have hB_eq_B' : Fintype.card B = Fintype.card B' := by
    exact_mod_cast hB_eq_B'_real
  have hB_sqrt_eq :
      Real.sqrt (Fintype.card B : ℝ) = Fintype.card B := by
    exact le_antisymm hsqrt_le_B
      (le_trans hB_le_B'_real h_range)
  have hB_one_real : (Fintype.card B : ℝ) = 1 := by
    have hsq := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ Fintype.card B)
    rw [hB_sqrt_eq] at hsq
    have hB_ge_one_nat : 1 ≤ Fintype.card B := hB_nat
    have hB_ge_one : (1 : ℝ) ≤ Fintype.card B := by
      exact_mod_cast hB_ge_one_nat
    nlinarith
  have hB_one : Fintype.card B = 1 := by
    exact_mod_cast hB_one_real
  exact ⟨hB_one, hB_eq_B'.symm.trans hB_one⟩

/-- In the Corollary 2 unit boundary, the source condition `b = n` identifies
the full component universe with the singleton batch universe.

Book citation: `book/research/PAGE.json#/extension/additions/main_theorem/
proof/6` consumes the unit-boundary branch together with
`Corollary2_finite_sum_index_bridge`; this lemma exposes that bridge before
the boundary convergence proof is attempted. -/
theorem corollaryTwo_unit_boundary_component_card
    (h_full_batch : CorollaryTwoFiniteSumIndex (ι := ι) (B := B))
    (h_boundary : CorollaryTwoUnitBatchBoundary (B := B) (B' := B')) :
    Fintype.card ι = 1 := by
  exact h_full_batch ▸ h_boundary.1

/-- Canonical arithmetic domain for the source's epsilon-approximation
parameter. The paper's displayed quotients are not exposed at epsilon zero. -/
def CorollaryTwoEpsilon : Type :=
  SOptLib.PositiveRealParameter

/-- Paper-facing Corollary 2 iteration arithmetic over its scalar batch
parameters. This definition does not identify those scalars with Lean
cardinalities; that translation belongs to the corrected adapter.

Book citation: `book/research/PAGE.json#/extension/additions/main_theorem/
statement_math`:
`"T=\\frac{2\\Delta_0L}{\\epsilon^2}\\left(1+\\frac{\\sqrt{b}}{b'}\\right)"`.
The positive-epsilon subtype is the canonical arithmetic domain for this
displayed quotient. -/
noncomputable def corollaryTwoSourceIterationCount
    (M : CorollaryTwoSourceModel (E := E) n)
    (L : ℝ) (b b' : CorollaryTwoBatchSize)
    (ε : CorollaryTwoEpsilon) : ℝ :=
  2 * (corollaryTwoSourceSetup M b b').initialGap * L / ε.1 ^ 2 *
    (1 + Real.sqrt (b.1 : ℝ) / (b'.1 : ℝ))

/-- Paper-facing Corollary 2 gradient-complexity arithmetic over its scalar
batch parameters.

Book citation: `book/research/PAGE.json#/extension/additions/main_theorem/
proof/8` and `/proof/9`: “`#grad=b+T(pb+(1-p)b')`” and, after
`p=b'/(b+b')`, “`#grad=b+T*2bb'/(b+b')`.” The final source inequality is
recorded at `/extension/additions/main_theorem/statement_math`. -/
noncomputable def corollaryTwoSourceGradientComplexity
    (M : CorollaryTwoSourceModel (E := E) n)
    (L : ℝ) (b b' : CorollaryTwoBatchSize)
    (ε : CorollaryTwoEpsilon) : ℝ :=
  (n.1 : ℝ) +
    corollaryTwoSourceIterationCount M L b b' ε *
      (2 * (b.1 : ℝ) * (b'.1 : ℝ) /
        ((b.1 : ℝ) + (b'.1 : ℝ)))

/-- Corollary 2's specialized iteration count after the corrected adapter has
identified the source batch scalars with finite index cardinalities. -/
noncomputable def corollaryTwoIterationCount
    (L : ℝ) (ε : CorollaryTwoEpsilon) : ℝ :=
  2 * S.initialGap * L / ε.1 ^ 2 *
    (1 + Real.sqrt (Fintype.card B : ℝ) /
      (Fintype.card B' : ℝ))

/-- Corollary 2's expected per-iteration gradient cost after substituting
`p = b' / (b + b')`. -/
noncomputable def corollaryTwoExpectedIterationCost : ℝ :=
  2 * (Fintype.card B : ℝ) * (Fintype.card B' : ℝ) /
    ((Fintype.card B : ℝ) + (Fintype.card B' : ℝ))

/-- Corollary 2's total stochastic-gradient count on the positive epsilon
domain, before the final `b = n`, `b' <= sqrt(b)` inequality. -/
noncomputable def corollaryTwoGradientComplexity
    (L : ℝ) (ε : CorollaryTwoEpsilon) : ℝ :=
  (Fintype.card B : ℝ) +
    S.corollaryTwoIterationCount L ε *
      corollaryTwoExpectedIterationCost (B := B) (B' := B')

/-- Real-valued iteration arithmetic used only by the corrected adapter
boundary, after it has received an explicit positive-epsilon premise. -/
noncomputable def corollaryTwoAdapterIterationCount
    (L : ℝ) (ε : CorollaryTwoEpsilon) : ℝ :=
  2 * S.initialGap * L / ε.1 ^ 2 *
    (1 + Real.sqrt (Fintype.card B : ℝ) /
      (Fintype.card B' : ℝ))

/-- Real-valued gradient-complexity arithmetic used only by the corrected
adapter boundary, after it has received an explicit positive-epsilon premise. -/
noncomputable def corollaryTwoAdapterGradientComplexity
    (L : ℝ) (ε : CorollaryTwoEpsilon) : ℝ :=
  (Fintype.card B : ℝ) +
    S.corollaryTwoAdapterIterationCount L ε *
      corollaryTwoExpectedIterationCost (B := B) (B' := B')

@[simp]
theorem corollaryTwoProbability_pos :
    0 < corollaryTwoProbability (B := B) (B' := B') := by
  unfold corollaryTwoProbability
  have hb : 0 < (Fintype.card B : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card B)
  have hb' : 0 < (Fintype.card B' : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card B')
  positivity

@[simp]
theorem corollaryTwoProbability_le_one :
    corollaryTwoProbability (B := B) (B' := B') ≤ 1 := by
  unfold corollaryTwoProbability
  have hb : 0 < (Fintype.card B : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card B)
  have hb' : 0 < (Fintype.card B' : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card B')
  have hsum : 0 < (Fintype.card B : ℝ) + (Fintype.card B' : ℝ) := by
    positivity
  exact (div_le_one hsum).2 (le_add_of_nonneg_left hb.le)

theorem corollaryTwoExpectedIterationCost_eq :
    corollaryTwoProbability (B := B) (B' := B') * (Fintype.card B : ℝ) +
        (1 - corollaryTwoProbability (B := B) (B' := B')) *
            (Fintype.card B' : ℝ) =
      corollaryTwoExpectedIterationCost (B := B) (B' := B') := by
  unfold corollaryTwoProbability corollaryTwoExpectedIterationCost
  have hb : 0 < (Fintype.card B : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card B)
  have hb' : 0 < (Fintype.card B' : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card B')
  have hsum : (Fintype.card B : ℝ) + (Fintype.card B' : ℝ) ≠ 0 := by
    positivity
  field_simp [hsum]
  ring

/-- Source-derived ratio simplification
`sqrt((1-p)/(p b')) = sqrt(b)/b'`.

The positivity and denominator obligations are kept explicit because they are
formal domain facts, not additional paper assumptions. -/
theorem corollaryTwo_ratio_identity :
    Real.sqrt
        ((1 - corollaryTwoProbability (B := B) (B' := B')) /
          (corollaryTwoProbability (B := B) (B' := B') *
            (Fintype.card B' : ℝ))) =
      Real.sqrt (Fintype.card B : ℝ) / (Fintype.card B' : ℝ) := by
  let b : ℝ := Fintype.card B
  let b' : ℝ := Fintype.card B'
  have hb : 0 < b := by
    dsimp [b]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card B)
  have hb' : 0 < b' := by
    dsimp [b']
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card B')
  have hsum : b + b' ≠ 0 := by positivity
  have hratio :
      (1 - b' / (b + b')) / ((b' / (b + b')) * b') =
        b / b' ^ 2 := by
    field_simp [hsum, ne_of_gt hb']
    ring
  rw [show corollaryTwoProbability (B := B) (B' := B') = b' / (b + b') by
    rfl, hratio]
  rw [Real.sqrt_div (by positivity : 0 ≤ b)]
  rw [Real.sqrt_sq_eq_abs, abs_of_pos hb']

@[simp]
theorem corollaryTwoIterationCount_def
    (L : ℝ) (ε : CorollaryTwoEpsilon) :
    S.corollaryTwoIterationCount L ε =
      2 * S.initialGap * L / ε.1 ^ 2 *
        (1 + Real.sqrt (Fintype.card B : ℝ) /
          (Fintype.card B' : ℝ)) := by
  rfl

@[simp]
theorem corollaryTwoGradientComplexity_def
    (L : ℝ) (ε : CorollaryTwoEpsilon) :
    S.corollaryTwoGradientComplexity L ε =
      (Fintype.card B : ℝ) +
        S.corollaryTwoIterationCount L ε *
          corollaryTwoExpectedIterationCost (B := B) (B' := B') := by
  rfl

@[simp]
theorem corollaryTwoAdapterIterationCount_def
    (L : ℝ) (ε : CorollaryTwoEpsilon) :
    S.corollaryTwoAdapterIterationCount L ε =
      2 * S.initialGap * L / ε.1 ^ 2 *
        (1 + Real.sqrt (Fintype.card B : ℝ) /
          (Fintype.card B' : ℝ)) := by
  rfl

@[simp]
theorem corollaryTwoAdapterGradientComplexity_def
    (L : ℝ) (ε : CorollaryTwoEpsilon) :
    S.corollaryTwoAdapterGradientComplexity L ε =
      (Fintype.card B : ℝ) +
        S.corollaryTwoAdapterIterationCount L ε *
          corollaryTwoExpectedIterationCost (B := B) (B' := B') := by
  rfl

theorem corollaryTwoAdapterIterationCount_eq_theoremOneIterationCount
    {L : ℝ} (ε : CorollaryTwoEpsilon) :
    S.theoremOneIterationCount L
        (corollaryTwoProbability (B := B) (B' := B')) ε.1 =
      S.corollaryTwoAdapterIterationCount L ε := by
  rw [theoremOneIterationCount_def, corollaryTwoAdapterIterationCount_def,
    corollaryTwo_ratio_identity]

/-- Corrected-adapter output guarantee for the source Corollary 2 semantics.

The paper calls an output epsilon-approximate when
`E[||nabla f(xhat_T)||] <= epsilon`. The source's real iteration expression
is interpreted by the finite-dimensional PAGE interface as: every positive
natural horizon `T` at least that expression has the expected-gradient
guarantee. The positive-epsilon premise is a domain guard, not an added
paper regularity assumption. -/
def CorollaryTwoAdapterOutputGuarantee [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (L : ℝ) (ε : CorollaryTwoEpsilon) : Prop :=
  ∀ {T : ℕ} [NeZero T],
    S.corollaryTwoAdapterIterationCount L ε ≤ (T : ℝ) →
      S.SelectedGradientNormIntegrable P T ∧
        S.expectedSelectedGradientNorm P T ≤ ε.1

/-- The strict-branch Corollary 2 adapter.  This is the reusable formal route
to the inherited PAGE convergence theorem; it does not duplicate Theorem 1. -/
theorem corollaryTwo_strict_adapter [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    {L : ℝ} (ε : CorollaryTwoEpsilon)
    (h_average_smooth : S.AverageLSmooth L)
    (h_endpoint : S.CorollaryTwoMaximalEndpoint L)
    (h_full_batch : CorollaryTwoFiniteSumIndex (ι := ι) (B := B))
    (h_strict_batch : CorollaryTwoStrictBatch (B := B) (B' := B'))
    (h_probability :
      ∀ t : ℕ,
        S.refreshProbability t =
          corollaryTwoProbability (B := B) (B' := B'))
    (h_laws : S.StochasticLaws P)
    {T : ℕ} [NeZero T]
    (hT : S.corollaryTwoAdapterIterationCount L ε ≤ (T : ℝ)) :
    S.SelectedGradientNormIntegrable P T ∧
      S.expectedSelectedGradientNorm P T ≤ ε.1 := by
  have hη_pos : 0 < S.η := by
    rw [h_endpoint]
    unfold corollaryTwoStepsizeEndpoint
    have hL : 0 < L := h_average_smooth.1
    have hb' : 0 < (Fintype.card B' : ℝ) := by
      exact_mod_cast (Fintype.card_pos : 0 < Fintype.card B')
    positivity
  have hratio :=
    corollaryTwo_ratio_identity (B := B) (B' := B')
  have h_schedule :
      S.TheoremOneSchedule L
        (corollaryTwoProbability (B := B) (B' := B')) := by
    refine ⟨hη_pos, ?_, h_full_batch, h_strict_batch, h_probability,
      corollaryTwoProbability_pos (B := B) (B' := B'),
      corollaryTwoProbability_le_one (B := B) (B' := B')⟩
    calc
      S.η = corollaryTwoStepsizeEndpoint (B := B) (B' := B') L := h_endpoint
      _ =
          (L *
            (1 + Real.sqrt
              ((1 - corollaryTwoProbability (B := B) (B' := B')) /
                (corollaryTwoProbability (B := B) (B' := B') *
                  (Fintype.card B' : ℝ)))))⁻¹ := by
            rw [corollaryTwoStepsizeEndpoint, hratio]
  have hcount :
      S.theoremOneIterationCount L corollaryTwoProbability ε.1 =
        S.corollaryTwoAdapterIterationCount L ε :=
    S.corollaryTwoAdapterIterationCount_eq_theoremOneIterationCount ε
  have hT' :
      S.theoremOneIterationCount L
          (corollaryTwoProbability (B := B) (B' := B')) ε.1 ≤ (T : ℝ) := by
    rw [hcount]
    exact hT
  exact
    (S.theoremOne_finiteDimensional P h_average_smooth h_schedule h_laws ε.2).1
      hT'

/-- Corrected Lean realization contract for Corollary 2.

Book citation: `book/research/PAGE.json#/extension/additions/main_theorem/
formal_adapter_statement`: "The conditional Lean extension route is separately
parameterized by the named positive-epsilon, endpoint, scalar/cardinality,
stochastic-law, boundary, and selected-horizon adapter obligations." This
declaration is intentionally not the paper-facing source statement. -/
def CorollaryTwoConclusion [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    {L : ℝ} (ε : CorollaryTwoEpsilon)
    : Prop :=
    S.CorollaryTwoAdapterOutputGuarantee P L ε ∧
        S.corollaryTwoAdapterIterationCount L ε =
          2 * S.initialGap * L / ε.1 ^ 2 *
            (1 + Real.sqrt (Fintype.card B : ℝ) /
              (Fintype.card B' : ℝ)) ∧
        S.corollaryTwoAdapterGradientComplexity L ε ≤
          (Fintype.card ι : ℝ) +
            8 * S.initialGap * L * Real.sqrt (Fintype.card ι : ℝ) / ε.1 ^ 2

/-- Shared Corollary 2 complexity arithmetic after the corrected adapter has
received the source full-batch bridge `b = n` and the source range
`b' <= sqrt(b)`.

Book citation: `book/research/PAGE.json#/extension/additions/main_theorem/
proof/10` and `/proof/11` bound
`#grad = b + T(pb+(1-p)b')` by
`n + 8 Delta_0 L sqrt(n) / epsilon^2`. -/
theorem corollaryTwoAdapterGradientComplexity_bound
    {L : ℝ} (ε : CorollaryTwoEpsilon)
    (h_average_smooth : S.AverageLSmooth L)
    (h_initial_gap : 0 ≤ S.initialGap)
    (h_full_batch : CorollaryTwoFiniteSumIndex (ι := ι) (B := B))
    (h_batch_range : CorollaryTwoBatchRange (B := B) (B' := B')) :
    S.corollaryTwoAdapterGradientComplexity L ε ≤
      (Fintype.card ι : ℝ) +
        8 * S.initialGap * L * Real.sqrt (Fintype.card ι : ℝ) /
          ε.1 ^ 2 := by
  rw [corollaryTwoAdapterGradientComplexity_def,
      corollaryTwoAdapterIterationCount_def]
  let b : ℝ := Fintype.card B
  let b' : ℝ := Fintype.card B'
  let q : ℝ := 2 * S.initialGap * L / ε.1 ^ 2
  have hb : 0 < b := by
    dsimp [b]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card B)
  have hb' : 0 < b' := by
    dsimp [b']
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card B')
  have hsum : 0 < b + b' := by positivity
  have hcost :
      2 * b * b' / (b + b') ≤ 2 * b' := by
    have hfrac : b / (b + b') ≤ 1 := by
      exact (div_le_one hsum).2 (by nlinarith [hb'.le])
    have hmul :=
      mul_le_mul_of_nonneg_right hfrac
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hb'.le)
    calc
      2 * b * b' / (b + b') = (b / (b + b')) * (2 * b') := by
        field_simp [ne_of_gt hsum]
      _ ≤ 1 * (2 * b') := hmul
      _ = 2 * b' := by ring
  have hfactor :
      (1 + Real.sqrt b / b') *
          (2 * b * b' / (b + b')) ≤ 4 * Real.sqrt b := by
    have hfactor' :
        (1 + Real.sqrt b / b') * (2 * b') ≤
          4 * Real.sqrt b := by
      have heq :
          (1 + Real.sqrt b / b') * (2 * b') =
            2 * b' + 2 * Real.sqrt b := by
        field_simp [ne_of_gt hb']
      rw [heq]
      have hrange : b' ≤ Real.sqrt b := by
        simpa [b, b'] using h_batch_range
      nlinarith [Real.sqrt_nonneg b]
    exact
      le_trans
        (mul_le_mul_of_nonneg_left hcost
          (by positivity : 0 ≤ 1 + Real.sqrt b / b'))
        hfactor'
  have hq : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) h_initial_gap)
        h_average_smooth.1.le)
      (sq_nonneg _)
  have hprod :
      q * ((1 + Real.sqrt b / b') *
          (2 * b * b' / (b + b'))) ≤ q * (4 * Real.sqrt b) :=
    mul_le_mul_of_nonneg_left hfactor hq
  have hfull_real : b = (Fintype.card ι : ℝ) := by
    dsimp [b]
    exact_mod_cast h_full_batch
  change
    (Fintype.card B : ℝ) +
        (2 * S.initialGap * L / ε.1 ^ 2 *
          (1 + Real.sqrt (Fintype.card B : ℝ) /
            (Fintype.card B' : ℝ))) *
          (2 * (Fintype.card B : ℝ) * (Fintype.card B' : ℝ) /
            ((Fintype.card B : ℝ) + (Fintype.card B' : ℝ))) ≤
      (Fintype.card ι : ℝ) +
        8 * S.initialGap * L * Real.sqrt (Fintype.card ι : ℝ) /
          ε.1 ^ 2
  calc
    (Fintype.card B : ℝ) +
        (2 * S.initialGap * L / ε.1 ^ 2 *
          (1 + Real.sqrt (Fintype.card B : ℝ) /
            (Fintype.card B' : ℝ))) *
          (2 * (Fintype.card B : ℝ) * (Fintype.card B' : ℝ) /
            ((Fintype.card B : ℝ) + (Fintype.card B' : ℝ))) =
        b + q * ((1 + Real.sqrt b / b') *
          (2 * b * b' / (b + b'))) := by
            simp [b, b', q]
            ring
    _ ≤ b + q * (4 * Real.sqrt b) := by
      simpa [add_comm] using add_le_add_left hprod b
    _ = (Fintype.card ι : ℝ) +
        8 * S.initialGap * L * Real.sqrt (Fintype.card ι : ℝ) /
          ε.1 ^ 2 := by
            rw [hfull_real]
            dsimp [q]
            ring

/-! The source output is realized on PAGE's canonical random-source path
space. The ambient probability space used by a later Lean adapter is a
separate realization of that same algorithmic randomness. -/

/-- Source specialization of the probability parameter.

Book citation: `book/research/PAGE.json#/extension/additions/assumptions/0`:
`"math": "\\eta\\le \\frac{1}{L(1+\\frac{\\sqrt{b}}{b'})},\\quad b=n,\\quad
b'\\le \\sqrt{b},\\quad p_t\\equiv \\frac{b'}{b+b'}"`.
The probability component used here is the source clause
`p_t\\equiv \\frac{b'}{b+b'}`. -/
noncomputable def corollaryTwoSourceProbability
    (b b' : CorollaryTwoBatchSize) : ℝ :=
  (b'.1 : ℝ) / ((b.1 : ℝ) + (b'.1 : ℝ))

theorem corollaryTwoSourceProbability_domain
    (b b' : CorollaryTwoBatchSize) :
    ∀ t : ℕ,
      0 < corollaryTwoSourceProbability b b' ∧
        corollaryTwoSourceProbability b b' ≤ 1 := by
  intro t
  unfold corollaryTwoSourceProbability
  have hb : 0 < (b.1 : ℝ) := by exact_mod_cast b.2
  have hb' : 0 < (b'.1 : ℝ) := by exact_mod_cast b'.2
  constructor
  · positivity
  · exact (div_le_one (by positivity)).2 (le_add_of_nonneg_left hb.le)

/-- Canonical PAGE random-source path space for the scalar source batch sizes.

The source scalars are realized by the actual finite index types `Fin b` and
`Fin b'`; they are not merely compared with unrelated ambient types. -/
abbrev CorollaryTwoRandomSource
    (n b b' : CorollaryTwoBatchSize) : Type _ :=
  RandomSource (ι := Fin n.1) (B := Fin b.1) (B' := Fin b'.1)

instance corollaryTwoBatchSizeFinNonempty
    (b : CorollaryTwoBatchSize) : Nonempty (Fin b.1) :=
  ⟨⟨0, b.2⟩⟩

theorem corollaryTwoSource_batch_cardinality_bridge
    (b b' : CorollaryTwoBatchSize) :
    Fintype.card (Fin b.1) = b.1 ∧
      Fintype.card (Fin b'.1) = b'.1 := by
  simp

/-- Canonical source output `xhat_T`, uniform over the generated source
iterates at an explicitly supplied finite output window.

Book citation: `book/research/PAGE.json#/algorithm_spec/output`: “`xhat_T`
chosen uniformly from `{x^t}_{t∈[T]}`.” PDF citation: `paper/PAGE.pdf`,
Algorithm 1 output clause, p. 4. The source paper writes `T` as a
real-valued iteration bound, while Lean's finite uniform output is indexed by
an explicitly supplied `Fin T`; the source-boundary convention is recorded by
`corollaryTwoSourceOutputWindow`. -/
noncomputable def corollaryTwoSourceOutput
    (M : CorollaryTwoSourceModel (E := E) n)
    (b b' : CorollaryTwoBatchSize) (T : ℕ)
    (k : CorollaryTwoSourceOutputWindow T)
    (ξ : CorollaryTwoRandomSource n b b') : E :=
  (corollaryTwoSourceSetup M b b').uniformOutput T k ξ

/-!
The source-facing expected-gradient object is built from the canonical PAGE
source law and the uniformly selected generated iterate. It deliberately does
not mention an ambient probability space; ambient-measure identification and
the adapter's concrete window/count instantiation belong below.

Book citation: `book/research/PAGE.json#/algorithm_spec/output`:
`"\\hat{x}_T\\text{ chosen uniformly from }\\{x^t\\}_{t\\in[T]}"`.
-/
noncomputable def corollaryTwoSourceLaw
    (M : CorollaryTwoSourceModel (E := E) n)
    (b b' : CorollaryTwoBatchSize) :
    MeasureTheory.Measure (CorollaryTwoRandomSource n b b') := by
  letI : MeasurableSpace (Fin n.1) := ⊤
  let Ssrc := corollaryTwoSourceSetup M b b'
  let hp : Ssrc.RefreshProbabilityDomain := by
    intro t
    simpa [Ssrc, corollaryTwoSourceSetup] using
      corollaryTwoSourceProbability_domain b b' t
  exact Ssrc.randomSourceLaw hp

def CorollaryTwoSourceIntegrable
    (M : CorollaryTwoSourceModel (E := E) n)
    (b b' : CorollaryTwoBatchSize) (T : ℕ) [NeZero T] : Prop :=
  letI : MeasurableSpace (Fin n.1) := ⊤
  let Ssrc := corollaryTwoSourceSetup M b b'
  Ssrc.SelectedGradientNormIntegrable (corollaryTwoSourceLaw M b b') T

/-- The canonical source law is integrable on every positive finite output
window.  The proof uses the existing finite-past PAGE integrability bridge;
the source-law realization itself is proved once and is not a source theorem
input. -/
theorem corollaryTwoSource_stochasticLaws
    (M : CorollaryTwoSourceModel (E := E) n)
    (b b' : CorollaryTwoBatchSize) :
    letI : MeasurableSpace (Fin n.1) := ⊤
    (corollaryTwoSourceSetup M b b').StochasticLaws
      (corollaryTwoSourceLaw M b b') := by
  classical
  letI : MeasurableSpace (Fin n.1) := ⊤
  let Ssrc := corollaryTwoSourceSetup M b b'
  let hp : Ssrc.RefreshProbabilityDomain := by
    intro t
    simpa [Ssrc, corollaryTwoSourceSetup] using
      corollaryTwoSourceProbability_domain b b' t
  refine ⟨hp, ?_⟩
  have hpath : Ssrc.randomSourcePath =
      (fun ξ : CorollaryTwoRandomSource n b b' => ξ) := by
    funext ξ
    rcases ξ with ⟨branch, refresh, recursive⟩
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · funext t j
        simp [Ssrc, corollaryTwoSourceSetup, randomSourcePath,
          refreshSamplePath, refreshFinSample, Function.comp_def]
      · funext t j
        simp [Ssrc, corollaryTwoSourceSetup, randomSourcePath,
          recursiveSamplePath, recursiveFinSample, Function.comp_def]
  rw [hpath]
  simp [corollaryTwoSourceLaw, Ssrc, hp]

theorem corollaryTwoSource_integrable
    (M : CorollaryTwoSourceModel (E := E) n)
    (b b' : CorollaryTwoBatchSize) (T : ℕ) [NeZero T] :
    CorollaryTwoSourceIntegrable M b b' T := by
  classical
  letI : MeasurableSpace (Fin n.1) := ⊤
  let Ssrc := corollaryTwoSourceSetup M b b'
  let μ := corollaryTwoSourceLaw M b b'
  haveI : MeasureTheory.IsProbabilityMeasure μ := by
    dsimp [μ]
    unfold corollaryTwoSourceLaw
    dsimp
    unfold randomSourceLaw branchPathLaw refreshMiniBatchSourceLaw
      recursiveMiniBatchSourceLaw componentUniformMeasure
    infer_instance
  have h_laws : Ssrc.StochasticLaws μ := by
    simpa [Ssrc, μ] using corollaryTwoSource_stochasticLaws M b b'
  exact
    selected_gradient_norm_integrable_of_fiber_integrable (S := Ssrc) μ
      (fun k =>
        selected_gradient_norm_fiber_integrable_of_stochastic_laws
          (S := Ssrc) μ h_laws k.val)

/-- Canonical source-law expectation of the gradient norm at the uniformly
selected PAGE output in an explicitly supplied positive finite window.

The source-law integrability theorem above is consumed before the Bochner
integral is formed. Thus this is a source object, not a totalized-integral
fallback or a theorem-head integrability witness.

Book citations:
* `book/research/PAGE.json#/extension/additions/main_theorem/measure`:
  `"Expected gradient norm E[||nabla f(xhat_T)||] <= epsilon, together with
  the total stochastic-gradient computation count."`
* `book/research/PAGE.json#/algorithm_spec/output`:
  `"\\hat{x}_T\\text{ chosen uniformly from }\\{x^t\\}_{t\\in[T]}"`. -/
noncomputable def corollaryTwoSourceExpectedGradientNorm
    (M : CorollaryTwoSourceModel (E := E) n)
    (b b' : CorollaryTwoBatchSize) (T : ℕ) [NeZero T] : ℝ := by
  letI : MeasurableSpace (Fin n.1) := ⊤
  have h_int : CorollaryTwoSourceIntegrable M b b' T :=
    corollaryTwoSource_integrable M b b' T
  let Ssrc := corollaryTwoSourceSetup M b b'
  exact
    ∫ q : Fin T × CorollaryTwoRandomSource n b b',
      Ssrc.selectedGradientNormIntegrand T q ∂
        outputJointLaw (corollaryTwoSourceLaw M b b') T

/-- Canonical source-law expectation at the source-boundary realization of a
real-valued iteration horizon.  The positive finite window is supplied by
`corollaryTwoSourceOutputWindow`; its `NeZero` instance is internal to this
definition and is not a source theorem input.

Book citations:
* `book/research/PAGE.json#/extension/additions/main_theorem/measure`:
  `"Expected gradient norm E[||nabla f(xhat_T)||] <= epsilon, together with
  the total stochastic-gradient computation count."`
* `book/research/PAGE.json#/algorithm_spec/output`:
  `"\\hat{x}_T\\text{ chosen uniformly from }\\{x^t\\}_{t\\in[T]}"`.
* `book/research/PAGE.json#/extension/additions/main_theorem/statement_math`:
  `"\\text{Corollary 2 (Optimal result for problem (2)) Suppose that Assumption
  2 holds. Choose the stepsize }\\eta\\le
  \\frac{1}{L(1+\\frac{\\sqrt{b}}{b'})},\\text{ minibatch size }b=n,
  \\text{ secondary minibatch size }b'\\le \\sqrt{b}\\text{ and probability
  }p_t\\equiv \\frac{b'}{b+b'}.\\text{ Then the number of iterations performed
  by PAGE to find an }\\epsilon\\text{-approximate solution of the nonconvex
  finite-sum problem (2) can be bounded by
  }T=\\frac{2\\Delta_0L}{\\epsilon^2}\\left(1+\\frac{\\sqrt{b}}{b'}\\right).
  \\text{ Moreover, the number of stochastic gradient computations (i.e.,
  gradient complexity) is }\\#\\mathrm{grad}\\le n+
  \\frac{8\\Delta_0L\\sqrt{n}}{\\epsilon^2}
  =O\\left(n+\\frac{\\sqrt{n}}{\\epsilon^2}\\right)."`

The `max 1 (Nat.ceil τ)` finite-window realization is Lean-only boundary
machinery for combining those two source declarations; it is not asserted as
a paper convention. -/
noncomputable def corollaryTwoSourceExpectedGradientNormAtRealHorizon
    (M : CorollaryTwoSourceModel (E := E) n)
    (b b' : CorollaryTwoBatchSize) (τ : ℝ) : ℝ := by
  let T := corollaryTwoSourceOutputWindow τ
  have hT : 0 < T := by
    simpa [T] using corollaryTwoSourceOutputWindow_pos τ
  letI : NeZero T := ⟨Nat.ne_of_gt hT⟩
  exact corollaryTwoSourceExpectedGradientNorm M b b' T

@[simp]
theorem corollaryTwoSourceExpectedGradientNorm_def
    (M : CorollaryTwoSourceModel (E := E) n)
    (b b' : CorollaryTwoBatchSize) (T : ℕ) [NeZero T] :
    corollaryTwoSourceExpectedGradientNorm M b b' T =
      ∫ q : Fin T × CorollaryTwoRandomSource n b b',
        (corollaryTwoSourceSetup M b b').selectedGradientNormIntegrand T q ∂
          outputJointLaw (corollaryTwoSourceLaw M b b') T := by
  rfl

/-- Corrected-adapter alias for the same canonical source-law expectation.
Ambient-law identification is introduced only by the adapter declarations
below; this alias does not define a second expectation object. -/
noncomputable def corollaryTwoAdapterSourceExpectedGradientNormAtWindow
    (M : CorollaryTwoSourceModel (E := E) n)
    (b b' : CorollaryTwoBatchSize) (T : ℕ) [NeZero T] : ℝ :=
  corollaryTwoSourceExpectedGradientNorm M b b' T

@[simp]
theorem corollaryTwoAdapterSourceExpectedGradientNormAtWindow_def
    (M : CorollaryTwoSourceModel (E := E) n)
    (b b' : CorollaryTwoBatchSize) (T : ℕ) [NeZero T] :
    corollaryTwoAdapterSourceExpectedGradientNormAtWindow M b b' T =
      corollaryTwoSourceExpectedGradientNorm M b b' T := by
  rfl

/-- The source-facing expected-gradient conclusion uses the explicit
real-horizon representation convention above. It therefore has no selected
natural window, `NeZero` premise, or count-at-least premise in its source
contract.

Book citations:
* `book/research/PAGE.json#/extension/additions/main_theorem/measure`:
  `"Expected gradient norm E[||nabla f(xhat_T)||] <= epsilon, together with
  the total stochastic-gradient computation count."`
* `book/research/PAGE.json#/algorithm_spec/output`:
  `"\\hat{x}_T\\text{ chosen uniformly from }\\{x^t\\}_{t\\in[T]}"`.
* `book/research/PAGE.json#/extension/additions/main_theorem/statement_math`:
  `"\\text{Corollary 2 (Optimal result for problem (2)) Suppose that Assumption
  2 holds. Choose the stepsize }\\eta\\le
  \\frac{1}{L(1+\\frac{\\sqrt{b}}{b'})},\\text{ minibatch size }b=n,
  \\text{ secondary minibatch size }b'\\le \\sqrt{b}\\text{ and probability
  }p_t\\equiv \\frac{b'}{b+b'}."` -/
def CorollaryTwoSourceOutputGuarantee
    (M : CorollaryTwoSourceModel (E := E) n)
    (L : ℝ) (b b' : CorollaryTwoBatchSize)
    (ε : CorollaryTwoEpsilon) : Prop :=
  corollaryTwoSourceExpectedGradientNormAtRealHorizon M b b'
      (corollaryTwoSourceIterationCount M L b b' ε) ≤ ε.1

/-!
The source-facing expected-gradient object is built from the canonical PAGE
source law and the uniformly selected generated iterate. It deliberately does
not mention an ambient probability space; ambient-measure identification and
the adapter's concrete window/count instantiation belong below.
-/
noncomputable def corollaryTwoAdapterSourceLawExpectationSpec
    (M : CorollaryTwoSourceModel (E := E) n)
    (b b' : CorollaryTwoBatchSize)
    (T : ℕ) [NeZero T] (r : ℝ) : Prop := by
  letI : MeasurableSpace (Fin n.1) := ⊤
  exact
    CorollaryTwoSourceIntegrable M b b' T ∧
      r = corollaryTwoSourceExpectedGradientNorm M b b' T

/-- Corrected-adapter identification between the canonical source-law
expectation and the ambient-measure expectation. -/
def CorollaryTwoAdapterOutputIdentification [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω)
    (M : CorollaryTwoSourceModel (E := E) n)
    (b b' : CorollaryTwoBatchSize)
    (T : ℕ) [NeZero T] : Prop :=
  S.SelectedGradientNormIntegrable P T ∧
    ∀ r : ℝ,
    corollaryTwoAdapterSourceLawExpectationSpec M b b' T r →
        r = S.expectedSelectedGradientNorm P T

@[simp]
theorem corollaryTwoAdapterOutputIdentification_def [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω)
    (M : CorollaryTwoSourceModel (E := E) n)
    (b b' : CorollaryTwoBatchSize)
    (T : ℕ) [NeZero T] :
    S.CorollaryTwoAdapterOutputIdentification P M b b' T ↔
      (S.SelectedGradientNormIntegrable P T ∧
        ∀ r : ℝ,
          corollaryTwoAdapterSourceLawExpectationSpec M b b' T r →
            r = S.expectedSelectedGradientNorm P T) := by
  rfl

/-!
Corrected-adapter identification for the canonical source expected-gradient
object.  This relation is deliberately separate from the source contract:
the source side supplies the canonical source-law expectation, while this
adapter relates it to the ambient probability-space expectation and records
ambient integrability.
-/
def CorollaryTwoAdapterSourceOutputIdentification [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω)
    (M : CorollaryTwoSourceModel (E := E) n)
    (b b' : CorollaryTwoBatchSize)
    (T : ℕ) [NeZero T] : Prop :=
  S.SelectedGradientNormIntegrable P T ∧
    S.expectedSelectedGradientNorm P T =
      corollaryTwoAdapterSourceExpectedGradientNormAtWindow M b b' T

theorem corollaryTwo_source_output_to_selected_gradient_norm
    [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    (M : CorollaryTwoSourceModel (E := E) n)
    (b b' : CorollaryTwoBatchSize) (T : ℕ) [NeZero T]
    (ε : CorollaryTwoEpsilon)
    (h_source_bound :
      ∃ r : ℝ,
        corollaryTwoAdapterSourceLawExpectationSpec M b b' T r ∧
          r ≤ ε.1)
    (hidentification :
      S.CorollaryTwoAdapterOutputIdentification P M b b' T) :
    S.expectedSelectedGradientNorm P T ≤ ε.1 := by
  rcases h_source_bound with ⟨r, hr, hle⟩
  rw [← hidentification.2 r hr]
  exact hle

theorem corollaryTwo_source_output_to_selected_gradient_norm_of_identification
    [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    (M : CorollaryTwoSourceModel (E := E) n)
    (b b' : CorollaryTwoBatchSize) (T : ℕ) [NeZero T]
    (ε : CorollaryTwoEpsilon)
    (h_source_bound :
      corollaryTwoAdapterSourceExpectedGradientNormAtWindow M b b' T ≤ ε.1)
    (hidentification :
      S.CorollaryTwoAdapterSourceOutputIdentification P M b b' T) :
    S.expectedSelectedGradientNorm P T ≤ ε.1 := by
  rw [hidentification.2]
  exact h_source_bound

/-- Corrected-adapter output guarantee on the canonical source-law realization.

The source realization uses exactly one finite output window: the disclosed
`max 1 (Nat.ceil τ)` convention applied to the paper's real-valued iteration
expression. It does not quantify over every later natural horizon; those
horizons belong to the independent ambient Theorem 1 adapter.

Book citations:
* `book/research/PAGE.json#/extension/additions/main_theorem/measure`:
  `"Expected gradient norm E[||nabla f(xhat_T)||] <= epsilon, together with
  the total stochastic-gradient computation count."`
* `book/research/PAGE.json#/algorithm_spec/output`:
  `"\\hat{x}_T\\text{ chosen uniformly from }\\{x^t\\}_{t\\in[T]}"`.
* `book/research/PAGE.json#/extension/additions/main_theorem/statement_math`:
  `"\\text{Then the number of iterations performed by PAGE to find an
  }\\epsilon\\text{-approximate solution of the nonconvex finite-sum problem
  (2) can be bounded by }T=\\frac{2\\Delta_0L}{\\epsilon^2}
  \\left(1+\\frac{\\sqrt{b}}{b'}\\right)."` -/
def CorollaryTwoAdapterSourceLawOutputGuarantee
    (M : CorollaryTwoSourceModel (E := E) n)
    (L : ℝ) (b b' : CorollaryTwoBatchSize)
    (ε : CorollaryTwoEpsilon) : Prop :=
  let T :=
    corollaryTwoSourceOutputWindow
      (corollaryTwoSourceIterationCount M L b b' ε)
  letI : NeZero T :=
    ⟨Nat.ne_of_gt
      (corollaryTwoSourceOutputWindow_pos
        (corollaryTwoSourceIterationCount M L b b' ε))⟩
  ∃ r : ℝ,
    corollaryTwoAdapterSourceLawExpectationSpec M b b' T r ∧
      r ≤ ε.1

theorem corollaryTwo_source_output_to_source_law_window
    (M : CorollaryTwoSourceModel (E := E) n)
    (b b' : CorollaryTwoBatchSize) {L : ℝ}
    (ε : CorollaryTwoEpsilon)
    (h_source_output :
      CorollaryTwoSourceOutputGuarantee M L b b' ε) :
    CorollaryTwoAdapterSourceLawOutputGuarantee M L b b' ε := by
  let T :=
    corollaryTwoSourceOutputWindow
      (corollaryTwoSourceIterationCount M L b b' ε)
  have hT : 0 < T := by
    simpa [T] using
      corollaryTwoSourceOutputWindow_pos
        (corollaryTwoSourceIterationCount M L b b' ε)
  letI : NeZero T := ⟨Nat.ne_of_gt hT⟩
  change ∃ r : ℝ,
    corollaryTwoAdapterSourceLawExpectationSpec M b b' T r ∧
      r ≤ ε.1
  refine ⟨corollaryTwoSourceExpectedGradientNorm M b b' T, ?_, ?_⟩
  · exact ⟨corollaryTwoSource_integrable M b b' T, rfl⟩
  · simpa [T, corollaryTwoSourceExpectedGradientNormAtRealHorizon] using
      h_source_output

/-- Source-facing arithmetic specialization of Corollary 2.

Book citation: `book/research/PAGE.json#/extension/additions/main_theorem/
statement_math`: the source states
`"\\text{Then the number of iterations performed by PAGE to find an
}\\epsilon\\text{-approximate solution of the nonconvex finite-sum problem
(2) can be bounded by }T=\\frac{2\\Delta_0L}{\\epsilon^2}
\\left(1+\\frac{\\sqrt{b}}{b'}\\right).\\text{ Moreover, the number of
stochastic gradient computations (i.e., gradient complexity) is }
\\#\\mathrm{grad}\\le n+\\frac{8\\Delta_0L\\sqrt{n}}{\\epsilon^2}
=O\\left(n+\\frac{\\sqrt{n}}{\\epsilon^2}\\right)."`
The positive-epsilon domain is carried by `CorollaryTwoEpsilon`; no
probability-space or selected-horizon realization is part of this source
arithmetic relation. -/
def CorollaryTwoSourceArithmetic
    (M : CorollaryTwoSourceModel (E := E) n)
    (L : ℝ) (b b' : CorollaryTwoBatchSize)
    (ε : CorollaryTwoEpsilon) : Prop :=
  corollaryTwoSourceIterationCount M L b b' ε =
      2 * (corollaryTwoSourceSetup M b b').initialGap * L / ε.1 ^ 2 *
        (1 + Real.sqrt (b.1 : ℝ) / (b'.1 : ℝ)) ∧
    corollaryTwoSourceGradientComplexity M L b b' ε ≤
      (n.1 : ℝ) + 8 * (corollaryTwoSourceSetup M b b').initialGap * L *
        Real.sqrt (n.1 : ℝ) / ε.1 ^ 2

theorem corollaryTwoSourceArithmetic_of_schedule
    (M : CorollaryTwoSourceModel (E := E) n)
    {L : ℝ} (b b' : CorollaryTwoBatchSize)
    (ε : CorollaryTwoEpsilon)
    (h_average_smooth :
      (corollaryTwoSourceSetup M b b').AverageLSmooth L)
    (h_source_schedule :
      CorollaryTwoSourceSchedule M L b b') :
    CorollaryTwoSourceArithmetic M L b b' ε := by
  let Ssrc := corollaryTwoSourceSetup M b b'
  have h_initial_gap : 0 ≤ Ssrc.initialGap := by
    dsimp [Ssrc, initialGap]
    exact sub_nonneg.mpr
      ((corollaryTwoSourceSetup M b b').fStar_le_objective
        (corollaryTwoSourceSetup M b b').x0)
  have h_full_batch :
      CorollaryTwoFiniteSumIndex (ι := Fin n.1) (B := Fin b.1) := by
    simpa [CorollaryTwoFiniteSumIndex] using h_source_schedule.2.1
  have h_batch_range :
      CorollaryTwoBatchRange (B := Fin b.1) (B' := Fin b'.1) := by
    simpa [CorollaryTwoBatchRange] using h_source_schedule.2.2
  have h_bound :
      Ssrc.corollaryTwoAdapterGradientComplexity L ε ≤
        (Fintype.card (Fin n.1) : ℝ) +
          8 * Ssrc.initialGap * L * Real.sqrt (Fintype.card (Fin n.1) : ℝ) /
            ε.1 ^ 2 :=
    Ssrc.corollaryTwoAdapterGradientComplexity_bound ε h_average_smooth
      h_initial_gap h_full_batch h_batch_range
  constructor
  · rfl
  · simpa [Ssrc, corollaryTwoSourceGradientComplexity,
      corollaryTwoSourceIterationCount, corollaryTwoAdapterGradientComplexity,
      corollaryTwoAdapterIterationCount, corollaryTwoExpectedIterationCost,
      h_source_schedule.2.1] using h_bound

/-- Strict-branch formal Corollary 2 route. This is the adapter that exposes
the endpoint, full-batch, strict-cardinality, stochastic-law, and positive-
epsilon obligations required by the inherited Theorem 1 declaration. -/
theorem corollaryTwo_strict_formal_adapter [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    {L : ℝ} (ε : CorollaryTwoEpsilon)
    (h_average_smooth : S.AverageLSmooth L)
    (h_initial_gap : 0 ≤ S.initialGap)
    (h_endpoint : S.CorollaryTwoMaximalEndpoint L)
    (h_full_batch : CorollaryTwoFiniteSumIndex (ι := ι) (B := B))
    (h_strict_batch : CorollaryTwoStrictBatch (B := B) (B' := B'))
    (h_batch_range : CorollaryTwoBatchRange (B := B) (B' := B'))
    (h_probability :
      ∀ t : ℕ,
        S.refreshProbability t =
          corollaryTwoProbability (B := B) (B' := B'))
    (h_laws : S.StochasticLaws P) :
    S.CorollaryTwoConclusion (L := L) P ε := by
  refine ⟨?_, ?_, ?_⟩
  · intro T hne hT
    exact
      S.corollaryTwo_strict_adapter P ε h_average_smooth h_endpoint
        h_full_batch h_strict_batch h_probability h_laws hT
  · exact S.corollaryTwoAdapterIterationCount_def L ε
  · exact
      S.corollaryTwoAdapterGradientComplexity_bound ε h_average_smooth
        h_initial_gap h_full_batch h_batch_range

/-- Unit-batch formal Corollary 2 route. The source allows the boundary
`b' = sqrt(b)`, while the inherited Theorem 1 interface does not; the
boundary proof therefore remains a named obligation rather than being hidden
inside the strict adapter. -/
theorem corollaryTwo_unit_formal_adapter [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    {L : ℝ} (ε : CorollaryTwoEpsilon)
    (h_average_smooth : S.AverageLSmooth L)
    (h_initial_gap : 0 ≤ S.initialGap)
    (h_endpoint : S.CorollaryTwoMaximalEndpoint L)
    (h_full_batch : CorollaryTwoFiniteSumIndex (ι := ι) (B := B))
    (h_boundary : CorollaryTwoUnitBatchBoundary (B := B) (B' := B'))
    (h_batch_range : CorollaryTwoBatchRange (B := B) (B' := B'))
    (h_probability :
      ∀ t : ℕ,
        S.refreshProbability t =
          corollaryTwoProbability (B := B) (B' := B'))
    (h_laws : S.StochasticLaws P) :
    S.CorollaryTwoConclusion (L := L) P ε := by
  refine ⟨?_, ?_, ?_⟩
  · have h_component_card :
        Fintype.card ι = 1 :=
      corollaryTwo_unit_boundary_component_card
        (ι := ι) (B := B) (B' := B') h_full_batch h_boundary
    intro T hne hT
    have hη_pos : 0 < S.η := by
      rw [h_endpoint]
      unfold corollaryTwoStepsizeEndpoint
      have hL : 0 < L := h_average_smooth.1
      have hb' : 0 < (Fintype.card B' : ℝ) := by
        exact_mod_cast (Fintype.card_pos : 0 < Fintype.card B')
      positivity
    have hratio :=
      corollaryTwo_ratio_identity (B := B) (B' := B')
    have h_output_schedule :
        S.TheoremOneOutputSchedule L
          (corollaryTwoProbability (B := B) (B' := B')) := by
      refine ⟨hη_pos, ?_, h_full_batch, h_probability,
        corollaryTwoProbability_pos (B := B) (B' := B'),
        corollaryTwoProbability_le_one (B := B) (B' := B')⟩
      calc
        S.η = corollaryTwoStepsizeEndpoint (B := B) (B' := B') L := h_endpoint
        _ =
            (L *
              (1 + Real.sqrt
                ((1 - corollaryTwoProbability (B := B) (B' := B')) /
                  (corollaryTwoProbability (B := B) (B' := B') *
                    (Fintype.card B' : ℝ)))))⁻¹ := by
              rw [corollaryTwoStepsizeEndpoint, hratio]
    have hcount :
        S.theoremOneIterationCount L corollaryTwoProbability ε.1 =
          S.corollaryTwoAdapterIterationCount L ε :=
      S.corollaryTwoAdapterIterationCount_eq_theoremOneIterationCount ε
    have hT' :
        S.theoremOneIterationCount L
            (corollaryTwoProbability (B := B) (B' := B')) ε.1 ≤ (T : ℝ) := by
      rw [hcount]
      exact hT
    exact
      S.theoremOne_output_of_outputSchedule P h_average_smooth
        h_output_schedule h_laws ε.2 hT'
  · exact S.corollaryTwoAdapterIterationCount_def L ε
  · exact
      S.corollaryTwoAdapterGradientComplexity_bound ε h_average_smooth
        h_initial_gap h_full_batch h_batch_range

/-- Recombined formal adapter for Corollary 2. The source-facing theorem keeps
the non-strict range; this route makes the strict-or-unit correction explicit
before any inherited convergence theorem is consumed. -/
theorem corollaryTwo_formal_adapter [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    {L : ℝ} (ε : CorollaryTwoEpsilon)
    (h_average_smooth : S.AverageLSmooth L)
    (h_initial_gap : 0 ≤ S.initialGap)
    (h_endpoint : S.CorollaryTwoMaximalEndpoint L)
    (h_full_batch : CorollaryTwoFiniteSumIndex (ι := ι) (B := B))
    (h_batch :
      CorollaryTwoStrictBatch (B := B) (B' := B') ∨
        CorollaryTwoUnitBatchBoundary (B := B) (B' := B'))
    (h_batch_range : CorollaryTwoBatchRange (B := B) (B' := B'))
    (h_probability :
      ∀ t : ℕ,
        S.refreshProbability t =
          corollaryTwoProbability (B := B) (B' := B'))
    (h_laws : S.StochasticLaws P) :
    S.CorollaryTwoConclusion (L := L) P ε := by
  rcases h_batch with h_strict | h_boundary
  · exact
      S.corollaryTwo_strict_formal_adapter P ε h_average_smooth h_initial_gap
        h_endpoint h_full_batch h_strict h_batch_range h_probability h_laws
  · exact
      S.corollaryTwo_unit_formal_adapter P ε h_average_smooth h_initial_gap
        h_endpoint h_full_batch h_boundary h_batch_range h_probability h_laws

/-- Corrected adapter conclusion: the independent ambient Theorem 1 route is
kept for every admissible natural horizon, while the source-law bridge is
recorded only at its disclosed canonical window. -/
def CorollaryTwoCorrectedAdapterConclusion [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    {L : ℝ} (ε : CorollaryTwoEpsilon)
    (M : CorollaryTwoSourceModel (E := E) n)
    (b b' : CorollaryTwoBatchSize) : Prop :=
  S.CorollaryTwoConclusion (L := L) P ε ∧
    (let T :=
      corollaryTwoSourceOutputWindow
        (corollaryTwoSourceIterationCount M L b b' ε)
     letI : NeZero T :=
      ⟨Nat.ne_of_gt
        (corollaryTwoSourceOutputWindow_pos
          (corollaryTwoSourceIterationCount M L b b' ε))⟩
     S.expectedSelectedGradientNorm P T ≤ ε.1)

/-- Corrected source-law proof root for the PAGE Corollary 2 extension.

The theorem instantiates PAGE with the canonical source setup and canonical
source law, derives the finite-index, batch-range, probability, stochastic-law,
and initial-gap obligations internally, and then consumes
`corollaryTwo_formal_adapter`. The explicit maximal-endpoint premise is the
B-track correction for the displayed L-based horizon. -/
theorem corollaryTwo_corrected_adapter_root
    {L : ℝ} (ε : CorollaryTwoEpsilon)
    {b b' n : CorollaryTwoBatchSize}
    (M : CorollaryTwoSourceModel (E := E) n)
    (h_average_smooth :
      (corollaryTwoSourceSetup M b b').AverageLSmooth L)
    (h_source_schedule :
      CorollaryTwoSourceSchedule M L b b')
    (h_endpoint :
      (corollaryTwoSourceSetup M b b').CorollaryTwoMaximalEndpoint L) :
    CorollaryTwoSourceOutputGuarantee M L b b' ε ∧
      CorollaryTwoSourceArithmetic M L b b' ε := by
  classical
  letI : MeasurableSpace (Fin n.1) := ⊤
  let Ssrc := corollaryTwoSourceSetup M b b'
  let Psrc := corollaryTwoSourceLaw M b b'
  haveI : MeasureTheory.IsProbabilityMeasure Psrc := by
    dsimp [Psrc]
    unfold corollaryTwoSourceLaw
    dsimp
    unfold randomSourceLaw branchPathLaw refreshMiniBatchSourceLaw
      recursiveMiniBatchSourceLaw componentUniformMeasure
    infer_instance
  have h_initial_gap : 0 ≤ Ssrc.initialGap := by
    dsimp [Ssrc, initialGap]
    exact sub_nonneg.mpr
      ((corollaryTwoSourceSetup M b b').fStar_le_objective
        (corollaryTwoSourceSetup M b b').x0)
  have h_full_batch :
      CorollaryTwoFiniteSumIndex (ι := Fin n.1) (B := Fin b.1) := by
    simpa [CorollaryTwoFiniteSumIndex] using h_source_schedule.2.1
  have h_batch_range :
      CorollaryTwoBatchRange (B := Fin b.1) (B' := Fin b'.1) := by
    simpa [CorollaryTwoBatchRange] using h_source_schedule.2.2
  have h_batch :
      CorollaryTwoStrictBatch (B := Fin b.1) (B' := Fin b'.1) ∨
        CorollaryTwoUnitBatchBoundary (B := Fin b.1) (B' := Fin b'.1) := by
    by_cases h_strict :
        CorollaryTwoStrictBatch (B := Fin b.1) (B' := Fin b'.1)
    · exact Or.inl h_strict
    · exact Or.inr
        (corollaryTwo_batch_boundary_split
          (B := Fin b.1) (B' := Fin b'.1) h_batch_range h_strict)
  have h_probability :
      ∀ t : ℕ,
        Ssrc.refreshProbability t =
          corollaryTwoProbability (B := Fin b.1) (B' := Fin b'.1) := by
    intro t
    simp [Ssrc, corollaryTwoSourceSetup, corollaryTwoProbability]
  have h_laws : Ssrc.StochasticLaws Psrc := by
    simpa [Ssrc, Psrc] using corollaryTwoSource_stochasticLaws M b b'
  have h_adapter :
      Ssrc.CorollaryTwoConclusion (L := L) Psrc ε :=
    Ssrc.corollaryTwo_formal_adapter Psrc ε h_average_smooth h_initial_gap
      h_endpoint h_full_batch h_batch h_batch_range h_probability h_laws
  have h_source_output :
      CorollaryTwoSourceOutputGuarantee M L b b' ε := by
    let τ := corollaryTwoSourceIterationCount M L b b' ε
    let T := corollaryTwoSourceOutputWindow τ
    have hT_pos : 0 < T := by
      simpa [T, τ] using corollaryTwoSourceOutputWindow_pos τ
    letI : NeZero T := ⟨Nat.ne_of_gt hT_pos⟩
    have hT_lower :
        Ssrc.corollaryTwoAdapterIterationCount L ε ≤ (T : ℝ) := by
      simpa [Ssrc, τ, T, corollaryTwoSourceIterationCount,
        corollaryTwoAdapterIterationCount] using
        corollaryTwoSourceOutputWindow_real_horizon_le τ
    have h_selected :
        Ssrc.SelectedGradientNormIntegrable Psrc T ∧
          Ssrc.expectedSelectedGradientNorm Psrc T ≤ ε.1 :=
      h_adapter.1 hT_lower
    have h_expected_eq :
        corollaryTwoSourceExpectedGradientNorm M b b' T =
          Ssrc.expectedSelectedGradientNorm Psrc T := by
      simpa [corollaryTwoSourceExpectedGradientNorm, Ssrc, Psrc] using
        (Ssrc.expectedSelectedGradientNorm_of_integrable Psrc T
          h_selected.1).symm
    calc
      corollaryTwoSourceExpectedGradientNormAtRealHorizon M b b' τ =
          corollaryTwoSourceExpectedGradientNorm M b b' T := by
            simp [corollaryTwoSourceExpectedGradientNormAtRealHorizon, T, τ]
      _ = Ssrc.expectedSelectedGradientNorm Psrc T := h_expected_eq
      _ ≤ ε.1 := h_selected.2
  exact ⟨h_source_output,
    corollaryTwoSourceArithmetic_of_schedule M b b' ε
      h_average_smooth h_source_schedule⟩

end Setup

end PAGE
end Unverified
end Algorithms
