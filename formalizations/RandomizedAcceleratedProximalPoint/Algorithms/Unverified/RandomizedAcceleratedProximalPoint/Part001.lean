import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.IdentDistribIndep
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.PNat.Defs
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Strong
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import SOptLib.Analysis.ConvexSmoothExtension
import SOptLib.Model.BlockSampling
import SOptLib.Model.Bregman
import SOptLib.Model.Carrier
import SOptLib.Model.Filtration
import SOptLib.Model.Iterates
import SOptLib.Model.Objective
import SOptLib.Model.ParameterChoices
import SOptLib.Model.Selection
import SOptLib.Model.Stationarity
import SOptLib.Model.StochasticOracle
import SOptLib.Glue.Algebra
import SOptLib.Glue.Analysis
import SOptLib.Glue.Calculus
import SOptLib.Glue.Probability
import SOptLib.Layer0.ConvexFOC
import SOptLib.Layer0.Objective
import SOptLib.Layer1.Descent
import SOptLib.Layer1.Proximal

/-!
# Randomized Accelerated Proximal-Point Method (RapGrad / RaGrad)

Statement-only formalization of Lan's randomized accelerated proximal-point method
for nonconvex finite-sum optimization from Section 6.6 of
*First-Order and Stochastic Optimization Methods for Machine Learning*.

The file packages the finite-sum nonconvex objective, the component smoothness and
one-sided curvature conditions, the strongly convex proximal subproblems, the RaGrad
inner-solver state (primal iterate `xᵗ`, per-component memory arrays `xᵢᵗ` and `yᵢᵗ`,
extrapolated point `x̃ᵗ`, and averaged gradient estimator `ỹᵢᵗ`), and the outer
RapGrad recursion into `RandomizedAcceleratedProximalPointSetup`. It then defines the
inner-loop process, the per-component memory state, the Bregman divergence for the
quadratic prox, the approximate stationarity notion, and declares the corrected
source-domain lemma chain (`eq_6_6_45`, Lemma 6.12, Lemma 6.13, Theorem 6.17,
Lemma 6.14, and Theorem 6.16), with the remaining analytic proof bodies left as
`proof-placeholder`.
-/

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι]
variable {Ω : Type*} [MeasurableSpace Ω]

/-- State for one outer iteration of RapGrad / RaGrad.  We store the current primal
iterate `x`, the per-component primal memories `xMem i`, and the per-component gradient
memories `yMem i`.  The extrapolated point and averaged estimator are computed on-the-fly
from this state. -/
structure RaGradState (ι : Type*) (E : Type*) where
  x   : E
  xPrev : E
  xMem : ι → E
  yMem : ι → E

/-- State collected after completing all inner iterations for one outer proximal
subproblem of RapGrad.  In addition to the final RaGrad state we also expose the
inner-iterate trajectory so later statements can refer to `xᵗ`. -/
structure RapGradOuterState (ι : Type*) (E : Type*) where
  inner    : ℕ → RaGradState ι E
  xBar     : E
  xBarMem  : ι → E
  yBarMem  : ι → E

/-- Complete setup for the Randomized Accelerated Proximal-Point Method (Algorithm 6.8).

The structure stores the finite-sum nonconvex objective data, the uniform sampling
law, and the paper parameters.  Lean regularity obligations such as selector
measurability are kept as derived theorems rather than setup fields.  Parameters
`μ` and `L` satisfy `0 < μ ≤ L`; the hat-smoothness constant is `L̂ = L + 2μ`.
The outer step count is `k` and the inner step count for each proximal subproblem is
`s`.  The parameter sequences `α`, `τ`, `η`, `γ` are all indexed by the inner-loop
counter, and Algorithm 6.9's stated input boundary requires `{α_t}`, `{τ_t}`, and
`{η_t}` to be nonnegative. -/
structure RandomizedAcceleratedProximalPointSetup
    (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    (Ω : Type*) [MeasurableSpace Ω] where
  /-- Feasible set `X`.

  Source: `book/FOML/RandomizedAcceleratedProximalPoint.json#/setup/variable_space`.
  The JSON states: `X ⊆ ℝ^n is a closed convex set` following Eq. (6.6.1). -/
  X        : Set E
  /-- Initial point `x̄⁰ ∈ X`.

  Source: `book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec/initialization`.
  The JSON initializes Algorithm 6.8 with `\bar{x}^0 ∈ X`. -/
  x₀       : E
  /-- Paper optimizer `x*` of problem (6.6.1), as named in Theorem 6.16.

  Source: `book/FOML/RandomizedAcceleratedProximalPoint.json#/assumptions/2`,
  which says `x^*` denotes an optimal solution of problem (6.6.1); Theorem 6.16
  refers to the same `x^*` in
  `book/FOML/RandomizedAcceleratedProximalPoint.json#/main_theorem/statement_math`. -/
  xStar    : E
  /-- Component objectives `fᵢ : X → ℝ`.

  Source: `book/FOML/RandomizedAcceleratedProximalPoint.json#/setup/problem`
  states `f(x) := 1/m ∑ f_i(x)`, and
  `book/FOML/RandomizedAcceleratedProximalPoint.json#/setup/variable_space`
  states `f_i : X → ℝ` are nonconvex smooth functions. -/
  f        : ι → {x : E // x ∈ X} → ℝ
  /-- Source-domain differentiability of the component objectives.

  Source: `book/FOML/RandomizedAcceleratedProximalPoint.json#/setup/variable_space`
  states that `f_i : X → ℝ` are smooth functions, and Eq. (6.6.2) states the
  component gradients are Lipschitz on `X`.  Lean realizes the paper gradient
  below as SOptLib's boundary-safe carrier gradient; Mathlib's `gradientWithin`
  is kept only as an internal derivative bridge, not as the source-facing
  gradient selector. -/
  hgradf_differentiableWithinAt :
    ∀ i (x : {x : E // x ∈ X}),
      DifferentiableWithinAt ℝ (SOptLib.carrierTotalizeOn X (f i)) X x.1
  /-- Gradient smoothness constant shared by all components; book JSON
  `book/FOML/RandomizedAcceleratedProximalPoint.json#/assumptions/0`, Eq. (6.6.2):
  `‖∇f_i(x_1)-∇f_i(x_2)‖ ≤ L‖x_1-x_2‖`. -/
  L        : ℝ
  /-- One-sided curvature constant.

  Source: `book/FOML/RandomizedAcceleratedProximalPoint.json#/assumptions/1`,
  Eq. (6.6.3), with parameter condition `0 < μ ≤ L`. -/
  μ        : ℝ
  /-- Contraction rate for RaGrad inner loop.

  Source: `book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec/parameters/0`,
  Eq. (6.6.16): `α = 1 - 2/(m(√(1+16c/m)+1))`, `c = 2 + L/μ`. -/
  α        : ℝ
  /-- Inner-loop momentum sequence.

  Source: `book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec/parameters/1`,
  Eq. (6.6.17): `α_t = α` for `t = 1, ..., s`. -/
  αSeq     : ℕ → ℝ
  /-- Inner-loop primal step-size sequence.

  Source: `book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec/parameters/1`,
  Eq. (6.6.17): `τ_t = 1/(m(1-α))-1` for `t = 1, ..., s`. -/
  τSeq     : ℕ → ℝ
  /-- Inner-loop dual step-size sequence.

  Source: `book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec/parameters/1`,
  Eq. (6.6.17): `η_t = α/(1-α)` for `t = 1, ..., s`. -/
  ηSeq     : ℕ → ℝ
  /-- Inner-loop weight sequence.

  Source: `book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec/parameters/1`,
  Eq. (6.6.17): `γ_t = α^{-t}` for `t = 1, ..., s`. -/
  γSeq     : ℕ → ℝ
  /-- Number of inner iterations per outer proximal subproblem.

  Sources:
  `book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec/parameters/0`
  and `book/FOML/RandomizedAcceleratedProximalPoint.json#/assumptions/4`; both
  identify `s` as the Algorithm 6.9 inner-loop length. -/
  s        : ℕ
  /-- Positive number of outer RapGrad iterations.  The paper output
  `ℓ̂ ∈ [k]` is only source-meaningful for a nonempty window, so positivity is
  modeled in the object itself rather than as a theorem-head hypothesis.  Book
  JSON `book/FOML/RandomizedAcceleratedProximalPoint.json#/main_theorem/statement_math`
  says the generated outer iterates are indexed by `ℓ = 1, ..., k`, and
  `book/FOML/RandomizedAcceleratedProximalPoint.json#/assumptions/3` says
  `\hat{\ell}` is randomly selected from `[k]`. -/
  k        : ℕ+
  /-- Uniform sample stream selecting a component index at each inner step; book
  JSON `book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec/steps/3`,
  Algorithm 6.9 random component: `i_t` is uniformly distributed over `[m]`. -/
  ξ        : ℕ → Ω → ι
  /-- Reference probability measure used to interpret Algorithm 6.9 random choices.

  Source: `book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec/steps/3`
  states that each `i_t` is uniformly distributed; this measure is the Lean
  probability space on which those random variables are interpreted. -/
  P        : Measure Ω
  -- Hypotheses
  /-- Probability-space structure for the random component choices.

  Source: `book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec/steps/3`
  states the Algorithm 6.9 component `i_t` is uniformly distributed over `[m]`;
  Lean records that distribution relative to the probability measure `P`. -/
  hP              : IsProbabilityMeasure P
  /-- Closedness of the feasible set.

  Source: `book/FOML/RandomizedAcceleratedProximalPoint.json#/setup/variable_space`
  states `X ⊆ ℝ^n is a closed convex set`. -/
  hX_closed       : IsClosed X
  /-- Convexity of the feasible set.

  Source: `book/FOML/RandomizedAcceleratedProximalPoint.json#/setup/variable_space`
  states `X ⊆ ℝ^n is a closed convex set`. -/
  hX_convex       : Convex ℝ X
  /-- Initial point feasibility.

  Source: `book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec/initialization`
  states Algorithm 6.8 starts with `\bar{x}^0 ∈ X`. -/
  hx₀_mem         : x₀ ∈ X
  /-- Theorem 6.16's `x*` lies in the feasible set.

  Source: `book/FOML/RandomizedAcceleratedProximalPoint.json#/assumptions/2`
  says `x^*` denotes an optimal solution to problem (6.6.1), whose feasible
  domain is `x ∈ X` by
  `book/FOML/RandomizedAcceleratedProximalPoint.json#/setup/problem`. -/
  hxStar_mem      : xStar ∈ X
  /-- Theorem 6.16's `x*` is an optimal solution of problem (6.6.1).

  Source: `book/FOML/RandomizedAcceleratedProximalPoint.json#/assumptions/2`
  states `x^*` denotes the optimal solution to problem (6.6.1); the objective is
  the finite average `1/m ∑ f_i(x)` from
  `book/FOML/RandomizedAcceleratedProximalPoint.json#/setup/problem`. -/
  hxStar_min      :
    ∀ z : {x : E // x ∈ X},
      (Fintype.card ι : ℝ)⁻¹ *
          Finset.sum Finset.univ (fun i => f i ⟨xStar, hxStar_mem⟩) ≤
        (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ (fun i => f i z)
  /-- Positivity part of the one-sided curvature parameter condition.

  Source: `book/FOML/RandomizedAcceleratedProximalPoint.json#/assumptions/1`
  lists the Eq. (6.6.3) parameter condition `0 < μ ≤ L`. -/
  hμ_pos          : 0 < μ
  /-- Upper-bound part of the one-sided curvature parameter condition.

  Source: `book/FOML/RandomizedAcceleratedProximalPoint.json#/assumptions/1`
  lists the Eq. (6.6.3) parameter condition `0 < μ ≤ L`. -/
  hμ_le_L         : μ ≤ L
  /-- Component gradient L-smoothness.

  Source: `book/FOML/RandomizedAcceleratedProximalPoint.json#/assumptions/0`,
  Eq. (6.6.2): `‖∇f_i(x_1)-∇f_i(x_2)‖ ≤ L‖x_1-x_2‖` for all
  `x_1,x_2 ∈ X`. -/
  hsmooth         :
    ∀ i (x₁ x₂ : {x : E // x ∈ X}),
      ‖SOptLib.carrierGradient X (f i) x₁ -
          SOptLib.carrierGradient X (f i) x₂‖ ≤
        L * ‖x₁.1 - x₂.1‖
  /-- One-sided curvature condition.

  Source: `book/FOML/RandomizedAcceleratedProximalPoint.json#/assumptions/1`,
  Eq. (6.6.3): `f_i(x_1)-f_i(x_2)-⟪∇f_i(x_2),x_1-x_2⟫ ≥
  - μ/2 ‖x_1-x_2‖^2` for all `x_1,x_2 ∈ X`. -/
  hone_sided      :
    ∀ i (x₁ x₂ : {x : E // x ∈ X}),
      f i x₁ - f i x₂ -
          ⟪SOptLib.carrierGradient X (f i) x₂, x₁.1 - x₂.1⟫_ℝ ≥
        -(μ / 2) * ‖x₁.1 - x₂.1‖ ^ 2
  /-- Algorithm 6.9 input boundary: `{α_t}` is nonnegative on the paper run
  range `t = 1, ..., s`.

  Source: `source/FOML/First-order and stochastic optimization methods for machine learning.pdf`,
  Algorithm 6.9 around extracted lines 23488-23512: the input line assumes
  nonnegative parameters `{α_t}`, `{τ_t}`, and `{η_t}`. -/
  hαSeq_nonneg    : ∀ t, 1 ≤ t → t ≤ s → 0 ≤ αSeq t
  /-- Algorithm 6.9 input boundary: `{τ_t}` is nonnegative on the paper run
  range `t = 1, ..., s`.

  Source: `source/FOML/First-order and stochastic optimization methods for machine learning.pdf`,
  Algorithm 6.9 around extracted lines 23488-23512: the input line assumes
  nonnegative parameters `{α_t}`, `{τ_t}`, and `{η_t}`. -/
  hτSeq_nonneg    : ∀ t, 1 ≤ t → t ≤ s → 0 ≤ τSeq t
  /-- Algorithm 6.9 input boundary: `{η_t}` is nonnegative on the paper run
  range `t = 1, ..., s`.

  Source: `source/FOML/First-order and stochastic optimization methods for machine learning.pdf`,
  Algorithm 6.9 around extracted lines 23488-23512: the input line assumes
  nonnegative parameters `{α_t}`, `{τ_t}`, and `{η_t}`. -/
  hηSeq_nonneg    : ∀ t, 1 ≤ t → t ≤ s → 0 ≤ ηSeq t
  /-- Algorithm 6.9 says to generate a random variable `i_t`; measurability is part
  of that random-variable datum, not a theorem derived from uniform singleton
  masses.

  Source: `book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec/steps/3`
  states `i_t` is uniformly distributed over `[m]`; the PDF Algorithm 6.9 line
  says to generate a random variable `i_t` uniformly distributed over `[m]`. -/
  hξ_measurable    : ∀ n, Measurable (ξ n)
  /-- Freshness of the Algorithm 6.9 component samples.

  Source: `book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec/steps/3`
  states that at each RaGrad step the algorithm generates `i_t` uniformly over
  `[m]`.  The PDF proof of Lemma 6.13 then writes `E_s` for expectation over
  `i_1, ..., i_s` and uses `E_{i_t}` in Eq. (6.6.30), which is the product-stream
  freshness interface rather than merely a list of marginal singleton masses. -/
  hξ_iIndep       : iIndepFun ξ P
  /-- Uniform marginal distribution of the random component in Algorithm 6.9.

  Source: `book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec/steps/3`
  states `i_t` is uniformly distributed over `[m]`. -/
  hξ_uniform      :
    ∀ n i, P {ω | ξ n ω = i} = (Fintype.card ι : ENNReal)⁻¹

  /-- Additional repair condition: the convex regularized component subproblem
  admits a whole-space extension preserving values, intrinsic gradients and
  the source constant Lhat = L + 2 * μ. -/
  subproblem_extension : ∀ z ∈ X, ∀ i, Nonempty (SOptLib.ConvexSmoothExtensionOn X
    (fun x => SOptLib.quadraticRegularizedObjectiveOn (f i) μ z x)
    (fun x => SOptLib.quadraticRegularizedGradientOn
      (SOptLib.carrierGradient X (f i)) μ z x)
    (normSeminorm ℝ E) (L + 2 * μ))

namespace RandomizedAcceleratedProximalPointSetup


variable (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)

/-- State for one outer iteration of RapGrad / RaGrad.  We store the current primal
iterate `x`, the per-component primal memories `xMem i`, and the per-component gradient
memories `yMem i`.  The extrapolated point and averaged estimator are computed on-the-fly
from this state. -/
structure RaGradState (ι : Type*) (E : Type*) where
  x   : E
  xPrev : E
  xMem : ι → E
  yMem : ι → E

/-- State collected after completing all inner iterations for one outer proximal
subproblem of RapGrad.  In addition to the final RaGrad state we also expose the
inner-iterate trajectory so later statements can refer to `xᵗ`. -/
structure RapGradOuterState (ι : Type*) (E : Type*) where
  inner    : ℕ → RaGradState ι E
  xBar     : E
  xBarMem  : ι → E
  yBarMem  : ι → E

/-- Complete setup for the Randomized Accelerated Proximal-Point Method (Algorithm 6.8).

The structure stores the finite-sum nonconvex objective data, the uniform sampling
law, and the paper parameters.  Lean regularity obligations such as selector
measurability are kept as derived theorems rather than setup fields.  Parameters
`μ` and `L` satisfy `0 < μ ≤ L`; the hat-smoothness constant is `L̂ = L + 2μ`.
The outer step count is `k` and the inner step count for each proximal subproblem is
`s`.  The parameter sequences `α`, `τ`, `η`, `γ` are all indexed by the inner-loop
counter, and Algorithm 6.9's stated input boundary requires `{α_t}`, `{τ_t}`, and
`{η_t}` to be nonnegative. -/
structure RandomizedAcceleratedProximalPointSetup
    (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    (Ω : Type*) [MeasurableSpace Ω] where
  /-- Feasible set `X`.

  Source: `book/FOML/RandomizedAcceleratedProximalPoint.json#/setup/variable_space`.
  The JSON states: `X ⊆ ℝ^n is a closed convex set` following Eq. (6.6.1). -/
  X        : Set E
  /-- Initial point `x̄⁰ ∈ X`.

  Source: `book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec/initialization`.
  The JSON initializes Algorithm 6.8 with `\bar{x}^0 ∈ X`. -/
  x₀       : E
  /-- Paper optimizer `x*` of problem (6.6.1), as named in Theorem 6.16.

  Source: `book/FOML/RandomizedAcceleratedProximalPoint.json#/assumptions/2`,
  which says `x^*` denotes an optimal solution of problem (6.6.1); Theorem 6.16
  refers to the same `x^*` in
  `book/FOML/RandomizedAcceleratedProximalPoint.json#/main_theorem/statement_math`. -/
  xStar    : E
  /-- Component objectives `fᵢ : X → ℝ`.

  Source: `book/FOML/RandomizedAcceleratedProximalPoint.json#/setup/problem`
  states `f(x) := 1/m ∑ f_i(x)`, and
  `book/FOML/RandomizedAcceleratedProximalPoint.json#/setup/variable_space`
  states `f_i : X → ℝ` are nonconvex smooth functions. -/
  f        : ι → {x : E // x ∈ X} → ℝ
  /-- Source-domain differentiability of the component objectives.

  Source: `book/FOML/RandomizedAcceleratedProximalPoint.json#/setup/variable_space`
  states that `f_i : X → ℝ` are smooth functions, and Eq. (6.6.2) states the
  component gradients are Lipschitz on `X`.  Lean realizes the paper gradient
  below as SOptLib's boundary-safe carrier gradient; Mathlib's `gradientWithin`
  is kept only as an internal derivative bridge, not as the source-facing
  gradient selector. -/
  hgradf_differentiableWithinAt :
    ∀ i (x : {x : E // x ∈ X}),
      DifferentiableWithinAt ℝ (SOptLib.carrierTotalizeOn X (f i)) X x.1
  /-- Gradient smoothness constant shared by all components; book JSON
  `book/FOML/RandomizedAcceleratedProximalPoint.json#/assumptions/0`, Eq. (6.6.2):
  `‖∇f_i(x_1)-∇f_i(x_2)‖ ≤ L‖x_1-x_2‖`. -/
  L        : ℝ
  /-- One-sided curvature constant.

  Source: `book/FOML/RandomizedAcceleratedProximalPoint.json#/assumptions/1`,
  Eq. (6.6.3), with parameter condition `0 < μ ≤ L`. -/
  μ        : ℝ
  /-- Contraction rate for RaGrad inner loop.

  Source: `book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec/parameters/0`,
  Eq. (6.6.16): `α = 1 - 2/(m(√(1+16c/m)+1))`, `c = 2 + L/μ`. -/
  α        : ℝ
  /-- Inner-loop momentum sequence.

  Source: `book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec/parameters/1`,
  Eq. (6.6.17): `α_t = α` for `t = 1, ..., s`. -/
  αSeq     : ℕ → ℝ
  /-- Inner-loop primal step-size sequence.

  Source: `book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec/parameters/1`,
  Eq. (6.6.17): `τ_t = 1/(m(1-α))-1` for `t = 1, ..., s`. -/
  τSeq     : ℕ → ℝ
  /-- Inner-loop dual step-size sequence.

  Source: `book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec/parameters/1`,
  Eq. (6.6.17): `η_t = α/(1-α)` for `t = 1, ..., s`. -/
  ηSeq     : ℕ → ℝ
  /-- Inner-loop weight sequence.

  Source: `book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec/parameters/1`,
  Eq. (6.6.17): `γ_t = α^{-t}` for `t = 1, ..., s`. -/
  γSeq     : ℕ → ℝ
  /-- Number of inner iterations per outer proximal subproblem.

  Sources:
  `book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec/parameters/0`
  and `book/FOML/RandomizedAcceleratedProximalPoint.json#/assumptions/4`; both
  identify `s` as the Algorithm 6.9 inner-loop length. -/
  s        : ℕ
  /-- Positive number of outer RapGrad iterations.  The paper output
  `ℓ̂ ∈ [k]` is only source-meaningful for a nonempty window, so positivity is
  modeled in the object itself rather than as a theorem-head hypothesis.  Book
  JSON `book/FOML/RandomizedAcceleratedProximalPoint.json#/main_theorem/statement_math`
  says the generated outer iterates are indexed by `ℓ = 1, ..., k`, and
  `book/FOML/RandomizedAcceleratedProximalPoint.json#/assumptions/3` says
  `\hat{\ell}` is randomly selected from `[k]`. -/
  k        : ℕ+
  /-- Uniform sample stream selecting a component index at each inner step; book
  JSON `book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec/steps/3`,
  Algorithm 6.9 random component: `i_t` is uniformly distributed over `[m]`. -/
  ξ        : ℕ → Ω → ι
  /-- Reference probability measure used to interpret Algorithm 6.9 random choices.

  Source: `book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec/steps/3`
  states that each `i_t` is uniformly distributed; this measure is the Lean
  probability space on which those random variables are interpreted. -/
  P        : Measure Ω
  -- Hypotheses
  /-- Probability-space structure for the random component choices.

  Source: `book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec/steps/3`
  states the Algorithm 6.9 component `i_t` is uniformly distributed over `[m]`;
  Lean records that distribution relative to the probability measure `P`. -/
  hP              : IsProbabilityMeasure P
  /-- Closedness of the feasible set.

  Source: `book/FOML/RandomizedAcceleratedProximalPoint.json#/setup/variable_space`
  states `X ⊆ ℝ^n is a closed convex set`. -/
  hX_closed       : IsClosed X
  /-- Convexity of the feasible set.

  Source: `book/FOML/RandomizedAcceleratedProximalPoint.json#/setup/variable_space`
  states `X ⊆ ℝ^n is a closed convex set`. -/
  hX_convex       : Convex ℝ X
  /-- Initial point feasibility.

  Source: `book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec/initialization`
  states Algorithm 6.8 starts with `\bar{x}^0 ∈ X`. -/
  hx₀_mem         : x₀ ∈ X
  /-- Theorem 6.16's `x*` lies in the feasible set.

  Source: `book/FOML/RandomizedAcceleratedProximalPoint.json#/assumptions/2`
  says `x^*` denotes an optimal solution to problem (6.6.1), whose feasible
  domain is `x ∈ X` by
  `book/FOML/RandomizedAcceleratedProximalPoint.json#/setup/problem`. -/
  hxStar_mem      : xStar ∈ X
  /-- Theorem 6.16's `x*` is an optimal solution of problem (6.6.1).

  Source: `book/FOML/RandomizedAcceleratedProximalPoint.json#/assumptions/2`
  states `x^*` denotes the optimal solution to problem (6.6.1); the objective is
  the finite average `1/m ∑ f_i(x)` from
  `book/FOML/RandomizedAcceleratedProximalPoint.json#/setup/problem`. -/
  hxStar_min      :
    ∀ z : {x : E // x ∈ X},
      (Fintype.card ι : ℝ)⁻¹ *
          Finset.sum Finset.univ (fun i => f i ⟨xStar, hxStar_mem⟩) ≤
        (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ (fun i => f i z)
  /-- Positivity part of the one-sided curvature parameter condition.

  Source: `book/FOML/RandomizedAcceleratedProximalPoint.json#/assumptions/1`
  lists the Eq. (6.6.3) parameter condition `0 < μ ≤ L`. -/
  hμ_pos          : 0 < μ
  /-- Upper-bound part of the one-sided curvature parameter condition.

  Source: `book/FOML/RandomizedAcceleratedProximalPoint.json#/assumptions/1`
  lists the Eq. (6.6.3) parameter condition `0 < μ ≤ L`. -/
  hμ_le_L         : μ ≤ L
  /-- Component gradient L-smoothness.

  Source: `book/FOML/RandomizedAcceleratedProximalPoint.json#/assumptions/0`,
  Eq. (6.6.2): `‖∇f_i(x_1)-∇f_i(x_2)‖ ≤ L‖x_1-x_2‖` for all
  `x_1,x_2 ∈ X`. -/
  hsmooth         :
    ∀ i (x₁ x₂ : {x : E // x ∈ X}),
      ‖SOptLib.carrierGradient X (f i) x₁ -
          SOptLib.carrierGradient X (f i) x₂‖ ≤
        L * ‖x₁.1 - x₂.1‖
  /-- One-sided curvature condition.

  Source: `book/FOML/RandomizedAcceleratedProximalPoint.json#/assumptions/1`,
  Eq. (6.6.3): `f_i(x_1)-f_i(x_2)-⟪∇f_i(x_2),x_1-x_2⟫ ≥
  - μ/2 ‖x_1-x_2‖^2` for all `x_1,x_2 ∈ X`. -/
  hone_sided      :
    ∀ i (x₁ x₂ : {x : E // x ∈ X}),
      f i x₁ - f i x₂ -
          ⟪SOptLib.carrierGradient X (f i) x₂, x₁.1 - x₂.1⟫_ℝ ≥
        -(μ / 2) * ‖x₁.1 - x₂.1‖ ^ 2
  /-- Algorithm 6.9 input boundary: `{α_t}` is nonnegative on the paper run
  range `t = 1, ..., s`.

  Source: `source/FOML/First-order and stochastic optimization methods for machine learning.pdf`,
  Algorithm 6.9 around extracted lines 23488-23512: the input line assumes
  nonnegative parameters `{α_t}`, `{τ_t}`, and `{η_t}`. -/
  hαSeq_nonneg    : ∀ t, 1 ≤ t → t ≤ s → 0 ≤ αSeq t
  /-- Algorithm 6.9 input boundary: `{τ_t}` is nonnegative on the paper run
  range `t = 1, ..., s`.

  Source: `source/FOML/First-order and stochastic optimization methods for machine learning.pdf`,
  Algorithm 6.9 around extracted lines 23488-23512: the input line assumes
  nonnegative parameters `{α_t}`, `{τ_t}`, and `{η_t}`. -/
  hτSeq_nonneg    : ∀ t, 1 ≤ t → t ≤ s → 0 ≤ τSeq t
  /-- Algorithm 6.9 input boundary: `{η_t}` is nonnegative on the paper run
  range `t = 1, ..., s`.

  Source: `source/FOML/First-order and stochastic optimization methods for machine learning.pdf`,
  Algorithm 6.9 around extracted lines 23488-23512: the input line assumes
  nonnegative parameters `{α_t}`, `{τ_t}`, and `{η_t}`. -/
  hηSeq_nonneg    : ∀ t, 1 ≤ t → t ≤ s → 0 ≤ ηSeq t
  /-- Algorithm 6.9 says to generate a random variable `i_t`; measurability is part
  of that random-variable datum, not a theorem derived from uniform singleton
  masses.

  Source: `book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec/steps/3`
  states `i_t` is uniformly distributed over `[m]`; the PDF Algorithm 6.9 line
  says to generate a random variable `i_t` uniformly distributed over `[m]`. -/
  hξ_measurable    : ∀ n, Measurable (ξ n)
  /-- Freshness of the Algorithm 6.9 component samples.

  Source: `book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec/steps/3`
  states that at each RaGrad step the algorithm generates `i_t` uniformly over
  `[m]`.  The PDF proof of Lemma 6.13 then writes `E_s` for expectation over
  `i_1, ..., i_s` and uses `E_{i_t}` in Eq. (6.6.30), which is the product-stream
  freshness interface rather than merely a list of marginal singleton masses. -/
  hξ_iIndep       : iIndepFun ξ P
  /-- Uniform marginal distribution of the random component in Algorithm 6.9.

  Source: `book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec/steps/3`
  states `i_t` is uniformly distributed over `[m]`. -/
  hξ_uniform      :
    ∀ n i, P {ω | ξ n ω = i} = (Fintype.card ι : ENNReal)⁻¹

  /-- Additional repair condition: the convex regularized component subproblem
  admits a whole-space extension preserving values, intrinsic gradients and
  the source constant Lhat = L + 2 * μ. -/
  subproblem_extension : ∀ z ∈ X, ∀ i, Nonempty (SOptLib.ConvexSmoothExtensionOn X
    (fun x => SOptLib.quadraticRegularizedObjectiveOn (f i) μ z x)
    (fun x => SOptLib.quadraticRegularizedGradientOn
      (SOptLib.carrierGradient X (f i)) μ z x)
    (normSeminorm ℝ E) (L + 2 * μ))

namespace RandomizedAcceleratedProximalPointSetup

variable (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)

/-- Hat smoothness constant `L̂ = L + 2μ` from the text preceding Lemma 6.12.

Book citation:
`book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec/parameters/2`.

No SOptLib match: searched "hat smoothness L plus two mu parameter", scanned
`SOptLib/Model/ParameterChoices.lean`, `SOptLib/Model/Budget.lean`,
`SOptLib/Layer0/Objective.lean`, and `SOptLib/Layer1/Proximal.lean`; none align
with the paper's local definition of `L̂` because they provide generic budget,
parameter-choice, or smoothness proof tools rather than this Eq. (6.6.8)
subproblem curvature constant. -/
noncomputable def Lhat : ℝ :=
  setup.L + 2 * setup.μ

/-- Defining equation for the paper constant `L̂`.

Book JSON `book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec/parameters/2`
states `\hat{L}=L+2\mu`; this theorem records the definitional equality rather
than storing it as setup data. -/
theorem Lhat_def : setup.Lhat = setup.L + 2 * setup.μ := by
  rfl

/-- Ambient totalization of the carrier component objective.

This is a bridge, not the paper-facing component datum: the setup stores
`fᵢ : X → ℝ` exactly as stated after Eq. (6.6.1).  The bridge reuses
`SOptLib.carrierTotalizeOn`, which was checked because it is the reusable
carrier-to-ambient totalization primitive; all paper-facing evaluations below
carry feasibility facts or are paired with feasible-point rewrite theorems. -/
noncomputable def fAmbient (i : ι) : E → ℝ :=
  SOptLib.carrierTotalizeOn setup.X (setup.f i)

/-- Feasible-point rewrite for the ambient bridge of `fᵢ : X → ℝ`. -/
@[simp]
theorem fAmbient_of_mem (i : ι) {x : E} (hx : x ∈ setup.X) :
    setup.fAmbient i x = setup.f i ⟨x, hx⟩ := by
  simp [fAmbient, SOptLib.carrierTotalizeOn, hx]

/-- Internal ambient within-gradient selector for the carrier component objective.

This is not the paper-facing gradient object.  It is the Mathlib derivative
selector used to bridge carrier-gradient pairings to `HasGradientWithinAt`
statements when a proof needs ambient calculus. -/
noncomputable def gradfWithin (i : ι) (x : {x : E // x ∈ setup.X}) : E :=
  gradientWithin (setup.fAmbient i) setup.X x.1

/-- Component gradient `∇fᵢ` on the source domain `X`.

This is the paper's displayed `∇f_i(x)` for `x ∈ X`, realized as SOptLib's
boundary-safe carrier gradient in the affine span of `X`.  The old
`gradientWithin` selector is retained only as the private derivative bridge
`gradfWithin`; it is not canonical on lower-dimensional carriers because its
normal component is invisible to feasible displacements. -/
noncomputable def gradf (i : ι) (x : {x : E // x ∈ setup.X}) : E :=
  SOptLib.carrierGradient setup.X (setup.f i) x

/-- The source-domain component gradient has the derivative semantics of the
paper's smooth component objective. -/
theorem gradf_hasGradientWithinAt (i : ι) (x : {x : E // x ∈ setup.X}) :
    HasGradientWithinAt (setup.fAmbient i) (setup.gradf i x) setup.X x.1 := by
  exact SOptLib.carrierGradient_hasGradientWithinAt_of_totalizeOn
    (X := setup.X) (f := setup.f i) x setup.hX_convex
    (setup.hgradf_differentiableWithinAt i x)

/-- Definitional projection of the internal within-gradient bridge. -/
theorem gradfWithin_eq_gradientWithin (i : ι) (x : {x : E // x ∈ setup.X}) :
    setup.gradfWithin i x = gradientWithin (setup.fAmbient i) setup.X x.1 := by
  rfl

/-- Feasible-direction pairing bridge from the source carrier gradient to the
internal within-gradient selector. -/
theorem gradf_inner_eq_gradientWithin_on_feasible_direction
    (i : ι) (anchor z x : {x : E // x ∈ setup.X}) :
    ⟪SOptLib.carrierGradientFrom setup.X (setup.f i) anchor z, x.1 - z.1⟫_ℝ =
      ⟪gradientWithin (setup.fAmbient i) setup.X z.1, x.1 - z.1⟫_ℝ := by
  exact
    SOptLib.carrierGradientFrom_inner_eq_gradientWithin_on_feasible_direction
      (X := setup.X) (v := setup.f i) (ν := setup.fAmbient i)
      anchor z x setup.hX_convex
      (setup.hgradf_differentiableWithinAt i z)
      (by
        intro y
        exact (setup.fAmbient_of_mem i y.2).symm)

/-- The source carrier gradient has the same feasible-direction pairing as the
internal within-gradient selector. -/
theorem gradf_inner_eq_gradientWithin
    (i : ι) (z x : {x : E // x ∈ setup.X}) :
    ⟪setup.gradf i z, x.1 - z.1⟫_ℝ =
      ⟪gradientWithin (setup.fAmbient i) setup.X z.1, x.1 - z.1⟫_ℝ := by
  simpa [gradf, SOptLib.carrierGradient] using
    setup.gradf_inner_eq_gradientWithin_on_feasible_direction i z z x

/-- Averaged finite-sum objective on the source domain:
`f(x) = (1/m) ∑ᵢ fᵢ(x)` for `x ∈ X`. -/
noncomputable def fAvgOn (x : {x : E // x ∈ setup.X}) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ (fun i => setup.f i x)

/-- Ambient bridge for the averaged objective, obtained from the component
totalizations.  The paper-facing objective is `fAvgOn`; this definition exists
only for statements that still use ambient iterates together with feasibility
invariants. -/
noncomputable def fAvg (x : E) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ (fun i => setup.fAmbient i x)

/-- Feasible-point rewrite for the averaged finite-sum objective. -/
@[simp]
theorem fAvg_of_mem {x : E} (hx : x ∈ setup.X) :
    setup.fAvg x = setup.fAvgOn ⟨x, hx⟩ := by
  rw [fAvg, fAvgOn]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => setup.fAmbient_of_mem i hx)

/-- Averaged finite-sum gradient on the source domain:
`∇f(x) = (1/m) ∑ᵢ ∇fᵢ(x)`. -/
noncomputable def gradFOn (x : {x : E // x ∈ setup.X}) : E :=
  (Fintype.card ι : ℝ)⁻¹ • Finset.sum Finset.univ (fun i => setup.gradf i x)

/-- Derivative bridge for the source-domain finite-sum gradient.

The proof is deferred: it combines the component derivative bridges with finite
linearity of the average.  This is a theorem obligation, not an extra theorem-head
assumption. -/
theorem gradFOn_hasGradientWithinAt (x : {x : E // x ∈ setup.X}) :
    HasGradientWithinAt setup.fAvg (setup.gradFOn x) setup.X x.1 := by
  classical
  simpa [RandomizedAcceleratedProximalPointSetup.fAvg,
    RandomizedAcceleratedProximalPointSetup.gradFOn, x.2] using
    (SOptLib.HasGradientWithinAt.fintype_average
      (F := setup.fAmbient)
      (G := fun i y => if hy : y ∈ setup.X then setup.gradf i ⟨y, hy⟩ else 0)
      (X := setup.X) (x := x.1)
      (by
        intro i
        simpa [x.2] using setup.gradf_hasGradientWithinAt i x))

/-- Internal ambient totalization of the finite-sum gradient.

This is not the paper-facing gradient object.  It exists only for legacy ambient
helpers; on feasible inputs it reduces to `gradFOn`, and outside `X` it carries no
source meaning. -/
noncomputable def gradF (x : E) : E :=
  by
    classical
    exact if hx : x ∈ setup.X then setup.gradFOn ⟨x, hx⟩ else 0

/-- On feasible points, the internal ambient bridge reduces to the source-domain
finite-sum gradient. -/
theorem gradF_eq_gradFOn {x : E} (hx : x ∈ setup.X) :
    setup.gradF x = setup.gradFOn ⟨x, hx⟩ := by
  simp [gradF, hx]

/-- The source assumption `0 < μ ≤ L` implies the smoothness constant is positive.

This is a derived bridge from Eq. (6.6.3), not primitive setup data. -/
theorem L_pos : 0 < setup.L :=
  lt_of_lt_of_le setup.hμ_pos setup.hμ_le_L

/-- Source-domain explicit-center proximal component objective
`ψᵢ,z(x) = fᵢ(x) + μ‖x − z‖²` for `x ∈ X`.

This is the recursive kernel for Algorithm 6.8's subproblem split.  `SOptLib`
`compositeObjective`/`compositeObjectiveAmbient` were considered, but they model
generic finite-sum/composite objectives and do not expose the paper's literal
per-component quadratic shift over the source domain from Eq. (6.6.8). -/
noncomputable def psiAtOn (z : E) (i : ι) (x : {x : E // x ∈ setup.X}) : ℝ :=
  SOptLib.quadraticRegularizedObjectiveOn (setup.f i) setup.μ z x

/-- Internal ambient compatibility wrapper for `ψᵢ,z`.

This is not the paper-facing objective: Eq. (6.6.8) defines `ψ_i` only for
`x ∈ X`, represented by `psiAtOn`.  The ambient wrapper is kept for Mathlib
`HasGradientWithinAt` and `IsMinOn` bridge statements.  `SOptLib.compositeObjective`
and `SOptLib.compositeObjectiveAmbient` were checked; they only provide generic
pointwise addition and do not encode Lan's literal finite-sum subproblem split. -/
noncomputable def psiAt (z : E) (i : ι) (x : E) : ℝ :=
  setup.fAmbient i x + setup.μ * ‖x - z‖ ^ 2

/-- Feasible-point rewrite for the ambient compatibility wrapper of `ψᵢ,z`. -/
@[simp]
theorem psiAt_of_mem (z : E) (i : ι) {x : E} (hx : x ∈ setup.X) :
    setup.psiAt z i x = setup.psiAtOn z i ⟨x, hx⟩ := by
  simp [psiAt, psiAtOn, setup.fAmbient_of_mem i hx]

/-- Source-domain gradient of `ψᵢ,z`.

Algorithm 6.9 evaluates `∇ψᵢ` only at refreshed component points in `X`
(Eq. 6.6.11).  `SOptLib.objectiveKernel`/`objectiveWellDefined` were checked,
but they model stochastic objective evaluation and integrability rather than the
domain-restricted deterministic component gradient needed here, so this local
subtype wrapper records the paper boundary explicitly. -/
noncomputable def gradPsiOnAt (z : E) (i : ι) (x : {x : E // x ∈ setup.X}) : E :=
  SOptLib.quadraticRegularizedGradientOn (setup.gradf i) setup.μ z x

/-- Derivative bridge for the explicit-center subproblem component gradient.

This records that the source-domain expression used for `∇ψᵢ,z` is the derivative
of `ψᵢ,z` on `X`; the proof is deferred to the prover because it combines
`gradf_hasGradientWithinAt` with the quadratic-gradient calculation. -/
theorem gradPsiOnAt_hasGradientWithinAt
    (z : E) (i : ι) (x : {x : E // x ∈ setup.X}) :
    HasGradientWithinAt (setup.psiAt z i) (setup.gradPsiOnAt z i x) setup.X x.1 := by
  simpa [RandomizedAcceleratedProximalPointSetup.psiAt,
    RandomizedAcceleratedProximalPointSetup.gradPsiOnAt,
    SOptLib.quadraticRegularizedGradientOn] using
      (setup.gradf_hasGradientWithinAt i x).add_const_mul_norm_sub_sq setup.μ z

/-- Internal ambient totalization of the explicit-center gradient.

This is a compatibility bridge for ambient helper code, not the source-facing
gradient object.  On feasible inputs it reduces to `gradPsiOnAt`; outside `X` it
has no paper semantics. -/
noncomputable def gradPsiAt (z : E) (i : ι) (x : E) : E :=
  by
    classical
    exact if hx : x ∈ setup.X then setup.gradPsiOnAt z i ⟨x, hx⟩ else 0

/-- Feasible-point rewrite for the internal ambient bridge of `∇ψᵢ,z`. -/
theorem gradPsiAt_of_mem (z : E) (i : ι) {x : E} (hx : x ∈ setup.X) :
    setup.gradPsiAt z i x = setup.gradPsiOnAt z i ⟨x, hx⟩ := by
  simp [gradPsiAt, hx]

/-- Coercion bridge from the source-domain `∇ψᵢ,z` to the internal ambient
totalization. -/
theorem gradPsiOnAt_coe (z : E) (i : ι) (x : {x : E // x ∈ setup.X}) :
    setup.gradPsiOnAt z i x = setup.gradPsiAt z i x.1 := by
  rw [setup.gradPsiAt_of_mem z i x.2]

/-- Component Bregman error `Ψ_i(x,y)` from Eq. (6.6.28), specialized to the
explicit-center component objective `ψᵢ,z`.  `carrierBregmanDivergence` and
`carrierBregmanFormula` were checked; they are paper-neutral carrier APIs, while
Lemma 6.13 needs the literal `psiAtOn`/`gradPsiOnAt` expression appearing in
`SubproblemCurvature_6_6_8`. -/
noncomputable def psiBregmanAt
    (z : E) (i : ι) (x y : {x : E // x ∈ setup.X}) : ℝ :=
  setup.psiAtOn z i x - setup.psiAtOn z i y -
    ⟪setup.gradPsiOnAt z i y, x.1 - y.1⟫_ℝ

/-- Curvature bounds for the Eq. (6.6.28) component Bregman error.  This is the
source step used in Eqs. (6.6.35)-(6.6.36), projected from
`SubproblemCurvature_6_6_8` without changing the public theorem statement. -/
theorem psiBregmanAt_curvature_bounds
    (z : E)
    (hcurv :
      ∀ i (x y : {x : E // x ∈ setup.X}),
        setup.μ / 2 * ‖x.1 - y.1‖ ^ 2 ≤
          setup.psiAtOn z i x - setup.psiAtOn z i y -
            ⟪setup.gradPsiOnAt z i y, x.1 - y.1⟫_ℝ ∧
        setup.psiAtOn z i x - setup.psiAtOn z i y -
            ⟪setup.gradPsiOnAt z i y, x.1 - y.1⟫_ℝ ≤
          setup.Lhat / 2 * ‖x.1 - y.1‖ ^ 2)
    (i : ι) (x y : {x : E // x ∈ setup.X}) :
    setup.μ / 2 * ‖x.1 - y.1‖ ^ 2 ≤ setup.psiBregmanAt z i x y ∧
      setup.psiBregmanAt z i x y ≤ setup.Lhat / 2 * ‖x.1 - y.1‖ ^ 2 := by
  simpa [psiBregmanAt] using hcurv i x y

/-- The explicit-center component gradient `∇ψᵢ,z` is `L̂`-Lipschitz on the
source carrier.

Aligns with the smoothness premise used in Lan Lemma 6.13 after Eq. (6.6.35):
the candidate `carrierGradient_lipschitz_of_assumption` only projects an
already-stored Lipschitz hypothesis, while here the paper's `ψᵢ,z` gradient
must be assembled from `setup.hsmooth` for `fᵢ` and the quadratic shift
`L̂ = L + 2μ`.  The searched Bregman candidates provide distance lower bounds
or smooth upper models, not this literal component-gradient Lipschitz bridge. -/
theorem gradPsiOnAt_lipschitz
    (z : E) (i : ι) (x y : {x : E // x ∈ setup.X}) :
    ‖setup.gradPsiOnAt z i x - setup.gradPsiOnAt z i y‖ ≤
      setup.Lhat * ‖x.1 - y.1‖ := by
  have hf :
      ‖setup.gradf i x - setup.gradf i y‖ ≤
        setup.L * ‖x.1 - y.1‖ := by
    exact setup.hsmooth i x y
  simpa [RandomizedAcceleratedProximalPointSetup.gradPsiOnAt,
    SOptLib.quadraticRegularizedGradientOn, setup.Lhat_def] using
    (norm_add_nonneg_smul_sub_center_sub_le
      (g := setup.gradf i)
      (eval := fun x : {x : E // x ∈ setup.X} => x.1)
      (L := setup.L) (c := 2 * setup.μ) (z := z)
      (by nlinarith [setup.hμ_pos]) x y hf)

/-- The fixed-anchor carrier gradient lives in the affine-span direction space of
the carrier.  This is the source-facing reason normal components cannot enter
the gradient norm used in Lemma 6.13. -/
theorem carrierGradientFrom_mem_affineSpan_direction
    {X : Set E} (v : {x : E // x ∈ X} → ℝ)
    (anchor x : {x : E // x ∈ X}) :
    SOptLib.carrierGradientFrom X v anchor x ∈ (affineSpan ℝ X).direction := by
  exact SOptLib.carrierGradientFrom_mem_direction (X := X) v anchor x

/-- The evaluation-anchored carrier gradient lies in the affine-span direction
space of the carrier. -/
theorem carrierGradient_mem_affineSpan_direction
    {X : Set E} (v : {x : E // x ∈ X} → ℝ) (x : {x : E // x ∈ X}) :
    SOptLib.carrierGradient X v x ∈ (affineSpan ℝ X).direction := by
  simpa [SOptLib.carrierGradient] using
    carrierGradientFrom_mem_affineSpan_direction (X := X) v x x

/-- The paper component gradient has no normal component relative to the
feasible carrier's affine span. -/
theorem gradf_mem_affineSpan_direction
    (i : ι) (x : {x : E // x ∈ setup.X}) :
    setup.gradf i x ∈ (affineSpan ℝ setup.X).direction := by
  simpa [RandomizedAcceleratedProximalPointSetup.gradf] using
    carrierGradient_mem_affineSpan_direction (X := setup.X) (setup.f i) x

/-- The explicit-center component gradient used in Lemma 6.13 remains in the
feasible carrier's affine-span direction when the proximal center is feasible. -/
theorem gradPsiOnAt_mem_affineSpan_direction
    (z : E) (hz : z ∈ setup.X) (i : ι) (x : {x : E // x ∈ setup.X}) :
    setup.gradPsiOnAt z i x ∈ (affineSpan ℝ setup.X).direction := by
  simpa [RandomizedAcceleratedProximalPointSetup.gradPsiOnAt] using
    SOptLib.carrier_regularizedGradient_mem_affineSpan_direction
      (X := setup.X) (setup.gradf i) setup.μ hz x
      (setup.gradf_mem_affineSpan_direction i x)

/-- Algebraic identity converting the two one-sided carrier Bregman errors into
the gradient monotonicity pairing. -/
theorem carrier_bregman_symm_sum_eq_inner_grad_sub
    {X : Set E} (v : {x : E // x ∈ X} → ℝ) (grad : {x : E // x ∈ X} → E)
    (x y : {x : E // x ∈ X}) :
    (v x - v y - ⟪grad y, x.1 - y.1⟫_ℝ) +
        (v y - v x - ⟪grad x, y.1 - x.1⟫_ℝ) =
      ⟪grad x - grad y, x.1 - y.1⟫_ℝ := by
  let d : E := x.1 - y.1
  have hyx : y.1 - x.1 = -d := by
    dsimp [d]
    abel
  calc
    (v x - v y - ⟪grad y, x.1 - y.1⟫_ℝ) +
        (v y - v x - ⟪grad x, y.1 - x.1⟫_ℝ)
        =
      (v x - v y - ⟪grad y, d⟫_ℝ) +
        (v y - v x + ⟪grad x, d⟫_ℝ) := by
        rw [show x.1 - y.1 = d by rfl, hyx, inner_neg_right]
        ring
    _ = ⟪grad x, d⟫_ℝ - ⟪grad y, d⟫_ℝ := by ring
    _ = ⟪grad x - grad y, x.1 - y.1⟫_ℝ := by
        simp [d, inner_sub_left]

/-- First-order convexity, expressed as nonnegative carrier Bregman errors,
implies monotonicity of the selected carrier gradient. -/
theorem carrier_gradient_monotone_of_bregman_nonneg
    {X : Set E} (v : {x : E // x ∈ X} → ℝ) (grad : {x : E // x ∈ X} → E)
    (hBreg_nonneg :
      ∀ x y : {x : E // x ∈ X},
        0 ≤ v x - v y - ⟪grad y, x.1 - y.1⟫_ℝ)
    (x y : {x : E // x ∈ X}) :
    0 ≤ ⟪grad x - grad y, x.1 - y.1⟫_ℝ := by
  exact carrierGradient_monotone_of_bregman_nonneg (v := v) (grad := grad)
    (fun a b => by
      simpa [SOptLib.carrierBregmanDivergence, carrierBregmanDivergence] using
        hBreg_nonneg b a)
    x y

/-- Single-sided gradient gap for a regularized component subproblem.

The repaired setup explicitly supplies a whole-space convex smooth extension.
Its gradient agrees with the intrinsic carrier gradient, and its quadratic
upper model uses the original constant Lhat = L + 2 * μ. The descent argument
is proved in SOptLib.ConvexSmoothExtensionOn.norm_gap; no unconditional carrier
Baillon-Haddad axiom is used by this theorem. -/
theorem psiBregmanAt_grad_norm_sq_le
    (z : E)
    (hz : z ∈ setup.X)
    (hcurv :
      ∀ i (x y : {x : E // x ∈ setup.X}),
        setup.μ / 2 * ‖x.1 - y.1‖ ^ 2 ≤
          setup.psiAtOn z i x - setup.psiAtOn z i y -
            ⟪setup.gradPsiOnAt z i y, x.1 - y.1⟫_ℝ ∧
        setup.psiAtOn z i x - setup.psiAtOn z i y -
            ⟪setup.gradPsiOnAt z i y, x.1 - y.1⟫_ℝ ≤
          setup.Lhat / 2 * ‖x.1 - y.1‖ ^ 2)
    (i : ι) (x y : {x : E // x ∈ setup.X}) :
    (1 / (2 * setup.Lhat)) *
        ‖setup.gradPsiOnAt z i x - setup.gradPsiOnAt z i y‖ ^ 2 ≤
      setup.psiBregmanAt z i x y := by
  obtain ⟨ext⟩ := setup.subproblem_extension z hz i
  have hL : 0 < setup.L + 2 * setup.μ := by
    have h := setup.L_pos
    nlinarith [setup.hμ_pos]
  simpa only [Lhat, psiBregmanAt, psiAtOn, gradPsiOnAt, gradf] using
    ext.norm_gap hL x y

theorem psiBregmanAt_grad_norm_sq_le_scalar_obstruction :
    ∃ μ L B G D : ℝ,
      0 < μ ∧ 0 < L ∧
        μ / 2 * D ^ 2 ≤ B ∧
        B ≤ L / 2 * D ^ 2 ∧
        G ≤ L * D ∧
        ¬ ((1 / (2 * L)) * G ^ 2 ≤ B) := by
  refine ⟨1, (3 / 2 : ℝ), (1 / 2 : ℝ), (7 / 5 : ℝ), 1, ?_⟩
  norm_num

/-- Guarded ambient correction of the gradient-memory update.

When the refreshed component point is in `X`, this is exactly the paper gradient
`∇ψᵢ`.  When it is not in `X`, the corrected ambient recursion keeps the previous
gradient memory instead of manufacturing a `gradPsiAt` fallback value.  This
keeps off-domain totalization out of theorem-facing arbitrary-memory routes.  It
is not the paper's literal Eq. (6.6.11); the literal source-domain line is
`sourceInnerStepAt`, which requires the missing component-memory domain witness. -/
noncomputable def gradPsiAtOrElse (z : E) (i : ι) (x fallback : E) : E :=
  by
    classical
    exact if hx : x ∈ setup.X then setup.gradPsiOnAt z i ⟨x, hx⟩ else fallback

/-- On feasible arguments the guarded Eq. (6.6.11) update is the source gradient. -/
theorem gradPsiAtOrElse_of_mem (z : E) (i : ι) {x fallback : E} (hx : x ∈ setup.X) :
    setup.gradPsiAtOrElse z i x fallback = setup.gradPsiOnAt z i ⟨x, hx⟩ := by
  simp [gradPsiAtOrElse, hx]

/-- Off the source domain, the corrected ambient Eq. (6.6.11) update preserves
the previous gradient memory and does not use `gradPsiAt`'s fallback branch. -/
theorem gradPsiAtOrElse_of_not_mem (z : E) (i : ι) {x fallback : E}
    (hx : x ∉ setup.X) :
    setup.gradPsiAtOrElse z i x fallback = fallback := by
  simp [gradPsiAtOrElse, hx]

/-- Explicit-center quadratic regulariser `φ_z(x) = (μ/2)‖x − z‖²`.

No SOptLib primitive was reused: `Bregman.div` and the prox-objective helpers are
paper-neutral over an abstract generator, while Eq. (6.6.8) fixes this literal
quadratic center. -/
noncomputable def phiAt (z : E) (x : E) : ℝ :=
  SOptLib.centeredQuadraticPotential setup.μ z x

/-- Explicit-center gradient of `φ_z`. -/
noncomputable def gradPhiAt (z : E) (x : E) : E :=
  setup.μ • (x - z)

/-- Quadratic Bregman divergence for the paper regularizer `φ_z`.

Aligns with Eq. (6.6.8): `φ^ℓ(x)=μ/2‖x-x̄^{ℓ-1}‖²`.  `SOptLib.Bregman.div`
and `SOptLib.paperMirrorObjective` were considered; those are paper-neutral
interfaces over an abstract divergence, while this file needs the literal
quadratic `φ` expansion used in Lan's Eq. (6.6.13). -/
noncomputable def quadraticBregmanAt (z : E) (x y : E) : ℝ :=
  SOptLib.centeredQuadraticBregman setup.μ z x y

/-- Expanded formula for the quadratic Bregman divergence generated by `φ^ℓ`. -/
theorem quadraticBregmanAt_eq (z x y : E) :
    setup.quadraticBregmanAt z x y =
      (setup.μ / 2) * ‖x - z‖ ^ 2 -
        (setup.μ / 2) * ‖y - z‖ ^ 2 -
        ⟪setup.μ • (y - z), x - y⟫_ℝ := by
  rfl

/-- Feasible-point nonnegativity of the Eq. (6.6.13) Bregman term.

Aligns with Eq. (6.6.8): the already proved curvature statement for the
quadratic `φ` supplies the half-squared-distance lower bound.  The compact-prox
candidate `SOptLib.proxObjective_exists_isMinOn_compact` was considered and
rejected here because this helper is only the local nonnegativity bridge needed
for the noncompact coercivity route, while that candidate assumes compactness of
the whole prox domain and a different abstract objective shape. -/
theorem quadraticBregmanAt_nonneg_of_mem
    (z x y : E) (_hz : z ∈ setup.X) (_hx : x ∈ setup.X) (_hy : y ∈ setup.X) :
    0 ≤ setup.quadraticBregmanAt z x y := by
  have hquad :
      setup.quadraticBregmanAt z x y = (setup.μ / 2) * ‖x - y‖ ^ 2 := by
    rw [setup.quadraticBregmanAt_eq z x y]
    rw [norm_sub_sq_real x z, norm_sub_sq_real y z, norm_sub_sq_real x y]
    simp [inner_sub_left, inner_sub_right, inner_smul_left, real_inner_comm]
    ring_nf
  rw [hquad]
  have hmu_half_nonneg : 0 ≤ setup.μ / 2 := le_of_lt (div_pos setup.hμ_pos two_pos)
  exact mul_nonneg hmu_half_nonneg (sq_nonneg _)

/-- In-range nonnegativity of the scaled Eq. (6.6.13) Bregman term.

Aligns with Algorithm 6.9's input boundary `η_t ≥ 0` for `t = 1, ..., s`;
`SOptLib.proxObjective_exists_isMinOn_compact` and
`SOptLib.objectiveMinimum_exists_of_isCompact_continuousOn` were checked, but
neither packages this source-range scalar sign fact, so the helper specializes
the local setup hypotheses directly. -/
theorem eta_mul_quadraticBregmanAt_nonneg_of_mem
    (z : E) (t : ℕ) (xPrev x : E)
    (hz : z ∈ setup.X) (ht : 1 ≤ t) (hts : t ≤ setup.s)
    (hxPrev : xPrev ∈ setup.X) (hx : x ∈ setup.X) :
    0 ≤ setup.ηSeq t * setup.quadraticBregmanAt z x xPrev := by
  exact mul_nonneg (setup.hηSeq_nonneg t ht hts)
    (setup.quadraticBregmanAt_nonneg_of_mem z x xPrev hz hx hxPrev)

/-- Positive quadratic functions eventually dominate any affine lower target.

Delegates to the staged Glue lemma for the noncompact coercivity tail used in
the prox-existence truncation argument. -/
theorem eventually_le_pos_quadratic_minus_linear
    {a : ℝ} (ha : 0 < a) (b c B : ℝ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ r : ℝ, R ≤ r → B ≤ a * r ^ 2 - b * r + c := by
  exact exists_nonneg_forall_le_quadratic_sub_linear_of_pos ha b c B

/-- Carrier smooth upper model from within-gradients and a Lipschitz carrier
gradient.

Aligns with Lan Eq. (6.6.8), upper `ψᵢ` branch: this is the missing
component-`fᵢ` descent step before adding the quadratic shift.  Considered
`Convex.carrier_smooth_quadratic_upper_bound` and
`smooth_quadratic_upper_bound_of_hasGradientAt_lipschitzOn_convex`; the former
requires `ContDiffOn`, while the latter requires global `HasGradientAt`, so this
variant keeps the source-available `HasGradientWithinAt` hypothesis on `X` and
reuses `le_value_add_of_hasDerivWithinAt_le_affine_on_Icc`. -/
theorem carrier_smooth_upper_bound_of_hasGradientWithinAt_lipschitz
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
  exact
    Convex.carrier_smooth_quadratic_upper_bound_of_hasGradientWithinAt_lipschitz
      (f := f) (F := F) (grad := grad) (L := L)
      hX hF_eval hgrad hgrad_lipschitz x y

/-- Voucher step for the standard descent-point proof of the Baillon-Haddad
lower bound.

If the comparison point `x - L⁻¹(grad x - grad y)` is feasible, convexity at
`y` and the smooth upper model at `x` imply the desired Bregman/gradient lower
bound by pure Hilbert algebra.  The general closed-convex-carrier proof must
replace this feasibility premise with the appropriate projected or relative-
interior argument; this lemma isolates the exact missing constrained step. -/
theorem _voucher_step_carrier_segment_baillon_haddad_lower_descent_point
    {X : Set E} (v : {x : E // x ∈ X} → ℝ)
    (grad : {x : E // x ∈ X} → E) (L : ℝ)
    (hL_pos : 0 < L)
    (hBreg_nonneg :
      ∀ x y : {x : E // x ∈ X},
        0 ≤ v x - v y - ⟪grad y, x.1 - y.1⟫_ℝ)
    (hBreg_upper :
      ∀ x y : {x : E // x ∈ X},
        v x - v y - ⟪grad y, x.1 - y.1⟫_ℝ ≤
          L / 2 * ‖x.1 - y.1‖ ^ 2)
    (x y u : {x : E // x ∈ X})
    (hu : u.1 = x.1 - (1 / L) • (grad x - grad y)) :
    (1 / (2 * L)) * ‖grad x - grad y‖ ^ 2 ≤
      v x - v y - ⟪grad y, x.1 - y.1⟫_ℝ := by
  classical
  let g : E := grad x - grad y
  have hL_ne : L ≠ 0 := ne_of_gt hL_pos
  have hux : u.1 - x.1 = -(1 / L) • g := by
    have hcalc : x.1 - (1 / L) • g - x.1 = -((1 / L) • g) := by
      abel
    rw [hu]
    simpa [g, neg_smul] using hcalc
  have huy :
      u.1 - y.1 = (x.1 - y.1) + (u.1 - x.1) := by
    abel
  have hnorm_ux : ‖u.1 - x.1‖ ^ 2 = (1 / L) ^ 2 * ‖g‖ ^ 2 := by
    rw [hux, norm_smul, norm_neg, Real.norm_of_nonneg (by positivity : 0 ≤ (1 / L))]
    ring
  have hconv_y :
      v y ≤ v u - ⟪grad y, u.1 - y.1⟫_ℝ := by
    have h := hBreg_nonneg u y
    linarith
  have hsmooth_u :
      v u - v x - ⟪grad x, u.1 - x.1⟫_ℝ ≤
        L / 2 * ‖u.1 - x.1‖ ^ 2 := by
    exact hBreg_upper u x
  have hB_lower :
      v x - v y - ⟪grad y, x.1 - y.1⟫_ℝ ≥
        -⟪g, u.1 - x.1⟫_ℝ - L / 2 * ‖u.1 - x.1‖ ^ 2 := by
    have hstep :
        v x - v y - ⟪grad y, x.1 - y.1⟫_ℝ ≥
          v x - v u + ⟪grad y, u.1 - x.1⟫_ℝ := by
      calc
        v x - v y - ⟪grad y, x.1 - y.1⟫_ℝ
            ≥ v x - (v u - ⟪grad y, u.1 - y.1⟫_ℝ) -
                ⟪grad y, x.1 - y.1⟫_ℝ := by
              linarith
        _ = v x - v u + ⟪grad y, u.1 - x.1⟫_ℝ := by
              rw [huy]
              rw [inner_add_right]
              ring
    have hsmooth_rearr :
        v x - v u ≥
          -⟪grad x, u.1 - x.1⟫_ℝ - L / 2 * ‖u.1 - x.1‖ ^ 2 := by
      linarith
    have hcombine :
        v x - v u + ⟪grad y, u.1 - x.1⟫_ℝ ≥
          -⟪g, u.1 - x.1⟫_ℝ - L / 2 * ‖u.1 - x.1‖ ^ 2 := by
      dsimp [g]
      rw [inner_sub_left]
      linarith
    exact le_trans hcombine hstep
  have hcore :
      -⟪g, u.1 - x.1⟫_ℝ - L / 2 * ‖u.1 - x.1‖ ^ 2 =
        (1 / (2 * L)) * ‖g‖ ^ 2 := by
    rw [hux, inner_smul_right, real_inner_self_eq_norm_sq, norm_smul, norm_neg,
      Real.norm_of_nonneg (by positivity : 0 ≤ (1 / L))]
    field_simp [hL_ne]
    ring
  rw [hcore] at hB_lower
  simpa [g] using hB_lower

/-- Iteration-11 exact-head voucher attempt for the source-faithful segment
Baillon-Haddad leaf.

The proof state intentionally keeps the real source objects, not scalar endpoint
surrogates: the ambient realization `F`, the feasible segment, its within
derivative, endpoint evaluation, Bregman nonnegativity, the smooth upper model
obtained by integrating the derivative bound with
`le_value_add_of_hasDerivWithinAt_le_affine_on_Icc`, and the carrier-gradient
Lipschitz control.  The final `proof-placeholder` is only the remaining analytic
Baillon-Haddad lower-bound step for this exact strengthened head. -/
theorem SubproblemCurvature_6_6_8 (z : E) (hz : z ∈ setup.X) :
    (∀ i (x y : {x : E // x ∈ setup.X}),
      setup.μ / 2 * ‖x.1 - y.1‖ ^ 2 ≤
        setup.psiAtOn z i x - setup.psiAtOn z i y -
          ⟪setup.gradPsiOnAt z i y, x.1 - y.1⟫_ℝ ∧
      setup.psiAtOn z i x - setup.psiAtOn z i y -
          ⟪setup.gradPsiOnAt z i y, x.1 - y.1⟫_ℝ ≤
        setup.Lhat / 2 * ‖x.1 - y.1‖ ^ 2) ∧
    (∀ x y, x ∈ setup.X → y ∈ setup.X →
      setup.μ / 2 * ‖x - y‖ ^ 2 ≤
        setup.phiAt z x - setup.phiAt z y -
          ⟪setup.gradPhiAt z y, x - y⟫_ℝ) := by
  constructor
  · intro i x y
    constructor
    · have hone := setup.hone_sided i x y
      have hone_gradf :
          setup.f i x - setup.f i y -
              ⟪setup.gradf i y, x.1 - y.1⟫_ℝ ≥
            -(setup.μ / 2) * ‖x.1 - y.1‖ ^ 2 := by
        simpa [RandomizedAcceleratedProximalPointSetup.gradf] using hone
      have hquad :
          setup.μ * ‖x.1 - z‖ ^ 2 - setup.μ * ‖y.1 - z‖ ^ 2 -
              ⟪(2 * setup.μ) • (y.1 - z), x.1 - y.1⟫_ℝ =
            setup.μ * ‖x.1 - y.1‖ ^ 2 := by
        rw [norm_sub_sq_real x.1 z, norm_sub_sq_real y.1 z,
          norm_sub_sq_real x.1 y.1]
        simp [inner_sub_left, inner_sub_right, inner_smul_left, real_inner_comm]
        ring_nf
      have hsplit :
          setup.psiAtOn z i x - setup.psiAtOn z i y -
              ⟪setup.gradPsiOnAt z i y, x.1 - y.1⟫_ℝ =
            (setup.f i x - setup.f i y -
                ⟪setup.gradf i y, x.1 - y.1⟫_ℝ) +
              (setup.μ * ‖x.1 - z‖ ^ 2 - setup.μ * ‖y.1 - z‖ ^ 2 -
                ⟪(2 * setup.μ) • (y.1 - z), x.1 - y.1⟫_ℝ) := by
        unfold RandomizedAcceleratedProximalPointSetup.psiAtOn
          RandomizedAcceleratedProximalPointSetup.gradPsiOnAt
          SOptLib.quadraticRegularizedObjectiveOn
          SOptLib.quadraticRegularizedGradientOn
        rw [inner_add_left]
        ring_nf
      rw [hsplit, hquad]
      nlinarith
    · have hf :
          setup.f i x - setup.f i y -
              ⟪setup.gradf i y, x.1 - y.1⟫_ℝ ≤
            setup.L / 2 * ‖x.1 - y.1‖ ^ 2 := by
        exact
          carrier_smooth_upper_bound_of_hasGradientWithinAt_lipschitz
            (X := setup.X) (setup.f i) (setup.fAmbient i) (setup.gradf i)
            setup.L setup.hX_convex
            (fun w hw => setup.fAmbient_of_mem i hw)
            (setup.gradf_hasGradientWithinAt i)
            (fun u v => setup.hsmooth i v u) x y
      have hquad :
          setup.μ * ‖x.1 - z‖ ^ 2 - setup.μ * ‖y.1 - z‖ ^ 2 -
              ⟪(2 * setup.μ) • (y.1 - z), x.1 - y.1⟫_ℝ =
            setup.μ * ‖x.1 - y.1‖ ^ 2 := by
        rw [norm_sub_sq_real x.1 z, norm_sub_sq_real y.1 z,
          norm_sub_sq_real x.1 y.1]
        simp [inner_sub_left, inner_sub_right, inner_smul_left, real_inner_comm]
        ring_nf
      unfold RandomizedAcceleratedProximalPointSetup.psiAtOn
        RandomizedAcceleratedProximalPointSetup.gradPsiOnAt
        SOptLib.quadraticRegularizedGradientOn
      rw [inner_add_left]
      calc
        setup.f i x + setup.μ * ‖x.1 - z‖ ^ 2 -
              (setup.f i y + setup.μ * ‖y.1 - z‖ ^ 2) -
              (⟪setup.gradf i y, x.1 - y.1⟫_ℝ +
                ⟪(2 * setup.μ) • (y.1 - z), x.1 - y.1⟫_ℝ)
            ≤ setup.L / 2 * ‖x.1 - y.1‖ ^ 2 +
                setup.μ * ‖x.1 - y.1‖ ^ 2 := by
              nlinarith
        _ = setup.Lhat / 2 * ‖x.1 - y.1‖ ^ 2 := by
              rw [setup.Lhat_def]
              ring
  · intro x y hx hy
    unfold RandomizedAcceleratedProximalPointSetup.phiAt
      RandomizedAcceleratedProximalPointSetup.gradPhiAt
      SOptLib.centeredQuadraticPotential
    rw [norm_sub_sq_real x z, norm_sub_sq_real y z, norm_sub_sq_real x y]
    simp [inner_sub_left, inner_sub_right, inner_smul_left, real_inner_comm]
    ring_nf
    rfl

/-- Source-domain objective minimized by the RaGrad prox step in Eq. (6.6.13).

Aligns with Algorithm 6.9 / Eq. (6.6.13).  `SOptLib.proxObjective` and
`SOptLib.proxStep` were checked: they cover a zero/simple-term inverse-stepsize
mirror prox form over `Set.univ`, but Eq. (6.6.13) includes the additional
`φ^ℓ(x)` term and minimizes over the paper feasible set `X`, so the local
objective records the literal paper expression on the subtype domain. -/
noncomputable def proxObjectiveAtOn (z : E) (t : ℕ) (xPrev g : E)
    (x : {x : E // x ∈ setup.X}) : ℝ :=
  setup.phiAt z x.1 + ⟪g, x.1⟫_ℝ +
    setup.ηSeq t * setup.quadraticBregmanAt z x.1 xPrev

/-- Internal ambient compatibility wrapper for the Eq. (6.6.13) prox objective.

The source-facing object is `proxObjectiveAtOn`, whose argument carries `x ∈ X`.
This wrapper exists only for legacy `IsMinOn` bridge statements over ambient
sets. -/
noncomputable def proxObjectiveAt (z : E) (t : ℕ) (xPrev g x : E) : ℝ :=
  setup.phiAt z x + ⟪g, x⟫_ℝ +
    setup.ηSeq t * setup.quadraticBregmanAt z x xPrev

/-- Feasible-point rewrite for the ambient prox-objective wrapper. -/
@[simp]
theorem proxObjectiveAt_of_mem (z : E) (t : ℕ) (xPrev g : E) {x : E}
    (hx : x ∈ setup.X) :
    setup.proxObjectiveAt z t xPrev g x =
      setup.proxObjectiveAtOn z t xPrev g ⟨x, hx⟩ := by
  rfl

/-- Coercive lower-tail bound for the Eq. (6.6.13) ambient compatibility objective.

Aligns with the bounded-truncation proof of the source `argmin`: the positive
quadratic `φ_z`, Cauchy-Schwarz for the linear term, and in-range
`η_t V_φ ≥ 0` give an outside-ball lower bound.  Compact-domain candidates
`SOptLib.objectiveMinimum_exists_of_isCompact_continuousOn` and
`SOptLib.proxObjective_exists_isMinOn_compact` were checked; they handle the
subsequent compact truncation step, not this noncompact tail comparison. -/
theorem proxObjectiveAt_coercive_lower_bound
    (z : E) (t : ℕ) (xPrev g : E)
    (hz : z ∈ setup.X) (ht : 1 ≤ t) (hts : t ≤ setup.s)
    (hxPrev : xPrev ∈ setup.X) :
    ∀ B : ℝ, ∃ R : ℝ, ‖setup.x₀ - z‖ ≤ R ∧
      ∀ x : E, x ∈ setup.X → R ≤ ‖x - z‖ →
        B ≤ setup.proxObjectiveAt z t xPrev g x := by
  refine
    coercive_lower_bound_of_pos_quadratic_add_linear_add_nonneg
      (X := setup.X) (x0 := setup.x₀) (z := z) (g := g)
      (a := setup.μ / 2)
      (Rterm := fun x => setup.ηSeq t * setup.quadraticBregmanAt z x xPrev)
      (F := setup.proxObjectiveAt z t xPrev g)
      (ha := div_pos setup.hμ_pos two_pos) ?_ ?_
  · intro x hx
    simp [RandomizedAcceleratedProximalPointSetup.proxObjectiveAt,
      RandomizedAcceleratedProximalPointSetup.phiAt,
      SOptLib.centeredQuadraticPotential]
  · intro x hx
    exact setup.eta_mul_quadraticBregmanAt_nonneg_of_mem z t xPrev x hz ht hts hxPrev hx

/-- Continuous coercive objectives on a closed nonempty feasible set attain a minimum.

Aligns with the compact truncation step implicit in Eq. (6.6.13): minimize on
`X ∩ closedBall z R` and use the outside-ball lower bound to extend the
minimizer to all of `X`.  This helper deliberately uses
`SOptLib.objectiveMinimum_exists_of_isCompact_continuousOn`; the compact prox
candidate `SOptLib.proxObjective_exists_isMinOn_compact` was considered but
does not match because the paper objective has an additional `φ` term and the
domain is a closed noncompact feasible set before truncation. -/
theorem exists_isMinOn_closed_of_coercive_on_closedBall
    {X : Set E} (hX_closed : IsClosed X) (x0 z : E) (hx0 : x0 ∈ X)
    (F : E → ℝ) (hcont : ContinuousOn F X)
    (hcoerc : ∀ B : ℝ, ∃ R : ℝ, ‖x0 - z‖ ≤ R ∧
      ∀ x : E, x ∈ X → R ≤ ‖x - z‖ → B ≤ F x) :
    ∃ x : E, x ∈ X ∧ IsMinOn F X x := by
  haveI : ProperSpace E := FiniteDimensional.proper ℝ E
  refine exists_isMinOn_of_closed_coercive_closedBall hX_closed x0 z hx0 F hcont ?_
  obtain ⟨R, hx0_le_R, htail⟩ := hcoerc (F x0)
  refine ⟨R, ?_, ?_⟩
  · simpa [dist_eq_norm] using hx0_le_R
  · intro x hx hR_le_dist
    exact htail x hx (by simpa [dist_eq_norm] using hR_le_dist)

/-- Step-0 falsity artifact for the retired unrestricted `proxStepAtCore_exists`
shape.

The deleted private theorem asserted an ambient minimizer for every time index and
every value of `η_t`.  In the one-dimensional off-range model with `X = Set.univ`
and a negative quadratic objective, the old conclusion would specialize to the
impossible claim below.  This theorem is intentionally independent of the setup:
it records why the arbitrary-time minimizer scaffold must not be recreated. -/
theorem no_isMinOn_neg_sq_univ :
    ¬ ∃ x : ℝ, IsMinOn (fun y : ℝ => - y ^ 2) Set.univ x := by
  rintro ⟨x, hmin⟩
  let y : ℝ := |x| + 1
  have hle : -x ^ 2 ≤ -y ^ 2 := hmin (show y ∈ Set.univ by simp)
  have hy_nonneg : 0 ≤ y := by
    dsimp [y]
    positivity
  have h_abs_lt_y : |x| < y := by
    dsimp [y]
    linarith
  have hsq_lt : x ^ 2 < y ^ 2 := by
    rw [show x ^ 2 = |x| ^ 2 by exact (sq_abs x).symm]
    exact sq_lt_sq.mpr (by simpa [abs_of_nonneg hy_nonneg] using h_abs_lt_y)
  nlinarith

/-- Selection obligation for the Eq. (6.6.13) prox subproblem on the paper domain.

The book JSON and PDF state the update as an `argmin` over `X` in Algorithm 6.9
for `t = 1, ..., s`.  Compactness/coercivity/selector regularity are not listed
as primitive theorem assumptions, so solvability is a derived proof obligation
restricted to the source boundary rather than a setup field or all-time axiom. -/
theorem proxStepAt_exists (z : E) (t : ℕ)
    (_hz : z ∈ setup.X) (_ht : 1 ≤ t) (_hts : t ≤ setup.s)
    (xPrev : E) (_hxPrev : xPrev ∈ setup.X) (g : E) :
    ∃ x : {x : E // x ∈ setup.X},
      IsMinOn (setup.proxObjectiveAtOn z t xPrev g) Set.univ x := by
  classical
  let F : E → ℝ := setup.proxObjectiveAt z t xPrev g
  have hcont : ContinuousOn F setup.X := by
    have hphi : Continuous (fun x : E => setup.phiAt z x) := by
      unfold RandomizedAcceleratedProximalPointSetup.phiAt
      exact continuous_const.mul (((continuous_id.sub continuous_const).norm).pow 2)
    have hinner : Continuous (fun x : E => ⟪g, x⟫_ℝ) := by
      exact continuous_const.inner continuous_id
    have hbreg : Continuous (fun x : E => setup.quadraticBregmanAt z x xPrev) := by
      unfold RandomizedAcceleratedProximalPointSetup.quadraticBregmanAt
        SOptLib.centeredQuadraticBregman
        SOptLib.centeredQuadraticPotential
      exact ((continuous_const.mul (((continuous_id.sub continuous_const).norm).pow 2)).sub
        (continuous_const.mul (((continuous_const.sub continuous_const).norm).pow 2))).sub
        (continuous_const.inner (continuous_id.sub continuous_const))
    have hFcont : Continuous F := by
      dsimp [F]
      unfold RandomizedAcceleratedProximalPointSetup.proxObjectiveAt
      exact (hphi.add hinner).add (continuous_const.mul hbreg)
    exact hFcont.continuousOn
  have hcoerc : ∀ B : ℝ, ∃ R : ℝ, ‖setup.x₀ - z‖ ≤ R ∧
      ∀ x : E, x ∈ setup.X → R ≤ ‖x - z‖ → B ≤ F x := by
    simpa [F] using
      setup.proxObjectiveAt_coercive_lower_bound z t xPrev g _hz _ht _hts _hxPrev
  obtain ⟨xmin, hxmin, hmin⟩ :=
    exists_isMinOn_closed_of_coercive_on_closedBall
      setup.hX_closed setup.x₀ z setup.hx₀_mem F hcont hcoerc
  refine ⟨⟨xmin, hxmin⟩, ?_⟩
  intro y _
  have hy : F xmin ≤ F y.1 := hmin y.2
  simpa [F, RandomizedAcceleratedProximalPointSetup.proxObjectiveAt_of_mem] using hy

/-- Canonical subtype-valued RaGrad prox step selected from the Eq. (6.6.13)
source-domain argmin.

`SOptLib.proxStep` was considered and rejected for this paper-facing object because
its abstract mirror objective does not include the extra `φ^ℓ` term of Eq. (6.6.13)
nor the minimization over `X`; this definition selects from the paper's literal
prox objective only under the source facts `z ∈ X`, `x^{t-1} ∈ X`, and
`t = 1, ..., s`.  There is deliberately no public fallback branch outside
Algorithm 6.9's domain. -/
noncomputable def proxStepAtOn (z : E) (t : ℕ)
    (hz : z ∈ setup.X) (ht : 1 ≤ t) (hts : t ≤ setup.s)
    (xPrev : E) (hxPrev : xPrev ∈ setup.X) (g : E) : {x : E // x ∈ setup.X} :=
  Classical.choose (setup.proxStepAt_exists z t hz ht hts xPrev hxPrev g)

/-- Ambient point projection of the source-domain Eq. (6.6.13) prox step. -/
noncomputable def proxStepAt (z : E) (t : ℕ)
    (hz : z ∈ setup.X) (ht : 1 ≤ t) (hts : t ≤ setup.s)
    (xPrev : E) (hxPrev : xPrev ∈ setup.X) (g : E) : E :=
  (setup.proxStepAtOn z t hz ht hts xPrev hxPrev g).1

/-- The selected prox step stays in the feasible set `X`. -/
theorem proxStepAt_mem (z : E) (t : ℕ)
    (hz : z ∈ setup.X) (ht : 1 ≤ t) (hts : t ≤ setup.s)
    (xPrev : E) (hxPrev : xPrev ∈ setup.X) (g : E) :
    setup.proxStepAt z t hz ht hts xPrev hxPrev g ∈ setup.X :=
by
  exact (setup.proxStepAtOn z t hz ht hts xPrev hxPrev g).2

/-- The selected source-domain prox step realizes the Eq. (6.6.13) subtype argmin. -/
theorem proxStepAtOn_is_argmin (z : E) (t : ℕ)
    (hz : z ∈ setup.X) (ht : 1 ≤ t) (hts : t ≤ setup.s)
    (xPrev : E) (hxPrev : xPrev ∈ setup.X) (g : E) :
    IsMinOn (setup.proxObjectiveAtOn z t xPrev g) Set.univ
      (setup.proxStepAtOn z t hz ht hts xPrev hxPrev g) :=
by
  classical
  exact Classical.choose_spec (setup.proxStepAt_exists z t hz ht hts xPrev hxPrev g)

/-- Ambient bridge for the selected prox step's Eq. (6.6.13) argmin property. -/
theorem proxStepAt_is_argmin (z : E) (t : ℕ)
    (hz : z ∈ setup.X) (ht : 1 ≤ t) (hts : t ≤ setup.s)
    (xPrev : E) (hxPrev : xPrev ∈ setup.X) (g : E) :
    IsMinOn (setup.proxObjectiveAt z t xPrev g) setup.X
      (setup.proxStepAt z t hz ht hts xPrev hxPrev g) :=
by
  classical
  intro y hy
  have hmin := setup.proxStepAtOn_is_argmin z t hz ht hts xPrev hxPrev g
  have hle := hmin (a := ⟨y, hy⟩) (by simp)
  simpa [proxStepAt, proxObjectiveAt_of_mem] using hle

/-- Internal extrapolated point from Eq. (6.6.9) computed from a pre-step state.

This raw helper is private because Algorithm 6.9 exposes `x̃ᵗ` only on the
source range `t = 1, ..., s`; public generated-process access uses the bounded
`xTildeAt` wrapper below.  Source:
`book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec/steps/4`,
Eq. (6.6.9), states `\tilde{x}^t = α_t(x^{t-1}-x^{t-2})+x^{t-1}`. -/
noncomputable def xTildeAtState (t : ℕ) (st : RaGradState ι E) : E :=
  setup.αSeq t • (st.x - st.xPrev) + st.x

/-- Eq. (6.6.33) extrapolation algebra for the raw state-level `x̃ᵗ`.

SOptLib candidates `accelerated_step_from_state_x` and
`average_sub_search_eq_alpha_smul_step_sub_weighted_center` were considered;
they describe different accelerated-state/weighted-center transports, while
Lan Eq. (6.6.33) needs this literal `xTildeAtState` field identity. -/
theorem xTildeAtState_sub_next_eq_step_sub_alpha_prev
    (t : ℕ) (stPrev stNext : RaGradState ι E) :
    setup.xTildeAtState t stPrev - stNext.x =
      (stPrev.x - stNext.x) - setup.αSeq t • (stPrev.xPrev - stPrev.x) := by
  simp [xTildeAtState]
  module

/-- Component memory value produced by Eq. (6.6.10) for a fixed sampled component.

No SOptLib match: searched `recursive iterate process finite bounded update state`
and scanned `SOptLib/Model/Iterates.lean`; the reusable process helpers provide
abstract recursion and measurability bridges, while Eq. (6.6.10) is this literal
sample-conditioned affine refresh.  Source:
`book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec/steps/5`,
Eq. (6.6.10), gives the sampled component update. -/
noncomputable def xMemAfterSampleAtState (t : ℕ) (_ht : 1 ≤ t) (_hts : t ≤ setup.s)
    (sample i : ι)
    (st : RaGradState ι E) : E :=
  SOptLib.sampledAffineMemoryRefresh (setup.τSeq t)
    (setup.xTildeAtState t st) st.xMem sample i

/-- Defining equation for the affine component refresh in Eq. (6.6.10).

This theorem deliberately does **not** assert membership in `X`: the book/PDF
prints the affine formula but does not state a closure condition ensuring that
the refreshed point is in the domain of `f_i : X → ℝ`. -/
theorem xMemAfterSampleAtState_eq
    (t : ℕ) (ht : 1 ≤ t) (hts : t ≤ setup.s)
    (sample i : ι) (st : RaGradState ι E) :
    setup.xMemAfterSampleAtState t ht hts sample i st =
      if i = sample then
        ((1 : ℝ) + setup.τSeq t)⁻¹ •
          (setup.xTildeAtState t st + setup.τSeq t • st.xMem i)
      else st.xMem i := by
  simpa [xMemAfterSampleAtState] using
    (SOptLib.sampledAffineMemoryRefresh_def (setup.τSeq t)
      (setup.xTildeAtState t st) st.xMem sample i)

/-- Sampled affine rearrangement of Algorithm 6.9 Eq. (6.6.10).

SOptLib candidates `average_sub_search_eq_alpha_smul_step_sub_weighted_center`
and `inv_card_smul_sum_sub_const_eq`, plus target-file helpers
`xMemAfterSampleAtState_eq` and `sourceInnerStepAt_xMem_eq_xMemAfterSampleAtState`,
were considered.  The SOptLib lemmas concern different averaged/search-point
transports; the target definition equation is usable but does not package the
literal sampled rearrangement `τᵗ(xᵢᵗ⁻¹ - x̂ᵢᵗ) = x̂ᵢᵗ - x̃ᵗ` needed by Lan
Eq. (6.6.29). -/
theorem xMemAfterSampleAtState_self_affine_relation
    (t : ℕ) (ht : 1 ≤ t) (hts : t ≤ setup.s)
    (sample : ι) (st : RaGradState ι E)
    (hτ : 0 < setup.τSeq t) :
    setup.τSeq t •
        (st.xMem sample -
          setup.xMemAfterSampleAtState t ht hts sample sample st) =
      setup.xMemAfterSampleAtState t ht hts sample sample st -
        setup.xTildeAtState t st := by
  exact SOptLib.smul_sub_eq_sub_of_eq_inv_one_add_smul_add (by linarith) (by
    simp [xMemAfterSampleAtState_eq])

/-- Formal obstruction to deriving component-memory feasibility from the current
source assumptions alone.

The sampled refresh in Eq. (6.6.10) is an affine extrapolation.  Even for a closed
convex feasible interval and nonnegative parameters, feasible `xᵗ⁻¹`, `xᵗ⁻²`,
and `xᵢᵗ⁻¹` do not force the refreshed component memory to remain feasible.
This is why outer component-memory feasibility cannot be manufactured from
`hX_closed`, `hX_convex`, and the Algorithm 6.9 nonnegativity inputs. -/
theorem affine_component_refresh_not_closed_under_closed_convex_set :
    ∃ (X : Set ℝ) (α τ x xPrev xMem : ℝ),
      IsClosed X ∧ Convex ℝ X ∧
        0 ≤ α ∧ 0 ≤ τ ∧ x ∈ X ∧ xPrev ∈ X ∧ xMem ∈ X ∧
          ((1 + τ)⁻¹ * ((α * (x - xPrev) + x) + τ * xMem)) ∉ X := by
  refine ⟨Set.Icc (0 : ℝ) 1, 1, 0, 1, 0, 1, ?_⟩
  constructor
  · exact isClosed_Icc
  constructor
  · exact convex_Icc 0 1
  norm_num

/-- Corrected ambient realization of one Algorithm 6.9 inner update.

No SOptLib match: searched `iterate state recursive process block update feasible`,
checked `SOptLib.BlockIterateState`, and scanned `SOptLib/Model/Iterates.lean`;
those provide abstract process views and block-state containers, while Algorithm
6.9 requires the literal extrapolation, component refresh, gradient-memory update,
gradient estimator, and constrained prox equations.  This declaration is the
ambient-corrected total recursion used by the generated process, not the literal
paper source object: because the source does not prove the affine refreshed
component points remain in `X`, the gradient-memory line is guarded.  The literal
source-domain step is `sourceInnerStepAt`, and
`ambientInnerStepAt_eq_sourceInnerStepAt_of_mem` is the only bridge from this
corrected totalization back to Eq. (6.6.11). -/
noncomputable def ambientInnerStepAt
    (offset : ℕ) (z : E) (t : ℕ)
    (hz : z ∈ setup.X) (ht : 1 ≤ t) (hts : t ≤ setup.s)
    (ω : Ω) (st : RaGradState ι E)
    (hx : st.x ∈ setup.X) :
    RaGradState ι E :=
  let it := setup.ξ (offset + (t - 1)) ω
  let xMemNew : ι → E :=
    fun i => setup.xMemAfterSampleAtState t ht hts it i st
  let yMemNew : ι → E :=
    fun i =>
      if i = it then
        setup.gradPsiAtOrElse z i (xMemNew i) (st.yMem i)
      else st.yMem i
  let avgY : E :=
    (Fintype.card ι : ℝ)⁻¹ •
      Finset.sum Finset.univ
        (fun i =>
          (Fintype.card ι : ℝ) • (yMemNew i - st.yMem i) + st.yMem i)
  { x := setup.proxStepAt z t hz ht hts st.x hx avgY
    xPrev := st.x
    xMem := xMemNew
    yMem := yMemNew }

/-- Literal source-domain Algorithm 6.9 inner update.

This is the paper formula for Eqs. (6.6.9)-(6.6.13): the sampled gradient-memory
line uses `∇ψᵢ(xᵢᵗ)` with an explicit proof that every refreshed component
memory lies in the source domain `X`.  It is separated from
`ambientInnerStepAt` because the PDF states `f_i : X → ℝ` and does not prove
that the affine refresh in Eq. (6.6.10) preserves `X`.

No SOptLib match: searched `recursive process sample update state`, checked
`SOptLib.recursiveProcess_succ_eq_sample_update`, and reused the existing local
Eq. (6.6.10) primitive `xMemAfterSampleAtState`; SOptLib provides generic
recursive-process transport, not this paper's domain-indexed gradient-memory
line. -/
noncomputable def sourceInnerStepAt
    (offset : ℕ) (z : E) (t : ℕ)
    (hz : z ∈ setup.X) (ht : 1 ≤ t) (hts : t ≤ setup.s)
    (ω : Ω) (st : RaGradState ι E)
    (hx : st.x ∈ setup.X)
    (hxMemNew :
      ∀ i : ι,
        setup.xMemAfterSampleAtState t ht hts
          (setup.ξ (offset + (t - 1)) ω) i st ∈ setup.X) :
    RaGradState ι E :=
  let it := setup.ξ (offset + (t - 1)) ω
  let xMemNew : ι → E :=
    fun i => setup.xMemAfterSampleAtState t ht hts it i st
  let yMemNew : ι → E :=
    fun i =>
      if _ : i = it then
        setup.gradPsiOnAt z i ⟨xMemNew i, hxMemNew i⟩
      else st.yMem i
  let avgY : E :=
    (Fintype.card ι : ℝ)⁻¹ •
      Finset.sum Finset.univ
        (fun i =>
          (Fintype.card ι : ℝ) • (yMemNew i - st.yMem i) + st.yMem i)
  { x := setup.proxStepAt z t hz ht hts st.x hx avgY
    xPrev := st.x
    xMem := xMemNew
    yMem := yMemNew }

/-- `x`-field projection for the literal source-domain step, aligned with
Lan Eq. (6.6.13) and used in the Eq. (6.6.31) route.

Considered SOptLib candidates `finset_weighted_residual_sum_eq_zero`,
`finset_weighted_variance_eq_second_moment_sub_norm_mean_sq`,
`weighted_sq_norm_sub_center_le`,
`coefficients_for_average_minus_search_eq_alpha_step_minus_center`, and
`average_sub_search_eq_alpha_smul_step_sub_weighted_center`; none match because
this is not weighted algebra but the definitional prox field of the paper's
source step.  Target-file helpers for the realized `yMem` branch were reused
separately, but they do not project the prox field. -/
theorem sourceInnerStepAt_x_eq_proxStepAt_realized_estimator
    (offset : ℕ) (z : E) (t : ℕ)
    (hz : z ∈ setup.X) (ht : 1 ≤ t) (hts : t ≤ setup.s)
    (ω : Ω) (st : RaGradState ι E)
    (hx : st.x ∈ setup.X)
    (hxMemNew :
      ∀ i : ι,
        setup.xMemAfterSampleAtState t ht hts
          (setup.ξ (offset + (t - 1)) ω) i st ∈ setup.X) :
    let stNext :=
      setup.sourceInnerStepAt offset z t hz ht hts ω st hx hxMemNew
    let yTilde : ι → E :=
      fun i =>
        (Fintype.card ι : ℝ) • (stNext.yMem i - st.yMem i) + st.yMem i
    stNext.x =
      setup.proxStepAt z t hz ht hts st.x hx
        ((Fintype.card ι : ℝ)⁻¹ • Finset.sum Finset.univ yTilde) := by
  rfl

/-- `xMem`-field projection for the literal source-domain step.

This is the companion projection to `sourceInnerStepAt_x_eq_proxStepAt_realized_estimator`
used in the Lan Lemma 6.13 Eq. (6.6.31) route: the tau-memory summand must
rewrite the realized next memory as the one-hot Eq. (6.6.10) refresh.  SOptLib
weighted residual and iterate-process candidates were considered; none expose
this paper-specific source-step field projection. -/
theorem sourceInnerStepAt_xMem_eq_xMemAfterSampleAtState
    (offset : ℕ) (z : E) (t : ℕ)
    (hz : z ∈ setup.X) (ht : 1 ≤ t) (hts : t ≤ setup.s)
    (ω : Ω) (st : RaGradState ι E)
    (hx : st.x ∈ setup.X)
    (hxMemNew :
      ∀ i : ι,
        setup.xMemAfterSampleAtState t ht hts
          (setup.ξ (offset + (t - 1)) ω) i st ∈ setup.X)
    (i : ι) :
    (setup.sourceInnerStepAt offset z t hz ht hts ω st hx hxMemNew).xMem i =
      setup.xMemAfterSampleAtState t ht hts
        (setup.ξ (offset + (t - 1)) ω) i st := by
  rfl

/-- The guarded ambient step agrees with the literal source-domain Algorithm 6.9
step exactly when the sampled component-memory refreshes are known to lie in
`X`.  This is the formal statement-correction bridge: downstream source proofs
may use the paper formula only after supplying this domain witness. -/
theorem ambientInnerStepAt_eq_sourceInnerStepAt_of_mem
    (offset : ℕ) (z : E) (t : ℕ)
    (hz : z ∈ setup.X) (ht : 1 ≤ t) (hts : t ≤ setup.s)
    (ω : Ω) (st : RaGradState ι E)
    (hx : st.x ∈ setup.X)
    (hxMemNew :
      ∀ i : ι,
        setup.xMemAfterSampleAtState t ht hts
          (setup.ξ (offset + (t - 1)) ω) i st ∈ setup.X) :
    setup.ambientInnerStepAt offset z t hz ht hts ω st hx =
      setup.sourceInnerStepAt offset z t hz ht hts ω st hx hxMemNew := by
  classical
  simp [ambientInnerStepAt, sourceInnerStepAt, gradPsiAtOrElse, hxMemNew]

/-- Corrected ambient invariant for the prox iterate produced by the Algorithm 6.9
realization.

The component-memory part of the old invariant is intentionally absent: Eq.
(6.6.10)'s affine refresh is not source-proved to remain in `X`. -/
theorem eq_6_6_13_ambientInnerStepAt_mem
    (offset : ℕ) (z : E) (t : ℕ)
    (hz : z ∈ setup.X) (ht : 1 ≤ t) (hts : t ≤ setup.s)
    (ω : Ω) (st : RaGradState ι E)
    (hx : st.x ∈ setup.X) :
    (setup.ambientInnerStepAt offset z t hz ht hts ω st hx).x ∈ setup.X ∧
      (setup.ambientInnerStepAt offset z t hz ht hts ω st hx).xPrev ∈ setup.X := by
  constructor
  · simp [ambientInnerStepAt, setup.proxStepAt_mem z t hz ht hts st.x hx]
  · simpa [ambientInnerStepAt] using hx

/-- Source-domain bridge for Algorithm 6.9's gradient-memory line, Eq. (6.6.11).

`ambientInnerStepAt` is the corrected ambient totalization, not the literal paper
step.  When a component-memory domain proof is available, the sampled `yMem`
update is exactly the source-domain gradient `gradPsiOnAt`; equivalently the
whole state rewrites through `ambientInnerStepAt_eq_sourceInnerStepAt_of_mem`. -/
theorem ambientInnerStepAt_yMem_eq_source
    (offset : ℕ) (z : E) (t : ℕ)
    (hz : z ∈ setup.X) (ht : 1 ≤ t) (hts : t ≤ setup.s)
    (ω : Ω) (st : RaGradState ι E)
    (hx : st.x ∈ setup.X)
    (hxMem :
      ∀ i : ι,
        setup.xMemAfterSampleAtState t ht hts
          (setup.ξ (offset + (t - 1)) ω) i st ∈ setup.X)
    (i : ι) :
    (setup.ambientInnerStepAt offset z t hz ht hts ω st hx).yMem i =
      if _ : i = setup.ξ (offset + (t - 1)) ω then
        setup.gradPsiOnAt z i
          ⟨setup.xMemAfterSampleAtState t ht hts
              (setup.ξ (offset + (t - 1)) ω) i st,
            hxMem i⟩
      else st.yMem i := by
  classical
  by_cases hi : i = setup.ξ (offset + (t - 1)) ω
  · subst i
    simp [ambientInnerStepAt, setup.gradPsiAtOrElse_of_mem z
      (setup.ξ (offset + (t - 1)) ω)
      (hxMem (setup.ξ (offset + (t - 1)) ω))]
  · simp [ambientInnerStepAt, hi]

/-- Guarded form of Algorithm 6.9's gradient-memory line in the corrected ambient
realization.

This theorem is the formal statement-correction boundary for arbitrary-memory
fixed runs: the source gradient is used only with an `X` proof, and the
off-domain branch is a no-op on `yMem`, not `gradPsiAt`'s zero fallback. -/
theorem ambientInnerStepAt_yMem_eq_guarded_source
    (offset : ℕ) (z : E) (t : ℕ)
    (hz : z ∈ setup.X) (ht : 1 ≤ t) (hts : t ≤ setup.s)
    (ω : Ω) (st : RaGradState ι E)
    (hx : st.x ∈ setup.X)
    (i : ι) :
    (setup.ambientInnerStepAt offset z t hz ht hts ω st hx).yMem i =
      if _ : i = setup.ξ (offset + (t - 1)) ω then
        setup.gradPsiAtOrElse z i
          (setup.xMemAfterSampleAtState t ht hts
            (setup.ξ (offset + (t - 1)) ω) i st)
          (st.yMem i)
      else st.yMem i := by
  rfl

/-- If the sampled refreshed point is off `X`, the corrected ambient
gradient-memory update keeps the previous memory. -/
theorem ambientInnerStepAt_yMem_eq_previous_of_sample_not_mem
    (offset : ℕ) (z : E) (t : ℕ)
    (hz : z ∈ setup.X) (ht : 1 ≤ t) (hts : t ≤ setup.s)
    (ω : Ω) (st : RaGradState ι E)
    (hx : st.x ∈ setup.X)
    (i : ι)
    (hi : i = setup.ξ (offset + (t - 1)) ω)
    (hnot :
      setup.xMemAfterSampleAtState t ht hts
        (setup.ξ (offset + (t - 1)) ω) i st ∉ setup.X) :
    (setup.ambientInnerStepAt offset z t hz ht hts ω st hx).yMem i = st.yMem i := by
  classical
  subst i
  simp [ambientInnerStepAt, gradPsiAtOrElse, hnot]

/-- Private fallback state for total recursive code outside Algorithm 6.9's source
range.

The fallback is intentionally not a prox step.  It uses the stated feasible
initial point `x₀ ∈ X` as a harmless total value, so the private recursion does
not assert any minimizer for `proxObjectiveAt` when the paper hypotheses
`z ∈ X`, `x^{t-1} ∈ X`, and `t = 1, ..., s` are unavailable. -/
noncomputable def innerFallbackState
    (xMem yMem : ι → E) : RaGradState ι E :=
  { x := setup.x₀
    xPrev := setup.x₀
    xMem := xMem
    yMem := yMem }

/-- The private total-recursion fallback is feasible in its primal fields because
Algorithm 6.8 starts from `x₀ ∈ X`. -/
theorem innerFallbackState_mem
    (xMem yMem : ι → E) :
    (setup.innerFallbackState xMem yMem).x ∈ setup.X ∧
      (setup.innerFallbackState xMem yMem).xPrev ∈ setup.X := by
  exact ⟨setup.hx₀_mem, setup.hx₀_mem⟩

/-- Internal zero-based totalization of one RaGrad update.

On the corrected ambient boundary it is exactly `ambientInnerStepAt`, hence its
prox line goes through the bounded Eq. (6.6.13) selector and `proxStepAt_exists`.
Outside that boundary it falls back to `x₀` and makes no mathematical prox claim.
The literal paper source step is `sourceInnerStepAt` and requires the refreshed
component-memory domain witness. -/
noncomputable def innerStepAtCore
    (offset : ℕ) (z : E) (t : ℕ) (ω : Ω) (st : RaGradState ι E) :
    RaGradState ι E := by
  classical
  exact
    if hz : z ∈ setup.X then
      if hx : st.x ∈ setup.X then
        if hts : t + 1 ≤ setup.s then
          setup.ambientInnerStepAt offset z (t + 1) hz (Nat.succ_pos t) hts ω st hx
        else
          setup.innerFallbackState st.xMem st.yMem
      else
        setup.innerFallbackState st.xMem st.yMem
    else
      setup.innerFallbackState st.xMem st.yMem

/-- Internal total recursion used to realize finite Algorithm 6.9 prefixes in Lean.

This private core is total as a Lean function, but source-range successor facts
are stated through `ambientFixedInnerProcess_exists`, which calls the bounded
`ambientInnerStepAt` interface.  The private fallback branch above has no paper
meaning and is not exposed as an argmin or minimizer theorem. -/
noncomputable def ambientFixedInnerProcessCore
    (offset : ℕ) (z x0 : E) (xMem0 : ι → E) (yMem0 : ι → E) :
    ℕ → Ω → RaGradState ι E := fun
  | 0 => fun _ =>
      { x := x0
        xPrev := x0
        xMem := xMem0
        yMem := yMem0 }
  | t + 1 => fun ω =>
      setup.innerStepAtCore offset z t ω
        (ambientFixedInnerProcessCore offset z x0 xMem0 yMem0 t ω)

/-- Existence of the corrected ambient fixed-subproblem Algorithm 6.9 run.

The selected run is characterized only on the paper range `t = 0, ..., s` by
the public `ambientInnerStepAt` update.  `SOptLib.recursiveProcess_succ_eq_sample_update`
was checked, but it bridges total raw recursions; here the name records that the
selected process is an ambient realization of the printed formulas, not a proof
that refreshed component memories remain in the paper domain. -/
theorem ambientFixedInnerProcess_exists
    (offset : ℕ) (z x0 : E) (xMem0 yMem0 : ι → E)
    (hz : z ∈ setup.X) (hx0 : x0 ∈ setup.X) :
    ∃ run : ℕ → Ω → RaGradState ι E,
      ∃ hmem : ∀ n, n ≤ setup.s → ∀ ω : Ω,
        (run n ω).x ∈ setup.X ∧ (run n ω).xPrev ∈ setup.X,
        (∀ ω : Ω,
          run 0 ω =
            { x := x0
              xPrev := x0
              xMem := xMem0
              yMem := yMem0 }) ∧
        (∀ n (hn : n + 1 ≤ setup.s), ∀ ω : Ω,
          run (n + 1) ω =
            setup.ambientInnerStepAt offset z (n + 1) hz (Nat.succ_pos n) hn
              ω (run n ω)
              ((hmem n (Nat.le_of_succ_le hn) ω).1)) := by
  classical
  let run := setup.ambientFixedInnerProcessCore offset z x0 xMem0 yMem0
  have hmem : ∀ n, n ≤ setup.s → ∀ ω : Ω,
      (run n ω).x ∈ setup.X ∧ (run n ω).xPrev ∈ setup.X := by
    intro n
    induction n with
    | zero =>
        intro hn ω
        simp [run, ambientFixedInnerProcessCore, hx0]
    | succ n ih =>
        intro hn ω
        have hprev := ih (Nat.le_of_succ_le hn) ω
        have hstep :=
          setup.eq_6_6_13_ambientInnerStepAt_mem offset z (n + 1) hz
            (Nat.succ_pos n) hn ω (run n ω) hprev.1
        simpa [run, ambientFixedInnerProcessCore, innerStepAtCore, hz, hprev.1, hn]
          using hstep
  refine ⟨run, hmem, ?_, ?_⟩
  · intro ω
    simp [run, ambientFixedInnerProcessCore]
  · intro n hn ω
    have hprev := hmem n (Nat.le_of_succ_le hn) ω
    simp [run, ambientFixedInnerProcessCore, innerStepAtCore, hz, hprev.1, hn]

/-- Corrected ambient fixed-subproblem Algorithm 6.9 process selected from the
bounded recursive equations.

Theorem 6.17 is about RaGrad applied to one fixed subproblem (6.6.8), with a fixed
quadratic center `z` and fixed optimal solution `x*`; it is not an all-time ambient
recursion.  No SOptLib match: checked `SOptLib.recursiveProcess_succ_eq_sample_update`
and `SOptLib.BlockIterateState`; those are useful proof infrastructure for total
or block-generic processes, while this corrected object is the bounded ambient run
generated by Algorithm 6.9 on `t = 1, ..., s`. -/
noncomputable def ambientFixedInnerProcess
    (offset : ℕ) (z x0 : E) (xMem0 yMem0 : ι → E)
    (hz : z ∈ setup.X) (hx0 : x0 ∈ setup.X) :
    ℕ → Ω → RaGradState ι E :=
  Classical.choose (setup.ambientFixedInnerProcess_exists offset z x0 xMem0 yMem0 hz hx0)

/-- Prox-iterate feasibility invariant for the corrected fixed Algorithm 6.9 run. -/
theorem ambientFixedInnerProcess_mem
    (offset : ℕ) (z x0 : E) (xMem0 yMem0 : ι → E)
    (hz : z ∈ setup.X) (hx0 : x0 ∈ setup.X)
    (n : ℕ) (hn : n ≤ setup.s) :
    ∀ ω : Ω,
      (setup.ambientFixedInnerProcess offset z x0 xMem0 yMem0 hz hx0 n ω).x ∈ setup.X ∧
        (setup.ambientFixedInnerProcess offset z x0 xMem0 yMem0 hz hx0 n ω).xPrev ∈ setup.X := by
  classical
  let hspec :=
    Classical.choose_spec
      (setup.ambientFixedInnerProcess_exists offset z x0 xMem0 yMem0 hz hx0)
  exact Classical.choose hspec n hn

/-- Initial equation for the selected fixed Algorithm 6.9 run. -/
theorem ambientFixedInnerProcess_zero
    (offset : ℕ) (z x0 : E) (xMem0 yMem0 : ι → E)
    (hz : z ∈ setup.X) (hx0 : x0 ∈ setup.X) :
    ∀ ω : Ω,
      setup.ambientFixedInnerProcess offset z x0 xMem0 yMem0 hz hx0 0 ω =
        { x := x0
          xPrev := x0
          xMem := xMem0
          yMem := yMem0 } := by
  classical
  intro ω
  let hspec :=
    Classical.choose_spec
      (setup.ambientFixedInnerProcess_exists offset z x0 xMem0 yMem0 hz hx0)
  exact (Classical.choose_spec hspec).1 ω

/-- Successor equation for the selected fixed Algorithm 6.9 run on the paper range. -/
theorem ambientFixedInnerProcess_succ
    (offset : ℕ) (z x0 : E) (xMem0 yMem0 : ι → E)
    (hz : z ∈ setup.X) (hx0 : x0 ∈ setup.X)
    (n : ℕ) (hn : n + 1 ≤ setup.s) :
    ∀ ω : Ω,
      setup.ambientFixedInnerProcess offset z x0 xMem0 yMem0 hz hx0 (n + 1) ω =
        setup.ambientInnerStepAt offset z (n + 1) hz (Nat.succ_pos n) hn ω
          (setup.ambientFixedInnerProcess offset z x0 xMem0 yMem0 hz hx0 n ω)
          (((setup.ambientFixedInnerProcess_mem offset z x0 xMem0 yMem0 hz hx0 n
            (Nat.le_of_succ_le hn)) ω).1) := by
  classical
  intro ω
  let hspec :=
    Classical.choose_spec
      (setup.ambientFixedInnerProcess_exists offset z x0 xMem0 yMem0 hz hx0)
  exact (Classical.choose_spec hspec).2 n hn ω

/-- Source-domain condition for a corrected fixed Algorithm 6.9 run.

At every source-range successor step, the refreshed component memories produced
by Eq. (6.6.10) must lie in `X` before the literal gradient-memory line
Eq. (6.6.11) can be used.  This is not a Setup assumption: it is the exact local
predicate separating the paper's source-domain recursion from the corrected
ambient totalization. -/
def ambientFixedSourceDomain
    (offset : ℕ) (z x0 : E) (xMem0 yMem0 : ι → E)
    (hz : z ∈ setup.X) (hx0 : x0 ∈ setup.X) : Prop :=
  ∀ n (hn : n + 1 ≤ setup.s) (ω : Ω) (i : ι),
    setup.xMemAfterSampleAtState (n + 1) (Nat.succ_pos n) hn
      (setup.ξ (offset + ((n + 1) - 1)) ω) i
      (setup.ambientFixedInnerProcess offset z x0 xMem0 yMem0 hz hx0 n ω) ∈
        setup.X

/-- Source-domain condition for the Lemma 6.12 candidate points `x̂ᵢᵗ`.

Eq. (6.6.30) uses Lemma 6.12 with the candidate refresh
`x̂ᵢᵗ = (1 + τₜ)⁻¹(x̃ᵗ + τₜ xᵢᵗ⁻¹)` for every component `i`.  This predicate is
the fixed-run source boundary for those candidate points.  It is weaker and more
source-literal than the older all-`j,i` counterfactual sampled-state predicate
below: the candidate gradient term depends on `i`, while only the estimator
`ỹᵢᵗ` is averaged over a hypothetical current sample `j`. -/
def ambientFixedHatSourceDomain
    (offset : ℕ) (z x0 : E) (xMem0 yMem0 : ι → E)
    (hz : z ∈ setup.X) (hx0 : x0 ∈ setup.X) : Prop :=
  ∀ n (hn : n + 1 ≤ setup.s) (ω : Ω) (i : ι),
    setup.xMemAfterSampleAtState (n + 1) (Nat.succ_pos n) hn i i
      (setup.ambientFixedInnerProcess offset z x0 xMem0 yMem0 hz hx0 n ω) ∈
        setup.X

/-- Stronger counterfactual sampled-state source-domain condition.

`ambientFixedSourceDomain` is the sampled-source boundary for the realized
Algorithm 6.9 run.  Eq. (6.6.30) also averages the displayed `δ₂ᵗ` summand over
every candidate value of the fresh current index, so the source-gradient kernel
has to be typed for all hypothetical samples `j`, not only the realized
`ξ_{offset+n}` branch.  The active Eq. (6.6.30) route now uses the weaker
`ambientFixedHatSourceDomain`; this predicate is retained as a stronger supplier
and comparison point for older counterfactual-route evidence. -/
def ambientFixedCounterfactualSourceDomain
    (offset : ℕ) (z x0 : E) (xMem0 yMem0 : ι → E)
    (hz : z ∈ setup.X) (hx0 : x0 ∈ setup.X) : Prop :=
  ∀ n (hn : n + 1 ≤ setup.s) (ω : Ω) (j i : ι),
    setup.xMemAfterSampleAtState (n + 1) (Nat.succ_pos n) hn j i
      (setup.ambientFixedInnerProcess offset z x0 xMem0 yMem0 hz hx0 n ω) ∈
        setup.X

/-- The counterfactual Eq. (6.6.30) source-domain boundary implies the sampled
source-domain boundary used to expose the realized Algorithm 6.9 update. -/
theorem ambientFixedSourceDomain_of_counterfactual
    (offset : ℕ) (z x0 : E) (xMem0 yMem0 : ι → E)
    (hz : z ∈ setup.X) (hx0 : x0 ∈ setup.X)
    (hcounter :
      setup.ambientFixedCounterfactualSourceDomain offset z x0 xMem0 yMem0 hz hx0) :
    setup.ambientFixedSourceDomain offset z x0 xMem0 yMem0 hz hx0 := by
  intro n hn ω i
  exact hcounter n hn ω (setup.ξ (offset + ((n + 1) - 1)) ω) i

/-- The stronger all-current-index source-domain boundary supplies the Lemma
6.12 hat-point boundary.

This is the typed comparison point for the same-interface Lemma 6.13 source
issue: the formula route needs candidate refresh membership for arbitrary `i`,
while the realized source-domain boundary below only gives it at the sampled
current index. -/
theorem ambientFixedCounterfactualSourceDomain_candidate_refresh_mem
    (offset : ℕ) (z x0 : E) (xMem0 yMem0 : ι → E)
    (hz : z ∈ setup.X) (hx0 : x0 ∈ setup.X)
    (hcounter :
      setup.ambientFixedCounterfactualSourceDomain offset z x0 xMem0 yMem0 hz hx0) :
    setup.ambientFixedHatSourceDomain offset z x0 xMem0 yMem0 hz hx0 := by
  intro n hn ω i
  exact hcounter n hn ω i i

/-- The realized source-domain boundary supplies the Lemma 6.12 candidate refresh
only for the actually sampled current index.

Together with `ambientFixedCounterfactualSourceDomain_candidate_refresh_mem`,
this records the exact source-boundary gap blocking a same-interface call from
the former hsource-only Lemma 6.13 route to the formula-level Eq. (6.6.30) route. -/
theorem ambientFixedSourceDomain_realized_refresh_mem
    (offset : ℕ) (z x0 : E) (xMem0 yMem0 : ι → E)
    (hz : z ∈ setup.X) (hx0 : x0 ∈ setup.X)
    (hsource : setup.ambientFixedSourceDomain offset z x0 xMem0 yMem0 hz hx0) :
    ∀ n (hn : n + 1 ≤ setup.s) (ω : Ω),
      setup.xMemAfterSampleAtState (n + 1) (Nat.succ_pos n) hn
        (setup.ξ (offset + ((n + 1) - 1)) ω)
        (setup.ξ (offset + ((n + 1) - 1)) ω)
        (setup.ambientFixedInnerProcess offset z x0 xMem0 yMem0 hz hx0 n ω) ∈
          setup.X := by
  intro n hn ω
  exact hsource n hn ω (setup.ξ (offset + ((n + 1) - 1)) ω)

/- The retired hsource-only attempt to derive `ambientFixedHatSourceDomain` from
`ambientFixedSourceDomain` is intentionally not a compiled declaration.  The
compiled evidence kept above is only the realized-sample implication
`ambientFixedSourceDomain_realized_refresh_mem`; the missing non-sampled
candidate branch is the source gap that forced the hsource+hhat route split. -/

/-- Under the fixed-run source-domain condition, the selected corrected fixed
process follows the literal source-domain Algorithm 6.9 step at every successor
time.

This is the statement-correction bridge for Lemma 6.13: any proof step that wants
to use the paper's Eq. (6.6.11) must first route through this theorem, so the
missing component-memory domain witness is no longer hidden in the ambient
recursion. -/
theorem ambientFixedInnerProcess_succ_eq_sourceInnerStepAt_of_domain
    (offset : ℕ) (z x0 : E) (xMem0 yMem0 : ι → E)
    (hz : z ∈ setup.X) (hx0 : x0 ∈ setup.X)
    (hsource : setup.ambientFixedSourceDomain offset z x0 xMem0 yMem0 hz hx0)
    (n : ℕ) (hn : n + 1 ≤ setup.s) :
    ∀ ω : Ω,
      setup.ambientFixedInnerProcess offset z x0 xMem0 yMem0 hz hx0 (n + 1) ω =
        setup.sourceInnerStepAt offset z (n + 1) hz (Nat.succ_pos n) hn
          ω (setup.ambientFixedInnerProcess offset z x0 xMem0 yMem0 hz hx0 n ω)
          (((setup.ambientFixedInnerProcess_mem offset z x0 xMem0 yMem0 hz hx0 n
            (Nat.le_of_succ_le hn)) ω).1)
          (hsource n hn ω) := by
  intro ω
  rw [setup.ambientFixedInnerProcess_succ offset z x0 xMem0 yMem0 hz hx0 n hn ω]
  exact setup.ambientInnerStepAt_eq_sourceInnerStepAt_of_mem
    offset z (n + 1) hz (Nat.succ_pos n) hn ω
    (setup.ambientFixedInnerProcess offset z x0 xMem0 yMem0 hz hx0 n ω)
    (((setup.ambientFixedInnerProcess_mem offset z x0 xMem0 yMem0 hz hx0 n
      (Nat.le_of_succ_le hn)) ω).1)
    (hsource n hn ω)

/-- Fixed-run source-domain form of Algorithm 6.9's gradient-memory line.

This is the theorem-level bridge consumed by the source-domain Lemma 6.13 split:
under `ambientFixedSourceDomain`, the selected fixed process exposes the literal
Eq. (6.6.11) update rather than the guarded ambient fallback. -/
theorem ambientFixedInnerProcess_yMem_eq_source_of_domain
    (offset : ℕ) (z x0 : E) (xMem0 yMem0 : ι → E)
    (hz : z ∈ setup.X) (hx0 : x0 ∈ setup.X)
    (hsource : setup.ambientFixedSourceDomain offset z x0 xMem0 yMem0 hz hx0)
    (n : ℕ) (hn : n + 1 ≤ setup.s) (ω : Ω) (i : ι) :
    (setup.ambientFixedInnerProcess offset z x0 xMem0 yMem0 hz hx0 (n + 1) ω).yMem i =
      if _ : i = setup.ξ (offset + ((n + 1) - 1)) ω then
        setup.gradPsiOnAt z i
          ⟨setup.xMemAfterSampleAtState (n + 1) (Nat.succ_pos n) hn
              (setup.ξ (offset + ((n + 1) - 1)) ω) i
              (setup.ambientFixedInnerProcess offset z x0 xMem0 yMem0 hz hx0 n ω),
            hsource n hn ω i⟩
      else
        (setup.ambientFixedInnerProcess offset z x0 xMem0 yMem0 hz hx0 n ω).yMem i := by
  classical
  rw [setup.ambientFixedInnerProcess_succ_eq_sourceInnerStepAt_of_domain
    offset z x0 xMem0 yMem0 hz hx0 hsource n hn ω]
  rfl

/-- Source-domain component-memory feasibility along the fixed Algorithm 6.9 run.

This is the typed invariant needed to instantiate the paper's component Bregman
terms `Ψ_i(x_i^t,x*)` inside Lemma 6.13.  Considered
`ambientFixedInnerProcess_mem`, `ambientFixedSourceDomain_realized_refresh_mem`,
and `ambientFixedInnerProcess_succ_eq_sourceInnerStepAt_of_domain`; the first
tracks only prox fields, the second only the realized refreshed branch, and the
third is the exact step equation used here to propagate all component memories. -/
theorem ambientFixedInnerProcess_xMem_mem_of_sourceDomain
    (offset : ℕ) (z x0 : E) (xMem0 yMem0 : ι → E)
    (hz : z ∈ setup.X) (hx0 : x0 ∈ setup.X)
    (hxMem0 : ∀ i, xMem0 i ∈ setup.X)
    (hsource : setup.ambientFixedSourceDomain offset z x0 xMem0 yMem0 hz hx0) :
    ∀ n, n ≤ setup.s → ∀ ω : Ω, ∀ i : ι,
      (setup.ambientFixedInnerProcess offset z x0 xMem0 yMem0 hz hx0 n ω).xMem i ∈
        setup.X := by
  intro n hn
  induction n with
  | zero =>
      intro ω i
      rw [setup.ambientFixedInnerProcess_zero offset z x0 xMem0 yMem0 hz hx0 ω]
      exact hxMem0 i
  | succ n _ih =>
      intro ω i
      rw [setup.ambientFixedInnerProcess_succ_eq_sourceInnerStepAt_of_domain
        offset z x0 xMem0 yMem0 hz hx0 hsource n hn ω]
      simpa [sourceInnerStepAt] using hsource n hn ω i

/-- Initial gradient-memory boundary for a fixed Algorithm 6.9 run.

This is not a setup assumption: it is the route-local form of Algorithm 6.8's
initialization `\bar y_i^0 = ∇f_i(\bar x^0)` and the invariant needed by
Lemma 6.13's Eq. (6.6.34) terminal rewrite. -/
def ambientFixedInitialGradientMemory
    (z : E) (xMem0 yMem0 : ι → E) (hxMem0 : ∀ i, xMem0 i ∈ setup.X) : Prop :=
  SOptLib.coordinateGradientMemoryMatches (setup.gradPsiOnAt z) xMem0 yMem0 hxMem0

/-- Fixed-run gradient-memory invariant for source-domain Algorithm 6.9.

If the initial component memories are already the corresponding `∇ψ_i` values,
then every stale non-sampled memory remains gradient-valued and every sampled
memory is refreshed by Eq. (6.6.11).  This is the private semantic bridge needed
before the residual telescope may use the all-component terminal rewrite in
Lemma 6.13, Eq. (6.6.34). -/
theorem ambientFixedInnerProcess_yMem_gradPsiOnAt_of_initial
    (offset : ℕ) (z x0 : E) (xMem0 yMem0 : ι → E)
    (hz : z ∈ setup.X) (hx0 : x0 ∈ setup.X)
    (hxMem0 : ∀ i, xMem0 i ∈ setup.X)
    (hsource : setup.ambientFixedSourceDomain offset z x0 xMem0 yMem0 hz hx0)
    (hgradMem0 :
      setup.ambientFixedInitialGradientMemory z xMem0 yMem0 hxMem0) :
    ∀ n (hn : n ≤ setup.s) (ω : Ω) (i : ι),
      (setup.ambientFixedInnerProcess offset z x0 xMem0 yMem0 hz hx0 n ω).yMem i =
        setup.gradPsiOnAt z i
          ⟨(setup.ambientFixedInnerProcess offset z x0 xMem0 yMem0 hz hx0 n ω).xMem i,
            setup.ambientFixedInnerProcess_xMem_mem_of_sourceDomain
              offset z x0 xMem0 yMem0 hz hx0 hxMem0 hsource n hn ω i⟩ := by
  classical
  intro n hn ω i
  exact SOptLib.coordinateGradientMemoryMatches_apply
    (SOptLib.coordinateGradientMemoryMatches_of_oneHotRefresh
    (X := setup.X) setup.s
    (setup.ambientFixedInnerProcess offset z x0 xMem0 yMem0 hz hx0)
    (fun n ω => setup.ξ (offset + n) ω)
    (fun st i => st.xMem i) (fun st i => st.yMem i)
    (setup.gradPsiOnAt z)
    (setup.ambientFixedInnerProcess_xMem_mem_of_sourceDomain
      offset z x0 xMem0 yMem0 hz hx0 hxMem0 hsource)
    (by
      intro ω
      apply SOptLib.coordinateGradientMemoryMatches_intro
      intro i
      let st0 := setup.ambientFixedInnerProcess offset z x0 xMem0 yMem0 hz hx0 0 ω
      have hzero := setup.ambientFixedInnerProcess_zero offset z x0 xMem0 yMem0 hz hx0 ω
      have hy : st0.yMem i = yMem0 i := by
        simpa [st0, hzero]
      have hx : st0.xMem i = xMem0 i := by
        simpa [st0, hzero]
      have hsub :
          (⟨st0.xMem i,
            setup.ambientFixedInnerProcess_xMem_mem_of_sourceDomain
              offset z x0 xMem0 yMem0 hz hx0 hxMem0 hsource 0
                (Nat.zero_le setup.s) ω i⟩ :
              {x : E // x ∈ setup.X}) =
            ⟨xMem0 i, hxMem0 i⟩ := by
        exact Subtype.ext hx
      change st0.yMem i =
        setup.gradPsiOnAt z i
          ⟨st0.xMem i,
            setup.ambientFixedInnerProcess_xMem_mem_of_sourceDomain
              offset z x0 xMem0 yMem0 hz hx0 hxMem0 hsource 0
                (Nat.zero_le setup.s) ω i⟩
      rw [hy, hsub]
      exact hgradMem0 i)
    (by
      intro n hn ω
      have hy :=
        setup.ambientFixedInnerProcess_yMem_eq_source_of_domain
          offset z x0 xMem0 yMem0 hz hx0 hsource n hn ω
            (setup.ξ (offset + n) ω)
      have hstep :=
        setup.ambientFixedInnerProcess_succ_eq_sourceInnerStepAt_of_domain
          offset z x0 xMem0 yMem0 hz hx0 hsource n hn ω
      have hx_next :
          (setup.ambientFixedInnerProcess offset z x0 xMem0 yMem0 hz hx0 (n + 1) ω).xMem
              (setup.ξ (offset + n) ω) =
            setup.xMemAfterSampleAtState (n + 1) (Nat.succ_pos n) hn
              (setup.ξ (offset + n) ω) (setup.ξ (offset + n) ω)
              (setup.ambientFixedInnerProcess offset z x0 xMem0 yMem0 hz hx0 n ω) := by
        simpa using congrArg
          (fun st : RaGradState ι E => st.xMem (setup.ξ (offset + n) ω)) hstep
      have hsub :
          (⟨(setup.ambientFixedInnerProcess offset z x0 xMem0 yMem0 hz hx0 (n + 1) ω).xMem
              (setup.ξ (offset + n) ω),
            setup.ambientFixedInnerProcess_xMem_mem_of_sourceDomain
              offset z x0 xMem0 yMem0 hz hx0 hxMem0 hsource (n + 1) hn ω
                (setup.ξ (offset + n) ω)⟩ :
              {x : E // x ∈ setup.X}) =
            ⟨setup.xMemAfterSampleAtState (n + 1) (Nat.succ_pos n) hn
              (setup.ξ (offset + n) ω) (setup.ξ (offset + n) ω)
              (setup.ambientFixedInnerProcess offset z x0 xMem0 yMem0 hz hx0 n ω),
              hsource n hn ω (setup.ξ (offset + n) ω)⟩ := by
        exact Subtype.ext hx_next
      calc
        (setup.ambientFixedInnerProcess offset z x0 xMem0 yMem0 hz hx0 (n + 1) ω).yMem
              (setup.ξ (offset + n) ω) =
            setup.gradPsiOnAt z (setup.ξ (offset + n) ω)
              ⟨setup.xMemAfterSampleAtState (n + 1) (Nat.succ_pos n) hn
                  (setup.ξ (offset + n) ω) (setup.ξ (offset + n) ω)
                  (setup.ambientFixedInnerProcess offset z x0 xMem0 yMem0 hz hx0 n ω),
                hsource n hn ω (setup.ξ (offset + n) ω)⟩ := by
                  simpa using hy
        _ = setup.gradPsiOnAt z (setup.ξ (offset + n) ω)
              ⟨(setup.ambientFixedInnerProcess offset z x0 xMem0 yMem0 hz hx0 (n + 1) ω).xMem
                  (setup.ξ (offset + n) ω),
                setup.ambientFixedInnerProcess_xMem_mem_of_sourceDomain
                  offset z x0 xMem0 yMem0 hz hx0 hxMem0 hsource (n + 1) hn ω
                    (setup.ξ (offset + n) ω)⟩ := by
                  exact congrArg (setup.gradPsiOnAt z (setup.ξ (offset + n) ω)) hsub.symm)
    (by
      intro n hn ω i hi
      have hy :=
        setup.ambientFixedInnerProcess_yMem_eq_source_of_domain
          offset z x0 xMem0 yMem0 hz hx0 hsource n hn ω i
      simp [hi] at hy
      simpa using hy)
    (by
      intro n hn ω i hi
      have hn' : n ≤ setup.s := Nat.le_of_succ_le hn
      have hstep :=
        setup.ambientFixedInnerProcess_succ_eq_sourceInnerStepAt_of_domain
          offset z x0 xMem0 yMem0 hz hx0 hsource n hn ω
      have hx_to_refresh :
          (setup.ambientFixedInnerProcess offset z x0 xMem0 yMem0 hz hx0 (n + 1) ω).xMem i =
            setup.xMemAfterSampleAtState (n + 1) (Nat.succ_pos n) hn
              (setup.ξ (offset + ((n + 1) - 1)) ω) i
              (setup.ambientFixedInnerProcess offset z x0 xMem0 yMem0 hz hx0 n ω) := by
        rw [hstep]
        exact setup.sourceInnerStepAt_xMem_eq_xMemAfterSampleAtState
          offset z (n + 1) hz (Nat.succ_pos n) hn ω
          (setup.ambientFixedInnerProcess offset z x0 xMem0 yMem0 hz hx0 n ω)
          (((setup.ambientFixedInnerProcess_mem offset z x0 xMem0 yMem0 hz hx0 n hn') ω).1)
          (hsource n hn ω) i
      have hi' : ¬ i = setup.ξ (offset + ((n + 1) - 1)) ω := by
        have hindex : offset + ((n + 1) - 1) = offset + n := by omega
        simpa [hindex] using hi
      calc
        (setup.ambientFixedInnerProcess offset z x0 xMem0 yMem0 hz hx0 (n + 1) ω).xMem i =
            setup.xMemAfterSampleAtState (n + 1) (Nat.succ_pos n) hn
              (setup.ξ (offset + ((n + 1) - 1)) ω) i
              (setup.ambientFixedInnerProcess offset z x0 xMem0 yMem0 hz hx0 n ω) := hx_to_refresh
        _ = (setup.ambientFixedInnerProcess offset z x0 xMem0 yMem0 hz hx0 n ω).xMem i := by
            rw [setup.xMemAfterSampleAtState_eq]
            simp [hi]) n hn ω) i

/-- Starting position in the global sample stream for the `ℓ`-th outer subproblem.

Algorithm 6.8 calls Algorithm 6.9 once per outer iteration, and Algorithm 6.9 then
generates fresh `i_t` for `t = 1, ..., s`.  No SOptLib match: searched generated
sample-prefix and recursive-process helpers in `SOptLib/Model/Filtration.lean` and
`SOptLib/Model/Iterates.lean`; those provide filtrations/process bridges, while
this paper needs the literal block offset assigning disjoint sample positions to
successive Algorithm 6.9 calls. -/
def outerSampleOffset (ℓ : ℕ) : ℕ :=
  ℓ * setup.s

/-- Existence of the corrected ambient Algorithm 6.8 outer run.

The paper states `ℓ = 1, ..., k`; this existence theorem characterizes the
selected process on that source window using the corrected ambient fixed-subproblem
Algorithm 6.9 run with a fresh sample-stream block for each outer subproblem.  It
does not assert outer component-memory feasibility. -/
theorem ambientProcess_exists :
    ∃ proc : ℕ → Ω → RapGradOuterState ι E,
      ∃ hmem : ∀ ℓ, ℓ ≤ (setup.k : ℕ) → ∀ ω : Ω,
        (proc ℓ ω).xBar ∈ setup.X,
        (∀ ω : Ω,
          proc 0 ω =
            { inner := fun _ =>
                { x := setup.x₀
                  xPrev := setup.x₀
                  xMem := fun _ => setup.x₀
                  yMem := fun i => setup.gradf i ⟨setup.x₀, setup.hx₀_mem⟩ }
              xBar := setup.x₀
              xBarMem := fun _ => setup.x₀
              yBarMem := fun i => setup.gradf i ⟨setup.x₀, setup.hx₀_mem⟩ }) ∧
          (∀ ℓ (hℓ : ℓ + 1 ≤ (setup.k : ℕ)), ∀ ω : Ω,
            proc (ℓ + 1) ω =
              let prev := proc ℓ ω
              let hprev := hmem ℓ (Nat.le_of_succ_le hℓ) ω
              let innerRec :=
                setup.ambientFixedInnerProcess (setup.outerSampleOffset ℓ)
                  prev.xBar prev.xBar prev.xBarMem prev.yBarMem
                  hprev hprev
              let final := innerRec setup.s ω
              { inner := fun t => innerRec t ω
                xBar := final.x
                xBarMem := final.xMem
                yBarMem := fun i =>
                  final.yMem i + (2 * setup.μ) • (prev.xBar - final.x) }) := by
  classical
  let initial : RapGradOuterState ι E :=
    { inner := fun _ =>
        { x := setup.x₀
          xPrev := setup.x₀
          xMem := fun _ => setup.x₀
          yMem := fun i => setup.gradf i ⟨setup.x₀, setup.hx₀_mem⟩ }
      xBar := setup.x₀
      xBarMem := fun _ => setup.x₀
      yBarMem := fun i => setup.gradf i ⟨setup.x₀, setup.hx₀_mem⟩ }
  let step (ℓ : ℕ) (ω : Ω) (prev : RapGradOuterState ι E) :
      RapGradOuterState ι E :=
    if hprev : prev.xBar ∈ setup.X then
      let innerRec :=
        setup.ambientFixedInnerProcess (setup.outerSampleOffset ℓ)
          prev.xBar prev.xBar prev.xBarMem prev.yBarMem hprev hprev
      let final := innerRec setup.s ω
      { inner := fun t => innerRec t ω
        xBar := final.x
        xBarMem := final.xMem
        yBarMem := fun i =>
          final.yMem i + (2 * setup.μ) • (prev.xBar - final.x) }
    else initial
  let proc : ℕ → Ω → RapGradOuterState ι E :=
    Nat.rec (fun _ => initial) (fun ℓ prevFun => fun ω => step ℓ ω (prevFun ω))
  have hmem : ∀ ℓ, ℓ ≤ (setup.k : ℕ) → ∀ ω : Ω,
      (proc ℓ ω).xBar ∈ setup.X := by
    intro ℓ
    induction ℓ with
    | zero =>
        intro hℓ ω
        simp [proc, initial, setup.hx₀_mem]
    | succ ℓ ih =>
        intro hℓ ω
        have hprev := ih (Nat.le_of_succ_le hℓ) ω
        have hinner :=
          (setup.ambientFixedInnerProcess_mem (setup.outerSampleOffset ℓ)
            (proc ℓ ω).xBar (proc ℓ ω).xBar
            (proc ℓ ω).xBarMem (proc ℓ ω).yBarMem
            hprev hprev setup.s le_rfl) ω
        simpa [proc, step, hprev] using hinner.1
  refine ⟨proc, hmem, ?_, ?_⟩
  · intro ω
    simp [proc, initial]
  · intro ℓ hℓ ω
    have hprev := hmem ℓ (Nat.le_of_succ_le hℓ) ω
    simp [proc, step, hprev]

/-- Corrected ambient outer process generated by Algorithm 6.8 on the source window
`ℓ = 0, ..., k`.

No SOptLib match: searched selected-output and recursive-process primitives and
checked `SOptLib.recursiveProcess_succ_eq_sample_update`; those are proof bridges
for total processes, while this declaration is the bounded ambient outer run whose
successor calls the corrected Algorithm 6.9 realization on each proximal
subproblem. -/
noncomputable def ambientProcess : ℕ → Ω → RapGradOuterState ι E :=
  Classical.choose setup.ambientProcess_exists

/-- Prox-iterate feasibility invariant for generated outer prox iterates.

No component-memory feasibility claim is included here: the Algorithm 6.9
component refresh is not source-stated to preserve `X`. -/
theorem eq_6_6_13_ambientProcess_mem (ℓ : ℕ) (hℓ : ℓ ≤ (setup.k : ℕ)) :
    ∀ ω : Ω, (setup.ambientProcess ℓ ω).xBar ∈ setup.X := by
  classical
  let hspec := Classical.choose_spec setup.ambientProcess_exists
  exact Classical.choose hspec ℓ hℓ

/-- Initial equation for the selected Algorithm 6.8 outer process.

This exposes the initialization clause printed in Algorithm 6.8 for the
`Classical.choose`-selected generated process. -/
theorem ambientProcess_zero :
    ∀ ω : Ω,
      setup.ambientProcess 0 ω =
        { inner := fun _ =>
            { x := setup.x₀
              xPrev := setup.x₀
              xMem := fun _ => setup.x₀
              yMem := fun i => setup.gradf i ⟨setup.x₀, setup.hx₀_mem⟩ }
          xBar := setup.x₀
          xBarMem := fun _ => setup.x₀
          yBarMem := fun i => setup.gradf i ⟨setup.x₀, setup.hx₀_mem⟩ } := by
  classical
  intro ω
  let hspec := Classical.choose_spec setup.ambientProcess_exists
  exact (Classical.choose_spec hspec).1 ω

/-- Algorithm 6.8 initial outer memory satisfies the fixed-run gradient-memory
boundary for the first subproblem center `x̄⁰`.

This is the base case paired with
`outerProcess_yBarMem_initialGradientMemory_for_next_run`: Algorithm 6.8 sets
`x̄_i⁰ = x̄⁰` and `ȳ_i⁰ = ∇ f_i(x̄⁰)`, while
`∇ψ_{i,x̄⁰}(x̄⁰) = ∇f_i(x̄⁰)`. -/
theorem ambientProcess_zero_initialGradientMemory
    (ω : Ω)
    (hxMem0 : ∀ i : ι, (setup.ambientProcess 0 ω).xBarMem i ∈ setup.X) :
    setup.ambientFixedInitialGradientMemory (setup.ambientProcess 0 ω).xBar
      (setup.ambientProcess 0 ω).xBarMem
      (setup.ambientProcess 0 ω).yBarMem hxMem0 := by
  classical
  intro i
  have hproc := setup.ambientProcess_zero ω
  have hbar : (setup.ambientProcess 0 ω).xBar = setup.x₀ := by
    simpa using congrArg (fun st : RapGradOuterState ι E => st.xBar) hproc
  have hxbar : (setup.ambientProcess 0 ω).xBarMem i = setup.x₀ := by
    simpa using congrArg (fun st : RapGradOuterState ι E => st.xBarMem i) hproc
  have hybar :
      (setup.ambientProcess 0 ω).yBarMem i =
        setup.gradf i ⟨setup.x₀, setup.hx₀_mem⟩ := by
    simpa using congrArg (fun st : RapGradOuterState ι E => st.yBarMem i) hproc
  have hsub :
      (⟨(setup.ambientProcess 0 ω).xBarMem i, hxMem0 i⟩ :
          {x : E // x ∈ setup.X}) =
        ⟨setup.x₀, setup.hx₀_mem⟩ := Subtype.ext hxbar
  rw [hybar, hsub, hbar]
  simp [RandomizedAcceleratedProximalPointSetup.gradPsiOnAt]

/-- Successor equation for the selected Algorithm 6.8 outer process on the paper
window `ℓ + 1 ≤ k`.

This bridge makes the selected process definitionally accountable to Algorithm
6.8's recursive subproblem solve and outer memory update, instead of leaving it
as an opaque existence witness. -/
theorem ambientProcess_succ (ℓ : ℕ) (hℓ : ℓ + 1 ≤ (setup.k : ℕ)) :
    ∀ ω : Ω,
      setup.ambientProcess (ℓ + 1) ω =
        let prev := setup.ambientProcess ℓ ω
        let hprev := setup.eq_6_6_13_ambientProcess_mem ℓ (Nat.le_of_succ_le hℓ) ω
        let innerRec :=
          setup.ambientFixedInnerProcess (setup.outerSampleOffset ℓ)
            prev.xBar prev.xBar prev.xBarMem prev.yBarMem
            hprev hprev
        let final := innerRec setup.s ω
        { inner := fun t => innerRec t ω
          xBar := final.x
          xBarMem := final.xMem
          yBarMem := fun i =>
            final.yMem i + (2 * setup.μ) • (prev.xBar - final.x) } := by
  classical
  intro ω
  let hspec := Classical.choose_spec setup.ambientProcess_exists
  exact (Classical.choose_spec hspec).2 ℓ hℓ ω

/-- Algorithm 6.8 outer-update supplier for the next fixed-run gradient-memory
boundary.

If the completed fixed run started with gradient-valued memories, then the
Algorithm 6.8 update
`yBarMem := final.yMem + (2 * μ) • (prev.xBar - final.x)` converts old-center
`∇ψ_i` memories into the next-center `∇ψ_i` memories.  This is the private
source bridge promised by the Lemma 6.13 route; it does not add a setup
assumption. -/
theorem outerProcess_yBarMem_initialGradientMemory_for_next_run
    (n : ℕ) (hn : n + 1 ≤ (setup.k : ℕ)) (ω : Ω)
    (hxMemPrev : ∀ i : ι, (setup.ambientProcess n ω).xBarMem i ∈ setup.X)
    (hsourcePrev :
      setup.ambientFixedSourceDomain (setup.outerSampleOffset n)
        (setup.ambientProcess n ω).xBar (setup.ambientProcess n ω).xBar
        (setup.ambientProcess n ω).xBarMem (setup.ambientProcess n ω).yBarMem
        (setup.eq_6_6_13_ambientProcess_mem n (Nat.le_of_succ_le hn) ω)
        (setup.eq_6_6_13_ambientProcess_mem n (Nat.le_of_succ_le hn) ω))
    (hgradPrev :
      setup.ambientFixedInitialGradientMemory (setup.ambientProcess n ω).xBar
        (setup.ambientProcess n ω).xBarMem (setup.ambientProcess n ω).yBarMem
        hxMemPrev)
    (hxMemNext : ∀ i : ι, (setup.ambientProcess (n + 1) ω).xBarMem i ∈ setup.X) :
    setup.ambientFixedInitialGradientMemory (setup.ambientProcess (n + 1) ω).xBar
      (setup.ambientProcess (n + 1) ω).xBarMem
      (setup.ambientProcess (n + 1) ω).yBarMem hxMemNext := by
  classical
  intro i
  let prev := setup.ambientProcess n ω
  let hprev := setup.eq_6_6_13_ambientProcess_mem n (Nat.le_of_succ_le hn) ω
  let innerRec :=
    setup.ambientFixedInnerProcess (setup.outerSampleOffset n)
      prev.xBar prev.xBar prev.xBarMem prev.yBarMem hprev hprev
  let final := innerRec setup.s ω
  have hfinal_y :
      final.yMem i =
        setup.gradPsiOnAt prev.xBar i
          ⟨final.xMem i,
            setup.ambientFixedInnerProcess_xMem_mem_of_sourceDomain
              (setup.outerSampleOffset n) prev.xBar prev.xBar prev.xBarMem prev.yBarMem
              hprev hprev hxMemPrev hsourcePrev setup.s le_rfl ω i⟩ := by
    simpa [prev, hprev, innerRec, final] using
      setup.ambientFixedInnerProcess_yMem_gradPsiOnAt_of_initial
        (setup.outerSampleOffset n) prev.xBar prev.xBar prev.xBarMem prev.yBarMem
        hprev hprev hxMemPrev hsourcePrev hgradPrev setup.s le_rfl ω i
  have hproc := setup.ambientProcess_succ n hn ω
  have hbar : (setup.ambientProcess (n + 1) ω).xBar = final.x := by
    simpa [prev, hprev, innerRec, final] using
      congrArg (fun st : RapGradOuterState ι E => st.xBar) hproc
  have hsub :
      (⟨(setup.ambientProcess (n + 1) ω).xBarMem i, hxMemNext i⟩ :
          {x : E // x ∈ setup.X}) =
        ⟨final.xMem i,
          setup.ambientFixedInnerProcess_xMem_mem_of_sourceDomain
            (setup.outerSampleOffset n) prev.xBar prev.xBar prev.xBarMem prev.yBarMem
            hprev hprev hxMemPrev hsourcePrev setup.s le_rfl ω i⟩ := by
    apply Subtype.ext
    simpa [prev, hprev, innerRec, final] using
      congrArg (fun st : RapGradOuterState ι E => st.xBarMem i) hproc
  calc
    (setup.ambientProcess (n + 1) ω).yBarMem i
        = final.yMem i + (2 * setup.μ) • (prev.xBar - final.x) := by
          simpa [prev, hprev, innerRec, final] using
            congrArg (fun st : RapGradOuterState ι E => st.yBarMem i) hproc
    _ = setup.gradPsiOnAt prev.xBar i
          ⟨final.xMem i,
            setup.ambientFixedInnerProcess_xMem_mem_of_sourceDomain
              (setup.outerSampleOffset n) prev.xBar prev.xBar prev.xBarMem prev.yBarMem
              hprev hprev hxMemPrev hsourcePrev setup.s le_rfl ω i⟩ +
          (2 * setup.μ) • (prev.xBar - final.x) := by
          rw [hfinal_y]
    _ = setup.gradPsiOnAt (setup.ambientProcess (n + 1) ω).xBar i
          ⟨(setup.ambientProcess (n + 1) ω).xBarMem i, hxMemNext i⟩ := by
          rw [hsub]
          rw [hbar]
          simpa [RandomizedAcceleratedProximalPointSetup.gradPsiOnAt] using
            (SOptLib.quadraticRegularizedGradient_shift_center
              (grad := setup.gradf i) (μ := setup.μ)
              (zOld := prev.xBar) (zNew := final.x)
              (x := ⟨final.xMem i,
                setup.ambientFixedInnerProcess_xMem_mem_of_sourceDomain
                  (setup.outerSampleOffset n) prev.xBar prev.xBar
                  prev.xBarMem prev.yBarMem hprev hprev hxMemPrev hsourcePrev
                  setup.s le_rfl ω i⟩))

/-- Corrected actual-offset source-domain prefix for generated Algorithm 6.8 runs.

The frozen fixed-run Theorem 6.17 call below uses offset `0` after conditioning on
an outer prefix.  The generated outer memory invariant, however, is produced by
the real Algorithm 6.8 recursion, whose completed fixed runs use offsets
`outerSampleOffset r`.  This boundary records exactly those actual
source-domain premises for the strict outer prefix; it does not assume the
gradient-memory boundary that it is used to derive.

Source correction: Algorithm 6.8 runs Algorithm 6.9 successively, carrying
`x_i^s` and `y_i^s + 2μ(\bar x^{ell-1}-\bar x^ell)` to the next subproblem.
Lean's source-domain realization must therefore expose the fixed-run
source-domain facts for those completed actual-offset inner runs before deriving
the next initial gradient-memory boundary. -/
def outerGeneratedFixedSourceDomainPrefix (n : ℕ) (ω : Ω) : Prop :=
  ∀ r : {r : ℕ // r < n},
    ∀ hprev : (setup.ambientProcess r ω).xBar ∈ setup.X,
      setup.ambientFixedSourceDomain (setup.outerSampleOffset r.1)
        (setup.ambientProcess r.1 ω).xBar (setup.ambientProcess r.1 ω).xBar
        (setup.ambientProcess r.1 ω).xBarMem (setup.ambientProcess r.1 ω).yBarMem
        hprev hprev

/-- Projection from the corrected strict-prefix boundary to the concrete
actual-offset fixed-run source-domain fact needed for one completed Algorithm
6.8 subproblem. -/
theorem outerGeneratedFixedSourceDomainPrefix_ambientFixedSourceDomain
    (n : ℕ) (ω : Ω)
    (hprefix : setup.outerGeneratedFixedSourceDomainPrefix n ω)
    (r : ℕ) (hr : r < n)
    (hprev : (setup.ambientProcess r ω).xBar ∈ setup.X) :
    setup.ambientFixedSourceDomain (setup.outerSampleOffset r)
      (setup.ambientProcess r ω).xBar (setup.ambientProcess r ω).xBar
      (setup.ambientProcess r ω).xBarMem (setup.ambientProcess r ω).yBarMem
      hprev hprev :=
  hprefix ⟨r, hr⟩ hprev

/-- Generated Algorithm 6.8 prefix supplier for initial gradient memory.

This is the outer induction promised by the Lemma 6.13 route: the base case is
Algorithm 6.8's initialization, and the successor case uses the actual-offset
fixed-run source semantics plus the outer `yBarMem` update.  The theorem returns
the component-memory feasibility needed by the dependent subtype argument and the
gradient-memory boundary for any proof of that feasibility. -/
theorem outerProcess_initialGradientMemory_of_sourceDomainPrefix
    (n : ℕ) (hn : n ≤ (setup.k : ℕ)) (ω : Ω)
    (hsourcePrefix : setup.outerGeneratedFixedSourceDomainPrefix n ω) :
    (∀ i : ι, (setup.ambientProcess n ω).xBarMem i ∈ setup.X) ∧
      ∀ hxMem : ∀ i : ι, (setup.ambientProcess n ω).xBarMem i ∈ setup.X,
        setup.ambientFixedInitialGradientMemory (setup.ambientProcess n ω).xBar
          (setup.ambientProcess n ω).xBarMem
          (setup.ambientProcess n ω).yBarMem hxMem := by
  classical
  induction n with
  | zero =>
      have hxMem0 : ∀ i : ι, (setup.ambientProcess 0 ω).xBarMem i ∈ setup.X := by
        intro i
        have hproc := setup.ambientProcess_zero ω
        have hxbar : (setup.ambientProcess 0 ω).xBarMem i = setup.x₀ := by
          simpa using congrArg (fun st : RapGradOuterState ι E => st.xBarMem i) hproc
        simpa [hxbar] using setup.hx₀_mem
      refine ⟨hxMem0, ?_⟩
      intro hxMem
      have hgrad0 := setup.ambientProcess_zero_initialGradientMemory ω hxMem0
      intro i
      have hsub :
          (⟨(setup.ambientProcess 0 ω).xBarMem i, hxMem0 i⟩ :
              {x : E // x ∈ setup.X}) =
            ⟨(setup.ambientProcess 0 ω).xBarMem i, hxMem i⟩ := by
        exact Subtype.ext rfl
      rw [hgrad0 i, hsub]
  | succ n ih =>
      have hn_prev : n ≤ (setup.k : ℕ) := Nat.le_of_succ_le hn
      have hsourcePrev :
          setup.ambientFixedSourceDomain (setup.outerSampleOffset n)
            (setup.ambientProcess n ω).xBar (setup.ambientProcess n ω).xBar
            (setup.ambientProcess n ω).xBarMem (setup.ambientProcess n ω).yBarMem
            (setup.eq_6_6_13_ambientProcess_mem n hn_prev ω)
            (setup.eq_6_6_13_ambientProcess_mem n hn_prev ω) :=
        setup.outerGeneratedFixedSourceDomainPrefix_ambientFixedSourceDomain
          (n + 1) ω hsourcePrefix n (Nat.lt_succ_self n)
          (setup.eq_6_6_13_ambientProcess_mem n hn_prev ω)
      have hsourcePrefixPrev :
          setup.outerGeneratedFixedSourceDomainPrefix n ω := by
        intro r hprev
        exact setup.outerGeneratedFixedSourceDomainPrefix_ambientFixedSourceDomain
          (n + 1) ω hsourcePrefix r.1
          (Nat.lt_trans r.2 (Nat.lt_succ_self n)) hprev
      rcases ih hn_prev hsourcePrefixPrev with ⟨hxMemPrev, hgradPrevAll⟩
      have hgradPrev :
          setup.ambientFixedInitialGradientMemory (setup.ambientProcess n ω).xBar
            (setup.ambientProcess n ω).xBarMem (setup.ambientProcess n ω).yBarMem
            hxMemPrev :=
        hgradPrevAll hxMemPrev
      have hxMemNext : ∀ i : ι, (setup.ambientProcess (n + 1) ω).xBarMem i ∈ setup.X := by
        intro i
        let prev := setup.ambientProcess n ω
        let hprev := setup.eq_6_6_13_ambientProcess_mem n hn_prev ω
        let innerRec :=
          setup.ambientFixedInnerProcess (setup.outerSampleOffset n)
            prev.xBar prev.xBar prev.xBarMem prev.yBarMem hprev hprev
        let final := innerRec setup.s ω
        have hfinal_mem :
            final.xMem i ∈ setup.X := by
          simpa [prev, hprev, innerRec, final] using
            setup.ambientFixedInnerProcess_xMem_mem_of_sourceDomain
              (setup.outerSampleOffset n) prev.xBar prev.xBar prev.xBarMem prev.yBarMem
              hprev hprev hxMemPrev hsourcePrev setup.s le_rfl ω i
        have hproc := setup.ambientProcess_succ n hn ω
        have hxbar :
            (setup.ambientProcess (n + 1) ω).xBarMem i = final.xMem i := by
          simpa [prev, hprev, innerRec, final] using
            congrArg (fun st : RapGradOuterState ι E => st.xBarMem i) hproc
        simpa [hxbar] using hfinal_mem
      refine ⟨hxMemNext, ?_⟩
      intro hxMem
      have hgradNext0 :=
        setup.outerProcess_yBarMem_initialGradientMemory_for_next_run
          n hn ω hxMemPrev hsourcePrev hgradPrev hxMemNext
      intro i
      have hsub :
          (⟨(setup.ambientProcess (n + 1) ω).xBarMem i, hxMemNext i⟩ :
              {x : E // x ∈ setup.X}) =
            ⟨(setup.ambientProcess (n + 1) ω).xBarMem i, hxMem i⟩ := by
        exact Subtype.ext rfl
      rw [hgradNext0 i, hsub]

/-- Outer iterate `x̄^ℓ` generated by Algorithm 6.8.

Source: `book/FOML/RandomizedAcceleratedProximalPoint.json#/main_theorem/statement_math`
says the iterates `\bar{x}^ℓ`, `ℓ = 1, ..., k`, are generated by Algorithm 6.8;
`book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec/steps/9`
states the outer update `\bar{x}^ℓ = x^s`. -/
noncomputable def xBarIter (ℓ : ℕ) : Ω → E :=
  fun ω => (setup.ambientProcess ℓ ω).xBar

/-- Generated center for the `ℓ`-th outer proximal subproblem.

This is Algorithm 6.8's `x̄^{ℓ-1}`; `outerCenter 0` is totalized to `x̄⁰` only
for Lean indexing outside the paper range.  Source:
`book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec/steps/0`
defines the outer subproblem centered at `\bar{x}^{ℓ-1}`, and
`book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec/steps/1`
defines `ψ_i^ℓ` and `φ^ℓ` with the same center.
No SOptLib match: searched selected
output/iterate primitives and scanned `SOptLib/Model/Iterates.lean`; those
provide abstract output-window helpers, not this paper's previous-outer-iterate
center from Eq. (6.6.8). -/
noncomputable def outerCenter : ℕ → Ω → E
  := SOptLib.previousIterateOrInitial setup.x₀ setup.xBarIter

/-- Algorithm 6.8 starts from `x̄⁰`. -/
theorem outerCenter_zero : setup.outerCenter 0 = fun _ : Ω => setup.x₀ := by
  rfl

/-- For paper outer index `ℓ+1`, the subproblem center is the generated `x̄^ℓ`. -/
theorem outerCenter_succ (ℓ : ℕ) :
    setup.outerCenter (ℓ + 1) = setup.xBarIter ℓ := by
  rfl

/-- Algorithm 6.8's paper output window `{1, ..., k}`.

Source: `book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec/output`
says the returned iterate is `\bar{x}^{\hat{\ell}}` for random
`\hat{\ell} ∈ [k]`, and
`book/FOML/RandomizedAcceleratedProximalPoint.json#/assumptions/3` repeats that
Theorem 6.16 selects `\hat{\ell}` from `[k]`.

No SOptLib match: checked `SOptLib.normalizedFiniteWindowPMF`,
`SOptLib.finiteWindowSelectedOutputExpectation_eq_weighted_sum`, and the
positive-time output-window telescope helpers.  Those are reusable probability
or telescope lemmas for an already supplied finite window; Theorem 6.16 needs the
literal source window `[k]` over generated outer iterates. -/
def outputWindow : Finset ℕ :=
  Finset.Icc 1 (setup.k : ℕ)

/-- Bounded index type for the random outer iterate `ℓ̂ ∈ [k]` in Theorem 6.16.

Source: `book/FOML/RandomizedAcceleratedProximalPoint.json#/main_theorem/statement_math`
states `\hat{\ell}` is randomly selected from `[k]`; this subtype prevents the
paper-facing API from exposing outer indices outside that source window. -/
abbrev OutputIndex : Type :=
  {ℓ : ℕ // ℓ ∈ setup.outputWindow}

/-- Bounded inner-loop index type for Algorithm 6.9's paper range `t = 1, ..., s`.

Source: `book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec/steps`
lists Algorithm 6.9's update equations for `t = 1, ..., s`; the PDF Algorithm
6.9 line extracted around 23488-23512 also states `for t = 1, ..., s do`.

No SOptLib match: checked the positive-time output-window helpers in
`SOptLib/Model/Iterates.lean` and `SOptLib/Layer1/Telescope.lean`; those model
generic positive-time windows for weighting/telescoping, while Algorithm 6.9 needs
the literal closed range tied to this setup's inner-loop length `s`. -/
abbrev InnerIndex : Type :=
  {t : ℕ // 1 ≤ t ∧ t ≤ setup.s}

/-- The paper range `t = 1, ..., s` is nonempty only when `1 ≤ s`.

This records the statement-correction guard used by the corrected Lemma 6.13
source-domain route: the printed lemma is about iterates indexed by
`t = 1, ..., s`, not Lean's totalized zero-step fallback. -/
theorem one_le_s_of_innerIndex (t : setup.InnerIndex) : 1 ≤ setup.s :=
  le_trans t.2.1 t.2.2

/-- Feasibility of generated outer iterates is a derived invariant of Algorithm 6.8
on the source window `ℓ = 0, ..., k`, not a source-facing setup field. -/
theorem xBarIter_mem (ℓ : ℕ) (hℓ : ℓ ≤ (setup.k : ℕ)) :
    ∀ ω : Ω, setup.xBarIter ℓ ω ∈ setup.X := by
  intro ω
  simpa [xBarIter] using setup.eq_6_6_13_ambientProcess_mem ℓ hℓ ω

/-- Feasibility of the generated subproblem center on Algorithm 6.8's source
window `ℓ = 1, ..., k`. -/
theorem outerCenter_mem (ℓ : setup.OutputIndex) :
    ∀ ω : Ω, setup.outerCenter ℓ.1 ω ∈ setup.X := by
  intro ω
  have hIcc : ℓ.1 ∈ Finset.Icc 1 (setup.k : ℕ) := by
    simpa [outputWindow] using ℓ.2
  have hbounds := Finset.mem_Icc.mp hIcc
  have hpos0 : 0 < ℓ.1 := lt_of_lt_of_le Nat.zero_lt_one hbounds.1
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos0)
  have hsuccle : n + 1 ≤ (setup.k : ℕ) := by
    simpa [hn] using hbounds.2
  have hnle : n ≤ (setup.k : ℕ) := Nat.le_of_succ_le hsuccle
  rw [hn]
  simpa [outerCenter] using setup.xBarIter_mem n hnle ω

/-- Source-domain proximal component objective for outer iteration ℓ:
`ψᵢ^ℓ(ω,x) = fᵢ(x) + μ‖x − x̄^{ℓ−1}(ω)‖²` for `x ∈ X`.

Source: `book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec/steps/1`,
Eq. (6.6.8), defines
`ψ_i^ℓ(x) := f_i(x)+ μ‖x-\bar{x}^{ℓ-1}‖^2`. -/
noncomputable def psiOn (ℓ : ℕ) (i : ι) (ω : Ω) (x : {x : E // x ∈ setup.X}) : ℝ :=
  setup.psiAtOn (setup.outerCenter ℓ ω) i x

/-- Internal ambient compatibility wrapper for generated-center `ψᵢ^ℓ`.

The source object is `psiOn`; this total ambient function is only a bridge for
legacy statements and derivative-within APIs. -/
noncomputable def psi (ℓ : ℕ) (i : ι) (ω : Ω) (x : E) : ℝ :=
  setup.psiAt (setup.outerCenter ℓ ω) i x

/-- Feasible-point rewrite for generated-center `ψᵢ^ℓ`. -/
@[simp]
theorem psi_of_mem (ℓ : ℕ) (i : ι) (ω : Ω) {x : E} (hx : x ∈ setup.X) :
    setup.psi ℓ i ω x = setup.psiOn ℓ i ω ⟨x, hx⟩ := by
  simpa [psi, psiOn] using setup.psiAt_of_mem (setup.outerCenter ℓ ω) i hx

/-- Internal ambient compatibility wrapper for the generated-center `ψᵢ^ℓ` gradient.

The paper-facing object is `gradPsiOn`, evaluated only at points carrying their
membership in `X`.  This wrapper reduces to that object on feasible inputs through
`gradPsiOn_coe` and otherwise has no source semantics. -/
noncomputable def gradPsi (ℓ : ℕ) (i : ι) (ω : Ω) (x : E) : E :=
  setup.gradPsiAt (setup.outerCenter ℓ ω) i x

/-- Source-domain gradient of the generated-center `ψᵢ^ℓ`.

Algorithm 6.9's gradient-memory update (Eq. 6.6.11) is only paper-meaningful at
component points already known to lie in `X`; this wrapper keeps that domain fact
in the object-layer API while `gradPsi` remains the ambient formula bridge.
Source: `book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec/steps/6`. -/
noncomputable def gradPsiOn (ℓ : ℕ) (i : ι) (ω : Ω)
    (x : {x : E // x ∈ setup.X}) : E :=
  setup.gradPsiOnAt (setup.outerCenter ℓ ω) i x

/-- Coercion bridge for the generated-center source-domain gradient. -/
theorem gradPsiOn_coe (ℓ : ℕ) (i : ι) (ω : Ω) (x : {x : E // x ∈ setup.X}) :
    setup.gradPsiOn ℓ i ω x = setup.gradPsi ℓ i ω x.1 := by
  simpa [gradPsiOn, gradPsi] using setup.gradPsiOnAt_coe (setup.outerCenter ℓ ω) i x

/-- Quadratic regulariser for outer iteration ℓ:
`φ^ℓ(ω,x) = (μ/2)‖x − x̄^{ℓ−1}(ω)‖²`.

Source: `book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec/steps/1`,
Eq. (6.6.8), defines `φ^ℓ(x) := μ/2‖x-\bar{x}^{ℓ-1}‖^2`. -/
noncomputable def phi (ℓ : ℕ) (ω : Ω) (x : E) : ℝ :=
  setup.phiAt (setup.outerCenter ℓ ω) x

/-- Gradient of the generated-center `φ^ℓ` at `x`.

Source: `book/FOML/RandomizedAcceleratedProximalPoint.json#/main_theorem/proof/0`
uses `∇φ^{\hat{\ell}}(x_{\hat{\ell}}^*)` in the proximal-subproblem optimality
condition. -/
noncomputable def gradPhi (ℓ : ℕ) (ω : Ω) (x : E) : E :=
  setup.gradPhiAt (setup.outerCenter ℓ ω) x

/-- Quadratic Bregman divergence generated by the paper's `φ^ℓ`.

Source: `book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec/steps/8`,
Eq. (6.6.13), uses `V_φ(x,x^{t-1})` in the prox objective. -/
noncomputable def quadraticBregman (ℓ : ℕ) (ω : Ω) (x y : E) : ℝ :=
  setup.quadraticBregmanAt (setup.outerCenter ℓ ω) x y

/-- Source-domain Eq. (6.6.13) prox objective with the generated center.

Source: `book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec/steps/8`
states the Algorithm 6.9 prox update as an `argmin` over `X` of
`φ(x)+⟪(1/m)∑ᵢ \tilde y_i^t,x⟫+η_t V_φ(x,x^{t-1})`. -/
noncomputable def proxObjectiveOn (ℓ t : ℕ) (ω : Ω) (xPrev g : E)
    (x : {x : E // x ∈ setup.X}) : ℝ :=
  setup.proxObjectiveAtOn (setup.outerCenter ℓ ω) t xPrev g x

/-- Internal ambient compatibility wrapper for Eq. (6.6.13) with generated center. -/
noncomputable def proxObjective (ℓ t : ℕ) (ω : Ω) (xPrev g x : E) : ℝ :=
  setup.proxObjectiveAt (setup.outerCenter ℓ ω) t xPrev g x

/-- Paper-facing Eq. (6.6.13) prox step with the generated center and bounded
Algorithm 6.8/6.9 source indices.

Source: `book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec/steps/8`,
Eq. (6.6.13), defines `x^t` by the displayed constrained prox `argmin`. -/
noncomputable def proxStep (ℓ : setup.OutputIndex) (t : setup.InnerIndex)
    (ω : Ω) (xPrev : E) (hxPrev : xPrev ∈ setup.X) (g : E) : E :=
  setup.proxStepAt (setup.outerCenter ℓ.1 ω) t.1 (setup.outerCenter_mem ℓ ω)
    t.2.1 t.2.2 xPrev hxPrev g

/-- The generated-center prox step is feasible when its source-domain inputs are feasible. -/
theorem proxStep_mem (ℓ : setup.OutputIndex) (t : setup.InnerIndex)
    (ω : Ω) (xPrev : E) (hxPrev : xPrev ∈ setup.X) (g : E) :
    setup.proxStep ℓ t ω xPrev hxPrev g ∈ setup.X := by
  exact setup.proxStepAt_mem (setup.outerCenter ℓ.1 ω) t.1 (setup.outerCenter_mem ℓ ω)
    t.2.1 t.2.2 xPrev hxPrev g

/-- The generated-center prox step realizes the Eq. (6.6.13) argmin. -/
theorem proxStep_is_argmin (ℓ : setup.OutputIndex) (t : setup.InnerIndex)
    (ω : Ω) (xPrev : E) (hxPrev : xPrev ∈ setup.X) (g : E) :
    IsMinOn (setup.proxObjectiveOn ℓ.1 t.1 ω xPrev g) Set.univ
      (setup.proxStepAtOn (setup.outerCenter ℓ.1 ω) t.1
        (setup.outerCenter_mem ℓ ω) t.2.1 t.2.2 xPrev hxPrev g) := by
  exact setup.proxStepAtOn_is_argmin (setup.outerCenter ℓ.1 ω) t.1
    (setup.outerCenter_mem ℓ ω) t.2.1 t.2.2 xPrev hxPrev g

/-- Inner primal iterate `xᵗ` inside outer iteration `ℓ`. -/
noncomputable def xInnerIter (ℓ t : ℕ) : Ω → E :=
  fun ω => (setup.ambientProcess ℓ ω).inner t |>.x

/-- Feasibility of generated inner prox iterates is a derived invariant of Algorithm
6.9's Eq. (6.6.13) argmin recursion on the source window `t = 0, ..., s`. -/
theorem xInnerIter_mem (ℓ : setup.OutputIndex) (t : ℕ) (ht : t ≤ setup.s) :
    ∀ ω : Ω, setup.xInnerIter ℓ.1 t ω ∈ setup.X := by
  intro ω
  have hIcc : ℓ.1 ∈ Finset.Icc 1 (setup.k : ℕ) := by
    simpa [outputWindow] using ℓ.2
  have hbounds := Finset.mem_Icc.mp hIcc
  have hpos0 : 0 < ℓ.1 := lt_of_lt_of_le Nat.zero_lt_one hbounds.1
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos0)
  have hsucc : n + 1 ≤ (setup.k : ℕ) := by
    simpa [hn] using hbounds.2
  have hprev :=
    setup.eq_6_6_13_ambientProcess_mem n (Nat.le_of_succ_le hsucc) ω
  have hfixed :=
    (setup.ambientFixedInnerProcess_mem (setup.outerSampleOffset n)
      (setup.ambientProcess n ω).xBar (setup.ambientProcess n ω).xBar
      (setup.ambientProcess n ω).xBarMem (setup.ambientProcess n ω).yBarMem
      hprev hprev t ht ω).1
  rw [hn]
  simpa [xInnerIter, setup.ambientProcess_succ n hsucc ω] using hfixed

/-- Inner per-component primal memory `xᵢᵗ` inside outer iteration `ℓ`. -/
noncomputable def xMemIter (ℓ t : ℕ) (i : ι) : Ω → E :=
  fun ω => (setup.ambientProcess ℓ ω).inner t |>.xMem i

/-- Explicit boundary version of component-memory feasibility.

The source does not prove this for the affine refresh in Eq. (6.6.10); consumers
that need source-domain component objectives must supply the domain fact
separately, and results using it are corrected/internal rather than the original
paper statement. -/
theorem xMemIter_mem_sourceBoundary (ℓ : setup.OutputIndex) (t : ℕ) (_ht : t ≤ setup.s)
    (i : ι) (hmem : ∀ ω : Ω, setup.xMemIter ℓ.1 t i ω ∈ setup.X) :
    ∀ ω : Ω, setup.xMemIter ℓ.1 t i ω ∈ setup.X :=
  hmem

/-- Base outer boundary for applying a frozen Lemma 6.13/Theorem 6.17 call.

This contains exactly the selected-run component-memory feasibility, fixed-run
source-domain, and fixed-run hat-source-domain facts at offset `0`.  It
intentionally omits the actual-offset strict-prefix source-domain facts for
earlier generated Algorithm 6.8 runs; those are a separate corrected boundary
component because they are not derivable from this selected-run data alone in
the current Lean interface. -/
def outerPrefixHatSourceDomainBase (ℓ : setup.OutputIndex) : Prop :=
  ∀ ω₀ : Ω,
    let z : E := setup.outerCenter ℓ.1 ω₀
    let hz : z ∈ setup.X := by
      simpa [z] using setup.outerCenter_mem ℓ ω₀
    let xMem0 : ι → E := (setup.ambientProcess (ℓ.1 - 1) ω₀).xBarMem
    let yMem0 : ι → E := (setup.ambientProcess (ℓ.1 - 1) ω₀).yBarMem
    (∀ i : ι, xMem0 i ∈ setup.X) ∧
      setup.ambientFixedSourceDomain 0 z z xMem0 yMem0 hz hz ∧
      setup.ambientFixedHatSourceDomain 0 z z xMem0 yMem0 hz hz

/-- Corrected outer boundary for applying Lemma 6.13/Theorem 6.17 through
the source formula route.

The base part exposes the selected frozen Algorithm 6.9 source and hat-domain
facts.  The actual-offset prefix source-domain part is the smaller
generated-process premise from which Algorithm 6.8/6.9's initial
gradient-valued memory boundary is derived privately; the boundary itself is not
stored here as an assumption. -/
def outerPrefixHatSourceDomain (ℓ : setup.OutputIndex) : Prop :=
  setup.outerPrefixHatSourceDomainBase ℓ ∧
    ∀ ω₀ : Ω,
      setup.outerGeneratedFixedSourceDomainPrefix (ℓ.1 - 1) ω₀

/-- Identity bridge for the corrected outer hat-source boundary. -/
theorem outer_prefix_ambientFixedHatSourceDomain
    (ℓ : setup.OutputIndex) (hhat : setup.outerPrefixHatSourceDomain ℓ) :
    setup.outerPrefixHatSourceDomain ℓ :=
  hhat

/-- Projection to the selected frozen-run source and hat-domain boundary. -/
theorem outerPrefixHatSourceDomain_base
    (ℓ : setup.OutputIndex) (hhat : setup.outerPrefixHatSourceDomain ℓ) :
    setup.outerPrefixHatSourceDomainBase ℓ :=
  hhat.1

/-- The corrected outer boundary explicitly exposes the actual-offset strict
prefix source-domain facts needed to derive Algorithm 6.8's generated
gradient-memory initialization for the selected fixed run. -/
theorem outerPrefixHatSourceDomain_actualOffsetPrefix
    (ℓ : setup.OutputIndex) (hhat : setup.outerPrefixHatSourceDomain ℓ) (ω₀ : Ω) :
    setup.outerGeneratedFixedSourceDomainPrefix (ℓ.1 - 1) ω₀ :=
  hhat.2 ω₀

/- The historical Phase 2B audit attempt to derive
`outerGeneratedFixedSourceDomainPrefix` from only
`outerPrefixHatSourceDomainBase` is intentionally retired.  The base boundary is
selected-run, offset-0 data; actual-offset strict-prefix generated-run facts are
not a consequence of it and are instead the second conjunct of
`outerPrefixHatSourceDomain`, projected by
`outerPrefixHatSourceDomain_actualOffsetPrefix` above. -/

/-- Inner per-component gradient memory `yᵢᵗ` inside outer iteration `ℓ`. -/
noncomputable def yMemIter (ℓ t : ℕ) (i : ι) : Ω → E :=
  fun ω => (setup.ambientProcess ℓ ω).inner t |>.yMem i

/-- Internal totalized extrapolated primal point used by recursive implementation.

Algorithm 6.9's public source-facing object is `xTildeAt`, restricted to
`t = 1, ..., s`.  This helper exists only because Lean process families are total
functions on `ℕ`.  Source:
`book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec/steps/4`,
Eq. (6.6.9), states `\tilde{x}^t = α_t(x^{t-1}-x^{t-2})+x^{t-1}`. -/
noncomputable def xTilde (ℓ t : ℕ) : Ω → E :=
  fun ω =>
    let st := (setup.ambientProcess ℓ ω).inner (t - 1)
    SOptLib.extrapolatedPoint (setup.αSeq t) st.x st.xPrev

/-- Per-component refreshed primal memory at step `t` of outer iteration `ℓ`
(Eq. 6.6.10).

No SOptLib match: searched conditional-expectation/sample-index primitives and
checked the finite residual algebra candidates; those prove weighted-sum identities
once an update is supplied, while this paper object is the literal affine refresh
`(1 + τ_t)^{-1}(x̃^t + τ_t x_i^{t-1})`.  The source does not state the domain
closure needed before evaluating `∇ψ_i`; that fact is not hidden in this
definition. -/
noncomputable def xHat (ℓ t : ℕ) (i : ι) : Ω → E :=
  fun ω =>
    let st := (setup.ambientProcess ℓ ω).inner (t - 1)
    SOptLib.relaxedMemoryRefreshPoint (setup.τSeq t)
      (setup.xTilde ℓ t ω) (st.xMem i)

/-- The refreshed point is the affine formula of Eq. (6.6.10). -/
theorem xHat_eq_formula (ℓ t : ℕ) (i : ι) (ω : Ω) :
    setup.xHat ℓ t i ω =
      let st := (setup.ambientProcess ℓ ω).inner (t - 1)
      (1 + setup.τSeq t)⁻¹ •
        (setup.xTilde ℓ t ω + setup.τSeq t • st.xMem i) := by
  rfl

/-- Defining equation for the paper range of Eq. (6.6.9), avoiding the totalized
`t - 1` case in later proofs. -/
theorem xTilde_succ (ℓ t : ℕ) :
    setup.xTilde ℓ (t + 1) =
      fun ω =>
        let st := (setup.ambientProcess ℓ ω).inner t
        setup.αSeq (t + 1) • (st.x - st.xPrev) + st.x := by
  rfl

/-- Defining equation for the paper range of Eq. (6.6.10). -/
theorem xHat_succ (ℓ t : ℕ) (i : ι) :
    setup.xHat ℓ (t + 1) i =
      fun ω =>
        let st := (setup.ambientProcess ℓ ω).inner t
        (1 + setup.τSeq (t + 1))⁻¹ •
          (setup.xTilde ℓ (t + 1) ω + setup.τSeq (t + 1) • st.xMem i) := by
  funext ω
  exact setup.xHat_eq_formula ℓ (t + 1) i ω

/-- Component memory that would result at paper step `t` if the fresh index were
`j`, with the past held fixed.

No SOptLib match: searched conditional-expectation/sample-index primitives and
checked the finite residual algebra candidates; they prove weighted-sum identities
after an update is supplied, while Lemma 6.12 needs the literal Algorithm 6.9
case split from Eq. (6.6.10). -/
noncomputable def xMemAfterSample (ℓ t : ℕ) (j i : ι) : Ω → E :=
  fun ω =>
    if i = j then setup.xHat ℓ t i ω
    else setup.xMemIter ℓ (t - 1) i ω

/-- Gradient memory that would result at paper step `t` if the fresh index were
`j`, matching Eq. (6.6.11). -/
noncomputable def yMemAfterSample (ℓ t : ℕ) (j i : ι) : Ω → E :=
  fun ω =>
    if i = j then setup.gradPsi ℓ i ω (setup.xMemAfterSample ℓ t j i ω)
    else setup.yMemIter ℓ (t - 1) i ω

/-- Component estimator that would result at paper step `t` under a fresh index `j`,
matching Eq. (6.6.12). -/
noncomputable def yTildeAfterSample (ℓ t : ℕ) (j i : ι) : Ω → E :=
  fun ω =>
    (Fintype.card ι : ℝ) •
        (setup.yMemAfterSample ℓ t j i ω - setup.yMemIter ℓ (t - 1) i ω) +
      setup.yMemIter ℓ (t - 1) i ω

/-- Uniform conditional average over the single current component index `i_t`.

No SOptLib match: the available probability lemmas target measure-space conditional
expectations, while Lemma 6.12 is a finite one-step `E_{i_t}` identity over the
uniform current index in Algorithm 6.9. -/
noncomputable def currentIndexAverage {β : Type*} [AddCommMonoid β] [Module ℝ β]
    (g : ι → β) : β :=
  SOptLib.finiteUniformAverage g

/-- Averaged gradient estimator for the prox step (Eq. 6.6.12):
`ỹᵢᵗ = m(yᵢᵗ − yᵢᵗ⁻¹) + yᵢᵗ⁻¹`. -/
noncomputable def yTilde (ℓ t : ℕ) : Ω → ι → E :=
  fun ω i =>
    let st := (setup.ambientProcess ℓ ω).inner t
    let stPrev := (setup.ambientProcess ℓ ω).inner (t - 1)
    (Fintype.card ι : ℝ) • (st.yMem i - stPrev.yMem i) + stPrev.yMem i

/-- Average of `ỹᵢᵗ` over components, used in the prox step (Eq. 6.6.13). -/
noncomputable def avgYTilde (ℓ t : ℕ) : Ω → E :=
  fun ω =>
    (Fintype.card ι : ℝ)⁻¹ •
      Finset.sum Finset.univ (fun i => setup.yTilde ℓ t ω i)

/-- Ambient fixed-subproblem primal iterate `xᵗ` of the corrected Algorithm 6.9 realization. -/
noncomputable def ambientFixedX (z x0 : E) (xMem0 yMem0 : ι → E)
    (hz : z ∈ setup.X) (hx0 : x0 ∈ setup.X) (hxMem0 : ∀ i, xMem0 i ∈ setup.X)
    (t : ℕ) : Ω → E :=
  fun ω => (setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 t ω).x

/-- Ambient fixed-subproblem component memory `xᵢᵗ` of the corrected Algorithm 6.9 realization. -/
noncomputable def ambientFixedXMem (z x0 : E) (xMem0 yMem0 : ι → E)
    (hz : z ∈ setup.X) (hx0 : x0 ∈ setup.X) (hxMem0 : ∀ i, xMem0 i ∈ setup.X)
    (t : ℕ) (i : ι) : Ω → E :=
  fun ω => (setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 t ω).xMem i

/-- Ambient fixed-subproblem weighted potential used by the corrected Lemma 6.13 boundary. -/
noncomputable def ambientFixedWeightedPotential
    (z x0 : E) (xMem0 yMem0 : ι → E)
    (hz : z ∈ setup.X) (hx0 : x0 ∈ setup.X) (hxMem0 : ∀ i, xMem0 i ∈ setup.X)
    (t : ℕ) (xStar : E) : Ω → ℝ :=
  fun ω =>
    setup.γSeq t * (1 + setup.ηSeq t) *
        ((setup.μ / 2) *
          ‖setup.ambientFixedX z x0 xMem0 yMem0 hz hx0 hxMem0 t ω - xStar‖ ^ 2) +
      Finset.sum Finset.univ
        (fun i =>
          setup.μ * setup.γSeq t * (1 + setup.τSeq t) / 4 *
            ‖setup.ambientFixedXMem z x0 xMem0 yMem0 hz hx0 hxMem0 t i ω - xStar‖ ^ 2)

/-- Measurability of the sampled component stream is a Lean regularity obligation
carried by Algorithm 6.9's random-variable datum, not derived from singleton
probability masses. -/
theorem sample_measurable (n : ℕ) : Measurable (setup.ξ n) := by
  exact setup.hξ_measurable n

/-- The generated component-index stream is independent across time.

This is the Lean form of Algorithm 6.9's fresh draws used by the proof notation
`E_{i_t}` in Eq. (6.6.30).  It is source-level sampler structure, not the
derived conditional expectation identity itself. -/
theorem sample_iIndep : iIndepFun setup.ξ setup.P := by
  exact setup.hξ_iIndep

/-- The current component sample is independent of the strict sample prefix.

This is the reusable freshness bridge needed before applying Lemma 6.12 inside
Lemma 6.13: any state expression already measurable with respect to the strict
prefix before time `t` may be conditioned independently from `ξ t`. -/
theorem currentSample_indep_strictPast (t : ℕ) :
    Indep ((SOptLib.filtration setup.ξ setup.hξ_measurable).seq t)
      (MeasurableSpace.comap (setup.ξ t)
        (by infer_instance : MeasurableSpace ι)) setup.P := by
  simpa [SOptLib.filtration_seq] using
    (iIndepFun.indep_past_iSup_current
      (ξ := setup.ξ) (μ := setup.P) (t := t)
      setup.hξ_measurable setup.hξ_iIndep)

/-- Prefix-measurable state variables are independent of any later component sample.

This is the route-local API FILL should use to justify the paper's `E_{i_t}`
step: first prove the RaGrad state expression is measurable with respect to the
strict prefix, then apply this theorem to obtain independence from the fresh
sample coordinate. -/
theorem prefixMeasurable_indep_current
    {β : Type*} [MeasurableSpace β] {Z : Ω → β} {n i : ℕ}
    (hZ : Measurable[(SOptLib.filtration setup.ξ setup.hξ_measurable).seq n] Z)
    (hni : n ≤ i) :
    IndepFun Z (setup.ξ i) setup.P := by
  exact iIndepFun.indepFun_prefixMeasurable_future
    (ξ := setup.ξ) (μ := setup.P)
    setup.hξ_measurable setup.hξ_iIndep hZ hni

/-- Singleton-mass form of the uniform current-index law. -/
theorem currentSample_uniform_atom (n : ℕ) (i : ι) :
    setup.P {ω | setup.ξ n ω = i} = (Fintype.card ι : ENNReal)⁻¹ := by
  exact setup.hξ_uniform n i

/-- Any two generated component samples have the same one-dimensional uniform law.

Aligns with Algorithm 6.9's repeated uniform component draws, used in Lan
Lemma 6.14 when replacing the offset-0 fixed block by an actual generated block.
Considered `sample_identDistrib_finiteImportancePMF`, but the setup stores
singleton uniform atom masses directly rather than a PMF law; `Measure.ext_of_singleton`
is the exact finite-type bridge from those atom masses to identical
distributions. -/
theorem sample_identDistrib_of_uniform (n m : ℕ) :
    IdentDistrib (setup.ξ n) (setup.ξ m) setup.P setup.P := by
  exact identDistrib_of_countable_singleton_preimage_eq
    (P := setup.P) (Q := setup.P) (X := setup.ξ n) (Y := setup.ξ m)
    (setup.sample_measurable n).aemeasurable (setup.sample_measurable m).aemeasurable
    (by
      intro i
      change setup.P {ω | setup.ξ n ω = i} = setup.P {ω | setup.ξ m ω = i}
      rw [setup.currentSample_uniform_atom n i, setup.currentSample_uniform_atom m i])

/-- Real-valued singleton-mass form of the uniform current-index law.

This is the form needed by Bochner integral finite-sum expansions. -/
theorem currentSample_uniform_real_atom (n : ℕ) (i : ι) :
    (Measure.map (setup.ξ n) setup.P).real ({i} : Set ι) =
      (Fintype.card ι : ℝ)⁻¹ := by
  classical
  rw [Measure.real]
  have hmap :
      Measure.map (setup.ξ n) setup.P ({i} : Set ι) =
        setup.P {ω | setup.ξ n ω = i} := by
    rw [Measure.map_apply (setup.hξ_measurable n) (measurableSet_singleton i)]
    rfl
  rw [hmap, setup.currentSample_uniform_atom n i]
  rw [ENNReal.toReal_inv]
  simp

/-- Source-granularity finite-average bridge for the current fresh component index.

If a state variable `Z` is measurable with respect to the strict prefix before
time `n`, then sampling a real kernel at the fresh index `ξ n` has the same
expectation as first taking the finite uniform current-index average.  This is
the Lean form of the `E_{i_t}` replacement used in Lan Eq. (6.6.30). -/
theorem current_sample_conditional_uniform_average
    {W : Type*} [MeasurableSpace W]
    (n : ℕ) {Z : Ω → W}
    (hZ : Measurable[(SOptLib.filtration setup.ξ setup.hξ_measurable).seq n] Z)
    (F : W → ι → ℝ)
    (hF : Measurable (fun q : W × ι => F q.1 q.2))
    (hF_int : ∀ i : ι, Integrable (fun ω : Ω => F (Z ω) i) setup.P) :
    (∫ ω : Ω, F (Z ω) (setup.ξ n ω) ∂setup.P) =
      ∫ ω : Ω,
        RandomizedAcceleratedProximalPointSetup.currentIndexAverage
          (fun i : ι => F (Z ω) i) ∂setup.P := by
  classical
  haveI : IsProbabilityMeasure setup.P := setup.hP
  have hZ_top : Measurable Z := by
    exact hZ.mono ((SOptLib.filtration setup.ξ setup.hξ_measurable).le n) le_rfl
  have hindep : IndepFun Z (setup.ξ n) setup.P := by
    exact setup.prefixMeasurable_indep_current hZ le_rfl
  simpa [RandomizedAcceleratedProximalPointSetup.currentIndexAverage, smul_eq_mul] using
      (SOptLib.integral_comp_indep_finite_uniform_eq_integral_inv_card_sum
        (P := setup.P) (idx := setup.ξ n) (Z := Z) (F := F)
        hZ_top (setup.hξ_measurable n) hindep
        (setup.currentSample_uniform_real_atom n) hF hF_int)

/-- Zero-integral centered form of the fresh current-index average.

This is the scalar cancellation form of Lan Eq. (6.6.30) used inside Lemma
6.13: after the current-sample expectation is rewritten as the uniform
current-index average, any deterministic scalar multiple of
`average - sampled` integrates to zero.  Searched target/SOptLib for
"current sample average sampled integral zero scalar"; the exact primitive is
`current_sample_conditional_uniform_average`, while SOptLib martingale and
mini-batch zero-mean lemmas have different oracle/inner-product hypotheses. -/
theorem current_sample_average_sub_sample_integral_zero
    {W : Type*} [MeasurableSpace W]
    (n : ℕ) {Z : Ω → W}
    (hZ : Measurable[(SOptLib.filtration setup.ξ setup.hξ_measurable).seq n] Z)
    (F : W → ι → ℝ)
    (hF : Measurable (fun q : W × ι => F q.1 q.2))
    (hF_int : ∀ i : ι, Integrable (fun ω : Ω => F (Z ω) i) setup.P)
    (hsample_int : Integrable (fun ω : Ω => F (Z ω) (setup.ξ n ω)) setup.P)
    (γ : ℝ) :
    (∫ ω : Ω,
        γ *
          (RandomizedAcceleratedProximalPointSetup.currentIndexAverage
              (fun i : ι => F (Z ω) i) -
            F (Z ω) (setup.ξ n ω)) ∂setup.P) = 0 := by
  classical
  haveI : IsProbabilityMeasure setup.P := setup.hP
  have hZ_top : Measurable Z := by
    exact hZ.mono ((SOptLib.filtration setup.ξ setup.hξ_measurable).le n) le_rfl
  have hindep : IndepFun Z (setup.ξ n) setup.P := by
    exact setup.prefixMeasurable_indep_current hZ le_rfl
  simpa [RandomizedAcceleratedProximalPointSetup.currentIndexAverage,
    SOptLib.finiteUniformAverage, smul_eq_mul] using
      (SOptLib.integral_const_mul_finiteUniformAverage_sub_sample_eq_zero
        (P := setup.P) (idx := setup.ξ n) (Z := Z) (F := F) (γ := γ)
        hZ_top (setup.hξ_measurable n) hindep
        (setup.currentSample_uniform_real_atom n) hF hF_int hsample_int)

/-- Measurability of the sampled affine component refresh in Eq. (6.6.10).

This is the finite-dispatch bridge used by bounded fixed-process integrability
proofs.  The paper's component index is the finite set `[m]`; Lean records this
as a finite measurable-singleton index space so the branch
`i = i_t` is measurable whenever the sample `i_t` is a random variable. -/
theorem xMemAfterSampleAtState_sample_measurable
    (offset t : ℕ) (ht : 1 ≤ t) (hts : t ≤ setup.s) (i : ι)
    (x xPrev : Ω → E) (xMem yMem : ι → Ω → E)
    (hx : Measurable x) (hxPrev : Measurable xPrev)
    (hxMem : ∀ j : ι, Measurable (xMem j)) :
    Measurable
      (fun ω : Ω =>
        setup.xMemAfterSampleAtState t ht hts
          (setup.ξ (offset + (t - 1)) ω) i
          { x := x ω
            xPrev := xPrev ω
            xMem := fun j => xMem j ω
            yMem := fun j => yMem j ω }) := by
  classical
  refine measurable_fintype_dispatch
    (α := Ω) (β := E) (δ := ι)
    (idx := setup.ξ (offset + (t - 1)))
    (f := fun sample ω =>
      setup.xMemAfterSampleAtState t ht hts sample i
        { x := x ω
          xPrev := xPrev ω
          xMem := fun j => xMem j ω
          yMem := fun j => yMem j ω })
    (setup.sample_measurable (offset + (t - 1))) ?_
  intro sample
  by_cases hi : i = sample
  · have htilde :
        Measurable
          (fun ω : Ω =>
            setup.xTildeAtState t
              { x := x ω
                xPrev := xPrev ω
                xMem := fun j => xMem j ω
                yMem := fun j => yMem j ω }) := by
      simpa [xTildeAtState] using ((hx.sub hxPrev).const_smul (setup.αSeq t)).add hx
    simpa [xMemAfterSampleAtState, hi, smul_add] using
      (htilde.const_smul (((1 : ℝ) + setup.τSeq t)⁻¹)).add
        (((hxMem sample).const_smul (setup.τSeq t)).const_smul
          (((1 : ℝ) + setup.τSeq t)⁻¹))
  · simpa [xMemAfterSampleAtState, hi] using hxMem i

/-- Finite sample prefix used by one fixed Algorithm 6.9 run.

For the fixed inner process starting at sample offset `offset`, the source
iterate at time `t` only depends on the finite vector
`(ξ offset, ..., ξ (offset + t - 1))`. -/
noncomputable def ambientFixedSamplePrefix (offset t : ℕ) : Ω → Fin t → ι :=
  SOptLib.sampleWindow setup.ξ offset t

/-- Fixed-run sample windows of the same length have identical finite-vector laws.

This is the finite-block law component of Lan Lemma 6.14,
Eqs. (6.6.38)-(6.6.39): offset-0 fixed inner samples and actual generated
offset samples have the same product distribution. Considered SOptLib
`iIndepFun.indepFun_finset_subtype_blocks` and
`IdentDistrib.integral_comp_eq_of_measurable`; those handle block independence
and integral transport, while this helper supplies the missing finite-window
identical-law bridge via Mathlib `IdentDistrib.pi`, `iIndepFun.precomp`, and the
local uniform atom law `sample_identDistrib_of_uniform`. -/
theorem ambientFixedSamplePrefix_identDistrib
    (offset offset' t : ℕ) :
    IdentDistrib (setup.ambientFixedSamplePrefix offset t)
      (setup.ambientFixedSamplePrefix offset' t) setup.P setup.P := by
  exact sampleWindow_identDistrib_of_identDistrib_iIndep
    setup.sample_identDistrib_of_uniform setup.hξ_iIndep offset offset' t

/-- The strict previous outer sample prefix and the generated fresh inner block use
disjoint sample indices.

Aligns with Lan Lemma 6.14, Eqs. (6.6.38)-(6.6.39): the block starting at
`outerSampleOffset (ℓ - 1)` is fresh relative to the first `(ℓ - 1) * s`
samples. Considered SOptLib `iIndepFun.indepFun_finset_subtype_blocks`; it is
the next consumer once this disjointness fact is lifted to subtype-vector
independence, but the current helper isolates the arithmetic boundary because
the dependent function-space lift caused verifier timeouts in this round. -/
theorem outer_prefix_offset_block_finsets_disjoint
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (ℓ : setup.OutputIndex) :
    Disjoint
      (Finset.range ((ℓ.1 - 1) * setup.s))
      (Finset.image
        (fun r : Fin setup.s => setup.outerSampleOffset (ℓ.1 - 1) + r.1)
        Finset.univ) := by
  classical
  let N : ℕ := (ℓ.1 - 1) * setup.s
  let offset : ℕ := setup.outerSampleOffset (ℓ.1 - 1)
  let I : Finset ℕ := Finset.range N
  let J : Finset ℕ := Finset.image (fun r : Fin setup.s => offset + r.1) Finset.univ
  have hoffset : offset = N := by
    simp [offset, N, RandomizedAcceleratedProximalPointSetup.outerSampleOffset]
  have hdisj : Disjoint I J := by
    refine Finset.disjoint_left.mpr ?_
    intro n hnI hnJ
    have hn_lt : n < N := by
      simpa [I] using (Finset.mem_range.mp hnI)
    rcases (by simpa [J] using hnJ : ∃ r : Fin setup.s, offset + r.1 = n) with
      ⟨r, hr⟩
    have hN_le : N ≤ n := by
      rw [← hr]
      rw [hoffset]
      exact Nat.le_add_right N r.1
    exact (Nat.not_le_of_gt hn_lt) hN_le
  simpa [I, J, N, offset] using hdisj

/-- Finset-block independence transported to the paper's `Fin` vector windows.

Aligns with Lan Lemma 6.14, Eqs. (6.6.38)-(6.6.39): the strict prefix and
fresh inner block are disjoint sample windows.  Considered SOptLib
`iIndepFun.indepFun_finset_subtype_blocks`, which gives the needed independence
over subtype-indexed finite blocks; this helper only performs the measurable
coordinate restriction from those subtype vectors to the paper's literal
`Fin`-indexed windows. The proof uses the closely related SOptLib
`iIndepFun.indepFun_finset_sum_inl_inr` specialization after proving, from
`hdisj`, that the two window-index embeddings into the ambient sample stream are
jointly injective. -/
theorem indepFun_range_image_fin_vectors_of_disjoint
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (N offset t : ℕ)
    (hdisj :
      Disjoint
        (Finset.range N)
        (Finset.image (fun r : Fin t => offset + r.1) Finset.univ)) :
    IndepFun
      (fun ω : Ω => fun r : Fin N => setup.ξ r.1 ω)
      (fun ω : Ω => fun r : Fin t => setup.ξ (offset + r.1) ω)
      setup.P := by
  exact iIndepFun.indepFun_fin_range_offset_windows_of_disjoint
    setup.ξ setup.P N offset t setup.hξ_measurable setup.hξ_iIndep hdisj

/-- Independence of the strict outer prefix and the generated fresh inner block.

Aligns with Lan Lemma 6.14, Eqs. (6.6.38)-(6.6.39): the first
`(ℓ - 1) * s` generated samples are independent of the next block used by the
outer iteration. Considered SOptLib `iIndepFun.indepFun_finset_sum_inl_inr`
and `iIndepFun.indepFun_finset_subtype_blocks`; the Sum-indexed helper is the
right mathematical route from `setup.hξ_iIndep`, but the remaining Lean gap is
the explicit univ-subtype vector composition back to `Fin` vectors without
triggering timeout-prone definitional simplification. -/
theorem outer_prefix_offset_block_indep
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (ℓ : setup.OutputIndex) :
    IndepFun
      (fun ω : Ω => fun r : Fin ((ℓ.1 - 1) * setup.s) => setup.ξ r.1 ω)
      (fun ω : Ω =>
        setup.ambientFixedSamplePrefix
          (setup.outerSampleOffset (ℓ.1 - 1)) setup.s ω)
      setup.P := by
  classical
  have hdisj := setup.outer_prefix_offset_block_finsets_disjoint ℓ
  change IndepFun
    (fun ω : Ω => fun r : Fin ((ℓ.1 - 1) * setup.s) => setup.ξ r.1 ω)
    (fun ω : Ω => fun r : Fin setup.s =>
      setup.ξ (setup.outerSampleOffset (ℓ.1 - 1) + r.1) ω)
    setup.P
  exact setup.indepFun_range_image_fin_vectors_of_disjoint
    ((ℓ.1 - 1) * setup.s) (setup.outerSampleOffset (ℓ.1 - 1)) setup.s hdisj

/-- Finite-factor measurability transfer.

This local helper is the same finite-prefix pattern used in nearby Lan
formalizations: once a random variable factors through a finite-valued measurable
prefix, arbitrary scalar expressions of that frozen prefix are measurable. -/
theorem measurable_of_finite_range_factor
    {α β : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] {m : MeasurableSpace Ω}
    {Y : Ω → α} {Z : Ω → β}
    (hY : @Measurable Ω α m _ Y)
    (hfin : (Set.range Y).Finite)
    (hconst : ∀ ⦃ω ω' : Ω⦄, Y ω = Y ω' → Z ω = Z ω') :
    @Measurable Ω β m _ Z := by
  letI : MeasurableSpace Ω := m
  exact measurable_of_finite_range_fiber_const hY hfin hconst

/-- Finite-valued measurable real random variables are integrable on finite
measures. -/
theorem integrable_real_of_finite_range
    {μ : Measure Ω} [IsFiniteMeasure μ] {Z : Ω → ℝ}
    (hZ : Measurable Z) (hfin : (Set.range Z).Finite) :
    Integrable Z μ := by
  exact integrable_of_finite_range hZ.aestronglyMeasurable hfin

/-- Real observables that factor through a finite-valued prefix are integrable on
finite measures. -/
theorem integrable_real_of_finite_range_factor
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {Y : Ω → α} {Z : Ω → ℝ}
    (hY : Measurable Y) (hfin : (Set.range Y).Finite)
    (hconst : ∀ ⦃ω ω' : Ω⦄, Y ω = Y ω' → Z ω = Z ω') :
    Integrable Z μ := by
  exact integrable_of_finiteRange_factor hY hfin hconst

/-- The fixed Algorithm 6.9 state at a bounded time is determined by the finite
sample prefix up to that time.

This is the route-local bridge requested by the Phase 2b audit: the successor
case rewrites `ambientFixedInnerProcess_succ`, hence reaches the `proxStepAt`
`x`-field of Eq. (6.6.13), but avoids any non-source global prox-selector
measurability assumption. -/
theorem ambientFixedInnerProcess_prefix_const
    (offset : ℕ) (z x0 : E) (xMem0 yMem0 : ι → E)
    (hz : z ∈ setup.X) (hx0 : x0 ∈ setup.X)
    (t : ℕ) (ht : t ≤ setup.s) :
    ∀ ⦃ω ω' : Ω⦄,
      setup.ambientFixedSamplePrefix offset t ω =
        setup.ambientFixedSamplePrefix offset t ω' →
      setup.ambientFixedInnerProcess offset z x0 xMem0 yMem0 hz hx0 t ω =
        setup.ambientFixedInnerProcess offset z x0 xMem0 yMem0 hz hx0 t ω' := by
  classical
  exact
    SOptLib.recursive_process_eq_of_driver_prefix_eq
      (ξ := setup.ξ)
      (process := setup.ambientFixedInnerProcess offset z x0 xMem0 yMem0 hz hx0)
      (offset := offset)
      (R := setup.s)
      (t := t)
      (initial :=
        { x := x0
          xPrev := x0
          xMem := xMem0
          yMem := yMem0 })
      (h_zero := setup.ambientFixedInnerProcess_zero offset z x0 xMem0 yMem0 hz hx0)
      (h_succ_congr := by
        intro n hn ω ω' hprev hsample
        rw [setup.ambientFixedInnerProcess_succ offset z x0 xMem0 yMem0 hz hx0 n hn ω,
          setup.ambientFixedInnerProcess_succ offset z x0 xMem0 yMem0 hz hx0 n hn ω']
        simp [ambientInnerStepAt, xMemAfterSampleAtState, hprev, hsample])
      (ht := ht)

/-- Cross-offset form of fixed Algorithm 6.9 finite-prefix determinism.

Aligns with Lan Lemma 6.14, Eqs. (6.6.38)-(6.6.39): the terminal fixed run is a
deterministic function of its length-`t` sample block, regardless of where that
block sits in the ambient stream. Considered target-local
`ambientFixedInnerProcess_prefix_const`, `ambientFixedSamplePrefix`, and the
SOptLib/Mathlib product-law helpers found by searching "fixed inner process
sample prefix offset equality deterministic"; the existing same-offset helper is
not enough for the offset-0 versus generated-offset transport, while the
product-law helpers do not expose the Algorithm 6.9 recursion. -/
theorem ambientFixedInnerProcess_eq_of_samplePrefix_eq_offsets
    (offset offset' : ℕ) (z x0 : E) (xMem0 yMem0 : ι → E)
    (hz : z ∈ setup.X) (hx0 : x0 ∈ setup.X)
    (t : ℕ) (ht : t ≤ setup.s) :
    ∀ ⦃ω ω' : Ω⦄,
      setup.ambientFixedSamplePrefix offset t ω =
        setup.ambientFixedSamplePrefix offset' t ω' →
      setup.ambientFixedInnerProcess offset z x0 xMem0 yMem0 hz hx0 t ω =
        setup.ambientFixedInnerProcess offset' z x0 xMem0 yMem0 hz hx0 t ω' := by
  classical
  exact
    SOptLib.recursiveProcess_eq_of_driverWindow_eq_offsets
      (ξ := setup.ξ)
      (process := fun offset t ω =>
        setup.ambientFixedInnerProcess offset z x0 xMem0 yMem0 hz hx0 t ω)
      (offset := offset)
      (offset' := offset')
      (R := setup.s)
      (t := t)
      (initial :=
        { x := x0
          xPrev := x0
          xMem := xMem0
          yMem := yMem0 })
      (h_zero := by
        intro offset ω
        exact setup.ambientFixedInnerProcess_zero offset z x0 xMem0 yMem0 hz hx0 ω)
      (h_succ_congr := by
        intro offset offset' n hn ω ω' hprev hsample
        change
          setup.ambientFixedInnerProcess offset z x0 xMem0 yMem0 hz hx0 (n + 1) ω =
            setup.ambientFixedInnerProcess offset' z x0 xMem0 yMem0 hz hx0 (n + 1) ω'
        rw [setup.ambientFixedInnerProcess_succ offset z x0 xMem0 yMem0 hz hx0 n hn ω,
          setup.ambientFixedInnerProcess_succ offset' z x0 xMem0 yMem0 hz hx0 n hn ω']
        simp [ambientInnerStepAt, xMemAfterSampleAtState, hprev, hsample])
      (ht := ht)

/-- The fixed Algorithm 6.9 primal iterate at a bounded time is determined by
the finite sample prefix up to that time. -/
theorem ambientFixedX_prefix_const
    (z x0 : E) (xMem0 yMem0 : ι → E)
    (hz : z ∈ setup.X) (hx0 : x0 ∈ setup.X) (hxMem0 : ∀ i, xMem0 i ∈ setup.X)
    (t : ℕ) (ht : t ≤ setup.s) :
    ∀ ⦃ω ω' : Ω⦄,
      setup.ambientFixedSamplePrefix 0 t ω =
        setup.ambientFixedSamplePrefix 0 t ω' →
      setup.ambientFixedX z x0 xMem0 yMem0 hz hx0 hxMem0 t ω =
        setup.ambientFixedX z x0 xMem0 yMem0 hz hx0 hxMem0 t ω' := by
  intro ω ω' hprefix
  exact congrArg RaGradState.x
    (setup.ambientFixedInnerProcess_prefix_const 0 z x0 xMem0 yMem0 hz hx0 t ht hprefix)

/-- Real observables of a fixed bounded Algorithm 6.9 run are integrable when
they factor through the finite sample prefix.

This is the source-faithful replacement for trying to prove arbitrary global
measurability/integrability of the `Classical.choose` prox recursion: for each
paper-bounded time, the generated state is a deterministic function of finitely
many finite component samples. -/
theorem ambientFixed_prefix_integrable_real
    (offset t : ℕ) {Z : Ω → ℝ}
    (hconst :
      ∀ ⦃ω ω' : Ω⦄,
        setup.ambientFixedSamplePrefix offset t ω =
          setup.ambientFixedSamplePrefix offset t ω' →
        Z ω = Z ω') :
    Integrable Z setup.P := by
  classical
  letI : IsProbabilityMeasure setup.P := setup.hP
  exact integrable_of_finiteSampleWindow_factor
    (μ := setup.P) setup.ξ offset t setup.hξ_measurable (by
      intro ω ω' hwindow
      exact hconst (by simpa [ambientFixedSamplePrefix] using hwindow))

/-- Evaluate a representative kernel selected from a finite prefix range.

This is route-local infrastructure for Lan Lemma 6.13's Eq. (6.6.31)
representative kernels: once a raw scalar observable is constant on equal
prefix states, the `Classical.choose` representative agrees with the original
observable on actual prefixes.  Searched SOptLib/target for range
representative and prefix-constancy helpers; existing hits such as
`ambientFixedDelta2CurrentKernel_prefix_const` prove source-specific
constancy, while this lemma packages only the generic `Set.range`/`choose`
bookkeeping. -/
theorem range_representative_kernel_eval
    {W : Type*} (Z : Ω → W) (raw : Ω → ι → ℝ)
    [DecidablePred (fun q => q ∈ Set.range Z)]
    (hconst :
      ∀ ⦃ω ω' : Ω⦄, Z ω = Z ω' → ∀ j : ι, raw ω j = raw ω' j) :
    ∀ (ω : Ω) (j : ι),
      (if hq : Z ω ∈ Set.range Z then raw (Classical.choose hq) j else 0) =
        raw ω j := by
  exact rangeRepresentative_eval_of_const_on_fibers Z raw hconst

/-- Real observables determined by a finite global sample prefix are integrable.

This is the global-prefix analogue of `ambientFixed_prefix_integrable_real`.
Considered SOptLib finite-window selection and bounded-process integrability
candidates; the local finite-range factor helper is the exact match because
the paper expectations here are well-defined by finite sample-prefix
determinism, not by an added diameter or selector-measurability assumption. -/
theorem outer_prefix_integrable_real
    (N : ℕ) {Z : Ω → ℝ}
    (hconst :
      ∀ ⦃ω ω' : Ω⦄,
        (fun r : Fin N => setup.ξ r.1 ω) =
          (fun r : Fin N => setup.ξ r.1 ω') →
        Z ω = Z ω') :
    Integrable Z setup.P := by
  classical
  letI : IsProbabilityMeasure setup.P := setup.hP
  let prefixVec : Ω → Fin N → ι := fun ω r => setup.ξ r.1 ω
  have hprefix_meas : Measurable prefixVec := by
    change Measurable (fun ω : Ω => fun r : Fin N => setup.ξ r.1 ω)
    exact measurable_pi_lambda
      (fun ω : Ω => fun r : Fin N => setup.ξ r.1 ω)
      (fun r : Fin N => setup.sample_measurable r.1)
  have hprefix_fin : (Set.range prefixVec).Finite := Set.toFinite _
  exact integrable_real_of_finite_range_factor (μ := setup.P) hprefix_meas hprefix_fin hconst

/-- The Algorithm 6.8 outer summary fields at time `n` are determined by the
first `n * s` global component samples.

This specializes the already proved fixed-inner prefix determinism to the outer
recursion of Algorithm 6.8.  SOptLib recursive-process measurability candidates
were considered; they provide sigma-algebra measurability, while this proof needs
pointwise constancy under literal equality of finite sample prefixes.  The full
`ambientProcess` state also stores a total inner trajectory beyond the source
window, so the route-relevant outer fields are the faithful deterministic object. -/
theorem ambientProcess_outerFields_prefix_const
    (n : ℕ) (hn : n ≤ (setup.k : ℕ)) :
    ∀ ⦃ω ω' : Ω⦄,
      (fun r : Fin (n * setup.s) => setup.ξ r.1 ω) =
        (fun r : Fin (n * setup.s) => setup.ξ r.1 ω') →
      (setup.ambientProcess n ω).xBar = (setup.ambientProcess n ω').xBar ∧
        (setup.ambientProcess n ω).xBarMem = (setup.ambientProcess n ω').xBarMem ∧
        (setup.ambientProcess n ω).yBarMem = (setup.ambientProcess n ω').yBarMem := by
  classical
  induction n with
  | zero =>
      intro ω ω' _hprefix
      rw [setup.ambientProcess_zero ω, setup.ambientProcess_zero ω']
      simp
  | succ n ih =>
      intro ω ω' hprefix
      have hprevPrefix :
          (fun r : Fin (n * setup.s) => setup.ξ r.1 ω) =
            (fun r : Fin (n * setup.s) => setup.ξ r.1 ω') := by
        funext r
        exact congrFun hprefix
          ⟨r.1, Nat.lt_of_lt_of_le r.2
            (by
              simpa [Nat.succ_eq_add_one] using
                Nat.mul_le_mul_right setup.s (Nat.le_succ n))⟩
      have hprev :
          (setup.ambientProcess n ω).xBar = (setup.ambientProcess n ω').xBar ∧
            (setup.ambientProcess n ω).xBarMem = (setup.ambientProcess n ω').xBarMem ∧
            (setup.ambientProcess n ω).yBarMem = (setup.ambientProcess n ω').yBarMem :=
        ih (Nat.le_of_succ_le hn) hprevPrefix
      have hblock :
          setup.ambientFixedSamplePrefix (setup.outerSampleOffset n) setup.s ω =
            setup.ambientFixedSamplePrefix (setup.outerSampleOffset n) setup.s ω' := by
        funext r
        exact congrFun hprefix
          ⟨setup.outerSampleOffset n + r.1,
            by
              calc
                setup.outerSampleOffset n + r.1 <
                    setup.outerSampleOffset n + setup.s :=
                  Nat.add_lt_add_left r.2 (setup.outerSampleOffset n)
                _ = (n + 1) * setup.s := by
                  simp [outerSampleOffset, Nat.succ_mul]⟩
      have hfixed :
          setup.ambientFixedInnerProcess (setup.outerSampleOffset n)
              (setup.ambientProcess n ω).xBar (setup.ambientProcess n ω).xBar
              (setup.ambientProcess n ω).xBarMem (setup.ambientProcess n ω).yBarMem
              (setup.eq_6_6_13_ambientProcess_mem n (Nat.le_of_succ_le hn) ω)
              (setup.eq_6_6_13_ambientProcess_mem n (Nat.le_of_succ_le hn) ω)
              setup.s ω =
            setup.ambientFixedInnerProcess (setup.outerSampleOffset n)
              (setup.ambientProcess n ω).xBar (setup.ambientProcess n ω).xBar
              (setup.ambientProcess n ω).xBarMem (setup.ambientProcess n ω).yBarMem
              (setup.eq_6_6_13_ambientProcess_mem n (Nat.le_of_succ_le hn) ω)
              (setup.eq_6_6_13_ambientProcess_mem n (Nat.le_of_succ_le hn) ω)
              setup.s ω' := by
        exact setup.ambientFixedInnerProcess_prefix_const
          (setup.outerSampleOffset n)
          (setup.ambientProcess n ω).xBar (setup.ambientProcess n ω).xBar
          (setup.ambientProcess n ω).xBarMem (setup.ambientProcess n ω).yBarMem
          (setup.eq_6_6_13_ambientProcess_mem n (Nat.le_of_succ_le hn) ω)
          (setup.eq_6_6_13_ambientProcess_mem n (Nat.le_of_succ_le hn) ω)
          setup.s le_rfl hblock
      have hfixed' :
          setup.ambientFixedInnerProcess (setup.outerSampleOffset n)
              (setup.ambientProcess n ω').xBar (setup.ambientProcess n ω').xBar
              (setup.ambientProcess n ω').xBarMem (setup.ambientProcess n ω').yBarMem
              (setup.eq_6_6_13_ambientProcess_mem n (Nat.le_of_succ_le hn) ω')
              (setup.eq_6_6_13_ambientProcess_mem n (Nat.le_of_succ_le hn) ω')
              setup.s ω =
            setup.ambientFixedInnerProcess (setup.outerSampleOffset n)
              (setup.ambientProcess n ω').xBar (setup.ambientProcess n ω').xBar
              (setup.ambientProcess n ω').xBarMem (setup.ambientProcess n ω').yBarMem
              (setup.eq_6_6_13_ambientProcess_mem n (Nat.le_of_succ_le hn) ω')
              (setup.eq_6_6_13_ambientProcess_mem n (Nat.le_of_succ_le hn) ω')
              setup.s ω' := by
        simpa [hprev.1, hprev.2.1, hprev.2.2] using hfixed
      rw [setup.ambientProcess_succ n hn ω, setup.ambientProcess_succ n hn ω']
      simpa [hprev.1, hprev.2.1, hprev.2.2, hfixed']

/-- Projection of outer-field prefix determinism to the generated output
iterate `x̄ⁿ`. -/
theorem xBarIter_prefix_const
    (n : ℕ) (hn : n ≤ (setup.k : ℕ)) :
    ∀ ⦃ω ω' : Ω⦄,
      (fun r : Fin (n * setup.s) => setup.ξ r.1 ω) =
        (fun r : Fin (n * setup.s) => setup.ξ r.1 ω') →
      setup.xBarIter n ω = setup.xBarIter n ω' := by
  intro ω ω' hprefix
  exact (setup.ambientProcess_outerFields_prefix_const n hn hprefix).1

/-- Natural filtration generated by the global sample stream `ξ`.

This reuses `SOptLib.filtration`, which is the paper-neutral generated-prefix
filtration primitive.  The only additional ingredient is the derived sample
measurability obligation above. -/
noncomputable def filtration : Filtration ℕ ‹MeasurableSpace Ω› where
  seq := (SOptLib.filtration setup.ξ setup.sample_measurable).seq
  mono' := (SOptLib.filtration setup.ξ setup.sample_measurable).mono'
  le' := (SOptLib.filtration setup.ξ setup.sample_measurable).le'

/-- Normal cone from Definition 6.1:
`N_X(x) = {v | ∀ y ∈ X, ⟪v, y - x⟫ ≤ 0}`. -/
def normalCone (x : E) : Set E :=
  SOptLib.normalCone setup.X x

/-- Negative normal cone `-N_X(x)` as used in Definition 6.1's
`d(∇f(x), -N_X(x))`.

No SOptLib match: searched stationarity/subdifferential primitives; those model
general subdifferential membership, while Definition 6.1 prints this normal-cone
distance explicitly for the feasible set `X`. -/
def negativeNormalCone (x : E) : Set E :=
  {v : E | -v ∈ setup.normalCone x}

/-- Distance to a set as in Definition 6.1, modeled by Mathlib's metric
`infDist` primitive: `d(x, Z) = inf_{z∈Z} ‖x-z‖`.

This replaces the former inline subtype infimum in `normalConeGap`.  The relevant
candidate was `Metric.infDist`, which exactly models distance from a point to a set;
SOptLib stationarity wrappers were considered but they package different projected
gradient certificates rather than Definition 6.1's literal distance-to-set object. -/
noncomputable def distanceToSet
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω) (x : E) (Z : Set E) : ℝ :=
  Metric.infDist x Z

/-- The Mathlib distance-to-set wrapper denotes Definition 6.1's infimum form. -/
theorem distanceToSet_eq_iInf (x : E) (Z : Set E) :
    setup.distanceToSet x Z = ⨅ z : {z : E // z ∈ Z}, ‖x - z.1‖ := by
  simpa [RandomizedAcceleratedProximalPointSetup.distanceToSet, dist_eq_norm] using
    (Metric.infDist_eq_iInf (x := x) (s := Z))

/-- Distance from the source-domain gradient `∇f(x)` to the negative normal cone
`-N_X(x)`, formalising Definition 6.1's stationarity measure
`d(∇f(x), -N_X(x))` for `x ∈ X`. -/
noncomputable def normalConeGapOn (x : {x : E // x ∈ setup.X}) : ℝ :=
  SOptLib.normalConeStationarityGap setup.X (setup.gradFOn x) x.1

/-- Internal ambient compatibility wrapper for the stationarity gap.

The paper-facing object is `normalConeGapOn`.  This wrapper exists only for
legacy statements over ambient functions and reduces to the source-domain gap on
feasible points; outside `X` it has no source meaning. -/
noncomputable def normalConeGap (x : E) : ℝ :=
  by
    classical
    exact if hx : x ∈ setup.X then
      SOptLib.normalConeStationarityGap setup.X (setup.gradFOn ⟨x, hx⟩) x
    else 0

/-- Feasible-point rewrite for the ambient stationarity-gap bridge. -/
theorem normalConeGap_of_mem {x : E} (hx : x ∈ setup.X) :
    setup.normalConeGap x = setup.normalConeGapOn ⟨x, hx⟩ := by
  simp [normalConeGap, normalConeGapOn, hx]

/-- Definition 6.1 deterministic `(ε, δ)`-solution predicate.

The book states that `x ∈ X` is an `(ε, δ)`-solution if there exists
`xHat ∈ X` with squared stationarity gap at `xHat` at most `ε` and
`‖x - xHat‖² ≤ δ`. -/
def approximateSolution (ε δ : ℝ) (x : E) : Prop :=
  SOptLib.ApproximateStationarySolution setup.X setup.normalConeGapOn ε δ x

/-- Proof-carrying real observable whose expectation is well-defined under `P`.

No SOptLib match: checked `SOptLib.objectiveExpectation`, which packages
expectations of stochastic objective kernels, and searched finite-window selected
output expectation helpers; those do not model Definition 6.1's arbitrary real
random variables.  This subtype records the ordinary expectation boundary without
turning integrability into a theorem-head assumption. -/
abbrev IntegrableObservable : Type _ :=
  {g : Ω → ℝ // Integrable g setup.P}

/-- Ordinary expectation of a proof-carrying real observable.

This is a thin wrapper around Mathlib's Bochner integral.  The paper writes `E[...]`;
the subtype argument supplies the well-definedness proof that Lean's total integral
does not carry by itself. -/
noncomputable def expectation (g : setup.IntegrableObservable) : ℝ :=
  ∫ ω, g.1 ω ∂setup.P

/-- Integrability obligation for Lemma 6.13's terminal weighted potential.

The source states an ordinary `E_s[...]` expectation over the Algorithm 6.9
sample path.  This theorem records the well-definedness obligation for that
observable rather than letting Mathlib's total integral stand for the paper
expectation. -/
theorem ambientFixedWeightedPotential_integrable
    (z x0 : E) (xMem0 yMem0 : ι → E)
    (hz : z ∈ setup.X) (hx0 : x0 ∈ setup.X) (hxMem0 : ∀ i, xMem0 i ∈ setup.X)
    (t : ℕ) (ht : t ≤ setup.s) (xStar : E) :
    Integrable
      (setup.ambientFixedWeightedPotential z x0 xMem0 yMem0 hz hx0 hxMem0 t xStar)
      setup.P := by
  classical
  refine setup.ambientFixed_prefix_integrable_real 0 t ?_
  intro ω ω' hprefix
  have hstate :=
    setup.ambientFixedInnerProcess_prefix_const 0 z x0 xMem0 yMem0 hz hx0 t ht hprefix
  simp [ambientFixedWeightedPotential, ambientFixedX, ambientFixedXMem, hstate]

/-- Integrability obligation for fixed-inner-loop squared distance to `x*`.

This is used for the `E_s‖x* - xᵗ‖²` terms in Lemma 6.13 and Theorem 6.17. -/
theorem ambientFixedDistanceToOpt_integrable
    (z x0 : E) (xMem0 yMem0 : ι → E)
    (hz : z ∈ setup.X) (hx0 : x0 ∈ setup.X) (hxMem0 : ∀ i, xMem0 i ∈ setup.X)
    (t : ℕ) (ht : t ≤ setup.s) (xStar : E) :
    Integrable
      (fun ω : Ω =>
        ‖xStar - setup.ambientFixedX z x0 xMem0 yMem0 hz hx0 hxMem0 t ω‖ ^ 2)
      setup.P := by
  classical
  refine setup.ambientFixed_prefix_integrable_real 0 t ?_
  intro ω ω' hprefix
  have hx_eq :=
    setup.ambientFixedX_prefix_const z x0 xMem0 yMem0 hz hx0 hxMem0 t ht hprefix
  simp [hx_eq]

/-- Integrability obligation for fixed-inner-loop component-memory distance to `x*`.

This is the component observable in the right side of Lemma 6.13. -/
theorem ambientFixedMemoryDistanceToOpt_integrable
    (z x0 : E) (xMem0 yMem0 : ι → E)
    (hz : z ∈ setup.X) (hx0 : x0 ∈ setup.X) (hxMem0 : ∀ i, xMem0 i ∈ setup.X)
    (t : ℕ) (ht : t ≤ setup.s) (i : ι) (xStar : E) :
    Integrable
      (fun ω : Ω =>
        ‖setup.ambientFixedXMem z x0 xMem0 yMem0 hz hx0 hxMem0 t i ω - xStar‖ ^ 2)
      setup.P := by
  classical
  refine setup.ambientFixed_prefix_integrable_real 0 t ?_
  intro ω ω' hprefix
  have hstate :=
    setup.ambientFixedInnerProcess_prefix_const 0 z x0 xMem0 yMem0 hz hx0 t ht hprefix
  simp [ambientFixedXMem, hstate]

/-- Integrability obligation for Theorem 6.17's initial contraction observable
`‖x* - x⁰‖² + m⁻¹∑ᵢ‖xᵢ⁰ - x⁰‖²`. -/
theorem ambientFixedInitialContraction_integrable
    (z x0 : E) (xMem0 yMem0 : ι → E)
    (hz : z ∈ setup.X) (hx0 : x0 ∈ setup.X) (hxMem0 : ∀ i, xMem0 i ∈ setup.X)
    (xStar : E) :
    Integrable
      (fun ω : Ω =>
        ‖xStar - setup.ambientFixedX z x0 xMem0 yMem0 hz hx0 hxMem0 0 ω‖ ^ 2 +
          (Fintype.card ι : ℝ)⁻¹ *
            Finset.sum Finset.univ
              (fun i =>
                ‖setup.ambientFixedXMem z x0 xMem0 yMem0 hz hx0 hxMem0 0 i ω -
                  setup.ambientFixedX z x0 xMem0 yMem0 hz hx0 hxMem0 0 ω‖ ^ 2))
      setup.P := by
  classical
  letI : IsProbabilityMeasure setup.P := setup.hP
  have hzero := setup.ambientFixedInnerProcess_zero 0 z x0 xMem0 yMem0 hz hx0
  have hconst :
      (fun ω : Ω =>
        ‖xStar - setup.ambientFixedX z x0 xMem0 yMem0 hz hx0 hxMem0 0 ω‖ ^ 2 +
          (Fintype.card ι : ℝ)⁻¹ *
            Finset.sum Finset.univ
              (fun i =>
                ‖setup.ambientFixedXMem z x0 xMem0 yMem0 hz hx0 hxMem0 0 i ω -
                  setup.ambientFixedX z x0 xMem0 yMem0 hz hx0 hxMem0 0 ω‖ ^ 2)) =
        (fun _ : Ω =>
          ‖xStar - x0‖ ^ 2 +
            (Fintype.card ι : ℝ)⁻¹ *
              Finset.sum Finset.univ (fun i => ‖xMem0 i - x0‖ ^ 2)) := by
    funext ω
    simp [ambientFixedX, ambientFixedXMem, hzero ω]
  rw [hconst]
  exact MeasureTheory.integrable_const _

/-- Integrability obligation for Theorem 6.17's component-memory dispersion
observable `m⁻¹∑ᵢ‖xᵢᵗ - xᵗ‖²`. -/
theorem ambientFixedMemoryDispersion_integrable
    (z x0 : E) (xMem0 yMem0 : ι → E)
    (hz : z ∈ setup.X) (hx0 : x0 ∈ setup.X) (hxMem0 : ∀ i, xMem0 i ∈ setup.X)
    (t : ℕ) (ht : t ≤ setup.s) :
    Integrable
      (fun ω : Ω =>
        (Fintype.card ι : ℝ)⁻¹ *
          Finset.sum Finset.univ
            (fun i =>
              ‖setup.ambientFixedXMem z x0 xMem0 yMem0 hz hx0 hxMem0 t i ω -
                setup.ambientFixedX z x0 xMem0 yMem0 hz hx0 hxMem0 t ω‖ ^ 2))
      setup.P := by
  classical
  refine setup.ambientFixed_prefix_integrable_real 0 t ?_
  intro ω ω' hprefix
  have hstate :=
    setup.ambientFixedInnerProcess_prefix_const 0 z x0 xMem0 yMem0 hz hx0 t ht hprefix
  simp [ambientFixedX, ambientFixedXMem, hstate]

/-- Proof-carrying terminal weighted-potential observable for Lemma 6.13. -/
noncomputable def ambientFixedWeightedPotentialObservable
    (z x0 : E) (xMem0 yMem0 : ι → E)
    (hz : z ∈ setup.X) (hx0 : x0 ∈ setup.X) (hxMem0 : ∀ i, xMem0 i ∈ setup.X)
    (t : ℕ) (ht : t ≤ setup.s) (xStar : E) : setup.IntegrableObservable :=
  ⟨setup.ambientFixedWeightedPotential z x0 xMem0 yMem0 hz hx0 hxMem0 t xStar,
    setup.ambientFixedWeightedPotential_integrable
      z x0 xMem0 yMem0 hz hx0 hxMem0 t ht xStar⟩

/-- Proof-carrying fixed-inner-loop squared-distance observable. -/
noncomputable def ambientFixedDistanceToOptObservable
    (z x0 : E) (xMem0 yMem0 : ι → E)
    (hz : z ∈ setup.X) (hx0 : x0 ∈ setup.X) (hxMem0 : ∀ i, xMem0 i ∈ setup.X)
    (t : ℕ) (ht : t ≤ setup.s) (xStar : E) : setup.IntegrableObservable :=
  ⟨fun ω : Ω =>
      ‖xStar - setup.ambientFixedX z x0 xMem0 yMem0 hz hx0 hxMem0 t ω‖ ^ 2,
    setup.ambientFixedDistanceToOpt_integrable
      z x0 xMem0 yMem0 hz hx0 hxMem0 t ht xStar⟩

/-- Proof-carrying component-memory squared-distance observable. -/
noncomputable def ambientFixedMemoryDistanceToOptObservable
    (z x0 : E) (xMem0 yMem0 : ι → E)
    (hz : z ∈ setup.X) (hx0 : x0 ∈ setup.X) (hxMem0 : ∀ i, xMem0 i ∈ setup.X)
    (t : ℕ) (ht : t ≤ setup.s) (i : ι) (xStar : E) : setup.IntegrableObservable :=
  ⟨fun ω : Ω =>
      ‖setup.ambientFixedXMem z x0 xMem0 yMem0 hz hx0 hxMem0 t i ω - xStar‖ ^ 2,
    setup.ambientFixedMemoryDistanceToOpt_integrable
      z x0 xMem0 yMem0 hz hx0 hxMem0 t ht i xStar⟩

/-- Proof-carrying initial contraction observable for Theorem 6.17. -/
noncomputable def ambientFixedInitialContractionObservable
    (z x0 : E) (xMem0 yMem0 : ι → E)
    (hz : z ∈ setup.X) (hx0 : x0 ∈ setup.X) (hxMem0 : ∀ i, xMem0 i ∈ setup.X)
    (xStar : E) : setup.IntegrableObservable :=
  ⟨fun ω : Ω =>
      ‖xStar - setup.ambientFixedX z x0 xMem0 yMem0 hz hx0 hxMem0 0 ω‖ ^ 2 +
        (Fintype.card ι : ℝ)⁻¹ *
          Finset.sum Finset.univ
            (fun i =>
              ‖setup.ambientFixedXMem z x0 xMem0 yMem0 hz hx0 hxMem0 0 i ω -
                setup.ambientFixedX z x0 xMem0 yMem0 hz hx0 hxMem0 0 ω‖ ^ 2),
    setup.ambientFixedInitialContraction_integrable
      z x0 xMem0 yMem0 hz hx0 hxMem0 xStar⟩

/-- Proof-carrying component-memory dispersion observable for Theorem 6.17. -/
noncomputable def ambientFixedMemoryDispersionObservable
    (z x0 : E) (xMem0 yMem0 : ι → E)
    (hz : z ∈ setup.X) (hx0 : x0 ∈ setup.X) (hxMem0 : ∀ i, xMem0 i ∈ setup.X)
    (t : ℕ) (ht : t ≤ setup.s) : setup.IntegrableObservable :=
  ⟨fun ω : Ω =>
      (Fintype.card ι : ℝ)⁻¹ *
        Finset.sum Finset.univ
          (fun i =>
            ‖setup.ambientFixedXMem z x0 xMem0 yMem0 hz hx0 hxMem0 t i ω -
              setup.ambientFixedX z x0 xMem0 yMem0 hz hx0 hxMem0 t ω‖ ^ 2),
    setup.ambientFixedMemoryDispersion_integrable z x0 xMem0 yMem0 hz hx0 hxMem0 t ht⟩

/-! Arbitrary-memory fixed-run observables.

The ambient Algorithm 6.9 realization above does not require component memories
`xᵢ⁰` to lie in `X`; only the proximal iterate `x⁰` and center `z` must be
feasible so that the constrained prox step is meaningful.  Algorithm 6.8 sets
the next subproblem's component memories to the previous RaGrad component
outputs, and Eq. (6.6.10) is not closed under a merely closed convex set.  These
observables are the corrected fixed-run boundary consumed by the outer Lemma 6.14
bridge: they use the same ambient recursion but do not ask for a false generated
memory feasibility invariant.
-/

/-- Ambient fixed-subproblem primal iterate with arbitrary initial component
memories.  No SOptLib match: searched `fixed process arbitrary memory observable
distance integrability finite prefix` and `recursive process finite prefix
integrable observable memory dispersion`; the exact primitive is this paper's
`ambientFixedInnerProcess`, which already omits any component-memory feasibility
premise. -/
noncomputable def ambientFixedXAnyMem
    (z x0 : E) (xMem0 yMem0 : ι → E)
    (hz : z ∈ setup.X) (hx0 : x0 ∈ setup.X)
    (t : ℕ) : Ω → E :=
  fun ω => (setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 t ω).x

/-- Ambient fixed-subproblem component memory with arbitrary initial component
memories. -/
noncomputable def ambientFixedXMemAnyMem
    (z x0 : E) (xMem0 yMem0 : ι → E)
    (hz : z ∈ setup.X) (hx0 : x0 ∈ setup.X)
    (t : ℕ) (i : ι) : Ω → E :=
  fun ω => (setup.ambientFixedInnerProcess 0 z x0 xMem0 yMem0 hz hx0 t ω).xMem i

/-- Fixed-run squared-distance integrability for arbitrary initial memories. -/
theorem ambientFixedDistanceToOptAnyMem_integrable
    (z x0 : E) (xMem0 yMem0 : ι → E)
    (hz : z ∈ setup.X) (hx0 : x0 ∈ setup.X)
    (t : ℕ) (ht : t ≤ setup.s) (xStar : E) :
    Integrable
      (fun ω : Ω =>
        ‖xStar - setup.ambientFixedXAnyMem z x0 xMem0 yMem0 hz hx0 t ω‖ ^ 2)
      setup.P := by
  classical
  refine setup.ambientFixed_prefix_integrable_real 0 t ?_
  intro ω ω' hprefix
  have hstate :=
    setup.ambientFixedInnerProcess_prefix_const 0 z x0 xMem0 yMem0 hz hx0 t ht hprefix
  simp [ambientFixedXAnyMem, hstate]

/-- Fixed-run component-memory squared-distance integrability for arbitrary
initial memories. -/
theorem ambientFixedMemoryDistanceToOptAnyMem_integrable
    (z x0 : E) (xMem0 yMem0 : ι → E)
    (hz : z ∈ setup.X) (hx0 : x0 ∈ setup.X)
    (t : ℕ) (ht : t ≤ setup.s) (i : ι) (xStar : E) :
    Integrable
      (fun ω : Ω =>
        ‖setup.ambientFixedXMemAnyMem z x0 xMem0 yMem0 hz hx0 t i ω - xStar‖ ^ 2)
      setup.P := by
  classical
  refine setup.ambientFixed_prefix_integrable_real 0 t ?_
  intro ω ω' hprefix
  have hstate :=
    setup.ambientFixedInnerProcess_prefix_const 0 z x0 xMem0 yMem0 hz hx0 t ht hprefix
  simp [ambientFixedXMemAnyMem, hstate]

/-- Initial contraction integrability for arbitrary initial component memories. -/
theorem ambientFixedInitialContractionAnyMem_integrable
    (z x0 : E) (xMem0 yMem0 : ι → E)
    (hz : z ∈ setup.X) (hx0 : x0 ∈ setup.X)
    (xStar : E) :
    Integrable
      (fun ω : Ω =>
        ‖xStar - setup.ambientFixedXAnyMem z x0 xMem0 yMem0 hz hx0 0 ω‖ ^ 2 +
          (Fintype.card ι : ℝ)⁻¹ *
            Finset.sum Finset.univ
              (fun i =>
                ‖setup.ambientFixedXMemAnyMem z x0 xMem0 yMem0 hz hx0 0 i ω -
                  setup.ambientFixedXAnyMem z x0 xMem0 yMem0 hz hx0 0 ω‖ ^ 2))
      setup.P := by
  classical
  letI : IsProbabilityMeasure setup.P := setup.hP
  have hzero := setup.ambientFixedInnerProcess_zero 0 z x0 xMem0 yMem0 hz hx0
  have hconst :
      (fun ω : Ω =>
        ‖xStar - setup.ambientFixedXAnyMem z x0 xMem0 yMem0 hz hx0 0 ω‖ ^ 2 +
          (Fintype.card ι : ℝ)⁻¹ *
            Finset.sum Finset.univ
              (fun i =>
                ‖setup.ambientFixedXMemAnyMem z x0 xMem0 yMem0 hz hx0 0 i ω -
                  setup.ambientFixedXAnyMem z x0 xMem0 yMem0 hz hx0 0 ω‖ ^ 2)) =
        (fun _ : Ω =>
          ‖xStar - x0‖ ^ 2 +
            (Fintype.card ι : ℝ)⁻¹ *
              Finset.sum Finset.univ (fun i => ‖xMem0 i - x0‖ ^ 2)) := by
    funext ω
    simp [ambientFixedXAnyMem, ambientFixedXMemAnyMem, hzero ω]
  rw [hconst]
  exact MeasureTheory.integrable_const _

/-- Component-memory dispersion integrability for arbitrary initial memories. -/
theorem ambientFixedMemoryDispersionAnyMem_integrable
    (z x0 : E) (xMem0 yMem0 : ι → E)
    (hz : z ∈ setup.X) (hx0 : x0 ∈ setup.X)
    (t : ℕ) (ht : t ≤ setup.s) :
    Integrable
      (fun ω : Ω =>
        (Fintype.card ι : ℝ)⁻¹ *
          Finset.sum Finset.univ
            (fun i =>
              ‖setup.ambientFixedXMemAnyMem z x0 xMem0 yMem0 hz hx0 t i ω -
                setup.ambientFixedXAnyMem z x0 xMem0 yMem0 hz hx0 t ω‖ ^ 2))
      setup.P := by
  classical
  refine setup.ambientFixed_prefix_integrable_real 0 t ?_
  intro ω ω' hprefix
  have hstate :=
    setup.ambientFixedInnerProcess_prefix_const 0 z x0 xMem0 yMem0 hz hx0 t ht hprefix
  simp [ambientFixedXAnyMem, ambientFixedXMemAnyMem, hstate]

/-- Proof-carrying fixed-inner-loop squared-distance observable with arbitrary
initial component memories. -/
noncomputable def ambientFixedDistanceToOptAnyMemObservable
    (z x0 : E) (xMem0 yMem0 : ι → E)
    (hz : z ∈ setup.X) (hx0 : x0 ∈ setup.X)
    (t : ℕ) (ht : t ≤ setup.s) (xStar : E) : setup.IntegrableObservable :=
  ⟨fun ω : Ω =>
      ‖xStar - setup.ambientFixedXAnyMem z x0 xMem0 yMem0 hz hx0 t ω‖ ^ 2,
    setup.ambientFixedDistanceToOptAnyMem_integrable
      z x0 xMem0 yMem0 hz hx0 t ht xStar⟩

/-- Proof-carrying component-memory squared-distance observable with arbitrary
initial component memories. -/
noncomputable def ambientFixedMemoryDistanceToOptAnyMemObservable
    (z x0 : E) (xMem0 yMem0 : ι → E)
    (hz : z ∈ setup.X) (hx0 : x0 ∈ setup.X)
    (t : ℕ) (ht : t ≤ setup.s) (i : ι) (xStar : E) : setup.IntegrableObservable :=
  ⟨fun ω : Ω =>
      ‖setup.ambientFixedXMemAnyMem z x0 xMem0 yMem0 hz hx0 t i ω - xStar‖ ^ 2,
    setup.ambientFixedMemoryDistanceToOptAnyMem_integrable
      z x0 xMem0 yMem0 hz hx0 t ht i xStar⟩

/-- Proof-carrying initial contraction observable with arbitrary initial
component memories. -/
noncomputable def ambientFixedInitialContractionAnyMemObservable
    (z x0 : E) (xMem0 yMem0 : ι → E)
    (hz : z ∈ setup.X) (hx0 : x0 ∈ setup.X)
    (xStar : E) : setup.IntegrableObservable :=
  ⟨fun ω : Ω =>
      ‖xStar - setup.ambientFixedXAnyMem z x0 xMem0 yMem0 hz hx0 0 ω‖ ^ 2 +
        (Fintype.card ι : ℝ)⁻¹ *
          Finset.sum Finset.univ
            (fun i =>
              ‖setup.ambientFixedXMemAnyMem z x0 xMem0 yMem0 hz hx0 0 i ω -
                setup.ambientFixedXAnyMem z x0 xMem0 yMem0 hz hx0 0 ω‖ ^ 2),
    setup.ambientFixedInitialContractionAnyMem_integrable
      z x0 xMem0 yMem0 hz hx0 xStar⟩

/-- Proof-carrying component-memory dispersion observable with arbitrary initial
component memories. -/
noncomputable def ambientFixedMemoryDispersionAnyMemObservable
    (z x0 : E) (xMem0 yMem0 : ι → E)
    (hz : z ∈ setup.X) (hx0 : x0 ∈ setup.X)
    (t : ℕ) (ht : t ≤ setup.s) : setup.IntegrableObservable :=
  ⟨fun ω : Ω =>
      (Fintype.card ι : ℝ)⁻¹ *
        Finset.sum Finset.univ
          (fun i =>
            ‖setup.ambientFixedXMemAnyMem z x0 xMem0 yMem0 hz hx0 t i ω -
              setup.ambientFixedXAnyMem z x0 xMem0 yMem0 hz hx0 t ω‖ ^ 2),
    setup.ambientFixedMemoryDispersionAnyMem_integrable z x0 xMem0 yMem0 hz hx0 t ht⟩

/-- Integrand for Definition 6.1's stochastic stationarity criterion. -/
noncomputable def stochasticStationarityIntegrand (xHat : Ω → E) : Ω → ℝ :=
  SOptLib.normalConeStationarityGapIntegrand setup.X setup.normalConeGapOn xHat

/-- Integrand for Definition 6.1's stochastic proximity criterion. -/
noncomputable def stochasticProximityIntegrand (x xHat : Ω → E) : Ω → ℝ :=
  SOptLib.squaredProximityIntegrand x xHat

/-- Definition 6.1 stochastic `(ε, δ)`-solution predicate.

The source states ordinary expectations.  Since Mathlib's integral is total, this
definition packages the needed integrability facts inside the stochastic-solution
predicate itself rather than adding them as separate theorem assumptions. -/
noncomputable def stochasticApproximateSolution (ε δ : ℝ) (x xHat : Ω → E) : Prop :=
  SOptLib.StochasticApproximateSolution setup.P setup.X setup.normalConeGapOn ε δ x xHat

/-- The weighted potential used in the Lemma 6.13 recursion:
`Γₜ = γₜ(1 + ηₜ)Vφ(x*, xᵗ) + ∑ᵢ (μγₜ(1+τₜ)/4)‖xᵢᵗ − x*‖²`. -/
noncomputable def weightedPotential (ℓ t : ℕ) (xStar : Ω → E) : Ω → ℝ :=
  fun ω =>
    setup.γSeq t * (1 + setup.ηSeq t) *
        ((setup.μ / 2) * ‖setup.xInnerIter ℓ t ω - xStar ω‖ ^ 2) +
      Finset.sum Finset.univ
        (fun i =>
          setup.μ * setup.γSeq t * (1 + setup.τSeq t) / 4 *
            ‖setup.xMemIter ℓ t i ω - xStar ω‖ ^ 2)

/-- The global optimizer `x*` of problem (6.6.1), as named in Theorem 6.16.

`SOptLib.argminSelectorOfSource` and `SOptLib.selectedOptimizer` were checked; they
wrap an already supplied optimizer witness.  Theorem 6.16 itself supplies `x*` as
the optimal-solution datum, so the paper-facing object is the setup field rather
than a derived global-attainment theorem. -/
noncomputable def globalOpt : E :=
  setup.xStar

/-- The selected global optimizer lies in `X`. -/
theorem globalOpt_mem : setup.globalOpt ∈ setup.X := by
  simpa [globalOpt] using setup.hxStar_mem

/-- The selected global optimizer minimizes the finite-sum objective on `X`. -/
theorem globalOpt_is_minimizer :
    ∀ z : {x : E // x ∈ setup.X}, setup.fAvgOn ⟨setup.globalOpt, setup.globalOpt_mem⟩ ≤
      setup.fAvgOn z := by
  intro z
  simpa [globalOpt, fAvgOn] using setup.hxStar_min z

/-- Source-domain objective of the exact proximal subproblem (6.6.7)/(6.6.8)
at outer index `ℓ`.

`SOptLib.compositeObjective` and `SOptLib.compositeObjectiveAmbient` were checked;
they model generic pointwise sums, while Eq. (6.6.8) fixes the finite average of
the generated `ψ_i^ℓ` plus the quadratic `φ^ℓ` over `x ∈ X`. -/
noncomputable def subproblemObjectiveOn
    (ℓ : ℕ) (ω : Ω) (x : {x : E // x ∈ setup.X}) : ℝ :=
  SOptLib.finiteAverageRegularizedObjectiveOn
    (fun i x => setup.psiOn ℓ i ω x) (fun x => setup.phi ℓ ω x.1) x

/-- Internal ambient compatibility wrapper for the exact proximal subproblem.

The paper-facing objective is `subproblemObjectiveOn`, whose argument carries
`x ∈ X`; this wrapper is retained only for bridge statements over ambient sets. -/
noncomputable def subproblemObjective (ℓ : ℕ) (ω : Ω) (x : E) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ (fun i => setup.psi ℓ i ω x) +
    setup.phi ℓ ω x

/-- Feasible-point rewrite for the ambient subproblem-objective wrapper. -/
@[simp]
theorem subproblemObjective_of_mem (ℓ : ℕ) (ω : Ω) {x : E} (hx : x ∈ setup.X) :
    setup.subproblemObjective ℓ ω x = setup.subproblemObjectiveOn ℓ ω ⟨x, hx⟩ := by
  rw [subproblemObjective, subproblemObjectiveOn]
  congr 1
  exact congrArg (fun s : ℝ => (Fintype.card ι : ℝ)⁻¹ * s)
    (Finset.sum_congr rfl (fun i _ => setup.psi_of_mem ℓ i ω hx))

/-- Continuity on `X` of the ambient wrapper for the exact proximal subproblem.

Aligns with Eq. (6.6.8): the finite average of generated `ψ_i^ℓ` terms is
continuous within `X` from `gradPsiOnAt_hasGradientWithinAt`, and the quadratic
`φ^ℓ` is globally continuous.  Considered `SOptLib.compositeObjective` and
`finiteAverageObjective_hasGradientAt`; the former is only a generic pointwise
constructor and the latter needs global `HasGradientAt`, while this paper only
provides within-gradients on the feasible carrier. -/
theorem subproblemObjective_continuousOn (ℓ : ℕ) (ω : Ω) :
    ContinuousOn (setup.subproblemObjective ℓ ω) setup.X := by
  intro x hx
  have hsum_deriv : HasFDerivWithinAt
      (fun y : E => Finset.sum Finset.univ (fun i => setup.psi ℓ i ω y))
      (Finset.sum Finset.univ
        (fun i : ι =>
          InnerProductSpace.toDual ℝ E
            (setup.gradPsiOnAt (setup.outerCenter ℓ ω) i ⟨x, hx⟩)))
      setup.X x := by
    refine HasFDerivWithinAt.fun_sum ?_
    intro i _hi
    simpa [RandomizedAcceleratedProximalPointSetup.psi] using
      (setup.gradPsiOnAt_hasGradientWithinAt
        (setup.outerCenter ℓ ω) i ⟨x, hx⟩).hasFDerivWithinAt
  have hsum : ContinuousWithinAt
      (fun y : E => Finset.sum Finset.univ (fun i => setup.psi ℓ i ω y)) setup.X x :=
    hsum_deriv.continuousWithinAt
  have hscaled : ContinuousWithinAt
      (fun y : E =>
        (Fintype.card ι : ℝ)⁻¹ * Finset.sum Finset.univ (fun i => setup.psi ℓ i ω y))
      setup.X x := by
    exact continuousWithinAt_const.mul hsum
  have hphi : ContinuousWithinAt (fun y : E => setup.phi ℓ ω y) setup.X x := by
    have hphi_global : Continuous (fun y : E => setup.phiAt (setup.outerCenter ℓ ω) y) := by
      unfold RandomizedAcceleratedProximalPointSetup.phiAt
      exact continuous_const.mul (((continuous_id.sub continuous_const).norm).pow 2)
    simpa [RandomizedAcceleratedProximalPointSetup.phi] using hphi_global.continuousWithinAt
  unfold RandomizedAcceleratedProximalPointSetup.subproblemObjective
  exact hscaled.add hphi

/-- Existence obligation for the exact optimizer `x_ℓ^*` of the generated proximal
subproblem on the paper output window `ℓ ∈ {1, ..., k}`.

The JSON/PDF state that these are optimal solutions but do not give compactness or
coercivity assumptions as theorem-head regularity facts, so solvability remains a
named proof obligation. -/
theorem subproblemOpt_exists (ℓ : ℕ) (hℓ : ℓ ∈ Finset.Icc 1 (setup.k : ℕ)) (ω : Ω) :
    ∃ x : {x : E // x ∈ setup.X},
      IsMinOn (setup.subproblemObjectiveOn ℓ ω) Set.univ x := by
  classical
  let zc := setup.outerCenter ℓ ω
  let F : E → ℝ := setup.subproblemObjective ℓ ω
  have hcont : ContinuousOn F setup.X := by
    simpa [F] using setup.subproblemObjective_continuousOn ℓ ω
  have hcoerc : ∀ B : ℝ, ∃ R : ℝ, ‖setup.x₀ - zc‖ ≤ R ∧
      ∀ x : E, x ∈ setup.X → R ≤ ‖x - zc‖ → B ≤ F x := by
    refine finite_average_quadratic_regularized_coercive_lower_tail
      (X := setup.X) (x0 := setup.x₀) (z := zc) (μ := setup.μ)
      (f := setup.f) (grad0 := fun i : ι => setup.gradf i ⟨setup.x₀, setup.hx₀_mem⟩)
      (F := F) setup.hx₀_mem setup.hμ_pos ?_ ?_
    · intro i x hx
      let xBase : {x : E // x ∈ setup.X} := ⟨setup.x₀, setup.hx₀_mem⟩
      have hone := setup.hone_sided i ⟨x, hx⟩ xBase
      have hinner_abs :
          |⟪setup.gradf i xBase, x - setup.x₀⟫_ℝ| ≤
            ‖setup.gradf i xBase‖ * ‖x - setup.x₀‖ :=
        abs_real_inner_le_norm (setup.gradf i xBase) (x - setup.x₀)
      have hinner_lower :
          -(‖setup.gradf i xBase‖ * ‖x - setup.x₀‖) ≤
            ⟪setup.gradf i xBase, x - setup.x₀⟫_ℝ := by
        have hneg_abs :
            -⟪setup.gradf i xBase, x - setup.x₀⟫_ℝ ≤
              |⟪setup.gradf i xBase, x - setup.x₀⟫_ℝ| := neg_le_abs _
        linarith
      simp [RandomizedAcceleratedProximalPointSetup.gradf,
        RandomizedAcceleratedProximalPointSetup.fAmbient, xBase] at hone hinner_lower ⊢
      nlinarith
    · intro x hx
      let r : ℝ := ‖x - zc‖
      have hcard_nat : 0 < Fintype.card ι := Fintype.card_pos
      have hcard_real_pos : 0 < (Fintype.card ι : ℝ) := by
        exact_mod_cast hcard_nat
      have hcard_real_ne : (Fintype.card ι : ℝ) ≠ 0 := ne_of_gt hcard_real_pos
      have hF_expand :
          F x = (Fintype.card ι : ℝ)⁻¹ *
                Finset.sum Finset.univ (fun i : ι => setup.f i ⟨x, hx⟩) +
              setup.μ * r ^ 2 + (setup.μ / 2) * r ^ 2 := by
        let q : ℝ := setup.μ * r ^ 2
        let p : ℝ := (setup.μ / 2) * r ^ 2
        have hsum_psi :
            Finset.sum Finset.univ (fun i : ι => setup.psi ℓ i ω x) =
              Finset.sum Finset.univ (fun i : ι => setup.f i ⟨x, hx⟩ + q) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          rw [RandomizedAcceleratedProximalPointSetup.psi,
            RandomizedAcceleratedProximalPointSetup.psiAt]
          rw [setup.fAmbient_of_mem i hx]
        have hsum_split :
            Finset.sum Finset.univ (fun i : ι => setup.f i ⟨x, hx⟩ + q) =
              Finset.sum Finset.univ (fun i : ι => setup.f i ⟨x, hx⟩) +
                (Fintype.card ι : ℝ) * q := by
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
          simp
        calc
          F x =
              (Fintype.card ι : ℝ)⁻¹ *
                  Finset.sum Finset.univ (fun i : ι => setup.psi ℓ i ω x) +
                setup.phi ℓ ω x := by
            rfl
          _ =
              (Fintype.card ι : ℝ)⁻¹ *
                  (Finset.sum Finset.univ (fun i : ι => setup.f i ⟨x, hx⟩) +
                    (Fintype.card ι : ℝ) * q) +
                p := by
            rw [hsum_psi, hsum_split, RandomizedAcceleratedProximalPointSetup.phi,
              RandomizedAcceleratedProximalPointSetup.phiAt,
              SOptLib.centeredQuadraticPotential]
          _ =
              (Fintype.card ι : ℝ)⁻¹ *
                  Finset.sum Finset.univ (fun i : ι => setup.f i ⟨x, hx⟩) +
                q + p := by
            rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hcard_real_ne, one_mul]
          _ =
              (Fintype.card ι : ℝ)⁻¹ *
                  Finset.sum Finset.univ (fun i : ι => setup.f i ⟨x, hx⟩) +
                setup.μ * r ^ 2 + (setup.μ / 2) * r ^ 2 := by
            rfl
      exact le_of_eq hF_expand.symm
  obtain ⟨xmin, hxmin_mem, hxmin_min⟩ :=
    exists_isMinOn_closed_of_coercive_on_closedBall
      setup.hX_closed setup.x₀ zc setup.hx₀_mem F hcont hcoerc
  refine ⟨⟨xmin, hxmin_mem⟩, ?_⟩
  intro y _
  have hyF : F xmin ≤ F y.1 := hxmin_min y.2
  have hy : setup.subproblemObjective ℓ ω xmin ≤ setup.subproblemObjective ℓ ω y.1 := by
    simpa [F] using hyF
  calc
    setup.subproblemObjectiveOn ℓ ω ⟨xmin, hxmin_mem⟩ =
        setup.subproblemObjective ℓ ω xmin := by
          exact (setup.subproblemObjective_of_mem ℓ ω hxmin_mem).symm
    _ ≤ setup.subproblemObjective ℓ ω y.1 := hy
    _ = setup.subproblemObjectiveOn ℓ ω y := by
          exact setup.subproblemObjective_of_mem ℓ ω y.2

/-- Canonically selected exact proximal subproblem optimizer `x_ℓ^*` as a point
of the source domain `X`.

`SOptLib.ObjectiveMinimum` and `argminSelectorOfSource` were considered, but they
bundle externally supplied optimizer data.  Theorem 6.16's paper object is the exact
optimizer family for the generated subproblems, selected here from the local
source-backed solvability theorem. -/
noncomputable def subproblemOptOn
    (ℓ : ℕ) (hℓ : ℓ ∈ Finset.Icc 1 (setup.k : ℕ)) :
    Ω → {x : E // x ∈ setup.X} :=
  fun ω => Classical.choose (setup.subproblemOpt_exists ℓ hℓ ω)

/-- Ambient point projection of the selected exact proximal subproblem optimizer. -/
noncomputable def subproblemOpt (ℓ : ℕ) (hℓ : ℓ ∈ Finset.Icc 1 (setup.k : ℕ)) : Ω → E :=
  fun ω => (setup.subproblemOptOn ℓ hℓ ω).1

/-- The selected exact proximal subproblem optimizer lies in `X`. -/
theorem subproblemOpt_mem (ℓ : ℕ) (hℓ : ℓ ∈ Finset.Icc 1 (setup.k : ℕ)) :
    ∀ ω : Ω, setup.subproblemOpt ℓ hℓ ω ∈ setup.X := by
  intro ω
  exact (setup.subproblemOptOn ℓ hℓ ω).2

/-- The selected exact proximal subproblem optimizer minimizes the source-domain
(6.6.7)/(6.6.8) objective. -/
theorem subproblemOptOn_is_minimizer (ℓ : ℕ) (hℓ : ℓ ∈ Finset.Icc 1 (setup.k : ℕ)) :
    ∀ ω, IsMinOn (setup.subproblemObjectiveOn ℓ ω) Set.univ
      (setup.subproblemOptOn ℓ hℓ ω) := by
  intro ω
  exact Classical.choose_spec (setup.subproblemOpt_exists ℓ hℓ ω)

/-- Ambient bridge for the selected exact proximal subproblem optimizer. -/
theorem subproblemOpt_is_minimizer (ℓ : ℕ) (hℓ : ℓ ∈ Finset.Icc 1 (setup.k : ℕ)) :
    ∀ ω, IsMinOn (setup.subproblemObjective ℓ ω) setup.X
      (setup.subproblemOpt ℓ hℓ ω) := by
  classical
  intro ω y hy
  have hmin := setup.subproblemOptOn_is_minimizer ℓ hℓ ω
  have hle := hmin (a := ⟨y, hy⟩) (by simp)
  have hopt : setup.subproblemOpt ℓ hℓ ω ∈ setup.X := setup.subproblemOpt_mem ℓ hℓ ω
  calc
    setup.subproblemObjective ℓ ω (setup.subproblemOpt ℓ hℓ ω)
        = setup.subproblemObjectiveOn ℓ ω ⟨setup.subproblemOpt ℓ hℓ ω, hopt⟩ :=
          setup.subproblemObjective_of_mem ℓ ω hopt
    _ = setup.subproblemObjectiveOn ℓ ω (setup.subproblemOptOn ℓ hℓ ω) := by
          simp [subproblemOpt]
    _ ≤ setup.subproblemObjectiveOn ℓ ω ⟨y, hy⟩ := hle
    _ = setup.subproblemObjective ℓ ω y := (setup.subproblemObjective_of_mem ℓ ω hy).symm

/-- Equal generated centers give the same exact proximal subproblem objective.

This is the Eq. (6.6.8) bridge needed for finite-prefix determinism of the
paper's selected exact optimizer.  The SOptLib composite-objective candidates are
too abstract for this literal generated-center formula, so the proof unfolds the
local `ψ_i^ℓ` and `φ^ℓ` definitions. -/
theorem subproblemObjectiveOn_eq_of_outerCenter_eq
    (ℓ : ℕ) {ω ω' : Ω}
    (hcenter : setup.outerCenter ℓ ω = setup.outerCenter ℓ ω') :
    setup.subproblemObjectiveOn ℓ ω = setup.subproblemObjectiveOn ℓ ω' := by
  funext x
  simp [subproblemObjectiveOn, psiOn, phi, psiAtOn, phiAt, hcenter]

/-- `Classical.choose` for an existential predicate is invariant under predicate
equality, up to proof irrelevance of the two existence proofs. -/
theorem choose_exists_eq_of_pred_eq
    {α : Type*} {p q : α → Prop} (hpq : p = q)
    (hp : ∃ x, p x) (hq : ∃ x, q x) :
    Classical.choose hp = Classical.choose hq := by
  cases hpq
  congr

/-- The canonical exact proximal optimizer is stable under equality of the
generated subproblem center.

This consumes the local objective-equality bridge above.  SOptLib argmin selector
helpers were checked but model externally supplied selectors or abstract prox
objects; here the selector is the `Classical.choose` value from the source-backed
`subproblemOpt_exists` theorem for Eq. (6.6.8). -/
theorem subproblemOptOn_const_of_outerCenter_eq
    (ℓ : ℕ) (hℓ : ℓ ∈ Finset.Icc 1 (setup.k : ℕ)) {ω ω' : Ω}
    (hcenter : setup.outerCenter ℓ ω = setup.outerCenter ℓ ω') :
    setup.subproblemOptOn ℓ hℓ ω = setup.subproblemOptOn ℓ hℓ ω' := by
  classical
  have hobj := setup.subproblemObjectiveOn_eq_of_outerCenter_eq ℓ hcenter
  unfold subproblemOptOn
  exact choose_exists_eq_of_pred_eq
    (α := {x : E // x ∈ setup.X})
    (p := fun x => IsMinOn (setup.subproblemObjectiveOn ℓ ω) Set.univ x)
    (q := fun x => IsMinOn (setup.subproblemObjectiveOn ℓ ω') Set.univ x)
    (by
      funext x
      rw [hobj])
    (setup.subproblemOpt_exists ℓ hℓ ω)
    (setup.subproblemOpt_exists ℓ hℓ ω')

/-- Ambient projection of exact proximal optimizer stability under equal generated
centers. -/
theorem subproblemOpt_const_of_outerCenter_eq
    (ℓ : ℕ) (hℓ : ℓ ∈ Finset.Icc 1 (setup.k : ℕ)) {ω ω' : Ω}
    (hcenter : setup.outerCenter ℓ ω = setup.outerCenter ℓ ω') :
    setup.subproblemOpt ℓ hℓ ω = setup.subproblemOpt ℓ hℓ ω' := by
  exact congrArg Subtype.val
    (setup.subproblemOptOn_const_of_outerCenter_eq ℓ hℓ hcenter)

/-- The exact proximal optimizer at paper index `ℓ` is determined by the first
`ℓ * s` samples of the global stream. -/
theorem subproblemOpt_prefix_const
    (ℓ : ℕ) (hℓ : ℓ ∈ Finset.Icc 1 (setup.k : ℕ)) :
    ∀ ⦃ω ω' : Ω⦄,
      (fun r : Fin (ℓ * setup.s) => setup.ξ r.1 ω) =
        (fun r : Fin (ℓ * setup.s) => setup.ξ r.1 ω') →
      setup.subproblemOpt ℓ hℓ ω = setup.subproblemOpt ℓ hℓ ω' := by
  classical
  intro ω ω' hprefix
  have hbounds := Finset.mem_Icc.mp hℓ
  have hpos : 0 < ℓ := lt_of_lt_of_le Nat.zero_lt_one hbounds.1
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  have hmle : m ≤ (setup.k : ℕ) := by
    exact Nat.le_of_succ_le (by simpa [hm] using hbounds.2)
  have hprevPrefix :
      (fun r : Fin (m * setup.s) => setup.ξ r.1 ω) =
        (fun r : Fin (m * setup.s) => setup.ξ r.1 ω') := by
    funext r
    exact congrFun hprefix
      ⟨r.1, Nat.lt_of_lt_of_le r.2
        (by
          rw [hm]
          simpa [Nat.succ_mul] using
            Nat.le_add_right (m * setup.s) setup.s)⟩
  have hxbar : setup.xBarIter m ω = setup.xBarIter m ω' :=
    setup.xBarIter_prefix_const m hmle hprevPrefix
  have hcenter : setup.outerCenter ℓ ω = setup.outerCenter ℓ ω' := by
    rw [hm]
    simpa [outerCenter] using hxbar
  exact setup.subproblemOpt_const_of_outerCenter_eq ℓ hℓ hcenter

/-- Exact proximal subproblem optimizer at a bounded paper output index. -/
noncomputable def subproblemOptOutput (ℓ : setup.OutputIndex) : Ω → E :=
  setup.subproblemOpt ℓ.1 (by simpa [outputWindow] using ℓ.2)

/-- The bounded exact proximal subproblem optimizer lies in `X`. -/
theorem subproblemOptOutput_mem (ℓ : setup.OutputIndex) :
    ∀ ω : Ω, setup.subproblemOptOutput ℓ ω ∈ setup.X := by
  intro ω
  simpa [subproblemOptOutput] using
    setup.subproblemOpt_mem ℓ.1 (by simpa [outputWindow] using ℓ.2) ω

/-- Generated outer iterate on the paper output window `ℓ ∈ [k]`. -/
noncomputable def xBarOutput (ℓ : setup.OutputIndex) : Ω → E :=
  setup.xBarIter ℓ.1

/-- Generated inner primal iterate on the bounded source window of Algorithms 6.8
and 6.9. -/
noncomputable def xInnerIterAt (ℓ : setup.OutputIndex) (t : setup.InnerIndex) : Ω → E :=
  setup.xInnerIter ℓ.1 t.1

/-- Generated inner primal iterates are feasible on the bounded Algorithm 6.9
source window. -/
theorem xInnerIterAt_mem (ℓ : setup.OutputIndex) (t : setup.InnerIndex) :
    ∀ ω : Ω, setup.xInnerIterAt ℓ t ω ∈ setup.X := by
  simpa [xInnerIterAt] using setup.xInnerIter_mem ℓ t.1 t.2.2

/-- Generated inner component memory on the bounded source window. -/
noncomputable def xMemIterAt (ℓ : setup.OutputIndex) (t : setup.InnerIndex)
    (i : ι) : Ω → E :=
  setup.xMemIter ℓ.1 t.1 i

/-- Explicit boundary version of bounded component-memory feasibility.

This is not a derived invariant of Algorithm 6.9 under the printed assumptions. -/
theorem xMemIterAt_mem_sourceBoundary (ℓ : setup.OutputIndex) (t : setup.InnerIndex)
    (i : ι) (hmem : ∀ ω : Ω, setup.xMemIterAt ℓ t i ω ∈ setup.X) :
    ∀ ω : Ω, setup.xMemIterAt ℓ t i ω ∈ setup.X :=
  hmem

/-- Bounded Algorithm 6.9 extrapolated point `x̃ᵗ` on the source range
`t = 1, ..., s`.

This is the public version of Eq. (6.6.9).  The raw `ℕ` helper is private so the
paper-facing API does not expose a totalized `t - 1` case outside Algorithm 6.9's
loop.  Source:
`book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec/steps/4`,
Eq. (6.6.9), states `\tilde{x}^t = α_t(x^{t-1}-x^{t-2})+x^{t-1}`. -/
noncomputable def xTildeAt (ℓ : setup.OutputIndex) (t : setup.InnerIndex) : Ω → E :=
  fun ω =>
    let st := (setup.ambientProcess ℓ.1 ω).inner (t.1 - 1)
    setup.αSeq t.1 • (st.x - st.xPrev) + st.x

/-- Refreshed affine component point on the bounded source window.

Source: `book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec/steps/5`,
Eq. (6.6.10), updates the sampled component by
`(1+τ_t)^{-1}(\tilde{x}^t+τ_t x_i^{t-1})` and leaves other components unchanged. -/
noncomputable def xHatAt (ℓ : setup.OutputIndex) (t : setup.InnerIndex)
    (i : ι) : Ω → E :=
  fun ω =>
    let st := (setup.ambientProcess ℓ.1 ω).inner (t.1 - 1)
    (1 + setup.τSeq t.1)⁻¹ •
      (setup.xTildeAt ℓ t ω + setup.τSeq t.1 • st.xMem i)

/-- Explicit boundary version of refreshed-point feasibility.

This is the missing domain condition for using the source-domain value
`∇ψ_i(x̂_i^t)`.  It is not derived from the printed Algorithm 6.9 assumptions. -/
theorem xHatAt_mem_sourceBoundary (ℓ : setup.OutputIndex) (t : setup.InnerIndex)
    (i : ι) (hmem : ∀ ω : Ω, setup.xHatAt ℓ t i ω ∈ setup.X) :
    ∀ ω : Ω, setup.xHatAt ℓ t i ω ∈ setup.X :=
  hmem

/-- Hypothetical component memory after refreshing index `j`, restricted to the
bounded source window used in Lemma 6.12.

Source: `book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec/steps/5`,
Eq. (6.6.10), gives the sampled/non-sampled cases for `x_i^t`. -/
noncomputable def xMemAfterSampleAt (ℓ : setup.OutputIndex) (t : setup.InnerIndex)
    (j i : ι) : Ω → E :=
  fun ω =>
    if i = j then setup.xHatAt ℓ t i ω
    else setup.xMemIter ℓ.1 (t.1 - 1) i ω

/-- Explicit boundary version of hypothetical refreshed-memory feasibility.

This is a corrected/internal domain condition for Lemma 6.12-style
source-domain evaluations, not a theorem derived from Algorithm 6.9. -/
theorem xMemAfterSampleAt_mem_sourceBoundary (ℓ : setup.OutputIndex) (t : setup.InnerIndex)
    (j i : ι) (hmem : ∀ ω : Ω, setup.xMemAfterSampleAt ℓ t j i ω ∈ setup.X) :
    ∀ ω : Ω, setup.xMemAfterSampleAt ℓ t j i ω ∈ setup.X :=
  hmem

/-- Hypothetical estimator after refreshing index `j`, restricted to the bounded
source window used in Lemma 6.12.

Source: `book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec/steps/7`,
Eq. (6.6.12), defines `\tilde{y}_i^t = m(y_i^t-y_i^{t-1})+y_i^{t-1}`. -/
noncomputable def yTildeAfterSampleAt (ℓ : setup.OutputIndex) (t : setup.InnerIndex)
    (j i : ι) : Ω → E :=
  fun ω =>
    let yMemAfterSample : E :=
      if i = j then
        setup.gradPsi ℓ.1 i ω (setup.xMemAfterSampleAt ℓ t j i ω)
      else setup.yMemIter ℓ.1 (t.1 - 1) i ω
    SOptLib.uniformFiniteSumControlVariateEstimator (ι := ι)
      (setup.yMemIter ℓ.1 (t.1 - 1) i ω) yMemAfterSample

/-- Generated-center component objective evaluated on bounded paper indices and
on the source domain `X`.

Source: `book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec/steps/1`,
Eq. (6.6.8), defines `ψ_i^ℓ`. -/
noncomputable def psiAtIndex (ℓ : setup.OutputIndex) (i : ι) (ω : Ω)
    (x : {x : E // x ∈ setup.X}) : ℝ :=
  setup.psiOn ℓ.1 i ω x

/-- Internal ambient compatibility wrapper for the generated-center component
gradient on bounded paper indices.

The source-facing bounded-index gradient is `gradPsiOnAtIndex`, which requires an
`X`-membership proof for its argument. -/
noncomputable def gradPsiAtIndex (ℓ : setup.OutputIndex) (i : ι) (ω : Ω) (x : E) : E :=
  setup.gradPsi ℓ.1 i ω x

/-- Generated-center component gradient on bounded paper indices, evaluated only at
points carrying their `X`-membership.

This is the bounded-index version of Algorithm 6.9's Eq. (6.6.11) boundary.
Source: `book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec/steps/6`. -/
noncomputable def gradPsiOnAtIndex (ℓ : setup.OutputIndex) (i : ι) (ω : Ω)
    (x : {x : E // x ∈ setup.X}) : E :=
  setup.gradPsiOn ℓ.1 i ω x

/-- Generated gradient estimator on the bounded source window.

Source: `book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec/steps/7`,
Eq. (6.6.12), defines `\tilde{y}_i^t=m(y_i^t-y_i^{t-1})+y_i^{t-1}` for
all components. -/
noncomputable def yTildeAt (ℓ : setup.OutputIndex) (t : setup.InnerIndex) :
    Ω → ι → E :=
  fun ω i =>
    let st := (setup.ambientProcess ℓ.1 ω).inner t.1
    let stPrev := (setup.ambientProcess ℓ.1 ω).inner (t.1 - 1)
    (Fintype.card ι : ℝ) • (st.yMem i - stPrev.yMem i) + stPrev.yMem i

/-- Uniform finite average over Algorithm 6.8's random outer-output window
`{1, ..., k}`.

This replaces theorem-local `lHat`/`hk` witnesses for the paper phrase "randomly
selected from `[k]`".  `SOptLib.Model.Selection` finite-window expectation
lemmas were considered; they bridge laws of already-selected outputs, while this
paper-facing wrapper records the literal uniform `1/k` average used in Lemma 6.14
and Theorem 6.16 over the canonical bounded window.
Source: `book/FOML/RandomizedAcceleratedProximalPoint.json#/algorithm_spec/output`
states the output is `\bar{x}^{\hat{\ell}}` for random `\hat{\ell} ∈ [k]`;
`book/FOML/RandomizedAcceleratedProximalPoint.json#/key_lemmas/6/statement_math`
and `book/FOML/RandomizedAcceleratedProximalPoint.json#/main_theorem/statement_math`
give expectations at that random index. -/
noncomputable def randomOuterAverage (g : ℕ → Ω → ℝ) : ℝ :=
  ((setup.k : ℕ) : ℝ)⁻¹ *
    Finset.sum setup.outputWindow (fun ℓ => ∫ ω, g ℓ ω ∂setup.P)

/-- Uniform finite average over the attached paper output window `{1, ..., k}`.

This is the bounded-index version needed for objects such as `x_ℓ^*`, which the
paper defines only for generated subproblems `ℓ = 1, ..., k`.  `SOptLib`
finite-window selected-output lemmas were checked and kept as proof tools rather
than this source-facing object because they do not construct the exact subproblem
optimizer family; `SOptLib.outputWeightDenominator_pos` was checked as a proof
tool for nonempty denominators, but this paper's object is the literal uniform
window average.  Source:
`book/FOML/RandomizedAcceleratedProximalPoint.json#/assumptions/2` names
`x_ℓ^*` as the optimal solution of the `ℓ`-th subproblem, and
`book/FOML/RandomizedAcceleratedProximalPoint.json#/assumptions/3` selects
`\hat{\ell}` from `[k]`. -/
noncomputable def randomOuterAverageWindow
    (g : setup.OutputIndex → Ω → ℝ) : ℝ :=
  ((setup.k : ℕ) : ℝ)⁻¹ *
    Finset.sum setup.outputWindow.attach
      (fun ℓ => ∫ ω, g ℓ ω ∂setup.P)

/-- Proof-carrying finite-window observable for the paper's uniformly selected
outer index.

No SOptLib match: checked the finite-window selected-output expectation lemmas and
`SOptLib.objectiveExpectation`; they are proof bridges for already-modelled output
laws or objective kernels, while Theorem 6.16 needs a literal uniform average over
the attached paper window `[k]` with per-index integrability packaged. -/
abbrev IntegrableWindowObservable : Type _ :=
  {g : setup.OutputIndex → Ω → ℝ // ∀ ℓ, Integrable (g ℓ) setup.P}

/-- Uniform-random-index expectation of a proof-carrying finite-window observable. -/
noncomputable def randomOuterExpectation (g : setup.IntegrableWindowObservable) : ℝ :=
  setup.randomOuterAverageWindow g.1

/-- Per-index stationarity integrand in Theorem 6.16.

The exact subproblem optimizer is the canonical selected `x_ℓ^*` on the paper's
random-output window `[k]`, not a theorem-head witness family.
Source: `book/FOML/RandomizedAcceleratedProximalPoint.json#/main_theorem/statement_math`
states `E[d(∇f(x_{\hat{\ell}}^*),-N_X(x_{\hat{\ell}}^*))^2]` is bounded. -/
noncomputable def selectedStationarityIntegrand : setup.OutputIndex → Ω → ℝ :=
  fun ℓ ω =>
    (setup.normalConeGapOn
      ⟨setup.subproblemOptOutput ℓ ω, setup.subproblemOptOutput_mem ℓ ω⟩) ^ 2

/-- Per-index output-proximity integrand in Theorem 6.16.

Source: `book/FOML/RandomizedAcceleratedProximalPoint.json#/main_theorem/statement_math`
states `E‖\bar{x}^{\hat{\ell}}-x_{\hat{\ell}}^*‖^2` is bounded. -/
noncomputable def selectedOutputProximityIntegrand : setup.OutputIndex → Ω → ℝ :=
  fun ℓ ω => ‖setup.xBarOutput ℓ ω - setup.subproblemOptOutput ℓ ω‖ ^ 2

/-- Per-index displacement from the exact proximal solution to the previous outer
center in Lemma 6.14. -/
noncomputable def selectedPreviousProxDisplacementIntegrand :
    setup.OutputIndex → Ω → ℝ :=
  fun ℓ ω => ‖setup.subproblemOptOutput ℓ ω - setup.xBarIter (ℓ.1 - 1) ω‖ ^ 2

/-- Per-index displacement from the exact proximal solution to the current generated
outer iterate in Lemma 6.14. -/
noncomputable def selectedCurrentProxDisplacementIntegrand :
    setup.OutputIndex → Ω → ℝ :=
  fun ℓ ω => ‖setup.subproblemOptOutput ℓ ω - setup.xBarIter ℓ.1 ω‖ ^ 2

/-- Outer component-memory dispersion at a deterministic outer time.

No SOptLib match: searched finite-window output and iterate-dispersion primitives,
and checked the existing local `ambientFixedMemoryDispersionObservable`; those
cover fixed inner runs or generic selected windows, while Lemma 6.14 needs the
literal Algorithm 6.8 quantity
`m⁻¹∑ᵢ ‖\bar{x}_i^ℓ-\bar{x}^ℓ‖²` for the generated outer memories. -/
noncomputable def outerMemoryDispersionIntegrand (ℓ : ℕ) : Ω → ℝ :=
  fun ω =>
    SOptLib.finiteMemoryDispersion
      (fun i => (setup.ambientProcess ℓ ω).xBarMem i) (setup.xBarIter ℓ ω)

/-- Integrability obligation for Theorem 6.16's stationarity expectation.

The source states an ordinary expectation.  Mathlib's Bochner integral is total, so
this theorem records the regularity fact that must be derived for the generated
random output rather than assumed in the theorem head. -/
theorem selectedStationarity_integrable (ℓ : ℕ) (hℓ : ℓ ∈ Finset.Icc 1 (setup.k : ℕ)) :
    Integrable
      (fun ω : Ω =>
        (setup.normalConeGapOn
          ⟨setup.subproblemOpt ℓ hℓ ω, setup.subproblemOpt_mem ℓ hℓ ω⟩) ^ 2)
      setup.P := by
  classical
  refine setup.outer_prefix_integrable_real (N := ℓ * setup.s) ?_
  intro ω ω' hprefix
  have hopt : setup.subproblemOpt ℓ hℓ ω = setup.subproblemOpt ℓ hℓ ω' :=
    setup.subproblemOpt_prefix_const ℓ hℓ hprefix
  have hsub :
      (⟨setup.subproblemOpt ℓ hℓ ω, setup.subproblemOpt_mem ℓ hℓ ω⟩ :
          {x : E // x ∈ setup.X}) =
        ⟨setup.subproblemOpt ℓ hℓ ω', setup.subproblemOpt_mem ℓ hℓ ω'⟩ :=
    Subtype.ext hopt
  simpa [hsub]

/-- Bounded-window form of the stationarity integrability obligation. -/
theorem selectedStationarityIntegrand_integrable (ℓ : setup.OutputIndex) :
    Integrable (setup.selectedStationarityIntegrand ℓ) setup.P := by
  simpa [selectedStationarityIntegrand, subproblemOptOutput] using
    setup.selectedStationarity_integrable ℓ.1 (by simpa [outputWindow] using ℓ.2)

/-- Integrability obligation for Theorem 6.16's output-distance expectation.

This keeps expectation well-definedness as a proof obligation for Algorithm 6.8's
generated process, not as an extra source-facing assumption. -/
theorem selectedOutputProximity_integrable (ℓ : ℕ) (hℓ : ℓ ∈ Finset.Icc 1 (setup.k : ℕ)) :
    Integrable
      (fun ω : Ω => ‖setup.xBarIter ℓ ω - setup.subproblemOpt ℓ hℓ ω‖ ^ 2) setup.P := by
  classical
  have hle : ℓ ≤ (setup.k : ℕ) := (Finset.mem_Icc.mp hℓ).2
  refine setup.outer_prefix_integrable_real (N := ℓ * setup.s) ?_
  intro ω ω' hprefix
  have hx : setup.xBarIter ℓ ω = setup.xBarIter ℓ ω' :=
    setup.xBarIter_prefix_const ℓ hle hprefix
  have hopt : setup.subproblemOpt ℓ hℓ ω = setup.subproblemOpt ℓ hℓ ω' :=
    setup.subproblemOpt_prefix_const ℓ hℓ hprefix
  simp [hx, hopt]

/-- Bounded-window form of the output-proximity integrability obligation. -/
theorem selectedOutputProximityIntegrand_integrable (ℓ : setup.OutputIndex) :
    Integrable (setup.selectedOutputProximityIntegrand ℓ) setup.P := by
  simpa [selectedOutputProximityIntegrand, xBarOutput, subproblemOptOutput] using
    setup.selectedOutputProximity_integrable ℓ.1 (by simpa [outputWindow] using ℓ.2)

/-- Integrability obligation for Lemma 6.14's previous-center displacement
expectation. -/
theorem selectedPreviousProxDisplacementIntegrand_integrable (ℓ : setup.OutputIndex) :
    Integrable (setup.selectedPreviousProxDisplacementIntegrand ℓ) setup.P := by
  classical
  have hIcc : ℓ.1 ∈ Finset.Icc 1 (setup.k : ℕ) := by
    simpa [outputWindow] using ℓ.2
  have hle : ℓ.1 ≤ (setup.k : ℕ) := (Finset.mem_Icc.mp hIcc).2
  have hprev_le : ℓ.1 - 1 ≤ (setup.k : ℕ) :=
    le_trans (Nat.sub_le ℓ.1 1) hle
  refine setup.outer_prefix_integrable_real (N := ℓ.1 * setup.s) ?_
  intro ω ω' hprefix
  have hopt :
      setup.subproblemOpt ℓ.1 hIcc ω = setup.subproblemOpt ℓ.1 hIcc ω' :=
    setup.subproblemOpt_prefix_const ℓ.1 hIcc hprefix
  have hprevPrefix :
      (fun r : Fin ((ℓ.1 - 1) * setup.s) => setup.ξ r.1 ω) =
        (fun r : Fin ((ℓ.1 - 1) * setup.s) => setup.ξ r.1 ω') := by
    simpa [Fin.castLE] using
      (fin_prefix_eq_of_le (α := ι)
        (m := (ℓ.1 - 1) * setup.s) (n := ℓ.1 * setup.s)
        (f := fun r : Fin (ℓ.1 * setup.s) => setup.ξ r.1 ω)
        (g := fun r : Fin (ℓ.1 * setup.s) => setup.ξ r.1 ω')
        (Nat.mul_le_mul_right setup.s (Nat.sub_le ℓ.1 1)) hprefix)
  have hxprev :
      setup.xBarIter (ℓ.1 - 1) ω = setup.xBarIter (ℓ.1 - 1) ω' :=
    setup.xBarIter_prefix_const (ℓ.1 - 1) hprev_le hprevPrefix
  simp [selectedPreviousProxDisplacementIntegrand, subproblemOptOutput, hIcc,
    hopt, hxprev]

/-- Integrability obligation for Lemma 6.14's current-iterate displacement
expectation. -/
theorem selectedCurrentProxDisplacementIntegrand_integrable (ℓ : setup.OutputIndex) :
    Integrable (setup.selectedCurrentProxDisplacementIntegrand ℓ) setup.P := by
  classical
  have h := setup.selectedOutputProximityIntegrand_integrable ℓ
  have heq :
      setup.selectedCurrentProxDisplacementIntegrand ℓ =
        setup.selectedOutputProximityIntegrand ℓ := by
    funext ω
    simp [selectedCurrentProxDisplacementIntegrand, selectedOutputProximityIntegrand,
      xBarOutput, subproblemOptOutput, norm_sub_rev]
  simpa [heq] using h

/-- Integrability obligation for the generated outer component-memory dispersion.

The proof uses finite-prefix determinism of the Algorithm 6.8 outer fields, not a
new boundedness assumption. -/
theorem outerMemoryDispersionIntegrand_integrable (ℓ : ℕ) (hℓ : ℓ ≤ (setup.k : ℕ)) :
    Integrable (setup.outerMemoryDispersionIntegrand ℓ) setup.P := by
  classical
  refine setup.outer_prefix_integrable_real (N := ℓ * setup.s) ?_
  intro ω ω' hprefix
  have hfields := setup.ambientProcess_outerFields_prefix_const ℓ hℓ hprefix
  simp [outerMemoryDispersionIntegrand, xBarIter, hfields.1, hfields.2.1]

/-- Integrability of the previous outer component-memory dispersion on the paper
output window. -/
theorem outerPreviousMemoryDispersionIntegrand_integrable (ℓ : setup.OutputIndex) :
    Integrable (setup.outerMemoryDispersionIntegrand (ℓ.1 - 1)) setup.P := by
  classical
  have hIcc : ℓ.1 ∈ Finset.Icc 1 (setup.k : ℕ) := by
    simpa [outputWindow] using ℓ.2
  have hle : ℓ.1 ≤ (setup.k : ℕ) := (Finset.mem_Icc.mp hIcc).2
  exact setup.outerMemoryDispersionIntegrand_integrable (ℓ.1 - 1)
    (le_trans (Nat.sub_le ℓ.1 1) hle)

/-- Integrability of the current outer component-memory dispersion on the paper
output window. -/
theorem outerCurrentMemoryDispersionIntegrand_integrable (ℓ : setup.OutputIndex) :
    Integrable (setup.outerMemoryDispersionIntegrand ℓ.1) setup.P := by
  classical
  have hIcc : ℓ.1 ∈ Finset.Icc 1 (setup.k : ℕ) := by
    simpa [outputWindow] using ℓ.2
  exact setup.outerMemoryDispersionIntegrand_integrable ℓ.1 (Finset.mem_Icc.mp hIcc).2

/-- Proof-carrying stationarity observable for Theorem 6.16's random outer index. -/
noncomputable def selectedStationarityObservable : setup.IntegrableWindowObservable :=
  ⟨setup.selectedStationarityIntegrand, setup.selectedStationarityIntegrand_integrable⟩

/-- Proof-carrying output-proximity observable for Theorem 6.16's random outer index. -/
noncomputable def selectedOutputProximityObservable : setup.IntegrableWindowObservable :=
  ⟨setup.selectedOutputProximityIntegrand,
    setup.selectedOutputProximityIntegrand_integrable⟩

/-- Proof-carrying previous-center displacement observable for Lemma 6.14. -/
noncomputable def selectedPreviousProxDisplacementObservable :
    setup.IntegrableWindowObservable :=
  ⟨setup.selectedPreviousProxDisplacementIntegrand,
    setup.selectedPreviousProxDisplacementIntegrand_integrable⟩

/-- Proof-carrying current-iterate displacement observable for Lemma 6.14. -/
noncomputable def selectedCurrentProxDisplacementObservable :
    setup.IntegrableWindowObservable :=
  ⟨setup.selectedCurrentProxDisplacementIntegrand,
    setup.selectedCurrentProxDisplacementIntegrand_integrable⟩

/-- Uniform-random-index stationarity expectation in Theorem 6.16. -/
noncomputable def selectedStationarity : ℝ :=
  setup.randomOuterExpectation setup.selectedStationarityObservable

/-- Uniform-random-index output-proximity expectation in Theorem 6.16. -/
noncomputable def selectedOutputProximity : ℝ :=
  setup.randomOuterExpectation setup.selectedOutputProximityObservable

/-- Uniform-random-index previous-center displacement expectation in Lemma 6.14. -/
noncomputable def selectedPreviousProxDisplacement : ℝ :=
  setup.randomOuterExpectation setup.selectedPreviousProxDisplacementObservable

/-- Uniform-random-index current-iterate displacement expectation in Lemma 6.14. -/
noncomputable def selectedCurrentProxDisplacement : ℝ :=
  setup.randomOuterExpectation setup.selectedCurrentProxDisplacementObservable

end RandomizedAcceleratedProximalPointSetup

namespace RandomizedAcceleratedProximalPoint

/-! The next bridge exposes Algorithm 6.9's generated inner iterate as the
selected Eq. (6.6.13) prox minimizer. -/

/-- Literal norm-square form of the quadratic Bregman divergence generated by
`φ_z(x)=μ/2‖x-z‖²`.

Aligns with Lan Eq. (6.6.8) as used in Eq. (6.6.45).  The pre-existing local
candidate `quadraticBregmanAt_eq` gives the expanded inner-product form; SOptLib
Bregman identities are paper-neutral, while this helper specializes the file's
literal quadratic constants and orientation. -/
theorem quadraticBregmanAt_eq_mu_half_norm_sq
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω) (z x y : E) :
    setup.quadraticBregmanAt z x y = (setup.μ / 2) * ‖x - y‖ ^ 2 := by
  rw [setup.quadraticBregmanAt_eq z x y]
  rw [norm_sub_sq_real x z, norm_sub_sq_real y z, norm_sub_sq_real x y]
  simp [inner_sub_left, inner_sub_right, inner_smul_left, real_inner_comm]
  ring_nf

/-- Gradient of the literal quadratic regularizer `φ_z(x)=μ/2‖x-z‖²`.

Aligns with Lan Eq. (6.6.8) as used in Eq. (6.6.45).  SOptLib's ambient
Bregman segment derivative was reused below, but it needs this local
paper-specific quadratic-gradient bridge for `phiAt`. -/
theorem phiAt_hasGradientAt
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω) (z x : E) :
    HasGradientAt (setup.phiAt z) (setup.gradPhiAt z x) x := by
  simpa [RandomizedAcceleratedProximalPointSetup.phiAt,
    RandomizedAcceleratedProximalPointSetup.gradPhiAt,
    SOptLib.centeredQuadraticPotential] using
    (hasGradientAt_const_mul_norm_sub_sq_centered (E := E) setup.μ z x)

/-- Three-point identity for the quadratic Bregman divergence in Eq. (6.6.45).

Aligns with Lan Eq. (6.6.45)'s conversion from first-order prox optimality to
three Bregman terms.  SOptLib's `carrierBregmanDivergence_three_point_identity`
was considered, but this local identity specializes the file's concrete
`quadraticBregmanAt` orientation needed by `two_bregman_argmin_descent`. -/
theorem quadraticBregmanAt_three_point_identity
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω) (z a b c : E) :
    setup.quadraticBregmanAt z c a =
      setup.quadraticBregmanAt z b a +
        ⟪setup.gradPhiAt z b - setup.gradPhiAt z a, c - b⟫_ℝ +
      setup.quadraticBregmanAt z c b := by
  simpa [RandomizedAcceleratedProximalPointSetup.quadraticBregmanAt,
    RandomizedAcceleratedProximalPointSetup.gradPhiAt] using
    (SOptLib.centeredQuadraticBregman_three_point_identity
      (μ := setup.μ) (z := z) (a := a) (b := b) (c := c))

/-- Deterministic Eq. (6.6.45) prox three-point inequality.

Aligns with Lan Eq. (6.6.45): the source step is exactly the optimality
condition of Eq. (6.6.13) converted into the three Bregman terms.  The
SOptLib candidate `two_bregman_argmin_descent` is specialized here with
`V a b = quadraticBregmanAt z b a`, `p u = ⟪g,u⟫`, `mu1 = 1`, and
`mu2 = η_t`; `prox_three_point_of_isMinOn_linear_bregman` was considered but
does not directly include the second weighted Bregman center `xPrev`. -/
theorem proxObjectiveAt_quadratic_three_point
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (z : E) (t : ℕ) (xPrev g y x : E)
    (_hz : z ∈ setup.X) (ht : 1 ≤ t) (hts : t ≤ setup.s)
    (_hxPrev : xPrev ∈ setup.X) (hy : y ∈ setup.X) (hx : x ∈ setup.X)
    (hmin : IsMinOn (setup.proxObjectiveAt z t xPrev g) setup.X y) :
    setup.phiAt z y - setup.phiAt z x + ⟪g, y - x⟫_ℝ ≤
      setup.ηSeq t * setup.quadraticBregmanAt z x xPrev -
        (1 + setup.ηSeq t) * setup.quadraticBregmanAt z x y -
      setup.ηSeq t * setup.quadraticBregmanAt z y xPrev := by
  classical
  let p : E → ℝ := fun u => ⟪g, u⟫_ℝ
  let V : E → E → ℝ := fun a b => setup.quadraticBregmanAt z b a
  have hp_convex : ConvexOn ℝ setup.X p := by
    refine ⟨setup.hX_convex, ?_⟩
    intro x hx y hy a b ha hb hab
    simp [p, inner_add_right, inner_smul_right, smul_eq_mul]
  have hV_segment_deriv :
      ∀ (a z0 u : E), z0 ∈ setup.X →
        let d : E := u - z0
        let β : ℝ → ℝ := fun r =>
          if _hr : r ∈ Set.Icc (0 : ℝ) 1 then
            V a (AffineMap.lineMap z0 u r) - V a z0
          else 0
        HasDerivWithinAt β
          ⟪setup.gradPhiAt z z0 - setup.gradPhiAt z a, d⟫_ℝ
          (Set.Icc (0 : ℝ) 1) 0 := by
    intro a z0 u _hz0
    have hseg :=
      bregman_segment_difference_hasDerivWithinAt_zero
        (setup.phiAt z) (setup.gradPhiAt z) (x := a) (xp := z0) (u := u)
        (phiAt_hasGradientAt setup z z0)
    simpa [V, carrierBregmanFormula,
      RandomizedAcceleratedProximalPointSetup.quadraticBregmanAt] using hseg
  have hV_three :
      ∀ a b c : E,
        V a c = V a b + ⟪setup.gradPhiAt z b - setup.gradPhiAt z a, c - b⟫_ℝ +
          V b c := by
    intro a b c
    simpa [V, add_assoc] using
      quadraticBregmanAt_three_point_identity setup z a b c
  have h_opt :
      ∀ u, u ∈ setup.X →
        p y + (1 : ℝ) * V z y + setup.ηSeq t * V xPrev y ≤
          p u + (1 : ℝ) * V z u + setup.ηSeq t * V xPrev u := by
    intro u hu
    have hle := hmin hu
    simp [p, V, RandomizedAcceleratedProximalPointSetup.proxObjectiveAt,
      RandomizedAcceleratedProximalPointSetup.quadraticBregmanAt,
      RandomizedAcceleratedProximalPointSetup.phiAt,
      RandomizedAcceleratedProximalPointSetup.gradPhiAt] at hle ⊢
    nlinarith
  have hdescent :=
    two_bregman_argmin_descent setup.X p V (setup.gradPhiAt z) hp_convex
      (xTilde := z) (yTilde := xPrev) (uHat := y)
      (mu1 := (1 : ℝ)) (mu2 := setup.ηSeq t)
      hy (by norm_num) (setup.hηSeq_nonneg t ht hts)
      hV_segment_deriv hV_three h_opt x hx
  have hcenter_y : V z y = setup.phiAt z y := by
    simp [V, RandomizedAcceleratedProximalPointSetup.quadraticBregmanAt,
      RandomizedAcceleratedProximalPointSetup.phiAt,
      RandomizedAcceleratedProximalPointSetup.gradPhiAt]
  have hcenter_x : V z x = setup.phiAt z x := by
    simp [V, RandomizedAcceleratedProximalPointSetup.quadraticBregmanAt,
      RandomizedAcceleratedProximalPointSetup.phiAt,
      RandomizedAcceleratedProximalPointSetup.gradPhiAt]
  have hinner : ⟪g, y - x⟫_ℝ = ⟪g, y⟫_ℝ - ⟪g, x⟫_ℝ := by
    rw [inner_sub_right]
  dsimp [p, V] at hdescent
  have hcenter_y' : setup.quadraticBregmanAt z y z = setup.phiAt z y := by
    simpa [V] using hcenter_y
  have hcenter_x' : setup.quadraticBregmanAt z x z = setup.phiAt z x := by
    simpa [V] using hcenter_x
  rw [hcenter_y', hcenter_x'] at hdescent
  simp at hdescent
  rw [hinner]
  nlinarith

/-- Generated `xInnerIterAt` realizes the Eq. (6.6.13) prox argmin.

Aligns with Lan Eq. (6.6.13) as used in Eq. (6.6.45): this specializes the
already selected `proxStepAt_is_argmin` through the Algorithm 6.8/6.9 process
successor equations.  Considered SOptLib prox candidates
`prox_three_point_of_isMinOn_linear_bregman` and `two_bregman_argmin_descent`;
they consume an argmin certificate but do not expose this paper's generated
process as the selected prox step. -/
theorem xInnerIterAt_is_proxObjectiveAt_argmin
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (ℓ : setup.OutputIndex) (t : setup.InnerIndex) (ω : Ω) :
    IsMinOn
      (setup.proxObjectiveAt (setup.outerCenter ℓ.1 ω) t.1
        (setup.xInnerIter ℓ.1 (t.1 - 1) ω)
        ((Fintype.card ι : ℝ)⁻¹ •
          Finset.sum Finset.univ (fun i => setup.yTildeAt ℓ t ω i)))
      setup.X (setup.xInnerIterAt ℓ t ω) := by
  classical
  have hIcc : ℓ.1 ∈ Finset.Icc 1 (setup.k : ℕ) := by
    simpa [RandomizedAcceleratedProximalPointSetup.outputWindow] using ℓ.2
  have hbounds := Finset.mem_Icc.mp hIcc
  have hpos0 : 0 < ℓ.1 := lt_of_lt_of_le Nat.zero_lt_one hbounds.1
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos0)
  have hsucc : n + 1 ≤ (setup.k : ℕ) := by
    simpa [hn] using hbounds.2
  have hprev :
      (setup.ambientProcess n ω).xBar ∈ setup.X :=
    setup.eq_6_6_13_ambientProcess_mem n (Nat.le_of_succ_le hsucc) ω
  let innerRec :=
    setup.ambientFixedInnerProcess (setup.outerSampleOffset n)
      (setup.ambientProcess n ω).xBar (setup.ambientProcess n ω).xBar
      (setup.ambientProcess n ω).xBarMem (setup.ambientProcess n ω).yBarMem
      hprev hprev
  have ht_succ : (t.1 - 1) + 1 ≤ setup.s := by
    simpa [Nat.sub_add_cancel t.2.1] using t.2.2
  have hfixed :=
    setup.ambientFixedInnerProcess_succ (setup.outerSampleOffset n)
      (setup.ambientProcess n ω).xBar (setup.ambientProcess n ω).xBar
      (setup.ambientProcess n ω).xBarMem (setup.ambientProcess n ω).yBarMem
      hprev hprev (t.1 - 1) ht_succ ω
  have ht_eq : (t.1 - 1) + 1 = t.1 := Nat.sub_add_cancel t.2.1
  have hfixed_t := hfixed
  simp [ht_eq] at hfixed_t
  have houter := setup.ambientProcess_succ n hsucc ω
  have hxPrev_mem :
      setup.xInnerIter ℓ.1 (t.1 - 1) ω ∈ setup.X :=
    setup.xInnerIter_mem ℓ (t.1 - 1) (le_trans (Nat.sub_le _ _) t.2.2) ω
  have hmin :=
    setup.proxStepAt_is_argmin (setup.outerCenter ℓ.1 ω) t.1
      (setup.outerCenter_mem ℓ ω) t.2.1 t.2.2
      (setup.xInnerIter ℓ.1 (t.1 - 1) ω) hxPrev_mem
      ((Fintype.card ι : ℝ)⁻¹ •
        Finset.sum Finset.univ (fun i => setup.yTildeAt ℓ t ω i))
  convert hmin using 1
  conv_lhs =>
    rw [RandomizedAcceleratedProximalPointSetup.xInnerIterAt,
      RandomizedAcceleratedProximalPointSetup.xInnerIter, hn, houter]
  conv_lhs =>
    dsimp
    rw [← ht_eq, hfixed]
  simp [RandomizedAcceleratedProximalPointSetup.ambientInnerStepAt,
    RandomizedAcceleratedProximalPointSetup.yTildeAt,
    RandomizedAcceleratedProximalPointSetup.outerCenter,
    RandomizedAcceleratedProximalPointSetup.xBarIter,
    RandomizedAcceleratedProximalPointSetup.xInnerIter,
    hn, ht_eq, houter, hfixed, hfixed_t]

/-! `eq_6_6_45` is the one-step prox optimality inequality for the inner RaGrad update
(Eq. 6.6.13).  It is the foundational inequality used in `lemma_6_13`. -/
theorem eq_6_6_45
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (ℓ : setup.OutputIndex) (t : setup.InnerIndex)
    (xStar : E)
    (hxStar : xStar ∈ setup.X) :
    ∀ ω : Ω,
      setup.phi ℓ.1 ω (setup.xInnerIterAt ℓ t ω) -
          setup.phi ℓ.1 ω xStar +
          ⟪(Fintype.card ι : ℝ)⁻¹ •
              Finset.sum Finset.univ (fun i => setup.yTildeAt ℓ t ω i),
            setup.xInnerIterAt ℓ t ω - xStar⟫_ℝ ≤
        setup.ηSeq t.1 *
            ((setup.μ / 2) * ‖xStar - setup.xInnerIter ℓ.1 (t.1 - 1) ω‖ ^ 2) -
          (1 + setup.ηSeq t.1) *
            ((setup.μ / 2) * ‖xStar - setup.xInnerIterAt ℓ t ω‖ ^ 2) -
          setup.ηSeq t.1 *
            ((setup.μ / 2) *
              ‖setup.xInnerIterAt ℓ t ω - setup.xInnerIter ℓ.1 (t.1 - 1) ω‖ ^ 2) := by
  intro ω
  let z : E := setup.outerCenter ℓ.1 ω
  let y : E := setup.xInnerIterAt ℓ t ω
  let xPrev : E := setup.xInnerIter ℓ.1 (t.1 - 1) ω
  let g : E :=
    (Fintype.card ι : ℝ)⁻¹ •
      Finset.sum Finset.univ (fun i => setup.yTildeAt ℓ t ω i)
  have hz : z ∈ setup.X := by
    simpa [z] using setup.outerCenter_mem ℓ ω
  have hy : y ∈ setup.X := by
    simpa [y] using setup.xInnerIterAt_mem ℓ t ω
  have hxPrev : xPrev ∈ setup.X := by
    simpa [xPrev] using
      setup.xInnerIter_mem ℓ (t.1 - 1) (le_trans (Nat.sub_le _ _) t.2.2) ω
  have hmin :
      IsMinOn (setup.proxObjectiveAt z t.1 xPrev g) setup.X y := by
    simpa [z, y, xPrev, g] using
      xInnerIterAt_is_proxObjectiveAt_argmin setup ℓ t ω
  have hstep :=
    proxObjectiveAt_quadratic_three_point setup z t.1 xPrev g y xStar
      hz t.2.1 t.2.2 hxPrev hy hxStar hmin
  simpa [z, y, xPrev, g, RandomizedAcceleratedProximalPointSetup.phi,
    quadraticBregmanAt_eq_mu_half_norm_sq setup] using hstep

/-! `eq_6_6_45_ambientFixed_sourceDomain` is the fixed-subproblem version of
Eq. (6.6.45) used by the source-domain Lemma 6.13 route.  The public
`eq_6_6_45` above is generated-output-indexed; Lemma 6.13 is stated for an
arbitrary fixed proximal subproblem, so this theorem exposes the same prox
optimality equation on that corrected boundary. -/
theorem eq_6_6_45_ambientFixed_sourceDomain
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (offset : ℕ) (z x0 xStar : E) (xMem0 yMem0 : ι → E)
    (hz : z ∈ setup.X) (hx0 : x0 ∈ setup.X) (hxStar : xStar ∈ setup.X)
    (n : ℕ) (hn : n + 1 ≤ setup.s) :
    ∀ ω : Ω,
      let stPrev :=
        setup.ambientFixedInnerProcess offset z x0 xMem0 yMem0 hz hx0 n ω
      let stNext :=
        setup.ambientFixedInnerProcess offset z x0 xMem0 yMem0 hz hx0 (n + 1) ω
      let yTilde : ι → E :=
        fun i =>
          (Fintype.card ι : ℝ) • (stNext.yMem i - stPrev.yMem i) + stPrev.yMem i
      setup.phiAt z stNext.x - setup.phiAt z xStar +
          ⟪(Fintype.card ι : ℝ)⁻¹ • Finset.sum Finset.univ yTilde,
            stNext.x - xStar⟫_ℝ ≤
        setup.ηSeq (n + 1) *
            ((setup.μ / 2) * ‖xStar - stPrev.x‖ ^ 2) -
          (1 + setup.ηSeq (n + 1)) *
            ((setup.μ / 2) * ‖xStar - stNext.x‖ ^ 2) -
          setup.ηSeq (n + 1) *
            ((setup.μ / 2) * ‖stNext.x - stPrev.x‖ ^ 2) := by
  classical
  intro ω
  let stPrev :=
    setup.ambientFixedInnerProcess offset z x0 xMem0 yMem0 hz hx0 n ω
  let yMemNew : ι → E :=
    fun i =>
      if i = setup.ξ (offset + ((n + 1) - 1)) ω then
        setup.gradPsiAtOrElse z i
          (setup.xMemAfterSampleAtState (n + 1) (Nat.succ_pos n) hn
            (setup.ξ (offset + ((n + 1) - 1)) ω) i stPrev)
          (stPrev.yMem i)
      else stPrev.yMem i
  let g : E :=
    (Fintype.card ι : ℝ)⁻¹ •
      Finset.sum Finset.univ
        (fun i => (Fintype.card ι : ℝ) • (yMemNew i - stPrev.yMem i) + stPrev.yMem i)
  let y : E :=
    setup.proxStepAt z (n + 1) hz (Nat.succ_pos n) hn stPrev.x
      (((setup.ambientFixedInnerProcess_mem offset z x0 xMem0 yMem0 hz hx0 n
        (Nat.le_of_succ_le hn)) ω).1) g
  have hPrevMem :
      stPrev.x ∈ setup.X := by
    simpa [stPrev] using
      (((setup.ambientFixedInnerProcess_mem offset z x0 xMem0 yMem0 hz hx0 n
        (Nat.le_of_succ_le hn)) ω).1)
  have hy : y ∈ setup.X := by
    simpa [y] using
      setup.proxStepAt_mem z (n + 1) hz (Nat.succ_pos n) hn stPrev.x hPrevMem g
  have hmin :
      IsMinOn (setup.proxObjectiveAt z (n + 1) stPrev.x g) setup.X y := by
    simpa [y] using
      setup.proxStepAt_is_argmin z (n + 1) hz (Nat.succ_pos n) hn stPrev.x hPrevMem g
  have hstep :=
    proxObjectiveAt_quadratic_three_point setup z (n + 1) stPrev.x g y xStar
      hz (Nat.succ_pos n) hn hPrevMem hy hxStar hmin
  have hsucc :=
    setup.ambientFixedInnerProcess_succ offset z x0 xMem0 yMem0 hz hx0 n hn ω
  simpa [stPrev, y, g, yMemNew,
    RandomizedAcceleratedProximalPointSetup.ambientInnerStepAt,
    quadraticBregmanAt_eq_mu_half_norm_sq setup, hsucc] using hstep

/-- The generated center of an in-window proximal subproblem is the previous
outer iterate.

Aligns with Lan Algorithm 6.8, Eq. (6.6.8): the `ℓ`-th subproblem is centered at
`\bar{x}^{ℓ-1}`.  The local definitions `outerCenter` and `xBarIter` already encode
this; this helper only exposes the predecessor form used by Theorem 6.16's
stationarity distance. -/
theorem outerCenter_eq_xBarIter_pred
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (ℓ : setup.OutputIndex) (ω : Ω) :
    setup.outerCenter ℓ.1 ω = setup.xBarIter (ℓ.1 - 1) ω := by
  classical
  have hIcc : ℓ.1 ∈ Finset.Icc 1 (setup.k : ℕ) := by
    simpa [RandomizedAcceleratedProximalPointSetup.outputWindow] using ℓ.2
  have hpos : 0 < ℓ.1 := lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hIcc).1
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  rw [hn]
  simp [RandomizedAcceleratedProximalPointSetup.outerCenter]

/-- The exact proximal optimizer at output index `ℓ` is determined by the
strict previous outer prefix `(ℓ - 1) * s`.

Aligns with Lan Lemma 6.14, Eqs. (6.6.38)-(6.6.39): the `ℓ`-th subproblem
minimizer depends on the previous generated center `x̄^{ℓ-1}`, not on the fresh
inner block used to compute `x̄^ℓ`. Considered target-file
`subproblemOpt_prefix_const`, but it uses the longer `ℓ * s` prefix; the
transport proof needs the sharper previous-prefix boundary, obtained from
`outerCenter_eq_xBarIter_pred`, `xBarIter_prefix_const`, and
`subproblemOpt_const_of_outerCenter_eq`. -/
theorem subproblemOptOutput_prevPrefix_const
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (ℓ : setup.OutputIndex) :
    ∀ ⦃ω ω' : Ω⦄,
      (fun r : Fin ((ℓ.1 - 1) * setup.s) => setup.ξ r.1 ω) =
        (fun r : Fin ((ℓ.1 - 1) * setup.s) => setup.ξ r.1 ω') →
      setup.subproblemOptOutput ℓ ω = setup.subproblemOptOutput ℓ ω' := by
  classical
  intro ω ω' hprefix
  have hIcc : ℓ.1 ∈ Finset.Icc 1 (setup.k : ℕ) := by
    simpa [RandomizedAcceleratedProximalPointSetup.outputWindow] using ℓ.2
  have hbounds := Finset.mem_Icc.mp hIcc
  have hprev_le : ℓ.1 - 1 ≤ (setup.k : ℕ) :=
    Nat.le_trans (Nat.sub_le ℓ.1 1) hbounds.2
  have hxbar :
      setup.xBarIter (ℓ.1 - 1) ω = setup.xBarIter (ℓ.1 - 1) ω' :=
    setup.xBarIter_prefix_const (ℓ.1 - 1) hprev_le hprefix
  have hcenter : setup.outerCenter ℓ.1 ω = setup.outerCenter ℓ.1 ω' := by
    calc
      setup.outerCenter ℓ.1 ω = setup.xBarIter (ℓ.1 - 1) ω :=
        outerCenter_eq_xBarIter_pred setup ℓ ω
      _ = setup.xBarIter (ℓ.1 - 1) ω' := hxbar
      _ = setup.outerCenter ℓ.1 ω' :=
        (outerCenter_eq_xBarIter_pred setup ℓ ω').symm
  simpa [RandomizedAcceleratedProximalPointSetup.subproblemOptOutput] using
    setup.subproblemOpt_const_of_outerCenter_eq ℓ.1 hIcc hcenter

/-- Terminal parameters for the `ℓ`-th Theorem 6.17 call are strict-previous-prefix
measurable.

Aligns with Lan Lemma 6.14, Eqs. (6.6.38)-(6.6.39): after freezing the first
`(ℓ - 1) * s` samples, the subproblem center, exact minimizer, and carried
component memories are fixed before the fresh inner block is sampled. Considered
target-file `subproblemOpt_prefix_const`, but it fixes the longer `ℓ * s`
prefix; this helper combines the sharper `subproblemOptOutput_prevPrefix_const`
with `ambientProcess_outerFields_prefix_const` for the actual terminal
parameters. -/
theorem outer_terminal_params_prevPrefix_const
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (ℓ : setup.OutputIndex) :
    ∀ ⦃ω ω' : Ω⦄,
      (fun r : Fin ((ℓ.1 - 1) * setup.s) => setup.ξ r.1 ω) =
        (fun r : Fin ((ℓ.1 - 1) * setup.s) => setup.ξ r.1 ω') →
      setup.outerCenter ℓ.1 ω = setup.outerCenter ℓ.1 ω' ∧
        setup.subproblemOptOutput ℓ ω = setup.subproblemOptOutput ℓ ω' ∧
        (setup.ambientProcess (ℓ.1 - 1) ω).xBarMem =
          (setup.ambientProcess (ℓ.1 - 1) ω').xBarMem ∧
        (setup.ambientProcess (ℓ.1 - 1) ω).yBarMem =
          (setup.ambientProcess (ℓ.1 - 1) ω').yBarMem := by
  classical
  intro ω ω' hprefix
  have hIcc : ℓ.1 ∈ Finset.Icc 1 (setup.k : ℕ) := by
    simpa [RandomizedAcceleratedProximalPointSetup.outputWindow] using ℓ.2
  have hbounds := Finset.mem_Icc.mp hIcc
  have hprev_le : ℓ.1 - 1 ≤ (setup.k : ℕ) :=
    Nat.le_trans (Nat.sub_le ℓ.1 1) hbounds.2
  have hfields :=
    setup.ambientProcess_outerFields_prefix_const (ℓ.1 - 1) hprev_le hprefix
  have hcenter : setup.outerCenter ℓ.1 ω = setup.outerCenter ℓ.1 ω' := by
    calc
      setup.outerCenter ℓ.1 ω = setup.xBarIter (ℓ.1 - 1) ω :=
        outerCenter_eq_xBarIter_pred setup ℓ ω
      _ = setup.xBarIter (ℓ.1 - 1) ω' := by
        simpa [RandomizedAcceleratedProximalPointSetup.xBarIter] using hfields.1
      _ = setup.outerCenter ℓ.1 ω' :=
        (outerCenter_eq_xBarIter_pred setup ℓ ω').symm
  exact ⟨hcenter, subproblemOptOutput_prevPrefix_const setup ℓ hprefix,
    hfields.2.1, hfields.2.2⟩

/-- Corrected outer boundary supplier for the fixed-run initial gradient memory.

This is the compiled consumer-local evidence that the actual-offset prefix
source-domain component of `outerPrefixHatSourceDomain` is not a spare wrapper:
it is exactly the premise needed by the generated Algorithm 6.8 induction
`outerProcess_initialGradientMemory_of_sourceDomainPrefix`, after rewriting the
paper center `x̄^{ℓ-1}` to the selected generated outer state. -/
theorem outerPrefixHatSourceDomain_initialGradientMemory
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (ℓ : setup.OutputIndex)
    (houter_hat : setup.outerPrefixHatSourceDomain ℓ)
    (ω₀ : Ω) :
    let z : E := setup.outerCenter ℓ.1 ω₀
    let xMem0 : ι → E := (setup.ambientProcess (ℓ.1 - 1) ω₀).xBarMem
    let yMem0 : ι → E := (setup.ambientProcess (ℓ.1 - 1) ω₀).yBarMem
    (∀ i : ι, xMem0 i ∈ setup.X) ∧
      ∀ hxMem : ∀ i : ι, xMem0 i ∈ setup.X,
        setup.ambientFixedInitialGradientMemory z xMem0 yMem0 hxMem := by
  classical
  let z : E := setup.outerCenter ℓ.1 ω₀
  let xMem0 : ι → E := (setup.ambientProcess (ℓ.1 - 1) ω₀).xBarMem
  let yMem0 : ι → E := (setup.ambientProcess (ℓ.1 - 1) ω₀).yBarMem
  have hIcc : ℓ.1 ∈ Finset.Icc 1 (setup.k : ℕ) := by
    simpa [RandomizedAcceleratedProximalPointSetup.outputWindow] using ℓ.2
  have hbounds := Finset.mem_Icc.mp hIcc
  have hcenter :
      setup.outerCenter ℓ.1 ω₀ = setup.xBarIter (ℓ.1 - 1) ω₀ :=
    outerCenter_eq_xBarIter_pred setup ℓ ω₀
  have hsource_requirements :
      (∀ i : ι, xMem0 i ∈ setup.X) ∧
        setup.ambientFixedSourceDomain 0 z z xMem0 yMem0
          (by simpa [z] using setup.outerCenter_mem ℓ ω₀)
          (by simpa [z] using setup.outerCenter_mem ℓ ω₀) ∧
        setup.ambientFixedHatSourceDomain 0 z z xMem0 yMem0
          (by simpa [z] using setup.outerCenter_mem ℓ ω₀)
          (by simpa [z] using setup.outerCenter_mem ℓ ω₀) := by
    simpa [z, xMem0, yMem0] using
      setup.outerPrefixHatSourceDomain_base ℓ houter_hat ω₀
  refine ⟨hsource_requirements.1, ?_⟩
  intro hxMem
  have hn_pred : ℓ.1 - 1 ≤ (setup.k : ℕ) := by
    exact Nat.le_trans (Nat.sub_le ℓ.1 1) hbounds.2
  have hactualPrefix :
      setup.outerGeneratedFixedSourceDomainPrefix (ℓ.1 - 1) ω₀ :=
    setup.outerPrefixHatSourceDomain_actualOffsetPrefix ℓ houter_hat ω₀
  have hprefix_grad :
      setup.ambientFixedInitialGradientMemory
        (setup.ambientProcess (ℓ.1 - 1) ω₀).xBar
        (setup.ambientProcess (ℓ.1 - 1) ω₀).xBarMem
        (setup.ambientProcess (ℓ.1 - 1) ω₀).yBarMem hxMem :=
    (setup.outerProcess_initialGradientMemory_of_sourceDomainPrefix
      (ℓ.1 - 1) hn_pred ω₀ hactualPrefix).2 hxMem
  have hcenter_eq :
      z = (setup.ambientProcess (ℓ.1 - 1) ω₀).xBar := by
    simpa [z, RandomizedAcceleratedProximalPointSetup.xBarIter] using hcenter
  simpa [z, xMem0, yMem0, hcenter_eq] using hprefix_grad

/-- Within-gradient of the exact proximal subproblem objective at a feasible point.

Aligns with Lan Eq. (6.6.43)-(6.6.44): differentiating the exact proximal
subproblem `(1/m)∑ᵢ ψᵢ^ℓ + φ^ℓ` gives
`∇f(x) + 3μ (x-\bar{x}^{ℓ-1})`.  Considered
`Convex.first_order_condition_of_isMinOn_hasFDerivWithinAt` and
`gradPsiOnAt_hasGradientWithinAt`; the former consumes this derivative but does
not provide it, while the latter supplies the component derivative that must be
summed and combined with the local quadratic `phiAt_hasGradientAt`. -/
theorem subproblemObjective_hasGradientWithinAt
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (ℓ : setup.OutputIndex) (ω : Ω) (x : {x : E // x ∈ setup.X}) :
    HasGradientWithinAt (setup.subproblemObjective ℓ.1 ω)
      (setup.gradFOn x + (3 * setup.μ) • (x.1 - setup.outerCenter ℓ.1 ω))
      setup.X x.1 := by
  classical
  let z : E := setup.outerCenter ℓ.1 ω
  have hcard_ne : (Fintype.card ι : ℝ) ≠ 0 := by
    have hpos : 0 < Fintype.card ι := Fintype.card_pos
    exact_mod_cast Nat.ne_of_gt hpos
  have hcard_inv : ((Fintype.card ι : ℝ)⁻¹ * (Fintype.card ι : ℝ)) = 1 := by
    field_simp [hcard_ne]
  have h :
      HasGradientWithinAt
        (fun y : E =>
          (Fintype.card ι : ℝ)⁻¹ *
              Finset.sum Finset.univ (fun i : ι => setup.psi ℓ.1 i ω y) +
            (setup.μ / 2) * ‖y - z‖ ^ 2)
        (((Fintype.card ι : ℝ)⁻¹ •
            Finset.sum Finset.univ (fun i : ι => setup.gradPsiOnAt z i x)) +
          setup.μ • (x.1 - z)) setup.X x.1 :=
    (SOptLib.HasGradientWithinAt.fintype_average_add_centered_quadratic
      (F := fun i : ι => setup.psi ℓ.1 i ω)
      (gradF := fun i : ι => fun _ : E => setup.gradPsiOnAt z i x)
      (X := setup.X) (mu := setup.μ) (z := z) (x := x.1)
      (by
        intro i
        simpa [z, RandomizedAcceleratedProximalPointSetup.psi,
          RandomizedAcceleratedProximalPointSetup.gradPsiOn] using
          setup.gradPsiOnAt_hasGradientWithinAt z i x))
  convert h using 1
  · simp [z, RandomizedAcceleratedProximalPointSetup.subproblemObjective,
      RandomizedAcceleratedProximalPointSetup.phi,
      RandomizedAcceleratedProximalPointSetup.phiAt,
      SOptLib.centeredQuadraticPotential,
      RandomizedAcceleratedProximalPointSetup.gradPsiOnAt,
      RandomizedAcceleratedProximalPointSetup.gradFOn, z, Finset.sum_add_distrib,
      Finset.sum_const]
    simp [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, hcard_inv]
    module

/-- Exact subproblem optimality gives the normal-cone certificate used in
Theorem 6.16.

Aligns with Lan Eq. (6.6.43)-(6.6.45): apply the constrained first-order
condition to the exact proximal subproblem minimizer and rewrite the resulting
variational inequality as membership in `-N_X`. -/
theorem subproblem_opt_certificate_mem_negativeNormalCone
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (ℓ : setup.OutputIndex) (ω : Ω) :
    setup.gradFOn
          ⟨setup.subproblemOptOutput ℓ ω, setup.subproblemOptOutput_mem ℓ ω⟩ +
        (3 * setup.μ) •
          (setup.subproblemOptOutput ℓ ω - setup.outerCenter ℓ.1 ω) ∈
      setup.negativeNormalCone (setup.subproblemOptOutput ℓ ω) := by
  classical
  let x : {x : E // x ∈ setup.X} :=
    ⟨setup.subproblemOptOutput ℓ ω, setup.subproblemOptOutput_mem ℓ ω⟩
  let G : E :=
    setup.gradFOn x + (3 * setup.μ) • (x.1 - setup.outerCenter ℓ.1 ω)
  have hIcc : ℓ.1 ∈ Finset.Icc 1 (setup.k : ℕ) := by
    simpa [RandomizedAcceleratedProximalPointSetup.outputWindow] using ℓ.2
  have hmin : IsMinOn (setup.subproblemObjective ℓ.1 ω) setup.X x.1 := by
    simpa [x, RandomizedAcceleratedProximalPointSetup.subproblemOptOutput] using
      setup.subproblemOpt_is_minimizer ℓ.1 hIcc ω
  have hderiv : HasGradientWithinAt (setup.subproblemObjective ℓ.1 ω) G setup.X x.1 := by
    simpa [G, x] using subproblemObjective_hasGradientWithinAt setup ℓ ω x
  simpa [G, x, RandomizedAcceleratedProximalPointSetup.negativeNormalCone,
    RandomizedAcceleratedProximalPointSetup.normalCone] using
    (SOptLib.mem_negativeNormalCone_of_isMinOn_hasGradientWithinAt
      (X := setup.X) (f := setup.subproblemObjective ℓ.1 ω)
      (x := x.1) (G := G) setup.hX_convex x.2 hmin hderiv)

/-- Pointwise stationarity residual bound for the exact selected subproblem
solution.

Aligns with the proof of Lan Theorem 6.16 after Eq. (6.6.45): the normal-cone
certificate from exact proximal optimality is used as the witness in
`Metric.infDist_le_dist_of_mem`, reducing the stationarity gap to the previous
proximal displacement. -/
theorem subproblem_opt_stationarity_gap_sq_le_previous_displacement
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (ℓ : setup.OutputIndex) (ω : Ω) :
    (setup.normalConeGapOn
        ⟨setup.subproblemOptOutput ℓ ω, setup.subproblemOptOutput_mem ℓ ω⟩) ^ 2 ≤
      (3 * setup.μ) ^ 2 *
        ‖setup.subproblemOptOutput ℓ ω - setup.xBarIter (ℓ.1 - 1) ω‖ ^ 2 := by
  classical
  simpa [RandomizedAcceleratedProximalPointSetup.normalConeGapOn,
    outerCenter_eq_xBarIter_pred setup ℓ ω] using
    (SOptLib.normalConeGap_sq_le_sq_mul_norm_sub_sq_of_affine_certificate
      (X := setup.X)
      (grad := setup.gradFOn
        ⟨setup.subproblemOptOutput ℓ ω, setup.subproblemOptOutput_mem ℓ ω⟩)
      (x := setup.subproblemOptOutput ℓ ω)
      (c := setup.outerCenter ℓ.1 ω)
      (a := 3 * setup.μ)
      (hcert := by
        simpa [RandomizedAcceleratedProximalPointSetup.negativeNormalCone,
          RandomizedAcceleratedProximalPointSetup.normalCone] using
          subproblem_opt_certificate_mem_negativeNormalCone setup ℓ ω))

/-- The pointwise normal-cone estimate lifts through the uniformly selected output
window.

Aligns with Lan Theorem 6.16 after Eq. (6.6.45): average the exact-subproblem
stationarity residual bound over the random outer index `\hat{\ell}`.  SOptLib
finite-window selected-output lemmas were considered, but the local
`randomOuterAverageWindow` is already the literal uniform `[k]` average, so this
proof uses direct `integral_mono` and `Finset.sum_le_sum`. -/
theorem selectedStationarity_le_scaled_selectedPreviousProxDisplacement
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω) :
    setup.selectedStationarity ≤
      (3 * setup.μ) ^ 2 * setup.selectedPreviousProxDisplacement := by
  classical
  let c : ℝ := (3 * setup.μ) ^ 2
  have hpoint :
      ∀ ℓ : setup.OutputIndex, ∀ ω : Ω,
        setup.selectedStationarityIntegrand ℓ ω ≤
          c * setup.selectedPreviousProxDisplacementIntegrand ℓ ω := by
    intro ℓ ω
    simpa [c, RandomizedAcceleratedProximalPointSetup.selectedStationarityIntegrand,
      RandomizedAcceleratedProximalPointSetup.selectedPreviousProxDisplacementIntegrand]
      using subproblem_opt_stationarity_gap_sq_le_previous_displacement setup ℓ ω
  unfold RandomizedAcceleratedProximalPointSetup.selectedStationarity
    RandomizedAcceleratedProximalPointSetup.selectedPreviousProxDisplacement
    RandomizedAcceleratedProximalPointSetup.randomOuterExpectation
    RandomizedAcceleratedProximalPointSetup.randomOuterAverageWindow
  simpa [SOptLib.normalizedWeightedExpectedCertificate, c] using
    (SOptLib.normalizedWeightedExpectedCertificate_le_const_mul
      (times := setup.outputWindow.attach)
      (denom := ((setup.k : ℕ) : ℝ))
      (c := c)
      (w := fun _ℓ : setup.OutputIndex => 1)
      (μ := setup.P)
      (A := setup.selectedStationarityIntegrand)
      (B := setup.selectedPreviousProxDisplacementIntegrand)
      (hdenom_inv_nonneg := by positivity)
      (hw_nonneg := by intro ℓ hℓ; positivity)
      (hA_int := by intro ℓ hℓ; exact setup.selectedStationarityIntegrand_integrable ℓ)
      (hB_int := by
        intro ℓ hℓ
        exact setup.selectedPreviousProxDisplacementIntegrand_integrable ℓ)
      (hpoint := by intro ℓ hℓ; exact ae_of_all setup.P (hpoint ℓ)))

/-- The Lemma 6.14 current-displacement observable is exactly Theorem 6.16's
output-proximity observable.

Aligns with Lan Theorem 6.16's second bound: the reported output is
`\bar{x}^{\hat{\ell}}`, so the current exact-subproblem displacement differs
from the output-proximity integrand only by norm symmetry. -/
theorem selectedCurrentProxDisplacement_eq_selectedOutputProximity
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω) :
    setup.selectedCurrentProxDisplacement = setup.selectedOutputProximity := by
  classical
  unfold RandomizedAcceleratedProximalPointSetup.selectedCurrentProxDisplacement
    RandomizedAcceleratedProximalPointSetup.selectedOutputProximity
    RandomizedAcceleratedProximalPointSetup.randomOuterExpectation
    RandomizedAcceleratedProximalPointSetup.randomOuterAverageWindow
  congr 1
  refine Finset.sum_congr rfl ?_
  intro ℓ _hℓ
  congr 1
  funext ω
  simp [RandomizedAcceleratedProximalPointSetup.selectedCurrentProxDisplacementObservable,
    RandomizedAcceleratedProximalPointSetup.selectedOutputProximityObservable,
    RandomizedAcceleratedProximalPointSetup.selectedCurrentProxDisplacementIntegrand,
    RandomizedAcceleratedProximalPointSetup.selectedOutputProximityIntegrand,
    RandomizedAcceleratedProximalPointSetup.xBarOutput,
    RandomizedAcceleratedProximalPointSetup.subproblemOptOutput,
    norm_sub_rev]

/-- Eq. (6.6.16) places the inner contraction factor in `(0, 1)`.

Aligns with Lan Eq. (6.6.16) for Theorem 6.16.  Considered SOptLib
`ceil_log_div_log_pos_of_one_lt_div`, `ceil_log_two_div_le_three_log_one_div_over_log_two`,
and the local selected-output helpers from the pre-search digest; none match because
this helper is the literal `α = 1 - 2/(m(√(1+16c/m)+1))` sign package, not a
ceiling selector or output-window transport fact. -/
theorem alpha_schedule_bounds_for_theorem_6_16
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (hα_schedule :
      setup.α =
        1 - 2 / ((Fintype.card ι : ℝ) *
          (Real.sqrt (1 + 16 * (2 + setup.L / setup.μ) / (Fintype.card ι : ℝ)) + 1))) :
    0 < setup.α ∧ setup.α < 1 ∧ Real.log setup.α < 0 := by
  refine SOptLib.sqrt_alpha_schedule_pos_lt_one_log_neg
    (Fintype.card ι : ℝ) (2 + setup.L / setup.μ) setup.α ?_ ?_ hα_schedule
  · exact_mod_cast (Nat.succ_le_of_lt (Fintype.card_pos : 0 < Fintype.card ι))
  · have hratio_ge_one : 1 ≤ setup.L / setup.μ := by
      rw [le_div_iff₀ setup.hμ_pos]
      simpa using setup.hμ_le_L
    nlinarith

/-- A negative-log ceiling schedule for a base `α ∈ (0, 1)` gives the corresponding
inverse power bound.

Aligns with Lan Theorem 6.16's exact inner-loop length after Eq. (6.6.16).
Considered SOptLib `ceil_log_div_log_pos_of_one_lt_div`,
`ceil_log_two_div_le_three_log_one_div_over_log_two`, `le_positive_ceil_max_one`,
and `natCast_max_one_ceil_le_add_two`; none match because those helpers bound
positive-log ceilings, while this proof needs a negative logarithmic denominator
and the conversion from `Nat.ceil` to `α^s ≤ B⁻¹`. -/
theorem ceil_log_alpha_schedule_pow_le_inv
    {α B : ℝ} {s : ℕ}
    (hα0 : 0 < α) (hα1 : α < 1) (hB : 0 < B)
    (hs : s = Nat.ceil (-Real.log B / Real.log α)) :
    α ^ s ≤ B⁻¹ := by
  have hs_le : -Real.log B / Real.log α ≤ (s : ℝ) := by
    rw [hs]
    exact Nat.le_ceil _
  exact pow_nat_le_inv_of_neg_log_div_log_le hα0 hα1 hB hs_le

/-- The exact `M_F` inner-loop length in Theorem 6.16 gives both scalar power
bounds used after Lemma 6.14.

Aligns with Lan Theorem 6.16 after Eq. (6.6.45).  The pre-searched selected-output
and stationarity helpers are downstream observable transports, while SOptLib
ceiling helpers such as `ceil_log_div_log_pos_of_one_lt_div` and
`ceil_log_two_div_le_three_log_one_div_over_log_two` do not contain the paper's
`M_F = M * max {6/5, (L/μ)^2}` schedule; this helper specializes the proved
negative-log ceiling bridge to that literal source expression. -/
theorem theorem_6_16_power_bounds
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (hα_schedule :
      setup.α =
        1 - 2 / ((Fintype.card ι : ℝ) *
          (Real.sqrt (1 + 16 * (2 + setup.L / setup.μ) / (Fintype.card ι : ℝ)) + 1)))
    (hs_schedule :
      setup.s =
        Nat.ceil
          (-Real.log
            (6 * (5 + 2 * setup.L / setup.μ) *
              max (6 / 5 : ℝ) ((setup.L / setup.μ) ^ 2)) /
            Real.log setup.α)) :
    let M : ℝ := 6 * (5 + 2 * setup.L / setup.μ)
    (M * setup.α ^ setup.s ≤ 5 / 6) ∧
      (M * setup.α ^ setup.s ≤ setup.μ ^ 2 / setup.L ^ 2) := by
  classical
  rcases alpha_schedule_bounds_for_theorem_6_16 setup hα_schedule with
    ⟨hα_pos, hα_lt_one, _hlogα_neg⟩
  let M : ℝ := 6 * (5 + 2 * setup.L / setup.μ)
  let R : ℝ := setup.L / setup.μ
  let C : ℝ := max (6 / 5 : ℝ) (R ^ 2)
  let MF : ℝ := M * C
  have hL_pos : 0 < setup.L := setup.L_pos
  have hμ_ne : setup.μ ≠ 0 := ne_of_gt setup.hμ_pos
  have hL_ne : setup.L ≠ 0 := ne_of_gt hL_pos
  have hR_ge_one : 1 ≤ R := by
    dsimp [R]
    rw [le_div_iff₀ setup.hμ_pos]
    simpa using setup.hμ_le_L
  have hR_pos : 0 < R := lt_of_lt_of_le zero_lt_one hR_ge_one
  have hM_pos : 0 < M := by
    have hinside : 0 < 5 + 2 * setup.L / setup.μ := by
      have hterm_pos : 0 < 2 * setup.L / setup.μ := by
        exact div_pos (mul_pos (by norm_num) hL_pos) setup.hμ_pos
      linarith
    dsimp [M]
    exact mul_pos (by norm_num) hinside
  have hC_ge_65 : (6 / 5 : ℝ) ≤ C := by
    dsimp [C]
    exact le_max_left _ _
  have hC_ge_Rsq : R ^ 2 ≤ C := by
    dsimp [C]
    exact le_max_right _ _
  have hC_pos : 0 < C := lt_of_lt_of_le (by norm_num) hC_ge_65
  have hMF_pos : 0 < MF := by
    dsimp [MF]
    exact mul_pos hM_pos hC_pos
  have hs_MF : setup.s = Nat.ceil (-Real.log MF / Real.log setup.α) := by
    simpa [MF, M, C, R, mul_assoc] using hs_schedule
  have hpow : setup.α ^ setup.s ≤ MF⁻¹ :=
    ceil_log_alpha_schedule_pow_le_inv hα_pos hα_lt_one hMF_pos hs_MF
  have hbounds :
      M * setup.α ^ setup.s ≤ (6 / 5 : ℝ)⁻¹ ∧
        M * setup.α ^ setup.s ≤ (R ^ 2)⁻¹ := by
    exact
      mul_le_inv_bounds_of_le_inv_mul_max_bound
        hM_pos (by norm_num) (sq_pos_of_pos hR_pos) hC_ge_65 hC_ge_Rsq
        (by simpa [MF] using hpow)
  have hq_le_Cinv : M * setup.α ^ setup.s ≤ (6 / 5 : ℝ)⁻¹ := hbounds.1
  have hCinv_le_56 : (6 / 5 : ℝ)⁻¹ ≤ 5 / 6 := by norm_num
  have hCinv_le_muL : (R ^ 2)⁻¹ ≤ setup.μ ^ 2 / setup.L ^ 2 := by
    have hRsq_inv :
        (R ^ 2)⁻¹ = setup.μ ^ 2 / setup.L ^ 2 := by
      dsimp [R]
      field_simp [hμ_ne, hL_ne]
    simpa [hRsq_inv]
  exact ⟨le_trans hq_le_Cinv hCinv_le_56, le_trans hbounds.2 hCinv_le_muL⟩

/-- The exact `M_F` ceiling schedule is long enough for Lemma 6.14's printed
`7M/6` ceiling premise.

Aligns with Lan Lemma 6.14 as invoked in Theorem 6.16.  SOptLib ceiling helpers
`ceil_log_div_log_pos_of_one_lt_div`, `le_positive_ceil_max_one`, and
`Nat.ceil` upper-bound utilities were considered; none match because this is a
monotonicity comparison between the paper's two same-source logarithmic ceilings
with the negative denominator `log α`. -/
theorem theorem_6_16_hs_lower
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (hα_schedule :
      setup.α =
        1 - 2 / ((Fintype.card ι : ℝ) *
          (Real.sqrt (1 + 16 * (2 + setup.L / setup.μ) / (Fintype.card ι : ℝ)) + 1)))
    (hs_schedule :
      setup.s =
        Nat.ceil
          (-Real.log
            (6 * (5 + 2 * setup.L / setup.μ) *
              max (6 / 5 : ℝ) ((setup.L / setup.μ) ^ 2)) /
            Real.log setup.α)) :
    setup.s ≥
      Nat.ceil
        (-Real.log (7 * (6 * (5 + 2 * setup.L / setup.μ)) / 6) /
          Real.log setup.α) := by
  classical
  rcases alpha_schedule_bounds_for_theorem_6_16 setup hα_schedule with
    ⟨hα_pos, hα_lt_one, _hlogα_neg⟩
  let M : ℝ := 6 * (5 + 2 * setup.L / setup.μ)
  let R : ℝ := setup.L / setup.μ
  let C : ℝ := max (6 / 5 : ℝ) (R ^ 2)
  let A : ℝ := 7 * M / 6
  let MF : ℝ := M * C
  have hL_pos : 0 < setup.L := setup.L_pos
  have hM_pos : 0 < M := by
    have hinside : 0 < 5 + 2 * setup.L / setup.μ := by
      have hterm_pos : 0 < 2 * setup.L / setup.μ := by
        exact div_pos (mul_pos (by norm_num) hL_pos) setup.hμ_pos
      linarith
    dsimp [M]
    exact mul_pos (by norm_num) hinside
  have hA_pos : 0 < A := by
    dsimp [A]
    positivity
  have hA_le_MF : A ≤ MF := by
    have hmul : M * (7 / 6 : ℝ) ≤ M * C := by
      refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hM_pos)
      have hC_ge_65 : (6 / 5 : ℝ) ≤ C := by
        dsimp [C]
        exact le_max_left _ _
      linarith
    dsimp [A, MF]
    linarith
  rw [hs_schedule]
  simpa [A, MF, M, C, R, mul_assoc] using
    (natCeil_neg_log_div_log_mono_of_base_lt_one
      (alpha := setup.α) (A := A) (B := MF)
      hα_pos hα_lt_one hA_pos hA_le_MF)

/-- The complete scalar schedule package extracted from Theorem 6.16's exact
inner-loop length.

Aligns with Lan Theorem 6.16's use of Eq. (6.6.16) immediately before applying
Lemma 6.14.  Existing SOptLib ceiling and output-selection candidates were
considered in the component helpers above; this package only bundles the proved
same-source consequences, so downstream proofs can consume the source-derived
schedule facts without adding theorem-head assumptions. -/
theorem theorem_6_16_schedule_bounds
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (hα_schedule :
      setup.α =
        1 - 2 / ((Fintype.card ι : ℝ) *
          (Real.sqrt (1 + 16 * (2 + setup.L / setup.μ) / (Fintype.card ι : ℝ)) + 1)))
    (hs_schedule :
      setup.s =
        Nat.ceil
          (-Real.log
            (6 * (5 + 2 * setup.L / setup.μ) *
              max (6 / 5 : ℝ) ((setup.L / setup.μ) ^ 2)) /
            Real.log setup.α)) :
    let M : ℝ := 6 * (5 + 2 * setup.L / setup.μ)
    setup.s ≥
        Nat.ceil
          (-Real.log (7 * M / 6) / Real.log setup.α) ∧
      M * setup.α ^ setup.s ≤ 5 / 6 ∧
      M * setup.α ^ setup.s ≤ setup.μ ^ 2 / setup.L ^ 2 := by
  classical
  let M : ℝ := 6 * (5 + 2 * setup.L / setup.μ)
  have hs_lower := theorem_6_16_hs_lower setup hα_schedule hs_schedule
  have hpow := theorem_6_16_power_bounds setup hα_schedule hs_schedule
  simpa [M] using And.intro hs_lower hpow

/-- Scalar absorption for the stationarity branch of Theorem 6.16 after Lemma 6.14.

Aligns with Lan Theorem 6.16 after Eq. (6.6.45), where `q = M α^s ≤ 5/6`
turns the Lemma 6.14 previous-displacement coefficient into `4/(k μ)`, then the
normal-cone bridge contributes `(3μ)^2`.  SOptLib algebraic absorption helpers
for Young/completion-square and telescope budgets were considered; none match this
specific rational coefficient `(1-q)/(6-7q)` with denominator `6-7q`. -/
theorem theorem_6_16_stationarity_scalar_absorb
    {μ k q gap : ℝ} (hμ : 0 < μ) (hk : 0 < k) (hgap : 0 ≤ gap)
    (hq56 : q ≤ 5 / 6) :
    (3 * μ) ^ 2 * (4 * (1 - q) / (k * (μ * (6 - 7 * q))) * gap) ≤
      36 * μ / k * gap := by
  have hden_pos : 0 < 6 - 7 * q := by nlinarith
  have hratio : (1 - q) / (6 - 7 * q) ≤ 1 := by
    rw [div_le_one hden_pos]
    nlinarith
  have hcoeff :
      (3 * μ) ^ 2 * (4 * (1 - q) / (k * (μ * (6 - 7 * q)))) ≤
        36 * μ / k := by
    calc
      (3 * μ) ^ 2 * (4 * (1 - q) / (k * (μ * (6 - 7 * q)))) =
          (36 * μ / k) * ((1 - q) / (6 - 7 * q)) := by
        field_simp [ne_of_gt hμ, ne_of_gt hk, ne_of_gt hden_pos]
        ring
      _ ≤ (36 * μ / k) * 1 :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = 36 * μ / k := by ring
  calc
    (3 * μ) ^ 2 * (4 * (1 - q) / (k * (μ * (6 - 7 * q))) * gap) =
        ((3 * μ) ^ 2 * (4 * (1 - q) / (k * (μ * (6 - 7 * q))))) * gap := by
      ring
    _ ≤ 36 * μ / k * gap := mul_le_mul_of_nonneg_right hcoeff hgap

/-- Scalar absorption for the output-proximity branch of Theorem 6.16 after
Lemma 6.14.

Aligns with Lan Theorem 6.16 after Eq. (6.6.45): `q ≤ 5/6` makes
`6-7q` positive with enough slack, and `q ≤ μ²/L²` converts the remaining
`q/μ` coefficient into `μ/L²`.  The SOptLib scalar helpers searched above cover
Young inequalities and telescope-budget substitutions, not this paper-specific
`q/(6-7q)` rational absorption. -/
theorem theorem_6_16_proximity_scalar_absorb
    {μ L k q gap : ℝ} (hμ : 0 < μ) (hL : 0 < L) (hk : 0 < k)
    (hgap : 0 ≤ gap) (hq56 : q ≤ 5 / 6) (hqL : q ≤ μ ^ 2 / L ^ 2) :
    (2 * q / (3 * k * (μ * (6 - 7 * q))) * gap) ≤
      4 * μ / (k * L ^ 2) * gap := by
  have hden_pos : 0 < 6 - 7 * q := by nlinarith
  have hden_ge : (1 / 6 : ℝ) ≤ 6 - 7 * q := by nlinarith
  have hL_ne : L ≠ 0 := ne_of_gt hL
  have hqL_mul : q * L ^ 2 ≤ μ ^ 2 := by
    calc
      q * L ^ 2 ≤ (μ ^ 2 / L ^ 2) * L ^ 2 :=
        mul_le_mul_of_nonneg_right hqL (sq_nonneg L)
      _ = μ ^ 2 := by
        field_simp [hL_ne]
  have hcoeff :
      2 * q / (3 * k * (μ * (6 - 7 * q))) ≤
        4 * μ / (k * L ^ 2) := by
    field_simp [ne_of_gt hμ, ne_of_gt hL, ne_of_gt hk, ne_of_gt hden_pos]
    have hleft : 2 * q * L ^ 2 ≤ 2 * μ ^ 2 := by nlinarith
    have hright : 2 * μ ^ 2 ≤ 12 * μ ^ 2 * (6 - 7 * q) := by
      have hμsq_nonneg : 0 ≤ μ ^ 2 := sq_nonneg μ
      nlinarith
    calc
      2 * q * L ^ 2 / (6 - q * 7) =
          2 * q * L ^ 2 / (6 - 7 * q) := by ring
      _ ≤ 2 * μ ^ 2 / (6 - 7 * q) :=
          div_le_div_of_nonneg_right hleft (le_of_lt hden_pos)
      _ ≤ 12 * μ ^ 2 := (div_le_iff₀ hden_pos).mpr hright
      _ = 3 * μ ^ 2 * 4 := by ring
  exact mul_le_mul_of_nonneg_right hcoeff hgap

/-- Uniform one-hot finite average for a single refreshed component.

SOptLib candidates `finset_weighted_residual_sum_eq_zero`,
`finset_weighted_variance_eq_second_moment_sub_norm_mean_sq`,
`weighted_variance_le_second_moment`, `weighted_sq_norm_sub_center_le`,
`finite_window_weighted_recurrence_telescope_with_tail_sums`, and
`summed_one_step_gap_bound_of_telescope` were considered; none match because
Lemma 6.12 needs the literal Algorithm 6.9 one-index `if` refresh average rather
than residual centering, variance, norm, or telescope algebra. -/
theorem currentIndexAverage_ite_eq_inv_card_smul_sub_add
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (i : ι) (a b : V) :
    RandomizedAcceleratedProximalPointSetup.currentIndexAverage
        (fun j : ι => if i = j then a else b) =
      ((Fintype.card ι : ℝ)⁻¹) • (a - b) + b := by
  simpa [RandomizedAcceleratedProximalPointSetup.currentIndexAverage] using
    (finite_uniform_average_ite_eq_inv_card_smul_sub_add (i := i) (a := a) (b := b))

/-- Lemma 6.12 finite-conditioning identity for scalar/vector refreshed values.

This is the direct module form of the one-hot average above, aligned with Lan
Lemma 6.12's conditioning on whether the uniform index equals `i`. -/
theorem currentIndexAverage_ite_update_module
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (i : ι) (a b : V) :
    a =
      (Fintype.card ι : ℝ) •
          RandomizedAcceleratedProximalPointSetup.currentIndexAverage
            (fun j : ι => if i = j then a else b) -
        ((Fintype.card ι : ℝ) - 1) • b := by
  classical
  let n : ℝ := Fintype.card ι
  have hcard_ne : n ≠ 0 := by
    have hpos : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr inferInstance
    have hcard_ne' : (Fintype.card ι : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt hpos
    simpa [n] using hcard_ne'
  rw [currentIndexAverage_ite_eq_inv_card_smul_sub_add (i := i) (a := a) (b := b)]
  change a = n • (n⁻¹ • (a - b) + b) - (n - 1) • b
  rw [smul_add, smul_smul]
  have hmul : n * n⁻¹ = 1 := by
    field_simp [hcard_ne]
  rw [hmul, one_smul]
  module

/-- Lemma 6.12 estimator-update average for Eq. (6.6.12).

This consumes the same one-hot average algebra as the preceding helper and
matches the paper substitution `ỹᵢᵗ = m(yᵢᵗ-yᵢᵗ⁻¹)+yᵢᵗ⁻¹`. -/
theorem currentIndexAverage_estimator_update_eq
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (i : ι) (a b : V) :
    RandomizedAcceleratedProximalPointSetup.currentIndexAverage
        (fun j : ι =>
          if i = j then (Fintype.card ι : ℝ) • (a - b) + b else b) =
      a := by
  classical
  let n : ℝ := Fintype.card ι
  have hcard_ne : n ≠ 0 := by
    have hpos : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr inferInstance
    have hcard_ne' : (Fintype.card ι : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt hpos
    simpa [n] using hcard_ne'
  rw [currentIndexAverage_ite_eq_inv_card_smul_sub_add
    (i := i) (a := (Fintype.card ι : ℝ) • (a - b) + b) (b := b)]
  change n⁻¹ • ((n • (a - b) + b) - b) + b = a
  rw [add_sub_cancel_right, smul_smul]
  have hmul : n⁻¹ * n = 1 := by
    field_simp [hcard_ne]
  rw [hmul, one_smul]
  module

/-- Averaged `δ₂` inner-product algebra after Lemma 6.12.

This is the finite-current-index expansion used in Lan Eq. (6.6.30): once
`currentIndexAverage (fun j => y j i) = g i`, the averaged displayed `δ₂`
summand can be rewritten as the averaged source inner product
`⟪y_j i - g*_i, xTilde - xNext_j⟫`.  SOptLib candidates
`finset_weighted_residual_sum_eq_zero`, `integral_selected_finite_index_prod_eq_sum_weights`,
and the target-file `currentIndexAverage_estimator_update_eq` were considered;
none states this exact inner-product expansion, because the first is residual
centering, the second is a measure-product integral rule, and the third supplies
only the estimator mean used as this helper's hypothesis. -/
theorem currentIndexAverage_delta2_component_inner_product_expansion
    (g gStar : E) (xTilde xNextStar : E)
    (y : ι → E) (xNext : ι → E)
    (hyavg :
      RandomizedAcceleratedProximalPointSetup.currentIndexAverage y = g) :
    Finset.sum Finset.univ
        (fun j : ι =>
          ⟪g - gStar, xTilde⟫_ℝ -
              ⟪y j - gStar, xNext j⟫_ℝ +
            ⟪y j - g, xNextStar⟫_ℝ) =
      Finset.sum Finset.univ
        (fun j : ι =>
          ⟪y j - gStar, xTilde - xNext j⟫_ℝ) := by
  classical
  let c : ℝ := Fintype.card ι
  change c⁻¹ • Finset.sum Finset.univ y = g at hyavg
  have hcard_pos_nat : 0 < Fintype.card ι :=
    Fintype.card_pos_iff.mpr inferInstance
  have hc_ne : c ≠ 0 := by
    have hc_ne' : (Fintype.card ι : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt hcard_pos_nat
    simpa [c] using hc_ne'
  have hy_sum : Finset.sum Finset.univ y = c • g := by
    have hmul : c * c⁻¹ = 1 := mul_inv_cancel₀ hc_ne
    have hscaled := congrArg (fun v : E => c • v) hyavg
    simpa [smul_smul, hmul] using hscaled
  have hconst_sum : Finset.sum Finset.univ (fun _j : ι => g) = c • g := by
    calc
      Finset.sum Finset.univ (fun _j : ι => g) = Fintype.card ι • g := by
        rw [Finset.sum_const]
        rfl
      _ = (Fintype.card ι : ℝ) • g := by
        rw [← Nat.cast_smul_eq_nsmul ℝ]
      _ = c • g := by
        rfl
  have hres : Finset.sum Finset.univ (fun j : ι => y j - g) = 0 := by
    calc
      Finset.sum Finset.univ (fun j : ι => y j - g)
          = Finset.sum Finset.univ y -
              Finset.sum Finset.univ (fun _j : ι => g) := by
              rw [Finset.sum_sub_distrib]
      _ = c • g - c • g := by rw [hy_sum, hconst_sum]
      _ = 0 := sub_self (c • g)
  have hres_inner :
      Finset.sum Finset.univ (fun j : ι => ⟪y j - g, xNextStar⟫_ℝ) = 0 := by
    calc
      Finset.sum Finset.univ (fun j : ι => ⟪y j - g, xNextStar⟫_ℝ)
          = Finset.sum Finset.univ (fun j : ι => ⟪xNextStar, y j - g⟫_ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro j _hj
            exact (real_inner_comm (y j - g) xNextStar).symm
      _ = ⟪xNextStar, Finset.sum Finset.univ (fun j : ι => y j - g)⟫_ℝ := by
            exact (inner_sum Finset.univ (fun j : ι => y j - g) xNextStar).symm
      _ = ⟪xNextStar, 0⟫_ℝ := by rw [hres]
      _ = 0 := inner_zero_right xNextStar
  have hshift_sum :
      Finset.sum Finset.univ (fun j : ι => y j - gStar) =
        Finset.sum Finset.univ (fun _j : ι => g - gStar) := by
    calc
      Finset.sum Finset.univ (fun j : ι => y j - gStar)
          = Finset.sum Finset.univ
              (fun j : ι => (g - gStar) + (y j - g)) := by
              refine Finset.sum_congr rfl ?_
              intro j _hj
              rw [add_comm (g - gStar) (y j - g), sub_add_sub_cancel]
      _ = Finset.sum Finset.univ (fun _j : ι => g - gStar) +
            Finset.sum Finset.univ (fun j : ι => y j - g) := by
            rw [Finset.sum_add_distrib]
      _ = Finset.sum Finset.univ (fun _j : ι => g - gStar) := by
            rw [hres, add_zero]
  have hshift_inner :
      Finset.sum Finset.univ (fun j : ι => ⟪y j - gStar, xTilde⟫_ℝ) =
        Finset.sum Finset.univ (fun _j : ι => ⟪g - gStar, xTilde⟫_ℝ) := by
    calc
      Finset.sum Finset.univ (fun j : ι => ⟪y j - gStar, xTilde⟫_ℝ)
          = Finset.sum Finset.univ (fun j : ι => ⟪xTilde, y j - gStar⟫_ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro j _hj
            exact (real_inner_comm (y j - gStar) xTilde).symm
      _ = ⟪xTilde, Finset.sum Finset.univ (fun j : ι => y j - gStar)⟫_ℝ := by
            exact (inner_sum Finset.univ (fun j : ι => y j - gStar) xTilde).symm
      _ = ⟪xTilde, Finset.sum Finset.univ (fun _j : ι => g - gStar)⟫_ℝ := by
            rw [hshift_sum]
      _ = Finset.sum Finset.univ (fun _j : ι => ⟪xTilde, g - gStar⟫_ℝ) := by
            exact inner_sum Finset.univ (fun _j : ι => g - gStar) xTilde
      _ = Finset.sum Finset.univ (fun _j : ι => ⟪g - gStar, xTilde⟫_ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro j _hj
            exact (real_inner_comm xTilde (g - gStar)).symm
  have hleft_no_res :
      Finset.sum Finset.univ
          (fun j : ι =>
            ⟪g - gStar, xTilde⟫_ℝ -
                ⟪y j - gStar, xNext j⟫_ℝ +
              ⟪y j - g, xNextStar⟫_ℝ) =
        Finset.sum Finset.univ
          (fun j : ι =>
            ⟪g - gStar, xTilde⟫_ℝ - ⟪y j - gStar, xNext j⟫_ℝ) := by
    calc
      Finset.sum Finset.univ
          (fun j : ι =>
            ⟪g - gStar, xTilde⟫_ℝ -
                ⟪y j - gStar, xNext j⟫_ℝ +
              ⟪y j - g, xNextStar⟫_ℝ)
          =
        Finset.sum Finset.univ
            (fun j : ι =>
              ⟪g - gStar, xTilde⟫_ℝ - ⟪y j - gStar, xNext j⟫_ℝ) +
          Finset.sum Finset.univ
            (fun j : ι => ⟪y j - g, xNextStar⟫_ℝ) := by
            rw [Finset.sum_add_distrib]
      _ = Finset.sum Finset.univ
            (fun j : ι =>
              ⟪g - gStar, xTilde⟫_ℝ - ⟪y j - gStar, xNext j⟫_ℝ) := by
            rw [hres_inner, add_zero]
  have hreplace_const :
      Finset.sum Finset.univ
          (fun j : ι =>
            ⟪g - gStar, xTilde⟫_ℝ - ⟪y j - gStar, xNext j⟫_ℝ) =
        Finset.sum Finset.univ
          (fun j : ι =>
            ⟪y j - gStar, xTilde⟫_ℝ - ⟪y j - gStar, xNext j⟫_ℝ) := by
    calc
      Finset.sum Finset.univ
          (fun j : ι =>
            ⟪g - gStar, xTilde⟫_ℝ - ⟪y j - gStar, xNext j⟫_ℝ)
          =
        Finset.sum Finset.univ (fun _j : ι => ⟪g - gStar, xTilde⟫_ℝ) -
          Finset.sum Finset.univ (fun j : ι => ⟪y j - gStar, xNext j⟫_ℝ) := by
            rw [Finset.sum_sub_distrib]
      _ =
        Finset.sum Finset.univ (fun j : ι => ⟪y j - gStar, xTilde⟫_ℝ) -
          Finset.sum Finset.univ (fun j : ι => ⟪y j - gStar, xNext j⟫_ℝ) := by
            rw [hshift_inner]
      _ =
        Finset.sum Finset.univ
          (fun j : ι =>
            ⟪y j - gStar, xTilde⟫_ℝ - ⟪y j - gStar, xNext j⟫_ℝ) := by
            rw [Finset.sum_sub_distrib]
  have hright_expand :
      Finset.sum Finset.univ
          (fun j : ι =>
            ⟪y j - gStar, xTilde⟫_ℝ - ⟪y j - gStar, xNext j⟫_ℝ) =
        Finset.sum Finset.univ
          (fun j : ι =>
            ⟪y j - gStar, xTilde - xNext j⟫_ℝ) := by
    refine Finset.sum_congr rfl ?_
    intro j _hj
    rw [inner_sub_right]
  calc
    Finset.sum Finset.univ
        (fun j : ι =>
          ⟪g - gStar, xTilde⟫_ℝ -
              ⟪y j - gStar, xNext j⟫_ℝ +
            ⟪y j - g, xNextStar⟫_ℝ)
        = Finset.sum Finset.univ
            (fun j : ι =>
              ⟪g - gStar, xTilde⟫_ℝ - ⟪y j - gStar, xNext j⟫_ℝ) := hleft_no_res
    _ = Finset.sum Finset.univ
            (fun j : ι =>
              ⟪y j - gStar, xTilde⟫_ℝ - ⟪y j - gStar, xNext j⟫_ℝ) := hreplace_const
    _ = Finset.sum Finset.univ
            (fun j : ι =>
              ⟪y j - gStar, xTilde - xNext j⟫_ℝ) := hright_expand

/-- Finite-current-index averaged `δ₂` expansion after applying the
componentwise Eq. (6.6.30) identity.

This aligns with Lan Eq. (6.6.30) at the double-sum level used inside Lemma
6.13.  SOptLib candidates `finset_weighted_residual_sum_eq_zero`,
`finset_weighted_variance_eq_second_moment_sub_norm_mean_sq`,
`weighted_variance_le_second_moment`, `weighted_sq_norm_sub_center_le`,
`coefficients_for_average_minus_search_eq_alpha_step_minus_center`, and
`average_sub_search_eq_alpha_smul_step_sub_weighted_center`, plus the target-file
helper `currentIndexAverage_delta2_component_inner_product_expansion`, were
considered; only the target-file component helper matches the source inner-product
algebra, while this lemma adds the missing finite average and sum-commutation
normalization. -/
theorem currentIndexAverage_delta2_double_sum_expansion
    (g gStar : ι → E) (xTilde xNextStar : E)
    (y : ι → ι → E) (xNext : ι → E)
    (hyavg :
      ∀ i : ι,
        RandomizedAcceleratedProximalPointSetup.currentIndexAverage
          (fun j : ι => y j i) = g i) :
    RandomizedAcceleratedProximalPointSetup.currentIndexAverage
        (fun j : ι =>
          (Fintype.card ι : ℝ)⁻¹ *
            Finset.sum Finset.univ
              (fun i : ι =>
                ⟪g i - gStar i, xTilde⟫_ℝ -
                    ⟪y j i - gStar i, xNext j⟫_ℝ +
                  ⟪y j i - g i, xNextStar⟫_ℝ)) =
      (Fintype.card ι : ℝ)⁻¹ * (Fintype.card ι : ℝ)⁻¹ *
        Finset.sum Finset.univ
          (fun i : ι =>
            Finset.sum Finset.univ
              (fun j : ι =>
                ⟪y j i - gStar i, xTilde - xNext j⟫_ℝ)) := by
  classical
  let c : ℝ := Fintype.card ι
  have hcomponents :
      Finset.sum Finset.univ
          (fun i : ι =>
            Finset.sum Finset.univ
              (fun j : ι =>
                ⟪g i - gStar i, xTilde⟫_ℝ -
                    ⟪y j i - gStar i, xNext j⟫_ℝ +
                  ⟪y j i - g i, xNextStar⟫_ℝ)) =
        Finset.sum Finset.univ
          (fun i : ι =>
            Finset.sum Finset.univ
              (fun j : ι =>
                ⟪y j i - gStar i, xTilde - xNext j⟫_ℝ)) := by
    refine Finset.sum_congr rfl ?_
    intro i _hi
    exact currentIndexAverage_delta2_component_inner_product_expansion
      (g := g i) (gStar := gStar i) (xTilde := xTilde)
      (xNextStar := xNextStar) (y := fun j : ι => y j i)
      (xNext := xNext) (hyavg i)
  unfold RandomizedAcceleratedProximalPointSetup.currentIndexAverage SOptLib.finiteUniformAverage
  change
    c⁻¹ •
        Finset.sum Finset.univ
          (fun j : ι =>
            c⁻¹ *
              Finset.sum Finset.univ
                (fun i : ι =>
                  ⟪g i - gStar i, xTilde⟫_ℝ -
                      ⟪y j i - gStar i, xNext j⟫_ℝ +
                    ⟪y j i - g i, xNextStar⟫_ℝ)) =
      c⁻¹ * c⁻¹ *
        Finset.sum Finset.univ
          (fun i : ι =>
            Finset.sum Finset.univ
              (fun j : ι =>
                ⟪y j i - gStar i, xTilde - xNext j⟫_ℝ))
  simp only [smul_eq_mul]
  calc
    c⁻¹ *
        Finset.sum Finset.univ
          (fun j : ι =>
            c⁻¹ *
              Finset.sum Finset.univ
                (fun i : ι =>
                  ⟪g i - gStar i, xTilde⟫_ℝ -
                      ⟪y j i - gStar i, xNext j⟫_ℝ +
                    ⟪y j i - g i, xNextStar⟫_ℝ))
        =
      c⁻¹ *
        (c⁻¹ *
          Finset.sum Finset.univ
            (fun j : ι =>
              Finset.sum Finset.univ
                (fun i : ι =>
                  ⟪g i - gStar i, xTilde⟫_ℝ -
                      ⟪y j i - gStar i, xNext j⟫_ℝ +
                    ⟪y j i - g i, xNextStar⟫_ℝ))) := by
          rw [← Finset.mul_sum]
    _ =
      c⁻¹ *
        (c⁻¹ *
          Finset.sum Finset.univ
            (fun i : ι =>
              Finset.sum Finset.univ
                (fun j : ι =>
                  ⟪g i - gStar i, xTilde⟫_ℝ -
                      ⟪y j i - gStar i, xNext j⟫_ℝ +
                    ⟪y j i - g i, xNextStar⟫_ℝ))) := by
          rw [Finset.sum_comm]
    _ =
      c⁻¹ *
        (c⁻¹ *
          Finset.sum Finset.univ
            (fun i : ι =>
              Finset.sum Finset.univ
                (fun j : ι =>
                  ⟪y j i - gStar i, xTilde - xNext j⟫_ℝ))) := by
          rw [hcomponents]
    _ =
      c⁻¹ * c⁻¹ *
        Finset.sum Finset.univ
          (fun i : ι =>
            Finset.sum Finset.univ
              (fun j : ι =>
                ⟪y j i - gStar i, xTilde - xNext j⟫_ℝ)) := by
          ring

/-- Affine component-memory algebra for Lan Eq. (6.6.29).

This is the scalar identity behind the displayed rewrite of `δ₁ᵗ` into
`τ Ψ(xᵢᵗ⁻¹,x*) - (1+τ)Ψ(x̂ᵢᵗ,x*) - τ Ψ(xᵢᵗ⁻¹,x̂ᵢᵗ)`.  SOptLib candidates
`carrierBregmanDivergence_three_point_identity`,
`bregmanDivergence_three_point_identity`, and
`carrierBregmanDivergence_add_swap_eq_inner_grad_sub` were checked; they provide
paper-neutral Bregman algebra, but this helper also incorporates the literal
Algorithm 6.9 affine relation `τ(prev-hat)=hat-xTilde` needed by Eq. (6.6.29). -/
theorem affine_bregman_delta1_identity
    (τ : ℝ) (vPrev vHat vStar : ℝ)
    (gHat gStar prev hat star xTilde : E)
    (haff : τ • (prev - hat) = hat - xTilde) :
    τ * (vPrev - vStar - ⟪gStar, prev - star⟫_ℝ) -
        (1 + τ) * (vHat - vStar - ⟪gStar, hat - star⟫_ℝ) -
        τ * (vPrev - vHat - ⟪gHat, prev - hat⟫_ℝ) =
      vStar - ⟪gStar, star⟫_ℝ -
        (vHat - ⟪gHat, hat⟫_ℝ + ⟪gHat - gStar, xTilde⟫_ℝ) := by
  have hHat : τ * ⟪gHat, prev - hat⟫_ℝ =
      ⟪gHat, hat⟫_ℝ - ⟪gHat, xTilde⟫_ℝ := by
    calc
      τ * ⟪gHat, prev - hat⟫_ℝ = ⟪gHat, τ • (prev - hat)⟫_ℝ := by
        rw [inner_smul_right]
      _ = ⟪gHat, hat - xTilde⟫_ℝ := by
        rw [haff]
      _ = ⟪gHat, hat⟫_ℝ - ⟪gHat, xTilde⟫_ℝ := by
        rw [inner_sub_right]
  have hHatRaw :
      τ * (⟪gHat, prev⟫_ℝ - ⟪gHat, hat⟫_ℝ) =
        ⟪gHat, hat⟫_ℝ - ⟪gHat, xTilde⟫_ℝ := by
    calc
      τ * (⟪gHat, prev⟫_ℝ - ⟪gHat, hat⟫_ℝ) =
          τ * ⟪gHat, prev - hat⟫_ℝ := by
        rw [inner_sub_right]
      _ = ⟪gHat, hat⟫_ℝ - ⟪gHat, xTilde⟫_ℝ := hHat
  have hStarRaw :
      τ * (⟪gStar, prev⟫_ℝ - ⟪gStar, hat⟫_ℝ) =
        ⟪gStar, hat⟫_ℝ - ⟪gStar, xTilde⟫_ℝ := by
    calc
      τ * (⟪gStar, prev⟫_ℝ - ⟪gStar, hat⟫_ℝ) =
          τ * ⟪gStar, prev - hat⟫_ℝ := by
        rw [inner_sub_right]
      _ = ⟪gStar, τ • (prev - hat)⟫_ℝ := by
        rw [inner_smul_right]
      _ = ⟪gStar, hat - xTilde⟫_ℝ := by
        rw [haff]
      _ = ⟪gStar, hat⟫_ℝ - ⟪gStar, xTilde⟫_ℝ := by
        rw [inner_sub_right]
  have hStar :
      (1 + τ) * ⟪gStar, hat⟫_ℝ - τ * ⟪gStar, prev⟫_ℝ =
        ⟪gStar, xTilde⟫_ℝ := by
    linarith [hStarRaw]
  rw [inner_sub_left]
  repeat rw [inner_sub_right]
  linear_combination hHatRaw + hStar

/-- One-hot finite-sum algebra for the sampled tau-memory update.

This aligns with the sampled-memory part of Lan Lemma 6.13, Eq. (6.6.31):
the actual memory array changes only at the current component, so the finite
tau-memory sum can be separated into the sampled update and the uniform
subtraction over previous memories.  SOptLib candidates
`finset_weighted_residual_sum_eq_zero`, `Finset.weighted_variance_le_second_moment`,
`weighted_sq_norm_sub_center_le`, and the target-file `currentIndexAverage_*`
lemmas were considered; none states this scalar one-hot tau-memory regrouping. -/
theorem one_hot_tau_memory_sum_eq
    (γ τ invCard : ℝ) (sample : ι) (prev next : ι → ℝ) :
    Finset.sum Finset.univ
        (fun i : ι =>
          γ * ((1 + τ) - invCard) * prev i -
            γ * (1 + τ) * (if i = sample then next i else prev i)) =
      γ * (1 + τ) * prev sample - γ * (1 + τ) * next sample -
        γ * invCard * Finset.sum Finset.univ prev := by
  classical
  have hif_sum :
      Finset.sum Finset.univ (fun i : ι => if i = sample then next i else prev i) =
        next sample + Finset.sum Finset.univ prev - prev sample := by
    calc
      Finset.sum Finset.univ (fun i : ι => if i = sample then next i else prev i)
          =
        Finset.sum Finset.univ
          (fun i : ι => prev i + if i = sample then next sample - prev sample else 0) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          by_cases hi : i = sample
          · subst i
            simp
          · simp [hi]
      _ =
        Finset.sum Finset.univ prev +
          Finset.sum Finset.univ
            (fun i : ι => if i = sample then next sample - prev sample else 0) := by
          rw [Finset.sum_add_distrib]
      _ = Finset.sum Finset.univ prev + (next sample - prev sample) := by
          simpa using
            (Finset.sum_ite_eq (i := sample)
              (f := fun _j : ι => next sample - prev sample))
      _ = next sample + Finset.sum Finset.univ prev - prev sample := by ring
  calc
    Finset.sum Finset.univ
        (fun i : ι =>
          γ * ((1 + τ) - invCard) * prev i -
            γ * (1 + τ) * (if i = sample then next i else prev i))
        =
      γ * ((1 + τ) - invCard) * Finset.sum Finset.univ prev -
        γ * (1 + τ) *
          Finset.sum Finset.univ (fun i : ι => if i = sample then next i else prev i) := by
        rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
    _ =
      γ * ((1 + τ) - invCard) * Finset.sum Finset.univ prev -
        γ * (1 + τ) *
          (next sample + Finset.sum Finset.univ prev - prev sample) := by
        rw [hif_sum]
    _ =
      γ * (1 + τ) * prev sample - γ * (1 + τ) * next sample -
        γ * invCard * Finset.sum Finset.univ prev := by
        ring

/-! `lemma_6_12_domain_corrected` gives the conditional expectation identities
for the averaged gradient estimator under explicit domain facts for the affine
component refresh.  The printed Lemma 6.12 omits these closure facts, so this is a
corrected/internal boundary theorem rather than an A-level original statement. -/
theorem lemma_6_12_domain_corrected
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (ℓ : setup.OutputIndex) (t : setup.InnerIndex)
    (hHat : ∀ ω i, setup.xHatAt ℓ t i ω ∈ setup.X)
    (hAfter : ∀ ω j i, setup.xMemAfterSampleAt ℓ t j i ω ∈ setup.X)
    (hPrev : ∀ ω i, setup.xMemIter ℓ.1 (t.1 - 1) i ω ∈ setup.X) :
    (∀ ω i,
      setup.psiAtIndex ℓ i ω
          ⟨setup.xHatAt ℓ t i ω, hHat ω i⟩ =
        (Fintype.card ι : ℝ) *
            RandomizedAcceleratedProximalPointSetup.currentIndexAverage
              (fun j =>
                setup.psiAtIndex ℓ i ω
                  ⟨setup.xMemAfterSampleAt ℓ t j i ω,
                    hAfter ω j i⟩) -
          ((Fintype.card ι : ℝ) - 1) *
            setup.psiAtIndex ℓ i ω
              ⟨setup.xMemIter ℓ.1 (t.1 - 1) i ω,
                hPrev ω i⟩) ∧
    (∀ ω i,
      setup.gradPsiOnAtIndex ℓ i ω
          ⟨setup.xHatAt ℓ t i ω,
            hHat ω i⟩ =
        (Fintype.card ι : ℝ) •
            RandomizedAcceleratedProximalPointSetup.currentIndexAverage
              (fun j =>
                setup.gradPsiOnAtIndex ℓ i ω
                  ⟨setup.xMemAfterSampleAt ℓ t j i ω,
                    hAfter ω j i⟩) -
          ((Fintype.card ι : ℝ) - 1) •
            setup.gradPsiOnAtIndex ℓ i ω
              ⟨setup.xMemIter ℓ.1 (t.1 - 1) i ω,
                hPrev ω i⟩) ∧
    (∀ ω i,
      RandomizedAcceleratedProximalPointSetup.currentIndexAverage
          (fun j => setup.yTildeAfterSampleAt ℓ t j i ω) =
        setup.gradPsiOnAtIndex ℓ i ω
          ⟨setup.xHatAt ℓ t i ω,
            hHat ω i⟩) := by
  classical
  constructor
  · intro ω i
    let a : ℝ :=
      setup.psiAtIndex ℓ i ω
        ⟨setup.xHatAt ℓ t i ω, hHat ω i⟩
    let b : ℝ :=
      setup.psiAtIndex ℓ i ω
        ⟨setup.xMemIter ℓ.1 (t.1 - 1) i ω, hPrev ω i⟩
    have hbranch :
        (fun j : ι =>
          setup.psiAtIndex ℓ i ω
            ⟨setup.xMemAfterSampleAt ℓ t j i ω, hAfter ω j i⟩) =
        (fun j : ι => if i = j then a else b) := by
      funext j
      by_cases hij : i = j
      · simp [a, RandomizedAcceleratedProximalPointSetup.xMemAfterSampleAt, hij]
      · simp [b, RandomizedAcceleratedProximalPointSetup.xMemAfterSampleAt, hij]
    have h :=
      currentIndexAverage_ite_update_module (i := i) (a := a) (b := b)
    rw [hbranch]
    simpa [a, b, smul_eq_mul] using h
  · constructor
    · intro ω i
      let a : E :=
        setup.gradPsiOnAtIndex ℓ i ω
          ⟨setup.xHatAt ℓ t i ω, hHat ω i⟩
      let b : E :=
        setup.gradPsiOnAtIndex ℓ i ω
          ⟨setup.xMemIter ℓ.1 (t.1 - 1) i ω, hPrev ω i⟩
      have hbranch :
          (fun j : ι =>
            setup.gradPsiOnAtIndex ℓ i ω
              ⟨setup.xMemAfterSampleAt ℓ t j i ω, hAfter ω j i⟩) =
          (fun j : ι => if i = j then a else b) := by
        funext j
        by_cases hij : i = j
        · simp [a, RandomizedAcceleratedProximalPointSetup.xMemAfterSampleAt, hij]
        · simp [b, RandomizedAcceleratedProximalPointSetup.xMemAfterSampleAt, hij]
      have h :=
        currentIndexAverage_ite_update_module (i := i) (a := a) (b := b)
      rw [hbranch]
      simpa [a, b] using h
    · intro ω i
      let a : E :=
        setup.gradPsiOnAtIndex ℓ i ω
          ⟨setup.xHatAt ℓ t i ω, hHat ω i⟩
      let b : E := setup.yMemIter ℓ.1 (t.1 - 1) i ω
      have hbranch :
          (fun j : ι => setup.yTildeAfterSampleAt ℓ t j i ω) =
          (fun j : ι =>
            if i = j then (Fintype.card ι : ℝ) • (a - b) + b else b) := by
        funext j
        by_cases hij : i = j
        · subst j
          simp [a, b, RandomizedAcceleratedProximalPointSetup.yTildeAfterSampleAt,
            RandomizedAcceleratedProximalPointSetup.xMemAfterSampleAt,
            RandomizedAcceleratedProximalPointSetup.gradPsiOnAtIndex,
            setup.gradPsiOn_coe]
        · simp [a, b, RandomizedAcceleratedProximalPointSetup.yTildeAfterSampleAt, hij]
      rw [hbranch]
      simpa [a, b] using
        (currentIndexAverage_estimator_update_eq (i := i) (a := a) (b := b))

/-! `eq_6_6_30_conditional_current_index` is the first formula-level source
interface used by the corrected Lemma 6.13 route.

It packages exactly the two book-visible dependencies needed at Eq. (6.6.30):
the Lemma 6.12 source-domain estimator identity and the fresh-current-index
finite-average bridge.  The later Lemma 6.13 telescope should instantiate the
real kernel `delta2Current` with the displayed `δ₂ᵗ` inner-product summand and
then perform only algebraic substitution. -/
theorem eq_6_6_30_conditional_current_index
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (ℓ : setup.OutputIndex) (t : setup.InnerIndex)
    (hHat : ∀ ω i, setup.xHatAt ℓ t i ω ∈ setup.X)
    (hAfter : ∀ ω j i, setup.xMemAfterSampleAt ℓ t j i ω ∈ setup.X)
    (hPrev : ∀ ω i, setup.xMemIter ℓ.1 (t.1 - 1) i ω ∈ setup.X)
    {W : Type*} [MeasurableSpace W]
    (n : ℕ) {Z : Ω → W}
    (hZ : Measurable[(SOptLib.filtration setup.ξ setup.hξ_measurable).seq n] Z)
    (delta2Current : W → ι → ℝ)
    (hDelta2_meas : Measurable (fun q : W × ι => delta2Current q.1 q.2))
    (hDelta2_int : ∀ j : ι, Integrable (fun ω : Ω => delta2Current (Z ω) j) setup.P) :
    ((∫ ω : Ω, delta2Current (Z ω) (setup.ξ n ω) ∂setup.P) =
      ∫ ω : Ω,
        RandomizedAcceleratedProximalPointSetup.currentIndexAverage
          (fun j : ι => delta2Current (Z ω) j) ∂setup.P) ∧
    (∀ ω i,
      RandomizedAcceleratedProximalPointSetup.currentIndexAverage
          (fun j => setup.yTildeAfterSampleAt ℓ t j i ω) =
        setup.gradPsiOnAtIndex ℓ i ω
          ⟨setup.xHatAt ℓ t i ω, hHat ω i⟩) := by
  classical
  have h612 := lemma_6_12_domain_corrected setup ℓ t hHat hAfter hPrev
  have hcurrent :=
    setup.current_sample_conditional_uniform_average
      n hZ delta2Current hDelta2_meas hDelta2_int
  exact ⟨hcurrent, h612.2.2⟩

/-- The source-level `δ₂ᵗ` summand from Lemma 6.13, Eq. (6.6.29), for a fixed
subproblem and a hypothetical current sample `j`.

This is the actual kernel that Eq. (6.6.30) averages over the fresh current
index.  It uses source-domain gradients at the Lemma 6.12 candidate points
`x̂ᵢᵗ`; only the estimator `ỹᵢᵗ` depends on the hypothetical sample `j`. -/
noncomputable def ambientFixedDelta2CurrentKernel
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (offset : ℕ) (z x0 xStar : E) (xMem0 yMem0 : ι → E)
    (hz : z ∈ setup.X) (hx0 : x0 ∈ setup.X) (hxStar : xStar ∈ setup.X)
    (n : ℕ) (hn : n + 1 ≤ setup.s)
    (hhat :
      ∀ (ω : Ω) (i : ι),
        setup.xMemAfterSampleAtState (n + 1) (Nat.succ_pos n) hn i i
          (setup.ambientFixedInnerProcess offset z x0 xMem0 yMem0 hz hx0 n ω) ∈
            setup.X)
    (ω : Ω) (j : ι) : ℝ :=
  let stPrev :=
    setup.ambientFixedInnerProcess offset z x0 xMem0 yMem0 hz hx0 n ω
  let xHat : ι → E :=
    fun i =>
      setup.xMemAfterSampleAtState (n + 1) (Nat.succ_pos n) hn i i stPrev
  let xMemNew : ι → E :=
    fun i =>
      setup.xMemAfterSampleAtState (n + 1) (Nat.succ_pos n) hn j i stPrev
  let yMemNew : ι → E :=
    fun i =>
      if _ : i = j then
        setup.gradPsiOnAt z i ⟨xHat i, hhat ω i⟩
      else stPrev.yMem i
  let yTilde : ι → E :=
    fun i => (Fintype.card ι : ℝ) • (yMemNew i - stPrev.yMem i) + stPrev.yMem i
  let avgY : E :=
    (Fintype.card ι : ℝ)⁻¹ • Finset.sum Finset.univ yTilde
  let hxPrev : stPrev.x ∈ setup.X := by
    simpa [stPrev] using
      (((setup.ambientFixedInnerProcess_mem offset z x0 xMem0 yMem0 hz hx0 n
        (Nat.le_of_succ_le hn)) ω).1)
  let xNext : E :=
    setup.proxStepAt z (n + 1) hz (Nat.succ_pos n) hn stPrev.x hxPrev avgY
  (Fintype.card ι : ℝ)⁻¹ *
    Finset.sum Finset.univ
      (fun i =>
        ⟪setup.gradPsiOnAt z i ⟨xHat i, hhat ω i⟩ -
              setup.gradPsiOnAt z i ⟨xStar, hxStar⟩,
            setup.xTildeAtState (n + 1) stPrev⟫_ℝ -
          ⟪yTilde i - setup.gradPsiOnAt z i ⟨xStar, hxStar⟩,
            xNext⟫_ℝ +
          ⟪yTilde i - setup.gradPsiOnAt z i ⟨xHat i, hhat ω i⟩,
            xStar⟫_ℝ)

/-- Current-index average expansion for the fixed-time `δ₂` kernel.

This is the kernel-level Lan Eq. (6.6.30) bridge used by Lemma 6.13: after
unfolding the Algorithm 6.9 hypothetical current sample, the finite average of
`ambientFixedDelta2CurrentKernel` is the double current-index sum of
`⟪ỹ_j i - ∇ψ_i(x*), x̃ - x_j^+⟫`.  SOptLib weighted residual/variance candidates
`finset_weighted_residual_sum_eq_zero`,
`finset_weighted_variance_eq_second_moment_sub_norm_mean_sq`,
`weighted_variance_le_second_moment`, `weighted_sq_norm_sub_center_le`,
`coefficients_for_average_minus_search_eq_alpha_step_minus_center`, and
`average_sub_search_eq_alpha_smul_step_sub_weighted_center` were considered;
none unfolds this paper-specific kernel, so this helper specializes the
target-file algebra helper `currentIndexAverage_delta2_double_sum_expansion`. -/
theorem ambientFixedDelta2CurrentKernel_average_expansion
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (offset : ℕ) (z x0 xStar : E) (xMem0 yMem0 : ι → E)
    (hz : z ∈ setup.X) (hx0 : x0 ∈ setup.X) (hxStar : xStar ∈ setup.X)
    (n : ℕ) (hn : n + 1 ≤ setup.s)
    (hhat :
      ∀ (ω : Ω) (i : ι),
        setup.xMemAfterSampleAtState (n + 1) (Nat.succ_pos n) hn i i
          (setup.ambientFixedInnerProcess offset z x0 xMem0 yMem0 hz hx0 n ω) ∈
            setup.X)
    (ω : Ω) :
    let stPrev :=
      setup.ambientFixedInnerProcess offset z x0 xMem0 yMem0 hz hx0 n ω
    let xHat : ι → E :=
      fun i =>
        setup.xMemAfterSampleAtState (n + 1) (Nat.succ_pos n) hn i i stPrev
    let hxHat : ∀ i : ι, xHat i ∈ setup.X := by
      intro i
      exact hhat ω i
    let yHyp : ι → ι → E := fun j i =>
      (Fintype.card ι : ℝ) •
          ((if _ : i = j then
              setup.gradPsiOnAt z i ⟨xHat i, hxHat i⟩
            else stPrev.yMem i) - stPrev.yMem i) +
        stPrev.yMem i
    let xNextHyp : ι → E := fun j =>
      setup.proxStepAt z (n + 1) hz (Nat.succ_pos n) hn stPrev.x
        (by
          simpa [stPrev] using
            (((setup.ambientFixedInnerProcess_mem offset z x0 xMem0 yMem0
              hz hx0 n (Nat.le_of_succ_le hn)) ω).1))
        ((Fintype.card ι : ℝ)⁻¹ • Finset.sum Finset.univ (fun i => yHyp j i))
    RandomizedAcceleratedProximalPointSetup.currentIndexAverage
        (fun j : ι =>
          ambientFixedDelta2CurrentKernel
            (setup := setup) (offset := offset) (z := z) (x0 := x0)
            (xStar := xStar) (xMem0 := xMem0) (yMem0 := yMem0)
            (hz := hz) (hx0 := hx0) (hxStar := hxStar)
            n hn hhat ω j) =
      (Fintype.card ι : ℝ)⁻¹ * (Fintype.card ι : ℝ)⁻¹ *
        Finset.sum Finset.univ
          (fun i : ι =>
            Finset.sum Finset.univ
              (fun j : ι =>
                ⟪yHyp j i - setup.gradPsiOnAt z i ⟨xStar, hxStar⟩,
                  setup.xTildeAtState (n + 1) stPrev - xNextHyp j⟫_ℝ)) := by
  classical
  dsimp only
  let stPrev :=
    setup.ambientFixedInnerProcess offset z x0 xMem0 yMem0 hz hx0 n ω
  let xHat : ι → E :=
    fun i =>
      setup.xMemAfterSampleAtState (n + 1) (Nat.succ_pos n) hn i i stPrev
  let hxHat : ∀ i : ι, xHat i ∈ setup.X := by
    intro i
    exact hhat ω i
  let yHyp : ι → ι → E := fun j i =>
    (Fintype.card ι : ℝ) •
        ((if _ : i = j then
            setup.gradPsiOnAt z i ⟨xHat i, hxHat i⟩
          else stPrev.yMem i) - stPrev.yMem i) +
      stPrev.yMem i
  let xNextHyp : ι → E := fun j =>
    setup.proxStepAt z (n + 1) hz (Nat.succ_pos n) hn stPrev.x
      (by
        simpa [stPrev] using
          (((setup.ambientFixedInnerProcess_mem offset z x0 xMem0 yMem0
            hz hx0 n (Nat.le_of_succ_le hn)) ω).1))
      ((Fintype.card ι : ℝ)⁻¹ • Finset.sum Finset.univ (fun i => yHyp j i))
  have hyavg_component :
      ∀ i : ι,
        RandomizedAcceleratedProximalPointSetup.currentIndexAverage
            (fun j : ι => yHyp j i) =
          setup.gradPsiOnAt z i ⟨xHat i, hxHat i⟩ := by
    intro i
    have hbranch :
        (fun j : ι => yHyp j i) =
          (fun j : ι =>
            if i = j then
              (Fintype.card ι : ℝ) •
                  (setup.gradPsiOnAt z i ⟨xHat i, hxHat i⟩ - stPrev.yMem i) +
                stPrev.yMem i
            else stPrev.yMem i) := by
      funext j
      by_cases hij : i = j
      · simp [yHyp, hij]
      · simp [yHyp, hij]
    rw [hbranch]
    exact
      (currentIndexAverage_estimator_update_eq
        (i := i)
        (a := setup.gradPsiOnAt z i ⟨xHat i, hxHat i⟩)
        (b := stPrev.yMem i))
  dsimp [ambientFixedDelta2CurrentKernel]
  simpa [stPrev, xHat, yHyp, xNextHyp] using
    (currentIndexAverage_delta2_double_sum_expansion
      (g := fun i : ι => setup.gradPsiOnAt z i ⟨xHat i, hxHat i⟩)
      (gStar := fun i : ι => setup.gradPsiOnAt z i ⟨xStar, hxStar⟩)
      (xTilde := setup.xTildeAtState (n + 1) stPrev)
      (xNextStar := xStar)
      (y := yHyp)
      (xNext := xNextHyp)
      hyavg_component)

/-! Regularity interface for instantiating Eq. (6.6.30) with the displayed
`δ₂ᵗ` kernel.

The finite-current-index averaging theorem is stated for a prefix-measurable
state `Z` and a measurable/integrable kernel on that state.  The source formula
for `δ₂ᵗ` is written as an observable of the full sample point `ω`, so the
replacement route records the required prefix-state representation explicitly
rather than hiding it as local measurability sorries inside Lemma 6.13. -/
def ambientFixedDelta2CurrentKernelRegularity
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (offset : ℕ) (z x0 xStar : E) (xMem0 yMem0 : ι → E)
    (hz : z ∈ setup.X) (hx0 : x0 ∈ setup.X) (hxStar : xStar ∈ setup.X)
    (hhat :
      setup.ambientFixedHatSourceDomain offset z x0 xMem0 yMem0 hz hx0) :
    Prop :=
  ∀ n (hn : n + 1 ≤ setup.s),
    ∃ Z : Ω → (Fin n → ι), ∃ delta2Current : (Fin n → ι) → ι → ℝ,
        Measurable[(SOptLib.filtration setup.ξ setup.hξ_measurable).seq n] Z ∧
        Measurable (fun q : (Fin n → ι) × ι => delta2Current q.1 q.2) ∧
        (∀ j : ι, Integrable (fun ω : Ω => delta2Current (Z ω) j) setup.P) ∧
        ∀ (ω : Ω) (j : ι),
          delta2Current (Z ω) j =
            ambientFixedDelta2CurrentKernel
              (setup := setup) (offset := offset) (z := z) (x0 := x0)
              (xStar := xStar) (xMem0 := xMem0) (yMem0 := yMem0)
              (hz := hz) (hx0 := hx0) (hxStar := hxStar)
              n hn (hhat n hn) ω j

/-- The displayed `δ₂ᵗ` current-index kernel is determined by the strict
sample prefix before the current draw.

Considered SOptLib algebra candidates
`finset_weighted_residual_sum_eq_zero`,
`finset_weighted_variance_eq_second_moment_sub_norm_mean_sq`,
`weighted_variance_le_second_moment`, `weighted_sq_norm_sub_center_le`,
`coefficients_for_average_minus_search_eq_alpha_step_minus_center`, and
`average_sub_search_eq_alpha_smul_step_sub_weighted_center`; none match because
this boundary is not a weighted-variance identity but the literal finite-prefix
determinism needed for Lan Lemma 6.13 Eq. (6.6.30). -/
theorem ambientFixedDelta2CurrentKernel_prefix_const
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (offset : ℕ) (z x0 xStar : E) (xMem0 yMem0 : ι → E)
    (hz : z ∈ setup.X) (hx0 : x0 ∈ setup.X) (hxStar : xStar ∈ setup.X)
    (n : ℕ) (hn : n + 1 ≤ setup.s)
    (hhat :
      ∀ (ω : Ω) (i : ι),
        setup.xMemAfterSampleAtState (n + 1) (Nat.succ_pos n) hn i i
          (setup.ambientFixedInnerProcess offset z x0 xMem0 yMem0 hz hx0 n ω) ∈
            setup.X) :
    ∀ ⦃ω ω' : Ω⦄ (j : ι),
      setup.ambientFixedSamplePrefix offset n ω =
        setup.ambientFixedSamplePrefix offset n ω' →
      ambientFixedDelta2CurrentKernel
          (setup := setup) (offset := offset) (z := z) (x0 := x0)
          (xStar := xStar) (xMem0 := xMem0) (yMem0 := yMem0)
          (hz := hz) (hx0 := hx0) (hxStar := hxStar)
          n hn hhat ω j =
        ambientFixedDelta2CurrentKernel
          (setup := setup) (offset := offset) (z := z) (x0 := x0)
          (xStar := xStar) (xMem0 := xMem0) (yMem0 := yMem0)
          (hz := hz) (hx0 := hx0) (hxStar := hxStar)
          n hn hhat ω' j := by
  classical
  intro ω ω' j hprefix
  have hprev :
      setup.ambientFixedInnerProcess offset z x0 xMem0 yMem0 hz hx0 n ω =
        setup.ambientFixedInnerProcess offset z x0 xMem0 yMem0 hz hx0 n ω' :=
    setup.ambientFixedInnerProcess_prefix_const
      offset z x0 xMem0 yMem0 hz hx0 n (Nat.le_of_succ_le hn) hprefix
  unfold ambientFixedDelta2CurrentKernel
  simp [hprev]

/-- Integrability of the realized current-index `δ₂ᵗ` kernel at one fixed
source time.

SOptLib finite-sum and sampled-fiber integrability candidates were considered,
including `integrable_finset_sum_const_mul` and finite PMF transport lemmas; this
summand is instead a finite-prefix observable of Algorithm 6.9, so the local
`ambientFixed_prefix_integrable_real` plus
`ambientFixedDelta2CurrentKernel_prefix_const` is the exact match for Lan
Eq. (6.6.30). -/
theorem ambientFixedDelta2CurrentKernel_realized_integrable
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (offset : ℕ) (z x0 xStar : E) (xMem0 yMem0 : ι → E)
    (hz : z ∈ setup.X) (hx0 : x0 ∈ setup.X) (hxStar : xStar ∈ setup.X)
    (n : ℕ) (hn : n + 1 ≤ setup.s)
    (hhat :
      ∀ (ω : Ω) (i : ι),
        setup.xMemAfterSampleAtState (n + 1) (Nat.succ_pos n) hn i i
          (setup.ambientFixedInnerProcess offset z x0 xMem0 yMem0 hz hx0 n ω) ∈
            setup.X)
    (γ : ℝ) :
    Integrable
      (fun ω : Ω =>
        γ *
          ambientFixedDelta2CurrentKernel
            (setup := setup) (offset := offset) (z := z) (x0 := x0)
            (xStar := xStar) (xMem0 := xMem0) (yMem0 := yMem0)
            (hz := hz) (hx0 := hx0) (hxStar := hxStar)
            n hn hhat ω (setup.ξ (offset + n) ω)) setup.P := by
  classical
  refine setup.ambientFixed_prefix_integrable_real offset (n + 1) ?_
  intro ω ω' hprefix
  have hprefix_prev :
      setup.ambientFixedSamplePrefix offset n ω =
        setup.ambientFixedSamplePrefix offset n ω' := by
    funext r
    exact congrFun hprefix ⟨r.1, Nat.lt_trans r.2 (Nat.lt_succ_self n)⟩
  have hsample :
      setup.ξ (offset + n) ω = setup.ξ (offset + n) ω' := by
    exact congrFun hprefix ⟨n, Nat.lt_succ_self n⟩
  rw [hsample]
  congr 1
  exact ambientFixedDelta2CurrentKernel_prefix_const
    (setup := setup) (offset := offset) (z := z) (x0 := x0)
    (xStar := xStar) (xMem0 := xMem0) (yMem0 := yMem0)
    (hz := hz) (hx0 := hx0) (hxStar := hxStar)
    n hn hhat (setup.ξ (offset + n) ω') hprefix_prev

/-- Integrability of the current-index average of the fixed-time `δ₂ᵗ` kernel.

SOptLib finite-average integrability helpers were considered; none handles this
proof-dependent Algorithm 6.9 kernel directly.  The paper summand in
Eq. (6.6.30) is constant on the strict sample prefix, so the local finite-prefix
integrability helper is the aligned source route. -/
theorem ambientFixedDelta2CurrentKernel_average_integrable
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (offset : ℕ) (z x0 xStar : E) (xMem0 yMem0 : ι → E)
    (hz : z ∈ setup.X) (hx0 : x0 ∈ setup.X) (hxStar : xStar ∈ setup.X)
    (n : ℕ) (hn : n + 1 ≤ setup.s)
    (hhat :
      ∀ (ω : Ω) (i : ι),
        setup.xMemAfterSampleAtState (n + 1) (Nat.succ_pos n) hn i i
          (setup.ambientFixedInnerProcess offset z x0 xMem0 yMem0 hz hx0 n ω) ∈
            setup.X)
    (γ : ℝ) :
    Integrable
      (fun ω : Ω =>
        γ *
          RandomizedAcceleratedProximalPointSetup.currentIndexAverage
            (fun j : ι =>
              ambientFixedDelta2CurrentKernel
                (setup := setup) (offset := offset) (z := z) (x0 := x0)
                (xStar := xStar) (xMem0 := xMem0) (yMem0 := yMem0)
                (hz := hz) (hx0 := hx0) (hxStar := hxStar)
                n hn hhat ω j)) setup.P := by
  classical
  refine setup.ambientFixed_prefix_integrable_real offset n ?_
  intro ω ω' hprefix
  congr 1
  unfold RandomizedAcceleratedProximalPointSetup.currentIndexAverage SOptLib.finiteUniformAverage
  congr 1
  refine Finset.sum_congr rfl ?_
  intro j _hj
  exact ambientFixedDelta2CurrentKernel_prefix_const
    (setup := setup) (offset := offset) (z := z) (x0 := x0)
    (xStar := xStar) (xMem0 := xMem0) (yMem0 := yMem0)
    (hz := hz) (hx0 := hx0) (hxStar := hxStar)
    n hn hhat j hprefix

/-- Guarded `Icc` specialization of realized `δ₂ᵗ` integrability.

This is a local Eq. (6.6.30) wrapper used to keep Lemma 6.13's integrated
bridge cheap to elaborate.  Searched target/SOptLib for "integrable current
index average delta2 kernel"; the matching primitives are
`ambientFixedDelta2CurrentKernel_realized_integrable` and
`ambientFixedDelta2CurrentKernel_average_integrable`, but no existing lemma
states the guarded `t ∈ Finset.Icc 1 s` summand used by Eq. (6.6.31). -/
theorem ambientFixedDelta2CurrentKernel_realized_guarded_Icc_integrable
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (z x0 xStar : E) (xMem0 yMem0 : ι → E)
    (hz : z ∈ setup.X) (hx0 : x0 ∈ setup.X) (hxStar : xStar ∈ setup.X)
    (hhat :
      setup.ambientFixedHatSourceDomain 0 z x0 xMem0 yMem0 hz hx0)
    (t : ℕ) (ht : t ∈ Finset.Icc 1 setup.s) :
    Integrable
      (fun ω : Ω =>
        if ht1 : 1 ≤ t then
          if hts : t ≤ setup.s then
            setup.γSeq t *
              ambientFixedDelta2CurrentKernel
                (setup := setup) (offset := 0) (z := z) (x0 := x0)
                (xStar := xStar) (xMem0 := xMem0) (yMem0 := yMem0)
                (hz := hz) (hx0 := hx0) (hxStar := hxStar)
                (t - 1)
                (by simpa [Nat.sub_add_cancel ht1] using hts)
                (hhat (t - 1)
                  (by simpa [Nat.sub_add_cancel ht1] using hts))
                ω (setup.ξ (t - 1) ω)
          else 0
        else 0) setup.P := by
  rcases Finset.mem_Icc.mp ht with ⟨ht1, hts⟩
  simpa [ht1, hts] using
    ambientFixedDelta2CurrentKernel_realized_integrable
      (setup := setup) (offset := 0) (z := z) (x0 := x0)
      (xStar := xStar) (xMem0 := xMem0) (yMem0 := yMem0)
      (hz := hz) (hx0 := hx0) (hxStar := hxStar)
      (n := t - 1)
      (hn := by simpa [Nat.sub_add_cancel ht1] using hts)
      (hhat := hhat (t - 1)
        (by simpa [Nat.sub_add_cancel ht1] using hts))
      (γ := setup.γSeq t)

/-- Guarded `Icc` specialization of averaged `δ₂ᵗ` integrability.

This is the averaged companion to
`ambientFixedDelta2CurrentKernel_realized_guarded_Icc_integrable`.  The
same search found only the fixed-time primitives and no guarded Eq. (6.6.31)
summand lemma, so this wrapper only discharges the local `Icc` guards and
delegates the mathematical content to
`ambientFixedDelta2CurrentKernel_average_integrable`. -/
theorem ambientFixedDelta2CurrentKernel_average_guarded_Icc_integrable
    (setup : RandomizedAcceleratedProximalPointSetup ι E Ω)
    (z x0 xStar : E) (xMem0 yMem0 : ι → E)
    (hz : z ∈ setup.X) (hx0 : x0 ∈ setup.X) (hxStar : xStar ∈ setup.X)
    (hhat :
      setup.ambientFixedHatSourceDomain 0 z x0 xMem0 yMem0 hz hx0)
    (t : ℕ) (ht : t ∈ Finset.Icc 1 setup.s) :
    Integrable
      (fun ω : Ω =>
        if ht1 : 1 ≤ t then
          if hts : t ≤ setup.s then
            setup.γSeq t *
              RandomizedAcceleratedProximalPointSetup.currentIndexAverage
                (fun j : ι =>
                  ambientFixedDelta2CurrentKernel
                    (setup := setup) (offset := 0) (z := z) (x0 := x0)
                    (xStar := xStar) (xMem0 := xMem0) (yMem0 := yMem0)
                    (hz := hz) (hx0 := hx0) (hxStar := hxStar)
                    (t - 1)
                    (by simpa [Nat.sub_add_cancel ht1] using hts)
                    (hhat (t - 1)
                      (by simpa [Nat.sub_add_cancel ht1] using hts))
                    ω j)
          else 0
        else 0) setup.P := by
  rcases Finset.mem_Icc.mp ht with ⟨ht1, hts⟩
  simpa [ht1, hts] using
    ambientFixedDelta2CurrentKernel_average_integrable
      (setup := setup) (offset := 0) (z := z) (x0 := x0)
      (xStar := xStar) (xMem0 := xMem0) (yMem0 := yMem0)
      (hz := hz) (hx0 := hx0) (hxStar := hxStar)
      (n := t - 1)
      (hn := by simpa [Nat.sub_add_cancel ht1] using hts)
      (hhat := hhat (t - 1)
        (by simpa [Nat.sub_add_cancel ht1] using hts))
      (γ := setup.γSeq t)

/-! Source-boundary supplier for the `δ₂ᵗ` regularity interface at offset `0`.

The kernel is represented as a function of the strict finite sample prefix
`(ξ 0, ..., ξ (n-1))`; this is exactly the sigma-algebra boundary required by
the current-index averaging theorem. -/

end RandomizedAcceleratedProximalPoint

end RandomizedAcceleratedProximalPointSetup
