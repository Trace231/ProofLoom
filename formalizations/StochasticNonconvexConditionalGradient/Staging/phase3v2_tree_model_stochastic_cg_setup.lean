import Mathlib.Probability.IdentDistrib
import SOptLib.Model.ConditionalGradient
import SOptLib.Model.Objective
import SOptLib.Model.StochasticOracle

/-!
# Stochastic Conditional-Gradient Setup

This staging module extracts the reusable Model-layer portion of the source
`StochasticNonconvexConditionalGradientSetup`. The generalization keeps the
compact convex carrier, expectation objective, bounded-variance unbiased
stochastic oracle, IID sample stream, and measurable linear minimization oracle.
It drops the Algorithm 7.13 horizon, epoch, batch, stepsize, output-law, and
theorem-boundary fields because those are paper-local scheduling data rather
than prerequisites of a stochastic Frank-Wolfe model.

The finite-sum conditional-gradient setup is the strongest nearby alternative,
but it fixes component-index sampling and finite-sum smoothness data, so it does
not cover a general sample-space oracle over `Ξ`. The extracted contract is for
future stochastic conditional-gradient and Frank-Wolfe developments that add
their own schedules and estimator recurrences on top of a common model setup.
-/

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace SOptLib

/-- Model data for stochastic conditional-gradient analyses over a compact
convex feasible set with an expectation objective, a bounded-variance unbiased
stochastic-gradient oracle, an IID sample stream, and a measurable linear
minimization oracle. -/
structure StochasticConditionalGradientSetup
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    (Ω : Type*) [MeasurableSpace Ω]
    (Ξ : Type*) [MeasurableSpace Ξ] where
  X : Set E
  x₀ : E
  F : E → Ξ → ℝ
  gradf : E → E
  gradF : E → Ξ → E
  L : ℝ
  σ : ℝ
  ξ : ℕ → Ω → Ξ
  P : Measure Ω
  hP : IsProbabilityMeasure P
  lmo : LinearMinimizationOracle E X
  hξ_meas : ∀ k : ℕ, Measurable (ξ k)
  stochasticOracle :
    BoundedVarianceUnbiasedOracleOn X (Measure.map (ξ 0) P)
      gradF gradf (fun v : E => ‖v‖) σ
  hX_closed : IsClosed X
  hX_compact : IsCompact X
  hX_convex : Convex ℝ X
  hx₀_mem : x₀ ∈ X
  hL_pos : 0 < L
  hσ_nonneg : 0 ≤ σ
  hF_objective_wellDefined :
    ∀ x : E, x ∈ X → objectiveWellDefined P F (ξ 0) x
  hF_hasGradientAt_ae :
    ∀ᵐ ω ∂P,
      ∀ x : E, x ∈ X →
        HasGradientAt (fun z : E => F z (ξ 0 ω)) (gradF x (ξ 0 ω)) x
  hF_smooth_ae :
    ∀ᵐ ω ∂P,
      ∀ x y : E, x ∈ X → y ∈ X →
        ‖gradF x (ξ 0 ω) - gradF y (ξ 0 ω)‖ ≤ L * ‖x - y‖
  hgradf_hasGradientAt :
    ∀ x : E, x ∈ X →
      HasGradientAt (objectiveExpectation P F (ξ 0)) (gradf x) x
  hgradf_smooth :
    ∀ x y : E, x ∈ X → y ∈ X →
      ‖gradf x - gradf y‖ ≤ L * ‖x - y‖
  hgradfOnX_measurable : Measurable (fun x : X => gradf (x : E))
  hξ_indep : ProbabilityTheory.iIndepFun ξ P
  hξ_ident : ∀ k : ℕ, ProbabilityTheory.IdentDistrib (ξ k) (ξ 0) P P

namespace StochasticConditionalGradientSetup

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
variable {Ω : Type*} [MeasurableSpace Ω]
variable {Ξ : Type*} [MeasurableSpace Ξ]

/-- The feasible set is nonempty because the setup stores a feasible initial
point. -/
theorem hX_nonempty (setup : StochasticConditionalGradientSetup E Ω Ξ) :
    Set.Nonempty setup.X :=
  ⟨setup.x₀, setup.hx₀_mem⟩

/-- Expected objective associated with the reference sample law. -/
noncomputable def objective (setup : StochasticConditionalGradientSetup E Ω Ξ)
    (x : E) : ℝ :=
  objectiveExpectation setup.P setup.F (setup.ξ 0) x

/-- Fixed-query unbiasedness transported from the sample law of `ξ 0` to the
base probability space. -/
theorem oracle_unbiased (setup : StochasticConditionalGradientSetup E Ω Ξ)
    (x : E) (hx : x ∈ setup.X) :
    oracleWellDefined setup.P setup.gradF (setup.ξ 0) x ∧
      oracleMean setup.P setup.gradF (setup.ξ 0) x = setup.gradf x := by
  have hsrc := setup.stochasticOracle.unbiased x hx
  constructor
  · simpa [oracleWellDefined, oracleKernel, Function.comp_def] using
      hsrc.1.comp_measurable (setup.hξ_meas 0)
  · have hmap :
        ∫ s, setup.gradF x s ∂Measure.map (setup.ξ 0) setup.P =
          ∫ ω, setup.gradF x (setup.ξ 0 ω) ∂setup.P := by
      simpa [Function.comp_def] using
        integral_map (setup.hξ_meas 0).aemeasurable hsrc.1.aestronglyMeasurable
    calc
      oracleMean setup.P setup.gradF (setup.ξ 0) x
          = ∫ ω, setup.gradF x (setup.ξ 0 ω) ∂setup.P := rfl
      _ = ∫ s, setup.gradF x s ∂Measure.map (setup.ξ 0) setup.P := hmap.symm
      _ = setup.gradf x := by
            simpa [oracleMean, oracleKernel] using hsrc.2

/-- Fixed-query variance bound transported from the sample law of `ξ 0` to the
base probability space. -/
theorem oracle_variance_bound (setup : StochasticConditionalGradientSetup E Ω Ξ)
    (x : E) (hx : x ∈ setup.X) :
    Integrable (fun ω => ‖setup.gradF x (setup.ξ 0 ω) - setup.gradf x‖ ^ 2)
        setup.P ∧
      ∫ ω, ‖setup.gradF x (setup.ξ 0 ω) - setup.gradf x‖ ^ 2 ∂setup.P ≤
        setup.σ ^ 2 := by
  have hsrc := setup.stochasticOracle.variance x hx
  constructor
  · simpa [Function.comp_def] using hsrc.1.comp_measurable (setup.hξ_meas 0)
  · have hmap :
        ∫ s, ‖setup.gradF x s - setup.gradf x‖ ^ 2 ∂Measure.map (setup.ξ 0) setup.P =
          ∫ ω, ‖setup.gradF x (setup.ξ 0 ω) - setup.gradf x‖ ^ 2 ∂setup.P := by
      simpa [Function.comp_def] using
        integral_map (setup.hξ_meas 0).aemeasurable hsrc.1.aestronglyMeasurable
    rw [← hmap]
    exact hsrc.2

/-- Gradient interface for the expected objective. -/
theorem gradf_hasGradientAt (setup : StochasticConditionalGradientSetup E Ω Ξ)
    (x : E) (hx : x ∈ setup.X) :
    HasGradientAt (objectiveExpectation setup.P setup.F (setup.ξ 0)) (setup.gradf x) x :=
  setup.hgradf_hasGradientAt x hx

/-- Feasible Lipschitz smoothness of the deterministic gradient selector. -/
theorem gradf_smooth (setup : StochasticConditionalGradientSetup E Ω Ξ)
    (x y : E) (hx : x ∈ setup.X) (hy : y ∈ setup.X) :
    ‖setup.gradf x - setup.gradf y‖ ≤ setup.L * ‖x - y‖ :=
  setup.hgradf_smooth x y hx hy

/-- Measurability of the deterministic gradient selector on the feasible
carrier. -/
theorem gradfOnX_measurable (setup : StochasticConditionalGradientSetup E Ω Ξ) :
    Measurable (fun x : setup.X => setup.gradf (x : E)) :=
  setup.hgradfOnX_measurable

/-- Joint measurability of the feasible stochastic-gradient kernel. -/
theorem gradF_feasible_joint_measurable
    (setup : StochasticConditionalGradientSetup E Ω Ξ) :
    Measurable (fun p : setup.X × Ξ => setup.gradF (p.1 : E) p.2) := by
  have hres := setup.stochasticOracle.residual_joint_measurable
  have htarget :
      Measurable (fun p : setup.X × Ξ => setup.gradf (p.1 : E)) :=
    setup.gradfOnX_measurable.comp measurable_fst
  simpa [sub_add_cancel] using hres.add htarget

/-- Fixed feasible stochastic-gradient fibers are measurable in the sample. -/
theorem gradF_fiber_measurable_of_mem
    (setup : StochasticConditionalGradientSetup E Ω Ξ)
    (x : E) (hx : x ∈ setup.X) :
    Measurable (fun s : Ξ => setup.gradF x s) := by
  simpa using
    (measurable_fiber_of_prod_measurable
      (G := fun x : setup.X => fun s : Ξ => setup.gradF (x : E) s)
      setup.gradF_feasible_joint_measurable ⟨x, hx⟩)

/-- Paired feasible stochastic-gradient differences are jointly measurable. -/
theorem paired_gradDiff_feasible_joint_measurable
    (setup : StochasticConditionalGradientSetup E Ω Ξ) :
    Measurable
      (fun p : (setup.X × setup.X) × Ξ =>
        setup.gradF (p.1.1 : E) p.2 - setup.gradF (p.1.2 : E) p.2) := by
  have hleft :
      Measurable
        (fun p : (setup.X × setup.X) × Ξ =>
          setup.gradF (p.1.1 : E) p.2) := by
    simpa using
      setup.gradF_feasible_joint_measurable.comp
        (((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  have hright :
      Measurable
        (fun p : (setup.X × setup.X) × Ξ =>
          setup.gradF (p.1.2 : E) p.2) := by
    simpa using
      setup.gradF_feasible_joint_measurable.comp
        (((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  exact hleft.sub hright

/-- Sampled stochastic-oracle regularity for feasible random queries. -/
theorem sampled_gradF_measurable (setup : StochasticConditionalGradientSetup E Ω Ξ)
    (k : ℕ) {x : Ω → E} (hx : Measurable x)
    (hx_mem : ∀ ω, x ω ∈ setup.X) :
    Measurable (fun ω => setup.gradF (x ω) (setup.ξ k ω)) := by
  have hxX : Measurable (fun ω => (⟨x ω, hx_mem ω⟩ : setup.X)) :=
    hx.subtype_mk
  simpa using
    setup.gradF_feasible_joint_measurable.comp
      (hxX.prodMk (setup.hξ_meas k))

/-- Measurability of the selected linear-minimization oracle. -/
theorem linearMinimizer_measurable
    (setup : StochasticConditionalGradientSetup E Ω Ξ) :
    Measurable setup.lmo.toFun :=
  setup.lmo.measurable

end StochasticConditionalGradientSetup

end SOptLib
