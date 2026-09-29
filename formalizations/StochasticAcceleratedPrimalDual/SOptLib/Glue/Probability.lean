-- SOptLib/Glue/Probability.lean
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.MeasurableSpace.MeasurablyGenerated
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Process.Filtration
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.Probability.Moments.IntegrableExpMul
import SOptLib.Glue.Algebra
import SOptLib.Glue.Analysis


open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace NNReal

/-- Transfer fixed-fiber integrability through an independent random parameter.

If `Y` has law `ν`, `X` is independent of `Y`, and every nonnegative fiber
`φ w ·` is integrable with uniformly bounded integral, then
`ω ↦ φ (X ω) (Y ω)` is integrable.

Layer: Glue | Gap: Level 1 (product-law/Fubini integrability transfer)
Proof: identify the joint law using independence, apply product integrability, and
  dominate the fiber `L¹` norms by the uniform integral bound.
Source: Mathlib product-measure integration and independence APIs
Used in: stochastic mirror descent random-iterate variance bridge
Book citation: book/PAPER/ALG.json#/stochastic_mirror_descent
Origin algorithm: Lan stochastic mirror descent variance transfer -/
theorem integrable_comp_of_indep_fixed_integral_bound
    {Ω W S : Type*} [MeasurableSpace Ω] [MeasurableSpace W] [MeasurableSpace S]
    {P : Measure Ω} {ν : Measure S} [IsFiniteMeasure P]
    {φ : W → S → ℝ} {X : Ω → W} {Y : Ω → S} {C : ℝ}
    (hφ : Measurable (Function.uncurry φ))
    (hX : Measurable X) (hY : Measurable Y)
    (h_indep : IndepFun X Y P)
    (h_dist : Measure.map Y P = ν)
    (hφ_nonneg : ∀ w s, 0 ≤ φ w s)
    (hC_nonneg : 0 ≤ C)
    (hfixed_int : ∀ w, Integrable (fun s => φ w s) ν)
    (hfixed_bound : ∀ w, ∫ s, φ w s ∂ν ≤ C) :
    Integrable (fun ω => φ (X ω) (Y ω)) P := by
  have h_joint_meas : AEMeasurable (fun ω => (X ω, Y ω)) P :=
    (hX.prodMk hY).aemeasurable
  have h_f_meas : Measurable (fun p : W × S => φ p.1 p.2) := hφ
  have h_prod_eq : P.map (fun ω => (X ω, Y ω)) = (P.map X).prod ν := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable).mp
      h_indep, h_dist]
  haveI : IsFiniteMeasure ν := by
    rw [← h_dist]
    exact Measure.isFiniteMeasure_map P Y
  haveI : IsFiniteMeasure (P.map X) :=
    Measure.isFiniteMeasure_map P X
  suffices h_prod : Integrable (fun p : W × S => φ p.1 p.2) ((P.map X).prod ν) by
    have h_on_map : Integrable (fun p : W × S => φ p.1 p.2)
        (P.map (fun ω => (X ω, Y ω))) := h_prod_eq ▸ h_prod
    exact (integrable_map_measure h_f_meas.aestronglyMeasurable h_joint_meas).mp h_on_map
  rw [integrable_prod_iff h_f_meas.aestronglyMeasurable]
  refine ⟨Filter.Eventually.of_forall hfixed_int, ?_⟩
  refine Integrable.mono (integrable_const C)
    ((h_f_meas.norm.stronglyMeasurable.integral_prod_right').aestronglyMeasurable)
    (Filter.Eventually.of_forall ?_)
  intro w
  have h_abs_eq :
      (∫ y, ‖φ (w, y).1 (w, y).2‖ ∂ν) = ∫ s, φ w s ∂ν := by
    refine integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro s
    exact Real.norm_of_nonneg (hφ_nonneg w s)
  have h_int_nonneg : 0 ≤ ∫ s, φ w s ∂ν := by
    exact integral_nonneg fun s => hφ_nonneg w s
  rw [h_abs_eq, Real.norm_eq_abs, abs_of_nonneg h_int_nonneg,
    Real.norm_eq_abs, abs_of_nonneg hC_nonneg]
  exact hfixed_bound w



/-- Transfer a uniform fixed-fiber integral bound through an independent random parameter.

If `Y` has law `ν`, `X` is independent of `Y`, and each fixed-fiber integral
`∫ s, φ w s ∂ν` is bounded above by `C`, then the composed random integral
`∫ ω, φ (X ω) (Y ω) ∂P` is bounded above by `C`, provided the composed kernel is
integrable.

Layer: Glue | Gap: Level 1 (product-law/Fubini integral-bound transfer)
Proof: identify the joint law using independence, rewrite as a product integral,
  apply Fubini, and integrate the pointwise fixed-fiber bound.
Source: Mathlib product-measure integration and independence APIs
Used in: stochastic mirror descent random-iterate variance bridge
Book citation: book/PAPER/ALG.json#/stochastic_mirror_descent
Origin algorithm: Lan stochastic mirror descent variance transfer -/
theorem integral_comp_le_of_indep_fixed_integral_bound
    {Ω W S : Type*} [MeasurableSpace Ω] [MeasurableSpace W] [MeasurableSpace S]
    {P : Measure Ω} {ν : Measure S} [IsProbabilityMeasure P] [IsProbabilityMeasure ν]
    {φ : W → S → ℝ} {X : Ω → W} {Y : Ω → S} {C : ℝ}
    (hφ : Measurable (Function.uncurry φ))
    (hX : Measurable X) (hY : Measurable Y)
    (h_indep : IndepFun X Y P)
    (h_dist : Measure.map Y P = ν)
    (h_int : Integrable (fun ω => φ (X ω) (Y ω)) P)
    (hfixed_bound : ∀ w, ∫ s, φ w s ∂ν ≤ C) :
    ∫ ω, φ (X ω) (Y ω) ∂P ≤ C := by
  have h_joint_meas : AEMeasurable (fun ω => (X ω, Y ω)) P :=
    (hX.prodMk hY).aemeasurable
  have h_f_meas : Measurable (fun p : W × S => φ p.1 p.2) := hφ
  have h_prod_eq : P.map (fun ω => (X ω, Y ω)) = (P.map X).prod ν := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable).mp
      h_indep, h_dist]
  have h_int_prod : Integrable (fun p : W × S => φ p.1 p.2) ((P.map X).prod ν) := by
    have h1 : Integrable (fun p : W × S => φ p.1 p.2)
        (P.map (fun ω => (X ω, Y ω))) :=
      (integrable_map_measure h_f_meas.aestronglyMeasurable h_joint_meas).mpr h_int
    rwa [h_prod_eq] at h1
  haveI : IsProbabilityMeasure (P.map X) :=
    Measure.isProbabilityMeasure_map hX.aemeasurable
  calc
    ∫ ω, φ (X ω) (Y ω) ∂P
        = ∫ p : W × S, φ p.1 p.2 ∂P.map (fun ω => (X ω, Y ω)) :=
          (integral_map h_joint_meas h_f_meas.aestronglyMeasurable).symm
    _ = ∫ p : W × S, φ p.1 p.2 ∂(P.map X).prod ν := by rw [h_prod_eq]
    _ = ∫ w : W, ∫ s : S, φ w s ∂ν ∂P.map X := integral_prod _ h_int_prod
    _ ≤ ∫ _ : W, C ∂P.map X := by
      exact integral_mono h_int_prod.integral_prod_left (integrable_const C)
        (fun w => hfixed_bound w)
    _ = C := by simp [integral_const, probReal_univ]



/-- Transfer fixed-fiber zero integrals through an independent random parameter.

If `Y` has law `ν`, `X` is independent of `Y`, and every fixed fiber
`∫ s, φ w s ∂ν` is zero, then the composed random integral
`∫ ω, φ (X ω) (Y ω) ∂P` is zero, provided the composed kernel is integrable.

Layer: Glue | Gap: Level 1 (product-law/Fubini vector cancellation)
Proof: identify the joint law using independence, rewrite as a product integral,
  apply Fubini, and integrate the fixed-fiber zero identity.
Source: Mathlib product-measure integration and independence APIs
Used in: stochastic mirror descent random-iterate oracle unbiasedness bridge
Book citation: book/PAPER/ALG.json#/stochastic_mirror_descent
Origin algorithm: Lan stochastic mirror descent oracle unbiasedness transfer -/
theorem integral_comp_eq_zero_of_indep_fixed_integral_zero
    {Ω W S V : Type*} [MeasurableSpace Ω] [MeasurableSpace W] [MeasurableSpace S]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    {P : Measure Ω} {ν : Measure S} [IsFiniteMeasure P] [SFinite ν]
    {φ : W → S → V} {X : Ω → W} {Y : Ω → S}
    (hφ : Measurable (Function.uncurry φ))
    (hX : Measurable X) (hY : Measurable Y)
    (h_indep : IndepFun X Y P)
    (h_dist : Measure.map Y P = ν)
    (h_int : Integrable (fun ω => φ (X ω) (Y ω)) P)
    (hfixed_zero : ∀ w, ∫ s, φ w s ∂ν = 0) :
    ∫ ω, φ (X ω) (Y ω) ∂P = 0 := by
  have h_joint_meas : AEMeasurable (fun ω => (X ω, Y ω)) P :=
    (hX.prodMk hY).aemeasurable
  have h_f_meas : Measurable (fun p : W × S => φ p.1 p.2) := hφ
  have h_prod_eq : P.map (fun ω => (X ω, Y ω)) = (P.map X).prod ν := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable).mp
      h_indep, h_dist]
  have h_int_prod : Integrable (fun p : W × S => φ p.1 p.2) ((P.map X).prod ν) := by
    have h1 : Integrable (fun p : W × S => φ p.1 p.2)
        (P.map (fun ω => (X ω, Y ω))) :=
      (integrable_map_measure h_f_meas.aestronglyMeasurable h_joint_meas).mpr h_int
    rwa [h_prod_eq] at h1
  calc
    ∫ ω, φ (X ω) (Y ω) ∂P
        = ∫ p : W × S, φ p.1 p.2 ∂P.map (fun ω => (X ω, Y ω)) :=
          (integral_map h_joint_meas h_f_meas.aestronglyMeasurable).symm
    _ = ∫ p : W × S, φ p.1 p.2 ∂(P.map X).prod ν := by rw [h_prod_eq]
    _ = ∫ w : W, ∫ s : S, φ w s ∂ν ∂P.map X := integral_prod _ h_int_prod
    _ = 0 := by simp [hfixed_zero]


open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory

/-- An independent sequence has its current coordinate independent of the sigma-algebra
generated by all strictly earlier coordinates.

Layer: Glue | Gap: Level 1 (independence of a current sample from its natural past)
Proof: apply independence of disjoint indexed `iSup`s to `{j | j < t}` and `{t}`.
Source: Mathlib independence API for independent families of sigma-algebras
Used in: stochastic mirror descent sample filtration independence
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan stochastic mirror descent -/
theorem iIndepFun.indep_past_iSup_current
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    {μ : Measure Ω} (ξ : ℕ → Ω → S) (t : ℕ)
    (hξ_measurable : ∀ n, Measurable (ξ n))
    (hξ_iIndep : iIndepFun ξ μ) :
    Indep (⨆ j < t, MeasurableSpace.comap (ξ j)
        (by infer_instance : MeasurableSpace S))
      (MeasurableSpace.comap (ξ t)
        (by infer_instance : MeasurableSpace S)) μ := by
  classical
  let mNat : ℕ → MeasurableSpace Ω :=
    fun j => MeasurableSpace.comap (ξ j)
      (by infer_instance : MeasurableSpace S)
  have hiNat : iIndep mNat μ := by
    simpa [mNat] using hξ_iIndep.iIndep
  have h_le : ∀ j, mNat j ≤ (by infer_instance : MeasurableSpace Ω) := by
    intro j
    simpa [mNat] using (hξ_measurable j).comap_le
  let Sset : Set ℕ := {j | j < t}
  let Tset : Set ℕ := {j | j = t}
  have hST : Disjoint Sset Tset := by
    rw [Set.disjoint_iff_inter_eq_empty]
    ext j
    simp [Sset, Tset]
  have h_ind : Indep (⨆ j ∈ Sset, mNat j) (⨆ j ∈ Tset, mNat j) μ :=
    indep_iSup_of_disjoint (m := mNat) h_le hiNat (S := Sset) (T := Tset) hST
  simpa [mNat, Sset, Tset] using h_ind

end ProbabilityTheory


open MeasureTheory ProbabilityTheory

/-- A random variable measurable with respect to a past sigma-algebra is independent of
the current sample whenever that past sigma-algebra is independent of the current
sample's generated sigma-algebra.

Layer: Glue | Gap: Level 1 (past/current sample independence bridge)
Proof: rewrite `IndepFun` as sigma-algebra independence and shrink the independent
  left sigma-algebra using past measurability.
Source: Mathlib independence API for sub-sigma-algebras and random variables
Used in: stochastic mirror descent current-sample independence of adapted iterates
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan stochastic mirror descent -/
theorem indepFun_of_past_measurable_current_iid_sample
    {Ω W S : Type*} [MeasurableSpace Ω] [MeasurableSpace W] [MeasurableSpace S]
    {μ : Measure Ω} {past : MeasurableSpace Ω} {X : Ω → W} {Y : Ω → S}
    (hX_past : Measurable[past] X)
    (h_past_indep_current :
      Indep past (MeasurableSpace.comap Y (by infer_instance : MeasurableSpace S)) μ) :
    IndepFun X Y μ := by
  rw [IndepFun_iff_Indep]
  exact indep_of_indep_of_le_left h_past_indep_current hX_past.comap_le

/-- A left-measurable random variable inherits independence from its sigma-algebra.

If `X` is measurable with respect to a sub-sigma-algebra `m`, and `m` is
independent of the sigma-algebra generated by `Y`, then `X` and `Y` are
independent random variables.

Layer: Glue | Gap: Level 0 (sigma-algebra independence transfer)
Proof: rewrite `IndepFun` as independence of generated sigma-algebras, then use
  monotonicity of independence on the left with `hX.comap_le`.
Source: Mathlib probability independence and measurable-space comap APIs
Used in: stochastic mirror descent oracle independence and variance control
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem indepFun_of_measurable_left_of_indep_comap
    {Ω W S : Type*} [MeasurableSpace Ω] [MeasurableSpace W] [MeasurableSpace S]
    {μ : Measure Ω} {m : MeasurableSpace Ω} {X : Ω → W} {Y : Ω → S}
    (hX : Measurable[m] X)
    (h_indep : Indep m (MeasurableSpace.comap Y (by infer_instance : MeasurableSpace S)) μ) :
    IndepFun X Y μ := by
  rw [IndepFun_iff_Indep]
  exact indep_of_indep_of_le_left h_indep hX.comap_le

namespace ProbabilityTheory

/-- Equal distribution transports measurable one-sample integrals through post-composition.

If `ξ` and `ξ'` are identically distributed under the same measure and `φ` is a
measurable kernel into a Borel normed vector space, then the one-sample
integrals of `φ ∘ ξ` and `φ ∘ ξ'` agree.

Layer: Glue | Gap: Level 0 (IdentDistrib integral transport)
Proof: Compose the identical-distribution hypothesis with the measurable map
  `φ`, then apply the Mathlib integral equality for identically distributed
  random variables.
Source: Mathlib probability `IdentDistrib` and Bochner integral APIs
Used in: stochastic mirror descent sample expectation transport for measurable
  one-sample kernels
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem IdentDistrib.integral_comp_eq_of_measurable
    {Ω S β : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    [MeasurableSpace β] [NormedAddCommGroup β] [NormedSpace ℝ β] [BorelSpace β]
    {P : Measure Ω} {ξ ξ' : Ω → S} {φ : S → β} (hξ : IdentDistrib ξ ξ' P P)
    (hφ : Measurable φ) :
    ∫ ω, φ (ξ ω) ∂P = ∫ ω, φ (ξ' ω) ∂P := by
  simpa using (hξ.comp hφ).integral_eq

end ProbabilityTheory

namespace Integrable

/-- Inner products with a bounded random displacement are integrable.

If `δ` is integrable and `x - c` is almost surely bounded by `R`, then the
real-valued random variable `⟪δ ω, x ω - c⟫_ℝ` is integrable.

Layer: Glue | Gap: Level 1 (bounded-displacement inner-product integrability)
Proof: Build almost-everywhere strong measurability of the scalar inner product
  and dominate its norm by `R * ‖δ ω‖` using `norm_inner_le_norm`. Integrability
  follows from `Integrable.mono'` and integrability of the norm of `δ`.
Source: Mathlib measure theory Bochner integrability APIs and inner product norm
  inequalities
Used in: stochastic mirror descent stochastic error-term integrability for
  bounded prox iterates
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem inner_sub_const_of_bounded
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {μ : Measure Ω} {δ x : Ω → E} {c : E} {R : ℝ}
    (hx_meas : AEStronglyMeasurable x μ)
    (hδ_int : Integrable δ μ)
    (hx_bound : ∀ᵐ ω ∂μ, ‖x ω - c‖ ≤ R) :
    Integrable (fun ω => ⟪δ ω, x ω - c⟫_ℝ) μ := by
  have hbound_int : Integrable (fun ω => R * ‖δ ω‖) μ :=
    hδ_int.norm.const_mul R
  have hscalar_meas :
      AEStronglyMeasurable (fun ω => ⟪δ ω, x ω - c⟫_ℝ) μ := by
    exact hδ_int.aestronglyMeasurable.inner
      (hx_meas.sub aestronglyMeasurable_const)
  have hpoint_bound :
      ∀ᵐ ω ∂μ, ‖⟪δ ω, x ω - c⟫_ℝ‖ ≤ R * ‖δ ω‖ := by
    filter_upwards [hx_bound] with ω hxR
    calc
      ‖⟪δ ω, x ω - c⟫_ℝ‖
          ≤ ‖δ ω‖ * ‖x ω - c‖ := norm_inner_le_norm _ _
      _ ≤ ‖δ ω‖ * R := mul_le_mul_of_nonneg_left hxR (norm_nonneg _)
      _ = R * ‖δ ω‖ := by ring
  exact Integrable.mono' hbound_int hscalar_meas hpoint_bound

end Integrable

/-- A measurable oracle-deviation map is almost everywhere strongly measurable.

If a map from the sample space into a second-countable pseudometrizable
measurable topological space is measurable, then it is
`AEStronglyMeasurable` with respect to any measure on the sample space.

Layer: Glue | Gap: Level 0 (measurable to a.e. strongly measurable bridge)
Proof: apply Mathlib's `Measurable.aestronglyMeasurable` coercion theorem
  for second-countable pseudometrizable target spaces.
Source: Mathlib measure theory strongly measurable and Borel measurability APIs
Used in: stochastic mirror descent measurable oracle deviation construction
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem Measurable.aestronglyMeasurable_measure
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [TopologicalSpace E]
    [TopologicalSpace.PseudoMetrizableSpace E]
    [SecondCountableTopology E] [OpensMeasurableSpace E]
    {μ : Measure Ω} {f : Ω → E}
    (hf : Measurable f) :
    AEStronglyMeasurable f μ := by
  exact hf.aestronglyMeasurable

/-- A fixed-target Bregman formula section is measurable.

For a fixed `z`, if the scalar potential `v`, point evaluation map `eval`, and
gradient selector `grad` are measurable, then
`x ↦ v z - v x - ⟪grad x, eval z - eval x⟫_ℝ` is measurable.

Layer: Glue | Gap: Level 1 (Bregman formula measurability)
Proof: build measurability of the displacement by measurable subtraction, then
  compose `continuous_inner.measurable` with the product map
  `hgrad.prodMk hdisp`; close under scalar subtraction.
Source: Mathlib MeasureTheory measurable arithmetic and continuous inner
  product APIs
Used in: stochastic mirror descent measurability of fixed-target Bregman prox
  objective sections
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem Measurable.bregmanFormula_left
    {P : Type*} [MeasurableSpace P]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [MeasurableSub₂ E] [OpensMeasurableSpace (E × E)]
    {v : P → ℝ} {eval grad : P → E}
    (hv : Measurable v) (heval : Measurable eval) (hgrad : Measurable grad)
    (z : P) :
    Measurable (fun x : P => v z - v x - ⟪grad x, eval z - eval x⟫_ℝ) := by
  have hdisp : Measurable (fun x : P => eval z - eval x) :=
    measurable_const.sub heval
  have hinner :
      Measurable (fun x : P => ⟪grad x, eval z - eval x⟫_ℝ) := by
    simpa [Function.comp_def] using
      (continuous_inner.measurable.comp (hgrad.prodMk hdisp))
  exact (measurable_const.sub hv).sub hinner

/-- A function measurable for a past filtration is measurable in the ambient space.

If `f` is measurable with respect to a sub-sigma-algebra `m` on `Ω`, and
`m ≤ mΩ`, then the same function is measurable for the ambient measurable
space `mΩ`.

Layer: Glue | Gap: Level 0 (sub-sigma-algebra measurability upgrade)
Proof: apply `Measurable.mono` with the domain monotonicity hypothesis and
  reflexivity on the codomain measurable space.
Source: Mathlib MeasureTheory measurability monotonicity APIs
Used in: stochastic mirror descent past-filtration measurability lifted to
  ambient random-variable measurability
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem Measurable.of_measurableSpace_le
    {Ω E : Type*} [mΩ : MeasurableSpace Ω] [mE : MeasurableSpace E]
    {m : MeasurableSpace Ω} {f : Ω → E}
    (hf : @Measurable Ω E m mE f)
    (hm : m ≤ mΩ) :
    @Measurable Ω E mΩ mE f := by
  exact hf.mono hm (by rfl)

/-- A ternary prox-style selector remains measurable after measurable random inputs.

If a selector `prox` is measurable as a function on `P × E × ℝ`, and the
iterate, gradient surrogate, and stepsize observables are measurable, then the
samplewise prox step `ω ↦ prox (x ω) (g ω) (γ ω)` is measurable.

Layer: Model | Gap: Level 0 (ternary prox-step measurability composition)
Proof: build the measurable product map with `Measurable.prodMk`, compose it
  with the measurable selector using `Measurable.comp`, and simplify the
  product projections.
Source: Mathlib measure theory measurability composition and product APIs
Used in: stochastic mirror descent proxStep measurability for random iterates, stochastic gradients, and stepsizes
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem Measurable.proxStep_comp
    {Ω P E : Type*} [MeasurableSpace Ω] [MeasurableSpace P] [MeasurableSpace E]
    {prox : P → E → ℝ → P} {x : Ω → P} {g : Ω → E} {γ : Ω → ℝ}
    (hprox : Measurable (fun p : P × E × ℝ => prox p.1 p.2.1 p.2.2))
    (hx : Measurable x) (hg : Measurable g) (hγ : Measurable γ) :
    Measurable (fun ω => prox (x ω) (g ω) (γ ω)) := by
  simpa [Function.comp_def] using hprox.comp (hx.prodMk (hg.prodMk hγ))

/-- The canonical start-point Bregman observable is measurable by composition.

For a fixed start anchor `z`, if the right section `fun x => V x z` of the
Bregman kernel is measurable and the start iterate `X` is measurable, then
`fun ω => V (X ω) z` is measurable.

Layer: Glue | Gap: Level 0 (canonical start Bregman measurability)
Proof: direct use of Mathlib's measurable-function composition API via
  `hV.comp hX`.
Source: Mathlib measure-theoretic measurability composition APIs
Used in: stochastic mirror descent canonical start Bregman observable measurability
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem startBregman_measurable
    {Ω P : Type*} [MeasurableSpace Ω] [MeasurableSpace P]
    (V : P → P → ℝ) (X : Ω → P) (z : P)
    (hV : Measurable (fun x : P => V x z))
    (hX : Measurable X) :
    Measurable (fun ω => V (X ω) z) := by
  exact hV.comp hX

open scoped BigOperators

/-- Square-integrability implies integrability for strongly measurable random variables on a finite measure.

If `v` is strongly measurable and `‖v ω‖ ^ 2` is integrable under a finite
measure, then `v` is integrable.

Layer: Glue | Gap: Level 1 (finite-measure L2-to-L1 integrability bridge)
Proof: Use Mathlib's `integrable_norm_pow_of_le` to derive integrability of
  `‖v‖` from integrability of `‖v‖ ^ 2`, then convert back with
  `integrable_norm_iff`.
Source: Mathlib measure theory integrability and finite measure APIs
Used in: stochastic mirror descent noise and stochastic subgradient integrability
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem integrable_of_integrable_norm_sq
    {Ω : Type*} [MeasurableSpace Ω]
    {E : Type*} [NormedAddCommGroup E]
    {μ : Measure Ω} [IsFiniteMeasure μ] {v : Ω → E}
    (hv_meas : AEStronglyMeasurable v μ)
    (hv_sq : Integrable (fun ω => ‖v ω‖ ^ 2) μ) :
    Integrable v μ := by
  have hnorm : Integrable (fun ω => ‖v ω‖) μ := by
    simpa using
      (integrable_norm_pow_of_le (μ := μ) hv_meas
        (by norm_num : (1 : ℕ) ≤ 2) hv_sq)
  exact (integrable_norm_iff hv_meas).1 hnorm

/-- A bounded measurable real random variable is integrable on a finite measure space.

A measurable scalar random variable whose norm is uniformly bounded by a real
constant is integrable with respect to any finite measure.

Layer: Glue | Gap: Level 0 (bounded measurable real random variable integrability)
Proof: apply `Integrable.of_bound` using measurability upgraded to strong
  measurability and convert the pointwise bound into an almost-everywhere bound
  with `ae_of_all`.
Source: Mathlib measure theory integrability and finite-measure APIs
Used in: stochastic mirror descent bounded oracle-noise integrability checks
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem integrable_of_measurable_bounded_real
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {Z : Ω → ℝ} (hZ : Measurable Z) {C : ℝ} (hC : ∀ ω, ‖Z ω‖ ≤ C) :
    Integrable Z μ := by
  exact Integrable.of_bound hZ.aestronglyMeasurable C (ae_of_all μ hC)

/-- The parameterized oracle mean is measurable from joint oracle measurability.

If the oracle kernel `(x, s) ↦ oracle x s` is measurable and the sample map
`ξ` is measurable, then the Bochner integral mean
`x ↦ ∫ ω, oracle x (ξ ω) ∂μ` is measurable.

Layer: Model | Gap: Level 1 (measurability of parameterized oracle means)
Proof: compose the jointly measurable oracle with the measurable product map
  `(x, ω) ↦ (x, ξ ω)`, then use strong measurability and Mathlib's
  `integral_prod_right.measurable` API for Bochner integrals.
Source: Mathlib measure theory Bochner integral and product measurability APIs
Used in: stochastic mirror descent oracle mean construction from a measurable
  stochastic first-order oracle
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem oracleMean_measurable_of_joint_measurable
    {Ω X S E : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace S]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    (μ : Measure Ω) [SFinite μ]
    (oracle : X → S → E) (ξ : Ω → S)
    (h_oracle : Measurable (fun p : X × S => oracle p.1 p.2))
    (hξ : Measurable ξ) :
    Measurable (fun x : X => ∫ ω, oracle x (ξ ω) ∂μ) := by
  have hpair : Measurable (fun p : X × Ω => (p.1, ξ p.2)) :=
    Measurable.prodMk measurable_fst (hξ.comp measurable_snd)
  have hkernel : Measurable (fun p : X × Ω => oracle p.1 (ξ p.2)) :=
    h_oracle.comp hpair
  exact hkernel.stronglyMeasurable.integral_prod_right.measurable

/-- The oracle noise deviation is measurable when the sampled oracle, mean oracle, and iterate are measurable.

For a measurable sample oracle `G`, measurable mean oracle `g`, and measurable iterate `x`,
the pointwise deviation `ω ↦ G ω - g (x ω)` is measurable.

Layer: Layer0 | Gap: Level 0 (oracle deviation measurability)
Proof: compose the mean oracle measurability with iterate measurability, then apply
  the measurable subtraction API to `G` and `g ∘ x`.
Source: Mathlib measurable algebra APIs for subtraction and composition
Used in: stochastic mirror descent oracle-noise deviation as a measurable random variable
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic mirror descent -/
theorem oracleDeviation_measurable
    {Ω X E : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace E]
    [Sub E] [MeasurableSub₂ E]
    (G : Ω → E) (g : X → E) (x : Ω → X)
    (hG : Measurable G) (hg : Measurable g) (hx : Measurable x) :
    Measurable (fun ω => G ω - g (x ω)) := by
  exact hG.sub (hg.comp hx)

/-- A bounded measurable Bregman-shaped real random variable is integrable.

If the Bregman kernel slice `fun x => V x z` is measurable, the iterate random
variable `X` is measurable, and the composed value is uniformly norm-bounded,
then `fun ω => V (X ω) z` is integrable under any finite measure.

Layer: Glue | Gap: Level 0 (bounded measurable Bregman integrability)
Proof: compose measurability of the kernel slice with `X` to obtain
  a.e.-strong measurability, then apply `Integrable.of_bound` with the
  pointwise norm bound converted to an a.e. bound by `ae_of_all`.
Source: Mathlib measure theory integrability APIs for finite measures
Used in: stochastic mirror descent Bregman prox-step integrability estimates
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem integrable_bregman_of_measurable_bounded
    {Ω P : Type*} [MeasurableSpace Ω] [MeasurableSpace P]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    (V : P → P → ℝ) {X : Ω → P} {z : P}
    (hV : Measurable (fun x : P => V x z)) (hX : Measurable X)
    {C : ℝ} (hC : ∀ ω, ‖V (X ω) z‖ ≤ C) :
    Integrable (fun ω => V (X ω) z) μ := by
  exact Integrable.of_bound (hV.comp hX).aestronglyMeasurable C (ae_of_all μ hC)

/-- Integrability of a scalar multiple of an affine finite-sum difference.

If `A` is integrable and each summand in the finite families `B` and `C` is
integrable on `s`, then the pathwise expression
`W⁻¹ * (A + ∑ i ∈ s, B i - ∑ i ∈ s, C i)` is integrable.

Layer: Glue | Gap: Level 0 (finite-sum affine integrability closure)
Proof: finite sums are integrable by `MeasureTheory.integrable_finset_sum`.
  The result follows from integrability closure under addition, subtraction,
  and deterministic scalar multiplication.
Source: Mathlib measure theory integrability finite-sum and algebra closure APIs
Used in: stochastic mirror descent pathwise right-hand-side integrability for finite accumulated error sums
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem integrable_const_mul_add_finset_sum_sub_finset_sum
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (s : Finset ι) (W : ℝ) (A : Ω → ℝ) (B C : ι → Ω → ℝ)
    (hA : Integrable A μ)
    (hB : ∀ i ∈ s, Integrable (B i) μ)
    (hC : ∀ i ∈ s, Integrable (C i) μ) :
    Integrable (fun ω =>
      W⁻¹ * (A ω + Finset.sum s (fun i => B i ω) -
        Finset.sum s (fun i => C i ω))) μ := by
  classical
  have hBsum : Integrable (fun ω => Finset.sum s (fun i => B i ω)) μ := by
    simpa using
      (MeasureTheory.integrable_finset_sum (μ := μ) (s := s)
        (f := fun i ω => B i ω) hB)
  have hCsum : Integrable (fun ω => Finset.sum s (fun i => C i ω)) μ := by
    simpa using
      (MeasureTheory.integrable_finset_sum (μ := μ) (s := s)
        (f := fun i ω => C i ω) hC)
  exact ((hA.add hBsum).sub hCsum).const_mul W⁻¹

/-- Integrability is preserved by finite sums of deterministic scalar multiples.

If each indexed random vector `Z i` is integrable on a finite index set `s`,
then the pointwise finite sum of deterministic real multiples `c i • Z i` is
integrable.

Layer: Glue | Gap: Level 0 (finite-sum constant-multiple integrability)
Proof: apply Mathlib's finite-sum integrability closure theorem and discharge
  each summand with scalar-multiple preservation of integrability.
Source: Mathlib MeasureTheory Bochner integrability and finite-sum APIs
Used in: stochastic mirror descent aggregation of finitely many scaled
  integrable oracle terms
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem integrable_finset_sum_const_mul
    {Ω ι E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure Ω} (s : Finset ι) (c : ι → ℝ) (Z : ι → Ω → E)
    (hZ : ∀ i ∈ s, Integrable (Z i) μ) :
    Integrable (fun ω => Finset.sum s (fun i => c i • Z i ω)) μ := by
  classical
  exact
    MeasureTheory.integrable_finset_sum (μ := μ) (s := s)
      (f := fun i ω => c i • Z i ω)
      (fun i hi => (hZ i hi).smul (c i))

/-- Integrating a pointwise affine upper bound for real-valued random variables.

If `A` is pointwise bounded above by the affine combination `a • B + b • C`
and all three functions are integrable, then the integral of `A` is bounded by
the same affine combination of the integrals of `B` and `C`.

Layer: Glue | Gap: Level 1 (affine integral monotonicity bookkeeping)
Proof: apply `MeasureTheory.integral_mono` to the pointwise bound after proving
  integrability of the affine upper bound, then rewrite the right-hand integral
  using `integral_add` and `integral_const_mul`.
Source: Mathlib measure theory Bochner integral monotonicity and linearity APIs
Used in: stochastic mirror descent integration of pointwise affine descent bounds
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem integral_le_integral_affine_combination
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω)
    (A B C : Ω → ℝ) (a b : ℝ)
    (hA : Integrable A μ)
    (hB : Integrable B μ)
    (hC : Integrable C μ)
    (hpoint : A ≤ fun ω => a * B ω + b * C ω) :
    ∫ ω, A ω ∂ μ ≤ a * (∫ ω, B ω ∂ μ) + b * (∫ ω, C ω ∂ μ) := by
  have hright : Integrable (fun ω => a * B ω + b * C ω) μ :=
    (hB.const_mul a).add (hC.const_mul b)
  have hle := MeasureTheory.integral_mono hA hright hpoint
  have hright_eq :
      (∫ ω, a * B ω + b * C ω ∂ μ) =
        a * (∫ ω, B ω ∂ μ) + b * (∫ ω, C ω ∂ μ) := by
    rw [integral_add (hB.const_mul a) (hC.const_mul b)]
    simp [integral_const_mul]
  rw [hright_eq] at hle
  exact hle

/-- Coordinate restriction along an embedding into a finite mapped block is measurable.

For a finite source block `I` and a target block `J` containing `I.map e`, the
map that restricts a dependent coordinate vector on `J` to the coordinates
indexed by `I` through `e` is measurable.

Layer: Glue | Gap: Level 1 (finite product coordinate restriction measurability)
Proof: use `measurable_pi_lambda`; each output coordinate is a measurable
  coordinate projection from the target finite product space.
Source: Mathlib finite product measurable-space and `Finset.map` APIs
Used in: nonconvex stochastic mirror descent validation samples independent of
  optimization-phase finite sample blocks
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
theorem measurable_pi_subtype_restrict_of_mem_map
    {A B S : Type*} [MeasurableSpace S]
    (e : A ↪ B) (I : Finset A) (J : Finset B)
    (hIJ : I.map e ≤ J) :
    Measurable (fun y : ({b // b ∈ J} → S) =>
      fun a : {a // a ∈ I} =>
        y ⟨e a.1, hIJ (Finset.mem_map.mpr ⟨a.1, a.2, rfl⟩)⟩) := by
  refine measurable_pi_lambda _ ?_
  intro a
  exact measurable_pi_apply
    (⟨e a.1, hIJ (Finset.mem_map.mpr ⟨a.1, a.2, rfl⟩)⟩ : {b // b ∈ J})

open scoped BigOperators

namespace PMF

/-- A finite PMF/product-measure fiber event expands as a weighted finite sum.

For a finite discrete law `p` on the first coordinate and an arbitrary measure
`μ` on the second coordinate, the product-measure mass of the event whose fiber
over `a` is `A a` is the finite sum of `p a * μ (A a)`.

Layer: Glue | Gap: Level 1 (finite PMF product-measure fiber expansion)
Proof: split the event into finitely many first-coordinate fibers and use
  `Measure.prod_prod` together with the singleton mass formula for `PMF.toMeasure`.
Source: Mathlib probability mass functions, product measures, and finite sums
  for discrete-continuous joint laws
Used in: nonconvex stochastic mirror descent stopping-index/sample product tail
  probability expansion
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
theorem toMeasure_prod_fiber_event_eq_sum
    {α Ω : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace Ω] (p : PMF α) (μ : Measure Ω) [SFinite μ]
    (A : α → Set Ω) :
    (p.toMeasure.prod μ) {q : α × Ω | q.2 ∈ A q.1} =
      ∑ a : α, p a * μ (A a) := by
  classical
  let B : Finset α → Set (α × Ω) :=
    fun s => {q | q.1 ∈ (s : Set α) ∧ q.2 ∈ A q.1}
  have hB_univ : B Finset.univ = {q : α × Ω | q.2 ∈ A q.1} := by
    ext q
    simp [B]
  have hB :
      ∀ s : Finset α,
        (p.toMeasure.prod μ) (B s) = ∑ a ∈ s, p a * μ (A a) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        simp [B]
    | insert a s ha ih =>
        let F : Set (α × Ω) := ({a} : Set α) ×ˢ (Set.univ : Set Ω)
        have hF_meas : NullMeasurableSet F (p.toMeasure.prod μ) := by
          have hF : MeasurableSet F := by
            exact (measurableSet_singleton a).prod MeasurableSet.univ
          exact hF.nullMeasurableSet
        have hsplit :=
          measure_inter_add_diff₀
            (μ := p.toMeasure.prod μ) (s := B (insert a s)) (t := F) hF_meas
        have h_inter : B (insert a s) ∩ F = ({a} : Set α) ×ˢ A a := by
          ext q
          by_cases hqa : q.1 = a
          · simp [B, F, hqa]
          · simp [B, F, hqa]
        have h_diff : B (insert a s) \ F = B s := by
          ext q
          by_cases hqa : q.1 = a
          · simp [B, F, hqa, ha]
          · simp [B, F, hqa]
        have hprod :
            (p.toMeasure.prod μ) (({a} : Set α) ×ˢ A a) = p a * μ (A a) := by
          rw [Measure.prod_prod]
          rw [PMF.toMeasure_apply_singleton p a (measurableSet_singleton a)]
        rw [← hsplit, h_inter, h_diff, hprod, ih]
        simp [Finset.sum_insert, ha]
  calc
    (p.toMeasure.prod μ) {q : α × Ω | q.2 ∈ A q.1}
        = (p.toMeasure.prod μ) (B Finset.univ) := by rw [hB_univ]
    _ = ∑ a : α, p a * μ (A a) := by
        simpa using hB Finset.univ

/-- A finite PMF/product-measure section event expands as a weighted finite sum.

For a finite discrete law `p` on the first coordinate and an arbitrary measure
`μ` on the second coordinate, the product-measure mass of the section event
whose fiber over `a` is `A a` is the finite sum of `p a * μ (A a)`.

Layer: Glue | Gap: Level 1 (finite PMF product-measure section expansion)
Proof: reuse the finite PMF product-fiber expansion, which decomposes the event
  into singleton first-coordinate sections and evaluates each rectangle by
  `Measure.prod_prod` and `PMF.toMeasure_apply_singleton`.
Source: Mathlib probability mass functions, product measures, and finite sums
  for discrete-continuous joint laws
Used in: nonconvex stochastic mirror descent stopping-vector/sample product tail
  probability expansion
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
theorem prod_section_measure_eq_sum
    {α Ω : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace Ω] (p : PMF α) (μ : Measure Ω) [SFinite μ]
    (A : α → Set Ω) :
    (p.toMeasure.prod μ) {q : α × Ω | q.2 ∈ A q.1} =
      ∑ a : α, p a * μ (A a) := by
  exact PMF.toMeasure_prod_fiber_event_eq_sum p μ A

/-- A finite PMF/product-measure section event expands as a weighted finite sum.

For a finite discrete law `p` on the first coordinate and an arbitrary measure
`μ` on the second coordinate, the product-measure mass of the event with fiber
`A a` over `a` is the finite sum of `p a * μ (A a)`.

Layer: Glue | Gap: Level 1 (finite PMF product-section measure expansion)
Proof: this is an alias of the staged finite PMF product-section expansion,
  which reduces the product event to singleton first-coordinate fibers.
Source: Mathlib probability mass functions, product measures, and finite sums
  for discrete-continuous joint laws
Used in: nonconvex stochastic mirror descent stopping-vector/sample product tail probability expansion
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, nonconvex stochastic mirror descent -/
theorem prod_section_measure_eq_sum_alias
    {α Ω : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace Ω] (p : PMF α) (μ : Measure Ω) [SFinite μ]
    (A : α → Set Ω) :
    (p.toMeasure.prod μ) {q : α × Ω | q.2 ∈ A q.1} =
      ∑ a : α, p a * μ (A a) := by
  exact PMF.prod_section_measure_eq_sum p μ A

/-- A finite PMF/product-measure fiber set expands as a weighted sigma sum.

For a finite discrete law `p` on the first coordinate and an arbitrary measure
`μ` on the second coordinate, the product-measure mass of the dependent fiber
set is the finite sum of the first-coordinate masses times the fiber measures.

Layer: Glue | Gap: Level 1 (finite PMF product-measure dependent fiber expansion)
Proof: exact reuse of the finite `PMF.toMeasure` product-fiber expansion, which decomposes the set into singleton first-coordinate fibers and applies `Measure.prod_prod`.
Source: Mathlib probability mass functions, product measures, and finite sums for discrete-continuous joint laws
Used in: nonconvex stochastic mirror descent stopping-vector/sample product tail probability expansion
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, nonconvex stochastic mirror descent -/
theorem prod_measure_set_sigma_eq_sum
    {α Ω : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace Ω] (p : PMF α) (μ : Measure Ω) [SFinite μ]
    (A : α → Set Ω) :
    (p.toMeasure.prod μ) {q : α × Ω | q.2 ∈ A q.1} =
      ∑ a : α, p a * μ (A a) := by
  exact PMF.toMeasure_prod_fiber_event_eq_sum p μ A

/-- A finite PMF/sample product observable is integrable when every sample fiber is integrable.

For a finite discrete law on the first coordinate and an arbitrary sample
measure on the second coordinate, product integrability reduces to fiber
integrability because the remaining outer norm integral is over a finite
measure on a finite measurable space.

Layer: Glue | Gap: Level 1 (finite PMF product integrability from fibers)
Proof: rewrite product integrability with `integrable_prod_iff`; the fiber
  condition supplies the inner integrability and `Integrable.of_finite`
  discharges the outer finite PMF integral.
Source: Mathlib product-measure integration, probability mass functions, and
  finite measurable-space integrability
Used in: nonconvex stochastic mirror descent randomized-output stationarity
  integrability over the stopping-index/sample product law
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
theorem integrable_prod_of_fiber_integrable
    {α Ω E : Type*} [Finite α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace Ω] [NormedAddCommGroup E] (p : PMF α) (μ : Measure Ω) [SFinite μ]
    (F : α → Ω → E)
    (hF_aestronglyMeasurable :
      AEStronglyMeasurable (fun q : α × Ω => F q.1 q.2) (p.toMeasure.prod μ))
    (hF_integrable : ∀ a, Integrable (F a) μ) :
    Integrable (fun q : α × Ω => F q.1 q.2) (p.toMeasure.prod μ) := by
  rw [MeasureTheory.integrable_prod_iff hF_aestronglyMeasurable]
  exact ⟨Filter.Eventually.of_forall hF_integrable, Integrable.of_finite⟩

end PMF

open MeasureTheory ProbabilityTheory

/-- Integrability descends from a pullback random variable to its pushforward law.

If `Y` pushes a base measure `P` forward to the sample law and `φ ∘ Y` is
integrable on the base space, then `φ` is integrable under the sample law,
provided `φ` is a.e. strongly measurable for that pushforward measure.

Layer: Glue | Gap: Level 0 (pushforward-law integrability transport)
Proof: apply the reverse implication of Mathlib's `integrable_map_measure`
  equivalence for a.e. measurable maps.
Source: Mathlib measure theory Bochner integrability and map-measure APIs
Used in: stochastic mirror descent fixed-query validation variance under a
  pushed-forward sample law
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic mirror descent -/
theorem integrable_map_measure_of_integrable_comp
    {Ω S E : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    [NormedAddCommGroup E]
    {P : Measure Ω} {Y : Ω → S} {φ : S → E}
    (hφ : AEStronglyMeasurable φ (Measure.map Y P))
    (hY : AEMeasurable Y P)
    (hbase : Integrable (φ ∘ Y) P) :
    Integrable φ (Measure.map Y P) := by
  exact (MeasureTheory.integrable_map_measure hφ hY).2 hbase

/-- The scalar inner product of two square-integrable vector processes is integrable.

If two random vectors have a.e. strongly measurable representatives and
integrable squared norms, then their pointwise real inner product is Bochner
integrable as a real-valued random variable.

Layer: Glue | Gap: Level 1 (inner-product integrability from L2 vector bounds)
Proof: convert the squared-norm hypotheses to `MemLp` at exponent two, apply
  Hölder to the product of the norms, and dominate the absolute inner product
  by Cauchy-Schwarz.
Source: Mathlib Lp-space, Bochner integrability, and inner-product norm APIs
Used in: stochastic mirror descent mini-batch residual covariance expansion
Book citation: book/FOML/StochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic mirror descent -/
theorem integrable_inner_of_integrable_sq_norm
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {P : Measure Ω} {u v : Ω → E}
    (hu_meas : AEStronglyMeasurable u P)
    (hv_meas : AEStronglyMeasurable v P)
    (hu_sq : Integrable (fun ω => ‖u ω‖ ^ 2) P)
    (hv_sq : Integrable (fun ω => ‖v ω‖ ^ 2) P) :
    Integrable (fun ω => ⟪u ω, v ω⟫_ℝ) P := by
  have hu_l2 : MemLp u 2 P :=
    (memLp_two_iff_integrable_sq_norm hu_meas).2 hu_sq
  have hv_l2 : MemLp v 2 P :=
    (memLp_two_iff_integrable_sq_norm hv_meas).2 hv_sq
  have hprod : Integrable (fun ω => ‖u ω‖ * ‖v ω‖) P := by
    simpa [Pi.mul_apply] using
      (MemLp.integrable_mul hu_l2.norm hv_l2.norm :
        Integrable ((fun ω => ‖u ω‖) * (fun ω => ‖v ω‖)) P)
  exact hprod.mono'
    (AEStronglyMeasurable.inner hu_meas hv_meas)
    (Filter.Eventually.of_forall fun ω => by
      simpa [Real.norm_eq_abs] using abs_real_inner_le_norm (u ω) (v ω))

/-- A past-measurable random variable paired with one current sample is independent of a distinct current sample.

If `X` is measurable with respect to a past sigma-algebra and the sigma-algebra
generated by that past together with `Yj` is independent of the sigma-algebra
generated by `Yi`, then the random pair `(X, Yj)` is independent of `Yi`.

Layer: Glue | Gap: Level 1 (past-current product independence bridge)
Proof: show `(X, Yj)` is measurable with respect to `past ⊔ comap Yj`, then
  transfer sigma-algebra independence to random-variable independence.
Source: Mathlib probability independence API for sub-sigma-algebras and product
  measurable spaces
Used in: nonconvex stochastic mirror descent off-diagonal mini-batch sample
  independence for an iterate paired with a peer current sample
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
theorem indepFun_prod_past_current_of_indep_current
    {Ω A B C : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C]
    {μ : Measure Ω} {past : MeasurableSpace Ω} {X : Ω → A} {Yj : Ω → B}
    {Yi : Ω → C}
    (hX_past : Measurable[past] X)
    (hpast_current_indep :
      Indep
        (past ⊔ MeasurableSpace.comap Yj (by infer_instance : MeasurableSpace B))
        (MeasurableSpace.comap Yi (by infer_instance : MeasurableSpace C))
        μ) :
    IndepFun (fun ω => (X ω, Yj ω)) Yi μ := by
  have hpair :
      Measurable[
        past ⊔ MeasurableSpace.comap Yj (by infer_instance : MeasurableSpace B)]
        (fun ω => (X ω, Yj ω)) := by
    have hX :
        Measurable[
          past ⊔ MeasurableSpace.comap Yj (by infer_instance : MeasurableSpace B)]
          X :=
      measurable_iff_comap_le.mpr <|
        le_trans hX_past.comap_le le_sup_left
    have hYj :
        Measurable[
          past ⊔ MeasurableSpace.comap Yj (by infer_instance : MeasurableSpace B)]
          Yj :=
      measurable_iff_comap_le.mpr le_sup_right
    exact hX.prodMk hYj
  rw [IndepFun_iff_Indep]
  exact indep_of_indep_of_le_left hpast_current_indep hpair.comap_le

/-- A nonnegative integrable real random variable has a non-strict Markov tail
bound at a positive threshold from an integral bound.

This packages the common passage from a real Bochner integral estimate to an
`ENNReal` measure estimate for `{ω | f ω ≥ t}`.

Layer: Glue | Gap: Level 1 (non-strict nonnegative Markov tail at positive threshold)
Proof: apply `meas_ge_le_lintegral_div` to `ENNReal.ofReal f`, rewrite the
  lintegral by `ofReal_integral_eq_lintegral_ofReal`, and compare the real
  ratio before coercing through `ENNReal.ofReal`.
Source: Mathlib measure-theory Markov inequality and Bochner integral APIs
Used in: nonconvex stochastic mirror descent exact-stationarity and
  validation-residual tail probability estimates
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/convergence_results
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
theorem measure_ge_le_of_integral_le_of_nonneg
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (f : Ω → ℝ) (t C b : ℝ)
    (hf_int : Integrable f μ) (hf_nonneg : ∀ ω, 0 ≤ f ω)
    (h_int_le : ∫ ω, f ω ∂μ ≤ C)
    (ht_pos : 0 < t)
    (hpos : C / t ≤ b) :
    μ {ω | f ω ≥ t} ≤ ENNReal.ofReal b := by
  have hf_ae : AEMeasurable (fun ω => ENNReal.ofReal (f ω)) μ := by
    simpa [Function.comp_def] using
      (ENNReal.measurable_ofReal.comp_aemeasurable
        hf_int.aestronglyMeasurable.aemeasurable)
  have hsubset :
      {ω | f ω ≥ t} ⊆ {ω | ENNReal.ofReal t ≤ ENNReal.ofReal (f ω)} := by
    intro ω hω
    exact ENNReal.ofReal_le_ofReal hω
  have hmarkov := MeasureTheory.meas_ge_le_lintegral_div (μ := μ) hf_ae
    (ε := ENNReal.ofReal t) (ne_of_gt (ENNReal.ofReal_pos.mpr ht_pos)) (by simp)
  have hlintegral :
      (∫⁻ a, ENNReal.ofReal (f a) ∂μ) = ENNReal.ofReal (∫ a, f a ∂μ) := by
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hf_int]
    exact ae_of_all _ hf_nonneg
  have hdiv_le :
      (∫⁻ a, ENNReal.ofReal (f a) ∂μ) / ENNReal.ofReal t ≤
        ENNReal.ofReal b := by
    rw [hlintegral]
    rw [← ENNReal.ofReal_div_of_pos ht_pos]
    exact ENNReal.ofReal_le_ofReal
      (le_trans (div_le_div_of_nonneg_right h_int_le (le_of_lt ht_pos)) hpos)
  exact le_trans (measure_mono hsubset) (le_trans hmarkov hdiv_le)

/-- A finite product stopping law turns all-coordinate non-strict tail mass into a product of one-coordinate tail masses.

If the stopping vector `q` has coordinatewise product masses from a one-step
PMF `p`, and each fixed-vector tail fiber factors into coordinate fibers
`B i (R i)`, then the joint PMF/sample probability of the all-coordinate event
is the product of the corresponding one-coordinate weighted probabilities.

Layer: Glue | Gap: Level 1 (finite product stopping-vector tail probability factorization)
Proof: expand the PMF/sample product measure into finite fibers, substitute the
  coordinate product law and fixed-vector fiber product law, and use
  `Finset.prod_univ_sum` to exchange the finite sum over functions with a
  product of finite sums.
Source: Mathlib probability mass functions, product measures, and finite
  big-operator APIs
Used in: nonconvex stochastic mirror descent all-runs optimization tail
  probability product law
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/convergence_results/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
theorem pi_stopping_tail_probability_eq_product_of_nonStrict
    {ι α Ω : Type*} [Fintype ι] [Fintype α]
    [MeasurableSpace (ι → α)] [MeasurableSingletonClass (ι → α)]
    [MeasurableSpace Ω]
    (p : PMF α) (q : PMF (ι → α)) (μ : Measure Ω) [SFinite μ]
    (Pall : ENNReal) (Pone : ι → ENNReal)
    (A : (ι → α) → Set Ω) (B : ι → α → Set Ω)
    (hPall : Pall = (q.toMeasure.prod μ) {x : (ι → α) × Ω | x.2 ∈ A x.1})
    (hq : ∀ R : ι → α, q R = ∏ i : ι, p (R i))
    (hfiber : ∀ R : ι → α, μ (A R) = ∏ i : ι, μ (B i (R i)))
    (hPone : ∀ i : ι, Pone i = ∑ a : α, p a * μ (B i a)) :
    Pall = ∏ i : ι, Pone i := by
  classical
  calc
    Pall = ∑ R : ι → α, q R * μ (A R) := by
      rw [hPall]
      exact PMF.prod_measure_set_sigma_eq_sum q μ A
    _ = ∑ R : ι → α,
          (∏ i : ι, p (R i)) * ∏ i : ι, μ (B i (R i)) := by
        refine Finset.sum_congr rfl ?_
        intro R _hR
        rw [hq R, hfiber R]
    _ = ∑ R : ι → α, ∏ i : ι, (p (R i) * μ (B i (R i))) := by
        refine Finset.sum_congr rfl ?_
        intro R _hR
        rw [Finset.prod_mul_distrib]
    _ = ∏ i : ι, ∑ a : α, p a * μ (B i a) := by
        simpa [Fintype.piFinset_univ] using
          (Finset.prod_univ_sum
            (fun _ : ι => (Finset.univ : Finset α))
            (fun i a => p a * μ (B i a))).symm
    _ = ∏ i : ι, Pone i := by
        refine Finset.prod_congr rfl ?_
        intro i _hi
        exact (hPone i).symm

/-- A finite product stopping law turns all-coordinate tail mass into a product of one-coordinate tail masses.

If the stopping vector `q` has coordinatewise product masses from a one-step
PMF `p`, and each fixed-vector tail fiber factors into coordinate fibers
`B i (R i)`, then the joint PMF/sample probability of the all-coordinate event
is the product of the corresponding one-coordinate weighted probabilities.

Layer: Glue | Gap: Level 1 (finite product stopping-vector tail probability factorization)
Proof: expand the PMF/sample product measure into finite fibers, substitute the
  coordinate product law and fixed-vector fiber product law, and use
  `Finset.prod_univ_sum` to exchange the finite sum over functions with a
  product of finite sums.
Source: Mathlib probability mass functions, product measures, and finite
  big-operator APIs
Used in: nonconvex stochastic mirror descent strict all-runs optimization tail
  probability product law
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/convergence_results/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
theorem pi_stopping_tail_probability_eq_product
    {ι α Ω : Type*} [Fintype ι] [Fintype α]
    [MeasurableSpace (ι → α)] [MeasurableSingletonClass (ι → α)]
    [MeasurableSpace Ω]
    (p : PMF α) (q : PMF (ι → α)) (μ : Measure Ω) [SFinite μ]
    (Pall : ENNReal) (Pone : ι → ENNReal)
    (A : (ι → α) → Set Ω) (B : ι → α → Set Ω)
    (hPall : Pall = (q.toMeasure.prod μ) {x : (ι → α) × Ω | x.2 ∈ A x.1})
    (hq : ∀ R : ι → α, q R = ∏ i : ι, p (R i))
    (hfiber : ∀ R : ι → α, μ (A R) = ∏ i : ι, μ (B i (R i)))
    (hPone : ∀ i : ι, Pone i = ∑ a : α, p a * μ (B i a)) :
    Pall = ∏ i : ι, Pone i := by
  exact pi_stopping_tail_probability_eq_product_of_nonStrict
    p q μ Pall Pone A B hPall hq hfiber hPone

namespace ProbabilityTheory

/-- Disjoint finite blocks of one independent family are independent as subtype-indexed vectors.

For an `iIndepFun` family, the random vector collecting the coordinates in a
finite block `I` is independent of the random vector collecting the coordinates
in any disjoint finite block `J`.

Layer: Glue | Gap: Level 1 (finite subtype-vector block independence)
Proof: apply Mathlib's finite-block independence theorem for `iIndepFun`
  directly to the two disjoint finsets.
Source: Mathlib probability independence API for independent random-variable
  families and finite product measurable spaces
Used in: nonconvex stochastic mirror descent independent optimization-run
  product law for Eq. (6.2.62)
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
theorem iIndepFun.indepFun_finset_subtype_blocks
    {ι Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (ξ : ι → Ω → S) (μ : Measure Ω)
    (I J : Finset ι)
    (hξ_meas : ∀ q, Measurable (ξ q))
    (hξ_iIndep : iIndepFun ξ μ)
    (hIJ : Disjoint I J) :
    IndepFun
      (fun ω => fun p : {p // p ∈ I} => ξ p.1 ω)
      (fun ω => fun q : {q // q ∈ J} => ξ q.1 ω)
      μ := by
  exact hξ_iIndep.indepFun_finset I J hIJ hξ_meas

/-- Disjoint finite blocks selected by opposite `Sum` tags are independent as sample vectors.

For an independent family indexed by `ι ⊕ κ`, the vector of coordinates over a
finite `inl` block is independent of the vector of coordinates over a finite
`inr` block.

Layer: Glue | Gap: Level 1 (finite block independence across tagged sample families)
Proof: map the two finite blocks into the sum index type, use finite-block
  independence for disjoint index sets, and compose with measurable coordinate
  projections back to the original block types.
Source: Mathlib probability independence API for independent random-variable families
  and finite product measurable spaces
Used in: nonconvex stochastic mirror descent validation samples independent of
  optimization-phase sample blocks
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
theorem iIndepFun.indepFun_finset_sum_inl_inr
    {ι κ Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (ξ : ι ⊕ κ → Ω → S) (μ : Measure Ω)
    (I : Finset ι) (J : Finset κ)
    (hξ_meas : ∀ q, Measurable (ξ q))
    (hξ_iIndep : iIndepFun ξ μ) :
    IndepFun
      (fun ω => fun p : {p // p ∈ I} => ξ (Sum.inl p.1) ω)
      (fun ω => fun q : {q // q ∈ J} => ξ (Sum.inr q.1) ω)
      μ := by
  classical
  let inlEmb : ι ↪ (ι ⊕ κ) :=
    ⟨Sum.inl, by
      intro a b h
      exact Sum.inl.inj h⟩
  let inrEmb : κ ↪ (ι ⊕ κ) :=
    ⟨Sum.inr, by
      intro a b h
      exact Sum.inr.inj h⟩
  let I' : Finset (ι ⊕ κ) := I.map inlEmb
  let J' : Finset (ι ⊕ κ) := J.map inrEmb
  have hdisj : Disjoint I' J' := by
    rw [Finset.disjoint_left]
    intro x hx hy
    rcases Finset.mem_map.mp hx with ⟨a, ha, rfl⟩
    rcases Finset.mem_map.mp hy with ⟨b, hb, h⟩
    cases h
  have hind :
      IndepFun
        (fun ω => fun q : {q // q ∈ I'} => ξ q.1 ω)
        (fun ω => fun q : {q // q ∈ J'} => ξ q.1 ω)
        μ :=
    hξ_iIndep.indepFun_finset I' J' hdisj hξ_meas
  let φ :
      ({q // q ∈ I'} → S) → ({p // p ∈ I} → S) :=
    fun y p =>
      y ⟨Sum.inl p.1, by
        exact Finset.mem_map.mpr ⟨p.1, p.2, rfl⟩⟩
  let ψ :
      ({q // q ∈ J'} → S) → ({p // p ∈ J} → S) :=
    fun y p =>
      y ⟨Sum.inr p.1, by
        exact Finset.mem_map.mpr ⟨p.1, p.2, rfl⟩⟩
  have hφ : Measurable φ := by
    refine measurable_pi_lambda _ ?_
    intro p
    exact measurable_pi_apply
      (⟨Sum.inl p.1, by
        exact Finset.mem_map.mpr ⟨p.1, p.2, rfl⟩⟩ : {q // q ∈ I'})
  have hψ : Measurable ψ := by
    refine measurable_pi_lambda _ ?_
    intro p
    exact measurable_pi_apply
      (⟨Sum.inr p.1, by
        exact Finset.mem_map.mpr ⟨p.1, p.2, rfl⟩⟩ : {q // q ∈ J'})
  simpa [φ, ψ, I', J', inlEmb, inrEmb, Function.comp_def] using
    hind.comp hφ hψ

end ProbabilityTheory

/-- A block-measurable random output is independent of a fresh sample.

If an output random variable is measurable with respect to a sub-sigma-algebra
`m`, and `m` is independent of the sigma-algebra generated by the sample `Y`,
then the output and sample are independent random variables.

Layer: Glue | Gap: Level 0 (block-measurable output independence transfer)
Proof: rewrite random-variable independence as independence of generated
  sigma-algebras and shrink the left sigma-algebra using block measurability.
Source: Mathlib probability independence APIs for sub-sigma-algebras and random
  variables
Used in: nonconvex stochastic mirror descent randomized optimization output
  independence from fresh validation samples
Book citation: book/PAPER/ALG.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, randomized stochastic mirror descent -/
theorem indepFun_of_block_measurable_and_fresh_sample
    {Ω X S : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace S]
    (P : Measure Ω) (m : MeasurableSpace Ω) (Xout : Ω → X) (Y : Ω → S)
    (hXout : Measurable[m] Xout)
    (hblock_indep_sample :
      Indep m (MeasurableSpace.comap Y (by infer_instance : MeasurableSpace S)) P) :
    IndepFun Xout Y P := by
  rw [IndepFun_iff_Indep]
  exact indep_of_indep_of_le_left hblock_indep_sample hXout.comap_le

/-- Vector-valued block independence descends to smaller generated sigma-algebras.

If two vector-valued random variables are independent through their comap
sigma-algebras, then any left and right sigma-algebras bounded by those comaps
are independent as well.

Layer: Glue | Gap: Level 0 (sub-sigma-algebra independence shrink)
Proof: apply Mathlib monotonicity of `Indep` on the left and then on the right
  using the supplied `≤` bounds into the vector comap sigma-algebras.
Source: Mathlib probability independence API for sub-sigma-algebras and
  measure-theory comap sigma-algebras
Used in: nonconvex stochastic mirror descent validation-sample block freshness
  after shrinking finite tagged sample vectors to generated coordinate
  sigma-algebras
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
theorem indep_of_vector_block_indep_of_le_comap
    {Ω A B S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) (X : Ω → A → S) (Y : Ω → B → S)
    (mX mY : MeasurableSpace Ω)
    (hvec :
      Indep
        (MeasurableSpace.comap X
          (by infer_instance : MeasurableSpace (A → S)))
        (MeasurableSpace.comap Y
          (by infer_instance : MeasurableSpace (B → S)))
        P)
    (hleft :
      mX ≤
        MeasurableSpace.comap X
          (by infer_instance : MeasurableSpace (A → S)))
    (hright :
      mY ≤
        MeasurableSpace.comap Y
          (by infer_instance : MeasurableSpace (B → S))) :
    Indep mX mY P := by
  exact indep_of_indep_of_le_right
    (indep_of_indep_of_le_left hvec hleft) hright

/-- A finite sample-block sigma-algebra is independent of a fresh singleton sample coordinate.

If the vector of all coordinates in a finite block is independent of the vector
consisting of one fresh coordinate, then the sigma-algebra generated by the
finite block is independent of the singleton coordinate's generated
sigma-algebra.

Layer: Glue | Gap: Level 1 (finite block to singleton sigma-algebra independence)
Proof: rewrite vector independence as independence of comap sigma-algebras, then
  shrink both sides using coordinate projections from the finite pi vectors.
Source: Mathlib probability independence API for random variables and
  measure-theory comap sigma-algebras
Used in: nonconvex stochastic mirror descent validation freshness for a
  randomized output measurable from the optimization sample footprint
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
theorem indep_sampleBlock_singleton_of_disjoint_indices
    {Ω S I J : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (μ : Measure Ω) (ξI : I → Ω → S) (ξJ : J → Ω → S)
    (A : Finset I) (j : J)
    (h_indep :
      IndepFun
        (fun ω => fun p : {p // p ∈ A} => ξI p.1 ω)
        (fun ω => fun q : {q // q ∈ ({j} : Finset J)} => ξJ q.1 ω)
        μ) :
    Indep
      (⨆ q : {q // q ∈ A},
        MeasurableSpace.comap (fun ω => ξI q.1 ω)
          (by infer_instance : MeasurableSpace S))
      (MeasurableSpace.comap (ξJ j) (by infer_instance : MeasurableSpace S)) μ := by
  classical
  let B : Finset J := {j}
  let X : Ω → ({p // p ∈ A} → S) := fun ω p => ξI p.1 ω
  let Y : Ω → ({q // q ∈ B} → S) := fun ω q => ξJ q.1 ω
  have hvec :
      Indep
        (MeasurableSpace.comap X
          (by infer_instance : MeasurableSpace ({p // p ∈ A} → S)))
        (MeasurableSpace.comap Y
          (by infer_instance : MeasurableSpace ({q // q ∈ B} → S)))
        μ := by
    rw [← IndepFun_iff_Indep]
    simpa [X, Y, B] using h_indep
  have hleft :
      (⨆ q : {q // q ∈ A},
        MeasurableSpace.comap (fun ω => ξI q.1 ω)
          (by infer_instance : MeasurableSpace S)) ≤
        MeasurableSpace.comap X
          (by infer_instance : MeasurableSpace ({p // p ∈ A} → S)) := by
    have hX_comap :
        Measurable[MeasurableSpace.comap X
          (by infer_instance : MeasurableSpace ({p // p ∈ A} → S))] X := by
      exact measurable_iff_comap_le.mpr le_rfl
    refine iSup_le ?_
    intro q
    exact ((measurable_pi_apply q).comp hX_comap).comap_le
  have hright :
      MeasurableSpace.comap (ξJ j) (by infer_instance : MeasurableSpace S) ≤
        MeasurableSpace.comap Y
          (by infer_instance : MeasurableSpace ({q // q ∈ B} → S)) := by
    let q0 : {q // q ∈ B} := ⟨j, by simp [B]⟩
    have hY_comap :
        Measurable[MeasurableSpace.comap Y
          (by infer_instance : MeasurableSpace ({q // q ∈ B} → S))] Y := by
      exact measurable_iff_comap_le.mpr le_rfl
    have hq :
        Measurable[MeasurableSpace.comap Y
          (by infer_instance : MeasurableSpace ({q // q ∈ B} → S))]
          (fun ω => Y ω q0) :=
      (measurable_pi_apply q0).comp hY_comap
    simpa [Y, q0, B] using hq.comap_le
  exact indep_of_indep_of_le_right
    (indep_of_indep_of_le_left hvec hleft) hright

/-- A nonnegative integrable real random variable has a strict Markov tail bound from
an integral bound, including a safe zero-threshold branch.

When the threshold is positive, this is Markov's inequality for
`ENNReal.ofReal ∘ f`.  When the threshold is zero, the supplied zero-threshold
side condition forces the integral to vanish, so nonnegativity makes the strict
positive tail null.

Layer: Glue | Gap: Level 1 (strict nonnegative Markov tail with zero threshold)
Proof: apply `meas_ge_le_lintegral_div` to `ENNReal.ofReal f` for positive
  thresholds, then use `integral_eq_zero_iff_of_nonneg` for the zero-threshold
  case.
Source: Mathlib measure-theory Markov inequality and Bochner integral APIs
Used in: nonconvex stochastic mirror descent strict exact-stationarity and
  validation-residual tail probability estimates
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec/convergence_results
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
theorem measure_gt_le_of_integral_le_of_nonneg
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (f : Ω → ℝ) (t C b : ℝ)
    (hf_int : Integrable f μ) (hf_nonneg : ∀ ω, 0 ≤ f ω)
    (h_int_le : ∫ ω, f ω ∂μ ≤ C)
    (ht_nonneg : 0 ≤ t)
    (hpos : 0 < t → C / t ≤ b)
    (hzero : t = 0 → C ≤ 0) :
    μ {ω | f ω > t} ≤ ENNReal.ofReal b := by
  by_cases htpos : 0 < t
  · have hf_ae : AEMeasurable (fun ω => ENNReal.ofReal (f ω)) μ := by
      simpa [Function.comp_def] using
        (ENNReal.measurable_ofReal.comp_aemeasurable
          hf_int.aestronglyMeasurable.aemeasurable)
    have hsubset :
        {ω | f ω > t} ⊆ {ω | ENNReal.ofReal t ≤ ENNReal.ofReal (f ω)} := by
      intro ω hω
      exact ENNReal.ofReal_le_ofReal (le_of_lt hω)
    have hmarkov := MeasureTheory.meas_ge_le_lintegral_div (μ := μ) hf_ae
      (ε := ENNReal.ofReal t) (ne_of_gt (ENNReal.ofReal_pos.mpr htpos)) (by simp)
    have hlintegral :
        (∫⁻ a, ENNReal.ofReal (f a) ∂μ) = ENNReal.ofReal (∫ a, f a ∂μ) := by
      rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hf_int]
      exact ae_of_all _ hf_nonneg
    have hdiv_le :
        (∫⁻ a, ENNReal.ofReal (f a) ∂μ) / ENNReal.ofReal t ≤
          ENNReal.ofReal b := by
      rw [hlintegral]
      rw [← ENNReal.ofReal_div_of_pos htpos]
      exact ENNReal.ofReal_le_ofReal
        (le_trans (div_le_div_of_nonneg_right h_int_le (le_of_lt htpos))
          (hpos htpos))
    exact le_trans (measure_mono hsubset) (le_trans hmarkov hdiv_le)
  · have htzero : t = 0 := le_antisymm (le_of_not_gt htpos) ht_nonneg
    have hint_nonneg : 0 ≤ ∫ ω, f ω ∂μ := integral_nonneg hf_nonneg
    have hint_zero : ∫ ω, f ω ∂μ = 0 := by
      have hCle : C ≤ 0 := hzero htzero
      linarith
    have hae_zero : f =ᶠ[ae μ] 0 :=
      (MeasureTheory.integral_eq_zero_iff_of_nonneg (μ := μ) hf_nonneg hf_int).mp
        hint_zero
    have hevent_zero : μ {ω | f ω > t} = 0 := by
      rw [htzero]
      have hnot : ∀ᵐ ω ∂μ, ¬ f ω > 0 := by
        filter_upwards [hae_zero] with ω hω
        rw [hω]
        exact not_lt.mpr le_rfl
      simpa [not_not] using
        ((MeasureTheory.ae_iff (μ := μ) (p := fun ω => ¬ f ω > 0)).mp hnot)
    rw [hevent_zero]
    exact zero_le _

/-- A finite past sample block joined with one coordinate is independent of a disjoint coordinate.

For an independent sample family, if the finite block `pastBlock ∪ {j}` is
disjoint from the singleton `{i}`, then the sigma-algebra generated by
`pastBlock` together with coordinate `j` is independent of coordinate `i`.

Layer: Glue | Gap: Level 1 (finite block plus coordinate independence)
Proof: apply finite-block independence for disjoint index sets to the vector of
  coordinates in `pastBlock ∪ {j}` and `{i}`, then shrink both comap
  sigma-algebras using coordinate projections.
Source: Mathlib probability independence API for independent families and
  measure-theory comap sigma-algebras
Used in: nonconvex stochastic mirror descent off-diagonal mini-batch sample
  independence from the strict optimization sample past plus a peer sample
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
theorem indep_strictPast_sup_coordinate_of_disjoint_current
    {Ω Ξ β : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] [DecidableEq β]
    (ξ : β → Ω → Ξ) (pastBlock : Finset β) (j i : β) (μ : Measure Ω)
    (hξ_meas : ∀ q, Measurable (ξ q))
    (hξ_iIndep : iIndepFun ξ μ)
    (hdisj : Disjoint (pastBlock ∪ ({j} : Finset β)) ({i} : Finset β)) :
    Indep
      ((⨆ q : {q // q ∈ pastBlock},
          MeasurableSpace.comap (fun ω => ξ q.1 ω)
            (by infer_instance : MeasurableSpace Ξ)) ⊔
        MeasurableSpace.comap (ξ j) (by infer_instance : MeasurableSpace Ξ))
      (MeasurableSpace.comap (ξ i) (by infer_instance : MeasurableSpace Ξ))
      μ := by
  classical
  let leftBlock : Finset β := pastBlock ∪ ({j} : Finset β)
  let rightBlock : Finset β := {i}
  let Zleft : Ω → ({q // q ∈ leftBlock} → Ξ) := fun ω q => ξ q.1 ω
  let Zright : Ω → ({q // q ∈ rightBlock} → Ξ) := fun ω q => ξ q.1 ω
  have hvec :
      Indep
        (MeasurableSpace.comap Zleft
          (by infer_instance : MeasurableSpace ({q // q ∈ leftBlock} → Ξ)))
        (MeasurableSpace.comap Zright
          (by infer_instance : MeasurableSpace ({q // q ∈ rightBlock} → Ξ)))
        μ := by
    rw [← IndepFun_iff_Indep]
    simpa [Zleft, Zright, leftBlock, rightBlock] using
      hξ_iIndep.indepFun_finset leftBlock rightBlock hdisj hξ_meas
  have hZleft_comap :
      Measurable[MeasurableSpace.comap Zleft
        (by infer_instance : MeasurableSpace ({q // q ∈ leftBlock} → Ξ))] Zleft := by
    exact measurable_iff_comap_le.mpr le_rfl
  have hpast_le :
      (⨆ q : {q // q ∈ pastBlock},
          MeasurableSpace.comap (fun ω => ξ q.1 ω)
            (by infer_instance : MeasurableSpace Ξ)) ≤
        MeasurableSpace.comap Zleft
          (by infer_instance : MeasurableSpace ({q // q ∈ leftBlock} → Ξ)) := by
    refine iSup_le ?_
    intro q
    have hq_left : q.1 ∈ leftBlock := by
      exact Finset.mem_union_left _ q.2
    have hcoord :
        Measurable[MeasurableSpace.comap Zleft
          (by infer_instance : MeasurableSpace ({q // q ∈ leftBlock} → Ξ))]
          (fun ω => ξ q.1 ω) := by
      have h :=
        (measurable_pi_apply (⟨q.1, hq_left⟩ : {q // q ∈ leftBlock})).comp
          hZleft_comap
      simpa [Zleft] using h
    exact hcoord.comap_le
  have hYj_le :
      MeasurableSpace.comap (ξ j) (by infer_instance : MeasurableSpace Ξ) ≤
        MeasurableSpace.comap Zleft
          (by infer_instance : MeasurableSpace ({q // q ∈ leftBlock} → Ξ)) := by
    have hqj : j ∈ leftBlock := by
      exact Finset.mem_union_right _ (by simp)
    have hcoord :
        Measurable[MeasurableSpace.comap Zleft
          (by infer_instance : MeasurableSpace ({q // q ∈ leftBlock} → Ξ))]
          (ξ j) := by
      have h :=
        (measurable_pi_apply (⟨j, hqj⟩ : {q // q ∈ leftBlock})).comp
          hZleft_comap
      simpa [Zleft] using h
    exact hcoord.comap_le
  have hpastYj_le :
      (⨆ q : {q // q ∈ pastBlock},
          MeasurableSpace.comap (fun ω => ξ q.1 ω)
            (by infer_instance : MeasurableSpace Ξ)) ⊔
          MeasurableSpace.comap (ξ j) (by infer_instance : MeasurableSpace Ξ) ≤
        MeasurableSpace.comap Zleft
          (by infer_instance : MeasurableSpace ({q // q ∈ leftBlock} → Ξ)) := by
    exact sup_le hpast_le hYj_le
  have hZright_comap :
      Measurable[MeasurableSpace.comap Zright
        (by infer_instance : MeasurableSpace ({q // q ∈ rightBlock} → Ξ))] Zright := by
    exact measurable_iff_comap_le.mpr le_rfl
  have hYi_le :
      MeasurableSpace.comap (ξ i) (by infer_instance : MeasurableSpace Ξ) ≤
        MeasurableSpace.comap Zright
          (by infer_instance : MeasurableSpace ({q // q ∈ rightBlock} → Ξ)) := by
    have hqi : i ∈ rightBlock := by
      simp [rightBlock]
    have hcoord :
        Measurable[MeasurableSpace.comap Zright
          (by infer_instance : MeasurableSpace ({q // q ∈ rightBlock} → Ξ))]
          (ξ i) := by
      have h :=
        (measurable_pi_apply (⟨i, hqi⟩ : {q // q ∈ rightBlock})).comp
          hZright_comap
      simpa [Zright] using h
    exact hcoord.comap_le
  exact
    indep_of_indep_of_le_right
      (indep_of_indep_of_le_left hvec hpastYj_le) hYi_le

/-- A measurable sampled value minus a continuous target evaluated at a measurable query is measurable.

This packages the common residual measurability pattern `ω ↦ sampled ω - target (query ω)`,
where the deterministic target field is continuous and the random query is measurable.

Layer: Glue | Gap: Level 0 (composed continuous target residual measurability)
Proof: convert continuity of the target to measurability, compose it with the
  measurable query, and apply Mathlib's measurable subtraction API.
Source: Mathlib measure-theory APIs for continuous functions, composition, and subtraction
Used in: nonconvex stochastic mirror descent validation residual at a randomized output
Book citation: book/FOML/NonconvexStochasticMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex stochastic mirror descent -/
theorem measurable_sub_comp_continuous_of_measurable
    {Ω X E : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [TopologicalSpace X]
    [MeasurableSpace E] [TopologicalSpace E] [BorelSpace X] [BorelSpace E]
    [OpensMeasurableSpace E] [Sub E] [MeasurableSub₂ E]
    {sampled : Ω → E} {query : Ω → X} {target : X → E}
    (hsampled : Measurable sampled) (hquery : Measurable query)
    (htarget : Continuous target) :
    Measurable (fun ω => sampled ω - target (query ω)) := by
  exact hsampled.sub (htarget.measurable.comp hquery)

namespace AEStronglyMeasurable

/-- A nonnegative real random variable is a.e. strongly measurable if its square
is integrable.

This is useful when second-moment assumptions are stated directly on a
nonnegative scalar majorant: the square is already strongly measurable by
integrability, and the original variable is recovered as the square root of its
square.

Layer: Glue | Gap: Level 1 (measurability from nonnegative square integrability)
Proof: compose the a.e. strong measurability of `Z^2` with continuity of
  `Real.sqrt`, then use `sqrt (Z^2) = Z` from a.e. nonnegativity.
Source: Mathlib measure theory strongly measurable functions and real square-root API
Used in: stochastic mirror descent scalar second-moment majorant measurability
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem of_integrable_sq_of_nonneg
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {Z : Ω → ℝ}
    (hZ2 : Integrable (fun ω => Z ω ^ 2) μ) (hZ_nonneg : ∀ᵐ ω ∂μ, 0 ≤ Z ω) :
    AEStronglyMeasurable Z μ := by
  have hsqrt :
      AEStronglyMeasurable (fun ω => Real.sqrt (Z ω ^ 2)) μ :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hZ2.aestronglyMeasurable
  refine hsqrt.congr ?_
  filter_upwards [hZ_nonneg] with ω hω
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hω]

end AEStronglyMeasurable

/-- A nonnegative square-integrable scalar has an `L¹` bound by its second moment plus one.

On a probability space, if `Z^2` is integrable and has integral at most `C`,
then a.e. nonnegativity of `Z` is enough to make `Z` integrable and to bound
`∫ Z` by `C + 1`.

Layer: Glue | Gap: Level 1 (nonnegative scalar L2-to-L1 expectation bound)
Proof: recover a.e. strong measurability of `Z` from square integrability and
  nonnegativity, apply the finite-measure L2-to-L1 integrability bridge, then
  integrate the pointwise inequality `z ≤ z^2 + 1`.
Source: Mathlib measure theory Bochner integrability and integral monotonicity APIs
Used in: stochastic block mirror descent fixed-fiber block dual-norm L1 control
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem integrable_of_nonneg_sq_integrable_integral_le_sq_bound_add_one
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Z : Ω → ℝ} {C : ℝ}
    (hZ_sq_int : Integrable (fun ω => Z ω ^ 2) μ)
    (hZ_nonneg : ∀ᵐ ω ∂μ, 0 ≤ Z ω)
    (hZ_sq_integral_le : ∫ ω, Z ω ^ 2 ∂μ ≤ C) :
    Integrable Z μ ∧ ∫ ω, Z ω ∂μ ≤ C + 1 := by
  have hZ_meas : AEStronglyMeasurable Z μ :=
    AEStronglyMeasurable.of_integrable_sq_of_nonneg hZ_sq_int hZ_nonneg
  have hZ_norm_sq : Integrable (fun ω => ‖Z ω‖ ^ 2) μ := by
    simpa [Real.norm_eq_abs, sq_abs] using hZ_sq_int
  have hZ_int : Integrable Z μ :=
    integrable_of_integrable_norm_sq hZ_meas hZ_norm_sq
  have hupper_int : Integrable (fun ω => Z ω ^ 2 + (1 : ℝ)) μ :=
    hZ_sq_int.add (integrable_const (c := (1 : ℝ)))
  have hmono : Z ≤ fun ω => Z ω ^ 2 + (1 : ℝ) := by
    intro ω
    nlinarith [sq_nonneg (Z ω)]
  have hint_le :
      ∫ ω, Z ω ∂μ ≤ ∫ ω, Z ω ^ 2 + (1 : ℝ) ∂μ :=
    integral_mono hZ_int hupper_int hmono
  refine ⟨hZ_int, ?_⟩
  calc
    ∫ ω, Z ω ∂μ ≤ ∫ ω, Z ω ^ 2 + (1 : ℝ) ∂μ := hint_le
    _ = (∫ ω, Z ω ^ 2 ∂μ) + 1 := by
          simp [integral_add hZ_sq_int (integrable_const (c := (1 : ℝ)))]
    _ ≤ C + 1 := by
          nlinarith

/-- Singleton fibers have the atom mass of any named law equal to the pushforward.

If a random variable `Y` pushes `P` forward to a law `mu`, then the source mass
of the fiber over a point `a` equals the singleton mass of `a` under `mu`.

Layer: Glue | Gap: Level 0 (pushforward-law singleton fiber mass)
Proof: specialize Mathlib's pushforward-set mass formula to measurable
  singletons, then rewrite the mapped measure by the supplied law equality.
Source: Mathlib measure theory map-measure API and measurable singleton classes
Used in: stochastic block mirror descent selected-block probability reduction to
  the named finite block law
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem measure_preimage_singleton_eq_of_map_eq
    {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSingletonClass A]
    {P : Measure Ω} {Y : Ω → A} {mu : Measure A} (a : A)
    (hY : AEMeasurable Y P) (hmap : Measure.map Y P = mu) :
    P (Y ⁻¹' ({a} : Set A)) = mu ({a} : Set A) := by
  rw [← hmap]
  rw [Measure.map_apply_of_aemeasurable hY (measurableSet_singleton a)]

/-- A pair-valued random variable with product probability law has independent components.

If the pushforward law of `Z : Ω → A × B` is the product `mu.prod nu` of two
probability laws, then the first and second projections of `Z` are independent
random variables under the source measure.

Layer: Glue | Gap: Level 1 (product joint law to component independence)
Proof: identify the projection pushforward laws from the product measure
  marginals, transfer sigma-finiteness across these law equalities, and apply
  Mathlib's product-law characterization of `IndepFun`.
Source: Mathlib probability independence API and product-measure marginal laws
Used in: stochastic block mirror descent same-time oracle draw/block-index independence
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/main_theorem/proof/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem indepFun_of_map_prod_eq_prod_laws
    {Ω A B : Type*} [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
    {P : Measure Ω} {Z : Ω → A × B} {mu : Measure A} {nu : Measure B}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hZ : AEMeasurable Z P) (hZ_law : Measure.map Z P = mu.prod nu) :
    IndepFun (fun ω => (Z ω).1) (fun ω => (Z ω).2) P := by
  have hfst_ae : AEMeasurable (fun ω => (Z ω).1) P :=
    hZ.fst
  have hsnd_ae : AEMeasurable (fun ω => (Z ω).2) P :=
    hZ.snd
  have hfst_law : Measure.map (fun ω => (Z ω).1) P = mu := by
    calc
      Measure.map (fun ω => (Z ω).1) P = Measure.map Prod.fst (Measure.map Z P) :=
        (AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable hZ).symm
      _ = Measure.map Prod.fst (mu.prod nu) := by rw [hZ_law]
      _ = mu := by simp
  have hsnd_law : Measure.map (fun ω => (Z ω).2) P = nu := by
    calc
      Measure.map (fun ω => (Z ω).2) P = Measure.map Prod.snd (Measure.map Z P) :=
        (AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable hZ).symm
      _ = Measure.map Prod.snd (mu.prod nu) := by rw [hZ_law]
      _ = nu := by simp
  haveI : SigmaFinite (Measure.map (fun ω => (Z ω).1) P) := by
    rw [hfst_law]
    infer_instance
  haveI : SigmaFinite (Measure.map (fun ω => (Z ω).2) P) := by
    rw [hsnd_law]
    infer_instance
  rw [indepFun_iff_map_prod_eq_prod_map_map' hfst_ae hsnd_ae
    (by infer_instance) (by infer_instance)]
  calc
    Measure.map (fun ω => ((Z ω).1, (Z ω).2)) P = Measure.map Z P := by rfl
    _ = mu.prod nu := hZ_law
    _ = (Measure.map (fun ω => (Z ω).1) P).prod
          (Measure.map (fun ω => (Z ω).2) P) := by
      rw [hfst_law, hsnd_law]

/-- A real-valued product integral over a finite selected index expands as a weighted
sum of fiber integrals.

For an arbitrary sample measure `μ`, finite index measure `ν`, real weights `p`,
and integrable fibers `F i`, integrating the selected fiber `F q.2 q.1` over
`μ.prod ν` is the sum of the singleton real masses of `ν` times the sample
fiber integrals.

Layer: Glue | Gap: Level 1 (finite-index product-law integral expansion)
Proof: decompose the selected integrand as a finite sum of singleton-index
  indicators to prove product integrability, apply Fubini, expand the finite
  index integral by singleton real masses, and commute the sample integral
  through the finite sum.
Source: Mathlib product-measure Bochner integration and finite-type integral APIs
Used in: stochastic block mirror descent selected-block second-moment expansion
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem integral_selected_finite_index_prod_eq_sum_weights
    {S ι : Type*} [MeasurableSpace S] [MeasurableSpace ι]
    [Fintype ι] [MeasurableSingletonClass ι]
    (μ : Measure S) (ν : Measure ι) [SFinite μ] [IsFiniteMeasure ν]
    (p : ι → ℝ) (F : ι → S → ℝ)
    (hν_singleton : ∀ i, ν.real ({i} : Set ι) = p i)
    (hF_int : ∀ i, Integrable (F i) μ) :
    ∫ q : S × ι, F q.2 q.1 ∂(μ.prod ν) =
      Finset.sum Finset.univ (fun i => p i * ∫ s, F i s ∂μ) := by
  classical
  let Fpair : S × ι → ℝ := fun q => F q.2 q.1
  have hFpair_int : Integrable Fpair (μ.prod ν) := by
    let G : ι → S × ι → ℝ := fun i q =>
      ({r : S × ι | r.2 = i}.indicator (fun q => F i q.1) q)
    have hG_int : ∀ i ∈ Finset.univ, Integrable (G i) (μ.prod ν) := by
      intro i _hi
      have hbaseProd : Integrable (fun q : S × ι => F i q.1) (μ.prod ν) :=
        (hF_int i).comp_fst ν
      have hset : MeasurableSet ({r : S × ι | r.2 = i} : Set (S × ι)) :=
        measurable_snd (measurableSet_singleton i)
      exact hbaseProd.indicator hset
    have hsum : Integrable (fun q => Finset.sum Finset.univ (fun i => G i q))
        (μ.prod ν) :=
      MeasureTheory.integrable_finset_sum (s := Finset.univ) (μ := μ.prod ν) hG_int
    refine hsum.congr ?_
    filter_upwards with q
    dsimp [Fpair, G]
    symm
    rw [Finset.sum_eq_single q.2]
    · simp
    · intro j _hj hqj
      have hne : q.2 ≠ j := fun h => hqj h.symm
      simp [hne]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ q.2))
  calc
    ∫ q : S × ι, F q.2 q.1 ∂(μ.prod ν)
        = ∫ s : S, ∫ i : ι, F i s ∂ν ∂μ := by
            simpa [Fpair] using
              (MeasureTheory.integral_prod (fun q : S × ι => Fpair q) hFpair_int)
    _ = ∫ s : S, Finset.sum Finset.univ (fun i => p i * F i s) ∂μ := by
            apply integral_congr_ae
            filter_upwards with s
            rw [MeasureTheory.integral_fintype (μ := ν)]
            · apply Finset.sum_congr rfl
              intro i _hi
              rw [hν_singleton i]
              rfl
            · exact Integrable.of_finite
    _ = Finset.sum Finset.univ (fun i => ∫ s : S, p i * F i s ∂μ) := by
            rw [integral_finset_sum]
            intro i _hi
            exact (hF_int i).const_mul (p i)
    _ = Finset.sum Finset.univ (fun i => p i * ∫ s, F i s ∂μ) := by
            apply Finset.sum_congr rfl
            intro i _hi
            rw [integral_const_mul]

/-- A finite sum of scalar multiples depending only on the first coordinate of a
product probability measure integrates as the sum of its first-coordinate
integrals.

For a sample measure `μ`, probability auxiliary measure `ν`, scalar weights
`c`, and integrable real normed vector-space fibers `F i`, the auxiliary
coordinate contributes total mass one, so integration over `μ.prod ν` reduces
to the usual finite sum of sample integrals.

Layer: Glue | Gap: Level 1 (first-coordinate product-law finite-sum expansion)
Proof: commute the finite sum through the Bochner integral, reduce each
  product integral with `MeasureTheory.integral_fun_fst`, then pull out each
  deterministic scalar by `integral_const_mul`.
Source: Mathlib product-measure Bochner integration and finite-sum linearity APIs
Used in: stochastic block mirror descent all-block second-moment expansion
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem integral_fst_finset_sum_smul_eq_sum_smul_integrals
    {S ι E : Type*} [MeasurableSpace S] [MeasurableSpace ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure S) (ν : Measure ι) [SFinite μ] [IsProbabilityMeasure ν]
    (s : Finset ι) (c : ι → ℝ) (F : ι → S → E)
    (hF_int : ∀ i ∈ s, Integrable (F i) μ) :
    ∫ q : S × ι, Finset.sum s (fun i => c i • F i q.1) ∂(μ.prod ν) =
      Finset.sum s (fun i => c i • ∫ x : S, F i x ∂μ) := by
  classical
  have hterms :
      ∀ i ∈ s, Integrable (fun q : S × ι => c i • F i q.1) (μ.prod ν) := by
    intro i hi
    have hbase : Integrable (fun x : S => c i • F i x) μ := by
      simpa [Pi.smul_apply] using (hF_int i hi).smul (c i)
    simpa using hbase.comp_fst ν
  calc
    ∫ q : S × ι, Finset.sum s (fun i => c i • F i q.1) ∂(μ.prod ν)
        = Finset.sum s (fun i =>
            ∫ q : S × ι, c i • F i q.1 ∂(μ.prod ν)) := by
            rw [integral_finset_sum]
            exact hterms
    _ = Finset.sum s (fun i => ∫ x : S, c i • F i x ∂μ) := by
            apply Finset.sum_congr rfl
            intro i _hi
            rw [MeasureTheory.integral_fun_fst (μ := μ) (ν := ν)
              (f := fun x : S => c i • F i x)]
            simp
    _ = Finset.sum s (fun i => c i • ∫ x : S, F i x ∂μ) := by
            apply Finset.sum_congr rfl
            intro i _hi
            rw [integral_smul]

/-- Transport an integral of a composed random variable across a named pushforward law.

If `Y` has pushforward law `nu` under `P`, then integrating `phi ∘ Y` over the
base space is the same as integrating `phi` over `nu`, assuming precisely the
a.e. measurability needed by the Bochner integral map theorem.

Layer: Glue | Gap: Level 0 (pushforward-law Bochner integral transport)
Proof: first apply Mathlib's `integral_map` to rewrite the base integral as an
  integral over `Measure.map Y P`, then rewrite that mapped measure by the
  supplied law equality.
Source: Mathlib measure theory Bochner integral map API
Used in: stochastic block mirror descent objective and oracle sample-law
  transport from generated streams to named one-step laws
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem integral_comp_eq_integral_of_map_eq
    {Omega S E : Type*} [MeasurableSpace Omega] [MeasurableSpace S]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Measure Omega} {Y : Omega -> S} {nu : Measure S} {phi : S -> E}
    (hY : AEMeasurable Y P)
    (hphi : AEStronglyMeasurable phi (Measure.map Y P))
    (hmap : Measure.map Y P = nu) :
    (∫ omega, phi (Y omega) ∂P) = ∫ s, phi s ∂nu := by
  calc
    (∫ omega, phi (Y omega) ∂P) = ∫ s, phi s ∂Measure.map Y P :=
      (MeasureTheory.integral_map hY hphi).symm
    _ = ∫ s, phi s ∂nu := by rw [hmap]

/-- On a probability space, the square of the integral of a real random variable is bounded by
the integral of its square.

This is the scalar `L2` contraction of expectation, stated in the form most stochastic
optimization estimates use when passing from a mean oracle norm to a second moment.

Layer: Glue | Gap: Level 0 (scalar probability second-moment contraction)
Proof: convert square-integrability to `MemLp`, rewrite variance as second moment minus squared
  mean, and use nonnegativity of variance.
Source: Mathlib probability variance and `L2` integrability APIs
Used in: stochastic block mirror descent deterministic mean bound for block oracle dual norms
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  stochastic block mirror descent -/
theorem sq_integral_le_integral_sq
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Z : Ω → ℝ}
    (hZ_meas : AEStronglyMeasurable Z μ)
    (hZ2 : Integrable (fun ω => Z ω ^ 2) μ) :
    (∫ ω, Z ω ∂μ) ^ 2 ≤ ∫ ω, Z ω ^ 2 ∂μ := by
  have hmem : MemLp Z 2 μ :=
    (MeasureTheory.memLp_two_iff_integrable_sq hZ_meas).2 hZ2
  have hvar_nonneg : 0 ≤ ProbabilityTheory.variance Z μ :=
    ProbabilityTheory.variance_nonneg Z μ
  have hvar_sub :
      0 ≤ (∫ ω, (Z ^ 2) ω ∂μ) - (∫ ω, Z ω ∂μ) ^ 2 := by
    simpa [ProbabilityTheory.variance_eq_sub hmem] using hvar_nonneg
  simpa [Pi.pow_apply] using sub_nonneg.mp hvar_sub

/-- The second component of a pair-valued random variable with product law has the
second marginal law.

If `Y : Ω → A × B` pushes `P` forward to `μ.prod ν` and the first marginal
`μ` is a probability measure, then the pushforward law of `fun ω => (Y ω).2`
is exactly `ν`.

Layer: Glue | Gap: Level 1 (product joint law to second marginal law)
Proof: rewrite the component pushforward as the second-projection pushforward
  of the pair law, substitute the product-law hypothesis, and use Mathlib's
  product-measure second-marginal theorem.
Source: Mathlib measure theory product measures and pushforward-map composition
Used in: stochastic block mirror descent block-index marginal law from the
  oracle/block product stream
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem map_snd_eq_of_map_prod_eq
    {Ω A B : Type*} [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
    {P : Measure Ω} {Y : Ω → A × B} {μ : Measure A} {ν : Measure B}
    [IsProbabilityMeasure μ] [SFinite ν]
    (hY : AEMeasurable Y P) (hY_law : Measure.map Y P = μ.prod ν) :
    Measure.map (fun ω => (Y ω).2) P = ν := by
  calc
    Measure.map (fun ω => (Y ω).2) P = Measure.map Prod.snd (Measure.map Y P) :=
      (AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable hY).symm
    _ = Measure.map Prod.snd (μ.prod ν) := by rw [hY_law]
    _ = ν := by rw [Measure.map_snd_prod, measure_univ, one_smul]

/-- The first component of a pair-valued random variable with product law has the
first marginal law.

If `Y : Ω → A × B` pushes `P` forward to `μ.prod ν` and the second marginal
`ν` is a probability measure, then the pushforward law of `fun ω => (Y ω).1`
is exactly `μ`.

Layer: Glue | Gap: Level 1 (product joint law to first marginal law)
Proof: rewrite the component pushforward as the first-projection pushforward of
  the pair law, substitute the product-law hypothesis, and use Mathlib's
  product-measure first-marginal theorem.
Source: Mathlib measure theory product measures and pushforward-map composition
Used in: stochastic block mirror descent oracle-sample marginal law from the
  oracle/block product stream
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic block mirror descent -/
theorem map_fst_eq_of_map_prod_eq
    {Ω A B : Type*} [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
    {P : Measure Ω} {Y : Ω → A × B} {μ : Measure A} {ν : Measure B}
    [IsProbabilityMeasure ν]
    (hY : AEMeasurable Y P) (hY_law : Measure.map Y P = μ.prod ν) :
    Measure.map (fun ω => (Y ω).1) P = μ := by
  calc
    Measure.map (fun ω => (Y ω).1) P = Measure.map Prod.fst (Measure.map Y P) :=
      (AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable hY).symm
    _ = Measure.map Prod.fst (μ.prod ν) := by rw [hY_law]
    _ = μ := by simp

/-- A centered Bochner-integrable vector has zero integral after scalarization by
a fixed Hilbert-space direction.

If `F` is integrable under a probability measure and its Bochner integral is the
deterministic mean `mean`, then the deviation `F - mean` has zero expected inner
product with any deterministic direction.

Layer: Glue | Gap: Level 0 (centered Bochner integral scalarization)
Proof: first integrate the centered vector using Bochner integral subtraction and
  the probability-space integral of a constant, then commute the integral through
  the continuous linear functional `u ↦ ⟪u, direction⟫_ℝ`.
Source: Mathlib Bochner integral linearity and Hilbert continuous-linear-map APIs
Used in: stochastic block mirror descent fixed sample-pair scalar oracle-noise centering
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  stochastic block mirror descent -/
theorem integral_inner_sub_mean_eq_zero_of_integral_eq
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Ω → E) (mean direction : E)
    (hF_int : Integrable F μ)
    (hmean : ∫ ω, F ω ∂μ = mean) :
    Integrable (fun ω => ⟪F ω - mean, direction⟫_ℝ) μ ∧
      ∫ ω, ⟪F ω - mean, direction⟫_ℝ ∂μ = 0 := by
  have hdev_int : Integrable (fun ω => F ω - mean) μ :=
    hF_int.sub (integrable_const (c := mean))
  have hscalar_int : Integrable (fun ω => ⟪F ω - mean, direction⟫_ℝ) μ := by
    simpa only [innerSLFlip_apply_apply] using
      (innerSLFlip ℝ direction).integrable_comp hdev_int
  have hvec_zero : ∫ ω, F ω - mean ∂μ = 0 := by
    calc
      ∫ ω, F ω - mean ∂μ =
          (∫ ω, F ω ∂μ) - ∫ _ω : Ω, mean ∂μ := by
            exact integral_sub hF_int (integrable_const (c := mean))
      _ = 0 := by
          simp [hmean]
  have hlin :=
    ContinuousLinearMap.integral_comp_comm (L := innerSLFlip ℝ direction) hdev_int
  have hzero :
      ∫ ω, ⟪F ω - mean, direction⟫_ℝ ∂μ = 0 := by
    have hzero' :
        ∫ ω, (innerSLFlip ℝ direction) (F ω - mean) ∂μ = 0 := by
      exact hlin.trans (by rw [hvec_zero]; simp)
    simpa only [innerSLFlip_apply_apply] using hzero'
  exact ⟨hscalar_int, hzero⟩

/-- A nonnegative scalar random variable has expectation at most `C` when its
second moment is bounded by `C^2`.

On a probability space this is the common `L2` to `L1` passage for
nonnegative estimator majorants: recover measurability from square
integrability, apply `E[Z]^2 ≤ E[Z^2]`, then compare nonnegative squares.

Layer: Glue | Gap: Level 1 (nonnegative scalar L2-to-L1 moment bound)
Proof: recover a.e. strong measurability from square-integrability and
  a.e. nonnegativity, use the scalar probability second-moment contraction,
  then close the square comparison by ordered real arithmetic.
Source: Mathlib probability variance API and real ordered-ring square comparison
Used in: stochastic nonconvex conditional gradient estimator-error L1 absorption
  from an epochwise second-moment estimate
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/main_theorem/proof/3
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem integral_nonneg_le_of_integral_sq_le_sq
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Z : Ω → ℝ} {C : ℝ}
    (hZ_sq_int : Integrable (fun ω => Z ω ^ 2) μ)
    (hZ_nonneg : ∀ᵐ ω ∂μ, 0 ≤ Z ω)
    (hC_nonneg : 0 ≤ C)
    (hZ_sq_le : ∫ ω, Z ω ^ 2 ∂μ ≤ C ^ 2) :
    ∫ ω, Z ω ∂μ ≤ C := by
  have hZ_meas : AEStronglyMeasurable Z μ :=
    AEStronglyMeasurable.of_integrable_sq_of_nonneg hZ_sq_int hZ_nonneg
  have hsq_l1 :
      (∫ ω, Z ω ∂μ) ^ 2 ≤ ∫ ω, Z ω ^ 2 ∂μ :=
    sq_integral_le_integral_sq hZ_meas hZ_sq_int
  have hsq_bound : (∫ ω, Z ω ∂μ) ^ 2 ≤ C ^ 2 :=
    le_trans hsq_l1 hZ_sq_le
  have hleft_nonneg : 0 ≤ ∫ ω, Z ω ∂μ :=
    integral_nonneg_of_ae hZ_nonneg
  nlinarith

/-- A function strongly measurable on a measurable support subtype is a.e. strongly
measurable under any mapped law supported on that set.

If `φ` is strongly measurable after restricting its domain to a measurable set
`A`, and the pushforward law of `wt` is a.e. supported on `A`, then the ambient
function `φ` is a.e. strongly measurable for that pushforward law.

Layer: Glue | Gap: Level 1 (support-subtype measurability under pushforward law)
Proof: extend the subtype function to the ambient space using the measurable
  embedding of `Subtype.val`, prove the extension strongly measurable, then use
  a.e. equality on the pushed-forward support.
Source: Mathlib measure theory strongly measurable extension and map-measure
  support APIs
Used in: nonconvex variance-reduced conditional gradient paired-gradient
  cancellation under a feasible-support map law
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, nonconvex variance-reduced conditional gradient -/
theorem aestronglyMeasurable_map_of_measurable_on_ae_support
    {Ω Z R : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    [TopologicalSpace R]
    {P : Measure Ω} {wt : Ω → Z} {A : Set Z} {φ : Z → R}
    (hA : MeasurableSet A)
    (hφA : StronglyMeasurable (fun z : A => φ z))
    (hsupport : ∀ᵐ z ∂Measure.map wt P, z ∈ A) :
    AEStronglyMeasurable φ (Measure.map wt P) := by
  classical
  obtain ⟨φext, hφext_sm, hφext_eq⟩ :=
    (MeasurableEmbedding.subtype_coe hA).exists_stronglyMeasurable_extend
      (f := fun z : A => φ z) hφA (fun z => ⟨φ z⟩)
  refine hφext_sm.aestronglyMeasurable.congr ?_
  filter_upwards [hsupport] with z hz
  exact congrFun hφext_eq ⟨z, hz⟩

/-- A Dirac measure gives zero mass to any set that avoids its measurable atom.

This is useful when the ambient measurable space does not have measurable
singletons globally: the proof only needs measurability of the singleton at the
Dirac atom, not measurability of the target set.

Layer: Glue | Gap: Level 0 (Dirac support outside a measurable atom)
Proof: bound the target set by the complement of the measurable singleton atom,
  then evaluate the Dirac measure on that measurable complement.
Source: Mathlib Dirac measure, measurable-set complement, and measure monotonicity APIs
Used in: stochastic nonconvex conditional gradient degenerate-law measurability counterexample
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning,
  stochastic nonconvex conditional gradient -/
theorem dirac_eq_zero_of_not_mem
    {Ω : Type*} [MeasurableSpace Ω] {x : Ω}
    (hx : MeasurableSet ({x} : Set Ω)) {s : Set Ω} (hs : x ∉ s) :
    Measure.dirac x s = 0 := by
  apply nonpos_iff_eq_zero.mp
  have hsub : s ⊆ ({x} : Set Ω)ᶜ := by
    intro y hy hyx
    rw [Set.mem_singleton_iff] at hyx
    subst y
    exact hs hy
  calc
    Measure.dirac x s ≤ Measure.dirac x (({x} : Set Ω)ᶜ) := measure_mono hsub
    _ = 0 := by
      rw [Measure.dirac_apply' _ hx.compl]
      simp

/-- Pairing two left-measurable random variables preserves independence from a right variable.

If `X` is measurable with respect to `m`, `m ≤ m'`, `Y` is measurable with
respect to `m'`, and `m'` is independent of the sigma-algebra generated by
`Z`, then the pair `(X, Y)` is independent of `Z`.

Layer: Glue | Gap: Level 1 (left-product independence from sigma-algebra freshness)
Proof: transport `X`-measurability along `m ≤ m'`, build the product map
  `(X, Y)`, then rewrite `IndepFun` as sigma-algebra independence and shrink
  the left side using the product map's comap bound.
Source: Mathlib probability independence API for sub-sigma-algebras and product
  measurable spaces
Used in: stochastic nonconvex conditional-gradient off-diagonal mini-batch
  covariance cancellation
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem indepFun_prod_of_measurable_le_of_indep_comap
    {Ω A B S : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace S]
    {μ : Measure Ω} {m m' : MeasurableSpace Ω}
    {X : Ω → A} {Y : Ω → B} {Z : Ω → S}
    (hX : Measurable[m] X) (hm_le : m ≤ m') (hY : Measurable[m'] Y)
    (hm'_indep_Z :
      Indep m' (MeasurableSpace.comap Z (by infer_instance : MeasurableSpace S)) μ) :
    IndepFun (fun ω => (X ω, Y ω)) Z μ := by
  have hX' : Measurable[m'] X := hX.mono hm_le le_rfl
  have hpair : Measurable[m'] (fun ω => (X ω, Y ω)) := hX'.prodMk hY
  rw [IndepFun_iff_Indep]
  exact indep_of_indep_of_le_left hm'_indep_Z hpair.comap_le

namespace SOptLib

/-- A finite sum of paired kernel differences is measurable from coordinate
measurability.

If `K` is jointly measurable, `x` and `y` are measurable into its query space,
and each selected sample coordinate is measurable for the same source
sigma-algebra, then the finite sum of the paired differences
`K (x omega, Y (idx i) omega) - K (y omega, Y (idx i) omega)` is measurable.

Layer: Glue | Gap: Level 0 (finite kernel-difference sum measurability)
Proof: compose the joint kernel with the two measurable query-coordinate
  product maps for each summand, close under measurable subtraction, and apply
  finite-sum measurability.
Source: Mathlib MeasureTheory APIs for product measurability, subtraction, and
  finite sums
Used in: stochastic nonconvex conditional-gradient recursive mini-batch
  gradient-difference adaptedness over a prefix filtration
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem measurable_finset_sum_kernel_diff_comp_of_coordinate_measurable
    {Ω E S F ι : Type*} [MeasurableSpace E] [MeasurableSpace S]
    [MeasurableSpace F] [AddCommMonoid F] [Sub F] [MeasurableAdd₂ F]
    [MeasurableSub₂ F]
    (mΩ : MeasurableSpace Ω) (I : Finset ι) (K : E × S → F)
    (hK : Measurable K) {x y : Ω → E} (hx : Measurable[mΩ] x)
    (hy : Measurable[mΩ] y) (Y : ℕ → Ω → S) (idx : ι → ℕ)
    (hY : ∀ i, i ∈ I → Measurable[mΩ] (Y (idx i))) :
    Measurable[mΩ]
      (fun ω =>
        Finset.sum I
          (fun i => K (x ω, Y (idx i) ω) - K (y ω, Y (idx i) ω))) := by
  refine Finset.measurable_sum I ?_
  intro i hi
  have hYi : Measurable[mΩ] (Y (idx i)) := hY i hi
  exact (hK.comp (hx.prodMk hYi)).sub (hK.comp (hy.prodMk hYi))

/-- A finite sum of composed kernel evaluations is measurable from coordinate
measurability.

If `K` is jointly measurable, `x` is measurable into its query space, and each
selected sample coordinate is measurable for the same source sigma-algebra, then
the finite sum of `K (x omega, Y (idx i) omega)` over the selected finite index
set is measurable.

Layer: Glue | Gap: Level 0 (finite kernel-sum measurability)
Proof: compose the joint kernel with the measurable query-coordinate product
  map for each summand, then apply finite-sum measurability.
Source: Mathlib MeasureTheory APIs for product measurability and finite sums
Used in: stochastic nonconvex conditional-gradient mini-batch gradient
  adaptedness over a prefix filtration
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem measurable_finset_sum_kernel_comp_of_coordinate_measurable
    {Ω E S F ι : Type*} [MeasurableSpace E] [MeasurableSpace S]
    [MeasurableSpace F] [AddCommMonoid F] [MeasurableAdd₂ F]
    (mΩ : MeasurableSpace Ω) (I : Finset ι) (K : E × S → F)
    (hK : Measurable K) {x : Ω → E} (hx : Measurable[mΩ] x)
    (Y : ℕ → Ω → S) (idx : ι → ℕ)
    (hY : ∀ i, i ∈ I → Measurable[mΩ] (Y (idx i))) :
    Measurable[mΩ]
      (fun ω =>
        Finset.sum I
          (fun i => K (x ω, Y (idx i) ω))) := by
  refine Finset.measurable_sum I ?_
  intro i hi
  exact hK.comp (hx.prodMk (hY i hi))

/-- An a.e. uniform norm bound gives squared-norm integrability and a second-moment bound.

On a probability space, if a normed-space-valued process is a.e. strongly
measurable and its norm is bounded by `G` almost everywhere, then its squared
norm is integrable and its second moment is at most `G ^ 2`.

Layer: Glue | Gap: Level 1 (a.e. bounded-process second-moment bridge)
Proof: square the a.e. norm domination to dominate `‖f ω‖ ^ 2` by the constant
  `G ^ 2`, use integrability by domination against a constant, then apply
  a.e. integral monotonicity and evaluate the constant integral on a probability
  space.
Source: Mathlib measure theory Bochner integrability, a.e. domination, and
  probability constant-integral APIs
Used in: nonconvex stochastic conditional gradient oracle second-moment control
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem integrable_sq_norm_of_ae_bound
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    {f : Ω → E} {G : ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hf_meas : AEStronglyMeasurable f μ)
    (hbounded : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ G) :
    Integrable (fun ω => ‖f ω‖ ^ 2) μ ∧ ∫ ω, ‖f ω‖ ^ 2 ∂μ ≤ G ^ 2 := by
  have hbound : ∀ᵐ ω ∂μ, ‖‖f ω‖ ^ 2‖ ≤ ‖G ^ 2‖ := by
    refine hbounded.mono ?_
    intro ω hω
    rw [Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg (sq_nonneg G)]
    exact pow_le_pow_left₀ (norm_nonneg _) hω 2
  have hint : Integrable (fun ω => ‖f ω‖ ^ 2) μ :=
    Integrable.mono (integrable_const (G ^ 2)) (hf_meas.norm.pow 2) hbound
  constructor
  · exact hint
  · calc
      ∫ ω, ‖f ω‖ ^ 2 ∂μ
          ≤ ∫ _ω, G ^ 2 ∂μ :=
            integral_mono_ae hint (integrable_const _)
              (hbounded.mono fun ω hω => pow_le_pow_left₀ (norm_nonneg _) hω 2)
      _ = G ^ 2 := by simp [integral_const, probReal_univ]

/-- A selector-first finite product integral expands as a weighted sum of fiber integrals.

For a finite index measure `ν` on the first coordinate and a sample measure
`μ` on the second coordinate, integrating the selected real-valued fiber
`F q.1 q.2` over `ν.prod μ` is the finite sum of singleton real masses of `ν`
times the corresponding sample fiber integrals.

Layer: Glue | Gap: Level 1 (selector-first finite-index product integral expansion)
Proof: swap the selector-first product integral to the sample-first orientation,
  then apply the finite selected-index product expansion by singleton real masses.
Source: Mathlib product-measure Bochner integration and finite-type integral APIs
Used in: stochastic nonconvex conditional-gradient randomized output expectation
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec/output
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem integral_finite_index_first_prod_eq_sum_weights
    {S ι : Type*} [MeasurableSpace S] [MeasurableSpace ι]
    [Fintype ι] [MeasurableSingletonClass ι]
    (ν : Measure ι) (μ : Measure S) [SFinite μ] [IsFiniteMeasure ν]
    (p : ι → ℝ) (F : ι → S → ℝ)
    (hν_singleton : ∀ i, ν.real ({i} : Set ι) = p i)
    (hF_int : ∀ i, Integrable (F i) μ) :
    ∫ q : ι × S, F q.1 q.2 ∂(ν.prod μ) =
      Finset.sum Finset.univ (fun i => p i * ∫ s, F i s ∂μ) := by
  classical
  have hswap :
      ∫ q : ι × S, F q.1 q.2 ∂(ν.prod μ) =
        ∫ q : S × ι, F q.2 q.1 ∂(μ.prod ν) := by
    simpa using
      (MeasureTheory.integral_prod_swap (μ := μ) (ν := ν)
        (f := fun q : S × ι => F q.2 q.1))
  rw [hswap]
  exact _root_.integral_selected_finite_index_prod_eq_sum_weights
    (μ := μ) (ν := ν) (p := p) (F := F) hν_singleton hF_int

end SOptLib

/-- An iid identically distributed sequence need not have measurable coordinates.

On any type with three distinguished points, equip the domain with the sigma-algebra
generated by one singleton and use a Dirac measure at that point. A function that differs
from a constant only at a second point is a.e. equal to that constant, hence supplies iid
and identically distributed representatives, but its exceptional singleton is not measurable.

Layer: Glue | Gap: Level 1 (iid representatives do not imply coordinate measurability)
Proof: construct a Dirac-supported representative that is a.e. equal to a constant, prove
  finite-family independence by evaluating all factors at the Dirac support, and refute
  measurability using `measurableSet_generateFrom_singleton_iff`.
Source: Mathlib probability `iIndepFun`, `IdentDistrib`, Dirac measures, and generated
  measurable-space APIs
Used in: stochastic conditional-gradient sample-field audit separating iid laws from
  coordinate measurability assumptions
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine
  Learning, stochastic nonconvex conditional gradient -/
theorem exists_iid_identDistrib_not_forall_measurable
    {Ω Ξ : Type*} [MeasurableSpace Ξ]
    (z o tw : Ω) (ff tt : Ξ)
    (hz_ne_o : z ≠ o) (htw_ne_z : tw ≠ z) (htw_ne_o : tw ≠ o)
    (htt_meas : MeasurableSet ({tt} : Set Ξ)) (hff_ne_tt : ff ≠ tt) :
    let _ : MeasurableSpace Ω :=
      MeasurableSpace.generateFrom ({({z} : Set Ω)} : Set (Set Ω))
    ∃ (ξ : ℕ → Ω → Ξ) (P : Measure Ω),
      IsProbabilityMeasure P ∧
      iIndepFun (β := fun _ : ℕ => Ξ) ξ P ∧
      (∀ k : ℕ, IdentDistrib (ξ k) (ξ 0) P P) ∧
      ¬ (∀ k : ℕ, Measurable (ξ k)) := by
  classical
  letI : MeasurableSpace Ω :=
    MeasurableSpace.generateFrom ({({z} : Set Ω)} : Set (Set Ω))
  let badSample : Ω → Ξ := fun ω => if ω = o then tt else ff
  let goodSample : Ω → Ξ := fun _ => ff
  have measurableSet_z : MeasurableSet ({z} : Set Ω) := by
    apply MeasurableSpace.measurableSet_generateFrom
    simp
  have badSample_z : badSample z = ff := by
    simp [badSample, hz_ne_o]
  have dirac_z_eq_zero_of_notMem {s : Set Ω} (hs : z ∉ s) :
      Measure.dirac z s = 0 :=
    dirac_eq_zero_of_not_mem measurableSet_z hs
  have badSample_not_measurable : ¬ Measurable badSample := by
    intro h
    have hpre : MeasurableSet (badSample ⁻¹' ({tt} : Set Ξ)) := h htt_meas
    have hsingleton : MeasurableSet ({o} : Set Ω) := by
      convert hpre using 1
      ext x
      by_cases hx : x = o
      · subst x
        simp [badSample]
      · simp [badSample, hx, hff_ne_tt]
    rw [measurableSet_generateFrom_singleton_iff] at hsingleton
    rcases hsingleton with h | h | h | h
    · have : o ∈ ({o} : Set Ω) := by simp
      rw [h] at this
      simp at this
    · have : o ∈ ({z} : Set Ω) := by
        rw [← h]
        simp
      simp [hz_ne_o.symm] at this
    · have : tw ∈ ({z} : Set Ω)ᶜ := by
        simp [htw_ne_z]
      rw [← h] at this
      simp [htw_ne_o] at this
    · have : z ∈ ({o} : Set Ω) := by
        rw [h]
        simp
      simp [hz_ne_o] at this
  have badSample_ae_eq_goodSample :
      badSample =ᵐ[Measure.dirac z] goodSample := by
    apply Filter.mem_of_superset (show ({z} : Set Ω) ∈ ae (Measure.dirac z) from by
      exact (mem_ae_dirac_iff measurableSet_z).2 (by simp))
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    simp [badSample_z, goodSample]
  have badSample_aemeasurable :
      AEMeasurable badSample (Measure.dirac z) := by
    exact ⟨goodSample, measurable_const, badSample_ae_eq_goodSample⟩
  refine ⟨fun _ => badSample, Measure.dirac z, inferInstance, ?_, ?_, ?_⟩
  · rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
    intro S sets _hsets
    by_cases hAll : ∀ i, i ∈ S → ff ∈ sets i
    · have hz_mem : z ∈ ⋂ i ∈ S, badSample ⁻¹' sets i := by
        simp only [Set.mem_iInter, Set.mem_preimage]
        intro i hi
        simpa [badSample_z] using hAll i hi
      have hleft : Measure.dirac z (⋂ i ∈ S, badSample ⁻¹' sets i) = 1 :=
        Measure.dirac_apply_of_mem hz_mem
      have hright :
          (∏ i ∈ S, Measure.dirac z (badSample ⁻¹' sets i)) = 1 := by
        refine Finset.prod_eq_one ?_
        intro i hi
        exact Measure.dirac_apply_of_mem (by simpa [badSample_z] using hAll i hi)
      rw [hleft, hright]
    · push Not at hAll
      rcases hAll with ⟨i, hiS, hi_not⟩
      have hz_not_left : z ∉ ⋂ i ∈ S, badSample ⁻¹' sets i := by
        intro hz_mem
        have hmem_i : z ∈ badSample ⁻¹' sets i :=
          (Set.mem_iInter.mp (Set.mem_iInter.mp hz_mem i) hiS)
        exact hi_not (by simpa [badSample_z] using hmem_i)
      have hleft : Measure.dirac z (⋂ i ∈ S, badSample ⁻¹' sets i) = 0 :=
        dirac_z_eq_zero_of_notMem hz_not_left
      have hfactor : Measure.dirac z (badSample ⁻¹' sets i) = 0 := by
        apply dirac_z_eq_zero_of_notMem
        intro hzmem
        exact hi_not (by simpa [badSample_z] using hzmem)
      have hright : (∏ j ∈ S, Measure.dirac z (badSample ⁻¹' sets j)) = 0 := by
        exact Finset.prod_eq_zero hiS hfactor
      rw [hleft, hright]
  · intro k
    exact IdentDistrib.refl badSample_aemeasurable
  · intro hmeas
    exact badSample_not_measurable (hmeas 0)

namespace ProbabilityTheory

/-- A future sample is independent of the sample-prefix natural filtration.

For an independent sample stream `ξ`, the sigma-algebra generated by any future
coordinate `ξ i` is independent of the filtration generated by the strict sample
prefix before time `n`, whenever `n ≤ i`.

Layer: Glue | Gap: Level 1 (future-sample independence from generated prefix)
Proof: unfold the sample-prefix filtration, apply independence of disjoint
  indexed `iSup`s to `{j | j < n}` and `{i}`, and discharge disjointness with
  the cutoff inequality `n ≤ i`.
Source: Mathlib probability independence APIs for independent families of
  sigma-algebras and complete-lattice `iSup`s
Used in: stochastic conditional-gradient adapted-prefix independence from a
  later mini-batch sample
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem iIndepFun.indep_prefixFiltration_future
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    {μ : Measure Ω}
    (ξ : ℕ → Ω → S)
    (hξ_measurable : ∀ n, Measurable (ξ n))
    (hξ_iIndep : iIndepFun ξ μ)
    {n i : ℕ} (hni : n ≤ i) :
    Indep (⨆ j < n, MeasurableSpace.comap (ξ j)
        (by infer_instance : MeasurableSpace S))
      (MeasurableSpace.comap (ξ i)
        (by infer_instance : MeasurableSpace S)) μ := by
  classical
  let mNat : ℕ → MeasurableSpace Ω :=
    fun j => MeasurableSpace.comap (ξ j)
      (by infer_instance : MeasurableSpace S)
  have hiNat : iIndep mNat μ := by
    simpa [mNat] using hξ_iIndep.iIndep
  have h_le : ∀ j, mNat j ≤ (by infer_instance : MeasurableSpace Ω) := by
    intro j
    simpa [mNat] using (hξ_measurable j).comap_le
  let Sset : Set ℕ := {j | j < n}
  let Tset : Set ℕ := ({i} : Set ℕ)
  have hST : Disjoint Sset Tset := by
    rw [Set.disjoint_singleton_right]
    intro hj
    exact not_lt_of_ge hni hj
  have h_ind : Indep (⨆ j ∈ Sset, mNat j) (⨆ j ∈ Tset, mNat j) μ :=
    indep_iSup_of_disjoint (m := mNat) h_le hiNat (S := Sset) (T := Tset) hST
  simpa [mNat, Sset, Tset] using h_ind

/-- A prefix-measurable random variable is independent of any future sample.

For an independent sample stream `ξ`, every random variable measurable with
respect to the natural sample-prefix filtration at cutoff `n` is independent of
coordinate `ξ i` whenever `n ≤ i`.

Layer: Glue | Gap: Level 1 (adapted prefix-measurable future-sample independence)
Proof: first use the sample-prefix/future-coordinate independence theorem for
  the generated filtration, then shrink the left sigma-algebra through the
  measurability of the adapted random variable.
Source: Mathlib probability independence APIs for random variables and
  sub-sigma-algebras, plus SOptLib sample-prefix filtration glue
Used in: stochastic conditional-gradient mini-batch freshness for adapted
  iterate and estimator states
Book citation: book/FOML/StochasticNonconvexConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem iIndepFun.indepFun_prefixMeasurable_future
    {Ω S β : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace β]
    {μ : Measure Ω}
    (ξ : ℕ → Ω → S)
    (hξ_measurable : ∀ n, Measurable (ξ n))
    (hξ_iIndep : iIndepFun ξ μ)
    {wt : Ω → β} {n i : ℕ}
    (hwt : Measurable[(⨆ j < n, MeasurableSpace.comap (ξ j)
        (by infer_instance : MeasurableSpace S))] wt)
    (hni : n ≤ i) :
    IndepFun wt (ξ i) μ :=
  indepFun_of_measurable_left_of_indep_comap hwt
    (iIndepFun.indep_prefixFiltration_future ξ hξ_measurable hξ_iIndep hni)

/-- A finite sample-block sigma-algebra is independent of any coordinate outside the block.

For an independent family of random variables, the sigma-algebra generated by a
finite block of coordinates is independent of the sigma-algebra generated by a
single coordinate not in that block.

Layer: Glue | Gap: Level 1 (finite sample-block freshness from iIndepFun)
Proof: turn `j ∉ block` into disjointness from `{j}`, apply finite-block
  independence for `iIndepFun`, then shrink the vector comap sigma-algebras to
  the generated finite block and singleton coordinate.
Source: Mathlib probability independence APIs for independent random-variable
  families and generated comap sigma-algebras
Used in: nonconvex stochastic conditional gradient validation freshness for a
  randomized output measurable from the optimization sample footprint
Book citation: book/FOML/NonconvexStochasticConditionalGradient.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic nonconvex conditional gradient -/
theorem iIndepFun.indep_sampleBlock_singleton_of_not_mem
    {Ω Ξ I : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] [DecidableEq I]
    (ξ : I → Ω → Ξ) (μ : Measure Ω) (block : Finset I) {j : I}
    (hξ_meas : ∀ i, Measurable (ξ i))
    (hξ_iIndep : iIndepFun ξ μ) (hj : j ∉ block) :
    Indep (⨆ q : {q // q ∈ block},
        MeasurableSpace.comap (fun ω => ξ q.1 ω)
          (by infer_instance : MeasurableSpace Ξ))
      (MeasurableSpace.comap (ξ j) (by infer_instance : MeasurableSpace Ξ)) μ := by
  classical
  have hdisj : Disjoint block ({j} : Finset I) := by
    rw [Finset.disjoint_left]
    intro x hx hxj
    have hx_eq : x = j := by simpa using hxj
    exact hj (by simpa [hx_eq] using hx)
  have hvec :
      IndepFun
        (fun ω => fun p : {p // p ∈ block} => ξ p.1 ω)
        (fun ω => fun q : {q // q ∈ ({j} : Finset I)} => ξ q.1 ω)
        μ :=
    hξ_iIndep.indepFun_finset block ({j} : Finset I) hdisj hξ_meas
  simpa using
    (indep_sampleBlock_singleton_of_disjoint_indices
      (μ := μ) (ξI := ξ) (ξJ := ξ) (A := block) (j := j) hvec)

end ProbabilityTheory

/-- A selected nonnegative summand is integrable when a positive weighted
finite sum is integrable.

If the coefficient at `k` is positive, all coefficients and summands are
nonnegative on a finite set `s`, and the weighted sum over `s` is integrable,
then the selected real-valued random variable `Y k` is integrable.

Layer: Glue | Gap: Level 1 (finite weighted-sum summand integrability)
Proof: bound the selected weighted summand by the whole nonnegative finite
  sum using `Finset.single_le_sum`, rescale by the positive coefficient, and
  apply `Integrable.mono'`.
Source: Mathlib finite-sum order lemmas and Bochner integrability domination
Used in: stochastic accelerated gradient descent terminal state-square
  integrability from a finite Lyapunov window
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
theorem integrable_of_le_integrable_weighted_finset_sum
    {Ω I : Type*} [MeasurableSpace Ω] [DecidableEq I]
    {μ : Measure Ω} (s : Finset I) (k : I) (c : I → ℝ)
    (Y : I → Ω → ℝ)
    (hk : k ∈ s)
    (hsum_int :
      Integrable (fun ω => Finset.sum s (fun t => c t * Y t ω)) μ)
    (hY_meas : AEStronglyMeasurable (Y k) μ)
    (hc_pos : 0 < c k)
    (hc_nonneg : ∀ t ∈ s, 0 ≤ c t)
    (hY_nonneg : ∀ᵐ ω ∂μ, ∀ t ∈ s, 0 ≤ Y t ω) :
    Integrable (Y k) μ := by
  classical
  have hscaled_int :
      Integrable
        (fun ω => (1 / c k) * Finset.sum s (fun t => c t * Y t ω)) μ :=
    hsum_int.const_mul (1 / c k)
  refine Integrable.mono' hscaled_int hY_meas ?_
  filter_upwards [hY_nonneg] with ω hYω
  have hterm_le :
      c k * Y k ω ≤ Finset.sum s (fun t => c t * Y t ω) := by
    exact Finset.single_le_sum
      (fun t ht => mul_nonneg (hc_nonneg t ht) (hYω t ht)) hk
  have hYk_nonneg : 0 ≤ Y k ω := hYω k hk
  have hinv_nonneg : 0 ≤ 1 / c k := by
    simpa [one_div] using inv_nonneg.mpr (le_of_lt hc_pos)
  have hscaled_le :
      Y k ω ≤ (1 / c k) * Finset.sum s (fun t => c t * Y t ω) := by
    have hmul := mul_le_mul_of_nonneg_left hterm_le hinv_nonneg
    calc
      Y k ω = (1 / c k) * (c k * Y k ω) := by
        field_simp [ne_of_gt hc_pos]
      _ ≤ (1 / c k) * Finset.sum s (fun t => c t * Y t ω) := hmul
  simpa [Real.norm_of_nonneg hYk_nonneg] using hscaled_le

/-- A nonnegative scalar with bounded second moment has a shifted-square bound.

On a probability space, if `Z^2` is integrable and has expectation at most
`sigma^2`, then `(M + Z)^2` is integrable and its expectation is bounded by
`2 * (M^2 + sigma^2)`.

Layer: Glue | Gap: Level 1 (shifted-square moment bound from second moment)
Proof: first obtain `L¹` integrability of the nonnegative scalar from the
  existing L2-to-L1 bridge. Then expand the shifted square as a polynomial,
  dominate it pointwise by `2 * (M^2 + Z^2)`, and integrate the inequality.
Source: Mathlib measure theory Bochner integral linearity, integral monotonicity,
  and real ordered-ring square inequalities
Used in: accelerated stochastic gradient shifted oracle-noise square estimate
  before one-step stochastic-error integration
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
theorem integrable_sq_add_nonneg_of_integrable_sq_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Z : Ω → ℝ} {M sigma : ℝ}
    (hZ_sq_int : Integrable (fun ω => Z ω ^ 2) μ)
    (hZ_nonneg : ∀ᵐ ω ∂μ, 0 ≤ Z ω)
    (hZ_sq_bound : ∫ ω, Z ω ^ 2 ∂μ ≤ sigma ^ 2) :
    Integrable (fun ω => (M + Z ω) ^ 2) μ ∧
      ∫ ω, (M + Z ω) ^ 2 ∂μ ≤ 2 * (M ^ 2 + sigma ^ 2) := by
  have hZ_int : Integrable Z μ :=
    (integrable_of_nonneg_sq_integrable_integral_le_sq_bound_add_one
      hZ_sq_int hZ_nonneg hZ_sq_bound).1
  have hpoly_int :
      Integrable (fun ω => M ^ 2 + (2 * M) * Z ω + Z ω ^ 2) μ := by
    exact ((integrable_const (c := M ^ 2)).add
      (hZ_int.const_mul (2 * M))).add hZ_sq_int
  have hshift_int : Integrable (fun ω => (M + Z ω) ^ 2) μ := by
    refine hpoly_int.congr ?_
    filter_upwards with ω
    ring
  have hupper_int : Integrable (fun ω => 2 * (M ^ 2 + Z ω ^ 2)) μ := by
    exact ((integrable_const (c := M ^ 2)).add hZ_sq_int).const_mul 2
  have hpoint : ∀ ω, (M + Z ω) ^ 2 ≤ 2 * (M ^ 2 + Z ω ^ 2) := by
    intro ω
    nlinarith [sq_nonneg (M - Z ω)]
  have hint_le :
      ∫ ω, (M + Z ω) ^ 2 ∂μ ≤
        ∫ ω, 2 * (M ^ 2 + Z ω ^ 2) ∂μ :=
    integral_mono hshift_int hupper_int hpoint
  refine ⟨hshift_int, ?_⟩
  calc
    ∫ ω, (M + Z ω) ^ 2 ∂μ
        ≤ ∫ ω, 2 * (M ^ 2 + Z ω ^ 2) ∂μ := hint_le
    _ = 2 * (M ^ 2 + ∫ ω, Z ω ^ 2 ∂μ) := by
        rw [integral_const_mul]
        rw [integral_add (integrable_const (c := M ^ 2)) hZ_sq_int]
        simp
    _ ≤ 2 * (M ^ 2 + sigma ^ 2) := by
        nlinarith [hZ_sq_bound]

namespace SOptLib

/-- Centered square-integrability is preserved by a two-stage affine combination.

If `x` and `xBar` have integrable squared distance from a fixed center `c`,
then the point obtained by first forming `(1 - q) • xBar + q • x` and then
forming the affine blend `a • · + b • x` also has integrable squared distance
from `c`.

Layer: Glue | Gap: Level 1 (centered L2 transport through nested affine updates)
Proof: convert centered squared-norm integrability to `MemLp` at exponent two,
  rewrite each centered affine blend as the corresponding affine blend of
  centered displacements, close `MemLp` under addition and scalar
  multiplication, and convert back by `memLp_two_iff_integrable_sq_norm`.
Source: Mathlib Lp-space closure, Bochner measurability, and norm-square
  integrability APIs
Used in: stochastic accelerated gradient descent auxiliary-point multiplier
  square-integrability; stochastic mirror descent momentum-point L2 transport
Book citation: book/FOML/StochasticAcceleratedGradientDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated gradient descent -/
theorem integrable_sq_norm_const_sub_two_stage_affine
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    (c : E) (x xBar : Ω → E) (q a b : ℝ)
    (hx_meas : AEStronglyMeasurable x μ)
    (hxBar_meas : AEStronglyMeasurable xBar μ)
    (hx_sq : Integrable (fun ω => ‖c - x ω‖ ^ 2) μ)
    (hxBar_sq : Integrable (fun ω => ‖c - xBar ω‖ ^ 2) μ)
    (hab : a + b = 1) :
    Integrable
      (fun ω => ‖c - (a • ((1 - q) • xBar ω + q • x ω) + b • x ω)‖ ^ 2)
      μ := by
  have hx_disp_meas : AEStronglyMeasurable (fun ω => c - x ω) μ :=
    (aestronglyMeasurable_const.sub hx_meas)
  have hxBar_disp_meas : AEStronglyMeasurable (fun ω => c - xBar ω) μ :=
    (aestronglyMeasurable_const.sub hxBar_meas)
  have hx_disp_l2 : MemLp (fun ω => c - x ω) 2 μ :=
    (memLp_two_iff_integrable_sq_norm hx_disp_meas).2 hx_sq
  have hxBar_disp_l2 : MemLp (fun ω => c - xBar ω) 2 μ :=
    (memLp_two_iff_integrable_sq_norm hxBar_disp_meas).2 hxBar_sq
  have hfirst_raw :
      MemLp (fun ω => (1 - q) • (c - xBar ω) + q • (c - x ω)) 2 μ :=
    (hxBar_disp_l2.const_smul (1 - q)).add (hx_disp_l2.const_smul q)
  have hfirst_l2 :
      MemLp (fun ω => c - ((1 - q) • xBar ω + q • x ω)) 2 μ := by
    refine MemLp.ae_eq ?_ hfirst_raw
    refine Filter.Eventually.of_forall ?_
    intro ω
    change (1 - q) • (c - xBar ω) + q • (c - x ω) =
      c - ((1 - q) • xBar ω + q • x ω)
    module
  have hsecond_raw :
      MemLp
        (fun ω =>
          a • (c - ((1 - q) • xBar ω + q • x ω)) + b • (c - x ω))
        2 μ :=
    (hfirst_l2.const_smul a).add (hx_disp_l2.const_smul b)
  have htarget_l2 :
      MemLp
        (fun ω => c - (a • ((1 - q) • xBar ω + q • x ω) + b • x ω))
        2 μ := by
    refine MemLp.ae_eq ?_ hsecond_raw
    refine Filter.Eventually.of_forall ?_
    intro ω
    change a • (c - ((1 - q) • xBar ω + q • x ω)) + b • (c - x ω) =
      c - (a • ((1 - q) • xBar ω + q • x ω) + b • x ω)
    have hb : b = 1 - a := by linarith
    rw [hb]
    module
  exact
    (memLp_two_iff_integrable_sq_norm htarget_l2.aestronglyMeasurable).1
      htarget_l2

end SOptLib

-- Promoted from .sgd_phase3_staging/SOptLib/Glue/integrable_comp_of_indep_fixed_norm_bound_by_integrable_budget.lean
-- Generalization plan (G0):
-- G0.1 naming: integrable_comp_of_indep_fixed_norm_bound_by_integrable_budget
--   (orig was: integrable_scalar_comp_of_indep_fixed_norm_bound_by_integrable_budget)
-- G0.2 typeclass level used:
--   E: NormedAddCommGroup with MeasurableSpace, BorelSpace, and SecondCountableTopology
--      for Mathlib's measurable-to-a.e.-strongly-measurable bridge; no linear or
--      inner-product structure is used because the proof only integrates the norm.
--   measure: abstract finite base measure P and sample law ν, with ν recovered finite from
--      map Y P = ν.
--   convexity: none.
-- G0.3 reusability — could instantiate:
--   1. stochastic block mirror descent scalar martingale-difference integrability.
--   2. stochastic mirror descent or variance-reduced mirror descent random-query noise
--      integrability with query-dependent L1 budgets.
-- G0.4 search trace:
--   queries: ["Integrable product fiber bound",
--     "independent fixed norm integrable variable budget"]
--   top hits: ["integrable_comp_of_indep_fixed_integral_bound",
--     "integrable_scalar_oracle_noise_of_indep_uniform_l1_bound",
--     "MeasureTheory.Measure.integrable_compProd_iff",
--     "MeasureTheory.Integrable.prod_right_ae"]
--   coverage: partial — overlaps with constant-budget product-law transfer but does not
--     subsume an integrable variable budget C (X ω).
-- G0.4 not-a-thin-wrapper rationale: the statement packages independence, law transport,
--   product integrability, norm reduction, and domination by an integrable variable fiber
--   budget; no existing hit has this quantifier and budget structure.
-- G0.5 structural-content rationale: theorem-shaped Glue entry with no new wrapper def or
--   structure; it proves a reusable product-law L1 transfer.
-- G0.5c thin-wrapper self-detect: clean — body has a multi-step product-law/Fubini proof
--   plus norm-to-kernel integrability conversion.
-- G0.5d minimal-hypothesis check: all already minimal; global measurability is used for
--   map-measure transfer and product integrability, and the fiber hypotheses are pointwise.

open MeasureTheory ProbabilityTheory

/-- Transfer fixed-fiber norm integrability through an independent random parameter with a
query-dependent integrable budget.

If `Y` has law `ν`, `X` is independent of `Y`, every fixed fiber of
`s ↦ ‖noise z s‖` is integrable, and its fiber `L¹` norm is bounded by a
measurable budget `C z` whose pullback along `X` is integrable, then the
composed random kernel `ω ↦ noise (X ω) (Y ω)` is integrable.

Layer: Glue | Gap: Level 1 (variable-budget product-law/Fubini integrability transfer)
Proof: identify the joint law using independence, apply product integrability to the
  norm kernel, dominate the outer fiber-norm integral by the integrable budget, and
  convert integrability of the norm back to integrability of the kernel.
Source: Mathlib product-measure integration, Bochner integrability, and probability
  independence APIs
Used in: stochastic block mirror descent scalar martingale-difference integrability with
  query-dependent radius budget
Book citation: book/FOML/StochasticBlockMirrorDescent.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine
  Learning, stochastic block mirror descent -/
theorem integrable_comp_of_indep_fixed_norm_bound_by_integrable_budget
    {Ω Z S E : Type*} [MeasurableSpace Ω] [MeasurableSpace Z] [MeasurableSpace S]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {P : Measure Ω} {ν : Measure S} [IsFiniteMeasure P]
    {X : Ω → Z} {Y : Ω → S} {noise : Z → S → E} {C : Z → ℝ}
    (hnoise : Measurable (Function.uncurry noise))
    (hC : Measurable C)
    (hX : Measurable X) (hY : Measurable Y)
    (h_indep : IndepFun X Y P)
    (h_dist : Measure.map Y P = ν)
    (hC_int : Integrable (fun ω => C (X ω)) P)
    (hfixed_int : ∀ z, Integrable (fun s => ‖noise z s‖) ν)
    (hfixed_bound : ∀ z, ∫ s, ‖noise z s‖ ∂ν ≤ C z) :
    Integrable (fun ω => noise (X ω) (Y ω)) P := by
  classical
  let normNoise : Z → S → ℝ := fun z s => ‖noise z s‖
  have hnormNoise : Measurable (Function.uncurry normNoise) := by
    simpa [normNoise, Function.uncurry] using hnoise.norm
  have h_joint_meas : AEMeasurable (fun ω => (X ω, Y ω)) P :=
    (hX.prodMk hY).aemeasurable
  have h_prod_eq : P.map (fun ω => (X ω, Y ω)) = (P.map X).prod ν := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable).mp
      h_indep, h_dist]
  haveI : IsFiniteMeasure ν := by
    rw [← h_dist]
    exact Measure.isFiniteMeasure_map P Y
  haveI : IsFiniteMeasure (P.map X) :=
    Measure.isFiniteMeasure_map P X
  have hC_int_map : Integrable C (P.map X) :=
    (integrable_map_measure hC.aestronglyMeasurable hX.aemeasurable).mpr hC_int
  have hnorm_comp : Integrable (fun ω => normNoise (X ω) (Y ω)) P := by
    suffices h_prod :
        Integrable (fun p : Z × S => normNoise p.1 p.2) ((P.map X).prod ν) by
      have h_on_map : Integrable (fun p : Z × S => normNoise p.1 p.2)
          (P.map (fun ω => (X ω, Y ω))) := h_prod_eq ▸ h_prod
      exact (integrable_map_measure hnormNoise.aestronglyMeasurable h_joint_meas).mp
        h_on_map
    change Integrable (Function.uncurry normNoise) ((P.map X).prod ν)
    rw [integrable_prod_iff hnormNoise.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall ?_, ?_⟩
    · intro z
      simpa [normNoise] using hfixed_int z
    · refine Integrable.mono hC_int_map
        ((hnormNoise.norm.stronglyMeasurable.integral_prod_right').aestronglyMeasurable)
        (Filter.Eventually.of_forall ?_)
      intro z
      have h_abs_eq :
          (∫ y, ‖Function.uncurry normNoise (z, y)‖ ∂ν) =
            ∫ s, normNoise z s ∂ν := by
        refine integral_congr_ae (Filter.Eventually.of_forall ?_)
        intro s
        exact Real.norm_of_nonneg (norm_nonneg _)
      have h_int_nonneg : 0 ≤ ∫ s, normNoise z s ∂ν := by
        exact integral_nonneg fun s => norm_nonneg _
      have hC_nonneg : 0 ≤ C z := le_trans h_int_nonneg (hfixed_bound z)
      rw [h_abs_eq, Real.norm_eq_abs, abs_of_nonneg h_int_nonneg,
        Real.norm_eq_abs, abs_of_nonneg hC_nonneg]
      simpa [normNoise] using hfixed_bound z
  have hkernel_aemeas :
      AEStronglyMeasurable (fun ω => noise (X ω) (Y ω)) P := by
    exact (hnoise.comp (hX.prodMk hY)).aestronglyMeasurable
  exact (integrable_norm_iff hkernel_aemeas).1 (by simpa [normNoise] using hnorm_comp)


open MeasureTheory

-- Generalization plan (G0):
-- concept/name: conditional-expectation bound carrying well-definedness; orig was SapdConditionalExpectationBound
-- generality used: arbitrary measurable space, arbitrary measure, arbitrary conditioning measurable space, and real-valued input/bound functions; no probability, filtration, convexity, oracle, topology, or finite-dimensional assumptions
-- portable call pattern: stochastic mirror descent, stochastic accelerated primal-dual, and stochastic mirror-prox light-tail or conditional-MGF steps assume a conditional expectation upper bound and later need both the integrability of the input and the a.e. inequality for `condExp_mono`, `condExp_add`, and tower arguments
-- counterargument checked: not merely paper-local traceability because Lean's totalized conditional expectation makes this bundled predicate a reusable well-definedness boundary; not a one-line theorem duplicate because Mathlib exposes integrability and conditional-expectation inequalities separately, not this named package with projection API
-- coverage search: LeanSearch query "predicate packages integrability and almost everywhere conditional expectation upper bound" found `MeasureTheory.ae_bdd_condExp_of_ae_bdd`, `MeasureTheory.condExp_of_aestronglyMeasurable'`, and kernel representation lemmas; SOptLib/catalog search found martingale zero-integral and weighted-integral consequences, but no predicate bundling `Integrable f μ` with `μ[f | m] ≤ᵐ[μ] bound`
-- minimal hypotheses: all already minimal; the statement keeps only the measure and functions needed to form the conditional expectation and a.e. bound

/-- A conditional-expectation upper bound packaged with input integrability.

This predicate records the well-definedness fact needed when using Mathlib's
totalized conditional expectation together with an a.e. upper bound.

Layer: Glue | Concept: Conditional expectation
Proof: (definitional construction; conjunction of input integrability and an
  a.e. conditional-expectation upper bound)
Source: Mathlib conditional expectation and Bochner integrability APIs
Used in: stochastic optimization light-tail and conditional-MGF proofs that
  carry well-defined conditional expectations through monotonicity and tower
  steps
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/assumptions/8
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
def condExpBound
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (μ : @Measure Ω mΩ)
    (m : MeasurableSpace Ω) (f bound : Ω → ℝ) : Prop :=
  Integrable f μ ∧ μ[f | m] ≤ᵐ[μ] bound

/-- The conditional-expectation bound predicate unfolds to integrability and an
a.e. conditional-expectation upper bound.

Layer: Glue | Gap: Level 0 (conditional-expectation bound unfolding)
Proof: by rfl after unfolding `condExpBound`.
Source: Mathlib conditional expectation and Bochner integrability APIs
Used in: stochastic optimization light-tail and conditional-MGF proofs that
  need to expose both components of a packaged conditional bound
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/assumptions/8
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
@[simp]
theorem condExpBound_def
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (μ : @Measure Ω mΩ)
    (m : MeasurableSpace Ω) (f bound : Ω → ℝ) :
    condExpBound μ m f bound ↔ Integrable f μ ∧ μ[f | m] ≤ᵐ[μ] bound := by
  rfl

namespace condExpBound

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {μ : @Measure Ω mΩ} {m : MeasurableSpace Ω}
variable {f bound : Ω → ℝ}

/-- Integrability component of a packaged conditional-expectation upper bound.

Layer: Glue | Gap: Level 0 (conditional-expectation bound projection)
Proof: unfold the packaged bound and take the first conjunct.
Source: Mathlib conditional expectation and Bochner integrability APIs
Used in: stochastic optimization light-tail and conditional-MGF proofs before
  applying conditional-expectation monotonicity and linearity lemmas
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/assumptions/8
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
theorem integrable (h : condExpBound μ m f bound) :
    Integrable f μ :=
  h.1

/-- A.e. inequality component of a packaged conditional-expectation upper bound.

Layer: Glue | Gap: Level 0 (conditional-expectation bound projection)
Proof: unfold the packaged bound and take the second conjunct.
Source: Mathlib conditional expectation and almost-everywhere order APIs
Used in: stochastic optimization light-tail and conditional-MGF proofs when
  transporting source bounds through conditional-expectation inequalities
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/assumptions/8
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
theorem ae_le (h : condExpBound μ m f bound) :
    μ[f | m] ≤ᵐ[μ] bound :=
  h.2

end condExpBound



open MeasureTheory ProbabilityTheory

-- Generalization plan (G0):
-- concept/name: conditional exponential-moment attenuation under conditional expectation; orig was condExp_exp_scaled_sq_le_of_cond_light_tail
-- generality used: arbitrary measurable sample space, finite measure, sub-sigma-algebra `m ≤ mΩ`, real-valued random variable, and scale `a ∈ [0,1]`; no filtration, oracle, optimization setup, convexity, smoothness, or finite-dimensional assumptions
-- portable call pattern: stochastic accelerated primal-dual, stochastic mirror descent, stochastic mirror-prox, and martingale concentration proofs first prove `E[exp X | m] ≤ exp 1` and then need the same conditional MGF bound for smaller deterministic tilts `a * X`
-- counterargument checked: not paper-local traceability because it is the reusable conditional Jensen step turning a unit exponential moment bound into all subunit exponential moment bounds; not a pure wrapper because it composes Mathlib integrability transfer, conditional Jensen for concave powers, conditional nonnegativity, and monotonicity of `rpow`
-- coverage search: LeanSearch found `ProbabilityTheory.integrable_exp_mul_of_nonneg_of_le`, `HasCondSubgaussianMGF.ae_condExp_le`, and `MeasureTheory.condExp_mono`; SOptLib/catalog searches for `condExp exp`, `conditional MGF`, and `light_tail` found packaged sub-Gaussian adapters and scalar exponential lemmas but no theorem deriving `μ[exp (a * X) | m] ≤ exp a` from `μ[exp X | m] ≤ exp 1`
-- minimal hypotheses: replaces the paper light-tail package with the two used facts `Integrable (exp ∘ X) μ` and the a.e. conditional bound; `Measurable X` is not needed because Mathlib's exponential-tilt integrability lemma supplies the subunit integrability

/-- A unit conditional exponential-moment bound implies every subunit tilt bound.

If `E[exp X | m] ≤ exp 1` a.e. and `0 ≤ a ≤ 1`, conditional Jensen for the
concave map `y ↦ y^a` on `[0,∞)` gives
`E[exp (a * X) | m] ≤ exp a`.

Layer: Glue | Gap: Level 1 (conditional exponential-moment attenuation)
Proof: use Mathlib's integrability transfer for smaller exponential tilts,
  apply conditional Jensen to the concave power function on nonnegative
  reals, and compare the resulting powered conditional expectation with
  `(exp 1)^a = exp a`.
Source: Mathlib conditional Jensen, real powers, and exponential integrability
  APIs
Used in: stochastic optimization light-tail martingale proofs that rescale a
  one-step conditional square-exponential bound to smaller deterministic tilts
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/key_lemmas/5/proof
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
theorem condExp_exp_mul_le_exp_of_condExp_exp_le_exp_one
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ : @Measure Ω mΩ} [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {X : Ω → ℝ} {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hexp_int : Integrable (fun ω => Real.exp (X ω)) μ)
    (hcond_exp_le : μ[fun ω => Real.exp (X ω) | m] ≤ᵐ[μ] fun _ => Real.exp 1) :
    μ[fun ω => Real.exp (a * X ω) | m] ≤ᵐ[μ] fun _ => Real.exp a := by
  have hscaled_int : Integrable (fun ω => Real.exp (a * X ω)) μ := by
    have hone_int : Integrable (fun ω => Real.exp ((1 : ℝ) * X ω)) μ := by
      simpa [one_mul] using hexp_int
    exact ProbabilityTheory.integrable_exp_mul_of_nonneg_of_le
      (X := X) (μ := μ) (t := a) (u := 1) hone_int ha0 ha1
  have hpow_int :
      Integrable (fun ω => (Real.exp (X ω)) ^ a) μ := by
    refine hscaled_int.congr ?_
    filter_upwards [] with ω
    rw [← Real.exp_mul]
    ring_nf
  have hJ :
      μ[(fun y : ℝ => y ^ a) ∘ (fun ω => Real.exp (X ω)) | m] ≤ᵐ[μ]
        (fun y : ℝ => y ^ a) ∘ μ[fun ω => Real.exp (X ω) | m] := by
    have hnonneg : ∀ᵐ ω ∂μ, Real.exp (X ω) ∈ Set.Ici (0 : ℝ) := by
      filter_upwards [] with ω
      exact le_of_lt (Real.exp_pos _)
    have hclosed : IsClosed (Set.Ici (0 : ℝ)) := isClosed_Ici
    have hcont : UpperSemicontinuousOn (fun y : ℝ => y ^ a) (Set.Ici (0 : ℝ)) := by
      exact (Real.continuous_rpow_const ha0).continuousOn.upperSemicontinuousOn
    exact
      (Real.concaveOn_rpow ha0 ha1).condExp_map_le
        (μ := μ) (m := m) hm hcont hnonneg hclosed hexp_int hpow_int
  have hcond_nonneg :
      0 ≤ᵐ[μ] μ[fun ω => Real.exp (X ω) | m] := by
    refine condExp_nonneg (μ := μ) (m := m) ?_
    filter_upwards [] with ω
    exact le_of_lt (Real.exp_pos _)
  have hpow_bound :
      ((fun y : ℝ => y ^ a) ∘ μ[fun ω => Real.exp (X ω) | m]) ≤ᵐ[μ]
        fun _ => (Real.exp 1) ^ a := by
    filter_upwards [hcond_exp_le, hcond_nonneg] with ω hω hω_nonneg
    exact Real.rpow_le_rpow hω_nonneg hω ha0
  have htarget :
      μ[(fun y : ℝ => y ^ a) ∘ (fun ω => Real.exp (X ω)) | m] ≤ᵐ[μ]
        fun _ => Real.exp a := by
    refine hJ.trans ?_
    filter_upwards [hpow_bound] with ω hω
    simpa [Real.exp_one_rpow] using hω
  have hinput :
      (fun ω => Real.exp (a * X ω)) = (fun ω => (Real.exp (X ω)) ^ a) := by
    funext ω
    rw [← Real.exp_mul]
    ring_nf
  simpa [Function.comp_def, hinput] using htarget


open MeasureTheory ProbabilityTheory

-- Generalization plan (G0):
-- concept/name: conditional-expectation exponential rescaling; orig was condExp_exp_scaled_sq_bound_of_cond_light_tail
-- generality used: arbitrary measurable space, arbitrary finite measure, arbitrary conditioning measurable space, a real random variable, and a deterministic scale a in [0,1], all packaged through `condExpBound`
-- portable call pattern: stochastic accelerated primal-dual light-tail steps, stochastic mirror descent, and martingale MGF arguments first establish a unit exponential conditional bound and then need the same packaged bound after shrinking the tilt by a deterministic factor
-- counterargument checked: not paper-local traceability because the statement is the reusable `condExpBound`-level rescaling boundary; not a wrapper around a caller-side expression because it composes integrability transfer with the existing conditional exponential rescaling theorem
-- coverage search: LeanSearch found `HasCondSubgaussianMGF.ae_condExp_le`, `MeasureTheory.condExp_mono`, and `MeasureTheory.integrable_condExp`; SOptLib staging already has `condExpBound` and the a.e.-only `condExp_exp_mul_le_exp_of_condExp_exp_le_exp_one`, but no packaged integrability-carrying rescaling theorem
-- minimal hypotheses: all used hypotheses are kept; the theorem only needs the integrability and a.e. components already present in `condExpBound`, plus the deterministic scale bounds `0 ≤ a ≤ 1`

/-- A packaged conditional exponential bound is stable under deterministic rescaling of the tilt.

If `exp X` has a packaged conditional-expectation upper bound by `exp 1`, then for any
`0 ≤ a ≤ 1` the same package holds for `exp (a * X)` with bound `exp a`.

Layer: Glue | Gap: Level 1 (conditional-expectation exponential rescaling)
Proof: derive integrability of the smaller tilt from the unit exponential integrability,
  then apply the existing a.e. conditional-expectation rescaling lemma and repackage the
  result as `condExpBound`.
Source: Mathlib conditional expectation, exponential integrability, and concave power APIs
Used in: stochastic accelerated primal-dual light-tail conditional MGF bounds after shrinking
  a unit exponential moment to a subunit deterministic tilt
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/key_lemmas/5/proof
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic accelerated primal-dual -/
theorem condExpBound_exp_mul_of_condExpBound_exp
    {Ω : Type*} [MeasurableSpace Ω]
    {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {X : Ω → ℝ} {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (h : condExpBound μ m (fun ω => Real.exp (X ω)) (fun _ => Real.exp 1)) :
    condExpBound μ m (fun ω => Real.exp (a * X ω)) (fun _ => Real.exp a) := by
  have hscaled_int : Integrable (fun ω => Real.exp (a * X ω)) μ := by
    have hone_int : Integrable (fun ω => Real.exp ((1 : ℝ) * X ω)) μ := by
      simpa [one_mul] using h.integrable
    exact ProbabilityTheory.integrable_exp_mul_of_nonneg_of_le
      (X := X) (μ := μ) (t := a) (u := 1) hone_int ha0 ha1
  exact
    ⟨hscaled_int,
      condExp_exp_mul_le_exp_of_condExp_exp_le_exp_one
        (μ := μ) (m := m) (mΩ := mΩ) hm ha0 ha1 h.integrable h.ae_le⟩


open MeasureTheory

-- Generalization plan (G0):
-- concept/name: scalar integrability from square-exponential conditional light-tail control; orig was lemma_4_1_zeta_integrable_of_cond_light_tail
-- generality used: arbitrary measurable sample space, arbitrary measure, arbitrary conditioning measurable space, real-valued random variable, positive deterministic scale; no probability, filtration, oracle, convexity, smoothness, topology, or finite-dimensional assumptions
-- portable call pattern: stochastic accelerated primal-dual, stochastic mirror-prox, stochastic mirror descent, and martingale MGF proofs assume conditional light-tail control of `exp (X^2 / sigma^2)` and need `Integrable X μ` before using conditional means or totalized conditional expectations
-- counterargument checked: not paper-local traceability because the statement is a reusable measure-level well-definedness bridge; not a pure wrapper because it composes the packaged conditional-bound integrability projection with a scalar exponential envelope to recover `L1` integrability of the original random variable
-- coverage search: LeanSearch for "if exp of square of real random variable is integrable then the random variable is integrable" found two-sided exponential-moment-to-polynomial-integrability lemmas, not this square-exponential conditional-bound shape; `lean_search_symbols` for "integrable exp sq div sq" found the staged tilt-integrability and scalar envelope lemmas but no `Integrable X μ` consequence
-- minimal hypotheses: replaces SAPD setup fields and indexed zeta/sigma with pointwise `X`, `sigma`, `μ`, and `m`; only measurability of `X`, positivity of `sigma`, and the integrability component of `condExpBound` are used

/-- A square-exponential conditional bound makes the underlying scalar random
variable integrable.

If the packaged conditional bound supplies integrability of
`exp (X^2 / sigma^2)`, then the pointwise envelope
`|X| <= sigma * exp (X^2 / sigma^2)` transfers integrability back to `X`.

Layer: Glue | Gap: Level 1 (scalar integrability from square-exponential light tails)
Proof: project integrability from `condExpBound`, multiply by the positive
  deterministic scale, and dominate `|X|` pointwise using
  `abs_le_pos_mul_exp_sq_div_sq`.
Source: Mathlib Bochner integrability monotonicity and real exponential
  domination APIs
Used in: stochastic optimization light-tail martingale proofs before
  conditional mean-zero and conditional MGF steps
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/assumptions/8
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
theorem integrable_of_exp_sq_condExp_bound
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : @Measure Ω mΩ} {m : MeasurableSpace Ω}
    {X bound : Ω → ℝ} {sigma : ℝ}
    (hX_meas : @Measurable Ω ℝ mΩ (borel ℝ) X)
    (hsigma : 0 < sigma)
    (hbound :
      condExpBound μ m
        (fun ω => Real.exp ((X ω) ^ 2 / sigma ^ 2)) bound) :
    Integrable X μ := by
  have hexp_int :
      Integrable (fun ω => Real.exp ((X ω) ^ 2 / sigma ^ 2)) μ :=
    condExpBound.integrable hbound
  have hdom_int :
      Integrable (fun ω => sigma * Real.exp ((X ω) ^ 2 / sigma ^ 2)) μ :=
    hexp_int.const_mul sigma
  refine hdom_int.mono' hX_meas.aestronglyMeasurable ?_
  filter_upwards [] with ω
  simpa [Real.norm_eq_abs] using
    abs_le_pos_mul_exp_sq_div_sq (X ω) sigma hsigma


open MeasureTheory

-- Generalization plan (G0):
-- concept/name: exponential-tilt integrability from exponential-square light-tail control; orig was lemma_4_1_exp_tilt_integrable_of_cond_light_tail
-- generality used: arbitrary measurable sample space, arbitrary measure, arbitrary conditioning measurable space, real-valued random variable, nonzero deterministic scale, and fixed tilt; no probability, filtration, oracle, convexity, smoothness, topology, or finite-dimensional assumptions
-- portable call pattern: stochastic mirror descent, stochastic accelerated primal-dual, stochastic mirror-prox, and SGD martingale light-tail proofs assume conditional exponential-square control and then need every one-step exponential tilt to be integrable before applying conditional-expectation monotonicity or MGF bounds
-- counterargument checked: not paper-local traceability because this is the reusable measure-level consequence of a named conditional light-tail package; not a duplicate of Mathlib sub-Gaussian APIs, which assume MGF bounds rather than derive tilt integrability from an exponential-square conditional expectation bound
-- coverage search: rg over SOptLib/Staging/Algorithms found the scalar completed-square inequality and conditional-MGF adapters, but no integrability consequence from `condExpBound`; LeanSearch for "If exp of X squared over sigma squared is integrable then exp theta times X is integrable" returned exponential-domain lemmas such as `ProbabilityTheory.integrable_exp_mul_of_abs_le`, but no square-exponential domination bridge
-- minimal hypotheses: the conditional bound is used only for its integrability projection, the scale only needs `sigma ≠ 0`, and `Measurable X` is kept to prove measurability of the tilted exponential

/-- A conditional exponential-square bound makes every linear exponential tilt
integrable.

If `exp (X^2 / sigma^2)` is packaged in a conditional-expectation bound, then
its integrability component and a completed-square domination imply
integrability of `exp (theta * X)` for any real tilt.

Layer: Glue | Gap: Level 1 (exponential tilt integrability from square-exponential control)
Proof: project integrability from `condExpBound`, multiply by the deterministic
  completed-square constant, and dominate the tilted exponential pointwise using
  `exp_mul_le_exp_sq_div_mul_const`.
Source: Mathlib Bochner integrability monotonicity and real exponential
  completed-square arithmetic
Used in: stochastic optimization light-tail martingale proofs before one-step
  conditional MGF monotonicity
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/key_lemmas/2/proof/0
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
theorem integrable_exp_tilt_of_exp_sq_condExp_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ : @Measure Ω mΩ} {mCond : MeasurableSpace Ω}
    {X : Ω → ℝ} {bound : Ω → ℝ} {sigma theta : ℝ}
    (hX_meas : @Measurable Ω ℝ mΩ (borel ℝ) X)
    (hsigma : 0 < sigma)
    (hbound :
      condExpBound μ mCond
        (fun ω => Real.exp ((X ω) ^ 2 / sigma ^ 2))
        bound) :
    Integrable (fun ω => Real.exp (theta * X ω)) μ := by
  have hsq_int :
      Integrable (fun ω => Real.exp ((X ω) ^ 2 / sigma ^ 2)) μ :=
    condExpBound.integrable hbound
  have hdom_int :
      Integrable
        (fun ω =>
          Real.exp ((theta ^ 2 * sigma ^ 2) / 4) *
            Real.exp ((X ω) ^ 2 / sigma ^ 2)) μ :=
    hsq_int.const_mul (Real.exp ((theta ^ 2 * sigma ^ 2) / 4))
  have htilt_meas :
      @Measurable Ω ℝ mΩ (borel ℝ) (fun ω => Real.exp (theta * X ω)) :=
    (measurable_const.mul hX_meas).exp
  refine hdom_int.mono' htilt_meas.aestronglyMeasurable ?_
  filter_upwards [] with ω
  have hle :
      Real.exp (theta * X ω) ≤
        Real.exp ((theta ^ 2 * sigma ^ 2) / 4) *
          Real.exp ((X ω) ^ 2 / sigma ^ 2) :=
    exp_mul_le_exp_sq_div_mul_const (X ω) sigma theta hsigma
  have hright_nonneg :
      0 ≤ Real.exp ((theta ^ 2 * sigma ^ 2) / 4) *
        Real.exp ((X ω) ^ 2 / sigma ^ 2) :=
    mul_nonneg (le_of_lt (Real.exp_pos _)) (le_of_lt (Real.exp_pos _))
  simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_of_nonneg hright_nonneg]
    using hle


open MeasureTheory ProbabilityTheory

-- Generalization plan (G0):
-- concept/name: conditional small-tilt exponential MGF bound from mean-zero cancellation and a square-exponential conditional bound; orig was lemma_4_1_one_step_condExp_mgf_ae_small_branch
-- generality used: arbitrary measurable sample space, arbitrary measure, conditioning measurable space, real random variable, positive variance scale, and deterministic tilt; no filtration, oracle, algorithm state, convexity, smoothness, or finite-dimensional assumptions
-- portable call pattern: stochastic accelerated primal-dual, stochastic mirror descent, stochastic mirror-prox, and light-tail SGD martingale proofs use the same step after proving conditional mean zero and a conditional square-exponential bound for the martingale increment
-- counterargument checked: not paper-local traceability because it packages the reusable conditional-expectation transport of the scalar small-tilt MGF inequality; not a duplicate of Mathlib `HasCondSubgaussianMGF.ae_condExp_le`, which consumes an already-built sub-Gaussian object rather than deriving the small branch from mean-zero and square-exponential light-tail hypotheses
-- coverage search: LeanSearch query "conditional expectation exponential moment small tilt mean zero square exponential bound" returned bounded-support and `HasCondSubgaussianMGF` API, not this derivation; SOptLib/Staging searches found scalar exponential envelopes, `condExpBound`, and exponential rescaling lemmas, but no theorem combining `condExp_mono`, conditional additivity, conditional scalar pull-out, and mean-zero cancellation
-- minimal hypotheses: replaces SAPD setup fields and indexed filtration by `μ`, `m`, `X`, `sigma`, and `theta`; replaces the paper light-tail package by the single used packaged bound at `a = 9*(theta*sigma)^2/16`; keeps only integrability hypotheses needed by Mathlib conditional-expectation monotonicity and linearity

/-- A small-tilt conditional exponential moment is controlled by a
square-exponential conditional bound after conditional mean-zero cancellation.

If `|theta * sigma| < 4/3`, `E[X | m] = 0` a.e., and the conditional
expectation of
`exp (a * X^2 / sigma^2)` is bounded by `exp a` for
`a = 9 * (theta * sigma)^2 / 16`, then
`E[exp (theta * X) | m] <= exp (3 * theta^2 * sigma^2 / 4)` a.e.

Layer: Glue | Gap: Level 1 (conditional small-tilt MGF transport)
Proof: apply the scalar envelope `exp (r*x) <= r*x + exp (9*r^2*x^2/16)`,
  push it through conditional-expectation monotonicity, split and pull out the
  linear term with conditional linearity, cancel it by the mean-zero hypothesis,
  and compare the scaled-square bound with the target constant.
Source: Mathlib conditional expectation linearity/monotonicity APIs and real
  exponential quadratic-envelope inequalities
Used in: stochastic optimization light-tail martingale proofs deriving one-step
  conditional MGF bounds from mean-zero oracle noise and square-exponential tails
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/key_lemmas/5/proof
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
theorem condExp_exp_linear_le_small_branch_of_mean_zero_exp_sq_bound
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω}
    {m : MeasurableSpace Ω}
    {X : Ω → ℝ} {sigma theta : ℝ}
    (hsigma : 0 < sigma)
    (hsmall : ¬ (4 / 3 : ℝ) ≤ |theta * sigma|)
    (hX_int : Integrable X μ)
    (htilt_int : Integrable (fun ω => Real.exp (theta * X ω)) μ)
    (hcond_mean_zero : μ[X | m] =ᵐ[μ] 0)
    (hcond_scaled_sq_bound :
      condExpBound μ m
        (fun ω =>
          Real.exp (((9 * (theta * sigma) ^ 2) / 16) * ((X ω) ^ 2 / sigma ^ 2)))
        (fun _ => Real.exp ((9 * (theta * sigma) ^ 2) / 16))) :
    μ[fun ω => Real.exp (theta * X ω) | m] ≤ᵐ[μ]
      fun _ => Real.exp (((3 * theta ^ 2) / 4) * sigma ^ 2) := by
  let a : ℝ := (9 * (theta * sigma) ^ 2) / 16
  let G : Ω → ℝ := fun ω => Real.exp (a * ((X ω) ^ 2 / sigma ^ 2))
  have hsmall_lt : |theta * sigma| < (4 / 3 : ℝ) := lt_of_not_ge hsmall
  have hsmall_le : |theta * sigma| ≤ (4 / 3 : ℝ) := le_of_lt hsmall_lt
  have hsquare_le : (theta * sigma) ^ 2 ≤ (4 / 3 : ℝ) ^ 2 := by
    rw [sq_le_sq]
    simpa [abs_of_nonneg (by norm_num : 0 ≤ (4 / 3 : ℝ))] using hsmall_le
  have ha0 : 0 ≤ a := by
    dsimp [a]
    positivity
  have ha1 : a ≤ 1 := by
    dsimp [a]
    nlinarith
  have hscaled_bound :
      condExpBound μ m G (fun _ => Real.exp a) := by
    simpa [G, a] using hcond_scaled_sq_bound
  have hG_int : Integrable G μ :=
    condExpBound.integrable hscaled_bound
  have hlin_int : Integrable (fun ω => theta * X ω) μ := by
    simpa using hX_int.const_mul theta
  have hsum_int : Integrable (fun ω => theta * X ω + G ω) μ :=
    hlin_int.add hG_int
  have hpoint :
      (fun ω => Real.exp (theta * X ω)) ≤ᵐ[μ]
        fun ω => theta * X ω + G ω := by
    filter_upwards [] with ω
    have hscalar :=
      Real.exp_mul_le_mul_add_exp_nine_sixteen_mul_sq_mul_sq
        (theta * sigma) (X ω / sigma)
    have hlin :
        (theta * sigma) * (X ω / sigma) = theta * X ω := by
      field_simp [ne_of_gt hsigma]
    have hsq :
        (X ω / sigma) ^ 2 = (X ω) ^ 2 / sigma ^ 2 := by
      field_simp [ne_of_gt hsigma]
    have hcoef :
        ((9 * (theta * sigma) ^ 2) / 16) * (X ω / sigma) ^ 2 =
          a * ((X ω) ^ 2 / sigma ^ 2) := by
      rw [hsq]
    simpa [G, hlin, hcoef] using hscalar
  have hmono :
      μ[fun ω => Real.exp (theta * X ω) | m] ≤ᵐ[μ]
        μ[fun ω => theta * X ω + G ω | m] :=
    MeasureTheory.condExp_mono htilt_int hsum_int hpoint
  have hadd :
      μ[fun ω => theta * X ω + G ω | m] =ᵐ[μ]
        μ[fun ω => theta * X ω | m] + μ[G | m] := by
    simpa using MeasureTheory.condExp_add hlin_int hG_int m
  have hlin_pull :
      μ[fun ω => theta * X ω | m] =ᵐ[μ] fun ω => theta * μ[X | m] ω := by
    simpa [Pi.smul_apply, smul_eq_mul] using
      MeasureTheory.condExp_smul (μ := μ) theta X m
  have hscaled_ae := condExpBound.ae_le hscaled_bound
  have hexp_a_le_target :
      Real.exp a ≤ Real.exp (((3 * theta ^ 2) / 4) * sigma ^ 2) := by
    apply Real.exp_le_exp.mpr
    dsimp [a]
    nlinarith [sq_nonneg (theta * sigma)]
  filter_upwards [hmono, hadd, hlin_pull, hcond_mean_zero, hscaled_ae] with
    ω hmonoω haddω hlinω hmeanω hscaledω
  calc
    μ[fun ω => Real.exp (theta * X ω) | m] ω
        ≤ μ[fun ω => theta * X ω + G ω | m] ω := hmonoω
    _ = μ[fun ω => theta * X ω | m] ω + μ[G | m] ω := by
          simpa using haddω
    _ = theta * μ[X | m] ω + μ[G | m] ω := by
          rw [hlinω]
    _ = μ[G | m] ω := by
          rw [hmeanω]
          simp
    _ ≤ Real.exp a := hscaledω
    _ ≤ Real.exp (((3 * theta ^ 2) / 4) * sigma ^ 2) := hexp_a_le_target


open MeasureTheory ProbabilityTheory

-- Generalization plan (G0):
-- concept/name: conditional large-tilt exponential MGF bound from a square-exponential conditional bound; orig was lemma_4_1_one_step_condExp_mgf_ae_large_branch
-- generality used: arbitrary measurable sample space, arbitrary measure, conditioning measurable space, real random variable, positive variance scale, and deterministic tilt; no filtration, oracle, algorithm state, convexity, smoothness, or finite-dimensional assumptions
-- portable call pattern: stochastic accelerated primal-dual, stochastic mirror descent, stochastic mirror-prox, and light-tail SGD martingale proofs use the same large-tilt step after proving a conditional square-exponential bound for the martingale increment
-- counterargument checked: not paper-local traceability because it packages the reusable conditional-expectation transport of the scalar large-tilt MGF inequality; not a duplicate of Mathlib `HasCondSubgaussianMGF.ae_condExp_le`, which consumes an already-built sub-Gaussian object rather than deriving the large branch from square-exponential light-tail hypotheses
-- coverage search: LeanSearch query "conditional expectation exponential moment large tilt square exponential bound" returned bounded-support and `HasCondSubgaussianMGF` API, not this derivation; SOptLib/Staging searches found scalar exponential envelopes, `condExpBound`, and exponential rescaling lemmas, but no theorem combining `condExp_mono`, conditional scalar pull-out, and large-branch constant absorption
-- minimal hypotheses: replaces SAPD setup fields and indexed filtration by `μ`, `m`, `X`, `sigma`, and `theta`; replaces the paper light-tail package by the single used packaged bound at exponent `2/3`; keeps only integrability hypotheses needed by Mathlib conditional-expectation monotonicity and scalar pull-out

/-- A large-tilt conditional exponential moment is controlled by a
square-exponential conditional bound.

If `4/3 <= |theta * sigma|` and the conditional expectation of
`exp ((2/3) * X^2 / sigma^2)` is bounded by `exp (2/3)`, then
`E[exp (theta * X) | m] <= exp (3 * theta^2 * sigma^2 / 4)` a.e.

Layer: Glue | Gap: Level 1 (conditional large-tilt MGF transport)
Proof: apply the scalar envelope
  `exp (r*x) <= exp (3*r^2/8) * exp ((2/3)*x^2)`, push it through
  conditional-expectation monotonicity, pull out the deterministic scalar, and
  absorb the residual `exp (2/3)` using the large-tilt hypothesis.
Source: Mathlib conditional expectation monotonicity/scalar APIs and real
  exponential weighted-Young inequalities
Used in: stochastic optimization light-tail martingale proofs deriving one-step
  conditional MGF bounds from square-exponential tails in the large-tilt branch
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/key_lemmas/5/proof
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
theorem condExp_exp_linear_le_large_branch_of_exp_sq_condExp_bound
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω}
    {m : MeasurableSpace Ω}
    {X : Ω → ℝ} {sigma theta : ℝ}
    (hsigma : 0 < sigma)
    (htilt_int : Integrable (fun ω => Real.exp (theta * X ω)) μ)
    (hcond_scaled_sq_bound :
      condExpBound μ m
        (fun ω => Real.exp ((2 / 3 : ℝ) * ((X ω) ^ 2 / sigma ^ 2)))
        (fun _ => Real.exp (2 / 3 : ℝ)))
    (hlarge : (4 / 3 : ℝ) ≤ |theta * sigma|) :
    μ[fun ω => Real.exp (theta * X ω) | m] ≤ᵐ[μ]
      fun _ => Real.exp (((3 * theta ^ 2) / 4) * sigma ^ 2) := by
  let C : ℝ := Real.exp ((3 * (theta * sigma) ^ 2) / 8)
  let G : Ω → ℝ :=
    fun ω => Real.exp ((2 / 3 : ℝ) * ((X ω) ^ 2 / sigma ^ 2))
  have hscaled_bound :
      condExpBound μ m G (fun _ => Real.exp (2 / 3 : ℝ)) := by
    simpa [G] using hcond_scaled_sq_bound
  have hG_int : Integrable G μ :=
    condExpBound.integrable hscaled_bound
  have hCG_int : Integrable (fun ω => C • G ω) μ :=
    hG_int.smul C
  have hpoint :
      (fun ω => Real.exp (theta * X ω)) ≤ᵐ[μ] fun ω => C • G ω := by
    filter_upwards [] with ω
    have hscalar :=
      exp_mul_le_exp_three_eighth_sq_mul_exp_two_thirds_sq
        (theta * sigma) (X ω / sigma)
    have hlin :
        (theta * sigma) * (X ω / sigma) = theta * X ω := by
      field_simp [ne_of_gt hsigma]
    have hsq :
        (X ω / sigma) ^ 2 = (X ω) ^ 2 / sigma ^ 2 := by
      field_simp [ne_of_gt hsigma]
    simpa [C, G, hlin, hsq] using hscalar
  have hmono :
      μ[fun ω => Real.exp (theta * X ω) | m] ≤ᵐ[μ]
        μ[fun ω => C • G ω | m] :=
    MeasureTheory.condExp_mono htilt_int hCG_int hpoint
  have hpull :
      μ[fun ω => C • G ω | m] =ᵐ[μ]
        fun ω => C • μ[G | m] ω := by
    simpa using MeasureTheory.condExp_smul (μ := μ) C G m
  have hscaled_ae := condExpBound.ae_le hscaled_bound
  have hconst :
      C * Real.exp (2 / 3 : ℝ) ≤
        Real.exp (((3 * theta ^ 2) / 4) * sigma ^ 2) := by
    have hlarge_const :
        Real.exp ((3 * (theta * sigma) ^ 2) / 8) * Real.exp (2 / 3 : ℝ) ≤
          Real.exp ((3 * (theta * sigma) ^ 2) / 4) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hsq_abs : |theta * sigma| ^ 2 = (theta * sigma) ^ 2 := by
        simpa using sq_abs (theta * sigma)
      have hnonneg : 0 ≤ |theta * sigma| := abs_nonneg _
      nlinarith [sq_nonneg (|theta * sigma| - (4 / 3 : ℝ))]
    have hcoef :
        (3 * (theta * sigma) ^ 2) / 4 =
          ((3 * theta ^ 2) / 4) * sigma ^ 2 := by
      ring
    simpa [C, hcoef] using hlarge_const
  filter_upwards [hmono, hpull, hscaled_ae] with ω hmonoω hpullω hscaledω
  calc
    μ[fun ω => Real.exp (theta * X ω) | m] ω
        ≤ μ[fun ω => C • G ω | m] ω := hmonoω
    _ = C * μ[G | m] ω := by
          simpa using hpullω
    _ ≤ C * Real.exp (2 / 3 : ℝ) := by
          exact mul_le_mul_of_nonneg_left hscaledω (le_of_lt (Real.exp_pos _))
    _ ≤ Real.exp (((3 * theta ^ 2) / 4) * sigma ^ 2) := hconst


open MeasureTheory ProbabilityTheory
open scoped NNReal

-- Generalization plan (G0):
-- concept/name: conditional-expectation rational MGF bounds imply kernel sub-Gaussian MGF; orig was condExp_fixed_rat_bounds_to_kernel_hasSubgaussianMGF
-- generality used: arbitrary standard Borel measurable space, finite measure, sub-sigma-algebra, real random variable, and NNReal variance proxy; no algorithm setup, filtration index, convexity, smoothness, or oracle fields
-- portable call pattern: martingale/light-tail proofs in stochastic mirror descent, stochastic accelerated primal-dual, and stochastic mirror-prox first prove rational conditional MGF bounds, then need Mathlib's kernel-based conditional sub-Gaussian API
-- counterargument checked: not paper-local traceability because the statement is exactly the reusable trim/condExpKernel bridge from conditional expectations to Kernel.HasSubgaussianMGF; not a pure wrapper because it composes rational densification, trim transfer, and the conditional-expectation kernel representation
-- coverage search: searched "Kernel.HasSubgaussianMGF of_rat condExpKernel trim", "condExp_ae_eq_trim_integral_condExpKernel", and SOptLib/catalog sub-Gaussian tokens; Mathlib has Kernel.HasSubgaussianMGF.of_rat and condExpKernel lemmas separately, but no combined conditional-expectation rational-MGF bridge
-- minimal hypotheses: replaces SAPD fixed-time objects with pointwise X, μ, m, hm, c, all-real tilt integrability, and rational conditional expectation bounds; StandardBorelSpace and IsFiniteMeasure are required by condExpKernel

namespace ProbabilityTheory

/-- Rational conditional moment-generating-function bounds give a kernel
sub-Gaussian MGF bound for the conditional-expectation kernel.

If every exponential tilt of `X` is integrable under `μ`, and the conditional
expectation of each rational tilt is bounded by the sub-Gaussian envelope, then
`X` is sub-Gaussian with respect to `condExpKernel μ m` and `μ.trim hm`.

Layer: Glue | Gap: Level 1 (conditional MGF to kernel sub-Gaussian bridge)
Proof: use `Kernel.HasSubgaussianMGF.of_rat`; transfer the rational conditional
  expectation bound to `μ.trim hm`, then rewrite conditional expectations as
  integrals against `condExpKernel`.
Source: Mathlib conditional expectation kernels and sub-Gaussian MGF APIs
Used in: stochastic optimization martingale light-tail proofs converting
  scalar conditional MGF estimates into conditional sub-Gaussian increments
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/key_lemmas/lemma_4_1
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine
  Learning, stochastic accelerated primal-dual -/
theorem Kernel.hasSubgaussianMGF_of_condExp_rat_mgf_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] [hSB : StandardBorelSpace Ω]
    {μ : @Measure Ω mΩ} [hfin : IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {X : Ω → ℝ} {c : ℝ≥0}
    (h_int : ∀ theta : ℝ, Integrable (fun ω => Real.exp (theta * X ω)) μ)
    (h_rat :
      ∀ q : ℚ,
        μ[fun ω => Real.exp ((q : ℝ) * X ω) | m] ≤ᵐ[μ]
          fun _ => Real.exp ((c : ℝ) * (q : ℝ) ^ 2 / 2)) :
    @HasCondSubgaussianMGF Ω m mΩ hm hSB X c μ hfin := by
  change @Kernel.HasSubgaussianMGF Ω Ω mΩ m X c
    (@condExpKernel Ω mΩ hSB μ hfin m) (μ.trim hm)
  refine Kernel.HasSubgaussianMGF.of_rat ?h_int ?h_rat
  · intro theta
    simpa [condExpKernel_comp_trim] using h_int theta
  · intro q
    have hfixed_trim :
        μ[fun ω => Real.exp ((q : ℝ) * X ω) | m] ≤ᵐ[μ.trim hm]
          fun _ => Real.exp ((c : ℝ) * (q : ℝ) ^ 2 / 2) := by
      exact
        StronglyMeasurable.ae_le_trim_of_stronglyMeasurable hm
          (stronglyMeasurable_condExp (μ := μ) (m := m)
            (f := fun ω => Real.exp ((q : ℝ) * X ω)))
          stronglyMeasurable_const (h_rat q)
    have hkernel_eq :
        μ[fun ω => Real.exp ((q : ℝ) * X ω) | m] =ᵐ[μ.trim hm]
          fun ω =>
            ∫ y, Real.exp ((q : ℝ) * X y) ∂
              (@condExpKernel Ω mΩ hSB μ hfin m) ω :=
      @condExp_ae_eq_trim_integral_condExpKernel Ω ℝ m mΩ hSB μ hfin
        inferInstance (fun ω => Real.exp ((q : ℝ) * X ω))
        inferInstance inferInstance hm (h_int (q : ℝ))
    filter_upwards [hfixed_trim, hkernel_eq] with ω hle heq
    calc
      mgf X ((@condExpKernel Ω mΩ hSB μ hfin m) ω) (q : ℝ)
          = μ[fun ω => Real.exp ((q : ℝ) * X ω) | m] ω := by
            simpa [mgf] using heq.symm
      _ ≤ Real.exp ((c : ℝ) * (q : ℝ) ^ 2 / 2) := hle

end ProbabilityTheory


open MeasureTheory ProbabilityTheory
open scoped NNReal

-- Generalization plan (G0):
-- concept/name: conditional sub-Gaussian MGF from conditional mean zero and square-exponential light-tail control; orig was Lemma41CondSubgaussianMGF_of_source_light_tail
-- generality used: arbitrary standard Borel measurable sample space, arbitrary finite measure, arbitrary conditioning measurable space below the ambient sigma-algebra, real random variable, and positive deterministic scale; no filtration, oracle, iterate, convexity, smoothness, or finite-dimensional assumptions
-- portable call pattern: stochastic accelerated primal-dual, stochastic mirror descent, stochastic mirror-prox, and light-tail SGD martingale proofs prove conditional mean-zero increments plus a conditional bound on `exp (X^2/sigma^2)` and then need Mathlib's `HasCondSubgaussianMGF` API for finite-sum concentration
-- counterargument checked: not paper-local traceability because the statement is paper-free and targets Mathlib's canonical conditional sub-Gaussian object; not a duplicate of the small/large branch lemmas or kernel bridge because it composes those reusable steps from the raw light-tail hypotheses future algorithms naturally assume
-- coverage search: LeanSearch for "conditional mean zero square exponential moment implies conditional subgaussian moment generating function" found Mathlib `HasCondSubgaussianMGF` constructors/API and bounded-support Hoeffding lemmas, but no square-exponential light-tail derivation; SOptLib/Staging searches found the component branch, integrability, rescaling, and kernel bridge lemmas but no end-to-end theorem with this statement shape
-- minimal hypotheses: replaces SAPD setup fields and indexed filtration by `μ`, `m`, `hm`, `X`, and `sigma`; keeps `Measurable X` to derive tilt integrability, `0 < sigma` for normalization, finite measure and standard Borel assumptions for `condExpKernel`, and a packaged `condExpBound` for the unit square-exponential conditional bound

/-- Conditional mean-zero and a square-exponential conditional bound give a
conditional sub-Gaussian MGF bound.

If `E[X | m] = 0` a.e. and `E[exp (X^2/sigma^2) | m] <= exp 1` with the
integrability carried by `condExpBound`, then `X` has conditional
sub-Gaussian MGF proxy `(3/2) * sigma^2`.

Layer: Glue | Gap: Level 2 (conditional light-tail to sub-Gaussian MGF)
Proof: derive `L¹` and tilted exponential integrability from the
  square-exponential bound, rescale the square-exponential conditional bound
  for subunit coefficients, split rational tilts into small and large branches,
  and apply the conditional-expectation-to-kernel sub-Gaussian bridge.
Source: Mathlib conditional expectation kernels, sub-Gaussian MGF APIs, and
  real exponential square-domination inequalities
Used in: stochastic optimization light-tail martingale proofs converting
  conditional mean-zero oracle noise with square-exponential tails into
  one-step conditional sub-Gaussian increments
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/key_lemmas/5/proof
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
theorem hasCondSubgaussianMGF_of_condExp_mean_zero_and_exp_sq_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] [hSB : StandardBorelSpace Ω]
    {μ : @Measure Ω mΩ} [hfin : IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {X : Ω → ℝ} {sigma : ℝ}
    (hX_meas : @Measurable Ω ℝ mΩ (borel ℝ) X)
    (hsigma : 0 < sigma)
    (hcond_mean_zero : μ[X | m] =ᵐ[μ] 0)
    (hcond_exp_sq_bound :
      condExpBound μ m
        (fun ω => Real.exp ((X ω) ^ 2 / sigma ^ 2))
        (fun _ => Real.exp 1)) :
    @HasCondSubgaussianMGF Ω m mΩ hm hSB X
      ⟨((3 : ℝ) / 2) * sigma ^ 2, by positivity⟩ μ
      hfin := by
  have hX_aesm : @AEStronglyMeasurable Ω ℝ _ mΩ mΩ X μ :=
    @Measurable.aestronglyMeasurable Ω ℝ _ mΩ mΩ μ X _ _ _ _ hX_meas
  have hX_int : Integrable X μ :=
    integrable_of_exp_sq_condExp_bound
      (μ := μ) (m := m) (X := X) (sigma := sigma)
      hX_meas hsigma hcond_exp_sq_bound
  have htilt_int :
      ∀ theta : ℝ, Integrable (fun ω => Real.exp (theta * X ω)) μ := by
    intro theta
    exact
      @integrable_exp_tilt_of_exp_sq_condExp_bound Ω mΩ μ m X (fun _ => Real.exp 1)
        sigma theta hX_meas hsigma hcond_exp_sq_bound
  have hcond_scaled_sq_bound :
      ∀ a : ℝ, 0 ≤ a → a ≤ 1 →
        condExpBound μ m
          (fun ω => Real.exp (a * ((X ω) ^ 2 / sigma ^ 2)))
          (fun _ => Real.exp a) := by
    intro a ha0 ha1
    exact
      @condExpBound_exp_mul_of_condExpBound_exp Ω mΩ mΩ μ hfin m hm
        (fun ω => (X ω) ^ 2 / sigma ^ 2) a ha0 ha1 hcond_exp_sq_bound
  have hrat :
      ∀ q : ℚ,
        μ[fun ω => Real.exp ((q : ℝ) * X ω) | m] ≤ᵐ[μ]
          fun _ =>
            Real.exp ((((3 : ℝ) / 2) * sigma ^ 2) * (q : ℝ) ^ 2 / 2) := by
    intro q
    have hfixed :
        μ[fun ω => Real.exp ((q : ℝ) * X ω) | m] ≤ᵐ[μ]
          fun _ => Real.exp ((((3 * (q : ℝ) ^ 2) / 4) * sigma ^ 2)) := by
      by_cases hlarge : (4 / 3 : ℝ) ≤ |(q : ℝ) * sigma|
      · simpa [mul_assoc, mul_left_comm, mul_comm] using
          @condExp_exp_linear_le_large_branch_of_exp_sq_condExp_bound
            Ω mΩ μ m X sigma (q : ℝ)
            hsigma (htilt_int (q : ℝ))
            (by
              simpa using
                hcond_scaled_sq_bound (2 / 3) (by norm_num) (by norm_num))
            hlarge
      · simpa [mul_assoc, mul_left_comm, mul_comm] using
          @condExp_exp_linear_le_small_branch_of_mean_zero_exp_sq_bound
            Ω mΩ μ m X sigma (q : ℝ)
            hsigma hlarge hX_int (htilt_int (q : ℝ)) hcond_mean_zero
            (by
              simpa using
                hcond_scaled_sq_bound ((9 * ((q : ℝ) * sigma) ^ 2) / 16)
                  (by positivity) (by
                    have hsmall_lt : |(q : ℝ) * sigma| < (4 / 3 : ℝ) :=
                      lt_of_not_ge hlarge
                    have hsmall_le : |(q : ℝ) * sigma| ≤ (4 / 3 : ℝ) :=
                      le_of_lt hsmall_lt
                    have hsquare_le :
                        ((q : ℝ) * sigma) ^ 2 ≤ (4 / 3 : ℝ) ^ 2 := by
                      rw [sq_le_sq]
                      simpa [abs_of_nonneg (by norm_num : 0 ≤ (4 / 3 : ℝ))]
                        using hsmall_le
                    nlinarith))
    filter_upwards [hfixed] with ω hle
    calc
      μ[fun ω => Real.exp ((q : ℝ) * X ω) | m] ω
          ≤ Real.exp ((((3 * (q : ℝ) ^ 2) / 4) * sigma ^ 2)) := hle
      _ = Real.exp ((((3 : ℝ) / 2) * sigma ^ 2) * (q : ℝ) ^ 2 / 2) := by
            congr 1
            ring
  exact
    @Kernel.hasSubgaussianMGF_of_condExp_rat_mgf_le Ω mΩ hSB μ hfin m hm X
      ⟨((3 : ℝ) / 2) * sigma ^ 2, by positivity⟩ htilt_int hrat

open MeasureTheory ProbabilityTheory

-- Generalization plan (G0):
-- concept/name: finite family of one-step conditional MGF bounds from conditional sub-Gaussian increments; orig was Lemma41OneStepConditionalMGFBound
-- generality used: arbitrary standard Borel measurable space, finite measure, Mathlib filtration, real-valued increments, deterministic real scale schedule, horizon, and tilt; no optimization setup, oracle, convexity, or smoothness fields
-- portable call pattern: stochastic mirror descent, stochastic accelerated primal-dual, and stochastic mirror-prox light-tail martingale proofs derive per-step `HasCondSubgaussianMGF` increments and then need explicit integrability plus conditional-expectation exponential bounds for a finite tower or supermartingale induction
-- counterargument checked: not merely paper-local traceability because the statement converts Mathlib's canonical conditional sub-Gaussian object into the explicit one-step conditional MGF family used by several martingale/tail arguments; not a raw duplicate because Mathlib supplies the atomic integrability and a.e. bound lemmas separately, not the indexed finite-family coefficient-normalized adapter
-- coverage search: LeanSearch for "conditional subgaussian moment generating function integrable exponential conditional expectation bound" found `HasCondSubgaussianMGF.integrable_exp_mul` and `HasCondSubgaussianMGF.ae_condExp_le`; SOptLib/catalog search found the rational-condExp-to-kernel bridge but no theorem packaging a finite family of one-step conditional MGF bounds from `HasCondSubgaussianMGF`
-- minimal hypotheses: keeps only `StandardBorelSpace` and `IsFiniteMeasure` required by Mathlib's conditional sub-Gaussian API; coefficient is the concrete `3 / 2 * sigma t ^ 2` proxy used to yield the normalized `3 * theta ^ 2 / 4 * sigma t ^ 2` envelope

/-- Conditional sub-Gaussian increments give finite one-step conditional MGF bounds.

For a real process indexed over a finite interval, if each increment is
conditionally sub-Gaussian with variance proxy `(3 / 2) * sigma t ^ 2` with
respect to the previous filtration level, then every fixed tilt has the
corresponding integrability and conditional exponential moment bound.

Layer: Glue | Gap: Level 1 (finite conditional sub-Gaussian MGF adapter)
Proof: apply Mathlib's `HasCondSubgaussianMGF.integrable_exp_mul` and
  `HasCondSubgaussianMGF.ae_condExp_le` pointwise, then normalize the scalar
  coefficient by ring arithmetic.
Source: Mathlib conditional sub-Gaussian MGF and filtration APIs
Used in: stochastic optimization light-tail martingale proofs supplying
  one-step exponential-supermartingale bounds for finite-horizon tail estimates
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/assumptions/8
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine
  Learning, stochastic accelerated primal-dual -/
theorem OneStepConditionalMGFBound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {μ : @Measure Ω mΩ} [IsFiniteMeasure μ]
    (filt : Filtration ℕ mΩ)
    (zeta : ℕ → Ω → ℝ) (sigma : ℕ → ℝ) (N : ℕ) (theta : ℝ)
    (hsub :
      ∀ t, t ∈ Finset.Icc 1 N →
        HasCondSubgaussianMGF
          (filt.seq (t - 1))
          (filt.le (t - 1))
          (zeta t)
          ⟨((3 : ℝ) / 2) * sigma t ^ 2, by positivity⟩
          μ) :
    ∀ t, t ∈ Finset.Icc 1 N →
      Integrable (fun ω => Real.exp (theta * zeta t ω)) μ ∧
        μ[fun ω => Real.exp (theta * zeta t ω) | filt.seq (t - 1)] ≤ᵐ[μ]
          fun _ => Real.exp (((3 * theta ^ 2) / 4) * sigma t ^ 2) := by
  intro t ht
  refine ⟨?_, ?_⟩
  · exact HasCondSubgaussianMGF.integrable_exp_mul (hsub t ht) theta
  · have hae := HasCondSubgaussianMGF.ae_condExp_le (hsub t ht) theta
    filter_upwards [hae] with ω hω
    have hcoef :
        (((3 : ℝ) / 2) * sigma t ^ 2 * theta ^ 2 / 2) =
          ((3 * theta ^ 2) / 4) * sigma t ^ 2 := by
      ring
    simpa [hcoef] using hω


open MeasureTheory ProbabilityTheory

-- Generalization plan (G0):
-- concept/name: one-step conditional MGF bound package from conditional sub-Gaussian increments; orig was Lemma41OneStepConditionalMGFBound_of_condSubgaussian
-- generality used: arbitrary standard Borel measurable space, abstract finite measure, Mathlib filtration, real-valued indexed increments, NNReal variance proxy, finite horizon, and fixed tilt; no optimization setup, objective, oracle, convexity, or smoothness fields
-- portable call pattern: stochastic mirror descent, stochastic accelerated primal-dual, mirror-prox, and variance-reduced martingale tail proofs first prove per-step `HasCondSubgaussianMGF` and then need a packaged one-step conditional exponential-moment bound for tower or supermartingale induction
-- counterargument checked: not paper-local because the theorem only converts Mathlib's canonical conditional sub-Gaussian MGF hypothesis into the reusable `condExpBound` package; not a pure duplicate of `oneStep_condSubgaussianMGF_bound` because that older staging theorem returns an unbundled conjunction while this statement exposes the named conditional-expectation-bound predicate used at call sites
-- coverage search: `rg` and `lean_search_symbols` for `HasCondSubgaussianMGF`, `condExpBound`, and one-step conditional MGF found Mathlib's atomic `integrable_exp_mul`/`ae_condExp_le` and the staged unbundled finite-family adapter, but no packaged `condExpBound` theorem with this statement shape
-- minimal hypotheses: keeps only `StandardBorelSpace` and `IsFiniteMeasure` required by Mathlib's conditional sub-Gaussian API; all stochastic-optimization structure is removed

/-- Conditional sub-Gaussian increments give packaged one-step conditional MGF bounds.

For a finite family of real increments adapted through a filtration, a
pointwise `HasCondSubgaussianMGF` assumption supplies both integrability of the
tilted exponential and the a.e. conditional-expectation upper bound, bundled as
`condExpBound`.

Layer: Glue | Gap: Level 1 (packaged finite conditional sub-Gaussian MGF adapter)
Proof: apply Mathlib's `HasCondSubgaussianMGF.integrable_exp_mul` and
  `HasCondSubgaussianMGF.ae_condExp_le` at each time index, then package the
  two facts as `condExpBound`.
Source: Mathlib conditional sub-Gaussian MGF, filtration, and conditional
  expectation APIs
Used in: stochastic optimization light-tail martingale proofs supplying
  one-step conditional exponential-supermartingale bounds for finite-horizon
  tail estimates
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/assumptions/8
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
theorem oneStepConditionalMGFBound_of_hasCondSubgaussianMGF
    {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {μ : @Measure Ω mΩ} [IsFiniteMeasure μ]
    (filt : Filtration ℕ mΩ)
    (zeta : ℕ → Ω → ℝ) (varianceProxy : ℕ → NNReal) (N : ℕ) (theta : ℝ)
    (hsub :
      ∀ t, t ∈ Finset.Icc 1 N →
        HasCondSubgaussianMGF
          (filt.seq (t - 1))
          (filt.le (t - 1))
          (zeta t)
          (varianceProxy t)
          μ) :
    ∀ t, t ∈ Finset.Icc 1 N →
      condExpBound μ
        (filt.seq (t - 1))
        (fun ω => Real.exp (theta * zeta t ω))
        (fun _ => Real.exp (((varianceProxy t : ℝ) * theta ^ 2) / 2)) := by
  intro t ht
  refine ⟨?_, ?_⟩
  · exact HasCondSubgaussianMGF.integrable_exp_mul (hsub t ht) theta
  · exact HasCondSubgaussianMGF.ae_condExp_le (hsub t ht) theta


open MeasureTheory ProbabilityTheory

-- Generalization plan (G0):
-- concept/name: positive-horizon finite-sum moment-generating-function bound; orig was Lemma41PositiveHorizonMGFBound
-- generality used: arbitrary measurable sample space, abstract measure, real-valued indexed increments, deterministic scale schedule, finite horizon, and tilt; the theorem variants use Mathlib `HasSubgaussianMGF`/`HasCondSubgaussianMGF` and filtrations, with no optimization setup fields
-- portable call pattern: stochastic mirror descent, stochastic accelerated primal-dual, stochastic mirror-prox, and variance-reduced martingale light-tail proofs first assemble conditional sub-Gaussian increments, then need the explicit integrability plus MGF integral bound for a finite exponential-supermartingale or Markov step
-- counterargument checked: the bare formula could be a caller-side expression, so the staging entry includes API theorems from Mathlib sub-Gaussian objects; it is not a duplicate of Mathlib because Mathlib states `HasSubgaussianMGF`, while downstream optimization files often need the explicit integrability/integral pair over a one-based horizon
-- coverage search: LeanSearch for "finite sum conditional subgaussian moment generating function bound" found `HasSubgaussianMGF.sum_of_hasCondSubgaussianMGF`, `HasSubgaussianMGF.mgf_le`, and `HasSubgaussianMGF.integrable_exp_mul`; SOptLib/catalog search found the one-step conditional adapter and kernel bridge but no positive-horizon explicit-MGF-bound adapter
-- minimal hypotheses: the proposition itself has only the measure and formula parameters; the direct adapter needs only `[IsFiniteMeasure μ]`, while the conditional range adapter uses `[StandardBorelSpace Ω]` and `[IsProbabilityMeasure μ]` required by Mathlib's filtration sub-Gaussian sum theorem

/-- The explicit finite-horizon exponential integrability and MGF bound.

For real increments `zeta t`, scale schedule `sigma t`, horizon `N`, and tilt
`theta`, this proposition records the two outputs commonly needed after a
finite sub-Gaussian martingale-sum argument: integrability of the exponential
tilt and the corresponding exponential upper bound on its integral.

Layer: Glue | Concept: MGF
Proof: (definitional construction; canonical finite-horizon MGF-bound predicate)
Source: Mathlib sub-Gaussian moment-generating-function APIs
Used in: stochastic optimization light-tail martingale proofs converting finite
  conditional sub-Gaussian increments into Markov-ready exponential bounds
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/assumptions/8
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine
  Learning, stochastic accelerated primal-dual -/
def PositiveHorizonMGFBound
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (zeta : ℕ → Ω → ℝ) (sigma : ℕ → ℝ) (N : ℕ) (theta : ℝ) :
    Prop :=
  Integrable
      (fun ω =>
        Real.exp
          (theta * Finset.sum (Finset.Icc 1 N) (fun t => zeta t ω)))
      μ ∧
  ∫ ω,
        Real.exp
          (theta * Finset.sum (Finset.Icc 1 N) (fun t => zeta t ω)) ∂μ ≤
      Real.exp
        (((3 * theta ^ 2) / 4) *
          Finset.sum (Finset.Icc 1 N) (fun t => sigma t ^ 2))

/-- The finite-horizon MGF-bound predicate unfolds to its integrability and integral bound.

Layer: Glue | Gap: Level 0 (finite-horizon MGF-bound unfolding)
Proof: by rfl after unfolding `PositiveHorizonMGFBound`.
Source: Mathlib sub-Gaussian moment-generating-function APIs
Used in: stochastic optimization light-tail martingale proofs simplifying named
  finite-horizon MGF-bound goals back to explicit integrability and integral bounds
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/assumptions/8
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine
  Learning, stochastic accelerated primal-dual -/
@[simp] theorem PositiveHorizonMGFBound_def
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (zeta : ℕ → Ω → ℝ) (sigma : ℕ → ℝ) (N : ℕ) (theta : ℝ) :
    PositiveHorizonMGFBound μ zeta sigma N theta ↔
      Integrable
          (fun ω =>
            Real.exp
              (theta * Finset.sum (Finset.Icc 1 N) (fun t => zeta t ω)))
          μ ∧
      ∫ ω,
            Real.exp
              (theta * Finset.sum (Finset.Icc 1 N) (fun t => zeta t ω)) ∂μ ≤
          Real.exp
            (((3 * theta ^ 2) / 4) *
              Finset.sum (Finset.Icc 1 N) (fun t => sigma t ^ 2)) :=
  Iff.rfl

/-- A sub-Gaussian finite sum gives the explicit positive-horizon MGF bound.

If the one-based finite sum of increments is sub-Gaussian with variance proxy
`(3 / 2) * sum sigma^2`, then its exponential tilt is integrable and its MGF is
bounded by the `3 / 4` envelope used in finite-horizon light-tail arguments.

Layer: Glue | Gap: Level 1 (sub-Gaussian sum to explicit MGF bound)
Proof: apply `HasSubgaussianMGF.integrable_exp_mul` and
  `HasSubgaussianMGF.mgf_le`, then normalize the scalar coefficient.
Source: Mathlib sub-Gaussian moment-generating-function APIs
Used in: stochastic optimization light-tail martingale proofs after collapsing
  conditional increments to a finite sub-Gaussian sum
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/assumptions/8
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine
  Learning, stochastic accelerated primal-dual -/
theorem positiveHorizonMGFBound_of_hasSubgaussian_sum
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    (zeta : ℕ → Ω → ℝ) (sigma : ℕ → ℝ) (N : ℕ) (theta : ℝ)
    (hsub :
      HasSubgaussianMGF
        (fun ω => Finset.sum (Finset.Icc 1 N) (fun t => zeta t ω))
        ⟨((3 : ℝ) / 2) * Finset.sum (Finset.Icc 1 N) (fun t => sigma t ^ 2),
          by positivity⟩
        μ) :
    PositiveHorizonMGFBound μ zeta sigma N theta := by
  constructor
  · exact hsub.integrable_exp_mul theta
  · have hmgf := hsub.mgf_le theta
    have hcoef :
        theta ^ 2 *
              (((3 : ℝ) / 2) *
                Finset.sum (Finset.Icc 1 N) (fun t => sigma t ^ 2)) / 2 =
          theta ^ 2 * 3 / 4 *
            Finset.sum (Finset.Icc 1 N) (fun t => sigma t ^ 2) := by
      ring
    simpa [PositiveHorizonMGFBound, mgf, hcoef, mul_comm, mul_left_comm, mul_assoc] using
      hmgf

/-- Conditional sub-Gaussian increments give the explicit one-based horizon MGF bound.

This adapts Mathlib's zero-based `range` theorem for filtered conditional
sub-Gaussian sums to a caller-specified one-based `Icc 1 N` sum. The equalities
`hY_sum` and `hcY_sum` are the only indexing bridge; the probabilistic content
comes from Mathlib's finite conditional sub-Gaussian sum theorem.

Layer: Glue | Gap: Level 1 (conditional sub-Gaussian range to one-based MGF bound)
Proof: use `HasSubgaussianMGF.sum_of_hasCondSubgaussianMGF` on the zero-based
  adapted process, then apply the explicit finite-sum MGF bound and rewrite the
  caller's one-based sum and coefficient.
Source: Mathlib filtrations and sub-Gaussian moment-generating-function APIs
Used in: stochastic optimization light-tail martingale proofs converting
  adapted one-step conditional MGF bounds into positive-horizon exponential bounds
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/assumptions/8
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine
  Learning, stochastic accelerated primal-dual -/
theorem positiveHorizonMGFBound_of_condSubgaussian_range
    {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {μ : @Measure Ω mΩ} [IsProbabilityMeasure μ]
    (filt : Filtration ℕ mΩ)
    (zeta : ℕ → Ω → ℝ) (sigma : ℕ → ℝ) (N : ℕ) (theta : ℝ)
    (Y : ℕ → Ω → ℝ) (cY : ℕ → NNReal)
    (h_adapted : StronglyAdapted filt Y)
    (h0 : HasSubgaussianMGF (Y 0) (cY 0) μ)
    (h_subG :
      ∀ i, i < N →
        HasCondSubgaussianMGF
          (filt.seq i)
          (filt.le i)
          (Y (i + 1)) (cY (i + 1)) μ)
    (hY_sum :
      ∀ ω,
        Finset.sum (Finset.Icc 1 N) (fun t => zeta t ω) =
          Finset.sum (Finset.range (N + 1)) (fun i => Y i ω))
    (hcY_sum :
      ((Finset.sum (Finset.range (N + 1)) (fun i => cY i) : NNReal) : ℝ) =
        ((3 : ℝ) / 2) * Finset.sum (Finset.Icc 1 N) (fun t => sigma t ^ 2)) :
    PositiveHorizonMGFBound μ zeta sigma N theta := by
  have hsumSubG :
      HasSubgaussianMGF
        (fun ω => Finset.sum (Finset.range (N + 1)) (fun i => Y i ω))
        (Finset.sum (Finset.range (N + 1)) (fun i => cY i))
        μ := by
    refine
      HasSubgaussianMGF.sum_of_hasCondSubgaussianMGF
        (μ := μ) (ℱ := filt)
        (Y := Y) (cY := cY) h_adapted h0 (N + 1) ?_
    intro i hi
    exact h_subG i (by simpa using hi)
  constructor
  · have hint := hsumSubG.integrable_exp_mul theta
    have hfun :
        (fun ω =>
          Real.exp
            (theta * Finset.sum (Finset.Icc 1 N) (fun t => zeta t ω))) =
        (fun ω =>
          Real.exp
            (theta * Finset.sum (Finset.range (N + 1)) (fun i => Y i ω))) := by
      funext ω
      rw [hY_sum ω]
    simpa [hfun] using hint
  · have hmgf := hsumSubG.mgf_le theta
    have hcoef :
        (theta ^ 2 *
              Finset.sum (Finset.range (N + 1)) (fun i => (cY i : ℝ))) /
            2 =
          theta ^ 2 * 3 / 4 *
            Finset.sum (Finset.Icc 1 N) (fun t => sigma t ^ 2) := by
      have hcY_sum' :
          Finset.sum (Finset.range (N + 1)) (fun i => (cY i : ℝ)) =
            ((3 : ℝ) / 2) * Finset.sum (Finset.Icc 1 N) (fun t => sigma t ^ 2) := by
        simpa using hcY_sum
      rw [hcY_sum']
      ring
    have hfun :
        (fun ω =>
          Real.exp
            (theta * Finset.sum (Finset.Icc 1 N) (fun t => zeta t ω))) =
        (fun ω =>
          Real.exp
            (theta * Finset.sum (Finset.range (N + 1)) (fun i => Y i ω))) := by
      funext ω
      rw [hY_sum ω]
    simpa [PositiveHorizonMGFBound, mgf, hfun, hcoef, mul_comm, mul_left_comm,
      mul_assoc] using hmgf



open MeasureTheory

-- Generalization plan (G0):
-- concept/name: monotone nonnegative truncation limit integrability; orig was
--   nonnegative_lintegral_bound_of_monotone_truncations.
-- generality used: arbitrary measurable space and measure; real-valued
--   nonnegative truncations and limit; no probability, filtration, convexity,
--   oracle, or finite-measure assumptions are used.
-- portable call pattern: unbounded multiplier passages in stochastic
--   supermartingale and oracle-moment proofs; H, Z, K and the truncation
--   monotone-convergence hypotheses change while the integrability and integral
--   bound conclusion stays the same.
-- counterargument checked: not paper-local traceability or a one-line wrapper;
--   the proof composes Beppo-Levi lintegral convergence with the real
--   ofReal-integral bridge to obtain both integrability and a bound.
-- coverage search: queried SOptLib/Mathlib for "integrable monotone
--   nonnegative integral bounded lintegral" and semantic LeanSearch for
--   "monotone nonnegative functions uniformly bounded integrals integrable
--   limit"; hits such as MeasureTheory.lintegral_iSup',
--   UniformIntegrable.integrable_of_ae_tendsto, and existing SOptLib
--   bounded/L2 integrability lemmas are partial but do not cover this
--   bounded-integral monotone-truncation conclusion.
-- minimal hypotheses: pointwise formulas are not parameterized; assumptions are
--   exactly measurability/nonnegativity of the limit, integrability and
--   nonnegativity of truncations, a.e. monotonicity, a.e. supremum identity, and
--   uniform real integral bound.

/-- Monotone nonnegative real truncations with uniformly bounded integrals have
an integrable limit with the same integral bound.

If `H n` is a.e. nonnegative, integrable, and a.e. monotone in `n`, its
`ENNReal.ofReal` supremum agrees a.e. with `Z`, and the real integrals of
`H n` are bounded by `K`, then `Z` is integrable and `∫ Z ≤ K`.

Layer: Glue | Gap: Level 1 (monotone nonnegative truncation integrability)
Proof: rewrite the limit lintegral with `lintegral_iSup'`, bound the supremum
  by the uniform real integral bound via `ofReal_integral_eq_lintegral_ofReal`,
  then use Mathlib's nonnegative `lintegral_ofReal` integrability criterion.
Source: Mathlib measure theory Beppo-Levi lintegral convergence and Bochner
  integral/lintegral comparison APIs
Used in: stochastic accelerated primal-dual exponential-supermartingale
  unbounded multiplier truncation
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
theorem integrable_of_monotone_nonnegative_integral_bounded
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {H : ℕ → Ω → ℝ} {Z : Ω → ℝ} {K : ℝ}
    (hZ_aesm : AEStronglyMeasurable Z μ)
    (hZ_nonneg : 0 ≤ᵐ[μ] Z)
    (hK_nonneg : 0 ≤ K)
    (hH_int : ∀ n, Integrable (H n) μ)
    (hH_nonneg : ∀ n, 0 ≤ᵐ[μ] H n)
    (hH_mono : ∀ᵐ ω ∂μ, Monotone fun n => H n ω)
    (hH_iSup :
      (fun ω => ⨆ n : ℕ, ENNReal.ofReal (H n ω)) =ᵐ[μ]
        fun ω => ENNReal.ofReal (Z ω))
    (hH_bound : ∀ n, ∫ ω, H n ω ∂μ ≤ K) :
    Integrable Z μ ∧ ∫ ω, Z ω ∂μ ≤ K := by
  have hf :
      ∀ n, AEMeasurable (fun ω => ENNReal.ofReal (H n ω)) μ := by
    intro n
    exact AEMeasurable.ennreal_ofReal
      (hH_int n).aestronglyMeasurable.aemeasurable
  have hmono_ofReal :
      ∀ᵐ ω ∂μ, Monotone fun n => ENNReal.ofReal (H n ω) := by
    filter_upwards [hH_mono] with ω hmono n k hnk
    exact ENNReal.ofReal_le_ofReal (hmono hnk)
  have hlin_trunc :
      (∫⁻ ω, ENNReal.ofReal (Z ω) ∂μ) =
        ⨆ n : ℕ, ∫⁻ ω, ENNReal.ofReal (H n ω) ∂μ := by
    calc
      (∫⁻ ω, ENNReal.ofReal (Z ω) ∂μ)
          = ∫⁻ ω, (⨆ n : ℕ, ENNReal.ofReal (H n ω)) ∂μ :=
              MeasureTheory.lintegral_congr_ae hH_iSup.symm
      _ = ⨆ n : ℕ, ∫⁻ ω, ENNReal.ofReal (H n ω) ∂μ :=
              MeasureTheory.lintegral_iSup' hf hmono_ofReal
  have htrunc_lintegral_le :
      ∀ n : ℕ, (∫⁻ ω, ENNReal.ofReal (H n ω) ∂μ) ≤ ENNReal.ofReal K := by
    intro n
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      (hH_int n) (hH_nonneg n)]
    exact ENNReal.ofReal_le_ofReal (hH_bound n)
  have hlin_le :
      (∫⁻ ω, ENNReal.ofReal (Z ω) ∂μ) ≤ ENNReal.ofReal K := by
    rw [hlin_trunc]
    exact iSup_le htrunc_lintegral_le
  have hlin_lt_top :
      (∫⁻ ω, ENNReal.ofReal (Z ω) ∂μ) < ⊤ :=
    lt_of_le_of_lt hlin_le ENNReal.ofReal_lt_top
  have hZ_int : Integrable Z μ := by
    exact
      (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hZ_aesm hZ_nonneg).mp
        (ne_of_lt hlin_lt_top)
  have hofReal_integral_le :
      ENNReal.ofReal (∫ ω, Z ω ∂μ) ≤ ENNReal.ofReal K := by
    rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hZ_int hZ_nonneg]
    exact hlin_le
  exact ⟨hZ_int, (ENNReal.ofReal_le_ofReal_iff hK_nonneg).mp hofReal_integral_le⟩


open MeasureTheory ProbabilityTheory

-- Generalization plan (G0):
-- concept/name: conditional-expectation weighted integral bound; orig was condExp_bounded_nonnegative_adapted_mul_integral_le
-- generality used: arbitrary measurable space, finite measure, sub-sigma-algebra, real-valued integrable functions; no convexity, oracle, filtration, or algorithm setup fields
-- portable call pattern: exponential-supermartingale and stochastic-descent tower steps where a nonnegative adapted multiplier weights a random factor whose conditional expectation is bounded by a constant
-- counterargument checked: not paper-local traceability because the statement removes SAPD notation and packages a recurring conditional-expectation pull-out plus integral comparison; not a pure wrapper because Mathlib supplies only the pull-out, not the final weighted integral inequality
-- coverage search: queried conditional expectation bounded nonnegative measurable multiplier integral; SOptLib hits were martingale zero-integral lemmas only, and Mathlib hit MeasureTheory.condExp_stronglyMeasurable_mul_of_bound/condExp_mul pull-out but no full integral bound
-- minimal hypotheses: replaces SapdConditionalExpectationBound with the two used facts Integrable G μ and μ[G | m] ≤ᵐ[μ] const C; keeps boundedness of F because the proof uses bounded pull-out/integrability

/-- A bounded nonnegative sub-sigma-algebra-measurable multiplier transfers a conditional
expectation bound into an unconditional weighted integral bound.

If `F` is nonnegative, integrable, bounded, and strongly measurable with respect to
`m`, while `G` is integrable and satisfies `μ[G | m] ≤ C` a.e., then `F * G` is
integrable and its integral is at most `C * ∫ F`.

Layer: Glue | Gap: Level 1 (conditional expectation pull-out weighted integral bound)
Proof: prove integrability of `F * G` from the a.e. bound on `F`, pull `F` out of
  the conditional expectation, compare conditionally using nonnegativity of `F`,
  and integrate the a.e. inequality with `MeasureTheory.integral_condExp`.
Source: Mathlib conditional expectation pull-out and Bochner integral monotonicity APIs
Used in: stochastic accelerated primal-dual exponential-supermartingale tower step
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine
  Learning, stochastic accelerated primal-dual -/
theorem integral_mul_le_const_mul_integral_of_condExp_le_bounded_nonnegative
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : @Measure Ω mΩ} [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {F G : Ω → ℝ} {C B : ℝ}
    (hF_meas : StronglyMeasurable[m] F)
    (hF_int : Integrable F μ)
    (hF_nonneg : 0 ≤ᵐ[μ] F)
    (hF_bound : ∀ᵐ ω ∂μ, ‖F ω‖ ≤ B)
    (hG_int : Integrable G μ)
    (hG_cond_le : μ[G | m] ≤ᵐ[μ] fun _ => C) :
    Integrable (fun ω => F ω * G ω) μ ∧
      ∫ ω, F ω * G ω ∂μ ≤ C * ∫ ω, F ω ∂μ := by
  have hprod_int : Integrable (fun ω => F ω * G ω) μ := by
    have hprod_aesm :=
      (hF_meas.mono hm).aestronglyMeasurable.mul hG_int.aestronglyMeasurable
    have hmajor_int : Integrable (fun ω => B * ‖G ω‖) μ :=
      hG_int.norm.const_mul B
    refine hmajor_int.mono' hprod_aesm ?_
    filter_upwards [hF_bound] with ω hBω
    calc
      ‖F ω * G ω‖ = ‖F ω‖ * ‖G ω‖ := by rw [norm_mul]
      _ ≤ B * ‖G ω‖ := mul_le_mul_of_nonneg_right hBω (norm_nonneg _)
  have hpull :
      μ[fun ω => F ω * G ω | m] =ᵐ[μ] fun ω => F ω * μ[G | m] ω :=
    MeasureTheory.condExp_mul_of_stronglyMeasurable_left
      (μ := μ) (m := m) hF_meas hprod_int hG_int
  have hcond_le :
      (fun ω => μ[fun ω => F ω * G ω | m] ω) ≤ᵐ[μ] fun ω => C * F ω := by
    filter_upwards [hpull, hG_cond_le, hF_nonneg] with ω hpullω hGω hFω
    calc
      μ[fun ω => F ω * G ω | m] ω = F ω * μ[G | m] ω := hpullω
      _ ≤ F ω * C := mul_le_mul_of_nonneg_left hGω hFω
      _ = C * F ω := by ring
  have hleft_int : Integrable (fun ω => μ[fun ω => F ω * G ω | m] ω) μ :=
    MeasureTheory.integrable_condExp
  have hright_int : Integrable (fun ω => C * F ω) μ :=
    hF_int.const_mul C
  refine ⟨hprod_int, ?_⟩
  calc
    ∫ ω, F ω * G ω ∂μ
        = ∫ ω, μ[fun ω => F ω * G ω | m] ω ∂μ := by
          symm
          exact MeasureTheory.integral_condExp (μ := μ)
            (m := m) (f := fun ω => F ω * G ω) hm
    _ ≤ ∫ ω, C * F ω ∂μ :=
          MeasureTheory.integral_mono_ae hleft_int hright_int hcond_le
    _ = C * ∫ ω, F ω ∂μ := by
          simp [MeasureTheory.integral_const_mul]


open MeasureTheory ProbabilityTheory

-- Generalization plan (G0):
-- concept/name: unbounded conditional-expectation weighted integral bound; orig was condExp_nonnegative_adapted_mul_integral_le
-- generality used: arbitrary measurable space, finite measure, sub-sigma-algebra, real-valued integrable functions; no convexity, oracle, filtration, or algorithm setup fields
-- portable call pattern: exponential-supermartingale tower steps and stochastic descent moment bounds where an unbounded nonnegative adapted multiplier weights a random factor with bounded conditional expectation
-- counterargument checked: not paper-local traceability because the statement removes SAPD notation and composes a reusable pull-out inequality with a monotone truncation passage; not covered by the bounded staged theorem because no a.e. bound on F is assumed
-- coverage search: queried "conditional expectation nonnegative multiplier integral bound" and "integral mul le const mul integral condExp nonnegative"; hits included the bounded staged theorem, Mathlib condExp pull-out lemmas, and martingale zero-integral lemmas, but no unbounded weighted conditional-expectation inequality
-- minimal hypotheses: replaces SapdConditionalExpectationBound with the two used facts Integrable G μ and μ[G | m] ≤ᵐ[μ] const C; adds only nonnegativity of G and C needed for the monotone nonnegative truncation bound

/-- A nonnegative sub-sigma-algebra-measurable multiplier transfers a conditional
expectation bound into an unconditional weighted integral bound.

If `F` is nonnegative, integrable, and strongly measurable with respect to `m`,
while `G` is nonnegative, integrable, and satisfies `μ[G | m] ≤ C` a.e., then
`F * G` is integrable and its integral is at most `C * ∫ F`.

Layer: Glue | Gap: Level 1 (unbounded conditional expectation weighted integral bound)
Proof: apply the bounded multiplier theorem to truncations `min F n`, then pass
  to the nonnegative monotone limit with the staged Beppo-Levi integrability
  criterion.
Source: Mathlib conditional expectation pull-out and Beppo-Levi lintegral APIs
Used in: stochastic accelerated primal-dual exponential-supermartingale tower step
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine
  Learning, stochastic accelerated primal-dual -/
theorem integral_mul_le_const_mul_integral_of_condExp_le_nonnegative
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : @Measure Ω mΩ} [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {F G : Ω → ℝ} {C : ℝ}
    (hF_meas : StronglyMeasurable[m] F)
    (hF_int : Integrable F μ)
    (hF_nonneg : 0 ≤ᵐ[μ] F)
    (hG_nonneg : 0 ≤ᵐ[μ] G)
    (hC_nonneg : 0 ≤ C)
    (hG_int : Integrable G μ)
    (hG_cond_le : μ[G | m] ≤ᵐ[μ] fun _ => C) :
    Integrable (fun ω => F ω * G ω) μ ∧
      ∫ ω, F ω * G ω ∂μ ≤ C * ∫ ω, F ω ∂μ := by
  have htrunc_step :
      ∀ R : ℝ, 0 ≤ R →
        Integrable (fun ω => min (F ω) R * G ω) μ ∧
          ∫ ω, min (F ω) R * G ω ∂μ ≤
            C * ∫ ω, min (F ω) R ∂μ := by
    intro R hR
    have hFcap_meas : Measurable[m] (fun ω => min (F ω) R) :=
      hF_meas.measurable.min measurable_const
    have hFcap_int : Integrable (fun ω => min (F ω) R) μ := by
      have hmajor_int : Integrable (fun ω => ‖F ω‖ + ‖R‖) μ :=
        hF_int.norm.add (integrable_const ‖R‖)
      refine hmajor_int.mono' ((hFcap_meas.mono hm le_rfl).aestronglyMeasurable) ?_
      refine ae_of_all _ ?_
      intro ω
      by_cases hle : F ω ≤ R
      · rw [min_eq_left hle]
        exact le_add_of_nonneg_right (norm_nonneg R)
      · have hge : R ≤ F ω := le_of_not_ge hle
        rw [min_eq_right hge]
        exact le_add_of_nonneg_left (norm_nonneg (F ω))
    have hFcap_nonneg : 0 ≤ᵐ[μ] fun ω => min (F ω) R := by
      filter_upwards [hF_nonneg] with ω hFω
      exact le_min hFω hR
    have hFcap_bound : ∀ᵐ ω ∂μ, ‖min (F ω) R‖ ≤ R := by
      filter_upwards [hF_nonneg] with ω hFω
      have hmin_nonneg : 0 ≤ min (F ω) R := le_min hFω hR
      rw [Real.norm_of_nonneg hmin_nonneg]
      exact min_le_right (F ω) R
    exact
      integral_mul_le_const_mul_integral_of_condExp_le_bounded_nonnegative
        (μ := μ) (m := m) (F := fun ω => min (F ω) R) (G := G)
        (C := C) (B := R) hm hFcap_meas.stronglyMeasurable hFcap_int
        hFcap_nonneg hFcap_bound hG_int hG_cond_le
  have hprod_aesm :=
    (hF_meas.mono hm).aestronglyMeasurable.mul hG_int.aestronglyMeasurable
  have hprod_nonneg : 0 ≤ᵐ[μ] fun ω => F ω * G ω := by
    filter_upwards [hF_nonneg, hG_nonneg] with ω hFω hGω
    exact mul_nonneg hFω hGω
  let H : ℕ → Ω → ℝ := fun n ω => min (F ω) (n : ℝ) * G ω
  let K : ℝ := C * ∫ ω, F ω ∂μ
  have hK_nonneg : 0 ≤ K := by
    have hF_integral_nonneg : 0 ≤ ∫ ω, F ω ∂μ :=
      MeasureTheory.integral_nonneg_of_ae hF_nonneg
    exact mul_nonneg hC_nonneg hF_integral_nonneg
  have hH_int : ∀ n, Integrable (H n) μ := by
    intro n
    simpa [H] using (htrunc_step (n : ℝ) (Nat.cast_nonneg n)).1
  have hH_nonneg : ∀ n, 0 ≤ᵐ[μ] H n := by
    intro n
    filter_upwards [hF_nonneg, hG_nonneg] with ω hFω hGω
    have hmin_nonneg : 0 ≤ min (F ω) (n : ℝ) :=
      le_min hFω (Nat.cast_nonneg n)
    exact mul_nonneg hmin_nonneg hGω
  have hH_mono : ∀ᵐ ω ∂μ, Monotone fun n => H n ω := by
    filter_upwards [hG_nonneg] with ω hGω n k hnk
    have hnkle : (n : ℝ) ≤ (k : ℝ) := by exact_mod_cast hnk
    have hmin_le : min (F ω) (n : ℝ) ≤ min (F ω) (k : ℝ) :=
      min_le_min_left (F ω) hnkle
    exact mul_le_mul_of_nonneg_right hmin_le hGω
  have hH_iSup :
      (fun ω => ⨆ n : ℕ, ENNReal.ofReal (H n ω)) =ᵐ[μ]
        fun ω => ENNReal.ofReal (F ω * G ω) := by
    filter_upwards [hF_nonneg, hG_nonneg] with ω hFω hGω
    apply le_antisymm
    · refine iSup_le ?_
      intro n
      have hmin_le : min (F ω) (n : ℝ) ≤ F ω := min_le_left _ _
      exact ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right hmin_le hGω)
    · have hceil : F ω ≤ ((Nat.ceil (F ω) : ℕ) : ℝ) := Nat.le_ceil _
      have hmin_eq : min (F ω) ((Nat.ceil (F ω) : ℕ) : ℝ) = F ω :=
        min_eq_left hceil
      have hle_sup :
          ENNReal.ofReal
              (min (F ω) ((Nat.ceil (F ω) : ℕ) : ℝ) * G ω) ≤
            ⨆ n : ℕ, ENNReal.ofReal (H n ω) :=
        le_iSup (fun n : ℕ => ENNReal.ofReal (H n ω)) (Nat.ceil (F ω))
      simpa [H, hmin_eq] using hle_sup
  have hFcap_int : ∀ n, Integrable (fun ω => min (F ω) (n : ℝ)) μ := by
    intro n
    have hFcap_meas : Measurable[m] (fun ω => min (F ω) (n : ℝ)) :=
      hF_meas.measurable.min measurable_const
    have hmajor_int : Integrable (fun ω => ‖F ω‖ + ‖(n : ℝ)‖) μ :=
      hF_int.norm.add (integrable_const ‖(n : ℝ)‖)
    refine hmajor_int.mono'
      ((hFcap_meas.mono hm le_rfl).aestronglyMeasurable) ?_
    refine ae_of_all _ ?_
    intro ω
    by_cases hle : F ω ≤ (n : ℝ)
    · rw [min_eq_left hle]
      exact le_add_of_nonneg_right (norm_nonneg (n : ℝ))
    · have hge : (n : ℝ) ≤ F ω := le_of_not_ge hle
      rw [min_eq_right hge]
      exact le_add_of_nonneg_left (norm_nonneg (F ω))
  have hH_bound : ∀ n, ∫ ω, H n ω ∂μ ≤ K := by
    intro n
    have htrunc_bound :
        ∫ ω, min (F ω) (n : ℝ) * G ω ∂μ ≤
          C * ∫ ω, min (F ω) (n : ℝ) ∂μ :=
      (htrunc_step (n : ℝ) (Nat.cast_nonneg n)).2
    have hcap_le :
        ∫ ω, min (F ω) (n : ℝ) ∂μ ≤ ∫ ω, F ω ∂μ := by
      refine MeasureTheory.integral_mono_ae (hFcap_int n) hF_int ?_
      exact ae_of_all _ (fun ω => min_le_left (F ω) (n : ℝ))
    have hmul_le :
        C * ∫ ω, min (F ω) (n : ℝ) ∂μ ≤ C * ∫ ω, F ω ∂μ :=
      mul_le_mul_of_nonneg_left hcap_le hC_nonneg
    exact le_trans (by simpa [H] using htrunc_bound) (by simpa [K] using hmul_le)
  exact
    @integrable_of_monotone_nonnegative_integral_bounded Ω mΩ μ H
      (fun ω => F ω * G ω) K hprod_aesm hprod_nonneg hK_nonneg hH_int hH_nonneg
      hH_mono hH_iSup hH_bound


open MeasureTheory ProbabilityTheory

-- Generalization plan (G0):
-- concept/name: measurability of an exponential tilt of a finite adapted
--   partial sum; orig was `lemma41_past_exp_sum_measurable`, renamed away from
--   the paper lemma number and toward the fixed-horizon filtration concept.
-- generality used: arbitrary measurable space `Ω`, arbitrary Mathlib
--   `Filtration ℕ mΩ`, real-valued indexed summands, finite horizon `N`,
--   partial horizon `k`, and scalar tilt `theta`; no measure, probability,
--   independence, integrability, convexity, oracle, or algorithm setup fields.
-- portable call pattern: martingale/MGF tower steps in stochastic mirror
--   descent, accelerated primal-dual, mirror-prox, and variance-reduced proofs
--   need the past exponential multiplier to be measurable in the current
--   filtration when each increment is adapted.
-- counterargument checked: not paper-local traceability because the statement
--   is exactly the reusable adapted finite-sum closure needed by conditional
--   expectation pull-out arguments; not a pure wrapper around existing
--   SOptLib kernel-sum helpers, which require a jointly measurable kernel and
--   sampled-coordinate shape rather than arbitrary adapted scalar summands.
-- coverage search: LeanSearch for "measurable exponential constant finite sum
--   adapted process filtration" found Mathlib `ProgMeasurable.finset_sum`,
--   `Measurable.exp`, and a.e. exponential-sum measurability; SOptLib catalog
--   search found `measurable_finset_sum_kernel_comp_of_coordinate_measurable`
--   and related kernel helpers. Coverage is partial: these do not state fixed
--   horizon measurability of `exp (theta * ∑ t ∈ Icc 1 k, zeta t)` from
--   per-index filtration measurability over a larger horizon.
-- minimal hypotheses: all already minimal; `hk : k ≤ N` is exactly needed to
--   reuse the horizon-indexed measurability assumption, and no measure
--   assumptions are used.

/-- An exponential tilt of a finite adapted partial sum is measurable at the
partial-sum horizon.

If every real summand `zeta t` is measurable with respect to the `t`th
sigma-algebra of a filtration up to horizon `N`, then for every `k ≤ N` the map
`omega ↦ exp (theta * ∑ t ∈ Icc 1 k, zeta t omega)` is measurable with respect
to the `k`th sigma-algebra.

Layer: Glue | Gap: Level 0 (adapted finite exponential-sum measurability)
Proof: use finite-sum measurability after lifting each summand from
  `filt.seq t` to `filt.seq k` by filtration monotonicity, then close under
  multiplication by a constant and `Real.exp`.
Source: Mathlib finite-sum measurability, real exponential measurability, and
  filtration monotonicity APIs
Used in: stochastic optimization martingale-MGF tower arguments where the
  past exponential multiplier must be pulled through conditional expectation
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/key_lemmas
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
theorem measurable_exp_mul_sum_Icc_of_filtration_measurable
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (filt : Filtration ℕ mΩ) (zeta : ℕ → Ω → ℝ) (N k : ℕ) (theta : ℝ)
    (hk : k ≤ N)
    (hzeta :
      ∀ t, t ∈ Finset.Icc 1 N →
        @Measurable Ω ℝ (filt.seq t) (borel ℝ) (zeta t)) :
    Measurable[filt.seq k]
      (fun ω => Real.exp
        (theta * Finset.sum (Finset.Icc 1 k) (fun t => zeta t ω))) := by
  have hsum :
      Measurable[filt.seq k]
        (fun ω => Finset.sum (Finset.Icc 1 k) (fun t => zeta t ω)) := by
    refine Finset.measurable_sum (Finset.Icc 1 k) ?_
    intro t ht
    have ht_bounds := Finset.mem_Icc.mp ht
    have htN : t ∈ Finset.Icc 1 N := by
      exact Finset.mem_Icc.mpr ⟨ht_bounds.1, Nat.le_trans ht_bounds.2 hk⟩
    exact (hzeta t htN).mono (filt.mono ht_bounds.2) le_rfl
  exact (measurable_const.mul hsum).exp

open MeasureTheory ProbabilityTheory

-- Generalization plan (G0):
-- concept/name: finite-horizon MGF bound from one-step conditional MGF bounds; orig was Lemma41PositiveHorizonMGFBound_of_oneStepConditionalMGF
-- generality used: arbitrary measurable sample space, abstract probability measure, Mathlib filtration, real-valued increments, deterministic scale schedule, finite horizon, and fixed tilt; no optimization setup, oracle, convexity, smoothness, or paper fields
-- portable call pattern: stochastic mirror descent, stochastic accelerated primal-dual, mirror-prox, and variance-reduced martingale light-tail proofs first prove per-step conditional exponential-moment bounds, then need a direct tower induction producing an explicit finite-horizon exponential-integrability and MGF bound
-- counterargument checked: Mathlib has a stronger sub-Gaussian finite-sum route under `StandardBorelSpace`, and SOptLib already stages that route in `positiveHorizonMGFBound_of_condSubgaussian_range`; this theorem is not a duplicate because it avoids conditional-kernel sub-Gaussian structure and consumes only packaged `condExpBound` one-step estimates plus adaptedness of scalar increments
-- coverage search: `rg` found staged `PositiveHorizonMGFBound`, `oneStep_condSubgaussianMGF_bound`, `measurable_exp_mul_sum_Icc_of_filtration_measurable`, and weighted conditional-expectation integral lemmas; LeanSearch found `HasSubgaussianMGF.sum_of_hasCondSubgaussianMGF`, `HasCondSubgaussianMGF.ae_condExp_le`, and `Filtration.condExp_condExp`, but no Mathlib theorem for this direct non-kernel tower from a finite family of explicit conditional MGF bounds
-- minimal hypotheses: uses `[IsProbabilityMeasure μ]` for the zero-horizon `∫ 1 ≤ 1` case, filtration measurability only for indices in the horizon, and one-step `condExpBound` only on `Icc 1 N`

/-- One-step conditional MGF bounds imply the positive-horizon finite-sum MGF bound.

For a real adapted process over a filtration, if each one-step exponential tilt
has conditional expectation at most the deterministic variance envelope, then
the exponential tilt of the one-based partial sum is integrable and satisfies
the product envelope bound.

Layer: Glue | Gap: Level 1 (conditional MGF tower to finite-horizon MGF bound)
Proof: induct on the horizon. At the successor step, pull the nonnegative
  adapted past exponential multiplier through the one-step conditional bound
  using the staged weighted conditional-expectation inequality, then multiply
  the previous horizon bound by the new deterministic envelope.
Source: Mathlib conditional expectation, finite-sum measurability, filtration,
  and real exponential APIs
Used in: stochastic optimization martingale-MGF tower arguments converting
  per-step conditional exponential bounds into Markov-ready horizon bounds
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/assumptions/8
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine
  Learning, stochastic accelerated primal-dual -/
theorem positiveHorizonMGFBound_of_oneStepConditionalMGFBound
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ : @Measure Ω mΩ} [IsProbabilityMeasure μ]
    (filt : Filtration ℕ mΩ)
    (zeta : ℕ → Ω → ℝ) (sigma : ℕ → ℝ) (N : ℕ) (theta : ℝ)
    (hzeta :
      ∀ t, t ∈ Finset.Icc 1 N →
        @Measurable Ω ℝ (filt.seq t) (borel ℝ) (zeta t))
    (hone :
      ∀ t, t ∈ Finset.Icc 1 N →
        condExpBound μ
          (filt.seq (t - 1))
          (fun ω => Real.exp (theta * zeta t ω))
          (fun _ => Real.exp (((3 * theta ^ 2) / 4) * sigma t ^ 2))) :
    PositiveHorizonMGFBound μ zeta sigma N theta := by
  classical
  induction N with
  | zero =>
      constructor
      · simp
      · simp
  | succ k ih =>
      have hzeta_k :
          ∀ t, t ∈ Finset.Icc 1 k →
            @Measurable Ω ℝ (filt.seq t) (borel ℝ) (zeta t) := by
        intro t ht
        exact hzeta t
          (Finset.mem_Icc.mpr
            ⟨(Finset.mem_Icc.mp ht).1,
              Nat.le_trans (Finset.mem_Icc.mp ht).2 (Nat.le_succ k)⟩)
      have hone_k :
          ∀ t, t ∈ Finset.Icc 1 k →
            condExpBound μ
              (filt.seq (t - 1))
              (fun ω => Real.exp (theta * zeta t ω))
              (fun _ => Real.exp (((3 * theta ^ 2) / 4) * sigma t ^ 2)) := by
        intro t ht
        exact hone t
          (Finset.mem_Icc.mpr
            ⟨(Finset.mem_Icc.mp ht).1,
              Nat.le_trans (Finset.mem_Icc.mp ht).2 (Nat.le_succ k)⟩)
      have hprev : PositiveHorizonMGFBound μ zeta sigma k theta :=
        ih hzeta_k hone_k
      let F : Ω → ℝ :=
        fun ω => Real.exp (theta * Finset.sum (Finset.Icc 1 k) (fun t => zeta t ω))
      let G : Ω → ℝ := fun ω => Real.exp (theta * zeta (k + 1) ω)
      let C : ℝ := Real.exp (((3 * theta ^ 2) / 4) * sigma (k + 1) ^ 2)
      have hF_meas : Measurable[filt.seq k] F := by
        simpa [F] using
          measurable_exp_mul_sum_Icc_of_filtration_measurable
            filt zeta k k theta le_rfl hzeta_k
      have hF_int : Integrable F μ := by
        simpa [F, PositiveHorizonMGFBound] using hprev.1
      have hF_nonneg : 0 ≤ᵐ[μ] F :=
        ae_of_all _ fun ω => (Real.exp_pos _).le
      have hG_nonneg : 0 ≤ᵐ[μ] G :=
        ae_of_all _ fun ω => (Real.exp_pos _).le
      have hstep_one :
          condExpBound μ (filt.seq k) G (fun _ => C) := by
        have ht : k + 1 ∈ Finset.Icc 1 (k + 1) := by
          exact Finset.mem_Icc.mpr ⟨Nat.succ_pos k, le_rfl⟩
        simpa [G, C] using hone (k + 1) ht
      have hstep :
          Integrable (fun ω => F ω * G ω) μ ∧
            ∫ ω, F ω * G ω ∂μ ≤ C * ∫ ω, F ω ∂μ :=
        integral_mul_le_const_mul_integral_of_condExp_le_nonnegative
          (μ := μ) (m := filt.seq k) (F := F) (G := G) (C := C)
          (filt.le k) hF_meas.stronglyMeasurable hF_int hF_nonneg hG_nonneg
          (Real.exp_pos _).le
          (condExpBound.integrable hstep_one)
          (condExpBound.ae_le hstep_one)
      have hprod_eq :
          (fun ω => F ω * G ω) =
            fun ω =>
              Real.exp
                (theta * Finset.sum (Finset.Icc 1 (k + 1)) (fun t => zeta t ω)) := by
        funext ω
        rw [show Finset.sum (Finset.Icc 1 (k + 1)) (fun t => zeta t ω) =
            Finset.sum (Finset.Icc 1 k) (fun t => zeta t ω) + zeta (k + 1) ω by
          rw [Finset.sum_Icc_succ_top (Nat.succ_pos k)]]
        simp [F, G, Real.exp_add, mul_add, mul_comm]
      constructor
      · simpa [hprod_eq] using hstep.1
      · have hprev_bound :
            ∫ ω, F ω ∂μ ≤
              Real.exp
                (((3 * theta ^ 2) / 4) *
                  Finset.sum (Finset.Icc 1 k) (fun t => sigma t ^ 2)) := by
          simpa [F, PositiveHorizonMGFBound] using hprev.2
        calc
          ∫ ω,
              Real.exp
                (theta * Finset.sum (Finset.Icc 1 (k + 1)) (fun t => zeta t ω)) ∂μ
              = ∫ ω, F ω * G ω ∂μ := by
                rw [← hprod_eq]
          _ ≤ C * ∫ ω, F ω ∂μ := hstep.2
          _ ≤ C *
              Real.exp
                (((3 * theta ^ 2) / 4) *
                  Finset.sum (Finset.Icc 1 k) (fun t => sigma t ^ 2)) := by
                exact mul_le_mul_of_nonneg_left hprev_bound (Real.exp_pos _).le
          _ =
              Real.exp
                (((3 * theta ^ 2) / 4) *
                  Finset.sum (Finset.Icc 1 (k + 1)) (fun t => sigma t ^ 2)) := by
                rw [← Real.exp_add]
                congr 1
                rw [Finset.sum_Icc_succ_top (Nat.succ_pos k)]
                ring


open MeasureTheory ProbabilityTheory

-- Generalization plan (G0):
-- concept/name: scaled a.e. upper-bound integration against an additive budget; orig was expected_gap_scaled_envelope_integral_bridge
-- generality used: arbitrary measurable space, probability measure, real-valued functions, integrability, positive real scale
-- portable call pattern: accelerated stochastic approximation expected-gap proof step; the gap process, correction term, scale, and deterministic budget change while the conclusion stays an inverse-scaled integral budget
-- counterargument checked: not paper-local traceability because the statement is the reusable measure-theoretic passage from a scaled pathwise/a.e. descent envelope to an expected bound; not a pure wrapper around one Mathlib lemma because it combines unscaling, a.e. integral monotonicity, probability constant integration, and scalar budget spending
-- coverage search: queried SOptLib/Mathlib for integral monotonicity, affine integral bounds, inverse scaling, and budget bounds; closest hits were `integral_le_integral_affine_combination` and bounded-process moment lemmas, which do not consume an a.e. scaled envelope plus deterministic integral budget in this shape
-- minimal hypotheses: all already minimal for this proof shape except probability can be weakened to a measure with total mass one; `[IsProbabilityMeasure μ]` is the Mathlib-style carrier for that fact

/-- Integrate a scaled a.e. envelope and spend an additive scalar budget.

If `c * f` is almost everywhere bounded by a deterministic budget `B0` plus an
integrable correction `U`, and `B0 + ∫ U` is at most `R`, then the integral of
`f` is at most `c⁻¹ * R`.

Layer: Glue | Gap: Level 1 (scaled a.e. envelope integration)
Proof: unscale the a.e. bound by the nonnegative inverse, apply a.e. integral
  monotonicity, rewrite the integral of the constant-plus-correction term on a
  probability space, and multiply the scalar budget by `c⁻¹`.
Source: Mathlib measure theory Bochner integral monotonicity, linearity, and
  probability-measure constant integral APIs
Used in: accelerated stochastic primal-dual expected saddle-gap envelope
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/main_results/0
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem integral_le_inv_mul_budget_of_ae_mul_le_add
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f U : Ω → ℝ} {c B0 R : ℝ}
    (hc : 0 < c)
    (hf_int : Integrable f μ)
    (hU_int : Integrable U μ)
    (hupper : ∀ᵐ ω ∂μ, c * f ω ≤ B0 + U ω)
    (hbudget : B0 + ∫ ω, U ω ∂μ ≤ R) :
    ∫ ω, f ω ∂μ ≤ c⁻¹ * R := by
  have hc_nonneg : 0 ≤ c⁻¹ := inv_nonneg.mpr (le_of_lt hc)
  have hright_int : Integrable (fun ω : Ω => c⁻¹ * (B0 + U ω)) μ := by
    have hconst : Integrable (fun _ : Ω => B0) μ := integrable_const B0
    simpa using (hconst.add hU_int).const_mul c⁻¹
  have hupper_unscaled :
      ∀ᵐ ω ∂μ, f ω ≤ c⁻¹ * (B0 + U ω) := by
    filter_upwards [hupper] with ω hω
    have hscaled :
        c⁻¹ * (c * f ω) ≤ c⁻¹ * (B0 + U ω) :=
      mul_le_mul_of_nonneg_left hω hc_nonneg
    have hcne : c ≠ 0 := ne_of_gt hc
    calc
      f ω = c⁻¹ * (c * f ω) := by
        rw [← mul_assoc, inv_mul_cancel₀ hcne, one_mul]
      _ ≤ c⁻¹ * (B0 + U ω) := hscaled
  have hintegral_le :
      ∫ ω, f ω ∂μ ≤ ∫ ω, c⁻¹ * (B0 + U ω) ∂μ :=
    integral_mono_ae hf_int hright_int hupper_unscaled
  have hscaled_integral :
      ∫ ω, c⁻¹ * (B0 + U ω) ∂μ =
        c⁻¹ * (B0 + ∫ ω, U ω ∂μ) := by
    have hconst : Integrable (fun _ : Ω => B0) μ := integrable_const B0
    rw [integral_const_mul]
    rw [integral_add hconst hU_int]
    simp
  calc
    ∫ ω, f ω ∂μ
        ≤ ∫ ω, c⁻¹ * (B0 + U ω) ∂μ := hintegral_le
    _ = c⁻¹ * (B0 + ∫ ω, U ω ∂μ) := hscaled_integral
    _ ≤ c⁻¹ * R := mul_le_mul_of_nonneg_left hbudget hc_nonneg

open MeasureTheory
open scoped BigOperators

-- Generalization plan (G0):
-- concept/name: finite-sum integrability and integral bound from per-index
--   hypotheses; orig was finset_integrable_integral_bound_of_per_index, renamed
--   to expose the Mathlib-style statement shape.
-- generality used: arbitrary index type, measurable sample space, arbitrary
--   Measure Ω, real-valued summands and real deterministic bounds; no
--   probability, independence, convexity, smoothness, or oracle assumptions.
-- portable call pattern: finite-horizon stochastic descent proofs aggregate
--   per-iteration moment, residual, or error-budget bounds into a single
--   window bound; the summand formula and bound sequence change while the
--   finite-sum integrability/integral conclusion stays the same.
-- counterargument checked: Mathlib has `integrable_finset_sum` and
--   `integral_finset_sum`, but no single theorem packaging integrability,
--   integral linearity, and ordered finite-sum comparison against per-index
--   bounds; SOptLib has square-noise specializations, which this strengthens.
-- coverage search: queries "Integrable Finset.sum integral_finset_sum
--   sum_le_sum" and "from per index Integrable and integral bounds prove
--   Integrable finite sum and integral of finite sum bounded by sum bounds";
--   top hits were `MeasureTheory.integrable_finset_sum`,
--   `MeasureTheory.integral_finset_sum`, and oracle square-moment wrappers;
--   coverage partial, not full.
-- minimal hypotheses: all already minimal; the proof uses exactly per-index
--   integrability and per-index integral inequalities on the chosen finite set.

/-- Per-index integrability and integral bounds aggregate over a finite sum.

For real-valued summands indexed by a finite set, integrability of each active
summand and a per-index upper bound on its integral imply integrability of the
pointwise finite sum and the corresponding bound by the finite sum of budgets.

Layer: Glue | Gap: Level 0 (finite-sum integral-bound aggregation)
Proof: apply Mathlib finite-sum integrability, commute the Bochner integral
  through the finite sum, then use ordered finite-sum monotonicity.
Source: Mathlib Bochner integral finite-sum linearity and ordered real
  finite-sum APIs
Used in: stochastic accelerated primal-dual finite-horizon noise moment
  aggregation before descent-envelope integration
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
theorem integrable_finset_sum_and_integral_le_sum_of_per_index
    {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (s : Finset ι) (f : ι → Ω → ℝ) (B : ι → ℝ)
    (hf_int : ∀ i ∈ s, Integrable (f i) μ)
    (hf_bound : ∀ i ∈ s, ∫ ω, f i ω ∂μ ≤ B i) :
    Integrable (fun ω => Finset.sum s (fun i => f i ω)) μ ∧
      ∫ ω, Finset.sum s (fun i => f i ω) ∂μ ≤ Finset.sum s B := by
  constructor
  · exact MeasureTheory.integrable_finset_sum (μ := μ) (s := s) (f := f) hf_int
  · calc
      ∫ ω, Finset.sum s (fun i => f i ω) ∂μ
          = Finset.sum s (fun i => ∫ ω, f i ω ∂μ) := by
            rw [MeasureTheory.integral_finset_sum s hf_int]
      _ ≤ Finset.sum s B := by
            exact Finset.sum_le_sum hf_bound

namespace MeasureTheory

-- Generalization plan (G0):
-- concept/name: a.e.-strong measurability of the squared norm of a random
--   vector; orig was
--   generatedDeltaXHatf_sqDeviation_aestronglyMeasurable_of_realization_variational_stability.
-- generality used: arbitrary measurable domain, arbitrary measure, and a
--   seminormed additive commutative group target. No probability,
--   independence, integrability, finite-dimensional, convexity, smoothness, or
--   oracle assumptions are used.
-- portable call pattern: stochastic gradient, mirror descent, accelerated
--   primal-dual, and variance-reduced moment proofs repeatedly first prove
--   vector-valued noise measurability and then need measurability of its
--   squared norm before L2 or variance bounds; the residual/noise process and
--   measure change while the conclusion shape stays fixed.
-- counterargument checked: this is a one-line composition of Mathlib
--   `AEStronglyMeasurable.norm` and `AEStronglyMeasurable.pow`, but not a pure
--   rename of either theorem: it packages the common L2-observable target
--   shape directly. The algorithm-local generated delta theorem remains only
--   the caller-side traceability boundary.
-- coverage search: searched SOptLib catalog and symbols for
--   `AEStronglyMeasurable norm pow`, `sq norm AEStronglyMeasurable`, and
--   `norm_sq`; LeanSearch top hits were
--   `MeasureTheory.AEStronglyMeasurable.norm`,
--   `MeasureTheory.AEStronglyMeasurable.pow`, and
--   `MeasureTheory.memLp_two_iff_integrable_sq_norm`. Coverage is partial:
--   Mathlib has the two component closures but no direct squared-norm
--   measurability lemma.
-- minimal hypotheses: all already minimal; only a seminorm is needed for the
--   norm and no Borel or second-countability assumption is needed because the
--   proof starts from `AEStronglyMeasurable`.

/-- The squared norm of an a.e.-strongly measurable random vector is
a.e.-strongly measurable.

This packages the common L2 observable obtained after proving vector-valued
noise or residual measurability.

Layer: Glue | Gap: Level 0 (squared-norm measurability closure)
Proof: compose Mathlib's a.e.-strong measurability closure under `norm` with
  closure under natural powers.
Source: Mathlib measure-theoretic strongly-measurable function algebra APIs
Used in: stochastic optimization noise and residual moment measurability before
  second-moment bounds
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem AEStronglyMeasurable.norm_sq
    {Ω E : Type*} [MeasurableSpace Ω] [SeminormedAddCommGroup E]
    {μ : Measure Ω} {f : Ω → E}
    (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun ω => ‖f ω‖ ^ 2) μ := by
  simpa using hf.norm.pow 2

end MeasureTheory

open MeasureTheory
open scoped InnerProductSpace

-- Generalization plan (G0):
-- concept/name: L2 sum second-moment bound with a nonpositive expected cross
--   term; orig was generatedDeltaX_sqDeviation_integrable_and_bound_of_independent_component_bounds.
-- generality used: arbitrary measurable space and measure, real inner-product
--   target, three random vectors with a pointwise additive decomposition,
--   component squared-norm integrability, component moment budgets, and an
--   expected cross-term sign condition; no probability, filtration, convexity,
--   oracle, or independence assumptions are used by this proof.
-- portable call pattern: stochastic mirror descent, variance-reduced gradient,
--   accelerated primal-dual, and mini-batch residual decompositions call this
--   after splitting one noise vector into two L2 components and proving their
--   expected covariance cross term is nonpositive or zero.
-- counterargument checked: not paper-local because the statement contains only
--   measure, Hilbert-space random vectors, and moment/cross-moment hypotheses;
--   not covered by the existing two-multiple Young bound, which loses the
--   cross-term information and concludes `2 * Bu + 2 * Bv`.
-- coverage search: queried CATALOG/rg and lean_search_symbols for
--   "integrable sq norm add integral inner nonpositive", "cross term second
--   moment bound", and "integral norm sq add inner"; top relevant hits were
--   `integrable_sq_norm_add_and_integral_le_two_mul_add`,
--   `integrable_inner_of_integrable_sq_norm`, and
--   `integral_norm_sq_sub_le_integral_norm_sq_of_inner_sub_zero`; coverage is
--   partial only, since none proves the sharp `Bu + Bv` bound for a sum from a
--   nonpositive expected cross term.
-- minimal hypotheses: weakened setup.P to an arbitrary measure and removed
--   algorithm-specific measurability/independence fields; kept exactly the
--   component a.e. strong measurability needed to derive inner-product
--   integrability from squared-norm integrability.

/-- The squared norm of a sum is integrable and bounded by the component budgets
when the expected cross term is nonpositive.

If `w = u + v`, the component squared norms are integrable with expectations
bounded by `Bu` and `Bv`, and `∫ 2 * ⟪u, v⟫ ≤ 0`, then the squared norm of `w`
is integrable and has integral at most `Bu + Bv`.

Layer: Glue | Gap: Level 1 (sharp L2 sum bound from a nonpositive cross moment)
Proof: derive integrability of the scalar inner product from the two L2
  component hypotheses, expand `‖u + v‖ ^ 2` by the real Hilbert norm-square
  identity, use Bochner integral linearity, and apply the cross-term inequality.
Source: Mathlib Bochner integrability, integral linearity, and real Hilbert-space
  norm-square expansion APIs
Used in: stochastic accelerated primal-dual primal-noise decomposition with
  independent component residuals
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem integrable_sq_norm_add_and_integral_le_of_cross_nonpos
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {μ : Measure Ω} (u v w : Ω → E) (Bu Bv : ℝ)
    (hu_meas : AEStronglyMeasurable u μ)
    (hv_meas : AEStronglyMeasurable v μ)
    (hw_eq : ∀ ω, w ω = u ω + v ω)
    (hu_sq : Integrable (fun ω => ‖u ω‖ ^ 2) μ)
    (hu_bound : ∫ ω, ‖u ω‖ ^ 2 ∂μ ≤ Bu)
    (hv_sq : Integrable (fun ω => ‖v ω‖ ^ 2) μ)
    (hv_bound : ∫ ω, ‖v ω‖ ^ 2 ∂μ ≤ Bv)
    (hcross_nonpos : ∫ ω, 2 * ⟪u ω, v ω⟫_ℝ ∂μ ≤ 0) :
    Integrable (fun ω => ‖w ω‖ ^ 2) μ ∧
      ∫ ω, ‖w ω‖ ^ 2 ∂μ ≤ Bu + Bv := by
  have hinner_int : Integrable (fun ω => ⟪u ω, v ω⟫_ℝ) μ :=
    integrable_inner_of_integrable_sq_norm hu_meas hv_meas hu_sq hv_sq
  have hsq_eq :
      (fun ω => ‖w ω‖ ^ 2) =
        fun ω => ‖u ω‖ ^ 2 + ‖v ω‖ ^ 2 + 2 * ⟪u ω, v ω⟫_ℝ := by
    funext ω
    calc
      ‖w ω‖ ^ 2 = ‖u ω + v ω‖ ^ 2 := by rw [hw_eq ω]
      _ = ‖u ω‖ ^ 2 + 2 * ⟪u ω, v ω⟫_ℝ + ‖v ω‖ ^ 2 := by
        simpa using norm_add_sq_real (u ω) (v ω)
      _ = ‖u ω‖ ^ 2 + ‖v ω‖ ^ 2 + 2 * ⟪u ω, v ω⟫_ℝ := by
        ring
  have hw_sq : Integrable (fun ω => ‖w ω‖ ^ 2) μ := by
    rw [hsq_eq]
    exact (hu_sq.add hv_sq).add (hinner_int.const_mul 2)
  have hintegral_eq :
      ∫ ω, ‖w ω‖ ^ 2 ∂μ =
        ∫ ω, ‖u ω‖ ^ 2 ∂μ +
          ∫ ω, ‖v ω‖ ^ 2 ∂μ +
            ∫ ω, 2 * ⟪u ω, v ω⟫_ℝ ∂μ := by
    rw [hsq_eq]
    calc
      ∫ ω, ‖u ω‖ ^ 2 + ‖v ω‖ ^ 2 + 2 * ⟪u ω, v ω⟫_ℝ ∂μ
          =
            ∫ ω, (‖u ω‖ ^ 2 + ‖v ω‖ ^ 2) ∂μ +
              ∫ ω, 2 * ⟪u ω, v ω⟫_ℝ ∂μ := by
            exact integral_add (hu_sq.add hv_sq) (hinner_int.const_mul 2)
      _ =
          (∫ ω, ‖u ω‖ ^ 2 ∂μ + ∫ ω, ‖v ω‖ ^ 2 ∂μ) +
            ∫ ω, 2 * ⟪u ω, v ω⟫_ℝ ∂μ := by
            rw [integral_add hu_sq hv_sq]
      _ =
          ∫ ω, ‖u ω‖ ^ 2 ∂μ +
            ∫ ω, ‖v ω‖ ^ 2 ∂μ +
              ∫ ω, 2 * ⟪u ω, v ω⟫_ℝ ∂μ := by
            ring
  constructor
  · exact hw_sq
  · rw [hintegral_eq]
    nlinarith [hu_bound, hv_bound, hcross_nonpos]

open MeasureTheory

-- Generalization plan (G0):
-- concept/name: totalized conditional expectation bounded by a nonnegative constant; orig was lemma_4_1_totalized_condExp_light_tail_bound_of_not_integrable
-- generality used: arbitrary measurable space, arbitrary measure, arbitrary conditioning measurable space, real-valued input, and a real constant; no probability, filtration, convexity, oracle, topology, or finite-dimensional assumptions
-- portable call pattern: stochastic accelerated primal-dual, stochastic mirror descent, and martingale light-tail audits can use this when separating Mathlib's totalized conditional expectation behavior from source assumptions that must prove integrability
-- counterargument checked: not paper-local traceability because it exposes the reusable totalization boundary for conditional expectations; not a duplicate wrapper around `MeasureTheory.condExp_of_not_integrable` because downstream goals usually need the a.e. order consequence `μ[f | m] ≤ᵐ[μ] const`
-- coverage search: LeanSearch query "conditional expectation zero if function is not integrable" found `MeasureTheory.condExp_of_not_integrable` as the underlying primitive plus unrelated kernel and set integral lemmas; SOptLib/catalog searches for "condExp not integrable" and "conditional expectation le const" found packaged conditional-bound and weighted-integral lemmas, but no theorem producing this a.e. constant bound from nonintegrability
-- minimal hypotheses: added exactly the necessary `0 ≤ C` hypothesis when generalizing the paper's `Real.exp 1` bound; all other assumptions are required only to form `μ[f | m]`

/-- A nonintegrable input has totalized conditional expectation bounded by any
nonnegative constant.

Mathlib defines `μ[f | m]` to be zero when `f` is not integrable.  This lemma
packages that totalization rule in the a.e. order form used by conditional
light-tail and martingale MGF arguments.

Layer: Glue | Gap: Level 0 (conditional-expectation totalization order bound)
Proof: rewrite the conditional expectation with
  `MeasureTheory.condExp_of_not_integrable`, then use the nonnegativity of the
  constant pointwise.
Source: Mathlib conditional expectation totalization and almost-everywhere order APIs
Used in: stochastic optimization light-tail audits distinguishing totalized
  conditional-expectation bounds from source-level integrability assumptions
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/key_lemmas/lemma_4_1
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
theorem condExp_le_const_of_not_integrable
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : @Measure Ω mΩ}
    (m : MeasurableSpace Ω) {f : Ω → ℝ} {C : ℝ}
    (hf : ¬ Integrable f μ) (hC : 0 ≤ C) :
    μ[f | m] ≤ᵐ[μ] fun _ => C := by
  rw [MeasureTheory.condExp_of_not_integrable (μ := μ) (m := m) hf]
  filter_upwards [] with ω
  exact hC

open MeasureTheory

-- Generalization plan (G0):
-- concept/name: exponential Markov strict-tail reduction for a positive tilt; orig was lemma_4_1_light_tail_markov_reduction
-- generality used: arbitrary measurable space and measure; real observable; no probability, filtration, convexity, or finite-dimensional assumptions
-- portable call pattern: stochastic accelerated primal-dual, stochastic mirror descent, mirror-prox, and variance-reduced martingale proofs derive an optimized exponential-moment bound for a finite noise sum and then convert it into a strict tail probability
-- counterargument checked: not paper-local traceability because the statement is the reusable Chernoff/Markov bridge from an exponential integral bound to a strict tail; not a duplicate of the existing Markov helper because it also exponentiates the event and cancels the threshold factor
-- coverage search: SOptLib hits measure_gt_le_of_integral_le_of_nonneg and measure_ge_le_of_integral_le_of_nonneg are lower-level Markov wrappers; Mathlib hit ProbabilityTheory.measure_ge_le_exp_mul_mgf uses μ.real, non-strict tails, and mgf rather than caller-supplied ENNReal strict-tail bounds; this theorem specializes the needed strict-tail exponential-integral shape
-- minimal hypotheses: all already minimal except the source finite sum and square-root variance expression are generalized to an observable and threshold

/-- A positive exponential tilt converts an integral bound into a strict upper-tail
bound.

If `∫ exp (theta * S) ≤ exp (theta * threshold + b)` with `theta > 0`, then
the strict tail `{S > threshold}` has mass at most `exp b`.  This is the
Chernoff/Markov reduction after the exponential-moment estimate has already
been optimized.

Layer: Glue | Gap: Level 1 (strict exponential Markov tail from optimized integral bound)
Proof: map the strict tail through monotonicity of `Real.exp`, apply the SOptLib
  strict Markov wrapper to `ω ↦ exp (theta * S ω)`, and cancel the positive
  exponential threshold.
Source: Mathlib measure-theory Markov inequality and real exponential order APIs
Used in: stochastic accelerated primal-dual light-tail martingale reduction
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/key_lemmas/lemma_4_1
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
theorem measure_sum_gt_sqrt_variance_le_of_exp_integral_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (S : Ω → ℝ) (threshold theta b : ℝ)
    (htheta_pos : 0 < theta)
    (h_exp_int : Integrable (fun ω => Real.exp (theta * S ω)) μ)
    (h_exp_bound :
      ∫ ω, Real.exp (theta * S ω) ∂μ ≤ Real.exp (theta * threshold + b)) :
    μ {ω | S ω > threshold} ≤ ENNReal.ofReal (Real.exp b) := by
  have hsubset :
      {ω : Ω | S ω > threshold} ⊆
        {ω : Ω | Real.exp (theta * S ω) > Real.exp (theta * threshold)} := by
    intro ω hω
    exact Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_left hω htheta_pos)
  have hmarkov :
      μ {ω : Ω | Real.exp (theta * S ω) > Real.exp (theta * threshold)} ≤
        ENNReal.ofReal (Real.exp b) := by
    refine
      measure_gt_le_of_integral_le_of_nonneg
        (μ := μ)
        (f := fun ω => Real.exp (theta * S ω))
        (t := Real.exp (theta * threshold))
        (C := Real.exp (theta * threshold + b))
        (b := Real.exp b)
        h_exp_int ?_ h_exp_bound ?_ ?_ ?_
    · intro ω
      exact le_of_lt (Real.exp_pos _)
    · exact le_of_lt (Real.exp_pos _)
    · intro _ht
      rw [Real.exp_add]
      field_simp [Real.exp_ne_zero]
      exact le_rfl
    · intro hzero
      exfalso
      exact (Real.exp_ne_zero (theta * threshold)) hzero
  exact le_trans (measure_mono hsubset) hmarkov

open MeasureTheory ProbabilityTheory

-- Generalization plan (G0):
-- concept/name: positive-horizon exponential-supermartingale MGF bound from conditional mean-zero square-exponential light tails; orig was lemma_4_1_light_tail_exponential_supermartingale_induction_positive
-- generality used: arbitrary measurable sample space, abstract probability measure, Mathlib filtration, real increments, deterministic positive scale schedule, positive horizon, and positive tilt; no optimization setup, oracle, convexity, smoothness, or finite-dimensional assumptions
-- portable call pattern: stochastic accelerated primal-dual, stochastic mirror descent, mirror-prox, and light-tail SGD martingale proofs assume adapted mean-zero increments with conditional square-exponential bounds and need the same Markov-ready finite-sum MGF envelope
-- counterargument checked: not paper-local traceability because the statement removes SAPD setup fields and exposes the reusable martingale light-tail-to-MGF bridge; not a duplicate because existing staged entries separately cover one-step branch bounds and the tower from one-step bounds, while this theorem composes the raw assumptions future callers naturally have
-- coverage search: LeanSearch found Mathlib `HasCondSubgaussianMGF` and `HasSubgaussianMGF.sum_of_hasCondSubgaussianMGF`, which require conditional sub-Gaussian objects or standard Borel kernel structure; SOptLib/Staging search found the scalar small/large branch lemmas and `positiveHorizonMGFBound_of_oneStepConditionalMGFBound`, but no no-StandardBorel theorem from conditional mean-zero plus square-exponential bounds directly to the positive-horizon MGF conclusion
-- minimal hypotheses: keeps the positive horizon and positive tilt because this is the positive branch backfilled in the algorithm file, while all optimization-specific setup fields are replaced by `μ`, `filt`, `zeta`, and `sigma`

/-- Conditional mean-zero square-exponential light tails give a positive-horizon
finite-sum MGF bound.

For adapted real increments over a filtration, if each increment has zero
conditional mean and a conditional bound on `exp (zeta_t^2 / sigma_t^2)`, then
the exponential moment of the one-based finite sum is bounded by the standard
`3/4` square-scale envelope.

Layer: Glue | Gap: Level 2 (light-tail martingale MGF supermartingale bound)
Proof: derive a packaged one-step conditional MGF bound by splitting into the
  small- and large-tilt scalar branches, then apply the staged finite-horizon
  conditional-MGF tower theorem.
Source: Mathlib conditional expectation, filtration, Bochner integrability, and
  real exponential square-domination APIs
Used in: stochastic optimization light-tail martingale proofs converting
  adapted conditional mean-zero noise with square-exponential tails into
  finite-horizon exponential concentration bounds
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/key_lemmas/5/proof
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
theorem exp_supermartingale_mgf_bound_of_cond_mean_zero_exp_sq_bound_pos
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ : @Measure Ω mΩ} [IsProbabilityMeasure μ]
    (filt : Filtration ℕ mΩ)
    (zeta : ℕ → Ω → ℝ) (sigma : ℕ → ℝ) (N : ℕ) (theta : ℝ)
    (_hN : 1 ≤ N)
    (_htheta : 0 < theta)
    (hzeta :
      ∀ t, t ∈ Finset.Icc 1 N →
        @Measurable Ω ℝ (filt.seq t) (borel ℝ) (zeta t))
    (hsigma_pos : ∀ t, t ∈ Finset.Icc 1 N → 0 < sigma t)
    (hcond_mean_zero :
      ∀ t, t ∈ Finset.Icc 1 N →
        μ[zeta t | filt.seq (t - 1)] =ᵐ[μ] 0)
    (hcond_exp_sq_bound :
      ∀ t, t ∈ Finset.Icc 1 N →
        condExpBound μ
          (filt.seq (t - 1))
          (fun ω => Real.exp ((zeta t ω) ^ 2 / (sigma t) ^ 2))
          (fun _ => Real.exp 1)) :
    PositiveHorizonMGFBound μ zeta sigma N theta := by
  have hone :
      ∀ t, t ∈ Finset.Icc 1 N →
        condExpBound μ
          (filt.seq (t - 1))
          (fun ω => Real.exp (theta * zeta t ω))
          (fun _ => Real.exp (((3 * theta ^ 2) / 4) * sigma t ^ 2)) := by
    intro t ht
    refine ⟨?_, ?_⟩
    · have hzeta_meas : Measurable (zeta t) :=
        (hzeta t ht).mono (filt.le t) le_rfl
      exact
        integrable_exp_tilt_of_exp_sq_condExp_bound
          (μ := μ) (mCond := filt.seq (t - 1)) (X := zeta t)
          (bound := fun _ => Real.exp 1) (sigma := sigma t) (theta := theta)
          hzeta_meas (hsigma_pos t ht) (hcond_exp_sq_bound t ht)
    · have hzeta_meas : Measurable (zeta t) :=
        (hzeta t ht).mono (filt.le t) le_rfl
      have hcond_scaled_sq_bound :
          ∀ a : ℝ, 0 ≤ a → a ≤ 1 →
            condExpBound μ
              (filt.seq (t - 1))
              (fun ω => Real.exp (a * ((zeta t ω) ^ 2 / (sigma t) ^ 2)))
              (fun _ => Real.exp a) := by
        intro a ha0 ha1
        exact
          condExpBound_exp_mul_of_condExpBound_exp
            (μ := μ) (mΩ := mΩ) (m := filt.seq (t - 1))
            (X := fun ω => (zeta t ω) ^ 2 / (sigma t) ^ 2)
            (a := a) (filt.le (t - 1)) ha0 ha1 (hcond_exp_sq_bound t ht)
      by_cases hlarge : (4 / 3 : ℝ) ≤ |theta * sigma t|
      · have htilt_int :
            Integrable (fun ω => Real.exp (theta * zeta t ω)) μ :=
          integrable_exp_tilt_of_exp_sq_condExp_bound
            (μ := μ) (mCond := filt.seq (t - 1)) (X := zeta t)
            (bound := fun _ => Real.exp 1) (sigma := sigma t) (theta := theta)
            hzeta_meas (hsigma_pos t ht) (hcond_exp_sq_bound t ht)
        have hlarge_bound :=
          condExp_exp_linear_le_large_branch_of_exp_sq_condExp_bound
            (μ := μ) (m := filt.seq (t - 1)) (X := zeta t)
            (sigma := sigma t) (theta := theta)
            (hsigma_pos t ht) htilt_int
            (hcond_scaled_sq_bound (2 / 3) (by norm_num) (by norm_num))
            hlarge
        simpa [mul_assoc, mul_left_comm, mul_comm] using hlarge_bound
      · have hzeta_int : Integrable (zeta t) μ :=
          integrable_of_exp_sq_condExp_bound
            (μ := μ) (m := filt.seq (t - 1)) (X := zeta t)
            (bound := fun _ => Real.exp 1) (sigma := sigma t)
            hzeta_meas (hsigma_pos t ht) (hcond_exp_sq_bound t ht)
        have htilt_int :
            Integrable (fun ω => Real.exp (theta * zeta t ω)) μ :=
          integrable_exp_tilt_of_exp_sq_condExp_bound
            (μ := μ) (mCond := filt.seq (t - 1)) (X := zeta t)
            (bound := fun _ => Real.exp 1) (sigma := sigma t) (theta := theta)
            hzeta_meas (hsigma_pos t ht) (hcond_exp_sq_bound t ht)
        have hsmall_bound :=
          condExp_exp_linear_le_small_branch_of_mean_zero_exp_sq_bound
            (μ := μ) (m := filt.seq (t - 1)) (X := zeta t)
            (sigma := sigma t) (theta := theta)
            (hsigma_pos t ht) hlarge hzeta_int htilt_int
            (hcond_mean_zero t ht)
            (hcond_scaled_sq_bound ((9 * (theta * sigma t) ^ 2) / 16)
              (by positivity)
              (by
                have hsmall_lt : |theta * sigma t| < (4 / 3 : ℝ) :=
                  lt_of_not_ge hlarge
                have hsmall_le : |theta * sigma t| ≤ (4 / 3 : ℝ) :=
                  le_of_lt hsmall_lt
                have hsquare_le :
                    (theta * sigma t) ^ 2 ≤ (4 / 3 : ℝ) ^ 2 := by
                  rw [sq_le_sq]
                  simpa [abs_of_nonneg (by norm_num : 0 ≤ (4 / 3 : ℝ))]
                    using hsmall_le
                nlinarith))
        simpa [mul_assoc, mul_left_comm, mul_comm] using hsmall_bound
  exact
    positiveHorizonMGFBound_of_oneStepConditionalMGFBound
      (μ := μ) filt zeta sigma N theta hzeta hone

/-- Conditional mean-zero square-exponential light tails give a finite-horizon
MGF bound for nonnegative tilts.

Layer: Glue | Gap: Level 2 (light-tail martingale MGF supermartingale bound)
Proof: handle the zero horizon and zero tilt directly, otherwise call the
  positive-horizon positive-tilt bridge.
Source: Mathlib conditional expectation, filtration, Bochner integrability, and
  real exponential square-domination APIs
Used in: stochastic optimization light-tail martingale proofs converting
  adapted conditional mean-zero noise with square-exponential tails into
  finite-horizon exponential concentration bounds
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/key_lemmas/5/proof
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
theorem exp_supermartingale_mgf_bound_of_cond_mean_zero_exp_sq_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ : @Measure Ω mΩ} [IsProbabilityMeasure μ]
    (filt : Filtration ℕ mΩ)
    (zeta : ℕ → Ω → ℝ) (sigma : ℕ → ℝ) (N : ℕ) (theta : ℝ)
    (htheta : 0 ≤ theta)
    (hzeta :
      ∀ t, t ∈ Finset.Icc 1 N →
        @Measurable Ω ℝ (filt.seq t) (borel ℝ) (zeta t))
    (hsigma_pos : ∀ t, t ∈ Finset.Icc 1 N → 0 < sigma t)
    (hcond_mean_zero :
      ∀ t, t ∈ Finset.Icc 1 N →
        μ[zeta t | filt.seq (t - 1)] =ᵐ[μ] 0)
    (hcond_exp_sq_bound :
      ∀ t, t ∈ Finset.Icc 1 N →
        condExpBound μ
          (filt.seq (t - 1))
          (fun ω => Real.exp ((zeta t ω) ^ 2 / (sigma t) ^ 2))
          (fun _ => Real.exp 1)) :
    PositiveHorizonMGFBound μ zeta sigma N theta := by
  classical
  by_cases hN0 : N = 0
  · subst N
    constructor
    · simpa using (integrable_const (c := (1 : ℝ)) (μ := μ))
    · simp [PositiveHorizonMGFBound]
  by_cases htheta0 : theta = 0
  · subst theta
    constructor
    · simpa using (integrable_const (c := (1 : ℝ)) (μ := μ))
    · simp [PositiveHorizonMGFBound]
  have hNpos : 1 ≤ N := by omega
  have htheta_pos : 0 < theta := lt_of_le_of_ne htheta (Ne.symm htheta0)
  exact
    exp_supermartingale_mgf_bound_of_cond_mean_zero_exp_sq_bound_pos
      (μ := μ) filt zeta sigma N theta hNpos htheta_pos
      hzeta hsigma_pos hcond_mean_zero hcond_exp_sq_bound

open MeasureTheory ProbabilityTheory
open scoped NNReal

-- Generalization plan (G0):
-- concept/name: light-tail martingale tail bound over a filtration; orig was lemma_4_1_light_tail_martingale_bound_filtration_extension
-- generality used: arbitrary measurable space, a probability measure, a natural-number filtration, real-valued increments, deterministic positive scales, and pointwise adaptedness plus conditional mean-zero/light-tail hypotheses on the one-based horizon
-- portable call pattern: stochastic accelerated primal-dual, stochastic mirror descent, and mirror-prox proofs that derive conditional mean-zero increments with square-exponential tails and then need a direct finite-horizon concentration bound after choosing the optimized Markov tilt
-- counterargument checked: not paper-local traceability because the theorem packages the reusable filtration-level tail bound from raw conditional light-tail inputs; not a duplicate of Mathlib's conditional sub-Gaussian sum theorem because it starts from mean-zero plus exp-square control and uses the direct conditional-MGF tower without standard-Borel kernel hypotheses
-- coverage search: LeanSearch found `ProbabilityTheory.measure_sum_ge_le_of_HasCondSubgaussianMGF`, `HasSubgaussianMGF_sum_of_HasCondSubgaussianMGF`, and the conditional sub-Gaussian constructors; SOptLib staging already has the one-step conditional MGF bridge and positive-horizon MGF bound, but no direct tail theorem from raw mean-zero + square-exponential filtration hypotheses
-- minimal hypotheses: replace the SAPD setup fields by abstract `μ`, `filt`, `zeta`, `sigma`, `N`, and `lambda`; keep pointwise measurability for adaptedness, `0 < sigma t` for normalization, and a probability measure so the Markov tail step and finite-horizon MGF bound align with Mathlib's probability API

/-- A filtration-adapted sum of centered light-tailed increments has a Gaussian tail.

The hypotheses are the reusable ones used in stochastic-optimization martingale
arguments: each increment is measurable with respect to the current filtration
level, the conditional mean is zero, and the conditional square-exponential
moment is bounded by `exp 1`.  The conclusion is the optimized one-sided tail
bound for the one-based partial sum.

Layer: Glue | Gap: Level 2 (light-tail martingale tail bound over a filtration)
Proof: assemble the finite-horizon exponential MGF bound from the raw
  conditional mean-zero and square-exponential hypotheses, then optimize the
  Markov tilt at `2 λ / (3 √variance)`.
Source: Mathlib conditional sub-Gaussian and filtration APIs
Used in: stochastic accelerated primal-dual and related light-tail martingale
  concentration steps after deriving conditional mean-zero increments
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/key_lemmas/lemma_4_1
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic accelerated primal-dual -/
theorem measure_sum_gt_sqrt_variance_le_of_cond_mean_zero_exp_sq_bound_filtration
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : @Measure Ω mΩ} [IsProbabilityMeasure μ]
    (filt : Filtration ℕ mΩ)
    (zeta : ℕ → Ω → ℝ) (sigma : ℕ → ℝ) (N : ℕ) (lambda : ℝ)
    (hlambda : 0 ≤ lambda)
    (hzeta_meas :
      ∀ t, t ∈ Finset.Icc 1 N →
        @Measurable Ω ℝ (filt.seq t) (borel ℝ) (zeta t))
    (hsigma_pos : ∀ t, t ∈ Finset.Icc 1 N → 0 < sigma t)
    (hcond_mean_zero :
      ∀ t, t ∈ Finset.Icc 1 N →
        μ[zeta t | filt.seq (t - 1)] =ᵐ[μ] 0)
    (hcond_light_tail :
      ∀ t, t ∈ Finset.Icc 1 N →
        condExpBound μ (filt.seq (t - 1))
          (fun ω => Real.exp ((zeta t ω) ^ 2 / (sigma t) ^ 2))
          (fun _ => Real.exp 1)) :
    μ
        {ω : Ω |
          Finset.sum (Finset.Icc 1 N) (fun t => zeta t ω) >
            lambda * Real.sqrt (Finset.sum (Finset.Icc 1 N) (fun t => sigma t ^ 2))} ≤
      ENNReal.ofReal (Real.exp (-(lambda ^ 2) / 3)) := by
  classical
  by_cases hN : N = 0
  · subst N
    have hnonneg : 0 ≤ ENNReal.ofReal (Real.exp (-(lambda ^ 2) / 3)) := by
      exact zero_le _
    simpa using hnonneg
  by_cases hlambda_zero : lambda = 0
  · subst lambda
    calc
      μ
          {ω : Ω |
            Finset.sum (Finset.Icc 1 N) (fun t => zeta t ω) >
              0 * Real.sqrt (Finset.sum (Finset.Icc 1 N) (fun t => sigma t ^ 2))}
          ≤ μ Set.univ := measure_mono (Set.subset_univ _)
      _ = ENNReal.ofReal (Real.exp (-(0 ^ 2) / 3)) := by
        simp [measure_univ]
  let varianceProxy : ℝ :=
    Finset.sum (Finset.Icc 1 N) (fun t => sigma t ^ 2)
  have hvariance_nonneg : 0 ≤ varianceProxy := by
    exact Finset.sum_nonneg (fun i _hi => sq_nonneg (sigma i))
  have hvariance_pos : 0 < varianceProxy := by
    have hNpos : 1 ≤ N := by omega
    have hmem : 1 ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨le_rfl, hNpos⟩
    have hs1 : 0 < sigma 1 := hsigma_pos 1 hmem
    have hs1sq : 0 < sigma 1 ^ 2 := sq_pos_of_pos hs1
    have hle : sigma 1 ^ 2 ≤ varianceProxy := by
      dsimp [varianceProxy]
      exact Finset.single_le_sum (fun i _hi => sq_nonneg (sigma i)) hmem
    exact lt_of_lt_of_le hs1sq hle
  let theta : ℝ := 2 * lambda / (3 * Real.sqrt varianceProxy)
  have hlambda_pos : 0 < lambda := lt_of_le_of_ne hlambda (Ne.symm hlambda_zero)
  have htheta_pos : 0 < theta := by
    have hsqrt_pos : 0 < Real.sqrt varianceProxy := Real.sqrt_pos.mpr hvariance_pos
    have hden_pos : 0 < 3 * Real.sqrt varianceProxy := by positivity
    have hnum_pos : 0 < 2 * lambda := by positivity
    exact div_pos hnum_pos hden_pos
  have hsuper :
      PositiveHorizonMGFBound μ zeta sigma N theta := by
    exact
      exp_supermartingale_mgf_bound_of_cond_mean_zero_exp_sq_bound
        (μ := μ) filt zeta sigma N theta (le_of_lt htheta_pos)
        hzeta_meas hsigma_pos hcond_mean_zero hcond_light_tail
  have hmgf :
      Integrable
          (fun ω =>
            Real.exp
              (theta * Finset.sum (Finset.Icc 1 N) (fun t => zeta t ω)))
          μ ∧
        ∫ ω,
            Real.exp
              (theta * Finset.sum (Finset.Icc 1 N) (fun t => zeta t ω)) ∂μ ≤
          Real.exp
            (((3 * theta ^ 2) / 4) *
              Finset.sum (Finset.Icc 1 N) (fun t => sigma t ^ 2)) := by
    simpa [PositiveHorizonMGFBound] using hsuper
  have hbound :
      ∫ ω,
          Real.exp
            (theta * Finset.sum (Finset.Icc 1 N) (fun t => zeta t ω)) ∂μ ≤
        Real.exp
          (theta *
              (lambda * Real.sqrt (Finset.sum (Finset.Icc 1 N) (fun t => sigma t ^ 2))) -
            lambda ^ 2 / 3) := by
    have hsqrt_pos : 0 < Real.sqrt varianceProxy := Real.sqrt_pos.mpr hvariance_pos
    have hsqrt_ne : Real.sqrt varianceProxy ≠ 0 := ne_of_gt hsqrt_pos
    have hsqrt_sq : (Real.sqrt varianceProxy) ^ 2 = varianceProxy := by
      exact Real.sq_sqrt hvariance_nonneg
    have hleft :
        ((3 * theta ^ 2) / 4) * varianceProxy = (1 / 3) * lambda ^ 2 := by
      rw [← hsqrt_sq]
      change ((3 * (2 * lambda / (3 * Real.sqrt varianceProxy)) ^ 2) / 4) *
          (Real.sqrt varianceProxy) ^ 2 = (1 / 3) * lambda ^ 2
      field_simp [hsqrt_ne]
      ring
    have hright :
        theta *
            (lambda *
              Real.sqrt (Finset.sum (Finset.Icc 1 N) (fun t => sigma t ^ 2))) -
          lambda ^ 2 / 3 =
        (1 / 3) * lambda ^ 2 := by
      change theta * (lambda * Real.sqrt varianceProxy) - lambda ^ 2 / 3 =
        (1 / 3) * lambda ^ 2
      change (2 * lambda / (3 * Real.sqrt varianceProxy)) *
          (lambda * Real.sqrt varianceProxy) - lambda ^ 2 / 3 =
        (1 / 3) * lambda ^ 2
      field_simp [hsqrt_ne]
      ring
    exact le_trans hmgf.2 <| by
      apply Real.exp_le_exp.mpr
      rw [hleft, hright]
  exact
    measure_sum_gt_sqrt_variance_le_of_exp_integral_bound
      (μ := μ)
      (S := fun ω => Finset.sum (Finset.Icc 1 N) (fun t => zeta t ω))
      (threshold :=
        lambda * Real.sqrt (Finset.sum (Finset.Icc 1 N) (fun t => sigma t ^ 2)))
      (theta := theta) (b := -lambda ^ 2 / 3)
      htheta_pos hmgf.1 (by
        have harg :
            theta *
                (lambda *
                  Real.sqrt (Finset.sum (Finset.Icc 1 N) (fun t => sigma t ^ 2))) +
              -lambda ^ 2 / 3 =
            theta *
                (lambda *
                  Real.sqrt (Finset.sum (Finset.Icc 1 N) (fun t => sigma t ^ 2))) -
              lambda ^ 2 / 3 := by
          ring
        rwa [harg])

namespace ProbabilityTheory

-- Generalization plan (G0):
-- concept/name: subtype-valued prefix-measurable query independence from the current sample; orig was generatedAxQueryPoint_indep_current_sample_of_prefix_measurable.
-- generality used: arbitrary measurable spaces Ω, S, and X; arbitrary measure μ; an iIndepFun sample stream ξ; an arbitrary carrier predicate and raw query with pointwise carrier membership.
-- portable call pattern: constrained random-query variance and unbiasedness bridges in stochastic mirror descent, stochastic primal-dual, and conditional-gradient proofs; the carrier, query, and sample index change while the independence conclusion for the subtype query has the same shape.
-- counterargument checked: existing iIndepFun.indepFun_prefixMeasurable_future covers already subtype-valued queries, but not the common raw-query-plus-membership packaging step; this theorem composes that prefix lemma with Mathlib's Measurable.subtype_mk.
-- coverage search: searched SOptLib/CATALOG for iIndepFun, prefixMeasurable, subtype; top partial hits are iIndepFun.indepFun_prefixMeasurable_future and iIndepFun.indep_prefixFiltration_future. LeanSearch found Measurable.subtype_mk as the subtype measurability API; no full duplicate of this packaged independence bridge.
-- minimal hypotheses: no probability or finite-measure assumption is needed; the proof only uses sample measurability, iIndepFun, prefix measurability of the raw query, and pointwise carrier membership.

/-- A raw prefix-measurable query packaged into a subtype is independent of the
current sample.

For an independent sample stream `ξ`, if `query` is measurable with respect to
the strict prefix before `i` and every query value lies in a carrier predicate,
then the corresponding subtype-valued query is independent of `ξ i`.

Layer: Glue | Gap: Level 1 (subtype packaging for prefix/current independence)
Proof: use `Measurable.subtype_mk` to make the subtype-valued query prefix
  measurable, then apply the existing SOptLib prefix-measurable future-sample
  independence theorem at `n = i`.
Source: Mathlib measurable subtype API and probability independence for
  `iIndepFun` sample-prefix filtrations
Used in: stochastic primal-dual constrained random-query variance bridge
Book citation: book/PAPER/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual -/
theorem iIndepFun.indepFun_subtype_prefixMeasurable_current
    {Ω S X : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace X]
    {μ : Measure Ω}
    (ξ : ℕ → Ω → S)
    (hξ_measurable : ∀ n, Measurable (ξ n))
    (hξ_iIndep : iIndepFun ξ μ)
    {carrier : X → Prop} {query : Ω → X} {i : ℕ}
    (hquery :
      Measurable[(⨆ j < i, MeasurableSpace.comap (ξ j)
        (by infer_instance : MeasurableSpace S))] query)
    (hmem : ∀ ω, carrier (query ω)) :
    IndepFun (fun ω => (⟨query ω, hmem ω⟩ : {x : X // carrier x})) (ξ i) μ := by
  have hquery_subtype :
      Measurable[(⨆ j < i, MeasurableSpace.comap (ξ j)
        (by infer_instance : MeasurableSpace S))]
        (fun ω => (⟨query ω, hmem ω⟩ : {x : X // carrier x})) :=
    hquery.subtype_mk
  exact
    iIndepFun.indepFun_prefixMeasurable_future
      (ξ := ξ)
      (hξ_measurable := hξ_measurable)
      (hξ_iIndep := hξ_iIndep)
      (wt := fun ω => (⟨query ω, hmem ω⟩ : {x : X // carrier x}))
      (n := i)
      (i := i)
      hquery_subtype
      (le_rfl : i ≤ i)

end ProbabilityTheory


-- Generalization plan (G0):
-- concept/name: measurable strict upper-level set above a constant threshold; orig was sapd_high_probability_event_measurable_extension.
-- generality used: arbitrary measurable domain and ordered Borel codomain with the Mathlib hypotheses needed by measurableSet_lt; no measure, convexity, smoothness, or oracle assumptions.
-- portable call pattern: high-probability event formation for stochastic mirror descent, stochastic primal-dual, variance-reduced, and martingale-tail proofs; the observable and threshold change while the event measurability conclusion stays the same.
-- counterargument checked: this is a short wrapper around measurableSet_lt, but it is not a pure rename: it specializes one side to a constant and exposes the common event shape used before applying probability bounds.
-- coverage search: LeanSearch query "if f is measurable then set of omega where c < f omega is measurable" returned Mathlib measurableSet_lt; project/SOptLib searches found no named gt-constant upper-level event lemma, so this is a concept-shaped specialization rather than a duplicate.
-- minimal hypotheses: no measure parameter is included; all hypotheses are exactly those required by Mathlib's ordered Borel measurability API for measurableSet_lt.

/-- The strict upper-level event of a measurable observable above a constant is measurable.

This packages the common probability-event shape `{omega | f omega > c}` from
`measurableSet_lt`, with the lower side specialized to a constant threshold.

Layer: Glue | Gap: Level 0 (measurable strict upper-level event)
Proof: apply Mathlib's measurability theorem for strict order comparisons to
  the constant observable and the given measurable observable.
Source: Mathlib Borel ordered-space measurability API
Used in: stochastic primal-dual high-probability event formation before applying tail bounds
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for Machine Learning, stochastic accelerated primal-dual method -/
theorem measurableSet_gt_const_of_measurable
    {Ω α : Type*} [MeasurableSpace Ω]
    [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    [LinearOrder α] [SecondCountableTopology α] [OrderClosedTopology α]
    {f : Ω → α} {c : α} (hf : Measurable f) :
    MeasurableSet {ω | f ω > c} := by
  exact measurableSet_lt measurable_const hf


-- Generalization plan (G0):
-- concept/name: L2 closure and second-moment Young bound for a sum of two
--   random vectors; orig was sq_norm_add_integrable_and_bound_of_component_bounds.
-- generality used: arbitrary measurable space and measure, seminormed additive
--   commutative group target, component squared-norm integrability and scalar
--   integral bounds; no probability, filtration, convexity, or oracle assumptions.
-- portable call pattern: stochastic mirror descent, accelerated primal-dual,
--   and variance-reduced residual decompositions call this after splitting one
--   noise vector into two square-integrable components with separate budgets.
-- counterargument checked: not paper-local because the statement contains only
--   measure, random vectors, and moment budgets; not a pure wrapper because it
--   combines pointwise Young domination with integrability-by-domination and
--   integral monotonicity.
-- coverage search: queried CATALOG and lean_search_symbols for
--   "integrable sq_norm add component bounds" and "norm add memLp integral";
--   top hits were SOptLib.norm_add_sq_le_two_mul_norm_sq_add_two_mul_norm_sq,
--   integrable_inner_of_integrable_sq_norm, and integrable_sq_norm_of_ae_bound;
--   coverage partial only, since none packages the sum integrability plus
--   integral bound from two component second-moment budgets.
-- minimal hypotheses: weakened E from inner-product/normed-space to
--   SeminormedAddCommGroup and setup.P to an arbitrary measure; kept only the
--   sum squared-norm a.e. strong measurability needed by Integrable.mono.

/-- The squared norm of a sum is integrable and bounded by twice the component budgets.

If two vector-valued random variables have integrable squared norms with
second-moment bounds `Bu` and `Bv`, then the squared norm of their pointwise sum
is integrable and has integral at most `2 * Bu + 2 * Bv`.

Layer: Glue | Gap: Level 1 (L2 closure and Young second-moment bound for sums)
Proof: dominate `‖u + v‖ ^ 2` by `2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2` using the
  pointwise norm-square Young inequality, then apply integrability domination,
  a.e. integral monotonicity, and linearity of the Bochner integral on `ℝ`.
Source: Mathlib Bochner integrability, integral monotonicity, and seminormed
  additive-group norm inequalities
Used in: stochastic accelerated primal-dual primal-noise decomposition and
  stochastic mirror descent residual moment aggregation
Book citation: book/FOML/StochasticAcceleratedPrimalDual.json#/algorithm_spec/steps/2
Origin algorithm: Lan, First-order and Stochastic Optimization Methods for
  Machine Learning, stochastic accelerated primal-dual method -/
theorem integrable_sq_norm_add_and_integral_le_two_mul_add
    {Ω E : Type*} [MeasurableSpace Ω] [SeminormedAddCommGroup E]
    {μ : Measure Ω} (u v : Ω → E) (Bu Bv : ℝ)
    (hu_int : Integrable (fun ω => ‖u ω‖ ^ 2) μ)
    (hu_bound : ∫ ω, ‖u ω‖ ^ 2 ∂μ ≤ Bu)
    (hv_int : Integrable (fun ω => ‖v ω‖ ^ 2) μ)
    (hv_bound : ∫ ω, ‖v ω‖ ^ 2 ∂μ ≤ Bv)
    (hsum_aesm : AEStronglyMeasurable (fun ω => ‖u ω + v ω‖ ^ 2) μ) :
    Integrable (fun ω => ‖u ω + v ω‖ ^ 2) μ ∧
      ∫ ω, ‖u ω + v ω‖ ^ 2 ∂μ ≤ 2 * Bu + 2 * Bv := by
  let uSq : Ω → ℝ := fun ω => ‖u ω‖ ^ 2
  let vSq : Ω → ℝ := fun ω => ‖v ω‖ ^ 2
  have hu_int' : Integrable uSq μ := by
    simpa [uSq] using hu_int
  have hv_int' : Integrable vSq μ := by
    simpa [vSq] using hv_int
  have hmajor_int : Integrable (fun ω => 2 * uSq ω + 2 * vSq ω) μ :=
    (hu_int'.const_mul 2).add (hv_int'.const_mul 2)
  have hpoint_norm :
      ∀ᵐ ω ∂μ,
        ‖(‖u ω + v ω‖ ^ 2 : ℝ)‖ ≤ ‖2 * uSq ω + 2 * vSq ω‖ := by
    refine Filter.Eventually.of_forall fun ω => ?_
    have hle : ‖u ω + v ω‖ ^ 2 ≤ 2 * uSq ω + 2 * vSq ω := by
      simpa [uSq, vSq] using
        SOptLib.norm_add_sq_le_two_mul_norm_sq_add_two_mul_norm_sq (u ω) (v ω)
    have hleft_nonneg : 0 ≤ ‖u ω + v ω‖ ^ 2 := sq_nonneg _
    have hright_nonneg : 0 ≤ 2 * uSq ω + 2 * vSq ω := by
      positivity
    simpa [Real.norm_eq_abs, abs_of_nonneg hleft_nonneg,
      abs_of_nonneg hright_nonneg] using hle
  have hsum_int : Integrable (fun ω => ‖u ω + v ω‖ ^ 2) μ :=
    Integrable.mono hmajor_int hsum_aesm hpoint_norm
  have hpoint_le :
      ∀ᵐ ω ∂μ, ‖u ω + v ω‖ ^ 2 ≤ 2 * uSq ω + 2 * vSq ω := by
    refine Filter.Eventually.of_forall fun ω => ?_
    simpa [uSq, vSq] using
      SOptLib.norm_add_sq_le_two_mul_norm_sq_add_two_mul_norm_sq (u ω) (v ω)
  have hintegral_le :
      ∫ ω, ‖u ω + v ω‖ ^ 2 ∂μ ≤
        ∫ ω, (2 * uSq ω + 2 * vSq ω) ∂μ :=
    integral_mono_ae hsum_int hmajor_int hpoint_le
  constructor
  · exact hsum_int
  · calc
      ∫ ω, ‖u ω + v ω‖ ^ 2 ∂μ
          ≤ ∫ ω, (2 * uSq ω + 2 * vSq ω) ∂μ := hintegral_le
      _ = 2 * ∫ ω, uSq ω ∂μ + 2 * ∫ ω, vSq ω ∂μ := by
            rw [integral_add (hu_int'.const_mul 2) (hv_int'.const_mul 2)]
            rw [integral_const_mul, integral_const_mul]
      _ ≤ 2 * Bu + 2 * Bv := by
            nlinarith [hu_bound, hv_bound]
